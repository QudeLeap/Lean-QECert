import QEC.Coding.BalancedProduct.HorizontalSubsystem
import QEC.Coding.BalancedProduct.LiftedProductDuality
import QEC.Coding.BalancedProduct.TannerExpansion
import QEC.Coding.CodeReduction.Classical.Distance
import QEC.Coding.FiberBundle.CohomologyRepresentatives
import QEC.Coding.FiberBundle.HomologyRepresentatives

/-!
# Panteleev--Kalachev cyclic distance lemmas

This module develops the exact cyclic combinatorics used in the two cases of
PK20 Proposition 2 and its BE20 specialization.  It begins with coordinate
permutations and cyclic shifts; the later case analysis consumes these lemmas
to prove dressed-distance bounds for the horizontal subsystem.
-/

namespace QEC.Coding.BalancedProduct.PKDistance

open QEC.Coding

universe u v w

/-- Hamming weight is invariant under a bijective reindexing of coordinates. -/
theorem HammingWeight_precomp_equiv
    {F : Type u} [Zero F] [DecidableEq F]
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (z : Word F ι) :
    HammingWeight (fun k => z (e k)) = HammingWeight z := by
  classical
  have hSupport :
      (hammingSupport (fun k => z (e k))).map e.toEmbedding =
        hammingSupport z := by
    ext i
    simp [hammingSupport]
  rw [HammingWeight_eq_card_hammingSupport,
    HammingWeight_eq_card_hammingSupport, ← hSupport, Finset.card_map]

/-- Translation of the cyclic coordinate by `t`. -/
def cyclicShift
    {I : Type u} {G : Type v} [Group G] (t : G) :
    Word (ZMod 2) (I × G) →ₗ[ZMod 2] Word (ZMod 2) (I × G) where
  toFun z p := z (p.1, p.2 * t⁻¹)
  map_add' z w := by ext p; rfl
  map_smul' c z := by ext p; rfl

@[simp]
theorem cyclicShift_apply
    {I : Type u} {G : Type v} [Group G]
    (t : G) (z : Word (ZMod 2) (I × G)) (i : I) (g : G) :
    cyclicShift t z (i, g) = z (i, g * t⁻¹) := rfl

theorem HammingWeight_cyclicShift
    {I : Type u} {G : Type v} [Group G]
    [Fintype I] [Fintype G] (t : G)
    (z : Word (ZMod 2) (I × G)) :
    HammingWeight (cyclicShift t z) = HammingWeight z := by
  let e : I × G ≃ I × G :=
    (Equiv.refl I).prodCongr (Equiv.mulRight t⁻¹)
  exact HammingWeight_precomp_equiv e z

/-- The elementary triangle estimate used for every cyclic difference. -/
theorem HammingWeight_add_cyclicShift_le_two_mul
    {I : Type u} {G : Type v} [Group G]
    [Fintype I] [Fintype G] (t : G)
    (z : Word (ZMod 2) (I × G)) :
    HammingWeight (z + cyclicShift t z) ≤ 2 * HammingWeight z := by
  calc
    HammingWeight (z + cyclicShift t z) ≤
        HammingWeight z + HammingWeight (cyclicShift t z) :=
      HammingWeight_add_le z (cyclicShift t z)
    _ = HammingWeight z + HammingWeight z := by
      rw [HammingWeight_cyclicShift]
    _ = 2 * HammingWeight z := by omega

/-! ## Binary overlap and fibre weights -/

/-- The number of coordinates occupied by both binary words. -/
def binaryOverlap
    {ι : Type u} [Fintype ι]
    (left right : Word (ZMod 2) ι) : Nat :=
  HammingWeight fun i => left i * right i

private theorem binary_eq_one_of_ne_zero (value : ZMod 2)
    (hvalue : value ≠ 0) : value = 1 := by
  have hvalNe : value.val ≠ 0 :=
    (ZMod.val_eq_zero value).not.mpr hvalue
  have hvalLt : value.val < 2 := ZMod.val_lt value
  apply (ZMod.val_eq_one (by omega) value).mp
  omega

/-- Hamming weight written as a sum of coordinate indicators. -/
theorem HammingWeight_eq_sum_indicator
    {F : Type u} [Zero F] [DecidableEq F]
    {ι : Type v} [Fintype ι] (z : Word F ι) :
    HammingWeight z = ∑ i, if z i ≠ 0 then 1 else 0 := by
  classical
  rw [HammingWeight, hammingSupport, Finset.card_filter]

/-- Binary inclusion--exclusion: XOR weight plus twice the overlap is the
sum of the two input weights. -/
theorem HammingWeight_add_add_two_mul_binaryOverlap
    {ι : Type u} [Fintype ι]
    (left right : Word (ZMod 2) ι) :
    HammingWeight (left + right) + 2 * binaryOverlap left right =
      HammingWeight left + HammingWeight right := by
  classical
  have hpoint : ∀ i : ι,
      (if left i ≠ 0 then 1 else 0) + (if right i ≠ 0 then 1 else 0) =
        (if left i + right i ≠ 0 then 1 else 0) +
          2 * (if left i * right i ≠ 0 then 1 else 0) := by
    intro i
    by_cases hleft : left i = 0
    · simp [hleft]
    · rw [binary_eq_one_of_ne_zero _ hleft]
      by_cases hright : right i = 0
      · simp [hright]
      · rw [binary_eq_one_of_ne_zero _ hright]
        decide
  have hsum := Finset.sum_congr rfl
    (fun i (_hi : i ∈ (Finset.univ : Finset ι)) => hpoint i)
  simp only [HammingWeight, hammingSupport, Finset.card_filter, binaryOverlap]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hsum
  simpa only [Pi.add_apply] using hsum.symm

/-- Weight in one cyclic fibre. -/
def fibreWeight
    {I : Type u} {G : Type v} [Fintype G]
    (z : Word (ZMod 2) (I × G)) (i : I) : Nat :=
  HammingWeight fun g => z (i, g)

/-- Translation in the cyclic coordinate preserves each individual fibre
weight, not only the total word weight. -/
theorem fibreWeight_cyclicShift
    {I : Type u} {G : Type v} [Group G] [Fintype G]
    (t : G) (z : Word (ZMod 2) (I × G)) (i : I) :
    fibreWeight (cyclicShift t z) i = fibreWeight z i := by
  let e : G ≃ G := Equiv.mulRight t⁻¹
  exact HammingWeight_precomp_equiv e (fun g => z (i, g))

/-- Total weight is the sum of the weights of its cyclic fibres. -/
theorem HammingWeight_eq_sum_fibreWeight
    {I : Type u} {G : Type v} [Fintype I] [Fintype G]
    (z : Word (ZMod 2) (I × G)) :
    HammingWeight z = ∑ i, fibreWeight z i := by
  classical
  rw [HammingWeight_eq_sum_indicator]
  simp_rw [fibreWeight, HammingWeight_eq_sum_indicator]
  exact Fintype.sum_prod_type _

/-- Overlap with a cyclic shift decomposes fibrewise. -/
theorem binaryOverlap_cyclicShift_eq_sum
    {I : Type u} {G : Type v} [Group G]
    [Fintype I] [Fintype G] (t : G)
    (z : Word (ZMod 2) (I × G)) :
    binaryOverlap z (cyclicShift t z) =
      ∑ i, ∑ g, if z (i, g) ≠ 0 ∧ z (i, g * t⁻¹) ≠ 0 then 1 else 0 := by
  classical
  rw [binaryOverlap, HammingWeight_eq_sum_indicator,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro g _hg
  simp only [cyclicShift_apply]
  simp

/-- For a fixed cyclic coordinate, summing the second support indicator over
all translations recovers the weight of that fibre. -/
theorem sum_shift_indicator_eq_fibreWeight
    {I : Type u} {G : Type v} [Group G]
    [Fintype G] (z : Word (ZMod 2) (I × G)) (i : I) (g : G) :
    (∑ t, if z (i, g * t⁻¹) ≠ 0 then 1 else 0) = fibreWeight z i := by
  classical
  rw [fibreWeight, HammingWeight_eq_sum_indicator]
  let e : G ≃ G := (Equiv.inv G).trans (Equiv.mulLeft g)
  exact Fintype.sum_equiv e
    (fun t => if z (i, g * t⁻¹) ≠ 0 then 1 else 0)
    (fun x => if z (i, x) ≠ 0 then 1 else 0) (fun t => by rfl)

/-- Exact autocorrelation count: summing the overlap over every cyclic shift
gives the sum of the squares of the fibre weights. -/
theorem sum_binaryOverlap_cyclicShift
    {I : Type u} {G : Type v} [Group G]
    [Fintype I] [Fintype G]
    (z : Word (ZMod 2) (I × G)) :
    (∑ t, binaryOverlap z (cyclicShift t z)) =
      ∑ i, fibreWeight z i * fibreWeight z i := by
  classical
  calc
    (∑ t, binaryOverlap z (cyclicShift t z)) =
        ∑ t, ∑ i, ∑ g,
          if z (i, g) ≠ 0 ∧ z (i, g * t⁻¹) ≠ 0 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro t _ht
      exact binaryOverlap_cyclicShift_eq_sum t z
    _ = ∑ i, ∑ t, ∑ g,
          if z (i, g) ≠ 0 ∧ z (i, g * t⁻¹) ≠ 0 then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i, fibreWeight z i * fibreWeight z i := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_comm]
      calc
        (∑ g, ∑ t,
            if z (i, g) ≠ 0 ∧ z (i, g * t⁻¹) ≠ 0 then 1 else 0) =
            ∑ g, if z (i, g) ≠ 0 then fibreWeight z i else 0 := by
          apply Finset.sum_congr rfl
          intro g _hg
          by_cases hz : z (i, g) = 0
          · simp [hz]
          · simp only [hz, ne_eq, not_false_eq_true, true_and]
            exact sum_shift_indicator_eq_fibreWeight z i g
        _ = fibreWeight z i * fibreWeight z i := by
          rw [fibreWeight, HammingWeight_eq_sum_indicator, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro g _hg
          by_cases hz : z (i, g) = 0 <;> simp [hz]

/-- The fibrewise half-circle condition bounds twice the total cyclic
autocorrelation by `|G|` times the total weight. -/
theorem two_mul_sum_binaryOverlap_cyclicShift_le
    {I : Type u} {G : Type v} [Group G]
    [Fintype I] [Fintype G]
    (z : Word (ZMod 2) (I × G))
    (hhalf : ∀ i, 2 * fibreWeight z i ≤ Fintype.card G) :
    2 * (∑ t, binaryOverlap z (cyclicShift t z)) ≤
      Fintype.card G * HammingWeight z := by
  rw [sum_binaryOverlap_cyclicShift, HammingWeight_eq_sum_fibreWeight,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _hi
  calc
    2 * (fibreWeight z i * fibreWeight z i) =
        (2 * fibreWeight z i) * fibreWeight z i := by
      simp only [Nat.mul_assoc]
    _ ≤ Fintype.card G * fibreWeight z i :=
      Nat.mul_le_mul_right (fibreWeight z i) (hhalf i)

/-- PK20's finite averaging step: some cyclic shift has overlap at most half
the total word weight. -/
theorem exists_two_mul_binaryOverlap_cyclicShift_le
    {I : Type u} {G : Type v} [Group G]
    [Fintype I] [Fintype G]
    (z : Word (ZMod 2) (I × G))
    (hhalf : ∀ i, 2 * fibreWeight z i ≤ Fintype.card G) :
    ∃ t : G, 2 * binaryOverlap z (cyclicShift t z) ≤ HammingWeight z := by
  classical
  have htotal :
      (∑ t, 2 * binaryOverlap z (cyclicShift t z)) ≤
        Fintype.card G * HammingWeight z := by
    rw [← Finset.mul_sum]
    exact two_mul_sum_binaryOverlap_cyclicShift_le z hhalf
  by_contra hnot
  push Not at hnot
  have hlower :
      Fintype.card G * (HammingWeight z + 1) ≤
        ∑ t, 2 * binaryOverlap z (cyclicShift t z) := by
    have hconst :
        Finset.univ.sum (fun _t : G => HammingWeight z + 1) =
          Fintype.card G * (HammingWeight z + 1) := by
      simp
    rw [← hconst]
    exact Finset.sum_le_sum fun t _ht => by
      have ht := hnot t
      omega
  have hcard : 0 < Fintype.card G := Fintype.card_pos
  have himpossible :
      Fintype.card G * HammingWeight z + Fintype.card G ≤
        Fintype.card G * HammingWeight z := by
    simpa [Nat.mul_add] using hlower.trans htotal
  omega

/-- If every cyclic fibre uses at most half of its coordinates, one cyclic
difference has weight at least that of the original word.

Source: [PK20, Lemma `lm:autcorr`].
-/
theorem exists_HammingWeight_le_add_cyclicShift
    {I : Type u} {G : Type v} [Group G]
    [Fintype I] [Fintype G]
    (z : Word (ZMod 2) (I × G))
    (hhalf : ∀ i, 2 * fibreWeight z i ≤ Fintype.card G) :
    ∃ t : G, HammingWeight z ≤ HammingWeight (z + cyclicShift t z) := by
  obtain ⟨t, hoverlap⟩ :=
    exists_two_mul_binaryOverlap_cyclicShift_le z hhalf
  refine ⟨t, ?_⟩
  have hxor := HammingWeight_add_add_two_mul_binaryOverlap
    z (cyclicShift t z)
  rw [HammingWeight_cyclicShift] at hxor
  omega

/-- Canonical-index form of the autocorrelation lemma: the witnessing
translation is a generator power with exponent strictly below `q`. -/
theorem exists_cyclicPower_HammingWeight_le_add_shift
    {I : Type u} [Fintype I]
    (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hhalf : ∀ i, 2 * fibreWeight z i ≤ q) :
    ∃ t < q, HammingWeight z ≤ HammingWeight
      (z + cyclicShift (Cyclic.cyclicGenerator q ^ t) z) := by
  have hhalf' : ∀ i, 2 * fibreWeight z i ≤
      Fintype.card (Cyclic.CyclicGroup q) := by
    intro i
    simpa [Cyclic.CyclicGroup, ZMod.card] using hhalf i
  obtain ⟨g, hg⟩ := exists_HammingWeight_le_add_cyclicShift z hhalf'
  let k := (Cyclic.finCyclicEquiv q).symm g
  refine ⟨k.val, k.isLt, ?_⟩
  have hk : Cyclic.cyclicGenerator q ^ k.val = g := by
    rw [← Cyclic.finCyclicEquiv_apply_eq_generator_pow]
    exact (Cyclic.finCyclicEquiv q).apply_symm_apply g
  simpa only [hk] using hg

/-- Opposite-orientation canonical-index form of the autocorrelation lemma. -/
theorem exists_invCyclicPower_HammingWeight_le_add_shift
    {I : Type u} [Fintype I]
    (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hhalf : ∀ i, 2 * fibreWeight z i ≤ q) :
    ∃ t < q, HammingWeight z ≤ HammingWeight
      (z + cyclicShift ((Cyclic.cyclicGenerator q)⁻¹ ^ t) z) := by
  have hhalf' : ∀ i, 2 * fibreWeight z i ≤
      Fintype.card (Cyclic.CyclicGroup q) := by
    intro i
    simpa [Cyclic.CyclicGroup, ZMod.card] using hhalf i
  obtain ⟨g, hg⟩ := exists_HammingWeight_le_add_cyclicShift z hhalf'
  let k := (Cyclic.finCyclicInvEquiv q).symm g
  refine ⟨k.val, k.isLt, ?_⟩
  have hk : (Cyclic.cyclicGenerator q)⁻¹ ^ k.val = g := by
    rw [← Cyclic.finCyclicInvEquiv_apply_eq_invGenerator_pow]
    exact (Cyclic.finCyclicInvEquiv q).apply_symm_apply g
  simpa only [hk] using hg

/-! ## Minimal-threshold crossing for PK20 Case 1 -/

/-- Over binary words, the later word is bounded by the earlier word plus
their difference. -/
theorem HammingWeight_le_add_HammingWeight_add
    {ι : Type u} [Fintype ι]
    (earlier later : Word (ZMod 2) ι) :
    HammingWeight later ≤
      HammingWeight earlier + HammingWeight (later + earlier) := by
  have hreconstruct : earlier + (later + earlier) = later := by
    ext i
    change earlier i + (later i + earlier i) = later i
    by_cases hzero : earlier i = 0
    · simp [hzero]
    · rw [binary_eq_one_of_ne_zero _ hzero,
        add_comm (later i) 1, ← add_assoc]
      have htwo : (1 : ZMod 2) + 1 = 0 := by
        change (2 : ZMod 2) = 0
        exact ZMod.natCast_self 2
      rw [htwo, zero_add]
  calc
    HammingWeight later =
        HammingWeight (earlier + (later + earlier)) := by rw [hreconstruct]
    _ ≤ HammingWeight earlier + HammingWeight (later + earlier) :=
      HammingWeight_add_le earlier (later + earlier)

/-- A finite sequence that starts below a threshold and ends above it has a
first crossing.  If every step has weight at most `stepBound`, the word just
before that crossing is within `stepBound` of the threshold.

This is the minimal-`t₀` combinatorial step in [PK20, Proposition 2, Case 1].
-/
theorem exists_weight_before_first_crossing
    {ι : Type u} [Fintype ι]
    (sequence : Nat → Word (ZMod 2) ι)
    (last threshold stepBound : Nat)
    (hstart : HammingWeight (sequence 0) < threshold)
    (hend : threshold ≤ HammingWeight (sequence last))
    (hstep : ∀ t < last,
      HammingWeight (sequence (t + 1) + sequence t) ≤ stepBound) :
    ∃ t < last,
      HammingWeight (sequence t) < threshold ∧
      threshold ≤ HammingWeight (sequence (t + 1)) ∧
      threshold ≤ HammingWeight (sequence t) + stepBound := by
  induction last with
  | zero => omega
  | succ last ih =>
      by_cases hprevious : threshold ≤ HammingWeight (sequence last)
      · obtain ⟨t, htlast, htbelow, htabove, htnear⟩ :=
          ih hprevious (fun t ht => hstep t (by omega))
        exact ⟨t, by omega, htbelow, htabove, htnear⟩
      · refine ⟨last, by omega, by omega, ?_, ?_⟩
        · simpa only [Nat.succ_eq_add_one] using hend
        · have htriangle := HammingWeight_le_add_HammingWeight_add
            (sequence last) (sequence (last + 1))
          have hlastStep := hstep last (by omega)
          omega

/-! ## Cyclic prefix sums -/

/-- A binary word added to itself vanishes coordinatewise. -/
theorem binaryWord_add_self
    {ι : Type u} (z : Word (ZMod 2) ι) : z + z = 0 := by
  ext i
  change z i + z i = 0
  by_cases hz : z i = 0
  · simp [hz]
  · rw [binary_eq_one_of_ne_zero _ hz]
    change (2 : ZMod 2) = 0
    exact ZMod.natCast_self 2

/-- The polynomial prefix `1 + x + ⋯ + x^(t-1)` acting by cyclic shifts. -/
def cyclicPrefix
    {I : Type u} {G : Type v} [Group G]
    (x : G) (t : Nat) (z : Word (ZMod 2) (I × G)) :
    Word (ZMod 2) (I × G) :=
  ∑ k ∈ Finset.range t, cyclicShift (x ^ k) z

@[simp]
theorem cyclicPrefix_zero
    {I : Type u} {G : Type v} [Group G]
    (x : G) (z : Word (ZMod 2) (I × G)) :
    cyclicPrefix x 0 z = 0 := by
  simp [cyclicPrefix]

theorem cyclicPrefix_succ
    {I : Type u} {G : Type v} [Group G]
    (x : G) (t : Nat) (z : Word (ZMod 2) (I × G)) :
    cyclicPrefix x (t + 1) z =
      cyclicPrefix x t z + cyclicShift (x ^ t) z := by
  simp [cyclicPrefix, Finset.sum_range_succ]

/-- Consecutive prefix sums differ by one translated copy of the input. -/
theorem cyclicPrefix_succ_add_self
    {I : Type u} {G : Type v} [Group G]
    (x : G) (t : Nat) (z : Word (ZMod 2) (I × G)) :
    cyclicPrefix x (t + 1) z + cyclicPrefix x t z =
      cyclicShift (x ^ t) z := by
  rw [cyclicPrefix_succ, add_assoc,
    add_comm (cyclicShift (x ^ t) z) (cyclicPrefix x t z),
    ← add_assoc, binaryWord_add_self, zero_add]

/-- Every prefix step has exactly the original word's Hamming weight. -/
theorem HammingWeight_cyclicPrefix_step
    {I : Type u} {G : Type v} [Group G]
    [Fintype I] [Fintype G]
    (x : G) (t : Nat) (z : Word (ZMod 2) (I × G)) :
    HammingWeight (cyclicPrefix x (t + 1) z + cyclicPrefix x t z) =
      HammingWeight z := by
  rw [cyclicPrefix_succ_add_self, HammingWeight_cyclicShift]

theorem cyclicShift_one
    {I : Type u} {G : Type v} [Group G]
    (z : Word (ZMod 2) (I × G)) :
    cyclicShift (1 : G) z = z := by
  ext p
  simp [cyclicShift]

theorem cyclicShift_cyclicShift
    {I : Type u} {G : Type v} [Group G]
    (s t : G) (z : Word (ZMod 2) (I × G)) :
    cyclicShift s (cyclicShift t z) = cyclicShift (t * s) z := by
  ext p
  rcases p with ⟨i, g⟩
  change z (i, (g * s⁻¹) * t⁻¹) = z (i, g * (t * s)⁻¹)
  rw [mul_inv_rev]
  rw [mul_assoc]

/-- The binary geometric-series identity
`(1 + x)(1 + ⋯ + x^(t-1)) = 1 + x^t`, expressed on cyclic words. -/
theorem cyclicPrefix_add_shift
    {I : Type u} {G : Type v} [Group G]
    (x : G) (t : Nat) (z : Word (ZMod 2) (I × G)) :
    cyclicPrefix x t z + cyclicShift x (cyclicPrefix x t z) =
      z + cyclicShift (x ^ t) z := by
  induction t with
  | zero =>
      simp only [cyclicPrefix_zero, map_zero, zero_add, pow_zero,
        cyclicShift_one, binaryWord_add_self]
  | succ t ih =>
      rw [cyclicPrefix_succ, map_add, cyclicShift_cyclicShift,
        ← pow_succ]
      calc
        (cyclicPrefix x t z + cyclicShift (x ^ t) z) +
            (cyclicShift x (cyclicPrefix x t z) +
              cyclicShift (x ^ (t + 1)) z) =
            (cyclicPrefix x t z + cyclicShift x (cyclicPrefix x t z)) +
              (cyclicShift (x ^ t) z + cyclicShift (x ^ (t + 1)) z) := by
                abel
        _ = (z + cyclicShift (x ^ t) z) +
              (cyclicShift (x ^ t) z + cyclicShift (x ^ (t + 1)) z) := by
                rw [ih]
        _ = z + cyclicShift (x ^ (t + 1)) z := by
          rw [add_assoc, ← add_assoc (cyclicShift (x ^ t) z),
            binaryWord_add_self, zero_add]

/-! ## Concrete Tanner and cyclic blocks of the lifted-product boundary -/

/-- The right-regular action of the group-algebra Tanner matrix on its lifted
column word.  This is exactly the horizontal block of `LiftedProduct.boundary1`. -/
noncomputable def tannerAction
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) :
    Word (ZMod 2) (aCol × G) →ₗ[ZMod 2]
      Word (ZMod 2) (aRow × G) :=
  Matrix.toLin' fun (r, go) (c, gi) =>
    LiftedProduct.rightRegularMatrix (A r c) go gi

@[simp]
theorem tannerAction_apply
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (z : Word (ZMod 2) (aCol × G)) (r : aRow) (go : G) :
    tannerAction A z (r, go) =
      ∑ c, ∑ gi,
        LiftedProduct.rightRegularMatrix (A r c) go gi * z (c, gi) := by
  change (∑ pair : aCol × G,
    LiftedProduct.rightRegularMatrix (A r pair.1) go pair.2 * z pair) = _
  exact Fintype.sum_prod_type _

/-! ### Constant-orbit quotient lifts -/

/-- Repeat a quotient word constantly along every group orbit. -/
def constantOrbitWord
    {I G : Type} (z : Word (ZMod 2) I) : Word (ZMod 2) (I × G) :=
  fun p => z p.1

@[simp]
theorem constantOrbitWord_apply
    {I G : Type} (z : Word (ZMod 2) I) (i : I) (g : G) :
    constantOrbitWord (G := G) z (i, g) = z i := rfl

/-- Constant repetition multiplies Hamming weight by the orbit size. -/
theorem HammingWeight_constantOrbitWord
    {I G : Type} [Fintype I] [Fintype G]
    (z : Word (ZMod 2) I) :
    HammingWeight (constantOrbitWord (G := G) z) =
      Fintype.card G * HammingWeight z := by
  classical
  rw [HammingWeight_eq_sum_indicator, HammingWeight_eq_sum_indicator,
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hzi : z i = 0 <;> simp [hzi]

/-- The lifted Tanner action on a constant orbit word is the constant lift of
the augmented quotient boundary. -/
theorem tannerAction_constantOrbitWord
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (z : Word (ZMod 2) aCol) :
    tannerAction A (constantOrbitWord (G := G) z) =
      constantOrbitWord (G := G) (HorizontalSubsystem.quotientBoundary A z) := by
  funext p
  rcases p with ⟨r, go⟩
  rw [tannerAction_apply]
  simp only [constantOrbitWord_apply]
  simp_rw [HorizontalSubsystem.sum_rightRegularMatrix_row_mul]
  rfl

/-- Small-set expansion of the lifted Tanner action forces the attained
quotient Tanner distance above every radius whose constant-orbit lift is
covered by the expansion hypothesis. -/
theorem quotientMinimumDistance_ge_of_smallSetExpanding
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    {actualDistance distanceLowerBound expansionNumerator
      expansionDenominator : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode
        actualDistance)
    (hNumeratorPositive : 0 < expansionNumerator)
    (hExpansion : (tannerAction A).SmallSetExpanding
      (Fintype.card G * distanceLowerBound)
      expansionNumerator expansionDenominator) :
    distanceLowerBound ≤ actualDistance := by
  by_contra hLower
  have hDistanceLt : actualDistance < distanceLowerBound := Nat.lt_of_not_ge hLower
  rcases hMinimum with ⟨z, hz, hzNe, hzWeight, _hLeast⟩
  let lifted := constantOrbitWord (G := G) z
  have hLiftedWeight : HammingWeight lifted =
      Fintype.card G * actualDistance := by
    rw [HammingWeight_constantOrbitWord, hzWeight]
  have hRadius : HammingWeight lifted ≤
      Fintype.card G * distanceLowerBound := by
    rw [hLiftedWeight]
    exact Nat.mul_le_mul_left _ (Nat.le_of_lt hDistanceLt)
  have hzBoundary : HorizontalSubsystem.quotientBoundary A z = 0 :=
    ((HorizontalSubsystem.quotientTannerComplex A).mem_middleCycleCode_iff z).1 hz
  have hLiftedBoundary : tannerAction A lifted = 0 := by
    rw [tannerAction_constantOrbitWord, hzBoundary]
    rfl
  have hExpanded := hExpansion.2 lifted hRadius
  rw [hLiftedBoundary, HammingWeight_zero, Nat.mul_zero] at hExpanded
  have hzWeightPositive : 0 < HammingWeight z := by
    exact Nat.pos_of_ne_zero ((HammingWeight_eq_zero_iff z).not.mpr hzNe)
  have hGroupPositive : 0 < Fintype.card G := Fintype.card_pos
  have hLiftedWeightPositive : 0 < HammingWeight lifted := by
    rw [HammingWeight_constantOrbitWord]
    exact Nat.mul_pos hGroupPositive hzWeightPositive
  have hExpandedPositive :
      0 < expansionNumerator * HammingWeight lifted :=
    Nat.mul_pos hNumeratorPositive hLiftedWeightPositive
  omega

/-- Over a commutative balancing group, the lifted Tanner block commutes with
every cyclic translation. -/
theorem tannerAction_cyclicShift
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (t : G) (z : Word (ZMod 2) (aCol × G)) :
    tannerAction A (cyclicShift t z) =
      cyclicShift t (tannerAction A z) := by
  ext p
  rcases p with ⟨r, go⟩
  simp only [tannerAction_apply, cyclicShift_apply]
  apply Finset.sum_congr rfl
  intro c _hc
  calc
    (∑ gi, LiftedProduct.rightRegularMatrix (A r c) go gi *
        z (c, gi * t⁻¹)) =
        ∑ gi, LiftedProduct.rightRegularMatrix (A r c) go (gi * t) *
          z (c, gi) := by
      rw [← Equiv.sum_comp (Equiv.mulRight t⁻¹)
        (fun gi : G =>
          LiftedProduct.rightRegularMatrix (A r c) go (gi * t) *
            z (c, gi))]
      apply Fintype.sum_congr
      intro gi
      simp
    _ = ∑ gi, LiftedProduct.rightRegularMatrix (A r c) (go * t⁻¹) gi *
          z (c, gi) := by
      apply Fintype.sum_congr
      intro gi
      simp only [LiftedProduct.rightRegularMatrix]
      congr 2
      simp [mul_comm, mul_assoc]

/-- The Tanner action commutes with every finite cyclic polynomial prefix. -/
theorem tannerAction_cyclicPrefix
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (x : G) (t : Nat) (z : Word (ZMod 2) (aCol × G)) :
    tannerAction A (cyclicPrefix x t z) =
      cyclicPrefix x t (tannerAction A z) := by
  classical
  simp only [cyclicPrefix, map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  exact tannerAction_cyclicShift A (x ^ k) z

/-- Restrict a lifted-product qubit word to its horizontal block. -/
def horizontalPart
    {G aRow aCol : Type} :
    Word (ZMod 2)
        (LiftedProduct.QubitIndex aRow aCol Unit Unit G) →ₗ[ZMod 2]
      Word (ZMod 2) (aCol × G) where
  toFun z p := z (Sum.inl (p.1, (), p.2))
  map_add' z w := by ext p; rfl
  map_smul' c z := by ext p; rfl

/-- Restrict a lifted-product qubit word to its vertical block. -/
def verticalPart
    {G aRow aCol : Type} :
    Word (ZMod 2)
        (LiftedProduct.QubitIndex aRow aCol Unit Unit G) →ₗ[ZMod 2]
      Word (ZMod 2) (aRow × G) where
  toFun z p := z (Sum.inr (p.1, (), p.2))
  map_add' z w := by ext p; rfl
  map_smul' c z := by ext p; rfl

@[simp]
theorem horizontalPart_apply
    {G aRow aCol : Type}
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (c : aCol) (g : G) :
    horizontalPart z (c, g) = z (Sum.inl (c, (), g)) := rfl

@[simp]
theorem verticalPart_apply
    {G aRow aCol : Type}
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (r : aRow) (g : G) :
    verticalPart z (r, g) = z (Sum.inr (r, (), g)) := rfl

/-- The two concrete lifted-product blocks partition the physical qubits, so
their Hamming weights add exactly. -/
theorem HammingWeight_eq_horizontalPart_add_verticalPart
    {G aRow aCol : Type}
    [Fintype G] [Fintype aRow] [Fintype aCol]
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G)) :
    HammingWeight z =
      HammingWeight (horizontalPart z) + HammingWeight (verticalPart z) := by
  classical
  rw [HammingWeight_eq_sum_indicator, HammingWeight_eq_sum_indicator,
    HammingWeight_eq_sum_indicator, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_unique,
    horizontalPart_apply, verticalPart_apply]
  rfl

/-- The left-regular action of the concrete group-algebra element `1+x` is
the binary cyclic difference `z + shift x z`. -/
theorem sum_leftRegularMatrix_cyclicBoundaryElement
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G]
    (x : G) (z : Word (ZMod 2) G) (go : G) :
    (∑ gi, LiftedProduct.leftRegularMatrix
        (Cyclic.cyclicBoundaryElement x) go gi * z gi) =
      z go + z (go * x⁻¹) := by
  classical
  have hone :
      (∑ gi : G, (if go * gi⁻¹ = 1 then 1 else 0) * z gi) = z go := by
    rw [Fintype.sum_eq_single go]
    · simp
    · intro gi hne
      have hnot : go * gi⁻¹ ≠ 1 := by
        intro heq
        apply hne
        simpa using congrArg (fun y => y⁻¹ * go) heq
      simp [hnot]
  have hx :
      (∑ gi : G, (if go * gi⁻¹ = x then 1 else 0) * z gi) =
        z (go * x⁻¹) := by
    rw [Fintype.sum_eq_single (go * x⁻¹)]
    · simp [mul_comm]
    · intro gi hne
      have hnot : go * gi⁻¹ ≠ x := by
        intro heq
        apply hne
        have := congrArg (fun y => y⁻¹ * go) heq
        simpa [mul_comm, mul_assoc] using this
      simp [hnot]
  rw [Cyclic.cyclicBoundaryElement,
    LiftedProduct.leftRegularMatrix_add]
  simp only [Matrix.add_apply, LiftedProduct.leftRegularMatrix,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  simpa [eq_comm] using congrArg₂ (fun a b : ZMod 2 => a + b) hone hx

/-- Coordinatewise decomposition of the concrete cyclic lifted-product
boundary into the Tanner action on the horizontal block and `1+x` on the
vertical block. -/
theorem boundary1_eq_tannerAction_add_cyclicDifference
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (r : aRow) (go : G) :
    LiftedProduct.boundary1 (Cyclic.liftedProductData A x) z
        (r, (), go) =
      tannerAction A (horizontalPart z) (r, go) +
        (verticalPart z + cyclicShift x (verticalPart z)) (r, go) := by
  classical
  simp only [LiftedProduct.boundary1, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fintype.sum_prod_type, LiftedProduct.boundary1Matrix_inl_apply,
    LiftedProduct.boundary1Matrix_inr_apply_zmod2,
    Cyclic.liftedProductData_A, Cyclic.liftedProductData_B_apply,
    tannerAction_apply, horizontalPart_apply, verticalPart_apply,
    Pi.add_apply, cyclicShift_apply]
  simp only [if_true, Fintype.sum_unique]
  simp only [ite_mul, zero_mul]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Fintype.sum_ite_eq]
  rw [sum_leftRegularMatrix_cyclicBoundaryElement]

/-- A concrete lifted-product cycle satisfies the PK20 cycle equation
`A u = (1+x)v`; the equation is derived from `boundary1 z = 0`, not supplied
as a theorem field. -/
theorem tannerAction_horizontalPart_eq_cyclicDifference_verticalPart
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (hz : LiftedProduct.boundary1
      (Cyclic.liftedProductData A x) z = 0) :
    tannerAction A (horizontalPart z) =
      verticalPart z + cyclicShift x (verticalPart z) := by
  ext p
  rcases p with ⟨r, go⟩
  have hzero := congrFun hz (r, (), go)
  rw [boundary1_eq_tannerAction_add_cyclicDifference] at hzero
  simp only [Pi.zero_apply] at hzero
  have hself := binaryWord_add_self
    (verticalPart z + cyclicShift x (verticalPart z))
  change tannerAction A (horizontalPart z) (r, go) =
    (verticalPart z + cyclicShift x (verticalPart z)) (r, go)
  let b := (verticalPart z + cyclicShift x (verticalPart z)) (r, go)
  have hb : b + b = 0 := by
    have := congrFun hself (r, go)
    simpa only [Pi.add_apply, Pi.zero_apply, b] using this
  calc
    tannerAction A (horizontalPart z) (r, go) =
        tannerAction A (horizontalPart z) (r, go) + 0 := by simp
    _ = tannerAction A (horizontalPart z) (r, go) + (b + b) := by rw [hb]
    _ = (tannerAction A (horizontalPart z) (r, go) + b) + b := by
      rw [add_assoc]
    _ = b := by rw [hzero, zero_add]

/-- Regard a horizontal cyclic word as a degree-two word of the one-column
cyclic lifted product. -/
def primitiveTwoChain
    {G aCol : Type}
    (h : Word (ZMod 2) (aCol × G)) :
    Word (ZMod 2) (LiftedProduct.C2Index aCol Unit G) :=
  fun p => h (p.1, p.2.2)

/-- The horizontal block of the actual boundary generated by `h` is its
`1+x` cyclic difference. -/
theorem horizontalPart_boundary2_primitiveTwoChain
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (h : Word (ZMod 2) (aCol × G)) :
    horizontalPart
        (LiftedProduct.boundary2 (Cyclic.liftedProductData A x)
          (primitiveTwoChain h)) =
      h + cyclicShift x h := by
  ext p
  rcases p with ⟨c, go⟩
  simp only [horizontalPart_apply, LiftedProduct.boundary2,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, LiftedProduct.boundary2Matrix_inl_apply,
    Cyclic.liftedProductData_B_apply, primitiveTwoChain,
    Pi.add_apply, cyclicShift_apply]
  simp only [ite_mul, zero_mul, Fintype.sum_unique]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Fintype.sum_ite_eq]
  exact sum_leftRegularMatrix_cyclicBoundaryElement x (fun g => h (c, g)) go

/-- The vertical block of the same actual boundary is the Tanner action
`A h`. -/
theorem verticalPart_boundary2_primitiveTwoChain
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (h : Word (ZMod 2) (aCol × G)) :
    verticalPart
        (LiftedProduct.boundary2 (Cyclic.liftedProductData A x)
          (primitiveTwoChain h)) =
      tannerAction A h := by
  ext p
  rcases p with ⟨r, go⟩
  simp only [verticalPart_apply, LiftedProduct.boundary2,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, LiftedProduct.boundary2Matrix_inr_apply,
    Cyclic.liftedProductData_A, primitiveTwoChain, tannerAction_apply]
  simp only [Fintype.sum_unique, if_true]

/-- The vertical remainder after subtracting the boundary generated by a
horizontal primitive.  Over `ZMod 2`, subtraction is addition. -/
noncomputable def caseTwoRemainder
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (h : Word (ZMod 2) (aCol × G)) : Word (ZMod 2) (aRow × G) :=
  verticalPart z + tannerAction A h

/-- For a concrete cycle with `u=(1+x)h`, the residual vertical word is
invariant under the cyclic generator. -/
theorem caseTwoRemainder_add_shift_eq_zero
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (hz : LiftedProduct.boundary1
      (Cyclic.liftedProductData A x) z = 0)
    (h : Word (ZMod 2) (aCol × G))
    (hu : horizontalPart z = h + cyclicShift x h) :
    caseTwoRemainder A z h + cyclicShift x (caseTwoRemainder A z h) = 0 := by
  have heq :=
    tannerAction_horizontalPart_eq_cyclicDifference_verticalPart A x z hz
  rw [hu, map_add, tannerAction_cyclicShift] at heq
  rw [caseTwoRemainder, map_add]
  calc
    (verticalPart z + tannerAction A h) +
        (cyclicShift x (verticalPart z) +
          cyclicShift x (tannerAction A h)) =
      (verticalPart z + cyclicShift x (verticalPart z)) +
        (tannerAction A h + cyclicShift x (tannerAction A h)) := by
          module
    _ = (tannerAction A h + cyclicShift x (tannerAction A h)) +
        (tannerAction A h + cyclicShift x (tannerAction A h)) := by
      rw [← heq]
    _ = 0 := binaryWord_add_self _

/-- If the residual word vanished, the original word would be the actual
degree-two boundary generated by `h`.  Hence a non-boundary cycle has a
nonzero Case-2 remainder. -/
theorem caseTwoRemainder_ne_zero_of_not_boundary
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (hzNotBoundary : z ∉ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A x)).middleBoundaryCode.carrier)
    (h : Word (ZMod 2) (aCol × G))
    (hu : horizontalPart z = h + cyclicShift x h) :
    caseTwoRemainder A z h ≠ 0 := by
  intro hzero
  change verticalPart z + tannerAction A h = 0 at hzero
  have hv : verticalPart z = tannerAction A h := by
    have hself := binaryWord_add_self (tannerAction A h)
    calc
      verticalPart z = verticalPart z + 0 := by rw [add_zero]
      _ = verticalPart z + (tannerAction A h + tannerAction A h) := by
        rw [hself]
      _ = (verticalPart z + tannerAction A h) + tannerAction A h := by
        rw [add_assoc]
      _ = tannerAction A h := by rw [hzero, zero_add]
  apply hzNotBoundary
  apply ((LiftedProduct.chainComplex
    (Cyclic.liftedProductData A x)).mem_middleBoundaryCode_iff z).2
  refine ⟨primitiveTwoChain h, ?_⟩
  funext q
  cases q with
  | inl p =>
      rcases p with ⟨c, u, g⟩
      cases u
      have hblock := congrFun
        (horizontalPart_boundary2_primitiveTwoChain A x h) (c, g)
      have hu' := congrFun hu (c, g)
      exact hblock.trans hu'.symm
  | inr p =>
      rcases p with ⟨r, u, g⟩
      cases u
      have hblock := congrFun
        (verticalPart_boundary2_primitiveTwoChain A x h) (r, g)
      have hv' := congrFun hv (r, g)
      exact hblock.trans hv'.symm

/-- Over binary coefficients, a word whose `1+x` cyclic difference vanishes
is fixed by the generator. -/
theorem eq_cyclicShift_of_add_shift_eq_zero
    {I : Type u} {G : Type v} [Group G]
    (x : G) (z : Word (ZMod 2) (I × G))
    (hzero : z + cyclicShift x z = 0) :
    z = cyclicShift x z := by
  have hself := binaryWord_add_self (cyclicShift x z)
  calc
    z = z + 0 := by rw [add_zero]
    _ = z + (cyclicShift x z + cyclicShift x z) := by rw [hself]
    _ = (z + cyclicShift x z) + cyclicShift x z := by rw [add_assoc]
    _ = cyclicShift x z := by rw [hzero, zero_add]

/-- Generator invariance propagates to every nonnegative power. -/
theorem eq_cyclicShift_pow_of_add_shift_eq_zero
    {I : Type u} {G : Type v} [Group G]
    (x : G) (z : Word (ZMod 2) (I × G))
    (hzero : z + cyclicShift x z = 0) (t : Nat) :
    z = cyclicShift (x ^ t) z := by
  induction t with
  | zero =>
      simp only [pow_zero, cyclicShift_one]
  | succ t ih =>
      calc
        z = cyclicShift x z :=
          eq_cyclicShift_of_add_shift_eq_zero x z hzero
        _ = cyclicShift x (cyclicShift (x ^ t) z) := by rw [← ih]
        _ = cyclicShift (x ^ (t + 1)) z := by
          rw [cyclicShift_cyclicShift, pow_succ]

/-- A binary word invariant under the canonical generator of `CyclicGroup q`
is constant on each cyclic fibre. -/
theorem cyclicInvariant_apply_eq
    {I : Type u} (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hzero : z + cyclicShift (Cyclic.cyclicGenerator q) z = 0)
    (i : I) (g g' : Cyclic.CyclicGroup q) :
    z (i, g) = z (i, g') := by
  let k := (Cyclic.finCyclicEquiv q).symm (g'⁻¹ * g)
  have hk : Cyclic.cyclicGenerator q ^ k.val = g'⁻¹ * g := by
    rw [← Cyclic.finCyclicEquiv_apply_eq_generator_pow]
    exact (Cyclic.finCyclicEquiv q).apply_symm_apply (g'⁻¹ * g)
  have hpow := congrFun
    (eq_cyclicShift_pow_of_add_shift_eq_zero
      (Cyclic.cyclicGenerator q) z hzero k.val) (i, g)
  rw [cyclicShift_apply] at hpow
  calc
    z (i, g) = z (i, g * (Cyclic.cyclicGenerator q ^ k.val)⁻¹) := hpow
    _ = z (i, g') := by rw [hk]; simp

/-- Exact weight of a generator-invariant cyclic word: every occupied fibre
contributes all `q` coordinates. -/
theorem HammingWeight_cyclicInvariant
    {I : Type u} [Fintype I]
    (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hzero : z + cyclicShift (Cyclic.cyclicGenerator q) z = 0) :
    HammingWeight z = q * HammingWeight (fun i => z (i, 1)) := by
  classical
  rw [HammingWeight_eq_sum_indicator, HammingWeight_eq_sum_indicator,
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  have hconstant : ∀ g : Cyclic.CyclicGroup q, z (i, g) = z (i, 1) :=
    fun g => cyclicInvariant_apply_eq q z hzero i g 1
  simp_rw [hconstant]
  by_cases hi : z (i, 1) = 0
  · simp [hi]
  · simp [hi, Cyclic.CyclicGroup, ZMod.card]

/-- A nonzero generator-invariant cyclic word therefore has weight at least
the full cyclic-fibre size. -/
theorem cyclic_card_le_HammingWeight_of_invariant_ne_zero
    {I : Type u} [Fintype I]
    (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hzero : z + cyclicShift (Cyclic.cyclicGenerator q) z = 0)
    (hne : z ≠ 0) :
    q ≤ HammingWeight z := by
  rw [HammingWeight_cyclicInvariant q z hzero]
  have hbase : (fun i => z (i, 1)) ≠ 0 := by
    intro hbaseZero
    apply hne
    funext p
    rcases p with ⟨i, g⟩
    rw [cyclicInvariant_apply_eq q z hzero i g 1]
    exact congrFun hbaseZero i
  have hweightNe : HammingWeight (fun i => z (i, 1)) ≠ 0 := by
    intro hweightZero
    exact hbase ((HammingWeight_eq_zero_iff _).mp hweightZero)
  simpa using Nat.mul_le_mul_left q (Nat.one_le_iff_ne_zero.mpr hweightNe)

/-- Concrete PK Case 2 conclusion before the Tanner locality estimate: after
removing the explicit horizontal primitive boundary, every non-boundary cycle
has a residual vertical word of weight at least `q`. -/
theorem cyclic_card_le_HammingWeight_caseTwoRemainder
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit
        (Cyclic.CyclicGroup q)))
    (hz : LiftedProduct.boundary1 (Cyclic.data q A) z = 0)
    (hzNotBoundary : z ∉ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleBoundaryCode.carrier)
    (h : Word (ZMod 2) (aCol × Cyclic.CyclicGroup q))
    (hu : horizontalPart z =
      h + cyclicShift (Cyclic.cyclicGenerator q) h) :
    q ≤ HammingWeight (caseTwoRemainder A z h) := by
  apply cyclic_card_le_HammingWeight_of_invariant_ne_zero q
  · exact caseTwoRemainder_add_shift_eq_zero
      A (Cyclic.cyclicGenerator q) z hz h hu
  · exact caseTwoRemainder_ne_zero_of_not_boundary
      A (Cyclic.cyclicGenerator q) z hzNotBoundary h hu

/-- Invariance under the inverse canonical generator has the same full-fibre
weight consequence. -/
theorem cyclic_card_le_HammingWeight_of_invInvariant_ne_zero
    {I : Type u} [Fintype I]
    (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hzero : z + cyclicShift (Cyclic.cyclicGenerator q)⁻¹ z = 0)
    (hne : z ≠ 0) :
    q ≤ HammingWeight z := by
  have hInvFixed : z = cyclicShift (Cyclic.cyclicGenerator q)⁻¹ z :=
    eq_cyclicShift_of_add_shift_eq_zero
      (Cyclic.cyclicGenerator q)⁻¹ z hzero
  have hForwardFixed : cyclicShift (Cyclic.cyclicGenerator q) z = z := by
    calc
      cyclicShift (Cyclic.cyclicGenerator q) z =
          cyclicShift (Cyclic.cyclicGenerator q)
            (cyclicShift (Cyclic.cyclicGenerator q)⁻¹ z) := by rw [← hInvFixed]
      _ = cyclicShift
          ((Cyclic.cyclicGenerator q)⁻¹ * Cyclic.cyclicGenerator q) z := by
        rw [cyclicShift_cyclicShift]
      _ = z := by rw [inv_mul_cancel, cyclicShift_one]
  have hForwardZero :
      z + cyclicShift (Cyclic.cyclicGenerator q) z = 0 := by
    rw [hForwardFixed, binaryWord_add_self]
  exact cyclic_card_le_HammingWeight_of_invariant_ne_zero
    q z hForwardZero hne

/-- Actual remainder lower bound in the reversed cyclic orientation used by
the dual lifted product. -/
theorem cyclic_card_le_HammingWeight_caseTwoRemainder_invGenerator
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit
        (Cyclic.CyclicGroup q)))
    (hz : LiftedProduct.boundary1
      (Cyclic.liftedProductData A (Cyclic.cyclicGenerator q)⁻¹) z = 0)
    (hzNotBoundary : z ∉ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A
        (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryCode.carrier)
    (h : Word (ZMod 2) (aCol × Cyclic.CyclicGroup q))
    (hu : horizontalPart z =
      h + cyclicShift (Cyclic.cyclicGenerator q)⁻¹ h) :
    q ≤ HammingWeight (caseTwoRemainder A z h) := by
  apply cyclic_card_le_HammingWeight_of_invInvariant_ne_zero q
  · exact caseTwoRemainder_add_shift_eq_zero
      A (Cyclic.cyclicGenerator q)⁻¹ z hz h hu
  · exact caseTwoRemainder_ne_zero_of_not_boundary
      A (Cyclic.cyclicGenerator q)⁻¹ z hzNotBoundary h hu

/-- The source's `w`-limited estimate, applied to the actual Case-2
remainder.  The premise is the concrete column-basis bound of the Tanner map;
the terminal BE20 construction proves it from its checked-in matrix. -/
theorem caseTwo_primitive_weight_lower_bound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit
        (Cyclic.CyclicGroup q)))
    (hz : LiftedProduct.boundary1 (Cyclic.data q A) z = 0)
    (hzNotBoundary : z ∉ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleBoundaryCode.carrier)
    (h : Word (ZMod 2) (aCol × Cyclic.CyclicGroup q))
    (hu : horizontalPart z =
      h + cyclicShift (Cyclic.cyclicGenerator q) h)
    (w : Nat)
    (hColumnWeight : ∀ i : aCol × Cyclic.CyclicGroup q,
      HammingWeight (tannerAction A (Pi.single i 1)) ≤ w) :
    q ≤ HammingWeight (verticalPart z) + w * HammingWeight h := by
  have hRemainder := cyclic_card_le_HammingWeight_caseTwoRemainder
    q A z hz hzNotBoundary h hu
  have hTriangle : HammingWeight (caseTwoRemainder A z h) ≤
      HammingWeight (verticalPart z) + HammingWeight (tannerAction A h) := by
    exact HammingWeight_add_le (verticalPart z) (tannerAction A h)
  have hTanner : HammingWeight (tannerAction A h) ≤ w * HammingWeight h :=
    HammingWeight_linearMap_le_of_basis (tannerAction A) w hColumnWeight h
  exact hRemainder.trans
    (hTriangle.trans (Nat.add_le_add_left hTanner _))

/-- If the concrete vertical block is smaller than half a cyclic fibre, the
normalized primitive must carry the complementary source-scale weight. -/
theorem caseTwo_cyclic_card_le_two_mul_locality_mul_primitive_weight
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit
        (Cyclic.CyclicGroup q)))
    (hz : LiftedProduct.boundary1 (Cyclic.data q A) z = 0)
    (hzNotBoundary : z ∉ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleBoundaryCode.carrier)
    (h : Word (ZMod 2) (aCol × Cyclic.CyclicGroup q))
    (hu : horizontalPart z =
      h + cyclicShift (Cyclic.cyclicGenerator q) h)
    (w : Nat)
    (hColumnWeight : ∀ i : aCol × Cyclic.CyclicGroup q,
      HammingWeight (tannerAction A (Pi.single i 1)) ≤ w)
    (hVerticalHalf : 2 * HammingWeight (verticalPart z) ≤ q) :
    q ≤ 2 * w * HammingWeight h := by
  have hLower := caseTwo_primitive_weight_lower_bound
    q A z hz hzNotBoundary h hu w hColumnWeight
  have hqW : q ≤ 2 * (w * HammingWeight h) := by omega
  simpa only [Nat.mul_assoc] using hqW

theorem cyclicPrefix_add
    {I : Type u} {G : Type v} [Group G]
    (x : G) (t : Nat)
    (z w : Word (ZMod 2) (I × G)) :
    cyclicPrefix x t (z + w) =
      cyclicPrefix x t z + cyclicPrefix x t w := by
  classical
  simp only [cyclicPrefix, map_add, Finset.sum_add_distrib]

/-- Prefixing commutes with one further shift by the same cyclic generator. -/
theorem cyclicPrefix_cyclicShift
    {I : Type u} {G : Type v} [Group G]
    (x : G) (t : Nat) (z : Word (ZMod 2) (I × G)) :
    cyclicPrefix x t (cyclicShift x z) =
      cyclicShift x (cyclicPrefix x t z) := by
  classical
  simp only [cyclicPrefix, map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [cyclicShift_cyclicShift, cyclicShift_cyclicShift]
  congr 2
  exact (pow_mul_comm' x k).symm

/-- Applying a cyclic prefix to the `1+x` difference produces the endpoint
difference `1+x^t`. -/
theorem cyclicPrefix_cyclicDifference
    {I : Type u} {G : Type v} [Group G]
    (x : G) (t : Nat) (z : Word (ZMod 2) (I × G)) :
    cyclicPrefix x t (z + cyclicShift x z) =
      z + cyclicShift (x ^ t) z := by
  rw [cyclicPrefix_add, cyclicPrefix_cyclicShift,
    cyclicPrefix_add_shift]

/-- In Case 2, the constant cyclic remainder cancels from every translated
Tanner difference, leaving exactly the corresponding difference of the
concrete vertical block. -/
theorem tannerAction_cyclicDifference_eq_verticalDifference_caseTwo
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (hz : LiftedProduct.boundary1 (Cyclic.liftedProductData A x) z = 0)
    (h : Word (ZMod 2) (aCol × G))
    (hu : horizontalPart z = h + cyclicShift x h)
    (t : Nat) :
    tannerAction A (h + cyclicShift (x ^ t) h) =
      verticalPart z + cyclicShift (x ^ t) (verticalPart z) := by
  let r := caseTwoRemainder A z h
  have hrGenerator : r + cyclicShift x r = 0 :=
    caseTwoRemainder_add_shift_eq_zero A x z hz h hu
  have hrPower : r = cyclicShift (x ^ t) r :=
    eq_cyclicShift_pow_of_add_shift_eq_zero x r hrGenerator t
  change verticalPart z + tannerAction A h =
      cyclicShift (x ^ t) (verticalPart z + tannerAction A h) at hrPower
  rw [map_add, tannerAction_cyclicShift]
  rw [map_add] at hrPower
  have hcancel :
      (verticalPart z + tannerAction A h) +
        (cyclicShift (x ^ t) (verticalPart z) +
          cyclicShift (x ^ t) (tannerAction A h)) = 0 := by
    rw [hrPower, binaryWord_add_self]
  calc
    tannerAction A h + cyclicShift (x ^ t) (tannerAction A h) =
      (verticalPart z + cyclicShift (x ^ t) (verticalPart z)) +
        ((verticalPart z + tannerAction A h) +
          (cyclicShift (x ^ t) (verticalPart z) +
            cyclicShift (x ^ t) (tannerAction A h))) := by
        calc
          tannerAction A h + cyclicShift (x ^ t) (tannerAction A h) =
            (verticalPart z + verticalPart z) +
              (cyclicShift (x ^ t) (verticalPart z) +
                cyclicShift (x ^ t) (verticalPart z)) +
              (tannerAction A h + cyclicShift (x ^ t) (tannerAction A h)) := by
            rw [binaryWord_add_self, binaryWord_add_self, zero_add, zero_add]
          _ = (verticalPart z + cyclicShift (x ^ t) (verticalPart z)) +
              ((verticalPart z + tannerAction A h) +
                (cyclicShift (x ^ t) (verticalPart z) +
                  cyclicShift (x ^ t) (tannerAction A h))) := by
            abel
    _ = verticalPart z + cyclicShift (x ^ t) (verticalPart z) := by
      rw [hcancel, add_zero]

/-- Weight form of the preceding cancellation, matching PK20 Proposition 2,
Case 2, equation `|(1+x^t)Ah| <= 2|v|`. -/
theorem HammingWeight_tannerAction_cyclicDifference_le_two_vertical
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (hz : LiftedProduct.boundary1 (Cyclic.liftedProductData A x) z = 0)
    (h : Word (ZMod 2) (aCol × G))
    (hu : horizontalPart z = h + cyclicShift x h)
    (t : Nat) :
    HammingWeight (tannerAction A (h + cyclicShift (x ^ t) h)) ≤
        2 * HammingWeight (verticalPart z) := by
  rw [tannerAction_cyclicDifference_eq_verticalDifference_caseTwo
    A x z hz h hu t]
  exact HammingWeight_add_cyclicShift_le_two_mul (x ^ t) (verticalPart z)

/-- Source-exact first crossing for the Case-2 differences
`(1+x^t)h`.  The endpoint is supplied by the indexed autocorrelation lemma,
and each step has exactly the concrete horizontal weight `|(1+x)h|`. -/
theorem exists_caseTwo_cyclicDifference_before_crossing
    {I : Type u} [Fintype I]
    (q : Nat) [NeZero q]
    (h : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hhalf : ∀ i, 2 * fibreWeight h i ≤ q)
    (threshold : Nat) (hthreshold : 0 < threshold)
    (hPrimitive : threshold ≤ HammingWeight h) :
    ∃ t < q,
      HammingWeight
          (h + cyclicShift (Cyclic.cyclicGenerator q ^ t) h) < threshold ∧
      threshold ≤ HammingWeight
          (h + cyclicShift (Cyclic.cyclicGenerator q ^ (t + 1)) h) ∧
      threshold ≤
        HammingWeight (h + cyclicShift (Cyclic.cyclicGenerator q ^ t) h) +
          HammingWeight (h + cyclicShift (Cyclic.cyclicGenerator q) h) := by
  obtain ⟨last, hlastq, hlast⟩ :=
    exists_cyclicPower_HammingWeight_le_add_shift q h hhalf
  let sequence : Nat → Word (ZMod 2) (I × Cyclic.CyclicGroup q) :=
    fun t => h + cyclicShift (Cyclic.cyclicGenerator q ^ t) h
  have hstart : HammingWeight (sequence 0) < threshold := by
    change HammingWeight
      (h + cyclicShift (Cyclic.cyclicGenerator q ^ 0) h) < threshold
    rw [pow_zero, cyclicShift_one, binaryWord_add_self, HammingWeight_zero]
    exact hthreshold
  have hend : threshold ≤ HammingWeight (sequence last) :=
    hPrimitive.trans hlast
  have hstep : ∀ t < last,
      HammingWeight (sequence (t + 1) + sequence t) ≤
        HammingWeight
          (h + cyclicShift (Cyclic.cyclicGenerator q) h) := by
    intro t _ht
    change HammingWeight
      ((h + cyclicShift (Cyclic.cyclicGenerator q ^ (t + 1)) h) +
        (h + cyclicShift (Cyclic.cyclicGenerator q ^ t) h)) ≤ _
    rw [← cyclicPrefix_cyclicDifference
        (Cyclic.cyclicGenerator q) (t + 1) h,
      ← cyclicPrefix_cyclicDifference (Cyclic.cyclicGenerator q) t h,
      HammingWeight_cyclicPrefix_step]
  obtain ⟨t, htlast, htbelow, htabove, htnear⟩ :=
    exists_weight_before_first_crossing sequence last threshold
      (HammingWeight
        (h + cyclicShift (Cyclic.cyclicGenerator q) h))
      hstart hend hstep
  exact ⟨t, htlast.trans hlastq, htbelow, htabove, htnear⟩

/-- First-crossing theorem in the opposite cyclic orientation. -/
theorem exists_caseTwo_invCyclicDifference_before_crossing
    {I : Type u} [Fintype I]
    (q : Nat) [NeZero q]
    (h : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hhalf : ∀ i, 2 * fibreWeight h i ≤ q)
    (threshold : Nat) (hthreshold : 0 < threshold)
    (hPrimitive : threshold ≤ HammingWeight h) :
    ∃ t < q,
      HammingWeight
          (h + cyclicShift ((Cyclic.cyclicGenerator q)⁻¹ ^ t) h) < threshold ∧
      threshold ≤ HammingWeight
          (h + cyclicShift ((Cyclic.cyclicGenerator q)⁻¹ ^ (t + 1)) h) ∧
      threshold ≤ HammingWeight
          (h + cyclicShift ((Cyclic.cyclicGenerator q)⁻¹ ^ t) h) +
        HammingWeight
          (h + cyclicShift (Cyclic.cyclicGenerator q)⁻¹ h) := by
  obtain ⟨last, hlastq, hlast⟩ :=
    exists_invCyclicPower_HammingWeight_le_add_shift q h hhalf
  let x := (Cyclic.cyclicGenerator q)⁻¹
  let sequence : Nat → Word (ZMod 2) (I × Cyclic.CyclicGroup q) :=
    fun t => h + cyclicShift (x ^ t) h
  have hstart : HammingWeight (sequence 0) < threshold := by
    change HammingWeight (h + cyclicShift (x ^ 0) h) < threshold
    rw [pow_zero, cyclicShift_one, binaryWord_add_self, HammingWeight_zero]
    exact hthreshold
  have hend : threshold ≤ HammingWeight (sequence last) :=
    hPrimitive.trans hlast
  have hstep : ∀ t < last,
      HammingWeight (sequence (t + 1) + sequence t) ≤
        HammingWeight (h + cyclicShift x h) := by
    intro t _ht
    change HammingWeight
      ((h + cyclicShift (x ^ (t + 1)) h) +
        (h + cyclicShift (x ^ t) h)) ≤ _
    rw [← cyclicPrefix_cyclicDifference x (t + 1) h,
      ← cyclicPrefix_cyclicDifference x t h,
      HammingWeight_cyclicPrefix_step]
  obtain ⟨t, htlast, htbelow, htabove, htnear⟩ :=
    exists_weight_before_first_crossing sequence last threshold
      (HammingWeight (h + cyclicShift x h)) hstart hend hstep
  exact ⟨t, htlast.trans hlastq, htbelow, htabove, htnear⟩

/-- Quantitative core of PK20 Proposition 2, Case 2.  Once the normalized
primitive reaches `threshold`, expansion and cancellation of the constant
remainder force the concrete vertical block to be large. -/
theorem verticalPart_lowerBound_of_caseTwo_primitive_crossing
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit
        (Cyclic.CyclicGroup q)))
    (hz : LiftedProduct.boundary1 (Cyclic.data q A) z = 0)
    (h : Word (ZMod 2) (aCol × Cyclic.CyclicGroup q))
    (hu : horizontalPart z =
      h + cyclicShift (Cyclic.cyclicGenerator q) h)
    (hhalf : ∀ i, 2 * fibreWeight h i ≤ q)
    (threshold expansionRadius expansionNumerator expansionDenominator : Nat)
    (hthreshold : 0 < threshold)
    (hPrimitive : threshold ≤ HammingWeight h)
    (hRadius : threshold ≤ expansionRadius)
    (hExpansion : (tannerAction A).SmallSetExpanding
      expansionRadius expansionNumerator expansionDenominator) :
    expansionNumerator *
        (threshold - HammingWeight (horizontalPart z)) ≤
      2 * expansionDenominator * HammingWeight (verticalPart z) := by
  obtain ⟨t, _htq, htbelow, _htabove, htnear⟩ :=
    exists_caseTwo_cyclicDifference_before_crossing
      q h hhalf threshold hthreshold hPrimitive
  let difference := h + cyclicShift (Cyclic.cyclicGenerator q ^ t) h
  have htnear' : threshold ≤
      HammingWeight difference + HammingWeight (horizontalPart z) := by
    dsimp [difference]
    rw [hu]
    exact htnear
  have hsub : threshold - HammingWeight (horizontalPart z) ≤
      HammingWeight difference := by
    omega
  have hDifferenceRadius : HammingWeight difference ≤ expansionRadius := by
    exact (Nat.le_of_lt htbelow).trans hRadius
  have hExpand : expansionNumerator * HammingWeight difference ≤
      expansionDenominator * HammingWeight (tannerAction A difference) :=
    hExpansion.2 difference hDifferenceRadius
  have hOutput : HammingWeight (tannerAction A difference) ≤
      2 * HammingWeight (verticalPart z) := by
    exact HammingWeight_tannerAction_cyclicDifference_le_two_vertical
      A (Cyclic.cyclicGenerator q) z hz h hu t
  calc
    expansionNumerator *
        (threshold - HammingWeight (horizontalPart z)) ≤
      expansionNumerator * HammingWeight difference :=
        Nat.mul_le_mul_left expansionNumerator hsub
    _ ≤ expansionDenominator * HammingWeight (tannerAction A difference) :=
      hExpand
    _ ≤ expansionDenominator * (2 * HammingWeight (verticalPart z)) :=
      Nat.mul_le_mul_left expansionDenominator hOutput
    _ = 2 * expansionDenominator * HammingWeight (verticalPart z) := by
      simp only [Nat.mul_assoc, Nat.mul_comm]

/-- Quantitative Case-2 expansion core in the inverse cyclic orientation used
by the dual lifted product. -/
theorem verticalPart_lowerBound_of_caseTwo_invPrimitive_crossing
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit
        (Cyclic.CyclicGroup q)))
    (hz : LiftedProduct.boundary1
      (Cyclic.liftedProductData A (Cyclic.cyclicGenerator q)⁻¹) z = 0)
    (h : Word (ZMod 2) (aCol × Cyclic.CyclicGroup q))
    (hu : horizontalPart z =
      h + cyclicShift (Cyclic.cyclicGenerator q)⁻¹ h)
    (hhalf : ∀ i, 2 * fibreWeight h i ≤ q)
    (threshold expansionRadius expansionNumerator expansionDenominator : Nat)
    (hthreshold : 0 < threshold)
    (hPrimitive : threshold ≤ HammingWeight h)
    (hRadius : threshold ≤ expansionRadius)
    (hExpansion : (tannerAction A).SmallSetExpanding
      expansionRadius expansionNumerator expansionDenominator) :
    expansionNumerator *
        (threshold - HammingWeight (horizontalPart z)) ≤
      2 * expansionDenominator * HammingWeight (verticalPart z) := by
  obtain ⟨t, _htq, htbelow, _htabove, htnear⟩ :=
    exists_caseTwo_invCyclicDifference_before_crossing
      q h hhalf threshold hthreshold hPrimitive
  let x := (Cyclic.cyclicGenerator q)⁻¹
  let difference := h + cyclicShift (x ^ t) h
  have htnear' : threshold ≤
      HammingWeight difference + HammingWeight (horizontalPart z) := by
    dsimp [difference, x]
    rw [hu]
    exact htnear
  have hsub : threshold - HammingWeight (horizontalPart z) ≤
      HammingWeight difference := by omega
  have hDifferenceRadius : HammingWeight difference ≤ expansionRadius :=
    (Nat.le_of_lt htbelow).trans hRadius
  have hExpand : expansionNumerator * HammingWeight difference ≤
      expansionDenominator * HammingWeight (tannerAction A difference) :=
    hExpansion.2 difference hDifferenceRadius
  have hOutput : HammingWeight (tannerAction A difference) ≤
      2 * HammingWeight (verticalPart z) := by
    exact HammingWeight_tannerAction_cyclicDifference_le_two_vertical
      A x z hz h hu t
  calc
    expansionNumerator *
        (threshold - HammingWeight (horizontalPart z)) ≤
      expansionNumerator * HammingWeight difference :=
        Nat.mul_le_mul_left expansionNumerator hsub
    _ ≤ expansionDenominator * HammingWeight (tannerAction A difference) :=
      hExpand
    _ ≤ expansionDenominator * (2 * HammingWeight (verticalPart z)) :=
      Nat.mul_le_mul_left expansionDenominator hOutput
    _ = 2 * expansionDenominator * HammingWeight (verticalPart z) := by
      simp only [Nat.mul_assoc, Nat.mul_comm]

/-- For every prefix `u^(t)` of the horizontal part of a concrete cycle,
the Tanner syndrome is the cyclic endpoint difference `(1+x^t)v` from PK20
Proposition 2, Case 1. -/
theorem tannerAction_cyclicPrefix_horizontalPart_eq
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (hz : LiftedProduct.boundary1
      (Cyclic.liftedProductData A x) z = 0)
    (t : Nat) :
    tannerAction A (cyclicPrefix x t (horizontalPart z)) =
      verticalPart z + cyclicShift (x ^ t) (verticalPart z) := by
  rw [tannerAction_cyclicPrefix,
    tannerAction_horizontalPart_eq_cyclicDifference_verticalPart A x z hz,
    cyclicPrefix_cyclicDifference]

/-- Quantitative core of PK20 Proposition 2, Case 1.  Once a cyclic prefix of
the concrete horizontal block crosses `threshold`, small-set expansion forces
the concrete vertical block to be large.  The endpoint-crossing premise is
later discharged from the nonzero quotient Tanner class and its distance. -/
theorem verticalPart_lowerBound_of_cyclicPrefix_crossing
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (hz : LiftedProduct.boundary1
      (Cyclic.liftedProductData A x) z = 0)
    (last threshold stepBound expansionNumerator expansionDenominator : Nat)
    (hthreshold : 0 < threshold)
    (hend : threshold ≤
      HammingWeight (cyclicPrefix x last (horizontalPart z)))
    (hstepBound : HammingWeight (horizontalPart z) ≤ stepBound)
    (hExpansion : (tannerAction A).SmallSetExpanding
      threshold expansionNumerator expansionDenominator) :
    expansionNumerator * (threshold - stepBound) ≤
      2 * expansionDenominator * HammingWeight (verticalPart z) := by
  let sequence : Nat → Word (ZMod 2) (aCol × G) :=
    fun t => cyclicPrefix x t (horizontalPart z)
  have hstart : HammingWeight (sequence 0) < threshold := by
    simp [sequence, hthreshold]
  have hstep : ∀ t < last,
      HammingWeight (sequence (t + 1) + sequence t) ≤ stepBound := by
    intro t _ht
    rw [show sequence (t + 1) + sequence t =
      cyclicPrefix x (t + 1) (horizontalPart z) +
        cyclicPrefix x t (horizontalPart z) by rfl,
      HammingWeight_cyclicPrefix_step]
    exact hstepBound
  obtain ⟨t, _htlast, htbelow, _htabove, htnear⟩ :=
    exists_weight_before_first_crossing sequence last threshold stepBound
      hstart hend hstep
  have hsub : threshold - stepBound ≤ HammingWeight (sequence t) := by
    omega
  have hexpand :
      expansionNumerator * HammingWeight (sequence t) ≤
        expansionDenominator * HammingWeight (tannerAction A (sequence t)) :=
    hExpansion.2 (sequence t) (Nat.le_of_lt htbelow)
  have hsyndrome :
      tannerAction A (sequence t) =
        verticalPart z + cyclicShift (x ^ t) (verticalPart z) := by
    exact tannerAction_cyclicPrefix_horizontalPart_eq A x z hz t
  have houtput :
      HammingWeight (tannerAction A (sequence t)) ≤
        2 * HammingWeight (verticalPart z) := by
    rw [hsyndrome]
    exact HammingWeight_add_cyclicShift_le_two_mul (x ^ t) (verticalPart z)
  calc
    expansionNumerator * (threshold - stepBound) ≤
        expansionNumerator * HammingWeight (sequence t) :=
      Nat.mul_le_mul_left expansionNumerator hsub
    _ ≤ expansionDenominator * HammingWeight (tannerAction A (sequence t)) :=
      hexpand
    _ ≤ expansionDenominator * (2 * HammingWeight (verticalPart z)) :=
      Nat.mul_le_mul_left expansionDenominator houtput
    _ = 2 * expansionDenominator * HammingWeight (verticalPart z) := by
      simp only [Nat.mul_assoc, Nat.mul_comm]

/-! ## Full-orbit endpoint for the canonical cyclic group -/

/-- Sum one word over its entire cyclic fibre. -/
noncomputable def fibreSum
    {I : Type u} {G : Type v} [Fintype G]
    (z : Word (ZMod 2) (I × G)) : Word (ZMod 2) I :=
  fun i => ∑ g, z (i, g)

/-! ## Normalized primitives for the zero-augmentation case -/

/-- The explicit prefix primitive on every canonical cyclic fibre. -/
def cyclicFibrePrimitive
    {I : Type u} (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q)) :
    Word (ZMod 2) (I × Cyclic.CyclicGroup q) :=
  fun p =>
    FiberBundle.cycleFiberChainPrimitive q
      (fun a : ZMod q => z (p.1, Multiplicative.ofAdd a)) p.2.toAdd

/-- A word with zero sum on every canonical cyclic fibre is the concrete
`1+x` cyclic difference of its explicit prefix primitive. -/
theorem cyclicFibrePrimitive_add_shift_eq
    {I : Type u} (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hzero : fibreSum z = 0) :
    cyclicFibrePrimitive q z +
        cyclicShift (Cyclic.cyclicGenerator q) (cyclicFibrePrimitive q z) =
      z := by
  funext p
  rcases p with ⟨i, g⟩
  have hsum :
      (∑ a : ZMod q, z (i, Multiplicative.ofAdd a)) = 0 := by
    calc
      (∑ a : ZMod q, z (i, Multiplicative.ofAdd a)) =
          ∑ k : Fin q,
            z (i, Multiplicative.ofAdd (ZMod.finEquiv q k)) := by
        exact Fintype.sum_equiv (ZMod.finEquiv q).symm
          (fun a : ZMod q => z (i, Multiplicative.ofAdd a))
          (fun k : Fin q =>
            z (i, Multiplicative.ofAdd (ZMod.finEquiv q k)))
          (fun a => by simp)
      _ = ∑ h : Cyclic.CyclicGroup q, z (i, h) := by
        exact Fintype.sum_equiv (Cyclic.finCyclicEquiv q)
          (fun k : Fin q =>
            z (i, Multiplicative.ofAdd (ZMod.finEquiv q k)))
          (fun h : Cyclic.CyclicGroup q => z (i, h))
          (fun _ => rfl)
      _ = 0 := by
        have hi := congrFun hzero i
        simpa [fibreSum] using hi
  have hprimitive := congrFun
    (FiberBundle.cycleFiberChainBoundary_cycleFiberChainPrimitive
      q hq (fun a : ZMod q => z (i, Multiplicative.ofAdd a)) hsum)
    g.toAdd
  rw [FiberBundle.cycleFiberChainBoundary_apply q hq] at hprimitive
  simpa [cyclicFibrePrimitive, cyclicShift_apply,
    Cyclic.cyclicGenerator, sub_eq_add_neg] using hprimitive

/-- Normalize each binary cyclic fibre modulo its all-one word. -/
def normalizeCyclicFibres
    {I : Type u} {G : Type v} [Fintype G]
    (z : Word (ZMod 2) (I × G)) : Word (ZMod 2) (I × G) :=
  fun p => FiberBundle.normalizeBinaryWord (fun g : G => z (p.1, g)) p.2

/-- Every normalized cyclic fibre occupies at most half its coordinates. -/
theorem normalizeCyclicFibres_half
    {I : Type u} {G : Type v} [Fintype G]
    (z : Word (ZMod 2) (I × G)) (i : I) :
    2 * HammingWeight (fun g : G => normalizeCyclicFibres z (i, g)) ≤
      Fintype.card G := by
  exact FiberBundle.twice_hammingWeight_normalizeBinaryWord_le_card
    (fun g : G => z (i, g))

/-- Fibrewise normalization changes a word only by constants and therefore
does not change its `1+x` cyclic difference. -/
theorem normalizeCyclicFibres_add_shift
    {I : Type u} {G : Type v} [Group G] [Fintype G]
    (x : G) (z : Word (ZMod 2) (I × G)) :
    normalizeCyclicFibres z + cyclicShift x (normalizeCyclicFibres z) =
      z + cyclicShift x z := by
  funext p
  rcases p with ⟨i, g⟩
  rcases FiberBundle.normalizeBinaryWord_eq_self_or_complement
      (fun h : G => z (i, h)) with hself | hcomplement
  all_goals simp only [Pi.add_apply, cyclicShift_apply]
  · rw [show normalizeCyclicFibres z (i, g) = z (i, g) by
        exact congrFun hself g,
      show normalizeCyclicFibres z (i, g * x⁻¹) = z (i, g * x⁻¹) by
        exact congrFun hself (g * x⁻¹)]
  · rw [show normalizeCyclicFibres z (i, g) =
          FiberBundle.binaryComplement (fun h : G => z (i, h)) g by
        exact congrFun hcomplement g,
      show normalizeCyclicFibres z (i, g * x⁻¹) =
          FiberBundle.binaryComplement (fun h : G => z (i, h)) (g * x⁻¹) by
        exact congrFun hcomplement (g * x⁻¹)]
    simp only [FiberBundle.binaryComplement]
    have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    calc
      (1 + z (i, g)) + (1 + z (i, g * x⁻¹)) =
          (2 : ZMod 2) + (z (i, g) + z (i, g * x⁻¹)) := by ring
      _ = z (i, g) + z (i, g * x⁻¹) := by rw [htwo, zero_add]

/-- Zero fibre augmentation has a normalized `1+x` primitive with the exact
per-fibre half-weight condition used in PK20 Lemma `lm:autcorr`. -/
theorem exists_normalized_cyclicPrimitive
    {I : Type u} (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hzero : fibreSum z = 0) :
    ∃ h : Word (ZMod 2) (I × Cyclic.CyclicGroup q),
      z = h + cyclicShift (Cyclic.cyclicGenerator q) h ∧
      ∀ i, 2 * fibreWeight h i ≤ q := by
  refine ⟨normalizeCyclicFibres (cyclicFibrePrimitive q z), ?_, ?_⟩
  · rw [normalizeCyclicFibres_add_shift]
    exact (cyclicFibrePrimitive_add_shift_eq q hq z hzero).symm
  · intro i
    simpa [fibreWeight, Cyclic.CyclicGroup, ZMod.card] using
      normalizeCyclicFibres_half (cyclicFibrePrimitive q z) i

/-- The same normalized primitive in the opposite cyclic orientation. -/
theorem exists_normalized_invCyclicPrimitive
    {I : Type u} (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hzero : fibreSum z = 0) :
    ∃ h : Word (ZMod 2) (I × Cyclic.CyclicGroup q),
      z = h + cyclicShift ((Cyclic.cyclicGenerator q)⁻¹) h ∧
      ∀ i, 2 * fibreWeight h i ≤ q := by
  obtain ⟨h, hz, hhalf⟩ := exists_normalized_cyclicPrimitive q hq z hzero
  refine ⟨cyclicShift (Cyclic.cyclicGenerator q) h, ?_, ?_⟩
  · rw [cyclicShift_cyclicShift, mul_inv_cancel, cyclicShift_one, add_comm]
    exact hz
  · intro i
    rw [fibreWeight_cyclicShift]
    exact hhalf i

/-- A length-`q` prefix of the canonical generator traverses every element of
`CyclicGroup q` exactly once, so the result is constant on each fibre. -/
theorem cyclicPrefix_card_apply
    {I : Type u} (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (i : I) (g : Cyclic.CyclicGroup q) :
    cyclicPrefix (Cyclic.cyclicGenerator q) q z (i, g) = fibreSum z i := by
  classical
  rw [cyclicPrefix, fibreSum]
  simp only [Finset.sum_apply]
  rw [← Fin.sum_univ_eq_sum_range]
  let e : Fin q ≃ Cyclic.CyclicGroup q :=
    (Cyclic.finCyclicEquiv q).trans
      ((Equiv.inv (Cyclic.CyclicGroup q)).trans (Equiv.mulLeft g))
  exact Fintype.sum_equiv e
    (fun k : Fin q =>
      cyclicShift (Cyclic.cyclicGenerator q ^ k.val) z (i, g))
    (fun h : Cyclic.CyclicGroup q => z (i, h)) (fun k => by
      change z (i, g * (Cyclic.cyclicGenerator q ^ k.val)⁻¹) =
        z (i, g * (Cyclic.finCyclicEquiv q k)⁻¹)
      rw [Cyclic.finCyclicEquiv_apply_eq_generator_pow])

/-- The inverse generator also traverses every cyclic coordinate exactly
once, with the same full-prefix endpoint. -/
theorem invCyclicPrefix_card_apply
    {I : Type u} (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (i : I) (g : Cyclic.CyclicGroup q) :
    cyclicPrefix ((Cyclic.cyclicGenerator q)⁻¹) q z (i, g) = fibreSum z i := by
  classical
  rw [cyclicPrefix, fibreSum]
  simp only [Finset.sum_apply]
  rw [← Fin.sum_univ_eq_sum_range]
  let e : Fin q ≃ Cyclic.CyclicGroup q :=
    (Cyclic.finCyclicInvEquiv q).trans
      ((Equiv.inv (Cyclic.CyclicGroup q)).trans (Equiv.mulLeft g))
  exact Fintype.sum_equiv e
    (fun k : Fin q =>
      cyclicShift ((Cyclic.cyclicGenerator q)⁻¹ ^ k.val) z (i, g))
    (fun h : Cyclic.CyclicGroup q => z (i, h)) (fun k => by
      change z (i, g * ((Cyclic.cyclicGenerator q)⁻¹ ^ k.val)⁻¹) =
        z (i, g * (Cyclic.finCyclicInvEquiv q k)⁻¹)
      rw [Cyclic.finCyclicInvEquiv_apply_eq_invGenerator_pow])

/-- The full canonical prefix has exactly `q` copies of every nonzero fibre
sum. -/
theorem HammingWeight_cyclicPrefix_card
    {I : Type u} [Fintype I] (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q)) :
    HammingWeight (cyclicPrefix (Cyclic.cyclicGenerator q) q z) =
      q * HammingWeight (fibreSum z) := by
  classical
  rw [HammingWeight_eq_sum_indicator, HammingWeight_eq_sum_indicator,
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp_rw [cyclicPrefix_card_apply]
  by_cases hi : fibreSum z i = 0
  · simp [hi]
  · simp [hi, Cyclic.CyclicGroup, ZMod.card]

/-- Exact full-prefix weight in the inverse cyclic orientation. -/
theorem HammingWeight_invCyclicPrefix_card
    {I : Type u} [Fintype I] (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q)) :
    HammingWeight (cyclicPrefix ((Cyclic.cyclicGenerator q)⁻¹) q z) =
      q * HammingWeight (fibreSum z) := by
  classical
  rw [HammingWeight_eq_sum_indicator, HammingWeight_eq_sum_indicator,
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp_rw [invCyclicPrefix_card_apply]
  by_cases hi : fibreSum z i = 0
  · simp [hi]
  · simp [hi, Cyclic.CyclicGroup, ZMod.card]

theorem fibreSum_horizontalPart_eq_horizontalAugmentation
    {G aRow aCol : Type} [Fintype G]
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G)) :
    fibreSum (horizontalPart z) =
      HorizontalSubsystem.horizontalAugmentation z := by
  ext c
  rfl

/-- The zero-horizontal-projection branch of a concrete lifted-product cycle
has the normalized cyclic primitive required by PK20 Case 2. -/
theorem exists_normalized_horizontalPrimitive_of_homologyProjection_eq_zero
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCycleCode.carrier)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)
      ((LiftedProduct.chainComplex
        (Cyclic.data q A)).middleBoundaryInCycles.mkQ ⟨z, hz⟩) = 0) :
    ∃ h : Word (ZMod 2) (aCol × Cyclic.CyclicGroup q),
      horizontalPart z =
        h + cyclicShift (Cyclic.cyclicGenerator q) h ∧
      ∀ c, 2 * fibreWeight h c ≤ q := by
  have hAugmentation : HorizontalSubsystem.horizontalAugmentation z = 0 :=
    HorizontalSubsystem.horizontalAugmentation_eq_zero_of_homologyProjection_eq_zero
      A (Cyclic.cyclicGenerator q) z hz hProjected
  apply exists_normalized_cyclicPrimitive q hq (horizontalPart z)
  rw [fibreSum_horizontalPart_eq_horizontalAugmentation]
  exact hAugmentation

/-- Zero-horizontal-projection primitive for the inverse generator appearing
in the star-transposed lifted product. -/
theorem exists_normalized_horizontalPrimitive_invGenerator_of_projection_eq_zero
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A
        (Cyclic.cyclicGenerator q)⁻¹)).middleCycleCode.carrier)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)⁻¹
      ((LiftedProduct.chainComplex
        (Cyclic.liftedProductData A
          (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryInCycles.mkQ
            ⟨z, hz⟩) = 0) :
    ∃ h : Word (ZMod 2) (aCol × Cyclic.CyclicGroup q),
      horizontalPart z =
        h + cyclicShift (Cyclic.cyclicGenerator q)⁻¹ h ∧
      ∀ c, 2 * fibreWeight h c ≤ q := by
  have hAugmentation : HorizontalSubsystem.horizontalAugmentation z = 0 :=
    HorizontalSubsystem.horizontalAugmentation_eq_zero_of_homologyProjection_eq_zero
      A (Cyclic.cyclicGenerator q)⁻¹ z hz hProjected
  apply exists_normalized_invCyclicPrimitive q hq (horizontalPart z)
  rw [fibreSum_horizontalPart_eq_horizontalAugmentation]
  exact hAugmentation

/-- Source-shaped completion of PK20 Proposition 2, Case 2 for an actual
non-boundary cycle whose horizontal quotient class vanishes.  The scale
condition `2*w*threshold <= q` is the exact integer form used to derive the
primitive crossing threshold from the full cyclic remainder. -/
theorem zero_horizontalClass_caseTwo_weight_bound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit
        (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCycleCode.carrier)
    (hzNotBoundary : z ∉ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleBoundaryCode.carrier)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)
      ((LiftedProduct.chainComplex
        (Cyclic.data q A)).middleBoundaryInCycles.mkQ ⟨z, hz⟩) = 0)
    (w threshold expansionRadius expansionNumerator expansionDenominator : Nat)
    (hw : 0 < w) (hthreshold : 0 < threshold)
    (hThresholdScale : 2 * w * threshold ≤ q)
    (hColumnWeight : ∀ i : aCol × Cyclic.CyclicGroup q,
      HammingWeight (tannerAction A (Pi.single i 1)) ≤ w)
    (hRadius : threshold ≤ expansionRadius)
    (hExpansion : (tannerAction A).SmallSetExpanding
      expansionRadius expansionNumerator expansionDenominator) :
    expansionNumerator * threshold ≤
      max (2 * expansionNumerator) (4 * expansionDenominator) *
        HammingWeight z := by
  have hzBoundary : LiftedProduct.boundary1 (Cyclic.data q A) z = 0 :=
    ((LiftedProduct.chainComplex
      (Cyclic.data q A)).mem_middleCycleCode_iff z).1 hz
  obtain ⟨h, hu, hhalf⟩ :=
    exists_normalized_horizontalPrimitive_of_homologyProjection_eq_zero
      q hq A z hz hProjected
  let horizontalWeight := HammingWeight (horizontalPart z)
  let verticalWeight := HammingWeight (verticalPart z)
  have hsplit : HammingWeight z = horizontalWeight + verticalWeight :=
    HammingWeight_eq_horizontalPart_add_verticalPart z
  have hhorizontal : horizontalWeight ≤ HammingWeight z := by omega
  have hvertical : verticalWeight ≤ HammingWeight z := by omega
  by_cases hHorizontalLarge : threshold ≤ 2 * horizontalWeight
  · calc
      expansionNumerator * threshold ≤
          expansionNumerator * (2 * horizontalWeight) :=
        Nat.mul_le_mul_left expansionNumerator hHorizontalLarge
      _ = (2 * expansionNumerator) * horizontalWeight := by ac_rfl
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          horizontalWeight :=
        Nat.mul_le_mul_right horizontalWeight (Nat.le_max_left _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := Nat.mul_le_mul_left _ hhorizontal
  · by_cases hVerticalHalf : 2 * verticalWeight ≤ q
    · have hPrimitiveScaled : q ≤ 2 * w * HammingWeight h := by
        exact caseTwo_cyclic_card_le_two_mul_locality_mul_primitive_weight
          q A z hzBoundary hzNotBoundary h hu w hColumnWeight
            (by simpa [verticalWeight] using hVerticalHalf)
      have hScaled : 2 * w * threshold ≤ 2 * w * HammingWeight h :=
        hThresholdScale.trans hPrimitiveScaled
      have hPrimitive : threshold ≤ HammingWeight h := by
        exact Nat.le_of_mul_le_mul_left
          hScaled (by omega)
      have hForced : expansionNumerator *
          (threshold - horizontalWeight) ≤
          2 * expansionDenominator * verticalWeight := by
        simpa only [horizontalWeight, verticalWeight] using
          verticalPart_lowerBound_of_caseTwo_primitive_crossing
            q A z hzBoundary h hu hhalf threshold expansionRadius
              expansionNumerator expansionDenominator hthreshold hPrimitive
                hRadius hExpansion
      have hTwice : threshold ≤ 2 * (threshold - horizontalWeight) := by
        omega
      calc
        expansionNumerator * threshold ≤
            expansionNumerator * (2 * (threshold - horizontalWeight)) :=
          Nat.mul_le_mul_left expansionNumerator hTwice
        _ = 2 * (expansionNumerator *
            (threshold - horizontalWeight)) := by ac_rfl
        _ ≤ 2 * (2 * expansionDenominator * verticalWeight) :=
          Nat.mul_le_mul_left 2 hForced
        _ = (4 * expansionDenominator) * verticalWeight := by ring
        _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
            verticalWeight :=
          Nat.mul_le_mul_right verticalWeight (Nat.le_max_right _ _)
        _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
            HammingWeight z := Nat.mul_le_mul_left _ hvertical
    · have hThresholdLeQ : threshold ≤ q := by
        calc
          threshold = 1 * threshold := by rw [one_mul]
          _ ≤ (2 * w) * threshold :=
            Nat.mul_le_mul_right threshold (by omega)
          _ = 2 * w * threshold := by ac_rfl
          _ ≤ q := hThresholdScale
      have hThresholdVertical : threshold ≤ 2 * verticalWeight := by omega
      calc
        expansionNumerator * threshold ≤
            expansionNumerator * (2 * verticalWeight) :=
          Nat.mul_le_mul_left expansionNumerator hThresholdVertical
        _ = (2 * expansionNumerator) * verticalWeight := by ac_rfl
        _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
            verticalWeight :=
          Nat.mul_le_mul_right verticalWeight (Nat.le_max_left _ _)
        _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
            HammingWeight z := Nat.mul_le_mul_left _ hvertical

/-- Complete Case-2 bound for the inverse cyclic orientation of the dual
lifted product. -/
theorem zero_horizontalClass_caseTwo_invGenerator_weight_bound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit
        (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A
        (Cyclic.cyclicGenerator q)⁻¹)).middleCycleCode.carrier)
    (hzNotBoundary : z ∉ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A
        (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryCode.carrier)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)⁻¹
      ((LiftedProduct.chainComplex
        (Cyclic.liftedProductData A
          (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryInCycles.mkQ
            ⟨z, hz⟩) = 0)
    (w threshold expansionRadius expansionNumerator expansionDenominator : Nat)
    (hw : 0 < w) (hthreshold : 0 < threshold)
    (hThresholdScale : 2 * w * threshold ≤ q)
    (hColumnWeight : ∀ i : aCol × Cyclic.CyclicGroup q,
      HammingWeight (tannerAction A (Pi.single i 1)) ≤ w)
    (hRadius : threshold ≤ expansionRadius)
    (hExpansion : (tannerAction A).SmallSetExpanding
      expansionRadius expansionNumerator expansionDenominator) :
    expansionNumerator * threshold ≤
      max (2 * expansionNumerator) (4 * expansionDenominator) *
        HammingWeight z := by
  let x := (Cyclic.cyclicGenerator q)⁻¹
  have hzBoundary : LiftedProduct.boundary1
      (Cyclic.liftedProductData A x) z = 0 :=
    ((LiftedProduct.chainComplex
      (Cyclic.liftedProductData A x)).mem_middleCycleCode_iff z).1 hz
  obtain ⟨h, hu, hhalf⟩ :=
    exists_normalized_horizontalPrimitive_invGenerator_of_projection_eq_zero
      q hq A z hz hProjected
  let horizontalWeight := HammingWeight (horizontalPart z)
  let verticalWeight := HammingWeight (verticalPart z)
  have hsplit : HammingWeight z = horizontalWeight + verticalWeight :=
    HammingWeight_eq_horizontalPart_add_verticalPart z
  have hhorizontal : horizontalWeight ≤ HammingWeight z := by omega
  have hvertical : verticalWeight ≤ HammingWeight z := by omega
  by_cases hHorizontalLarge : threshold ≤ 2 * horizontalWeight
  · calc
      expansionNumerator * threshold ≤
          expansionNumerator * (2 * horizontalWeight) :=
        Nat.mul_le_mul_left expansionNumerator hHorizontalLarge
      _ = (2 * expansionNumerator) * horizontalWeight := by ac_rfl
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          horizontalWeight :=
        Nat.mul_le_mul_right horizontalWeight (Nat.le_max_left _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := Nat.mul_le_mul_left _ hhorizontal
  · by_cases hVerticalHalf : 2 * verticalWeight ≤ q
    · have hRemainder : q ≤ HammingWeight (caseTwoRemainder A z h) := by
        exact cyclic_card_le_HammingWeight_caseTwoRemainder_invGenerator
          q A z hzBoundary hzNotBoundary h hu
      have hTriangle : HammingWeight (caseTwoRemainder A z h) ≤
          HammingWeight (verticalPart z) + HammingWeight (tannerAction A h) :=
        HammingWeight_add_le (verticalPart z) (tannerAction A h)
      have hTanner : HammingWeight (tannerAction A h) ≤
          w * HammingWeight h :=
        HammingWeight_linearMap_le_of_basis
          (tannerAction A) w hColumnWeight h
      have hLower : q ≤ verticalWeight + w * HammingWeight h := by
        have := hRemainder.trans
          (hTriangle.trans (Nat.add_le_add_left hTanner _))
        simpa only [verticalWeight] using this
      have hPrimitiveScaled' : q ≤ 2 * (w * HammingWeight h) := by omega
      have hPrimitiveScaled : q ≤ 2 * w * HammingWeight h := by
        simpa only [Nat.mul_assoc] using hPrimitiveScaled'
      have hScaled : 2 * w * threshold ≤ 2 * w * HammingWeight h :=
        hThresholdScale.trans hPrimitiveScaled
      have hPrimitive : threshold ≤ HammingWeight h :=
        Nat.le_of_mul_le_mul_left hScaled (by omega)
      have hForced : expansionNumerator *
          (threshold - horizontalWeight) ≤
          2 * expansionDenominator * verticalWeight := by
        simpa only [horizontalWeight, verticalWeight] using
          verticalPart_lowerBound_of_caseTwo_invPrimitive_crossing
            q A z hzBoundary h hu hhalf threshold expansionRadius
              expansionNumerator expansionDenominator hthreshold hPrimitive
                hRadius hExpansion
      have hTwice : threshold ≤ 2 * (threshold - horizontalWeight) := by omega
      calc
        expansionNumerator * threshold ≤
            expansionNumerator * (2 * (threshold - horizontalWeight)) :=
          Nat.mul_le_mul_left expansionNumerator hTwice
        _ = 2 * (expansionNumerator *
            (threshold - horizontalWeight)) := by ac_rfl
        _ ≤ 2 * (2 * expansionDenominator * verticalWeight) :=
          Nat.mul_le_mul_left 2 hForced
        _ = (4 * expansionDenominator) * verticalWeight := by ring
        _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
            verticalWeight :=
          Nat.mul_le_mul_right verticalWeight (Nat.le_max_right _ _)
        _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
            HammingWeight z := Nat.mul_le_mul_left _ hvertical
    · have hThresholdLeQ : threshold ≤ q := by
        calc
          threshold = 1 * threshold := by rw [one_mul]
          _ ≤ (2 * w) * threshold :=
            Nat.mul_le_mul_right threshold (by omega)
          _ = 2 * w * threshold := by ac_rfl
          _ ≤ q := hThresholdScale
      have hThresholdVertical : threshold ≤ 2 * verticalWeight := by omega
      calc
        expansionNumerator * threshold ≤
            expansionNumerator * (2 * verticalWeight) :=
          Nat.mul_le_mul_left expansionNumerator hThresholdVertical
        _ = (2 * expansionNumerator) * verticalWeight := by ac_rfl
        _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
            verticalWeight :=
          Nat.mul_le_mul_right verticalWeight (Nat.le_max_left _ _)
        _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
            HammingWeight z := Nat.mul_le_mul_left _ hvertical

/-- Canonical-cycle form of the Case-1 expansion bound.  The full-prefix
endpoint has been eliminated in favor of the actual horizontal augmentation
of the lifted-product cycle. -/
theorem verticalPart_lowerBound_of_horizontalAugmentation
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : LiftedProduct.boundary1
      (Cyclic.data q A) z = 0)
    (threshold stepBound expansionNumerator expansionDenominator : Nat)
    (hthreshold : 0 < threshold)
    (haugmentation : threshold ≤ q * HammingWeight
      (HorizontalSubsystem.horizontalAugmentation z))
    (hstepBound : HammingWeight (horizontalPart z) ≤ stepBound)
    (hExpansion : (tannerAction A).SmallSetExpanding
      threshold expansionNumerator expansionDenominator) :
    expansionNumerator * (threshold - stepBound) ≤
      2 * expansionDenominator * HammingWeight (verticalPart z) := by
  apply verticalPart_lowerBound_of_cyclicPrefix_crossing
    A (Cyclic.cyclicGenerator q) z hz q threshold stepBound
      expansionNumerator expansionDenominator hthreshold
  · rw [HammingWeight_cyclicPrefix_card,
      fibreSum_horizontalPart_eq_horizontalAugmentation]
    exact haugmentation
  · exact hstepBound
  · exact hExpansion

/-- Canonical-cycle Case-1 expansion bound in the inverse orientation. -/
theorem verticalPart_lowerBound_of_horizontalAugmentation_invGenerator
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : LiftedProduct.boundary1
      (Cyclic.liftedProductData A (Cyclic.cyclicGenerator q)⁻¹) z = 0)
    (threshold stepBound expansionNumerator expansionDenominator : Nat)
    (hthreshold : 0 < threshold)
    (haugmentation : threshold ≤ q * HammingWeight
      (HorizontalSubsystem.horizontalAugmentation z))
    (hstepBound : HammingWeight (horizontalPart z) ≤ stepBound)
    (hExpansion : (tannerAction A).SmallSetExpanding
      threshold expansionNumerator expansionDenominator) :
    expansionNumerator * (threshold - stepBound) ≤
      2 * expansionDenominator * HammingWeight (verticalPart z) := by
  apply verticalPart_lowerBound_of_cyclicPrefix_crossing
    A (Cyclic.cyclicGenerator q)⁻¹ z hz q threshold stepBound
      expansionNumerator expansionDenominator hthreshold
  · rw [HammingWeight_invCyclicPrefix_card,
      fibreSum_horizontalPart_eq_horizontalAugmentation]
    exact haugmentation
  · exact hstepBound
  · exact hExpansion

/-- PK20 Proposition 2, Case 1 with the full-prefix endpoint discharged from
the selected horizontal logical class.  In particular, the lower bound on
the augmentation is not an extra hypothesis: it follows from the actual
quotient Tanner minimum distance. -/
theorem verticalPart_lowerBound_of_nonzero_horizontalClass
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCycleCode.carrier)
    {d : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode d)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)
      ((LiftedProduct.chainComplex
        (Cyclic.data q A)).middleBoundaryInCycles.mkQ ⟨z, hz⟩) ≠ 0)
    (stepBound expansionNumerator expansionDenominator : Nat)
    (hd : 0 < d)
    (hstepBound : HammingWeight (horizontalPart z) ≤ stepBound)
    (hExpansion : (tannerAction A).SmallSetExpanding
      (q * d) expansionNumerator expansionDenominator) :
    expansionNumerator * (q * d - stepBound) ≤
      2 * expansionDenominator * HammingWeight (verticalPart z) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hzBoundary : LiftedProduct.boundary1 (Cyclic.data q A) z = 0 :=
    ((LiftedProduct.chainComplex
      (Cyclic.data q A)).mem_middleCycleCode_iff z).1 hz
  have hAugmentation : d ≤ HammingWeight
      (HorizontalSubsystem.horizontalAugmentation z) :=
    HorizontalSubsystem.quotientMinimumDistance_le_horizontalAugmentation
      A (Cyclic.cyclicGenerator q) z hz hMinimum hProjected
  apply verticalPart_lowerBound_of_horizontalAugmentation
    q A z hzBoundary (q * d) stepBound expansionNumerator
      expansionDenominator
  · exact Nat.mul_pos hq hd
  · exact Nat.mul_le_mul_left q hAugmentation
  · exact hstepBound
  · exact hExpansion

/-- PK20 Case 1 with its endpoint discharged in the inverse cyclic
orientation. -/
theorem verticalPart_lowerBound_of_nonzero_horizontalClass_invGenerator
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A
        (Cyclic.cyclicGenerator q)⁻¹)).middleCycleCode.carrier)
    {d : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode d)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)⁻¹
      ((LiftedProduct.chainComplex
        (Cyclic.liftedProductData A
          (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryInCycles.mkQ
            ⟨z, hz⟩) ≠ 0)
    (stepBound expansionNumerator expansionDenominator : Nat)
    (hd : 0 < d)
    (hstepBound : HammingWeight (horizontalPart z) ≤ stepBound)
    (hExpansion : (tannerAction A).SmallSetExpanding
      (q * d) expansionNumerator expansionDenominator) :
    expansionNumerator * (q * d - stepBound) ≤
      2 * expansionDenominator * HammingWeight (verticalPart z) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hzBoundary : LiftedProduct.boundary1
      (Cyclic.liftedProductData A (Cyclic.cyclicGenerator q)⁻¹) z = 0 :=
    ((LiftedProduct.chainComplex
      (Cyclic.liftedProductData A
        (Cyclic.cyclicGenerator q)⁻¹)).mem_middleCycleCode_iff z).1 hz
  have hAugmentation : d ≤ HammingWeight
      (HorizontalSubsystem.horizontalAugmentation z) :=
    HorizontalSubsystem.quotientMinimumDistance_le_horizontalAugmentation
      A (Cyclic.cyclicGenerator q)⁻¹ z hz hMinimum hProjected
  apply verticalPart_lowerBound_of_horizontalAugmentation_invGenerator
    q A z hzBoundary (q * d) stepBound expansionNumerator
      expansionDenominator
  · exact Nat.mul_pos hq hd
  · exact Nat.mul_le_mul_left q hAugmentation
  · exact hstepBound
  · exact hExpansion

/-- Source-shaped completion of PK20 Proposition 2, Case 1.  The maximum on
the right is the denominator form of
`min (1 / 2) (expansionNumerator / (4 * expansionDenominator))`.
The two branches are exactly: the horizontal block is already large, or the
prefix-expansion argument forces the vertical block to be large. -/
theorem nonzero_horizontalClass_caseOne_weight_bound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCycleCode.carrier)
    {d : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode d)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)
      ((LiftedProduct.chainComplex
        (Cyclic.data q A)).middleBoundaryInCycles.mkQ ⟨z, hz⟩) ≠ 0)
    (expansionNumerator expansionDenominator : Nat)
    (hd : 0 < d)
    (hExpansion : (tannerAction A).SmallSetExpanding
      (q * d) expansionNumerator expansionDenominator) :
    expansionNumerator * (q * d) ≤
      max (2 * expansionNumerator) (4 * expansionDenominator) *
        HammingWeight z := by
  let horizontalWeight := HammingWeight (horizontalPart z)
  let verticalWeight := HammingWeight (verticalPart z)
  have hsplit : HammingWeight z = horizontalWeight + verticalWeight := by
    exact HammingWeight_eq_horizontalPart_add_verticalPart z
  have hhorizontal : horizontalWeight ≤ HammingWeight z := by omega
  have hvertical : verticalWeight ≤ HammingWeight z := by omega
  by_cases hlarge : q * d ≤ 2 * horizontalWeight
  · calc
      expansionNumerator * (q * d) ≤
          expansionNumerator * (2 * horizontalWeight) :=
        Nat.mul_le_mul_left expansionNumerator hlarge
      _ = (2 * expansionNumerator) * horizontalWeight := by
        ac_rfl
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          horizontalWeight :=
        Nat.mul_le_mul_right horizontalWeight (Nat.le_max_left _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z :=
        Nat.mul_le_mul_left _ hhorizontal
  · have htwice : q * d ≤ 2 * (q * d - horizontalWeight) := by
      omega
    have hforced : expansionNumerator * (q * d - horizontalWeight) ≤
        2 * expansionDenominator * verticalWeight := by
      exact verticalPart_lowerBound_of_nonzero_horizontalClass
        q A z hz hMinimum hProjected horizontalWeight expansionNumerator
          expansionDenominator hd (by rfl) hExpansion
    calc
      expansionNumerator * (q * d) ≤
          expansionNumerator * (2 * (q * d - horizontalWeight)) :=
        Nat.mul_le_mul_left expansionNumerator htwice
      _ = 2 * (expansionNumerator * (q * d - horizontalWeight)) := by
        ac_rfl
      _ ≤ 2 * (2 * expansionDenominator * verticalWeight) :=
        Nat.mul_le_mul_left 2 hforced
      _ = (4 * expansionDenominator) * verticalWeight := by
        ring
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          verticalWeight :=
        Nat.mul_le_mul_right verticalWeight (Nat.le_max_right _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z :=
        Nat.mul_le_mul_left _ hvertical

/-- Source-shaped Case-1 completion in the inverse cyclic orientation. -/
theorem nonzero_horizontalClass_caseOne_invGenerator_weight_bound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A
        (Cyclic.cyclicGenerator q)⁻¹)).middleCycleCode.carrier)
    {d : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode d)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)⁻¹
      ((LiftedProduct.chainComplex
        (Cyclic.liftedProductData A
          (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryInCycles.mkQ
            ⟨z, hz⟩) ≠ 0)
    (expansionNumerator expansionDenominator : Nat)
    (hd : 0 < d)
    (hExpansion : (tannerAction A).SmallSetExpanding
      (q * d) expansionNumerator expansionDenominator) :
    expansionNumerator * (q * d) ≤
      max (2 * expansionNumerator) (4 * expansionDenominator) *
        HammingWeight z := by
  let horizontalWeight := HammingWeight (horizontalPart z)
  let verticalWeight := HammingWeight (verticalPart z)
  have hsplit : HammingWeight z = horizontalWeight + verticalWeight :=
    HammingWeight_eq_horizontalPart_add_verticalPart z
  have hhorizontal : horizontalWeight ≤ HammingWeight z := by omega
  have hvertical : verticalWeight ≤ HammingWeight z := by omega
  by_cases hlarge : q * d ≤ 2 * horizontalWeight
  · calc
      expansionNumerator * (q * d) ≤
          expansionNumerator * (2 * horizontalWeight) :=
        Nat.mul_le_mul_left expansionNumerator hlarge
      _ = (2 * expansionNumerator) * horizontalWeight := by ac_rfl
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          horizontalWeight :=
        Nat.mul_le_mul_right horizontalWeight (Nat.le_max_left _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := Nat.mul_le_mul_left _ hhorizontal
  · have htwice : q * d ≤ 2 * (q * d - horizontalWeight) := by omega
    have hforced : expansionNumerator * (q * d - horizontalWeight) ≤
        2 * expansionDenominator * verticalWeight := by
      exact verticalPart_lowerBound_of_nonzero_horizontalClass_invGenerator
        q A z hz hMinimum hProjected horizontalWeight expansionNumerator
          expansionDenominator hd (by rfl) hExpansion
    calc
      expansionNumerator * (q * d) ≤
          expansionNumerator * (2 * (q * d - horizontalWeight)) :=
        Nat.mul_le_mul_left expansionNumerator htwice
      _ = 2 * (expansionNumerator * (q * d - horizontalWeight)) := by ac_rfl
      _ ≤ 2 * (2 * expansionDenominator * verticalWeight) :=
        Nat.mul_le_mul_left 2 hforced
      _ = (4 * expansionDenominator) * verticalWeight := by ring
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          verticalWeight :=
        Nat.mul_le_mul_right verticalWeight (Nat.le_max_right _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := Nat.mul_le_mul_left _ hvertical

/-- The completed Case-1 estimate, packaged as the actual dressed `Z`
distance predicate of the horizontal subsystem.  The arithmetic premise only
chooses an integral lower bound below the exact rational minimum; it contains
no code-distance conclusion. -/
theorem horizontalSubsystem_dressedZDistanceAtLeast_of_caseOne
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hOdd : Odd q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    {quotientDistance lowerBound : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode
        quotientDistance)
    (hDistancePositive : 0 < quotientDistance)
    (expansionNumerator expansionDenominator : Nat)
    (hExpansion : (tannerAction A).SmallSetExpanding
      (q * quotientDistance) expansionNumerator expansionDenominator)
    (hLowerBound :
      max (2 * expansionNumerator) (4 * expansionDenominator) * lowerBound ≤
        expansionNumerator * (q * quotientDistance)) :
    (HorizontalSubsystem.horizontalSubsystem A (Cyclic.cyclicGenerator q)
      (by simpa [Cyclic.CyclicGroup, ZMod.card] using hOdd)).DressedZDistanceAtLeast
        lowerBound := by
  intro z hz hProjected
  have hCase := nonzero_horizontalClass_caseOne_weight_bound
    q A z hz hMinimum hProjected expansionNumerator expansionDenominator
      hDistancePositive hExpansion
  have hScaled :
      max (2 * expansionNumerator) (4 * expansionDenominator) * lowerBound ≤
        max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z :=
    hLowerBound.trans hCase
  have hCoefficientPositive :
      0 < max (2 * expansionNumerator) (4 * expansionDenominator) := by
    have hDenominatorPositive := hExpansion.1
    exact lt_of_lt_of_le (by omega) (Nat.le_max_right _ _)
  exact Nat.le_of_mul_le_mul_left hScaled hCoefficientPositive

/-! ## Dual-cycle entry point for dressed X distance -/

/-- A cocycle whose selected horizontal cohomology class is nonzero becomes a
non-boundary cycle in the star-transposed lifted product.  This is the precise
logical-sector bridge needed before applying the two PK homology cases to the
dual complex. -/
theorem dualCycle_not_boundary_of_horizontalCohomologyProjection_ne_zero
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCocycleCode.carrier)
    (hProjected : HorizontalSubsystem.horizontalCohomologyProjection A
      (Cyclic.cyclicGenerator q)
      ((LiftedProduct.chainComplex
        (Cyclic.data q A)).middleCoboundaryInCocycles.mkQ ⟨z, hz⟩) ≠ 0) :
    LiftedProductDuality.swapWord z ∉
      (LiftedProduct.chainComplex
        (LiftedProductDuality.dualData
          (Cyclic.data q A))).middleBoundaryCode.carrier := by
  intro hBoundary
  have hCoboundary : z ∈
      (LiftedProduct.chainComplex
        (Cyclic.data q A)).firstCoboundaryCheckCode.carrier :=
    LiftedProductDuality.mem_firstCoboundaryCheckCode_of_swapWord_mem_middleBoundaryCode
      (Cyclic.data q A) z hBoundary
  apply hProjected
  have hClassZero :
      (LiftedProduct.chainComplex
        (Cyclic.data q A)).middleCoboundaryInCocycles.mkQ ⟨z, hz⟩ = 0 := by
    apply (Submodule.Quotient.mk_eq_zero
      (LiftedProduct.chainComplex
        (Cyclic.data q A)).middleCoboundaryInCocycles).2
    exact hCoboundary
  rw [hClassZero]
  exact (HorizontalSubsystem.horizontalCohomologyProjection A
    (Cyclic.cyclicGenerator q)).map_zero

/-- The exchanged cocycle is a cycle in the explicit inverse-generator
normal form of the dual lifted product. -/
theorem dualCycle_mem_invGenerator_middleCycleCode
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCocycleCode.carrier) :
    LiftedProductDuality.swapWord z ∈
      (LiftedProduct.chainComplex
        (Cyclic.liftedProductData (LiftedProduct.starTranspose A)
          (Cyclic.cyclicGenerator q)⁻¹)).middleCycleCode.carrier := by
  have hDual :=
    LiftedProductDuality.swapWord_mem_middleCycleCode_of_mem_middleCocycleCode
      (Cyclic.data q A) z hz
  change LiftedProductDuality.swapWord z ∈
    (LiftedProduct.chainComplex
      (LiftedProductDuality.dualData
        (Cyclic.liftedProductData A
          (Cyclic.cyclicGenerator q)))).middleCycleCode.carrier at hDual
  rw [LiftedProductDuality.dualData_cyclicLiftedProductData] at hDual
  exact hDual

/-- Nontrivial selected cohomology gives a non-boundary dual cycle in the same
explicit inverse-generator normal form. -/
theorem dualCycle_not_invGenerator_boundary_of_horizontalCohomologyProjection_ne_zero
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCocycleCode.carrier)
    (hProjected : HorizontalSubsystem.horizontalCohomologyProjection A
      (Cyclic.cyclicGenerator q)
      ((LiftedProduct.chainComplex
        (Cyclic.data q A)).middleCoboundaryInCocycles.mkQ ⟨z, hz⟩) ≠ 0) :
    LiftedProductDuality.swapWord z ∉
      (LiftedProduct.chainComplex
        (Cyclic.liftedProductData (LiftedProduct.starTranspose A)
          (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryCode.carrier := by
  have hDual := dualCycle_not_boundary_of_horizontalCohomologyProjection_ne_zero
    q A z hz hProjected
  change LiftedProductDuality.swapWord z ∉
    (LiftedProduct.chainComplex
      (LiftedProductDuality.dualData
        (Cyclic.liftedProductData A
          (Cyclic.cyclicGenerator q)))).middleBoundaryCode.carrier at hDual
  rw [LiftedProductDuality.dualData_cyclicLiftedProductData] at hDual
  exact hDual

/-- Both PK cohomology cases, combined on the actual star-transposed dual
cycle.  The minimum is exactly the common lower scale valid in both the
nonzero and zero dual-horizontal-projection branches. -/
theorem nonzero_horizontalCohomologyClass_cases_weight_bound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCocycleCode.carrier)
    (hProjected : HorizontalSubsystem.horizontalCohomologyProjection A
      (Cyclic.cyclicGenerator q)
      ((LiftedProduct.chainComplex
        (Cyclic.data q A)).middleCoboundaryInCocycles.mkQ ⟨z, hz⟩) ≠ 0)
    {dualQuotientDistance : Nat}
    (hDualMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex
        (LiftedProduct.starTranspose A)).middleCycleCode dualQuotientDistance)
    (hDualDistancePositive : 0 < dualQuotientDistance)
    (w threshold expansionRadius expansionNumerator expansionDenominator : Nat)
    (hw : 0 < w) (hthreshold : 0 < threshold)
    (hThresholdScale : 2 * w * threshold ≤ q)
    (hColumnWeight : ∀ i : aRow × Cyclic.CyclicGroup q,
      HammingWeight
        (tannerAction (LiftedProduct.starTranspose A) (Pi.single i 1)) ≤ w)
    (hRadius : threshold ≤ expansionRadius)
    (hCaseOneExpansion :
      (tannerAction (LiftedProduct.starTranspose A)).SmallSetExpanding
        (q * dualQuotientDistance) expansionNumerator expansionDenominator)
    (hCaseTwoExpansion :
      (tannerAction (LiftedProduct.starTranspose A)).SmallSetExpanding
        expansionRadius expansionNumerator expansionDenominator) :
    expansionNumerator * min (q * dualQuotientDistance) threshold ≤
      max (2 * expansionNumerator) (4 * expansionDenominator) *
        HammingWeight z := by
  let Adual := LiftedProduct.starTranspose A
  let dualZ := LiftedProductDuality.swapWord z
  have hDualWeight : HammingWeight dualZ = HammingWeight z := by
    exact LiftedProductDuality.HammingWeight_swapWord z
  have hzDual : dualZ ∈ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData Adual
        (Cyclic.cyclicGenerator q)⁻¹)).middleCycleCode.carrier :=
    dualCycle_mem_invGenerator_middleCycleCode q A z hz
  have hzDualNotBoundary : dualZ ∉ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData Adual
        (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryCode.carrier :=
    dualCycle_not_invGenerator_boundary_of_horizontalCohomologyProjection_ne_zero
      q A z hz hProjected
  let dualClass :=
    (LiftedProduct.chainComplex
      (Cyclic.liftedProductData Adual
        (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryInCycles.mkQ
          ⟨dualZ, hzDual⟩
  by_cases hDualProjected :
      HorizontalSubsystem.horizontalHomologyProjection Adual
        (Cyclic.cyclicGenerator q)⁻¹ dualClass ≠ 0
  · have hCaseOne := nonzero_horizontalClass_caseOne_invGenerator_weight_bound
      q Adual dualZ hzDual hDualMinimum hDualProjected
        expansionNumerator expansionDenominator hDualDistancePositive
          hCaseOneExpansion
    calc
      expansionNumerator * min (q * dualQuotientDistance) threshold ≤
          expansionNumerator * (q * dualQuotientDistance) :=
        Nat.mul_le_mul_left expansionNumerator (Nat.min_le_left _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight dualZ := hCaseOne
      _ = max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := by
        rw [hDualWeight]
  · have hDualProjectedZero :
        HorizontalSubsystem.horizontalHomologyProjection Adual
          (Cyclic.cyclicGenerator q)⁻¹ dualClass = 0 := by
      exact not_ne_iff.mp hDualProjected
    have hCaseTwo := zero_horizontalClass_caseTwo_invGenerator_weight_bound
      q hq Adual dualZ hzDual hzDualNotBoundary hDualProjectedZero
        w threshold expansionRadius expansionNumerator expansionDenominator
          hw hthreshold hThresholdScale hColumnWeight hRadius hCaseTwoExpansion
    calc
      expansionNumerator * min (q * dualQuotientDistance) threshold ≤
          expansionNumerator * threshold :=
        Nat.mul_le_mul_left expansionNumerator (Nat.min_le_right _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight dualZ := hCaseTwo
      _ = max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := by
        rw [hDualWeight]

/-- The completed two-case estimate packaged as the actual dressed `X`
distance predicate of the horizontal subsystem. -/
theorem horizontalSubsystem_dressedXDistanceAtLeast_of_dual_cases
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q) (hOdd : Odd q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    {dualQuotientDistance lowerBound : Nat}
    (hDualMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex
        (LiftedProduct.starTranspose A)).middleCycleCode dualQuotientDistance)
    (hDualDistancePositive : 0 < dualQuotientDistance)
    (w threshold expansionRadius expansionNumerator expansionDenominator : Nat)
    (hw : 0 < w) (hthreshold : 0 < threshold)
    (hThresholdScale : 2 * w * threshold ≤ q)
    (hColumnWeight : ∀ i : aRow × Cyclic.CyclicGroup q,
      HammingWeight
        (tannerAction (LiftedProduct.starTranspose A) (Pi.single i 1)) ≤ w)
    (hRadius : threshold ≤ expansionRadius)
    (hCaseOneExpansion :
      (tannerAction (LiftedProduct.starTranspose A)).SmallSetExpanding
        (q * dualQuotientDistance) expansionNumerator expansionDenominator)
    (hCaseTwoExpansion :
      (tannerAction (LiftedProduct.starTranspose A)).SmallSetExpanding
        expansionRadius expansionNumerator expansionDenominator)
    (hLowerBound :
      max (2 * expansionNumerator) (4 * expansionDenominator) * lowerBound ≤
        expansionNumerator * min (q * dualQuotientDistance) threshold) :
    (HorizontalSubsystem.horizontalSubsystem A (Cyclic.cyclicGenerator q)
      (by simpa [Cyclic.CyclicGroup, ZMod.card] using hOdd)).DressedXDistanceAtLeast
        lowerBound := by
  intro z hz hProjected
  have hCases := nonzero_horizontalCohomologyClass_cases_weight_bound
    q hq A z hz hProjected hDualMinimum hDualDistancePositive
      w threshold expansionRadius expansionNumerator expansionDenominator
        hw hthreshold hThresholdScale hColumnWeight hRadius
          hCaseOneExpansion hCaseTwoExpansion
  have hScaled :
      max (2 * expansionNumerator) (4 * expansionDenominator) * lowerBound ≤
        max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := hLowerBound.trans hCases
  have hCoefficientPositive :
      0 < max (2 * expansionNumerator) (4 * expansionDenominator) := by
    have hDenominatorPositive := hCaseTwoExpansion.1
    exact lt_of_lt_of_le (by omega) (Nat.le_max_right _ _)
  exact Nat.le_of_mul_le_mul_left hScaled hCoefficientPositive

/-! ## Distance-lower-bound interfaces

The source applications know a uniform lower bound on the quotient Tanner
distance, while the finite code has some (possibly larger) attained minimum
distance.  The following variants keep those two numbers distinct.  This
avoids incorrectly requiring small-set expansion all the way up to the
unknown attained minimum. -/

theorem verticalPart_lowerBound_of_nonzero_horizontalClass_distanceLowerBound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCycleCode.carrier)
    {actualDistance distanceLowerBound : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode
        actualDistance)
    (hDistanceLower : distanceLowerBound ≤ actualDistance)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)
      ((LiftedProduct.chainComplex
        (Cyclic.data q A)).middleBoundaryInCycles.mkQ ⟨z, hz⟩) ≠ 0)
    (stepBound expansionNumerator expansionDenominator : Nat)
    (hLowerPositive : 0 < distanceLowerBound)
    (hstepBound : HammingWeight (horizontalPart z) ≤ stepBound)
    (hExpansion : (tannerAction A).SmallSetExpanding
      (q * distanceLowerBound) expansionNumerator expansionDenominator) :
    expansionNumerator * (q * distanceLowerBound - stepBound) ≤
      2 * expansionDenominator * HammingWeight (verticalPart z) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hzBoundary : LiftedProduct.boundary1 (Cyclic.data q A) z = 0 :=
    ((LiftedProduct.chainComplex
      (Cyclic.data q A)).mem_middleCycleCode_iff z).1 hz
  have hAugmentation : distanceLowerBound ≤ HammingWeight
      (HorizontalSubsystem.horizontalAugmentation z) :=
    hDistanceLower.trans
      (HorizontalSubsystem.quotientMinimumDistance_le_horizontalAugmentation
        A (Cyclic.cyclicGenerator q) z hz hMinimum hProjected)
  apply verticalPart_lowerBound_of_horizontalAugmentation
    q A z hzBoundary (q * distanceLowerBound) stepBound expansionNumerator
      expansionDenominator
  · exact Nat.mul_pos hq hLowerPositive
  · exact Nat.mul_le_mul_left q hAugmentation
  · exact hstepBound
  · exact hExpansion

theorem verticalPart_lowerBound_of_nonzero_horizontalClass_invGenerator_distanceLowerBound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A
        (Cyclic.cyclicGenerator q)⁻¹)).middleCycleCode.carrier)
    {actualDistance distanceLowerBound : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode
        actualDistance)
    (hDistanceLower : distanceLowerBound ≤ actualDistance)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)⁻¹
      ((LiftedProduct.chainComplex
        (Cyclic.liftedProductData A
          (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryInCycles.mkQ
            ⟨z, hz⟩) ≠ 0)
    (stepBound expansionNumerator expansionDenominator : Nat)
    (hLowerPositive : 0 < distanceLowerBound)
    (hstepBound : HammingWeight (horizontalPart z) ≤ stepBound)
    (hExpansion : (tannerAction A).SmallSetExpanding
      (q * distanceLowerBound) expansionNumerator expansionDenominator) :
    expansionNumerator * (q * distanceLowerBound - stepBound) ≤
      2 * expansionDenominator * HammingWeight (verticalPart z) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hzBoundary : LiftedProduct.boundary1
      (Cyclic.liftedProductData A (Cyclic.cyclicGenerator q)⁻¹) z = 0 :=
    ((LiftedProduct.chainComplex
      (Cyclic.liftedProductData A
        (Cyclic.cyclicGenerator q)⁻¹)).mem_middleCycleCode_iff z).1 hz
  have hAugmentation : distanceLowerBound ≤ HammingWeight
      (HorizontalSubsystem.horizontalAugmentation z) :=
    hDistanceLower.trans
      (HorizontalSubsystem.quotientMinimumDistance_le_horizontalAugmentation
        A (Cyclic.cyclicGenerator q)⁻¹ z hz hMinimum hProjected)
  apply verticalPart_lowerBound_of_horizontalAugmentation_invGenerator
    q A z hzBoundary (q * distanceLowerBound) stepBound expansionNumerator
      expansionDenominator
  · exact Nat.mul_pos hq hLowerPositive
  · exact Nat.mul_le_mul_left q hAugmentation
  · exact hstepBound
  · exact hExpansion

theorem nonzero_horizontalClass_caseOne_weight_bound_distanceLowerBound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCycleCode.carrier)
    {actualDistance distanceLowerBound : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode
        actualDistance)
    (hDistanceLower : distanceLowerBound ≤ actualDistance)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)
      ((LiftedProduct.chainComplex
        (Cyclic.data q A)).middleBoundaryInCycles.mkQ ⟨z, hz⟩) ≠ 0)
    (expansionNumerator expansionDenominator : Nat)
    (hLowerPositive : 0 < distanceLowerBound)
    (hExpansion : (tannerAction A).SmallSetExpanding
      (q * distanceLowerBound) expansionNumerator expansionDenominator) :
    expansionNumerator * (q * distanceLowerBound) ≤
      max (2 * expansionNumerator) (4 * expansionDenominator) *
        HammingWeight z := by
  let horizontalWeight := HammingWeight (horizontalPart z)
  let verticalWeight := HammingWeight (verticalPart z)
  have hsplit : HammingWeight z = horizontalWeight + verticalWeight :=
    HammingWeight_eq_horizontalPart_add_verticalPart z
  have hhorizontal : horizontalWeight ≤ HammingWeight z := by omega
  have hvertical : verticalWeight ≤ HammingWeight z := by omega
  by_cases hlarge : q * distanceLowerBound ≤ 2 * horizontalWeight
  · calc
      expansionNumerator * (q * distanceLowerBound) ≤
          expansionNumerator * (2 * horizontalWeight) :=
        Nat.mul_le_mul_left expansionNumerator hlarge
      _ = (2 * expansionNumerator) * horizontalWeight := by ac_rfl
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          horizontalWeight :=
        Nat.mul_le_mul_right horizontalWeight (Nat.le_max_left _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := Nat.mul_le_mul_left _ hhorizontal
  · have htwice : q * distanceLowerBound ≤
        2 * (q * distanceLowerBound - horizontalWeight) := by omega
    have hforced : expansionNumerator *
        (q * distanceLowerBound - horizontalWeight) ≤
          2 * expansionDenominator * verticalWeight := by
      exact verticalPart_lowerBound_of_nonzero_horizontalClass_distanceLowerBound
        q A z hz hMinimum hDistanceLower hProjected horizontalWeight
          expansionNumerator expansionDenominator hLowerPositive (by rfl) hExpansion
    calc
      expansionNumerator * (q * distanceLowerBound) ≤
          expansionNumerator *
            (2 * (q * distanceLowerBound - horizontalWeight)) :=
        Nat.mul_le_mul_left expansionNumerator htwice
      _ = 2 * (expansionNumerator *
          (q * distanceLowerBound - horizontalWeight)) := by ac_rfl
      _ ≤ 2 * (2 * expansionDenominator * verticalWeight) :=
        Nat.mul_le_mul_left 2 hforced
      _ = (4 * expansionDenominator) * verticalWeight := by ring
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          verticalWeight :=
        Nat.mul_le_mul_right verticalWeight (Nat.le_max_right _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := Nat.mul_le_mul_left _ hvertical

theorem horizontalSubsystem_dressedZDistanceAtLeast_of_caseOne_distanceLowerBound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hOdd : Odd q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    {actualDistance distanceLowerBound dressedLowerBound : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode
        actualDistance)
    (hDistanceLower : distanceLowerBound ≤ actualDistance)
    (hDistanceLowerPositive : 0 < distanceLowerBound)
    (expansionNumerator expansionDenominator : Nat)
    (hExpansion : (tannerAction A).SmallSetExpanding
      (q * distanceLowerBound) expansionNumerator expansionDenominator)
    (hLowerBound :
      max (2 * expansionNumerator) (4 * expansionDenominator) *
          dressedLowerBound ≤
        expansionNumerator * (q * distanceLowerBound)) :
    (HorizontalSubsystem.horizontalSubsystem A (Cyclic.cyclicGenerator q)
      (by simpa [Cyclic.CyclicGroup, ZMod.card] using hOdd)).DressedZDistanceAtLeast
        dressedLowerBound := by
  intro z hz hProjected
  have hCase := nonzero_horizontalClass_caseOne_weight_bound_distanceLowerBound
    q A z hz hMinimum hDistanceLower hProjected expansionNumerator
      expansionDenominator hDistanceLowerPositive hExpansion
  have hScaled := hLowerBound.trans hCase
  have hCoefficientPositive :
      0 < max (2 * expansionNumerator) (4 * expansionDenominator) := by
    have hDenominatorPositive := hExpansion.1
    exact lt_of_lt_of_le (by omega) (Nat.le_max_right _ _)
  exact Nat.le_of_mul_le_mul_left hScaled hCoefficientPositive

/-- The inverse-generator Case-1 estimate with an explicit lower bound kept
distinct from the attained quotient minimum. -/
theorem nonzero_horizontalClass_caseOne_invGenerator_weight_bound_distanceLowerBound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A
        (Cyclic.cyclicGenerator q)⁻¹)).middleCycleCode.carrier)
    {actualDistance distanceLowerBound : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode
        actualDistance)
    (hDistanceLower : distanceLowerBound ≤ actualDistance)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)⁻¹
      ((LiftedProduct.chainComplex
        (Cyclic.liftedProductData A
          (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryInCycles.mkQ
            ⟨z, hz⟩) ≠ 0)
    (expansionNumerator expansionDenominator : Nat)
    (hLowerPositive : 0 < distanceLowerBound)
    (hExpansion : (tannerAction A).SmallSetExpanding
      (q * distanceLowerBound) expansionNumerator expansionDenominator) :
    expansionNumerator * (q * distanceLowerBound) ≤
      max (2 * expansionNumerator) (4 * expansionDenominator) *
        HammingWeight z := by
  let horizontalWeight := HammingWeight (horizontalPart z)
  let verticalWeight := HammingWeight (verticalPart z)
  have hsplit : HammingWeight z = horizontalWeight + verticalWeight :=
    HammingWeight_eq_horizontalPart_add_verticalPart z
  have hhorizontal : horizontalWeight ≤ HammingWeight z := by omega
  have hvertical : verticalWeight ≤ HammingWeight z := by omega
  by_cases hlarge : q * distanceLowerBound ≤ 2 * horizontalWeight
  · calc
      expansionNumerator * (q * distanceLowerBound) ≤
          expansionNumerator * (2 * horizontalWeight) :=
        Nat.mul_le_mul_left expansionNumerator hlarge
      _ = (2 * expansionNumerator) * horizontalWeight := by ac_rfl
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          horizontalWeight :=
        Nat.mul_le_mul_right horizontalWeight (Nat.le_max_left _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := Nat.mul_le_mul_left _ hhorizontal
  · have htwice : q * distanceLowerBound ≤
        2 * (q * distanceLowerBound - horizontalWeight) := by omega
    have hforced : expansionNumerator *
        (q * distanceLowerBound - horizontalWeight) ≤
          2 * expansionDenominator * verticalWeight := by
      exact verticalPart_lowerBound_of_nonzero_horizontalClass_invGenerator_distanceLowerBound
        q A z hz hMinimum hDistanceLower hProjected horizontalWeight
          expansionNumerator expansionDenominator hLowerPositive (by rfl) hExpansion
    calc
      expansionNumerator * (q * distanceLowerBound) ≤
          expansionNumerator *
            (2 * (q * distanceLowerBound - horizontalWeight)) :=
        Nat.mul_le_mul_left expansionNumerator htwice
      _ = 2 * (expansionNumerator *
          (q * distanceLowerBound - horizontalWeight)) := by ac_rfl
      _ ≤ 2 * (2 * expansionDenominator * verticalWeight) :=
        Nat.mul_le_mul_left 2 hforced
      _ = (4 * expansionDenominator) * verticalWeight := by ring
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          verticalWeight :=
        Nat.mul_le_mul_right verticalWeight (Nat.le_max_right _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := Nat.mul_le_mul_left _ hvertical

/-- Both PK cohomology cases with the available uniform lower bound separated
from the attained dual quotient distance. -/
theorem nonzero_horizontalCohomologyClass_cases_weight_bound_distanceLowerBound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCocycleCode.carrier)
    (hProjected : HorizontalSubsystem.horizontalCohomologyProjection A
      (Cyclic.cyclicGenerator q)
      ((LiftedProduct.chainComplex
        (Cyclic.data q A)).middleCoboundaryInCocycles.mkQ ⟨z, hz⟩) ≠ 0)
    {actualDualDistance dualDistanceLowerBound : Nat}
    (hDualMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex
        (LiftedProduct.starTranspose A)).middleCycleCode actualDualDistance)
    (hDualDistanceLower : dualDistanceLowerBound ≤ actualDualDistance)
    (hDualDistanceLowerPositive : 0 < dualDistanceLowerBound)
    (w threshold expansionRadius expansionNumerator expansionDenominator : Nat)
    (hw : 0 < w) (hthreshold : 0 < threshold)
    (hThresholdScale : 2 * w * threshold ≤ q)
    (hColumnWeight : ∀ i : aRow × Cyclic.CyclicGroup q,
      HammingWeight
        (tannerAction (LiftedProduct.starTranspose A) (Pi.single i 1)) ≤ w)
    (hRadius : threshold ≤ expansionRadius)
    (hCaseOneExpansion :
      (tannerAction (LiftedProduct.starTranspose A)).SmallSetExpanding
        (q * dualDistanceLowerBound) expansionNumerator expansionDenominator)
    (hCaseTwoExpansion :
      (tannerAction (LiftedProduct.starTranspose A)).SmallSetExpanding
        expansionRadius expansionNumerator expansionDenominator) :
    expansionNumerator * min (q * dualDistanceLowerBound) threshold ≤
      max (2 * expansionNumerator) (4 * expansionDenominator) *
        HammingWeight z := by
  let Adual := LiftedProduct.starTranspose A
  let dualZ := LiftedProductDuality.swapWord z
  have hDualWeight : HammingWeight dualZ = HammingWeight z :=
    LiftedProductDuality.HammingWeight_swapWord z
  have hzDual : dualZ ∈ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData Adual
        (Cyclic.cyclicGenerator q)⁻¹)).middleCycleCode.carrier :=
    dualCycle_mem_invGenerator_middleCycleCode q A z hz
  have hzDualNotBoundary : dualZ ∉ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData Adual
        (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryCode.carrier :=
    dualCycle_not_invGenerator_boundary_of_horizontalCohomologyProjection_ne_zero
      q A z hz hProjected
  let dualClass :=
    (LiftedProduct.chainComplex
      (Cyclic.liftedProductData Adual
        (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryInCycles.mkQ
          ⟨dualZ, hzDual⟩
  by_cases hDualProjected :
      HorizontalSubsystem.horizontalHomologyProjection Adual
        (Cyclic.cyclicGenerator q)⁻¹ dualClass ≠ 0
  · have hCaseOne :=
      nonzero_horizontalClass_caseOne_invGenerator_weight_bound_distanceLowerBound
        q Adual dualZ hzDual hDualMinimum hDualDistanceLower hDualProjected
          expansionNumerator expansionDenominator hDualDistanceLowerPositive
            hCaseOneExpansion
    calc
      expansionNumerator * min (q * dualDistanceLowerBound) threshold ≤
          expansionNumerator * (q * dualDistanceLowerBound) :=
        Nat.mul_le_mul_left expansionNumerator (Nat.min_le_left _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight dualZ := hCaseOne
      _ = max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := by rw [hDualWeight]
  · have hDualProjectedZero :
        HorizontalSubsystem.horizontalHomologyProjection Adual
          (Cyclic.cyclicGenerator q)⁻¹ dualClass = 0 :=
      not_ne_iff.mp hDualProjected
    have hCaseTwo := zero_horizontalClass_caseTwo_invGenerator_weight_bound
      q hq Adual dualZ hzDual hzDualNotBoundary hDualProjectedZero
        w threshold expansionRadius expansionNumerator expansionDenominator
          hw hthreshold hThresholdScale hColumnWeight hRadius hCaseTwoExpansion
    calc
      expansionNumerator * min (q * dualDistanceLowerBound) threshold ≤
          expansionNumerator * threshold :=
        Nat.mul_le_mul_left expansionNumerator (Nat.min_le_right _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight dualZ := hCaseTwo
      _ = max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := by rw [hDualWeight]

/-- Dressed-X distance from the dual two-case argument using a certified
lower bound on, rather than equality with, the attained dual quotient distance. -/
theorem horizontalSubsystem_dressedXDistanceAtLeast_of_dual_cases_distanceLowerBound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q) (hOdd : Odd q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    {actualDualDistance dualDistanceLowerBound lowerBound : Nat}
    (hDualMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex
        (LiftedProduct.starTranspose A)).middleCycleCode actualDualDistance)
    (hDualDistanceLower : dualDistanceLowerBound ≤ actualDualDistance)
    (hDualDistanceLowerPositive : 0 < dualDistanceLowerBound)
    (w threshold expansionRadius expansionNumerator expansionDenominator : Nat)
    (hw : 0 < w) (hthreshold : 0 < threshold)
    (hThresholdScale : 2 * w * threshold ≤ q)
    (hColumnWeight : ∀ i : aRow × Cyclic.CyclicGroup q,
      HammingWeight
        (tannerAction (LiftedProduct.starTranspose A) (Pi.single i 1)) ≤ w)
    (hRadius : threshold ≤ expansionRadius)
    (hCaseOneExpansion :
      (tannerAction (LiftedProduct.starTranspose A)).SmallSetExpanding
        (q * dualDistanceLowerBound) expansionNumerator expansionDenominator)
    (hCaseTwoExpansion :
      (tannerAction (LiftedProduct.starTranspose A)).SmallSetExpanding
        expansionRadius expansionNumerator expansionDenominator)
    (hLowerBound :
      max (2 * expansionNumerator) (4 * expansionDenominator) * lowerBound ≤
        expansionNumerator * min (q * dualDistanceLowerBound) threshold) :
    (HorizontalSubsystem.horizontalSubsystem A (Cyclic.cyclicGenerator q)
      (by simpa [Cyclic.CyclicGroup, ZMod.card] using hOdd)).DressedXDistanceAtLeast
        lowerBound := by
  intro z hz hProjected
  have hCases :=
    nonzero_horizontalCohomologyClass_cases_weight_bound_distanceLowerBound
      q hq A z hz hProjected hDualMinimum hDualDistanceLower
        hDualDistanceLowerPositive w threshold expansionRadius
          expansionNumerator expansionDenominator hw hthreshold hThresholdScale
            hColumnWeight hRadius hCaseOneExpansion hCaseTwoExpansion
  have hScaled := hLowerBound.trans hCases
  have hCoefficientPositive :
      0 < max (2 * expansionNumerator) (4 * expansionDenominator) := by
    have hDenominatorPositive := hCaseTwoExpansion.1
    exact lt_of_lt_of_le (by omega) (Nat.le_max_right _ _)
  exact Nat.le_of_mul_le_mul_left hScaled hCoefficientPositive

/-- A nonzero quotient Tanner homology class supplies a nonzero quotient
cycle, hence an attained finite minimum distance. -/
theorem exists_quotientMinimumDistance_of_middleHomology_ne_zero
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (hClass : (HorizontalSubsystem.quotientTannerComplex A).middleHomology)
    (hClassNe : hClass ≠ 0) :
    ∃ d : Nat, MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode d := by
  obtain ⟨x, hx⟩ :=
    (HorizontalSubsystem.quotientTannerComplex A).middleBoundaryInCycles.mkQ_surjective
      hClass
  have hxClassNe :
      (HorizontalSubsystem.quotientTannerComplex A).middleBoundaryInCycles.mkQ x ≠ 0 := by
    simpa [hx] using hClassNe
  have hxNe : (x : Word (ZMod 2) aCol) ≠ 0 := by
    intro hxZero
    apply hxClassNe
    have hxSubtypeZero : x = 0 := Subtype.ext hxZero
    rw [hxSubtypeZero]
    exact LinearMap.map_zero _
  apply exists_minimumDistance_of_exists_nonzero
  exact ⟨x, x.2, hxNe⟩

/-- The dual PK case split needs no global assertion that the quotient dual
code is nonzero: a nonzero projected class produces its own attained minimum,
while a zero projected class is handled directly by Case 2. -/
theorem nonzero_horizontalCohomologyClass_cases_weight_bound_of_expansion
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCocycleCode.carrier)
    (hProjected : HorizontalSubsystem.horizontalCohomologyProjection A
      (Cyclic.cyclicGenerator q)
      ((LiftedProduct.chainComplex
        (Cyclic.data q A)).middleCoboundaryInCocycles.mkQ ⟨z, hz⟩) ≠ 0)
    (dualDistanceLowerBound : Nat)
    (hDualDistanceLowerPositive : 0 < dualDistanceLowerBound)
    (w threshold expansionRadius expansionNumerator expansionDenominator : Nat)
    (hExpansionNumeratorPositive : 0 < expansionNumerator)
    (hw : 0 < w) (hthreshold : 0 < threshold)
    (hThresholdScale : 2 * w * threshold ≤ q)
    (hColumnWeight : ∀ i : aRow × Cyclic.CyclicGroup q,
      HammingWeight
        (tannerAction (LiftedProduct.starTranspose A) (Pi.single i 1)) ≤ w)
    (hRadius : threshold ≤ expansionRadius)
    (hCaseOneExpansion :
      (tannerAction (LiftedProduct.starTranspose A)).SmallSetExpanding
        (q * dualDistanceLowerBound) expansionNumerator expansionDenominator)
    (hCaseTwoExpansion :
      (tannerAction (LiftedProduct.starTranspose A)).SmallSetExpanding
        expansionRadius expansionNumerator expansionDenominator) :
    expansionNumerator * min (q * dualDistanceLowerBound) threshold ≤
      max (2 * expansionNumerator) (4 * expansionDenominator) *
        HammingWeight z := by
  let Adual := LiftedProduct.starTranspose A
  let dualZ := LiftedProductDuality.swapWord z
  have hDualWeight : HammingWeight dualZ = HammingWeight z :=
    LiftedProductDuality.HammingWeight_swapWord z
  have hzDual : dualZ ∈ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData Adual
        (Cyclic.cyclicGenerator q)⁻¹)).middleCycleCode.carrier :=
    dualCycle_mem_invGenerator_middleCycleCode q A z hz
  have hzDualNotBoundary : dualZ ∉ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData Adual
        (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryCode.carrier :=
    dualCycle_not_invGenerator_boundary_of_horizontalCohomologyProjection_ne_zero
      q A z hz hProjected
  let dualClass :=
    (LiftedProduct.chainComplex
      (Cyclic.liftedProductData Adual
        (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryInCycles.mkQ
          ⟨dualZ, hzDual⟩
  by_cases hDualProjected :
      HorizontalSubsystem.horizontalHomologyProjection Adual
        (Cyclic.cyclicGenerator q)⁻¹ dualClass ≠ 0
  · obtain ⟨actualDualDistance, hDualMinimum⟩ :=
      exists_quotientMinimumDistance_of_middleHomology_ne_zero Adual
        (HorizontalSubsystem.horizontalHomologyProjection Adual
          (Cyclic.cyclicGenerator q)⁻¹ dualClass) hDualProjected
    have hDualDistanceLower : dualDistanceLowerBound ≤ actualDualDistance := by
      apply quotientMinimumDistance_ge_of_smallSetExpanding Adual hDualMinimum
        hExpansionNumeratorPositive
      simpa [Cyclic.CyclicGroup, ZMod.card] using hCaseOneExpansion
    have hCaseOne :=
      nonzero_horizontalClass_caseOne_invGenerator_weight_bound_distanceLowerBound
        q Adual dualZ hzDual hDualMinimum hDualDistanceLower hDualProjected
          expansionNumerator expansionDenominator hDualDistanceLowerPositive
            hCaseOneExpansion
    calc
      expansionNumerator * min (q * dualDistanceLowerBound) threshold ≤
          expansionNumerator * (q * dualDistanceLowerBound) :=
        Nat.mul_le_mul_left expansionNumerator (Nat.min_le_left _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight dualZ := hCaseOne
      _ = max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := by rw [hDualWeight]
  · have hDualProjectedZero :
        HorizontalSubsystem.horizontalHomologyProjection Adual
          (Cyclic.cyclicGenerator q)⁻¹ dualClass = 0 :=
      not_ne_iff.mp hDualProjected
    have hCaseTwo := zero_horizontalClass_caseTwo_invGenerator_weight_bound
      q hq Adual dualZ hzDual hzDualNotBoundary hDualProjectedZero
        w threshold expansionRadius expansionNumerator expansionDenominator
          hw hthreshold hThresholdScale hColumnWeight hRadius hCaseTwoExpansion
    calc
      expansionNumerator * min (q * dualDistanceLowerBound) threshold ≤
          expansionNumerator * threshold :=
        Nat.mul_le_mul_left expansionNumerator (Nat.min_le_right _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight dualZ := hCaseTwo
      _ = max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := by rw [hDualWeight]

/-- Dressed-X distance using only the two proved expansion radii; quotient
dual minimum-distance existence is derived locally exactly when Case 1 needs it. -/
theorem horizontalSubsystem_dressedXDistanceAtLeast_of_expansion
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q) (hOdd : Odd q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    {dualDistanceLowerBound lowerBound : Nat}
    (hDualDistanceLowerPositive : 0 < dualDistanceLowerBound)
    (w threshold expansionRadius expansionNumerator expansionDenominator : Nat)
    (hExpansionNumeratorPositive : 0 < expansionNumerator)
    (hw : 0 < w) (hthreshold : 0 < threshold)
    (hThresholdScale : 2 * w * threshold ≤ q)
    (hColumnWeight : ∀ i : aRow × Cyclic.CyclicGroup q,
      HammingWeight
        (tannerAction (LiftedProduct.starTranspose A) (Pi.single i 1)) ≤ w)
    (hRadius : threshold ≤ expansionRadius)
    (hCaseOneExpansion :
      (tannerAction (LiftedProduct.starTranspose A)).SmallSetExpanding
        (q * dualDistanceLowerBound) expansionNumerator expansionDenominator)
    (hCaseTwoExpansion :
      (tannerAction (LiftedProduct.starTranspose A)).SmallSetExpanding
        expansionRadius expansionNumerator expansionDenominator)
    (hLowerBound :
      max (2 * expansionNumerator) (4 * expansionDenominator) * lowerBound ≤
        expansionNumerator * min (q * dualDistanceLowerBound) threshold) :
    (HorizontalSubsystem.horizontalSubsystem A (Cyclic.cyclicGenerator q)
      (by simpa [Cyclic.CyclicGroup, ZMod.card] using hOdd)).DressedXDistanceAtLeast
        lowerBound := by
  intro z hz hProjected
  have hCases := nonzero_horizontalCohomologyClass_cases_weight_bound_of_expansion
    q hq A z hz hProjected dualDistanceLowerBound hDualDistanceLowerPositive
      w threshold expansionRadius expansionNumerator expansionDenominator
        hExpansionNumeratorPositive hw hthreshold hThresholdScale hColumnWeight
          hRadius hCaseOneExpansion hCaseTwoExpansion
  have hScaled := hLowerBound.trans hCases
  have hCoefficientPositive :
      0 < max (2 * expansionNumerator) (4 * expansionDenominator) := by
    have hDenominatorPositive := hCaseTwoExpansion.1
    exact lt_of_lt_of_le (by omega) (Nat.le_max_right _ _)
  exact Nat.le_of_mul_le_mul_left hScaled hCoefficientPositive

end QEC.Coding.BalancedProduct.PKDistance
