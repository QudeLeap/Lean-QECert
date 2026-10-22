import QEC.Coding.FiniteAlternatingConstruction.GraphQuantitativeBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Actual local nonzero syndrome weight factors

Source: BDL26, paper.tex:3773–3777, complete context3763–3786,
`bdl26-local-complex-size-parameter`. The source specialization is t=beta/4,
where beta is the syndrome-weight parameter, not an asserted physical temperature.
The finite identities hold for every real t. Existing HHO20
`RandomPartition.sum_binaryWord_pow_hammingWeight` treats Fin(4*r); here the
arbitrary labelled carrier is applied to both unchanged actual syndrome fibers.
No witness assignment, energy, domination, Peierls or lifetime is asserted.
-/
noncomputable section
namespace QEC.Coding.BDL26LocalSyndromeWeights
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26ReplacementSupport BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26FiniteAlternatingCore BDL26DecodingGraph BDL26BoundedValence
open scoped BigOperators Classical

abbrev Bit := ZMod 2

/-- The weighted sum over a SET of distinct full local configurations. -/
def weightedFamily {I : Type*} [Fintype I]
    (A : Finset (Word Bit I)) (t : ℝ) : ℝ :=
  ∑ x ∈ A, Real.exp (-t * (HammingWeight x : ℝ))

/-- Every nonzero binary word, with the unique zero configuration omitted. -/
def nonzeroFactor (I : Type*) [Fintype I] (t : ℝ) : ℝ :=
  ∑ x : {x : Word Bit I // x ≠ 0}, Real.exp (-t * (HammingWeight x.val : ℝ))

/-- The literal positive-weight binomial sum; an empty range contributes zero. -/
def binomialFactor (N : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, (N.choose j : ℝ) * Real.exp (-t * (j : ℝ))

private theorem bit_eq_one (b : Bit) (h : b ≠ 0) : b = 1 := by
  apply ZMod.val_injective 2
  rw [ZMod.val_one]
  have hn : b.val ≠ 0 := (ZMod.val_eq_zero b).not.mpr h
  have hl : b.val < 2 := b.val_lt
  omega

private def supportWord {I : Type*} (A : Finset I) : Word Bit I := by
  classical
  exact fun i => if i ∈ A then 1 else 0

private theorem support_supportWord {I : Type*} [Fintype I] (A : Finset I) :
    hammingSupport (supportWord A) = A := by
  classical
  ext i
  simp [hammingSupport, supportWord]

private theorem word_supportWord {I : Type*} [Fintype I] (x : Word Bit I) :
    supportWord (hammingSupport x) = x := by
  classical
  funext i
  by_cases hi : x i = 0
  · simp [supportWord, hammingSupport, hi]
  · rw [bit_eq_one (x i) hi]
    simp only [supportWord, hammingSupport, Finset.mem_filter,
      Finset.mem_univ, true_and, if_pos hi]

private def supportEquiv (I : Type*) [Fintype I] : Word Bit I ≃ Finset I where
  toFun := hammingSupport
  invFun := supportWord
  left_inv := word_supportWord
  right_inv := support_supportWord

private theorem full_pow_sum (I : Type*) [Fintype I] (q : ℝ) :
    (∑ x : Word Bit I, q ^ HammingWeight x) = (1 + q) ^ Fintype.card I := by
  classical
  calc
    _ = ∑ A : Finset I, q ^ A.card :=
      Fintype.sum_equiv (supportEquiv I) _ _ (fun x => rfl)
    _ = ∑ A ∈ (Finset.univ : Finset I).powerset, q ^ A.card := by
      rw [Finset.powerset_univ]
    _ = (1 + q) ^ Fintype.card I := by
      rw [Finset.sum_powerset_apply_card]
      simpa [nsmul_eq_mul, mul_comm, add_comm] using
        (add_pow q 1 (Fintype.card I)).symm

private theorem exp_nat_weight (t : ℝ) (j : ℕ) :
    Real.exp (-t * (j : ℝ)) = Real.exp (-t) ^ j := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

private theorem full_exp_sum (I : Type*) [Fintype I] (t : ℝ) :
    (∑ x : Word Bit I, Real.exp (-t * (HammingWeight x : ℝ))) =
      (1 + Real.exp (-t)) ^ Fintype.card I := by
  simp_rw [exp_nat_weight]
  exact full_pow_sum I (Real.exp (-t))

/-- Exact deletion of the one zero-word contribution, for every real t. -/
theorem nonzeroFactor_eq_power (I : Type*) [Fintype I] (t : ℝ) :
    nonzeroFactor I t = (1 + Real.exp (-t)) ^ Fintype.card I - 1 := by
  let f : Word Bit I → ℝ := fun x => Real.exp (-t * (HammingWeight x : ℝ))
  have hs := full_exp_sum I t
  change (∑ x, f x) = _ at hs
  rw [Fintype.sum_eq_add_sum_subtype_ne f 0] at hs
  have hz : f 0 = 1 := by simp [f]
  rw [hz] at hs
  change 1 + nonzeroFactor I t = _ at hs
  linarith

/-- The binomial sum is precisely the nonconstant part of the power. -/
theorem binomialFactor_eq_power (N : ℕ) (t : ℝ) :
    binomialFactor N t = (1 + Real.exp (-t)) ^ N - 1 := by
  have hp : (∑ j ∈ Finset.range (N+1),
      (N.choose j : ℝ) * Real.exp (-t) ^ j) = (1 + Real.exp (-t)) ^ N := by
    simpa only [one_pow, mul_one, one_mul, mul_comm, add_comm] using
      (add_pow (Real.exp (-t)) 1 N).symm
  have hr : Finset.range (N+1) = insert 0 (Finset.Icc 1 N) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hr, Finset.sum_insert (by simp)] at hp
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one] at hp
  have hb : binomialFactor N t =
      ∑ j ∈ Finset.Icc 1 N, (N.choose j : ℝ) * Real.exp (-t) ^ j := by
    unfold binomialFactor
    apply Finset.sum_congr rfl
    intro j _
    rw [exp_nat_weight]
  rw [hb]
  linarith

/-- Both equalities of the source local-factor identity on arbitrary labels. -/
theorem nonzeroFactor_identity (I : Type*) [Fintype I] (t : ℝ) :
    nonzeroFactor I t = binomialFactor (Fintype.card I) t ∧
      binomialFactor (Fintype.card I) t = (1 + Real.exp (-t)) ^ Fintype.card I - 1 := by
  exact ⟨(nonzeroFactor_eq_power I t).trans
    (binomialFactor_eq_power (Fintype.card I) t).symm,
    binomialFactor_eq_power (Fintype.card I) t⟩

theorem weightedFamily_nonneg {I : Type*} [Fintype I]
    (A : Finset (Word Bit I)) (t : ℝ) : 0 ≤ weightedFamily A t :=
  Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)

/-- A constrained nonzero SET is dominated by all nonzero configurations. -/
theorem weightedFamily_le_nonzeroFactor {I : Type*} [Fintype I]
    (A : Finset (Word Bit I)) (t : ℝ) (hA : ∀ x ∈ A, x ≠ 0) :
    weightedFamily A t ≤ nonzeroFactor I t := by
  have hn : (0 : Word Bit I) ∉ A := fun h => hA 0 h rfl
  have hs := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ (insert (0 : Word Bit I) A))
    (fun x _ _ => (Real.exp_pos (-t * (HammingWeight x : ℝ))).le)
  rw [Finset.sum_insert hn] at hs
  have hf := full_exp_sum I t
  rw [hf] at hs
  change Real.exp (-t * (HammingWeight (0 : Word Bit I) : ℝ)) +
    weightedFamily A t ≤ _ at hs
  simp only [HammingWeight_zero, Nat.cast_zero, mul_zero, Real.exp_zero] at hs
  rw [nonzeroFactor_eq_power]
  linarith

/-- The size envelope is an upper bound, never an equality of measured sizes. -/
theorem nonzeroFactor_le_envelope (I : Type*) [Fintype I]
    (t : ℝ) (M : ℕ) (hM : Fintype.card I ≤ M) :
    nonzeroFactor I t ≤ (1 + Real.exp (-t)) ^ M - 1 := by
  rw [nonzeroFactor_eq_power]
  exact sub_le_sub_right (pow_le_pow_right₀
    (show 1 ≤ 1 + Real.exp (-t) by linarith [Real.exp_pos (-t)]) hM) 1

theorem weightedFamily_bounds {I : Type*} [Fintype I]
    (A : Finset (Word Bit I)) (t : ℝ) (hA : ∀ x ∈ A, x ≠ 0)
    (M : ℕ) (hM : Fintype.card I ≤ M) :
    0 ≤ weightedFamily A t ∧ weightedFamily A t ≤
      (1 + Real.exp (-t)) ^ M - 1 :=
  ⟨weightedFamily_nonneg A t, (weightedFamily_le_nonzeroFactor A t hA).trans
    (nonzeroFactor_le_envelope I t M hM)⟩

theorem weightedFamily_empty (I : Type*) [Fintype I] (t : ℝ) :
    weightedFamily (∅ : Finset (Word Bit I)) t = 0 := by simp [weightedFamily]

theorem nonzeroFactor_zero_parameter (I : Type*) [Fintype I] :
    nonzeroFactor I 0 = (2 : ℝ) ^ Fintype.card I - 1 := by
  rw [nonzeroFactor_eq_power]
  norm_num

theorem nonzeroFactor_empty_coordinates (I : Type*) [Fintype I] [IsEmpty I] (t : ℝ) :
    nonzeroFactor I t = 0 := by rw [nonzeroFactor_eq_power]; simp

/-- Extend a word on the entire original owner fiber by zero, retaining labels. -/
def fiberExtend {C Label : Type*} (owner : C → Label) (label : Label)
    (x : Word Bit {c : C // owner c = label}) : Word Bit C := by
  classical
  exact fun c => if hc : owner c = label then x ⟨c,hc⟩ else 0

theorem fiberExtend_apply {C Label : Type*} (owner : C → Label) (label : Label)
    (x : Word Bit {c : C // owner c = label}) (c : C) (hc : owner c = label) :
    fiberExtend owner label x c = x ⟨c,hc⟩ := by simp [fiberExtend,hc]

theorem fiberExtend_injective {C Label : Type*} (owner : C → Label) (label : Label) :
    Function.Injective (fiberExtend owner label) := by
  intro x y h
  funext c
  have he := congrFun h c.val
  rw [fiberExtend_apply owner label x c.val c.property,
    fiberExtend_apply owner label y c.val c.property] at he
  exact he

/-- Full support image in the actual carrier, including every geometric copy. -/
theorem fiberExtend_support {C Label : Type*} [Fintype C]
    (owner : C → Label) (label : Label) (x : Word Bit {c : C // owner c = label}) :
    hammingSupport (fiberExtend owner label x) =
      (hammingSupport x).image Subtype.val := by
  classical
  ext c
  constructor
  · intro hm
    have hn := (Finset.mem_filter.mp hm).2
    by_cases hc : owner c = label
    · exact Finset.mem_image.mpr ⟨⟨c,hc⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          simpa only [fiberExtend_apply owner label x c hc] using hn⟩,rfl⟩
    · simp [fiberExtend,hc] at hn
  · intro hm
    rcases Finset.mem_image.mp hm with ⟨a,ha,rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [fiberExtend_apply owner label x a.val a.property]
    exact (Finset.mem_filter.mp ha).2

theorem fiberExtend_weight {C Label : Type*} [Fintype C]
    (owner : C → Label) (label : Label) (x : Word Bit {c : C // owner c = label}) :
    HammingWeight (fiberExtend owner label x) = HammingWeight x := by
  classical
  rw [HammingWeight_eq_card_hammingSupport, fiberExtend_support]
  simpa only [HammingWeight] using
    (Finset.card_image_iff.mpr (by
      intro a _ b _ hab
      exact Subtype.ext hab))

/-- Same weighted family evaluated in the original full replacement carrier. -/
def fiberFactor {C Label : Type*} [Fintype C] (owner : C → Label) (label : Label)
    (A : Finset (Word Bit {c : C // owner c = label})) (t : ℝ) : ℝ :=
  ∑ x ∈ A, Real.exp (-t * (HammingWeight (fiberExtend owner label x) : ℝ))

theorem fiberFactor_eq_weightedFamily {C Label : Type*} [Fintype C]
    (owner : C → Label) (label : Label)
    (A : Finset (Word Bit {c : C // owner c = label})) (t : ℝ) :
    fiberFactor owner label A t = weightedFamily A t := by
  unfold fiberFactor weightedFamily
  apply Finset.sum_congr rfl
  intro x _
  rw [fiberExtend_weight]

/-- Injectivity makes the extension-indexed sum an actual original-word SET sum. -/
theorem fiberFactor_eq_image {C Label : Type*} [Fintype C]
    (owner : C → Label) (label : Label)
    (A : Finset (Word Bit {c : C // owner c = label})) (t : ℝ) :
    fiberFactor owner label A t =
      weightedFamily (A.image (fiberExtend owner label)) t := by
  classical
  unfold weightedFamily
  rw [Finset.sum_image]
  · rfl
  · intro x _ y _ hxy
    exact fiberExtend_injective owner label hxy

abbrev RXFiber (P : TannerSquarePresentation) (S : OddScale) (u : Vertex P) :=
  {c : RX2 P S // rxSyndromeOwner P S c = u}
abbrev RZFiber (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) :=
  {c : RZZ P S // rzSyndromeOwner P S c = z}

/-- Actual RX local factor evaluated on the full RX2 carrier. -/
def rxWeightFactor (P : TannerSquarePresentation) (S : OddScale) (u : Vertex P)
    (A : Finset (Word Bit (RXFiber P S u))) (t : ℝ) : ℝ :=
  fiberFactor (rxSyndromeOwner P S) u A t

/-- Actual RZ local factor evaluated on the full RZZ carrier. -/
def rzWeightFactor (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (A : Finset (Word Bit (RZFiber P S z))) (t : ℝ) : ℝ :=
  fiberFactor (rzSyndromeOwner P S) z A t

theorem rx_extend_weight (P : TannerSquarePresentation) (S : OddScale) (u : Vertex P)
    (x : Word Bit (RXFiber P S u)) :
    HammingWeight (fiberExtend (rxSyndromeOwner P S) u x) = HammingWeight x := by
  convert fiberExtend_weight (rxSyndromeOwner P S) u x using 1 <;>
    congr 1 <;> exact Subsingleton.elim _ _

theorem rz_extend_weight (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (x : Word Bit (RZFiber P S z)) :
    HammingWeight (fiberExtend (rzSyndromeOwner P S) z x) = HammingWeight x := by
  convert fiberExtend_weight (rzSyndromeOwner P S) z x using 1 <;>
    congr 1 <;> exact Subsingleton.elim _ _

theorem rxWeightFactor_eq_original_family (P : TannerSquarePresentation) (S : OddScale)
    (u : Vertex P) (A : Finset (Word Bit (RXFiber P S u))) (t : ℝ) :
    rxWeightFactor P S u A t =
      weightedFamily (A.image (fiberExtend (rxSyndromeOwner P S) u)) t := by
  classical
  unfold rxWeightFactor fiberFactor weightedFamily
  rw [Finset.sum_image]
  intro x _ y _ hxy
  exact fiberExtend_injective (rxSyndromeOwner P S) u hxy

theorem rzWeightFactor_eq_original_family (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (A : Finset (Word Bit (RZFiber P S z))) (t : ℝ) :
    rzWeightFactor P S z A t =
      weightedFamily (A.image (fiberExtend (rzSyndromeOwner P S) z)) t :=
  fiberFactor_eq_image _ _ A t

theorem rxWeightFactor_bounds (P : TannerSquarePresentation) (hP : BoundedValence P)
    (S : OddScale) (u : Vertex P) (A : Finset (Word Bit (RXFiber P S u)))
    (t : ℝ) (hA : ∀ x ∈ A, x ≠ 0) :
    0 ≤ rxWeightFactor P S u A t ∧ rxWeightFactor P S u A t ≤
      (1 + Real.exp (-t)) ^ (14 * S.ell^2) - 1 := by
  have heq : rxWeightFactor P S u A t = weightedFamily A t := by
    unfold rxWeightFactor fiberFactor weightedFamily
    apply Finset.sum_congr rfl
    intro x _
    rw [rx_extend_weight]
  rw [heq]
  exact weightedFamily_bounds A t hA (14 * S.ell^2)
    (rxSyndromeFiber_card_le P hP S u)

theorem rzWeightFactor_bounds (P : TannerSquarePresentation) (aP : TannerSquareAdmissible P)
    (hP : BoundedValence P) (S : OddScale) (z : P.Z)
    (A : Finset (Word Bit (RZFiber P S z))) (t : ℝ) (hA : ∀ x ∈ A, x ≠ 0) :
    0 ≤ rzWeightFactor P S z A t ∧ rzWeightFactor P S z A t ≤
      (1 + Real.exp (-t)) ^ (14 * S.ell^2) - 1 := by
  have heq : rzWeightFactor P S z A t = weightedFamily A t := by
    unfold rzWeightFactor fiberFactor weightedFamily
    apply Finset.sum_congr rfl
    intro x _
    rw [rz_extend_weight]
  rw [heq]
  exact weightedFamily_bounds A t hA (14 * S.ell^2)
    (rzSyndromeFiber_card_le P aP hP S z)

theorem state_rxWeightFactor_bounds (S : OddScale) (n : ℕ)
    (u : Vertex (state S n).presentation)
    (A : Finset (Word Bit (RXFiber (state S n).presentation S u)))
    (t : ℝ) (hA : ∀ x ∈ A, x ≠ 0) :
    0 ≤ rxWeightFactor (state S n).presentation S u A t ∧
      rxWeightFactor (state S n).presentation S u A t ≤
        (1 + Real.exp (-t)) ^ (14 * S.ell^2) - 1 :=
  rxWeightFactor_bounds _ (state_boundedValence S n) S u A t hA

theorem state_rzWeightFactor_bounds (S : OddScale) (n : ℕ) (z : (state S n).presentation.Z)
    (A : Finset (Word Bit (RZFiber (state S n).presentation S z)))
    (t : ℝ) (hA : ∀ x ∈ A, x ≠ 0) :
    0 ≤ rzWeightFactor (state S n).presentation S z A t ∧
      rzWeightFactor (state S n).presentation S z A t ≤
        (1 + Real.exp (-t)) ^ (14 * S.ell^2) - 1 :=
  rzWeightFactor_bounds _ (state S n).admissible.toTannerSquareAdmissible
    (state_boundedValence S n) S z A t hA

/-- The source's beta/4 convention, without a physical-temperature assertion. -/
def sourceEnvelope (S : OddScale) (beta : ℝ) : ℝ :=
  (1 + Real.exp (-(beta/4))) ^ (14 * S.ell^2) - 1

theorem state_rx_source_bounds (S : OddScale) (n : ℕ)
    (u : Vertex (state S n).presentation)
    (A : Finset (Word Bit (RXFiber (state S n).presentation S u)))
    (beta : ℝ) (hA : ∀ x ∈ A, x ≠ 0) :
    0 ≤ rxWeightFactor (state S n).presentation S u A (beta/4) ∧
      rxWeightFactor (state S n).presentation S u A (beta/4) ≤ sourceEnvelope S beta :=
  state_rxWeightFactor_bounds S n u A (beta/4) hA

theorem state_rz_source_bounds (S : OddScale) (n : ℕ) (z : (state S n).presentation.Z)
    (A : Finset (Word Bit (RZFiber (state S n).presentation S z)))
    (beta : ℝ) (hA : ∀ x ∈ A, x ≠ 0) :
    0 ≤ rzWeightFactor (state S n).presentation S z A (beta/4) ∧
      rzWeightFactor (state S n).presentation S z A (beta/4) ≤ sourceEnvelope S beta :=
  state_rzWeightFactor_bounds S n z A (beta/4) hA

end QEC.Coding.BDL26LocalSyndromeWeights
