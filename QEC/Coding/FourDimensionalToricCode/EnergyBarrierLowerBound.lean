import QEC.Coding.FourDimensionalToricCode.MembraneSyndrome
import QEC.Coding.Stabilizer.PathEnergy

/-!
# Linear lower bound for four-dimensional toric membrane paths

This module proves the finite separator estimate used in the lower half of the
four-dimensional toric-code energy-barrier argument.  The proof is internal:
it projects membrane configurations to a finite binary square, follows the
number of completely filled rows, and counts actual adjacent transitions.
No isoperimetric or barrier estimate is supplied as an input hypothesis.

The geometric projections and their comparison with the primal and dual
defect loops are developed below the reusable finite-grid lemmas.  Public
`Theta(L)` integration remains downstream of the separate upper-bound module.
-/

noncomputable section

namespace QEC.Coding.PeriodicCubical4

open scoped Classical BigOperators
open PauliSymplectic

namespace BinarySquare

/-- A binary `n x n` square.  We use open adjacent edges; these form a subset
of the edges of the periodic square and therefore suffice for a lower bound. -/
abbrev Grid (n : Nat) := Fin n → Fin n → ZMod 2

/-- Uncurry a square to the word on its cell coordinates. -/
def flatten {n : Nat} (g : Grid n) : Word (ZMod 2) (Fin n × Fin n) :=
  fun q => g q.1 q.2

/-- Adjacent horizontal differences within a row. -/
def horizontalDerivative {n : Nat} (g : Grid n) (y : Fin n) :
    Word (ZMod 2) (Fin (n - 1)) :=
  fun i => g y ⟨i.1 + 1, by omega⟩ + g y ⟨i.1, by omega⟩

/-- Adjacent vertical differences within a column. -/
def verticalDerivative {n : Nat} (g : Grid n) (x : Fin n) :
    Word (ZMod 2) (Fin (n - 1)) :=
  fun i => g ⟨i.1 + 1, by omega⟩ x + g ⟨i.1, by omega⟩ x

/-- Number of open square edges across which the binary value changes. -/
def openBoundaryLength {n : Nat} (g : Grid n) : Nat :=
  (∑ y : Fin n, HammingWeight (horizontalDerivative g y)) +
    ∑ x : Fin n, HammingWeight (verticalDerivative g x)

/-- Rows whose every entry is one. -/
def fullRows {n : Nat} (g : Grid n) : Finset (Fin n) :=
  Finset.univ.filter fun y => ∀ x, g y x = 1

/-- Rows whose every entry is zero. -/
def emptyRows {n : Nat} (g : Grid n) : Finset (Fin n) :=
  Finset.univ.filter fun y => ∀ x, g y x = 0

/-- Pointwise binary difference of two squares. -/
def difference {n : Nat} (g h : Grid n) : Word (ZMod 2) (Fin n × Fin n) :=
  fun p => g p.1 p.2 + h p.1 p.2

/-- The two squares differ on at most one cell. -/
def OneCellStep {n : Nat} (g h : Grid n) : Prop :=
  HammingWeight (difference g h) ≤ 1

@[simp] theorem mem_fullRows {n : Nat} (g : Grid n) (y : Fin n) :
    y ∈ fullRows g ↔ ∀ x, g y x = 1 := by
  simp [fullRows]

@[simp] theorem mem_emptyRows {n : Nat} (g : Grid n) (y : Fin n) :
    y ∈ emptyRows g ↔ ∀ x, g y x = 0 := by
  simp [emptyRows]

private theorem zmod_two_add_eq_zero_iff_eq (a b : ZMod 2) :
    a + b = 0 ↔ a = b := by
  rw [add_eq_zero_iff_eq_neg, ZMod.neg_eq_self_mod_two]

/-- If every adjacent difference on a finite line vanishes, the line is
constant. -/
theorem eq_zero_of_horizontalDerivative_eq_zero {n : Nat} (g : Grid n)
    (y : Fin n) (hzero : horizontalDerivative g y = 0) (i j : Fin n) :
    g y i = g y j := by
  have hstep (k : Nat) (hk : k + 1 < n) :
      g y ⟨k + 1, hk⟩ = g y ⟨k, by omega⟩ := by
    have h := congrFun hzero (⟨k, by omega⟩ : Fin (n - 1))
    simp only [horizontalDerivative, Pi.zero_apply] at h
    exact (zmod_two_add_eq_zero_iff_eq _ _).mp h
  have hfromZero (q : Fin n) : g y q = g y ⟨0, Nat.zero_lt_of_lt q.2⟩ := by
    have aux : ∀ k : Nat, ∀ hk : k < n,
        g y ⟨k, hk⟩ = g y ⟨0, Nat.zero_lt_of_lt hk⟩ := by
      intro k
      induction k with
      | zero => intro hk; rfl
      | succ k ih =>
          intro hk
          rw [hstep k hk]
          exact ih (by omega)
    exact aux q.1 q.2
  rw [hfromZero i, hfromZero j]

/-- A row containing both binary values has at least one open horizontal
boundary edge. -/
theorem one_le_horizontalWeight_of_exists_zero_one {n : Nat} (g : Grid n)
    (y : Fin n) (hzero : ∃ x, g y x = 0) (hone : ∃ x, g y x = 1) :
    1 ≤ HammingWeight (horizontalDerivative g y) := by
  by_contra hnot
  have hweight : HammingWeight (horizontalDerivative g y) = 0 := by omega
  have hderiv : horizontalDerivative g y = 0 :=
    (HammingWeight_eq_zero_iff _).mp hweight
  obtain ⟨x₀, hx₀⟩ := hzero
  obtain ⟨x₁, hx₁⟩ := hone
  have := eq_zero_of_horizontalDerivative_eq_zero g y hderiv x₀ x₁
  rw [hx₀, hx₁] at this
  exact zero_ne_one this

/-- A column containing both binary values has at least one open vertical
boundary edge. -/
theorem one_le_verticalWeight_of_exists_zero_one {n : Nat} (g : Grid n)
    (x : Fin n) (hzero : ∃ y, g y x = 0) (hone : ∃ y, g y x = 1) :
    1 ≤ HammingWeight (verticalDerivative g x) := by
  let gt : Grid n := fun y x => g x y
  have htranspose : verticalDerivative g x = horizontalDerivative gt x := by
    rfl
  rw [htranspose]
  exact one_le_horizontalWeight_of_exists_zero_one gt x hzero hone

private theorem zmod_two_eq_zero_of_ne_one {a : ZMod 2} (ha : a ≠ 1) :
    a = 0 := by
  by_contra ha0
  exact ha (PauliSymplectic.zmod_two_eq_one_of_ne_zero ha0)

/-- Changing at most one cell changes the number of full rows by at most one. -/
theorem fullRows_card_dist_le_one_of_oneCellStep {n : Nat} (g h : Grid n)
    (hstep : OneCellStep g h) :
    Nat.dist (fullRows g).card (fullRows h).card ≤ 1 := by
  by_cases heq : g = h
  · subst h
    simp
  have hdifference : difference g h ≠ 0 := by
    intro hzero
    apply heq
    funext y x
    have hx := congrFun hzero (y, x)
    simp only [difference, Pi.zero_apply] at hx
    exact (zmod_two_add_eq_zero_iff_eq _ _).mp hx
  have hsupp : (hammingSupport (difference g h)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hweight : HammingWeight (difference g h) = 0 := by
      simp [HammingWeight, hempty]
    exact hdifference ((HammingWeight_eq_zero_iff _).mp hweight)
  obtain ⟨p, hp⟩ := hsupp
  have hsupportCard : (hammingSupport (difference g h)).card ≤ 1 := by
    exact hstep
  have hsupport : hammingSupport (difference g h) = {p} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hp, ?_⟩
    intro q hq
    exact Finset.card_le_one.mp hsupportCard q hq p hp
  have hrow (y : Fin n) (hy : y ≠ p.1) :
      y ∈ fullRows g ↔ y ∈ fullRows h := by
    simp only [mem_fullRows]
    apply forall_congr'
    intro x
    have hnot : (y, x) ∉ hammingSupport (difference g h) := by
      rw [hsupport]
      simp only [Finset.mem_singleton]
      intro heq
      exact hy (congrArg Prod.fst heq)
    have hzero : difference g h (y, x) = 0 := by
      simpa [hammingSupport] using hnot
    have heqValue : g y x = h y x :=
      (zmod_two_add_eq_zero_iff_eq _ _).mp hzero
    rw [heqValue]
  have herase : (fullRows g).erase p.1 = (fullRows h).erase p.1 := by
    ext y
    by_cases hy : y = p.1
    · subst y; simp
    · simp [hy, hrow y hy]
  have hg : (fullRows g).card ≤ ((fullRows g).erase p.1).card + 1 := by
    by_cases hpRow : p.1 ∈ fullRows g
    · rw [Finset.card_erase_of_mem hpRow]
      omega
    · simp [Finset.erase_eq_of_notMem hpRow]
  have hh : (fullRows h).card ≤ ((fullRows h).erase p.1).card + 1 := by
    by_cases hpRow : p.1 ∈ fullRows h
    · rw [Finset.card_erase_of_mem hpRow]
      omega
    · simp [Finset.erase_eq_of_notMem hpRow]
  have hgErase : ((fullRows g).erase p.1).card ≤ (fullRows g).card :=
    Finset.card_erase_le
  have hhErase : ((fullRows h).erase p.1).card ≤ (fullRows h).card :=
    Finset.card_erase_le
  rw [herase] at hg hgErase
  unfold Nat.dist
  omega

/-- A nearest-neighbour walk of natural numbers hits every intermediate
integer. -/
theorem exists_eq_of_nat_walk
    (a : Nat → Nat) (N target : Nat)
    (hstart : a 0 ≤ target) (hend : target ≤ a N)
    (hstep : ∀ k < N, Nat.dist (a (k + 1)) (a k) ≤ 1) :
    ∃ k ≤ N, a k = target := by
  induction N with
  | zero =>
      exact ⟨0, le_rfl, by omega⟩
  | succ N ih =>
      by_cases hbefore : target ≤ a N
      · obtain ⟨k, hk, hktarget⟩ := ih hbefore (fun k hk => hstep k (by omega))
        exact ⟨k, by omega, hktarget⟩
      · refine ⟨N + 1, by omega, ?_⟩
        have hlast := hstep N (by omega)
        unfold Nat.dist at hlast
        omega

/-- A square with exactly `n / 2` completely filled rows has an open edge
boundary of length at least `n / 2`.  The two cases are constructive: an empty
row forces a transition in every column, while without an empty row each
non-full row forces a transition inside that row. -/
theorem half_le_openBoundaryLength_of_fullRows_card {n : Nat} (g : Grid n)
    (hcard : (fullRows g).card = n / 2) :
    n / 2 ≤ openBoundaryLength g := by
  by_cases hhalf : n / 2 = 0
  · simp [hhalf]
  by_cases hempty : (emptyRows g).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hempty
    have hfull : (fullRows g).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hnone
      have : (fullRows g).card = 0 := by simp [hnone]
      omega
    obtain ⟨y₁, hy₁⟩ := hfull
    have hcolumns : n ≤ ∑ x : Fin n, HammingWeight (verticalDerivative g x) := by
      simpa using Finset.sum_le_sum (s := Finset.univ)
        (fun x _ => one_le_verticalWeight_of_exists_zero_one g x
          ⟨y₀, (mem_emptyRows g y₀).mp hy₀ x⟩
          ⟨y₁, (mem_fullRows g y₁).mp hy₁ x⟩)
    unfold openBoundaryLength
    omega
  · have hempty_eq : emptyRows g = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hrows :
        (∑ y : Fin n, if y ∈ fullRows g then 0 else 1) ≤
          ∑ y : Fin n, HammingWeight (horizontalDerivative g y) := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : y ∈ fullRows g
      · simp [hy]
      · simp only [hy, ↓reduceIte]
        have hzero : ∃ x, g y x = 0 := by
          have hnotAll : ¬ ∀ x, g y x = 1 := by
            simpa [mem_fullRows] using hy
          push Not at hnotAll
          obtain ⟨x, hx⟩ := hnotAll
          exact ⟨x, zmod_two_eq_zero_of_ne_one hx⟩
        have hone : ∃ x, g y x = 1 := by
          by_contra hnot
          push Not at hnot
          have hyEmpty : y ∈ emptyRows g := (mem_emptyRows g y).2 fun x =>
            zmod_two_eq_zero_of_ne_one (hnot x)
          rw [hempty_eq] at hyEmpty
          simp at hyEmpty
        exact one_le_horizontalWeight_of_exists_zero_one g y hzero hone
    have hcount :
        (∑ y : Fin n, if y ∈ fullRows g then 0 else 1) = n - n / 2 := by
      calc
        (∑ y : Fin n, if y ∈ fullRows g then 0 else 1) =
            (Finset.univ.filter fun y => y ∉ fullRows g).card := by
              calc
                (∑ y : Fin n, if y ∈ fullRows g then 0 else 1) =
                    ∑ y ∈ Finset.univ,
                      if y ∉ fullRows g then (1 : Nat) else 0 := by
                        apply Finset.sum_congr rfl
                        intro y _
                        by_cases hy : y ∈ fullRows g <;> simp [hy]
                _ = (Finset.univ.filter fun y => y ∉ fullRows g).card :=
                  Finset.sum_boole (R := Nat)
                    (fun y : Fin n => y ∉ fullRows g) Finset.univ
        _ = n - n / 2 := by
          rw [Finset.filter_notMem_eq_sdiff,
            Finset.card_sdiff_of_subset (Finset.subset_univ _), hcard]
          simp
    unfold openBoundaryLength
    rw [hcount] at hrows
    omega

end BinarySquare

variable {L : Nat} [NeZero L] [Fact (1 < L)]

private theorem wordPairing_add_right_local {Index : Type*} [Fintype Index]
    (a b c : Word (ZMod 2) Index) :
    wordPairing a (b + c) = wordPairing a b + wordPairing a c := by
  simp [wordPairing_apply, dotProduct, mul_add, Finset.sum_add_distrib]

private theorem wordPairing_add_left_local {Index : Type*} [Fintype Index]
    (a b c : Word (ZMod 2) Index) :
    wordPairing (a + b) c = wordPairing a c + wordPairing b c := by
  simp [wordPairing_apply, dotProduct, add_mul, Finset.sum_add_distrib]

@[simp] private theorem wordPairing_cellWord_right_local
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (m : Word (ZMod 2) Index) (i : Index) :
    wordPairing m (cellWord i) = m i := by
  simp only [wordPairing_apply, dotProduct, cellWord]
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j hji
    simp [hji]

@[simp] private theorem wordPairing_cellWord_left_local
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (m : Word (ZMod 2) Index) (i : Index) :
    wordPairing (cellWord i) m = m i := by
  rw [wordPairing_apply, dotProduct_comm, ← wordPairing_apply]
  exact wordPairing_cellWord_right_local m i

private theorem exists_common_support_of_wordPairing_ne_zero
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (a b : Word (ZMod 2) Index) (hpair : wordPairing a b ≠ 0) :
    ∃ i, i ∈ hammingSupport a ∧ i ∈ hammingSupport b := by
  by_contra hnone
  push Not at hnone
  apply hpair
  simp only [wordPairing_apply, dotProduct]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hai : a i = 0
  · simp [hai]
  · have hain : i ∈ hammingSupport a := by
      simpa [hammingSupport] using hai
    have hbinot : i ∉ hammingSupport b := hnone i hain
    have hbi : b i = 0 := by
      by_contra hbne
      exact hbinot (by simpa [hammingSupport] using hbne)
    simp [hbi]

/-- Pairings against pairwise support-disjoint fibers cannot contain more
nonzero coordinates than the word being paired. -/
theorem HammingWeight_pairings_le_of_pairwise_disjoint
    {FiberIndex CellIndex : Type*}
    [Fintype FiberIndex] [DecidableEq FiberIndex]
    [Fintype CellIndex] [DecidableEq CellIndex]
    (fiber : FiberIndex → Word (ZMod 2) CellIndex)
    (u : Word (ZMod 2) CellIndex)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (hammingSupport (fiber i)) (hammingSupport (fiber j))) :
    HammingWeight (fun i => wordPairing (fiber i) u) ≤ HammingWeight u := by
  classical
  let output : Word (ZMod 2) FiberIndex := fun i => wordPairing (fiber i) u
  let sourceSupport := hammingSupport output
  let targetSupport := hammingSupport u
  have hwitness (i : {i // i ∈ sourceSupport}) :
      ∃ c, c ∈ hammingSupport (fiber i.1) ∧ c ∈ targetSupport := by
    apply exists_common_support_of_wordPairing_ne_zero (fiber i.1) u
    have hi : i.1 ∈ hammingSupport output := by
      simpa only [sourceSupport] using i.2
    have hine : output i.1 ≠ 0 := by
      simpa only [hammingSupport, Finset.mem_filter, Finset.mem_univ,
        true_and] using hi
    simpa only [output] using hine
  let chosen (i : {i // i ∈ sourceSupport}) : CellIndex :=
    Classical.choose (hwitness i)
  have chosen_spec (i : {i // i ∈ sourceSupport}) :
      chosen i ∈ hammingSupport (fiber i.1) ∧
        chosen i ∈ targetSupport :=
    Classical.choose_spec (hwitness i)
  let f : {i // i ∈ sourceSupport} → {c // c ∈ targetSupport} :=
    fun i => ⟨chosen i, (chosen_spec i).2⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hd := hdisjoint hne
    have hchosen : chosen i = chosen j := congrArg Subtype.val hij
    exact (Finset.disjoint_left.mp hd (chosen_spec i).1) (by
      rw [hchosen]
      exact (chosen_spec j).1)
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe sourceSupport, Fintype.card_coe targetSupport] at hcard
  exact hcard

/-- Convert the ordered finite-square coordinate to the periodic coordinate
used by the cubical cellulation. -/
abbrev finToPeriodic (i : Fin L) : ZMod L := ZMod.finEquiv L i

/-- Convert a periodic coordinate back to the ordered finite square. -/
abbrev periodicToFin (a : ZMod L) : Fin L := (ZMod.finEquiv L).symm a

private theorem coord4_components (c : Coord L) :
    coord4 (c .x) (c .y) (c .z) (c .w) = c := by
  ext a
  cases a <;> rfl

/-- Pair a plaquette word with every translated dual membrane.  A primal
logical membrane projects to the all-one square. -/
def primalSquareProjection (m : Word (ZMod 2) (Plaquette L)) :
    BinarySquare.Grid L :=
  fun y x => wordPairing (dualXYMembrane (finToPeriodic x) (finToPeriodic y)) m

/-- Pair a plaquette word with every translated primal membrane.  The paired
dual logical membrane projects to the all-one square. -/
def dualSquareProjection (m : Word (ZMod 2) (Plaquette L)) :
    BinarySquare.Grid L :=
  fun w z => wordPairing m (primalXYMembrane (finToPeriodic z) (finToPeriodic w))

@[simp] theorem primalSquareProjection_cellWord_apply (p : Plaquette L)
    (y x : Fin L) :
    primalSquareProjection (cellWord p) y x =
      if p.2 = .xy ∧ finToPeriodic x = p.1 .x ∧
          finToPeriodic y = p.1 .y then 1 else 0 := by
  rcases p with ⟨c, q⟩
  rw [← coord4_components c]
  rw [primalSquareProjection, wordPairing_cellWord_right_local]
  simpa [eq_comm] using
    (dualXYMembrane_apply_coord4 (L := L)
      (finToPeriodic x) (finToPeriodic y)
      (c .x) (c .y) (c .z) (c .w) q)

@[simp] theorem dualSquareProjection_cellWord_apply (p : Plaquette L)
    (w z : Fin L) :
    dualSquareProjection (cellWord p) w z =
      if p.2 = .xy ∧ p.1 .z = finToPeriodic z ∧
          p.1 .w = finToPeriodic w then 1 else 0 := by
  rcases p with ⟨c, q⟩
  rw [← coord4_components c]
  rw [dualSquareProjection, wordPairing_cellWord_left_local]
  exact primalXYMembrane_apply_coord4 (L := L)
    (finToPeriodic z) (finToPeriodic w)
    (c .x) (c .y) (c .z) (c .w) q

/-- A single plaquette has primal projection supported at at most its one
ordered `xy` coordinate. -/
theorem hammingSupport_primalSquareProjection_cellWord_subset (p : Plaquette L) :
    hammingSupport
        ((fun q : Fin L × Fin L =>
          primalSquareProjection (L := L) (cellWord p) q.1 q.2) :
          Word (ZMod 2) (Fin L × Fin L)) ⊆
      {(periodicToFin (p.1 .y), periodicToFin (p.1 .x))} := by
  rintro ⟨y, x⟩ hmem
  simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  change primalSquareProjection (cellWord p) y x ≠ 0 at hmem
  rw [primalSquareProjection_cellWord_apply] at hmem
  split_ifs at hmem with hcondition
  · rcases hcondition with ⟨_, hx, hy⟩
    simp only [Finset.mem_singleton]
    apply Prod.ext
    · exact (ZMod.finEquiv L).injective (by simpa using hy)
    · exact (ZMod.finEquiv L).injective (by simpa using hx)
  · exact (hmem rfl).elim

/-- A single plaquette changes at most one primal projected square cell. -/
theorem HammingWeight_primalSquareProjection_cellWord_le_one (p : Plaquette L) :
    HammingWeight
        ((fun q : Fin L × Fin L =>
          primalSquareProjection (L := L) (cellWord p) q.1 q.2) :
          Word (ZMod 2) (Fin L × Fin L)) ≤ 1 := by
  rw [HammingWeight_eq_card_hammingSupport]
  exact (Finset.card_le_card
    (hammingSupport_primalSquareProjection_cellWord_subset p)).trans (by simp)

/-- A single plaquette has dual projection supported at at most its one
ordered complementary coordinate. -/
theorem hammingSupport_dualSquareProjection_cellWord_subset (p : Plaquette L) :
    hammingSupport
        ((fun q : Fin L × Fin L =>
          dualSquareProjection (L := L) (cellWord p) q.1 q.2) :
          Word (ZMod 2) (Fin L × Fin L)) ⊆
      {(periodicToFin (p.1 .w), periodicToFin (p.1 .z))} := by
  rintro ⟨w, z⟩ hmem
  simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  change dualSquareProjection (cellWord p) w z ≠ 0 at hmem
  rw [dualSquareProjection_cellWord_apply] at hmem
  split_ifs at hmem with hcondition
  · rcases hcondition with ⟨_, hz, hw⟩
    simp only [Finset.mem_singleton]
    apply Prod.ext
    · exact (ZMod.finEquiv L).injective (by simpa using hw.symm)
    · exact (ZMod.finEquiv L).injective (by simpa using hz.symm)
  · exact (hmem rfl).elim

/-- A single plaquette changes at most one dual projected square cell. -/
theorem HammingWeight_dualSquareProjection_cellWord_le_one (p : Plaquette L) :
    HammingWeight
        ((fun q : Fin L × Fin L =>
          dualSquareProjection (L := L) (cellWord p) q.1 q.2) :
          Word (ZMod 2) (Fin L × Fin L)) ≤ 1 := by
  rw [HammingWeight_eq_card_hammingSupport]
  exact (Finset.card_le_card
    (hammingSupport_dualSquareProjection_cellWord_subset p)).trans (by simp)

/-- Over `ZMod 2`, a word of Hamming weight at most one is either zero or one
cell word.  This extracts the actual local increment rather than assuming a
chosen plaquette. -/
theorem eq_zero_or_eq_cellWord_of_HammingWeight_le_one
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (m : Word (ZMod 2) Index) (hm : HammingWeight m ≤ 1) :
    m = 0 ∨ ∃ i, m = cellWord i := by
  by_cases hm0 : m = 0
  · exact Or.inl hm0
  have hsupp : (hammingSupport m).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hweight : HammingWeight m = 0 := by
      simp [HammingWeight, hempty]
    exact hm0 ((HammingWeight_eq_zero_iff m).mp hweight)
  obtain ⟨i, hi⟩ := hsupp
  have hcard : (hammingSupport m).card ≤ 1 := by
    simpa [HammingWeight] using hm
  have hsupport : hammingSupport m = {i} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hi, ?_⟩
    intro j hj
    exact Finset.card_le_one.mp hcard j hj i hi
  refine Or.inr ⟨i, ?_⟩
  funext j
  by_cases hji : j = i
  · subst j
    have hne : m i ≠ 0 := by
      simpa [hammingSupport] using hi
    rw [PauliSymplectic.zmod_two_eq_one_of_ne_zero hne]
    simp [cellWord]
  · have hjnot : j ∉ hammingSupport m := by
      rw [hsupport]
      simp [hji]
    have hjzero : m j = 0 := by
      by_contra hj
      exact hjnot (by simpa [hammingSupport] using hj)
    simp [cellWord, hji, hjzero]

/-- Any weight-at-most-one plaquette word changes at most one primal projected
cell. -/
theorem oneCellStep_primalSquareProjection_of_HammingWeight_le_one
    (m : Word (ZMod 2) (Plaquette L)) (hm : HammingWeight m ≤ 1) :
    BinarySquare.OneCellStep (primalSquareProjection m) 0 := by
  rcases eq_zero_or_eq_cellWord_of_HammingWeight_le_one m hm with hm0 | ⟨p, rfl⟩
  · subst m
    change HammingWeight (fun q : Fin L × Fin L =>
      primalSquareProjection (L := L) 0 q.1 q.2 + 0) ≤ 1
    have hzero :
        (fun q : Fin L × Fin L =>
          primalSquareProjection (L := L) 0 q.1 q.2 + 0) =
          (0 : Word (ZMod 2) (Fin L × Fin L)) := by
      funext q
      simp [primalSquareProjection, wordPairing_apply]
    rw [hzero]
    simp
  · change HammingWeight (fun q : Fin L × Fin L =>
      primalSquareProjection (L := L) (cellWord p) q.1 q.2 + 0) ≤ 1
    simpa only [add_zero] using
      HammingWeight_primalSquareProjection_cellWord_le_one (L := L) p

/-- Any weight-at-most-one plaquette word changes at most one dual projected
cell. -/
theorem oneCellStep_dualSquareProjection_of_HammingWeight_le_one
    (m : Word (ZMod 2) (Plaquette L)) (hm : HammingWeight m ≤ 1) :
    BinarySquare.OneCellStep (dualSquareProjection m) 0 := by
  rcases eq_zero_or_eq_cellWord_of_HammingWeight_le_one m hm with hm0 | ⟨p, rfl⟩
  · subst m
    change HammingWeight (fun q : Fin L × Fin L =>
      dualSquareProjection (L := L) 0 q.1 q.2 + 0) ≤ 1
    have hzero :
        (fun q : Fin L × Fin L =>
          dualSquareProjection (L := L) 0 q.1 q.2 + 0) =
          (0 : Word (ZMod 2) (Fin L × Fin L)) := by
      funext q
      simp [dualSquareProjection, wordPairing_apply]
    rw [hzero]
    simp
  · change HammingWeight (fun q : Fin L × Fin L =>
      dualSquareProjection (L := L) (cellWord p) q.1 q.2 + 0) ≤ 1
    simpa only [add_zero] using
      HammingWeight_dualSquareProjection_cellWord_le_one (L := L) p

theorem primalSquareProjection_add
    (m₁ m₂ : Word (ZMod 2) (Plaquette L)) :
    primalSquareProjection (m₁ + m₂) =
      primalSquareProjection m₁ + primalSquareProjection m₂ := by
  funext y x
  simp [primalSquareProjection, wordPairing_apply, dotProduct,
    Finset.mul_sum, mul_add, Finset.sum_add_distrib]

theorem dualSquareProjection_add
    (m₁ m₂ : Word (ZMod 2) (Plaquette L)) :
    dualSquareProjection (m₁ + m₂) =
      dualSquareProjection m₁ + dualSquareProjection m₂ := by
  funext w z
  simp [dualSquareProjection, wordPairing_apply, dotProduct,
    add_mul, Finset.sum_add_distrib]

/-- Every representative of the primal membrane homology class has all-one
primal projection. -/
theorem primalSquareProjection_primalXYMembrane_add_boundary
    (z₀ w₀ : ZMod L) (c : Word (ZMod 2) (Cube L)) :
    primalSquareProjection (primalXYMembrane z₀ w₀ + boundary3 c) =
      fun _ _ => 1 := by
  funext y x
  rw [primalSquareProjection]
  have hboundary :
      wordPairing
          (dualXYMembrane (finToPeriodic x) (finToPeriodic y)) (boundary3 c) = 0 := by
    rw [← wordPairing_wordLinearMapTranspose]
    rw [transpose_boundary3_dualXYMembrane]
    simp
  rw [wordPairing_add_right_local, hboundary, add_zero,
    wordPairing_dual_primal]

/-- Every representative of the dual membrane cohomology class has all-one
dual projection. -/
theorem dualSquareProjection_dualXYMembrane_add_coboundary
    (x₀ y₀ : ZMod L) (e : Word (ZMod 2) (Link L)) :
    dualSquareProjection
        (dualXYMembrane x₀ y₀ + wordLinearMapTranspose boundary2 e) =
      fun _ _ => 1 := by
  funext w z
  rw [dualSquareProjection]
  have hboundary :
      wordPairing (wordLinearMapTranspose boundary2 e)
          (primalXYMembrane (finToPeriodic z) (finToPeriodic w)) = 0 := by
    rw [wordPairing_wordLinearMapTranspose]
    rw [boundary2_primalXYMembrane]
    simp
  rw [wordPairing_add_left_local, hboundary, add_zero]
  exact wordPairing_dual_primal _ _ _ _

private theorem shift_coord4_x_local (x y z w : ZMod L) :
    shift (coord4 x y z w) .x = coord4 (x + 1) y z w := by
  ext a
  cases a <;> simp [shift, coord4]

private theorem shift_coord4_y_local (x y z w : ZMod L) :
    shift (coord4 x y z w) .y = coord4 x (y + 1) z w := by
  ext a
  cases a <;> simp [shift, coord4]

private theorem shift_coord4_z_local (x y z w : ZMod L) :
    shift (coord4 x y z w) .z = coord4 x y (z + 1) w := by
  ext a
  cases a <;> simp [shift, coord4]

private theorem shift_coord4_w_local (x y z w : ZMod L) :
    shift (coord4 x y z w) .w = coord4 x y z (w + 1) := by
  ext a
  cases a <;> simp [shift, coord4]

private theorem add_one_eq_iff_eq_sub_one (a b : ZMod L) :
    a + 1 = b ↔ a = b - 1 :=
  eq_sub_iff_add_eq.symm

private theorem sum_add_one_local {M : Type*} [AddCommMonoid M]
    (f : ZMod L → M) :
    (∑ a : ZMod L, f (a + 1)) = ∑ a : ZMod L, f a :=
  Equiv.sum_comp (Equiv.addRight 1) f

/-- The periodic family of `y`-links between the two neighbouring dual
membrane slices at `x - 1` and `x`. -/
def primalHorizontalLinkFiber (x y : ZMod L) :
    Word (ZMod 2) (Link L) :=
  ∑ z : ZMod L, ∑ w : ZMod L, cellWord (coord4 x y z w, .y)

/-- The periodic family of `x`-links between the two neighbouring dual
membrane slices at `y - 1` and `y`. -/
def primalVerticalLinkFiber (x y : ZMod L) :
    Word (ZMod 2) (Link L) :=
  ∑ z : ZMod L, ∑ w : ZMod L, cellWord (coord4 x y z w, .x)

@[simp] theorem primalHorizontalLinkFiber_apply_coord4
    (x₀ y₀ x y z w : ZMod L) (a : Axis) :
    primalHorizontalLinkFiber x₀ y₀ (coord4 x y z w, a) =
      if a = .y ∧ x = x₀ ∧ y = y₀ then 1 else 0 := by
  by_cases ha : a = .y
  · subst a
    by_cases hx : x = x₀
    · subst x
      by_cases hy : y = y₀
      · subst y
        simp only [primalHorizontalLinkFiber, Finset.sum_apply]
        rw [Fintype.sum_eq_single z]
        · rw [Fintype.sum_eq_single w]
          · simp [cellWord]
          · intro b hbw
            simp [cellWord, Prod.ext_iff, hbw]
        · intro b hbz
          apply Fintype.sum_eq_zero
          intro d
          simp [cellWord, Prod.ext_iff, hbz]
      · simp [primalHorizontalLinkFiber, cellWord, Prod.ext_iff, hy]
    · simp [primalHorizontalLinkFiber, cellWord, Prod.ext_iff, hx]
  · simp [primalHorizontalLinkFiber, cellWord, Prod.ext_iff, ha]

@[simp] theorem primalVerticalLinkFiber_apply_coord4
    (x₀ y₀ x y z w : ZMod L) (a : Axis) :
    primalVerticalLinkFiber x₀ y₀ (coord4 x y z w, a) =
      if a = .x ∧ x = x₀ ∧ y = y₀ then 1 else 0 := by
  by_cases ha : a = .x
  · subst a
    by_cases hx : x = x₀
    · subst x
      by_cases hy : y = y₀
      · subst y
        simp only [primalVerticalLinkFiber, Finset.sum_apply]
        rw [Fintype.sum_eq_single z]
        · rw [Fintype.sum_eq_single w]
          · simp [cellWord]
          · intro b hbw
            simp [cellWord, Prod.ext_iff, hbw]
        · intro b hbz
          apply Fintype.sum_eq_zero
          intro d
          simp [cellWord, Prod.ext_iff, hbz]
      · simp [primalVerticalLinkFiber, cellWord, Prod.ext_iff, hy]
    · simp [primalVerticalLinkFiber, cellWord, Prod.ext_iff, hx]
  · simp [primalVerticalLinkFiber, cellWord, Prod.ext_iff, ha]

/-- The coboundary of a `y`-link fiber is the difference of its two adjacent
dual membrane slices. -/
theorem transpose_boundary2_primalHorizontalLinkFiber (x y : ZMod L) :
    wordLinearMapTranspose boundary2 (primalHorizontalLinkFiber x y) =
      dualXYMembrane x y + dualXYMembrane (x - 1) y := by
  ext p
  rcases p with ⟨c, q⟩
  rw [← coord4_components c]
  calc
    wordLinearMapTranspose boundary2 (primalHorizontalLinkFiber x y)
          (coord4 (c .x) (c .y) (c .z) (c .w), q) =
        wordPairing
          (wordLinearMapTranspose boundary2 (primalHorizontalLinkFiber x y))
          (cellWord (coord4 (c .x) (c .y) (c .z) (c .w), q)) := by
            symm
            apply wordPairing_cellWord_right_local
    _ = wordPairing (primalHorizontalLinkFiber x y)
          (boundary2 (cellWord (coord4 (c .x) (c .y) (c .z) (c .w), q))) :=
      wordPairing_wordLinearMapTranspose _ _ _
    _ = wordPairing (primalHorizontalLinkFiber x y)
          (plaquetteBoundary (coord4 (c .x) (c .y) (c .z) (c .w), q)) := by
      rw [boundary2, linearize_cellWord]
    _ = (dualXYMembrane x y + dualXYMembrane (x - 1) y)
          (coord4 (c .x) (c .y) (c .z) (c .w), q) := by
      cases q <;>
        simp only [plaquetteBoundary, wordPairing_add_right_local,
          wordPairing_cellWord_right_local] <;>
        simp [shift_coord4_x_local, shift_coord4_y_local,
          shift_coord4_z_local, shift_coord4_w_local,
          add_one_eq_iff_eq_sub_one] <;>
        try exact ZModModule.add_self _

/-- The coboundary of an `x`-link fiber is the difference of its two adjacent
dual membrane slices. -/
theorem transpose_boundary2_primalVerticalLinkFiber (x y : ZMod L) :
    wordLinearMapTranspose boundary2 (primalVerticalLinkFiber x y) =
      dualXYMembrane x y + dualXYMembrane x (y - 1) := by
  ext p
  rcases p with ⟨c, q⟩
  rw [← coord4_components c]
  calc
    wordLinearMapTranspose boundary2 (primalVerticalLinkFiber x y)
          (coord4 (c .x) (c .y) (c .z) (c .w), q) =
        wordPairing
          (wordLinearMapTranspose boundary2 (primalVerticalLinkFiber x y))
          (cellWord (coord4 (c .x) (c .y) (c .z) (c .w), q)) := by
            symm
            apply wordPairing_cellWord_right_local
    _ = wordPairing (primalVerticalLinkFiber x y)
          (boundary2 (cellWord (coord4 (c .x) (c .y) (c .z) (c .w), q))) :=
      wordPairing_wordLinearMapTranspose _ _ _
    _ = wordPairing (primalVerticalLinkFiber x y)
          (plaquetteBoundary (coord4 (c .x) (c .y) (c .z) (c .w), q)) := by
      rw [boundary2, linearize_cellWord]
    _ = (dualXYMembrane x y + dualXYMembrane x (y - 1))
          (coord4 (c .x) (c .y) (c .z) (c .w), q) := by
      cases q <;>
        simp only [plaquetteBoundary, wordPairing_add_right_local,
          wordPairing_cellWord_right_local] <;>
        simp [shift_coord4_x_local, shift_coord4_y_local,
          shift_coord4_z_local, shift_coord4_w_local,
          add_one_eq_iff_eq_sub_one] <;>
        try exact ZModModule.add_self _

private theorem finToPeriodic_openSucc (i : Fin (L - 1)) :
    finToPeriodic (⟨i.1 + 1, by omega⟩ : Fin L) =
      finToPeriodic (⟨i.1, by omega⟩ : Fin L) + 1 := by
  let j : Fin L := ⟨i.1, by omega⟩
  have hiL : i.1 + 1 < L := by omega
  have hadd : j + 1 = (⟨i.1 + 1, by omega⟩ : Fin L) := by
    apply Fin.ext
    rw [Fin.add_def]
    simpa [j] using Nat.mod_eq_of_lt hiL
  calc
    (ZMod.finEquiv L) ⟨i.1 + 1, by omega⟩ =
        (ZMod.finEquiv L) (j + 1) := by rw [hadd]
    _ = (ZMod.finEquiv L) j + (ZMod.finEquiv L) (1 : Fin L) :=
      (ZMod.finEquiv L).map_add j 1
    _ = (ZMod.finEquiv L) j + 1 :=
      congrArg (fun t : ZMod L => (ZMod.finEquiv L) j + t)
        (map_one (ZMod.finEquiv L))
    _ = (ZMod.finEquiv L) ⟨i.1, by omega⟩ + 1 := rfl

/-- A horizontal projected edge is the parity of the primal defect loop on
the corresponding `y`-link fiber. -/
theorem primalHorizontalDerivative_eq_fiberPairing
    (m : Word (ZMod 2) (Plaquette L)) (y : Fin L) (i : Fin (L - 1)) :
    BinarySquare.horizontalDerivative (primalSquareProjection m) y i =
      wordPairing
        (primalHorizontalLinkFiber
          (finToPeriodic (⟨i.1 + 1, by omega⟩ : Fin L))
          (finToPeriodic y))
        (primalDefectLoop m) := by
  rw [primalDefectLoop, ← wordPairing_wordLinearMapTranspose]
  rw [transpose_boundary2_primalHorizontalLinkFiber,
    wordPairing_add_left_local]
  have hback :
      finToPeriodic (⟨i.1 + 1, by omega⟩ : Fin L) - 1 =
        finToPeriodic (⟨i.1, by omega⟩ : Fin L) := by
    rw [finToPeriodic_openSucc]
    ring
  unfold BinarySquare.horizontalDerivative primalSquareProjection
  rw [hback]

/-- A vertical projected edge is the parity of the primal defect loop on
the corresponding `x`-link fiber. -/
theorem primalVerticalDerivative_eq_fiberPairing
    (m : Word (ZMod 2) (Plaquette L)) (x : Fin L) (i : Fin (L - 1)) :
    BinarySquare.verticalDerivative (primalSquareProjection m) x i =
      wordPairing
        (primalVerticalLinkFiber
          (finToPeriodic x)
          (finToPeriodic (⟨i.1 + 1, by omega⟩ : Fin L)))
        (primalDefectLoop m) := by
  rw [primalDefectLoop, ← wordPairing_wordLinearMapTranspose]
  rw [transpose_boundary2_primalVerticalLinkFiber,
    wordPairing_add_left_local]
  have hback :
      finToPeriodic (⟨i.1 + 1, by omega⟩ : Fin L) - 1 =
        finToPeriodic (⟨i.1, by omega⟩ : Fin L) := by
    rw [finToPeriodic_openSucc]
    ring
  unfold BinarySquare.verticalDerivative primalSquareProjection
  rw [hback]

private def primalHorizontalOpenFiber (q : Fin L × Fin (L - 1)) :
    Word (ZMod 2) (Link L) :=
  primalHorizontalLinkFiber
    (finToPeriodic (⟨q.2.1 + 1, by omega⟩ : Fin L))
    (finToPeriodic q.1)

private def primalVerticalOpenFiber (q : Fin L × Fin (L - 1)) :
    Word (ZMod 2) (Link L) :=
  primalVerticalLinkFiber
    (finToPeriodic q.1)
    (finToPeriodic (⟨q.2.1 + 1, by omega⟩ : Fin L))

private theorem pairwise_disjoint_primalHorizontalOpenFiber :
    Pairwise fun p q : Fin L × Fin (L - 1) =>
      Disjoint (hammingSupport (primalHorizontalOpenFiber p))
        (hammingSupport (primalHorizontalOpenFiber q)) := by
  intro p q hpq
  rw [Finset.disjoint_left]
  intro e hep heq
  rcases e with ⟨c, a⟩
  rw [← coord4_components c] at hep heq
  simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hep heq
  have hpcoord :
      a = .y ∧ c .x =
        finToPeriodic (⟨p.2.1 + 1, by omega⟩ : Fin L) ∧
        c .y = finToPeriodic p.1 := by
    simpa [hammingSupport, primalHorizontalOpenFiber] using hep
  have hqcoord :
      a = .y ∧ c .x =
        finToPeriodic (⟨q.2.1 + 1, by omega⟩ : Fin L) ∧
        c .y = finToPeriodic q.1 := by
    simpa [hammingSupport, primalHorizontalOpenFiber] using heq
  apply hpq
  apply Prod.ext
  · exact (ZMod.finEquiv L).injective (hpcoord.2.2.symm.trans hqcoord.2.2)
  · apply Fin.ext
    have hnext := (ZMod.finEquiv L).injective
      (hpcoord.2.1.symm.trans hqcoord.2.1)
    have hval := congrArg Fin.val hnext
    have hval' : p.2.1 + 1 = q.2.1 + 1 := by simpa using hval
    omega

private theorem pairwise_disjoint_primalVerticalOpenFiber :
    Pairwise fun p q : Fin L × Fin (L - 1) =>
      Disjoint (hammingSupport (primalVerticalOpenFiber p))
        (hammingSupport (primalVerticalOpenFiber q)) := by
  intro p q hpq
  rw [Finset.disjoint_left]
  intro e hep heq
  rcases e with ⟨c, a⟩
  rw [← coord4_components c] at hep heq
  simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hep heq
  have hpcoord :
      a = .x ∧ c .x = finToPeriodic p.1 ∧
        c .y = finToPeriodic (⟨p.2.1 + 1, by omega⟩ : Fin L) := by
    simpa [hammingSupport, primalVerticalOpenFiber] using hep
  have hqcoord :
      a = .x ∧ c .x = finToPeriodic q.1 ∧
        c .y = finToPeriodic (⟨q.2.1 + 1, by omega⟩ : Fin L) := by
    simpa [hammingSupport, primalVerticalOpenFiber] using heq
  apply hpq
  apply Prod.ext
  · exact (ZMod.finEquiv L).injective (hpcoord.2.1.symm.trans hqcoord.2.1)
  · apply Fin.ext
    have hnext := (ZMod.finEquiv L).injective
      (hpcoord.2.2.symm.trans hqcoord.2.2)
    have hval := congrArg Fin.val hnext
    have hval' : p.2.1 + 1 = q.2.1 + 1 := by simpa using hval
    omega

private theorem HammingWeight_uncurry_eq_sum
    {A B : Type*} [Fintype A] [Fintype B] (w : A → B → ZMod 2) :
    HammingWeight (fun q : A × B => w q.1 q.2) =
      ∑ a : A, HammingWeight (w a) := by
  simp only [HammingWeight, hammingSupport, Finset.card_filter,
    Fintype.sum_prod_type]

theorem primalHorizontalOpenBoundary_le_loopLength
    (m : Word (ZMod 2) (Plaquette L)) :
    HammingWeight (fun q : Fin L × Fin (L - 1) =>
      BinarySquare.horizontalDerivative (primalSquareProjection m) q.1 q.2) ≤
      primalLoopLength m := by
  rw [primalLoopLength]
  simpa only [primalHorizontalOpenFiber,
    primalHorizontalDerivative_eq_fiberPairing] using
    (HammingWeight_pairings_le_of_pairwise_disjoint
      primalHorizontalOpenFiber (primalDefectLoop m)
      pairwise_disjoint_primalHorizontalOpenFiber)

theorem primalVerticalOpenBoundary_le_loopLength
    (m : Word (ZMod 2) (Plaquette L)) :
    HammingWeight (fun q : Fin L × Fin (L - 1) =>
      BinarySquare.verticalDerivative (primalSquareProjection m) q.1 q.2) ≤
      primalLoopLength m := by
  rw [primalLoopLength]
  simpa only [primalVerticalOpenFiber,
    primalVerticalDerivative_eq_fiberPairing] using
    (HammingWeight_pairings_le_of_pairwise_disjoint
      primalVerticalOpenFiber (primalDefectLoop m)
      pairwise_disjoint_primalVerticalOpenFiber)

/-- The open edge boundary of the primal square projection is controlled by
twice the actual primal syndrome-loop length. -/
theorem primal_openBoundaryLength_le_two_mul_loopLength
    (m : Word (ZMod 2) (Plaquette L)) :
    BinarySquare.openBoundaryLength (primalSquareProjection m) ≤
      2 * primalLoopLength m := by
  rw [BinarySquare.openBoundaryLength,
    ← HammingWeight_uncurry_eq_sum,
    ← HammingWeight_uncurry_eq_sum]
  have hh := primalHorizontalOpenBoundary_le_loopLength m
  have hv := primalVerticalOpenBoundary_le_loopLength m
  omega

/-- The periodic family of `xyz` cubes between neighbouring primal membrane
slices in the `z` direction. -/
def dualHorizontalCubeFiber (z w : ZMod L) :
    Word (ZMod 2) (Cube L) :=
  ∑ x : ZMod L, ∑ y : ZMod L, cellWord (coord4 x y z w, .xyz)

/-- The periodic family of `xyw` cubes between neighbouring primal membrane
slices in the `w` direction. -/
def dualVerticalCubeFiber (z w : ZMod L) :
    Word (ZMod 2) (Cube L) :=
  ∑ x : ZMod L, ∑ y : ZMod L, cellWord (coord4 x y z w, .xyw)

@[simp] theorem dualHorizontalCubeFiber_apply_coord4
    (z₀ w₀ x y z w : ZMod L) (v : Volume) :
    dualHorizontalCubeFiber z₀ w₀ (coord4 x y z w, v) =
      if v = .xyz ∧ z = z₀ ∧ w = w₀ then 1 else 0 := by
  by_cases hv : v = .xyz
  · subst v
    by_cases hz : z = z₀
    · subst z
      by_cases hw : w = w₀
      · subst w
        simp only [dualHorizontalCubeFiber, Finset.sum_apply]
        rw [Fintype.sum_eq_single x]
        · rw [Fintype.sum_eq_single y]
          · simp [cellWord]
          · intro b hby
            simp [cellWord, Prod.ext_iff, hby]
        · intro a hax
          apply Fintype.sum_eq_zero
          intro b
          simp [cellWord, Prod.ext_iff, hax]
      · simp [dualHorizontalCubeFiber, cellWord, Prod.ext_iff, hw]
    · simp [dualHorizontalCubeFiber, cellWord, Prod.ext_iff, hz]
  · simp [dualHorizontalCubeFiber, cellWord, Prod.ext_iff, hv]

@[simp] theorem dualVerticalCubeFiber_apply_coord4
    (z₀ w₀ x y z w : ZMod L) (v : Volume) :
    dualVerticalCubeFiber z₀ w₀ (coord4 x y z w, v) =
      if v = .xyw ∧ z = z₀ ∧ w = w₀ then 1 else 0 := by
  by_cases hv : v = .xyw
  · subst v
    by_cases hz : z = z₀
    · subst z
      by_cases hw : w = w₀
      · subst w
        simp only [dualVerticalCubeFiber, Finset.sum_apply]
        rw [Fintype.sum_eq_single x]
        · rw [Fintype.sum_eq_single y]
          · simp [cellWord]
          · intro b hby
            simp [cellWord, Prod.ext_iff, hby]
        · intro a hax
          apply Fintype.sum_eq_zero
          intro b
          simp [cellWord, Prod.ext_iff, hax]
      · simp [dualVerticalCubeFiber, cellWord, Prod.ext_iff, hw]
    · simp [dualVerticalCubeFiber, cellWord, Prod.ext_iff, hz]
  · simp [dualVerticalCubeFiber, cellWord, Prod.ext_iff, hv]

/-- An `xyz` cube fiber fills precisely the gap between two adjacent primal
membrane slices. -/
theorem boundary3_dualHorizontalCubeFiber (z w : ZMod L) :
    boundary3 (dualHorizontalCubeFiber z w) =
      primalXYMembrane z w + primalXYMembrane (z + 1) w := by
  simp only [dualHorizontalCubeFiber, map_sum, boundary3,
    linearize_cellWord, cubeBoundary, shift_coord4_x_local,
    shift_coord4_y_local, shift_coord4_z_local, Finset.sum_add_distrib]
  rw [show (∑ x : ZMod L, ∑ y : ZMod L,
      cellWord (coord4 x (y + 1) z w, Plane.xz)) =
      ∑ x : ZMod L, ∑ y : ZMod L,
        cellWord (coord4 x y z w, Plane.xz) by
      apply Fintype.sum_congr
      intro x
      exact sum_add_one_local
        (fun y : ZMod L => cellWord (coord4 x y z w, Plane.xz))]
  rw [show (∑ x : ZMod L, ∑ y : ZMod L,
      cellWord (coord4 (x + 1) y z w, Plane.yz)) =
      ∑ x : ZMod L, ∑ y : ZMod L,
        cellWord (coord4 x y z w, Plane.yz) by
      exact sum_add_one_local
        (fun x : ZMod L => ∑ y : ZMod L,
          cellWord (coord4 x y z w, Plane.yz))]
  simp [primalXYMembrane, add_assoc]

/-- An `xyw` cube fiber fills precisely the gap between two adjacent primal
membrane slices. -/
theorem boundary3_dualVerticalCubeFiber (z w : ZMod L) :
    boundary3 (dualVerticalCubeFiber z w) =
      primalXYMembrane z w + primalXYMembrane z (w + 1) := by
  simp only [dualVerticalCubeFiber, map_sum, boundary3,
    linearize_cellWord, cubeBoundary, shift_coord4_x_local,
    shift_coord4_y_local, shift_coord4_w_local, Finset.sum_add_distrib]
  rw [show (∑ x : ZMod L, ∑ y : ZMod L,
      cellWord (coord4 x (y + 1) z w, Plane.xw)) =
      ∑ x : ZMod L, ∑ y : ZMod L,
        cellWord (coord4 x y z w, Plane.xw) by
      apply Fintype.sum_congr
      intro x
      exact sum_add_one_local
        (fun y : ZMod L => cellWord (coord4 x y z w, Plane.xw))]
  rw [show (∑ x : ZMod L, ∑ y : ZMod L,
      cellWord (coord4 (x + 1) y z w, Plane.yw)) =
      ∑ x : ZMod L, ∑ y : ZMod L,
        cellWord (coord4 x y z w, Plane.yw) by
      exact sum_add_one_local
        (fun x : ZMod L => ∑ y : ZMod L,
          cellWord (coord4 x y z w, Plane.yw))]
  simp [primalXYMembrane, add_assoc]

/-- A horizontal dual projected edge is the parity of the dual defect loop on
the corresponding `xyz` cube fiber. -/
theorem dualHorizontalDerivative_eq_fiberPairing
    (m : Word (ZMod 2) (Plaquette L)) (w : Fin L) (i : Fin (L - 1)) :
    BinarySquare.horizontalDerivative (dualSquareProjection m) w i =
      wordPairing
        (dualHorizontalCubeFiber
          (finToPeriodic (⟨i.1, by omega⟩ : Fin L))
          (finToPeriodic w))
        (dualDefectLoop m) := by
  rw [dualDefectLoop, wordPairing_apply, dotProduct_comm,
    ← wordPairing_apply, wordPairing_wordLinearMapTranspose]
  rw [boundary3_dualHorizontalCubeFiber, wordPairing_add_right_local]
  unfold BinarySquare.horizontalDerivative dualSquareProjection
  rw [finToPeriodic_openSucc]
  ac_rfl

/-- A vertical dual projected edge is the parity of the dual defect loop on
the corresponding `xyw` cube fiber. -/
theorem dualVerticalDerivative_eq_fiberPairing
    (m : Word (ZMod 2) (Plaquette L)) (z : Fin L) (i : Fin (L - 1)) :
    BinarySquare.verticalDerivative (dualSquareProjection m) z i =
      wordPairing
        (dualVerticalCubeFiber
          (finToPeriodic z)
          (finToPeriodic (⟨i.1, by omega⟩ : Fin L)))
        (dualDefectLoop m) := by
  rw [dualDefectLoop, wordPairing_apply, dotProduct_comm,
    ← wordPairing_apply, wordPairing_wordLinearMapTranspose]
  rw [boundary3_dualVerticalCubeFiber, wordPairing_add_right_local]
  unfold BinarySquare.verticalDerivative dualSquareProjection
  rw [finToPeriodic_openSucc]
  ac_rfl

private def dualHorizontalOpenFiber (q : Fin L × Fin (L - 1)) :
    Word (ZMod 2) (Cube L) :=
  dualHorizontalCubeFiber
    (finToPeriodic (⟨q.2.1, by omega⟩ : Fin L))
    (finToPeriodic q.1)

private def dualVerticalOpenFiber (q : Fin L × Fin (L - 1)) :
    Word (ZMod 2) (Cube L) :=
  dualVerticalCubeFiber
    (finToPeriodic q.1)
    (finToPeriodic (⟨q.2.1, by omega⟩ : Fin L))

private theorem pairwise_disjoint_dualHorizontalOpenFiber :
    Pairwise fun p q : Fin L × Fin (L - 1) =>
      Disjoint (hammingSupport (dualHorizontalOpenFiber p))
        (hammingSupport (dualHorizontalOpenFiber q)) := by
  intro p q hpq
  rw [Finset.disjoint_left]
  intro c hcp hcq
  rcases c with ⟨r, v⟩
  rw [← coord4_components r] at hcp hcq
  simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hcp hcq
  have hpcoord :
      v = .xyz ∧ r .z =
        finToPeriodic (⟨p.2.1, by omega⟩ : Fin L) ∧
        r .w = finToPeriodic p.1 := by
    simpa [hammingSupport, dualHorizontalOpenFiber] using hcp
  have hqcoord :
      v = .xyz ∧ r .z =
        finToPeriodic (⟨q.2.1, by omega⟩ : Fin L) ∧
        r .w = finToPeriodic q.1 := by
    simpa [hammingSupport, dualHorizontalOpenFiber] using hcq
  apply hpq
  apply Prod.ext
  · exact (ZMod.finEquiv L).injective (hpcoord.2.2.symm.trans hqcoord.2.2)
  · apply Fin.ext
    have hfin := (ZMod.finEquiv L).injective
      (hpcoord.2.1.symm.trans hqcoord.2.1)
    simpa using congrArg Fin.val hfin

private theorem pairwise_disjoint_dualVerticalOpenFiber :
    Pairwise fun p q : Fin L × Fin (L - 1) =>
      Disjoint (hammingSupport (dualVerticalOpenFiber p))
        (hammingSupport (dualVerticalOpenFiber q)) := by
  intro p q hpq
  rw [Finset.disjoint_left]
  intro c hcp hcq
  rcases c with ⟨r, v⟩
  rw [← coord4_components r] at hcp hcq
  simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hcp hcq
  have hpcoord :
      v = .xyw ∧ r .z = finToPeriodic p.1 ∧
        r .w = finToPeriodic (⟨p.2.1, by omega⟩ : Fin L) := by
    simpa [hammingSupport, dualVerticalOpenFiber] using hcp
  have hqcoord :
      v = .xyw ∧ r .z = finToPeriodic q.1 ∧
        r .w = finToPeriodic (⟨q.2.1, by omega⟩ : Fin L) := by
    simpa [hammingSupport, dualVerticalOpenFiber] using hcq
  apply hpq
  apply Prod.ext
  · exact (ZMod.finEquiv L).injective (hpcoord.2.1.symm.trans hqcoord.2.1)
  · apply Fin.ext
    have hfin := (ZMod.finEquiv L).injective
      (hpcoord.2.2.symm.trans hqcoord.2.2)
    simpa using congrArg Fin.val hfin

theorem dualHorizontalOpenBoundary_le_loopLength
    (m : Word (ZMod 2) (Plaquette L)) :
    HammingWeight (fun q : Fin L × Fin (L - 1) =>
      BinarySquare.horizontalDerivative (dualSquareProjection m) q.1 q.2) ≤
      dualLoopLength m := by
  rw [dualLoopLength]
  simpa only [dualHorizontalOpenFiber,
    dualHorizontalDerivative_eq_fiberPairing] using
    (HammingWeight_pairings_le_of_pairwise_disjoint
      dualHorizontalOpenFiber (dualDefectLoop m)
      pairwise_disjoint_dualHorizontalOpenFiber)

theorem dualVerticalOpenBoundary_le_loopLength
    (m : Word (ZMod 2) (Plaquette L)) :
    HammingWeight (fun q : Fin L × Fin (L - 1) =>
      BinarySquare.verticalDerivative (dualSquareProjection m) q.1 q.2) ≤
      dualLoopLength m := by
  rw [dualLoopLength]
  simpa only [dualVerticalOpenFiber,
    dualVerticalDerivative_eq_fiberPairing] using
    (HammingWeight_pairings_le_of_pairwise_disjoint
      dualVerticalOpenFiber (dualDefectLoop m)
      pairwise_disjoint_dualVerticalOpenFiber)

/-- The open edge boundary of the dual square projection is controlled by
twice the actual dual syndrome-loop length. -/
theorem dual_openBoundaryLength_le_two_mul_loopLength
    (m : Word (ZMod 2) (Plaquette L)) :
    BinarySquare.openBoundaryLength (dualSquareProjection m) ≤
      2 * dualLoopLength m := by
  rw [BinarySquare.openBoundaryLength,
    ← HammingWeight_uncurry_eq_sum,
    ← HammingWeight_uncurry_eq_sum]
  have hh := dualHorizontalOpenBoundary_le_loopLength m
  have hv := dualVerticalOpenBoundary_le_loopLength m
  omega

/-- The selected toric syndrome of an arbitrary Pauli splits into the primal
loop of its Z component and the dual loop of its X component. -/
theorem toricSyndrome_eq_componentDefectLoops (E : Binary (Plaquette L)) :
    stabilizerSyndrome (toricGenerator (L := L)) E =
      Sum.elim (primalDefectLoop E.vector.zPart)
        (dualDefectLoop E.vector.xPart) := by
  funext j
  cases j with
  | inl e =>
      simp [stabilizerSyndrome, stabilizerSyndromeBit, symplecticForm,
        primalDefectLoop]
      change wordPairing E.vector.zPart
        (wordLinearMapTranspose boundary2 (Pi.single e 1)) =
          boundary2 E.vector.zPart e
      rw [wordPairing_apply, dotProduct_comm, ← wordPairing_apply,
        wordPairing_wordLinearMapTranspose]
      simp [wordPairing_apply]
  | inr c =>
      simp [stabilizerSyndrome, stabilizerSyndromeBit, symplecticForm,
        dualDefectLoop]
      change wordPairing E.vector.xPart (boundary3 (Pi.single c 1)) =
        wordLinearMapTranspose boundary3 E.vector.xPart c
      rw [← wordPairing_wordLinearMapTranspose]
      simp [wordPairing_apply, dotProduct_comm]

private theorem syndromeWeight_eq_HammingWeight_syndrome
    {Index Check : Type*} [Fintype Index] [DecidableEq Index] [Fintype Check]
    (H : StabilizerCode.LocalStabilizerHamiltonian
      (ι := Index) (κ := Check)) (E : Binary Index) :
    H.syndromeWeight E = HammingWeight (stabilizerSyndrome H.generators E) := by
  rw [StabilizerCode.LocalStabilizerHamiltonian.syndromeWeight,
    HammingWeight]
  congr 1
  ext j
  simp only [StabilizerCode.LocalStabilizerHamiltonian.syndromeSupport,
    hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hj
    change stabilizerSyndrome H.generators E j ≠ 0
    rw [hj]
    exact one_ne_zero
  · exact PauliSymplectic.zmod_two_eq_one_of_ne_zero

private theorem HammingWeight_left_le_sum_elim
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (x : Word (ZMod 2) A) (y : Word (ZMod 2) B) :
    HammingWeight x ≤ HammingWeight (Sum.elim x y) := by
  rw [HammingWeight, HammingWeight]
  let emb : A ↪ Sum A B := ⟨Sum.inl, Sum.inl_injective⟩
  have hsubset : (hammingSupport x).map emb ⊆
      hammingSupport (Sum.elim x y) := by
    intro j hj
    rcases Finset.mem_map.mp hj with ⟨a, ha, rfl⟩
    simpa [hammingSupport, emb] using ha
  simpa [emb] using Finset.card_le_card hsubset

private theorem HammingWeight_right_le_sum_elim
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (x : Word (ZMod 2) A) (y : Word (ZMod 2) B) :
    HammingWeight y ≤ HammingWeight (Sum.elim x y) := by
  rw [HammingWeight, HammingWeight]
  let emb : B ↪ Sum A B := ⟨Sum.inr, Sum.inr_injective⟩
  have hsubset : (hammingSupport y).map emb ⊆
      hammingSupport (Sum.elim x y) := by
    intro j hj
    rcases Finset.mem_map.mp hj with ⟨b, hb, rfl⟩
    simpa [hammingSupport, emb] using hb
  simpa [emb] using Finset.card_le_card hsubset

/-- The full Pauli energy dominates twice the primal loop length of its Z
component, even when an X component is also present. -/
theorem two_mul_primalLoopLength_le_btExcessEnergy
    (E : Binary (Plaquette L)) :
    2 * primalLoopLength E.vector.zPart ≤
      (toricHamiltonian (L := L)).btExcessEnergy E := by
  rw [StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_eq_two_mul_syndromeWeight,
    syndromeWeight_eq_HammingWeight_syndrome,
    toricHamiltonian_generators, toricSyndrome_eq_componentDefectLoops]
  exact Nat.mul_le_mul_left 2
    (HammingWeight_left_le_sum_elim
      (primalDefectLoop E.vector.zPart) (dualDefectLoop E.vector.xPart))

/-- The full Pauli energy dominates twice the dual loop length of its X
component, even when a Z component is also present. -/
theorem two_mul_dualLoopLength_le_btExcessEnergy
    (E : Binary (Plaquette L)) :
    2 * dualLoopLength E.vector.xPart ≤
      (toricHamiltonian (L := L)).btExcessEnergy E := by
  rw [StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_eq_two_mul_syndromeWeight,
    syndromeWeight_eq_HammingWeight_syndrome,
    toricHamiltonian_generators, toricSyndrome_eq_componentDefectLoops]
  exact Nat.mul_le_mul_left 2
    (HammingWeight_right_le_sum_elim
      (primalDefectLoop E.vector.zPart) (dualDefectLoop E.vector.xPart))

/-- A path ends in the chosen nontrivial primal membrane sector when its Z
component represents a translated primal membrane modulo a 3-boundary.  Its X
component and binary phase are unrestricted. -/
def HasPrimalMembraneEndpoint
    (γ : PauliErrorPath (ι := Plaquette L)) : Prop :=
  ∃ z w : ZMod L, ∃ c : Word (ZMod 2) (Cube L),
    γ.endpoint.vector.zPart = primalXYMembrane z w + boundary3 c

/-- A path ends in the chosen nontrivial dual membrane sector when its X
component represents a translated dual membrane modulo a link coboundary.  Its
Z component and binary phase are unrestricted. -/
def HasDualMembraneEndpoint
    (γ : PauliErrorPath (ι := Plaquette L)) : Prop :=
  ∃ x y : ZMod L, ∃ e : Word (ZMod 2) (Link L),
    γ.endpoint.vector.xPart =
      dualXYMembrane x y + wordLinearMapTranspose boundary2 e

private theorem oneCellStep_add_self_of_oneCellStep_zero
    (g d : BinarySquare.Grid L) (h : BinarySquare.OneCellStep d 0) :
    BinarySquare.OneCellStep (g + d) g := by
  unfold BinarySquare.OneCellStep BinarySquare.difference at h ⊢
  have heq :
      (fun p : Fin L × Fin L =>
        (g + d) p.1 p.2 + g p.1 p.2) =
      (fun p : Fin L × Fin L => d p.1 p.2 + 0) := by
    funext p
    change (g p.1 p.2 + d p.1 p.2) + g p.1 p.2 = d p.1 p.2 + 0
    calc
      (g p.1 p.2 + d p.1 p.2) + g p.1 p.2 =
          d p.1 p.2 + (g p.1 p.2 + g p.1 p.2) := by ac_rfl
      _ = d p.1 p.2 + 0 := by rw [ZModModule.add_self]
  rw [heq]
  exact h

/-- Consecutive path states differ by at most one cell in the primal square
projection. -/
theorem oneCellStep_primalSquareProjection_stateAt_succ
    (γ : PauliErrorPath (ι := Plaquette L)) (n : Nat)
    (hn : n < γ.increments.length) :
    BinarySquare.OneCellStep
      (primalSquareProjection (γ.stateAt (n + 1)).vector.zPart)
      (primalSquareProjection (γ.stateAt n).vector.zPart) := by
  have hcomponent :
      HammingWeight γ.increments[n].vector.zPart ≤ 1 :=
    (hammingWeight_zPart_le_weight γ.increments[n]).trans
      (γ.getElem_weight_le_one n hn)
  have hlocal := oneCellStep_primalSquareProjection_of_HammingWeight_le_one
    γ.increments[n].vector.zPart hcomponent
  rw [γ.stateAt_succ n hn]
  change BinarySquare.OneCellStep
    (primalSquareProjection
      ((γ.stateAt n).vector.zPart + γ.increments[n].vector.zPart))
    (primalSquareProjection (γ.stateAt n).vector.zPart)
  rw [primalSquareProjection_add]
  exact oneCellStep_add_self_of_oneCellStep_zero _ _ hlocal

/-- Consecutive path states differ by at most one cell in the dual square
projection. -/
theorem oneCellStep_dualSquareProjection_stateAt_succ
    (γ : PauliErrorPath (ι := Plaquette L)) (n : Nat)
    (hn : n < γ.increments.length) :
    BinarySquare.OneCellStep
      (dualSquareProjection (γ.stateAt (n + 1)).vector.xPart)
      (dualSquareProjection (γ.stateAt n).vector.xPart) := by
  have hcomponent :
      HammingWeight γ.increments[n].vector.xPart ≤ 1 :=
    (hammingWeight_xPart_le_weight γ.increments[n]).trans
      (γ.getElem_weight_le_one n hn)
  have hlocal := oneCellStep_dualSquareProjection_of_HammingWeight_le_one
    γ.increments[n].vector.xPart hcomponent
  rw [γ.stateAt_succ n hn]
  change BinarySquare.OneCellStep
    (dualSquareProjection
      ((γ.stateAt n).vector.xPart + γ.increments[n].vector.xPart))
    (dualSquareProjection (γ.stateAt n).vector.xPart)
  rw [dualSquareProjection_add]
  exact oneCellStep_add_self_of_oneCellStep_zero _ _ hlocal

/-- Number of completely filled rows in the primal projection of a path
state. -/
def primalFullRowCount
    (γ : PauliErrorPath (ι := Plaquette L)) (n : Nat) : Nat :=
  (BinarySquare.fullRows
    (primalSquareProjection (γ.stateAt n).vector.zPart)).card

/-- Number of completely filled rows in the dual projection of a path state. -/
def dualFullRowCount
    (γ : PauliErrorPath (ι := Plaquette L)) (n : Nat) : Nat :=
  (BinarySquare.fullRows
    (dualSquareProjection (γ.stateAt n).vector.xPart)).card

@[simp] theorem primalFullRowCount_zero
    (γ : PauliErrorPath (ι := Plaquette L)) :
    primalFullRowCount γ 0 = 0 := by
  rw [primalFullRowCount, γ.stateAt_zero]
  simp [BinarySquare.fullRows, primalSquareProjection,
    wordPairing_apply, binaryOne]

@[simp] theorem dualFullRowCount_zero
    (γ : PauliErrorPath (ι := Plaquette L)) :
    dualFullRowCount γ 0 = 0 := by
  rw [dualFullRowCount, γ.stateAt_zero]
  simp [BinarySquare.fullRows, dualSquareProjection,
    wordPairing_apply, binaryOne]

theorem primalFullRowCount_endpoint
    (γ : PauliErrorPath (ι := Plaquette L))
    (hendpoint : HasPrimalMembraneEndpoint γ) :
    primalFullRowCount γ γ.increments.length = L := by
  rcases hendpoint with ⟨z, w, c, hendpoint⟩
  rw [primalFullRowCount, γ.stateAt_length, hendpoint,
    primalSquareProjection_primalXYMembrane_add_boundary]
  simp [BinarySquare.fullRows]

theorem dualFullRowCount_endpoint
    (γ : PauliErrorPath (ι := Plaquette L))
    (hendpoint : HasDualMembraneEndpoint γ) :
    dualFullRowCount γ γ.increments.length = L := by
  rcases hendpoint with ⟨x, y, e, hendpoint⟩
  rw [dualFullRowCount, γ.stateAt_length, hendpoint,
    dualSquareProjection_dualXYMembrane_add_coboundary]
  simp [BinarySquare.fullRows]

theorem primalFullRowCount_dist_succ_le_one
    (γ : PauliErrorPath (ι := Plaquette L)) (n : Nat)
    (hn : n < γ.increments.length) :
    Nat.dist (primalFullRowCount γ (n + 1))
      (primalFullRowCount γ n) ≤ 1 := by
  exact BinarySquare.fullRows_card_dist_le_one_of_oneCellStep _ _
    (oneCellStep_primalSquareProjection_stateAt_succ γ n hn)

theorem dualFullRowCount_dist_succ_le_one
    (γ : PauliErrorPath (ι := Plaquette L)) (n : Nat)
    (hn : n < γ.increments.length) :
    Nat.dist (dualFullRowCount γ (n + 1))
      (dualFullRowCount γ n) ≤ 1 := by
  exact BinarySquare.fullRows_card_dist_le_one_of_oneCellStep _ _
    (oneCellStep_dualSquareProjection_stateAt_succ γ n hn)

/-- Every path to the primal membrane sector contains a state whose primal
projection has exactly half of its rows filled. -/
theorem exists_primal_half_filled_state
    (γ : PauliErrorPath (ι := Plaquette L))
    (hendpoint : HasPrimalMembraneEndpoint γ) :
    ∃ n ≤ γ.increments.length, primalFullRowCount γ n = L / 2 := by
  apply BinarySquare.exists_eq_of_nat_walk
    (primalFullRowCount γ) γ.increments.length (L / 2)
  · simp
  · rw [primalFullRowCount_endpoint γ hendpoint]
    omega
  · intro n hn
    exact primalFullRowCount_dist_succ_le_one γ n hn

/-- Every path to the dual membrane sector contains a state whose dual
projection has exactly half of its rows filled. -/
theorem exists_dual_half_filled_state
    (γ : PauliErrorPath (ι := Plaquette L))
    (hendpoint : HasDualMembraneEndpoint γ) :
    ∃ n ≤ γ.increments.length, dualFullRowCount γ n = L / 2 := by
  apply BinarySquare.exists_eq_of_nat_walk
    (dualFullRowCount γ) γ.increments.length (L / 2)
  · simp
  · rw [dualFullRowCount_endpoint γ hendpoint]
    omega
  · intro n hn
    exact dualFullRowCount_dist_succ_le_one γ n hn

/-- Every path to the primal sector crosses a state whose actual primal
defect-loop length is linear in `L`, with the explicit finite-size constant
`L / 2 ≤ 2 * loopLength`. -/
theorem exists_primal_large_defect_loop
    (γ : PauliErrorPath (ι := Plaquette L))
    (hendpoint : HasPrimalMembraneEndpoint γ) :
    ∃ n ≤ γ.increments.length,
      L / 2 ≤ 2 * primalLoopLength (γ.stateAt n).vector.zPart := by
  obtain ⟨n, hn, hhalf⟩ := exists_primal_half_filled_state γ hendpoint
  refine ⟨n, hn, ?_⟩
  have hseparator :=
    BinarySquare.half_le_openBoundaryLength_of_fullRows_card
      (primalSquareProjection (γ.stateAt n).vector.zPart) (by
        simpa [primalFullRowCount] using hhalf)
  exact hseparator.trans
    (primal_openBoundaryLength_le_two_mul_loopLength
      (γ.stateAt n).vector.zPart)

/-- Every path to the dual sector crosses a state whose actual dual
defect-loop length is linear in `L`, with the same explicit constant. -/
theorem exists_dual_large_defect_loop
    (γ : PauliErrorPath (ι := Plaquette L))
    (hendpoint : HasDualMembraneEndpoint γ) :
    ∃ n ≤ γ.increments.length,
      L / 2 ≤ 2 * dualLoopLength (γ.stateAt n).vector.xPart := by
  obtain ⟨n, hn, hhalf⟩ := exists_dual_half_filled_state γ hendpoint
  refine ⟨n, hn, ?_⟩
  have hseparator :=
    BinarySquare.half_le_openBoundaryLength_of_fullRows_card
      (dualSquareProjection (γ.stateAt n).vector.xPart) (by
        simpa [dualFullRowCount] using hhalf)
  exact hseparator.trans
    (dual_openBoundaryLength_le_two_mul_loopLength
      (γ.stateAt n).vector.xPart)

/-- Explicit linear BT09 path-height lower bound for the primal membrane
sector. -/
theorem half_le_pathHeight_of_hasPrimalMembraneEndpoint
    (γ : PauliErrorPath (ι := Plaquette L))
    (hendpoint : HasPrimalMembraneEndpoint γ) :
    L / 2 ≤ (toricHamiltonian (L := L)).pathHeight γ := by
  obtain ⟨n, hn, hloop⟩ := exists_primal_large_defect_loop γ hendpoint
  exact hloop.trans ((two_mul_primalLoopLength_le_btExcessEnergy
    (γ.stateAt n)).trans
      ((toricHamiltonian (L := L)).btExcessEnergy_stateAt_le_pathHeight
        γ n hn))

/-- Explicit linear BT09 path-height lower bound for the dual membrane
sector. -/
theorem half_le_pathHeight_of_hasDualMembraneEndpoint
    (γ : PauliErrorPath (ι := Plaquette L))
    (hendpoint : HasDualMembraneEndpoint γ) :
    L / 2 ≤ (toricHamiltonian (L := L)).pathHeight γ := by
  obtain ⟨n, hn, hloop⟩ := exists_dual_large_defect_loop γ hendpoint
  exact hloop.trans ((two_mul_dualLoopLength_le_btExcessEnergy
    (γ.stateAt n)).trans
      ((toricHamiltonian (L := L)).btExcessEnergy_stateAt_le_pathHeight
        γ n hn))

/-- The fully proved finite lower-bound theorem for both chosen nontrivial
membrane sectors of the periodic four-dimensional toric code. -/
theorem fourDimensionalToric_membranePath_linearEnergyBarrier
    (γ : PauliErrorPath (ι := Plaquette L))
    (hendpoint : HasPrimalMembraneEndpoint γ ∨ HasDualMembraneEndpoint γ) :
    L / 2 ≤ (toricHamiltonian (L := L)).pathHeight γ := by
  rcases hendpoint with hprimal | hdual
  · exact half_le_pathHeight_of_hasPrimalMembraneEndpoint γ hprimal
  · exact half_le_pathHeight_of_hasDualMembraneEndpoint γ hdual

end QEC.Coding.PeriodicCubical4
