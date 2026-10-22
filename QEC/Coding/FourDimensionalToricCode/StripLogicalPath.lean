import QEC.Coding.FourDimensionalToricCode.AlternatingStripDistance
import QEC.Coding.Stabilizer.PathEnergy

/-!
# Row-by-row logical Pauli paths

This module constructs the actual single-qubit Pauli walk used in the
Bravyi--Terhal two-dimensional energy-barrier argument.  It reuses the
selected local stabilizer Hamiltonian and the concrete square-lattice strip
geometry; no energy barrier or path is stored as input data.
-/

noncomputable section

namespace QEC
namespace Coding

open PauliSymplectic
open scoped Classical

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

namespace PauliErrorPath

private theorem zmod_two_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

/-- The phase-free factor of `Q` supported at one physical site. -/
def siteFactor (Q : Binary ι) (i : ι) : Binary ι :=
  Locality.restrictBinaryTo {i} Q

theorem support_siteFactor_subset (Q : Binary ι) (i : ι) :
    support (siteFactor Q i) ⊆ {i} :=
  Locality.support_restrictBinaryTo_subset {i} Q

theorem weight_siteFactor_le_one (Q : Binary ι) (i : ι) :
    weight (siteFactor Q i) ≤ 1 := by
  exact (Finset.card_le_card (support_siteFactor_subset Q i)).trans (by simp)

omit [DecidableEq ι] in
theorem accumulate_cons (step : Binary ι) (steps : List (Binary ι)) :
    accumulate (step :: steps) = binaryMul step (accumulate steps) := by
  simp only [accumulate, List.foldl_cons, binaryMul_binaryOne_left]
  exact foldl_binaryMul_eq_binaryMul_accumulate steps step

/--
Accumulating distinct one-site factors has the vector obtained by restricting
the original Pauli to the enumerated sites.
-/
theorem accumulate_map_siteFactor_vector
    (Q : Binary ι) (sites : List ι) (hnodup : sites.Nodup) :
    (accumulate (sites.map (siteFactor Q))).vector =
      (Locality.restrictBinaryTo sites.toFinset Q).vector := by
  induction sites with
  | nil =>
      change
        ({ xPart := 0, zPart := 0 } : SymplecticVector (ZMod 2) ι) =
          { xPart := fun _ => 0, zPart := fun _ => 0 }
      rfl
  | cons i sites ih =>
      rw [List.nodup_cons] at hnodup
      rw [List.map_cons, accumulate_cons]
      have ihVector := ih hnodup.2
      change
        (siteFactor Q i).vector +
            (accumulate (sites.map (siteFactor Q))).vector =
          (Locality.restrictBinaryTo (i :: sites).toFinset Q).vector
      rw [ihVector]
      apply
        (SymplecticVector.toProdEquiv (F := ZMod 2) (ι := ι)).injective
      apply Prod.ext
      · funext q
        change
          ((siteFactor Q i).vector +
              (Locality.restrictBinaryTo sites.toFinset Q).vector).xPart q =
            (Locality.restrictBinaryTo (i :: sites).toFinset Q).vector.xPart q
        by_cases hqi : q = i
        · subst q
          simp [siteFactor, Locality.restrictBinaryTo, hnodup.1]
        · simp [siteFactor, Locality.restrictBinaryTo, hqi]
      · funext q
        change
          ((siteFactor Q i).vector +
              (Locality.restrictBinaryTo sites.toFinset Q).vector).zPart q =
            (Locality.restrictBinaryTo (i :: sites).toFinset Q).vector.zPart q
        by_cases hqi : q = i
        · subst q
          simp [siteFactor, Locality.restrictBinaryTo, hnodup.1]
        · simp [siteFactor, Locality.restrictBinaryTo, hqi]

/-- The product of all one-site factors in a duplicate-free enumeration. -/
def orderedCore (Q : Binary ι) (sites : List ι) (_hnodup : sites.Nodup) :
    PauliErrorPath (ι := ι) where
  increments := sites.map (siteFactor Q)
  step_weight_le_one := by
    intro step hstep
    rw [List.mem_map] at hstep
    obtain ⟨i, _hi, rfl⟩ := hstep
    exact weight_siteFactor_le_one Q i

@[simp]
theorem orderedCore_increments
    (Q : Binary ι) (sites : List ι) (hnodup : sites.Nodup) :
    (orderedCore Q sites hnodup).increments = sites.map (siteFactor Q) :=
  rfl

theorem orderedCore_endpoint_vector
    (Q : Binary ι) (sites : List ι) (hnodup : sites.Nodup) :
    (orderedCore Q sites hnodup).endpoint.vector =
      (Locality.restrictBinaryTo sites.toFinset Q).vector :=
  accumulate_map_siteFactor_vector Q sites hnodup

theorem orderedCore_stateAt_vector
    (Q : Binary ι) (sites : List ι) (hnodup : sites.Nodup)
    (n : Nat) :
    ((orderedCore Q sites hnodup).stateAt n).vector =
      (Locality.restrictBinaryTo (sites.take n).toFinset Q).vector := by
  rw [stateAt]
  change
    (accumulate ((sites.map (siteFactor Q)).take n)).vector =
      (Locality.restrictBinaryTo (sites.take n).toFinset Q).vector
  simpa using
    accumulate_map_siteFactor_vector Q (sites.take n)
      hnodup.take

/--
The exact path to `Q`: traverse all one-site restrictions in the supplied
enumeration, then apply the weight-zero global phase correction.
-/
def orderedExact
    (Q : Binary ι) (sites : List ι) (hnodup : sites.Nodup)
    (hcover : sites.toFinset = Finset.univ) :
    PauliErrorPath (ι := ι) :=
  let core := orderedCore Q sites hnodup
  let correction := binaryMul (binaryDagger core.endpoint) Q
  {
    increments := core.increments ++ [correction]
    step_weight_le_one := by
      intro step hstep
      rcases List.mem_append.mp hstep with hcore | hcorrection
      · exact core.step_weight_le_one step hcore
      · have hstepEq : step = correction := by
          simpa using hcorrection
        subst step
        have hvector : correction.vector = 0 := by
          change core.endpoint.vector + Q.vector = 0
          rw [orderedCore_endpoint_vector Q sites hnodup, hcover]
          apply
            (SymplecticVector.toProdEquiv (F := ZMod 2) (ι := ι)).injective
          apply Prod.ext
          · funext i
            change
              ((Locality.restrictBinaryTo Finset.univ Q).vector +
                  Q.vector).xPart i = (0 : SymplecticVector (ZMod 2) ι).xPart i
            simp [Locality.restrictBinaryTo, zmod_two_add_self]
          · funext i
            change
              ((Locality.restrictBinaryTo Finset.univ Q).vector +
                  Q.vector).zPart i = (0 : SymplecticVector (ZMod 2) ι).zPart i
            simp [Locality.restrictBinaryTo, zmod_two_add_self]
        have hsupp : support correction = ∅ := by
          ext i
          simp [support, xSupport, zSupport, binarySupport, hvector]
        rw [weight, hsupp]
        simp
  }

@[simp]
theorem orderedExact_increments
    (Q : Binary ι) (sites : List ι) (hnodup : sites.Nodup)
    (hcover : sites.toFinset = Finset.univ) :
    (orderedExact Q sites hnodup hcover).increments =
      (orderedCore Q sites hnodup).increments ++
        [binaryMul (binaryDagger (orderedCore Q sites hnodup).endpoint) Q] :=
  rfl

@[simp]
theorem orderedExact_endpoint
    (Q : Binary ι) (sites : List ι) (hnodup : sites.Nodup)
    (hcover : sites.toFinset = Finset.univ) :
    (orderedExact Q sites hnodup hcover).endpoint = Q := by
  rw [endpoint, orderedExact_increments, accumulate_append]
  rw [accumulate_singleton, ← binaryMul_assoc]
  have hright :
      binaryMul (orderedCore Q sites hnodup).endpoint
          (binaryDagger (orderedCore Q sites hnodup).endpoint) =
        binaryOne := by
    rcases (orderedCore Q sites hnodup).endpoint with ⟨phase, ⟨x, z⟩⟩
    simp [binaryMul, binaryMulPhase, binaryDagger, binaryDaggerPhase,
      binaryOne]
    have htwo (a : ZMod 2) : a + a = 0 := by
      fin_cases a <;> decide
    constructor
    · have htwo (a : ZMod 2) : a + a = 0 := by
        fin_cases a <;> decide
      let s : ZMod 2 := ∑ i, x i * z i
      change phase + (phase + s) + s = 0
      calc
        phase + (phase + s) + s = (phase + phase) + (s + s) := by abel
        _ = 0 := by simp [htwo]
    · constructor <;> funext i
      · change x i + x i = 0
        exact htwo (x i)
      · change z i + z i = 0
        exact htwo (z i)
  change
    binaryMul
        (binaryMul (orderedCore Q sites hnodup).endpoint
          (binaryDagger (orderedCore Q sites hnodup).endpoint)) Q =
      Q
  rw [hright]
  simp

theorem orderedExact_stateAt_vector
    (Q : Binary ι) (sites : List ι) (hnodup : sites.Nodup)
    (hcover : sites.toFinset = Finset.univ)
    (n : Nat) (hn : n ≤ sites.length) :
    ((orderedExact Q sites hnodup hcover).stateAt n).vector =
      (Locality.restrictBinaryTo (sites.take n).toFinset Q).vector := by
  let core := orderedCore Q sites hnodup
  have hlen : core.increments.length = sites.length := by
    simp [core, orderedCore]
  have hstate :
      (orderedExact Q sites hnodup hcover).stateAt n =
        core.stateAt n := by
    simp only [stateAt]
    change
      accumulate
          ((core.increments ++
              [binaryMul (binaryDagger core.endpoint) Q]).take n) =
        accumulate (core.increments.take n)
    rw [List.take_append_of_le_length]
    simpa [hlen] using hn
  rw [hstate]
  exact orderedCore_stateAt_vector Q sites hnodup n

end PauliErrorPath

namespace StabilizerCode.LocalStabilizerHamiltonian.StripGeometry

/-- The row-major linear index, with columns varying inside each row. -/
def rowMajorIndex {L : Nat} (p : Site L) : Nat :=
  p.2.val * L + p.1.val

theorem rowMajorIndex_eq_finProdFinEquiv_val
    {L : Nat} (p : Site L) :
    rowMajorIndex p = (finProdFinEquiv (p.2, p.1)).val := by
  simp [rowMajorIndex, finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

/-- The explicit row-major enumeration of the square lattice. -/
def rowMajorSites (L : Nat) : List (Site L) :=
  List.ofFn fun n : Fin (L * L) =>
    let yx : Fin L × Fin L := finProdFinEquiv.symm n
    (yx.2, yx.1)

@[simp]
theorem length_rowMajorSites (L : Nat) :
    (rowMajorSites L).length = L * L := by
  simp [rowMajorSites]

theorem rowMajorSites_nodup (L : Nat) :
    (rowMajorSites L).Nodup := by
  rw [rowMajorSites, List.nodup_ofFn]
  intro a b hab
  have hyx :
      finProdFinEquiv.symm a = finProdFinEquiv.symm b := by
    exact Prod.ext (congrArg Prod.snd hab) (congrArg Prod.fst hab)
  exact finProdFinEquiv.symm.injective hyx

@[simp]
theorem rowMajorIndex_rowMajorSites_getElem
    {L n : Nat} (hn : n < (rowMajorSites L).length) :
    rowMajorIndex (rowMajorSites L)[n] = n := by
  simp only [rowMajorSites, List.getElem_ofFn]
  rw [rowMajorIndex_eq_finProdFinEquiv_val]
  exact
    congrArg Fin.val
      (finProdFinEquiv.apply_symm_apply ⟨n, by simpa using hn⟩)

theorem rowMajorSites_getElem_rowMajorIndex
    {L : Nat} (p : Site L)
    (hindex : rowMajorIndex p < (rowMajorSites L).length) :
    (rowMajorSites L)[rowMajorIndex p]'hindex = p := by
  have hindex' : rowMajorIndex p < L * L := by
    simpa [length_rowMajorSites] using hindex
  have hfin :
      (⟨rowMajorIndex p, hindex'⟩ : Fin (L * L)) =
        finProdFinEquiv (p.2, p.1) := by
    apply Fin.ext
    exact rowMajorIndex_eq_finProdFinEquiv_val p
  simp only [rowMajorSites, List.getElem_ofFn]
  change
    ((finProdFinEquiv.symm
        (⟨rowMajorIndex p, hindex'⟩ : Fin (L * L))).2,
      (finProdFinEquiv.symm
        (⟨rowMajorIndex p, hindex'⟩ : Fin (L * L))).1) = p
  rw [hfin, finProdFinEquiv.symm_apply_apply]

theorem mem_take_rowMajorSites_iff
    {L n : Nat} (p : Site L) :
    p ∈ (rowMajorSites L).take n ↔
      rowMajorIndex p < min n (L * L) := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨j, hj, hp⟩
    rw [← hp, rowMajorIndex_rowMajorSites_getElem]
    simpa [length_rowMajorSites] using hj
  · intro hp
    have hindex : rowMajorIndex p < (rowMajorSites L).length := by
      simpa [length_rowMajorSites] using
        (lt_of_lt_of_le hp (min_le_right n (L * L)))
    exact
      ⟨rowMajorIndex p, by simpa [length_rowMajorSites] using hp,
        rowMajorSites_getElem_rowMajorIndex p hindex⟩

@[simp]
theorem rowMajorSites_toFinset (L : Nat) :
    (rowMajorSites L).toFinset =
      (Finset.univ : Finset (Site L)) := by
  ext p
  simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
  have hindex : rowMajorIndex p < (rowMajorSites L).length := by
    rw [length_rowMajorSites, rowMajorIndex_eq_finProdFinEquiv_val]
    exact (finProdFinEquiv (p.2, p.1)).isLt
  exact
    List.mem_iff_getElem.mpr
      ⟨rowMajorIndex p, hindex,
        rowMajorSites_getElem_rowMajorIndex p hindex⟩

/-- Prefix region cut out by the row-major index. -/
def rowMajorPrefix (L n : Nat) : Finset (Site L) :=
  Finset.univ.filter fun p => rowMajorIndex p < n

@[simp]
theorem mem_rowMajorPrefix_iff
    {L n : Nat} (p : Site L) :
    p ∈ rowMajorPrefix L n ↔ rowMajorIndex p < n := by
  simp [rowMajorPrefix]

theorem take_rowMajorSites_toFinset
    {L n : Nat} (hn : n ≤ L * L) :
    ((rowMajorSites L).take n).toFinset = rowMajorPrefix L n := by
  ext p
  rw [List.mem_toFinset, mem_take_rowMajorSites_iff,
    mem_rowMajorPrefix_iff, min_eq_left hn]

theorem support_eq_of_vector_eq
    {L : Nat}
    {E F : Binary (Site L)} (hvector : E.vector = F.vector) :
    support E = support F := by
  simp [support, xSupport, zSupport, hvector]

theorem support_restrictBinaryTo_subset_support
    {L : Nat}
    (R : Finset (Site L)) (Q : Binary (Site L)) :
    support (Locality.restrictBinaryTo R Q) ⊆ support Q := by
  intro p hp
  rw [mem_support] at hp ⊢
  rcases hp with hpX | hpZ
  · left
    simp [xSupport, Locality.restrictBinaryTo, binarySupport] at hpX
    simpa [xSupport, binarySupport] using hpX.2
  · right
    simp [zSupport, Locality.restrictBinaryTo, binarySupport] at hpZ
    simpa [zSupport, binarySupport] using hpZ.2

theorem rowMajorPrefix_row_bounds
    {L n : Nat} (hL : 0 < L) (p q : Site L)
    (hp : p ∈ rowMajorPrefix L n)
    (hq : q ∉ rowMajorPrefix L n) :
    p.2.val ≤ n / L ∧ n / L ≤ q.2.val := by
  have hpIndex : rowMajorIndex p < n :=
    (mem_rowMajorPrefix_iff p).1 hp
  have hqIndex : n ≤ rowMajorIndex q := by
    simpa [mem_rowMajorPrefix_iff] using hq
  constructor
  · apply (Nat.le_div_iff_mul_le hL).2
    have hbase : p.2.val * L ≤ rowMajorIndex p := by
      simp [rowMajorIndex]
    exact hbase.trans hpIndex.le
  · rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hL]
    have hindexUpper :
        rowMajorIndex q < (q.2.val + 1) * L := by
      rw [rowMajorIndex, Nat.add_mul]
      have hqX : q.1.val < L := q.1.isLt
      omega
    exact hqIndex.trans_lt hindexUpper

/-- The exact row-by-row path to a square-lattice Pauli representative. -/
def rowMajorExactPath {L : Nat} (Q : Binary (Site L)) :
    PauliErrorPath (ι := Site L) :=
  PauliErrorPath.orderedExact Q (rowMajorSites L)
    (rowMajorSites_nodup L) (rowMajorSites_toFinset L)

@[simp]
theorem rowMajorExactPath_endpoint
    {L : Nat} (Q : Binary (Site L)) :
    (rowMajorExactPath Q).endpoint = Q :=
  PauliErrorPath.orderedExact_endpoint Q (rowMajorSites L)
    (rowMajorSites_nodup L) (rowMajorSites_toFinset L)

theorem rowMajorExactPath_stateAt_vector
    {L n : Nat} (Q : Binary (Site L)) (hn : n ≤ L * L) :
    ((rowMajorExactPath Q).stateAt n).vector =
      (Locality.restrictBinaryTo (rowMajorPrefix L n) Q).vector := by
  rw [rowMajorExactPath,
    PauliErrorPath.orderedExact_stateAt_vector
      Q (rowMajorSites L) (rowMajorSites_nodup L)
        (rowMajorSites_toFinset L) n (by simpa using hn),
    take_rowMajorSites_toFinset hn]

@[simp]
theorem length_rowMajorExactPath_increments
    {L : Nat} (Q : Binary (Site L)) :
    (rowMajorExactPath Q).increments.length = L * L + 1 := by
  simp [rowMajorExactPath, PauliErrorPath.orderedExact,
    PauliErrorPath.orderedCore, length_rowMajorSites]

/-- An open-boundary interval of rows. -/
def openHorizontalInterval (L start width : Nat) : Finset (Site L) :=
  Finset.univ.filter fun p =>
    start ≤ p.2.val ∧ p.2.val < start + width

@[simp]
theorem mem_openHorizontalInterval_iff
    {L start width : Nat} (p : Site L) :
    p ∈ openHorizontalInterval L start width ↔
      start ≤ p.2.val ∧ p.2.val < start + width := by
  simp [openHorizontalInterval]

/-- A periodic interval of rows. -/
def periodicHorizontalInterval (L start width : Nat) : Finset (Site L) :=
  let s := start % L
  Finset.univ.filter fun p =>
    (s ≤ p.2.val ∧ p.2.val < s + width) ∨
      p.2.val + L < s + width

@[simp]
theorem mem_periodicHorizontalInterval_iff
    {L start width : Nat} (p : Site L) :
    p ∈ periodicHorizontalInterval L start width ↔
      ((start % L ≤ p.2.val ∧
          p.2.val < start % L + width) ∨
        p.2.val + L < start % L + width) := by
  simp [periodicHorizontalInterval]

/-- Actual open row-interval support locality for every selected generator. -/
def HasOpenRowIntervalGeneratorSupport
    {L : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := Site L) (κ := κ))
    (r : Nat) : Prop :=
  ∀ j, ∃ start width, width ≤ r ∧
    support (H.generators j) ⊆ openHorizontalInterval L start width

/-- Actual cyclic row-interval support locality for every selected generator. -/
def HasPeriodicRowIntervalGeneratorSupport
    {L : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := Site L) (κ := κ))
    (r : Nat) : Prop :=
  ∀ j, ∃ start width, width ≤ r ∧
    support (H.generators j) ⊆ periodicHorizontalInterval L start width

/-- The moving endpoint band on the already-built side of a row-major cut. -/
def movingFrontier
    (L stripStart stripWidth cursor r : Nat) : Finset (Site L) :=
  (openVerticalInterval L stripStart stripWidth).filter fun p =>
    p.2.val ≤ cursor ∧ cursor < p.2.val + r

@[simp]
theorem mem_movingFrontier_iff
    {L stripStart stripWidth cursor r : Nat} (p : Site L) :
    p ∈ movingFrontier L stripStart stripWidth cursor r ↔
      p ∈ openVerticalInterval L stripStart stripWidth ∧
        p.2.val ≤ cursor ∧ cursor < p.2.val + r := by
  simp [movingFrontier]

/-- The fixed seam band needed when rows are periodic. -/
def seamFrontier
    (L stripStart stripWidth r : Nat) : Finset (Site L) :=
  (openVerticalInterval L stripStart stripWidth).filter fun p =>
    p.2.val < r

@[simp]
theorem mem_seamFrontier_iff
    {L stripStart stripWidth r : Nat} (p : Site L) :
    p ∈ seamFrontier L stripStart stripWidth r ↔
      p ∈ openVerticalInterval L stripStart stripWidth ∧ p.2.val < r := by
  simp [seamFrontier]

theorem card_movingFrontier_le
    (L stripStart stripWidth cursor r : Nat) :
    (movingFrontier L stripStart stripWidth cursor r).card ≤
      stripWidth * r := by
  let f :
      {p // p ∈ movingFrontier L stripStart stripWidth cursor r} →
        Fin stripWidth × Fin r :=
    fun p =>
      (⟨p.1.1.val - stripStart, by
          have hp :=
            (mem_movingFrontier_iff p.1).1 p.2
          have hx :=
            (mem_openVerticalInterval_iff p.1).1 hp.1
          omega⟩,
        ⟨cursor - p.1.2.val, by
          have hp :=
            (mem_movingFrontier_iff p.1).1 p.2
          omega⟩)
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      have hp :=
        (mem_movingFrontier_iff p.1).1 p.2
      have hq :=
        (mem_movingFrontier_iff q.1).1 q.2
      have hpx :=
        (mem_openVerticalInterval_iff p.1).1 hp.1
      have hqx :=
        (mem_openVerticalInterval_iff q.1).1 hq.1
      have hval :
          p.1.1.val - stripStart = q.1.1.val - stripStart :=
        congrArg (fun z => z.1.val) hpq
      omega
    · apply Fin.ext
      have hp :=
        (mem_movingFrontier_iff p.1).1 p.2
      have hq :=
        (mem_movingFrontier_iff q.1).1 q.2
      have hval :
          cursor - p.1.2.val = cursor - q.1.2.val :=
        congrArg (fun z => z.2.val) hpq
      omega
  have hcard := Fintype.card_le_of_injective f hf
  rw [← Fintype.card_coe
    (movingFrontier L stripStart stripWidth cursor r)]
  simpa only [Fintype.card_prod, Fintype.card_fin] using hcard

theorem card_seamFrontier_le
    (L stripStart stripWidth r : Nat) :
    (seamFrontier L stripStart stripWidth r).card ≤
      stripWidth * r := by
  let f :
      {p // p ∈ seamFrontier L stripStart stripWidth r} →
        Fin stripWidth × Fin r :=
    fun p =>
      (⟨p.1.1.val - stripStart, by
          have hp :=
            (mem_seamFrontier_iff p.1).1 p.2
          have hx :=
            (mem_openVerticalInterval_iff p.1).1 hp.1
          omega⟩,
        ⟨p.1.2.val, (mem_seamFrontier_iff p.1).1 p.2 |>.2⟩)
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      have hp :=
        (mem_seamFrontier_iff p.1).1 p.2
      have hq :=
        (mem_seamFrontier_iff q.1).1 q.2
      have hpx :=
        (mem_openVerticalInterval_iff p.1).1 hp.1
      have hqx :=
        (mem_openVerticalInterval_iff q.1).1 hq.1
      have hval :
          p.1.1.val - stripStart = q.1.1.val - stripStart :=
        congrArg (fun z => z.1.val) hpq
      omega
    · apply Fin.ext
      exact congrArg (fun z : Fin stripWidth × Fin r => z.2.val) hpq
  have hcard := Fintype.card_le_of_injective f hf
  rw [← Fintype.card_coe
    (seamFrontier L stripStart stripWidth r)]
  simpa only [Fintype.card_prod, Fintype.card_fin] using hcard

theorem open_crossing_mem_movingFrontier
    {L r stripStart stripWidth cursor : Nat}
    {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := Site L) (κ := κ))
    (hLocal : HasOpenRowIntervalGeneratorSupport H r)
    (j : κ) (p q : Site L)
    (hpGenerator : p ∈ support (H.generators j))
    (hqGenerator : q ∈ support (H.generators j))
    (hpStrip : p ∈ openVerticalInterval L stripStart stripWidth)
    (hpCursor : p.2.val ≤ cursor) (hCursorQ : cursor ≤ q.2.val) :
    p ∈ movingFrontier L stripStart stripWidth cursor r := by
  obtain ⟨start, width, hwidth, hsupport⟩ := hLocal j
  have hpInterval :=
    (mem_openHorizontalInterval_iff p).1 (hsupport hpGenerator)
  have hqInterval :=
    (mem_openHorizontalInterval_iff q).1 (hsupport hqGenerator)
  rw [mem_movingFrontier_iff]
  exact ⟨hpStrip, hpCursor, by omega⟩

theorem periodic_crossing_mem_frontier
    {L r stripStart stripWidth cursor : Nat}
    {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := Site L) (κ := κ))
    (hLocal : HasPeriodicRowIntervalGeneratorSupport H r)
    (j : κ) (p q : Site L)
    (hpGenerator : p ∈ support (H.generators j))
    (hqGenerator : q ∈ support (H.generators j))
    (hpStrip : p ∈ openVerticalInterval L stripStart stripWidth)
    (hpCursor : p.2.val ≤ cursor) (hCursorQ : cursor ≤ q.2.val) :
    p ∈ movingFrontier L stripStart stripWidth cursor r ∪
      seamFrontier L stripStart stripWidth r := by
  obtain ⟨start, width, hwidth, hsupport⟩ := hLocal j
  have hpInterval :=
    (mem_periodicHorizontalInterval_iff p).1 (hsupport hpGenerator)
  have hqInterval :=
    (mem_periodicHorizontalInterval_iff q).1 (hsupport hqGenerator)
  rw [Finset.mem_union, mem_movingFrontier_iff, mem_seamFrontier_iff]
  rcases hpInterval with hpMain | hpWrap
  · rcases hqInterval with hqMain | hqWrap
    · left
      exact ⟨hpStrip, hpCursor, by omega⟩
    · by_cases hpr : p.2.val < r
      · right
        exact ⟨hpStrip, hpr⟩
      · left
        exact ⟨hpStrip, hpCursor, by omega⟩
  · right
    refine ⟨hpStrip, ?_⟩
    have hstartLt : start % L < L := Nat.mod_lt start (by omega)
    omega

end StabilizerCode.LocalStabilizerHamiltonian.StripGeometry

namespace StabilizerCode.LocalStabilizerHamiltonian

variable {κ : Type*} [Fintype κ]

/-- Selected generators incident on at least one site of a finite region. -/
def incidentGeneratorUnion
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) : Finset κ :=
  R.biUnion H.incidentGenerators

theorem card_incidentGeneratorUnion_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) :
    (H.incidentGeneratorUnion R).card ≤
      R.card * H.participationBound := by
  exact
    Finset.card_biUnion_le_card_mul R H.incidentGenerators
      H.participationBound fun i _hi => H.incidentGenerators_card_le i

theorem mem_incidentGeneratorUnion_of_mem_generatorSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) (i : ι) (j : κ)
    (hiR : i ∈ R) (hij : i ∈ support (H.generators j)) :
    j ∈ H.incidentGeneratorUnion R := by
  rw [incidentGeneratorUnion, Finset.mem_biUnion]
  refine ⟨i, hiR, ?_⟩
  simpa [incidentGenerators, generatorSupport] using hij

theorem violatedGenerators_eq_of_vector_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E F : Binary ι) (hvector : E.vector = F.vector) :
    H.violatedGenerators E = H.violatedGenerators F := by
  ext j
  simp [Commutes, hvector]

theorem btExcessEnergy_eq_of_vector_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E F : Binary ι) (hvector : E.vector = F.vector) :
    H.btExcessEnergy E = H.btExcessEnergy F := by
  simp [btExcessEnergy, unitDefectEnergy,
    H.violatedGenerators_eq_of_vector_eq E F hvector]

theorem binaryMul_complement_vector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q E F : Binary ι) (hdecomp : Q.vector = E.vector + F.vector) :
    (binaryMul Q F).vector = E.vector := by
  rw [show (binaryMul Q F).vector = Q.vector + F.vector by rfl,
    hdecomp]
  apply
    (SymplecticVector.toProdEquiv (F := ZMod 2) (ι := ι)).injective
  apply Prod.ext
  · funext i
    change (E.vector.xPart i + F.vector.xPart i) +
        F.vector.xPart i = E.vector.xPart i
    have htwo : F.vector.xPart i + F.vector.xPart i = 0 :=
      PauliErrorPath.zmod_two_add_self _
    rw [add_assoc, htwo, add_zero]
  · funext i
    change (E.vector.zPart i + F.vector.zPart i) +
        F.vector.zPart i = E.vector.zPart i
    have htwo : F.vector.zPart i + F.vector.zPart i = 0 :=
      PauliErrorPath.zmod_two_add_self _
    rw [add_assoc, htwo, add_zero]

theorem not_commutes_complement_of_not_commutes_restriction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (Q E F : Binary ι) (j : κ)
    (hQNormalizer : H.code.1.InBinaryNormalizer Q)
    (hdecomp : Q.vector = E.vector + F.vector)
    (hE : ¬ Commutes E (H.generators j)) :
    ¬ Commutes F (H.generators j) := by
  intro hF
  have hQ : Commutes Q (H.generators j) :=
    hQNormalizer (H.generators j) (H.generator_mem_generatedGroup j)
  have hproduct :
      Commutes (H.generators j) (binaryMul Q F) :=
    commutes_binaryMul_right
      ((commutes_comm _ _).2 hQ) ((commutes_comm _ _).2 hF)
  apply hE
  change symplecticForm E.vector (H.generators j).vector = 0
  rw [← binaryMul_complement_vector Q E F hdecomp]
  exact (commutes_comm _ _).2 hproduct

theorem violatedGenerators_restriction_subset_open_frontier
    {L r stripStart stripWidth n : Nat}
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hL : 0 < L)
    (hRowLocal :
      StripGeometry.HasOpenRowIntervalGeneratorSupport H r)
    (Q : Binary (StripGeometry.Site L))
    (hQNormalizer : H.code.1.InBinaryNormalizer Q)
    (hQStrip :
      support Q ⊆
        StripGeometry.openVerticalInterval L stripStart stripWidth) :
    H.violatedGenerators
        (Locality.restrictBinaryTo (StripGeometry.rowMajorPrefix L n) Q) ⊆
      H.incidentGeneratorUnion
        (StripGeometry.movingFrontier
          L stripStart stripWidth (n / L) r) := by
  intro j hj
  rw [mem_violatedGenerators] at hj
  let R := StripGeometry.rowMajorPrefix L n
  let E := Locality.restrictBinaryTo R Q
  let F := Locality.restrictBinaryTo Rᶜ Q
  have hnotDisjointE :
      ¬ Disjoint (support E) (support (H.generators j)) := by
    intro hdisjoint
    exact hj (QEC.Locality.commutes_of_disjoint_support E
      (H.generators j) hdisjoint)
  obtain ⟨p, hpE, hpGenerator⟩ :=
    Finset.not_disjoint_iff.mp hnotDisjointE
  have hpR : p ∈ R :=
    Locality.support_restrictBinaryTo_subset R Q hpE
  have hpQ : p ∈ support Q :=
    StripGeometry.support_restrictBinaryTo_subset_support R Q hpE
  have hRDisjoint : Disjoint R Rᶜ := by
    apply Finset.disjoint_left.mpr
    intro i hiR hiCompl
    exact (Finset.mem_compl.mp hiCompl) hiR
  have hQCover : support Q ⊆ R ∪ Rᶜ := by
    intro i _hi
    by_cases hiR : i ∈ R
    · exact Finset.mem_union_left _ hiR
    · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hiR)
  have hdecomp : Q.vector = E.vector + F.vector := by
    exact
      Locality.restrictBinaryTo_vector_add_of_support_subset_union
        R Rᶜ Q hRDisjoint hQCover
  have hFNotCommutes : ¬ Commutes F (H.generators j) :=
    H.not_commutes_complement_of_not_commutes_restriction
      Q E F j hQNormalizer hdecomp hj
  have hnotDisjointF :
      ¬ Disjoint (support F) (support (H.generators j)) := by
    intro hdisjoint
    exact hFNotCommutes
      (QEC.Locality.commutes_of_disjoint_support F
        (H.generators j) hdisjoint)
  obtain ⟨q, hqF, hqGenerator⟩ :=
    Finset.not_disjoint_iff.mp hnotDisjointF
  have hqCompl : q ∈ Rᶜ :=
    Locality.support_restrictBinaryTo_subset Rᶜ Q hqF
  have hqNotR : q ∉ R := Finset.mem_compl.mp hqCompl
  have hRows :=
    StripGeometry.rowMajorPrefix_row_bounds hL p q hpR hqNotR
  have hpFrontier :
      p ∈ StripGeometry.movingFrontier
        L stripStart stripWidth (n / L) r :=
    StripGeometry.open_crossing_mem_movingFrontier
      H hRowLocal j p q hpGenerator hqGenerator
        (hQStrip hpQ) hRows.1 hRows.2
  exact
    H.mem_incidentGeneratorUnion_of_mem_generatorSupport
      _ p j hpFrontier hpGenerator

theorem violatedGenerators_restriction_subset_periodic_frontier
    {L r stripStart stripWidth n : Nat}
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hL : 0 < L)
    (hRowLocal :
      StripGeometry.HasPeriodicRowIntervalGeneratorSupport H r)
    (Q : Binary (StripGeometry.Site L))
    (hQNormalizer : H.code.1.InBinaryNormalizer Q)
    (hQStrip :
      support Q ⊆
        StripGeometry.openVerticalInterval L stripStart stripWidth) :
    H.violatedGenerators
        (Locality.restrictBinaryTo (StripGeometry.rowMajorPrefix L n) Q) ⊆
      H.incidentGeneratorUnion
        (StripGeometry.movingFrontier
            L stripStart stripWidth (n / L) r ∪
          StripGeometry.seamFrontier
            L stripStart stripWidth r) := by
  intro j hj
  rw [mem_violatedGenerators] at hj
  let R := StripGeometry.rowMajorPrefix L n
  let E := Locality.restrictBinaryTo R Q
  let F := Locality.restrictBinaryTo Rᶜ Q
  have hnotDisjointE :
      ¬ Disjoint (support E) (support (H.generators j)) := by
    intro hdisjoint
    exact hj (QEC.Locality.commutes_of_disjoint_support E
      (H.generators j) hdisjoint)
  obtain ⟨p, hpE, hpGenerator⟩ :=
    Finset.not_disjoint_iff.mp hnotDisjointE
  have hpR : p ∈ R :=
    Locality.support_restrictBinaryTo_subset R Q hpE
  have hpQ : p ∈ support Q :=
    StripGeometry.support_restrictBinaryTo_subset_support R Q hpE
  have hRDisjoint : Disjoint R Rᶜ := by
    apply Finset.disjoint_left.mpr
    intro i hiR hiCompl
    exact (Finset.mem_compl.mp hiCompl) hiR
  have hQCover : support Q ⊆ R ∪ Rᶜ := by
    intro i _hi
    by_cases hiR : i ∈ R
    · exact Finset.mem_union_left _ hiR
    · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hiR)
  have hdecomp : Q.vector = E.vector + F.vector := by
    exact
      Locality.restrictBinaryTo_vector_add_of_support_subset_union
        R Rᶜ Q hRDisjoint hQCover
  have hFNotCommutes : ¬ Commutes F (H.generators j) :=
    H.not_commutes_complement_of_not_commutes_restriction
      Q E F j hQNormalizer hdecomp hj
  have hnotDisjointF :
      ¬ Disjoint (support F) (support (H.generators j)) := by
    intro hdisjoint
    exact hFNotCommutes
      (QEC.Locality.commutes_of_disjoint_support F
        (H.generators j) hdisjoint)
  obtain ⟨q, hqF, hqGenerator⟩ :=
    Finset.not_disjoint_iff.mp hnotDisjointF
  have hqCompl : q ∈ Rᶜ :=
    Locality.support_restrictBinaryTo_subset Rᶜ Q hqF
  have hqNotR : q ∉ R := Finset.mem_compl.mp hqCompl
  have hRows :=
    StripGeometry.rowMajorPrefix_row_bounds hL p q hpR hqNotR
  have hpFrontier :
      p ∈
        StripGeometry.movingFrontier
            L stripStart stripWidth (n / L) r ∪
          StripGeometry.seamFrontier
            L stripStart stripWidth r :=
    StripGeometry.periodic_crossing_mem_frontier
      H hRowLocal j p q hpGenerator hqGenerator
        (hQStrip hpQ) hRows.1 hRows.2
  exact
    H.mem_incidentGeneratorUnion_of_mem_generatorSupport
      _ p j hpFrontier hpGenerator

theorem btExcessEnergy_restriction_le_open_frontier
    {L r stripStart stripWidth n : Nat}
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hL : 0 < L) (hStripWidth : stripWidth ≤ r)
    (hRowLocal :
      StripGeometry.HasOpenRowIntervalGeneratorSupport H r)
    (Q : Binary (StripGeometry.Site L))
    (hQNormalizer : H.code.1.InBinaryNormalizer Q)
    (hQStrip :
      support Q ⊆
        StripGeometry.openVerticalInterval L stripStart stripWidth) :
    H.btExcessEnergy
        (Locality.restrictBinaryTo (StripGeometry.rowMajorPrefix L n) Q) ≤
      2 * r * r * H.participationBound := by
  have hsubset :=
    H.violatedGenerators_restriction_subset_open_frontier
      (n := n) hL hRowLocal Q hQNormalizer hQStrip
  have hincident :=
    H.card_incidentGeneratorUnion_le
      (StripGeometry.movingFrontier
        L stripStart stripWidth (n / L) r)
  have hfrontier :=
    StripGeometry.card_movingFrontier_le
      L stripStart stripWidth (n / L) r
  unfold btExcessEnergy unitDefectEnergy
  calc
    2 * (H.violatedGenerators
        (Locality.restrictBinaryTo
          (StripGeometry.rowMajorPrefix L n) Q)).card
        ≤ 2 * (H.incidentGeneratorUnion
            (StripGeometry.movingFrontier
              L stripStart stripWidth (n / L) r)).card :=
      Nat.mul_le_mul_left 2 (Finset.card_le_card hsubset)
    _ ≤ 2 *
        (StripGeometry.movingFrontier
          L stripStart stripWidth (n / L) r).card *
        H.participationBound := by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hincident
    _ ≤ 2 * (stripWidth * r) * H.participationBound := by
      exact Nat.mul_le_mul_right H.participationBound
        (Nat.mul_le_mul_left 2 hfrontier)
    _ ≤ 2 * r * r * H.participationBound := by
      have hwidthProduct : stripWidth * r ≤ r * r :=
        Nat.mul_le_mul_right r hStripWidth
      simpa [Nat.mul_assoc] using
        Nat.mul_le_mul_right H.participationBound
          (Nat.mul_le_mul_left 2 hwidthProduct)

theorem btExcessEnergy_restriction_le_periodic_frontier
    {L r stripStart stripWidth n : Nat}
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hL : 0 < L) (hStripWidth : stripWidth ≤ r)
    (hRowLocal :
      StripGeometry.HasPeriodicRowIntervalGeneratorSupport H r)
    (Q : Binary (StripGeometry.Site L))
    (hQNormalizer : H.code.1.InBinaryNormalizer Q)
    (hQStrip :
      support Q ⊆
        StripGeometry.openVerticalInterval L stripStart stripWidth) :
    H.btExcessEnergy
        (Locality.restrictBinaryTo (StripGeometry.rowMajorPrefix L n) Q) ≤
      4 * r * r * H.participationBound := by
  let moving :=
    StripGeometry.movingFrontier
      L stripStart stripWidth (n / L) r
  let seam :=
    StripGeometry.seamFrontier L stripStart stripWidth r
  have hsubset :=
    H.violatedGenerators_restriction_subset_periodic_frontier
      (n := n) hL hRowLocal Q hQNormalizer hQStrip
  have hincident :=
    H.card_incidentGeneratorUnion_le (moving ∪ seam)
  have hmoving :
      moving.card ≤ stripWidth * r :=
    StripGeometry.card_movingFrontier_le
      L stripStart stripWidth (n / L) r
  have hseam :
      seam.card ≤ stripWidth * r :=
    StripGeometry.card_seamFrontier_le
      L stripStart stripWidth r
  have hunion : (moving ∪ seam).card ≤ 2 * (stripWidth * r) := by
    exact
      (Finset.card_union_le moving seam).trans
        (by omega)
  unfold btExcessEnergy unitDefectEnergy
  calc
    2 * (H.violatedGenerators
        (Locality.restrictBinaryTo
          (StripGeometry.rowMajorPrefix L n) Q)).card
        ≤ 2 * (H.incidentGeneratorUnion (moving ∪ seam)).card :=
      Nat.mul_le_mul_left 2 (Finset.card_le_card hsubset)
    _ ≤ 2 * (moving ∪ seam).card * H.participationBound := by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hincident
    _ ≤ 2 * (2 * (stripWidth * r)) * H.participationBound := by
      exact Nat.mul_le_mul_right H.participationBound
        (Nat.mul_le_mul_left 2 hunion)
    _ ≤ 4 * r * r * H.participationBound := by
      have hwidthProduct : stripWidth * r ≤ r * r :=
        Nat.mul_le_mul_right r hStripWidth
      have hscaled :
          2 * (2 * (stripWidth * r)) ≤ 4 * (r * r) := by
        calc
          2 * (2 * (stripWidth * r)) = 4 * (stripWidth * r) := by ring
          _ ≤ 4 * (r * r) := Nat.mul_le_mul_left 4 hwidthProduct
      simpa [Nat.mul_assoc] using
        Nat.mul_le_mul_right H.participationBound hscaled

theorem btExcessEnergy_rowMajorExactPath_stateAt_le_open
    {L r stripStart stripWidth n : Nat}
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hL : 0 < L) (hStripWidth : stripWidth ≤ r)
    (hRowLocal :
      StripGeometry.HasOpenRowIntervalGeneratorSupport H r)
    (Q : Binary (StripGeometry.Site L))
    (hQNormalizer : H.code.1.InBinaryNormalizer Q)
    (hQStrip :
      support Q ⊆
        StripGeometry.openVerticalInterval L stripStart stripWidth)
    (hn : n ≤ (StripGeometry.rowMajorExactPath Q).increments.length) :
    H.btExcessEnergy ((StripGeometry.rowMajorExactPath Q).stateAt n) ≤
      2 * r * r * H.participationBound := by
  by_cases hnCore : n ≤ L * L
  · rw [H.btExcessEnergy_eq_of_vector_eq
      ((StripGeometry.rowMajorExactPath Q).stateAt n)
      (Locality.restrictBinaryTo
        (StripGeometry.rowMajorPrefix L n) Q)
      (StripGeometry.rowMajorExactPath_stateAt_vector Q hnCore)]
    exact
      H.btExcessEnergy_restriction_le_open_frontier
        hL hStripWidth hRowLocal Q hQNormalizer hQStrip
  · have hnEnd : n = (StripGeometry.rowMajorExactPath Q).increments.length := by
      rw [StripGeometry.length_rowMajorExactPath_increments] at hn
      rw [StripGeometry.length_rowMajorExactPath_increments]
      omega
    subst n
    rw [PauliErrorPath.stateAt_length,
      StripGeometry.rowMajorExactPath_endpoint]
    have hzero : H.violatedGenerators Q = ∅ := by
      ext j
      simp only [mem_violatedGenerators, Finset.notMem_empty, iff_false]
      push Not
      exact hQNormalizer (H.generators j)
        (H.generator_mem_generatedGroup j)
    simp [btExcessEnergy, unitDefectEnergy, hzero]

theorem btExcessEnergy_rowMajorExactPath_stateAt_le_periodic
    {L r stripStart stripWidth n : Nat}
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hL : 0 < L) (hStripWidth : stripWidth ≤ r)
    (hRowLocal :
      StripGeometry.HasPeriodicRowIntervalGeneratorSupport H r)
    (Q : Binary (StripGeometry.Site L))
    (hQNormalizer : H.code.1.InBinaryNormalizer Q)
    (hQStrip :
      support Q ⊆
        StripGeometry.openVerticalInterval L stripStart stripWidth)
    (hn : n ≤ (StripGeometry.rowMajorExactPath Q).increments.length) :
    H.btExcessEnergy ((StripGeometry.rowMajorExactPath Q).stateAt n) ≤
      4 * r * r * H.participationBound := by
  by_cases hnCore : n ≤ L * L
  · rw [H.btExcessEnergy_eq_of_vector_eq
      ((StripGeometry.rowMajorExactPath Q).stateAt n)
      (Locality.restrictBinaryTo
        (StripGeometry.rowMajorPrefix L n) Q)
      (StripGeometry.rowMajorExactPath_stateAt_vector Q hnCore)]
    exact
      H.btExcessEnergy_restriction_le_periodic_frontier
        hL hStripWidth hRowLocal Q hQNormalizer hQStrip
  · have hnEnd : n = (StripGeometry.rowMajorExactPath Q).increments.length := by
      rw [StripGeometry.length_rowMajorExactPath_increments] at hn
      rw [StripGeometry.length_rowMajorExactPath_increments]
      omega
    subst n
    rw [PauliErrorPath.stateAt_length,
      StripGeometry.rowMajorExactPath_endpoint]
    have hzero : H.violatedGenerators Q = ∅ := by
      ext j
      simp only [mem_violatedGenerators, Finset.notMem_empty, iff_false]
      push Not
      exact hQNormalizer (H.generators j)
        (H.generator_mem_generatedGroup j)
    simp [btExcessEnergy, unitDefectEnergy, hzero]

theorem exists_open_rowMajor_logical_path
    {L r stripStart stripWidth : Nat}
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hL : 0 < L) (hStripWidth : stripWidth ≤ r)
    (hRowLocal :
      StripGeometry.HasOpenRowIntervalGeneratorSupport H r)
    (Q : Binary (StripGeometry.Site L))
    (hQNormalizer : H.code.1.InBinaryNormalizer Q)
    (hQNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign Q)
    (hQStrip :
      support Q ⊆
        StripGeometry.openVerticalInterval L stripStart stripWidth) :
    ∃ γ : PauliErrorPath (ι := StripGeometry.Site L),
      γ.endpoint = Q ∧ H.HasLogicalEndpoint γ ∧
        H.pathHeight γ ≤ 2 * r * r * H.participationBound := by
  let γ := StripGeometry.rowMajorExactPath Q
  refine ⟨γ, StripGeometry.rowMajorExactPath_endpoint Q, ?_, ?_⟩
  · change
      H.code.1.InBinaryNormalizer γ.endpoint ∧
        ¬ H.code.1.InGeneratedGroupUpToSign γ.endpoint
    rw [show γ.endpoint = Q by
      exact StripGeometry.rowMajorExactPath_endpoint Q]
    exact ⟨hQNormalizer, hQNontrivial⟩
  · rw [pathHeight]
    apply Finset.sup_le
    intro n hn
    apply H.btExcessEnergy_rowMajorExactPath_stateAt_le_open
      hL hStripWidth hRowLocal Q hQNormalizer hQStrip
    simpa [γ, StripGeometry.length_rowMajorExactPath_increments] using
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))

theorem exists_periodic_rowMajor_logical_path
    {L r stripStart stripWidth : Nat}
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hL : 0 < L) (hStripWidth : stripWidth ≤ r)
    (hRowLocal :
      StripGeometry.HasPeriodicRowIntervalGeneratorSupport H r)
    (Q : Binary (StripGeometry.Site L))
    (hQNormalizer : H.code.1.InBinaryNormalizer Q)
    (hQNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign Q)
    (hQStrip :
      support Q ⊆
        StripGeometry.openVerticalInterval L stripStart stripWidth) :
    ∃ γ : PauliErrorPath (ι := StripGeometry.Site L),
      γ.endpoint = Q ∧ H.HasLogicalEndpoint γ ∧
        H.pathHeight γ ≤ 4 * r * r * H.participationBound := by
  let γ := StripGeometry.rowMajorExactPath Q
  refine ⟨γ, StripGeometry.rowMajorExactPath_endpoint Q, ?_, ?_⟩
  · change
      H.code.1.InBinaryNormalizer γ.endpoint ∧
        ¬ H.code.1.InGeneratedGroupUpToSign γ.endpoint
    rw [show γ.endpoint = Q by
      exact StripGeometry.rowMajorExactPath_endpoint Q]
    exact ⟨hQNormalizer, hQNontrivial⟩
  · rw [pathHeight]
    apply Finset.sup_le
    intro n hn
    apply H.btExcessEnergy_rowMajorExactPath_stateAt_le_periodic
      hL hStripWidth hRowLocal Q hQNormalizer hQStrip
    simpa [γ, StripGeometry.length_rowMajorExactPath_increments] using
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))

end StabilizerCode.LocalStabilizerHamiltonian
end Coding
end QEC
