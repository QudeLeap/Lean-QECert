import QEC.Coding.FourDimensionalToricCode.MembraneSyndrome
import QEC.Coding.FourDimensionalToricCode.StripLogicalPath

/-!
# Explicit membrane sweeps for the four-dimensional toric code

This module constructs row-major single-plaquette sweeps of the concrete
primal and dual membrane representatives from the periodic four-dimensional
cellulation.  Prefix geometry is computed on the actual plaquette chains and
then converted to the existing selected-term excess energy.

No path or asymptotic estimate is supplied as an input hypothesis.  The
combined lower-and-upper public theorem remains downstream.
-/

noncomputable section

namespace QEC.Coding.PeriodicCubical4

open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian

variable {L : Nat} [NeZero L] [Fact (1 < L)]

abbrev SweepSite (L : Nat) :=
  StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.Site L

/-- Embed a square site in the primal `xy` membrane at fixed `z,w`. -/
def primalSweepPlaquette (z w : ZMod L) (p : SweepSite L) : Plaquette L :=
  (coord4 (ZMod.finEquiv L p.1) (ZMod.finEquiv L p.2) z w, .xy)

/-- Embed a square site in the dual `zw` membrane represented on `xy`
plaquettes at fixed `x,y`. -/
def dualSweepPlaquette (x y : ZMod L) (p : SweepSite L) : Plaquette L :=
  (coord4 x y (ZMod.finEquiv L p.1) (ZMod.finEquiv L p.2), .xy)

theorem primalSweepPlaquette_injective (z w : ZMod L) :
    Function.Injective (primalSweepPlaquette z w) := by
  intro p q hpq
  have hcoord :
      coord4 (ZMod.finEquiv L p.1) (ZMod.finEquiv L p.2) z w =
        coord4 (ZMod.finEquiv L q.1) (ZMod.finEquiv L q.2) z w :=
    congrArg Prod.fst hpq
  have hparts := (coord4_eq_coord4_iff _ _ _ _ _ _ _ _).mp hcoord
  exact Prod.ext
    ((ZMod.finEquiv L).injective hparts.1)
    ((ZMod.finEquiv L).injective hparts.2.1)

theorem dualSweepPlaquette_injective (x y : ZMod L) :
    Function.Injective (dualSweepPlaquette x y) := by
  intro p q hpq
  have hcoord :
      coord4 x y (ZMod.finEquiv L p.1) (ZMod.finEquiv L p.2) =
        coord4 x y (ZMod.finEquiv L q.1) (ZMod.finEquiv L q.2) :=
    congrArg Prod.fst hpq
  have hparts := (coord4_eq_coord4_iff _ _ _ _ _ _ _ _).mp hcoord
  exact Prod.ext
    ((ZMod.finEquiv L).injective hparts.2.2.1)
    ((ZMod.finEquiv L).injective hparts.2.2.2)

/-- Row-major list of the plaquettes in a primal membrane. -/
def primalSweepPlaquettes (z w : ZMod L) : List (Plaquette L) :=
  (StripGeometry.rowMajorSites L).map (primalSweepPlaquette z w)

/-- Row-major list of the plaquettes in a dual membrane. -/
def dualSweepPlaquettes (x y : ZMod L) : List (Plaquette L) :=
  (StripGeometry.rowMajorSites L).map (dualSweepPlaquette x y)

@[simp] theorem length_primalSweepPlaquettes (z w : ZMod L) :
    (primalSweepPlaquettes z w).length = L * L := by
  simp [primalSweepPlaquettes]

@[simp] theorem length_dualSweepPlaquettes (x y : ZMod L) :
    (dualSweepPlaquettes x y).length = L * L := by
  simp [dualSweepPlaquettes]

theorem primalSweepPlaquettes_nodup (z w : ZMod L) :
    (primalSweepPlaquettes z w).Nodup := by
  exact (StripGeometry.rowMajorSites_nodup L).map
    (primalSweepPlaquette_injective z w)

theorem dualSweepPlaquettes_nodup (x y : ZMod L) :
    (dualSweepPlaquettes x y).Nodup := by
  exact (StripGeometry.rowMajorSites_nodup L).map
    (dualSweepPlaquette_injective x y)

@[simp] theorem mem_primalSweepPlaquettes_toFinset
    (z w : ZMod L) (q : Plaquette L) :
    q ∈ (primalSweepPlaquettes z w).toFinset ↔
      q.2 = .xy ∧ q.1 .z = z ∧ q.1 .w = w := by
  constructor
  · intro hq
    rcases List.mem_map.mp (List.mem_toFinset.mp hq) with ⟨p, hp, rfl⟩
    simp [primalSweepPlaquette]
  · rintro ⟨hplane, hz, hw⟩
    let p : SweepSite L :=
      ((ZMod.finEquiv L).symm (q.1 .x), (ZMod.finEquiv L).symm (q.1 .y))
    have hp : p ∈ StripGeometry.rowMajorSites L := by
      rw [← List.mem_toFinset, StripGeometry.rowMajorSites_toFinset]
      simp
    rw [List.mem_toFinset, primalSweepPlaquettes, List.mem_map]
    refine ⟨p, hp, ?_⟩
    apply Prod.ext
    · ext a
      cases a <;>
        simp [primalSweepPlaquette, p, hz, hw]
    · exact hplane.symm

@[simp] theorem mem_dualSweepPlaquettes_toFinset
    (x y : ZMod L) (q : Plaquette L) :
    q ∈ (dualSweepPlaquettes x y).toFinset ↔
      q.2 = .xy ∧ q.1 .x = x ∧ q.1 .y = y := by
  constructor
  · intro hq
    rcases List.mem_map.mp (List.mem_toFinset.mp hq) with ⟨p, hp, rfl⟩
    simp [dualSweepPlaquette]
  · rintro ⟨hplane, hx, hy⟩
    let p : SweepSite L :=
      ((ZMod.finEquiv L).symm (q.1 .z), (ZMod.finEquiv L).symm (q.1 .w))
    have hp : p ∈ StripGeometry.rowMajorSites L := by
      rw [← List.mem_toFinset, StripGeometry.rowMajorSites_toFinset]
      simp
    rw [List.mem_toFinset, dualSweepPlaquettes, List.mem_map]
    refine ⟨p, hp, ?_⟩
    apply Prod.ext
    · ext a
      cases a <;>
        simp [dualSweepPlaquette, p, hx, hy]
    · exact hplane.symm

theorem primalXYMembrane_eq_indicator_sweepPlaquettes (z w : ZMod L) :
    primalXYMembrane z w = fun q =>
      if q ∈ (primalSweepPlaquettes z w).toFinset then 1 else 0 := by
  funext q
  rcases q with ⟨c, plane⟩
  rw [← show coord4 (c .x) (c .y) (c .z) (c .w) = c by
    ext a
    cases a <;> rfl]
  rw [primalXYMembrane_apply_coord4]
  simp only [mem_primalSweepPlaquettes_toFinset]
  simp <;> rfl

theorem dualXYMembrane_eq_indicator_sweepPlaquettes (x y : ZMod L) :
    dualXYMembrane x y = fun q =>
      if q ∈ (dualSweepPlaquettes x y).toFinset then 1 else 0 := by
  funext q
  rcases q with ⟨c, plane⟩
  rw [← show coord4 (c .x) (c .y) (c .z) (c .w) = c by
    ext a
    cases a <;> rfl]
  rw [dualXYMembrane_apply_coord4]
  simp only [mem_dualSweepPlaquettes_toFinset]
  simp <;> rfl

/-- Actual primal plaquettes filled after the first `n` membrane steps. -/
def primalSweepRegion (z w : ZMod L) (n : Nat) : Finset (Plaquette L) :=
  ((primalSweepPlaquettes z w).take n).toFinset

/-- Actual dual plaquettes filled after the first `n` membrane steps. -/
def dualSweepRegion (x y : ZMod L) (n : Nat) : Finset (Plaquette L) :=
  ((dualSweepPlaquettes x y).take n).toFinset

/-- The primal prefix 2-chain as the indicator of its concrete region. -/
def primalSweepPrefix (z w : ZMod L) (n : Nat) :
    Word (ZMod 2) (Plaquette L) :=
  fun q => if q ∈ primalSweepRegion z w n then 1 else 0

/-- The dual prefix 2-chain as the indicator of its concrete region. -/
def dualSweepPrefix (x y : ZMod L) (n : Nat) :
    Word (ZMod 2) (Plaquette L) :=
  fun q => if q ∈ dualSweepRegion x y n then 1 else 0

theorem primalSweepRegion_subset (z w : ZMod L) (n : Nat) :
    primalSweepRegion z w n ⊆ (primalSweepPlaquettes z w).toFinset := by
  intro q hq
  rw [primalSweepRegion, List.mem_toFinset] at hq
  rw [List.mem_toFinset]
  exact List.mem_of_mem_take hq

theorem dualSweepRegion_subset (x y : ZMod L) (n : Nat) :
    dualSweepRegion x y n ⊆ (dualSweepPlaquettes x y).toFinset := by
  intro q hq
  rw [dualSweepRegion, List.mem_toFinset] at hq
  rw [List.mem_toFinset]
  exact List.mem_of_mem_take hq

@[simp] theorem primalSweepPlaquette_mem_sweepRegion_iff
    (z w : ZMod L) (p : SweepSite L) (n : Nat) :
    primalSweepPlaquette z w p ∈ primalSweepRegion z w n ↔
      StripGeometry.rowMajorIndex p < min n (L * L) := by
  rw [primalSweepRegion, List.mem_toFinset, primalSweepPlaquettes,
    ← List.map_take, List.mem_map]
  constructor
  · rintro ⟨q, hq, hpq⟩
    have hqp : q = p :=
      (primalSweepPlaquette_injective z w) hpq
    subst q
    exact (StripGeometry.mem_take_rowMajorSites_iff p).1 hq
  · intro hp
    exact ⟨p, (StripGeometry.mem_take_rowMajorSites_iff p).2 hp, rfl⟩

@[simp] theorem dualSweepPlaquette_mem_sweepRegion_iff
    (x y : ZMod L) (p : SweepSite L) (n : Nat) :
    dualSweepPlaquette x y p ∈ dualSweepRegion x y n ↔
      StripGeometry.rowMajorIndex p < min n (L * L) := by
  rw [dualSweepRegion, List.mem_toFinset, dualSweepPlaquettes,
    ← List.map_take, List.mem_map]
  constructor
  · rintro ⟨q, hq, hpq⟩
    have hqp : q = p :=
      (dualSweepPlaquette_injective x y) hpq
    subst q
    exact (StripGeometry.mem_take_rowMajorSites_iff p).1 hq
  · intro hp
    exact ⟨p, (StripGeometry.mem_take_rowMajorSites_iff p).2 hp, rfl⟩

/-- The two row bands that can meet a cyclic row-major cut.  Width two is
enough for a selected check joining two plaquettes of either membrane. -/
def sweepSiteFrontier (L n : Nat) : Finset (SweepSite L) :=
  StripGeometry.movingFrontier L 0 L (n / L) 2 ∪
    StripGeometry.seamFrontier L 0 L 2

theorem card_sweepSiteFrontier_le (L n : Nat) :
    (sweepSiteFrontier L n).card ≤ 4 * L := by
  calc
    (sweepSiteFrontier L n).card ≤
        (StripGeometry.movingFrontier L 0 L (n / L) 2).card +
          (StripGeometry.seamFrontier L 0 L 2).card :=
      Finset.card_union_le ..
    _ ≤ L * 2 + L * 2 :=
      Nat.add_le_add
        (StripGeometry.card_movingFrontier_le L 0 L (n / L) 2)
        (StripGeometry.card_seamFrontier_le L 0 L 2)
    _ = 4 * L := by omega

/-- Primal plaquettes incident on the row-major moving cut or periodic seam. -/
def primalSweepFrontier (z w : ZMod L) (n : Nat) : Finset (Plaquette L) :=
  (sweepSiteFrontier L n).image (primalSweepPlaquette z w)

/-- Dual plaquettes incident on the row-major moving cut or periodic seam. -/
def dualSweepFrontier (x y : ZMod L) (n : Nat) : Finset (Plaquette L) :=
  (sweepSiteFrontier L n).image (dualSweepPlaquette x y)

theorem card_primalSweepFrontier_le (z w : ZMod L) (n : Nat) :
    (primalSweepFrontier z w n).card ≤ 4 * L := by
  exact Finset.card_image_le.trans (card_sweepSiteFrontier_le L n)

theorem card_dualSweepFrontier_le (x y : ZMod L) (n : Nat) :
    (dualSweepFrontier x y n).card ≤ 4 * L := by
  exact Finset.card_image_le.trans (card_sweepSiteFrontier_le L n)

private theorem fin_add_one_val_cases (i : Fin L) :
    (i + 1).val = i.val + 1 ∨
      ((i + 1).val = 0 ∧ i.val + 1 = L) := by
  by_cases hi : i.val + 1 < L
  · left
    simp [Fin.add_def, Nat.mod_eq_of_lt hi]
  · right
    have hiL : i.val + 1 = L := by omega
    simp [Fin.add_def, hiL]

private theorem mem_periodicHorizontalInterval_two_of_row_eq_or_succ
    (a : Fin L) (p : SweepSite L)
    (hp : p.2 = a ∨ p.2 = a + 1) :
    p ∈ StripGeometry.periodicHorizontalInterval L a.val 2 := by
  rw [StripGeometry.mem_periodicHorizontalInterval_iff]
  have ha : a.val % L = a.val := Nat.mod_eq_of_lt a.isLt
  rw [ha]
  rcases hp with rfl | hp
  · left
    omega
  · rw [hp]
    rcases fin_add_one_val_cases a with hnext | ⟨hzero, hwrap⟩
    · left
      omega
    · right
      omega

private theorem fin_eq_or_succ_of_finEquiv_eq_or_add_one
    (a : ZMod L) (i : Fin L)
    (hi : (ZMod.finEquiv L) i = a ∨
      (ZMod.finEquiv L) i = a + 1) :
    i = (ZMod.finEquiv L).symm a ∨
      i = (ZMod.finEquiv L).symm a + 1 := by
  rcases hi with hi | hi
  · left
    exact (ZMod.finEquiv L).injective
      (hi.trans ((ZMod.finEquiv L).apply_symm_apply a).symm)
  · right
    apply (ZMod.finEquiv L).injective
    rw [(ZMod.finEquiv L).map_add,
      (ZMod.finEquiv L).apply_symm_apply, map_one]
    exact hi

private theorem primal_link_slice_row_interval
    (z w : ZMod L) (e : Link L) :
    ∃ start : Nat, ∀ p : SweepSite L,
      primalSweepPlaquette z w p ∈ linkPlaquettes e →
        p ∈ StripGeometry.periodicHorizontalInterval L start 2 := by
  rcases e with ⟨c, a⟩
  cases a with
  | x =>
      let base : Fin L := (ZMod.finEquiv L).symm (c .y - 1)
      refine ⟨base.val, fun p hp => ?_⟩
      simp [linkPlaquettes, primalSweepPlaquette, unshift] at hp
      apply mem_periodicHorizontalInterval_two_of_row_eq_or_succ base p
      apply fin_eq_or_succ_of_finEquiv_eq_or_add_one (c .y - 1) p.2
      rcases hp with hp | hp
      · right
        have hy := congrFun hp .y
        simpa using hy
      · left
        have hy := congrFun hp .y
        simpa using hy
  | y =>
      let base : Fin L := (ZMod.finEquiv L).symm (c .y)
      refine ⟨base.val, fun p hp => ?_⟩
      simp [linkPlaquettes, primalSweepPlaquette, unshift] at hp
      apply mem_periodicHorizontalInterval_two_of_row_eq_or_succ base p
      left
      apply (ZMod.finEquiv L).injective
      rw [(ZMod.finEquiv L).apply_symm_apply]
      rcases hp with hp | hp
      · exact congrFun hp .y
      · simpa using congrFun hp .y
  | z =>
      refine ⟨0, fun p hp => ?_⟩
      simp [linkPlaquettes, primalSweepPlaquette, unshift] at hp
  | w =>
      refine ⟨0, fun p hp => ?_⟩
      simp [linkPlaquettes, primalSweepPlaquette, unshift] at hp

private theorem dual_cube_slice_row_interval
    (x y : ZMod L) (c : Cube L) :
    ∃ start : Nat, ∀ p : SweepSite L,
      dualSweepPlaquette x y p ∈ cubePlaquettes c →
        p ∈ StripGeometry.periodicHorizontalInterval L start 2 := by
  rcases c with ⟨r, v⟩
  cases v with
  | xyz =>
      let base : Fin L := (ZMod.finEquiv L).symm (r .w)
      refine ⟨base.val, fun p hp => ?_⟩
      simp [cubePlaquettes, dualSweepPlaquette] at hp
      apply mem_periodicHorizontalInterval_two_of_row_eq_or_succ base p
      left
      apply (ZMod.finEquiv L).injective
      rw [(ZMod.finEquiv L).apply_symm_apply]
      rcases hp with hp | hp
      · exact congrFun hp .w
      · simpa [shift] using congrFun hp .w
  | xyw =>
      let base : Fin L := (ZMod.finEquiv L).symm (r .w)
      refine ⟨base.val, fun p hp => ?_⟩
      simp [cubePlaquettes, dualSweepPlaquette] at hp
      apply mem_periodicHorizontalInterval_two_of_row_eq_or_succ base p
      apply fin_eq_or_succ_of_finEquiv_eq_or_add_one (r .w) p.2
      rcases hp with hp | hp
      · left
        exact congrFun hp .w
      · right
        simpa [shift] using congrFun hp .w
  | xzw =>
      refine ⟨0, fun p hp => ?_⟩
      simp [cubePlaquettes, dualSweepPlaquette] at hp
  | yzw =>
      refine ⟨0, fun p hp => ?_⟩
      simp [cubePlaquettes, dualSweepPlaquette] at hp

private theorem mem_sweepSiteFrontier_of_periodic_crossing
    (n start : Nat) (p q : SweepSite L)
    (hpInterval :
      p ∈ StripGeometry.periodicHorizontalInterval L start 2)
    (hqInterval :
      q ∈ StripGeometry.periodicHorizontalInterval L start 2)
    (hpCursor : p.2.val ≤ n / L) (hCursorQ : n / L ≤ q.2.val) :
    p ∈ sweepSiteFrontier L n := by
  have hpStrip :
      p ∈ StripGeometry.openVerticalInterval L 0 L := by
    simp [StripGeometry.openVerticalInterval]
  have hpRows :=
    (StripGeometry.mem_periodicHorizontalInterval_iff p).1 hpInterval
  have hqRows :=
    (StripGeometry.mem_periodicHorizontalInterval_iff q).1 hqInterval
  rw [sweepSiteFrontier, Finset.mem_union,
    StripGeometry.mem_movingFrontier_iff,
    StripGeometry.mem_seamFrontier_iff]
  rcases hpRows with hpMain | hpWrap
  · rcases hqRows with hqMain | hqWrap
    · left
      exact ⟨hpStrip, hpCursor, by omega⟩
    · by_cases hpr : p.2.val < 2
      · right
        exact ⟨hpStrip, hpr⟩
      · left
        exact ⟨hpStrip, hpCursor, by omega⟩
  · right
    refine ⟨hpStrip, ?_⟩
    have hL : 0 < L := NeZero.pos L
    have hstartLt : start % L < L := Nat.mod_lt start hL
    omega

private theorem support_restrictBinaryTo_subset_support
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Finset ι) (Q : Binary ι) :
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

theorem restrict_primalMembrane_vector_eq_prefix
    (z w : ZMod L) (n : Nat) :
    (Locality.restrictBinaryTo (primalSweepRegion z w n)
      (primalMembraneError (primalXYMembrane z w))).vector =
    (primalMembraneError (primalSweepPrefix z w n)).vector := by
  apply (SymplecticVector.toProdEquiv (F := ZMod 2) (ι := Plaquette L)).injective
  apply Prod.ext
  · funext q
    change (if q ∈ primalSweepRegion z w n then 0 else 0) = 0
    simp
  · funext q
    change (if q ∈ primalSweepRegion z w n then primalXYMembrane z w q else 0) =
      primalSweepPrefix z w n q
    by_cases hq : q ∈ primalSweepRegion z w n
    · have hfull := primalSweepRegion_subset z w n hq
      simp [primalSweepPrefix, hq,
        primalXYMembrane_eq_indicator_sweepPlaquettes, hfull]
    · simp [primalSweepPrefix, hq]

theorem restrict_dualMembrane_vector_eq_prefix
    (x y : ZMod L) (n : Nat) :
    (Locality.restrictBinaryTo (dualSweepRegion x y n)
      (dualMembraneError (dualXYMembrane x y))).vector =
    (dualMembraneError (dualSweepPrefix x y n)).vector := by
  apply (SymplecticVector.toProdEquiv (F := ZMod 2) (ι := Plaquette L)).injective
  apply Prod.ext
  · funext q
    change (if q ∈ dualSweepRegion x y n then dualXYMembrane x y q else 0) =
      dualSweepPrefix x y n q
    by_cases hq : q ∈ dualSweepRegion x y n
    · have hfull := dualSweepRegion_subset x y n hq
      simp [dualSweepPrefix, hq,
        dualXYMembrane_eq_indicator_sweepPlaquettes, hfull]
    · simp [dualSweepPrefix, hq]
  · funext q
    change (if q ∈ dualSweepRegion x y n then 0 else 0) = 0
    simp

/-- Every selected check violated by a primal sweep prefix is incident on the
lifted moving frontier or the periodic seam. -/
theorem violatedGenerators_primalSweepPrefix_subset_frontier
    (z w : ZMod L) (n : Nat) (hn : n ≤ L * L) :
    (toricHamiltonian (L := L)).violatedGenerators
        (primalMembraneError (primalSweepPrefix z w n)) ⊆
      (toricHamiltonian (L := L)).incidentGeneratorUnion
        (primalSweepFrontier z w n) := by
  intro j hj
  let R := primalSweepRegion z w n
  let Q := primalMembraneError (primalXYMembrane z w)
  let E := Locality.restrictBinaryTo R Q
  let F := Locality.restrictBinaryTo Rᶜ Q
  have hEVector :
      E.vector = (primalMembraneError (primalSweepPrefix z w n)).vector := by
    simpa [E, Q, R] using restrict_primalMembrane_vector_eq_prefix z w n
  have hjE : j ∈ (toricHamiltonian (L := L)).violatedGenerators E := by
    rw [(toricHamiltonian (L := L)).violatedGenerators_eq_of_vector_eq
      E (primalMembraneError (primalSweepPrefix z w n)) hEVector]
    exact hj
  rw [mem_violatedGenerators] at hjE
  have hnotDisjointE :
      ¬ Disjoint (support E)
        (support ((toricHamiltonian (L := L)).generators j)) := by
    intro hdisjoint
    exact hjE (QEC.Locality.commutes_of_disjoint_support E
      ((toricHamiltonian (L := L)).generators j) hdisjoint)
  obtain ⟨p, hpE, hpGenerator⟩ :=
    Finset.not_disjoint_iff.mp hnotDisjointE
  have hpR : p ∈ R :=
    Locality.support_restrictBinaryTo_subset R Q hpE
  have hRDisjoint : Disjoint R Rᶜ := by
    apply Finset.disjoint_left.mpr
    intro i hiR hiCompl
    exact (Finset.mem_compl.mp hiCompl) hiR
  have hQCover : support Q ⊆ R ∪ Rᶜ := by
    intro i _hi
    by_cases hiR : i ∈ R
    · exact Finset.mem_union_left _ hiR
    · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hiR)
  have hdecomp : Q.vector = E.vector + F.vector :=
    Locality.restrictBinaryTo_vector_add_of_support_subset_union
      R Rᶜ Q hRDisjoint hQCover
  have hQNormalizer :
      (toricHamiltonian (L := L)).code.1.InBinaryNormalizer Q := by
    intro S hS
    apply primalZLogical_in_normalizer z w S
    have hS' :
        S ∈ (toricSourceValidCode (L := L)).1.generatedGroup := by
      simpa [toricHamiltonian_code, Q, primalZLogical,
        primalMembraneError] using hS
    have hgen :
        S ∈ generatedStabilizerSet (toricGenerator (L := L)) := by
      rw [toricGenerator_generated_eq]
      exact hS'
    simpa [generatedStabilizerSet] using hgen
  have hFNotCommutes :
      ¬ Commutes F ((toricHamiltonian (L := L)).generators j) :=
    (toricHamiltonian (L := L)).not_commutes_complement_of_not_commutes_restriction
      Q E F j hQNormalizer hdecomp hjE
  have hnotDisjointF :
      ¬ Disjoint (support F)
        (support ((toricHamiltonian (L := L)).generators j)) := by
    intro hdisjoint
    exact hFNotCommutes
      (QEC.Locality.commutes_of_disjoint_support F
        ((toricHamiltonian (L := L)).generators j) hdisjoint)
  obtain ⟨q, hqF, hqGenerator⟩ :=
    Finset.not_disjoint_iff.mp hnotDisjointF
  have hqCompl : q ∈ Rᶜ :=
    Locality.support_restrictBinaryTo_subset Rᶜ Q hqF
  have hqNotR : q ∉ R := Finset.mem_compl.mp hqCompl
  have hqQ : q ∈ support Q :=
    support_restrictBinaryTo_subset_support Rᶜ Q hqF
  have hpAll : p ∈ (primalSweepPlaquettes z w).toFinset :=
    primalSweepRegion_subset z w n (by simpa [R] using hpR)
  have hqAll : q ∈ (primalSweepPlaquettes z w).toFinset := by
    change q ∈ support (primalMembraneError (primalXYMembrane z w)) at hqQ
    rw [primalMembraneError, support_cssZCheck, hammingSupport] at hqQ
    have hqValue : primalXYMembrane z w q ≠ 0 :=
      (Finset.mem_filter.mp hqQ).2
    by_contra hq
    simp [primalXYMembrane_eq_indicator_sweepPlaquettes, hq] at hqValue
  rcases List.mem_map.mp (List.mem_toFinset.mp hpAll) with
    ⟨ps, _hps, rfl⟩
  rcases List.mem_map.mp (List.mem_toFinset.mp hqAll) with
    ⟨qs, _hqs, rfl⟩
  have hpsPrefix : ps ∈ StripGeometry.rowMajorPrefix L n := by
    rw [StripGeometry.mem_rowMajorPrefix_iff]
    have hmem :=
      (primalSweepPlaquette_mem_sweepRegion_iff z w ps n).1
        (by simpa [R] using hpR)
    simpa [min_eq_left hn] using hmem
  have hqsNotPrefix : qs ∉ StripGeometry.rowMajorPrefix L n := by
    rw [StripGeometry.mem_rowMajorPrefix_iff]
    intro hindex
    apply hqNotR
    have hmem : StripGeometry.rowMajorIndex qs < min n (L * L) := by
      simpa [min_eq_left hn] using hindex
    simpa [R] using
      (primalSweepPlaquette_mem_sweepRegion_iff z w qs n).2 hmem
  have hRows := StripGeometry.rowMajorPrefix_row_bounds
    (NeZero.pos L) ps qs hpsPrefix hqsNotPrefix
  cases j with
  | inl e =>
      rw [toricHamiltonian_generators, toricGenerator_support_inl] at hpGenerator hqGenerator
      obtain ⟨start, hinterval⟩ := primal_link_slice_row_interval z w e
      have hpsFrontier : ps ∈ sweepSiteFrontier L n :=
        mem_sweepSiteFrontier_of_periodic_crossing n start ps qs
          (hinterval ps hpGenerator) (hinterval qs hqGenerator)
          hRows.1 hRows.2
      have hpFrontier :
          primalSweepPlaquette z w ps ∈ primalSweepFrontier z w n := by
        exact Finset.mem_image.mpr ⟨ps, hpsFrontier, rfl⟩
      have hpGeneratorSupport :
          primalSweepPlaquette z w ps ∈
            support ((toricHamiltonian (L := L)).generators (Sum.inl e)) := by
        rw [toricHamiltonian_generators, toricGenerator_support_inl]
        exact hpGenerator
      exact
        (toricHamiltonian (L := L)).mem_incidentGeneratorUnion_of_mem_generatorSupport
          _ (primalSweepPlaquette z w ps) (Sum.inl e)
            hpFrontier hpGeneratorSupport
  | inr c =>
      exfalso
      rw [(toricHamiltonian (L := L)).violatedGenerators_eq_syndromeSupport,
        syndromeSupport_primalMembrane] at hj
      simp at hj

/-- Every selected check violated by a dual sweep prefix is incident on the
lifted moving frontier or the periodic seam. -/
theorem violatedGenerators_dualSweepPrefix_subset_frontier
    (x y : ZMod L) (n : Nat) (hn : n ≤ L * L) :
    (toricHamiltonian (L := L)).violatedGenerators
        (dualMembraneError (dualSweepPrefix x y n)) ⊆
      (toricHamiltonian (L := L)).incidentGeneratorUnion
        (dualSweepFrontier x y n) := by
  intro j hj
  let R := dualSweepRegion x y n
  let Q := dualMembraneError (dualXYMembrane x y)
  let E := Locality.restrictBinaryTo R Q
  let F := Locality.restrictBinaryTo Rᶜ Q
  have hEVector :
      E.vector = (dualMembraneError (dualSweepPrefix x y n)).vector := by
    simpa [E, Q, R] using restrict_dualMembrane_vector_eq_prefix x y n
  have hjE : j ∈ (toricHamiltonian (L := L)).violatedGenerators E := by
    rw [(toricHamiltonian (L := L)).violatedGenerators_eq_of_vector_eq
      E (dualMembraneError (dualSweepPrefix x y n)) hEVector]
    exact hj
  rw [mem_violatedGenerators] at hjE
  have hnotDisjointE :
      ¬ Disjoint (support E)
        (support ((toricHamiltonian (L := L)).generators j)) := by
    intro hdisjoint
    exact hjE (QEC.Locality.commutes_of_disjoint_support E
      ((toricHamiltonian (L := L)).generators j) hdisjoint)
  obtain ⟨p, hpE, hpGenerator⟩ :=
    Finset.not_disjoint_iff.mp hnotDisjointE
  have hpR : p ∈ R :=
    Locality.support_restrictBinaryTo_subset R Q hpE
  have hRDisjoint : Disjoint R Rᶜ := by
    apply Finset.disjoint_left.mpr
    intro i hiR hiCompl
    exact (Finset.mem_compl.mp hiCompl) hiR
  have hQCover : support Q ⊆ R ∪ Rᶜ := by
    intro i _hi
    by_cases hiR : i ∈ R
    · exact Finset.mem_union_left _ hiR
    · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hiR)
  have hdecomp : Q.vector = E.vector + F.vector :=
    Locality.restrictBinaryTo_vector_add_of_support_subset_union
      R Rᶜ Q hRDisjoint hQCover
  have hQNormalizer :
      (toricHamiltonian (L := L)).code.1.InBinaryNormalizer Q := by
    intro S hS
    apply dualXLogical_in_normalizer x y S
    have hS' :
        S ∈ (toricSourceValidCode (L := L)).1.generatedGroup := by
      simpa [toricHamiltonian_code, Q, dualXLogical,
        dualMembraneError] using hS
    have hgen :
        S ∈ generatedStabilizerSet (toricGenerator (L := L)) := by
      rw [toricGenerator_generated_eq]
      exact hS'
    simpa [generatedStabilizerSet] using hgen
  have hFNotCommutes :
      ¬ Commutes F ((toricHamiltonian (L := L)).generators j) :=
    (toricHamiltonian (L := L)).not_commutes_complement_of_not_commutes_restriction
      Q E F j hQNormalizer hdecomp hjE
  have hnotDisjointF :
      ¬ Disjoint (support F)
        (support ((toricHamiltonian (L := L)).generators j)) := by
    intro hdisjoint
    exact hFNotCommutes
      (QEC.Locality.commutes_of_disjoint_support F
        ((toricHamiltonian (L := L)).generators j) hdisjoint)
  obtain ⟨q, hqF, hqGenerator⟩ :=
    Finset.not_disjoint_iff.mp hnotDisjointF
  have hqCompl : q ∈ Rᶜ :=
    Locality.support_restrictBinaryTo_subset Rᶜ Q hqF
  have hqNotR : q ∉ R := Finset.mem_compl.mp hqCompl
  have hqQ : q ∈ support Q :=
    support_restrictBinaryTo_subset_support Rᶜ Q hqF
  have hpAll : p ∈ (dualSweepPlaquettes x y).toFinset :=
    dualSweepRegion_subset x y n (by simpa [R] using hpR)
  have hqAll : q ∈ (dualSweepPlaquettes x y).toFinset := by
    change q ∈ support (dualMembraneError (dualXYMembrane x y)) at hqQ
    rw [dualMembraneError, support_cssXCheck, hammingSupport] at hqQ
    have hqValue : dualXYMembrane x y q ≠ 0 :=
      (Finset.mem_filter.mp hqQ).2
    by_contra hq
    simp [dualXYMembrane_eq_indicator_sweepPlaquettes, hq] at hqValue
  rcases List.mem_map.mp (List.mem_toFinset.mp hpAll) with
    ⟨ps, _hps, rfl⟩
  rcases List.mem_map.mp (List.mem_toFinset.mp hqAll) with
    ⟨qs, _hqs, rfl⟩
  have hpsPrefix : ps ∈ StripGeometry.rowMajorPrefix L n := by
    rw [StripGeometry.mem_rowMajorPrefix_iff]
    have hmem :=
      (dualSweepPlaquette_mem_sweepRegion_iff x y ps n).1
        (by simpa [R] using hpR)
    simpa [min_eq_left hn] using hmem
  have hqsNotPrefix : qs ∉ StripGeometry.rowMajorPrefix L n := by
    rw [StripGeometry.mem_rowMajorPrefix_iff]
    intro hindex
    apply hqNotR
    have hmem : StripGeometry.rowMajorIndex qs < min n (L * L) := by
      simpa [min_eq_left hn] using hindex
    simpa [R] using
      (dualSweepPlaquette_mem_sweepRegion_iff x y qs n).2 hmem
  have hRows := StripGeometry.rowMajorPrefix_row_bounds
    (NeZero.pos L) ps qs hpsPrefix hqsNotPrefix
  cases j with
  | inl e =>
      exfalso
      rw [(toricHamiltonian (L := L)).violatedGenerators_eq_syndromeSupport,
        syndromeSupport_dualMembrane] at hj
      simp at hj
  | inr c =>
      rw [toricHamiltonian_generators, toricGenerator_support_inr] at hpGenerator hqGenerator
      obtain ⟨start, hinterval⟩ := dual_cube_slice_row_interval x y c
      have hpsFrontier : ps ∈ sweepSiteFrontier L n :=
        mem_sweepSiteFrontier_of_periodic_crossing n start ps qs
          (hinterval ps hpGenerator) (hinterval qs hqGenerator)
          hRows.1 hRows.2
      have hpFrontier :
          dualSweepPlaquette x y ps ∈ dualSweepFrontier x y n := by
        exact Finset.mem_image.mpr ⟨ps, hpsFrontier, rfl⟩
      have hpGeneratorSupport :
          dualSweepPlaquette x y ps ∈
            support ((toricHamiltonian (L := L)).generators (Sum.inr c)) := by
        rw [toricHamiltonian_generators, toricGenerator_support_inr]
        exact hpGenerator
      exact
        (toricHamiltonian (L := L)).mem_incidentGeneratorUnion_of_mem_generatorSupport
          _ (dualSweepPlaquette x y ps) (Sum.inr c)
            hpFrontier hpGeneratorSupport

/-- The primal defect loop exposed by any row-major prefix has linear length. -/
theorem primalLoopLength_sweepPrefix_le
    (z w : ZMod L) (n : Nat) (hn : n ≤ L * L) :
    primalLoopLength (primalSweepPrefix z w n) ≤ 32 * L := by
  rw [← unitDefectEnergy_primalMembrane]
  unfold unitDefectEnergy
  calc
    ((toricHamiltonian (L := L)).violatedGenerators
        (primalMembraneError (primalSweepPrefix z w n))).card ≤
        ((toricHamiltonian (L := L)).incidentGeneratorUnion
          (primalSweepFrontier z w n)).card :=
      Finset.card_le_card
        (violatedGenerators_primalSweepPrefix_subset_frontier z w n hn)
    _ ≤ (primalSweepFrontier z w n).card *
        (toricHamiltonian (L := L)).participationBound :=
      (toricHamiltonian (L := L)).card_incidentGeneratorUnion_le _
    _ ≤ (4 * L) * (toricHamiltonian (L := L)).participationBound :=
      Nat.mul_le_mul_right _ (card_primalSweepFrontier_le z w n)
    _ = 32 * L := by simp [toricHamiltonian]; omega

/-- The dual defect loop exposed by any row-major prefix has linear length. -/
theorem dualLoopLength_sweepPrefix_le
    (x y : ZMod L) (n : Nat) (hn : n ≤ L * L) :
    dualLoopLength (dualSweepPrefix x y n) ≤ 32 * L := by
  rw [← unitDefectEnergy_dualMembrane]
  unfold unitDefectEnergy
  calc
    ((toricHamiltonian (L := L)).violatedGenerators
        (dualMembraneError (dualSweepPrefix x y n))).card ≤
        ((toricHamiltonian (L := L)).incidentGeneratorUnion
          (dualSweepFrontier x y n)).card :=
      Finset.card_le_card
        (violatedGenerators_dualSweepPrefix_subset_frontier x y n hn)
    _ ≤ (dualSweepFrontier x y n).card *
        (toricHamiltonian (L := L)).participationBound :=
      (toricHamiltonian (L := L)).card_incidentGeneratorUnion_le _
    _ ≤ (4 * L) * (toricHamiltonian (L := L)).participationBound :=
      Nat.mul_le_mul_right _ (card_dualSweepFrontier_le x y n)
    _ = 32 * L := by simp [toricHamiltonian]; omega

/-- BT-normalized excess energy of every primal geometric prefix is linear. -/
theorem btExcessEnergy_primalSweepPrefix_le
    (z w : ZMod L) (n : Nat) (hn : n ≤ L * L) :
    (toricHamiltonian (L := L)).btExcessEnergy
        (primalMembraneError (primalSweepPrefix z w n)) ≤ 64 * L := by
  rw [btExcessEnergy_primalMembrane]
  have h := Nat.mul_le_mul_left 2
    (primalLoopLength_sweepPrefix_le z w n hn)
  omega

/-- BT-normalized excess energy of every dual geometric prefix is linear. -/
theorem btExcessEnergy_dualSweepPrefix_le
    (x y : ZMod L) (n : Nat) (hn : n ≤ L * L) :
    (toricHamiltonian (L := L)).btExcessEnergy
        (dualMembraneError (dualSweepPrefix x y n)) ≤ 64 * L := by
  rw [btExcessEnergy_dualMembrane]
  have h := Nat.mul_le_mul_left 2
    (dualLoopLength_sweepPrefix_le x y n hn)
  omega

/-- Complete a preferred list of sites to an enumeration of the entire finite
qubit set, preserving the preferred prefix. -/
private def completeSiteOrder {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sites : List ι) : List ι :=
  sites ++ (Finset.univ \ sites.toFinset).toList

private theorem completeSiteOrder_nodup
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {sites : List ι} (hnodup : sites.Nodup) :
    (completeSiteOrder sites).Nodup := by
  rw [completeSiteOrder, List.nodup_append']
  refine ⟨hnodup, (Finset.univ \ sites.toFinset).nodup_toList, ?_⟩
  rw [List.disjoint_left]
  intro q hqSites hqRest
  have hqMem : q ∈ Finset.univ \ sites.toFinset := by
    simpa using hqRest
  exact (Finset.mem_sdiff.mp hqMem).2 (by simpa using hqSites)

private theorem completeSiteOrder_toFinset
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sites : List ι) :
    (completeSiteOrder sites).toFinset = Finset.univ := by
  ext q
  simp [completeSiteOrder]

/-- Full plaquette order whose first `L^2` entries sweep the primal membrane. -/
def primalSweepOrder (z w : ZMod L) : List (Plaquette L) :=
  completeSiteOrder (primalSweepPlaquettes z w)

/-- Full plaquette order whose first `L^2` entries sweep the dual membrane. -/
def dualSweepOrder (x y : ZMod L) : List (Plaquette L) :=
  completeSiteOrder (dualSweepPlaquettes x y)

theorem primalSweepOrder_nodup (z w : ZMod L) :
    (primalSweepOrder z w).Nodup :=
  completeSiteOrder_nodup (primalSweepPlaquettes_nodup z w)

theorem dualSweepOrder_nodup (x y : ZMod L) :
    (dualSweepOrder x y).Nodup :=
  completeSiteOrder_nodup (dualSweepPlaquettes_nodup x y)

@[simp] theorem primalSweepOrder_toFinset (z w : ZMod L) :
    (primalSweepOrder z w).toFinset = Finset.univ :=
  completeSiteOrder_toFinset _

@[simp] theorem dualSweepOrder_toFinset (x y : ZMod L) :
    (dualSweepOrder x y).toFinset = Finset.univ :=
  completeSiteOrder_toFinset _

theorem take_primalSweepOrder_of_le (z w : ZMod L) {n : Nat}
    (hn : n ≤ L * L) :
    (primalSweepOrder z w).take n =
      (primalSweepPlaquettes z w).take n := by
  rw [primalSweepOrder, completeSiteOrder, List.take_append_of_le_length]
  simpa using hn

theorem take_dualSweepOrder_of_le (x y : ZMod L) {n : Nat}
    (hn : n ≤ L * L) :
    (dualSweepOrder x y).take n =
      (dualSweepPlaquettes x y).take n := by
  rw [dualSweepOrder, completeSiteOrder, List.take_append_of_le_length]
  simpa using hn

private theorem primalSweepPlaquettes_subset_take_order
    (z w : ZMod L) (n : Nat) (hn : L * L ≤ n) :
    (primalSweepPlaquettes z w).toFinset ⊆
      ((primalSweepOrder z w).take n).toFinset := by
  intro q hq
  rw [List.mem_toFinset] at hq ⊢
  rw [primalSweepOrder, completeSiteOrder, List.take_append,
    List.mem_append]
  left
  rw [List.take_of_length_le]
  · exact hq
  · simpa using hn

private theorem dualSweepPlaquettes_subset_take_order
    (x y : ZMod L) (n : Nat) (hn : L * L ≤ n) :
    (dualSweepPlaquettes x y).toFinset ⊆
      ((dualSweepOrder x y).take n).toFinset := by
  intro q hq
  rw [List.mem_toFinset] at hq ⊢
  rw [dualSweepOrder, completeSiteOrder, List.take_append,
    List.mem_append]
  left
  rw [List.take_of_length_le]
  · exact hq
  · simpa using hn

/-- The exact single-plaquette path that fills a primal membrane row by row. -/
def primalMembraneSweepPath (z w : ZMod L) :
    PauliErrorPath (ι := Plaquette L) :=
  PauliErrorPath.orderedExact (primalMembraneError (primalXYMembrane z w))
    (primalSweepOrder z w) (primalSweepOrder_nodup z w)
    (primalSweepOrder_toFinset z w)

/-- The exact single-plaquette path that fills a dual membrane row by row. -/
def dualMembraneSweepPath (x y : ZMod L) :
    PauliErrorPath (ι := Plaquette L) :=
  PauliErrorPath.orderedExact (dualMembraneError (dualXYMembrane x y))
    (dualSweepOrder x y) (dualSweepOrder_nodup x y)
    (dualSweepOrder_toFinset x y)

@[simp] theorem primalMembraneSweepPath_endpoint (z w : ZMod L) :
    (primalMembraneSweepPath z w).endpoint =
      primalMembraneError (primalXYMembrane z w) := by
  exact PauliErrorPath.orderedExact_endpoint _ _ _ _

@[simp] theorem dualMembraneSweepPath_endpoint (x y : ZMod L) :
    (dualMembraneSweepPath x y).endpoint =
      dualMembraneError (dualXYMembrane x y) := by
  exact PauliErrorPath.orderedExact_endpoint _ _ _ _

/-- During the geometric part of the primal sweep, the actual accumulated
Pauli vector is exactly the pure-Z error of the concrete row-major prefix. -/
theorem primalMembraneSweepPath_stateAt_vector
    (z w : ZMod L) (n : Nat) (hn : n ≤ L * L) :
    ((primalMembraneSweepPath z w).stateAt n).vector =
      (primalMembraneError (primalSweepPrefix z w n)).vector := by
  have hnOrder : n ≤ (primalSweepOrder z w).length := by
    calc
      n ≤ (primalSweepPlaquettes z w).length := by simpa using hn
      _ ≤ (primalSweepOrder z w).length := by
        simp [primalSweepOrder, completeSiteOrder]
  calc
    ((primalMembraneSweepPath z w).stateAt n).vector =
        (Locality.restrictBinaryTo (primalSweepRegion z w n)
          (primalMembraneError (primalXYMembrane z w))).vector := by
      simpa [primalMembraneSweepPath, primalSweepRegion,
        take_primalSweepOrder_of_le z w hn] using
        (PauliErrorPath.orderedExact_stateAt_vector
          (primalMembraneError (primalXYMembrane z w))
          (primalSweepOrder z w) (primalSweepOrder_nodup z w)
          (primalSweepOrder_toFinset z w) n hnOrder)
    _ = (primalMembraneError (primalSweepPrefix z w n)).vector :=
      restrict_primalMembrane_vector_eq_prefix z w n

/-- During the geometric part of the dual sweep, the actual accumulated
Pauli vector is exactly the pure-X error of the concrete row-major prefix. -/
theorem dualMembraneSweepPath_stateAt_vector
    (x y : ZMod L) (n : Nat) (hn : n ≤ L * L) :
    ((dualMembraneSweepPath x y).stateAt n).vector =
      (dualMembraneError (dualSweepPrefix x y n)).vector := by
  have hnOrder : n ≤ (dualSweepOrder x y).length := by
    calc
      n ≤ (dualSweepPlaquettes x y).length := by simpa using hn
      _ ≤ (dualSweepOrder x y).length := by
        simp [dualSweepOrder, completeSiteOrder]
  calc
    ((dualMembraneSweepPath x y).stateAt n).vector =
        (Locality.restrictBinaryTo (dualSweepRegion x y n)
          (dualMembraneError (dualXYMembrane x y))).vector := by
      simpa [dualMembraneSweepPath, dualSweepRegion,
        take_dualSweepOrder_of_le x y hn] using
        (PauliErrorPath.orderedExact_stateAt_vector
          (dualMembraneError (dualXYMembrane x y))
          (dualSweepOrder x y) (dualSweepOrder_nodup x y)
          (dualSweepOrder_toFinset x y) n hnOrder)
    _ = (dualMembraneError (dualSweepPrefix x y n)).vector :=
      restrict_dualMembrane_vector_eq_prefix x y n

@[simp] theorem length_primalMembraneSweepPath_increments (z w : ZMod L) :
    (primalMembraneSweepPath z w).increments.length =
      (primalSweepOrder z w).length + 1 := by
  simp [primalMembraneSweepPath, PauliErrorPath.orderedExact,
    PauliErrorPath.orderedCore]

@[simp] theorem length_dualMembraneSweepPath_increments (x y : ZMod L) :
    (dualMembraneSweepPath x y).increments.length =
      (dualSweepOrder x y).length + 1 := by
  simp [dualMembraneSweepPath, PauliErrorPath.orderedExact,
    PauliErrorPath.orderedCore]

theorem primalMembraneSweepPath_stateAt_vector_of_membrane_complete
    (z w : ZMod L) (n : Nat) (hmembrane : L * L ≤ n)
    (hcore : n ≤ (primalSweepOrder z w).length) :
    ((primalMembraneSweepPath z w).stateAt n).vector =
      (primalMembraneError (primalXYMembrane z w)).vector := by
  calc
    ((primalMembraneSweepPath z w).stateAt n).vector =
        (Locality.restrictBinaryTo
          ((primalSweepOrder z w).take n).toFinset
          (primalMembraneError (primalXYMembrane z w))).vector := by
      simpa [primalMembraneSweepPath] using
        (PauliErrorPath.orderedExact_stateAt_vector
          (primalMembraneError (primalXYMembrane z w))
          (primalSweepOrder z w) (primalSweepOrder_nodup z w)
          (primalSweepOrder_toFinset z w) n hcore)
    _ = (primalMembraneError (primalXYMembrane z w)).vector := by
      apply (SymplecticVector.toProdEquiv
        (F := ZMod 2) (ι := Plaquette L)).injective
      apply Prod.ext
      · funext q
        change
          (if q ∈ ((primalSweepOrder z w).take n).toFinset then 0 else 0) = 0
        simp
      · funext q
        change
          (if q ∈ ((primalSweepOrder z w).take n).toFinset then
            primalXYMembrane z w q else 0) = primalXYMembrane z w q
        by_cases hq : q ∈ (primalSweepPlaquettes z w).toFinset
        · have hqTake :=
            primalSweepPlaquettes_subset_take_order z w n hmembrane hq
          simp [hqTake]
        · have hqZero : primalXYMembrane z w q = 0 := by
            rw [primalXYMembrane_eq_indicator_sweepPlaquettes]
            simp [hq]
          simp [hqZero]

theorem dualMembraneSweepPath_stateAt_vector_of_membrane_complete
    (x y : ZMod L) (n : Nat) (hmembrane : L * L ≤ n)
    (hcore : n ≤ (dualSweepOrder x y).length) :
    ((dualMembraneSweepPath x y).stateAt n).vector =
      (dualMembraneError (dualXYMembrane x y)).vector := by
  calc
    ((dualMembraneSweepPath x y).stateAt n).vector =
        (Locality.restrictBinaryTo
          ((dualSweepOrder x y).take n).toFinset
          (dualMembraneError (dualXYMembrane x y))).vector := by
      simpa [dualMembraneSweepPath] using
        (PauliErrorPath.orderedExact_stateAt_vector
          (dualMembraneError (dualXYMembrane x y))
          (dualSweepOrder x y) (dualSweepOrder_nodup x y)
          (dualSweepOrder_toFinset x y) n hcore)
    _ = (dualMembraneError (dualXYMembrane x y)).vector := by
      apply (SymplecticVector.toProdEquiv
        (F := ZMod 2) (ι := Plaquette L)).injective
      apply Prod.ext
      · funext q
        change
          (if q ∈ ((dualSweepOrder x y).take n).toFinset then
            dualXYMembrane x y q else 0) = dualXYMembrane x y q
        by_cases hq : q ∈ (dualSweepPlaquettes x y).toFinset
        · have hqTake :=
            dualSweepPlaquettes_subset_take_order x y n hmembrane hq
          simp [hqTake]
        · have hqZero : dualXYMembrane x y q = 0 := by
            rw [dualXYMembrane_eq_indicator_sweepPlaquettes]
            simp [hq]
          simp [hqZero]
      · funext q
        change
          (if q ∈ ((dualSweepOrder x y).take n).toFinset then 0 else 0) = 0
        simp

@[simp] theorem primalLoopLength_primalXYMembrane (z w : ZMod L) :
    primalLoopLength (primalXYMembrane z w) = 0 := by
  simp [primalLoopLength, primalDefectLoop, boundary2_primalXYMembrane,
    HammingWeight]

@[simp] theorem dualLoopLength_dualXYMembrane (x y : ZMod L) :
    dualLoopLength (dualXYMembrane x y) = 0 := by
  simp [dualLoopLength, dualDefectLoop,
    transpose_boundary3_dualXYMembrane, HammingWeight]

theorem btExcessEnergy_primalMembraneSweepPath_stateAt_le
    (z w : ZMod L) (n : Nat)
    (hn : n ≤ (primalMembraneSweepPath z w).increments.length) :
    (toricHamiltonian (L := L)).btExcessEnergy
        ((primalMembraneSweepPath z w).stateAt n) ≤ 64 * L := by
  by_cases hcore : n ≤ (primalSweepOrder z w).length
  · by_cases hgeom : n ≤ L * L
    · calc
        (toricHamiltonian (L := L)).btExcessEnergy
            ((primalMembraneSweepPath z w).stateAt n) =
            (toricHamiltonian (L := L)).btExcessEnergy
              (primalMembraneError (primalSweepPrefix z w n)) :=
          (toricHamiltonian (L := L)).btExcessEnergy_eq_of_vector_eq _ _
            (primalMembraneSweepPath_stateAt_vector z w n hgeom)
        _ ≤ 64 * L := btExcessEnergy_primalSweepPrefix_le z w n hgeom
    · have hmembrane : L * L ≤ n := by omega
      calc
        (toricHamiltonian (L := L)).btExcessEnergy
            ((primalMembraneSweepPath z w).stateAt n) =
            (toricHamiltonian (L := L)).btExcessEnergy
              (primalMembraneError (primalXYMembrane z w)) :=
          (toricHamiltonian (L := L)).btExcessEnergy_eq_of_vector_eq _ _
            (primalMembraneSweepPath_stateAt_vector_of_membrane_complete
              z w n hmembrane hcore)
        _ = 0 := by rw [btExcessEnergy_primalMembrane]; simp
        _ ≤ 64 * L := Nat.zero_le _
  · have hnEnd :
        n = (primalMembraneSweepPath z w).increments.length := by
      rw [length_primalMembraneSweepPath_increments] at hn ⊢
      omega
    subst n
    rw [PauliErrorPath.stateAt_length, primalMembraneSweepPath_endpoint,
      btExcessEnergy_primalMembrane]
    simp

theorem btExcessEnergy_dualMembraneSweepPath_stateAt_le
    (x y : ZMod L) (n : Nat)
    (hn : n ≤ (dualMembraneSweepPath x y).increments.length) :
    (toricHamiltonian (L := L)).btExcessEnergy
        ((dualMembraneSweepPath x y).stateAt n) ≤ 64 * L := by
  by_cases hcore : n ≤ (dualSweepOrder x y).length
  · by_cases hgeom : n ≤ L * L
    · calc
        (toricHamiltonian (L := L)).btExcessEnergy
            ((dualMembraneSweepPath x y).stateAt n) =
            (toricHamiltonian (L := L)).btExcessEnergy
              (dualMembraneError (dualSweepPrefix x y n)) :=
          (toricHamiltonian (L := L)).btExcessEnergy_eq_of_vector_eq _ _
            (dualMembraneSweepPath_stateAt_vector x y n hgeom)
        _ ≤ 64 * L := btExcessEnergy_dualSweepPrefix_le x y n hgeom
    · have hmembrane : L * L ≤ n := by omega
      calc
        (toricHamiltonian (L := L)).btExcessEnergy
            ((dualMembraneSweepPath x y).stateAt n) =
            (toricHamiltonian (L := L)).btExcessEnergy
              (dualMembraneError (dualXYMembrane x y)) :=
          (toricHamiltonian (L := L)).btExcessEnergy_eq_of_vector_eq _ _
            (dualMembraneSweepPath_stateAt_vector_of_membrane_complete
              x y n hmembrane hcore)
        _ = 0 := by rw [btExcessEnergy_dualMembrane]; simp
        _ ≤ 64 * L := Nat.zero_le _
  · have hnEnd :
        n = (dualMembraneSweepPath x y).increments.length := by
      rw [length_dualMembraneSweepPath_increments] at hn ⊢
      omega
    subst n
    rw [PauliErrorPath.stateAt_length, dualMembraneSweepPath_endpoint,
      btExcessEnergy_dualMembrane]
    simp

/-- The explicit primal membrane sweep has a linear BT energy height. -/
theorem pathHeight_primalMembraneSweepPath_le (z w : ZMod L) :
    (toricHamiltonian (L := L)).pathHeight
        (primalMembraneSweepPath z w) ≤ 64 * L := by
  rw [pathHeight]
  apply Finset.sup_le
  intro n hn
  apply btExcessEnergy_primalMembraneSweepPath_stateAt_le z w n
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hn)

/-- The explicit dual membrane sweep has a linear BT energy height. -/
theorem pathHeight_dualMembraneSweepPath_le (x y : ZMod L) :
    (toricHamiltonian (L := L)).pathHeight
        (dualMembraneSweepPath x y) ≤ 64 * L := by
  rw [pathHeight]
  apply Finset.sup_le
  intro n hn
  apply btExcessEnergy_dualMembraneSweepPath_stateAt_le x y n
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hn)

end QEC.Coding.PeriodicCubical4
