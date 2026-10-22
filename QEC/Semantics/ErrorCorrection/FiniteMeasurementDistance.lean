import QEC.Semantics.ErrorCorrection.QuditNoInformation

/-!
# Attained finite measurement distance

A full-region local extension reaches every ambient operator. Two orthogonal
code states therefore witness failure of full-region no-information. The
least failed threshold is attained and bounded by the physical length for
such codes; its detecting property and all lower-bound comparisons are proved.
-/

noncomputable section

namespace QEC.Semantics.QuditSubsystem

open scoped BigOperators

universe u
variable {J : Type u} [Fintype J] [DecidableEq J] (q : J → Nat)

/-- The actual region containing every coordinate. -/
def fullRegion : QuditSubsystem q := ⟨Finset.univ⟩

def fullRegionLabelEquiv : Qudit.Label (fun j : (fullRegion q).SelectedCoordinates => q j.val) ≃
    Qudit.Label q where
  toFun x j := x ⟨j, Finset.mem_univ j⟩
  invFun x j := x j.val
  left_inv x := by funext j; rfl
  right_inv x := rfl

def extensionLinearMap (S : QuditSubsystem q) :
    Operator S.selectedSystem →ₗ[Complex] Operator (Qudit.QuditRegister q) where
  toFun := S.extendLocalToRegister
  map_add' := S.extendLocalToRegister_add
  map_smul' := S.extendLocalToRegister_smul

/-- On the full region every ambient operator is an actual local extension. -/
theorem fullRegion_extension_surjective (hq : ∀ j, 0 < q j) :
    Function.Surjective (fullRegion q).extendLocalToRegister := by
  have hd : Module.finrank Complex (fullRegion q).selectedSystem =
      Module.finrank Complex (Qudit.QuditRegister q) := by
    rw [finrank_euclideanSpace, finrank_euclideanSpace]
    exact Fintype.card_congr (fullRegionLabelEquiv q)
  have he : Module.finrank Complex (Operator (fullRegion q).selectedSystem) =
      Module.finrank Complex (Operator (Qudit.QuditRegister q)) := by
    change Module.finrank Complex ((fullRegion q).selectedSystem →ₗ[Complex]
      (fullRegion q).selectedSystem) =
      Module.finrank Complex (Qudit.QuditRegister q →ₗ[Complex] Qudit.QuditRegister q)
    rw [Module.finrank_linearMap, Module.finrank_linearMap, hd]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank he
    (f := extensionLinearMap q (fullRegion q))).mp
      ((fullRegion q).extendLocalToRegister_injective hq)

/-- Two orthogonal encoded states distinguish an actual full-region measurement. -/
theorem not_noInformationOn_fullRegion (C : QuantumCode (Qudit.QuditRegister q))
    (hq : ∀ j, 0 < q j) (x y : Qudit.QuditRegister q)
    (hx : x ∈ C.carrier) (hy : y ∈ C.carrier)
    (hxx : inner Complex x x = 1) (hyy : inner Complex y y = 1)
    (hxy : inner Complex x y = 0) : ¬ NoInformationOn C (fullRegion q) := by
  intro hinfo
  obtain ⟨E, hE⟩ := fullRegion_extension_surjective q hq
    (InnerProductSpace.rankOne Complex x x).toLinearMap
  have hs := (noInformationOn_iff_allLocalScalarCompression C (fullRegion q)).mp hinfo E
  rw [hE] at hs
  obtain ⟨c, hc⟩ := (scalarCompression_iff_detectableOn _ _).mp hs
  have h0 := hc x hx x hx
  have h1 := hc y hy y hy
  have hc0 : (1 : Complex) = c := by
    change inner Complex x (inner Complex x x • x) = c * inner Complex x x at h0
    rw [hxx, one_smul, mul_one, hxx] at h0
    exact h0
  have hc1 : (0 : Complex) = c := by
    change inner Complex y (inner Complex x y • x) = c * inner Complex y y at h1
    rw [hxy, zero_smul, inner_zero_right, hyy, mul_one] at h1
    exact h1
  exact one_ne_zero (hc0.trans hc1.symm)

theorem BPTMeasurementDistance.mono {C : QuantumCode (Qudit.QuditRegister q)}
    {d e : Nat} (hd : BPTMeasurementDistance C d) (he : e ≤ d) :
    BPTMeasurementDistance C e := by
  intro S hS
  exact hd S (hS.trans_le he)

/-- Least failed threshold. The natural-number fallback for an empty failure
set is zero; the finite-distance contract below requires and proves failure. -/
def finiteMeasurementDistance (C : QuantumCode (Qudit.QuditRegister q)) : Nat :=
  sInf {d : Nat | ¬ BPTMeasurementDistance C (d + 1)}

theorem finiteMeasurementDistance_detects (C : QuantumCode (Qudit.QuditRegister q)) :
    BPTMeasurementDistance C (finiteMeasurementDistance q C) := by
  classical
  intro S hS
  have hn := Nat.notMem_of_lt_sInf hS
  have hd : BPTMeasurementDistance C (Fintype.card S.SelectedCoordinates + 1) := by
    simpa only [Set.mem_setOf_eq, not_not] using hn
  exact hd S (Nat.lt_succ_self _)

theorem failedThreshold_nonempty (C : QuantumCode (Qudit.QuditRegister q))
    (hfull : ¬ NoInformationOn C (fullRegion q)) :
    {d : Nat | ¬ BPTMeasurementDistance C (d + 1)}.Nonempty := by
  refine ⟨Fintype.card J, ?_⟩
  intro hd
  apply hfull
  apply hd (fullRegion q)
  simp [SelectedCoordinates, fullRegion]

theorem finiteMeasurementDistance_fails_succ (C : QuantumCode (Qudit.QuditRegister q))
    (hfull : ¬ NoInformationOn C (fullRegion q)) :
    ¬ BPTMeasurementDistance C (finiteMeasurementDistance q C + 1) :=
  Nat.sInf_mem (failedThreshold_nonempty q C hfull)

theorem finiteMeasurementDistance_le_card (C : QuantumCode (Qudit.QuditRegister q))
    (hfull : ¬ NoInformationOn C (fullRegion q)) :
    finiteMeasurementDistance q C ≤ Fintype.card J := by
  apply Nat.sInf_le
  intro hd
  apply hfull
  apply hd (fullRegion q)
  simp [SelectedCoordinates, fullRegion]

theorem le_finiteMeasurementDistance (C : QuantumCode (Qudit.QuditRegister q))
    (hfull : ¬ NoInformationOn C (fullRegion q)) {d : Nat}
    (hd : BPTMeasurementDistance C d) : d ≤ finiteMeasurementDistance q C := by
  by_contra h
  apply finiteMeasurementDistance_fails_succ q C hfull
  exact hd.mono q (by omega)

end QEC.Semantics.QuditSubsystem
