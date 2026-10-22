import QEC.Coding.ChainComplex.Duality
import QEC.Coding.CSS.Subsystem

/-!
# Finite-coordinate duals of subsystem CSS data

The finite-coordinate chain dual exchanges the selected homological and
cohomological logical quotients.  This adapter is deliberately structural:
it transports the existing quotient maps and does not add a distance or
zero-gauge hypothesis.
-/

namespace QEC.Coding.SubsystemCSSData

universe u v

variable {i0 i1 i2 : Type u} {LogicalZ LogicalX : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]
variable [AddCommGroup LogicalZ] [Module (ZMod 2) LogicalZ]
variable [AddCommGroup LogicalX] [Module (ZMod 2) LogicalX]
variable [Module.Finite (ZMod 2) LogicalZ]
variable [Module.Finite (ZMod 2) LogicalX]

/-- A cocycle of the dual complex is the same coordinate word as a cycle of
the original complex. -/
noncomputable def dualCocycleToOriginalHomology
    (K : ChainComplexData (ZMod 2)
      (Word (ZMod 2) i0) (Word (ZMod 2) i1) (Word (ZMod 2) i2)) :
    (dualChainComplex K).middleCocycleCode.carrier →ₗ[ZMod 2]
      K.middleHomology where
  toFun x := K.middleBoundaryInCycles.mkQ
    ⟨x.1, by
      rw [K.mem_middleCycleCode_iff]
      have hx := ((dualChainComplex K).mem_middleCocycleCode_iff x.1).mp x.2
      simpa only [dualChainComplex_boundary2,
        wordLinearMapTranspose_transpose] using hx⟩
  map_add' x y := by
    change K.middleBoundaryInCycles.mkQ ⟨x.1 + y.1, _⟩ =
      K.middleBoundaryInCycles.mkQ ⟨x.1, _⟩ +
        K.middleBoundaryInCycles.mkQ ⟨y.1, _⟩
    rw [← map_add]
    rfl
  map_smul' c x := by
    change K.middleBoundaryInCycles.mkQ ⟨c • x.1, _⟩ =
      c • K.middleBoundaryInCycles.mkQ ⟨x.1, _⟩
    rw [← map_smul]
    rfl

theorem dual_middleCoboundary_le_ker_dualCocycleToOriginalHomology
    (K : ChainComplexData (ZMod 2)
      (Word (ZMod 2) i0) (Word (ZMod 2) i1) (Word (ZMod 2) i2)) :
    (dualChainComplex K).middleCoboundaryInCocycles ≤
      LinearMap.ker (dualCocycleToOriginalHomology K) := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  change K.middleBoundaryInCycles.mkQ ⟨x.1, _⟩ = 0
  apply (Submodule.Quotient.mk_eq_zero K.middleBoundaryInCycles).mpr
  change x.1 ∈ K.middleBoundaryCode.carrier
  change x.1 ∈ (dualChainComplex K).firstCoboundaryCheckCode.carrier at hx
  rcases ((dualChainComplex K).mem_firstCoboundaryCheckCode_iff x.1).mp hx with
    ⟨w, hw⟩
  apply (K.mem_middleBoundaryCode_iff x.1).mpr
  refine ⟨w, ?_⟩
  simpa only [dualChainComplex_boundary1,
    wordLinearMapTranspose_transpose] using hw

/-- The quotient-level identification `H¹(Kᵛ) → H₁(K)`. -/
noncomputable def dualCohomologyToOriginalHomology
    (K : ChainComplexData (ZMod 2)
      (Word (ZMod 2) i0) (Word (ZMod 2) i1) (Word (ZMod 2) i2)) :
    (dualChainComplex K).middleCohomology →ₗ[ZMod 2] K.middleHomology :=
  (dualChainComplex K).middleCoboundaryInCocycles.liftQ
    (dualCocycleToOriginalHomology K)
    (dual_middleCoboundary_le_ker_dualCocycleToOriginalHomology K)

@[simp]
theorem dualCohomologyToOriginalHomology_mk
    (K : ChainComplexData (ZMod 2)
      (Word (ZMod 2) i0) (Word (ZMod 2) i1) (Word (ZMod 2) i2))
    (x : (dualChainComplex K).middleCocycleCode.carrier) :
    dualCohomologyToOriginalHomology K
        ((dualChainComplex K).middleCoboundaryInCocycles.mkQ x) =
      K.middleBoundaryInCycles.mkQ
        ⟨x.1, by
          rw [K.mem_middleCycleCode_iff]
          have hx := ((dualChainComplex K).mem_middleCocycleCode_iff x.1).mp x.2
          simpa only [dualChainComplex_boundary2,
            wordLinearMapTranspose_transpose] using hx⟩ := rfl

theorem dualCohomologyToOriginalHomology_surjective
    (K : ChainComplexData (ZMod 2)
      (Word (ZMod 2) i0) (Word (ZMod 2) i1) (Word (ZMod 2) i2)) :
    Function.Surjective (dualCohomologyToOriginalHomology K) := by
  intro h
  obtain ⟨x, rfl⟩ := K.middleBoundaryInCycles.mkQ_surjective h
  let xd : (dualChainComplex K).middleCocycleCode.carrier :=
    ⟨x.1, by
      rw [(dualChainComplex K).mem_middleCocycleCode_iff]
      simpa only [dualChainComplex_boundary2,
        wordLinearMapTranspose_transpose] using
          (K.mem_middleCycleCode_iff x.1).mp x.2⟩
  exact ⟨(dualChainComplex K).middleCoboundaryInCocycles.mkQ xd, by
    rw [dualCohomologyToOriginalHomology_mk]⟩

/-- Swap the two selected logical sectors together with the finite-coordinate
chain dual. -/
noncomputable def dual
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) :
    SubsystemCSSData i2 i1 i0 LogicalX LogicalZ where
  complex := dualChainComplex D.complex
  homologyProjection := D.cohomologyProjection
  cohomologyProjection := D.homologyProjection.comp
    (dualCohomologyToOriginalHomology D.complex)
  homologyProjection_surjective := D.cohomologyProjection_surjective
  cohomologyProjection_surjective :=
    D.homologyProjection_surjective.comp
      (dualCohomologyToOriginalHomology_surjective D.complex)
  logical_finrank_eq := D.logical_finrank_eq.symm

@[simp]
theorem dual_complex
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) :
    D.dual.complex = dualChainComplex D.complex := rfl

theorem dual_dressedZDistanceAtLeast_iff
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) (d : Nat) :
    D.dual.DressedZDistanceAtLeast d ↔ D.DressedXDistanceAtLeast d := by
  rfl

theorem dual_dressedXDistanceAtLeast_iff
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) (d : Nat) :
    D.dual.DressedXDistanceAtLeast d ↔ D.DressedZDistanceAtLeast d := by
  constructor
  · intro h z hz hLogical
    apply h z (by
      change z ∈ (dualChainComplex D.complex).middleCocycleCode.carrier
      rw [(dualChainComplex D.complex).mem_middleCocycleCode_iff]
      simpa only [dualChainComplex_boundary2,
        wordLinearMapTranspose_transpose] using
          (D.complex.mem_middleCycleCode_iff z).mp hz)
    change D.homologyProjection
      (dualCohomologyToOriginalHomology D.complex
        ((dualChainComplex D.complex).middleCoboundaryInCocycles.mkQ
          ⟨z, _⟩)) ≠ 0
    rw [dualCohomologyToOriginalHomology_mk]
    exact hLogical
  · intro h x hx hLogical
    apply h x (by
      rw [D.complex.mem_middleCycleCode_iff]
      have hx' : x ∈ (dualChainComplex D.complex).middleCocycleCode.carrier := by
        exact hx
      have hx' := ((dualChainComplex D.complex).mem_middleCocycleCode_iff x).mp hx'
      simpa only [dualChainComplex_boundary2,
        wordLinearMapTranspose_transpose] using hx')
    change D.homologyProjection
      (D.complex.middleBoundaryInCycles.mkQ ⟨x, _⟩) ≠ 0
    change D.homologyProjection
      (dualCohomologyToOriginalHomology D.complex
        ((dualChainComplex D.complex).middleCoboundaryInCocycles.mkQ
          ⟨x, hx⟩)) ≠ 0 at hLogical
    simpa only [dualCohomologyToOriginalHomology_mk] using hLogical

@[simp]
theorem dual_logicalQubits
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) :
    D.dual.logicalQubits = D.logicalQubits := by
  exact D.logical_finrank_eq.symm

end QEC.Coding.SubsystemCSSData
