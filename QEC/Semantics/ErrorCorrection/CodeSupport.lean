import QEC.Semantics.Core.Definitions
/-!
# QEC.Semantics.CodeSupport

Projector and support lemmas for semantic quantum-code carriers.
-/

universe u

namespace QEC
namespace Semantics

open scoped ComplexOrder

noncomputable section

namespace QuantumCode

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

/-- The orthogonal projector onto a quantum code carrier. -/
noncomputable def projector (C : QuantumCode H) : Operator H :=
  C.carrier.starProjection.toLinearMap

theorem projector_apply (C : QuantumCode H) (v : H) :
    C.projector v = C.carrier.starProjection v :=
  rfl

theorem projector_mem_carrier (C : QuantumCode H) (v : H) :
    C.projector v ∈ C.carrier := by
  simp [projector]

theorem projector_eq_self_iff_mem (C : QuantumCode H) {v : H} :
    C.projector v = v ↔ v ∈ C.carrier := by
  simpa [projector] using (Submodule.starProjection_eq_self_iff (K := C.carrier) (v := v))

theorem projector_eq_self_of_mem (C : QuantumCode H) {v : H} (hv : v ∈ C.carrier) :
    C.projector v = v :=
  (C.projector_eq_self_iff_mem).2 hv

theorem projector_idempotent (C : QuantumCode H) :
    C.projector.comp C.projector = C.projector := by
  ext v
  exact C.projector_eq_self_of_mem (C.projector_mem_carrier v)

theorem projector_isSymmetric (C : QuantumCode H) :
    LinearMap.IsSymmetric C.projector := by
  simpa [projector] using C.carrier.starProjection_isSymmetric

theorem projector_adjoint_eq_self (C : QuantumCode H) :
    LinearMap.adjoint C.projector = C.projector :=
  (C.projector_isSymmetric).adjoint_eq

end QuantumCode

namespace DensityOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem toOperator_adjoint_eq_self (rho : DensityOperator H) :
    LinearMap.adjoint rho.toOperator = rho.toOperator :=
  rho.positive.adjoint_eq

/--
The normalized rank-one density operator associated to a nonzero vector.

This is the pure-state density `|x><x| / <x,x>` in the repository's
operator-space convention.
-/
noncomputable def pureOfNonzero (x : H) (hx : x ≠ 0) : DensityOperator H where
  toOperator :=
    (inner Complex x x)⁻¹ •
      (((InnerProductSpace.rankOne Complex x x : H →L[Complex] H) : H →ₗ[Complex] H))
  positive := by
    have hpos : LinearMap.IsPositive
        (((InnerProductSpace.rankOne Complex x x : H →L[Complex] H) : H →ₗ[Complex] H)) := by
      exact (InnerProductSpace.isPositive_rankOne_self (𝕜 := Complex) x).toLinearMap
    have hinner_nonneg : 0 ≤ inner Complex x x := by
      rw [inner_self_eq_norm_sq_to_K]
      positivity
    exact hpos.smul_of_nonneg ((inv_nonneg).2 hinner_nonneg)
  trace_one := by
    rw [map_smul, InnerProductSpace.trace_rankOne]
    exact inv_mul_cancel₀ (inner_self_ne_zero.mpr hx)

@[simp]
theorem pureOfNonzero_toOperator (x : H) (hx : x ≠ 0) :
    (pureOfNonzero x hx).toOperator =
      (inner Complex x x)⁻¹ •
        (((InnerProductSpace.rankOne Complex x x : H →L[Complex] H) :
          H →ₗ[Complex] H)) :=
  rfl

@[simp]
theorem pureOfNonzero_apply (x y : H) (hx : x ≠ 0) :
    (pureOfNonzero x hx).toOperator y =
      ((inner Complex x x)⁻¹ * inner Complex x y) • x := by
  simp [pureOfNonzero, mul_smul]

theorem pureOfNonzero_supportedOn {C : QuantumCode H} {x : H} (hx : x ≠ 0)
    (hxC : x ∈ C.carrier) : SupportedOn C (pureOfNonzero x hx) := by
  intro y
  rw [pureOfNonzero_apply]
  exact C.carrier.smul_mem _ hxC

theorem comp_pureOfNonzero_adjoint (A : Operator H) (x : H) (hx : x ≠ 0) :
    A.comp ((pureOfNonzero x hx).toOperator.comp (LinearMap.adjoint A)) =
      (inner Complex x x)⁻¹ •
        (((InnerProductSpace.rankOne Complex (A x) (A x) : H →L[Complex] H) :
          H →ₗ[Complex] H)) := by
  ext y
  simp [pureOfNonzero, LinearMap.comp_apply, LinearMap.adjoint_inner_right]

theorem supportedOn_iff_projector_comp_eq (C : QuantumCode H) (rho : DensityOperator H) :
    SupportedOn C rho ↔ C.projector.comp rho.toOperator = rho.toOperator := by
  constructor
  · intro hρ
    ext v
    exact C.projector_eq_self_of_mem (hρ v)
  · intro hρ v
    have hv := congrArg (fun A : Operator H => A v) hρ
    change C.projector (rho.toOperator v) = rho.toOperator v at hv
    exact (C.projector_eq_self_iff_mem).1 hv

theorem supportedOn_projector_comp_eq_self (C : QuantumCode H) (rho : DensityOperator H)
    (hρ : SupportedOn C rho) :
    C.projector.comp rho.toOperator = rho.toOperator :=
  (supportedOn_iff_projector_comp_eq C rho).1 hρ

theorem supportedOn_iff_comp_projector_eq (C : QuantumCode H) (rho : DensityOperator H) :
    SupportedOn C rho ↔ rho.toOperator.comp C.projector = rho.toOperator := by
  constructor
  · intro hρ
    have hleft : C.projector.comp rho.toOperator = rho.toOperator :=
      supportedOn_projector_comp_eq_self C rho hρ
    have hadj := congrArg LinearMap.adjoint hleft
    simpa [LinearMap.adjoint_comp, QuantumCode.projector_adjoint_eq_self,
      toOperator_adjoint_eq_self] using hadj
  · intro hright
    refine (supportedOn_iff_projector_comp_eq C rho).2 ?_
    have hadj := congrArg LinearMap.adjoint hright
    simpa [LinearMap.adjoint_comp, QuantumCode.projector_adjoint_eq_self,
      toOperator_adjoint_eq_self] using hadj

theorem supportedOn_comp_projector_eq_self (C : QuantumCode H) (rho : DensityOperator H)
    (hρ : SupportedOn C rho) :
    rho.toOperator.comp C.projector = rho.toOperator :=
  (supportedOn_iff_comp_projector_eq C rho).1 hρ

theorem supportedOn_projector_comp_toOperator_comp_projector_eq_self
    (C : QuantumCode H) (rho : DensityOperator H) (hρ : SupportedOn C rho) :
    C.projector.comp (rho.toOperator.comp C.projector) = rho.toOperator := by
  ext v
  have hleft := congrArg (fun A : Operator H => A (C.projector v))
    (supportedOn_projector_comp_eq_self C rho hρ)
  have hright := congrArg (fun A : Operator H => A v)
    (supportedOn_comp_projector_eq_self C rho hρ)
  exact hleft.trans hright

theorem supportedOn_iff_projector_comp_toOperator_comp_projector_eq
    (C : QuantumCode H) (rho : DensityOperator H) :
    SupportedOn C rho ↔ C.projector.comp (rho.toOperator.comp C.projector) = rho.toOperator := by
  constructor
  · exact supportedOn_projector_comp_toOperator_comp_projector_eq_self C rho
  · intro hρ v
    have hv := congrArg (fun A : Operator H => A v) hρ
    change C.projector (rho.toOperator (C.projector v)) = rho.toOperator v at hv
    have hmem : C.projector (rho.toOperator (C.projector v)) ∈ C.carrier :=
      C.projector_mem_carrier (rho.toOperator (C.projector v))
    exact hv ▸ hmem

end DensityOperator

end

end Semantics
end QEC
