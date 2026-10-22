import QEC.Semantics.ErrorCorrection.QuditSubsystem
import QEC.Semantics.ErrorCorrection.Detectability

/-!
# Local operators on finite-alphabet computational registers

A coordinatewise alphabet equivalence identifies field-labelled registers
with the canonical finite-qudit tensor substrate. Local operators below are
the actual identity extensions on that substrate, transported back along
this explicit basis identification.
-/

noncomputable section

namespace QEC.Semantics.FiniteAlphabet

open scoped BigOperators TensorProduct

universe u

variable (A I : Type u) [Fintype A] [Fintype I] [DecidableEq I]

local instance : Fintype (I → A) := Fintype.ofFinite _

/-- Relabel each coordinate separately by the finite alphabet enumeration. -/
def labelEquiv : (I → A) ≃ Qudit.Label (fun _ : I => Fintype.card A) :=
  Equiv.piCongrRight fun _ => Fintype.equivFin A

/-- The literal coordinatewise change of computational basis. -/
def registerUnitary :
    UnitaryTransport (EuclideanSpace Complex (I → A))
      (Qudit.QuditRegister (fun _ : I => Fintype.card A)) where
  toLinearEquiv := (LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex
    (labelEquiv A I)).toLinearEquiv
  map_inner := (LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex
    (labelEquiv A I)).inner_map_map

theorem registerUnitary_apply_basis (x : I → A) :
    registerUnitary A I (EuclideanSpace.basisFun (I → A) Complex x) =
      EuclideanSpace.basisFun (Qudit.Label (fun _ : I => Fintype.card A)) Complex
        (labelEquiv A I x) := by
  classical
  have hport := (EuclideanSpace.piLpCongrLeft_single (labelEquiv A I) x (1 : Complex))
  simp only [registerUnitary, EuclideanSpace.basisFun_apply] at hport ⊢
  exact hport

variable {A I}

/-- A tensor-local operator in native alphabet coordinates. -/
def localOperator (S : QuditSubsystem (fun _ : I => Fintype.card A))
    (E : Operator S.selectedSystem) : Operator (EuclideanSpace Complex (I → A)) :=
  (registerUnitary A I).symm.conjOperator (S.extendLocalToRegister E)

/-- The selected/complement tensor factors give the actual local matrix element. -/
theorem localOperator_basis_inner (S : QuditSubsystem (fun _ : I => Fintype.card A))
    (E : Operator S.selectedSystem) (x y : I → A) :
    inner Complex (EuclideanSpace.basisFun (I → A) Complex x)
      (localOperator S E (EuclideanSpace.basisFun (I → A) Complex y)) =
    inner Complex
        (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
          (S.splitLabel (labelEquiv A I x)).1)
        (E (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
          (S.splitLabel (labelEquiv A I y)).1)) *
      inner Complex
        (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
          (S.splitLabel (labelEquiv A I x)).2)
        (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
          (S.splitLabel (labelEquiv A I y)).2) := by
  rw [← inner_conj_symm, localOperator, UnitaryTransport.inner_conjOperator]
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.symm_symm]
  change star (inner Complex (S.extendLocalToRegister E
      (registerUnitary A I (EuclideanSpace.basisFun (I → A) Complex y)))
    (registerUnitary A I (EuclideanSpace.basisFun (I → A) Complex x))) = _
  rw [registerUnitary_apply_basis, registerUnitary_apply_basis]
  rw [QuditSubsystem.extendLocalToRegister, UnitaryTransport.inner_conjOperator]
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.symm_symm]
  rw [S.registerFactorization_apply_basis, S.registerFactorization_apply_basis,
    S.extendLocal_apply_tmul, TensorProduct.inner_tmul, star_mul]
  simp only [← starRingEnd_apply, inner_conj_symm]
  ring

/-- Identity action on the complementary factor annihilates distinct complement labels. -/
theorem localOperator_basis_inner_eq_zero
    (S : QuditSubsystem (fun _ : I => Fintype.card A)) (E : Operator S.selectedSystem)
    (x y : I → A) (h : ∃ j, j ∉ S.selected ∧ x j ≠ y j) :
    inner Complex (EuclideanSpace.basisFun (I → A) Complex x)
      (localOperator S E (EuclideanSpace.basisFun (I → A) Complex y)) = 0 := by
  classical
  obtain ⟨j, hj, hxy⟩ := h
  have hcomp : (S.splitLabel (labelEquiv A I x)).2 ≠
      (S.splitLabel (labelEquiv A I y)).2 := by
    intro heq
    have hv := congrFun heq ⟨j, hj⟩
    exact hxy ((Fintype.equivFin A).injective hv)
  rw [localOperator_basis_inner]
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, hcomp]

/-- A local diagonal expectation depends only on the selected alphabet coordinates. -/
theorem localOperator_basis_diagonal_eq
    (S : QuditSubsystem (fun _ : I => Fintype.card A)) (E : Operator S.selectedSystem)
    (x y : I → A) (h : ∀ j, j ∈ S.selected → x j = y j) :
    inner Complex (EuclideanSpace.basisFun (I → A) Complex x)
      (localOperator S E (EuclideanSpace.basisFun (I → A) Complex x)) =
    inner Complex (EuclideanSpace.basisFun (I → A) Complex y)
      (localOperator S E (EuclideanSpace.basisFun (I → A) Complex y)) := by
  classical
  have hsel : (S.splitLabel (labelEquiv A I x)).1 =
      (S.splitLabel (labelEquiv A I y)).1 := by
    funext j
    exact congrArg (Fintype.equivFin A) (h j j.property)
  rw [localOperator_basis_inner, localOperator_basis_inner, hsel]
  simp

/-- Native-alphabet detection is detection of the actual tensor-local operator
on the canonically relabelled quantum code. -/
theorem detectableOn_transport_of_localOperator
    (C : QuantumCode (EuclideanSpace Complex (I → A)))
    (S : QuditSubsystem (fun _ : I => Fintype.card A)) (E : Operator S.selectedSystem)
    (h : DetectableOn C (localOperator S E)) :
    DetectableOn (C.transport (registerUnitary A I)) (S.extendLocalToRegister E) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rintro x ⟨x₀, hx, rfl⟩ y ⟨y₀, hy, rfl⟩
  change inner Complex (registerUnitary A I x₀)
      (S.extendLocalToRegister E (registerUnitary A I y₀)) =
    c * inner Complex (registerUnitary A I x₀) (registerUnitary A I y₀)
  have hE : registerUnitary A I (localOperator S E y₀) =
      S.extendLocalToRegister E (registerUnitary A I y₀) := by
    simp [localOperator, UnitaryTransport.conjOperator, UnitaryTransport.symm]
  rw [← hE, (registerUnitary A I).map_inner, (registerUnitary A I).map_inner]
  exact hc x₀ hx y₀ hy

end QEC.Semantics.FiniteAlphabet
