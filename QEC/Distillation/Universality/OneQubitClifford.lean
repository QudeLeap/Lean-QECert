import QEC.Semantics.Core.Qubit
/-!
# Finite projective one-qubit Clifford action

This module defines the signed-axis model of the 24-element projective
one-qubit Clifford group and its finite actions on the exact `T`- and
`H`-direction types.  It is internal semantic API infrastructure; it does not
state a distillation threshold, an injection theorem, or a universality result.
-/

namespace QEC
namespace Distillation
namespace OneQubitMagic

open Semantics Semantics.Qubit
open scoped BigOperators

inductive PauliAxis where
  | x
  | y
  | z
  deriving DecidableEq, Repr

instance : Fintype PauliAxis where
  elems := {PauliAxis.x, PauliAxis.y, PauliAxis.z}
  complete a := by cases a <;> simp

def permuteSigns (p : Equiv.Perm PauliAxis) : MulAut (PauliAxis → ℤˣ) where
  toFun s i := s (p.symm i)
  invFun s i := s (p i)
  left_inv s := by ext i; simp
  right_inv s := by ext i; simp
  map_mul' s t := by ext i; rfl

def signAction : Equiv.Perm PauliAxis →* MulAut (PauliAxis → ℤˣ) where
  toFun := permuteSigns
  map_one' := by ext s i; rfl
  map_mul' p q := by ext s i; rfl

abbrev SignedAxisPermutation :=
  SemidirectProduct (PauliAxis → ℤˣ) (Equiv.Perm PauliAxis) signAction

instance : Fintype SignedAxisPermutation :=
  Fintype.ofEquiv ((PauliAxis → ℤˣ) × Equiv.Perm PauliAxis)
    SemidirectProduct.equivProd.symm

def coordinateSign : (PauliAxis → ℤˣ) →* ℤˣ where
  toFun s := ∏ i, s i
  map_one' := by simp
  map_mul' s t := by simp only [Pi.mul_apply, Finset.prod_mul_distrib]

@[simp] theorem coordinateSign_signAction (p : Equiv.Perm PauliAxis)
    (s : PauliAxis → ℤˣ) : coordinateSign (signAction p s) = coordinateSign s :=
  p.symm.prod_comp s

def signedDeterminant : SignedAxisPermutation →* ℤˣ where
  toFun g := coordinateSign g.left * Equiv.Perm.sign g.right
  map_one' := by simp
  map_mul' a b := by
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, map_mul]
    rw [coordinateSign_signAction]
    ac_rfl

abbrev ProjectiveClifford := signedDeterminant.ker

theorem card_signedAxisPermutation : Fintype.card SignedAxisPermutation = 48 := by
  native_decide

theorem card_projectiveClifford : Fintype.card ProjectiveClifford = 24 := by
  native_decide

inductive SignedCoordinate where
  | neg
  | zero
  | pos
  deriving DecidableEq, Repr

instance : Fintype SignedCoordinate where
  elems := {SignedCoordinate.neg, SignedCoordinate.zero, SignedCoordinate.pos}
  complete a := by cases a <;> simp

def signCoordinate (s : ℤˣ) : SignedCoordinate → SignedCoordinate
  | .zero => .zero
  | .pos => if s = 1 then .pos else .neg
  | .neg => if s = 1 then .neg else .pos

instance : MulAction ℤˣ SignedCoordinate where
  smul := signCoordinate
  one_smul := by native_decide
  mul_smul := by native_decide

def signedAxisAction (g : SignedAxisPermutation)
    (d : PauliAxis → SignedCoordinate) : PauliAxis → SignedCoordinate :=
  fun i => g.left i • d (g.right.symm i)

instance : MulAction SignedAxisPermutation (PauliAxis → SignedCoordinate) where
  smul := signedAxisAction
  one_smul := by native_decide
  mul_smul := by native_decide

def IsTDirection (d : PauliAxis → SignedCoordinate) : Prop :=
  ∀ i, d i ≠ .zero

def IsHDirection (d : PauliAxis → SignedCoordinate) : Prop :=
  (Finset.univ.filter fun i => d i = .zero).card = 1

instance (d : PauliAxis → SignedCoordinate) : Decidable (IsTDirection d) := by
  unfold IsTDirection
  infer_instance

instance (d : PauliAxis → SignedCoordinate) : Decidable (IsHDirection d) := by
  unfold IsHDirection
  infer_instance

abbrev TDirection := {d : PauliAxis → SignedCoordinate // IsTDirection d}

abbrev HDirection := {d : PauliAxis → SignedCoordinate // IsHDirection d}

theorem isTDirection_smul (g : SignedAxisPermutation)
    (d : PauliAxis → SignedCoordinate) :
    IsTDirection d → IsTDirection (g • d) := by
  revert g d
  native_decide

theorem isHDirection_smul (g : SignedAxisPermutation)
    (d : PauliAxis → SignedCoordinate) :
    IsHDirection d → IsHDirection (g • d) := by
  revert g d
  native_decide

instance : SMul SignedAxisPermutation TDirection where
  smul g d := ⟨g • d.1, isTDirection_smul g d.1 d.2⟩

instance : MulAction SignedAxisPermutation TDirection where
  one_smul d := by
    apply Subtype.ext
    change (1 : SignedAxisPermutation) • d.1 = d.1
    exact one_smul SignedAxisPermutation d.1
  mul_smul g h d := by
    apply Subtype.ext
    change (g * h) • d.1 = g • h • d.1
    exact mul_smul g h d.1

instance : SMul SignedAxisPermutation HDirection where
  smul g d := ⟨g • d.1, isHDirection_smul g d.1 d.2⟩

instance : MulAction SignedAxisPermutation HDirection where
  one_smul d := by
    apply Subtype.ext
    change (1 : SignedAxisPermutation) • d.1 = d.1
    exact one_smul SignedAxisPermutation d.1
  mul_smul g h d := by
    apply Subtype.ext
    change (g * h) • d.1 = g • h • d.1
    exact mul_smul g h d.1

theorem card_tDirection : Fintype.card TDirection = 8 := by
  native_decide

theorem card_hDirection : Fintype.card HDirection = 12 := by
  native_decide

theorem tDirection_transitive (a b : TDirection) :
    ∃ g : ProjectiveClifford, g • a = b := by
  revert a b
  native_decide

theorem hDirection_transitive (a b : HDirection) :
    ∃ g : ProjectiveClifford, g • a = b := by
  revert a b
  native_decide

def hadamardClifford : ProjectiveClifford :=
  ⟨⟨fun
      | .x => 1
      | .y => -1
      | .z => 1,
    Equiv.swap .x .z⟩,
    by native_decide⟩

def phaseClifford : ProjectiveClifford :=
  ⟨⟨fun
      | .x => -1
      | .y => 1
      | .z => 1,
    Equiv.swap .x .y⟩,
    by native_decide⟩

@[simp] theorem hadamardClifford_x (d : PauliAxis → SignedCoordinate) :
    (hadamardClifford.1 • d) .x = d .z := by
  change (1 : ℤˣ) • d .z = d .z
  simp

@[simp] theorem hadamardClifford_y (d : PauliAxis → SignedCoordinate) :
    (hadamardClifford.1 • d) .y = (-1 : ℤˣ) • d .y := by
  rfl

@[simp] theorem hadamardClifford_z (d : PauliAxis → SignedCoordinate) :
    (hadamardClifford.1 • d) .z = d .x := by
  change (1 : ℤˣ) • d .x = d .x
  simp

@[simp] theorem phaseClifford_x (d : PauliAxis → SignedCoordinate) :
    (phaseClifford.1 • d) .x = (-1 : ℤˣ) • d .y := by
  rfl

@[simp] theorem phaseClifford_y (d : PauliAxis → SignedCoordinate) :
    (phaseClifford.1 • d) .y = d .x := by
  change (1 : ℤˣ) • d .x = d .x
  simp

@[simp] theorem phaseClifford_z (d : PauliAxis → SignedCoordinate) :
    (phaseClifford.1 • d) .z = d .z := by
  change (1 : ℤˣ) • d .z = d .z
  simp

noncomputable section

/-! ## Concrete Clifford generators on the qubit Hilbert space -/

/-- The concrete Hadamard matrix in the computational basis. -/
def hadamardMatrix : Matrix (Fin 2) (Fin 2) Complex :=
  !![(Real.sqrt 2 : Complex)⁻¹, (Real.sqrt 2 : Complex)⁻¹;
     (Real.sqrt 2 : Complex)⁻¹, -(Real.sqrt 2 : Complex)⁻¹]

/-- The concrete phase matrix in the computational basis. -/
def phaseMatrix : Matrix (Fin 2) (Fin 2) Complex :=
  !![1, 0; 0, Complex.I]

/-- The inverse phase matrix in the computational basis. -/
def phaseInverseMatrix : Matrix (Fin 2) (Fin 2) Complex :=
  !![1, 0; 0, -Complex.I]

/-- Hadamard as an operator on the concrete qubit space. -/
def hadamardOperator : Operator QubitSpace :=
  Matrix.toEuclideanLin hadamardMatrix

/-- The phase gate as an operator on the concrete qubit space. -/
def phaseOperator : Operator QubitSpace :=
  Matrix.toEuclideanLin phaseMatrix

/-- The inverse phase gate as an operator on the concrete qubit space. -/
def phaseInverseOperator : Operator QubitSpace :=
  Matrix.toEuclideanLin phaseInverseMatrix

/-- Positivity of the normalization denominator used by Hadamard. -/
theorem sqrt_two_pos : 0 < Real.sqrt 2 :=
  Real.sqrt_pos.2 (by norm_num)

/-- The square-root identity used by the Hadamard inverse and isometry proofs. -/
theorem sqrt_two_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)

private theorem sqrt_two_ne_zero_complex : (Real.sqrt 2 : Complex) ≠ 0 := by
  exact_mod_cast sqrt_two_pos.ne'

private theorem sqrt_two_mul_self_complex :
    (Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex) = 2 := by
  exact_mod_cast sqrt_two_mul_self

private theorem two_mul_inv_sqrt_two_sq :
    (2 : Complex) *
      ((Real.sqrt 2 : Complex)⁻¹ * (Real.sqrt 2 : Complex)⁻¹) = 1 := by
  rw [← sqrt_two_mul_self_complex]
  field_simp [sqrt_two_ne_zero_complex]

@[simp] theorem hadamardOperator_apply_zero (psi : QubitSpace) :
    hadamardOperator psi 0 = (Real.sqrt 2 : Complex)⁻¹ * (psi 0 + psi 1) := by
  simp [hadamardOperator, hadamardMatrix, Matrix.mulVec, dotProduct]
  ring

@[simp] theorem hadamardOperator_apply_one (psi : QubitSpace) :
    hadamardOperator psi 1 = (Real.sqrt 2 : Complex)⁻¹ * (psi 0 - psi 1) := by
  simp [hadamardOperator, hadamardMatrix, Matrix.mulVec, dotProduct]
  ring

@[simp] theorem phaseOperator_apply_zero (psi : QubitSpace) :
    phaseOperator psi 0 = psi 0 := by
  simp [phaseOperator, phaseMatrix, Matrix.mulVec, dotProduct]

@[simp] theorem phaseOperator_apply_one (psi : QubitSpace) :
    phaseOperator psi 1 = Complex.I * psi 1 := by
  simp [phaseOperator, phaseMatrix, Matrix.mulVec, dotProduct]

@[simp] theorem phaseInverseOperator_apply_zero (psi : QubitSpace) :
    phaseInverseOperator psi 0 = psi 0 := by
  simp [phaseInverseOperator, phaseInverseMatrix, Matrix.mulVec, dotProduct]

@[simp] theorem phaseInverseOperator_apply_one (psi : QubitSpace) :
    phaseInverseOperator psi 1 = -Complex.I * psi 1 := by
  simp [phaseInverseOperator, phaseInverseMatrix, Matrix.mulVec, dotProduct]

/-- Hadamard is its own inverse, proved on the two concrete coordinates. -/
theorem hadamardOperator_square : hadamardOperator * hadamardOperator = 1 := by
  ext psi b
  fin_cases b
  · change hadamardOperator (hadamardOperator psi) 0 = psi 0
    rw [hadamardOperator_apply_zero, hadamardOperator_apply_zero,
      hadamardOperator_apply_one]
    calc
      (Real.sqrt 2 : Complex)⁻¹ *
          ((Real.sqrt 2 : Complex)⁻¹ * (psi 0 + psi 1) +
            (Real.sqrt 2 : Complex)⁻¹ * (psi 0 - psi 1)) =
          (2 * ((Real.sqrt 2 : Complex)⁻¹ *
            (Real.sqrt 2 : Complex)⁻¹)) * psi 0 := by
            ring
      _ = psi 0 := by rw [two_mul_inv_sqrt_two_sq, one_mul]
  · change hadamardOperator (hadamardOperator psi) 1 = psi 1
    rw [hadamardOperator_apply_one, hadamardOperator_apply_zero,
      hadamardOperator_apply_one]
    calc
      (Real.sqrt 2 : Complex)⁻¹ *
          ((Real.sqrt 2 : Complex)⁻¹ * (psi 0 + psi 1) -
            (Real.sqrt 2 : Complex)⁻¹ * (psi 0 - psi 1)) =
          (2 * ((Real.sqrt 2 : Complex)⁻¹ *
            (Real.sqrt 2 : Complex)⁻¹)) * psi 1 := by
            ring
      _ = psi 1 := by rw [two_mul_inv_sqrt_two_sq, one_mul]

/-- The phase operator followed by its explicit inverse is the identity. -/
theorem phaseOperator_phaseInverseOperator :
    phaseOperator * phaseInverseOperator = 1 := by
  ext psi b
  fin_cases b <;>
    simp [Module.End.mul_apply, ← mul_assoc, Complex.I_mul_I]

/-- The explicit phase inverse followed by phase is the identity. -/
theorem phaseInverseOperator_phaseOperator :
    phaseInverseOperator * phaseOperator = 1 := by
  ext psi b
  fin_cases b <;>
    simp [Module.End.mul_apply, ← mul_assoc, Complex.I_mul_I]

/-- The concrete Hadamard linear equivalence, with Hadamard itself as inverse. -/
def hadamardLinearEquiv : QubitSpace ≃ₗ[Complex] QubitSpace :=
  LinearEquiv.mk hadamardOperator hadamardOperator
    (fun psi => by
      have h := LinearMap.congr_fun hadamardOperator_square psi
      simpa [Module.End.mul_apply] using h)
    (fun psi => by
      have h := LinearMap.congr_fun hadamardOperator_square psi
      simpa [Module.End.mul_apply] using h)

/-- The concrete phase linear equivalence, with the explicit diagonal inverse. -/
def phaseLinearEquiv : QubitSpace ≃ₗ[Complex] QubitSpace :=
  LinearEquiv.mk phaseOperator phaseInverseOperator
    (fun psi => by
      have h := LinearMap.congr_fun phaseInverseOperator_phaseOperator psi
      simpa [Module.End.mul_apply] using h)
    (fun psi => by
      have h := LinearMap.congr_fun phaseOperator_phaseInverseOperator psi
      simpa [Module.End.mul_apply] using h)

@[simp] theorem hadamardLinearEquiv_apply (psi : QubitSpace) :
    hadamardLinearEquiv psi = hadamardOperator psi :=
  rfl

@[simp] theorem hadamardLinearEquiv_symm_apply (psi : QubitSpace) :
    hadamardLinearEquiv.symm psi = hadamardOperator psi :=
  rfl

@[simp] theorem phaseLinearEquiv_apply (psi : QubitSpace) :
    phaseLinearEquiv psi = phaseOperator psi :=
  rfl

@[simp] theorem phaseLinearEquiv_symm_apply (psi : QubitSpace) :
    phaseLinearEquiv.symm psi = phaseInverseOperator psi :=
  rfl

/-- Hadamard packaged as the existing proof-relevant unitary transport. -/
def hadamardTransport : UnitaryTransport QubitSpace QubitSpace where
  toLinearEquiv := hadamardLinearEquiv
  map_inner := by
    intro x y
    change inner Complex (hadamardOperator x) (hadamardOperator y) =
      inner Complex x y
    rw [PiLp.inner_apply, PiLp.inner_apply]
    simp only [Fin.sum_univ_two, hadamardOperator_apply_zero,
      hadamardOperator_apply_one, RCLike.inner_apply,
      map_add, map_sub, map_mul, map_inv₀, Complex.conj_ofReal]
    field_simp [sqrt_two_ne_zero_complex]
    rw [pow_two, sqrt_two_mul_self_complex]
    ring

/-- The phase gate packaged as the existing proof-relevant unitary transport. -/
def phaseTransport : UnitaryTransport QubitSpace QubitSpace where
  toLinearEquiv := phaseLinearEquiv
  map_inner := by
    intro x y
    change inner Complex (phaseOperator x) (phaseOperator y) = inner Complex x y
    rw [PiLp.inner_apply, PiLp.inner_apply]
    simp only [Fin.sum_univ_two, phaseOperator_apply_zero,
      phaseOperator_apply_one, RCLike.inner_apply,
      map_mul, Complex.conj_I]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- Hadamard fixes the identity operator under conjugation. -/
@[simp] theorem hadamard_conj_one :
    hadamardTransport.conjOperator (1 : Operator QubitSpace) = 1 :=
  UnitaryTransport.conjOperator_one hadamardTransport

/-- Phase fixes the identity operator under conjugation. -/
@[simp] theorem phase_conj_one :
    phaseTransport.conjOperator (1 : Operator QubitSpace) = 1 :=
  UnitaryTransport.conjOperator_one phaseTransport

/-- Concrete `H X H⁻¹ = Z`, realizing the `hadamardClifford` X-to-Z action. -/
theorem hadamard_conj_pauliX :
    hadamardTransport.conjOperator pauliX = pauliZ := by
  ext psi b
  change hadamardOperator (pauliX (hadamardOperator psi)) b = pauliZ psi b
  fin_cases b <;> simp <;>
    field_simp [sqrt_two_ne_zero_complex] <;>
    rw [pow_two, sqrt_two_mul_self_complex] <;> ring

/-- Concrete `H Y H⁻¹ = -Y`, realizing the signed `hadamardClifford` Y action. -/
theorem hadamard_conj_pauliY :
    hadamardTransport.conjOperator pauliY = -pauliY := by
  ext psi b
  change hadamardOperator (pauliY (hadamardOperator psi)) b = (-pauliY) psi b
  fin_cases b <;> simp <;>
    field_simp [sqrt_two_ne_zero_complex] <;>
    rw [pow_two, sqrt_two_mul_self_complex] <;> ring

/-- Concrete `H Z H⁻¹ = X`, realizing the `hadamardClifford` Z-to-X action. -/
theorem hadamard_conj_pauliZ :
    hadamardTransport.conjOperator pauliZ = pauliX := by
  ext psi b
  change hadamardOperator (pauliZ (hadamardOperator psi)) b = pauliX psi b
  fin_cases b <;> simp <;>
    field_simp [sqrt_two_ne_zero_complex] <;>
    rw [pow_two, sqrt_two_mul_self_complex] <;> ring

/-- Concrete `S X S⁻¹ = Y`, giving the X contribution in `phaseClifford`. -/
theorem phase_conj_pauliX :
    phaseTransport.conjOperator pauliX = pauliY := by
  ext psi b
  change phaseOperator (pauliX (phaseInverseOperator psi)) b = pauliY psi b
  fin_cases b <;>
    simp

/-- Concrete `S Y S⁻¹ = -X`, giving the signed Y contribution in `phaseClifford`. -/
theorem phase_conj_pauliY :
    phaseTransport.conjOperator pauliY = -pauliX := by
  ext psi b
  change phaseOperator (pauliY (phaseInverseOperator psi)) b = (-pauliX) psi b
  fin_cases b <;>
    simp [← mul_assoc, Complex.I_mul_I]

/-- Concrete `S Z S⁻¹ = Z`, giving the fixed Z coordinate in `phaseClifford`. -/
theorem phase_conj_pauliZ :
    phaseTransport.conjOperator pauliZ = pauliZ := by
  ext psi b
  change phaseOperator (pauliZ (phaseInverseOperator psi)) b = pauliZ psi b
  fin_cases b <;>
    simp [← mul_assoc, Complex.I_mul_I]

end
end OneQubitMagic
end Distillation
end QEC
