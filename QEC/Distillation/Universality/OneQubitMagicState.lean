import QEC.Distillation.Universality.OneQubitClifford
noncomputable section

namespace QEC
namespace Distillation
namespace OneQubitMagic

open Semantics Semantics.Qubit

def tBloch : PauliAxis -> Real
  | .x | .y | .z => (Real.sqrt 3)⁻¹

def hBloch : PauliAxis -> Real
  | .x | .z => (Real.sqrt 2)⁻¹
  | .y => 0

def tReference : TDirection := ⟨fun _ => .pos, by intro i; simp⟩

def hReference : HDirection :=
  ⟨fun | .x => .pos | .y => .zero | .z => .pos, by native_decide⟩

def signedCoordinateValue : SignedCoordinate -> Int
  | .neg => -1
  | .zero => 0
  | .pos => 1

def tBlochOfDirection (d : TDirection) : PauliAxis -> Real :=
  fun i => (signedCoordinateValue (d.1 i) : Real) * (Real.sqrt 3)⁻¹

def hBlochOfDirection (d : HDirection) : PauliAxis -> Real :=
  fun i => (signedCoordinateValue (d.1 i) : Real) * (Real.sqrt 2)⁻¹

def blochNormSq (r : PauliAxis -> Real) : Real :=
  r .x ^ 2 + r .y ^ 2 + r .z ^ 2

def pauliOperator : PauliAxis -> Operator QubitSpace
  | .x => pauliX
  | .y => pauliY
  | .z => pauliZ

def blochOperator (r : PauliAxis -> Real) : Operator QubitSpace :=
  (r .x : Complex) • pauliX + (r .y : Complex) • pauliY + (r .z : Complex) • pauliZ

def blochProjector (r : PauliAxis -> Real) : Operator QubitSpace :=
  (2 : Complex)⁻¹ • (1 + blochOperator r)

def tProjector (d : TDirection) : Operator QubitSpace :=
  blochProjector (tBlochOfDirection d)

def hProjector (d : HDirection) : Operator QubitSpace :=
  blochProjector (hBlochOfDirection d)

private theorem conjOperator_add
    (U : UnitaryTransport QubitSpace QubitSpace)
    (A B : Operator QubitSpace) :
    U.conjOperator (A + B) = U.conjOperator A + U.conjOperator B := by
  ext psi
  simp [UnitaryTransport.conjOperator]

private theorem conjOperator_smul
    (U : UnitaryTransport QubitSpace QubitSpace)
    (c : Complex) (A : Operator QubitSpace) :
    U.conjOperator (c • A) = c • U.conjOperator A := by
  ext psi
  simp [UnitaryTransport.conjOperator]

private def hadamardBlochAction (r : PauliAxis -> Real) : PauliAxis -> Real
  | .x => r .z
  | .y => -r .y
  | .z => r .x

private def phaseBlochAction (r : PauliAxis -> Real) : PauliAxis -> Real
  | .x => -r .y
  | .y => r .x
  | .z => r .z

private theorem hadamard_conj_blochProjector (r : PauliAxis -> Real) :
    hadamardTransport.conjOperator (blochProjector r) =
      blochProjector (hadamardBlochAction r) := by
  simp only [blochProjector, blochOperator, conjOperator_smul, conjOperator_add,
    hadamard_conj_one, hadamard_conj_pauliX, hadamard_conj_pauliY,
    hadamard_conj_pauliZ, hadamardBlochAction]
  module

private theorem phase_conj_blochProjector (r : PauliAxis -> Real) :
    phaseTransport.conjOperator (blochProjector r) =
      blochProjector (phaseBlochAction r) := by
  simp only [blochProjector, blochOperator, conjOperator_smul, conjOperator_add,
    phase_conj_one, phase_conj_pauliX, phase_conj_pauliY,
    phase_conj_pauliZ, phaseBlochAction]
  module

private theorem signedCoordinateValue_neg_smul (c : SignedCoordinate) :
    signedCoordinateValue ((-1 : ℤˣ) • c) = -signedCoordinateValue c := by
  cases c <;> rfl

private theorem hadamard_tDirection_val (d : TDirection) :
    (hadamardClifford • d).1 = hadamardClifford.1 • d.1 := rfl

private theorem phase_tDirection_val (d : TDirection) :
    (phaseClifford • d).1 = phaseClifford.1 • d.1 := rfl

private theorem hadamard_hDirection_val (d : HDirection) :
    (hadamardClifford • d).1 = hadamardClifford.1 • d.1 := rfl

private theorem phase_hDirection_val (d : HDirection) :
    (phaseClifford • d).1 = phaseClifford.1 • d.1 := rfl

private theorem hadamard_tBlochOfDirection (d : TDirection) :
    hadamardBlochAction (tBlochOfDirection d) =
      tBlochOfDirection (hadamardClifford • d) := by
  funext i
  simp only [tBlochOfDirection]
  rw [hadamard_tDirection_val]
  fin_cases i <;>
    simp [hadamardBlochAction, tBlochOfDirection, signedCoordinateValue_neg_smul]

private theorem phase_tBlochOfDirection (d : TDirection) :
    phaseBlochAction (tBlochOfDirection d) =
      tBlochOfDirection (phaseClifford • d) := by
  funext i
  simp only [tBlochOfDirection]
  rw [phase_tDirection_val]
  fin_cases i <;>
    simp [phaseBlochAction, tBlochOfDirection, signedCoordinateValue_neg_smul]

private theorem hadamard_hBlochOfDirection (d : HDirection) :
    hadamardBlochAction (hBlochOfDirection d) =
      hBlochOfDirection (hadamardClifford • d) := by
  funext i
  simp only [hBlochOfDirection]
  rw [hadamard_hDirection_val]
  fin_cases i <;>
    simp [hadamardBlochAction, hBlochOfDirection, signedCoordinateValue_neg_smul]

private theorem phase_hBlochOfDirection (d : HDirection) :
    phaseBlochAction (hBlochOfDirection d) =
      hBlochOfDirection (phaseClifford • d) := by
  funext i
  simp only [hBlochOfDirection]
  rw [phase_hDirection_val]
  fin_cases i <;>
    simp [phaseBlochAction, hBlochOfDirection, signedCoordinateValue_neg_smul]

theorem hadamard_conj_tProjector (d : TDirection) :
    hadamardTransport.conjOperator (tProjector d) =
      tProjector (hadamardClifford • d) := by
  simpa only [tProjector, hadamard_tBlochOfDirection] using
    hadamard_conj_blochProjector (tBlochOfDirection d)

theorem phase_conj_tProjector (d : TDirection) :
    phaseTransport.conjOperator (tProjector d) =
      tProjector (phaseClifford • d) := by
  simpa only [tProjector, phase_tBlochOfDirection] using
    phase_conj_blochProjector (tBlochOfDirection d)

theorem hadamard_conj_hProjector (d : HDirection) :
    hadamardTransport.conjOperator (hProjector d) =
      hProjector (hadamardClifford • d) := by
  simpa only [hProjector, hadamard_hBlochOfDirection] using
    hadamard_conj_blochProjector (hBlochOfDirection d)

theorem phase_conj_hProjector (d : HDirection) :
    phaseTransport.conjOperator (hProjector d) =
      hProjector (phaseClifford • d) := by
  simpa only [hProjector, phase_hBlochOfDirection] using
    phase_conj_blochProjector (hBlochOfDirection d)

theorem trace_pauli_mul_blochProjector
    (r : PauliAxis -> Real) (i : PauliAxis) :
    LinearMap.trace Complex QubitSpace
      (pauliOperator i * blochProjector r) = r i := by
  fin_cases i <;>
    simp [pauliOperator, blochProjector, blochOperator, mul_add,
      pauliX_trace, pauliY_trace, pauliZ_trace,
      pauliX_pauliX_trace, pauliX_pauliY_trace, pauliX_pauliZ_trace,
      pauliY_pauliX_trace, pauliY_pauliY_trace, pauliY_pauliZ_trace,
      pauliZ_pauliX_trace, pauliZ_pauliY_trace, pauliZ_pauliZ_trace] <;>
    ring

theorem blochProjector_injective : Function.Injective blochProjector := by
  intro r s hrs
  funext i
  apply Complex.ofReal_injective
  simpa only [trace_pauli_mul_blochProjector] using congrArg
    (fun projector =>
      LinearMap.trace Complex QubitSpace (pauliOperator i * projector)) hrs

/-- The real Pauli expectation coordinates of an arbitrary one-qubit density. -/
def densityBloch (rho : DensityOperator QubitSpace) : PauliAxis → Real :=
  fun i => (LinearMap.trace Complex QubitSpace
    (pauliOperator i * rho.toOperator)).re

/-- Every mixed one-qubit density has its exact Pauli/Bloch expansion. -/
theorem density_toOperator_eq_blochProjector
    (rho : DensityOperator QubitSpace) :
    rho.toOperator = blochProjector (densityBloch rho) := by
  let b := EuclideanSpace.basisFun (Fin 2) Complex
  let M := LinearMap.toMatrix b.toBasis b.toBasis rho.toOperator
  have htrace : Matrix.trace M = 1 := by
    rw [← LinearMap.trace_eq_matrix_trace Complex b.toBasis]
    exact rho.trace_one
  have hherm : Matrix.conjTranspose M = M := by
    rw [← LinearMap.toMatrix_adjoint b b]
    exact congrArg (LinearMap.toMatrix b.toBasis b.toBasis)
      rho.positive.adjoint_eq
  have h00 := congrFun (congrFun hherm (0 : Fin 2)) (0 : Fin 2)
  have h01 := congrFun (congrFun hherm (0 : Fin 2)) (1 : Fin 2)
  have h10 := congrFun (congrFun hherm (1 : Fin 2)) (0 : Fin 2)
  have h11 := congrFun (congrFun hherm (1 : Fin 2)) (1 : Fin 2)
  simp only [Matrix.conjTranspose_apply] at h00 h01 h10 h11
  have h00im : (M 0 0).im = 0 := by
    have h := congrArg Complex.im h00
    simp [RCLike.star_def] at h
    linarith
  have h11im : (M 1 1).im = 0 := by
    have h := congrArg Complex.im h11
    simp [RCLike.star_def] at h
    linarith
  have h10re : (M 1 0).re = (M 0 1).re := by
    have h := congrArg Complex.re h10
    simpa [RCLike.star_def] using h.symm
  have h10im : (M 1 0).im = -(M 0 1).im := by
    have h := congrArg Complex.im h10
    simpa [RCLike.star_def] using h.symm
  have htraceRe : (M 0 0).re + (M 1 1).re = 1 := by
    have h := congrArg Complex.re htrace
    simpa [Matrix.trace] using h
  have hXmatrix : LinearMap.toMatrix b.toBasis b.toBasis pauliX = pauliXMatrix := by
    simp [b, pauliX, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  have hYmatrix : LinearMap.toMatrix b.toBasis b.toBasis pauliY = pauliYMatrix := by
    simp [b, pauliY, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  have hZmatrix : LinearMap.toMatrix b.toBasis b.toBasis pauliZ = pauliZMatrix := by
    simp [b, pauliZ, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  have hx : LinearMap.trace Complex QubitSpace (pauliX * rho.toOperator) =
      M 1 0 + M 0 1 := by
    rw [LinearMap.trace_eq_matrix_trace Complex b.toBasis,
      LinearMap.toMatrix_mul, hXmatrix]
    change Matrix.trace (pauliXMatrix * M) = _
    simp [Matrix.trace, Matrix.mul_apply, pauliXMatrix, flipBit]
  have hy : LinearMap.trace Complex QubitSpace (pauliY * rho.toOperator) =
      Complex.I * M 0 1 - Complex.I * M 1 0 := by
    rw [LinearMap.trace_eq_matrix_trace Complex b.toBasis,
      LinearMap.toMatrix_mul, hYmatrix]
    change Matrix.trace (pauliYMatrix * M) = _
    simp [Matrix.trace, Matrix.mul_apply, pauliYMatrix]
    ring
  have hz : LinearMap.trace Complex QubitSpace (pauliZ * rho.toOperator) =
      M 0 0 - M 1 1 := by
    rw [LinearMap.trace_eq_matrix_trace Complex b.toBasis,
      LinearMap.toMatrix_mul, hZmatrix]
    change Matrix.trace (pauliZMatrix * M) = _
    simp [Matrix.trace, Matrix.mul_apply, pauliZMatrix, zPhase]
    ring
  apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
  ext i j
  fin_cases i <;> fin_cases j
  all_goals change M _ _ = _
  all_goals
    simp only [blochProjector, blochOperator, densityBloch, pauliOperator,
      map_smul, map_add, LinearMap.toMatrix_one]
  all_goals rw [hx, hy, hz]
  all_goals simp [hXmatrix, hYmatrix, hZmatrix, b,
    pauliXMatrix, pauliYMatrix, pauliZMatrix, flipBit, zPhase]
  all_goals apply Complex.ext <;> norm_num <;> linarith

theorem blochOperator_apply_zero (r : PauliAxis -> Real) (psi : QubitSpace) :
    blochOperator r psi 0 =
      (r .z : Complex) * psi 0 + ((r .x : Complex) - Complex.I * r .y) * psi 1 := by
  simp [blochOperator]
  ring

theorem blochOperator_apply_one (r : PauliAxis -> Real) (psi : QubitSpace) :
    blochOperator r psi 1 =
      ((r .x : Complex) + Complex.I * r .y) * psi 0 - (r .z : Complex) * psi 1 := by
  simp [blochOperator]
  ring

theorem bloch_square_zero_diagonal (r : PauliAxis -> Real) :
    (r .z : Complex) * (r .z : Complex) +
        ((r .x : Complex) - Complex.I * (r .y : Complex)) *
          ((r .x : Complex) + Complex.I * (r .y : Complex)) =
      (blochNormSq r : Complex) := by
  have hIry_sq :
      (Complex.I * (r .y : Complex)) * (Complex.I * (r .y : Complex)) =
        -((r .y : Complex) * (r .y : Complex)) := by
    calc
      (Complex.I * (r .y : Complex)) * (Complex.I * (r .y : Complex)) =
          (Complex.I * Complex.I) * ((r .y : Complex) * (r .y : Complex)) := by ring
      _ = -((r .y : Complex) * (r .y : Complex)) := by
        rw [Complex.I_mul_I]
        ring
  have hcast : (blochNormSq r : Complex) =
      (r .x : Complex) * (r .x : Complex) +
        (r .y : Complex) * (r .y : Complex) +
        (r .z : Complex) * (r .z : Complex) := by
    simp only [blochNormSq]
    norm_cast
    ring
  rw [hcast]
  rw [show ((r .x : Complex) - Complex.I * (r .y : Complex)) *
      ((r .x : Complex) + Complex.I * (r .y : Complex)) =
      (r .x : Complex) * (r .x : Complex) -
        (Complex.I * (r .y : Complex)) * (Complex.I * (r .y : Complex)) by ring]
  rw [hIry_sq]
  ring

theorem bloch_square_zero_off_diagonal (r : PauliAxis -> Real) :
    (r .z : Complex) * ((r .x : Complex) - Complex.I * (r .y : Complex)) -
      ((r .x : Complex) - Complex.I * (r .y : Complex)) * (r .z : Complex) = 0 := by
  ring

theorem bloch_square_one_diagonal (r : PauliAxis -> Real) :
    (r .z : Complex) * (r .z : Complex) +
        ((r .x : Complex) + Complex.I * (r .y : Complex)) *
          ((r .x : Complex) - Complex.I * (r .y : Complex)) =
      (blochNormSq r : Complex) := by
  have hIry_sq :
      (Complex.I * (r .y : Complex)) * (Complex.I * (r .y : Complex)) =
        -((r .y : Complex) * (r .y : Complex)) := by
    calc
      (Complex.I * (r .y : Complex)) * (Complex.I * (r .y : Complex)) =
          (Complex.I * Complex.I) * ((r .y : Complex) * (r .y : Complex)) := by ring
      _ = -((r .y : Complex) * (r .y : Complex)) := by
        rw [Complex.I_mul_I]
        ring
  have hcast : (blochNormSq r : Complex) =
      (r .x : Complex) * (r .x : Complex) +
        (r .y : Complex) * (r .y : Complex) +
        (r .z : Complex) * (r .z : Complex) := by
    simp only [blochNormSq]
    norm_cast
    ring
  rw [hcast]
  rw [show ((r .x : Complex) + Complex.I * (r .y : Complex)) *
      ((r .x : Complex) - Complex.I * (r .y : Complex)) =
      (r .x : Complex) * (r .x : Complex) -
        (Complex.I * (r .y : Complex)) * (Complex.I * (r .y : Complex)) by ring]
  rw [hIry_sq]
  ring

theorem bloch_square_one_off_diagonal (r : PauliAxis -> Real) :
    ((r .x : Complex) + Complex.I * (r .y : Complex)) * (r .z : Complex) -
      (r .z : Complex) * ((r .x : Complex) + Complex.I * (r .y : Complex)) = 0 := by
  ring

theorem tBloch_normalized : blochNormSq tBloch = 1 := by
  have hsquare : Real.sqrt (3 : Real) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt (3 : Real) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  simp only [blochNormSq, tBloch]
  field_simp [hne]
  nlinarith

theorem hBloch_normalized : blochNormSq hBloch = 1 := by
  have hsquare : Real.sqrt (2 : Real) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt (2 : Real) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  simp only [blochNormSq, hBloch]
  field_simp [hne]
  nlinarith

private theorem tDirection_signedCoordinate_sq_sum (d : TDirection) :
    signedCoordinateValue (d.1 .x) ^ 2 + signedCoordinateValue (d.1 .y) ^ 2 +
      signedCoordinateValue (d.1 .z) ^ 2 = 3 := by
  rcases d with ⟨d, hd⟩
  revert d
  native_decide

private theorem hDirection_signedCoordinate_sq_sum (d : HDirection) :
    signedCoordinateValue (d.1 .x) ^ 2 + signedCoordinateValue (d.1 .y) ^ 2 +
      signedCoordinateValue (d.1 .z) ^ 2 = 2 := by
  rcases d with ⟨d, hd⟩
  revert d
  native_decide

theorem tBlochOfDirection_normalized (d : TDirection) :
    blochNormSq (tBlochOfDirection d) = 1 := by
  have hsum :
      (signedCoordinateValue (d.1 .x) : Real) ^ 2 +
          (signedCoordinateValue (d.1 .y) : Real) ^ 2 +
          (signedCoordinateValue (d.1 .z) : Real) ^ 2 = 3 := by
    exact_mod_cast tDirection_signedCoordinate_sq_sum d
  have hsquare : Real.sqrt (3 : Real) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt (3 : Real) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  simp only [blochNormSq, tBlochOfDirection]
  calc
    _ = ((signedCoordinateValue (d.1 .x) : Real) ^ 2 +
          (signedCoordinateValue (d.1 .y) : Real) ^ 2 +
          (signedCoordinateValue (d.1 .z) : Real) ^ 2) *
        (Real.sqrt 3)⁻¹ ^ 2 := by ring
    _ = 3 * (Real.sqrt 3)⁻¹ ^ 2 := by rw [hsum]
    _ = 1 := by
      field_simp [hne]
      exact hsquare.symm

theorem hBlochOfDirection_normalized (d : HDirection) :
    blochNormSq (hBlochOfDirection d) = 1 := by
  have hsum :
      (signedCoordinateValue (d.1 .x) : Real) ^ 2 +
          (signedCoordinateValue (d.1 .y) : Real) ^ 2 +
          (signedCoordinateValue (d.1 .z) : Real) ^ 2 = 2 := by
    exact_mod_cast hDirection_signedCoordinate_sq_sum d
  have hsquare : Real.sqrt (2 : Real) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt (2 : Real) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  simp only [blochNormSq, hBlochOfDirection]
  calc
    _ = ((signedCoordinateValue (d.1 .x) : Real) ^ 2 +
          (signedCoordinateValue (d.1 .y) : Real) ^ 2 +
          (signedCoordinateValue (d.1 .z) : Real) ^ 2) *
        (Real.sqrt 2)⁻¹ ^ 2 := by ring
    _ = 2 * (Real.sqrt 2)⁻¹ ^ 2 := by rw [hsum]
    _ = 1 := by
      field_simp [hne]
      exact hsquare.symm

theorem blochOperator_square (r : PauliAxis -> Real) :
    blochOperator r * blochOperator r = (blochNormSq r : Complex) • 1 := by
  ext psi b
  fin_cases b
  · change (blochOperator r (blochOperator r psi)) 0 =
      (((blochNormSq r : Complex) • (1 : Operator QubitSpace)) psi) 0
    rw [blochOperator_apply_zero r (blochOperator r psi),
      blochOperator_apply_zero r psi,
      blochOperator_apply_one r psi]
    change
      (r .z : Complex) * ((r .z : Complex) * psi 0 +
          ((r .x : Complex) - Complex.I * (r .y : Complex)) * psi 1) +
        ((r .x : Complex) - Complex.I * (r .y : Complex)) *
          (((r .x : Complex) + Complex.I * (r .y : Complex)) * psi 0 -
            (r .z : Complex) * psi 1) =
        (blochNormSq r : Complex) * psi 0
    calc
      _ = ((r .z : Complex) * (r .z : Complex) +
            ((r .x : Complex) - Complex.I * (r .y : Complex)) *
              ((r .x : Complex) + Complex.I * (r .y : Complex))) * psi 0 +
          ((r .z : Complex) * ((r .x : Complex) - Complex.I * (r .y : Complex)) -
            ((r .x : Complex) - Complex.I * (r .y : Complex)) * (r .z : Complex)) * psi 1 := by
        ring
      _ = (blochNormSq r : Complex) * psi 0 + 0 * psi 1 := by
        rw [bloch_square_zero_diagonal, bloch_square_zero_off_diagonal]
      _ = _ := by simp
  · change (blochOperator r (blochOperator r psi)) 1 =
      (((blochNormSq r : Complex) • (1 : Operator QubitSpace)) psi) 1
    rw [blochOperator_apply_one r (blochOperator r psi),
      blochOperator_apply_zero r psi,
      blochOperator_apply_one r psi]
    change
      ((r .x : Complex) + Complex.I * (r .y : Complex)) *
          ((r .z : Complex) * psi 0 +
            ((r .x : Complex) - Complex.I * (r .y : Complex)) * psi 1) -
        (r .z : Complex) *
          (((r .x : Complex) + Complex.I * (r .y : Complex)) * psi 0 -
            (r .z : Complex) * psi 1) =
        (blochNormSq r : Complex) * psi 1
    calc
      _ = (((r .x : Complex) + Complex.I * (r .y : Complex)) * (r .z : Complex) -
            (r .z : Complex) * ((r .x : Complex) + Complex.I * (r .y : Complex))) * psi 0 +
          ((r .z : Complex) * (r .z : Complex) +
            ((r .x : Complex) + Complex.I * (r .y : Complex)) *
              ((r .x : Complex) - Complex.I * (r .y : Complex))) * psi 1 := by
        ring
      _ = 0 * psi 0 + (blochNormSq r : Complex) * psi 1 := by
        rw [bloch_square_one_off_diagonal, bloch_square_one_diagonal]
      _ = _ := by simp

theorem blochOperator_adjoint (r : PauliAxis -> Real) :
    LinearMap.adjoint (blochOperator r) = blochOperator r := by
  apply LinearMap.IsSymmetric.adjoint_eq
  unfold blochOperator
  apply LinearMap.IsSymmetric.add
  · apply LinearMap.IsSymmetric.add
    · apply LinearMap.IsSymmetric.smul
      · simp
      · rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
        exact pauliX_adjoint
    · apply LinearMap.IsSymmetric.smul
      · simp
      · rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
        exact pauliY_adjoint
  · apply LinearMap.IsSymmetric.smul
    · simp
    · rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
      exact pauliZ_adjoint

theorem blochProjector_idempotent (r : PauliAxis -> Real)
    (hr : blochNormSq r = 1) : blochProjector r * blochProjector r = blochProjector r := by
  have hsquare : blochOperator r * blochOperator r = 1 := by
    rw [blochOperator_square, hr]
    norm_num
  simp only [blochProjector, smul_mul_assoc, mul_smul_comm, smul_smul,
    mul_add, add_mul, one_mul, mul_one, hsquare]
  module

theorem blochProjector_isSymmetricProjection (r : PauliAxis -> Real)
    (hr : blochNormSq r = 1) : (blochProjector r).IsSymmetricProjection := by
  refine ⟨blochProjector_idempotent r hr, ?_⟩
  unfold blochProjector
  apply LinearMap.IsSymmetric.smul
  · simp only [starRingEnd_apply, star_inv₀, star_ofNat]
  · apply LinearMap.IsSymmetric.add
    · exact LinearMap.IsSymmetric.one
    · rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
      exact blochOperator_adjoint r

theorem blochProjector_positive (r : PauliAxis -> Real)
    (hr : blochNormSq r = 1) : LinearMap.IsPositive (blochProjector r) :=
  (blochProjector_isSymmetricProjection r hr).isPositive

theorem blochProjector_trace_one (r : PauliAxis -> Real)
    (hr : blochNormSq r = 1) : LinearMap.trace Complex QubitSpace (blochProjector r) = 1 := by
  simp [blochProjector, blochOperator, pauliI_trace, pauliX_trace, pauliY_trace,
    pauliZ_trace]

noncomputable def blochDensity (r : PauliAxis -> Real)
    (hr : blochNormSq r = 1) : DensityOperator QubitSpace where
  toOperator := blochProjector r
  positive := blochProjector_positive r hr
  trace_one := blochProjector_trace_one r hr

noncomputable def tMagicState : DensityOperator QubitSpace :=
  blochDensity tBloch tBloch_normalized

noncomputable def hMagicState : DensityOperator QubitSpace :=
  blochDensity hBloch hBloch_normalized

noncomputable def tMagicStateOfDirection (d : TDirection) : DensityOperator QubitSpace :=
  blochDensity (tBlochOfDirection d) (tBlochOfDirection_normalized d)

noncomputable def hMagicStateOfDirection (d : HDirection) : DensityOperator QubitSpace :=
  blochDensity (hBlochOfDirection d) (hBlochOfDirection_normalized d)

private theorem densityOperator_ext {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl

theorem hadamard_conj_tMagicState (d : TDirection) :
    hadamardTransport.conjDensity (tMagicStateOfDirection d) =
      tMagicStateOfDirection (hadamardClifford • d) := by
  apply densityOperator_ext
  rw [UnitaryTransport.conjDensity_toOperator]
  change hadamardTransport.conjOperator (tProjector d) =
    tProjector (hadamardClifford • d)
  exact hadamard_conj_tProjector d

theorem phase_conj_tMagicState (d : TDirection) :
    phaseTransport.conjDensity (tMagicStateOfDirection d) =
      tMagicStateOfDirection (phaseClifford • d) := by
  apply densityOperator_ext
  rw [UnitaryTransport.conjDensity_toOperator]
  change phaseTransport.conjOperator (tProjector d) =
    tProjector (phaseClifford • d)
  exact phase_conj_tProjector d

theorem hadamard_conj_hMagicState (d : HDirection) :
    hadamardTransport.conjDensity (hMagicStateOfDirection d) =
      hMagicStateOfDirection (hadamardClifford • d) := by
  apply densityOperator_ext
  rw [UnitaryTransport.conjDensity_toOperator]
  change hadamardTransport.conjOperator (hProjector d) =
    hProjector (hadamardClifford • d)
  exact hadamard_conj_hProjector d

theorem phase_conj_hMagicState (d : HDirection) :
    phaseTransport.conjDensity (hMagicStateOfDirection d) =
      hMagicStateOfDirection (phaseClifford • d) := by
  apply densityOperator_ext
  rw [UnitaryTransport.conjDensity_toOperator]
  change phaseTransport.conjOperator (hProjector d) =
    hProjector (phaseClifford • d)
  exact phase_conj_hProjector d

private theorem signedCoordinateValue_injective :
    Function.Injective signedCoordinateValue := by
  intro a b hab
  cases a <;> cases b <;> simp_all [signedCoordinateValue]

private theorem tBlochOfDirection_injective :
    Function.Injective tBlochOfDirection := by
  intro d e hde
  apply Subtype.ext
  funext i
  apply signedCoordinateValue_injective
  have hi := congrFun hde i
  simp only [tBlochOfDirection] at hi
  have hinv : (Real.sqrt 3)⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))
  have hvalue :
      (signedCoordinateValue (d.1 i) : Real) = signedCoordinateValue (e.1 i) :=
    mul_right_cancel₀ hinv hi
  exact_mod_cast hvalue

private theorem hBlochOfDirection_injective :
    Function.Injective hBlochOfDirection := by
  intro d e hde
  apply Subtype.ext
  funext i
  apply signedCoordinateValue_injective
  have hi := congrFun hde i
  simp only [hBlochOfDirection] at hi
  have hinv : (Real.sqrt 2)⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))
  have hvalue :
      (signedCoordinateValue (d.1 i) : Real) = signedCoordinateValue (e.1 i) :=
    mul_right_cancel₀ hinv hi
  exact_mod_cast hvalue

theorem tMagicState_injective : Function.Injective tMagicStateOfDirection := by
  intro d e hde
  apply tBlochOfDirection_injective
  apply blochProjector_injective
  simpa [tMagicStateOfDirection, blochDensity] using congrArg
    (fun rho : DensityOperator QubitSpace => rho.toOperator) hde

theorem hMagicState_injective : Function.Injective hMagicStateOfDirection := by
  intro d e hde
  apply hBlochOfDirection_injective
  apply blochProjector_injective
  simpa [hMagicStateOfDirection, blochDensity] using congrArg
    (fun rho : DensityOperator QubitSpace => rho.toOperator) hde

theorem card_tMagicStateRange : (Set.range tMagicStateOfDirection).ncard = 8 := by
  rw [Set.ncard_range_of_injective tMagicState_injective,
    Nat.card_eq_fintype_card, card_tDirection]

theorem card_hMagicStateRange : (Set.range hMagicStateOfDirection).ncard = 12 := by
  rw [Set.ncard_range_of_injective hMagicState_injective,
    Nat.card_eq_fintype_card, card_hDirection]

theorem density_exists_rankOne_ensemble
    (rho : DensityOperator QubitSpace) :
    ∃ (m : Nat) (u : Fin m → QubitSpace),
      rho.toOperator =
        ∑ i, (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap := by
  have hpositive :
      (LinearMap.toContinuousLinearMap rho.toOperator).IsPositive :=
    (LinearMap.isPositive_toContinuousLinearMap_iff rho.toOperator).2 rho.positive
  rcases (ContinuousLinearMap.isPositive_iff_eq_sum_rankOne).1 hpositive with
    ⟨m, u, hu⟩
  refine ⟨m, u, ?_⟩
  simpa using congrArg ContinuousLinearMap.toLinearMap hu

theorem rankOne_ensemble_trace_one
    (rho : DensityOperator QubitSpace) {m : Nat}
    (u : Fin m → QubitSpace)
    (hensemble : rho.toOperator =
      ∑ i, (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap) :
    ∑ i, inner Complex (u i) (u i) = 1 := by
  have htrace := rho.trace_one
  rw [hensemble] at htrace
  simpa [map_sum, InnerProductSpace.trace_rankOne] using htrace

theorem rankOne_ensemble_norm_sq_sum_one
    (rho : DensityOperator QubitSpace) {m : Nat}
    (u : Fin m → QubitSpace)
    (hensemble : rho.toOperator =
      ∑ i, (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap) :
    ∑ i, ‖u i‖ ^ 2 = 1 := by
  have htrace := rankOne_ensemble_trace_one rho u hensemble
  have hre := congrArg Complex.re htrace
  simpa [inner_self_eq_norm_sq_to_K, map_sum, pow_two] using hre

theorem trace_mul_rankOne
    (P : Operator QubitSpace) (u : QubitSpace) :
    LinearMap.trace Complex QubitSpace
      (P * (InnerProductSpace.rankOne Complex u u).toLinearMap) =
      inner Complex u (P u) := by
  have hcomp :
      P.comp (InnerProductSpace.rankOne Complex u u).toLinearMap =
        (InnerProductSpace.rankOne Complex (P u) u).toLinearMap := by
    ext z
    simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply]
  change LinearMap.trace Complex QubitSpace
      (P.comp (InnerProductSpace.rankOne Complex u u).toLinearMap) = _
  rw [hcomp, InnerProductSpace.trace_rankOne]

def projectionSquaredOverlap
    (P : Operator QubitSpace) (rho : DensityOperator QubitSpace) : Real :=
  (LinearMap.trace Complex QubitSpace (P * rho.toOperator)).re

def projectionFidelity
    (P : Operator QubitSpace) (rho : DensityOperator QubitSpace) : Real :=
  Real.sqrt (projectionSquaredOverlap P rho)

theorem projectionSquaredOverlap_mem_Icc
    (P : Operator QubitSpace) (rho : DensityOperator QubitSpace)
    (hP : P.IsSymmetricProjection) :
    projectionSquaredOverlap P rho ∈ Set.Icc 0 1 := by
  rcases density_exists_rankOne_ensemble rho with ⟨m, u, hensemble⟩
  have hnorm := rankOne_ensemble_norm_sq_sum_one rho u hensemble
  have hoverlap :
      projectionSquaredOverlap P rho =
        ∑ i, (inner Complex (u i) (P (u i))).re := by
    unfold projectionSquaredOverlap
    rw [hensemble, Finset.mul_sum]
    simp [map_sum, trace_mul_rankOne]
  have hOne : (1 : Operator QubitSpace).IsSymmetricProjection := by
    constructor
    · exact one_mul _
    · intro x y
      simp
  have hComplement : LinearMap.IsPositive (1 - P) :=
    (hP.sub_of_range_le_range hOne (by
      intro y _
      exact ⟨y, by simp⟩)).isPositive
  rw [hoverlap]
  constructor
  · exact Finset.sum_nonneg fun i _ =>
      hP.isPositive.re_inner_nonneg_right (u i)
  · calc
      (∑ i, (inner Complex (u i) (P (u i))).re) ≤
          ∑ i, ‖u i‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hnonneg := hComplement.re_inner_nonneg_right (u i)
        simpa [sub_apply, inner_sub_right, inner_self_eq_norm_sq_to_K,
          map_sub, pow_two] using hnonneg
      _ = 1 := hnorm

theorem projectionSquaredOverlap_nonneg
    (P : Operator QubitSpace) (rho : DensityOperator QubitSpace)
    (hP : P.IsSymmetricProjection) :
    0 ≤ projectionSquaredOverlap P rho :=
  (projectionSquaredOverlap_mem_Icc P rho hP).1

theorem projectionSquaredOverlap_le_one
    (P : Operator QubitSpace) (rho : DensityOperator QubitSpace)
    (hP : P.IsSymmetricProjection) :
    projectionSquaredOverlap P rho ≤ 1 :=
  (projectionSquaredOverlap_mem_Icc P rho hP).2

theorem projectionFidelity_nonneg
    (P : Operator QubitSpace) (rho : DensityOperator QubitSpace) :
    0 ≤ projectionFidelity P rho := by
  exact Real.sqrt_nonneg _

theorem projectionFidelity_le_one
    (P : Operator QubitSpace) (rho : DensityOperator QubitSpace)
    (hP : P.IsSymmetricProjection) :
    projectionFidelity P rho ≤ 1 := by
  rw [projectionFidelity, Real.sqrt_le_one]
  exact projectionSquaredOverlap_le_one P rho hP

theorem projectionFidelity_mem_Icc
    (P : Operator QubitSpace) (rho : DensityOperator QubitSpace)
    (hP : P.IsSymmetricProjection) :
    projectionFidelity P rho ∈ Set.Icc 0 1 :=
  ⟨projectionFidelity_nonneg P rho,
    projectionFidelity_le_one P rho hP⟩

theorem tProjector_isSymmetricProjection (d : TDirection) :
    (tProjector d).IsSymmetricProjection := by
  simpa only [tProjector] using
    blochProjector_isSymmetricProjection
      (tBlochOfDirection d) (tBlochOfDirection_normalized d)

theorem hProjector_isSymmetricProjection (d : HDirection) :
    (hProjector d).IsSymmetricProjection := by
  simpa only [hProjector] using
    blochProjector_isSymmetricProjection
      (hBlochOfDirection d) (hBlochOfDirection_normalized d)

def tDirectionFidelity
    (rho : DensityOperator QubitSpace) (d : TDirection) : Real :=
  projectionFidelity (tProjector d) rho

def hDirectionFidelity
    (rho : DensityOperator QubitSpace) (d : HDirection) : Real :=
  projectionFidelity (hProjector d) rho

theorem tDirectionFidelity_mem_Icc
    (rho : DensityOperator QubitSpace) (d : TDirection) :
    tDirectionFidelity rho d ∈ Set.Icc 0 1 := by
  unfold tDirectionFidelity
  exact projectionFidelity_mem_Icc (tProjector d) rho
    (tProjector_isSymmetricProjection d)

theorem hDirectionFidelity_mem_Icc
    (rho : DensityOperator QubitSpace) (d : HDirection) :
    hDirectionFidelity rho d ∈ Set.Icc 0 1 := by
  unfold hDirectionFidelity
  exact projectionFidelity_mem_Icc (hProjector d) rho
    (hProjector_isSymmetricProjection d)

def tFidelity (rho : DensityOperator QubitSpace) : Real :=
  Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨tReference⟩)
    (tDirectionFidelity rho)

def hFidelity (rho : DensityOperator QubitSpace) : Real :=
  Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨hReference⟩)
    (hDirectionFidelity rho)

theorem tFidelity_mem_Icc (rho : DensityOperator QubitSpace) :
    tFidelity rho ∈ Set.Icc 0 1 := by
  unfold tFidelity
  constructor
  · exact (tDirectionFidelity_mem_Icc rho tReference).1.trans
      (Finset.le_sup' (tDirectionFidelity rho) (Finset.mem_univ tReference))
  · exact Finset.sup'_le _ _ fun d _ =>
      (tDirectionFidelity_mem_Icc rho d).2

theorem hFidelity_mem_Icc (rho : DensityOperator QubitSpace) :
    hFidelity rho ∈ Set.Icc 0 1 := by
  unfold hFidelity
  constructor
  · exact (hDirectionFidelity_mem_Icc rho hReference).1.trans
      (Finset.le_sup' (hDirectionFidelity rho) (Finset.mem_univ hReference))
  · exact Finset.sup'_le _ _ fun d _ =>
      (hDirectionFidelity_mem_Icc rho d).2

theorem exists_tDirection_attaining_fidelity
    (rho : DensityOperator QubitSpace) :
    ∃ d, tFidelity rho = tDirectionFidelity rho d := by
  unfold tFidelity
  obtain ⟨d, _, hd⟩ :=
    Finset.exists_mem_eq_sup'
      (Finset.univ_nonempty_iff.mpr ⟨tReference⟩) (tDirectionFidelity rho)
  exact ⟨d, hd⟩

theorem exists_hDirection_attaining_fidelity
    (rho : DensityOperator QubitSpace) :
    ∃ d, hFidelity rho = hDirectionFidelity rho d := by
  unfold hFidelity
  obtain ⟨d, _, hd⟩ :=
    Finset.exists_mem_eq_sup'
      (Finset.univ_nonempty_iff.mpr ⟨hReference⟩) (hDirectionFidelity rho)
  exact ⟨d, hd⟩

noncomputable def tMaximizingDirection
    (rho : DensityOperator QubitSpace) : TDirection :=
  Classical.choose (exists_tDirection_attaining_fidelity rho)

noncomputable def hMaximizingDirection
    (rho : DensityOperator QubitSpace) : HDirection :=
  Classical.choose (exists_hDirection_attaining_fidelity rho)

theorem tMaximizingDirection_attains
    (rho : DensityOperator QubitSpace) :
    tFidelity rho = tDirectionFidelity rho (tMaximizingDirection rho) :=
  Classical.choose_spec (exists_tDirection_attaining_fidelity rho)

theorem hMaximizingDirection_attains
    (rho : DensityOperator QubitSpace) :
    hFidelity rho = hDirectionFidelity rho (hMaximizingDirection rho) :=
  Classical.choose_spec (exists_hDirection_attaining_fidelity rho)

theorem projectionSquaredOverlap_conjDensity
    (U : UnitaryTransport QubitSpace QubitSpace)
    (P : Operator QubitSpace) (rho : DensityOperator QubitSpace) :
    projectionSquaredOverlap (U.conjOperator P) (U.conjDensity rho) =
      projectionSquaredOverlap P rho := by
  unfold projectionSquaredOverlap
  rw [UnitaryTransport.conjDensity_toOperator,
    ← UnitaryTransport.conjOperator_mul,
    UnitaryTransport.trace_conjOperator]

theorem projectionFidelity_conjDensity
    (U : UnitaryTransport QubitSpace QubitSpace)
    (P : Operator QubitSpace) (rho : DensityOperator QubitSpace) :
    projectionFidelity (U.conjOperator P) (U.conjDensity rho) =
      projectionFidelity P rho := by
  unfold projectionFidelity
  rw [projectionSquaredOverlap_conjDensity]

theorem tDirectionFidelity_hadamard
    (rho : DensityOperator QubitSpace) (d : TDirection) :
    tDirectionFidelity (hadamardTransport.conjDensity rho)
        (hadamardClifford • d) =
      tDirectionFidelity rho d := by
  simpa only [tDirectionFidelity, hadamard_conj_tProjector] using
    projectionFidelity_conjDensity hadamardTransport (tProjector d) rho

theorem tDirectionFidelity_phase
    (rho : DensityOperator QubitSpace) (d : TDirection) :
    tDirectionFidelity (phaseTransport.conjDensity rho)
        (phaseClifford • d) =
      tDirectionFidelity rho d := by
  simpa only [tDirectionFidelity, phase_conj_tProjector] using
    projectionFidelity_conjDensity phaseTransport (tProjector d) rho

theorem hDirectionFidelity_hadamard
    (rho : DensityOperator QubitSpace) (d : HDirection) :
    hDirectionFidelity (hadamardTransport.conjDensity rho)
        (hadamardClifford • d) =
      hDirectionFidelity rho d := by
  simpa only [hDirectionFidelity, hadamard_conj_hProjector] using
    projectionFidelity_conjDensity hadamardTransport (hProjector d) rho

theorem hDirectionFidelity_phase
    (rho : DensityOperator QubitSpace) (d : HDirection) :
    hDirectionFidelity (phaseTransport.conjDensity rho)
        (phaseClifford • d) =
      hDirectionFidelity rho d := by
  simpa only [hDirectionFidelity, phase_conj_hProjector] using
    projectionFidelity_conjDensity phaseTransport (hProjector d) rho

private theorem univ_sup'_comp_equiv
    {α : Type*} [Fintype α]
    (reference : α) (f : α → Real) (e : α ≃ α) :
    Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨reference⟩) (f ∘ e) =
      Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨reference⟩) f := by
  simpa only [Finset.map_univ_equiv, Equiv.coe_toEmbedding] using
    Finset.sup'_comp_eq_map
      (s := Finset.univ) (f := e.toEmbedding) f
      (show (Finset.univ : Finset α).Nonempty from
        (Finset.univ_nonempty_iff.mpr ⟨reference⟩))

theorem tFidelity_hadamard (rho : DensityOperator QubitSpace) :
    tFidelity (hadamardTransport.conjDensity rho) = tFidelity rho := by
  unfold tFidelity
  calc
    _ = Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨tReference⟩)
        (tDirectionFidelity (hadamardTransport.conjDensity rho) ∘
          MulAction.toPerm hadamardClifford) :=
      (univ_sup'_comp_equiv tReference
        (tDirectionFidelity (hadamardTransport.conjDensity rho))
        (MulAction.toPerm hadamardClifford)).symm
    _ = _ := by
      simp only [Function.comp_apply, MulAction.toPerm_apply,
        tDirectionFidelity_hadamard]

theorem tFidelity_phase (rho : DensityOperator QubitSpace) :
    tFidelity (phaseTransport.conjDensity rho) = tFidelity rho := by
  unfold tFidelity
  calc
    _ = Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨tReference⟩)
        (tDirectionFidelity (phaseTransport.conjDensity rho) ∘
          MulAction.toPerm phaseClifford) :=
      (univ_sup'_comp_equiv tReference
        (tDirectionFidelity (phaseTransport.conjDensity rho))
        (MulAction.toPerm phaseClifford)).symm
    _ = _ := by
      simp only [Function.comp_apply, MulAction.toPerm_apply,
        tDirectionFidelity_phase]

theorem hFidelity_hadamard (rho : DensityOperator QubitSpace) :
    hFidelity (hadamardTransport.conjDensity rho) = hFidelity rho := by
  unfold hFidelity
  calc
    _ = Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨hReference⟩)
        (hDirectionFidelity (hadamardTransport.conjDensity rho) ∘
          MulAction.toPerm hadamardClifford) :=
      (univ_sup'_comp_equiv hReference
        (hDirectionFidelity (hadamardTransport.conjDensity rho))
        (MulAction.toPerm hadamardClifford)).symm
    _ = _ := by
      simp only [Function.comp_apply, MulAction.toPerm_apply,
        hDirectionFidelity_hadamard]

theorem hFidelity_phase (rho : DensityOperator QubitSpace) :
    hFidelity (phaseTransport.conjDensity rho) = hFidelity rho := by
  unfold hFidelity
  calc
    _ = Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨hReference⟩)
        (hDirectionFidelity (phaseTransport.conjDensity rho) ∘
          MulAction.toPerm phaseClifford) :=
      (univ_sup'_comp_equiv hReference
        (hDirectionFidelity (phaseTransport.conjDensity rho))
        (MulAction.toPerm phaseClifford)).symm
    _ = _ := by
      simp only [Function.comp_apply, MulAction.toPerm_apply,
        hDirectionFidelity_phase]

end OneQubitMagic
end Distillation
end QEC
