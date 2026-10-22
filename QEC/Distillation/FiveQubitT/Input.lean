import QEC.Distillation.Universality.OneQubitMagic
import QEC.Distillation.Core.TransversalGate
import QEC.Semantics.Entropy.Convexity
import QEC.Semantics.Instruments.Core
/-!
# BK05 five-qubit T-route input contract

This internal module isolates the source-normalization and one-qubit input
semantics used before the BK05 five-qubit protocol. It deliberately stops
before any five-qubit code, acceptance recurrence, or threshold argument.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace BK05T

open Semantics Semantics.Qubit
open OneQubitMagic
open scoped BigOperators

private theorem densityOperator_ext
    {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl

/-- BK05's distinguished `T_0` direction. -/
abbrev tZeroDirection : TDirection := tReference

/-- The antipodal `T_1` direction used for the diagonal error component. -/
def tOneDirection : TDirection :=
  ⟨fun _ => .neg, by intro i; simp⟩

/-- The distinguished ideal `T_0` density. -/
noncomputable def tZero : DensityOperator QubitSpace :=
  tMagicStateOfDirection tZeroDirection

/-- The distinguished error `T_1` density. -/
noncomputable def tOne : DensityOperator QubitSpace :=
  tMagicStateOfDirection tOneDirection

/-- The two source error components, with `0 = T_0` and `1 = T_1`. -/
noncomputable def tInputComponent : Fin 2 → DensityOperator QubitSpace
  | 0 => tZero
  | 1 => tOne

/-- The raw BK05 diagonal-input weights. These are defined on the full real
parameter line; density formation below separately requires admissibility. -/
def tInputWeight (epsilon : Real) : Fin 2 → Real
  | 0 => 1 - epsilon
  | 1 => epsilon

/-- The raw, generally unnormalised source branch for one input error word.

Unlike a conditional density, this exists at zero weight. -/
noncomputable def tRawInputBranch (epsilon : Real) (word : Fin 2) :
    Operator QubitSpace :=
  (tInputWeight epsilon word : Complex) • (tInputComponent word).toOperator

/-- A conditional error-word density is available only with a strictly
positive branch-weight witness. This guard intentionally does not govern
later aggregate accept/reject branches. -/
noncomputable def tInputConditional (epsilon : Real) (word : Fin 2)
    (_hpositive : 0 < tInputWeight epsilon word) : DensityOperator QubitSpace :=
  tInputComponent word

theorem tRawInputBranch_eq_weightedConditional (epsilon : Real) (word : Fin 2)
    (hpositive : 0 < tInputWeight epsilon word) :
    tRawInputBranch epsilon word =
      (tInputWeight epsilon word : Complex) •
        (tInputConditional epsilon word hpositive).toOperator :=
  rfl

/-- The `T_1` raw branch remains meaningful and is zero at `epsilon = 0`. -/
theorem tRawInputBranch_tOne_zero : tRawInputBranch 0 1 = 0 := by
  simp [tRawInputBranch, tInputWeight]

/-- No individual `T_1` error-word conditional can be manufactured at the
zero-error endpoint. -/
theorem no_tOneConditional_at_zero : ¬ 0 < tInputWeight 0 1 := by
  norm_num [tInputWeight]

theorem tInputWeight_nonneg (epsilon : Real) (hzero : 0 ≤ epsilon)
    (hone : epsilon ≤ 1) (word : Fin 2) : 0 ≤ tInputWeight epsilon word := by
  fin_cases word <;> simp [tInputWeight, hzero, sub_nonneg.mpr hone]

theorem tInputWeight_sum (epsilon : Real) :
    ∑ word : Fin 2, tInputWeight epsilon word = 1 := by
  simp [tInputWeight]

/-- BK05's diagonal input density `(1-epsilon) T_0 + epsilon T_1`.
The separate hypotheses keep the raw branch semantics valid at every endpoint. -/
noncomputable def tDiagonalInput (epsilon : Real) (hzero : 0 ≤ epsilon)
    (hone : epsilon ≤ 1) : DensityOperator QubitSpace :=
  DensityOperator.convexCombination Finset.univ (tInputWeight epsilon)
    tInputComponent
    (by
      intro word _hword
      exact tInputWeight_nonneg epsilon hzero hone word)
    (by simpa using tInputWeight_sum epsilon)

/-- Its density operator is the sum of the two raw error-word branches. -/
theorem tDiagonalInput_toOperator (epsilon : Real) (hzero : 0 ≤ epsilon)
    (hone : epsilon ≤ 1) :
    (tDiagonalInput epsilon hzero hone).toOperator =
      ∑ word : Fin 2, tRawInputBranch epsilon word := by
  rw [tDiagonalInput, DensityOperator.convexCombination_toOperator]
  simp only [DensityOperator.convexCombinationOperator, tRawInputBranch]

/-- The diagonal density at `epsilon = 0` is exactly `T_0`; the vanishing
`T_1` raw branch is not replaced by an invented conditional state. -/
theorem tDiagonalInput_zero :
    tDiagonalInput 0 (by norm_num) (by norm_num) = tZero := by
  apply densityOperator_ext
  rw [tDiagonalInput_toOperator]
  simp [tRawInputBranch, tInputWeight, tInputComponent]

private theorem tZero_bloch : tBlochOfDirection tZeroDirection = tBloch := by
  funext i
  fin_cases i <;> simp only [tZeroDirection, tReference, tBlochOfDirection, tBloch,
    signedCoordinateValue] <;> norm_num

private theorem tOne_bloch :
    tBlochOfDirection tOneDirection = fun i => -tBloch i := by
  funext i
  fin_cases i <;> simp only [tOneDirection, tBlochOfDirection, tBloch,
    signedCoordinateValue] <;> norm_num

private theorem blochOperator_neg (r : PauliAxis → Real) :
    blochOperator (fun i => -r i) = -blochOperator r := by
  unfold blochOperator
  module

/-- The two source components are orthogonal rank-one density operators. -/
theorem tZero_tOne_orthogonal : tZero.toOperator * tOne.toOperator = 0 := by
  change blochProjector (tBlochOfDirection tZeroDirection) *
    blochProjector (tBlochOfDirection tOneDirection) = 0
  rw [tZero_bloch, tOne_bloch]
  unfold blochProjector
  rw [blochOperator_neg]
  have hsquare : blochOperator tBloch * blochOperator tBloch = 1 := by
    rw [blochOperator_square, tBloch_normalized]
    norm_num
  rw [smul_mul_smul_comm]
  have hsum : (1 + blochOperator tBloch) * (1 + -blochOperator tBloch) = 0 := by
    simp only [add_mul, mul_add, one_mul, mul_one, mul_neg, hsquare]
    module
  rw [hsum, smul_zero]

/-- Orthogonality also holds in the opposite operator order. -/
theorem tOne_tZero_orthogonal : tOne.toOperator * tZero.toOperator = 0 := by
  change blochProjector (tBlochOfDirection tOneDirection) *
    blochProjector (tBlochOfDirection tZeroDirection) = 0
  rw [tZero_bloch, tOne_bloch]
  unfold blochProjector
  rw [blochOperator_neg]
  have hsquare : blochOperator tBloch * blochOperator tBloch = 1 := by
    rw [blochOperator_square, tBloch_normalized]
    norm_num
  rw [smul_mul_smul_comm]
  have hsum : (1 + -blochOperator tBloch) * (1 + blochOperator tBloch) = 0 := by
    simp only [add_mul, mul_add, one_mul, mul_one, neg_mul, hsquare]
    module
  rw [hsum, smul_zero]

/-- The antipodal source projectors resolve the one-qubit identity. -/
theorem tZero_tOne_projector_sum :
    tProjector tZeroDirection + tProjector tOneDirection = 1 := by
  simp [tProjector, tZeroDirection, tOneDirection, tReference,
    tBlochOfDirection, signedCoordinateValue, blochProjector, blochOperator]
  module

/-- The ideal T0 density is its rank-one projector. -/
theorem tZero_idempotent : tZero.toOperator * tZero.toOperator = tZero.toOperator := by
  change tProjector tZeroDirection * tProjector tZeroDirection =
    tProjector tZeroDirection
  exact (tProjector_isSymmetricProjection tZeroDirection).1

/-- The BK05 squared overlap with the distinguished `T_0` direction. -/
def tInputSquaredOverlap (rho : DensityOperator QubitSpace) : Real :=
  projectionSquaredOverlap (tProjector tZeroDirection) rho

/-- The associated square-root fidelity, retained rather than assuming a
separate error-rate law. -/
def tInputFidelity (rho : DensityOperator QubitSpace) : Real :=
  tDirectionFidelity rho tZeroDirection

/-- The diagonal mixture uses exactly epsilon as its squared-overlap error. -/
theorem tInputSquaredOverlap_diagonalInput
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    tInputSquaredOverlap (tDiagonalInput epsilon hzero hone) = 1 - epsilon := by
  unfold tInputSquaredOverlap projectionSquaredOverlap
  change (LinearMap.trace Complex QubitSpace
    (tZero.toOperator * (tDiagonalInput epsilon hzero hone).toOperator)).re = 1 - epsilon
  rw [tDiagonalInput_toOperator, Fin.sum_univ_two]
  simp only [tRawInputBranch, tInputWeight, tInputComponent]
  rw [mul_add, mul_smul_comm, mul_smul_comm, tZero_idempotent,
    tZero_tOne_orthogonal]
  simp [map_smul, tZero.trace_one]

/-- The input error is exactly one minus the actual squared overlap. -/
def tInputError (rho : DensityOperator QubitSpace) : Real :=
  1 - tInputSquaredOverlap rho

theorem tInputSquaredOverlap_eq_tInputFidelity_sq
    (rho : DensityOperator QubitSpace) :
    tInputSquaredOverlap rho = tInputFidelity rho ^ 2 := by
  unfold tInputSquaredOverlap tInputFidelity tDirectionFidelity projectionFidelity
  rw [Real.sq_sqrt]
  exact projectionSquaredOverlap_nonneg (tProjector tZeroDirection) rho
    (tProjector_isSymmetricProjection tZeroDirection)

/-- Squared overlap with any T direction is the square of its fidelity. -/
theorem tDirectionSquaredOverlap_eq_tDirectionFidelity_sq
    (rho : DensityOperator QubitSpace) (d : TDirection) :
    projectionSquaredOverlap (tProjector d) rho =
      tDirectionFidelity rho d ^ 2 := by
  unfold tDirectionFidelity projectionFidelity
  rw [Real.sq_sqrt]
  exact projectionSquaredOverlap_nonneg (tProjector d) rho
    (tProjector_isSymmetricProjection d)

/-- Squared overlaps with the antipodal T0/T1 pair sum to one. -/
theorem tDirectionSquaredOverlap_zero_add_one
    (rho : DensityOperator QubitSpace) :
    projectionSquaredOverlap (tProjector tZeroDirection) rho +
      projectionSquaredOverlap (tProjector tOneDirection) rho = 1 := by
  unfold projectionSquaredOverlap
  rw [← Complex.add_re, ← map_add, ← add_mul,
    tZero_tOne_projector_sum, one_mul, rho.trace_one]
  norm_num

/-- Some antipodal T direction has squared fidelity at least one half. -/
theorem tFidelity_sq_ge_half (rho : DensityOperator QubitSpace) :
    (1 / 2 : Real) ≤ tFidelity rho ^ 2 := by
  have hsum := tDirectionSquaredOverlap_zero_add_one rho
  rw [tDirectionSquaredOverlap_eq_tDirectionFidelity_sq,
    tDirectionSquaredOverlap_eq_tDirectionFidelity_sq] at hsum
  have hzero_nonneg := (tDirectionFidelity_mem_Icc rho tZeroDirection).1
  have hone_nonneg := (tDirectionFidelity_mem_Icc rho tOneDirection).1
  have hmax_nonneg := (tFidelity_mem_Icc rho).1
  have hzero_le : tDirectionFidelity rho tZeroDirection ≤ tFidelity rho := by
    unfold tFidelity
    exact Finset.le_sup' (tDirectionFidelity rho)
      (Finset.mem_univ tZeroDirection)
  have hone_le : tDirectionFidelity rho tOneDirection ≤ tFidelity rho := by
    unfold tFidelity
    exact Finset.le_sup' (tDirectionFidelity rho)
      (Finset.mem_univ tOneDirection)
  have hzero_sq : tDirectionFidelity rho tZeroDirection ^ 2 ≤
      tFidelity rho ^ 2 := by nlinarith
  have hone_sq : tDirectionFidelity rho tOneDirection ^ 2 ≤
      tFidelity rho ^ 2 := by nlinarith
  nlinarith

/-- The source error parameter is tied to squared, not merely square-root,
fidelity. -/
theorem tInputError_eq_one_sub_tInputFidelity_sq
    (rho : DensityOperator QubitSpace) :
    tInputError rho = 1 - tInputFidelity rho ^ 2 := by
  rw [tInputError, tInputSquaredOverlap_eq_tInputFidelity_sq]

/-- The Bloch vector of the diagonal `(1-epsilon) T0 + epsilon T1` mixture. -/
def tDiagonalBloch (epsilon : Real) : PauliAxis → Real :=
  fun _ => (1 - 2 * epsilon) * (Real.sqrt 3)⁻¹

/-- The diagonal density has the advertised one-axis Bloch representation. -/
theorem tDiagonalInput_toOperator_eq_blochProjector
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (tDiagonalInput epsilon hzero hone).toOperator =
      blochProjector (tDiagonalBloch epsilon) := by
  rw [tDiagonalInput_toOperator, Fin.sum_univ_two]
  simp only [tRawInputBranch, tInputWeight, tInputComponent]
  simp only [tZero, tOne, tMagicStateOfDirection, blochDensity]
  rw [tZero_bloch, tOne_bloch]
  unfold blochProjector
  rw [blochOperator_neg]
  unfold blochOperator tDiagonalBloch tBloch
  module

/-- The diagonal error parameter is exactly epsilon. -/
theorem tInputError_diagonalInput
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    tInputError (tDiagonalInput epsilon hzero hone) = epsilon := by
  rw [tInputError, tInputSquaredOverlap_diagonalInput epsilon hzero hone]
  ring

/-- The finite physical Clifford cycle used by BK05's `T` twirl: first `H`,
then phase `S`; it cycles the Pauli axes as `X -> Z -> Y -> X`. -/
noncomputable def tCycleTransport : UnitaryTransport QubitSpace QubitSpace :=
  hadamardTransport.trans phaseTransport

/-- The three unitary witnesses in the source twirl. -/
noncomputable def tTwirlUnitary : Fin 3 → UnitaryTransport QubitSpace QubitSpace
  | 0 => UnitaryTransport.identity QubitSpace
  | 1 => tCycleTransport
  | 2 => tCycleTransport.trans tCycleTransport

/-- The uniform probability weight for the three BK05 Clifford twirl branches. -/
def tTwirlWeight (_ : Fin 3) : Real := 1 / 3

theorem tTwirlWeight_nonneg (i : Fin 3) : 0 ≤ tTwirlWeight i := by
  norm_num [tTwirlWeight]

theorem tTwirlWeight_sum : ∑ i : Fin 3, tTwirlWeight i = 1 := by
  norm_num [tTwirlWeight]

private theorem tTwirlUnitary_adjoint_comp (i : Fin 3) :
    (LinearMap.adjoint (tTwirlUnitary i).toLinearEquiv.toLinearMap).comp
      (tTwirlUnitary i).toLinearEquiv.toLinearMap = 1 := by
  rw [(tTwirlUnitary i).adjoint_toLinearMap]
  apply LinearMap.ext
  intro x
  change (tTwirlUnitary i).toLinearEquiv.symm ((tTwirlUnitary i).toLinearEquiv x) = x
  exact (tTwirlUnitary i).toLinearEquiv.symm_apply_apply x

/-- The normalized Kraus amplitude for the three uniform unitary branches. -/
noncomputable def tTwirlAmplitude : Complex := (Real.sqrt 3 : Complex)⁻¹

private theorem tTwirlAmplitude_sq :
    star tTwirlAmplitude * tTwirlAmplitude = (1 / 3 : Complex) := by
  unfold tTwirlAmplitude
  have hneReal : Real.sqrt 3 ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hne : (Real.sqrt 3 : Complex) ≠ 0 := by
    exact_mod_cast hneReal
  have hsqReal : Real.sqrt 3 * Real.sqrt 3 = 3 := by
    exact Real.mul_self_sqrt (by norm_num)
  have hsq : (Real.sqrt 3 : Complex) * (Real.sqrt 3 : Complex) = 3 := by
    exact_mod_cast hsqReal
  rw [RCLike.star_def, map_inv₀ (starRingEnd ℂ), Complex.conj_ofReal]
  field_simp [hne]
  rw [pow_two, hsq]

noncomputable def tTwirlKrausUnscaled :
    FiniteKrausFamily (Fin 3) QubitSpace QubitSpace where
  operator i := (tTwirlUnitary i).toLinearEquiv.toLinearMap

noncomputable def tTwirlKraus : FiniteKrausFamily (Fin 3) QubitSpace QubitSpace :=
  tTwirlKrausUnscaled.scale (fun _ => tTwirlAmplitude)

private theorem tTwirlKraus_complete : tTwirlKraus.Complete := by
  apply FiniteKrausFamily.scale_complete_of_adjoint_square_sum
  calc
    (∑ i : Fin 3,
        (star tTwirlAmplitude * tTwirlAmplitude) •
          ((LinearMap.adjoint (tTwirlKrausUnscaled.operator i)).comp
            (tTwirlKrausUnscaled.operator i))) =
        ∑ _i : Fin 3, (1 / 3 : Complex) • (1 : Operator QubitSpace) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [tTwirlAmplitude_sq]
          exact congrArg (fun T : Operator QubitSpace => (1 / 3 : Complex) • T)
            (tTwirlUnitary_adjoint_comp i)
    _ = 1 := by
      rw [Fin.sum_univ_three]
      module

/-- The BK05 T twirl as an actual finite-Kraus CPTP quantum channel. -/
noncomputable def tTwirlChannel : QuantumChannel QubitSpace QubitSpace :=
  tTwirlKraus.toQuantumChannel tTwirlKraus_complete

/-- The actual finite random-unitary T twirl on one-qubit densities.  Its three
branches are precisely the concrete Clifford witnesses in `tTwirlUnitary`. -/
noncomputable def tTwirl (rho : DensityOperator QubitSpace) :
    DensityOperator QubitSpace :=
  DensityOperator.convexCombination Finset.univ tTwirlWeight
    (fun i => (tTwirlUnitary i).conjDensity rho)
    (by
      intro i _hi
      exact tTwirlWeight_nonneg i)
    (by simpa using tTwirlWeight_sum)

private theorem tTwirlKraus_branch (i : Fin 3) (A : Operator QubitSpace) :
    (tTwirlKraus.operator i).comp
        (A.comp (LinearMap.adjoint (tTwirlKraus.operator i))) =
      (1 / 3 : Complex) • (tTwirlUnitary i).conjOperator A := by
  unfold tTwirlKraus tTwirlKrausUnscaled
  rw [FiniteKrausFamily.scale_operator]
  have hAdj : LinearMap.adjoint
      (tTwirlAmplitude • (tTwirlUnitary i).toLinearEquiv.toLinearMap) =
      star tTwirlAmplitude •
        LinearMap.adjoint (tTwirlUnitary i).toLinearEquiv.toLinearMap := by
    exact map_smulₛₗ
      (LinearMap.adjoint : (QubitSpace →ₗ[Complex] QubitSpace) ≃ₗ⋆[Complex]
        (QubitSpace →ₗ[Complex] QubitSpace))
      tTwirlAmplitude (tTwirlUnitary i).toLinearEquiv.toLinearMap
  rw [hAdj]
  have hamplitude : (starRingEnd Complex) tTwirlAmplitude * tTwirlAmplitude =
      (3 : Complex)⁻¹ := by
    simpa [one_div] using tTwirlAmplitude_sq
  ext x
  simp [LinearMap.comp_apply, UnitaryTransport.conjOperator,
    (tTwirlUnitary i).adjoint_toLinearMap, mul_comm, mul_assoc]
  rw [← hamplitude]
  ring

/-- The finite-Kraus channel and the explicit random-unitary density twirl
coincide on every one-qubit density. -/
theorem tTwirlChannel_mapDensity (rho : DensityOperator QubitSpace) :
    tTwirlChannel.mapDensity rho = tTwirl rho := by
  apply densityOperator_ext
  rw [QuantumChannel.mapDensity_toOperator]
  change (tTwirlKraus.toQuantumChannel tTwirlKraus_complete) rho.toOperator =
    (tTwirl rho).toOperator
  rw [FiniteKrausFamily.toQuantumChannel_apply_sum]
  simp_rw [tTwirlKraus_branch]
  rw [tTwirl, DensityOperator.convexCombination_toOperator]
  simp [DensityOperator.convexCombinationOperator, tTwirlWeight]

private theorem trans_conjDensity
    (U V : UnitaryTransport QubitSpace QubitSpace)
    (rho : DensityOperator QubitSpace) :
    (U.trans V).conjDensity rho = V.conjDensity (U.conjDensity rho) := by
  apply densityOperator_ext
  rfl

private theorem trans_conjOperator
    (U V : UnitaryTransport QubitSpace QubitSpace) (A : Operator QubitSpace) :
    (U.trans V).conjOperator A = V.conjOperator (U.conjOperator A) := by
  ext x
  rfl

private theorem tConjOperator_add
    (U : UnitaryTransport QubitSpace QubitSpace)
    (A B : Operator QubitSpace) :
    U.conjOperator (A + B) = U.conjOperator A + U.conjOperator B := by
  ext psi
  simp [UnitaryTransport.conjOperator]

private theorem tConjOperator_smul
    (U : UnitaryTransport QubitSpace QubitSpace)
    (c : Complex) (A : Operator QubitSpace) :
    U.conjOperator (c • A) = c • U.conjOperator A := by
  ext psi
  simp [UnitaryTransport.conjOperator]

private def tHadamardBlochAction (r : PauliAxis → Real) : PauliAxis → Real
  | .x => r .z
  | .y => -r .y
  | .z => r .x

private def tPhaseBlochAction (r : PauliAxis → Real) : PauliAxis → Real
  | .x => -r .y
  | .y => r .x
  | .z => r .z

/-- The cyclic permutation of Bloch coordinates induced by the physical H-then-S transport. -/
def tCycleBlochAction (r : PauliAxis → Real) : PauliAxis → Real
  | .x => r .y
  | .y => r .z
  | .z => r .x

/-- The diagonal Bloch vector left after the three-branch BK05 T twirl. -/
def tTwirlBloch (r : PauliAxis → Real) : PauliAxis → Real :=
  fun _ => (r .x + r .y + r .z) / 3

private theorem tHadamard_conj_blochProjector (r : PauliAxis → Real) :
    hadamardTransport.conjOperator (blochProjector r) =
      blochProjector (tHadamardBlochAction r) := by
  simp only [blochProjector, blochOperator, tConjOperator_smul, tConjOperator_add,
    hadamard_conj_one, hadamard_conj_pauliX, hadamard_conj_pauliY,
    hadamard_conj_pauliZ, tHadamardBlochAction]
  module

private theorem tPhase_conj_blochProjector (r : PauliAxis → Real) :
    phaseTransport.conjOperator (blochProjector r) =
      blochProjector (tPhaseBlochAction r) := by
  simp only [blochProjector, blochOperator, tConjOperator_smul, tConjOperator_add,
    phase_conj_one, phase_conj_pauliX, phase_conj_pauliY, phase_conj_pauliZ,
    tPhaseBlochAction]
  module

private theorem tCycle_conj_blochProjector (r : PauliAxis → Real) :
    tCycleTransport.conjOperator (blochProjector r) =
      blochProjector (tCycleBlochAction r) := by
  rw [tCycleTransport, trans_conjOperator, tHadamard_conj_blochProjector,
    tPhase_conj_blochProjector]
  congr 1
  funext i
  fin_cases i <;> simp [tPhaseBlochAction, tHadamardBlochAction,
    tCycleBlochAction]

private theorem tTwirlUnitary_conj_blochProjector
    (i : Fin 3) (r : PauliAxis → Real) :
    (tTwirlUnitary i).conjOperator (blochProjector r) =
      blochProjector ((tCycleBlochAction^[i.1]) r) := by
  fin_cases i
  · rfl
  · exact tCycle_conj_blochProjector r
  · change (tCycleTransport.trans tCycleTransport).conjOperator
      (blochProjector r) = blochProjector
        (tCycleBlochAction (tCycleBlochAction r))
    rw [trans_conjOperator, tCycle_conj_blochProjector,
      tCycle_conj_blochProjector]

/-- For every density given by a Bloch-projector representation, the actual
three-branch twirl exactly removes the two transverse Bloch components. -/
theorem tTwirl_toOperator_eq_blochProjector_average
    (rho : DensityOperator QubitSpace) (r : PauliAxis → Real)
    (hrho : rho.toOperator = blochProjector r) :
    (tTwirl rho).toOperator = blochProjector (tTwirlBloch r) := by
  rw [tTwirl, DensityOperator.convexCombination_toOperator]
  simp only [DensityOperator.convexCombinationOperator,
    UnitaryTransport.conjDensity_toOperator]
  rw [hrho]
  simp_rw [tTwirlUnitary_conj_blochProjector]
  rw [Fin.sum_univ_three]
  simp [tTwirlWeight, blochProjector, blochOperator, tCycleBlochAction,
    tTwirlBloch]
  module

/-- The distinguished T0 overlap is the affine sum of the input Bloch
coordinates. -/
theorem tInputSquaredOverlap_eq_bloch_sum
    (rho : DensityOperator QubitSpace) (r : PauliAxis → Real)
    (hrho : rho.toOperator = blochProjector r) :
    tInputSquaredOverlap rho =
      (1 + (r .x + r .y + r .z) / Real.sqrt 3) / 2 := by
  unfold tInputSquaredOverlap projectionSquaredOverlap
  rw [hrho]
  have hprojector : tProjector tZeroDirection =
      (2 : Complex)⁻¹ • (1 + (Real.sqrt 3 : Complex)⁻¹ •
        (pauliX + pauliY + pauliZ)) := by
    simp [tProjector, tZeroDirection, tReference, tBlochOfDirection,
      signedCoordinateValue, blochProjector, blochOperator]
  have htrace : LinearMap.trace Complex QubitSpace (blochProjector r) = 1 := by
    simp [blochProjector, blochOperator, pauliX_trace, pauliY_trace,
      pauliZ_trace]
  have htx : LinearMap.trace Complex QubitSpace (pauliX * blochProjector r) = r .x := by
    simpa [pauliOperator] using trace_pauli_mul_blochProjector r .x
  have hty : LinearMap.trace Complex QubitSpace (pauliY * blochProjector r) = r .y := by
    simpa [pauliOperator] using trace_pauli_mul_blochProjector r .y
  have htz : LinearMap.trace Complex QubitSpace (pauliZ * blochProjector r) = r .z := by
    simpa [pauliOperator] using trace_pauli_mul_blochProjector r .z
  rw [hprojector]
  simp only [smul_mul_assoc, add_mul, one_mul, map_smul, map_add, htrace]
  rw [htx, hty, htz]
  have hsqrt : Real.sqrt (3 : Real) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsqrtSq : Real.sqrt (3 : Real) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  norm_num
  field_simp [hsqrt]
  ring_nf
  rw [hsqrtSq]
  ring

/-- The physical twirl's averaged Bloch vector is exactly the diagonal
T0/T1 vector at the density's measured input error. -/
theorem tTwirlBloch_eq_tDiagonalBloch_of_inputError
    (rho : DensityOperator QubitSpace) (r : PauliAxis → Real)
    (hrho : rho.toOperator = blochProjector r) :
    tTwirlBloch r = tDiagonalBloch (tInputError rho) := by
  have hoverlap := tInputSquaredOverlap_eq_bloch_sum rho r hrho
  funext i
  simp only [tTwirlBloch, tDiagonalBloch, tInputError]
  rw [hoverlap]
  have hsqrt : Real.sqrt (3 : Real) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsqrtSq : Real.sqrt (3 : Real) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  field_simp [hsqrt]
  ring_nf
  rw [hsqrtSq]

/-- The generic Bloch twirl equality is an equality to the concrete BK05
diagonal T0/T1 mixture whenever their displayed Bloch vectors agree. -/
theorem tTwirl_eq_diagonalInput_of_bloch
    (rho : DensityOperator QubitSpace) (r : PauliAxis → Real)
    (hrho : rho.toOperator = blochProjector r)
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (hdiagonal : tTwirlBloch r = tDiagonalBloch epsilon) :
    tTwirl rho = tDiagonalInput epsilon hzero hone := by
  apply densityOperator_ext
  rw [tTwirl_toOperator_eq_blochProjector_average rho r hrho,
    tDiagonalInput_toOperator_eq_blochProjector]
  rw [hdiagonal]

/-- The same diagonalization statement for the finite-Kraus CPTP channel. -/
theorem tTwirlChannel_eq_diagonalInput_of_bloch
    (rho : DensityOperator QubitSpace) (r : PauliAxis → Real)
    (hrho : rho.toOperator = blochProjector r)
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (hdiagonal : tTwirlBloch r = tDiagonalBloch epsilon) :
    tTwirlChannel.mapDensity rho = tDiagonalInput epsilon hzero hone := by
  rw [tTwirlChannel_mapDensity,
    tTwirl_eq_diagonalInput_of_bloch rho r hrho epsilon hzero hone hdiagonal]

/-- Every one-qubit density is diagonalized by the physical twirl at its
actual measured input error; no caller-supplied diagonalization premise is
needed. -/
theorem tTwirl_eq_diagonalInput_of_inputError
    (rho : DensityOperator QubitSpace)
    (hzero : 0 ≤ tInputError rho) (hone : tInputError rho ≤ 1) :
    tTwirl rho = tDiagonalInput (tInputError rho) hzero hone := by
  exact tTwirl_eq_diagonalInput_of_bloch rho (densityBloch rho)
    (density_toOperator_eq_blochProjector rho) (tInputError rho) hzero hone
    (tTwirlBloch_eq_tDiagonalBloch_of_inputError rho (densityBloch rho)
      (density_toOperator_eq_blochProjector rho))

/-- The same assumption-free diagonalization bridge for the finite-Kraus
CPTP channel. -/
theorem tTwirlChannel_eq_diagonalInput_of_inputError
    (rho : DensityOperator QubitSpace)
    (hzero : 0 ≤ tInputError rho) (hone : tInputError rho ≤ 1) :
    tTwirlChannel.mapDensity rho =
      tDiagonalInput (tInputError rho) hzero hone := by
  rw [tTwirlChannel_mapDensity,
    tTwirl_eq_diagonalInput_of_inputError rho hzero hone]

private theorem tCycle_target_zero :
    phaseClifford • (hadamardClifford • tZeroDirection) = tZeroDirection := by
  native_decide

private theorem tCycle_target_one :
    phaseClifford • (hadamardClifford • tOneDirection) = tOneDirection := by
  native_decide

private theorem tCycle_conj_tZero : tCycleTransport.conjDensity tZero = tZero := by
  calc
    tCycleTransport.conjDensity tZero =
        phaseTransport.conjDensity (hadamardTransport.conjDensity tZero) :=
      trans_conjDensity hadamardTransport phaseTransport tZero
    _ = phaseTransport.conjDensity
        (tMagicStateOfDirection (hadamardClifford • tZeroDirection)) := by
          change phaseTransport.conjDensity
            (hadamardTransport.conjDensity
              (tMagicStateOfDirection tZeroDirection)) = _
          rw [hadamard_conj_tMagicState]
    _ = tMagicStateOfDirection
        (phaseClifford • (hadamardClifford • tZeroDirection)) := by
          rw [phase_conj_tMagicState]
    _ = tZero := by
          unfold tZero
          rw [tCycle_target_zero]

private theorem tCycle_conj_tOne : tCycleTransport.conjDensity tOne = tOne := by
  calc
    tCycleTransport.conjDensity tOne =
        phaseTransport.conjDensity (hadamardTransport.conjDensity tOne) :=
      trans_conjDensity hadamardTransport phaseTransport tOne
    _ = phaseTransport.conjDensity
        (tMagicStateOfDirection (hadamardClifford • tOneDirection)) := by
          change phaseTransport.conjDensity
            (hadamardTransport.conjDensity
              (tMagicStateOfDirection tOneDirection)) = _
          rw [hadamard_conj_tMagicState]
    _ = tMagicStateOfDirection
        (phaseClifford • (hadamardClifford • tOneDirection)) := by
          rw [phase_conj_tMagicState]
    _ = tOne := by
          unfold tOne
          rw [tCycle_target_one]

private theorem tTwirlUnitary_conj_tZero (i : Fin 3) :
    (tTwirlUnitary i).conjDensity tZero = tZero := by
  fin_cases i
  · rfl
  · exact tCycle_conj_tZero
  · change (tCycleTransport.trans tCycleTransport).conjDensity tZero = tZero
    rw [trans_conjDensity, tCycle_conj_tZero, tCycle_conj_tZero]

private theorem tTwirlUnitary_conj_tOne (i : Fin 3) :
    (tTwirlUnitary i).conjDensity tOne = tOne := by
  fin_cases i
  · rfl
  · exact tCycle_conj_tOne
  · change (tCycleTransport.trans tCycleTransport).conjDensity tOne = tOne
    rw [trans_conjDensity, tCycle_conj_tOne, tCycle_conj_tOne]

/-- The physical twirl fixes each endpoint component of the diagonal BK05 input. -/
theorem tTwirl_tZero : tTwirl tZero = tZero := by
  apply densityOperator_ext
  rw [tTwirl, DensityOperator.convexCombination_toOperator]
  simp_rw [tTwirlUnitary_conj_tZero]
  simp only [DensityOperator.convexCombinationOperator]
  rw [Fin.sum_univ_three]
  norm_num [tTwirlWeight]
  module

theorem tTwirl_tOne : tTwirl tOne = tOne := by
  apply densityOperator_ext
  rw [tTwirl, DensityOperator.convexCombination_toOperator]
  simp_rw [tTwirlUnitary_conj_tOne]
  simp only [DensityOperator.convexCombinationOperator]
  rw [Fin.sum_univ_three]
  norm_num [tTwirlWeight]
  module

private theorem tTwirlUnitary_conj_tInputComponent
    (i : Fin 3) (word : Fin 2) :
    (tTwirlUnitary i).conjDensity (tInputComponent word) = tInputComponent word := by
  fin_cases word
  · exact tTwirlUnitary_conj_tZero i
  · exact tTwirlUnitary_conj_tOne i

private theorem tTwirlUnitary_conj_tRawInputBranch
    (epsilon : Real) (i : Fin 3) (word : Fin 2) :
    (tTwirlUnitary i).conjOperator (tRawInputBranch epsilon word) =
      tRawInputBranch epsilon word := by
  unfold tRawInputBranch
  change (tTwirlUnitary i).conjOperatorLinearMap
    ((tInputWeight epsilon word : Complex) • (tInputComponent word).toOperator) = _
  rw [map_smul]
  exact congrArg (fun sigma : DensityOperator QubitSpace =>
    (tInputWeight epsilon word : Complex) • sigma.toOperator)
    (tTwirlUnitary_conj_tInputComponent i word)

private theorem tTwirlUnitary_conj_tDiagonalInput
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) (i : Fin 3) :
    (tTwirlUnitary i).conjDensity (tDiagonalInput epsilon hzero hone) =
      tDiagonalInput epsilon hzero hone := by
  apply densityOperator_ext
  rw [UnitaryTransport.conjDensity_toOperator, tDiagonalInput_toOperator]
  change (tTwirlUnitary i).conjOperatorLinearMap
    (∑ word : Fin 2, tRawInputBranch epsilon word) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro word _hword
  exact tTwirlUnitary_conj_tRawInputBranch epsilon i word

/-- The actual CPTP/unitary twirl fixes the BK05 diagonal T0/T1 mixture. -/
theorem tTwirl_diagonalInput
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    tTwirl (tDiagonalInput epsilon hzero hone) = tDiagonalInput epsilon hzero hone := by
  apply densityOperator_ext
  rw [tTwirl, DensityOperator.convexCombination_toOperator]
  simp_rw [tTwirlUnitary_conj_tDiagonalInput epsilon hzero hone]
  simp only [DensityOperator.convexCombinationOperator]
  rw [Fin.sum_univ_three]
  norm_num [tTwirlWeight]
  module

private def tHStep (d : TDirection) : TDirection :=
  hadamardClifford • d

private def tSStep (d : TDirection) : TDirection :=
  phaseClifford • d

/-- A finite H/S-word library. Each word is a concrete one-qubit Clifford
transport and its matching signed-axis action. -/
noncomputable def tCanonicalizerCandidate : Fin 8 →
    UnitaryTransport QubitSpace QubitSpace
  | 0 => ((phaseTransport.trans hadamardTransport).trans phaseTransport).trans
      (phaseTransport.trans hadamardTransport)
  | 1 => phaseTransport.trans hadamardTransport
  | 2 => ((((hadamardTransport.trans phaseTransport).trans hadamardTransport).trans
      phaseTransport).trans phaseTransport).trans hadamardTransport
  | 3 => (phaseTransport.trans phaseTransport).trans hadamardTransport
  | 4 => ((hadamardTransport.trans phaseTransport).trans phaseTransport).trans
      hadamardTransport
  | 5 => hadamardTransport
  | 6 => (hadamardTransport.trans phaseTransport).trans hadamardTransport
  | 7 => UnitaryTransport.identity QubitSpace

private def tCanonicalizerTarget : Fin 8 → TDirection → TDirection
  | 0 => fun d => tHStep (tSStep (tSStep (tHStep (tSStep d))))
  | 1 => fun d => tHStep (tSStep d)
  | 2 => fun d => tHStep (tSStep (tSStep (tHStep (tSStep (tHStep d)))))
  | 3 => fun d => tHStep (tSStep (tSStep d))
  | 4 => fun d => tHStep (tSStep (tSStep (tHStep d)))
  | 5 => fun d => tHStep d
  | 6 => fun d => tHStep (tSStep (tHStep d))
  | 7 => fun d => d

private theorem tCanonicalizerCandidate_conj (i : Fin 8) (d : TDirection) :
    (tCanonicalizerCandidate i).conjDensity (tMagicStateOfDirection d) =
      tMagicStateOfDirection (tCanonicalizerTarget i d) := by
  fin_cases i <;>
    simp [tCanonicalizerCandidate, tCanonicalizerTarget, tHStep, tSStep,
      trans_conjDensity, hadamard_conj_tMagicState, phase_conj_tMagicState,
      UnitaryTransport.identity]
  all_goals rfl

private theorem tCanonicalizerCandidate_complete (d : TDirection) :
    ∃ i : Fin 8, tCanonicalizerTarget i d = tZeroDirection := by
  revert d
  native_decide

/-- A chosen member of the finite concrete H/S library that sends a T direction
to BK05s distinguished positive direction. -/
noncomputable def tCanonicalizerIndex (d : TDirection) : Fin 8 :=
  Classical.choose (tCanonicalizerCandidate_complete d)

/-- The actual finite-Clifford normalization witness for a T direction. -/
noncomputable def tCanonicalizer (d : TDirection) :
    UnitaryTransport QubitSpace QubitSpace :=
  tCanonicalizerCandidate (tCanonicalizerIndex d)

theorem tCanonicalizer_conj_tMagicState (d : TDirection) :
    (tCanonicalizer d).conjDensity (tMagicStateOfDirection d) = tZero := by
  rw [tCanonicalizer, tCanonicalizerCandidate_conj]
  unfold tZero
  exact congrArg tMagicStateOfDirection
    (Classical.choose_spec (tCanonicalizerCandidate_complete d))

/-- Normalize a density using the finite Clifford selected by its maximizing
T direction. -/
noncomputable def tCanonicalizedInput (rho : DensityOperator QubitSpace) :
    DensityOperator QubitSpace :=
  (tCanonicalizer (tMaximizingDirection rho)).conjDensity rho

theorem tCanonicalizer_conj_tProjector (d : TDirection) :
    (tCanonicalizer d).conjOperator (tProjector d) =
      tProjector tZeroDirection := by
  have h := congrArg (fun sigma : DensityOperator QubitSpace => sigma.toOperator)
    (tCanonicalizer_conj_tMagicState d)
  simpa [tZero, tMagicStateOfDirection, blochDensity, tProjector]
    using h

theorem tCanonicalizedInput_tInputFidelity (rho : DensityOperator QubitSpace) :
    tInputFidelity (tCanonicalizedInput rho) = tFidelity rho := by
  unfold tCanonicalizedInput tInputFidelity tDirectionFidelity
  rw [← tCanonicalizer_conj_tProjector (tMaximizingDirection rho)]
  rw [projectionFidelity_conjDensity]
  exact (tMaximizingDirection_attains rho).symm

/-- After finite Clifford normalization, the BK05 input error is exactly one
minus the squared maximum T fidelity of the original density. -/
theorem tCanonicalizedInput_error_eq_one_sub_tFidelity_sq
    (rho : DensityOperator QubitSpace) :
    tInputError (tCanonicalizedInput rho) = 1 - tFidelity rho ^ 2 := by
  rw [tInputError_eq_one_sub_tInputFidelity_sq,
    tCanonicalizedInput_tInputFidelity]

/-- The canonicalized BK05 error lies in the source interval `[0, 1/2]`. -/
theorem tCanonicalizedInput_error_mem_Icc_half
    (rho : DensityOperator QubitSpace) :
    1 - tFidelity rho ^ 2 ∈ Set.Icc (0 : Real) (1 / 2) := by
  have hF := tFidelity_mem_Icc rho
  have hhalf := tFidelity_sq_ge_half rho
  constructor
  · nlinarith [mul_nonneg hF.1 (sub_nonneg.mpr hF.2)]
  · nlinarith

/-- Finite Clifford normalization followed by the physical T twirl produces
the exact BK05 diagonal T0/T1 mixture at error `1 - F_T(rho)^2`. -/
theorem tTwirlChannel_mapDensity_canonicalizedInput
    (rho : DensityOperator QubitSpace) :
    tTwirlChannel.mapDensity (tCanonicalizedInput rho) =
      tDiagonalInput (1 - tFidelity rho ^ 2)
        (tCanonicalizedInput_error_mem_Icc_half rho).1
        ((tCanonicalizedInput_error_mem_Icc_half rho).2.trans (by norm_num)) := by
  rw [tTwirlChannel_mapDensity]
  have herror := tCanonicalizedInput_error_eq_one_sub_tFidelity_sq rho
  have hmem := tCanonicalizedInput_error_mem_Icc_half rho
  have hdiag := tTwirl_eq_diagonalInput_of_inputError
    (tCanonicalizedInput rho)
    (by simpa [herror] using hmem.1)
    (by rw [herror]; exact hmem.2.trans (by norm_num))
  simpa [herror] using hdiag

end BK05T
end Distillation
end QEC
