import QEC.Distillation.FiveQubitT.Postselection

/-!
# BK05 five-qubit T-state recurrence

This internal module normalizes the source-exact raw coefficients proved by
`FiveQubitTPostselection`, identifies the exact nontrivial fixed point, and
proves the below-threshold iteration theorem.  It introduces no new physical
instrument or decoder: all physical data are consumed from the preceding
checkpoint.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace BK05T

open Semantics Semantics.Qubit
open OneQubitMagic

private theorem densityOperator_ext
    {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl

/-- The normalized accepted output error after the source-specified swap. -/
def bk05TRecurrence (epsilon : Real) : Real :=
  fiveQubitRawTZeroCoefficient epsilon /
    fiveQubitSuccessProbability epsilon

/-- The odds coordinate used in BK05's displayed recurrence. -/
def bk05TOdds (epsilon : Real) : Real := epsilon / (1 - epsilon)

/-- The exact nontrivial physical fixed point of the five-to-one recurrence. -/
def bk05TThreshold : Real := (1 - Real.sqrt (3 / 7)) / 2

/-- The quadratic factor controlling the sign of one recurrence step. -/
def bk05TThresholdPolynomial (epsilon : Real) : Real :=
  7 * epsilon ^ 2 - 7 * epsilon + 1

private theorem sqrt_three_sevenths_sq :
    Real.sqrt (3 / 7 : Real) ^ 2 = 3 / 7 := by
  exact Real.sq_sqrt (by norm_num)

theorem bk05TThreshold_pos : 0 < bk05TThreshold := by
  have hsqrt_nonneg : 0 <= Real.sqrt (3 / 7 : Real) := Real.sqrt_nonneg _
  have hsqrt_lt_one : Real.sqrt (3 / 7 : Real) < 1 := by
    nlinarith [sqrt_three_sevenths_sq]
  unfold bk05TThreshold
  linarith

theorem bk05TThreshold_lt_half : bk05TThreshold < 1 / 2 := by
  have hsqrt_pos : 0 < Real.sqrt (3 / 7 : Real) :=
    Real.sqrt_pos.2 (by norm_num)
  unfold bk05TThreshold
  linarith

theorem bk05TThreshold_le_half : bk05TThreshold <= 1 / 2 :=
  bk05TThreshold_lt_half.le

theorem bk05TThresholdPolynomial_threshold :
    bk05TThresholdPolynomial bk05TThreshold = 0 := by
  unfold bk05TThresholdPolynomial bk05TThreshold
  nlinarith [sqrt_three_sevenths_sq]

theorem bk05TThresholdPolynomial_pos_of_lt
    (epsilon : Real) (hepsilon : epsilon < bk05TThreshold) :
    0 < bk05TThresholdPolynomial epsilon := by
  have hfactor :
      bk05TThresholdPolynomial epsilon =
        (epsilon - bk05TThreshold) *
          (7 * epsilon + 7 * bk05TThreshold - 7) := by
    calc
      bk05TThresholdPolynomial epsilon =
          bk05TThresholdPolynomial epsilon -
            bk05TThresholdPolynomial bk05TThreshold := by
              rw [bk05TThresholdPolynomial_threshold]
              ring
      _ = (epsilon - bk05TThreshold) *
          (7 * epsilon + 7 * bk05TThreshold - 7) := by
            unfold bk05TThresholdPolynomial
            ring
  rw [hfactor]
  exact mul_pos_of_neg_of_neg (sub_neg.mpr hepsilon) (by
    have := bk05TThreshold_lt_half
    nlinarith)

theorem bk05T_successProbability_pos
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    0 < fiveQubitSuccessProbability epsilon :=
  fiveQubitSuccessProbability_pos epsilon hzero (by linarith)

theorem bk05TRecurrence_nonneg
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    0 <= bk05TRecurrence epsilon := by
  exact div_nonneg
    (fiveQubitRawTZeroCoefficient_nonneg epsilon hzero (by linarith))
    (bk05T_successProbability_pos epsilon hzero hhalf).le

private theorem rawCoefficient_difference_factor
    (epsilon : Real) :
    fiveQubitRawTOneCoefficient epsilon -
        fiveQubitRawTZeroCoefficient epsilon =
      ((1 - 2 * epsilon) ^ 3 *
        (1 + epsilon * (1 - epsilon))) / 6 := by
  unfold fiveQubitRawTOneCoefficient fiveQubitRawTZeroCoefficient
  ring

theorem bk05TRecurrence_le_half
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    bk05TRecurrence epsilon <= 1 / 2 := by
  have hcomplement : 0 <= 1 - epsilon := by linarith
  have hlinear : 0 <= 1 - 2 * epsilon := by linarith
  have hfactor :
      0 <= (1 - 2 * epsilon) ^ 3 *
        (1 + epsilon * (1 - epsilon)) := by positivity
  have hcoeff :
      fiveQubitRawTZeroCoefficient epsilon <=
        fiveQubitRawTOneCoefficient epsilon := by
    have hdiff := rawCoefficient_difference_factor epsilon
    have hfactor' :
        0 <= ((1 - 2 * epsilon) ^ 3 *
          (1 + epsilon * (1 - epsilon))) / 6 := by positivity
    linarith
  have hsuccess := bk05T_successProbability_pos epsilon hzero hhalf
  rw [bk05TRecurrence, div_le_iff₀ hsuccess]
  unfold fiveQubitSuccessProbability
  linarith

theorem bk05TRecurrence_mem_physicalInterval
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    bk05TRecurrence epsilon ∈ Set.Icc (0 : Real) (1 / 2) :=
  ⟨bk05TRecurrence_nonneg epsilon hzero hhalf,
    bk05TRecurrence_le_half epsilon hzero hhalf⟩

/-- The normalized physical accepted density is the diagonal input whose error
parameter is the recurrence value. -/
theorem fiveQubitAcceptedOutput_eq_diagonalInput
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    fiveQubitAcceptedOutput epsilon hzero (by linarith) =
      tDiagonalInput (bk05TRecurrence epsilon)
        (bk05TRecurrence_nonneg epsilon hzero hhalf)
        ((bk05TRecurrence_le_half epsilon hzero hhalf).trans (by norm_num)) := by
  apply densityOperator_ext
  rw [fiveQubitAcceptedOutput_toOperator, tDiagonalInput_toOperator,
    Fin.sum_univ_two]
  simp only [tRawInputBranch, tInputWeight, tInputComponent]
  have hsuccess := bk05T_successProbability_pos epsilon hzero hhalf
  have hweight :
      1 - bk05TRecurrence epsilon =
        fiveQubitRawTOneCoefficient epsilon /
          fiveQubitSuccessProbability epsilon := by
    unfold bk05TRecurrence
    field_simp [hsuccess.ne']
    unfold fiveQubitSuccessProbability
    ring
  rw [hweight]
  rfl

/-- The actual accepted density has exactly the analytic recurrence error. -/
theorem fiveQubitAcceptedOutput_tInputError
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    tInputError (fiveQubitAcceptedOutput epsilon hzero (by linarith)) =
      bk05TRecurrence epsilon := by
  rw [fiveQubitAcceptedOutput_eq_diagonalInput epsilon hzero hhalf]
  exact tInputError_diagonalInput _ _ _

/-- The concrete protocol's reported accepted output realizes the recurrence. -/
theorem fiveQubitMagicStateProtocol_reportedOutput_tInputError
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    tInputError
        ((fiveQubitMagicStateProtocol epsilon hzero (by linarith)).run.reportedOutput
          (fiveQubitMagicStateProtocol epsilon hzero (by linarith)).behavior) =
      bk05TRecurrence epsilon := by
  rw [fiveQubitMagicStateProtocol_reportedOutput]
  exact fiveQubitAcceptedOutput_tInputError epsilon hzero hhalf

theorem bk05TOdds_nonneg
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    0 <= bk05TOdds epsilon := by
  exact div_nonneg hzero (by linarith)

theorem bk05TRecurrence_eq_oddsFormula
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    bk05TRecurrence epsilon =
      (bk05TOdds epsilon ^ 5 + 5 * bk05TOdds epsilon ^ 2) /
        (1 + 5 * bk05TOdds epsilon ^ 2 +
          5 * bk05TOdds epsilon ^ 3 + bk05TOdds epsilon ^ 5) := by
  have hsuccess := bk05T_successProbability_pos epsilon hzero hhalf
  have hcomplement : 1 - epsilon ≠ 0 := by linarith
  have hodds_nonneg := bk05TOdds_nonneg epsilon hzero hhalf
  have hodds_denom :
      0 < 1 + 5 * bk05TOdds epsilon ^ 2 +
        5 * bk05TOdds epsilon ^ 3 + bk05TOdds epsilon ^ 5 := by
    positivity
  unfold bk05TRecurrence bk05TOdds fiveQubitSuccessProbability
    fiveQubitRawTZeroCoefficient fiveQubitRawTOneCoefficient
  field_simp [hsuccess.ne', hcomplement, hodds_denom.ne']
  ring

theorem bk05TRecurrence_sub_input
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    bk05TRecurrence epsilon - epsilon =
      -(epsilon * (1 - epsilon) * (1 - 2 * epsilon) *
          bk05TThresholdPolynomial epsilon) /
        (6 * fiveQubitSuccessProbability epsilon) := by
  have hsuccess := bk05T_successProbability_pos epsilon hzero hhalf
  unfold bk05TRecurrence
  field_simp [hsuccess.ne']
  unfold bk05TThresholdPolynomial fiveQubitSuccessProbability
    fiveQubitRawTZeroCoefficient fiveQubitRawTOneCoefficient
  ring

theorem bk05TRecurrence_lt_input
    (epsilon : Real) (hzero : 0 < epsilon)
    (hthreshold : epsilon < bk05TThreshold) :
    bk05TRecurrence epsilon < epsilon := by
  have hhalf : epsilon <= 1 / 2 :=
    (hthreshold.trans bk05TThreshold_lt_half).le
  have hsuccess := bk05T_successProbability_pos epsilon hzero.le hhalf
  have hcomplement : 0 < 1 - epsilon := by linarith
  have hlinear : 0 < 1 - 2 * epsilon := by
    linarith [hthreshold.trans bk05TThreshold_lt_half]
  have hpolynomial :=
    bk05TThresholdPolynomial_pos_of_lt epsilon hthreshold
  have hdiff : bk05TRecurrence epsilon - epsilon < 0 := by
    rw [bk05TRecurrence_sub_input epsilon hzero.le hhalf]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (by positivity)
  linarith

theorem bk05TRecurrence_zero : bk05TRecurrence 0 = 0 := by
  norm_num [bk05TRecurrence, fiveQubitSuccessProbability,
    fiveQubitRawTZeroCoefficient, fiveQubitRawTOneCoefficient]

theorem bk05TRecurrence_half : bk05TRecurrence (1 / 2) = 1 / 2 := by
  norm_num [bk05TRecurrence, fiveQubitSuccessProbability,
    fiveQubitRawTZeroCoefficient, fiveQubitRawTOneCoefficient]

theorem bk05TRecurrence_threshold :
    bk05TRecurrence bk05TThreshold = bk05TThreshold := by
  have hzero := bk05TThreshold_pos.le
  have hhalf := bk05TThreshold_le_half
  have hsub := bk05TRecurrence_sub_input bk05TThreshold hzero hhalf
  rw [bk05TThresholdPolynomial_threshold] at hsub
  norm_num at hsub
  linarith

private theorem thresholdPolynomial_eq_zero_of_physical
    (epsilon : Real) (hhalf : epsilon <= 1 / 2)
    (hzero : bk05TThresholdPolynomial epsilon = 0) :
    epsilon = bk05TThreshold := by
  have hfactor :
      bk05TThresholdPolynomial epsilon =
        (epsilon - bk05TThreshold) *
          (7 * epsilon + 7 * bk05TThreshold - 7) := by
    calc
      bk05TThresholdPolynomial epsilon =
          bk05TThresholdPolynomial epsilon -
            bk05TThresholdPolynomial bk05TThreshold := by
              rw [bk05TThresholdPolynomial_threshold]
              ring
      _ = (epsilon - bk05TThreshold) *
          (7 * epsilon + 7 * bk05TThreshold - 7) := by
            unfold bk05TThresholdPolynomial
            ring
  rw [hfactor] at hzero
  rcases mul_eq_zero.mp hzero with hroot | hupper
  · exact sub_eq_zero.mp hroot
  · have hthreshold_lt := bk05TThreshold_lt_half
    nlinarith

theorem bk05TRecurrence_fixed_iff
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    bk05TRecurrence epsilon = epsilon <->
      epsilon = 0 \/ epsilon = bk05TThreshold \/ epsilon = 1 / 2 := by
  constructor
  · intro hfixed
    have hsub := bk05TRecurrence_sub_input epsilon hzero hhalf
    rw [hfixed] at hsub
    have hproduct :
        epsilon * (1 - epsilon) * (1 - 2 * epsilon) *
            bk05TThresholdPolynomial epsilon = 0 := by
      have hsuccess := bk05T_successProbability_pos epsilon hzero hhalf
      field_simp [hsuccess.ne'] at hsub
      linarith
    rcases mul_eq_zero.mp hproduct with hleft | hpoly
    · rcases mul_eq_zero.mp hleft with hleft | hlinear
      · rcases mul_eq_zero.mp hleft with hepsilon | hcomplement
        · exact Or.inl hepsilon
        · exfalso
          have : epsilon = 1 := by linarith
          linarith
      · exact Or.inr (Or.inr (by linarith))
    · exact Or.inr (Or.inl
        (thresholdPolynomial_eq_zero_of_physical epsilon hhalf hpoly))
  · rintro (rfl | rfl | rfl)
    · exact bk05TRecurrence_zero
    · exact bk05TRecurrence_threshold
    · exact bk05TRecurrence_half

/-! ## Accepted iteration below threshold -/

/-- The accepted-error sequence obtained by recursively reusing the protocol. -/
def bk05TIteration (epsilon : Real) (rounds : Nat) : Real :=
  (bk05TRecurrence^[rounds]) epsilon

@[simp]
theorem bk05TIteration_zero (epsilon : Real) :
    bk05TIteration epsilon 0 = epsilon := rfl

theorem bk05TIteration_succ (epsilon : Real) (rounds : Nat) :
    bk05TIteration epsilon (rounds + 1) =
      bk05TRecurrence (bk05TIteration epsilon rounds) := by
  rw [bk05TIteration, bk05TIteration, Function.iterate_succ_apply']

theorem bk05TIteration_nonneg_and_lt_threshold
    (epsilon : Real) (hzero : 0 <= epsilon)
    (hthreshold : epsilon < bk05TThreshold) (rounds : Nat) :
    0 <= bk05TIteration epsilon rounds ∧
      bk05TIteration epsilon rounds < bk05TThreshold := by
  induction rounds with
  | zero => exact ⟨hzero, hthreshold⟩
  | succ rounds ih =>
      rw [bk05TIteration_succ]
      have hhalf : bk05TIteration epsilon rounds <= 1 / 2 :=
        (ih.2.trans bk05TThreshold_lt_half).le
      refine ⟨bk05TRecurrence_nonneg _ ih.1 hhalf, ?_⟩
      by_cases hcurrent : bk05TIteration epsilon rounds = 0
      · rw [hcurrent, bk05TRecurrence_zero]
        exact bk05TThreshold_pos
      · have hcurrent_pos : 0 < bk05TIteration epsilon rounds :=
          lt_of_le_of_ne ih.1 (Ne.symm hcurrent)
        exact (bk05TRecurrence_lt_input _ hcurrent_pos ih.2).trans ih.2

theorem bk05TIteration_antitone
    (epsilon : Real) (hzero : 0 <= epsilon)
    (hthreshold : epsilon < bk05TThreshold) :
    Antitone (bk05TIteration epsilon) := by
  apply antitone_nat_of_succ_le
  intro rounds
  rw [bk05TIteration_succ]
  have hinvariant :=
    bk05TIteration_nonneg_and_lt_threshold epsilon hzero hthreshold rounds
  by_cases hcurrent : bk05TIteration epsilon rounds = 0
  · rw [hcurrent, bk05TRecurrence_zero]
  · exact (bk05TRecurrence_lt_input _
      (lt_of_le_of_ne hinvariant.1 (Ne.symm hcurrent)) hinvariant.2).le

private theorem bk05TRecurrence_continuousAt
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    ContinuousAt bk05TRecurrence epsilon := by
  have hsuccess := bk05T_successProbability_pos epsilon hzero hhalf
  have hrawZero : ContinuousAt fiveQubitRawTZeroCoefficient epsilon := by
    unfold fiveQubitRawTZeroCoefficient
    fun_prop
  have hrawOne : ContinuousAt fiveQubitRawTOneCoefficient epsilon := by
    unfold fiveQubitRawTOneCoefficient
    fun_prop
  have hsuccessContinuous :
      ContinuousAt fiveQubitSuccessProbability epsilon := by
    unfold fiveQubitSuccessProbability
    exact hrawZero.add hrawOne
  unfold bk05TRecurrence
  exact hrawZero.div hsuccessContinuous hsuccess.ne'

/-- Below the exact threshold, recursive accepted errors converge to zero. -/
theorem bk05TIteration_tendsto_zero
    (epsilon : Real) (hzero : 0 <= epsilon)
    (hthreshold : epsilon < bk05TThreshold) :
    Filter.Tendsto (bk05TIteration epsilon) Filter.atTop (nhds 0) := by
  let sequence : Nat -> Real := bk05TIteration epsilon
  have hinvariant : ∀ rounds,
      0 <= sequence rounds ∧ sequence rounds < bk05TThreshold := by
    intro rounds
    exact bk05TIteration_nonneg_and_lt_threshold
      epsilon hzero hthreshold rounds
  have hanti : Antitone sequence :=
    bk05TIteration_antitone epsilon hzero hthreshold
  have hbdd : BddBelow (Set.range sequence) := by
    refine ⟨0, ?_⟩
    rintro value ⟨rounds, rfl⟩
    exact (hinvariant rounds).1
  let limit : Real := ⨅ rounds, sequence rounds
  have htendsto : Filter.Tendsto sequence Filter.atTop (nhds limit) := by
    exact tendsto_atTop_ciInf hanti hbdd
  have hlimit_nonneg : 0 <= limit := by
    exact le_ciInf fun rounds => (hinvariant rounds).1
  have hlimit_le_input : limit <= epsilon := by
    have hle : limit <= sequence 0 := ciInf_le hbdd 0
    simpa [limit, sequence] using hle
  have hlimit_half : limit <= 1 / 2 := by
    linarith [hlimit_le_input, hthreshold, bk05TThreshold_lt_half]
  have hcontinuous : ContinuousAt bk05TRecurrence limit :=
    bk05TRecurrence_continuousAt limit hlimit_nonneg hlimit_half
  have hmap : Filter.Tendsto
      (fun rounds => bk05TRecurrence (sequence rounds)) Filter.atTop
      (nhds (bk05TRecurrence limit)) :=
    hcontinuous.tendsto.comp htendsto
  have hsucc_atTop : Filter.Tendsto (fun rounds : Nat => rounds + 1)
      Filter.atTop Filter.atTop := by
    exact (strictMono_nat_of_lt_succ fun rounds =>
      Nat.lt_succ_self (rounds + 1)).tendsto_atTop
  have hshift : Filter.Tendsto (fun rounds => sequence (rounds + 1))
      Filter.atTop (nhds limit) := htendsto.comp hsucc_atTop
  have hmap_shift : Filter.Tendsto (fun rounds => sequence (rounds + 1))
      Filter.atTop (nhds (bk05TRecurrence limit)) := by
    simpa [sequence, bk05TIteration_succ] using hmap
  have hfixed : bk05TRecurrence limit = limit :=
    tendsto_nhds_unique hmap_shift hshift
  have hlimit_zero : limit = 0 := by
    rcases (bk05TRecurrence_fixed_iff limit hlimit_nonneg hlimit_half).mp hfixed with
      hzero_limit | hthreshold_limit | hhalf_limit
    · exact hzero_limit
    · exfalso
      rw [hthreshold_limit] at hlimit_le_input
      linarith
    · exfalso
      rw [hhalf_limit] at hlimit_le_input
      linarith [hthreshold, bk05TThreshold_lt_half]
  simpa [sequence, hlimit_zero] using htendsto

/-- Every positive target error is reached after finitely many accepted rounds. -/
theorem bk05TIteration_eventually_lt
    (epsilon target : Real) (hzero : 0 <= epsilon)
    (hthreshold : epsilon < bk05TThreshold) (htarget : 0 < target) :
    ∃ rounds : Nat, bk05TIteration epsilon rounds < target := by
  have htendsto := bk05TIteration_tendsto_zero epsilon hzero hthreshold
  exact ((tendsto_order.mp htendsto).2 target htarget).exists

/-! ## Square-root fidelity and the actual #736 normalization/twirl -/

/-- The source input error expressed from the repository's square-root maximum
T fidelity. -/
def bk05TFidelityError (rho : DensityOperator QubitSpace) : Real :=
  1 - tFidelity rho ^ 2

/-- The exact square-root fidelity form of the BK05 threshold. -/
def bk05TFidelityThreshold : Real :=
  Real.sqrt ((1 + Real.sqrt (3 / 7)) / 2)

theorem bk05TFidelityError_nonneg (rho : DensityOperator QubitSpace) :
    0 <= bk05TFidelityError rho := by
  have hfidelity := tFidelity_mem_Icc rho
  unfold bk05TFidelityError
  nlinarith [hfidelity.1, hfidelity.2, sq_nonneg (tFidelity rho)]

theorem bk05TFidelityError_le_one (rho : DensityOperator QubitSpace) :
    bk05TFidelityError rho <= 1 := by
  unfold bk05TFidelityError
  nlinarith [sq_nonneg (tFidelity rho)]

/-- Finite-Clifford canonicalization ties the analytic error to actual maximum
square-root fidelity, without replacing `tFidelity` by a squared convention. -/
theorem tCanonicalizedInput_error_eq_bk05TFidelityError
    (rho : DensityOperator QubitSpace) :
    tInputError (tCanonicalizedInput rho) = bk05TFidelityError rho := by
  exact tCanonicalizedInput_error_eq_one_sub_tFidelity_sq rho

private def qubitDensityBloch (rho : DensityOperator QubitSpace) :
    PauliAxis -> Real
  | .x => 2 * (LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 2) Complex).toBasis
      (EuclideanSpace.basisFun (Fin 2) Complex).toBasis
      rho.toOperator 0 1).re
  | .y => -2 * (LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 2) Complex).toBasis
      (EuclideanSpace.basisFun (Fin 2) Complex).toBasis
      rho.toOperator 0 1).im
  | .z => 2 * (LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 2) Complex).toBasis
      (EuclideanSpace.basisFun (Fin 2) Complex).toBasis
      rho.toOperator 0 0).re - 1

private theorem qubitDensity_toOperator_eq_blochProjector
    (rho : DensityOperator QubitSpace) :
    rho.toOperator = blochProjector (qubitDensityBloch rho) := by
  let orthobasis := EuclideanSpace.basisFun (Fin 2) Complex
  let basis := orthobasis.toBasis
  let matrix := LinearMap.toMatrix basis basis rho.toOperator
  have hadjoint : matrix.conjTranspose = matrix := by
    calc
      matrix.conjTranspose = LinearMap.toMatrix basis basis
          (LinearMap.adjoint rho.toOperator) := by
        exact (LinearMap.toMatrix_adjoint
          (v₁ := orthobasis) (v₂ := orthobasis) rho.toOperator).symm
      _ = matrix := congrArg (LinearMap.toMatrix basis basis)
        (DensityOperator.toOperator_adjoint_eq_self rho)
  have htrace : matrix 0 0 + matrix 1 1 = 1 := by
    have h := rho.trace_one
    rw [LinearMap.trace_eq_matrix_trace Complex basis] at h
    simpa [matrix, Matrix.trace, Fin.sum_univ_two] using h
  have h00 : star (matrix 0 0) = matrix 0 0 := by
    simpa using congrFun (congrFun hadjoint 0) 0
  have h11 : star (matrix 1 1) = matrix 1 1 := by
    simpa using congrFun (congrFun hadjoint 1) 1
  have h10 : star (matrix 0 1) = matrix 1 0 := by
    simpa using congrFun (congrFun hadjoint 1) 0
  have h00im : (matrix 0 0).im = 0 := by
    have h := congrArg Complex.im h00
    simp at h
    linarith
  have h11im : (matrix 1 1).im = 0 := by
    have h := congrArg Complex.im h11
    simp at h
    linarith
  have htraceRe : (matrix 0 0).re + (matrix 1 1).re = 1 := by
    have h := congrArg Complex.re htrace
    simpa using h
  apply (LinearMap.toMatrix basis basis).injective
  ext row col
  fin_cases row <;> fin_cases col <;>
    simp [basis, orthobasis, qubitDensityBloch, blochProjector, blochOperator,
      pauliX, pauliY, pauliZ, Matrix.toEuclideanLin_eq_toLin_orthonormal,
      LinearMap.toMatrix_toLin, pauliXMatrix, pauliYMatrix, pauliZMatrix,
      zPhase] <;>
    apply Complex.ext <;> simp <;>
    first
    | linarith
    | have hre := congrArg Complex.re h10
      have him := congrArg Complex.im h10
      simp at hre him
      linarith

private theorem tInputSquaredOverlap_of_bloch
    (rho : DensityOperator QubitSpace) (r : PauliAxis -> Real)
    (hrho : rho.toOperator = blochProjector r) :
    tInputSquaredOverlap rho =
      (1 + (r .x + r .y + r .z) * (Real.sqrt 3)⁻¹) / 2 := by
  unfold tInputSquaredOverlap projectionSquaredOverlap
  have hzeroBloch : tBlochOfDirection tZeroDirection = tBloch := by
    funext i
    fin_cases i <;>
      simp [tZeroDirection, tReference, tBlochOfDirection,
        signedCoordinateValue, tBloch]
  rw [tProjector, hzeroBloch]
  change (LinearMap.trace Complex QubitSpace
    (blochProjector tBloch * rho.toOperator)).re = _
  rw [hrho]
  have htrace : LinearMap.trace Complex QubitSpace (blochProjector r) = 1 := by
    rw [← hrho]
    exact rho.trace_one
  change (LinearMap.trace Complex QubitSpace
    (((2 : Complex)⁻¹ • (1 + blochOperator tBloch)) *
      blochProjector r)).re = _
  have htraceX : LinearMap.trace Complex QubitSpace
      (pauliX * blochProjector r) = r .x := by
    simpa [pauliOperator] using trace_pauli_mul_blochProjector r .x
  have htraceY : LinearMap.trace Complex QubitSpace
      (pauliY * blochProjector r) = r .y := by
    simpa [pauliOperator] using trace_pauli_mul_blochProjector r .y
  have htraceZ : LinearMap.trace Complex QubitSpace
      (pauliZ * blochProjector r) = r .z := by
    simpa [pauliOperator] using trace_pauli_mul_blochProjector r .z
  rw [smul_mul_assoc, add_mul, one_mul, map_smul, map_add, htrace]
  unfold blochOperator
  rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
    map_add, map_add, map_smul, map_smul, map_smul,
    htraceX, htraceY, htraceZ]
  simp [tBloch]
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hinv : (Real.sqrt 3)⁻¹ = Real.sqrt 3 / 3 := by
    field_simp [hne]
    nlinarith [hsq]
  rw [hinv]
  ring

private theorem tCanonicalizedInput_twirlBloch_eq
    (rho : DensityOperator QubitSpace) :
    tTwirlBloch (qubitDensityBloch (tCanonicalizedInput rho)) =
      tDiagonalBloch (bk05TFidelityError rho) := by
  let r := qubitDensityBloch (tCanonicalizedInput rho)
  have hrho : (tCanonicalizedInput rho).toOperator = blochProjector r :=
    qubitDensity_toOperator_eq_blochProjector _
  have hoverlap :
      (1 + (r .x + r .y + r .z) * (Real.sqrt 3)⁻¹) / 2 =
        tFidelity rho ^ 2 := by
    calc
      _ = tInputSquaredOverlap (tCanonicalizedInput rho) :=
        (tInputSquaredOverlap_of_bloch (tCanonicalizedInput rho) r hrho).symm
      _ = tInputFidelity (tCanonicalizedInput rho) ^ 2 :=
        tInputSquaredOverlap_eq_tInputFidelity_sq _
      _ = tFidelity rho ^ 2 := by
        rw [tCanonicalizedInput_tInputFidelity]
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hinv : (Real.sqrt 3)⁻¹ = Real.sqrt 3 / 3 := by
    field_simp [hne]
    nlinarith [hsq]
  rw [hinv] at hoverlap
  funext i
  simp only [tTwirlBloch, tDiagonalBloch, bk05TFidelityError]
  calc
    (r .x + r .y + r .z) / 3 =
        (r .x + r .y + r .z) * (Real.sqrt 3 ^ 2) / 9 := by
          rw [hsq]
          ring
    _ = ((r .x + r .y + r .z) * (Real.sqrt 3 / 3)) *
        (Real.sqrt 3 / 3) := by ring
    _ = (2 * tFidelity rho ^ 2 - 1) * (Real.sqrt 3 / 3) := by
      congr 1
      linarith
    _ = (1 - 2 * (1 - tFidelity rho ^ 2)) * (Real.sqrt 3)⁻¹ := by
      rw [hinv]
      ring

/-- The concrete finite-Clifford normalization followed by the actual
three-branch T twirl is exactly the source diagonal input at error
`1 - tFidelity rho ^ 2`. -/
theorem tTwirl_canonicalizedInput_eq_diagonalInput
    (rho : DensityOperator QubitSpace) :
    tTwirl (tCanonicalizedInput rho) =
      tDiagonalInput (bk05TFidelityError rho)
        (bk05TFidelityError_nonneg rho) (bk05TFidelityError_le_one rho) := by
  exact tTwirl_eq_diagonalInput_of_bloch
    (tCanonicalizedInput rho)
    (qubitDensityBloch (tCanonicalizedInput rho))
    (qubitDensity_toOperator_eq_blochProjector _)
    (bk05TFidelityError rho)
    (bk05TFidelityError_nonneg rho) (bk05TFidelityError_le_one rho)
    (tCanonicalizedInput_twirlBloch_eq rho)

/-- The analytic error threshold is exactly the source square-root fidelity
threshold, with no silent squaring of the public fidelity API. -/
theorem bk05TFidelityError_lt_threshold_iff
    (rho : DensityOperator QubitSpace) :
    bk05TFidelityError rho < bk05TThreshold <->
      bk05TFidelityThreshold < tFidelity rho := by
  have hfidelity := tFidelity_mem_Icc rho
  have hthresholdSquare : 0 <= (1 + Real.sqrt (3 / 7 : Real)) / 2 := by
    positivity
  unfold bk05TFidelityError bk05TFidelityThreshold
  rw [Real.sqrt_lt hthresholdSquare hfidelity.1]
  unfold bk05TThreshold
  constructor <;> intro h <;> nlinarith

/-- Under the exact square-root fidelity hypothesis, the concrete protocol's
reported accepted density has the source recurrence error. -/
theorem fiveQubitMagicStateProtocol_reportedOutput_tInputError_of_tFidelity
    (rho : DensityOperator QubitSpace)
    (hfidelity : bk05TFidelityThreshold < tFidelity rho) :
    tInputError
        ((fiveQubitMagicStateProtocol (bk05TFidelityError rho)
          (bk05TFidelityError_nonneg rho) (bk05TFidelityError_le_one rho)).run.reportedOutput
          (fiveQubitMagicStateProtocol (bk05TFidelityError rho)
            (bk05TFidelityError_nonneg rho)
            (bk05TFidelityError_le_one rho)).behavior) =
      bk05TRecurrence (bk05TFidelityError rho) := by
  have hthreshold :=
    (bk05TFidelityError_lt_threshold_iff rho).mpr hfidelity
  exact fiveQubitMagicStateProtocol_reportedOutput_tInputError
    (bk05TFidelityError rho) (bk05TFidelityError_nonneg rho)
    ((hthreshold.trans bk05TThreshold_lt_half).le)

/-- The same exact square-root fidelity premise gives a finite accepted-round
witness for every positive target error. -/
theorem bk05TIteration_eventually_lt_of_tFidelity
    (rho : DensityOperator QubitSpace)
    (hfidelity : bk05TFidelityThreshold < tFidelity rho)
    (target : Real) (htarget : 0 < target) :
    ∃ rounds : Nat,
      bk05TIteration (bk05TFidelityError rho) rounds < target := by
  exact bk05TIteration_eventually_lt (bk05TFidelityError rho) target
    (bk05TFidelityError_nonneg rho)
    ((bk05TFidelityError_lt_threshold_iff rho).mpr hfidelity) htarget

/-- Source-facing terminal checkpoint: actual normalization and twirling feed
the concrete five-qubit recurrence, whose accepted iterations reach every
positive target below the exact square-root fidelity threshold. -/
theorem bk05TFidelityDistillation
    (rho : DensityOperator QubitSpace)
    (hfidelity : bk05TFidelityThreshold < tFidelity rho)
    (target : Real) (htarget : 0 < target) :
    tTwirl (tCanonicalizedInput rho) =
        tDiagonalInput (bk05TFidelityError rho)
          (bk05TFidelityError_nonneg rho) (bk05TFidelityError_le_one rho) ∧
      tInputError
          ((fiveQubitMagicStateProtocol (bk05TFidelityError rho)
            (bk05TFidelityError_nonneg rho)
            (bk05TFidelityError_le_one rho)).run.reportedOutput
            (fiveQubitMagicStateProtocol (bk05TFidelityError rho)
              (bk05TFidelityError_nonneg rho)
              (bk05TFidelityError_le_one rho)).behavior) =
        bk05TRecurrence (bk05TFidelityError rho) ∧
      ∃ rounds : Nat,
        bk05TIteration (bk05TFidelityError rho) rounds < target := by
  exact ⟨tTwirl_canonicalizedInput_eq_diagonalInput rho,
    fiveQubitMagicStateProtocol_reportedOutput_tInputError_of_tFidelity
      rho hfidelity,
    bk05TIteration_eventually_lt_of_tFidelity rho hfidelity target htarget⟩

end BK05T
end Distillation
end QEC
