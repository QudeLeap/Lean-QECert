import QEC.Distillation.FiveQubitT.Recurrence
import QEC.Distillation.FifteenQubitH.Threshold
import QEC.Distillation.Universality.FiniteRegisterUniversality
import QEC.Distillation.Universality.GeneratedUniversality
import QEC.Distillation.Universality.IdealResourceUniversality
import QEC.Semantics.Core.OperatorTraceNorm
import QEC.Semantics.Entropy.MatrixRelative
import QEC.Semantics.Channels.TraceNorm
import QEC.Semantics.Channels.ChoiKraus
import QEC.Semantics.Dynamics.ThermalEncoding
noncomputable section

universe u v

namespace QEC
namespace Distillation

open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open OneQubitMagic
open GeneratedUniversality
open FiniteRegisterUniversality
open FiniteRegisterUniversality.FiniteRegisterCircuit
open scoped BigOperators Matrix.Norms.Elementwise

private theorem densityOperator_ext
    {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl

private abbrev tInitialError (rho : DensityOperator QubitSpace) : Real :=
  BK05T.bk05TFidelityError rho

private abbrev tIteration (rho : DensityOperator QubitSpace) (rounds : Nat) : Real :=
  BK05T.bk05TIteration (tInitialError rho) rounds

inductive BK05TSemanticSchedule (rho : DensityOperator QubitSpace) : Nat -> Type
  | leaf (resource : DensityOperator QubitSpace) : BK05TSemanticSchedule rho 0
  | accepted {depth : Nat}
      (children : Fin 5 -> BK05TSemanticSchedule rho depth)
      (acceptedOutput : DensityOperator QubitSpace) :
      BK05TSemanticSchedule rho (depth + 1)

namespace BK05TSemanticSchedule

def leafCount {rho : DensityOperator QubitSpace} :
    {depth : Nat} -> BK05TSemanticSchedule rho depth -> Nat
  | _, .leaf _ => 1
  | _, .accepted children _ => Finset.univ.sum fun site => leafCount (children site)

def rootOutput {rho : DensityOperator QubitSpace} :
    {depth : Nat} -> BK05TSemanticSchedule rho depth -> DensityOperator QubitSpace
  | _, .leaf resource => resource
  | _, .accepted _ acceptedOutput => acceptedOutput

def rootInput {rho : DensityOperator QubitSpace} {depth : Nat}
    (schedule : BK05TSemanticSchedule rho (depth + 1)) :
    ResourceInput 5 QubitSpace :=
  match schedule with
  | .accepted children _ => fun site => rootOutput (children site)

noncomputable def preparedInput {rho : DensityOperator QubitSpace} {depth : Nat}
    (schedule : BK05TSemanticSchedule rho (depth + 1)) :
    DensityOperator BK05T.FiveQubitSpace :=
  BK05T.fiveQubitPrepareInput (rootInput schedule)

end BK05TSemanticSchedule

private theorem tIteration_bounds
    (rho : DensityOperator QubitSpace)
    (hthreshold : tInitialError rho < BK05T.bk05TThreshold) (rounds : Nat) :
    0 <= tIteration rho rounds /\ tIteration rho rounds <= 1 / 2 := by
  have h := BK05T.bk05TIteration_nonneg_and_lt_threshold
    (tInitialError rho) (BK05T.bk05TFidelityError_nonneg rho) hthreshold rounds
  exact ⟨h.1, (h.2.trans BK05T.bk05TThreshold_lt_half).le⟩

private theorem tIteration_le_one
    (rho : DensityOperator QubitSpace)
    (hthreshold : tInitialError rho < BK05T.bk05TThreshold) (rounds : Nat) :
    tIteration rho rounds <= 1 :=
  (tIteration_bounds rho hthreshold rounds).2.trans (by norm_num)

noncomputable def bk05TCompleteSemanticSchedule
    (rho : DensityOperator QubitSpace)
    (hthreshold : tInitialError rho < BK05T.bk05TThreshold) :
    (rounds : Nat) -> BK05TSemanticSchedule rho rounds
  | 0 => .leaf (BK05T.tTwirl (BK05T.tCanonicalizedInput rho))
  | depth + 1 => .accepted
      (fun _ => bk05TCompleteSemanticSchedule rho hthreshold depth)
      (BK05T.fiveQubitAcceptedOutput (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth))

theorem bk05TCompleteSemanticSchedule_leafCount
    (rho : DensityOperator QubitSpace)
    (hthreshold : tInitialError rho < BK05T.bk05TThreshold) (rounds : Nat) :
    BK05TSemanticSchedule.leafCount
        (bk05TCompleteSemanticSchedule rho hthreshold rounds) = 5 ^ rounds := by
  induction rounds with
  | zero => rfl
  | succ depth ih =>
      simp [bk05TCompleteSemanticSchedule, BK05TSemanticSchedule.leafCount, ih,
        Nat.pow_succ, Nat.mul_comm]

theorem bk05TCompleteSemanticSchedule_rootOutput_eq_diagonalInput
    (rho : DensityOperator QubitSpace)
    (hthreshold : tInitialError rho < BK05T.bk05TThreshold) (rounds : Nat) :
    BK05TSemanticSchedule.rootOutput
        (bk05TCompleteSemanticSchedule rho hthreshold rounds) =
      BK05T.tDiagonalInput (tIteration rho rounds)
        (tIteration_bounds rho hthreshold rounds).1
        (tIteration_le_one rho hthreshold rounds) := by
  cases rounds with
  | zero =>
      simpa [BK05TSemanticSchedule.rootOutput, bk05TCompleteSemanticSchedule] using
        BK05T.tTwirl_canonicalizedInput_eq_diagonalInput rho
  | succ depth =>
      simpa [BK05TSemanticSchedule.rootOutput, bk05TCompleteSemanticSchedule,
        BK05T.bk05TIteration_succ] using
        BK05T.fiveQubitAcceptedOutput_eq_diagonalInput (tIteration rho depth)
          (tIteration_bounds rho hthreshold depth).1
          (tIteration_bounds rho hthreshold depth).2

theorem bk05TCompleteSemanticSchedule_rootInput_eq_noisyInput
    (rho : DensityOperator QubitSpace)
    (hthreshold : tInitialError rho < BK05T.bk05TThreshold) (depth : Nat) :
    BK05TSemanticSchedule.rootInput
        (bk05TCompleteSemanticSchedule rho hthreshold (depth + 1)) =
      (BK05T.fiveQubitDistillationRun (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth)).noisyInput := by
  funext site
  change BK05TSemanticSchedule.rootOutput
      (bk05TCompleteSemanticSchedule rho hthreshold depth) =
    BK05T.tDiagonalInput (tIteration rho depth)
      (tIteration_bounds rho hthreshold depth).1
      (tIteration_le_one rho hthreshold depth)
  exact bk05TCompleteSemanticSchedule_rootOutput_eq_diagonalInput
    rho hthreshold depth

theorem bk05TCompleteSemanticSchedule_preparedInput_eq_run_preparedInput
    (rho : DensityOperator QubitSpace)
    (hthreshold : tInitialError rho < BK05T.bk05TThreshold) (depth : Nat) :
    BK05TSemanticSchedule.preparedInput
        (bk05TCompleteSemanticSchedule rho hthreshold (depth + 1)) =
      (BK05T.fiveQubitDistillationRun (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth)).prepareInput
        ((BK05T.fiveQubitDistillationRun (tIteration rho depth)
          (tIteration_bounds rho hthreshold depth).1
          (tIteration_le_one rho hthreshold depth)).noisyInput) := by
  change BK05T.fiveQubitPrepareInput
      (BK05TSemanticSchedule.rootInput
        (bk05TCompleteSemanticSchedule rho hthreshold (depth + 1))) =
    BK05T.fiveQubitPrepareInput
      ((BK05T.fiveQubitDistillationRun (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth)).noisyInput)
  rw [bk05TCompleteSemanticSchedule_rootInput_eq_noisyInput rho hthreshold depth]

theorem bk05TCompleteSemanticSchedule_rootOutput_eq_run_acceptedOutput
    (rho : DensityOperator QubitSpace)
    (hthreshold : tInitialError rho < BK05T.bk05TThreshold) (depth : Nat) :
    BK05TSemanticSchedule.rootOutput
        (bk05TCompleteSemanticSchedule rho hthreshold (depth + 1)) =
      (BK05T.fiveQubitDistillationRun (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth)).acceptedOutput := by
  change BK05T.fiveQubitAcceptedOutput (tIteration rho depth)
      (tIteration_bounds rho hthreshold depth).1
      (tIteration_le_one rho hthreshold depth) =
    (BK05T.fiveQubitDistillationRun (tIteration rho depth)
      (tIteration_bounds rho hthreshold depth).1
      (tIteration_le_one rho hthreshold depth)).acceptedOutput
  exact (BK05T.fiveQubitDistillationRun_acceptedOutput _ _ _).symm

theorem bk05TCompleteSemanticSchedule_realizes_actual_run
    (rho : DensityOperator QubitSpace)
    (hthreshold : tInitialError rho < BK05T.bk05TThreshold) (depth : Nat) :
    (BK05T.fiveQubitDistillationRun (tIteration rho depth)
      (tIteration_bounds rho hthreshold depth).1
      (tIteration_le_one rho hthreshold depth)).resourceCount = 5 /\
    BK05TSemanticSchedule.rootInput
        (bk05TCompleteSemanticSchedule rho hthreshold (depth + 1)) =
      (BK05T.fiveQubitDistillationRun (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth)).noisyInput /\
    BK05TSemanticSchedule.preparedInput
        (bk05TCompleteSemanticSchedule rho hthreshold (depth + 1)) =
      (BK05T.fiveQubitDistillationRun (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth)).prepareInput
        ((BK05T.fiveQubitDistillationRun (tIteration rho depth)
          (tIteration_bounds rho hthreshold depth).1
          (tIteration_le_one rho hthreshold depth)).noisyInput) /\
    BK05TSemanticSchedule.rootOutput
        (bk05TCompleteSemanticSchedule rho hthreshold (depth + 1)) =
      (BK05T.fiveQubitDistillationRun (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth)).acceptedOutput := by
  exact ⟨BK05T.fiveQubitDistillationRun_resourceCount _ _ _,
    bk05TCompleteSemanticSchedule_rootInput_eq_noisyInput rho hthreshold depth,
    bk05TCompleteSemanticSchedule_preparedInput_eq_run_preparedInput
      rho hthreshold depth,
    bk05TCompleteSemanticSchedule_rootOutput_eq_run_acceptedOutput
      rho hthreshold depth⟩

theorem bk05TCompleteSemanticSchedule_protocol_reportedOutput
    (rho : DensityOperator QubitSpace)
    (hthreshold : tInitialError rho < BK05T.bk05TThreshold) (depth : Nat) :
    BK05TSemanticSchedule.rootOutput
        (bk05TCompleteSemanticSchedule rho hthreshold (depth + 1)) =
      (BK05T.fiveQubitMagicStateProtocol (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth)).run.reportedOutput
        (BK05T.fiveQubitMagicStateProtocol (tIteration rho depth)
          (tIteration_bounds rho hthreshold depth).1
          (tIteration_le_one rho hthreshold depth)).behavior := by
  calc
    BK05TSemanticSchedule.rootOutput
        (bk05TCompleteSemanticSchedule rho hthreshold (depth + 1)) =
      (BK05T.fiveQubitDistillationRun (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth)).acceptedOutput :=
      bk05TCompleteSemanticSchedule_rootOutput_eq_run_acceptedOutput
        rho hthreshold depth
    _ = BK05T.fiveQubitAcceptedOutput (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth) :=
      BK05T.fiveQubitDistillationRun_acceptedOutput _ _ _
    _ = (BK05T.fiveQubitMagicStateProtocol (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth)).run.reportedOutput
        (BK05T.fiveQubitMagicStateProtocol (tIteration rho depth)
          (tIteration_bounds rho hthreshold depth).1
          (tIteration_le_one rho hthreshold depth)).behavior :=
      (BK05T.fiveQubitMagicStateProtocol_reportedOutput _ _ _).symm

theorem bk05TCompleteSemanticSchedule_protocol_inputPermitted
    (rho : DensityOperator QubitSpace)
    (hthreshold : tInitialError rho < BK05T.bk05TThreshold) (depth : Nat) :
    (BK05T.fiveQubitMagicStateProtocol (tIteration rho depth)
      (tIteration_bounds rho hthreshold depth).1
      (tIteration_le_one rho hthreshold depth)).inputErrorModel.Permits
      (BK05TSemanticSchedule.rootInput
        (bk05TCompleteSemanticSchedule rho hthreshold (depth + 1))) := by
  rw [bk05TCompleteSemanticSchedule_rootInput_eq_noisyInput rho hthreshold depth]
  exact (BK05T.fiveQubitMagicStateProtocol (tIteration rho depth)
    (tIteration_bounds rho hthreshold depth).1
    (tIteration_le_one rho hthreshold depth)).inputPermitted

private theorem tZero_eq_tMagicState : BK05T.tZero = tMagicState := by
  apply densityOperator_ext
  change blochProjector (tBlochOfDirection tReference) =
    blochProjector tBloch
  congr 1
  funext axis
  fin_cases axis <;>
    simp [tBlochOfDirection, tReference, tBloch, signedCoordinateValue]

theorem tDiagonalInput_traceNorm_sub_tMagicState_le
    (epsilon : Real) (hzero : 0 <= epsilon) (hone : epsilon <= 1) :
    traceNorm
      ((BK05T.tDiagonalInput epsilon hzero hone).toOperator -
        tMagicState.toOperator) <= 2 * epsilon := by
  rw [← tZero_eq_tMagicState]
  have hoperator :
      (BK05T.tDiagonalInput epsilon hzero hone).toOperator -
          BK05T.tZero.toOperator =
        (epsilon : Complex) •
          (BK05T.tOne.toOperator - BK05T.tZero.toOperator) := by
    rw [BK05T.tDiagonalInput_toOperator, Fin.sum_univ_two]
    simp only [BK05T.tRawInputBranch, BK05T.tInputWeight, BK05T.tInputComponent]
    module
  rw [hoperator, traceNorm_smul]
  have hendpoint :
      traceNorm (BK05T.tOne.toOperator - BK05T.tZero.toOperator) <= 2 := by
    calc
      traceNorm (BK05T.tOne.toOperator - BK05T.tZero.toOperator) =
          traceNorm (BK05T.tOne.toOperator + -BK05T.tZero.toOperator) := by
            rw [sub_eq_add_neg]
      _ <= traceNorm BK05T.tOne.toOperator +
          traceNorm (-BK05T.tZero.toOperator) := traceNorm_add_le _ _
      _ = 2 := by
        rw [traceNorm_neg, BK05T.tOne.traceNorm_eq_one,
          BK05T.tZero.traceNorm_eq_one]
        norm_num
  calc
    ‖(epsilon : Complex)‖ *
        traceNorm (BK05T.tOne.toOperator - BK05T.tZero.toOperator) =
      epsilon * traceNorm (BK05T.tOne.toOperator - BK05T.tZero.toOperator) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hzero]
    _ <= epsilon * 2 := mul_le_mul_of_nonneg_left hendpoint hzero
    _ = 2 * epsilon := by ring

theorem bk05TProducesTraceCloseResource
    (rho : DensityOperator QubitSpace)
    (hfidelity : BK05T.bk05TFidelityThreshold < tFidelity rho)
    (eta : Real) (heta : 0 < eta) :
    ∃ rounds : Nat,
      traceNorm
        ((BK05TSemanticSchedule.rootOutput
          (bk05TCompleteSemanticSchedule rho
            ((BK05T.bk05TFidelityError_lt_threshold_iff rho).mpr hfidelity)
            rounds)).toOperator - tMagicState.toOperator) < eta /\
      BK05TSemanticSchedule.leafCount
        (bk05TCompleteSemanticSchedule rho
          ((BK05T.bk05TFidelityError_lt_threshold_iff rho).mpr hfidelity)
          rounds) = 5 ^ rounds := by
  let hthreshold : tInitialError rho < BK05T.bk05TThreshold :=
    (BK05T.bk05TFidelityError_lt_threshold_iff rho).mpr hfidelity
  have hdistillation :=
    BK05T.bk05TFidelityDistillation rho hfidelity (eta / 2) (by linarith)
  obtain ⟨rounds, hrounds⟩ := hdistillation.2.2
  refine ⟨rounds, ?_, bk05TCompleteSemanticSchedule_leafCount rho hthreshold rounds⟩
  calc
    traceNorm
        ((BK05TSemanticSchedule.rootOutput
          (bk05TCompleteSemanticSchedule rho hthreshold rounds)).toOperator -
          tMagicState.toOperator) =
      traceNorm
        ((BK05T.tDiagonalInput (tIteration rho rounds)
          (tIteration_bounds rho hthreshold rounds).1
          (tIteration_le_one rho hthreshold rounds)).toOperator -
          tMagicState.toOperator) := by
        rw [bk05TCompleteSemanticSchedule_rootOutput_eq_diagonalInput
          rho hthreshold rounds]
    _ <= 2 * tIteration rho rounds :=
      tDiagonalInput_traceNorm_sub_tMagicState_le (tIteration rho rounds)
        (tIteration_bounds rho hthreshold rounds).1
        (tIteration_le_one rho hthreshold rounds)
    _ < eta := by linarith

/-- The raw zero-error BK15 endpoint is the literal reference H resource. -/
theorem bk15IdealReturnedHOutput_eq_hMagicState :
    BK15.Threshold.bk15IdealReturnedHOutput = hMagicState := by
  apply densityOperator_ext
  rw [BK15.Threshold.bk15IdealReturnedHOutput,
    BK15.Threshold.bk15RawZeroEndpoint_is_ideal,
    BK15.NoisyInput.aZeroDensity, BK15.NoisyInput.sourceA0Density,
    UnitaryTransport.conjDensity_toOperator]
  exact BK15.NoisyInput.sourceA0Transport.symm_conjOperator_conjOperator _

private theorem traceNorm_rankOne_le (x y : QubitSpace) :
    traceNorm (InnerProductSpace.rankOne Complex x y).toLinearMap ≤ ‖x‖ * ‖y‖ := by
  change ‖tracePairing (InnerProductSpace.rankOne Complex x y).toLinearMap‖ ≤ ‖x‖ * ‖y‖
  apply (tracePairing (InnerProductSpace.rankOne Complex x y).toLinearMap).opNorm_le_bound
  · positivity
  · intro B
    rw [show tracePairing (InnerProductSpace.rankOne Complex x y).toLinearMap B =
        inner Complex y (B x) by
      change LinearMap.trace Complex QubitSpace
          (B.toLinearMap * (InnerProductSpace.rankOne Complex x y).toLinearMap) = _
      rw [show B.toLinearMap * (InnerProductSpace.rankOne Complex x y).toLinearMap =
          (InnerProductSpace.rankOne Complex (B x) y).toLinearMap by
        ext z
        simp]
      exact InnerProductSpace.trace_rankOne (B x) y]
    calc
      ‖inner Complex y (B x)‖ ≤ ‖y‖ * ‖B x‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (‖B‖ * ‖x‖) := by
        gcongr
        exact B.le_opNorm x
      _ = (‖x‖ * ‖y‖) * ‖B‖ := by ring

private def hOrthogonalPart (u : QubitSpace) : QubitSpace :=
  u - inner Complex sourceHState u • sourceHState

private theorem hOrthogonalPart_split (u : QubitSpace) :
    u = inner Complex sourceHState u • sourceHState + hOrthogonalPart u := by
  simp [hOrthogonalPart]

private theorem hOrthogonalPart_inner (u : QubitSpace) :
    inner Complex sourceHState (hOrthogonalPart u) = 0 := by
  simp [hOrthogonalPart, inner_sub_right, inner_smul_right,
    sourceHState_inner_self]

private theorem hOrthogonalPart_norm_sq (u : QubitSpace) :
    ‖hOrthogonalPart u‖ ^ 2 = ‖u‖ ^ 2 - ‖inner Complex sourceHState u‖ ^ 2 := by
  rw [hOrthogonalPart, norm_sub_sq (𝕜 := Complex), norm_smul, sourceHState_norm]
  have hinner :
      (inner Complex u (inner Complex sourceHState u • sourceHState)).re =
        ‖inner Complex sourceHState u‖ ^ 2 := by
    rw [inner_smul_right]
    have hconj : inner Complex u sourceHState =
        starRingEnd Complex (inner Complex sourceHState u) :=
      (inner_conj_symm u sourceHState).symm
    rw [hconj]
    change ((inner Complex sourceHState u) *
      starRingEnd Complex (inner Complex sourceHState u)).re =
        ‖inner Complex sourceHState u‖ ^ 2
    rw [Complex.mul_conj]
    simpa using Complex.normSq_eq_norm_sq (inner Complex sourceHState u)
  change ‖u‖ ^ 2 - 2 *
      (inner Complex u (inner Complex sourceHState u • sourceHState)).re +
      (‖inner Complex sourceHState u‖ * 1) ^ 2 =
        ‖u‖ ^ 2 - ‖inner Complex sourceHState u‖ ^ 2
  rw [hinner]
  ring

private theorem rankOne_sub_hComponent (u : QubitSpace) :
    (InnerProductSpace.rankOne Complex u u).toLinearMap -
        (InnerProductSpace.rankOne Complex
          (inner Complex sourceHState u • sourceHState)
          (inner Complex sourceHState u • sourceHState)).toLinearMap =
      (InnerProductSpace.rankOne Complex (hOrthogonalPart u) u).toLinearMap +
        (InnerProductSpace.rankOne Complex
          (inner Complex sourceHState u • sourceHState)
          (hOrthogonalPart u)).toLinearMap := by
  let a : QubitSpace := inner Complex sourceHState u • sourceHState
  let v : QubitSpace := hOrthogonalPart u
  have hu : u = a + v := hOrthogonalPart_split u
  change (InnerProductSpace.rankOne Complex u u).toLinearMap -
      (InnerProductSpace.rankOne Complex a a).toLinearMap =
    (InnerProductSpace.rankOne Complex v u).toLinearMap +
      (InnerProductSpace.rankOne Complex a v).toLinearMap
  calc
    (InnerProductSpace.rankOne Complex u u).toLinearMap -
        (InnerProductSpace.rankOne Complex a a).toLinearMap =
      (InnerProductSpace.rankOne Complex (a + v) (a + v)).toLinearMap -
        (InnerProductSpace.rankOne Complex a a).toLinearMap := by rw [← hu]
    _ = (InnerProductSpace.rankOne Complex v (a + v)).toLinearMap +
        (InnerProductSpace.rankOne Complex a v).toLinearMap := by
      apply LinearMap.ext
      intro x
      change inner Complex (a + v) x • (a + v) - inner Complex a x • a =
        inner Complex (a + v) x • v + inner Complex v x • a
      rw [inner_add_left]
      module
    _ = (InnerProductSpace.rankOne Complex v u).toLinearMap +
        (InnerProductSpace.rankOne Complex a v).toLinearMap := by rw [hu]

private theorem rankOne_sub_hComponent_trace_bound (u : QubitSpace) :
    traceNorm ((InnerProductSpace.rankOne Complex u u).toLinearMap -
        (InnerProductSpace.rankOne Complex
          (inner Complex sourceHState u • sourceHState)
          (inner Complex sourceHState u • sourceHState)).toLinearMap) ≤
      2 * ‖u‖ * ‖hOrthogonalPart u‖ := by
  rw [rankOne_sub_hComponent]
  calc
    traceNorm
        ((InnerProductSpace.rankOne Complex (hOrthogonalPart u) u).toLinearMap +
          (InnerProductSpace.rankOne Complex
            (inner Complex sourceHState u • sourceHState)
            (hOrthogonalPart u)).toLinearMap) ≤
        traceNorm ((InnerProductSpace.rankOne Complex (hOrthogonalPart u) u).toLinearMap) +
          traceNorm ((InnerProductSpace.rankOne Complex
            (inner Complex sourceHState u • sourceHState)
            (hOrthogonalPart u)).toLinearMap) := traceNorm_add_le _ _
    _ ≤ ‖hOrthogonalPart u‖ * ‖u‖ +
          (‖inner Complex sourceHState u‖ * ‖hOrthogonalPart u‖) := by
      apply add_le_add
      · exact traceNorm_rankOne_le _ _
      · calc
          traceNorm ((InnerProductSpace.rankOne Complex
              (inner Complex sourceHState u • sourceHState)
              (hOrthogonalPart u)).toLinearMap) ≤
            ‖inner Complex sourceHState u • sourceHState‖ *
              ‖hOrthogonalPart u‖ := traceNorm_rankOne_le _ _
          _ = ‖inner Complex sourceHState u‖ *
              ‖hOrthogonalPart u‖ := by rw [norm_smul, sourceHState_norm, mul_one]
    _ ≤ ‖hOrthogonalPart u‖ * ‖u‖ + ‖u‖ * ‖hOrthogonalPart u‖ := by
      gcongr
      calc
        ‖inner Complex sourceHState u‖ ≤ ‖sourceHState‖ * ‖u‖ :=
          norm_inner_le_norm _ _
        _ = ‖u‖ := by rw [sourceHState_norm, one_mul]
    _ = 2 * ‖u‖ * ‖hOrthogonalPart u‖ := by ring

private theorem hReferenceProjector_eq_sourceH :
    hProjector hReference =
      (InnerProductSpace.rankOne Complex sourceHState sourceHState).toLinearMap := by
  rw [show hProjector hReference = hMagicState.toOperator by
    change blochProjector (hBlochOfDirection hReference) = blochProjector hBloch
    congr 1
    funext axis
    fin_cases axis <;>
      norm_num [hReference, hBlochOfDirection, hBloch, signedCoordinateValue],
    hMagicState_eq_sourceHDensity, sourceHDensity_toOperator]

private theorem rankOne_hComponent_eq_smul_hMagicState (u : QubitSpace) :
    (InnerProductSpace.rankOne Complex
      (inner Complex sourceHState u • sourceHState)
      (inner Complex sourceHState u • sourceHState)).toLinearMap =
      (‖inner Complex sourceHState u‖ ^ 2 : Complex) • hMagicState.toOperator := by
  rw [hMagicState_eq_sourceHDensity, sourceHDensity_toOperator]
  apply LinearMap.ext
  intro x
  let a : Complex := inner Complex sourceHState u
  change inner Complex (a • sourceHState) x • (a • sourceHState) =
    (‖a‖ ^ 2 : Complex) • (inner Complex sourceHState x • sourceHState)
  rw [inner_smul_left]
  have hcc : starRingEnd Complex a * a = (‖a‖ ^ 2 : Complex) := by
    calc
      starRingEnd Complex a * a = (Complex.normSq a : Complex) :=
        Complex.normSq_eq_conj_mul_self.symm
      _ = (‖a‖ ^ 2 : Complex) := by
        rw [Complex.normSq_eq_norm_sq]
        norm_cast
  change (starRingEnd Complex a * inner Complex sourceHState x) • a • sourceHState =
    (‖a‖ ^ 2 : Complex) • inner Complex sourceHState x • sourceHState
  have hs : (starRingEnd Complex a * inner Complex sourceHState x) * a =
      (‖a‖ ^ 2 : Complex) * inner Complex sourceHState x := by
    calc
      (starRingEnd Complex a * inner Complex sourceHState x) * a =
          (starRingEnd Complex a * a) * inner Complex sourceHState x := by ring
      _ = (‖a‖ ^ 2 : Complex) * inner Complex sourceHState x := by rw [hcc]
  simpa only [smul_smul] using
    congrArg (fun c : Complex => c • sourceHState) hs

private theorem qubit_traceNorm_sub_fixedPure_le_four_sqrt_infidelity
    (sigma : DensityOperator QubitSpace) :
    traceNorm (sigma.toOperator - hMagicState.toOperator) ≤
      4 * Real.sqrt
        (1 - projectionSquaredOverlap (hProjector hReference) sigma) := by
  classical
  rcases density_exists_rankOne_ensemble sigma with ⟨m, u, hensemble⟩
  have hnorm : ∑ i, ‖u i‖ ^ 2 = 1 :=
    rankOne_ensemble_norm_sq_sum_one sigma u hensemble
  have hoverlap :
      projectionSquaredOverlap (hProjector hReference) sigma =
        ∑ i, ‖inner Complex sourceHState (u i)‖ ^ 2 := by
    unfold projectionSquaredOverlap
    rw [hensemble, Finset.mul_sum]
    simp only [map_sum, trace_mul_rankOne]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hReferenceProjector_eq_sourceH]
    change (inner Complex (u i)
      (inner Complex sourceHState (u i) • sourceHState)).re = _
    rw [inner_smul_right]
    have hconj : inner Complex (u i) sourceHState =
        starRingEnd Complex (inner Complex sourceHState (u i)) :=
      (inner_conj_symm (u i) sourceHState).symm
    rw [hconj, Complex.mul_conj]
    simpa using Complex.normSq_eq_norm_sq
      (inner Complex sourceHState (u i))
  set e : Real := 1 - projectionSquaredOverlap (hProjector hReference) sigma with he
  have horthsum : (∑ i, ‖hOrthogonalPart (u i)‖ ^ 2) = e := by
    rw [he]
    calc
      (∑ i, ‖hOrthogonalPart (u i)‖ ^ 2) =
          ∑ i, (‖u i‖ ^ 2 - ‖inner Complex sourceHState (u i)‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hOrthogonalPart_norm_sq (u i)
      _ = (∑ i, ‖u i‖ ^ 2) -
          ∑ i, ‖inner Complex sourceHState (u i)‖ ^ 2 := by
        rw [Finset.sum_sub_distrib]
      _ = e := by rw [hnorm, ← hoverlap, he]
  have he_nonneg : 0 ≤ e := by
    rw [← horthsum]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have he_le_one : e ≤ 1 := by
    rw [he]
    have := projectionSquaredOverlap_nonneg (hProjector hReference) sigma
      (hProjector_isSymmetricProjection hReference)
    linarith
  have he_le_sqrt : e ≤ Real.sqrt e := by
    apply (Real.le_sqrt he_nonneg he_nonneg).mpr
    nlinarith
  have hcross : (∑ i, ‖u i‖ * ‖hOrthogonalPart (u i)‖) ≤ Real.sqrt e := by
    calc
      (∑ i, ‖u i‖ * ‖hOrthogonalPart (u i)‖) ≤
          Real.sqrt (∑ i, ‖u i‖ ^ 2) *
            Real.sqrt (∑ i, ‖hOrthogonalPart (u i)‖ ^ 2) := by
        simpa using (Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m))
          (fun i => ‖u i‖) (fun i => ‖hOrthogonalPart (u i)‖))
      _ = Real.sqrt e := by rw [hnorm, horthsum]; norm_num
  have hcomponents :
      (∑ i, (InnerProductSpace.rankOne Complex
        (inner Complex sourceHState (u i) • sourceHState)
        (inner Complex sourceHState (u i) • sourceHState)).toLinearMap) =
        (projectionSquaredOverlap (hProjector hReference) sigma : Complex) •
          hMagicState.toOperator := by
    have hsumC : (∑ i, (‖inner Complex sourceHState (u i)‖ ^ 2 : Complex)) =
        (projectionSquaredOverlap (hProjector hReference) sigma : Complex) := by
      exact_mod_cast hoverlap.symm
    rw [show (∑ i, (InnerProductSpace.rankOne Complex
        (inner Complex sourceHState (u i) • sourceHState)
        (inner Complex sourceHState (u i) • sourceHState)).toLinearMap) =
        ∑ i, (‖inner Complex sourceHState (u i)‖ ^ 2 : Complex) •
          hMagicState.toOperator by
      apply Finset.sum_congr rfl
      intro i hi
      exact rankOne_hComponent_eq_smul_hMagicState (u i)]
    rw [← Finset.sum_smul, hsumC]
  let remainder : Fin m → Operator QubitSpace := fun i =>
    (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap -
      (InnerProductSpace.rankOne Complex
        (inner Complex sourceHState (u i) • sourceHState)
        (inner Complex sourceHState (u i) • sourceHState)).toLinearMap
  have hdiff : sigma.toOperator - hMagicState.toOperator =
      (∑ i, remainder i) -
        (e : Complex) • hMagicState.toOperator := by
    change sigma.toOperator - hMagicState.toOperator =
      (∑ i, ((InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap -
        (InnerProductSpace.rankOne Complex
          (inner Complex sourceHState (u i) • sourceHState)
          (inner Complex sourceHState (u i) • sourceHState)).toLinearMap)) -
        (e : Complex) • hMagicState.toOperator
    rw [hensemble, Finset.sum_sub_distrib, hcomponents, he]
    push_cast
    module
  have htermTrace (i : Fin m) :
      traceNorm (remainder i) ≤ 2 * ‖u i‖ * ‖hOrthogonalPart (u i)‖ := by
    exact rankOne_sub_hComponent_trace_bound (u i)
  have hsumTrace : traceNorm (∑ i, remainder i) ≤
      ∑ i, 2 * ‖u i‖ * ‖hOrthogonalPart (u i)‖ := by
    calc
      traceNorm (∑ i, remainder i) ≤ ∑ i, traceNorm (remainder i) := by
        simpa using traceNorm_sum_le (H := QubitSpace) Finset.univ remainder
      _ ≤ ∑ i, 2 * ‖u i‖ * ‖hOrthogonalPart (u i)‖ := by
        exact Finset.sum_le_sum fun i _ => htermTrace i
  have htailTrace : traceNorm ((e : Complex) • hMagicState.toOperator) = e := by
    rw [traceNorm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg he_nonneg, DensityOperator.traceNorm_eq_one]
    norm_num
  have hfirst : traceNorm ((∑ i, remainder i) -
      (e : Complex) • hMagicState.toOperator) ≤ traceNorm (∑ i, remainder i) + e := by
    rw [sub_eq_add_neg]
    calc
      traceNorm ((∑ i, remainder i) + -((e : Complex) • hMagicState.toOperator)) ≤
          traceNorm (∑ i, remainder i) +
            traceNorm (-((e : Complex) • hMagicState.toOperator)) :=
        traceNorm_add_le _ _
      _ = traceNorm (∑ i, remainder i) + e := by
        rw [traceNorm_neg, htailTrace]
  have hsecond :
      (∑ i, 2 * ‖u i‖ * ‖hOrthogonalPart (u i)‖) + e ≤
        2 * Real.sqrt e + e := by
    apply add_le_add_left
    calc
      (∑ i, 2 * ‖u i‖ * ‖hOrthogonalPart (u i)‖) =
          ∑ i, 2 * (‖u i‖ * ‖hOrthogonalPart (u i)‖) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = 2 * ∑ i, ‖u i‖ * ‖hOrthogonalPart (u i)‖ :=
        by rw [Finset.mul_sum]
      _ ≤ 2 * Real.sqrt e :=
        mul_le_mul_of_nonneg_left hcross (by norm_num)
  calc
    traceNorm (sigma.toOperator - hMagicState.toOperator) =
        traceNorm ((∑ i, remainder i) -
          (e : Complex) • hMagicState.toOperator) := congrArg traceNorm hdiff
    _ ≤ traceNorm (∑ i, remainder i) + e := hfirst
    _ ≤ (∑ i, 2 * ‖u i‖ * ‖hOrthogonalPart (u i)‖) + e := by
      exact add_le_add_left hsumTrace _
    _ ≤ 2 * Real.sqrt e + e := hsecond
    _ ≤ 4 * Real.sqrt e := by nlinarith
    _ = 4 * Real.sqrt
        (1 - projectionSquaredOverlap (hProjector hReference) sigma) := by rw [he]

/-- Raw trace-norm strengthening of
`BK15.Threshold.bk15HfidelityDistillation`.  The strict branch exposes the
actual finite semantic run and returns its literal inverse-frame H density. -/
theorem bk15HProducesTraceCloseResource
    (rho : DensityOperator QubitSpace)
    (hfidelity : BK15.Threshold.FStar < hFidelity rho)
    (eta : Real) (heta : 0 < eta) :
    ∃ rounds : Nat,
      traceNorm
        ((BK15.Threshold.bk15AcceptedRunHOutput rho rounds).toOperator -
          hMagicState.toOperator) < eta ∧
        (BK15.Threshold.bk15HInputError rho = 0 ∨
          ∃ (hpositive : 0 < BK15.Threshold.bk15HInputError rho)
            (hthreshold : BK15.Threshold.bk15HInputError rho <
              BK15.Threshold.epsilonStar) (depth : Nat),
            rounds = depth + 1 ∧
            BK15.Threshold.BK15SemanticSchedule.leafCount
                (BK15.Threshold.bk15CompleteSemanticSchedule
                  rho hpositive hthreshold (depth + 1)) =
              15 ^ (depth + 1) ∧
            BK15.Threshold.BK15SemanticSchedule.rootInput
                (BK15.Threshold.bk15CompleteSemanticSchedule
                  rho hpositive hthreshold (depth + 1)) =
              (BK15.Protocol.bk15Run
                (BK15.Threshold.bk15IterationEpsilon
                  (BK15.Threshold.bk15HInputError rho) hpositive hthreshold depth)
                (BK15.Threshold.bk15Iteration_pos_and_lt_epsilonStar
                  (BK15.Threshold.bk15HInputError rho) hpositive hthreshold depth).1).noisyInput ∧
            BK15.Threshold.BK15SemanticSchedule.preparedInput
                (BK15.Threshold.bk15CompleteSemanticSchedule
                  rho hpositive hthreshold (depth + 1)) =
              (BK15.Protocol.bk15Run
                (BK15.Threshold.bk15IterationEpsilon
                  (BK15.Threshold.bk15HInputError rho) hpositive hthreshold depth)
                (BK15.Threshold.bk15Iteration_pos_and_lt_epsilonStar
                  (BK15.Threshold.bk15HInputError rho) hpositive hthreshold depth).1).prepareInput
                ((BK15.Protocol.bk15Run
                  (BK15.Threshold.bk15IterationEpsilon
                    (BK15.Threshold.bk15HInputError rho) hpositive hthreshold depth)
                  (BK15.Threshold.bk15Iteration_pos_and_lt_epsilonStar
                    (BK15.Threshold.bk15HInputError rho) hpositive hthreshold depth).1).noisyInput) ∧
            BK15.Threshold.BK15SemanticSchedule.rootOutput
                (BK15.Threshold.bk15CompleteSemanticSchedule
                  rho hpositive hthreshold (depth + 1)) =
              (BK15.Protocol.bk15Run
                (BK15.Threshold.bk15IterationEpsilon
                  (BK15.Threshold.bk15HInputError rho) hpositive hthreshold depth)
                (BK15.Threshold.bk15Iteration_pos_and_lt_epsilonStar
                  (BK15.Threshold.bk15HInputError rho) hpositive hthreshold depth).1).acceptedOutput ∧
            BK15.Threshold.bk15AcceptedRunHOutput rho (depth + 1) =
              BK15.NoisyInput.sourceA0Transport.symm.conjDensity
                (BK15.Threshold.BK15SemanticSchedule.rootOutput
                  (BK15.Threshold.bk15CompleteSemanticSchedule
                    rho hpositive hthreshold (depth + 1)))) := by
  have hthreshold : BK15.Threshold.bk15HInputError rho <
      BK15.Threshold.epsilonStar :=
    BK15.Threshold.bk15HInputError_lt_epsilonStar_of_FStar_lt rho hfidelity
  by_cases hzero : BK15.Threshold.bk15HInputError rho = 0
  · refine ⟨0, ?_, Or.inl hzero⟩
    have hnotstrict : ¬ (0 < BK15.Threshold.bk15HInputError rho ∧
        BK15.Threshold.bk15HInputError rho < BK15.Threshold.epsilonStar) := by
      rintro ⟨hpositive, _⟩
      linarith
    have hreturned : BK15.Threshold.bk15AcceptedRunHOutput rho 0 =
        BK15.Threshold.bk15IdealReturnedHOutput := by
      simp [BK15.Threshold.bk15AcceptedRunHOutput, hnotstrict, hzero]
    rw [hreturned, bk15IdealReturnedHOutput_eq_hMagicState, sub_self]
    rw [(traceNorm_eq_zero_iff (0 : Operator QubitSpace)).2 rfl]
    exact heta
  · have hpositive : 0 < BK15.Threshold.bk15HInputError rho :=
      lt_of_le_of_ne (BK15.Threshold.bk15HInputError_nonneg rho) (Ne.symm hzero)
    let delta : Real := (eta / 8) ^ 2
    have hdelta : 0 < delta := by
      dsimp [delta]
      exact sq_pos_of_pos (by positivity)
    obtain ⟨depth, hdepth⟩ := BK15.Threshold.bk15Iteration_eventually_lt
      (BK15.Threshold.bk15HInputError rho) delta hpositive hthreshold hdelta
    have hacceptedError : BK15.NoisyInput.aInputError
        (BK15.Threshold.bk15AcceptedLayer
          (BK15.Threshold.bk15HInputError rho) hpositive hthreshold depth) =
        BK15.Threshold.bk15Iteration
          (BK15.Threshold.bk15HInputError rho) (depth + 1) := by
      simpa [BK15.Protocol.bk15OutputError] using
        (BK15.Threshold.bk15AcceptedLayer_error_eq_iteration_succ
          (BK15.Threshold.bk15HInputError rho) hpositive hthreshold depth)
    have hrootError : BK15.NoisyInput.aInputError
        (BK15.Threshold.BK15SemanticSchedule.rootOutput
          (BK15.Threshold.bk15CompleteSemanticSchedule
            rho hpositive hthreshold (depth + 1))) < delta := by
      calc
        BK15.NoisyInput.aInputError
            (BK15.Threshold.BK15SemanticSchedule.rootOutput
              (BK15.Threshold.bk15CompleteSemanticSchedule
                rho hpositive hthreshold (depth + 1))) =
            BK15.NoisyInput.aInputError
              (BK15.Threshold.bk15AcceptedLayer
                (BK15.Threshold.bk15HInputError rho) hpositive hthreshold depth) := by
              rfl
        _ = BK15.Threshold.bk15Iteration
            (BK15.Threshold.bk15HInputError rho) (depth + 1) := hacceptedError
        _ ≤ BK15.Threshold.bk15Iteration
            (BK15.Threshold.bk15HInputError rho) depth :=
          BK15.Threshold.bk15Iteration_antitone
            (BK15.Threshold.bk15HInputError rho) hpositive hthreshold
            (Nat.le_succ depth)
        _ < delta := hdepth
    have hrefError : 1 - projectionSquaredOverlap (hProjector hReference)
        (BK15.Threshold.bk15AcceptedRunHOutput rho (depth + 1)) < delta := by
      rw [BK15.Threshold.bk15AcceptedRunHOutput_succ_eq_semanticSchedule
        rho hpositive hthreshold depth,
        BK15.Threshold.sourceAReturnedH_referenceSquaredOverlap]
      simpa [BK15.NoisyInput.aInputError] using hrootError
    have hsqrt : Real.sqrt delta = eta / 8 := by
      rw [show delta = (eta / 8) ^ 2 by rfl, Real.sqrt_sq_eq_abs,
        abs_of_pos (by positivity)]
    have htrace : traceNorm
        ((BK15.Threshold.bk15AcceptedRunHOutput rho (depth + 1)).toOperator -
          hMagicState.toOperator) < eta := by
      calc
        traceNorm
            ((BK15.Threshold.bk15AcceptedRunHOutput rho (depth + 1)).toOperator -
              hMagicState.toOperator) ≤
            4 * Real.sqrt
              (1 - projectionSquaredOverlap (hProjector hReference)
                (BK15.Threshold.bk15AcceptedRunHOutput rho (depth + 1))) :=
          qubit_traceNorm_sub_fixedPure_le_four_sqrt_infidelity _
        _ ≤ 4 * Real.sqrt delta :=
          mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt (le_of_lt hrefError)) (by norm_num)
        _ = eta / 2 := by rw [hsqrt]; ring
        _ < eta := by linarith
    have hrealization := BK15.Threshold.bk15SemanticSchedule_realizesRun
      rho hpositive hthreshold depth
    refine ⟨depth + 1, htrace, Or.inr ⟨hpositive, hthreshold, depth, rfl,
      BK15.Threshold.bk15SemanticSchedule_leafCount rho hpositive hthreshold
        (depth + 1), hrealization.2.1, hrealization.2.2.1,
      hrealization.2.2.2, ?_⟩⟩
    exact BK15.Threshold.bk15AcceptedRunHOutput_succ_eq_semanticSchedule
      rho hpositive hthreshold depth

/-!
Task 4 keeps the physical retry semantics local to #459.  In particular,
`AdaptiveProgram` is deliberately not used here: phase injection grows the
one-qubit data register to the concrete two-qubit injection register, and its
conditional-density semantics would remove zero-weight outcomes.  The carrier
below therefore records unnormalised operators for every syntactic outcome.
-/

open AdaptiveIdealClifford PhaseInjection

/- Exact ideal-resource facts consumed by the raw physical retry construction:
the accepted T pair really is the displayed phase resource up to a unit phase,
and both finite stopped walks retain their source-proved exponential tails. -/
private theorem sourceT_and_stopping_source_handoff
    (blocks : Nat) (startEight targetEight : ZMod 8)
    (startTwelve targetTwelve : ZMod 12)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (OneQubitMagic.hadamardOperator OneQubitMagic.sourceTEvenFirstQubit =
        OneQubitMagic.sourceTGlobalPhase •
          OneQubitMagic.phaseState (-Real.pi / 6)) ∧
    ‖OneQubitMagic.sourceTGlobalPhase‖ = 1 ∧
    phaseInjectionStoppingMissMass (blocks := blocks)
        startEight targetEight psi hpsi ≤ (255 / 256 : Real) ^ blocks ∧
    phaseInjectionStoppingMissMass (blocks := blocks)
        startTwelve targetTwelve psi hpsi ≤ (4095 / 4096 : Real) ^ blocks := by
  exact ⟨OneQubitMagic.sourceTEvenOutput_global_phase,
    OneQubitMagic.sourceTGlobalPhase_norm,
    phaseInjectionStoppingMissMass_eight_exponential_bound
      blocks startEight targetEight psi hpsi,
    phaseInjectionStoppingMissMass_twelve_exponential_bound
      blocks startTwelve targetTwelve psi hpsi⟩

private theorem phaseInjectionStoppingTrace_target_handoff
    {q blocks : Nat} [NeZero q]
    (target : ZMod q) (trace : PhaseRetry.BlockTrace q blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hvisit : PhaseRetry.traceVisitsTarget (0 : ZMod q) target blocks trace) :
    (phaseInjectionStoppingTrace (0 : ZMod q) target trace psi hpsi).1 =
      phaseInjectionHistoryGlobalPhase (phaseCycleAngle q)
          (stoppingHistory (0 : ZMod q) target
            (retryTraceCoins blocks trace)) •
        phaseCycleTargetAction q target psi :=
  phaseInjectionStoppingTrace_output_target_of_visit
    target trace psi hpsi hvisit

/-- Tokens debited by the #459-local raw H/T retry trees. -/
inductive BK05ResourceToken
  | h
  | t
deriving DecidableEq

/-- Every terminal physical reason remains visible in the raw retry tree. -/
inductive BK05RawLeafKind
  | targetHit
  | phaseExhausted
  | tPairExhausted
deriving DecidableEq

/-- An unnormalised terminal branch together with its literal resource ledger. -/
structure BK05RawLeaf where
  kind : BK05RawLeafKind
  history : List Bool
  ledger : ResourceLedger BK05ResourceToken
  raw : Operator QubitSpace

/-- The real trace mass of a raw terminal branch. -/
def rawWeight (leaf : BK05RawLeaf) : Real :=
  (LinearMap.trace Complex QubitSpace leaf.raw).re

/-- Total raw trace mass, including algebraically zero and exhausted leaves. -/
def rawMass (leaves : List BK05RawLeaf) : Real :=
  (leaves.map rawWeight).sum

/-- The unconditioned operator obtained by summing every retained leaf. -/
def rawAggregate (leaves : List BK05RawLeaf) : Operator QubitSpace :=
  (leaves.map BK05RawLeaf.raw).sum

/-- The retained raw trace mass of leaves with one literal terminal reason. -/
def rawMassOfKind (kind : BK05RawLeafKind) (leaves : List BK05RawLeaf) : Real :=
  rawMass (leaves.filter fun leaf => leaf.kind == kind)

/-- Tensor a data operator with the supplied phase resource and enter the
literal two-qubit injection coordinates. -/
def injectedInputRaw (data resource : Operator QubitSpace) :
    Operator TwoQubit.TwoQubitSpace :=
  TwoQubit.tensorRegisterTransport.conjOperator
    (TensorProduct.map data resource)

/-- One raw, measured phase-injection branch followed by the real XOR/discard
postprocessing channel. -/
def phaseBranchRaw (resource data : Operator QubitSpace) (coin : Bool) :
    Operator QubitSpace :=
  oneShotPostprocess
    (zzMeasurement.instrument.branchOperator (observedRetrySyndrome coin)
      (injectedInputRaw data resource))

/-- The actual H-resource frame used by an H injection. -/
def hPhaseRaw (h : DensityOperator QubitSpace) : Operator QubitSpace :=
  hResourceTransport.conjOperator h.toOperator

/-- One raw H-resource injection outcome. -/
def hStepRaw (h : DensityOperator QubitSpace) (coin : Bool)
    (data : Operator QubitSpace) : Operator QubitSpace :=
  phaseBranchRaw (hPhaseRaw h) data coin

/-- The two actual T resources, in the concrete two-qubit source register. -/
def tPairInputRaw (t : DensityOperator QubitSpace) :
    Operator TwoQubit.TwoQubitSpace :=
  TwoQubit.tensorRegisterTransport.conjOperator
    (TensorProduct.map t.toOperator t.toOperator)

/-- A raw accepted or rejected source-T pair outcome. -/
def tPairBranchRaw (t : DensityOperator QubitSpace) (coin : Bool) :
    Operator TwoQubit.TwoQubitSpace :=
  zzMeasurement.instrument.branchOperator (observedRetrySyndrome coin)
    (tPairInputRaw t)

/-- The accepted source-T pair becomes a phase resource only through its
actual parity branch, XOR/discard, and Hadamard channel. -/
def tAcceptedPhaseRaw (t : DensityOperator QubitSpace) : Operator QubitSpace :=
  (QuantumChannel.unitaryConj hadamardTransport)
    (oneShotPostprocess (tPairBranchRaw t true))

/-- On rejection the complete two-T resource is the right factor and is
discarded by the real partial-trace channel before a fresh pair is tried. -/
def tRejectedDataRaw (data : Operator QubitSpace)
    (t : DensityOperator QubitSpace) : Operator QubitSpace :=
  partialTraceRightRaw QubitSpace TwoQubit.TwoQubitSpace
    (TensorProduct.map data (tPairBranchRaw t false))

/-- The two Boolean retry labels enumerate exactly the two syndromes of the
single concrete ZZ check. -/
private theorem retrySyndrome_univ :
    (Finset.univ : Finset (JointSyndrome (Fin 1))) =
      {observedRetrySyndrome true, observedRetrySyndrome false} := by
  ext syndrome
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton]
  have hcases : syndrome = observedRetrySyndrome true ∨
      syndrome = observedRetrySyndrome false := by
    cases h : syndrome 0 with
    | positive =>
        left
        funext i
        fin_cases i
        simpa [observedRetrySyndrome, observedRetryOutcome, h]
    | negative =>
        right
        funext i
        fin_cases i
        simpa [observedRetrySyndrome, observedRetryOutcome, h]
  constructor
  · intro _
    exact hcases
  · intro _
    trivial

private theorem observedRetrySyndromes_ne :
    observedRetrySyndrome true ≠ observedRetrySyndrome false := by
  intro h
  have hzero := congrFun h 0
  simp [observedRetrySyndrome, observedRetryOutcome] at hzero

/-- The actual one-shot instrument and its trace-preserving postprocess split
the raw trace exactly over the two visible Boolean outcomes. -/
private theorem phaseBranchRaw_trace_sum
    (resource data : Operator QubitSpace) :
    LinearMap.trace Complex QubitSpace (phaseBranchRaw resource data true) +
      LinearMap.trace Complex QubitSpace (phaseBranchRaw resource data false) =
      LinearMap.trace Complex QubitSpace data *
        LinearMap.trace Complex QubitSpace resource := by
  let input := injectedInputRaw data resource
  have hbranches :
      zzMeasurement.instrument.branchOperator (observedRetrySyndrome true) input +
        zzMeasurement.instrument.branchOperator (observedRetrySyndrome false) input =
          zzMeasurement.instrument.kraus.inducedMap input := by
    have hnotmem : observedRetrySyndrome true ∉
        ({observedRetrySyndrome false} : Finset (JointSyndrome (Fin 1))) := by
      intro hmem
      exact observedRetrySyndromes_ne (by simpa using hmem)
    rw [← zzMeasurement.instrument.sum_branchOperator_eq_inducedMap, retrySyndrome_univ,
      Finset.sum_insert hnotmem, Finset.sum_singleton]
  calc
    LinearMap.trace Complex QubitSpace (phaseBranchRaw resource data true) +
        LinearMap.trace Complex QubitSpace (phaseBranchRaw resource data false) =
        LinearMap.trace Complex TwoQubit.TwoQubitSpace
          (zzMeasurement.instrument.branchOperator (observedRetrySyndrome true) input) +
          LinearMap.trace Complex TwoQubit.TwoQubitSpace
            (zzMeasurement.instrument.branchOperator (observedRetrySyndrome false) input) := by
          simp [phaseBranchRaw, input, oneShotPostprocess.trace_map]
    _ = LinearMap.trace Complex TwoQubit.TwoQubitSpace
          (zzMeasurement.instrument.kraus.inducedMap input) := by
          rw [← map_add, hbranches]
    _ = LinearMap.trace Complex TwoQubit.TwoQubitSpace input := by
          exact zzMeasurement.instrument.kraus.inducedMap_trace_preserving
            (jointStabilizerKrausFamily_complete zzMeasurement.checks zzMeasurement.commute) input
    _ = LinearMap.trace Complex QubitSpace data *
        LinearMap.trace Complex QubitSpace resource := by
          simp [input, injectedInputRaw, UnitaryTransport.trace_conjOperator,
            LinearMap.trace_tensorProduct']

/-- The rejected source-T branch is discarded as a complete two-qubit right
factor.  This local trace-pairing proof rules out a one-qubit or normalized
postselection surrogate. -/
theorem tRejectedDataRaw_discardsFullPair (data : Operator QubitSpace)
    (t : DensityOperator QubitSpace) :
    tRejectedDataRaw data t =
      (LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t false)) • data := by
  apply Semantics.operator_ext_of_trace_comp_right_eq
  intro X
  let basis : OrthonormalBasis
      (ULift (Fin (Module.finrank Complex TwoQubit.TwoQubitSpace))) Complex
        TwoQubit.TwoQubitSpace :=
    (stdOrthonormalBasis Complex TwoQubit.TwoQubitSpace).reindex Equiv.ulift.symm
  calc
    LinearMap.trace Complex QubitSpace (X.comp (tRejectedDataRaw data t)) =
        LinearMap.trace Complex QubitSpace ((tRejectedDataRaw data t).comp X) :=
      (LinearMap.trace_comp_comm' X (tRejectedDataRaw data t)).symm
    _ = LinearMap.trace Complex (CompositeSystem QubitSpace TwoQubit.TwoQubitSpace)
        ((TensorProduct.map data (tPairBranchRaw t false)).comp
          (TensorProduct.map X (LinearMap.id : TwoQubit.TwoQubitSpace →ₗ[Complex]
            TwoQubit.TwoQubitSpace))) := by
          exact Semantics.FiniteMatrixEntropy.partialTraceRightRaw_trace_pairing basis
            (TensorProduct.map data (tPairBranchRaw t false)) X
    _ = LinearMap.trace Complex QubitSpace
        (((LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t false)) • data).comp X) := by
          rw [← TensorProduct.map_comp, LinearMap.trace_tensorProduct']
          simp [LinearMap.smul_comp]
          ring
    _ = LinearMap.trace Complex QubitSpace
        (X.comp ((LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t false)) • data)) :=
      LinearMap.trace_comp_comm' X _

private theorem injectedInputRaw_positive (data resource : Operator QubitSpace)
    (hdata : LinearMap.IsPositive data) (hresource : LinearMap.IsPositive resource) :
    LinearMap.IsPositive (injectedInputRaw data resource) := by
  unfold injectedInputRaw
  apply TwoQubit.tensorRegisterTransport.isPositive_conjOperator
  exact ThermalEncoding.tensorMap_positive data resource hdata hresource

private theorem phaseBranchRaw_positive (resource data : Operator QubitSpace)
    (hresource : LinearMap.IsPositive resource) (hdata : LinearMap.IsPositive data)
    (coin : Bool) :
    LinearMap.IsPositive (phaseBranchRaw resource data coin) := by
  unfold phaseBranchRaw
  apply oneShotPostprocess.map_positive
  apply zzMeasurement.instrument.branchOperator_positive
  exact injectedInputRaw_positive data resource hdata hresource

private theorem hPhaseRaw_positive (h : DensityOperator QubitSpace) :
    LinearMap.IsPositive (hPhaseRaw h) := by
  unfold hPhaseRaw
  exact hResourceTransport.isPositive_conjOperator h.positive

private theorem hStepRaw_positive (h : DensityOperator QubitSpace) (coin : Bool)
    (data : Operator QubitSpace) (hdata : LinearMap.IsPositive data) :
    LinearMap.IsPositive (hStepRaw h coin data) := by
  exact phaseBranchRaw_positive (hPhaseRaw h) data (hPhaseRaw_positive h) hdata coin

private theorem tPairInputRaw_positive (t : DensityOperator QubitSpace) :
    LinearMap.IsPositive (tPairInputRaw t) := by
  unfold tPairInputRaw
  apply TwoQubit.tensorRegisterTransport.isPositive_conjOperator
  exact ThermalEncoding.tensorMap_positive t.toOperator t.toOperator t.positive t.positive

private theorem tPairBranchRaw_positive (t : DensityOperator QubitSpace) (coin : Bool) :
    LinearMap.IsPositive (tPairBranchRaw t coin) := by
  unfold tPairBranchRaw
  apply zzMeasurement.instrument.branchOperator_positive
  exact tPairInputRaw_positive t

private theorem tAcceptedPhaseRaw_positive (t : DensityOperator QubitSpace) :
    LinearMap.IsPositive (tAcceptedPhaseRaw t) := by
  unfold tAcceptedPhaseRaw
  apply (QuantumChannel.unitaryConj hadamardTransport).map_positive
  apply oneShotPostprocess.map_positive
  exact tPairBranchRaw_positive t true

private theorem tRejectedDataRaw_positive (data : Operator QubitSpace)
    (t : DensityOperator QubitSpace) (hdata : LinearMap.IsPositive data) :
    LinearMap.IsPositive (tRejectedDataRaw data t) := by
  unfold tRejectedDataRaw
  change LinearMap.IsPositive
    ((partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace).toLinearMap
      (TensorProduct.map data (tPairBranchRaw t false)))
  apply (partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace).map_positive
  exact ThermalEncoding.tensorMap_positive data (tPairBranchRaw t false) hdata
    (tPairBranchRaw_positive t false)

/-- Tensoring on a fixed data density is a concrete CPTP preparation followed
by a factor swap, and hence cannot increase the trace norm of a self-adjoint
resource difference. -/
private theorem traceNorm_tensor_left_resource_le
    (resource ideal data : DensityOperator QubitSpace) :
    traceNorm
      (TensorProduct.map resource.toOperator data.toOperator -
        TensorProduct.map ideal.toOperator data.toOperator) ≤
      traceNorm (resource.toOperator - ideal.toOperator) := by
  let Phi : QuantumChannel QubitSpace (CompositeSystem QubitSpace QubitSpace) :=
    ThermalEncoding.prepareRight QubitSpace QubitSpace data
  have hPhi (sigma : DensityOperator QubitSpace) :
      Phi sigma.toOperator = TensorProduct.map sigma.toOperator data.toOperator := by
    exact ThermalEncoding.prepareRight_apply QubitSpace QubitSpace data sigma.toOperator
  have hsym : (resource.toOperator - ideal.toOperator).IsSymmetric :=
    resource.positive.isSymmetric.sub ideal.positive.isSymmetric
  calc
    traceNorm
        (TensorProduct.map resource.toOperator data.toOperator -
          TensorProduct.map ideal.toOperator data.toOperator) =
        traceNorm (Phi (resource.toOperator - ideal.toOperator)) := by
          rw [map_sub, hPhi resource, hPhi ideal]
    _ ≤ traceNorm (resource.toOperator - ideal.toOperator) :=
      Phi.traceNorm_apply_le_of_isSymmetric _ hsym

/-- Tensoring on a fixed data density is a concrete CPTP preparation followed
by a factor swap, and hence cannot increase the trace norm of a self-adjoint
resource difference. -/
theorem traceNorm_tensor_right_resource_le
    (data resource ideal : DensityOperator QubitSpace) :
    traceNorm
      (TensorProduct.map data.toOperator resource.toOperator -
        TensorProduct.map data.toOperator ideal.toOperator) ≤
      traceNorm (resource.toOperator - ideal.toOperator) := by
  let Phi : QuantumChannel QubitSpace (CompositeSystem QubitSpace QubitSpace) :=
    QuantumChannel.comp
      (QuantumChannel.unitaryConj (DensityOperator.tensorSwap QubitSpace QubitSpace))
      (ThermalEncoding.prepareRight QubitSpace QubitSpace data)
  have hPhi (sigma : DensityOperator QubitSpace) :
      Phi sigma.toOperator = TensorProduct.map data.toOperator sigma.toOperator := by
    change (DensityOperator.tensorSwap QubitSpace QubitSpace).conjOperator
        ((ThermalEncoding.prepareRight QubitSpace QubitSpace data) sigma.toOperator) = _
    rw [ThermalEncoding.prepareRight_apply]
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [Phi, ThermalEncoding.prepareRight_apply]
    | tmul x y =>
        have hinv :
            (DensityOperator.tensorSwap QubitSpace QubitSpace).toLinearEquiv.symm
                (x ⊗ₜ[Complex] y) = y ⊗ₜ[Complex] x := by
          apply (DensityOperator.tensorSwap QubitSpace QubitSpace).toLinearEquiv.injective
          simp
        change (DensityOperator.tensorSwap QubitSpace QubitSpace).toLinearEquiv
            ((TensorProduct.map sigma.toOperator data.toOperator)
              ((DensityOperator.tensorSwap QubitSpace QubitSpace).toLinearEquiv.symm
                (x ⊗ₜ[Complex] y))) = _
        rw [hinv]
        simp [TensorProduct.map_tmul]
    | add x y hx hy => simp [map_add, hx, hy]
  have hsym : (resource.toOperator - ideal.toOperator).IsSymmetric :=
    resource.positive.isSymmetric.sub ideal.positive.isSymmetric
  calc
    traceNorm
        (TensorProduct.map data.toOperator resource.toOperator -
          TensorProduct.map data.toOperator ideal.toOperator) =
        traceNorm (Phi (resource.toOperator - ideal.toOperator)) := by
          rw [map_sub, hPhi resource, hPhi ideal]
    _ ≤ traceNorm (resource.toOperator - ideal.toOperator) :=
      Phi.traceNorm_apply_le_of_isSymmetric _ hsym

/-- Replacing both members of a T-resource pair costs at most two copies of
the one-resource trace distance, by a two-term tensor telescope. -/
theorem traceNorm_tensor_pair_resource_le
    (resource ideal : DensityOperator QubitSpace) :
    traceNorm
      (TensorProduct.map resource.toOperator resource.toOperator -
        TensorProduct.map ideal.toOperator ideal.toOperator) ≤
      2 * traceNorm (resource.toOperator - ideal.toOperator) := by
  calc
    traceNorm
        (TensorProduct.map resource.toOperator resource.toOperator -
          TensorProduct.map ideal.toOperator ideal.toOperator) =
        traceNorm
          ((TensorProduct.map resource.toOperator resource.toOperator -
            TensorProduct.map ideal.toOperator resource.toOperator) +
            (TensorProduct.map ideal.toOperator resource.toOperator -
              TensorProduct.map ideal.toOperator ideal.toOperator)) := by
          congr 1
          module
    _ ≤ traceNorm
          (TensorProduct.map resource.toOperator resource.toOperator -
            TensorProduct.map ideal.toOperator resource.toOperator) +
        traceNorm
          (TensorProduct.map ideal.toOperator resource.toOperator -
            TensorProduct.map ideal.toOperator ideal.toOperator) :=
      traceNorm_add_le _ _
    _ ≤ traceNorm (resource.toOperator - ideal.toOperator) +
        traceNorm (resource.toOperator - ideal.toOperator) := by
      apply add_le_add
      · exact traceNorm_tensor_left_resource_le resource ideal resource
      · exact traceNorm_tensor_right_resource_le ideal resource ideal
    _ = 2 * traceNorm (resource.toOperator - ideal.toOperator) := by ring

/-- A finite H retry tree that retains both physical parity outcomes without a
positive-weight side condition. -/
def hRetry {q : Nat} (h : DensityOperator QubitSpace) (target : ZMod q)
    (remaining : Nat) (position : ZMod q)
    (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
    (data : Operator QubitSpace) : List BK05RawLeaf :=
  if position = target then
    [⟨.targetHit, history, ledger, data⟩]
  else match remaining with
  | 0 => [⟨.phaseExhausted, history, ledger, data⟩]
  | n + 1 =>
      let nextLedger := ledger + ({.h} : ResourceLedger BK05ResourceToken)
      hRetry h target n (position + 1) nextLedger (true :: history)
          (hStepRaw h true data)
        ++
      hRetry h target n (position - 1) nextLedger (false :: history)
          (hStepRaw h false data)
termination_by remaining

/-- A raw outcome of one bounded fresh-T-pair supplier.  The accepted case
keeps both the accumulated raw data and the actual accepted phase resource;
the exhausted case carries its unnormalised data forward as a real leaf. -/
inductive BK05TSupplyOutcome where
  | accepted (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
      (data phaseResource : Operator QubitSpace) : BK05TSupplyOutcome
  | exhausted (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
      (data : Operator QubitSpace) : BK05TSupplyOutcome

/-- A syntactically complete bounded supplier.  Rejection first discards the
full two-qubit pair and then calls itself with a strictly smaller fresh-pair
budget; no pair is reused. -/
def tSupply (t : DensityOperator QubitSpace) (pairAttempts : Nat)
    (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
    (data : Operator QubitSpace) : List BK05TSupplyOutcome :=
  match pairAttempts with
  | 0 => [.exhausted ledger history data]
  | m + 1 =>
      let nextLedger := ledger + ({.t, .t} : ResourceLedger BK05ResourceToken)
      .accepted nextLedger (true :: history) data (tAcceptedPhaseRaw t)
        ::
      tSupply t m nextLedger (false :: history) (tRejectedDataRaw data t)
termination_by pairAttempts

/-- A finite T retry tree.  Each nonterminal phase attempt calls a new bounded
supplier; accepted suppliers enter both physical phase outcomes, whereas each
exhausted supplier remains an explicit terminal leaf. -/
def tRetry {q : Nat} (t : DensityOperator QubitSpace) (pairAttempts : Nat)
    (target : ZMod q) (remaining : Nat) (position : ZMod q)
    (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
    (data : Operator QubitSpace) : List BK05RawLeaf :=
  if position = target then
    [⟨.targetHit, history, ledger, data⟩]
  else match remaining with
  | 0 => [⟨.phaseExhausted, history, ledger, data⟩]
  | n + 1 =>
      (tSupply t pairAttempts ledger history data).flatMap fun supplied =>
        match supplied with
        | .accepted nextLedger nextHistory nextData phaseResource =>
            tRetry t pairAttempts target n (position + 1) nextLedger
                (true :: nextHistory) (phaseBranchRaw phaseResource nextData true)
              ++
            tRetry t pairAttempts target n (position - 1) nextLedger
                (false :: nextHistory) (phaseBranchRaw phaseResource nextData false)
        | .exhausted nextLedger nextHistory nextData =>
            [⟨.tPairExhausted, nextHistory, nextLedger, nextData⟩]
termination_by remaining

/-- The complete finite H retry tree uses the exact order-eight phase budget. -/
def hActualRawTree (h : DensityOperator QubitSpace) (target : ZMod 8)
    (blocks : Nat) (rho : DensityOperator QubitSpace) : List BK05RawLeaf :=
  hRetry h target (8 * blocks) 0 0 [] rho.toOperator

/-- The complete finite T retry tree supplies a fresh bounded pair tree at
every order-twelve phase attempt. -/
def tActualRawTree (t : DensityOperator QubitSpace) (pairAttempts : Nat)
    (target : ZMod 12) (blocks : Nat) (rho : DensityOperator QubitSpace) :
    List BK05RawLeaf :=
  tRetry t pairAttempts target (12 * blocks) 0 0 [] rho.toOperator

/-- Algebraically zero operators are not filtered by a positivity predicate:
once a zero raw leaf belongs to either literal first H branch, the root tree
retains it.  The target/budget assumptions are exactly the conditions under
which the first physical measurement is reached. -/
theorem rawRetryTree_retainsAlgebraicZeroLeaf
    (h : DensityOperator QubitSpace) (target : ZMod 8) (blocks : Nat)
    (rho : DensityOperator QubitSpace) :
    (0 : ZMod 8) ≠ target → 0 < blocks →
      ∀ (coin : Bool) (leaf : BK05RawLeaf),
        leaf ∈ hRetry h target (8 * blocks - 1)
          (if coin then 1 else -1) ({.h} : ResourceLedger BK05ResourceToken)
          [coin] (hStepRaw h coin rho.toOperator) →
        leaf.raw = 0 → leaf ∈ hActualRawTree h target blocks rho := by
  intro htarget hblocks coin leaf hmem hzero
  have hremaining : 8 * blocks = (8 * blocks - 1) + 1 := by omega
  rw [hActualRawTree, hremaining, hRetry, if_neg htarget]
  cases coin
  · exact List.mem_append_right _ (by simpa using hmem)
  · exact List.mem_append_left _ (by simpa using hmem)

/-- Away from the immediate target and with a nonzero phase budget, the raw H
tree is literally the appended positive and complementary negative branches.
This is a conditional structural statement because `target = 0` or a zero
budget legitimately stops before either branch is attempted. -/
theorem hActualRawTree_retainsComplementLeaf
    (h : DensityOperator QubitSpace) (target : ZMod 8) (blocks : Nat)
    (rho : DensityOperator QubitSpace)
    (htarget : (0 : ZMod 8) ≠ target) (hblocks : 0 < blocks) :
    hActualRawTree h target blocks rho =
      hRetry h target (8 * blocks - 1) 1 ({.h} : ResourceLedger BK05ResourceToken)
        [true] (hStepRaw h true rho.toOperator)
      ++
      hRetry h target (8 * blocks - 1) (-1) ({.h} : ResourceLedger BK05ResourceToken)
        [false] (hStepRaw h false rho.toOperator) := by
  have hremaining : 8 * blocks = (8 * blocks - 1) + 1 := by omega
  rw [hActualRawTree, hremaining, hRetry, if_neg htarget]
  simp

/-- The H retry ledger is computed by the recursion: each nonterminal split
adds one H token and no caller supplies a resource count. -/
private theorem hRetry_ledger_card_le {q : Nat}
    (h : DensityOperator QubitSpace) (target : ZMod q) (remaining : Nat) :
    ∀ (position : ZMod q) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace) (leaf : BK05RawLeaf),
      leaf ∈ hRetry h target remaining position ledger history data →
        leaf.ledger.card ≤ ledger.card + remaining := by
  induction remaining with
  | zero =>
      intro position ledger history data leaf hmem
      by_cases htarget : position = target
      · simp [hRetry, htarget] at hmem
        subst leaf
        rfl
      · simp [hRetry, htarget] at hmem
        subst leaf
        rfl
  | succ remaining ih =>
      intro position ledger history data leaf hmem
      by_cases htarget : position = target
      · simp [hRetry, htarget] at hmem
        subst leaf
        change ledger.card ≤ ledger.card + (remaining + 1)
        omega
      · simp only [hRetry, if_neg htarget, List.mem_append] at hmem
        let nextLedger := ledger + ({.h} : ResourceLedger BK05ResourceToken)
        rcases hmem with hmem | hmem
        · have hle := ih (position + 1) nextLedger (true :: history)
              (hStepRaw h true data) leaf (by simpa [nextLedger] using hmem)
          dsimp [nextLedger] at hle
          simp only [Multiset.card_add, Multiset.card_singleton] at hle
          omega
        · have hle := ih (position - 1) nextLedger (false :: history)
              (hStepRaw h false data) leaf (by simpa [nextLedger] using hmem)
          dsimp [nextLedger] at hle
          simp only [Multiset.card_add, Multiset.card_singleton] at hle
          omega

/-- Every retained H leaf consumes no more than the computed order-eight
phase budget. -/
theorem hActualRawTree_ledger_le
    (h : DensityOperator QubitSpace) (target : ZMod 8) (blocks : Nat)
    (rho : DensityOperator QubitSpace) (leaf : BK05RawLeaf)
    (hmem : leaf ∈ hActualRawTree h target blocks rho) :
    leaf.ledger.card ≤ 8 * blocks := by
  simpa [hActualRawTree] using
    hRetry_ledger_card_le h target (8 * blocks) 0 0 [] rho.toOperator leaf hmem

/-- Every nonzero fresh-pair budget starts with an accepted supplier outcome
whose ledger debits exactly the two physical T resources.  Rejected branches
are handled recursively after full-pair discard. -/
theorem tSupply_freshPair_ledger_increment
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (blocks : Nat) (rho : DensityOperator QubitSpace) (hpositive : 0 < pairAttempts) :
    ∃ history data phaseResource,
      BK05TSupplyOutcome.accepted ({.t, .t} : ResourceLedger BK05ResourceToken)
        history data phaseResource ∈ tSupply t pairAttempts 0 [] rho.toOperator := by
  cases pairAttempts with
  | zero => omega
  | succ attempts =>
      refine ⟨[true], rho.toOperator, tAcceptedPhaseRaw t, ?_⟩
      simp [tSupply]

private theorem replicate_false_append_cons (attempts : Nat) (history : List Bool) :
    List.replicate attempts false ++ false :: history =
      false :: List.replicate attempts false ++ history := by
  induction attempts with
  | zero => simp
  | succ attempts ih =>
      simp [List.replicate_succ, ih, List.cons_append]

/-- The finite supplier retains its literal all-rejected exhaustion outcome.
Its history records every `false` pair outcome and its ledger cardinality is
the exact debit of the corresponding complete T pairs. -/
private theorem tSupply_retainsAllRejected
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) :
    ∀ (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
      (data : Operator QubitSpace),
      ∃ nextLedger nextData,
        BK05TSupplyOutcome.exhausted nextLedger
            (List.replicate pairAttempts false ++ history) nextData ∈
          tSupply t pairAttempts ledger history data ∧
        nextLedger.card = ledger.card + 2 * pairAttempts := by
  induction pairAttempts with
  | zero =>
      intro ledger history data
      refine ⟨ledger, data, ?_, ?_⟩
      · simp [tSupply]
      · omega
  | succ attempts ih =>
      intro ledger history data
      let nextLedger := ledger + ({.t, .t} : ResourceLedger BK05ResourceToken)
      obtain ⟨lastLedger, lastData, hlast, hcard⟩ :=
        ih nextLedger (false :: history) (tRejectedDataRaw data t)
      refine ⟨lastLedger, lastData, ?_, ?_⟩
      · rw [replicate_false_append_cons attempts history] at hlast
        simpa [tSupply, nextLedger, List.replicate_succ, List.cons_append] using hlast
      · dsimp [nextLedger] at hcard
        simp [Multiset.card_add] at hcard
        omega

/-- If the first physical T phase attempt is reached, the bounded supplier's
all-rejected outcome becomes a retained `tPairExhausted` leaf.  The target and
zero-block cases are deliberately excluded because they stop before a pair is
requested. -/
theorem tActualRawTree_retainsRejectedPairLeaf
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (blocks : Nat) (rho : DensityOperator QubitSpace)
    (htarget : (0 : ZMod 12) ≠ target) (hblocks : 0 < blocks) :
    pairAttempts = 0 ∨
      (0 < pairAttempts →
        ∃ leaf ∈ tActualRawTree t pairAttempts target blocks rho,
          leaf.kind = .tPairExhausted ∧
          leaf.ledger.card = 2 * pairAttempts ∧
          List.replicate pairAttempts false = leaf.history ∧ false ∈ leaf.history) := by
  cases pairAttempts with
  | zero => exact Or.inl rfl
  | succ attempts =>
      right
      intro hpositive
      obtain ⟨lastLedger, lastData, hlast, hcard⟩ :=
        tSupply_retainsAllRejected t (attempts + 1) 0 [] rho.toOperator
      refine ⟨⟨.tPairExhausted, List.replicate (attempts + 1) false,
          lastLedger, lastData⟩, ?_, rfl, ?_, rfl, ?_⟩
      · have hremaining : 12 * blocks = (12 * blocks - 1) + 1 := by omega
        rw [tActualRawTree, hremaining, tRetry, if_neg htarget]
        apply List.mem_flatMap.2
        refine ⟨.exhausted lastLedger (List.replicate (attempts + 1) false)
          lastData, ?_, ?_⟩
        · simpa using hlast
        · simp
      · simpa using hcard
      · simpa using hpositive

/-- List mass is additive before any retry-specific reasoning. -/
private theorem rawMass_append (left right : List BK05RawLeaf) :
    rawMass (left ++ right) = rawMass left + rawMass right := by
  simp [rawMass]

private theorem rawMass_single (leaf : BK05RawLeaf) :
    rawMass [leaf] = rawWeight leaf := by
  simp [rawMass]

private theorem hPhaseRaw_trace_one (h : DensityOperator QubitSpace) :
    LinearMap.trace Complex QubitSpace (hPhaseRaw h) = 1 := by
  rw [hPhaseRaw, UnitaryTransport.trace_conjOperator, h.trace_one]

private theorem tPairBranchRaw_trace_sum (t : DensityOperator QubitSpace) :
    LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t true) +
        LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t false) = 1 := by
  let input := tPairInputRaw t
  have hbranches :
      zzMeasurement.instrument.branchOperator (observedRetrySyndrome true) input +
        zzMeasurement.instrument.branchOperator (observedRetrySyndrome false) input =
          zzMeasurement.instrument.kraus.inducedMap input := by
    have hnotmem : observedRetrySyndrome true ∉
        ({observedRetrySyndrome false} : Finset (JointSyndrome (Fin 1))) := by
      intro hmem
      exact observedRetrySyndromes_ne (by simpa using hmem)
    rw [← zzMeasurement.instrument.sum_branchOperator_eq_inducedMap, retrySyndrome_univ,
      Finset.sum_insert hnotmem, Finset.sum_singleton]
  calc
    LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t true) +
        LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t false) =
        LinearMap.trace Complex TwoQubit.TwoQubitSpace
          (zzMeasurement.instrument.kraus.inducedMap input) := by
            rw [← map_add]
            change
              LinearMap.trace Complex TwoQubit.TwoQubitSpace
                (zzMeasurement.instrument.branchOperator (observedRetrySyndrome true) input +
                  zzMeasurement.instrument.branchOperator (observedRetrySyndrome false) input) = _
            rw [hbranches]
    _ = LinearMap.trace Complex TwoQubit.TwoQubitSpace input := by
          exact zzMeasurement.instrument.kraus.inducedMap_trace_preserving
            (jointStabilizerKrausFamily_complete zzMeasurement.checks zzMeasurement.commute) input
    _ = 1 := by
          simp [input, tPairInputRaw, UnitaryTransport.trace_conjOperator,
            LinearMap.trace_tensorProduct', t.trace_one]

private theorem tAcceptedPhaseRaw_trace (t : DensityOperator QubitSpace) :
    LinearMap.trace Complex QubitSpace (tAcceptedPhaseRaw t) =
      LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t true) := by
  change
    LinearMap.trace Complex QubitSpace
        (hadamardTransport.conjOperator (oneShotPostprocess (tPairBranchRaw t true))) = _
  rw [UnitaryTransport.trace_conjOperator]
  exact oneShotPostprocess.trace_map _

private theorem tRejectedDataRaw_trace (data : Operator QubitSpace)
    (t : DensityOperator QubitSpace) :
    LinearMap.trace Complex QubitSpace (tRejectedDataRaw data t) =
      LinearMap.trace Complex QubitSpace data *
        LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t false) := by
  rw [tRejectedDataRaw_discardsFullPair, map_smul]
  ring

/-- Complex supplier mass: accepted outcomes carry the phase-resource trace,
whereas exhausted outcomes carry the raw data after complete-pair discard. -/
private def tSupplyWeight : BK05TSupplyOutcome → Complex
  | .accepted _ _ data phaseResource =>
      LinearMap.trace Complex QubitSpace data *
        LinearMap.trace Complex QubitSpace phaseResource
  | .exhausted _ _ data => LinearMap.trace Complex QubitSpace data

private def tSupplyMass (outcomes : List BK05TSupplyOutcome) : Complex :=
  (outcomes.map tSupplyWeight).sum

/-- A bounded fresh-pair supplier conserves complex trace mass.  This is an
induction over the actual accepted/rejected pair instrument, and the rejected
case uses `tRejectedDataRaw_discardsFullPair` rather than a normalized retry. -/
private theorem tSupplyMass_eq_trace (t : DensityOperator QubitSpace)
    (pairAttempts : Nat) :
    ∀ (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
      (data : Operator QubitSpace),
      tSupplyMass (tSupply t pairAttempts ledger history data) =
        LinearMap.trace Complex QubitSpace data := by
  induction pairAttempts with
  | zero =>
      intro ledger history data
      simp [tSupply, tSupplyMass, tSupplyWeight]
  | succ attempts ih =>
      intro ledger history data
      let nextLedger := ledger + ({.t, .t} : ResourceLedger BK05ResourceToken)
      rw [tSupply]
      change
        tSupplyWeight (.accepted nextLedger (true :: history) data (tAcceptedPhaseRaw t)) +
            tSupplyMass (tSupply t attempts nextLedger (false :: history)
              (tRejectedDataRaw data t)) =
          LinearMap.trace Complex QubitSpace data
      simp only [tSupplyWeight]
      rw [ih]
      rw [tAcceptedPhaseRaw_trace, tRejectedDataRaw_trace]
      calc
        LinearMap.trace Complex QubitSpace data *
              LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t true) +
            LinearMap.trace Complex QubitSpace data *
              LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t false) =
            LinearMap.trace Complex QubitSpace data *
              (LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t true) +
                LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t false)) := by
              ring
        _ = LinearMap.trace Complex QubitSpace data * 1 := by
              rw [tPairBranchRaw_trace_sum]
        _ = LinearMap.trace Complex QubitSpace data := by ring

private theorem rawMass_flatMap_eq_tSupplyMass_re
    (outcomes : List BK05TSupplyOutcome) (continuation : BK05TSupplyOutcome → List BK05RawLeaf)
    (hcontinuation : ∀ outcome,
      rawMass (continuation outcome) = (tSupplyWeight outcome).re) :
    rawMass (outcomes.flatMap continuation) = (tSupplyMass outcomes).re := by
  induction outcomes with
  | nil => simp [rawMass, tSupplyMass]
  | cons outcome outcomes ih =>
      rw [List.flatMap_cons, rawMass_append, hcontinuation, ih]
      simp [tSupplyMass]

/-- The complete raw H recursion conserves real trace mass, including every
target, exhaustion, and algebraically zero leaf. -/
private theorem hRetry_rawMass_eq_trace {q : Nat}
    (h : DensityOperator QubitSpace) (target : ZMod q) (remaining : Nat) :
    ∀ (position : ZMod q) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace),
      rawMass (hRetry h target remaining position ledger history data) =
        (LinearMap.trace Complex QubitSpace data).re := by
  induction remaining with
  | zero =>
      intro position ledger history data
      by_cases htarget : position = target
      · simp [hRetry, htarget, rawMass, rawWeight]
      · simp [hRetry, htarget, rawMass, rawWeight]
  | succ remaining ih =>
      intro position ledger history data
      by_cases htarget : position = target
      · simp [hRetry, htarget, rawMass, rawWeight]
      · rw [hRetry, if_neg htarget, rawMass_append]
        rw [ih, ih]
        change
          (LinearMap.trace Complex QubitSpace (hStepRaw h true data)).re +
              (LinearMap.trace Complex QubitSpace (hStepRaw h false data)).re =
            (LinearMap.trace Complex QubitSpace data).re
        change
          (LinearMap.trace Complex QubitSpace
              (phaseBranchRaw (hPhaseRaw h) data true)).re +
              (LinearMap.trace Complex QubitSpace
                (phaseBranchRaw (hPhaseRaw h) data false)).re =
            (LinearMap.trace Complex QubitSpace data).re
        have hsplit := congrArg Complex.re
          (phaseBranchRaw_trace_sum (hPhaseRaw h) data)
        rw [hPhaseRaw_trace_one] at hsplit
        simpa using hsplit

/-- The actual finite H retry tree has total raw mass one. -/
theorem hActualRawTree_totalMass
    (h : DensityOperator QubitSpace) (target : ZMod 8) (blocks : Nat)
    (rho : DensityOperator QubitSpace) :
    rawMass (hActualRawTree h target blocks rho) = 1 := by
  rw [hActualRawTree, hRetry_rawMass_eq_trace, rho.trace_one]
  norm_num

/-- The complete raw T recursion conserves mass through each fresh bounded
supplier.  Every accepted phase branch and every exhausted supplier leaf is
included before the supplier trace conservation theorem is applied. -/
private theorem tRetry_rawMass_eq_trace {q : Nat}
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod q)
    (remaining : Nat) :
    ∀ (position : ZMod q) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace),
      rawMass (tRetry t pairAttempts target remaining position ledger history data) =
        (LinearMap.trace Complex QubitSpace data).re := by
  induction remaining with
  | zero =>
      intro position ledger history data
      by_cases htarget : position = target
      · simp [tRetry, htarget, rawMass, rawWeight]
      · simp [tRetry, htarget, rawMass, rawWeight]
  | succ remaining ih =>
      intro position ledger history data
      by_cases htarget : position = target
      · simp [tRetry, htarget, rawMass, rawWeight]
      · rw [tRetry, if_neg htarget]
        let continuation : BK05TSupplyOutcome → List BK05RawLeaf := fun supplied =>
          match supplied with
          | .accepted nextLedger nextHistory nextData phaseResource =>
              tRetry t pairAttempts target remaining (position + 1) nextLedger
                  (true :: nextHistory) (phaseBranchRaw phaseResource nextData true)
                ++
              tRetry t pairAttempts target remaining (position - 1) nextLedger
                  (false :: nextHistory) (phaseBranchRaw phaseResource nextData false)
          | .exhausted nextLedger nextHistory nextData =>
              [⟨.tPairExhausted, nextHistory, nextLedger, nextData⟩]
        change rawMass ((tSupply t pairAttempts ledger history data).flatMap continuation) = _
        have hcontinuation : ∀ supplied,
            rawMass (continuation supplied) = (tSupplyWeight supplied).re := by
          intro supplied
          cases supplied with
          | accepted nextLedger nextHistory nextData phaseResource =>
              simp only [continuation]
              rw [rawMass_append, ih, ih]
              have hsplit := congrArg Complex.re
                (phaseBranchRaw_trace_sum phaseResource nextData)
              simpa [tSupplyWeight] using hsplit
          | exhausted nextLedger nextHistory nextData =>
              simp [continuation, rawMass, rawWeight, tSupplyWeight]
        calc
          rawMass ((tSupply t pairAttempts ledger history data).flatMap continuation) =
              (tSupplyMass (tSupply t pairAttempts ledger history data)).re :=
            rawMass_flatMap_eq_tSupplyMass_re _ _ hcontinuation
          _ = (LinearMap.trace Complex QubitSpace data).re := by
            rw [tSupplyMass_eq_trace]

/-- The actual finite T retry tree has total raw mass one, including the
all-rejected pair-exhaustion leaves. -/
theorem tActualRawTree_totalMass
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (blocks : Nat) (rho : DensityOperator QubitSpace) :
    rawMass (tActualRawTree t pairAttempts target blocks rho) = 1 := by
  rw [tActualRawTree, tRetry_rawMass_eq_trace, rho.trace_one]
  norm_num

/-- Every actual outcome of one bounded fresh-pair supplier is charged by no
more than its own bounded sequence of complete two-T pair attempts. -/
private theorem tSupply_outcome_ledger_card_le
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) :
    ∀ (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
      (data : Operator QubitSpace) (outcome : BK05TSupplyOutcome),
      outcome ∈ tSupply t pairAttempts ledger history data →
        (match outcome with
          | .accepted nextLedger _ _ _ => nextLedger
          | .exhausted nextLedger _ _ => nextLedger).card ≤
          ledger.card + 2 * pairAttempts := by
  induction pairAttempts with
  | zero =>
      intro ledger history data outcome hmem
      simp [tSupply] at hmem
      subst outcome
      simp
  | succ attempts ih =>
      intro ledger history data outcome hmem
      let nextLedger := ledger + ({.t, .t} : ResourceLedger BK05ResourceToken)
      rw [tSupply] at hmem
      change outcome ∈
        .accepted nextLedger (true :: history) data (tAcceptedPhaseRaw t) ::
          tSupply t attempts nextLedger (false :: history) (tRejectedDataRaw data t) at hmem
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst outcome
        dsimp [nextLedger]
        simp [Multiset.card_add]
        omega
      · have hle := ih nextLedger (false :: history) (tRejectedDataRaw data t) outcome htail
        dsimp [nextLedger] at hle ⊢
        simp [Multiset.card_add] at hle ⊢
        omega

/-- A retained raw T leaf is charged by the actual complete-pair debits of at
most one fresh supplier per phase attempt. -/
private theorem tRetry_ledger_card_le {q : Nat}
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod q)
    (remaining : Nat) :
    ∀ (position : ZMod q) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace) (leaf : BK05RawLeaf),
      leaf ∈ tRetry t pairAttempts target remaining position ledger history data →
        leaf.ledger.card ≤ ledger.card + 2 * pairAttempts * remaining := by
  induction remaining with
  | zero =>
      intro position ledger history data leaf hmem
      by_cases htarget : position = target
      · simp [tRetry, htarget] at hmem
        subst leaf
        simp
      · simp [tRetry, htarget] at hmem
        subst leaf
        simp
  | succ remaining ih =>
      intro position ledger history data leaf hmem
      by_cases htarget : position = target
      · simp [tRetry, htarget] at hmem
        subst leaf
        simpa using Nat.le_add_right ledger.card (2 * pairAttempts * (remaining + 1))
      · rw [tRetry, if_neg htarget] at hmem
        obtain ⟨outcome, houtcome, hleaf⟩ := List.mem_flatMap.mp hmem
        have hsupply := tSupply_outcome_ledger_card_le t pairAttempts ledger history data
          outcome houtcome
        cases outcome with
        | accepted nextLedger nextHistory nextData phaseResource =>
            simp only [List.mem_append] at hleaf
            rcases hleaf with hleft | hright
            · have hrec := ih (position + 1) nextLedger (true :: nextHistory)
                  (phaseBranchRaw phaseResource nextData true) leaf hleft
              calc
                leaf.ledger.card ≤ nextLedger.card + 2 * pairAttempts * remaining := hrec
                _ ≤ (ledger.card + 2 * pairAttempts) +
                    2 * pairAttempts * remaining := Nat.add_le_add_right hsupply _
                _ = ledger.card + 2 * pairAttempts * (remaining + 1) := by ring
            · have hrec := ih (position - 1) nextLedger (false :: nextHistory)
                  (phaseBranchRaw phaseResource nextData false) leaf hright
              calc
                leaf.ledger.card ≤ nextLedger.card + 2 * pairAttempts * remaining := hrec
                _ ≤ (ledger.card + 2 * pairAttempts) +
                    2 * pairAttempts * remaining := Nat.add_le_add_right hsupply _
                _ = ledger.card + 2 * pairAttempts * (remaining + 1) := by ring
        | exhausted nextLedger nextHistory nextData =>
            simp only [List.mem_singleton] at hleaf
            subst leaf
            calc
              nextLedger.card ≤ ledger.card + 2 * pairAttempts := hsupply
              _ ≤ ledger.card + 2 * pairAttempts * (remaining + 1) := by
                apply Nat.add_le_add_left
                exact le_mul_of_one_le_right (Nat.zero_le _) (by omega)

/-- Every retained T leaf consumes no more than the literal fresh-pair debit
at each of the computed order-twelve phase attempts. -/
theorem tActualRawTree_ledger_le
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (blocks : Nat) (rho : DensityOperator QubitSpace) (leaf : BK05RawLeaf)
    (hmem : leaf ∈ tActualRawTree t pairAttempts target blocks rho) :
    leaf.ledger.card ≤ 2 * pairAttempts * 12 * blocks := by
  have hle := tRetry_ledger_card_le t pairAttempts target (12 * blocks)
    0 0 [] rho.toOperator leaf (by simpa [tActualRawTree] using hmem)
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hle

private theorem hRetry_leaf_raw_positive {q : Nat}
    (h : DensityOperator QubitSpace) (target : ZMod q) (remaining : Nat) :
    ∀ (position : ZMod q) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace),
      LinearMap.IsPositive data → ∀ leaf,
        leaf ∈ hRetry h target remaining position ledger history data →
          LinearMap.IsPositive leaf.raw := by
  induction remaining with
  | zero =>
      intro position ledger history data hdata leaf hmem
      by_cases htarget : position = target
      · simp [hRetry, htarget] at hmem
        subst leaf
        exact hdata
      · simp [hRetry, htarget] at hmem
        subst leaf
        exact hdata
  | succ remaining ih =>
      intro position ledger history data hdata leaf hmem
      by_cases htarget : position = target
      · simp [hRetry, htarget] at hmem
        subst leaf
        exact hdata
      · rw [hRetry, if_neg htarget] at hmem
        rcases List.mem_append.mp hmem with hleft | hright
        · exact ih (position + 1) (ledger + {.h}) (true :: history)
            (hStepRaw h true data) (hStepRaw_positive h true data hdata) leaf hleft
        · exact ih (position - 1) (ledger + {.h}) (false :: history)
            (hStepRaw h false data) (hStepRaw_positive h false data hdata) leaf hright

private theorem tSupply_outcome_data_positive
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) :
    ∀ (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
      (data : Operator QubitSpace),
      LinearMap.IsPositive data → ∀ outcome,
        outcome ∈ tSupply t pairAttempts ledger history data →
          LinearMap.IsPositive
            (match outcome with
              | .accepted _ _ nextData _ => nextData
              | .exhausted _ _ nextData => nextData) := by
  induction pairAttempts with
  | zero =>
      intro ledger history data hdata outcome hmem
      simp [tSupply] at hmem
      subst outcome
      exact hdata
  | succ attempts ih =>
      intro ledger history data hdata outcome hmem
      let nextLedger := ledger + ({.t, .t} : ResourceLedger BK05ResourceToken)
      rw [tSupply] at hmem
      change outcome ∈
        .accepted nextLedger (true :: history) data (tAcceptedPhaseRaw t) ::
          tSupply t attempts nextLedger (false :: history) (tRejectedDataRaw data t) at hmem
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst outcome
        exact hdata
      · exact ih nextLedger (false :: history) (tRejectedDataRaw data t)
          (tRejectedDataRaw_positive data t hdata) outcome htail

private theorem tSupply_accepted_phase_positive
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) :
    ∀ (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
      (data : Operator QubitSpace) (nextLedger : ResourceLedger BK05ResourceToken)
      (nextHistory : List Bool) (nextData phaseResource : Operator QubitSpace),
      BK05TSupplyOutcome.accepted nextLedger nextHistory nextData phaseResource ∈
        tSupply t pairAttempts ledger history data →
          LinearMap.IsPositive phaseResource := by
  induction pairAttempts with
  | zero =>
      intro ledger history data nextLedger nextHistory nextData phaseResource hmem
      simp [tSupply] at hmem
  | succ attempts ih =>
      intro ledger history data nextLedger nextHistory nextData phaseResource hmem
      let supplierLedger := ledger + ({.t, .t} : ResourceLedger BK05ResourceToken)
      rw [tSupply] at hmem
      change BK05TSupplyOutcome.accepted nextLedger nextHistory nextData phaseResource ∈
        .accepted supplierLedger (true :: history) data (tAcceptedPhaseRaw t) ::
          tSupply t attempts supplierLedger (false :: history) (tRejectedDataRaw data t) at hmem
      rcases List.mem_cons.mp hmem with hhead | htail
      · have hphase : phaseResource = tAcceptedPhaseRaw t := by
          have hprojected := congrArg (fun outcome : BK05TSupplyOutcome =>
            match outcome with
            | .accepted _ _ _ resource => resource
            | .exhausted _ _ _ => 0) hhead
          simpa using hprojected
        rw [hphase]
        exact tAcceptedPhaseRaw_positive t
      · exact ih supplierLedger (false :: history) (tRejectedDataRaw data t)
          nextLedger nextHistory nextData phaseResource htail

private theorem tRetry_leaf_raw_positive {q : Nat}
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod q)
    (remaining : Nat) :
    ∀ (position : ZMod q) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace),
      LinearMap.IsPositive data → ∀ leaf,
        leaf ∈ tRetry t pairAttempts target remaining position ledger history data →
          LinearMap.IsPositive leaf.raw := by
  induction remaining with
  | zero =>
      intro position ledger history data hdata leaf hmem
      by_cases htarget : position = target
      · simp [tRetry, htarget] at hmem
        subst leaf
        exact hdata
      · simp [tRetry, htarget] at hmem
        subst leaf
        exact hdata
  | succ remaining ih =>
      intro position ledger history data hdata leaf hmem
      by_cases htarget : position = target
      · simp [tRetry, htarget] at hmem
        subst leaf
        exact hdata
      · rw [tRetry, if_neg htarget] at hmem
        obtain ⟨outcome, houtcome, hleaf⟩ := List.mem_flatMap.mp hmem
        have houtcomePositive := tSupply_outcome_data_positive t pairAttempts ledger history data
          hdata outcome houtcome
        cases outcome with
        | accepted nextLedger nextHistory nextData phaseResource =>
            have hphasePositive := tSupply_accepted_phase_positive t pairAttempts
              ledger history data nextLedger nextHistory nextData phaseResource houtcome
            simp only [List.mem_append] at hleaf
            rcases hleaf with hleft | hright
            · exact ih (position + 1) nextLedger (true :: nextHistory)
                (phaseBranchRaw phaseResource nextData true)
                (phaseBranchRaw_positive phaseResource nextData
                  hphasePositive (by simpa using houtcomePositive) true)
                leaf hleft
            · exact ih (position - 1) nextLedger (false :: nextHistory)
                (phaseBranchRaw phaseResource nextData false)
                (phaseBranchRaw_positive phaseResource nextData
                  hphasePositive (by simpa using houtcomePositive) false)
                leaf hright
        | exhausted nextLedger nextHistory nextData =>
            simp only [List.mem_singleton] at hleaf
            subst leaf
            simpa using houtcomePositive

/-- Every retained raw H leaf is positive by induction through the actual CP
instrument branches; positivity is not stored as a tree field or assumption. -/
theorem hActualRawTree_leaf_raw_positive
    (h : DensityOperator QubitSpace) (target : ZMod 8) (blocks : Nat)
    (rho : DensityOperator QubitSpace) (leaf : BK05RawLeaf)
    (hmem : leaf ∈ hActualRawTree h target blocks rho) :
    LinearMap.IsPositive leaf.raw := by
  exact hRetry_leaf_raw_positive h target (8 * blocks) 0 0 [] rho.toOperator
    rho.positive leaf (by simpa [hActualRawTree] using hmem)

/-- Positive H leaves have nonnegative real trace mass. -/
theorem hActualRawTree_leaf_weight_nonneg
    (h : DensityOperator QubitSpace) (target : ZMod 8) (blocks : Nat)
    (rho : DensityOperator QubitSpace) (leaf : BK05RawLeaf)
    (hmem : leaf ∈ hActualRawTree h target blocks rho) :
    0 ≤ rawWeight leaf := by
  change 0 ≤ (LinearMap.trace Complex QubitSpace leaf.raw).re
  exact (Complex.nonneg_iff.mp
    (hActualRawTree_leaf_raw_positive h target blocks rho leaf hmem).trace_nonneg).1

/-- Every retained raw T leaf is positive by induction through the actual
complete-pair supplier, its CP rejection discard, and the phase instrument. -/
theorem tActualRawTree_leaf_raw_positive
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (blocks : Nat) (rho : DensityOperator QubitSpace) (leaf : BK05RawLeaf)
    (hmem : leaf ∈ tActualRawTree t pairAttempts target blocks rho) :
    LinearMap.IsPositive leaf.raw := by
  exact tRetry_leaf_raw_positive t pairAttempts target (12 * blocks)
    0 0 [] rho.toOperator rho.positive leaf (by simpa [tActualRawTree] using hmem)

/-- Positive T leaves have nonnegative real trace mass. -/
theorem tActualRawTree_leaf_weight_nonneg
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (blocks : Nat) (rho : DensityOperator QubitSpace) (leaf : BK05RawLeaf)
    (hmem : leaf ∈ tActualRawTree t pairAttempts target blocks rho) :
    0 ≤ rawWeight leaf := by
  change 0 ≤ (LinearMap.trace Complex QubitSpace leaf.raw).re
  exact (Complex.nonneg_iff.mp
    (tActualRawTree_leaf_raw_positive t pairAttempts target blocks rho leaf hmem).trace_nonneg).1

/-- The ideal H source is the actual transported `hMagicState`: each raw
first-step branch therefore uses precisely `A_{-π/4}`. -/
private theorem hMagicStepRaw_eq_phaseBranch
    (data : Operator QubitSpace) (coin : Bool) :
    hStepRaw hMagicState coin data =
      phaseBranchRaw (phaseStateDensity (-Real.pi / 4)).toOperator data coin := by
  have hsource := congrArg DensityOperator.toOperator hResourceTransport_hMagicState
  change hResourceTransport.conjOperator hMagicState.toOperator =
    (phaseStateDensity (-Real.pi / 4)).toOperator at hsource
  simp only [hStepRaw]
  change phaseBranchRaw (hResourceTransport.conjOperator hMagicState.toOperator)
    data coin = _
  rw [hsource]

theorem hActualRawTree_ideal_sourceBranch
    (rho : DensityOperator QubitSpace) :
    ∀ coin,
      hStepRaw hMagicState coin rho.toOperator =
        phaseBranchRaw (phaseStateDensity (-Real.pi / 4)).toOperator rho.toOperator coin := by
  intro coin
  exact hMagicStepRaw_eq_phaseBranch rho.toOperator coin

private theorem phaseBranchRaw_trace_half_on_pure
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1) (coin : Bool) :
    LinearMap.trace Complex QubitSpace
        (phaseBranchRaw (phaseStateDensity theta).toOperator
          (sourceInputDensity psi hpsi).toOperator coin) = (1 / 2 : Real) := by
  have hinjection :
      injectedInputRaw (sourceInputDensity psi hpsi).toOperator
          (phaseStateDensity theta).toOperator =
        (injectionInputDensity psi theta hpsi).toOperator := by
    change (QuantumChannel.unitaryConj TwoQubit.tensorRegisterTransport)
      (DensityOperator.tensorDensity (sourceInputDensity psi hpsi)
        (phaseStateDensity theta)).toOperator = _
    exact congrArg DensityOperator.toOperator
      (phaseStateResourceUse_run_eq_injectionInputDensity psi theta hpsi)
  have hfair := oneShotMeasurementWeight_fair psi theta hpsi coin
  unfold oneShotMeasurementWeight oneShotInstrumentBranch at hfair
  rw [phaseStateResourceUse_run_eq_injectionInputDensity] at hfair
  calc
    LinearMap.trace Complex QubitSpace
        (phaseBranchRaw (phaseStateDensity theta).toOperator
          (sourceInputDensity psi hpsi).toOperator coin) =
        LinearMap.trace Complex TwoQubit.TwoQubitSpace
          (zzMeasurement.instrument.branchOperator (observedRetrySyndrome coin)
            (injectionInputDensity psi theta hpsi).toOperator) := by
              rw [phaseBranchRaw, oneShotPostprocess.trace_map, hinjection]
    _ = (zzMeasurement.instrument.bornWeight (observedRetrySyndrome coin)
        (injectionInputDensity psi theta hpsi) : Complex) :=
          zzMeasurement.instrument.trace_branchOperator_eq_bornWeight
            (observedRetrySyndrome coin) (injectionInputDensity psi theta hpsi)
    _ = (1 / 2 : Real) := by exact_mod_cast hfair

private theorem sourceInputDensity_toOperator_local
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (sourceInputDensity psi hpsi).toOperator =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  rw [sourceInputDensity, DensityOperator.pureOfNonzero_toOperator,
    inner_self_eq_norm_sq_to_K, hpsi]
  norm_num

private theorem rankOne_smul_self_local
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    (scalar : Complex) (psi : H) :
    (InnerProductSpace.rankOne Complex (scalar • psi) (scalar • psi)).toLinearMap =
      (star scalar * scalar) •
        (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  ext x
  simp [InnerProductSpace.rankOne_apply]
  rw [smul_smul]
  rw [mul_comm scalar (starRingEnd Complex scalar)]

/-- The fixed-resource raw injection branch is linear in its unnormalised
data operator.  Keeping this carrier local prevents a normalized-density
surrogate from entering the retry calculation. -/
private theorem injectedInputRaw_add (data₁ data₂ resource : Operator QubitSpace) :
    injectedInputRaw (data₁ + data₂) resource =
      injectedInputRaw data₁ resource + injectedInputRaw data₂ resource := by
  unfold injectedInputRaw
  rw [TensorProduct.map_add_left]
  exact TwoQubit.tensorRegisterTransport.conjOperatorLinearMap.map_add _ _

private theorem injectedInputRaw_smul (scalar : Complex) (data resource : Operator QubitSpace) :
    injectedInputRaw (scalar • data) resource =
      scalar • injectedInputRaw data resource := by
  unfold injectedInputRaw
  rw [TensorProduct.map_smul_left]
  exact TwoQubit.tensorRegisterTransport.conjOperatorLinearMap.map_smul scalar _

private noncomputable def phaseBranchRawLinear (resource : Operator QubitSpace)
    (coin : Bool) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace where
  toFun := fun data => phaseBranchRaw resource data coin
  map_add' := by
    intro data₁ data₂
    classical
    unfold phaseBranchRaw FiniteInstrument.branchOperator
    rw [injectedInputRaw_add]
    simp only [LinearMap.comp_add, LinearMap.add_comp]
    rw [← map_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  map_smul' := by
    intro scalar data
    classical
    unfold phaseBranchRaw FiniteInstrument.branchOperator
    rw [injectedInputRaw_smul]
    simp only [LinearMap.comp_smul, LinearMap.smul_comp]
    rw [← map_smul]
    congr 1
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp

private theorem phaseBranchRawLinear_apply (resource data : Operator QubitSpace)
    (coin : Bool) :
    phaseBranchRawLinear resource coin data = phaseBranchRaw resource data coin :=
  rfl

private theorem phaseBranchRaw_smul (resource data : Operator QubitSpace)
    (scalar : Complex) (coin : Bool) :
    phaseBranchRaw resource (scalar • data) coin =
      scalar • phaseBranchRaw resource data coin := by
  exact phaseBranchRawLinear resource coin |>.map_smul scalar data

private theorem phaseBranchRaw_zero (resource : Operator QubitSpace) (coin : Bool) :
    phaseBranchRaw resource 0 coin = 0 := by
  exact phaseBranchRawLinear resource coin |>.map_zero

private theorem phaseBranchRaw_ideal_trace_half_rankOne
    (theta : Real) (u : QubitSpace) (coin : Bool) :
    LinearMap.trace Complex QubitSpace
      (phaseBranchRaw (phaseStateDensity theta).toOperator
        (InnerProductSpace.rankOne Complex u u).toLinearMap coin) =
      (1 / 2 : Complex) * LinearMap.trace Complex QubitSpace
        (InnerProductSpace.rankOne Complex u u).toLinearMap := by
  by_cases hu : u = 0
  · subst u
    have hrankzero :
        (InnerProductSpace.rankOne Complex (0 : QubitSpace) (0 : QubitSpace)).toLinearMap =
          0 := by
      exact congrArg ContinuousLinearMap.toLinearMap
        (InnerProductSpace.rankOne_eq_zero.mpr (Or.inl rfl))
    rw [hrankzero, phaseBranchRaw_zero]
    simp
  · let psi : QubitSpace := ((‖u‖ : Complex)⁻¹) • u
    have hnorm_ne : (‖u‖ : Complex) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.mpr hu)
    have hpsi : ‖psi‖ = 1 := by
      dsimp [psi]
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg u)]
      field_simp
    have hu_eq : u = (‖u‖ : Complex) • psi := by
      calc
        u = (1 : Complex) • u := (one_smul Complex u).symm
        _ = ((‖u‖ : Complex) * (‖u‖ : Complex)⁻¹) • u := by
          congr 1
          field_simp
        _ = (‖u‖ : Complex) • (((‖u‖ : Complex)⁻¹) • u) := by
          rw [smul_smul]
        _ = (‖u‖ : Complex) • psi := rfl
    have hrank : (InnerProductSpace.rankOne Complex u u).toLinearMap =
        (‖u‖ ^ 2 : Complex) • (sourceInputDensity psi hpsi).toOperator := by
      calc
        (InnerProductSpace.rankOne Complex u u).toLinearMap =
            (InnerProductSpace.rankOne Complex
              ((‖u‖ : Complex) • psi) ((‖u‖ : Complex) • psi)).toLinearMap := by
                exact congrArg
                  (fun v : QubitSpace =>
                    (InnerProductSpace.rankOne Complex v v).toLinearMap) hu_eq
        _ = (star (‖u‖ : Complex) * (‖u‖ : Complex)) •
            (InnerProductSpace.rankOne Complex psi psi).toLinearMap :=
              rankOne_smul_self_local (‖u‖ : Complex) psi
        _ = (‖u‖ ^ 2 : Complex) •
            (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
              norm_num [pow_two]
        _ = (‖u‖ ^ 2 : Complex) • (sourceInputDensity psi hpsi).toOperator := by
              rw [sourceInputDensity_toOperator_local]
    calc
      LinearMap.trace Complex QubitSpace
          (phaseBranchRaw (phaseStateDensity theta).toOperator
            (InnerProductSpace.rankOne Complex u u).toLinearMap coin) =
          LinearMap.trace Complex QubitSpace
            (phaseBranchRaw (phaseStateDensity theta).toOperator
              ((‖u‖ ^ 2 : Complex) • (sourceInputDensity psi hpsi).toOperator) coin) := by
            rw [hrank]
      _ = (‖u‖ ^ 2 : Complex) * (1 / 2 : Complex) := by
            rw [phaseBranchRaw_smul, map_smul,
              phaseBranchRaw_trace_half_on_pure psi theta hpsi coin]
            simp only [smul_eq_mul]
            norm_num
      _ = (1 / 2 : Complex) * LinearMap.trace Complex QubitSpace
          (InnerProductSpace.rankOne Complex u u).toLinearMap := by
            rw [hrank, map_smul, sourceInputDensity_toOperator_local,
              InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq_to_K]
            rw [hpsi]
            norm_num
            ring

/-- Each literal ideal phase-state injection outcome carries exactly half the
trace of any positive, possibly unnormalised raw input, at every phase angle. -/
private theorem phaseBranchRaw_ideal_trace_half
    (theta : Real) (data : Operator QubitSpace) (hdata : LinearMap.IsPositive data)
    (coin : Bool) :
    LinearMap.trace Complex QubitSpace
      (phaseBranchRaw (phaseStateDensity theta).toOperator data coin) =
      (1 / 2 : Complex) * LinearMap.trace Complex QubitSpace data := by
  have hpositive : (LinearMap.toContinuousLinearMap data).IsPositive :=
    (LinearMap.isPositive_toContinuousLinearMap_iff data).2 hdata
  rcases (ContinuousLinearMap.isPositive_iff_eq_sum_rankOne).1 hpositive with
    ⟨m, u, hu⟩
  have hdata_sum : data = ∑ i : Fin m,
      (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap := by
    simpa using congrArg ContinuousLinearMap.toLinearMap hu
  rw [hdata_sum]
  change LinearMap.trace Complex QubitSpace
      (phaseBranchRawLinear (phaseStateDensity theta).toOperator coin
        (∑ i : Fin m,
          (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap)) = _
  have hbranch_sum :
      phaseBranchRawLinear (phaseStateDensity theta).toOperator coin
        (∑ i : Fin m,
          (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap) =
      ∑ i : Fin m,
        phaseBranchRawLinear (phaseStateDensity theta).toOperator coin
          (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap := by
        rw [map_sum]
  have htrace_sum : LinearMap.trace Complex QubitSpace
      (∑ i : Fin m, (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap) =
      ∑ i : Fin m, LinearMap.trace Complex QubitSpace
        (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap := by
        rw [map_sum]
  rw [hbranch_sum, htrace_sum, Finset.mul_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact phaseBranchRaw_ideal_trace_half_rankOne theta (u i) coin

/-- The classical coefficient of literal H-tree leaves which exhaust their
phase budget before reaching the requested order-eight target. -/
private def hExhaustionCoeff (target : ZMod 8) : Nat → ZMod 8 → Real
  | 0, position => if position = target then 0 else 1
  | remaining + 1, position =>
      if position = target then 0 else
        (hExhaustionCoeff target remaining (position + 1) +
          hExhaustionCoeff target remaining (position - 1)) / 2

private theorem rawMassOfKind_append (kind : BK05RawLeafKind)
    (left right : List BK05RawLeaf) :
    rawMassOfKind kind (left ++ right) =
      rawMassOfKind kind left + rawMassOfKind kind right := by
  simp [rawMassOfKind, rawMass]

private theorem hRetry_phaseExhausted_mass_eq_coeff
    (target : ZMod 8) (remaining : Nat) :
    ∀ (position : ZMod 8) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      rawMassOfKind .phaseExhausted
        (hRetry hMagicState target remaining position ledger history data) =
        hExhaustionCoeff target remaining position *
          (LinearMap.trace Complex QubitSpace data).re := by
  induction remaining with
  | zero =>
      intro position ledger history data hdata
      by_cases htarget : position = target
      · simp [hRetry, htarget, rawMassOfKind, rawMass, rawWeight,
          hExhaustionCoeff]
      · simp [hRetry, htarget, rawMassOfKind, rawMass, rawWeight,
          hExhaustionCoeff]
  | succ remaining ih =>
      intro position ledger history data hdata
      by_cases htarget : position = target
      · simp [hRetry, htarget, rawMassOfKind, rawMass, rawWeight,
          hExhaustionCoeff]
      · rw [hRetry, if_neg htarget, rawMassOfKind_append]
        rw [ih (position + 1)
          (ledger + ({.h} : ResourceLedger BK05ResourceToken)) (true :: history)
          (hStepRaw hMagicState true data)
          (hStepRaw_positive hMagicState true data hdata)]
        rw [ih (position - 1)
          (ledger + ({.h} : ResourceLedger BK05ResourceToken)) (false :: history)
          (hStepRaw hMagicState false data)
          (hStepRaw_positive hMagicState false data hdata)]
        have htrue :
            (LinearMap.trace Complex QubitSpace
              (hStepRaw hMagicState true data)).re =
              (1 / 2 : Real) * (LinearMap.trace Complex QubitSpace data).re := by
          rw [hMagicStepRaw_eq_phaseBranch,
            phaseBranchRaw_ideal_trace_half (-Real.pi / 4) data hdata true]
          simp [Complex.mul_re]
        have hfalse :
            (LinearMap.trace Complex QubitSpace
              (hStepRaw hMagicState false data)).re =
              (1 / 2 : Real) * (LinearMap.trace Complex QubitSpace data).re := by
          rw [hMagicStepRaw_eq_phaseBranch,
            phaseBranchRaw_ideal_trace_half (-Real.pi / 4) data hdata false]
          simp [Complex.mul_re]
        rw [htrue, hfalse]
        simp only [hExhaustionCoeff, if_neg htarget]
        ring

/-- The actual complete H tree's exhausted-leaf mass is exactly its local
classical coefficient times the literal input trace. -/
private theorem hActualRawTree_phaseExhausted_mass_eq_coeff
    (target : ZMod 8) (blocks : Nat) (rho : DensityOperator QubitSpace) :
    rawMassOfKind .phaseExhausted
      (hActualRawTree hMagicState target blocks rho) =
      hExhaustionCoeff target (8 * blocks) 0 := by
  rw [hActualRawTree,
    hRetry_phaseExhausted_mass_eq_coeff target (8 * blocks) 0 0 [] rho.toOperator rho.positive]
  simp [rho.trace_one]

private theorem hExhaustionCoeff_target (target : ZMod 8) : ∀ remaining,
    hExhaustionCoeff target remaining target = 0 := by
  intro remaining
  cases remaining <;> simp [hExhaustionCoeff]

private theorem hExhaustionCoeff_le_of_bound
    (target : ZMod 8) (remaining extra : Nat) (bound : Real)
    (hbound_nonneg : 0 ≤ bound)
    (hbound : ∀ position, hExhaustionCoeff target remaining position ≤ bound) :
    ∀ position, hExhaustionCoeff target (extra + remaining) position ≤ bound := by
  induction extra with
  | zero => simpa using hbound
  | succ extra ih =>
      intro position
      rw [Nat.succ_add]
      by_cases hposition : position = target
      · subst position
        simpa [hExhaustionCoeff_target] using hbound_nonneg
      · rw [hExhaustionCoeff, if_neg hposition]
        have hplus := ih (position + 1)
        have hminus := ih (position - 1)
        linarith

private theorem hExhaustionCoeff_path_le
    (target : ZMod 8) (remaining : Nat) (bound : Real)
    (hbound_nonneg : 0 ≤ bound)
    (hbound : ∀ position, hExhaustionCoeff target remaining position ≤ bound) :
    ∀ (coins : List Bool) (position : ZMod 8),
      PhaseRetry.visitsTarget position target coins →
      hExhaustionCoeff target (coins.length + remaining) position ≤
        (1 - (1 / 2 : Real) ^ coins.length) * bound := by
  intro coins
  induction coins with
  | nil =>
      intro position hvisit
      have hposition : target = position := by
        simpa [PhaseRetry.visitsTarget, PhaseRetry.positions] using hvisit
      subst position
      simp [hExhaustionCoeff_target]
  | cons coin coins ih =>
      intro position hvisit
      by_cases hposition : position = target
      · subst position
        rw [hExhaustionCoeff_target]
        exact mul_nonneg
          (sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))) hbound_nonneg
      · have htail : PhaseRetry.visitsTarget
            (position + PhaseRetry.signedIncrement coin) target coins := by
          unfold PhaseRetry.visitsTarget at hvisit ⊢
          simp only [PhaseRetry.positions, List.mem_cons] at hvisit
          exact hvisit.resolve_left (Ne.symm hposition)
        rw [List.length_cons, Nat.succ_add, hExhaustionCoeff, if_neg hposition]
        have hotherPlus := hExhaustionCoeff_le_of_bound target remaining
          coins.length bound hbound_nonneg hbound (position + 1)
        have hotherMinus := hExhaustionCoeff_le_of_bound target remaining
          coins.length bound hbound_nonneg hbound (position - 1)
        cases coin
        · have hchosen := ih (position - 1)
            (by simpa [PhaseRetry.signedIncrement, sub_eq_add_neg] using htail)
          rw [pow_succ]
          norm_num at hchosen ⊢
          nlinarith
        · have hchosen := ih (position + 1)
            (by simpa [PhaseRetry.signedIncrement] using htail)
          rw [pow_succ]
          norm_num at hchosen ⊢
          nlinarith

private theorem hExhaustionCoeff_eight_step_le
    (target position : ZMod 8) (remaining : Nat) (bound : Real)
    (hbound_nonneg : 0 ≤ bound)
    (hbound : ∀ next, hExhaustionCoeff target remaining next ≤ bound) :
    hExhaustionCoeff target (8 + remaining) position ≤
      (255 / 256 : Real) * bound := by
  have hpath := hExhaustionCoeff_path_le target remaining bound hbound_nonneg hbound
    (PhaseRetry.positiveBlock 8) position
    (PhaseRetry.positiveBlock_visits_target_eight position target)
  norm_num [PhaseRetry.positiveBlock] at hpath ⊢
  exact hpath

private theorem hExhaustionCoeff_blocks_le
    (target position : ZMod 8) (blocks : Nat) :
    hExhaustionCoeff target (8 * blocks) position ≤
      (255 / 256 : Real) ^ blocks := by
  induction blocks generalizing position with
  | zero =>
      by_cases hposition : position = target <;>
        simp [hExhaustionCoeff, hposition]
  | succ blocks ih =>
      rw [Nat.mul_succ, pow_succ]
      have hstep := hExhaustionCoeff_eight_step_le target position (8 * blocks)
        ((255 / 256 : Real) ^ blocks) (pow_nonneg (by norm_num) _) ih
      rw [Nat.add_comm] at hstep
      nlinarith

/-- The literal unconditioned H retry tree's exhausted-leaf submass decays at
the order-eight certificate rate.  All target-hit and algebraically zero
leaves remain in the tree; only `.phaseExhausted` is measured here. -/
theorem hActualRawTree_phaseTail_le
    (target : ZMod 8) (blocks : Nat) (rho : DensityOperator QubitSpace) :
    rawMassOfKind .phaseExhausted
      (hActualRawTree hMagicState target blocks rho) ≤
      (255 / 256 : Real) ^ blocks := by
  rw [hActualRawTree_phaseExhausted_mass_eq_coeff]
  exact hExhaustionCoeff_blocks_le target 0 blocks

/-- The literal raw two-resource input specializes to the registered source
T-pair vector, before either parity branch is selected. -/
private theorem tPairInputRaw_tMagicState_eq_source :
    tPairInputRaw tMagicState =
      (InnerProductSpace.rankOne Complex
        sourceTTwoQubitState sourceTTwoQubitState).toLinearMap := by
  unfold tPairInputRaw
  rw [← sourceTDensity_eq_tMagicState, sourceTDensity_toOperator,
    DensityOperator.tensorMap_rankOne, QuditSubsystem.conjOperator_rankOne]
  rfl

/-- A source-T parity branch is literally the selected joint projector
compressing the registered two-copy source vector. -/
private theorem tPairBranchRaw_tMagicState_eq_rankOne (coin : Bool) :
    tPairBranchRaw tMagicState coin =
      (InnerProductSpace.rankOne Complex
        (jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
          (observedRetrySyndrome coin) sourceTTwoQubitState)
        (jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
          (observedRetrySyndrome coin) sourceTTwoQubitState)).toLinearMap := by
  change (jointStabilizerInstrument zzMeasurement.checks zzMeasurement.commute).branchOperator
    _ _ = _
  rw [jointStabilizerInstrument_branchOperator,
    tPairInputRaw_tMagicState_eq_source]
  have hne : sourceTTwoQubitState ≠ 0 := by
    intro hzero
    have hnorm := sourceTTwoQubitState_norm
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  let projector := jointStabilizerProjector zzMeasurement.checks
    zzMeasurement.commute (observedRetrySyndrome coin)
  have hcomp := DensityOperator.comp_pureOfNonzero_adjoint projector
    sourceTTwoQubitState hne
  rw [DensityOperator.pureOfNonzero_toOperator,
    inner_self_eq_norm_sq_to_K, sourceTTwoQubitState_norm] at hcomp
  norm_num at hcomp
  dsimp [projector] at hcomp
  rw [jointStabilizerProjector_adjoint] at hcomp
  exact hcomp

private theorem tPairBranchRaw_tMagicState_true :
    tPairBranchRaw tMagicState true =
      (sourceTEvenWeight : Complex) • sourceTEvenBranch.toOperator := by
  rw [tPairBranchRaw_tMagicState_eq_rankOne]
  have hweight : 0 < TwoQubit.zzEvenWeight sourceTTwoQubitState := by
    change 0 < sourceTEvenWeight
    rw [sourceTEvenWeight_eq_two_thirds]
    norm_num
  have hbranch : sourceTEvenBranch.toOperator =
      (InnerProductSpace.rankOne Complex
        (TwoQubit.zzEvenBranchState sourceTTwoQubitState hweight)
        (TwoQubit.zzEvenBranchState sourceTTwoQubitState hweight)).toLinearMap := by
    unfold sourceTEvenBranch
    erw [TwoQubit.zzEvenBranchDensity_toOperator]
  change (InnerProductSpace.rankOne Complex
      (jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
        positiveSyndrome sourceTTwoQubitState)
      (jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
        positiveSyndrome sourceTTwoQubitState)).toLinearMap = _
  rw [jointProjector_positive]
  rw [hbranch, ← TwoQubit.zzEvenBranchState_rescale sourceTTwoQubitState hweight]
  rw [rankOne_smul_self_local]
  have hsquare : Real.sqrt sourceTEvenWeight * Real.sqrt sourceTEvenWeight =
      sourceTEvenWeight := by
    rw [← pow_two, Real.sq_sqrt]
    rw [sourceTEvenWeight_eq_two_thirds]
    norm_num
  change (star (Real.sqrt sourceTEvenWeight : Complex) *
      (Real.sqrt sourceTEvenWeight : Complex)) • _ = _
  have hscalar : star (Real.sqrt sourceTEvenWeight : Complex) *
      (Real.sqrt sourceTEvenWeight : Complex) = (sourceTEvenWeight : Complex) := by
    rw [Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast hsquare
  rw [hscalar]

private theorem tPairBranchRaw_tMagicState_false :
    tPairBranchRaw tMagicState false =
      (TwoQubit.zzOddWeight sourceTTwoQubitState : Complex) •
        sourceTOddBranch.toOperator := by
  rw [tPairBranchRaw_tMagicState_eq_rankOne]
  have hweight : 0 < TwoQubit.zzOddWeight sourceTTwoQubitState := by
    rw [sourceTOddWeight_eq_one_third]
    norm_num
  have hbranch : sourceTOddBranch.toOperator =
      (InnerProductSpace.rankOne Complex
        (TwoQubit.zzOddBranchState sourceTTwoQubitState hweight)
        (TwoQubit.zzOddBranchState sourceTTwoQubitState hweight)).toLinearMap := by
    unfold sourceTOddBranch
    rw [TwoQubit.zzOddBranchDensity_toOperator]
  change (InnerProductSpace.rankOne Complex
      (jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
        negativeSyndrome sourceTTwoQubitState)
      (jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
        negativeSyndrome sourceTTwoQubitState)).toLinearMap = _
  rw [jointProjector_negative]
  rw [hbranch, ← TwoQubit.zzOddBranchState_rescale sourceTTwoQubitState hweight]
  rw [rankOne_smul_self_local]
  have hsquare : Real.sqrt (TwoQubit.zzOddWeight sourceTTwoQubitState) *
      Real.sqrt (TwoQubit.zzOddWeight sourceTTwoQubitState) =
        TwoQubit.zzOddWeight sourceTTwoQubitState := by
    rw [← pow_two, Real.sq_sqrt]
    rw [sourceTOddWeight_eq_one_third]
    norm_num
  have hscalar : star (Real.sqrt (TwoQubit.zzOddWeight sourceTTwoQubitState) : Complex) *
      (Real.sqrt (TwoQubit.zzOddWeight sourceTTwoQubitState) : Complex) =
        (TwoQubit.zzOddWeight sourceTTwoQubitState : Complex) := by
    rw [Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast hsquare
  rw [hscalar]

/-- The actual accepted source-T branch, including XOR/discard and Hadamard,
is the unnormalised `-pi/6` phase resource with its literal `2/3` weight. -/
private theorem tMagicAcceptedPhaseRaw_eq :
    tAcceptedPhaseRaw tMagicState =
      (2 / 3 : Complex) • (phaseStateDensity (-Real.pi / 6)).toOperator := by
  have hsource := congrArg DensityOperator.toOperator
    IdealResourceUniversality.sourceTAcceptedBranch_to_phaseStateDensity
  have hsource' : (QuantumChannel.unitaryConj hadamardTransport)
      (oneShotPostprocess sourceTEvenBranch.toOperator) =
        (phaseStateDensity (-Real.pi / 6)).toOperator := by
    simpa [oneShotPostprocess, QuantumChannel.mapDensity_toOperator] using hsource
  unfold tAcceptedPhaseRaw
  rw [tPairBranchRaw_tMagicState_true, map_smul, map_smul]
  rw [hsource', sourceTEvenWeight_eq_two_thirds]
  norm_num

/-- The literal rejected source-T parity branch is completely discarded, so
the data retry carries exactly its unnormalised `1/3` branch weight. -/
private theorem tMagicRejectedDataRaw_eq (data : Operator QubitSpace) :
    tRejectedDataRaw data tMagicState = (1 / 3 : Complex) • data := by
  rw [tRejectedDataRaw_discardsFullPair, tPairBranchRaw_tMagicState_false,
    map_smul]
  simp only [DensityOperator.trace_one, mul_one]
  rw [sourceTOddWeight_eq_one_third]
  norm_num

/-- The raw injection circuit is separately linear in its unnormalised
resource factor.  The T retry proof uses this without replacing the accepted
phase resource by a normalized state. -/
private theorem injectedInputRaw_add_right
    (data resource₁ resource₂ : Operator QubitSpace) :
    injectedInputRaw data (resource₁ + resource₂) =
      injectedInputRaw data resource₁ + injectedInputRaw data resource₂ := by
  unfold injectedInputRaw
  rw [TensorProduct.map_add_right]
  exact TwoQubit.tensorRegisterTransport.conjOperatorLinearMap.map_add _ _

private theorem injectedInputRaw_smul_right
    (scalar : Complex) (data resource : Operator QubitSpace) :
    injectedInputRaw data (scalar • resource) =
      scalar • injectedInputRaw data resource := by
  unfold injectedInputRaw
  rw [TensorProduct.map_smul_right]
  exact TwoQubit.tensorRegisterTransport.conjOperatorLinearMap.map_smul scalar _

private noncomputable def phaseBranchRawResourceLinear
    (data : Operator QubitSpace) (coin : Bool) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace where
  toFun := fun resource => phaseBranchRaw resource data coin
  map_add' := by
    intro resource₁ resource₂
    classical
    unfold phaseBranchRaw FiniteInstrument.branchOperator
    rw [injectedInputRaw_add_right]
    simp only [LinearMap.comp_add, LinearMap.add_comp]
    rw [← map_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  map_smul' := by
    intro scalar resource
    classical
    unfold phaseBranchRaw FiniteInstrument.branchOperator
    rw [injectedInputRaw_smul_right]
    simp only [LinearMap.comp_smul, LinearMap.smul_comp]
    rw [← map_smul]
    congr 1
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp

private theorem phaseBranchRaw_resource_smul
    (scalar : Complex) (resource data : Operator QubitSpace) (coin : Bool) :
    phaseBranchRaw (scalar • resource) data coin =
      scalar • phaseBranchRaw resource data coin := by
  exact phaseBranchRawResourceLinear data coin |>.map_smul scalar resource

/-- At the ideal source point, the actual T-pair preparation has the exact
two physical raw outcomes used by the finite retry tree: an unnormalised
`-pi/6` phase resource on acceptance and an unnormalised data retry on
rejection.  The scheduling parameters remain explicit so clients cannot
silently exchange this source fact for a normalized postselection claim. -/
theorem tActualRawTree_ideal_sourceBranch
    (target : ZMod 12) (pairAttempts blocks : Nat)
    (rho : DensityOperator QubitSpace) :
    tAcceptedPhaseRaw tMagicState =
        (2 / 3 : Complex) • (phaseStateDensity (-Real.pi / 6)).toOperator ∧
      tRejectedDataRaw rho.toOperator tMagicState =
        (1 / 3 : Complex) • rho.toOperator := by
  exact ⟨tMagicAcceptedPhaseRaw_eq, tMagicRejectedDataRaw_eq rho.toOperator⟩

/-- The real trace contributed by the literal all-rejected supplier outcome. -/
private def tSupplyExhaustedMass (outcomes : List BK05TSupplyOutcome) : Real :=
  (outcomes.map fun outcome =>
    match outcome with
    | .accepted _ _ _ _ => 0
    | .exhausted _ _ data => (LinearMap.trace Complex QubitSpace data).re).sum

/-- For a fixed later phase coin, the real trace mass contributed by all
accepted supplier outcomes after their actual raw injection branch. -/
private def tSupplyAcceptedPhaseMass (coin : Bool)
    (outcomes : List BK05TSupplyOutcome) : Real :=
  (outcomes.map fun outcome =>
    match outcome with
    | .accepted _ _ data phaseResource =>
        (LinearMap.trace Complex QubitSpace
          (phaseBranchRaw phaseResource data coin)).re
    | .exhausted _ _ _ => 0).sum

private theorem tMagicAcceptedPhaseRaw_branch_trace_re
    (data : Operator QubitSpace) (hdata : LinearMap.IsPositive data) (coin : Bool) :
    (LinearMap.trace Complex QubitSpace
      (phaseBranchRaw (tAcceptedPhaseRaw tMagicState) data coin)).re =
      (1 / 3 : Real) * (LinearMap.trace Complex QubitSpace data).re := by
  rw [tMagicAcceptedPhaseRaw_eq, phaseBranchRaw_resource_smul, map_smul,
    phaseBranchRaw_ideal_trace_half (-Real.pi / 6) data hdata coin]
  simp [Complex.mul_re]
  ring

private theorem tMagicRejectedDataRaw_trace_re (data : Operator QubitSpace) :
    (LinearMap.trace Complex QubitSpace (tRejectedDataRaw data tMagicState)).re =
      (1 / 3 : Real) * (LinearMap.trace Complex QubitSpace data).re := by
  rw [tMagicRejectedDataRaw_eq, map_smul]
  simp [Complex.mul_re]

/-- The unique all-rejected path through the literal supplier carries the
raw data scaled by one factor of `1/3` for each complete pair it consumes. -/
private theorem tSupply_allRejected_outcome_eq (attempts : Nat) :
    ∀ (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
      (data : Operator QubitSpace),
      ∃ finalLedger,
        BK05TSupplyOutcome.exhausted finalLedger
            (List.replicate attempts false ++ history)
            ((1 / 3 : Complex) ^ attempts • data) ∈
          tSupply tMagicState attempts ledger history data := by
  induction attempts with
  | zero =>
      intro ledger history data
      refine ⟨ledger, ?_⟩
      simp [tSupply]
  | succ attempts ih =>
      intro ledger history data
      let nextLedger := ledger + ({.t, .t} : ResourceLedger BK05ResourceToken)
      obtain ⟨finalLedger, htail⟩ :=
        ih nextLedger (false :: history) (tRejectedDataRaw data tMagicState)
      refine ⟨finalLedger, ?_⟩
      rw [tSupply]
      simp only [List.mem_cons]
      right
      change BK05TSupplyOutcome.exhausted finalLedger
          (List.replicate (attempts + 1) false ++ history)
          ((1 / 3 : Complex) ^ (attempts + 1) • data) ∈
        tSupply tMagicState attempts nextLedger (false :: history)
          (tRejectedDataRaw data tMagicState)
      rw [tMagicRejectedDataRaw_eq] at htail ⊢
      rw [replicate_false_append_cons attempts history] at htail
      simpa [List.replicate_succ, List.cons_append, pow_succ, smul_smul] using htail

/-- Summing the literal exhausted outcomes is exact because the supplier
recurses only down its all-rejected branch. -/
private theorem tSupply_exhaustedMass_eq (attempts : Nat) :
    ∀ (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
      (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      tSupplyExhaustedMass (tSupply tMagicState attempts ledger history data) =
        (1 / 3 : Real) ^ attempts *
          (LinearMap.trace Complex QubitSpace data).re := by
  induction attempts with
  | zero =>
      intro ledger history data _
      simp [tSupply, tSupplyExhaustedMass]
  | succ attempts ih =>
      intro ledger history data hdata
      let nextLedger := ledger + ({.t, .t} : ResourceLedger BK05ResourceToken)
      rw [tSupply]
      simp only [tSupplyExhaustedMass, List.map_cons, List.sum_cons, zero_add]
      change tSupplyExhaustedMass
          (tSupply tMagicState attempts (ledger + ({.t, .t} : ResourceLedger BK05ResourceToken))
            (false :: history) (tRejectedDataRaw data tMagicState)) = _
      rw [ih nextLedger (false :: history) (tRejectedDataRaw data tMagicState)
        (tRejectedDataRaw_positive data tMagicState hdata)]
      rw [tMagicRejectedDataRaw_trace_re, pow_succ]
      ring

/-- For either literal phase coin, summing the actual injection branches of
all accepted supplier outcomes gives the finite geometric accepted mass. -/
private theorem tSupply_acceptedPhaseMass_eq (attempts : Nat) :
    ∀ (coin : Bool) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      tSupplyAcceptedPhaseMass coin
        (tSupply tMagicState attempts ledger history data) =
        ((1 - (1 / 3 : Real) ^ attempts) / 2) *
          (LinearMap.trace Complex QubitSpace data).re := by
  induction attempts with
  | zero =>
      intro coin ledger history data _
      simp [tSupply, tSupplyAcceptedPhaseMass]
  | succ attempts ih =>
      intro coin ledger history data hdata
      let nextLedger := ledger + ({.t, .t} : ResourceLedger BK05ResourceToken)
      rw [tSupply]
      simp only [tSupplyAcceptedPhaseMass, List.map_cons, List.sum_cons]
      change
        (LinearMap.trace Complex QubitSpace
          (phaseBranchRaw (tAcceptedPhaseRaw tMagicState) data coin)).re +
          tSupplyAcceptedPhaseMass coin
            (tSupply tMagicState attempts
              (ledger + ({.t, .t} : ResourceLedger BK05ResourceToken))
              (false :: history) (tRejectedDataRaw data tMagicState)) = _
      rw [tMagicAcceptedPhaseRaw_branch_trace_re data hdata coin]
      rw [ih coin nextLedger (false :: history) (tRejectedDataRaw data tMagicState)
        (tRejectedDataRaw_positive data tMagicState hdata)]
      rw [tMagicRejectedDataRaw_trace_re, pow_succ]
      ring

/-- Accepted supplier mass after either fixed phase coin is bounded by half
the incoming raw trace mass; the missing mass is retained by later rejected
supplier paths rather than normalized away. -/
private theorem tSupply_acceptedPhaseMass_le_half_trace (attempts : Nat)
    (coin : Bool) (ledger : ResourceLedger BK05ResourceToken)
    (history : List Bool) (data : Operator QubitSpace)
    (hdata : LinearMap.IsPositive data) :
    tSupplyAcceptedPhaseMass coin
      (tSupply tMagicState attempts ledger history data) ≤
        (1 / 2 : Real) * (LinearMap.trace Complex QubitSpace data).re := by
  rw [tSupply_acceptedPhaseMass_eq attempts coin ledger history data hdata]
  have htrace : 0 ≤ (LinearMap.trace Complex QubitSpace data).re := by
    exact (Complex.nonneg_iff.mp hdata.trace_nonneg).1
  have hpow : 0 ≤ (1 / 3 : Real) ^ attempts :=
    pow_nonneg (by norm_num) _
  have hcoefficient : (1 - (1 / 3 : Real) ^ attempts) / 2 ≤ 1 / 2 := by
    linarith
  exact mul_le_mul_of_nonneg_right hcoefficient htrace

private theorem rawMassOfKind_flatMap (kind : BK05RawLeafKind)
    (outcomes : List BK05TSupplyOutcome)
    (continuation : BK05TSupplyOutcome → List BK05RawLeaf) :
    rawMassOfKind kind (outcomes.flatMap continuation) =
      (outcomes.map fun outcome =>
        rawMassOfKind kind (continuation outcome)).sum := by
  induction outcomes with
  | nil => simp [rawMassOfKind, rawMass]
  | cons outcome outcomes ih =>
      rw [List.flatMap_cons, rawMassOfKind_append, ih]
      simp

private theorem tSupplyAcceptedPhaseMass_linear_combination
    (outcomes : List BK05TSupplyOutcome) (trueCoeff falseCoeff : Real) :
    (outcomes.map fun outcome =>
      match outcome with
      | .accepted _ _ data phaseResource =>
          trueCoeff * (LinearMap.trace Complex QubitSpace
            (phaseBranchRaw phaseResource data true)).re +
            falseCoeff * (LinearMap.trace Complex QubitSpace
              (phaseBranchRaw phaseResource data false)).re
      | .exhausted _ _ _ => 0).sum =
        trueCoeff * tSupplyAcceptedPhaseMass true outcomes +
          falseCoeff * tSupplyAcceptedPhaseMass false outcomes := by
  induction outcomes with
  | nil => simp [tSupplyAcceptedPhaseMass]
  | cons outcome outcomes ih =>
      cases outcome <;> simp [tSupplyAcceptedPhaseMass, ih] <;> ring

/-- The literal T retry coefficient: each phase coin is reached only through
the accepted mass of a bounded fresh-pair supplier. -/
private def tPhaseExhaustionCoeff (pairAttempts : Nat) (target : ZMod 12) :
    Nat → ZMod 12 → Real
  | 0, position => if position = target then 0 else 1
  | remaining + 1, position =>
      if position = target then 0 else
        ((1 - (1 / 3 : Real) ^ pairAttempts) / 2) *
          (tPhaseExhaustionCoeff pairAttempts target remaining (position + 1) +
            tPhaseExhaustionCoeff pairAttempts target remaining (position - 1))

/-- The actual T phase-retry exhaustion mass factors through the literal
accepted supplier branches.  Supplier-exhausted outcomes remain present in
the `flatMap`, but contribute zero to this one `.phaseExhausted` submass. -/
private theorem tRetry_phaseExhausted_mass_eq_coeff
    (pairAttempts : Nat) (target : ZMod 12) (remaining : Nat) :
    ∀ (position : ZMod 12) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      rawMassOfKind .phaseExhausted
        (tRetry tMagicState pairAttempts target remaining position ledger history data) =
        tPhaseExhaustionCoeff pairAttempts target remaining position *
          (LinearMap.trace Complex QubitSpace data).re := by
  induction remaining with
  | zero =>
      intro position ledger history data _
      by_cases htarget : position = target <;>
        simp [tRetry, htarget, rawMassOfKind, rawMass, rawWeight,
          tPhaseExhaustionCoeff]
  | succ remaining ih =>
      intro position ledger history data hdata
      by_cases htarget : position = target
      · simp [tRetry, htarget, rawMassOfKind, rawMass, rawWeight,
          tPhaseExhaustionCoeff]
      · rw [tRetry, if_neg htarget]
        let continuation : BK05TSupplyOutcome → List BK05RawLeaf := fun supplied =>
          match supplied with
          | .accepted nextLedger nextHistory nextData phaseResource =>
              tRetry tMagicState pairAttempts target remaining (position + 1) nextLedger
                  (true :: nextHistory) (phaseBranchRaw phaseResource nextData true)
                ++
              tRetry tMagicState pairAttempts target remaining (position - 1) nextLedger
                  (false :: nextHistory) (phaseBranchRaw phaseResource nextData false)
          | .exhausted nextLedger nextHistory nextData =>
              [⟨.tPairExhausted, nextHistory, nextLedger, nextData⟩]
        let trueCoeff :=
          tPhaseExhaustionCoeff pairAttempts target remaining (position + 1)
        let falseCoeff :=
          tPhaseExhaustionCoeff pairAttempts target remaining (position - 1)
        change rawMassOfKind .phaseExhausted
          ((tSupply tMagicState pairAttempts ledger history data).flatMap continuation) = _
        have hcontinuation : ∀ supplied,
            supplied ∈ tSupply tMagicState pairAttempts ledger history data →
            rawMassOfKind .phaseExhausted (continuation supplied) =
              match supplied with
              | .accepted _ _ nextData phaseResource =>
                  trueCoeff * (LinearMap.trace Complex QubitSpace
                    (phaseBranchRaw phaseResource nextData true)).re +
                    falseCoeff * (LinearMap.trace Complex QubitSpace
                      (phaseBranchRaw phaseResource nextData false)).re
              | .exhausted _ _ _ => 0 := by
          intro supplied hsupply
          cases supplied with
          | accepted nextLedger nextHistory nextData phaseResource =>
              have hnextData := tSupply_outcome_data_positive tMagicState pairAttempts
                ledger history data hdata
                (.accepted nextLedger nextHistory nextData phaseResource) hsupply
              have hphase := tSupply_accepted_phase_positive tMagicState pairAttempts
                ledger history data nextLedger nextHistory nextData phaseResource hsupply
              simp only [continuation]
              rw [rawMassOfKind_append]
              rw [ih (position + 1) nextLedger (true :: nextHistory)
                (phaseBranchRaw phaseResource nextData true)
                (phaseBranchRaw_positive phaseResource nextData hphase hnextData true)]
              rw [ih (position - 1) nextLedger (false :: nextHistory)
                (phaseBranchRaw phaseResource nextData false)
                (phaseBranchRaw_positive phaseResource nextData hphase hnextData false)]
          | exhausted nextLedger nextHistory nextData =>
              simp [continuation, rawMassOfKind, rawMass, rawWeight]
        have hterms :
            ((tSupply tMagicState pairAttempts ledger history data).map fun supplied =>
              rawMassOfKind .phaseExhausted (continuation supplied)).sum =
              ((tSupply tMagicState pairAttempts ledger history data).map fun supplied =>
                match supplied with
                | .accepted _ _ nextData phaseResource =>
                    trueCoeff * (LinearMap.trace Complex QubitSpace
                      (phaseBranchRaw phaseResource nextData true)).re +
                      falseCoeff * (LinearMap.trace Complex QubitSpace
                        (phaseBranchRaw phaseResource nextData false)).re
                | .exhausted _ _ _ => 0).sum := by
          congr 1
          apply List.map_congr_left
          intro supplied hsupply
          exact hcontinuation supplied hsupply
        calc
          rawMassOfKind .phaseExhausted
              ((tSupply tMagicState pairAttempts ledger history data).flatMap continuation) =
              ((tSupply tMagicState pairAttempts ledger history data).map fun supplied =>
                rawMassOfKind .phaseExhausted (continuation supplied)).sum :=
            rawMassOfKind_flatMap .phaseExhausted _ _
          _ = ((tSupply tMagicState pairAttempts ledger history data).map fun supplied =>
                match supplied with
                | .accepted _ _ nextData phaseResource =>
                    trueCoeff * (LinearMap.trace Complex QubitSpace
                      (phaseBranchRaw phaseResource nextData true)).re +
                      falseCoeff * (LinearMap.trace Complex QubitSpace
                        (phaseBranchRaw phaseResource nextData false)).re
                | .exhausted _ _ _ => 0).sum := hterms
          _ = trueCoeff * tSupplyAcceptedPhaseMass true
                (tSupply tMagicState pairAttempts ledger history data) +
              falseCoeff * tSupplyAcceptedPhaseMass false
                (tSupply tMagicState pairAttempts ledger history data) :=
            tSupplyAcceptedPhaseMass_linear_combination _ trueCoeff falseCoeff
          _ = tPhaseExhaustionCoeff pairAttempts target (remaining + 1) position *
              (LinearMap.trace Complex QubitSpace data).re := by
            rw [tSupply_acceptedPhaseMass_eq pairAttempts true ledger history data hdata,
              tSupply_acceptedPhaseMass_eq pairAttempts false ledger history data hdata]
            dsimp [trueCoeff, falseCoeff]
            simp only [tPhaseExhaustionCoeff, if_neg htarget]
            ring

private theorem tPhaseAcceptance_nonneg (pairAttempts : Nat) :
    0 ≤ (1 - (1 / 3 : Real) ^ pairAttempts) / 2 := by
  have hpow : (1 / 3 : Real) ^ pairAttempts ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  linarith

private theorem tPhaseAcceptance_le_half (pairAttempts : Nat) :
    (1 - (1 / 3 : Real) ^ pairAttempts) / 2 ≤ 1 / 2 := by
  have hpow : 0 ≤ (1 / 3 : Real) ^ pairAttempts :=
    pow_nonneg (by norm_num) _
  linarith

private theorem tPhaseExhaustionCoeff_nonneg
    (pairAttempts : Nat) (target : ZMod 12) :
    ∀ remaining position,
      0 ≤ tPhaseExhaustionCoeff pairAttempts target remaining position := by
  intro remaining
  induction remaining with
  | zero =>
      intro position
      by_cases hposition : position = target <;>
        simp [tPhaseExhaustionCoeff, hposition]
  | succ remaining ih =>
      intro position
      by_cases hposition : position = target
      · simp [tPhaseExhaustionCoeff, hposition]
      · rw [tPhaseExhaustionCoeff, if_neg hposition]
        exact mul_nonneg (tPhaseAcceptance_nonneg pairAttempts)
          (add_nonneg (ih (position + 1)) (ih (position - 1)))

private theorem tPhaseExhaustionCoeff_target
    (pairAttempts : Nat) (target : ZMod 12) : ∀ remaining,
    tPhaseExhaustionCoeff pairAttempts target remaining target = 0 := by
  intro remaining
  cases remaining <;> simp [tPhaseExhaustionCoeff]

private theorem tPhaseExhaustionCoeff_le_of_bound
    (pairAttempts : Nat) (target : ZMod 12) (remaining extra : Nat) (bound : Real)
    (hbound_nonneg : 0 ≤ bound)
    (hbound : ∀ position,
      tPhaseExhaustionCoeff pairAttempts target remaining position ≤ bound) :
    ∀ position,
      tPhaseExhaustionCoeff pairAttempts target (extra + remaining) position ≤ bound := by
  induction extra with
  | zero => simpa using hbound
  | succ extra ih =>
      intro position
      rw [Nat.succ_add]
      by_cases hposition : position = target
      · subst position
        simpa [tPhaseExhaustionCoeff_target] using hbound_nonneg
      · rw [tPhaseExhaustionCoeff, if_neg hposition]
        have hplus := ih (position + 1)
        have hminus := ih (position - 1)
        have hsum_nonneg : 0 ≤
            tPhaseExhaustionCoeff pairAttempts target (extra + remaining) (position + 1) +
              tPhaseExhaustionCoeff pairAttempts target (extra + remaining) (position - 1) :=
          add_nonneg
            (tPhaseExhaustionCoeff_nonneg pairAttempts target _ _)
            (tPhaseExhaustionCoeff_nonneg pairAttempts target _ _)
        have hsum_le :
            tPhaseExhaustionCoeff pairAttempts target (extra + remaining) (position + 1) +
              tPhaseExhaustionCoeff pairAttempts target (extra + remaining) (position - 1) ≤
                2 * bound := by
          linarith
        calc
          ((1 - (1 / 3 : Real) ^ pairAttempts) / 2) *
              (tPhaseExhaustionCoeff pairAttempts target (extra + remaining) (position + 1) +
                tPhaseExhaustionCoeff pairAttempts target (extra + remaining) (position - 1)) ≤
              (1 / 2 : Real) *
                (tPhaseExhaustionCoeff pairAttempts target (extra + remaining) (position + 1) +
                  tPhaseExhaustionCoeff pairAttempts target (extra + remaining) (position - 1)) :=
            mul_le_mul_of_nonneg_right (tPhaseAcceptance_le_half pairAttempts) hsum_nonneg
          _ ≤ (1 / 2 : Real) * (2 * bound) :=
            mul_le_mul_of_nonneg_left hsum_le (by norm_num)
          _ = bound := by ring

private theorem tPhaseExhaustionCoeff_path_le
    (pairAttempts : Nat) (target : ZMod 12) (remaining : Nat) (bound : Real)
    (hbound_nonneg : 0 ≤ bound)
    (hbound : ∀ position,
      tPhaseExhaustionCoeff pairAttempts target remaining position ≤ bound) :
    ∀ (coins : List Bool) (position : ZMod 12),
      PhaseRetry.visitsTarget position target coins →
      tPhaseExhaustionCoeff pairAttempts target (coins.length + remaining) position ≤
        (1 - (1 / 2 : Real) ^ coins.length) * bound := by
  intro coins
  induction coins with
  | nil =>
      intro position hvisit
      have hposition : target = position := by
        simpa [PhaseRetry.visitsTarget, PhaseRetry.positions] using hvisit
      subst position
      simp [tPhaseExhaustionCoeff_target]
  | cons coin coins ih =>
      intro position hvisit
      by_cases hposition : position = target
      · subst position
        rw [tPhaseExhaustionCoeff_target]
        exact mul_nonneg
          (sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))) hbound_nonneg
      · have htail : PhaseRetry.visitsTarget
            (position + PhaseRetry.signedIncrement coin) target coins := by
          unfold PhaseRetry.visitsTarget at hvisit ⊢
          simp only [PhaseRetry.positions, List.mem_cons] at hvisit
          exact hvisit.resolve_left (Ne.symm hposition)
        rw [List.length_cons, Nat.succ_add, tPhaseExhaustionCoeff, if_neg hposition]
        have hotherPlus := tPhaseExhaustionCoeff_le_of_bound pairAttempts target
          remaining coins.length bound hbound_nonneg hbound (position + 1)
        have hotherMinus := tPhaseExhaustionCoeff_le_of_bound pairAttempts target
          remaining coins.length bound hbound_nonneg hbound (position - 1)
        have hsum_nonneg : 0 ≤
            tPhaseExhaustionCoeff pairAttempts target (coins.length + remaining) (position + 1) +
              tPhaseExhaustionCoeff pairAttempts target (coins.length + remaining) (position - 1) :=
          add_nonneg
            (tPhaseExhaustionCoeff_nonneg pairAttempts target _ _)
            (tPhaseExhaustionCoeff_nonneg pairAttempts target _ _)
        cases coin
        · have hchosen := ih (position - 1)
            (by simpa [PhaseRetry.signedIncrement, sub_eq_add_neg] using htail)
          have hsum_le :
              tPhaseExhaustionCoeff pairAttempts target (coins.length + remaining) (position + 1) +
                tPhaseExhaustionCoeff pairAttempts target (coins.length + remaining) (position - 1) ≤
                  bound + (1 - (1 / 2 : Real) ^ coins.length) * bound := by
            linarith
          calc
            ((1 - (1 / 3 : Real) ^ pairAttempts) / 2) *
                (tPhaseExhaustionCoeff pairAttempts target (coins.length + remaining) (position + 1) +
                  tPhaseExhaustionCoeff pairAttempts target (coins.length + remaining) (position - 1)) ≤
                (1 / 2 : Real) *
                  (tPhaseExhaustionCoeff pairAttempts target (coins.length + remaining) (position + 1) +
                    tPhaseExhaustionCoeff pairAttempts target (coins.length + remaining) (position - 1)) :=
              mul_le_mul_of_nonneg_right (tPhaseAcceptance_le_half pairAttempts) hsum_nonneg
            _ ≤ (1 / 2 : Real) * (bound + (1 - (1 / 2 : Real) ^ coins.length) * bound) :=
              mul_le_mul_of_nonneg_left hsum_le (by norm_num)
            _ = (1 - (1 / 2 : Real) ^ (coins.length + 1)) * bound := by
              rw [pow_succ]
              ring
        · have hchosen := ih (position + 1)
            (by simpa [PhaseRetry.signedIncrement] using htail)
          have hsum_le :
              tPhaseExhaustionCoeff pairAttempts target (coins.length + remaining) (position + 1) +
                tPhaseExhaustionCoeff pairAttempts target (coins.length + remaining) (position - 1) ≤
                  (1 - (1 / 2 : Real) ^ coins.length) * bound + bound := by
            linarith
          calc
            ((1 - (1 / 3 : Real) ^ pairAttempts) / 2) *
                (tPhaseExhaustionCoeff pairAttempts target (coins.length + remaining) (position + 1) +
                  tPhaseExhaustionCoeff pairAttempts target (coins.length + remaining) (position - 1)) ≤
                (1 / 2 : Real) *
                  (tPhaseExhaustionCoeff pairAttempts target (coins.length + remaining) (position + 1) +
                    tPhaseExhaustionCoeff pairAttempts target (coins.length + remaining) (position - 1)) :=
              mul_le_mul_of_nonneg_right (tPhaseAcceptance_le_half pairAttempts) hsum_nonneg
            _ ≤ (1 / 2 : Real) * ((1 - (1 / 2 : Real) ^ coins.length) * bound + bound) :=
              mul_le_mul_of_nonneg_left hsum_le (by norm_num)
            _ = (1 - (1 / 2 : Real) ^ (coins.length + 1)) * bound := by
              rw [pow_succ]
              ring

private theorem tPhaseExhaustionCoeff_twelve_step_le
    (pairAttempts : Nat) (target position : ZMod 12) (remaining : Nat) (bound : Real)
    (hbound_nonneg : 0 ≤ bound)
    (hbound : ∀ next,
      tPhaseExhaustionCoeff pairAttempts target remaining next ≤ bound) :
    tPhaseExhaustionCoeff pairAttempts target (12 + remaining) position ≤
      (4095 / 4096 : Real) * bound := by
  have hpath := tPhaseExhaustionCoeff_path_le pairAttempts target remaining bound
    hbound_nonneg hbound (PhaseRetry.positiveBlock 12) position
    (PhaseRetry.positiveBlock_visits_target_twelve position target)
  norm_num [PhaseRetry.positiveBlock] at hpath ⊢
  exact hpath

private theorem tPhaseExhaustionCoeff_blocks_le
    (pairAttempts : Nat) (target position : ZMod 12) (blocks : Nat) :
    tPhaseExhaustionCoeff pairAttempts target (12 * blocks) position ≤
      (4095 / 4096 : Real) ^ blocks := by
  induction blocks generalizing position with
  | zero =>
      by_cases hposition : position = target <;>
        simp [tPhaseExhaustionCoeff, hposition]
  | succ blocks ih =>
      rw [Nat.mul_succ, pow_succ]
      have hstep := tPhaseExhaustionCoeff_twelve_step_le pairAttempts target position
        (12 * blocks) ((4095 / 4096 : Real) ^ blocks)
        (pow_nonneg (by norm_num) _) ih
      rw [Nat.add_comm] at hstep
      nlinarith

private theorem tActualRawTree_phaseExhausted_mass_eq_coeff
    (target : ZMod 12) (pairAttempts blocks : Nat) (rho : DensityOperator QubitSpace) :
    rawMassOfKind .phaseExhausted
      (tActualRawTree tMagicState pairAttempts target blocks rho) =
      tPhaseExhaustionCoeff pairAttempts target (12 * blocks) 0 := by
  rw [tActualRawTree,
    tRetry_phaseExhausted_mass_eq_coeff pairAttempts target (12 * blocks)
      0 0 [] rho.toOperator rho.positive]
  simp [rho.trace_one]

/-- The literal unconditioned T retry tree's phase-exhausted submass decays
at the order-twelve certificate rate.  Supplier-exhausted leaves remain in
the actual tree and are deliberately not included in this submass. -/
theorem tActualRawTree_phaseTail_le
    (target : ZMod 12) (pairAttempts blocks : Nat) (rho : DensityOperator QubitSpace) :
    rawMassOfKind .phaseExhausted
      (tActualRawTree tMagicState pairAttempts target blocks rho) ≤
      (4095 / 4096 : Real) ^ blocks := by
  rw [tActualRawTree_phaseExhausted_mass_eq_coeff]
  exact tPhaseExhaustionCoeff_blocks_le pairAttempts target 0 blocks

private theorem List.map_sum_le_map_sum_of_mem
    {α : Type*} (items : List α) (left right : α → Real)
    (hitem : ∀ item, item ∈ items → left item ≤ right item) :
    (items.map left).sum ≤ (items.map right).sum := by
  induction items with
  | nil => simp
  | cons item items ih =>
      simp only [List.mem_cons, List.map_cons, List.sum_cons]
      exact add_le_add (hitem item (by simp))
        (ih (fun item hmem => hitem item (by simp [hmem])))

private theorem tSupplyAcceptedAndExhaustedMass_combination
    (outcomes : List BK05TSupplyOutcome) (acceptedCoeff : Real) :
    (outcomes.map fun outcome =>
      match outcome with
      | .accepted _ _ data phaseResource =>
          acceptedCoeff *
            ((LinearMap.trace Complex QubitSpace
              (phaseBranchRaw phaseResource data true)).re +
              (LinearMap.trace Complex QubitSpace
                (phaseBranchRaw phaseResource data false)).re)
      | .exhausted _ _ data => (LinearMap.trace Complex QubitSpace data).re).sum =
        acceptedCoeff *
          (tSupplyAcceptedPhaseMass true outcomes +
            tSupplyAcceptedPhaseMass false outcomes) +
          tSupplyExhaustedMass outcomes := by
  induction outcomes with
  | nil => simp [tSupplyAcceptedPhaseMass, tSupplyExhaustedMass]
  | cons outcome outcomes ih =>
      cases outcome <;>
        simp [tSupplyAcceptedPhaseMass, tSupplyExhaustedMass, ih] <;> ring

/-- The retained supplier-exhaustion submass of the actual T retry tree is
bounded by one all-rejected supplier mass per reached phase site. -/
private theorem tRetry_pairExhaustion_mass_le
    (pairAttempts : Nat) (target : ZMod 12) (remaining : Nat) :
    ∀ (position : ZMod 12) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      rawMassOfKind .tPairExhausted
        (tRetry tMagicState pairAttempts target remaining position ledger history data) ≤
        (remaining : Real) * (1 / 3 : Real) ^ pairAttempts *
          (LinearMap.trace Complex QubitSpace data).re := by
  induction remaining with
  | zero =>
      intro position ledger history data _
      by_cases htarget : position = target <;>
        simp [tRetry, htarget, rawMassOfKind, rawMass, rawWeight]
  | succ remaining ih =>
      intro position ledger history data hdata
      have htrace : 0 ≤ (LinearMap.trace Complex QubitSpace data).re := by
        exact (Complex.nonneg_iff.mp hdata.trace_nonneg).1
      have hreject : 0 ≤ (1 / 3 : Real) ^ pairAttempts :=
        pow_nonneg (by norm_num) _
      by_cases htarget : position = target
      · have hbound : 0 ≤
            ((remaining + 1 : Nat) : Real) * (1 / 3 : Real) ^ pairAttempts *
              (LinearMap.trace Complex QubitSpace data).re := by
            exact mul_nonneg
              (mul_nonneg (by positivity) hreject) htrace
        simpa [tRetry, htarget, rawMassOfKind, rawMass, rawWeight] using hbound
      · rw [tRetry, if_neg htarget]
        let continuation : BK05TSupplyOutcome → List BK05RawLeaf := fun supplied =>
          match supplied with
          | .accepted nextLedger nextHistory nextData phaseResource =>
              tRetry tMagicState pairAttempts target remaining (position + 1) nextLedger
                  (true :: nextHistory) (phaseBranchRaw phaseResource nextData true)
                ++
              tRetry tMagicState pairAttempts target remaining (position - 1) nextLedger
                  (false :: nextHistory) (phaseBranchRaw phaseResource nextData false)
          | .exhausted nextLedger nextHistory nextData =>
              [⟨.tPairExhausted, nextHistory, nextLedger, nextData⟩]
        let acceptedCoeff : Real := (remaining : Real) * (1 / 3 : Real) ^ pairAttempts
        let continuationBound : BK05TSupplyOutcome → Real := fun supplied =>
          match supplied with
          | .accepted _ _ nextData phaseResource =>
              acceptedCoeff *
                ((LinearMap.trace Complex QubitSpace
                  (phaseBranchRaw phaseResource nextData true)).re +
                  (LinearMap.trace Complex QubitSpace
                    (phaseBranchRaw phaseResource nextData false)).re)
          | .exhausted _ _ nextData =>
              (LinearMap.trace Complex QubitSpace nextData).re
        change rawMassOfKind .tPairExhausted
          ((tSupply tMagicState pairAttempts ledger history data).flatMap continuation) ≤ _
        have hcontinuation : ∀ supplied,
            supplied ∈ tSupply tMagicState pairAttempts ledger history data →
            rawMassOfKind .tPairExhausted (continuation supplied) ≤
              continuationBound supplied := by
          intro supplied hsupply
          cases supplied with
          | accepted nextLedger nextHistory nextData phaseResource =>
              have hnextData := tSupply_outcome_data_positive tMagicState pairAttempts
                ledger history data hdata
                (.accepted nextLedger nextHistory nextData phaseResource) hsupply
              have hphase := tSupply_accepted_phase_positive tMagicState pairAttempts
                ledger history data nextLedger nextHistory nextData phaseResource hsupply
              simp only [continuation, continuationBound]
              rw [rawMassOfKind_append]
              calc
                rawMassOfKind .tPairExhausted
                    (tRetry tMagicState pairAttempts target remaining (position + 1) nextLedger
                      (true :: nextHistory) (phaseBranchRaw phaseResource nextData true)) +
                    rawMassOfKind .tPairExhausted
                      (tRetry tMagicState pairAttempts target remaining (position - 1) nextLedger
                        (false :: nextHistory) (phaseBranchRaw phaseResource nextData false)) ≤
                    acceptedCoeff * (LinearMap.trace Complex QubitSpace
                      (phaseBranchRaw phaseResource nextData true)).re +
                      acceptedCoeff * (LinearMap.trace Complex QubitSpace
                        (phaseBranchRaw phaseResource nextData false)).re := by
                      apply add_le_add
                      · exact ih (position + 1) nextLedger (true :: nextHistory)
                          (phaseBranchRaw phaseResource nextData true)
                          (phaseBranchRaw_positive phaseResource nextData hphase hnextData true)
                      · exact ih (position - 1) nextLedger (false :: nextHistory)
                          (phaseBranchRaw phaseResource nextData false)
                          (phaseBranchRaw_positive phaseResource nextData hphase hnextData false)
                _ = acceptedCoeff *
                    ((LinearMap.trace Complex QubitSpace
                      (phaseBranchRaw phaseResource nextData true)).re +
                      (LinearMap.trace Complex QubitSpace
                        (phaseBranchRaw phaseResource nextData false)).re) := by ring
          | exhausted nextLedger nextHistory nextData =>
              simp [continuation, continuationBound, rawMassOfKind, rawMass, rawWeight]
        calc
          rawMassOfKind .tPairExhausted
              ((tSupply tMagicState pairAttempts ledger history data).flatMap continuation) =
              ((tSupply tMagicState pairAttempts ledger history data).map fun supplied =>
                rawMassOfKind .tPairExhausted (continuation supplied)).sum :=
            rawMassOfKind_flatMap .tPairExhausted _ _
          _ ≤ ((tSupply tMagicState pairAttempts ledger history data).map
                continuationBound).sum :=
            List.map_sum_le_map_sum_of_mem _ _ _ hcontinuation
          _ = acceptedCoeff *
                (tSupplyAcceptedPhaseMass true
                  (tSupply tMagicState pairAttempts ledger history data) +
                  tSupplyAcceptedPhaseMass false
                    (tSupply tMagicState pairAttempts ledger history data)) +
                tSupplyExhaustedMass
                  (tSupply tMagicState pairAttempts ledger history data) :=
            tSupplyAcceptedAndExhaustedMass_combination _ acceptedCoeff
          _ ≤ ((remaining + 1 : Nat) : Real) * (1 / 3 : Real) ^ pairAttempts *
                (LinearMap.trace Complex QubitSpace data).re := by
            rw [tSupply_acceptedPhaseMass_eq pairAttempts true ledger history data hdata,
              tSupply_acceptedPhaseMass_eq pairAttempts false ledger history data hdata,
              tSupply_exhaustedMass_eq pairAttempts ledger history data hdata]
            dsimp [acceptedCoeff]
            have hgap : 0 ≤ (remaining : Real) * (1 / 3 : Real) ^ pairAttempts *
                (1 / 3 : Real) ^ pairAttempts *
                  (LinearMap.trace Complex QubitSpace data).re := by
              exact mul_nonneg
                (mul_nonneg
                  (mul_nonneg (by positivity) hreject) hreject) htrace
            calc
              (remaining : Real) * (1 / 3 : Real) ^ pairAttempts *
                    (((1 - (1 / 3 : Real) ^ pairAttempts) / 2) *
                      (LinearMap.trace Complex QubitSpace data).re +
                      ((1 - (1 / 3 : Real) ^ pairAttempts) / 2) *
                        (LinearMap.trace Complex QubitSpace data).re) +
                  (1 / 3 : Real) ^ pairAttempts *
                    (LinearMap.trace Complex QubitSpace data).re =
                  ((remaining + 1 : Nat) : Real) * (1 / 3 : Real) ^ pairAttempts *
                    (LinearMap.trace Complex QubitSpace data).re -
                    (remaining : Real) * (1 / 3 : Real) ^ pairAttempts *
                      (1 / 3 : Real) ^ pairAttempts *
                        (LinearMap.trace Complex QubitSpace data).re := by
                  push_cast
                  ring
              _ ≤ ((remaining + 1 : Nat) : Real) * (1 / 3 : Real) ^ pairAttempts *
                    (LinearMap.trace Complex QubitSpace data).re :=
                  sub_le_self _ hgap

/-- The actual order-twelve T retry tree retains all supplier-exhaustion
leaves, whose total raw mass is at most one all-rejected supplier factor per
phase site. -/
theorem tActualRawTree_pairExhaustion_le
    (target : ZMod 12) (pairAttempts blocks : Nat) (rho : DensityOperator QubitSpace) :
    rawMassOfKind .tPairExhausted
      (tActualRawTree tMagicState pairAttempts target blocks rho) ≤
      (12 * blocks : Real) * (1 / 3 : Real) ^ pairAttempts := by
  change rawMassOfKind .tPairExhausted
      (tRetry tMagicState pairAttempts target (12 * blocks) 0 0 [] rho.toOperator) ≤ _
  calc
    rawMassOfKind .tPairExhausted
        (tRetry tMagicState pairAttempts target (12 * blocks) 0 0 [] rho.toOperator) ≤
        ((12 * blocks : Nat) : Real) * (1 / 3 : Real) ^ pairAttempts *
          (LinearMap.trace Complex QubitSpace rho.toOperator).re :=
      tRetry_pairExhaustion_mass_le pairAttempts target (12 * blocks)
        0 0 [] rho.toOperator rho.positive
    _ = (12 * blocks : Real) * (1 / 3 : Real) ^ pairAttempts := by
      simp [rho.trace_one]

private theorem rawAggregate_append (left right : List BK05RawLeaf) :
    rawAggregate (left ++ right) = rawAggregate left + rawAggregate right := by
  simp [rawAggregate]

/-- The aggregate of one literal H retry continuation, packaged as a linear
map in its (possibly subnormalised) raw input.  Ledger and history bookkeeping
does not affect this operator-valued continuation. -/
private noncomputable def hRetryAggregateLinear
    (h : DensityOperator QubitSpace) (target : ZMod 8) :
    Nat → ZMod 8 → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | 0, _ => LinearMap.id
  | remaining + 1, position =>
      if position = target then LinearMap.id else
        (hRetryAggregateLinear h target remaining (position + 1)).comp
            (phaseBranchRawLinear (hPhaseRaw h) true) +
        (hRetryAggregateLinear h target remaining (position - 1)).comp
            (phaseBranchRawLinear (hPhaseRaw h) false)

/-- The local linear continuation is definitionally the aggregate of the
actual retained H tree, including target and exhaustion leaves. -/
private theorem hRetryAggregateLinear_apply
    (h : DensityOperator QubitSpace) (target : ZMod 8) (remaining : Nat) :
    ∀ (position : ZMod 8) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace),
      hRetryAggregateLinear h target remaining position data =
        rawAggregate (hRetry h target remaining position ledger history data) := by
  induction remaining with
  | zero =>
      intro position ledger history data
      by_cases htarget : position = target <;>
        simp [hRetry, hRetryAggregateLinear, rawAggregate, htarget]
  | succ remaining ih =>
      intro position ledger history data
      by_cases htarget : position = target
      · simp [hRetry, hRetryAggregateLinear, htarget, rawAggregate]
      · rw [hRetry, if_neg htarget, rawAggregate_append]
        simp only [hRetryAggregateLinear, if_neg htarget, LinearMap.add_apply,
          LinearMap.comp_apply, phaseBranchRawLinear_apply]
        rw [ih (position + 1)
          (ledger + ({.h} : ResourceLedger BK05ResourceToken)) (true :: history),
          ih (position - 1)
            (ledger + ({.h} : ResourceLedger BK05ResourceToken)) (false :: history)]
        simp [hStepRaw]

/-- Every branch-summed H continuation maps positive raw inputs to positive
raw outputs. -/
private theorem hRetryAggregateLinear_positive
    (h : DensityOperator QubitSpace) (target : ZMod 8) :
    ∀ (remaining : Nat) (position : ZMod 8) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      LinearMap.IsPositive (hRetryAggregateLinear h target remaining position data) := by
  intro remaining
  induction remaining with
  | zero =>
      intro position data hdata
      simpa [hRetryAggregateLinear] using hdata
  | succ remaining ih =>
      intro position data hdata
      by_cases htarget : position = target
      · simpa [hRetryAggregateLinear, htarget] using hdata
      · have htrue := ih (position + 1) (phaseBranchRaw (hPhaseRaw h) data true)
          (phaseBranchRaw_positive (hPhaseRaw h) data (hPhaseRaw_positive h) hdata true)
        have hfalse := ih (position - 1) (phaseBranchRaw (hPhaseRaw h) data false)
          (phaseBranchRaw_positive (hPhaseRaw h) data (hPhaseRaw_positive h) hdata false)
        simpa [hRetryAggregateLinear, htarget, LinearMap.add_apply,
          LinearMap.comp_apply, phaseBranchRawLinear_apply] using htrue.add hfalse

/-- The operator aggregate of every literal H continuation preserves complex
trace only after its two physical branches are summed. -/
private theorem hRetryAggregateLinear_trace
    (h : DensityOperator QubitSpace) (target : ZMod 8) :
    ∀ (remaining : Nat) (position : ZMod 8) (data : Operator QubitSpace),
      LinearMap.trace Complex QubitSpace
        (hRetryAggregateLinear h target remaining position data) =
        LinearMap.trace Complex QubitSpace data := by
  intro remaining
  induction remaining with
  | zero =>
      intro position data
      simp [hRetryAggregateLinear]
  | succ remaining ih =>
      intro position data
      by_cases htarget : position = target
      · simp [hRetryAggregateLinear, htarget]
      · simp only [hRetryAggregateLinear, if_neg htarget, LinearMap.add_apply,
          LinearMap.comp_apply, phaseBranchRawLinear_apply]
        rw [map_add,
          ih (position + 1) (phaseBranchRaw (hPhaseRaw h) data true),
          ih (position - 1) (phaseBranchRaw (hPhaseRaw h) data false)]
        have hsplit := phaseBranchRaw_trace_sum (hPhaseRaw h) data
        rw [hPhaseRaw_trace_one] at hsplit
        simpa using hsplit

private noncomputable def observedBranchLinear (coin : Bool) :
    Operator TwoQubit.TwoQubitSpace →ₗ[Complex] Operator TwoQubit.TwoQubitSpace where
  toFun := fun input =>
    zzMeasurement.instrument.branchOperator (observedRetrySyndrome coin) input
  map_add' := by
    intro input₁ input₂
    classical
    unfold FiniteInstrument.branchOperator
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp [LinearMap.comp_add, LinearMap.add_comp]
  map_smul' := by
    intro scalar input
    classical
    unfold FiniteInstrument.branchOperator
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp [LinearMap.comp_smul, LinearMap.smul_comp]

private theorem observedBranchLinear_apply (coin : Bool)
    (input : Operator TwoQubit.TwoQubitSpace) :
    observedBranchLinear coin input =
      zzMeasurement.instrument.branchOperator (observedRetrySyndrome coin) input :=
  rfl

/-- One branch-summed physical continuation from the injection register.  The
two next maps may differ because they retain their distinct phase histories. -/
private noncomputable def phaseContinuationLinear
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    Operator TwoQubit.TwoQubitSpace →ₗ[Complex] Operator QubitSpace :=
  nextTrue.comp (oneShotPostprocess.toLinearMap.comp (observedBranchLinear true)) +
    nextFalse.comp (oneShotPostprocess.toLinearMap.comp (observedBranchLinear false))

private theorem phaseContinuationLinear_apply
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (input : Operator TwoQubit.TwoQubitSpace) :
    phaseContinuationLinear nextTrue nextFalse input =
      nextTrue (oneShotPostprocess
        (zzMeasurement.instrument.branchOperator (observedRetrySyndrome true) input)) +
      nextFalse (oneShotPostprocess
        (zzMeasurement.instrument.branchOperator (observedRetrySyndrome false) input)) :=
  rfl

private theorem observedBranchPostprocess_trace_sum
    (input : Operator TwoQubit.TwoQubitSpace) :
    LinearMap.trace Complex QubitSpace
        (oneShotPostprocess
          (zzMeasurement.instrument.branchOperator (observedRetrySyndrome true) input)) +
      LinearMap.trace Complex QubitSpace
        (oneShotPostprocess
          (zzMeasurement.instrument.branchOperator (observedRetrySyndrome false) input)) =
        LinearMap.trace Complex TwoQubit.TwoQubitSpace input := by
  have hbranches :
      zzMeasurement.instrument.branchOperator (observedRetrySyndrome true) input +
        zzMeasurement.instrument.branchOperator (observedRetrySyndrome false) input =
          zzMeasurement.instrument.kraus.inducedMap input := by
    have hnotmem : observedRetrySyndrome true ∉
        ({observedRetrySyndrome false} : Finset (JointSyndrome (Fin 1))) := by
      intro hmem
      exact observedRetrySyndromes_ne (by simpa using hmem)
    rw [← zzMeasurement.instrument.sum_branchOperator_eq_inducedMap, retrySyndrome_univ,
      Finset.sum_insert hnotmem, Finset.sum_singleton]
  calc
    LinearMap.trace Complex QubitSpace
        (oneShotPostprocess
          (zzMeasurement.instrument.branchOperator (observedRetrySyndrome true) input)) +
      LinearMap.trace Complex QubitSpace
        (oneShotPostprocess
          (zzMeasurement.instrument.branchOperator (observedRetrySyndrome false) input)) =
        LinearMap.trace Complex TwoQubit.TwoQubitSpace
          (zzMeasurement.instrument.branchOperator (observedRetrySyndrome true) input) +
          LinearMap.trace Complex TwoQubit.TwoQubitSpace
            (zzMeasurement.instrument.branchOperator (observedRetrySyndrome false) input) := by
          simp [oneShotPostprocess.trace_map]
    _ = LinearMap.trace Complex TwoQubit.TwoQubitSpace
          (zzMeasurement.instrument.kraus.inducedMap input) := by
          rw [← map_add, hbranches]
    _ = LinearMap.trace Complex TwoQubit.TwoQubitSpace input := by
          exact zzMeasurement.instrument.kraus.inducedMap_trace_preserving
            (jointStabilizerKrausFamily_complete zzMeasurement.checks zzMeasurement.commute) input

private theorem phaseContinuationLinear_positive
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (htrue : ∀ data, LinearMap.IsPositive data → LinearMap.IsPositive (nextTrue data))
    (hfalse : ∀ data, LinearMap.IsPositive data → LinearMap.IsPositive (nextFalse data))
    (input : Operator TwoQubit.TwoQubitSpace) (hinput : LinearMap.IsPositive input) :
    LinearMap.IsPositive (phaseContinuationLinear nextTrue nextFalse input) := by
  rw [phaseContinuationLinear_apply]
  apply LinearMap.IsPositive.add
  · apply htrue
    apply oneShotPostprocess.map_positive
    exact zzMeasurement.instrument.branchOperator_positive _ hinput
  · apply hfalse
    apply oneShotPostprocess.map_positive
    exact zzMeasurement.instrument.branchOperator_positive _ hinput

private theorem phaseContinuationLinear_trace
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (htrue : ∀ data,
      LinearMap.trace Complex QubitSpace (nextTrue data) =
        LinearMap.trace Complex QubitSpace data)
    (hfalse : ∀ data,
      LinearMap.trace Complex QubitSpace (nextFalse data) =
        LinearMap.trace Complex QubitSpace data)
    (input : Operator TwoQubit.TwoQubitSpace) :
    LinearMap.trace Complex QubitSpace (phaseContinuationLinear nextTrue nextFalse input) =
      LinearMap.trace Complex TwoQubit.TwoQubitSpace input := by
  rw [phaseContinuationLinear_apply, map_add, htrue, hfalse]
  exact observedBranchPostprocess_trace_sum input

/-- A branch-summed observed continuation contracts the trace norm on
self-adjoint raw inputs once both physical outcomes are retained. -/
private theorem phaseContinuationLinear_traceNorm_le
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (htruePositive : ∀ data,
      LinearMap.IsPositive data → LinearMap.IsPositive (nextTrue data))
    (hfalsePositive : ∀ data,
      LinearMap.IsPositive data → LinearMap.IsPositive (nextFalse data))
    (htrueTrace : ∀ data,
      LinearMap.trace Complex QubitSpace (nextTrue data) =
        LinearMap.trace Complex QubitSpace data)
    (hfalseTrace : ∀ data,
      LinearMap.trace Complex QubitSpace (nextFalse data) =
        LinearMap.trace Complex QubitSpace data)
    (input : Operator TwoQubit.TwoQubitSpace) (hinput : input.IsSymmetric) :
    traceNorm (phaseContinuationLinear nextTrue nextFalse input) ≤ traceNorm input := by
  have hdecomp := positivePart_sub_negativePart input hinput
  have hpositive : ∀ data, LinearMap.IsPositive data →
      LinearMap.IsPositive (phaseContinuationLinear nextTrue nextFalse data) := by
    intro data hdata
    exact phaseContinuationLinear_positive nextTrue nextFalse
      htruePositive hfalsePositive data hdata
  have htrace : ∀ data,
      LinearMap.trace Complex QubitSpace (phaseContinuationLinear nextTrue nextFalse data) =
        LinearMap.trace Complex TwoQubit.TwoQubitSpace data := by
    intro data
    exact phaseContinuationLinear_trace nextTrue nextFalse htrueTrace hfalseTrace data
  calc
    traceNorm (phaseContinuationLinear nextTrue nextFalse input) =
        traceNorm (phaseContinuationLinear nextTrue nextFalse (positivePart input) -
          phaseContinuationLinear nextTrue nextFalse (negativePart input)) := by
          rw [← (phaseContinuationLinear nextTrue nextFalse).map_sub, hdecomp]
    _ ≤ traceNorm (phaseContinuationLinear nextTrue nextFalse (positivePart input)) +
        traceNorm (-phaseContinuationLinear nextTrue nextFalse (negativePart input)) := by
          simpa [sub_eq_add_neg] using traceNorm_add_le
            (phaseContinuationLinear nextTrue nextFalse (positivePart input))
            (-phaseContinuationLinear nextTrue nextFalse (negativePart input))
    _ = traceNorm (phaseContinuationLinear nextTrue nextFalse (positivePart input)) +
        traceNorm (phaseContinuationLinear nextTrue nextFalse (negativePart input)) := by
          rw [traceNorm_neg]
    _ = Complex.re (LinearMap.trace Complex QubitSpace
          (phaseContinuationLinear nextTrue nextFalse (positivePart input))) +
        Complex.re (LinearMap.trace Complex QubitSpace
          (phaseContinuationLinear nextTrue nextFalse (negativePart input))) := by
          rw [traceNorm_eq_re_trace_of_positive _
              (hpositive _ (positivePart_positive input)),
            traceNorm_eq_re_trace_of_positive _
              (hpositive _ (negativePart_positive input))]
    _ = Complex.re (LinearMap.trace Complex TwoQubit.TwoQubitSpace (positivePart input)) +
        Complex.re (LinearMap.trace Complex TwoQubit.TwoQubitSpace (negativePart input)) := by
          rw [htrace, htrace]
    _ = traceNorm (positivePart input) + traceNorm (negativePart input) := by
          rw [traceNorm_eq_re_trace_of_positive _ (positivePart_positive input),
            traceNorm_eq_re_trace_of_positive _ (negativePart_positive input)]
    _ = traceNorm input := (traceNorm_eq_sum_parts input hinput).symm

/-- The fixed-resource tensor estimate is homogeneous in a positive raw data
factor, so recursive subnormalised H branches keep their trace scale. -/
private theorem traceNorm_tensor_right_resource_le_raw
    (data : Operator QubitSpace) (hdata : LinearMap.IsPositive data)
    (resource ideal : DensityOperator QubitSpace) :
    traceNorm
      (TensorProduct.map data resource.toOperator -
        TensorProduct.map data ideal.toOperator) ≤
      (LinearMap.trace Complex QubitSpace data).re *
        traceNorm (resource.toOperator - ideal.toOperator) := by
  let scale : Real := (LinearMap.trace Complex QubitSpace data).re
  have hscale_nonneg : 0 ≤ scale := by
    exact (Complex.nonneg_iff.mp hdata.trace_nonneg).1
  by_cases hscale : scale = 0
  · have hnorm : traceNorm data = 0 := by
      rw [traceNorm_eq_re_trace_of_positive data hdata]
      exact hscale
    have hzero : data = 0 := (traceNorm_eq_zero_iff data).mp hnorm
    subst data
    have htensorTraceNormZero :
        traceNorm (0 : Operator (CompositeSystem QubitSpace QubitSpace)) = 0 :=
      (traceNorm_eq_zero_iff 0).mpr rfl
    rw [TensorProduct.map_zero_left, TensorProduct.map_zero_left]
    change traceNorm (0 - 0) ≤ (LinearMap.trace Complex QubitSpace 0).re *
      traceNorm (resource.toOperator - ideal.toOperator)
    simp only [zero_sub, map_zero, Complex.zero_re, zero_mul]
    simpa using (le_of_eq htensorTraceNormZero)
  · have htrace : LinearMap.trace Complex QubitSpace data = (scale : Complex) := by
      apply Complex.ext
      · rfl
      · simpa using (Complex.nonneg_iff.mp hdata.trace_nonneg).2.symm
    let normalized : DensityOperator QubitSpace :=
      { toOperator := ((scale⁻¹ : Real) : Complex) • data
        positive := by
          apply hdata.smul_of_nonneg
          exact_mod_cast inv_nonneg.mpr hscale_nonneg
        trace_one := by
          rw [map_smul, htrace]
          simp only [smul_eq_mul]
          norm_cast
          exact inv_mul_cancel₀ hscale }
    have hdata_eq : data = (scale : Complex) • normalized.toOperator := by
      change data = (scale : Complex) • (((scale⁻¹ : Real) : Complex) • data)
      rw [← mul_smul]
      norm_cast
      rw [mul_inv_cancel₀ hscale, one_smul]
    have hresource : TensorProduct.map data resource.toOperator =
        (scale : Complex) • TensorProduct.map normalized.toOperator resource.toOperator := by
      rw [hdata_eq, TensorProduct.map_smul_left]
    have hideal : TensorProduct.map data ideal.toOperator =
        (scale : Complex) • TensorProduct.map normalized.toOperator ideal.toOperator := by
      rw [hdata_eq, TensorProduct.map_smul_left]
    calc
      traceNorm
          (TensorProduct.map data resource.toOperator -
            TensorProduct.map data ideal.toOperator) =
          traceNorm ((scale : Complex) •
            (TensorProduct.map normalized.toOperator resource.toOperator -
              TensorProduct.map normalized.toOperator ideal.toOperator)) := by
            rw [hresource, hideal]
            rw [smul_sub]
      _ = scale * traceNorm
          (TensorProduct.map normalized.toOperator resource.toOperator -
            TensorProduct.map normalized.toOperator ideal.toOperator) := by
            rw [traceNorm_smul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hscale_nonneg]
      _ ≤ scale * traceNorm (resource.toOperator - ideal.toOperator) := by
            exact mul_le_mul_of_nonneg_left
              (traceNorm_tensor_right_resource_le normalized resource ideal) hscale_nonneg
      _ = (LinearMap.trace Complex QubitSpace data).re *
          traceNorm (resource.toOperator - ideal.toOperator) := by
            rfl

private theorem injectedInputRaw_hResource_difference_le
    (h : DensityOperator QubitSpace) (data : Operator QubitSpace)
    (hdata : LinearMap.IsPositive data) :
    traceNorm
      (injectedInputRaw data (hPhaseRaw h) -
        injectedInputRaw data (hPhaseRaw hMagicState)) ≤
      (LinearMap.trace Complex QubitSpace data).re *
        traceNorm (h.toOperator - hMagicState.toOperator) := by
  let hFrame := hResourceTransport.conjDensity h
  let idealFrame := hResourceTransport.conjDensity hMagicState
  have hhFrame : hFrame.toOperator = hPhaseRaw h := by
    simp [hFrame, hPhaseRaw]
  have hidealFrame : idealFrame.toOperator = hPhaseRaw hMagicState := by
    simp [idealFrame, hPhaseRaw]
  have hdataTrace : 0 ≤ (LinearMap.trace Complex QubitSpace data).re := by
    exact (Complex.nonneg_iff.mp hdata.trace_nonneg).1
  have htensorPositive : LinearMap.IsPositive
      (TensorProduct.map data hFrame.toOperator) := by
    exact ThermalEncoding.tensorMap_positive data hFrame.toOperator hdata hFrame.positive
  have hidealTensorPositive : LinearMap.IsPositive
      (TensorProduct.map data idealFrame.toOperator) := by
    exact ThermalEncoding.tensorMap_positive data idealFrame.toOperator hdata idealFrame.positive
  have htensorSymmetric :
      (TensorProduct.map data hFrame.toOperator -
        TensorProduct.map data idealFrame.toOperator).IsSymmetric :=
    htensorPositive.isSymmetric.sub hidealTensorPositive.isSymmetric
  have hresourceSymmetric :
      (h.toOperator - hMagicState.toOperator).IsSymmetric :=
    h.positive.isSymmetric.sub hMagicState.positive.isSymmetric
  have hframeTransport :
      traceNorm (hFrame.toOperator - idealFrame.toOperator) ≤
        traceNorm (h.toOperator - hMagicState.toOperator) := by
    change traceNorm
        (hResourceTransport.conjOperator h.toOperator -
          hResourceTransport.conjOperator hMagicState.toOperator) ≤ _
    simp only [← UnitaryTransport.conjOperatorLinearMap_apply]
    rw [← hResourceTransport.conjOperatorLinearMap.map_sub]
    exact (QuantumChannel.unitaryConj hResourceTransport).traceNorm_apply_le_of_isSymmetric
      _ hresourceSymmetric
  calc
    traceNorm
        (injectedInputRaw data (hPhaseRaw h) -
          injectedInputRaw data (hPhaseRaw hMagicState)) =
        traceNorm
          (TwoQubit.tensorRegisterTransport.conjOperator
            (TensorProduct.map data hFrame.toOperator) -
            TwoQubit.tensorRegisterTransport.conjOperator
              (TensorProduct.map data idealFrame.toOperator)) := by
          rw [hhFrame, hidealFrame]
          rfl
    _ ≤ traceNorm
          (TensorProduct.map data hFrame.toOperator -
            TensorProduct.map data idealFrame.toOperator) := by
          simp only [← UnitaryTransport.conjOperatorLinearMap_apply]
          rw [← TwoQubit.tensorRegisterTransport.conjOperatorLinearMap.map_sub]
          exact QuantumChannel.traceNorm_apply_le_of_isSymmetric
            (QuantumChannel.unitaryConj TwoQubit.tensorRegisterTransport)
            _ htensorSymmetric
    _ ≤ (LinearMap.trace Complex QubitSpace data).re *
          traceNorm (hFrame.toOperator - idealFrame.toOperator) :=
      traceNorm_tensor_right_resource_le_raw data hdata hFrame idealFrame
    _ ≤ (LinearMap.trace Complex QubitSpace data).re *
          traceNorm (h.toOperator - hMagicState.toOperator) :=
      mul_le_mul_of_nonneg_left hframeTransport hdataTrace

/-- Replacing the H resource in a literal branch-summed retry continuation is
charged once per remaining physical phase site, never once per terminal leaf. -/
private theorem hRetryAggregate_stable
    (h : DensityOperator QubitSpace) (target : ZMod 8) (remaining : Nat) :
    ∀ (position : ZMod 8) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      traceNorm
        (hRetryAggregateLinear h target remaining position data -
          hRetryAggregateLinear hMagicState target remaining position data) ≤
        (remaining : Real) * (LinearMap.trace Complex QubitSpace data).re *
          traceNorm (h.toOperator - hMagicState.toOperator) := by
  induction remaining with
  | zero =>
      intro position data hdata
      have hzero : traceNorm (0 : Operator QubitSpace) = 0 :=
        (traceNorm_eq_zero_iff 0).mpr rfl
      simp [hRetryAggregateLinear, hzero]
  | succ remaining ih =>
      intro position data hdata
      by_cases htarget : position = target
      · have htrace : 0 ≤ (LinearMap.trace Complex QubitSpace data).re :=
          (Complex.nonneg_iff.mp hdata.trace_nonneg).1
        have hright : 0 ≤ (remaining + 1 : Real) *
            (LinearMap.trace Complex QubitSpace data).re *
              traceNorm (h.toOperator - hMagicState.toOperator) := by
          exact mul_nonneg (mul_nonneg (by positivity) htrace) (traceNorm_nonneg _)
        have hzero : traceNorm (0 : Operator QubitSpace) = 0 :=
          (traceNorm_eq_zero_iff 0).mpr rfl
        simpa [hRetryAggregateLinear, htarget, hzero] using hright
      · have htruePositive : LinearMap.IsPositive
            (phaseBranchRaw (hPhaseRaw h) data true) :=
          phaseBranchRaw_positive (hPhaseRaw h) data (hPhaseRaw_positive h) hdata true
        have hfalsePositive : LinearMap.IsPositive
            (phaseBranchRaw (hPhaseRaw h) data false) :=
          phaseBranchRaw_positive (hPhaseRaw h) data (hPhaseRaw_positive h) hdata false
        have hbranchTrace := congrArg Complex.re
          (phaseBranchRaw_trace_sum (hPhaseRaw h) data)
        rw [hPhaseRaw_trace_one] at hbranchTrace
        have hbranchTraceReal :
            (LinearMap.trace Complex QubitSpace
                (phaseBranchRaw (hPhaseRaw h) data true)).re +
              (LinearMap.trace Complex QubitSpace
                (phaseBranchRaw (hPhaseRaw h) data false)).re =
              (LinearMap.trace Complex QubitSpace data).re := by
          simpa [Complex.add_re] using hbranchTrace
        have hinputPositive : LinearMap.IsPositive
            (injectedInputRaw data (hPhaseRaw h)) :=
          injectedInputRaw_positive data (hPhaseRaw h) hdata (hPhaseRaw_positive h)
        have hidealInputPositive : LinearMap.IsPositive
            (injectedInputRaw data (hPhaseRaw hMagicState)) :=
          injectedInputRaw_positive data (hPhaseRaw hMagicState) hdata
            (hPhaseRaw_positive hMagicState)
        have hinputSymmetric :
            (injectedInputRaw data (hPhaseRaw h) -
              injectedInputRaw data (hPhaseRaw hMagicState)).IsSymmetric :=
          hinputPositive.isSymmetric.sub hidealInputPositive.isSymmetric
        have hactual :
            hRetryAggregateLinear h target (remaining + 1) position data =
              phaseContinuationLinear
                (hRetryAggregateLinear h target remaining (position + 1))
                (hRetryAggregateLinear h target remaining (position - 1))
                (injectedInputRaw data (hPhaseRaw h)) := by
          simp [hRetryAggregateLinear, htarget, phaseContinuationLinear,
            observedBranchLinear_apply, phaseBranchRawLinear_apply, phaseBranchRaw]
        have hideal :
            hRetryAggregateLinear hMagicState target (remaining + 1) position data =
              phaseContinuationLinear
                (hRetryAggregateLinear hMagicState target remaining (position + 1))
                (hRetryAggregateLinear hMagicState target remaining (position - 1))
                (injectedInputRaw data (hPhaseRaw hMagicState)) := by
          simp [hRetryAggregateLinear, htarget, phaseContinuationLinear,
            observedBranchLinear_apply, phaseBranchRawLinear_apply, phaseBranchRaw]
        have hfuture :
            traceNorm
              (phaseContinuationLinear
                  (hRetryAggregateLinear h target remaining (position + 1))
                  (hRetryAggregateLinear h target remaining (position - 1))
                  (injectedInputRaw data (hPhaseRaw h)) -
                phaseContinuationLinear
                  (hRetryAggregateLinear hMagicState target remaining (position + 1))
                  (hRetryAggregateLinear hMagicState target remaining (position - 1))
                  (injectedInputRaw data (hPhaseRaw h))) ≤
              (remaining : Real) * (LinearMap.trace Complex QubitSpace data).re *
                traceNorm (h.toOperator - hMagicState.toOperator) := by
          change traceNorm
              (hRetryAggregateLinear h target remaining (position + 1)
                  (phaseBranchRaw (hPhaseRaw h) data true) +
                hRetryAggregateLinear h target remaining (position - 1)
                  (phaseBranchRaw (hPhaseRaw h) data false) -
                (hRetryAggregateLinear hMagicState target remaining (position + 1)
                    (phaseBranchRaw (hPhaseRaw h) data true) +
                  hRetryAggregateLinear hMagicState target remaining (position - 1)
                    (phaseBranchRaw (hPhaseRaw h) data false))) ≤ _
          calc
            traceNorm
                (hRetryAggregateLinear h target remaining (position + 1)
                    (phaseBranchRaw (hPhaseRaw h) data true) +
                  hRetryAggregateLinear h target remaining (position - 1)
                    (phaseBranchRaw (hPhaseRaw h) data false) -
                  (hRetryAggregateLinear hMagicState target remaining (position + 1)
                      (phaseBranchRaw (hPhaseRaw h) data true) +
                    hRetryAggregateLinear hMagicState target remaining (position - 1)
                      (phaseBranchRaw (hPhaseRaw h) data false))) =
                traceNorm
                  ((hRetryAggregateLinear h target remaining (position + 1)
                      (phaseBranchRaw (hPhaseRaw h) data true) -
                    hRetryAggregateLinear hMagicState target remaining (position + 1)
                      (phaseBranchRaw (hPhaseRaw h) data true)) +
                    (hRetryAggregateLinear h target remaining (position - 1)
                      (phaseBranchRaw (hPhaseRaw h) data false) -
                    hRetryAggregateLinear hMagicState target remaining (position - 1)
                      (phaseBranchRaw (hPhaseRaw h) data false))) := by
                    congr 1
                    module
            _ ≤ traceNorm
                (hRetryAggregateLinear h target remaining (position + 1)
                    (phaseBranchRaw (hPhaseRaw h) data true) -
                  hRetryAggregateLinear hMagicState target remaining (position + 1)
                    (phaseBranchRaw (hPhaseRaw h) data true)) +
                traceNorm
                  (hRetryAggregateLinear h target remaining (position - 1)
                    (phaseBranchRaw (hPhaseRaw h) data false) -
                  hRetryAggregateLinear hMagicState target remaining (position - 1)
                    (phaseBranchRaw (hPhaseRaw h) data false)) :=
              traceNorm_add_le _ _
            _ ≤ (remaining : Real) *
                  (LinearMap.trace Complex QubitSpace
                    (phaseBranchRaw (hPhaseRaw h) data true)).re *
                    traceNorm (h.toOperator - hMagicState.toOperator) +
                (remaining : Real) *
                  (LinearMap.trace Complex QubitSpace
                    (phaseBranchRaw (hPhaseRaw h) data false)).re *
                    traceNorm (h.toOperator - hMagicState.toOperator) := by
              apply add_le_add
              · exact ih (position + 1) (phaseBranchRaw (hPhaseRaw h) data true)
                  htruePositive
              · exact ih (position - 1) (phaseBranchRaw (hPhaseRaw h) data false)
                  hfalsePositive
            _ = (remaining : Real) * (LinearMap.trace Complex QubitSpace data).re *
                traceNorm (h.toOperator - hMagicState.toOperator) := by
              rw [← hbranchTraceReal]
              ring
        have hcurrent :
            traceNorm
              (phaseContinuationLinear
                  (hRetryAggregateLinear hMagicState target remaining (position + 1))
                  (hRetryAggregateLinear hMagicState target remaining (position - 1))
                  (injectedInputRaw data (hPhaseRaw h) -
                    injectedInputRaw data (hPhaseRaw hMagicState))) ≤
              (LinearMap.trace Complex QubitSpace data).re *
                traceNorm (h.toOperator - hMagicState.toOperator) := by
          calc
            traceNorm
                (phaseContinuationLinear
                    (hRetryAggregateLinear hMagicState target remaining (position + 1))
                    (hRetryAggregateLinear hMagicState target remaining (position - 1))
                    (injectedInputRaw data (hPhaseRaw h) -
                      injectedInputRaw data (hPhaseRaw hMagicState))) ≤
                traceNorm
                  (injectedInputRaw data (hPhaseRaw h) -
                    injectedInputRaw data (hPhaseRaw hMagicState)) := by
                exact phaseContinuationLinear_traceNorm_le
                  (hRetryAggregateLinear hMagicState target remaining (position + 1))
                  (hRetryAggregateLinear hMagicState target remaining (position - 1))
                  (fun raw hraw => hRetryAggregateLinear_positive hMagicState target
                    remaining (position + 1) raw hraw)
                  (fun raw hraw => hRetryAggregateLinear_positive hMagicState target
                    remaining (position - 1) raw hraw)
                  (fun raw => hRetryAggregateLinear_trace hMagicState target
                    remaining (position + 1) raw)
                  (fun raw => hRetryAggregateLinear_trace hMagicState target
                    remaining (position - 1) raw)
                  _ hinputSymmetric
            _ ≤ (LinearMap.trace Complex QubitSpace data).re *
                  traceNorm (h.toOperator - hMagicState.toOperator) :=
              injectedInputRaw_hResource_difference_le h data hdata
        rw [hactual, hideal]
        have htele :
            phaseContinuationLinear
                (hRetryAggregateLinear h target remaining (position + 1))
                (hRetryAggregateLinear h target remaining (position - 1))
                (injectedInputRaw data (hPhaseRaw h)) -
              phaseContinuationLinear
                (hRetryAggregateLinear hMagicState target remaining (position + 1))
                (hRetryAggregateLinear hMagicState target remaining (position - 1))
                (injectedInputRaw data (hPhaseRaw hMagicState)) =
              (phaseContinuationLinear
                  (hRetryAggregateLinear h target remaining (position + 1))
                  (hRetryAggregateLinear h target remaining (position - 1))
                  (injectedInputRaw data (hPhaseRaw h)) -
                phaseContinuationLinear
                  (hRetryAggregateLinear hMagicState target remaining (position + 1))
                  (hRetryAggregateLinear hMagicState target remaining (position - 1))
                  (injectedInputRaw data (hPhaseRaw h))) +
                phaseContinuationLinear
                  (hRetryAggregateLinear hMagicState target remaining (position + 1))
                  (hRetryAggregateLinear hMagicState target remaining (position - 1))
                  (injectedInputRaw data (hPhaseRaw h) -
                    injectedInputRaw data (hPhaseRaw hMagicState)) := by
              rw [(phaseContinuationLinear
                (hRetryAggregateLinear hMagicState target remaining (position + 1))
                (hRetryAggregateLinear hMagicState target remaining (position - 1))).map_sub]
              module
        rw [htele]
        calc
          traceNorm
              ((phaseContinuationLinear
                  (hRetryAggregateLinear h target remaining (position + 1))
                  (hRetryAggregateLinear h target remaining (position - 1))
                  (injectedInputRaw data (hPhaseRaw h)) -
                phaseContinuationLinear
                  (hRetryAggregateLinear hMagicState target remaining (position + 1))
                  (hRetryAggregateLinear hMagicState target remaining (position - 1))
                  (injectedInputRaw data (hPhaseRaw h))) +
                phaseContinuationLinear
                  (hRetryAggregateLinear hMagicState target remaining (position + 1))
                  (hRetryAggregateLinear hMagicState target remaining (position - 1))
                  (injectedInputRaw data (hPhaseRaw h) -
                    injectedInputRaw data (hPhaseRaw hMagicState))) ≤
              traceNorm
                (phaseContinuationLinear
                    (hRetryAggregateLinear h target remaining (position + 1))
                    (hRetryAggregateLinear h target remaining (position - 1))
                    (injectedInputRaw data (hPhaseRaw h)) -
                  phaseContinuationLinear
                    (hRetryAggregateLinear hMagicState target remaining (position + 1))
                    (hRetryAggregateLinear hMagicState target remaining (position - 1))
                    (injectedInputRaw data (hPhaseRaw h))) +
                traceNorm
                  (phaseContinuationLinear
                    (hRetryAggregateLinear hMagicState target remaining (position + 1))
                    (hRetryAggregateLinear hMagicState target remaining (position - 1))
                    (injectedInputRaw data (hPhaseRaw h) -
                      injectedInputRaw data (hPhaseRaw hMagicState))) :=
            traceNorm_add_le _ _
          _ ≤
              (remaining : Real) * (LinearMap.trace Complex QubitSpace data).re *
                traceNorm (h.toOperator - hMagicState.toOperator) +
                (LinearMap.trace Complex QubitSpace data).re *
                  traceNorm (h.toOperator - hMagicState.toOperator) :=
            add_le_add hfuture hcurrent
          _ = ((remaining + 1 : Nat) : Real) *
              (LinearMap.trace Complex QubitSpace data).re *
                traceNorm (h.toOperator - hMagicState.toOperator) := by
            push_cast
            ring

/-- The actual unconditioned H retry aggregate changes by at most one H
resource trace distance per order-eight phase site. -/
theorem hActualRawTree_aggregate_traceNorm_le
    (h : DensityOperator QubitSpace) (target : ZMod 8)
    (blocks : Nat) (rho : DensityOperator QubitSpace) :
    traceNorm
      (rawAggregate (hActualRawTree h target blocks rho) -
        rawAggregate (hActualRawTree hMagicState target blocks rho)) ≤
      (8 * blocks : Real) * traceNorm (h.toOperator - hMagicState.toOperator) := by
  change traceNorm
      (rawAggregate (hRetry h target (8 * blocks) 0 0 [] rho.toOperator) -
        rawAggregate (hRetry hMagicState target (8 * blocks) 0 0 [] rho.toOperator)) ≤ _
  rw [← hRetryAggregateLinear_apply h target (8 * blocks) 0 0 [] rho.toOperator,
    ← hRetryAggregateLinear_apply hMagicState target (8 * blocks) 0 0 [] rho.toOperator]
  have hstable := hRetryAggregate_stable h target (8 * blocks) 0 rho.toOperator rho.positive
  simpa [rho.trace_one] using hstable

/-- The rejected full-pair branch is linear in the raw pair input.  This is
kept separate from the supplier recursion so that its complete two-qubit
discard remains visible in the T aggregate. -/
private noncomputable def tPairRejectedDataLinear (data : Operator QubitSpace) :
    Operator TwoQubit.TwoQubitSpace →ₗ[Complex] Operator QubitSpace where
  toFun := fun pair =>
    partialTraceRightRaw QubitSpace TwoQubit.TwoQubitSpace
      (TensorProduct.map data pair)
  map_add' := by
    intro pair₁ pair₂
    change (partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace).toLinearMap
        (TensorProduct.map data (pair₁ + pair₂)) = _
    rw [TensorProduct.map_add_right]
    exact (partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace).toLinearMap.map_add _ _
  map_smul' := by
    intro scalar pair
    change (partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace).toLinearMap
        (TensorProduct.map data (scalar • pair)) = _
    rw [TensorProduct.map_smul_right]
    exact (partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace).toLinearMap.map_smul _ _

private theorem tPairRejectedDataLinear_apply (data : Operator QubitSpace)
    (pair : Operator TwoQubit.TwoQubitSpace) :
    tPairRejectedDataLinear data pair =
      partialTraceRightRaw QubitSpace TwoQubit.TwoQubitSpace
        (TensorProduct.map data pair) :=
  rfl

/-- The accepted source-pair branch, including its actual postprocess and
Hadamard frame, packaged linearly in the raw pair input. -/
private noncomputable def tPairAcceptedPhaseLinear :
    Operator TwoQubit.TwoQubitSpace →ₗ[Complex] Operator QubitSpace :=
  (QuantumChannel.unitaryConj hadamardTransport).toLinearMap.comp
    (oneShotPostprocess.toLinearMap.comp (observedBranchLinear true))

private theorem tPairAcceptedPhaseLinear_apply
    (pair : Operator TwoQubit.TwoQubitSpace) :
    tPairAcceptedPhaseLinear pair =
      (QuantumChannel.unitaryConj hadamardTransport)
        (oneShotPostprocess
          (zzMeasurement.instrument.branchOperator (observedRetrySyndrome true) pair)) :=
  rfl

/-- A single physical source-pair attempt followed by its two phase
continuations and its full-pair rejection continuation. -/
private noncomputable def tPairContinuationLinear
    (data : Operator QubitSpace)
    (nextTrue nextFalse onReject : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    Operator TwoQubit.TwoQubitSpace →ₗ[Complex] Operator QubitSpace :=
  nextTrue.comp ((phaseBranchRawResourceLinear data true).comp tPairAcceptedPhaseLinear) +
    nextFalse.comp ((phaseBranchRawResourceLinear data false).comp tPairAcceptedPhaseLinear) +
    onReject.comp ((tPairRejectedDataLinear data).comp (observedBranchLinear false))

private theorem tPairContinuationLinear_apply
    (data : Operator QubitSpace)
    (nextTrue nextFalse onReject : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (pair : Operator TwoQubit.TwoQubitSpace) :
    tPairContinuationLinear data nextTrue nextFalse onReject pair =
      nextTrue (phaseBranchRaw
        ((QuantumChannel.unitaryConj hadamardTransport)
          (oneShotPostprocess
            (zzMeasurement.instrument.branchOperator (observedRetrySyndrome true) pair)))
        data true) +
      nextFalse (phaseBranchRaw
        ((QuantumChannel.unitaryConj hadamardTransport)
          (oneShotPostprocess
            (zzMeasurement.instrument.branchOperator (observedRetrySyndrome true) pair)))
        data false) +
      onReject (partialTraceRightRaw QubitSpace TwoQubit.TwoQubitSpace
        (TensorProduct.map data
          (zzMeasurement.instrument.branchOperator (observedRetrySyndrome false) pair))) := by
  change nextTrue (phaseBranchRaw (tPairAcceptedPhaseLinear pair) data true) +
      nextFalse (phaseBranchRaw (tPairAcceptedPhaseLinear pair) data false) +
      onReject (tPairRejectedDataLinear data (observedBranchLinear false pair)) = _
  rw [tPairAcceptedPhaseLinear_apply, observedBranchLinear_apply,
    tPairRejectedDataLinear_apply]

/-- The literal rejection-and-discard map is linear in the accumulated raw
data when the source pair is fixed. -/
private noncomputable def tRejectedDataRawLinear (t : DensityOperator QubitSpace) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace where
  toFun := fun data => tRejectedDataRaw data t
  map_add' := by
    intro data₁ data₂
    change (partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace).toLinearMap
        (TensorProduct.map (data₁ + data₂) (tPairBranchRaw t false)) = _
    rw [TensorProduct.map_add_left]
    exact (partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace).toLinearMap.map_add _ _
  map_smul' := by
    intro scalar data
    change (partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace).toLinearMap
        (TensorProduct.map (scalar • data) (tPairBranchRaw t false)) = _
    rw [TensorProduct.map_smul_left]
    exact (partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace).toLinearMap.map_smul _ _

private theorem tRejectedDataRawLinear_apply (t : DensityOperator QubitSpace)
    (data : Operator QubitSpace) :
    tRejectedDataRawLinear t data = tRejectedDataRaw data t :=
  rfl

/-- The aggregate of one literal bounded fresh-T-pair supplier, linear in
the accumulated raw data.  Its accepted branches use the actual unnormalised
phase resource and every rejection recurses only after complete-pair discard. -/
private noncomputable def tSupplyAggregateLinear
    (t : DensityOperator QubitSpace) : Nat →
      (Operator QubitSpace →ₗ[Complex] Operator QubitSpace) →
      (Operator QubitSpace →ₗ[Complex] Operator QubitSpace) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | 0, _, _ => LinearMap.id
  | attempts + 1, nextTrue, nextFalse =>
      nextTrue.comp (phaseBranchRawLinear (tAcceptedPhaseRaw t) true) +
        nextFalse.comp (phaseBranchRawLinear (tAcceptedPhaseRaw t) false) +
        (tSupplyAggregateLinear t attempts nextTrue nextFalse).comp
          (tRejectedDataRawLinear t)

/-- The aggregate of the complete literal T retry tree, retaining target,
phase-exhausted, and supplier-exhausted leaves. -/
private noncomputable def tRetryAggregateLinear
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12) :
    Nat → ZMod 12 → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | 0, _ => LinearMap.id
  | remaining + 1, position =>
      if position = target then LinearMap.id else
        tSupplyAggregateLinear t pairAttempts
          (tRetryAggregateLinear t pairAttempts target remaining (position + 1))
          (tRetryAggregateLinear t pairAttempts target remaining (position - 1))

private theorem tPairAcceptedPhaseLinear_positive
    (pair : Operator TwoQubit.TwoQubitSpace) (hpair : LinearMap.IsPositive pair) :
    LinearMap.IsPositive (tPairAcceptedPhaseLinear pair) := by
  rw [tPairAcceptedPhaseLinear_apply]
  apply (QuantumChannel.unitaryConj hadamardTransport).map_positive
  apply oneShotPostprocess.map_positive
  exact zzMeasurement.instrument.branchOperator_positive _ hpair

private theorem tPairRejectedDataLinear_positive
    (data : Operator QubitSpace) (pair : Operator TwoQubit.TwoQubitSpace)
    (hdata : LinearMap.IsPositive data) (hpair : LinearMap.IsPositive pair) :
    LinearMap.IsPositive (tPairRejectedDataLinear data pair) := by
  rw [tPairRejectedDataLinear_apply]
  change LinearMap.IsPositive
    ((partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace).toLinearMap
      (TensorProduct.map data pair))
  apply (partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace).map_positive
  exact ThermalEncoding.tensorMap_positive data pair hdata hpair

private theorem tPairAcceptedPhaseLinear_trace
    (pair : Operator TwoQubit.TwoQubitSpace) :
    LinearMap.trace Complex QubitSpace (tPairAcceptedPhaseLinear pair) =
      LinearMap.trace Complex TwoQubit.TwoQubitSpace
        (zzMeasurement.instrument.branchOperator (observedRetrySyndrome true) pair) := by
  rw [tPairAcceptedPhaseLinear_apply]
  calc
    LinearMap.trace Complex QubitSpace
        ((QuantumChannel.unitaryConj hadamardTransport)
          (oneShotPostprocess
            (zzMeasurement.instrument.branchOperator (observedRetrySyndrome true) pair))) =
        LinearMap.trace Complex QubitSpace
          (oneShotPostprocess
            (zzMeasurement.instrument.branchOperator (observedRetrySyndrome true) pair)) :=
      (QuantumChannel.unitaryConj hadamardTransport).trace_map _
    _ = _ := oneShotPostprocess.trace_map _

private theorem tPairRejectedDataLinear_trace
    (data : Operator QubitSpace) (pair : Operator TwoQubit.TwoQubitSpace) :
    LinearMap.trace Complex QubitSpace (tPairRejectedDataLinear data pair) =
      LinearMap.trace Complex QubitSpace data *
        LinearMap.trace Complex TwoQubit.TwoQubitSpace pair := by
  rw [tPairRejectedDataLinear_apply,
    partialTraceRightRaw_trace_preserving QubitSpace TwoQubit.TwoQubitSpace]
  exact LinearMap.trace_tensorProduct' data pair

private theorem observedBranch_trace_sum
    (pair : Operator TwoQubit.TwoQubitSpace) :
    LinearMap.trace Complex TwoQubit.TwoQubitSpace (observedBranchLinear true pair) +
      LinearMap.trace Complex TwoQubit.TwoQubitSpace (observedBranchLinear false pair) =
      LinearMap.trace Complex TwoQubit.TwoQubitSpace pair := by
  rw [observedBranchLinear_apply, observedBranchLinear_apply]
  calc
    LinearMap.trace Complex TwoQubit.TwoQubitSpace
        (zzMeasurement.instrument.branchOperator (observedRetrySyndrome true) pair) +
      LinearMap.trace Complex TwoQubit.TwoQubitSpace
        (zzMeasurement.instrument.branchOperator (observedRetrySyndrome false) pair) =
        LinearMap.trace Complex QubitSpace
          (oneShotPostprocess
            (zzMeasurement.instrument.branchOperator (observedRetrySyndrome true) pair)) +
          LinearMap.trace Complex QubitSpace
            (oneShotPostprocess
              (zzMeasurement.instrument.branchOperator (observedRetrySyndrome false) pair)) := by
            simp [oneShotPostprocess.trace_map]
    _ = LinearMap.trace Complex TwoQubit.TwoQubitSpace pair :=
      observedBranchPostprocess_trace_sum pair

private theorem tPairContinuationLinear_positive
    (data : Operator QubitSpace)
    (nextTrue nextFalse onReject : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (htrue : ∀ raw, LinearMap.IsPositive raw → LinearMap.IsPositive (nextTrue raw))
    (hfalse : ∀ raw, LinearMap.IsPositive raw → LinearMap.IsPositive (nextFalse raw))
    (hreject : ∀ raw, LinearMap.IsPositive raw → LinearMap.IsPositive (onReject raw))
    (pair : Operator TwoQubit.TwoQubitSpace) (hdata : LinearMap.IsPositive data)
    (hpair : LinearMap.IsPositive pair) :
    LinearMap.IsPositive (tPairContinuationLinear data nextTrue nextFalse onReject pair) := by
  rw [tPairContinuationLinear_apply]
  apply LinearMap.IsPositive.add
  · apply LinearMap.IsPositive.add
    · apply htrue
      exact phaseBranchRaw_positive (tPairAcceptedPhaseLinear pair) data
        (tPairAcceptedPhaseLinear_positive pair hpair) hdata true
    · apply hfalse
      exact phaseBranchRaw_positive (tPairAcceptedPhaseLinear pair) data
        (tPairAcceptedPhaseLinear_positive pair hpair) hdata false
  · apply hreject
    exact tPairRejectedDataLinear_positive data (observedBranchLinear false pair) hdata
      (zzMeasurement.instrument.branchOperator_positive _ hpair)

private theorem tPairContinuationLinear_trace
    (data : Operator QubitSpace)
    (nextTrue nextFalse onReject : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (htrue : ∀ raw,
      LinearMap.trace Complex QubitSpace (nextTrue raw) = LinearMap.trace Complex QubitSpace raw)
    (hfalse : ∀ raw,
      LinearMap.trace Complex QubitSpace (nextFalse raw) = LinearMap.trace Complex QubitSpace raw)
    (hreject : ∀ raw,
      LinearMap.trace Complex QubitSpace (onReject raw) = LinearMap.trace Complex QubitSpace raw)
    (pair : Operator TwoQubit.TwoQubitSpace) :
    LinearMap.trace Complex QubitSpace
      (tPairContinuationLinear data nextTrue nextFalse onReject pair) =
      LinearMap.trace Complex QubitSpace data *
        LinearMap.trace Complex TwoQubit.TwoQubitSpace pair := by
  have haccepted :
      LinearMap.trace Complex QubitSpace
          ((QuantumChannel.unitaryConj hadamardTransport)
            (oneShotPostprocess
              (zzMeasurement.instrument.branchOperator (observedRetrySyndrome true) pair))) =
        LinearMap.trace Complex TwoQubit.TwoQubitSpace
          (zzMeasurement.instrument.branchOperator (observedRetrySyndrome true) pair) := by
    simpa [tPairAcceptedPhaseLinear_apply] using tPairAcceptedPhaseLinear_trace pair
  have hrejectData :
      LinearMap.trace Complex QubitSpace
          (partialTraceRightRaw QubitSpace TwoQubit.TwoQubitSpace
            (TensorProduct.map data
              (zzMeasurement.instrument.branchOperator (observedRetrySyndrome false) pair))) =
        LinearMap.trace Complex QubitSpace data *
          LinearMap.trace Complex TwoQubit.TwoQubitSpace
            (zzMeasurement.instrument.branchOperator (observedRetrySyndrome false) pair) := by
    have hreject := tPairRejectedDataLinear_trace data (observedBranchLinear false pair)
    rw [observedBranchLinear_apply] at hreject
    exact hreject
  have hbranches := observedBranch_trace_sum pair
  simp only [observedBranchLinear_apply] at hbranches
  rw [tPairContinuationLinear_apply, map_add, map_add, htrue, hfalse, hreject,
    phaseBranchRaw_trace_sum, haccepted, hrejectData, ← mul_add, hbranches]

private theorem tPairContinuationLinear_tPairInput_apply
    (t : DensityOperator QubitSpace) (data : Operator QubitSpace)
    (nextTrue nextFalse onReject : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    tPairContinuationLinear data nextTrue nextFalse onReject (tPairInputRaw t) =
      nextTrue (phaseBranchRaw (tAcceptedPhaseRaw t) data true) +
        nextFalse (phaseBranchRaw (tAcceptedPhaseRaw t) data false) +
        onReject (tRejectedDataRaw data t) := by
  rfl

/-- After both accepted phase outcomes and the full-pair rejection are
retained, a source-pair continuation contracts a self-adjoint pair difference
by the real trace of its raw data input. -/
private theorem tPairContinuationLinear_traceNorm_le
    (data : Operator QubitSpace)
    (nextTrue nextFalse onReject : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (htruePositive : ∀ raw, LinearMap.IsPositive raw → LinearMap.IsPositive (nextTrue raw))
    (hfalsePositive : ∀ raw, LinearMap.IsPositive raw → LinearMap.IsPositive (nextFalse raw))
    (hrejectPositive : ∀ raw, LinearMap.IsPositive raw → LinearMap.IsPositive (onReject raw))
    (htrueTrace : ∀ raw,
      LinearMap.trace Complex QubitSpace (nextTrue raw) = LinearMap.trace Complex QubitSpace raw)
    (hfalseTrace : ∀ raw,
      LinearMap.trace Complex QubitSpace (nextFalse raw) = LinearMap.trace Complex QubitSpace raw)
    (hrejectTrace : ∀ raw,
      LinearMap.trace Complex QubitSpace (onReject raw) = LinearMap.trace Complex QubitSpace raw)
    (input : Operator TwoQubit.TwoQubitSpace) (hdata : LinearMap.IsPositive data)
    (hinput : input.IsSymmetric) :
    traceNorm (tPairContinuationLinear data nextTrue nextFalse onReject input) ≤
      (LinearMap.trace Complex QubitSpace data).re * traceNorm input := by
  have hdecomp := positivePart_sub_negativePart input hinput
  have hpositive : ∀ pair, LinearMap.IsPositive pair →
      LinearMap.IsPositive (tPairContinuationLinear data nextTrue nextFalse onReject pair) := by
    intro pair hpair
    exact tPairContinuationLinear_positive data nextTrue nextFalse onReject htruePositive
      hfalsePositive hrejectPositive pair hdata hpair
  have htrace : ∀ pair,
      LinearMap.trace Complex QubitSpace
          (tPairContinuationLinear data nextTrue nextFalse onReject pair) =
        LinearMap.trace Complex QubitSpace data *
          LinearMap.trace Complex TwoQubit.TwoQubitSpace pair := by
    intro pair
    exact tPairContinuationLinear_trace data nextTrue nextFalse onReject htrueTrace
      hfalseTrace hrejectTrace pair
  have htrace_re : ∀ pair, LinearMap.IsPositive pair →
      (LinearMap.trace Complex QubitSpace
          (tPairContinuationLinear data nextTrue nextFalse onReject pair)).re =
        (LinearMap.trace Complex QubitSpace data).re *
          (LinearMap.trace Complex TwoQubit.TwoQubitSpace pair).re := by
    intro pair hpair
    rw [htrace]
    have hdataIm : (LinearMap.trace Complex QubitSpace data).im = 0 :=
      (Complex.nonneg_iff.mp hdata.trace_nonneg).2.symm
    have hpairIm : (LinearMap.trace Complex TwoQubit.TwoQubitSpace pair).im = 0 :=
      (Complex.nonneg_iff.mp hpair.trace_nonneg).2.symm
    simp [Complex.mul_re, hdataIm, hpairIm]
  calc
    traceNorm (tPairContinuationLinear data nextTrue nextFalse onReject input) =
        traceNorm
          (tPairContinuationLinear data nextTrue nextFalse onReject (positivePart input) -
            tPairContinuationLinear data nextTrue nextFalse onReject (negativePart input)) := by
          rw [← (tPairContinuationLinear data nextTrue nextFalse onReject).map_sub, hdecomp]
    _ ≤ traceNorm
          (tPairContinuationLinear data nextTrue nextFalse onReject (positivePart input)) +
        traceNorm
          (tPairContinuationLinear data nextTrue nextFalse onReject (negativePart input)) := by
          simpa [sub_eq_add_neg, traceNorm_neg] using traceNorm_add_le
            (tPairContinuationLinear data nextTrue nextFalse onReject (positivePart input))
            (-tPairContinuationLinear data nextTrue nextFalse onReject (negativePart input))
    _ = (LinearMap.trace Complex QubitSpace data).re *
          (LinearMap.trace Complex TwoQubit.TwoQubitSpace (positivePart input)).re +
        (LinearMap.trace Complex QubitSpace data).re *
          (LinearMap.trace Complex TwoQubit.TwoQubitSpace (negativePart input)).re := by
          rw [traceNorm_eq_re_trace_of_positive _
              (hpositive _ (positivePart_positive input)),
            traceNorm_eq_re_trace_of_positive _
              (hpositive _ (negativePart_positive input)),
            htrace_re _ (positivePart_positive input),
            htrace_re _ (negativePart_positive input)]
    _ = (LinearMap.trace Complex QubitSpace data).re *
        (traceNorm (positivePart input) + traceNorm (negativePart input)) := by
          rw [traceNorm_eq_re_trace_of_positive _ (positivePart_positive input),
            traceNorm_eq_re_trace_of_positive _ (negativePart_positive input)]
          ring
    _ = (LinearMap.trace Complex QubitSpace data).re * traceNorm input := by
          rw [traceNorm_eq_sum_parts input hinput]

private theorem tPairInputRaw_difference_le (t : DensityOperator QubitSpace) :
    traceNorm (tPairInputRaw t - tPairInputRaw tMagicState) ≤
      2 * traceNorm (t.toOperator - tMagicState.toOperator) := by
  have hpairPositive : LinearMap.IsPositive
      (TensorProduct.map t.toOperator t.toOperator) := by
    exact ThermalEncoding.tensorMap_positive t.toOperator t.toOperator t.positive t.positive
  have hidealPositive : LinearMap.IsPositive
      (TensorProduct.map tMagicState.toOperator tMagicState.toOperator) := by
    exact ThermalEncoding.tensorMap_positive tMagicState.toOperator tMagicState.toOperator
      tMagicState.positive tMagicState.positive
  have hpairSymmetric :
      (TensorProduct.map t.toOperator t.toOperator -
        TensorProduct.map tMagicState.toOperator tMagicState.toOperator).IsSymmetric :=
    hpairPositive.isSymmetric.sub hidealPositive.isSymmetric
  calc
    traceNorm (tPairInputRaw t - tPairInputRaw tMagicState) =
        traceNorm
          (TwoQubit.tensorRegisterTransport.conjOperator
            (TensorProduct.map t.toOperator t.toOperator -
              TensorProduct.map tMagicState.toOperator tMagicState.toOperator)) := by
          unfold tPairInputRaw
          simp only [← UnitaryTransport.conjOperatorLinearMap_apply]
          rw [← TwoQubit.tensorRegisterTransport.conjOperatorLinearMap.map_sub]
    _ ≤ traceNorm
          (TensorProduct.map t.toOperator t.toOperator -
            TensorProduct.map tMagicState.toOperator tMagicState.toOperator) := by
          exact QuantumChannel.traceNorm_apply_le_of_isSymmetric
            (QuantumChannel.unitaryConj TwoQubit.tensorRegisterTransport) _ hpairSymmetric
    _ ≤ 2 * traceNorm (t.toOperator - tMagicState.toOperator) :=
      traceNorm_tensor_pair_resource_le t tMagicState

private theorem tRejectedDataRaw_trace_re_le
    (data : Operator QubitSpace) (t : DensityOperator QubitSpace)
    (hdata : LinearMap.IsPositive data) :
    (LinearMap.trace Complex QubitSpace (tRejectedDataRaw data t)).re ≤
      (LinearMap.trace Complex QubitSpace data).re := by
  have htruePositive := tPairBranchRaw_positive t true
  have hfalsePositive := tPairBranchRaw_positive t false
  have hdataRe : 0 ≤ (LinearMap.trace Complex QubitSpace data).re :=
    (Complex.nonneg_iff.mp hdata.trace_nonneg).1
  have hfalseRe : 0 ≤
      (LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t false)).re :=
    (Complex.nonneg_iff.mp hfalsePositive.trace_nonneg).1
  have hsum := congrArg Complex.re (tPairBranchRaw_trace_sum t)
  have hsumRe :
      (LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t true)).re +
        (LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t false)).re = 1 := by
    simpa [Complex.add_re] using hsum
  have hfalseLe :
      (LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t false)).re ≤ 1 := by
    have htrueRe : 0 ≤
        (LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t true)).re :=
      (Complex.nonneg_iff.mp htruePositive.trace_nonneg).1
    linarith
  have hdataIm : (LinearMap.trace Complex QubitSpace data).im = 0 :=
    (Complex.nonneg_iff.mp hdata.trace_nonneg).2.symm
  have hfalseIm :
      (LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t false)).im = 0 :=
    (Complex.nonneg_iff.mp hfalsePositive.trace_nonneg).2.symm
  rw [tRejectedDataRaw_trace, Complex.mul_re]
  simp [hdataIm, hfalseIm]
  exact mul_le_of_le_one_right hdataRe hfalseLe

private theorem tSupplyAggregateLinear_continuation_stable
    (t : DensityOperator QubitSpace)
    (nextTrueActual nextFalseActual nextTrueIdeal nextFalseIdeal :
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (budget delta : Real) (hbudget : 0 ≤ budget) (hdelta : 0 ≤ delta)
    (htrue : ∀ raw, LinearMap.IsPositive raw →
      traceNorm (nextTrueActual raw - nextTrueIdeal raw) ≤
        budget * (LinearMap.trace Complex QubitSpace raw).re * delta)
    (hfalse : ∀ raw, LinearMap.IsPositive raw →
      traceNorm (nextFalseActual raw - nextFalseIdeal raw) ≤
        budget * (LinearMap.trace Complex QubitSpace raw).re * delta) :
    ∀ (attempts : Nat) (data : Operator QubitSpace), LinearMap.IsPositive data →
      traceNorm
        (tSupplyAggregateLinear t attempts nextTrueActual nextFalseActual data -
          tSupplyAggregateLinear t attempts nextTrueIdeal nextFalseIdeal data) ≤
        budget * (LinearMap.trace Complex QubitSpace data).re * delta := by
  intro attempts
  induction attempts with
  | zero =>
      intro data hdata
      have hzero : traceNorm (0 : Operator QubitSpace) = 0 :=
        (traceNorm_eq_zero_iff 0).mpr rfl
      have hdataRe : 0 ≤ (LinearMap.trace Complex QubitSpace data).re :=
        (Complex.nonneg_iff.mp hdata.trace_nonneg).1
      simpa [tSupplyAggregateLinear, hzero] using
        mul_nonneg (mul_nonneg hbudget hdataRe) hdelta
  | succ attempts ih =>
      intro data hdata
      have haccepted := tAcceptedPhaseRaw_positive t
      have htruePositive : LinearMap.IsPositive
          (phaseBranchRaw (tAcceptedPhaseRaw t) data true) :=
        phaseBranchRaw_positive _ _ haccepted hdata true
      have hfalsePositive : LinearMap.IsPositive
          (phaseBranchRaw (tAcceptedPhaseRaw t) data false) :=
        phaseBranchRaw_positive _ _ haccepted hdata false
      have hrejectPositive : LinearMap.IsPositive (tRejectedDataRaw data t) :=
        tRejectedDataRaw_positive data t hdata
      have hphaseTrace := congrArg Complex.re
        (phaseBranchRaw_trace_sum (tAcceptedPhaseRaw t) data)
      rw [tAcceptedPhaseRaw_trace] at hphaseTrace
      have hrejectTrace := congrArg Complex.re (tRejectedDataRaw_trace data t)
      have hpairTrace := congrArg Complex.re (tPairBranchRaw_trace_sum t)
      have hdataIm : (LinearMap.trace Complex QubitSpace data).im = 0 :=
        (Complex.nonneg_iff.mp hdata.trace_nonneg).2.symm
      have htruePairIm :
          (LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t true)).im = 0 :=
        (Complex.nonneg_iff.mp (tPairBranchRaw_positive t true).trace_nonneg).2.symm
      have hfalsePairIm :
          (LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t false)).im = 0 :=
        (Complex.nonneg_iff.mp (tPairBranchRaw_positive t false).trace_nonneg).2.symm
      have hmass :
          (LinearMap.trace Complex QubitSpace
              (phaseBranchRaw (tAcceptedPhaseRaw t) data true)).re +
            (LinearMap.trace Complex QubitSpace
              (phaseBranchRaw (tAcceptedPhaseRaw t) data false)).re +
            (LinearMap.trace Complex QubitSpace (tRejectedDataRaw data t)).re =
              (LinearMap.trace Complex QubitSpace data).re := by
        rw [← Complex.add_re, hphaseTrace, hrejectTrace]
        simp [Complex.add_re, Complex.mul_re, hdataIm, htruePairIm, hfalsePairIm] at hpairTrace ⊢
        calc
          (LinearMap.trace Complex QubitSpace data).re *
              (LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t true)).re +
            (LinearMap.trace Complex QubitSpace data).re *
              (LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t false)).re =
              (LinearMap.trace Complex QubitSpace data).re *
                ((LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t true)).re +
                  (LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t false)).re) := by
                ring
          _ = (LinearMap.trace Complex QubitSpace data).re := by
                rw [hpairTrace, mul_one]
      have hsplit :
          traceNorm
              (tSupplyAggregateLinear t (attempts + 1) nextTrueActual nextFalseActual data -
                tSupplyAggregateLinear t (attempts + 1) nextTrueIdeal nextFalseIdeal data) ≤
            traceNorm
              (nextTrueActual (phaseBranchRaw (tAcceptedPhaseRaw t) data true) -
                nextTrueIdeal (phaseBranchRaw (tAcceptedPhaseRaw t) data true)) +
              traceNorm
                (nextFalseActual (phaseBranchRaw (tAcceptedPhaseRaw t) data false) -
                  nextFalseIdeal (phaseBranchRaw (tAcceptedPhaseRaw t) data false)) +
                traceNorm
                  (tSupplyAggregateLinear t attempts nextTrueActual nextFalseActual
                      (tRejectedDataRaw data t) -
                    tSupplyAggregateLinear t attempts nextTrueIdeal nextFalseIdeal
                      (tRejectedDataRaw data t)) := by
        simp only [tSupplyAggregateLinear, LinearMap.add_apply, LinearMap.comp_apply,
          phaseBranchRawLinear_apply, tRejectedDataRawLinear_apply]
        calc
          traceNorm
              ((nextTrueActual (phaseBranchRaw (tAcceptedPhaseRaw t) data true) +
                  nextFalseActual (phaseBranchRaw (tAcceptedPhaseRaw t) data false) +
                  tSupplyAggregateLinear t attempts nextTrueActual nextFalseActual
                    (tRejectedDataRaw data t)) -
                (nextTrueIdeal (phaseBranchRaw (tAcceptedPhaseRaw t) data true) +
                  nextFalseIdeal (phaseBranchRaw (tAcceptedPhaseRaw t) data false) +
                  tSupplyAggregateLinear t attempts nextTrueIdeal nextFalseIdeal
                    (tRejectedDataRaw data t))) =
              traceNorm
                ((nextTrueActual (phaseBranchRaw (tAcceptedPhaseRaw t) data true) -
                    nextTrueIdeal (phaseBranchRaw (tAcceptedPhaseRaw t) data true)) +
                  (nextFalseActual (phaseBranchRaw (tAcceptedPhaseRaw t) data false) -
                    nextFalseIdeal (phaseBranchRaw (tAcceptedPhaseRaw t) data false)) +
                  (tSupplyAggregateLinear t attempts nextTrueActual nextFalseActual
                      (tRejectedDataRaw data t) -
                    tSupplyAggregateLinear t attempts nextTrueIdeal nextFalseIdeal
                      (tRejectedDataRaw data t))) := by
                congr 1
                module
          _ ≤ _ := by
            calc
              traceNorm
                  ((nextTrueActual (phaseBranchRaw (tAcceptedPhaseRaw t) data true) -
                      nextTrueIdeal (phaseBranchRaw (tAcceptedPhaseRaw t) data true)) +
                    (nextFalseActual (phaseBranchRaw (tAcceptedPhaseRaw t) data false) -
                      nextFalseIdeal (phaseBranchRaw (tAcceptedPhaseRaw t) data false)) +
                    (tSupplyAggregateLinear t attempts nextTrueActual nextFalseActual
                        (tRejectedDataRaw data t) -
                      tSupplyAggregateLinear t attempts nextTrueIdeal nextFalseIdeal
                        (tRejectedDataRaw data t))) ≤
                  traceNorm
                    ((nextTrueActual (phaseBranchRaw (tAcceptedPhaseRaw t) data true) -
                        nextTrueIdeal (phaseBranchRaw (tAcceptedPhaseRaw t) data true)) +
                      (nextFalseActual (phaseBranchRaw (tAcceptedPhaseRaw t) data false) -
                        nextFalseIdeal (phaseBranchRaw (tAcceptedPhaseRaw t) data false))) +
                    traceNorm
                      (tSupplyAggregateLinear t attempts nextTrueActual nextFalseActual
                          (tRejectedDataRaw data t) -
                        tSupplyAggregateLinear t attempts nextTrueIdeal nextFalseIdeal
                          (tRejectedDataRaw data t)) :=
                traceNorm_add_le _ _
              _ ≤ _ := by
                exact add_le_add (traceNorm_add_le _ _) (le_refl _)
      calc
        traceNorm
            (tSupplyAggregateLinear t (attempts + 1) nextTrueActual nextFalseActual data -
              tSupplyAggregateLinear t (attempts + 1) nextTrueIdeal nextFalseIdeal data) ≤
            traceNorm
              (nextTrueActual (phaseBranchRaw (tAcceptedPhaseRaw t) data true) -
                nextTrueIdeal (phaseBranchRaw (tAcceptedPhaseRaw t) data true)) +
              traceNorm
                (nextFalseActual (phaseBranchRaw (tAcceptedPhaseRaw t) data false) -
                  nextFalseIdeal (phaseBranchRaw (tAcceptedPhaseRaw t) data false)) +
                traceNorm
                  (tSupplyAggregateLinear t attempts nextTrueActual nextFalseActual
                      (tRejectedDataRaw data t) -
                    tSupplyAggregateLinear t attempts nextTrueIdeal nextFalseIdeal
                      (tRejectedDataRaw data t)) := hsplit
        _ ≤ budget *
              (LinearMap.trace Complex QubitSpace
                (phaseBranchRaw (tAcceptedPhaseRaw t) data true)).re * delta +
            budget *
              (LinearMap.trace Complex QubitSpace
                (phaseBranchRaw (tAcceptedPhaseRaw t) data false)).re * delta +
            budget * (LinearMap.trace Complex QubitSpace (tRejectedDataRaw data t)).re *
              delta := by
            gcongr
            · exact htrue _ htruePositive
            · exact hfalse _ hfalsePositive
            · exact ih (tRejectedDataRaw data t) hrejectPositive
        _ = budget * (LinearMap.trace Complex QubitSpace data).re * delta := by
            rw [← hmass]
            ring

private theorem tSupplyAggregateLinear_positive
    (t : DensityOperator QubitSpace)
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (htrue : ∀ raw, LinearMap.IsPositive raw → LinearMap.IsPositive (nextTrue raw))
    (hfalse : ∀ raw, LinearMap.IsPositive raw → LinearMap.IsPositive (nextFalse raw)) :
    ∀ (attempts : Nat) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      LinearMap.IsPositive (tSupplyAggregateLinear t attempts nextTrue nextFalse data) := by
  intro attempts
  induction attempts with
  | zero =>
      intro data hdata
      simpa [tSupplyAggregateLinear] using hdata
  | succ attempts ih =>
      intro data hdata
      have htail := ih (tRejectedDataRaw data t) (tRejectedDataRaw_positive data t hdata)
      have haccepted := tAcceptedPhaseRaw_positive t
      exact (LinearMap.IsPositive.add (LinearMap.IsPositive.add
          (htrue _ (phaseBranchRaw_positive _ _ haccepted hdata true))
          (hfalse _ (phaseBranchRaw_positive _ _ haccepted hdata false))) htail)

private theorem tSupplyAggregateLinear_trace
    (t : DensityOperator QubitSpace)
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (htrue : ∀ raw,
      LinearMap.trace Complex QubitSpace (nextTrue raw) = LinearMap.trace Complex QubitSpace raw)
    (hfalse : ∀ raw,
      LinearMap.trace Complex QubitSpace (nextFalse raw) = LinearMap.trace Complex QubitSpace raw) :
    ∀ (attempts : Nat) (data : Operator QubitSpace),
      LinearMap.trace Complex QubitSpace
        (tSupplyAggregateLinear t attempts nextTrue nextFalse data) =
        LinearMap.trace Complex QubitSpace data := by
  intro attempts
  induction attempts with
  | zero =>
      intro data
      simp [tSupplyAggregateLinear]
  | succ attempts ih =>
      intro data
      simp only [tSupplyAggregateLinear, LinearMap.add_apply, LinearMap.comp_apply,
        phaseBranchRawLinear_apply]
      rw [map_add, map_add, htrue, hfalse, ih, phaseBranchRaw_trace_sum,
        tAcceptedPhaseRaw_trace, tRejectedDataRawLinear_apply, tRejectedDataRaw_trace,
        ← mul_add, tPairBranchRaw_trace_sum, mul_one]

private theorem tSupplyAggregateLinear_source_stable
    (t : DensityOperator QubitSpace)
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (htruePositive : ∀ raw, LinearMap.IsPositive raw → LinearMap.IsPositive (nextTrue raw))
    (hfalsePositive : ∀ raw, LinearMap.IsPositive raw → LinearMap.IsPositive (nextFalse raw))
    (htrueTrace : ∀ raw,
      LinearMap.trace Complex QubitSpace (nextTrue raw) = LinearMap.trace Complex QubitSpace raw)
    (hfalseTrace : ∀ raw,
      LinearMap.trace Complex QubitSpace (nextFalse raw) = LinearMap.trace Complex QubitSpace raw) :
    ∀ (attempts : Nat) (data : Operator QubitSpace), LinearMap.IsPositive data →
      traceNorm
        (tSupplyAggregateLinear t attempts nextTrue nextFalse data -
          tSupplyAggregateLinear tMagicState attempts nextTrue nextFalse data) ≤
        (2 * attempts : Real) * (LinearMap.trace Complex QubitSpace data).re *
          traceNorm (t.toOperator - tMagicState.toOperator) := by
  intro attempts
  induction attempts with
  | zero =>
      intro data hdata
      have hzero : traceNorm (0 : Operator QubitSpace) = 0 :=
        (traceNorm_eq_zero_iff 0).mpr rfl
      simp [tSupplyAggregateLinear, hzero]
  | succ attempts ih =>
      intro data hdata
      let actualTail := tSupplyAggregateLinear t attempts nextTrue nextFalse
      let idealTail := tSupplyAggregateLinear tMagicState attempts nextTrue nextFalse
      have hrejectPositive : LinearMap.IsPositive (tRejectedDataRaw data t) :=
        tRejectedDataRaw_positive data t hdata
      have hrejectLe :
          (LinearMap.trace Complex QubitSpace (tRejectedDataRaw data t)).re ≤
            (LinearMap.trace Complex QubitSpace data).re :=
        tRejectedDataRaw_trace_re_le data t hdata
      have hfuture :
          traceNorm
            (tPairContinuationLinear data nextTrue nextFalse actualTail (tPairInputRaw t) -
              tPairContinuationLinear data nextTrue nextFalse idealTail (tPairInputRaw t)) ≤
            (2 * attempts : Real) * (LinearMap.trace Complex QubitSpace data).re *
              traceNorm (t.toOperator - tMagicState.toOperator) := by
        have hfutureEq :
            tPairContinuationLinear data nextTrue nextFalse actualTail (tPairInputRaw t) -
              tPairContinuationLinear data nextTrue nextFalse idealTail (tPairInputRaw t) =
              actualTail (tRejectedDataRaw data t) - idealTail (tRejectedDataRaw data t) := by
          rw [tPairContinuationLinear_tPairInput_apply,
            tPairContinuationLinear_tPairInput_apply]
          module
        rw [hfutureEq]
        calc
          traceNorm (actualTail (tRejectedDataRaw data t) -
              idealTail (tRejectedDataRaw data t)) ≤
              (2 * attempts : Real) *
                (LinearMap.trace Complex QubitSpace (tRejectedDataRaw data t)).re *
                  traceNorm (t.toOperator - tMagicState.toOperator) := by
            exact ih (tRejectedDataRaw data t) hrejectPositive
          _ ≤ (2 * attempts : Real) * (LinearMap.trace Complex QubitSpace data).re *
                traceNorm (t.toOperator - tMagicState.toOperator) := by
            have hcoefficient : 0 ≤ (2 * attempts : Real) := by positivity
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hrejectLe hcoefficient)
              (traceNorm_nonneg _)
      have hidealTailPositive : ∀ raw, LinearMap.IsPositive raw →
          LinearMap.IsPositive (idealTail raw) := by
        intro raw hraw
        exact tSupplyAggregateLinear_positive tMagicState nextTrue nextFalse
          htruePositive hfalsePositive attempts raw hraw
      have hidealTailTrace : ∀ raw,
          LinearMap.trace Complex QubitSpace (idealTail raw) =
            LinearMap.trace Complex QubitSpace raw := by
        intro raw
        exact tSupplyAggregateLinear_trace tMagicState nextTrue nextFalse
          htrueTrace hfalseTrace attempts raw
      have hpairActualPositive : LinearMap.IsPositive (tPairInputRaw t) :=
        tPairInputRaw_positive t
      have hpairIdealPositive : LinearMap.IsPositive (tPairInputRaw tMagicState) :=
        tPairInputRaw_positive tMagicState
      have hpairSymmetric :
          (tPairInputRaw t - tPairInputRaw tMagicState).IsSymmetric :=
        hpairActualPositive.isSymmetric.sub hpairIdealPositive.isSymmetric
      have hdataTrace : 0 ≤ (LinearMap.trace Complex QubitSpace data).re :=
        (Complex.nonneg_iff.mp hdata.trace_nonneg).1
      have hcurrent :
          traceNorm
            (tPairContinuationLinear data nextTrue nextFalse idealTail
              (tPairInputRaw t - tPairInputRaw tMagicState)) ≤
            2 * (LinearMap.trace Complex QubitSpace data).re *
              traceNorm (t.toOperator - tMagicState.toOperator) := by
        calc
          traceNorm
              (tPairContinuationLinear data nextTrue nextFalse idealTail
                (tPairInputRaw t - tPairInputRaw tMagicState)) ≤
              (LinearMap.trace Complex QubitSpace data).re *
                traceNorm (tPairInputRaw t - tPairInputRaw tMagicState) := by
            exact tPairContinuationLinear_traceNorm_le data nextTrue nextFalse idealTail
              htruePositive hfalsePositive hidealTailPositive htrueTrace hfalseTrace
              hidealTailTrace _ hdata hpairSymmetric
          _ ≤ (LinearMap.trace Complex QubitSpace data).re *
                (2 * traceNorm (t.toOperator - tMagicState.toOperator)) := by
            exact mul_le_mul_of_nonneg_left (tPairInputRaw_difference_le t) hdataTrace
          _ = 2 * (LinearMap.trace Complex QubitSpace data).re *
                traceNorm (t.toOperator - tMagicState.toOperator) := by ring
      have hactual :
          tSupplyAggregateLinear t (attempts + 1) nextTrue nextFalse data =
            tPairContinuationLinear data nextTrue nextFalse actualTail (tPairInputRaw t) := by
        rw [tPairContinuationLinear_tPairInput_apply]
        rfl
      have hideal :
          tSupplyAggregateLinear tMagicState (attempts + 1) nextTrue nextFalse data =
            tPairContinuationLinear data nextTrue nextFalse idealTail
              (tPairInputRaw tMagicState) := by
        rw [tPairContinuationLinear_tPairInput_apply]
        rfl
      rw [hactual, hideal]
      have htele :
          tPairContinuationLinear data nextTrue nextFalse actualTail (tPairInputRaw t) -
              tPairContinuationLinear data nextTrue nextFalse idealTail
                (tPairInputRaw tMagicState) =
            (tPairContinuationLinear data nextTrue nextFalse actualTail (tPairInputRaw t) -
              tPairContinuationLinear data nextTrue nextFalse idealTail (tPairInputRaw t)) +
            tPairContinuationLinear data nextTrue nextFalse idealTail
              (tPairInputRaw t - tPairInputRaw tMagicState) := by
        calc
          tPairContinuationLinear data nextTrue nextFalse actualTail (tPairInputRaw t) -
              tPairContinuationLinear data nextTrue nextFalse idealTail
                (tPairInputRaw tMagicState) =
              (tPairContinuationLinear data nextTrue nextFalse actualTail (tPairInputRaw t) -
                tPairContinuationLinear data nextTrue nextFalse idealTail (tPairInputRaw t)) +
              (tPairContinuationLinear data nextTrue nextFalse idealTail (tPairInputRaw t) -
                tPairContinuationLinear data nextTrue nextFalse idealTail
                  (tPairInputRaw tMagicState)) := by
                module
          _ = _ := by
                rw [← (tPairContinuationLinear data nextTrue nextFalse idealTail).map_sub]
      rw [htele]
      calc
        traceNorm
            ((tPairContinuationLinear data nextTrue nextFalse actualTail (tPairInputRaw t) -
                tPairContinuationLinear data nextTrue nextFalse idealTail (tPairInputRaw t)) +
              tPairContinuationLinear data nextTrue nextFalse idealTail
                (tPairInputRaw t - tPairInputRaw tMagicState)) ≤
            traceNorm
              (tPairContinuationLinear data nextTrue nextFalse actualTail (tPairInputRaw t) -
                tPairContinuationLinear data nextTrue nextFalse idealTail (tPairInputRaw t)) +
              traceNorm
                (tPairContinuationLinear data nextTrue nextFalse idealTail
                  (tPairInputRaw t - tPairInputRaw tMagicState)) :=
          traceNorm_add_le _ _
        _ ≤ (2 * attempts : Real) * (LinearMap.trace Complex QubitSpace data).re *
              traceNorm (t.toOperator - tMagicState.toOperator) +
            2 * (LinearMap.trace Complex QubitSpace data).re *
              traceNorm (t.toOperator - tMagicState.toOperator) :=
          add_le_add hfuture hcurrent
        _ = (2 * ((attempts + 1 : Nat) : Real)) *
              (LinearMap.trace Complex QubitSpace data).re *
                traceNorm (t.toOperator - tMagicState.toOperator) := by
          norm_num only [Nat.cast_add, Nat.cast_one]
          ring

private theorem tRetryAggregateLinear_positive
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12) :
    ∀ (remaining : Nat) (position : ZMod 12) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      LinearMap.IsPositive (tRetryAggregateLinear t pairAttempts target remaining position data) := by
  intro remaining
  induction remaining with
  | zero =>
      intro position data hdata
      simpa [tRetryAggregateLinear] using hdata
  | succ remaining ih =>
      intro position data hdata
      by_cases htarget : position = target
      · simpa [tRetryAggregateLinear, htarget] using hdata
      · simpa [tRetryAggregateLinear, htarget] using tSupplyAggregateLinear_positive t
          (tRetryAggregateLinear t pairAttempts target remaining (position + 1))
          (tRetryAggregateLinear t pairAttempts target remaining (position - 1))
          (fun raw hraw => ih (position + 1) raw hraw)
          (fun raw hraw => ih (position - 1) raw hraw)
          pairAttempts data hdata

private theorem tRetryAggregateLinear_trace
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12) :
    ∀ (remaining : Nat) (position : ZMod 12) (data : Operator QubitSpace),
      LinearMap.trace Complex QubitSpace
        (tRetryAggregateLinear t pairAttempts target remaining position data) =
        LinearMap.trace Complex QubitSpace data := by
  intro remaining
  induction remaining with
  | zero =>
      intro position data
      simp [tRetryAggregateLinear]
  | succ remaining ih =>
      intro position data
      by_cases htarget : position = target
      · simp [tRetryAggregateLinear, htarget]
      · simpa [tRetryAggregateLinear, htarget] using tSupplyAggregateLinear_trace t
          (tRetryAggregateLinear t pairAttempts target remaining (position + 1))
          (tRetryAggregateLinear t pairAttempts target remaining (position - 1))
          (fun raw => ih (position + 1) raw)
          (fun raw => ih (position - 1) raw)
          pairAttempts data

/-- A literal T retry aggregate charges a two-resource source replacement at
each reached phase site; the bounded supplier transports the remaining phase
continuation budget without multiplying it by its retry count. -/
private theorem tRetryAggregateLinear_stable
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (remaining : Nat) :
    ∀ (position : ZMod 12) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      traceNorm
        (tRetryAggregateLinear t pairAttempts target remaining position data -
          tRetryAggregateLinear tMagicState pairAttempts target remaining position data) ≤
        (2 * pairAttempts * remaining : Real) *
          (LinearMap.trace Complex QubitSpace data).re *
            traceNorm (t.toOperator - tMagicState.toOperator) := by
  induction remaining with
  | zero =>
      intro position data hdata
      have hzero : traceNorm (0 : Operator QubitSpace) = 0 :=
        (traceNorm_eq_zero_iff 0).mpr rfl
      simp [tRetryAggregateLinear, hzero]
  | succ remaining ih =>
      intro position data hdata
      by_cases htarget : position = target
      · have hright : 0 ≤ (2 * pairAttempts * (remaining + 1) : Real) *
            (LinearMap.trace Complex QubitSpace data).re *
              traceNorm (t.toOperator - tMagicState.toOperator) := by
            have hdataTrace : 0 ≤ (LinearMap.trace Complex QubitSpace data).re :=
              (Complex.nonneg_iff.mp hdata.trace_nonneg).1
            have hcoefficient : 0 ≤ (2 * pairAttempts * (remaining + 1) : Real) := by
              exact_mod_cast Nat.zero_le (2 * pairAttempts * (remaining + 1))
            exact mul_nonneg (mul_nonneg hcoefficient hdataTrace) (traceNorm_nonneg _)
        have hzero : traceNorm (0 : Operator QubitSpace) = 0 :=
          (traceNorm_eq_zero_iff 0).mpr rfl
        simpa [tRetryAggregateLinear, htarget, hzero] using hright
      · let nextTrueActual :=
          tRetryAggregateLinear t pairAttempts target remaining (position + 1)
        let nextFalseActual :=
          tRetryAggregateLinear t pairAttempts target remaining (position - 1)
        let nextTrueIdeal :=
          tRetryAggregateLinear tMagicState pairAttempts target remaining (position + 1)
        let nextFalseIdeal :=
          tRetryAggregateLinear tMagicState pairAttempts target remaining (position - 1)
        have hnextTrueActualPositive : ∀ raw, LinearMap.IsPositive raw →
            LinearMap.IsPositive (nextTrueActual raw) := by
          intro raw hraw
          exact tRetryAggregateLinear_positive t pairAttempts target remaining
            (position + 1) raw hraw
        have hnextFalseActualPositive : ∀ raw, LinearMap.IsPositive raw →
            LinearMap.IsPositive (nextFalseActual raw) := by
          intro raw hraw
          exact tRetryAggregateLinear_positive t pairAttempts target remaining
            (position - 1) raw hraw
        have hnextTrueActualTrace : ∀ raw,
            LinearMap.trace Complex QubitSpace (nextTrueActual raw) =
              LinearMap.trace Complex QubitSpace raw := by
          intro raw
          exact tRetryAggregateLinear_trace t pairAttempts target remaining
            (position + 1) raw
        have hnextFalseActualTrace : ∀ raw,
            LinearMap.trace Complex QubitSpace (nextFalseActual raw) =
              LinearMap.trace Complex QubitSpace raw := by
          intro raw
          exact tRetryAggregateLinear_trace t pairAttempts target remaining
            (position - 1) raw
        have hsource :
            traceNorm
              (tSupplyAggregateLinear t pairAttempts nextTrueActual nextFalseActual data -
                tSupplyAggregateLinear tMagicState pairAttempts
                  nextTrueActual nextFalseActual data) ≤
              (2 * pairAttempts : Real) *
                (LinearMap.trace Complex QubitSpace data).re *
                  traceNorm (t.toOperator - tMagicState.toOperator) := by
          exact tSupplyAggregateLinear_source_stable t nextTrueActual nextFalseActual
            hnextTrueActualPositive hnextFalseActualPositive
            hnextTrueActualTrace hnextFalseActualTrace pairAttempts data hdata
        have hbudget : 0 ≤ (2 * pairAttempts * remaining : Real) := by positivity
        have hdelta : 0 ≤ traceNorm (t.toOperator - tMagicState.toOperator) :=
          traceNorm_nonneg _
        have hcontinuation :
            traceNorm
              (tSupplyAggregateLinear tMagicState pairAttempts
                  nextTrueActual nextFalseActual data -
                tSupplyAggregateLinear tMagicState pairAttempts
                  nextTrueIdeal nextFalseIdeal data) ≤
              (2 * pairAttempts * remaining : Real) *
                (LinearMap.trace Complex QubitSpace data).re *
                  traceNorm (t.toOperator - tMagicState.toOperator) := by
          exact tSupplyAggregateLinear_continuation_stable tMagicState
            nextTrueActual nextFalseActual nextTrueIdeal nextFalseIdeal
            (2 * pairAttempts * remaining : Real)
            (traceNorm (t.toOperator - tMagicState.toOperator)) hbudget hdelta
            (fun raw hraw => ih (position + 1) raw hraw)
            (fun raw hraw => ih (position - 1) raw hraw)
            pairAttempts data hdata
        have hactual :
            tRetryAggregateLinear t pairAttempts target (remaining + 1) position data =
              tSupplyAggregateLinear t pairAttempts nextTrueActual nextFalseActual data := by
          simp [tRetryAggregateLinear, htarget, nextTrueActual, nextFalseActual]
        have hideal :
            tRetryAggregateLinear tMagicState pairAttempts target (remaining + 1) position data =
              tSupplyAggregateLinear tMagicState pairAttempts nextTrueIdeal nextFalseIdeal data := by
          simp [tRetryAggregateLinear, htarget, nextTrueIdeal, nextFalseIdeal]
        rw [hactual, hideal]
        have htele :
            tSupplyAggregateLinear t pairAttempts nextTrueActual nextFalseActual data -
              tSupplyAggregateLinear tMagicState pairAttempts nextTrueIdeal nextFalseIdeal data =
            (tSupplyAggregateLinear t pairAttempts nextTrueActual nextFalseActual data -
              tSupplyAggregateLinear tMagicState pairAttempts
                nextTrueActual nextFalseActual data) +
            (tSupplyAggregateLinear tMagicState pairAttempts
                nextTrueActual nextFalseActual data -
              tSupplyAggregateLinear tMagicState pairAttempts
                nextTrueIdeal nextFalseIdeal data) := by
          module
        rw [htele]
        calc
          traceNorm
              ((tSupplyAggregateLinear t pairAttempts nextTrueActual nextFalseActual data -
                  tSupplyAggregateLinear tMagicState pairAttempts
                    nextTrueActual nextFalseActual data) +
                (tSupplyAggregateLinear tMagicState pairAttempts
                    nextTrueActual nextFalseActual data -
                  tSupplyAggregateLinear tMagicState pairAttempts
                    nextTrueIdeal nextFalseIdeal data)) ≤
              traceNorm
                (tSupplyAggregateLinear t pairAttempts nextTrueActual nextFalseActual data -
                  tSupplyAggregateLinear tMagicState pairAttempts
                    nextTrueActual nextFalseActual data) +
                traceNorm
                  (tSupplyAggregateLinear tMagicState pairAttempts
                    nextTrueActual nextFalseActual data -
                  tSupplyAggregateLinear tMagicState pairAttempts
                    nextTrueIdeal nextFalseIdeal data) :=
            traceNorm_add_le _ _
          _ ≤ (2 * pairAttempts : Real) *
                (LinearMap.trace Complex QubitSpace data).re *
                  traceNorm (t.toOperator - tMagicState.toOperator) +
              (2 * pairAttempts * remaining : Real) *
                (LinearMap.trace Complex QubitSpace data).re *
                  traceNorm (t.toOperator - tMagicState.toOperator) :=
            add_le_add hsource hcontinuation
          _ = (2 * (pairAttempts : Real) * ((remaining + 1 : Nat) : Real)) *
                (LinearMap.trace Complex QubitSpace data).re *
                  traceNorm (t.toOperator - tMagicState.toOperator) := by
            norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
            ring

/-- Aggregate a concrete supplier outcome list through its phase and
exhaustion continuations. -/
private def tSupplyAggregateValue
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    List BK05TSupplyOutcome → Operator QubitSpace
  | [] => 0
  | .accepted _ _ data phaseResource :: outcomes =>
      nextTrue (phaseBranchRaw phaseResource data true) +
        nextFalse (phaseBranchRaw phaseResource data false) +
        tSupplyAggregateValue nextTrue nextFalse outcomes
  | .exhausted _ _ data :: outcomes =>
      data + tSupplyAggregateValue nextTrue nextFalse outcomes

private theorem tSupplyAggregateLinear_value
    (t : DensityOperator QubitSpace)
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    ∀ (attempts : Nat) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace),
      tSupplyAggregateLinear t attempts nextTrue nextFalse data =
        tSupplyAggregateValue nextTrue nextFalse (tSupply t attempts ledger history data) := by
  intro attempts
  induction attempts with
  | zero =>
      intro ledger history data
      simp [tSupply, tSupplyAggregateLinear, tSupplyAggregateValue]
  | succ attempts ih =>
      intro ledger history data
      let nextLedger := ledger + ({.t, .t} : ResourceLedger BK05ResourceToken)
      simp only [tSupply, tSupplyAggregateLinear, LinearMap.add_apply, LinearMap.comp_apply,
        phaseBranchRawLinear_apply, tSupplyAggregateValue]
      rw [tRejectedDataRawLinear_apply,
        ih nextLedger (false :: history) (tRejectedDataRaw data t)]

/-- The nested linear carrier is definitionally the aggregate of the literal
T retry tree, including the supplier's explicit exhausted-pair leaves. -/
private theorem tRetryAggregateLinear_apply
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (remaining : Nat) :
    ∀ (position : ZMod 12) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace),
      tRetryAggregateLinear t pairAttempts target remaining position data =
        rawAggregate (tRetry t pairAttempts target remaining position ledger history data) := by
  induction remaining with
  | zero =>
      intro position ledger history data
      by_cases htarget : position = target <;>
        simp [tRetry, tRetryAggregateLinear, rawAggregate, htarget]
  | succ remaining ih =>
      intro position ledger history data
      by_cases htarget : position = target
      · simp [tRetry, tRetryAggregateLinear, rawAggregate, htarget]
      · rw [tRetry, if_neg htarget]
        let continuation : BK05TSupplyOutcome → List BK05RawLeaf := fun supplied =>
          match supplied with
          | .accepted suppliedLedger suppliedHistory suppliedData phaseResource =>
              tRetry t pairAttempts target remaining (position + 1) suppliedLedger
                  (true :: suppliedHistory)
                  (phaseBranchRaw phaseResource suppliedData true)
                ++
              tRetry t pairAttempts target remaining (position - 1) suppliedLedger
                  (false :: suppliedHistory)
                  (phaseBranchRaw phaseResource suppliedData false)
          | .exhausted suppliedLedger suppliedHistory suppliedData =>
              [⟨.tPairExhausted, suppliedHistory, suppliedLedger, suppliedData⟩]
        let nextTrue := tRetryAggregateLinear t pairAttempts target remaining (position + 1)
        let nextFalse := tRetryAggregateLinear t pairAttempts target remaining (position - 1)
        have hvalue := tSupplyAggregateLinear_value t nextTrue nextFalse
          pairAttempts ledger history data
        have hflat :
            rawAggregate ((tSupply t pairAttempts ledger history data).flatMap continuation) =
              tSupplyAggregateValue nextTrue nextFalse (tSupply t pairAttempts ledger history data) := by
          induction tSupply t pairAttempts ledger history data with
          | nil => simp [tSupplyAggregateValue, rawAggregate]
          | cons supplied outcomes ihout =>
              cases supplied with
              | accepted suppliedLedger suppliedHistory suppliedData phaseResource =>
                  rw [List.flatMap_cons, rawAggregate_append, rawAggregate_append,
                    ← ih (position + 1) suppliedLedger (true :: suppliedHistory)
                      (phaseBranchRaw phaseResource suppliedData true),
                    ← ih (position - 1) suppliedLedger (false :: suppliedHistory)
                      (phaseBranchRaw phaseResource suppliedData false), ihout]
                  simp [continuation, nextTrue, nextFalse, tSupplyAggregateValue]
              | exhausted suppliedLedger suppliedHistory suppliedData =>
                  rw [List.flatMap_cons, rawAggregate_append, ihout]
                  simp [continuation, tSupplyAggregateValue, rawAggregate]
        have hcarrier :
            tSupplyAggregateLinear t pairAttempts nextTrue nextFalse data =
              tSupplyAggregateValue nextTrue nextFalse (tSupply t pairAttempts ledger history data) :=
          hvalue
        simpa [tRetryAggregateLinear, htarget, nextTrue, nextFalse] using
          hcarrier.trans hflat.symm

/-- The actual unconditioned T retry aggregate changes by at most two source
resource trace distances for each bounded fresh-pair attempt at each of the
literal order-twelve phase sites. -/
theorem tActualRawTree_aggregate_traceNorm_le
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (blocks : Nat) (rho : DensityOperator QubitSpace) :
    traceNorm
      (rawAggregate (tActualRawTree t pairAttempts target blocks rho) -
        rawAggregate (tActualRawTree tMagicState pairAttempts target blocks rho)) ≤
      (2 * pairAttempts * 12 * blocks : Real) *
        traceNorm (t.toOperator - tMagicState.toOperator) := by
  change traceNorm
      (rawAggregate
          (tRetry t pairAttempts target (12 * blocks) 0 0 [] rho.toOperator) -
        rawAggregate
          (tRetry tMagicState pairAttempts target (12 * blocks) 0 0 [] rho.toOperator)) ≤ _
  rw [← tRetryAggregateLinear_apply t pairAttempts target (12 * blocks)
      0 0 [] rho.toOperator,
    ← tRetryAggregateLinear_apply tMagicState pairAttempts target (12 * blocks)
      0 0 [] rho.toOperator]
  have hstable := tRetryAggregateLinear_stable t pairAttempts target (12 * blocks)
    0 rho.toOperator rho.positive
  simpa [rho.trace_one, Nat.cast_mul, mul_assoc] using hstable

/-- A finite algebraic word over the one-qubit generators used by the local
BK05 route.  This syntax deliberately has no topological-closure constructor. -/
private inductive BK05GeneratorWord
    (generators : Set (UnitaryGate (Fin 2))) : Type
  | one : BK05GeneratorWord generators
  | generator (gate : UnitaryGate (Fin 2))
      (hgate : gate ∈ generators) : BK05GeneratorWord generators
  | mul (left right : BK05GeneratorWord generators) :
      BK05GeneratorWord generators
  | inverse (word : BK05GeneratorWord generators) :
      BK05GeneratorWord generators

/-- Evaluate an algebraic word with the group-product orientation needed for
the later reversed circuit-composition compilation route. -/
private noncomputable def BK05GeneratorWord.eval
    {generators : Set (UnitaryGate (Fin 2))} :
    BK05GeneratorWord generators → UnitaryGate (Fin 2)
  | .one => 1
  | .generator gate _ => gate
  | .mul left right => left.eval * right.eval
  | .inverse word => word.eval⁻¹

/-- Every element of the algebraically generated subgroup has a literal finite
word.  The induction is over subgroup closure, not topological closure. -/
private theorem generatedUnitarySubgroup_exists_word
    (generators : Set (UnitaryGate (Fin 2)))
    {gate : UnitaryGate (Fin 2)}
    (hgate : gate ∈ generatedUnitarySubgroup generators) :
    ∃ word : BK05GeneratorWord generators, word.eval = gate := by
  change gate ∈ Subgroup.closure generators at hgate
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hgate
  · intro sourceGate hsourceGate
    exact ⟨.generator sourceGate hsourceGate, rfl⟩
  · exact ⟨.one, rfl⟩
  · intro left right _ _ hleft hright
    rcases hleft with ⟨leftWord, rfl⟩
    rcases hright with ⟨rightWord, rfl⟩
    exact ⟨.mul leftWord rightWord, rfl⟩
  · intro sourceGate _ hsourceGate
    rcases hsourceGate with ⟨word, rfl⟩
    exact ⟨.inverse word, rfl⟩

/-- Projective density supplies a representative; metric closure then supplies
an actual subgroup candidate, which is immediately reified as a finite word.
The bound is intentionally centered at that phase-equivalent representative. -/
private theorem projectivelyGeneratedDense_exists_word_matrix_close
    (generators : Set (UnitaryGate (Fin 2)))
    (hdense : ProjectivelyGeneratedDense generators)
    (target : UnitaryGate (Fin 2)) (ε : Real) (hε : 0 < ε) :
    ∃ representative : UnitaryGate (Fin 2),
      GlobalPhaseEquivalent target representative ∧
      ∃ word : BK05GeneratorWord generators,
        ‖(word.eval : Matrix (Fin 2) (Fin 2) Complex) -
          (representative : Matrix (Fin 2) (Fin 2) Complex)‖ < ε := by
  rcases hdense target with ⟨representative, hclosure, hphase⟩
  change representative ∈
    closure (generatedUnitarySubgroup generators : Set (UnitaryGate (Fin 2)))
    at hclosure
  rcases (Metric.mem_closure_iff.mp hclosure) ε hε with
    ⟨candidate, hcandidate, hdist⟩
  rcases generatedUnitarySubgroup_exists_word generators hcandidate with
    ⟨word, hword⟩
  refine ⟨representative, hphase, word, ?_⟩
  rw [← hword] at hdist
  calc
    ‖((word.eval : UnitaryGate (Fin 2)) :
        Matrix (Fin 2) (Fin 2) Complex) -
      (representative : Matrix (Fin 2) (Fin 2) Complex)‖ =
        ‖(representative : Matrix (Fin 2) (Fin 2) Complex) -
          ((word.eval : UnitaryGate (Fin 2)) :
            Matrix (Fin 2) (Fin 2) Complex)‖ := norm_sub_rev _ _
    _ = dist representative word.eval := by
      rw [Subtype.dist_eq, dist_eq_norm]
    _ < ε := hdist

/-- Whether a structural word compiler evaluates its word normally or as its
group inverse.  This is only ideal finite-register circuit semantics. -/
private inductive BK05WordPolarity where
  | normal | inverse

private def BK05WordPolarity.flip : BK05WordPolarity → BK05WordPolarity
  | .normal => .inverse
  | .inverse => .normal

/-- The one-qubit value selected by a normal or inverse compilation pass. -/
private noncomputable def BK05GeneratorWord.orientedEval
    {generators : Set (UnitaryGate (Fin 2))}
    (word : BK05GeneratorWord generators) :
    BK05WordPolarity → UnitaryGate (Fin 2)
  | .normal => word.eval
  | .inverse => word.eval⁻¹

/-- Compile a finite algebraic word on one selected register wire.  A product
is reversed at the circuit-syntax level because circuit composition evaluates
its second argument on the left. -/
private noncomputable def BK05GeneratorWord.compileAt
    {generators : Set (UnitaryGate (Fin 2))}
    {Wire : Type u} [Fintype Wire] [DecidableEq Wire] (wire : Wire) :
    (word : BK05GeneratorWord generators) → BK05WordPolarity →
      FiniteRegisterCircuit Wire
  | .one, _ => .identity
  | .generator gate _, .normal => .oneQubit wire gate
  | .generator gate _, .inverse => .oneQubit wire gate⁻¹
  | .mul left right, .normal =>
      .compose (right.compileAt wire .normal) (left.compileAt wire .normal)
  | .mul left right, .inverse =>
      .compose (left.compileAt wire .inverse) (right.compileAt wire .inverse)
  | .inverse word, polarity => word.compileAt wire polarity.flip

/-- The private compiler implements the selected-wire lift of the requested
word polarity.  Nested inverses are discharged structurally. -/
private theorem BK05GeneratorWord.compileAt_unitary
    {generators : Set (UnitaryGate (Fin 2))}
    {Wire : Type u} [Fintype Wire] [DecidableEq Wire] (wire : Wire) :
    ∀ (word : BK05GeneratorWord generators) (polarity : BK05WordPolarity),
      (word.compileAt wire polarity).unitary =
        singleQubitLift wire (word.orientedEval polarity) := by
  intro word
  induction word with
  | one =>
      intro polarity
      cases polarity <;>
        simp [BK05GeneratorWord.compileAt, BK05GeneratorWord.orientedEval,
          BK05GeneratorWord.eval, singleQubitLift_one]
  | generator gate hgate =>
      intro polarity
      cases polarity <;> rfl
  | mul left right ihLeft ihRight =>
      intro polarity
      cases polarity with
      | normal =>
          change
            (FiniteRegisterCircuit.compose (right.compileAt wire .normal)
                (left.compileAt wire .normal)).unitary =
              singleQubitLift wire (left.eval * right.eval)
          rw [FiniteRegisterCircuit.unitary_compose,
            ihLeft .normal, ihRight .normal]
          exact (singleQubitLift_mul wire left.eval right.eval).symm
      | inverse =>
          change
            (FiniteRegisterCircuit.compose (left.compileAt wire .inverse)
                (right.compileAt wire .inverse)).unitary =
              singleQubitLift wire (left.eval * right.eval)⁻¹
          rw [FiniteRegisterCircuit.unitary_compose,
            ihRight .inverse, ihLeft .inverse]
          simp only [BK05GeneratorWord.orientedEval]
          rw [← singleQubitLift_mul, ← mul_inv_rev]
  | inverse word ih =>
      intro polarity
      cases polarity with
      | normal =>
          change (word.compileAt wire .inverse).unitary =
            singleQubitLift wire word.eval⁻¹
          calc
            (word.compileAt wire .inverse).unitary =
                (singleQubitLift wire word.eval)⁻¹ := by
              rw [ih .inverse]
              exact singleQubitLift_inv wire word.eval
            _ = singleQubitLift wire word.eval⁻¹ :=
              (singleQubitLift_inv wire word.eval).symm
      | inverse =>
          simpa [BK05GeneratorWord.compileAt, BK05GeneratorWord.orientedEval,
            BK05GeneratorWord.eval, BK05WordPolarity.flip] using ih .normal

/-- The normal compiler specialization has exactly the original word value. -/
private theorem BK05GeneratorWord.compileAt_normal_unitary
    {generators : Set (UnitaryGate (Fin 2))}
    {Wire : Type u} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) (word : BK05GeneratorWord generators) :
    (word.compileAt wire .normal).unitary = singleQubitLift wire word.eval := by
  simpa [BK05GeneratorWord.orientedEval] using
    BK05GeneratorWord.compileAt_unitary wire word .normal

/-- The three positive atom kinds in a Clifford-plus-phase route. -/
private inductive BK05PhaseAtom (theta : Real) : Type
  | h
  | k
  | phase

private noncomputable def BK05PhaseAtom.eval (theta : Real) :
    BK05PhaseAtom theta → UnitaryGate (Fin 2)
  | .h => hadamardGate
  | .k => phaseGate
  | .phase => phaseShiftGate theta

/-- A route atom together with the algebraic sign applied to it. -/
private inductive BK05SignedPhaseLetter (theta : Real) : Type
  | positive (atom : BK05PhaseAtom theta)
  | negative (atom : BK05PhaseAtom theta)

private noncomputable def BK05SignedPhaseLetter.eval (theta : Real) :
    BK05SignedPhaseLetter theta → UnitaryGate (Fin 2)
  | .positive atom => atom.eval theta
  | .negative atom => (atom.eval theta)⁻¹

/-- The syntactic phase cost of a signed tagged atom. -/
private def BK05SignedPhaseLetter.phaseCost (theta : Real) :
    BK05SignedPhaseLetter theta → Nat
  | .positive .phase => 1
  | .negative .phase => 1
  | _ => 0

/-- A generator-set witness provides some matching route atom, without any
pairwise-distinctness assumption on the displayed generators. -/
private theorem exists_phaseAtom_eq_of_mem
    (theta : Real) (gate : UnitaryGate (Fin 2))
    (hgate : gate ∈ cliffordPhaseGenerators theta) :
    ∃ atom : BK05PhaseAtom theta, atom.eval theta = gate := by
  simp only [cliffordPhaseGenerators, Set.mem_insert_iff, Set.mem_singleton_iff]
    at hgate
  rcases hgate with hgate | hgate | hgate
  · exact ⟨.h, hgate.symm⟩
  · exact ⟨.k, hgate.symm⟩
  · exact ⟨.phase, hgate.symm⟩

/-- Choose one equality-certified tagged atom for a route generator. -/
private noncomputable def reifyPhaseAtom
    (theta : Real) (gate : UnitaryGate (Fin 2))
    (hgate : gate ∈ cliffordPhaseGenerators theta) :
    {atom : BK05PhaseAtom theta // atom.eval theta = gate} :=
  ⟨Classical.choose (exists_phaseAtom_eq_of_mem theta gate hgate),
    Classical.choose_spec (exists_phaseAtom_eq_of_mem theta gate hgate)⟩

private theorem reifyPhaseAtom_spec
    (theta : Real) (gate : UnitaryGate (Fin 2))
    (hgate : gate ∈ cliffordPhaseGenerators theta) :
    (reifyPhaseAtom theta gate hgate).1.eval theta = gate :=
  (reifyPhaseAtom theta gate hgate).2

/-- Push all source inverses into signs on a finite H/K/phase tagged list.
The list is ordered for group multiplication, not circuit execution. -/
private noncomputable def BK05GeneratorWord.normalizeSigned
    (theta : Real) :
    BK05WordPolarity →
    BK05GeneratorWord (cliffordPhaseGenerators theta) →
      List (BK05SignedPhaseLetter theta)
  | .normal, .one => []
  | .inverse, .one => []
  | .normal, .generator gate hgate =>
      [.positive (reifyPhaseAtom theta gate hgate).1]
  | .inverse, .generator gate hgate =>
      [.negative (reifyPhaseAtom theta gate hgate).1]
  | .normal, .mul left right =>
      left.normalizeSigned theta .normal ++ right.normalizeSigned theta .normal
  | .inverse, .mul left right =>
      right.normalizeSigned theta .inverse ++ left.normalizeSigned theta .inverse
  | polarity, .inverse word => word.normalizeSigned theta polarity.flip

private noncomputable def BK05SignedPhaseLetter.evalList (theta : Real) :
    List (BK05SignedPhaseLetter theta) → UnitaryGate (Fin 2)
  | [] => 1
  | letter :: tail => letter.eval theta * evalList theta tail

private theorem BK05SignedPhaseLetter.evalList_append
    (theta : Real) (left right : List (BK05SignedPhaseLetter theta)) :
    BK05SignedPhaseLetter.evalList theta (left ++ right) =
      BK05SignedPhaseLetter.evalList theta left *
        BK05SignedPhaseLetter.evalList theta right := by
  induction left with
  | nil => simp [BK05SignedPhaseLetter.evalList]
  | cons letter tail ih =>
      simp [BK05SignedPhaseLetter.evalList, ih, mul_assoc]

private def BK05SignedPhaseLetter.resourceCount (theta : Real) :
    List (BK05SignedPhaseLetter theta) → Nat
  | [] => 0
  | letter :: tail => letter.phaseCost theta + resourceCount theta tail

/-- Count phase-signed letters in the chosen tagged representation.  This is
not an intrinsic minimum when displayed generators coincide. -/
private noncomputable def BK05GeneratorWord.phaseLetterCount
    (theta : Real)
    (word : BK05GeneratorWord (cliffordPhaseGenerators theta)) : Nat :=
  BK05SignedPhaseLetter.resourceCount theta
    (word.normalizeSigned theta .normal)

/-- Signed normalization preserves the source word's exact group value in
either requested polarity. -/
private theorem BK05GeneratorWord.normalizeSigned_eval
    (theta : Real) :
    ∀ (polarity : BK05WordPolarity)
      (word : BK05GeneratorWord (cliffordPhaseGenerators theta)),
      BK05SignedPhaseLetter.evalList theta
          (word.normalizeSigned theta polarity) =
        match polarity with
        | .normal => word.eval
        | .inverse => word.eval⁻¹ := by
  intro polarity word
  induction word generalizing polarity with
  | one =>
      cases polarity <;>
        simp [BK05GeneratorWord.normalizeSigned, BK05SignedPhaseLetter.evalList,
          BK05GeneratorWord.eval]
  | generator gate hgate =>
      cases polarity with
      | normal =>
          simpa [BK05GeneratorWord.normalizeSigned,
            BK05SignedPhaseLetter.evalList, BK05SignedPhaseLetter.eval,
            BK05GeneratorWord.eval] using
            reifyPhaseAtom_spec theta gate hgate
      | inverse =>
          simpa [BK05GeneratorWord.normalizeSigned,
            BK05SignedPhaseLetter.evalList, BK05SignedPhaseLetter.eval,
            BK05GeneratorWord.eval] using
            congrArg (fun sourceGate : UnitaryGate (Fin 2) => sourceGate⁻¹)
              (reifyPhaseAtom_spec theta gate hgate)
  | mul left right ihLeft ihRight =>
      cases polarity with
      | normal =>
          change BK05SignedPhaseLetter.evalList theta
              (left.normalizeSigned theta .normal ++ right.normalizeSigned theta .normal) =
            left.eval * right.eval
          rw [BK05SignedPhaseLetter.evalList_append,
            ihLeft .normal, ihRight .normal]
      | inverse =>
          change BK05SignedPhaseLetter.evalList theta
              (right.normalizeSigned theta .inverse ++ left.normalizeSigned theta .inverse) =
            (left.eval * right.eval)⁻¹
          rw [BK05SignedPhaseLetter.evalList_append,
            ihRight .inverse, ihLeft .inverse, mul_inv_rev]
  | inverse word ih =>
      cases polarity with
      | normal =>
          simpa [BK05GeneratorWord.normalizeSigned, BK05GeneratorWord.eval,
            BK05WordPolarity.flip] using ih .inverse
      | inverse =>
          simpa [BK05GeneratorWord.normalizeSigned, BK05GeneratorWord.eval,
            BK05WordPolarity.flip] using ih .normal

/-- Whether a word-family leaf can consume another letter or is a retained
terminal stopping outcome. -/
private inductive BK05WordLeafStatus where
  | live
  | stoppedPhaseExhausted
  | stoppedTPairExhausted

/-- A compiler-local raw leaf.  Its payload is copied from the literal retry
tree and its status controls only whether a later letter may run. -/
private structure BK05WordRawLeaf where
  status : BK05WordLeafStatus
  history : List Bool
  ledger : ResourceLedger BK05ResourceToken
  raw : Operator QubitSpace

/-- Import every literal Task-4 terminal reason into the compiler-local
stopping carrier. -/
private def importRawStatus : BK05RawLeafKind → BK05WordLeafStatus
  | .targetHit => .live
  | .phaseExhausted => .stoppedPhaseExhausted
  | .tPairExhausted => .stoppedTPairExhausted

private def importRawLeaf (leaf : BK05RawLeaf) : BK05WordRawLeaf :=
  .mk (importRawStatus leaf.kind) leaf.history leaf.ledger leaf.raw

/-- Import a complete retry family without removing any of its leaves. -/
private def importRawLeaves (leaves : List BK05RawLeaf) : List BK05WordRawLeaf :=
  leaves.map importRawLeaf

private theorem importRawLeaf_raw (leaf : BK05RawLeaf) :
    (importRawLeaf leaf).raw = leaf.raw := by
  cases leaf with
  | mk kind history ledger raw =>
      cases kind <;> rfl

private theorem importRawLeaf_history (leaf : BK05RawLeaf) :
    (importRawLeaf leaf).history = leaf.history := by
  cases leaf with
  | mk kind history ledger raw =>
      cases kind <;> rfl

private theorem importRawLeaf_ledger (leaf : BK05RawLeaf) :
    (importRawLeaf leaf).ledger = leaf.ledger := by
  cases leaf with
  | mk kind history ledger raw =>
      cases kind <;> rfl

/-- Every literal source leaf, including an algebraic zero leaf, occurs in the
imported family with the same payload. -/
private theorem importRawLeaves_retains
    (leaves : List BK05RawLeaf) (leaf : BK05RawLeaf) (hmem : leaf ∈ leaves) :
    importRawLeaf leaf ∈ importRawLeaves leaves := by
  simpa [importRawLeaves] using List.mem_map_of_mem hmem

private def wordRawWeight (leaf : BK05WordRawLeaf) : Real :=
  (LinearMap.trace Complex QubitSpace leaf.raw).re

private def wordRawMass (leaves : List BK05WordRawLeaf) : Real :=
  (leaves.map wordRawWeight).sum

private def wordRawAggregate (leaves : List BK05WordRawLeaf) :
    Operator QubitSpace :=
  (leaves.map BK05WordRawLeaf.raw).sum

private theorem importRawLeaf_weight (leaf : BK05RawLeaf) :
    wordRawWeight (importRawLeaf leaf) = rawWeight leaf := by
  rw [wordRawWeight, rawWeight, importRawLeaf_raw]

/-- Importing a complete literal retry family preserves its total raw mass. -/
private theorem importRawLeaves_mass (leaves : List BK05RawLeaf) :
    wordRawMass (importRawLeaves leaves) = rawMass leaves := by
  induction leaves with
  | nil => simp [importRawLeaves, wordRawMass, rawMass]
  | cons leaf leaves ih =>
      change wordRawWeight (importRawLeaf leaf) +
          wordRawMass (importRawLeaves leaves) =
        rawWeight leaf + rawMass leaves
      rw [importRawLeaf_weight, ih]

/-- Importing a complete literal retry family preserves its full raw operator
aggregate. -/
private theorem importRawLeaves_aggregate (leaves : List BK05RawLeaf) :
    wordRawAggregate (importRawLeaves leaves) = rawAggregate leaves := by
  induction leaves with
  | nil => simp [importRawLeaves, wordRawAggregate, rawAggregate]
  | cons leaf leaves ih =>
      change (importRawLeaf leaf).raw + wordRawAggregate (importRawLeaves leaves) =
        leaf.raw + rawAggregate leaves
      rw [importRawLeaf_raw, ih]

private def stoppingStep
    (continuation : List Bool → ResourceLedger BK05ResourceToken →
      Operator QubitSpace → List BK05WordRawLeaf)
    (leaf : BK05WordRawLeaf) : List BK05WordRawLeaf :=
  match leaf.status with
  | .live => continuation leaf.history leaf.ledger leaf.raw
  | .stoppedPhaseExhausted => [leaf]
  | .stoppedTPairExhausted => [leaf]

/-- Continue only successful prefixes and retain each stopping leaf as a
singleton terminal outcome. -/
private def stoppingBind (leaves : List BK05WordRawLeaf)
    (continuation : List Bool → ResourceLedger BK05ResourceToken →
      Operator QubitSpace → List BK05WordRawLeaf) : List BK05WordRawLeaf :=
  leaves.flatMap (stoppingStep continuation)

private theorem stoppingStep_live
    (continuation : List Bool → ResourceLedger BK05ResourceToken →
      Operator QubitSpace → List BK05WordRawLeaf)
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) :
    stoppingStep continuation ⟨.live, history, ledger, raw⟩ =
      continuation history ledger raw :=
  rfl

private theorem stoppingStep_phaseExhausted
    (continuation : List Bool → ResourceLedger BK05ResourceToken →
      Operator QubitSpace → List BK05WordRawLeaf)
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) :
    stoppingStep continuation ⟨.stoppedPhaseExhausted, history, ledger, raw⟩ =
      [⟨.stoppedPhaseExhausted, history, ledger, raw⟩] :=
  rfl

private theorem stoppingStep_tPairExhausted
    (continuation : List Bool → ResourceLedger BK05ResourceToken →
      Operator QubitSpace → List BK05WordRawLeaf)
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) :
    stoppingStep continuation ⟨.stoppedTPairExhausted, history, ledger, raw⟩ =
      [⟨.stoppedTPairExhausted, history, ledger, raw⟩] :=
  rfl

private theorem stoppingBind_retains_phaseExhausted
    (leaves : List BK05WordRawLeaf)
    (continuation : List Bool → ResourceLedger BK05ResourceToken →
      Operator QubitSpace → List BK05WordRawLeaf)
    (leaf : BK05WordRawLeaf) (hmem : leaf ∈ leaves)
    (hstatus : leaf.status = .stoppedPhaseExhausted) :
    leaf ∈ stoppingBind leaves continuation := by
  refine List.mem_flatMap.mpr ⟨leaf, hmem, ?_⟩
  simp [stoppingStep, hstatus]

private theorem stoppingBind_retains_tPairExhausted
    (leaves : List BK05WordRawLeaf)
    (continuation : List Bool → ResourceLedger BK05ResourceToken →
      Operator QubitSpace → List BK05WordRawLeaf)
    (leaf : BK05WordRawLeaf) (hmem : leaf ∈ leaves)
    (hstatus : leaf.status = .stoppedTPairExhausted) :
    leaf ∈ stoppingBind leaves continuation := by
  refine List.mem_flatMap.mpr ⟨leaf, hmem, ?_⟩
  simp [stoppingStep, hstatus]

private def hPhaseTarget : BK05WordPolarity → ZMod 8
  | .normal => (1 : ZMod 8)
  | .inverse => -1

private def tPhaseTarget : BK05WordPolarity → ZMod 12
  | .normal => (1 : ZMod 12)
  | .inverse => -1

/-- Start a literal order-eight retry at residue zero from an arbitrary raw
prefix payload and import every returned terminal leaf. -/
private def runHPhaseFrom
    (h : DensityOperator QubitSpace) (sign : BK05WordPolarity) (blocks : Nat)
    (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
    (data : Operator QubitSpace) : List BK05WordRawLeaf :=
  importRawLeaves (hRetry h (hPhaseTarget sign) (8 * blocks) 0 ledger history data)

/-- Start a literal order-twelve retry at residue zero from an arbitrary raw
prefix payload and import every returned terminal leaf. -/
private def runTPhaseFrom
    (t : DensityOperator QubitSpace) (pairAttempts : Nat)
    (sign : BK05WordPolarity) (blocks : Nat)
    (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
    (data : Operator QubitSpace) : List BK05WordRawLeaf :=
  importRawLeaves
    (tRetry t pairAttempts (tPhaseTarget sign) (12 * blocks) 0 ledger history data)

private theorem runHPhaseFrom_fresh_eq_hActualRawTree
    (h : DensityOperator QubitSpace) (sign : BK05WordPolarity) (blocks : Nat)
    (rho : DensityOperator QubitSpace) :
    runHPhaseFrom h sign blocks 0 [] rho.toOperator =
      List.map importRawLeaf (hActualRawTree h (hPhaseTarget sign) blocks rho) :=
  rfl

private theorem runTPhaseFrom_fresh_eq_tActualRawTree
    (t : DensityOperator QubitSpace) (pairAttempts : Nat)
    (sign : BK05WordPolarity) (blocks : Nat) (rho : DensityOperator QubitSpace) :
    runTPhaseFrom t pairAttempts sign blocks 0 [] rho.toOperator =
      List.map importRawLeaf
        (tActualRawTree t pairAttempts (tPhaseTarget sign) blocks rho) :=
  rfl

private theorem phaseShiftOperator_add_full_turn
    (theta : Real) (k : Int) :
    OneQubitMagic.phaseShiftOperator
        (theta + (2 * Real.pi) * (k : Real)) =
      OneQubitMagic.phaseShiftOperator theta := by
  ext psi bit
  fin_cases bit
  · simp [OneQubitMagic.phaseShiftOperator_apply_zero]
  · change (OneQubitMagic.phaseShiftOperator
        (theta + (2 * Real.pi) * (k : Real)) psi) 1 =
      (OneQubitMagic.phaseShiftOperator theta psi) 1
    rw [OneQubitMagic.phaseShiftOperator_apply_one,
      OneQubitMagic.phaseShiftOperator_apply_one]
    rw [OneQubitMagic.phaseAmplitude_add,
      OneQubitMagic.phaseAmplitude_two_pi_mul_int]
    ring

private theorem phaseCycleTargetAction_eight_neg_one :
    phaseCycleTargetAction 8 (-1 : ZMod 8) =
      OneQubitMagic.phaseShiftOperator (Real.pi / 4) := by
  change phaseEightTargetAction (-1 : ZMod 8) = _
  rw [phaseEightTargetAction_eq]
  have hval : (-1 : ZMod 8).val = 7 := by norm_num
  rw [hval]
  have hangle : (-Real.pi / 4) * ((7 : Nat) : Real) =
      Real.pi / 4 + (2 * Real.pi) * ((-1 : Int) : Real) := by
    ring
  rw [hangle]
  exact phaseShiftOperator_add_full_turn (Real.pi / 4) (-1)

private theorem phaseCycleTargetAction_twelve_neg_one :
    phaseCycleTargetAction 12 (-1 : ZMod 12) =
      OneQubitMagic.phaseShiftOperator (Real.pi / 6) := by
  change phaseTwelveTargetAction (-1 : ZMod 12) = _
  rw [phaseTwelveTargetAction_eq]
  have hval : (-1 : ZMod 12).val = 11 := by norm_num
  rw [hval]
  have hangle : (-Real.pi / 6) * ((11 : Nat) : Real) =
      Real.pi / 6 + (2 * Real.pi) * ((-1 : Int) : Real) := by
    ring
  rw [hangle]
  exact phaseShiftOperator_add_full_turn (Real.pi / 6) (-1)

private def signedHLetter (theta : Real) :
    BK05WordPolarity → BK05SignedPhaseLetter theta
  | .normal => .positive .h
  | .inverse => .negative .h

private def signedKLetter (theta : Real) :
    BK05WordPolarity → BK05SignedPhaseLetter theta
  | .normal => .positive .k
  | .inverse => .negative .k

private noncomputable def signedHTransport :
    BK05WordPolarity → UnitaryTransport QubitSpace QubitSpace
  | .normal => hadamardTransport
  | .inverse => hadamardTransport

private noncomputable def signedKTransport :
    BK05WordPolarity → UnitaryTransport QubitSpace QubitSpace
  | .normal => phaseTransport
  | .inverse => phaseTransport.symm

private noncomputable def signedHRawLinear :
    BK05WordPolarity → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | .normal => hadamardTransport.conjOperatorLinearMap
  | .inverse => hadamardTransport.conjOperatorLinearMap

private noncomputable def signedKRawLinear :
    BK05WordPolarity → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | .normal => phaseTransport.conjOperatorLinearMap
  | .inverse => phaseTransport.symm.conjOperatorLinearMap

private theorem signedHTransport_apply_eq_eval
    (theta : Real) (sign : BK05WordPolarity) (psi : QubitSpace) :
    signedHTransport sign psi =
      Matrix.toEuclideanLin
        ((signedHLetter theta sign).eval theta :
          Matrix (Fin 2) (Fin 2) Complex) psi := by
  cases sign with
  | normal => exact (hadamardGate_apply psi).symm
  | inverse =>
      change hadamardTransport psi =
        Matrix.toEuclideanLin
          ((hadamardGate⁻¹ : UnitaryGate (Fin 2)) :
            Matrix (Fin 2) (Fin 2) Complex) psi
      rw [hadamardGate_inverse]
      exact (hadamardGate_apply psi).symm

private theorem signedKTransport_apply_eq_eval
    (theta : Real) (sign : BK05WordPolarity) (psi : QubitSpace) :
    signedKTransport sign psi =
      Matrix.toEuclideanLin
        ((signedKLetter theta sign).eval theta :
          Matrix (Fin 2) (Fin 2) Complex) psi := by
  cases sign with
  | normal => exact (phaseGate_apply psi).symm
  | inverse =>
      change phaseInverseOperator psi =
        Matrix.toEuclideanLin
          ((phaseGate⁻¹ : UnitaryGate (Fin 2)) :
            Matrix (Fin 2) (Fin 2) Complex) psi
      rw [phaseGate_inverse, phaseInverseGate_apply]

private theorem signedHTransport_operator_eq_eval
    (theta : Real) (sign : BK05WordPolarity) :
    (signedHTransport sign).toLinearEquiv.toLinearMap =
      Matrix.toEuclideanLin
        ((signedHLetter theta sign).eval theta :
          Matrix (Fin 2) (Fin 2) Complex) := by
  apply LinearMap.ext
  intro psi
  exact signedHTransport_apply_eq_eval theta sign psi

private theorem signedKTransport_operator_eq_eval
    (theta : Real) (sign : BK05WordPolarity) :
    (signedKTransport sign).toLinearEquiv.toLinearMap =
      Matrix.toEuclideanLin
        ((signedKLetter theta sign).eval theta :
          Matrix (Fin 2) (Fin 2) Complex) := by
  apply LinearMap.ext
  intro psi
  exact signedKTransport_apply_eq_eval theta sign psi

private theorem signedHRawLinear_apply
    (sign : BK05WordPolarity) (raw : Operator QubitSpace) :
    signedHRawLinear sign raw = (signedHTransport sign).conjOperator raw := by
  cases sign <;> rfl

private theorem signedKRawLinear_apply
    (sign : BK05WordPolarity) (raw : Operator QubitSpace) :
    signedKRawLinear sign raw = (signedKTransport sign).conjOperator raw := by
  cases sign <;> rfl

private theorem signedHRawLinear_positive
    (sign : BK05WordPolarity) (raw : Operator QubitSpace)
    (hraw : LinearMap.IsPositive raw) :
    LinearMap.IsPositive (signedHRawLinear sign raw) := by
  cases sign <;> simpa [signedHRawLinear] using
    hadamardTransport.isPositive_conjOperator hraw

private theorem signedKRawLinear_positive
    (sign : BK05WordPolarity) (raw : Operator QubitSpace)
    (hraw : LinearMap.IsPositive raw) :
    LinearMap.IsPositive (signedKRawLinear sign raw) := by
  cases sign with
  | normal =>
      simpa [signedKRawLinear] using phaseTransport.isPositive_conjOperator hraw
  | inverse =>
      simpa [signedKRawLinear] using phaseTransport.symm.isPositive_conjOperator hraw

private theorem signedHRawLinear_trace
    (sign : BK05WordPolarity) (raw : Operator QubitSpace) :
    LinearMap.trace Complex QubitSpace (signedHRawLinear sign raw) =
      LinearMap.trace Complex QubitSpace raw := by
  cases sign <;> simpa [signedHRawLinear] using
    hadamardTransport.trace_conjOperator raw

private theorem signedKRawLinear_trace
    (sign : BK05WordPolarity) (raw : Operator QubitSpace) :
    LinearMap.trace Complex QubitSpace (signedKRawLinear sign raw) =
      LinearMap.trace Complex QubitSpace raw := by
  cases sign with
  | normal =>
      simpa [signedKRawLinear] using phaseTransport.trace_conjOperator raw
  | inverse =>
      simpa [signedKRawLinear] using phaseTransport.symm.trace_conjOperator raw

private theorem signedHRawLinear_mass
    (sign : BK05WordPolarity) (raw : Operator QubitSpace) :
    (LinearMap.trace Complex QubitSpace (signedHRawLinear sign raw)).re =
      (LinearMap.trace Complex QubitSpace raw).re := by
  rw [signedHRawLinear_trace]

private theorem signedKRawLinear_mass
    (sign : BK05WordPolarity) (raw : Operator QubitSpace) :
    (LinearMap.trace Complex QubitSpace (signedKRawLinear sign raw)).re =
      (LinearMap.trace Complex QubitSpace raw).re := by
  rw [signedKRawLinear_trace]

private noncomputable def deterministicLiveLeaf
    (U : UnitaryTransport QubitSpace QubitSpace)
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) : BK05WordRawLeaf :=
  ⟨.live, history, ledger, U.conjOperator raw⟩

private noncomputable def deterministicContinuation
    (U : UnitaryTransport QubitSpace QubitSpace) :
    List Bool → ResourceLedger BK05ResourceToken → Operator QubitSpace →
      List BK05WordRawLeaf :=
  fun history ledger raw => [deterministicLiveLeaf U history ledger raw]

private noncomputable def runDeterministic
    (U : UnitaryTransport QubitSpace QubitSpace)
    (leaves : List BK05WordRawLeaf) : List BK05WordRawLeaf :=
  stoppingBind leaves (deterministicContinuation U)

private theorem deterministicLiveLeaf_status
    (U : UnitaryTransport QubitSpace QubitSpace)
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) :
    (deterministicLiveLeaf U history ledger raw).status = .live :=
  rfl

private theorem deterministicLiveLeaf_history
    (U : UnitaryTransport QubitSpace QubitSpace)
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) :
    (deterministicLiveLeaf U history ledger raw).history = history :=
  rfl

private theorem deterministicLiveLeaf_ledger
    (U : UnitaryTransport QubitSpace QubitSpace)
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) :
    (deterministicLiveLeaf U history ledger raw).ledger = ledger :=
  rfl

private theorem deterministicLiveLeaf_raw
    (U : UnitaryTransport QubitSpace QubitSpace)
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) :
    (deterministicLiveLeaf U history ledger raw).raw = U.conjOperator raw :=
  rfl

private theorem deterministicLiveLeaf_positive
    (U : UnitaryTransport QubitSpace QubitSpace)
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) (hraw : LinearMap.IsPositive raw) :
    LinearMap.IsPositive (deterministicLiveLeaf U history ledger raw).raw := by
  exact U.isPositive_conjOperator hraw

private theorem deterministicLiveLeaf_trace
    (U : UnitaryTransport QubitSpace QubitSpace)
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) :
    LinearMap.trace Complex QubitSpace (deterministicLiveLeaf U history ledger raw).raw =
      LinearMap.trace Complex QubitSpace raw := by
  exact U.trace_conjOperator raw

private theorem deterministicContinuation_mass
    (U : UnitaryTransport QubitSpace QubitSpace)
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) :
    wordRawMass (deterministicContinuation U history ledger raw) =
      (LinearMap.trace Complex QubitSpace raw).re := by
  simp only [deterministicContinuation, deterministicLiveLeaf, wordRawMass,
    wordRawWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  change (LinearMap.trace Complex QubitSpace (U.conjOperator raw)).re = _
  rw [U.trace_conjOperator]

private theorem runDeterministic_live
    (U : UnitaryTransport QubitSpace QubitSpace)
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) :
    runDeterministic U [⟨.live, history, ledger, raw⟩] =
      [deterministicLiveLeaf U history ledger raw] :=
  rfl

private theorem runDeterministic_phaseExhausted
    (U : UnitaryTransport QubitSpace QubitSpace)
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) :
    runDeterministic U [⟨.stoppedPhaseExhausted, history, ledger, raw⟩] =
      [⟨.stoppedPhaseExhausted, history, ledger, raw⟩] :=
  rfl

private theorem runDeterministic_tPairExhausted
    (U : UnitaryTransport QubitSpace QubitSpace)
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) :
    runDeterministic U [⟨.stoppedTPairExhausted, history, ledger, raw⟩] =
      [⟨.stoppedTPairExhausted, history, ledger, raw⟩] :=
  rfl

/- Later list execution must run the tail/right factor first, then the
head/left factor, because tagged-list evaluation is `head * tail`. -/

/- Task 5d3: ideal phase-branch operator semantics. -/

private noncomputable def oneShotSignedAngle (theta : Real) (coin : Bool) : Real :=
  if coin then theta else -theta

private theorem oneShotAttemptAngle_eq_signed
    (theta : Real) (coin : Bool) :
    oneShotAttemptAngle theta coin = oneShotSignedAngle theta coin := by
  cases coin <;> rfl

private theorem rankOne_global_phase_local
    (z : Complex) (v : QubitSpace) (hz : star z * z = 1) :
    (InnerProductSpace.rankOne Complex (z • v) (z • v)).toLinearMap =
      (InnerProductSpace.rankOne Complex v v).toLinearMap := by
  rw [rankOne_smul_self_local, hz, one_smul]

/- The public joint-instrument sandwich specialized to the literal pure
injection input.  This deliberately reconstructs the local branch rather
than appealing to the private convenience theorem in `PhaseInjection`. -/
private theorem injectionInput_norm_local (psi : QubitSpace) (theta : Real)
    (hpsi : ‖psi‖ = 1) : ‖injectionInput psi theta‖ = 1 := by
  change ‖TwoQubit.tensorRegisterTransport.toLinearIsometryEquiv
    (psi ⊗ₜ[Complex] OneQubitMagic.phaseState theta)‖ = 1
  rw [TwoQubit.tensorRegisterTransport.toLinearIsometryEquiv.norm_map,
    TensorProduct.norm_tmul, hpsi, OneQubitMagic.phaseState_norm]
  norm_num

private theorem phaseBranchRaw_ideal_instrument_rankOne
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1) (coin : Bool) :
    zzMeasurement.instrument.branchOperator (observedRetrySyndrome coin)
      (injectionInputDensity psi theta hpsi).toOperator =
      (InnerProductSpace.rankOne Complex
        (jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
          (observedRetrySyndrome coin) (injectionInput psi theta))
        (jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
          (observedRetrySyndrome coin) (injectionInput psi theta))).toLinearMap := by
  have hinjection :
      (injectionInputDensity psi theta hpsi).toOperator =
        (InnerProductSpace.rankOne Complex (injectionInput psi theta)
          (injectionInput psi theta)).toLinearMap := by
    unfold injectionInputDensity
    rw [DensityOperator.pureOfNonzero_toOperator,
      inner_self_eq_norm_sq_to_K, injectionInput_norm_local psi theta hpsi]
    norm_num
  change (jointStabilizerInstrument zzMeasurement.checks zzMeasurement.commute).branchOperator
    _ _ = _
  rw [jointStabilizerInstrument_branchOperator, hinjection]
  let projector := jointStabilizerProjector zzMeasurement.checks
    zzMeasurement.commute (observedRetrySyndrome coin)
  have hne : injectionInput psi theta ≠ 0 := by
    intro hzero
    have hnorm := injectionInput_norm_local psi theta hpsi
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have hcomp := DensityOperator.comp_pureOfNonzero_adjoint projector
    (injectionInput psi theta) hne
  rw [DensityOperator.pureOfNonzero_toOperator,
    inner_self_eq_norm_sq_to_K, injectionInput_norm_local psi theta hpsi] at hcomp
  norm_num at hcomp
  dsimp [projector] at hcomp
  rw [jointStabilizerProjector_adjoint] at hcomp
  simpa [Module.End.mul_eq_comp, LinearMap.comp_assoc] using hcomp

private theorem phaseBranchRaw_ideal_pure_branch
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1) (coin : Bool) :
    phaseBranchRaw (phaseStateDensity theta).toOperator
      (sourceInputDensity psi hpsi).toOperator coin =
      (1 / 2 : Complex) •
        (InnerProductSpace.rankOne Complex
          (oneShotAttempt psi theta hpsi coin)
          (oneShotAttempt psi theta hpsi coin)).toLinearMap := by
  have hinjection :
      injectedInputRaw (sourceInputDensity psi hpsi).toOperator
          (phaseStateDensity theta).toOperator =
        (injectionInputDensity psi theta hpsi).toOperator := by
    change (QuantumChannel.unitaryConj TwoQubit.tensorRegisterTransport)
      (DensityOperator.tensorDensity (sourceInputDensity psi hpsi)
        (phaseStateDensity theta)).toOperator = _
    exact congrArg DensityOperator.toOperator
      (phaseStateResourceUse_run_eq_injectionInputDensity psi theta hpsi)
  cases coin with
  | false =>
      have hweight : 0 < TwoQubit.zzOddWeight (injectionInput psi theta) := by
        rw [← oneShotWeight_negative, (oneShotCorrect psi theta hpsi).2.1]
        norm_num
      have hbranch :
          zzMeasurement.instrument.branchOperator (observedRetrySyndrome false)
            (injectionInputDensity psi theta hpsi).toOperator =
            (1 / 2 : Complex) •
              (TwoQubit.zzOddBranchDensity (injectionInput psi theta) hweight).toOperator := by
        rw [phaseBranchRaw_ideal_instrument_rankOne]
        change (InnerProductSpace.rankOne Complex
            (jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
              negativeSyndrome (injectionInput psi theta))
            (jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
              negativeSyndrome (injectionInput psi theta))).toLinearMap = _
        rw [jointProjector_negative, TwoQubit.zzOddBranchDensity_toOperator,
          ← TwoQubit.zzOddBranchState_rescale (injectionInput psi theta) hweight,
          rankOne_smul_self_local]
        have hsquare : Real.sqrt (TwoQubit.zzOddWeight (injectionInput psi theta)) *
            Real.sqrt (TwoQubit.zzOddWeight (injectionInput psi theta)) =
              TwoQubit.zzOddWeight (injectionInput psi theta) := by
          rw [← pow_two, Real.sq_sqrt]
          rw [← oneShotWeight_negative, (oneShotCorrect psi theta hpsi).2.1]
          norm_num
        have hscalar :
            star (Real.sqrt (TwoQubit.zzOddWeight (injectionInput psi theta)) : Complex) *
              (Real.sqrt (TwoQubit.zzOddWeight (injectionInput psi theta)) : Complex) =
              (1 / 2 : Complex) := by
          calc
            star (Real.sqrt (TwoQubit.zzOddWeight (injectionInput psi theta)) : Complex) *
                (Real.sqrt (TwoQubit.zzOddWeight (injectionInput psi theta)) : Complex) =
                (Real.sqrt (TwoQubit.zzOddWeight (injectionInput psi theta)) *
                  Real.sqrt (TwoQubit.zzOddWeight (injectionInput psi theta)) : Real) := by
                    rw [Complex.star_def, Complex.conj_ofReal]
                    norm_num
            _ = (TwoQubit.zzOddWeight (injectionInput psi theta) : Complex) := by
                    exact_mod_cast hsquare
            _ = (1 / 2 : Complex) := by
                    rw [← oneShotWeight_negative, (oneShotCorrect psi theta hpsi).2.1]
                    norm_num
        rw [hscalar]
      have hpost :
          oneShotPostprocess
              (TwoQubit.zzOddBranchDensity (injectionInput psi theta) hweight).toOperator =
            (TwoQubit.zzOddBranchFirstDensity (injectionInput psi theta) hweight).toOperator := by
        rw [← QuantumChannel.mapDensity_toOperator, oneShotPostprocess_oddBranch]
      have hfirst :
          (TwoQubit.zzOddBranchFirstDensity (injectionInput psi theta) hweight).toOperator =
            (InnerProductSpace.rankOne Complex
              (TwoQubit.zzOddBranchFirstQubit (injectionInput psi theta) hweight)
              (TwoQubit.zzOddBranchFirstQubit (injectionInput psi theta) hweight)).toLinearMap := by
        unfold TwoQubit.zzOddBranchFirstDensity
        rw [DensityOperator.pureOfNonzero_toOperator,
          inner_self_eq_norm_sq_to_K,
          TwoQubit.zzOddBranchFirstQubit_norm]
        norm_num
      have hattempt : oneShotAttempt psi theta hpsi false =
          TwoQubit.zzOddBranchFirstQubit (injectionInput psi theta) hweight := by
        simp [oneShotAttempt, negativeBranchOutput]
      calc
        phaseBranchRaw (phaseStateDensity theta).toOperator
            (sourceInputDensity psi hpsi).toOperator false =
            oneShotPostprocess
              (zzMeasurement.instrument.branchOperator (observedRetrySyndrome false)
                (injectionInputDensity psi theta hpsi).toOperator) := by
              rw [phaseBranchRaw, hinjection]
        _ = oneShotPostprocess ((1 / 2 : Complex) •
              (TwoQubit.zzOddBranchDensity (injectionInput psi theta) hweight).toOperator) := by
              rw [hbranch]
        _ = (1 / 2 : Complex) • oneShotPostprocess
              (TwoQubit.zzOddBranchDensity (injectionInput psi theta) hweight).toOperator := by
              rw [map_smul]
        _ = (1 / 2 : Complex) •
              (InnerProductSpace.rankOne Complex
                (oneShotAttempt psi theta hpsi false)
                (oneShotAttempt psi theta hpsi false)).toLinearMap := by
              rw [hpost, hfirst, hattempt]
  | true =>
      have hweight : 0 < TwoQubit.zzEvenWeight (injectionInput psi theta) := by
        rw [← oneShotWeight_positive, (oneShotCorrect psi theta hpsi).1]
        norm_num
      have hbranch :
          zzMeasurement.instrument.branchOperator (observedRetrySyndrome true)
            (injectionInputDensity psi theta hpsi).toOperator =
            (1 / 2 : Complex) •
              (TwoQubit.zzEvenBranchDensity (injectionInput psi theta) hweight).toOperator := by
        rw [phaseBranchRaw_ideal_instrument_rankOne]
        change (InnerProductSpace.rankOne Complex
            (jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
              positiveSyndrome (injectionInput psi theta))
            (jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
              positiveSyndrome (injectionInput psi theta))).toLinearMap = _
        rw [jointProjector_positive, TwoQubit.zzEvenBranchDensity_toOperator,
          ← TwoQubit.zzEvenBranchState_rescale (injectionInput psi theta) hweight,
          rankOne_smul_self_local]
        have hsquare : Real.sqrt (TwoQubit.zzEvenWeight (injectionInput psi theta)) *
            Real.sqrt (TwoQubit.zzEvenWeight (injectionInput psi theta)) =
              TwoQubit.zzEvenWeight (injectionInput psi theta) := by
          rw [← pow_two, Real.sq_sqrt]
          rw [← oneShotWeight_positive, (oneShotCorrect psi theta hpsi).1]
          norm_num
        have hscalar :
            star (Real.sqrt (TwoQubit.zzEvenWeight (injectionInput psi theta)) : Complex) *
              (Real.sqrt (TwoQubit.zzEvenWeight (injectionInput psi theta)) : Complex) =
              (1 / 2 : Complex) := by
          calc
            star (Real.sqrt (TwoQubit.zzEvenWeight (injectionInput psi theta)) : Complex) *
                (Real.sqrt (TwoQubit.zzEvenWeight (injectionInput psi theta)) : Complex) =
                (Real.sqrt (TwoQubit.zzEvenWeight (injectionInput psi theta)) *
                  Real.sqrt (TwoQubit.zzEvenWeight (injectionInput psi theta)) : Real) := by
                    rw [Complex.star_def, Complex.conj_ofReal]
                    norm_num
            _ = (TwoQubit.zzEvenWeight (injectionInput psi theta) : Complex) := by
                    exact_mod_cast hsquare
            _ = (1 / 2 : Complex) := by
                    rw [← oneShotWeight_positive, (oneShotCorrect psi theta hpsi).1]
                    norm_num
        rw [hscalar]
      have hpost :
          oneShotPostprocess
              (TwoQubit.zzEvenBranchDensity (injectionInput psi theta) hweight).toOperator =
            (TwoQubit.zzEvenBranchFirstDensity (injectionInput psi theta) hweight).toOperator := by
        rw [← QuantumChannel.mapDensity_toOperator, oneShotPostprocess_evenBranch]
      have hfirst :
          (TwoQubit.zzEvenBranchFirstDensity (injectionInput psi theta) hweight).toOperator =
            (InnerProductSpace.rankOne Complex
              (TwoQubit.zzEvenBranchFirstQubit (injectionInput psi theta) hweight)
              (TwoQubit.zzEvenBranchFirstQubit (injectionInput psi theta) hweight)).toLinearMap := by
        unfold TwoQubit.zzEvenBranchFirstDensity
        rw [DensityOperator.pureOfNonzero_toOperator,
          inner_self_eq_norm_sq_to_K,
          TwoQubit.zzEvenBranchFirstQubit_norm]
        norm_num
      have hattempt : oneShotAttempt psi theta hpsi true =
          TwoQubit.zzEvenBranchFirstQubit (injectionInput psi theta) hweight := by
        simp [oneShotAttempt, positiveBranchOutput]
      calc
        phaseBranchRaw (phaseStateDensity theta).toOperator
            (sourceInputDensity psi hpsi).toOperator true =
            oneShotPostprocess
              (zzMeasurement.instrument.branchOperator (observedRetrySyndrome true)
                (injectionInputDensity psi theta hpsi).toOperator) := by
              rw [phaseBranchRaw, hinjection]
        _ = oneShotPostprocess ((1 / 2 : Complex) •
              (TwoQubit.zzEvenBranchDensity (injectionInput psi theta) hweight).toOperator) := by
              rw [hbranch]
        _ = (1 / 2 : Complex) • oneShotPostprocess
              (TwoQubit.zzEvenBranchDensity (injectionInput psi theta) hweight).toOperator := by
              rw [map_smul]
        _ = (1 / 2 : Complex) •
              (InnerProductSpace.rankOne Complex
                (oneShotAttempt psi theta hpsi true)
                (oneShotAttempt psi theta hpsi true)).toLinearMap := by
              rw [hpost, hfirst, hattempt]

private theorem oneShotAttemptGlobalPhase_unit_local
    (theta : Real) (coin : Bool) :
    star (oneShotAttemptGlobalPhase theta coin) * oneShotAttemptGlobalPhase theta coin = 1 := by
  cases coin with
  | false =>
      change star (OneQubitMagic.phaseAmplitude theta) *
        OneQubitMagic.phaseAmplitude theta = 1
      rw [mul_comm, OneQubitMagic.phaseAmplitude_mul_conj]
  | true => norm_num [oneShotAttemptGlobalPhase, observedRetryOutcome, sourceOutcomeGlobalPhase]

/- An ideal phase-state use has the exact subnormalised branch action, not
merely its trace.  The vector global phase in the odd branch cancels at the
rank-one operator level. -/
private theorem phaseBranchRaw_ideal_pure_action
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1) (coin : Bool) :
    phaseBranchRaw (phaseStateDensity theta).toOperator
      (sourceInputDensity psi hpsi).toOperator coin =
      (1 / 2 : Complex) •
        (OneQubitMagic.phaseShiftTransport (oneShotSignedAngle theta coin)).conjOperator
          ((sourceInputDensity psi hpsi).toOperator) := by
  rw [phaseBranchRaw_ideal_pure_branch, oneShotAttempt_action,
    rankOne_global_phase_local _ _ (oneShotAttemptGlobalPhase_unit_local theta coin),
    sourceInputDensity_toOperator_local,
    QuditSubsystem.conjOperator_rankOne,
    oneShotAttemptAngle_eq_signed]
  rfl

private theorem phaseBranchRaw_ideal_rankOne_action
    (theta : Real) (u : QubitSpace) (coin : Bool) :
    phaseBranchRaw (phaseStateDensity theta).toOperator
      (InnerProductSpace.rankOne Complex u u).toLinearMap coin =
      (1 / 2 : Complex) •
        (OneQubitMagic.phaseShiftTransport (oneShotSignedAngle theta coin)).conjOperator
          ((InnerProductSpace.rankOne Complex u u).toLinearMap) := by
  by_cases hu : u = 0
  · subst u
    have hrankzero :
        (InnerProductSpace.rankOne Complex (0 : QubitSpace) (0 : QubitSpace)).toLinearMap =
          0 := by
      exact congrArg ContinuousLinearMap.toLinearMap
        (InnerProductSpace.rankOne_eq_zero.mpr (Or.inl rfl))
    rw [hrankzero, phaseBranchRaw_zero]
    change 0 = (1 / 2 : Complex) •
      (OneQubitMagic.phaseShiftTransport (oneShotSignedAngle theta coin)).conjOperator 0
    rw [show (OneQubitMagic.phaseShiftTransport (oneShotSignedAngle theta coin)).conjOperator 0 =
      0 by exact (OneQubitMagic.phaseShiftTransport
        (oneShotSignedAngle theta coin)).conjOperatorLinearMap.map_zero]
    simp
  · let psi : QubitSpace := ((‖u‖ : Complex)⁻¹) • u
    have hnorm_ne : (‖u‖ : Complex) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.mpr hu)
    have hpsi : ‖psi‖ = 1 := by
      dsimp [psi]
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg u)]
      field_simp
    have hu_eq : u = (‖u‖ : Complex) • psi := by
      calc
        u = (1 : Complex) • u := (one_smul Complex u).symm
        _ = ((‖u‖ : Complex) * (‖u‖ : Complex)⁻¹) • u := by
          congr 1
          field_simp
        _ = (‖u‖ : Complex) • (((‖u‖ : Complex)⁻¹) • u) := by
          rw [smul_smul]
        _ = (‖u‖ : Complex) • psi := rfl
    have hrank : (InnerProductSpace.rankOne Complex u u).toLinearMap =
        (‖u‖ ^ 2 : Complex) • (sourceInputDensity psi hpsi).toOperator := by
      calc
        (InnerProductSpace.rankOne Complex u u).toLinearMap =
            (InnerProductSpace.rankOne Complex
              ((‖u‖ : Complex) • psi) ((‖u‖ : Complex) • psi)).toLinearMap := by
                exact congrArg
                  (fun v : QubitSpace =>
                    (InnerProductSpace.rankOne Complex v v).toLinearMap) hu_eq
        _ = (star (‖u‖ : Complex) * (‖u‖ : Complex)) •
            (InnerProductSpace.rankOne Complex psi psi).toLinearMap :=
              rankOne_smul_self_local (‖u‖ : Complex) psi
        _ = (‖u‖ ^ 2 : Complex) •
            (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
              norm_num [pow_two]
        _ = (‖u‖ ^ 2 : Complex) • (sourceInputDensity psi hpsi).toOperator := by
              rw [sourceInputDensity_toOperator_local]
    calc
      phaseBranchRaw (phaseStateDensity theta).toOperator
          (InnerProductSpace.rankOne Complex u u).toLinearMap coin =
          phaseBranchRaw (phaseStateDensity theta).toOperator
            ((‖u‖ ^ 2 : Complex) • (sourceInputDensity psi hpsi).toOperator) coin := by
              rw [hrank]
      _ = (‖u‖ ^ 2 : Complex) •
          phaseBranchRaw (phaseStateDensity theta).toOperator
            (sourceInputDensity psi hpsi).toOperator coin := by
              rw [phaseBranchRaw_smul]
      _ = (‖u‖ ^ 2 : Complex) • ((1 / 2 : Complex) •
          (OneQubitMagic.phaseShiftTransport (oneShotSignedAngle theta coin)).conjOperator
            ((sourceInputDensity psi hpsi).toOperator)) := by
              rw [phaseBranchRaw_ideal_pure_action]
      _ = (1 / 2 : Complex) •
          (OneQubitMagic.phaseShiftTransport (oneShotSignedAngle theta coin)).conjOperator
            ((‖u‖ ^ 2 : Complex) • (sourceInputDensity psi hpsi).toOperator) := by
              have hmap :
                  (OneQubitMagic.phaseShiftTransport (oneShotSignedAngle theta coin)).conjOperator
                      ((‖u‖ ^ 2 : Complex) • (sourceInputDensity psi hpsi).toOperator) =
                    (‖u‖ ^ 2 : Complex) •
                      (OneQubitMagic.phaseShiftTransport (oneShotSignedAngle theta coin)).conjOperator
                        (sourceInputDensity psi hpsi).toOperator := by
                  exact (OneQubitMagic.phaseShiftTransport
                    (oneShotSignedAngle theta coin)).conjOperatorLinearMap.map_smul _ _
              rw [hmap]
              simp only [smul_smul]
              ring
      _ = (1 / 2 : Complex) •
          (OneQubitMagic.phaseShiftTransport (oneShotSignedAngle theta coin)).conjOperator
            ((InnerProductSpace.rankOne Complex u u).toLinearMap) := by
              rw [hrank]

private theorem phaseBranchRaw_ideal_action
    (theta : Real) (data : Operator QubitSpace)
    (hdata : LinearMap.IsPositive data) (coin : Bool) :
    phaseBranchRaw (phaseStateDensity theta).toOperator data coin =
      (1 / 2 : Complex) •
        (OneQubitMagic.phaseShiftTransport (oneShotSignedAngle theta coin)).conjOperator data := by
  have hpositive : (LinearMap.toContinuousLinearMap data).IsPositive :=
    (LinearMap.isPositive_toContinuousLinearMap_iff data).2 hdata
  rcases (ContinuousLinearMap.isPositive_iff_eq_sum_rankOne).1 hpositive with
    ⟨m, u, hu⟩
  have hdata_sum : data = ∑ i : Fin m,
      (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap := by
    simpa using congrArg ContinuousLinearMap.toLinearMap hu
  rw [hdata_sum]
  change phaseBranchRawLinear (phaseStateDensity theta).toOperator coin
      (∑ i : Fin m, (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap) =
    (1 / 2 : Complex) •
      (OneQubitMagic.phaseShiftTransport (oneShotSignedAngle theta coin)).conjOperatorLinearMap
          (∑ i : Fin m, (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap)
  have hbranch_sum : phaseBranchRawLinear (phaseStateDensity theta).toOperator coin
      (∑ i : Fin m, (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap) =
        ∑ i : Fin m, phaseBranchRawLinear (phaseStateDensity theta).toOperator coin
          (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap := by
        rw [map_sum]
  have htransport_sum :
      (OneQubitMagic.phaseShiftTransport (oneShotSignedAngle theta coin)).conjOperatorLinearMap
          (∑ i : Fin m, (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap) =
        ∑ i : Fin m,
          (OneQubitMagic.phaseShiftTransport (oneShotSignedAngle theta coin)).conjOperatorLinearMap
            (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap := by
        rw [map_sum]
  rw [hbranch_sum, htransport_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact phaseBranchRaw_ideal_rankOne_action theta (u i) coin

/- Task 5d3b: ideal H retry history semantics. -/

private theorem phaseShiftTransport_conjOperator_add
    (alpha beta : Real) (data : Operator QubitSpace) :
    (OneQubitMagic.phaseShiftTransport beta).conjOperator
        ((OneQubitMagic.phaseShiftTransport alpha).conjOperator data) =
      (OneQubitMagic.phaseShiftTransport (alpha + beta)).conjOperator data := by
  unfold UnitaryTransport.conjOperator
  apply LinearMap.ext
  intro psi
  change OneQubitMagic.phaseShiftOperator beta
      (OneQubitMagic.phaseShiftOperator alpha
        (data (OneQubitMagic.phaseShiftOperator (-alpha)
          (OneQubitMagic.phaseShiftOperator (-beta) psi)))) =
    OneQubitMagic.phaseShiftOperator (alpha + beta)
      (data (OneQubitMagic.phaseShiftOperator (-(alpha + beta)) psi))
  have houter (x : QubitSpace) :
      OneQubitMagic.phaseShiftOperator beta
          (OneQubitMagic.phaseShiftOperator alpha x) =
        OneQubitMagic.phaseShiftOperator (alpha + beta) x := by
    rw [← Module.End.mul_apply, OneQubitMagic.phaseShiftOperator_add, add_comm]
  have hinner (x : QubitSpace) :
      OneQubitMagic.phaseShiftOperator (-alpha)
          (OneQubitMagic.phaseShiftOperator (-beta) x) =
        OneQubitMagic.phaseShiftOperator (-(alpha + beta)) x := by
    rw [← Module.End.mul_apply, OneQubitMagic.phaseShiftOperator_add]
    congr 1
    ring
  rw [houter, hinner]

private noncomputable def hIdealHistoryRaw : List Bool →
    Operator QubitSpace → Operator QubitSpace
  | [], data => data
  | coin :: coins, data =>
      hIdealHistoryRaw coins (hStepRaw hMagicState coin data)

private theorem hIdealHistoryRaw_action
    (coins : List Bool) (data : Operator QubitSpace)
    (hdata : LinearMap.IsPositive data) :
    hIdealHistoryRaw coins data =
      (1 / 2 : Complex) ^ coins.length •
        (OneQubitMagic.phaseShiftTransport
          (phaseInjectionHistoryAngle (-Real.pi / 4) coins)).conjOperator data := by
  induction coins generalizing data with
  | nil =>
      simp only [hIdealHistoryRaw, List.length_nil, pow_zero, one_smul,
        phaseInjectionHistoryAngle]
      apply LinearMap.ext
      intro psi
      change data psi = OneQubitMagic.phaseShiftOperator 0
          (data (OneQubitMagic.phaseShiftOperator (-0) psi))
      rw [OneQubitMagic.phaseShiftOperator_zero]
      simp
  | cons coin coins ih =>
      rw [hIdealHistoryRaw, ih (hStepRaw hMagicState coin data)
        (hStepRaw_positive hMagicState coin data hdata)]
      rw [hMagicStepRaw_eq_phaseBranch,
        phaseBranchRaw_ideal_action (-Real.pi / 4) data hdata coin]
      have hmap :
          (OneQubitMagic.phaseShiftTransport
            (phaseInjectionHistoryAngle (-Real.pi / 4) coins)).conjOperator
              ((1 / 2 : Complex) •
                (OneQubitMagic.phaseShiftTransport
                  (oneShotSignedAngle (-Real.pi / 4) coin)).conjOperator data) =
            (1 / 2 : Complex) •
              (OneQubitMagic.phaseShiftTransport
                (phaseInjectionHistoryAngle (-Real.pi / 4) coins)).conjOperator
                  ((OneQubitMagic.phaseShiftTransport
                    (oneShotSignedAngle (-Real.pi / 4) coin)).conjOperator data) := by
        exact (OneQubitMagic.phaseShiftTransport
          (phaseInjectionHistoryAngle (-Real.pi / 4) coins)).conjOperatorLinearMap.map_smul _ _
      rw [hmap]
      rw [phaseShiftTransport_conjOperator_add]
      rw [show oneShotSignedAngle (-Real.pi / 4) coin =
          oneShotAttemptAngle (-Real.pi / 4) coin by
        exact (oneShotAttemptAngle_eq_signed (-Real.pi / 4) coin).symm]
      simp [phaseInjectionHistoryAngle, pow_succ, smul_smul]

private theorem hRetry_targetHit_history {q : Nat} (target : ZMod q) (remaining : Nat) :
    ∀ (position : ZMod q) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace) (leaf : BK05RawLeaf),
      leaf ∈ hRetry hMagicState target remaining position ledger history data →
      leaf.kind = .targetHit →
      ∃ coins : List Bool, leaf.history = coins.reverse ++ history ∧
        PhaseRetry.endpoint position coins = target := by
  induction remaining with
  | zero =>
      intro position ledger history data leaf hmem hkind
      by_cases htarget : position = target
      · simp [hRetry, htarget] at hmem
        subst leaf
        refine ⟨[], ?_, ?_⟩
        · simp
        · simpa [PhaseRetry.endpoint] using htarget
      · simp [hRetry, htarget] at hmem
        subst leaf
        cases hkind
  | succ remaining ih =>
      intro position ledger history data leaf hmem hkind
      by_cases htarget : position = target
      · simp [hRetry, htarget] at hmem
        subst leaf
        refine ⟨[], ?_, ?_⟩
        · simp
        · simpa [PhaseRetry.endpoint] using htarget
      · rw [hRetry, if_neg htarget] at hmem
        rcases List.mem_append.mp hmem with htrue | hfalse
        · rcases ih (position + 1) (ledger + ({.h} : ResourceLedger BK05ResourceToken))
              (true :: history) (hStepRaw hMagicState true data) leaf htrue hkind with
              ⟨coins, hhistory, hendpoint⟩
          refine ⟨true :: coins, ?_, ?_⟩
          · calc
              leaf.history = coins.reverse ++ true :: history := hhistory
              _ = (true :: coins).reverse ++ history := by
                simp [List.reverse_cons, List.append_assoc]
          · simpa [PhaseRetry.endpoint, PhaseRetry.signedIncrement] using hendpoint
        · rcases ih (position - 1) (ledger + ({.h} : ResourceLedger BK05ResourceToken))
              (false :: history) (hStepRaw hMagicState false data) leaf hfalse hkind with
              ⟨coins, hhistory, hendpoint⟩
          refine ⟨false :: coins, ?_, ?_⟩
          · calc
              leaf.history = coins.reverse ++ false :: history := hhistory
              _ = (false :: coins).reverse ++ history := by
                simp [List.reverse_cons, List.append_assoc]
          · simpa [PhaseRetry.endpoint, PhaseRetry.signedIncrement, sub_eq_add_neg] using
              hendpoint

private theorem hRetry_targetHit_history_root {q : Nat} (target : ZMod q)
    (remaining : Nat) (data : Operator QubitSpace) (leaf : BK05RawLeaf)
    (hmem : leaf ∈ hRetry hMagicState target remaining 0 0 [] data)
    (hkind : leaf.kind = .targetHit) :
    PhaseRetry.endpoint 0 leaf.history.reverse = target := by
  rcases hRetry_targetHit_history target remaining 0 0 [] data leaf hmem hkind with
    ⟨coins, hhistory, hendpoint⟩
  have hhistory' : leaf.history = coins.reverse := by
    simpa using hhistory
  rw [hhistory', List.reverse_reverse]
  exact hendpoint

/- Task 5d3c: ideal H target aggregate semantics. -/

private def rawAggregateOfKind (kind : BK05RawLeafKind)
    (leaves : List BK05RawLeaf) : Operator QubitSpace :=
  let retained := leaves.filter fun leaf => leaf.kind == kind
  rawAggregate retained

private def hTargetHitCoeff (target : ZMod 8) : Nat → ZMod 8 → Real
  | 0, position => if position = target then 1 else 0
  | remaining + 1, position =>
      if position = target then 1 else
        (hTargetHitCoeff target remaining (position + 1) +
          hTargetHitCoeff target remaining (position - 1)) / 2

private noncomputable def phaseCycleTargetChannel
    (q : Nat) (target : ZMod q) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace :=
  (OneQubitMagic.phaseShiftTransport
    (phaseCycleAngle q * target.val)).conjOperatorLinearMap

private theorem rawAggregateOfKind_append (kind : BK05RawLeafKind)
    (left right : List BK05RawLeaf) :
    rawAggregateOfKind kind (left ++ right) =
      rawAggregateOfKind kind left + rawAggregateOfKind kind right := by
  simp [rawAggregateOfKind, rawAggregate]

private theorem phaseShiftTransport_conjOperator_eq_of_operator_eq
    (alpha beta : Real) (data : Operator QubitSpace)
    (hoperator : OneQubitMagic.phaseShiftOperator alpha =
      OneQubitMagic.phaseShiftOperator beta) :
    (OneQubitMagic.phaseShiftTransport alpha).conjOperator data =
      (OneQubitMagic.phaseShiftTransport beta).conjOperator data := by
  have hinverse : OneQubitMagic.phaseShiftOperator (-alpha) =
      OneQubitMagic.phaseShiftOperator (-beta) := by
    calc
      OneQubitMagic.phaseShiftOperator (-alpha) =
          (OneQubitMagic.phaseShiftOperator (-beta) *
            OneQubitMagic.phaseShiftOperator beta) *
              OneQubitMagic.phaseShiftOperator (-alpha) := by
                rw [OneQubitMagic.phaseShiftOperator_neg_mul]
                simp
      _ = OneQubitMagic.phaseShiftOperator (-beta) *
          (OneQubitMagic.phaseShiftOperator beta *
            OneQubitMagic.phaseShiftOperator (-alpha)) := by
              rw [mul_assoc]
      _ = OneQubitMagic.phaseShiftOperator (-beta) *
          (OneQubitMagic.phaseShiftOperator alpha *
            OneQubitMagic.phaseShiftOperator (-alpha)) := by
              rw [hoperator]
      _ = OneQubitMagic.phaseShiftOperator (-beta) := by
              rw [OneQubitMagic.phaseShiftOperator_mul_neg]
              simp
  unfold UnitaryTransport.conjOperator
  apply LinearMap.ext
  intro psi
  change OneQubitMagic.phaseShiftOperator alpha
      (data (OneQubitMagic.phaseShiftOperator (-alpha) psi)) =
    OneQubitMagic.phaseShiftOperator beta
      (data (OneQubitMagic.phaseShiftOperator (-beta) psi))
  rw [hoperator, hinverse]

private theorem hRetry_leaf_raw_history (target : ZMod 8) (remaining : Nat) :
    ∀ (position : ZMod 8) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace) (leaf : BK05RawLeaf),
      leaf ∈ hRetry hMagicState target remaining position ledger history data →
      ∃ coins : List Bool, leaf.history = coins.reverse ++ history ∧
        leaf.raw = hIdealHistoryRaw coins data := by
  induction remaining with
  | zero =>
      intro position ledger history data leaf hmem
      by_cases htarget : position = target
      · simp [hRetry, htarget] at hmem
        subst leaf
        exact ⟨[], by simp, rfl⟩
      · simp [hRetry, htarget] at hmem
        subst leaf
        exact ⟨[], by simp, rfl⟩
  | succ remaining ih =>
      intro position ledger history data leaf hmem
      by_cases htarget : position = target
      · simp [hRetry, htarget] at hmem
        subst leaf
        exact ⟨[], by simp, rfl⟩
      · rw [hRetry, if_neg htarget] at hmem
        rcases List.mem_append.mp hmem with htrue | hfalse
        · rcases ih (position + 1) (ledger + ({.h} : ResourceLedger BK05ResourceToken))
              (true :: history) (hStepRaw hMagicState true data) leaf htrue with
              ⟨coins, hhistory, hraw⟩
          refine ⟨true :: coins, ?_, ?_⟩
          · calc
              leaf.history = coins.reverse ++ true :: history := hhistory
              _ = (true :: coins).reverse ++ history := by
                simp [List.reverse_cons, List.append_assoc]
          · simpa [hIdealHistoryRaw] using hraw
        · rcases ih (position - 1) (ledger + ({.h} : ResourceLedger BK05ResourceToken))
              (false :: history) (hStepRaw hMagicState false data) leaf hfalse with
              ⟨coins, hhistory, hraw⟩
          refine ⟨false :: coins, ?_, ?_⟩
          · calc
              leaf.history = coins.reverse ++ false :: history := hhistory
              _ = (false :: coins).reverse ++ history := by
                simp [List.reverse_cons, List.append_assoc]
          · simpa [hIdealHistoryRaw] using hraw

private theorem hRetry_targetHit_leaf_action (target : ZMod 8) (remaining : Nat)
    (data : Operator QubitSpace) (hdata : LinearMap.IsPositive data)
    (leaf : BK05RawLeaf)
    (hmem : leaf ∈ hRetry hMagicState target remaining 0 0 [] data)
    (hkind : leaf.kind = .targetHit) :
    leaf.raw = (1 / 2 : Complex) ^ leaf.history.length •
      phaseCycleTargetChannel 8 target data := by
  rcases hRetry_leaf_raw_history target remaining 0 0 [] data leaf hmem with
    ⟨coins, hhistory, hraw⟩
  have hleafhistory : leaf.history = coins.reverse := by
    simpa using hhistory
  obtain ⟨storedCoins, hstored, _⟩ := hRetry_targetHit_history target remaining
    0 0 [] data leaf hmem hkind
  have hcoins : coins = storedCoins := by
    have hreverse : coins.reverse = storedCoins.reverse := by
      calc
        coins.reverse = leaf.history := hleafhistory.symm
        _ = storedCoins.reverse := by simpa using hstored
    have := congrArg List.reverse hreverse
    simpa using this
  have hrootEndpoint := hRetry_targetHit_history_root target remaining data leaf hmem hkind
  have hendpoint : PhaseRetry.endpoint (0 : ZMod 8) coins = target := by
    calc
      PhaseRetry.endpoint (0 : ZMod 8) coins =
          PhaseRetry.endpoint (0 : ZMod 8) storedCoins := by rw [hcoins]
      _ = PhaseRetry.endpoint (0 : ZMod 8) leaf.history.reverse := by
          rw [hleafhistory, hcoins, List.reverse_reverse]
      _ = target := hrootEndpoint
  have hphase : OneQubitMagic.phaseShiftOperator
      (phaseInjectionHistoryAngle (-Real.pi / 4) coins) =
      phaseCycleTargetAction 8 target := by
    simpa [phaseCycleAngle_eight] using
      phaseCycleTargetAction_of_endpoint coins target hendpoint
  have htransport :
      (OneQubitMagic.phaseShiftTransport
        (phaseInjectionHistoryAngle (-Real.pi / 4) coins)).conjOperator data =
        phaseCycleTargetChannel 8 target data := by
    unfold phaseCycleTargetChannel
    apply phaseShiftTransport_conjOperator_eq_of_operator_eq
    simpa [phaseCycleTargetAction] using hphase
  calc
    leaf.raw = hIdealHistoryRaw coins data := hraw
    _ = (1 / 2 : Complex) ^ coins.length •
        (OneQubitMagic.phaseShiftTransport
          (phaseInjectionHistoryAngle (-Real.pi / 4) coins)).conjOperator data :=
      hIdealHistoryRaw_action coins data hdata
    _ = (1 / 2 : Complex) ^ leaf.history.length •
        (OneQubitMagic.phaseShiftTransport
          (phaseInjectionHistoryAngle (-Real.pi / 4) coins)).conjOperator data := by
            rw [hleafhistory, List.length_reverse]
    _ = (1 / 2 : Complex) ^ leaf.history.length •
        phaseCycleTargetChannel 8 target data := by rw [htransport]

private def hTargetHitHistoryWeight (leaves : List BK05RawLeaf) : Complex :=
  (leaves.filter fun leaf => leaf.kind == .targetHit).map
    (fun leaf => (1 / 2 : Complex) ^ leaf.history.length) |>.sum

private theorem hTargetHitHistoryWeight_append
    (left right : List BK05RawLeaf) :
    hTargetHitHistoryWeight (left ++ right) =
      hTargetHitHistoryWeight left + hTargetHitHistoryWeight right := by
  simp [hTargetHitHistoryWeight]

private theorem hRetry_targetHit_historyWeight (target : ZMod 8) (remaining : Nat) :
    ∀ (position : ZMod 8) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace),
      hTargetHitHistoryWeight
        (hRetry hMagicState target remaining position ledger history data) =
        (1 / 2 : Complex) ^ history.length *
          (hTargetHitCoeff target remaining position : Complex) := by
  induction remaining with
  | zero =>
      intro position ledger history data
      by_cases htarget : position = target <;>
        simp [hRetry, hTargetHitHistoryWeight, hTargetHitCoeff, htarget]
  | succ remaining ih =>
      intro position ledger history data
      by_cases htarget : position = target
      · simp [hRetry, hTargetHitHistoryWeight, hTargetHitCoeff, htarget]
      · rw [hRetry, if_neg htarget, hTargetHitHistoryWeight_append]
        rw [ih (position + 1) (ledger + ({.h} : ResourceLedger BK05ResourceToken))
          (true :: history) (hStepRaw hMagicState true data),
          ih (position - 1) (ledger + ({.h} : ResourceLedger BK05ResourceToken))
            (false :: history) (hStepRaw hMagicState false data)]
        simp only [hTargetHitCoeff, htarget, if_false, List.length_cons, pow_succ]
        push_cast
        ring

private theorem rawAggregateOfKind_eq_historyWeight_smul
    (leaves : List BK05RawLeaf) (action : Operator QubitSpace)
    (hraw : ∀ leaf, leaf ∈ leaves → leaf.kind = .targetHit →
      leaf.raw = (1 / 2 : Complex) ^ leaf.history.length • action) :
    rawAggregateOfKind .targetHit leaves =
      hTargetHitHistoryWeight leaves • action := by
  induction leaves with
  | nil => simp [rawAggregateOfKind, hTargetHitHistoryWeight, rawAggregate]
  | cons leaf leaves ih =>
      by_cases hkind : leaf.kind = .targetHit
      · have hleaf := hraw leaf (by simp) hkind
        have htail : ∀ next, next ∈ leaves → next.kind = .targetHit →
            next.raw = (1 / 2 : Complex) ^ next.history.length • action := by
              intro next hnext hnextkind
              exact hraw next (by simp [hnext]) hnextkind
        rw [show rawAggregateOfKind .targetHit (leaf :: leaves) =
            leaf.raw + rawAggregateOfKind .targetHit leaves by
              simp [rawAggregateOfKind, rawAggregate, hkind]]
        rw [hleaf, ih htail]
        simp [hTargetHitHistoryWeight, hkind, add_smul]
      · have htail : ∀ next, next ∈ leaves → next.kind = .targetHit →
            next.raw = (1 / 2 : Complex) ^ next.history.length • action := by
              intro next hnext hnextkind
              exact hraw next (by simp [hnext]) hnextkind
        rw [show rawAggregateOfKind .targetHit (leaf :: leaves) =
            rawAggregateOfKind .targetHit leaves by
              simp [rawAggregateOfKind, rawAggregate, hkind]]
        rw [ih htail]
        simp [hTargetHitHistoryWeight, hkind]

private theorem hRetry_ideal_targetHit_action_root
    (target : ZMod 8) (remaining : Nat)
    (data : Operator QubitSpace) (hdata : LinearMap.IsPositive data) :
    rawAggregateOfKind .targetHit
      (hRetry hMagicState target remaining 0 0 [] data) =
      (hTargetHitCoeff target remaining 0 : Complex) •
        phaseCycleTargetChannel 8 target data := by
  have hraw : ∀ leaf, leaf ∈ hRetry hMagicState target remaining 0 0 [] data →
      leaf.kind = .targetHit →
      leaf.raw = (1 / 2 : Complex) ^ leaf.history.length •
        phaseCycleTargetChannel 8 target data := by
          intro leaf hmem hkind
          exact hRetry_targetHit_leaf_action target remaining data hdata leaf hmem hkind
  calc
    rawAggregateOfKind .targetHit
        (hRetry hMagicState target remaining 0 0 [] data) =
        hTargetHitHistoryWeight
          (hRetry hMagicState target remaining 0 0 [] data) •
            phaseCycleTargetChannel 8 target data :=
      rawAggregateOfKind_eq_historyWeight_smul _ _ hraw
    _ = ((1 / 2 : Complex) ^ ([] : List Bool).length *
        (hTargetHitCoeff target remaining 0 : Complex)) •
          phaseCycleTargetChannel 8 target data := by
            rw [hRetry_targetHit_historyWeight target remaining 0 0 [] data]
    _ = (hTargetHitCoeff target remaining 0 : Complex) •
          phaseCycleTargetChannel 8 target data := by simp

private theorem hRetry_rawAggregate_decompose
    (target : ZMod 8) (remaining : Nat) :
    ∀ (position : ZMod 8) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace),
      rawAggregate (hRetry hMagicState target remaining position ledger history data) =
        rawAggregateOfKind .targetHit
          (hRetry hMagicState target remaining position ledger history data) +
        rawAggregateOfKind .phaseExhausted
          (hRetry hMagicState target remaining position ledger history data) := by
  induction remaining with
  | zero =>
      intro position ledger history data
      by_cases htarget : position = target <;>
        simp [hRetry, rawAggregate, rawAggregateOfKind, htarget]
  | succ remaining ih =>
      intro position ledger history data
      by_cases htarget : position = target
      · simp [hRetry, rawAggregate, rawAggregateOfKind, htarget]
      · rw [hRetry, if_neg htarget, rawAggregate_append,
          rawAggregateOfKind_append, rawAggregateOfKind_append]
        rw [ih (position + 1) (ledger + ({.h} : ResourceLedger BK05ResourceToken))
          (true :: history) (hStepRaw hMagicState true data),
          ih (position - 1) (ledger + ({.h} : ResourceLedger BK05ResourceToken))
            (false :: history) (hStepRaw hMagicState false data)]
        abel

/- Task 5d4: status-aware H word execution. -/

private theorem hRetry_targetHit_rawAggregate_metadata
    (target : ZMod 8) (remaining : Nat) :
    ∀ (position : ZMod 8) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace),
      rawAggregateOfKind .targetHit
        (hRetry hMagicState target remaining position ledger history data) =
        rawAggregateOfKind .targetHit
          (hRetry hMagicState target remaining position 0 [] data) := by
  induction remaining with
  | zero =>
      intro position ledger history data
      by_cases htarget : position = target <;>
        simp [hRetry, rawAggregateOfKind, rawAggregate, htarget]
  | succ remaining ih =>
      intro position ledger history data
      by_cases htarget : position = target
      · simp [hRetry, rawAggregateOfKind, rawAggregate, htarget]
      · calc
          rawAggregateOfKind .targetHit
              (hRetry hMagicState target (remaining + 1) position ledger history data) =
              rawAggregateOfKind .targetHit
                (hRetry hMagicState target remaining (position + 1)
                  (ledger + ({.h} : ResourceLedger BK05ResourceToken))
                  (true :: history) (hStepRaw hMagicState true data)) +
              rawAggregateOfKind .targetHit
                (hRetry hMagicState target remaining (position - 1)
                  (ledger + ({.h} : ResourceLedger BK05ResourceToken))
                  (false :: history) (hStepRaw hMagicState false data)) := by
                rw [hRetry, if_neg htarget, rawAggregateOfKind_append]
          _ = rawAggregateOfKind .targetHit
                (hRetry hMagicState target remaining (position + 1) 0 []
                  (hStepRaw hMagicState true data)) +
              rawAggregateOfKind .targetHit
                (hRetry hMagicState target remaining (position - 1) 0 []
                  (hStepRaw hMagicState false data)) := by
                rw [ih (position + 1)
                  (ledger + ({.h} : ResourceLedger BK05ResourceToken))
                  (true :: history) (hStepRaw hMagicState true data),
                  ih (position - 1)
                    (ledger + ({.h} : ResourceLedger BK05ResourceToken))
                    (false :: history) (hStepRaw hMagicState false data)]
          _ = rawAggregateOfKind .targetHit
                (hRetry hMagicState target remaining (position + 1)
                  (0 + ({.h} : ResourceLedger BK05ResourceToken)) [true]
                  (hStepRaw hMagicState true data)) +
              rawAggregateOfKind .targetHit
                (hRetry hMagicState target remaining (position - 1)
                  (0 + ({.h} : ResourceLedger BK05ResourceToken)) [false]
                  (hStepRaw hMagicState false data)) := by
                rw [ih (position + 1)
                  (0 + ({.h} : ResourceLedger BK05ResourceToken)) [true]
                  (hStepRaw hMagicState true data),
                  ih (position - 1)
                    (0 + ({.h} : ResourceLedger BK05ResourceToken)) [false]
                    (hStepRaw hMagicState false data)]
          _ = rawAggregateOfKind .targetHit
                (hRetry hMagicState target (remaining + 1) position 0 [] data) := by
                rw [hRetry, if_neg htarget, rawAggregateOfKind_append]

private theorem hRetry_ideal_targetHit_action
    (target : ZMod 8) (remaining : Nat)
    (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
    (data : Operator QubitSpace) (hdata : LinearMap.IsPositive data) :
    rawAggregateOfKind .targetHit
      (hRetry hMagicState target remaining 0 ledger history data) =
      (hTargetHitCoeff target remaining 0 : Complex) •
        phaseCycleTargetChannel 8 target data := by
  rw [hRetry_targetHit_rawAggregate_metadata target remaining 0 ledger history data]
  exact hRetry_ideal_targetHit_action_root target remaining data hdata

/- Task 5d4b: H retry stopping linear semantics. -/

private theorem phaseCycleTargetChannel_trace
    (q : Nat) (target : ZMod q) (data : Operator QubitSpace) :
    LinearMap.trace Complex QubitSpace
        (phaseCycleTargetChannel q target data) =
      LinearMap.trace Complex QubitSpace data := by
  simpa [phaseCycleTargetChannel] using
    (OneQubitMagic.phaseShiftTransport
      (phaseCycleAngle q * target.val)).trace_conjOperator data

private noncomputable def hRetryTargetHitLinear
    (h : DensityOperator QubitSpace) (target : ZMod 8) :
    Nat → ZMod 8 → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | 0, position => if position = target then LinearMap.id else 0
  | remaining + 1, position =>
      if position = target then LinearMap.id else
        (hRetryTargetHitLinear h target remaining (position + 1)).comp
            (phaseBranchRawLinear (hPhaseRaw h) true) +
        (hRetryTargetHitLinear h target remaining (position - 1)).comp
            (phaseBranchRawLinear (hPhaseRaw h) false)

private noncomputable def hRetryPhaseExhaustedLinear
    (h : DensityOperator QubitSpace) (target : ZMod 8) :
    Nat → ZMod 8 → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | 0, position => if position = target then 0 else LinearMap.id
  | remaining + 1, position =>
      if position = target then 0 else
        (hRetryPhaseExhaustedLinear h target remaining (position + 1)).comp
            (phaseBranchRawLinear (hPhaseRaw h) true) +
        (hRetryPhaseExhaustedLinear h target remaining (position - 1)).comp
            (phaseBranchRawLinear (hPhaseRaw h) false)

private theorem hRetryTargetHitLinear_apply
    (h : DensityOperator QubitSpace) (target : ZMod 8) (remaining : Nat) :
    ∀ (position : ZMod 8) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace),
      hRetryTargetHitLinear h target remaining position data =
        rawAggregateOfKind .targetHit
          (hRetry h target remaining position ledger history data) := by
  induction remaining with
  | zero =>
      intro position ledger history data
      by_cases htarget : position = target <;>
        simp [hRetryTargetHitLinear, hRetry, rawAggregateOfKind, rawAggregate, htarget]
  | succ remaining ih =>
      intro position ledger history data
      by_cases htarget : position = target
      · simp [hRetryTargetHitLinear, hRetry, rawAggregateOfKind, rawAggregate, htarget]
      · rw [hRetry, if_neg htarget, rawAggregateOfKind_append]
        simp only [hRetryTargetHitLinear, if_neg htarget, LinearMap.add_apply,
          LinearMap.comp_apply, phaseBranchRawLinear_apply]
        rw [ih (position + 1)
          (ledger + ({.h} : ResourceLedger BK05ResourceToken)) (true :: history),
          ih (position - 1)
            (ledger + ({.h} : ResourceLedger BK05ResourceToken)) (false :: history)]
        simp [hStepRaw]

private theorem hRetryPhaseExhaustedLinear_apply
    (h : DensityOperator QubitSpace) (target : ZMod 8) (remaining : Nat) :
    ∀ (position : ZMod 8) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace),
      hRetryPhaseExhaustedLinear h target remaining position data =
        rawAggregateOfKind .phaseExhausted
          (hRetry h target remaining position ledger history data) := by
  induction remaining with
  | zero =>
      intro position ledger history data
      by_cases htarget : position = target <;>
        simp [hRetryPhaseExhaustedLinear, hRetry, rawAggregateOfKind, rawAggregate, htarget]
  | succ remaining ih =>
      intro position ledger history data
      by_cases htarget : position = target
      · simp [hRetryPhaseExhaustedLinear, hRetry, rawAggregateOfKind, rawAggregate, htarget]
      · rw [hRetry, if_neg htarget, rawAggregateOfKind_append]
        simp only [hRetryPhaseExhaustedLinear, if_neg htarget, LinearMap.add_apply,
          LinearMap.comp_apply, phaseBranchRawLinear_apply]
        rw [ih (position + 1)
          (ledger + ({.h} : ResourceLedger BK05ResourceToken)) (true :: history),
          ih (position - 1)
            (ledger + ({.h} : ResourceLedger BK05ResourceToken)) (false :: history)]
        simp [hStepRaw]

private theorem hRetryTargetHitLinear_positive
    (h : DensityOperator QubitSpace) (target : ZMod 8) :
    ∀ (remaining : Nat) (position : ZMod 8) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      LinearMap.IsPositive (hRetryTargetHitLinear h target remaining position data) := by
  intro remaining
  induction remaining with
  | zero =>
      intro position data hdata
      by_cases htarget : position = target
      · simpa [hRetryTargetHitLinear, htarget] using hdata
      · simp [hRetryTargetHitLinear, htarget]
  | succ remaining ih =>
      intro position data hdata
      by_cases htarget : position = target
      · simpa [hRetryTargetHitLinear, htarget] using hdata
      · have htrue := ih (position + 1) (phaseBranchRaw (hPhaseRaw h) data true)
          (phaseBranchRaw_positive (hPhaseRaw h) data (hPhaseRaw_positive h) hdata true)
        have hfalse := ih (position - 1) (phaseBranchRaw (hPhaseRaw h) data false)
          (phaseBranchRaw_positive (hPhaseRaw h) data (hPhaseRaw_positive h) hdata false)
        simpa [hRetryTargetHitLinear, htarget, LinearMap.add_apply,
          LinearMap.comp_apply, phaseBranchRawLinear_apply] using htrue.add hfalse

private theorem hRetryPhaseExhaustedLinear_positive
    (h : DensityOperator QubitSpace) (target : ZMod 8) :
    ∀ (remaining : Nat) (position : ZMod 8) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      LinearMap.IsPositive
        (hRetryPhaseExhaustedLinear h target remaining position data) := by
  intro remaining
  induction remaining with
  | zero =>
      intro position data hdata
      by_cases htarget : position = target
      · simp [hRetryPhaseExhaustedLinear, htarget]
      · simpa [hRetryPhaseExhaustedLinear, htarget] using hdata
  | succ remaining ih =>
      intro position data hdata
      by_cases htarget : position = target
      · simp [hRetryPhaseExhaustedLinear, htarget]
      · have htrue := ih (position + 1) (phaseBranchRaw (hPhaseRaw h) data true)
          (phaseBranchRaw_positive (hPhaseRaw h) data (hPhaseRaw_positive h) hdata true)
        have hfalse := ih (position - 1) (phaseBranchRaw (hPhaseRaw h) data false)
          (phaseBranchRaw_positive (hPhaseRaw h) data (hPhaseRaw_positive h) hdata false)
        simpa [hRetryPhaseExhaustedLinear, htarget, LinearMap.add_apply,
          LinearMap.comp_apply, phaseBranchRawLinear_apply] using htrue.add hfalse

private theorem hRetryComponentLinear_sum
    (h : DensityOperator QubitSpace) (target : ZMod 8) :
    ∀ (remaining : Nat) (position : ZMod 8),
      hRetryTargetHitLinear h target remaining position +
        hRetryPhaseExhaustedLinear h target remaining position =
        hRetryAggregateLinear h target remaining position := by
  intro remaining
  induction remaining with
  | zero =>
      intro position
      apply LinearMap.ext
      intro data
      by_cases htarget : position = target <;>
        simp [hRetryTargetHitLinear, hRetryPhaseExhaustedLinear,
          hRetryAggregateLinear, htarget]
  | succ remaining ih =>
      intro position
      apply LinearMap.ext
      intro data
      by_cases htarget : position = target
      · simp [hRetryTargetHitLinear, hRetryPhaseExhaustedLinear,
          hRetryAggregateLinear, htarget]
      · simp only [hRetryTargetHitLinear, hRetryPhaseExhaustedLinear,
          hRetryAggregateLinear, if_neg htarget, LinearMap.add_apply,
          LinearMap.comp_apply, phaseBranchRawLinear_apply]
        rw [← ih (position + 1), ← ih (position - 1)]
        simp only [LinearMap.add_apply]
        abel

private theorem hRetryIdealComponentLinear_apply
    (target : ZMod 8) (remaining : Nat) :
    ∀ (position : ZMod 8) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace),
      (hRetryTargetHitLinear hMagicState target remaining position +
        hRetryPhaseExhaustedLinear hMagicState target remaining position) data =
        rawAggregate
          (hRetry hMagicState target remaining position ledger history data) := by
  intro position ledger history data
  rw [LinearMap.add_apply,
    hRetryTargetHitLinear_apply hMagicState target remaining position ledger history data,
    hRetryPhaseExhaustedLinear_apply hMagicState target remaining
      position ledger history data,
    ← hRetry_rawAggregate_decompose target remaining position ledger history data]

private theorem hRetryComponentLinear_trace
    (target : ZMod 8) (remaining : Nat) (position : ZMod 8)
    (data : Operator QubitSpace) :
    LinearMap.trace Complex QubitSpace
        (hRetryTargetHitLinear hMagicState target remaining position data) +
      LinearMap.trace Complex QubitSpace
        (hRetryPhaseExhaustedLinear hMagicState target remaining position data) =
        LinearMap.trace Complex QubitSpace data := by
  calc
    LinearMap.trace Complex QubitSpace
        (hRetryTargetHitLinear hMagicState target remaining position data) +
      LinearMap.trace Complex QubitSpace
        (hRetryPhaseExhaustedLinear hMagicState target remaining position data) =
        LinearMap.trace Complex QubitSpace
          ((hRetryTargetHitLinear hMagicState target remaining position +
            hRetryPhaseExhaustedLinear hMagicState target remaining position) data) := by
          rw [LinearMap.add_apply, map_add]
    _ = LinearMap.trace Complex QubitSpace
          (hRetryAggregateLinear hMagicState target remaining position data) := by
          rw [hRetryComponentLinear_sum hMagicState target remaining position]
    _ = LinearMap.trace Complex QubitSpace data :=
      hRetryAggregateLinear_trace hMagicState target remaining position data

private theorem hRetryTargetHitLinear_trace_nonneg
    (target : ZMod 8) (remaining : Nat) (position : ZMod 8)
    (data : Operator QubitSpace) (hdata : LinearMap.IsPositive data) :
    0 ≤ (LinearMap.trace Complex QubitSpace
      (hRetryTargetHitLinear hMagicState target remaining position data)).re := by
  exact (Complex.nonneg_iff.mp
    (hRetryTargetHitLinear_positive hMagicState target remaining position data hdata).trace_nonneg).1

private theorem hRetryTargetHitLinear_trace_le
    (target : ZMod 8) (remaining : Nat) (position : ZMod 8)
    (data : Operator QubitSpace) (hdata : LinearMap.IsPositive data) :
    (LinearMap.trace Complex QubitSpace
      (hRetryTargetHitLinear hMagicState target remaining position data)).re ≤
      (LinearMap.trace Complex QubitSpace data).re := by
  have hexhausted : 0 ≤ (LinearMap.trace Complex QubitSpace
      (hRetryPhaseExhaustedLinear hMagicState target remaining position data)).re :=
    (Complex.nonneg_iff.mp
      (hRetryPhaseExhaustedLinear_positive hMagicState target remaining position data hdata).trace_nonneg).1
  have htrace : (LinearMap.trace Complex QubitSpace
      (hRetryTargetHitLinear hMagicState target remaining position data)).re +
      (LinearMap.trace Complex QubitSpace
        (hRetryPhaseExhaustedLinear hMagicState target remaining position data)).re =
        (LinearMap.trace Complex QubitSpace data).re := by
    simpa only [Complex.add_re] using
      congrArg Complex.re (hRetryComponentLinear_trace target remaining position data)
  linarith

/- Task 5d4c: H retry stopping continuation semantics. -/

private noncomputable def hRetryStoppingTotalLinear
    (h : DensityOperator QubitSpace) (target : ZMod 8)
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    Nat → ZMod 8 → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | 0, position => if position = target then success else LinearMap.id
  | remaining + 1, position =>
      if position = target then success else
        (hRetryStoppingTotalLinear h target success remaining (position + 1)).comp
            (phaseBranchRawLinear (hPhaseRaw h) true) +
        (hRetryStoppingTotalLinear h target success remaining (position - 1)).comp
            (phaseBranchRawLinear (hPhaseRaw h) false)

private theorem hRetryStoppingTotalLinear_split
    (h : DensityOperator QubitSpace) (target : ZMod 8)
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    ∀ (remaining : Nat) (position : ZMod 8),
      hRetryStoppingTotalLinear h target success remaining position =
        success.comp (hRetryTargetHitLinear h target remaining position) +
          hRetryPhaseExhaustedLinear h target remaining position := by
  intro remaining
  induction remaining with
  | zero =>
      intro position
      apply LinearMap.ext
      intro data
      by_cases htarget : position = target <;>
        simp [hRetryStoppingTotalLinear, hRetryTargetHitLinear,
          hRetryPhaseExhaustedLinear, htarget]
  | succ remaining ih =>
      intro position
      apply LinearMap.ext
      intro data
      by_cases htarget : position = target
      · simp [hRetryStoppingTotalLinear, hRetryTargetHitLinear,
          hRetryPhaseExhaustedLinear, htarget]
      · simp only [hRetryStoppingTotalLinear, hRetryTargetHitLinear,
          hRetryPhaseExhaustedLinear, if_neg htarget, LinearMap.add_apply,
          LinearMap.comp_apply, phaseBranchRawLinear_apply]
        rw [ih (position + 1), ih (position - 1)]
        simp only [LinearMap.add_apply, LinearMap.comp_apply]
        rw [map_add]
        abel

private theorem hRetryStoppingTotalLinear_apply
    (h : DensityOperator QubitSpace) (target : ZMod 8)
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (remaining : Nat) :
    ∀ (position : ZMod 8) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace),
      hRetryStoppingTotalLinear h target success remaining position data =
        success (rawAggregateOfKind .targetHit
          (hRetry h target remaining position ledger history data)) +
          rawAggregateOfKind .phaseExhausted
            (hRetry h target remaining position ledger history data) := by
  intro position ledger history data
  rw [hRetryStoppingTotalLinear_split, LinearMap.add_apply, LinearMap.comp_apply,
    hRetryTargetHitLinear_apply h target remaining position ledger history data,
    hRetryPhaseExhaustedLinear_apply h target remaining position ledger history data]

private theorem hRetryStoppingTotalLinear_positive
    (h : DensityOperator QubitSpace) (target : ZMod 8)
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (hsuccess : ∀ data : Operator QubitSpace,
      LinearMap.IsPositive data → LinearMap.IsPositive (success data)) :
    ∀ (remaining : Nat) (position : ZMod 8) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      LinearMap.IsPositive
        (hRetryStoppingTotalLinear h target success remaining position data) := by
  intro remaining position data hdata
  rw [hRetryStoppingTotalLinear_split, LinearMap.add_apply, LinearMap.comp_apply]
  exact (hsuccess _
    (hRetryTargetHitLinear_positive h target remaining position data hdata)).add
      (hRetryPhaseExhaustedLinear_positive h target remaining position data hdata)

private theorem hRetryStoppingTotalLinear_trace
    (h : DensityOperator QubitSpace) (target : ZMod 8)
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (hsuccess : ∀ data : Operator QubitSpace,
      LinearMap.trace Complex QubitSpace (success data) =
        LinearMap.trace Complex QubitSpace data) :
    ∀ (remaining : Nat) (position : ZMod 8) (data : Operator QubitSpace),
      LinearMap.trace Complex QubitSpace
        (hRetryStoppingTotalLinear h target success remaining position data) =
        LinearMap.trace Complex QubitSpace data := by
  intro remaining position data
  calc
    LinearMap.trace Complex QubitSpace
        (hRetryStoppingTotalLinear h target success remaining position data) =
        LinearMap.trace Complex QubitSpace
          (success (hRetryTargetHitLinear h target remaining position data)) +
          LinearMap.trace Complex QubitSpace
            (hRetryPhaseExhaustedLinear h target remaining position data) := by
          rw [hRetryStoppingTotalLinear_split, LinearMap.add_apply,
            LinearMap.comp_apply, map_add]
    _ = LinearMap.trace Complex QubitSpace
          (hRetryTargetHitLinear h target remaining position data) +
          LinearMap.trace Complex QubitSpace
            (hRetryPhaseExhaustedLinear h target remaining position data) := by
          rw [hsuccess]
    _ = LinearMap.trace Complex QubitSpace
          ((hRetryTargetHitLinear h target remaining position +
            hRetryPhaseExhaustedLinear h target remaining position) data) := by
          rw [LinearMap.add_apply, map_add]
    _ = LinearMap.trace Complex QubitSpace
          (hRetryAggregateLinear h target remaining position data) := by
          rw [hRetryComponentLinear_sum h target remaining position]
    _ = LinearMap.trace Complex QubitSpace data :=
      hRetryAggregateLinear_trace h target remaining position data

private theorem hRetryStoppingTotalLinear_id
    (h : DensityOperator QubitSpace) (target : ZMod 8) :
    ∀ (remaining : Nat) (position : ZMod 8),
      hRetryStoppingTotalLinear h target LinearMap.id remaining position =
        hRetryAggregateLinear h target remaining position := by
  intro remaining position
  rw [hRetryStoppingTotalLinear_split]
  simpa using hRetryComponentLinear_sum h target remaining position

private theorem hRetryStoppingTotalLinear_id_apply
    (h : DensityOperator QubitSpace) (target : ZMod 8) (remaining : Nat) :
    ∀ (position : ZMod 8) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace),
      hRetryStoppingTotalLinear h target LinearMap.id remaining position data =
        rawAggregate (hRetry h target remaining position ledger history data) := by
  intro position ledger history data
  rw [hRetryStoppingTotalLinear_id h target remaining position,
    hRetryAggregateLinear_apply h target remaining position ledger history data]

/- Task 5d4d: H stopping source stability. -/

private theorem hRetryStoppingTotalLinear_stable
    (h : DensityOperator QubitSpace) (target : ZMod 8)
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (hsuccessPositive : ∀ data : Operator QubitSpace,
      LinearMap.IsPositive data → LinearMap.IsPositive (success data))
    (hsuccessTrace : ∀ data : Operator QubitSpace,
      LinearMap.trace Complex QubitSpace (success data) =
        LinearMap.trace Complex QubitSpace data)
    (remaining : Nat) :
    ∀ (position : ZMod 8) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      traceNorm
        (hRetryStoppingTotalLinear h target success remaining position data -
          hRetryStoppingTotalLinear hMagicState target success remaining position data) ≤
        (remaining : Real) * (LinearMap.trace Complex QubitSpace data).re *
          traceNorm (h.toOperator - hMagicState.toOperator) := by
  induction remaining with
  | zero =>
      intro position data hdata
      have hzero : traceNorm (0 : Operator QubitSpace) = 0 :=
        (traceNorm_eq_zero_iff 0).mpr rfl
      simp [hRetryStoppingTotalLinear, hzero]
  | succ remaining ih =>
      intro position data hdata
      by_cases htarget : position = target
      · have htrace : 0 ≤ (LinearMap.trace Complex QubitSpace data).re :=
          (Complex.nonneg_iff.mp hdata.trace_nonneg).1
        have hright : 0 ≤ (remaining + 1 : Real) *
            (LinearMap.trace Complex QubitSpace data).re *
              traceNorm (h.toOperator - hMagicState.toOperator) := by
          exact mul_nonneg (mul_nonneg (by positivity) htrace) (traceNorm_nonneg _)
        have hzero : traceNorm (0 : Operator QubitSpace) = 0 :=
          (traceNorm_eq_zero_iff 0).mpr rfl
        simpa [hRetryStoppingTotalLinear, htarget, hzero] using hright
      · have htruePositive : LinearMap.IsPositive
            (phaseBranchRaw (hPhaseRaw h) data true) :=
          phaseBranchRaw_positive (hPhaseRaw h) data (hPhaseRaw_positive h) hdata true
        have hfalsePositive : LinearMap.IsPositive
            (phaseBranchRaw (hPhaseRaw h) data false) :=
          phaseBranchRaw_positive (hPhaseRaw h) data (hPhaseRaw_positive h) hdata false
        have hbranchTrace := congrArg Complex.re
          (phaseBranchRaw_trace_sum (hPhaseRaw h) data)
        rw [hPhaseRaw_trace_one] at hbranchTrace
        have hbranchTraceReal :
            (LinearMap.trace Complex QubitSpace
                (phaseBranchRaw (hPhaseRaw h) data true)).re +
              (LinearMap.trace Complex QubitSpace
                (phaseBranchRaw (hPhaseRaw h) data false)).re =
              (LinearMap.trace Complex QubitSpace data).re := by
          simpa [Complex.add_re] using hbranchTrace
        have hinputPositive : LinearMap.IsPositive
            (injectedInputRaw data (hPhaseRaw h)) :=
          injectedInputRaw_positive data (hPhaseRaw h) hdata (hPhaseRaw_positive h)
        have hidealInputPositive : LinearMap.IsPositive
            (injectedInputRaw data (hPhaseRaw hMagicState)) :=
          injectedInputRaw_positive data (hPhaseRaw hMagicState) hdata
            (hPhaseRaw_positive hMagicState)
        have hinputSymmetric :
            (injectedInputRaw data (hPhaseRaw h) -
              injectedInputRaw data (hPhaseRaw hMagicState)).IsSymmetric :=
          hinputPositive.isSymmetric.sub hidealInputPositive.isSymmetric
        have hactual :
            hRetryStoppingTotalLinear h target success (remaining + 1) position data =
              phaseContinuationLinear
                (hRetryStoppingTotalLinear h target success remaining (position + 1))
                (hRetryStoppingTotalLinear h target success remaining (position - 1))
                (injectedInputRaw data (hPhaseRaw h)) := by
          simp [hRetryStoppingTotalLinear, htarget, phaseContinuationLinear,
            observedBranchLinear_apply, phaseBranchRawLinear_apply, phaseBranchRaw]
        have hideal :
            hRetryStoppingTotalLinear hMagicState target success (remaining + 1)
                position data =
              phaseContinuationLinear
                (hRetryStoppingTotalLinear hMagicState target success remaining
                  (position + 1))
                (hRetryStoppingTotalLinear hMagicState target success remaining
                  (position - 1))
                (injectedInputRaw data (hPhaseRaw hMagicState)) := by
          simp [hRetryStoppingTotalLinear, htarget, phaseContinuationLinear,
            observedBranchLinear_apply, phaseBranchRawLinear_apply, phaseBranchRaw]
        have hfuture :
            traceNorm
              (phaseContinuationLinear
                  (hRetryStoppingTotalLinear h target success remaining (position + 1))
                  (hRetryStoppingTotalLinear h target success remaining (position - 1))
                  (injectedInputRaw data (hPhaseRaw h)) -
                phaseContinuationLinear
                  (hRetryStoppingTotalLinear hMagicState target success remaining
                    (position + 1))
                  (hRetryStoppingTotalLinear hMagicState target success remaining
                    (position - 1))
                  (injectedInputRaw data (hPhaseRaw h))) ≤
              (remaining : Real) * (LinearMap.trace Complex QubitSpace data).re *
                traceNorm (h.toOperator - hMagicState.toOperator) := by
          change traceNorm
              (hRetryStoppingTotalLinear h target success remaining (position + 1)
                  (phaseBranchRaw (hPhaseRaw h) data true) +
                hRetryStoppingTotalLinear h target success remaining (position - 1)
                  (phaseBranchRaw (hPhaseRaw h) data false) -
                (hRetryStoppingTotalLinear hMagicState target success remaining
                    (position + 1) (phaseBranchRaw (hPhaseRaw h) data true) +
                  hRetryStoppingTotalLinear hMagicState target success remaining
                    (position - 1) (phaseBranchRaw (hPhaseRaw h) data false))) ≤ _
          calc
            traceNorm
                (hRetryStoppingTotalLinear h target success remaining (position + 1)
                    (phaseBranchRaw (hPhaseRaw h) data true) +
                  hRetryStoppingTotalLinear h target success remaining (position - 1)
                    (phaseBranchRaw (hPhaseRaw h) data false) -
                  (hRetryStoppingTotalLinear hMagicState target success remaining
                      (position + 1) (phaseBranchRaw (hPhaseRaw h) data true) +
                    hRetryStoppingTotalLinear hMagicState target success remaining
                      (position - 1) (phaseBranchRaw (hPhaseRaw h) data false))) =
                traceNorm
                  ((hRetryStoppingTotalLinear h target success remaining (position + 1)
                      (phaseBranchRaw (hPhaseRaw h) data true) -
                    hRetryStoppingTotalLinear hMagicState target success remaining
                      (position + 1) (phaseBranchRaw (hPhaseRaw h) data true)) +
                    (hRetryStoppingTotalLinear h target success remaining (position - 1)
                      (phaseBranchRaw (hPhaseRaw h) data false) -
                    hRetryStoppingTotalLinear hMagicState target success remaining
                      (position - 1) (phaseBranchRaw (hPhaseRaw h) data false))) := by
                    congr 1
                    module
            _ ≤ traceNorm
                (hRetryStoppingTotalLinear h target success remaining (position + 1)
                    (phaseBranchRaw (hPhaseRaw h) data true) -
                  hRetryStoppingTotalLinear hMagicState target success remaining
                    (position + 1) (phaseBranchRaw (hPhaseRaw h) data true)) +
                traceNorm
                  (hRetryStoppingTotalLinear h target success remaining (position - 1)
                    (phaseBranchRaw (hPhaseRaw h) data false) -
                  hRetryStoppingTotalLinear hMagicState target success remaining
                    (position - 1) (phaseBranchRaw (hPhaseRaw h) data false)) :=
              traceNorm_add_le _ _
            _ ≤ (remaining : Real) *
                  (LinearMap.trace Complex QubitSpace
                    (phaseBranchRaw (hPhaseRaw h) data true)).re *
                    traceNorm (h.toOperator - hMagicState.toOperator) +
                (remaining : Real) *
                  (LinearMap.trace Complex QubitSpace
                    (phaseBranchRaw (hPhaseRaw h) data false)).re *
                    traceNorm (h.toOperator - hMagicState.toOperator) := by
              apply add_le_add
              · exact ih (position + 1) (phaseBranchRaw (hPhaseRaw h) data true)
                  htruePositive
              · exact ih (position - 1) (phaseBranchRaw (hPhaseRaw h) data false)
                  hfalsePositive
            _ = (remaining : Real) * (LinearMap.trace Complex QubitSpace data).re *
                traceNorm (h.toOperator - hMagicState.toOperator) := by
              rw [← hbranchTraceReal]
              ring
        have hcurrent :
            traceNorm
              (phaseContinuationLinear
                  (hRetryStoppingTotalLinear hMagicState target success remaining
                    (position + 1))
                  (hRetryStoppingTotalLinear hMagicState target success remaining
                    (position - 1))
                  (injectedInputRaw data (hPhaseRaw h) -
                    injectedInputRaw data (hPhaseRaw hMagicState))) ≤
              (LinearMap.trace Complex QubitSpace data).re *
                traceNorm (h.toOperator - hMagicState.toOperator) := by
          calc
            traceNorm
                (phaseContinuationLinear
                    (hRetryStoppingTotalLinear hMagicState target success remaining
                      (position + 1))
                    (hRetryStoppingTotalLinear hMagicState target success remaining
                      (position - 1))
                    (injectedInputRaw data (hPhaseRaw h) -
                      injectedInputRaw data (hPhaseRaw hMagicState))) ≤
                traceNorm
                  (injectedInputRaw data (hPhaseRaw h) -
                    injectedInputRaw data (hPhaseRaw hMagicState)) := by
                exact phaseContinuationLinear_traceNorm_le
                  (hRetryStoppingTotalLinear hMagicState target success remaining
                    (position + 1))
                  (hRetryStoppingTotalLinear hMagicState target success remaining
                    (position - 1))
                  (fun raw hraw => hRetryStoppingTotalLinear_positive hMagicState target
                    success hsuccessPositive remaining (position + 1) raw hraw)
                  (fun raw hraw => hRetryStoppingTotalLinear_positive hMagicState target
                    success hsuccessPositive remaining (position - 1) raw hraw)
                  (fun raw => hRetryStoppingTotalLinear_trace hMagicState target success
                    hsuccessTrace remaining (position + 1) raw)
                  (fun raw => hRetryStoppingTotalLinear_trace hMagicState target success
                    hsuccessTrace remaining (position - 1) raw)
                  _ hinputSymmetric
            _ ≤ (LinearMap.trace Complex QubitSpace data).re *
                  traceNorm (h.toOperator - hMagicState.toOperator) :=
              injectedInputRaw_hResource_difference_le h data hdata
        let actualNext := phaseContinuationLinear
          (hRetryStoppingTotalLinear h target success remaining (position + 1))
          (hRetryStoppingTotalLinear h target success remaining (position - 1))
        let idealNext := phaseContinuationLinear
          (hRetryStoppingTotalLinear hMagicState target success remaining (position + 1))
          (hRetryStoppingTotalLinear hMagicState target success remaining (position - 1))
        let actualInput := injectedInputRaw data (hPhaseRaw h)
        let idealInput := injectedInputRaw data (hPhaseRaw hMagicState)
        have htele :
            actualNext actualInput - idealNext idealInput =
              (actualNext actualInput - idealNext actualInput) +
                idealNext (actualInput - idealInput) := by
          rw [idealNext.map_sub]
          module
        rw [hactual, hideal]
        change traceNorm (actualNext actualInput - idealNext idealInput) ≤ _
        rw [htele]
        calc
          traceNorm
              ((actualNext actualInput - idealNext actualInput) +
                idealNext (actualInput - idealInput)) ≤
              traceNorm (actualNext actualInput - idealNext actualInput) +
                traceNorm (idealNext (actualInput - idealInput)) :=
            traceNorm_add_le _ _
          _ ≤
              (remaining : Real) * (LinearMap.trace Complex QubitSpace data).re *
                traceNorm (h.toOperator - hMagicState.toOperator) +
                (LinearMap.trace Complex QubitSpace data).re *
                  traceNorm (h.toOperator - hMagicState.toOperator) := by
            exact add_le_add hfuture hcurrent
          _ = ((remaining + 1 : Nat) : Real) *
              (LinearMap.trace Complex QubitSpace data).re *
                traceNorm (h.toOperator - hMagicState.toOperator) := by
            push_cast
            ring

private theorem hRetryStoppingTotalLinear_stable_id
    (h : DensityOperator QubitSpace) (target : ZMod 8) (remaining : Nat) :
    ∀ (position : ZMod 8) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      traceNorm
        (hRetryStoppingTotalLinear h target LinearMap.id remaining position data -
          hRetryStoppingTotalLinear hMagicState target LinearMap.id remaining position data) ≤
        (remaining : Real) * (LinearMap.trace Complex QubitSpace data).re *
          traceNorm (h.toOperator - hMagicState.toOperator) := by
  intro position data hdata
  rw [hRetryStoppingTotalLinear_id h target remaining position,
    hRetryStoppingTotalLinear_id hMagicState target remaining position]
  exact hRetryAggregate_stable h target remaining position data hdata

/- Task 5d4e: literal H signed-word execution. -/

private noncomputable def runHSignedLetter
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letter : BK05SignedPhaseLetter (-Real.pi / 4)) (leaves : List BK05WordRawLeaf) :
    List BK05WordRawLeaf :=
  let execute (sign : BK05WordPolarity) (atom : BK05PhaseAtom (-Real.pi / 4)) :=
    match atom with
    | .h => runDeterministic (signedHTransport sign) leaves
    | .k => runDeterministic (signedKTransport sign) leaves
    | .phase => stoppingBind leaves
        (fun history ledger raw => runHPhaseFrom h sign blocks ledger history raw)
  match letter with
  | .positive atom => execute .normal atom
  | .negative atom => execute .inverse atom

private noncomputable def runHPhysicalLetters
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 4)) → List BK05WordRawLeaf → List BK05WordRawLeaf
  | [], leaves => leaves
  | letter :: tail, leaves =>
      runHPhysicalLetters h blocks tail (runHSignedLetter h blocks letter leaves)

private theorem runHPhysicalLetters_append
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    ∀ (left right : List (BK05SignedPhaseLetter (-Real.pi / 4))) (leaves : List BK05WordRawLeaf),
      runHPhysicalLetters h blocks (left ++ right) leaves =
        runHPhysicalLetters h blocks right (runHPhysicalLetters h blocks left leaves) := by
  intro left
  induction left with
  | nil =>
      intro right leaves
      rfl
  | cons letter tail ih =>
      intro right leaves
      simp [runHPhysicalLetters, ih]

private theorem runHPhysicalLetters_nil
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (leaves : List BK05WordRawLeaf) :
    runHPhysicalLetters h blocks ([] : List (BK05SignedPhaseLetter (-Real.pi / 4))) leaves = leaves :=
  rfl

private theorem runHPhysicalLetters_cons
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letter : BK05SignedPhaseLetter (-Real.pi / 4))
    (tail : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (leaves : List BK05WordRawLeaf) :
    runHPhysicalLetters h blocks (letter :: tail) leaves =
      runHPhysicalLetters h blocks tail (runHSignedLetter h blocks letter leaves) :=
  rfl

private noncomputable def runHSignedWord
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (leaves : List BK05WordRawLeaf) : List BK05WordRawLeaf :=
  runHPhysicalLetters h blocks letters.reverse leaves

private theorem runHSignedWord_nil
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (leaves : List BK05WordRawLeaf) :
    runHSignedWord h blocks ([] : List (BK05SignedPhaseLetter (-Real.pi / 4))) leaves = leaves :=
  rfl

private theorem runHSignedWord_cons
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (head : BK05SignedPhaseLetter (-Real.pi / 4))
    (tail : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (leaves : List BK05WordRawLeaf) :
    runHSignedWord h blocks (head :: tail) leaves =
      runHSignedLetter h blocks head (runHSignedWord h blocks tail leaves) := by
  calc
    runHSignedWord h blocks (head :: tail) leaves =
        runHPhysicalLetters h blocks (tail.reverse ++ [head]) leaves := by
          simp [runHSignedWord]
    _ = runHSignedLetter h blocks head
          (runHPhysicalLetters h blocks tail.reverse leaves) := by
          rw [runHPhysicalLetters_append]
          rfl
    _ = runHSignedLetter h blocks head (runHSignedWord h blocks tail leaves) := by
      rfl

private theorem runHSignedLetter_retains_phaseExhausted
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letter : BK05SignedPhaseLetter (-Real.pi / 4)) (leaves : List BK05WordRawLeaf)
    (leaf : BK05WordRawLeaf) (hmem : leaf ∈ leaves)
    (hstatus : leaf.status = .stoppedPhaseExhausted) :
    leaf ∈ runHSignedLetter h blocks letter leaves := by
  cases letter <;> rename_i atom <;> cases atom <;>
    exact stoppingBind_retains_phaseExhausted leaves _ leaf hmem hstatus

private theorem runHSignedLetter_retains_tPairExhausted
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letter : BK05SignedPhaseLetter (-Real.pi / 4)) (leaves : List BK05WordRawLeaf)
    (leaf : BK05WordRawLeaf) (hmem : leaf ∈ leaves)
    (hstatus : leaf.status = .stoppedTPairExhausted) :
    leaf ∈ runHSignedLetter h blocks letter leaves := by
  cases letter <;> rename_i atom <;> cases atom <;>
    exact stoppingBind_retains_tPairExhausted leaves _ leaf hmem hstatus

private theorem runHPhysicalLetters_retains_phaseExhausted
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) (leaves : List BK05WordRawLeaf)
      (leaf : BK05WordRawLeaf),
      leaf ∈ leaves → leaf.status = .stoppedPhaseExhausted →
        leaf ∈ runHPhysicalLetters h blocks letters leaves := by
  intro letters
  induction letters with
  | nil =>
      intro leaves leaf hmem hstatus
      exact hmem
  | cons letter tail ih =>
      intro leaves leaf hmem hstatus
      exact ih (runHSignedLetter h blocks letter leaves) leaf
        (runHSignedLetter_retains_phaseExhausted h blocks letter leaves leaf hmem hstatus)
        hstatus

private theorem runHPhysicalLetters_retains_tPairExhausted
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) (leaves : List BK05WordRawLeaf)
      (leaf : BK05WordRawLeaf),
      leaf ∈ leaves → leaf.status = .stoppedTPairExhausted →
        leaf ∈ runHPhysicalLetters h blocks letters leaves := by
  intro letters
  induction letters with
  | nil =>
      intro leaves leaf hmem hstatus
      exact hmem
  | cons letter tail ih =>
      intro leaves leaf hmem hstatus
      exact ih (runHSignedLetter h blocks letter leaves) leaf
        (runHSignedLetter_retains_tPairExhausted h blocks letter leaves leaf hmem hstatus)
        hstatus

private theorem runHSignedWord_retains_phaseExhausted
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) (leaves : List BK05WordRawLeaf)
    (leaf : BK05WordRawLeaf) (hmem : leaf ∈ leaves)
    (hstatus : leaf.status = .stoppedPhaseExhausted) :
    leaf ∈ runHSignedWord h blocks letters leaves := by
  exact runHPhysicalLetters_retains_phaseExhausted h blocks letters.reverse leaves leaf
    hmem hstatus

private theorem runHSignedWord_retains_tPairExhausted
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) (leaves : List BK05WordRawLeaf)
    (leaf : BK05WordRawLeaf) (hmem : leaf ∈ leaves)
    (hstatus : leaf.status = .stoppedTPairExhausted) :
    leaf ∈ runHSignedWord h blocks letters leaves := by
  exact runHPhysicalLetters_retains_tPairExhausted h blocks letters.reverse leaves leaf
    hmem hstatus

/- Task 5d4f: H signed-word aggregate compilation. -/

/- The aggregate compiler separates the prefixes that can execute another
literal letter from the terminal leaves that must be carried through unchanged. -/
private def wordRawStatusMatches (expected actual : BK05WordLeafStatus) : Bool :=
  match expected, actual with
  | .live, .live => true
  | .stoppedPhaseExhausted, .stoppedPhaseExhausted => true
  | .stoppedTPairExhausted, .stoppedTPairExhausted => true
  | _, _ => false

private def wordRawAggregateOfStatus (status : BK05WordLeafStatus)
    : List BK05WordRawLeaf → Operator QubitSpace
  | [] => 0
  | leaf :: leaves =>
      if wordRawStatusMatches status leaf.status then
        leaf.raw + wordRawAggregateOfStatus status leaves
      else wordRawAggregateOfStatus status leaves

private def wordRawLiveAggregate (leaves : List BK05WordRawLeaf) :
    Operator QubitSpace :=
  wordRawAggregateOfStatus .live leaves

private def wordRawStoppedAggregate (leaves : List BK05WordRawLeaf) :
    Operator QubitSpace :=
  wordRawAggregateOfStatus .stoppedPhaseExhausted leaves +
    wordRawAggregateOfStatus .stoppedTPairExhausted leaves

private theorem wordRawAggregateOfStatus_append (status : BK05WordLeafStatus)
    (left right : List BK05WordRawLeaf) :
    wordRawAggregateOfStatus status (left ++ right) =
      wordRawAggregateOfStatus status left + wordRawAggregateOfStatus status right := by
  induction left with
  | nil => simp [wordRawAggregateOfStatus]
  | cons leaf left ih =>
      by_cases hmatch : wordRawStatusMatches status leaf.status = true
      · simp [wordRawAggregateOfStatus, hmatch, ih]
        abel
      · simp [wordRawAggregateOfStatus, hmatch, ih]

private theorem wordRawLiveAggregate_append
    (left right : List BK05WordRawLeaf) :
    wordRawLiveAggregate (left ++ right) =
      wordRawLiveAggregate left + wordRawLiveAggregate right :=
  wordRawAggregateOfStatus_append .live left right

private theorem wordRawStoppedAggregate_append
    (left right : List BK05WordRawLeaf) :
    wordRawStoppedAggregate (left ++ right) =
      wordRawStoppedAggregate left + wordRawStoppedAggregate right := by
  simp only [wordRawStoppedAggregate, wordRawAggregateOfStatus_append]
  abel

private theorem wordRawLiveAggregate_nil :
    wordRawLiveAggregate [] = (0 : Operator QubitSpace) :=
  rfl

private theorem wordRawStoppedAggregate_nil :
    wordRawStoppedAggregate [] = (0 : Operator QubitSpace) := by
  simp [wordRawStoppedAggregate, wordRawAggregateOfStatus]

private theorem wordRawLiveAggregate_phaseExhausted_cons
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) (leaves : List BK05WordRawLeaf) :
    wordRawLiveAggregate (⟨.stoppedPhaseExhausted, history, ledger, raw⟩ :: leaves) =
      wordRawLiveAggregate leaves :=
  rfl

private theorem wordRawStoppedAggregate_phaseExhausted_cons
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) (leaves : List BK05WordRawLeaf) :
    wordRawStoppedAggregate (⟨.stoppedPhaseExhausted, history, ledger, raw⟩ :: leaves) =
      raw + wordRawStoppedAggregate leaves := by
  simp [wordRawStoppedAggregate, wordRawAggregateOfStatus, wordRawStatusMatches]
  abel

private theorem wordRawLiveAggregate_tPairExhausted_cons
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) (leaves : List BK05WordRawLeaf) :
    wordRawLiveAggregate (⟨.stoppedTPairExhausted, history, ledger, raw⟩ :: leaves) =
      wordRawLiveAggregate leaves :=
  rfl

private theorem wordRawStoppedAggregate_tPairExhausted_cons
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) (leaves : List BK05WordRawLeaf) :
    wordRawStoppedAggregate (⟨.stoppedTPairExhausted, history, ledger, raw⟩ :: leaves) =
      raw + wordRawStoppedAggregate leaves := by
  simp [wordRawStoppedAggregate, wordRawAggregateOfStatus, wordRawStatusMatches]
  abel

private theorem wordRawAggregate_partition (leaves : List BK05WordRawLeaf) :
    wordRawAggregate leaves =
      wordRawLiveAggregate leaves + wordRawStoppedAggregate leaves := by
  induction leaves with
  | nil => simp [wordRawAggregate, wordRawAggregateOfStatus, wordRawLiveAggregate,
      wordRawStoppedAggregate]
  | cons leaf leaves ih =>
      cases leaf with
      | mk status history ledger raw =>
          change raw + wordRawAggregate leaves = _
          rw [ih]
          cases status <;>
            simp [wordRawAggregateOfStatus, wordRawStatusMatches,
              wordRawLiveAggregate, wordRawStoppedAggregate] <;>
            abel

private theorem rawAggregateOfKind_cons (kind : BK05RawLeafKind)
    (leaf : BK05RawLeaf) (leaves : List BK05RawLeaf) :
    rawAggregateOfKind kind (leaf :: leaves) =
      if leaf.kind == kind then leaf.raw + rawAggregateOfKind kind leaves
      else rawAggregateOfKind kind leaves := by
  by_cases hkind : leaf.kind == kind <;>
    simp [rawAggregateOfKind, rawAggregate, hkind]

private theorem importRawLeaves_liveAggregate (leaves : List BK05RawLeaf) :
    wordRawLiveAggregate (importRawLeaves leaves) =
      rawAggregateOfKind .targetHit leaves := by
  induction leaves with
  | nil => simp [importRawLeaves, wordRawLiveAggregate, wordRawAggregateOfStatus,
      rawAggregateOfKind, rawAggregate]
  | cons leaf leaves ih =>
      cases leaf with
      | mk kind history ledger raw =>
          change wordRawAggregateOfStatus .live
            (importRawLeaf ⟨kind, history, ledger, raw⟩ :: importRawLeaves leaves) = _
          rw [rawAggregateOfKind_cons]
          have ih' : wordRawAggregateOfStatus .live (importRawLeaves leaves) =
              rawAggregateOfKind .targetHit leaves := by
            simpa [wordRawLiveAggregate] using ih
          cases kind <;>
            simp [importRawLeaf, importRawStatus,
              wordRawAggregateOfStatus, wordRawStatusMatches, ih']

private theorem importRawLeaves_phaseExhaustedAggregate (leaves : List BK05RawLeaf) :
    wordRawAggregateOfStatus .stoppedPhaseExhausted (importRawLeaves leaves) =
      rawAggregateOfKind .phaseExhausted leaves := by
  induction leaves with
  | nil => simp [importRawLeaves, wordRawAggregateOfStatus, rawAggregateOfKind,
      rawAggregate]
  | cons leaf leaves ih =>
      cases leaf with
      | mk kind history ledger raw =>
          change wordRawAggregateOfStatus .stoppedPhaseExhausted
            (importRawLeaf ⟨kind, history, ledger, raw⟩ :: importRawLeaves leaves) = _
          rw [rawAggregateOfKind_cons]
          cases kind <;>
            simp [importRawLeaf, importRawStatus, wordRawAggregateOfStatus,
              wordRawStatusMatches, ih]

private theorem importRawLeaves_tPairExhaustedAggregate (leaves : List BK05RawLeaf) :
    wordRawAggregateOfStatus .stoppedTPairExhausted (importRawLeaves leaves) =
      rawAggregateOfKind .tPairExhausted leaves := by
  induction leaves with
  | nil => simp [importRawLeaves, wordRawAggregateOfStatus, rawAggregateOfKind,
      rawAggregate]
  | cons leaf leaves ih =>
      cases leaf with
      | mk kind history ledger raw =>
          change wordRawAggregateOfStatus .stoppedTPairExhausted
            (importRawLeaf ⟨kind, history, ledger, raw⟩ :: importRawLeaves leaves) = _
          rw [rawAggregateOfKind_cons]
          cases kind <;>
            simp [importRawLeaf, importRawStatus, wordRawAggregateOfStatus,
              wordRawStatusMatches, ih]

private theorem hRetry_tPairExhausted_aggregate_zero
    (h : DensityOperator QubitSpace) (target : ZMod 8) (remaining : Nat) :
    ∀ (position : ZMod 8) (ledger : ResourceLedger BK05ResourceToken)
      (history : List Bool) (data : Operator QubitSpace),
      rawAggregateOfKind .tPairExhausted
        (hRetry h target remaining position ledger history data) = 0 := by
  induction remaining with
  | zero =>
      intro position ledger history data
      by_cases htarget : position = target <;>
        simp [hRetry, rawAggregateOfKind, rawAggregate, htarget]
  | succ remaining ih =>
      intro position ledger history data
      by_cases htarget : position = target
      · simp [hRetry, rawAggregateOfKind, rawAggregate, htarget]
      · rw [hRetry, if_neg htarget, rawAggregateOfKind_append]
        rw [ih (position + 1) (ledger + ({.h} : ResourceLedger BK05ResourceToken))
          (true :: history) (hStepRaw h true data),
          ih (position - 1) (ledger + ({.h} : ResourceLedger BK05ResourceToken))
            (false :: history) (hStepRaw h false data)]
        simp

private theorem stoppingBind_phaseExhausted_cons
    (continuation : List Bool → ResourceLedger BK05ResourceToken →
      Operator QubitSpace → List BK05WordRawLeaf)
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) (leaves : List BK05WordRawLeaf) :
    stoppingBind (⟨.stoppedPhaseExhausted, history, ledger, raw⟩ :: leaves) continuation =
      [⟨.stoppedPhaseExhausted, history, ledger, raw⟩] ++ stoppingBind leaves continuation :=
  rfl

private theorem stoppingBind_tPairExhausted_cons
    (continuation : List Bool → ResourceLedger BK05ResourceToken →
      Operator QubitSpace → List BK05WordRawLeaf)
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) (leaves : List BK05WordRawLeaf) :
    stoppingBind (⟨.stoppedTPairExhausted, history, ledger, raw⟩ :: leaves) continuation =
      [⟨.stoppedTPairExhausted, history, ledger, raw⟩] ++ stoppingBind leaves continuation :=
  rfl

private theorem stoppingBind_componentAggregate
    (success carrier : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (continuation : List Bool → ResourceLedger BK05ResourceToken →
      Operator QubitSpace → List BK05WordRawLeaf)
    (hcontinuation : ∀ history ledger raw,
      success (wordRawLiveAggregate (continuation history ledger raw)) +
        wordRawStoppedAggregate (continuation history ledger raw) = carrier raw) :
    ∀ leaves : List BK05WordRawLeaf,
      success (wordRawLiveAggregate (stoppingBind leaves continuation)) +
        wordRawStoppedAggregate (stoppingBind leaves continuation) =
          carrier (wordRawLiveAggregate leaves) + wordRawStoppedAggregate leaves := by
  intro leaves
  induction leaves with
  | nil =>
      simp [stoppingBind, wordRawLiveAggregate, wordRawStoppedAggregate,
        wordRawAggregateOfStatus]
  | cons leaf leaves ih =>
      cases leaf with
      | mk status history ledger raw =>
          cases status
          · change success (wordRawLiveAggregate
                (continuation history ledger raw ++ stoppingBind leaves continuation)) +
                wordRawStoppedAggregate
                  (continuation history ledger raw ++ stoppingBind leaves continuation) =
              carrier (raw + wordRawLiveAggregate leaves) +
                wordRawStoppedAggregate leaves
            calc
              success (wordRawLiveAggregate
                  (continuation history ledger raw ++ stoppingBind leaves continuation)) +
                  wordRawStoppedAggregate
                    (continuation history ledger raw ++ stoppingBind leaves continuation) =
                  (success (wordRawLiveAggregate (continuation history ledger raw)) +
                    wordRawStoppedAggregate (continuation history ledger raw)) +
                    (success (wordRawLiveAggregate (stoppingBind leaves continuation)) +
                      wordRawStoppedAggregate (stoppingBind leaves continuation)) := by
                    rw [wordRawLiveAggregate_append, wordRawStoppedAggregate_append, map_add]
                    abel
              _ = carrier raw +
                    (carrier (wordRawLiveAggregate leaves) + wordRawStoppedAggregate leaves) := by
                    rw [hcontinuation history ledger raw, ih]
              _ = carrier (raw + wordRawLiveAggregate leaves) +
                    wordRawStoppedAggregate leaves := by
                    rw [map_add]
                    abel
          · rw [stoppingBind_phaseExhausted_cons,
              wordRawLiveAggregate_append, wordRawStoppedAggregate_append,
              wordRawLiveAggregate_phaseExhausted_cons,
              wordRawStoppedAggregate_phaseExhausted_cons, map_add]
            calc
              success (wordRawLiveAggregate []) +
                  success (wordRawLiveAggregate (stoppingBind leaves continuation)) +
                  (raw + wordRawStoppedAggregate [] +
                    wordRawStoppedAggregate (stoppingBind leaves continuation)) =
                (success (wordRawLiveAggregate (stoppingBind leaves continuation)) +
                  wordRawStoppedAggregate (stoppingBind leaves continuation)) + raw := by
                    rw [wordRawLiveAggregate_nil, wordRawStoppedAggregate_nil, map_zero]
                    abel
              _ = (carrier (wordRawLiveAggregate leaves) +
                  wordRawStoppedAggregate leaves) + raw := by
                    rw [ih]
              _ = carrier
                    (wordRawLiveAggregate
                      (⟨.stoppedPhaseExhausted, history, ledger, raw⟩ :: leaves)) +
                    wordRawStoppedAggregate
                      (⟨.stoppedPhaseExhausted, history, ledger, raw⟩ :: leaves) := by
                    rw [wordRawLiveAggregate_phaseExhausted_cons,
                      wordRawStoppedAggregate_phaseExhausted_cons]
                    abel
          · rw [stoppingBind_tPairExhausted_cons,
              wordRawLiveAggregate_append, wordRawStoppedAggregate_append,
              wordRawLiveAggregate_tPairExhausted_cons,
              wordRawStoppedAggregate_tPairExhausted_cons, map_add]
            calc
              success (wordRawLiveAggregate []) +
                  success (wordRawLiveAggregate (stoppingBind leaves continuation)) +
                  (raw + wordRawStoppedAggregate [] +
                    wordRawStoppedAggregate (stoppingBind leaves continuation)) =
                (success (wordRawLiveAggregate (stoppingBind leaves continuation)) +
                  wordRawStoppedAggregate (stoppingBind leaves continuation)) + raw := by
                    rw [wordRawLiveAggregate_nil, wordRawStoppedAggregate_nil, map_zero]
                    abel
              _ = (carrier (wordRawLiveAggregate leaves) +
                  wordRawStoppedAggregate leaves) + raw := by
                    rw [ih]
              _ = carrier
                    (wordRawLiveAggregate
                      (⟨.stoppedTPairExhausted, history, ledger, raw⟩ :: leaves)) +
                    wordRawStoppedAggregate
                      (⟨.stoppedTPairExhausted, history, ledger, raw⟩ :: leaves) := by
                    rw [wordRawLiveAggregate_tPairExhausted_cons,
                      wordRawStoppedAggregate_tPairExhausted_cons]
                    abel

private theorem runDeterministic_componentAggregate
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (U : UnitaryTransport QubitSpace QubitSpace) (leaves : List BK05WordRawLeaf) :
    success (wordRawLiveAggregate (runDeterministic U leaves)) +
      wordRawStoppedAggregate (runDeterministic U leaves) =
        (success.comp U.conjOperatorLinearMap) (wordRawLiveAggregate leaves) +
          wordRawStoppedAggregate leaves := by
  have hcontinuation : ∀ history ledger raw,
      success (wordRawLiveAggregate (deterministicContinuation U history ledger raw)) +
        wordRawStoppedAggregate (deterministicContinuation U history ledger raw) =
          (success.comp U.conjOperatorLinearMap) raw := by
    intro history ledger raw
    simp [deterministicContinuation, deterministicLiveLeaf, wordRawLiveAggregate,
      wordRawStoppedAggregate, wordRawAggregateOfStatus, wordRawStatusMatches,
      LinearMap.comp_apply]
  simpa [runDeterministic] using stoppingBind_componentAggregate success
    (success.comp U.conjOperatorLinearMap) (deterministicContinuation U) hcontinuation leaves

private theorem runHPhaseFrom_componentAggregate
    (h : DensityOperator QubitSpace) (sign : BK05WordPolarity) (blocks : Nat)
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
    (raw : Operator QubitSpace) :
    success (wordRawLiveAggregate (runHPhaseFrom h sign blocks ledger history raw)) +
      wordRawStoppedAggregate (runHPhaseFrom h sign blocks ledger history raw) =
        hRetryStoppingTotalLinear h (hPhaseTarget sign) success (8 * blocks) 0 raw := by
  unfold runHPhaseFrom wordRawStoppedAggregate
  rw [importRawLeaves_liveAggregate, importRawLeaves_phaseExhaustedAggregate,
    importRawLeaves_tPairExhaustedAggregate,
    hRetry_tPairExhausted_aggregate_zero h (hPhaseTarget sign) (8 * blocks)
      0 ledger history raw,
    hRetryStoppingTotalLinear_apply h (hPhaseTarget sign) success (8 * blocks)
      0 ledger history raw]
  simp

private theorem runHPhaseStopping_componentAggregate
    (h : DensityOperator QubitSpace) (sign : BK05WordPolarity) (blocks : Nat)
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (leaves : List BK05WordRawLeaf) :
    success (wordRawLiveAggregate
      (stoppingBind leaves (fun history ledger raw =>
        runHPhaseFrom h sign blocks ledger history raw))) +
      wordRawStoppedAggregate
        (stoppingBind leaves (fun history ledger raw =>
          runHPhaseFrom h sign blocks ledger history raw)) =
        hRetryStoppingTotalLinear h (hPhaseTarget sign) success (8 * blocks) 0
          (wordRawLiveAggregate leaves) + wordRawStoppedAggregate leaves := by
  exact stoppingBind_componentAggregate success
    (hRetryStoppingTotalLinear h (hPhaseTarget sign) success (8 * blocks) 0)
    (fun history ledger raw => runHPhaseFrom h sign blocks ledger history raw)
    (fun history ledger raw =>
      runHPhaseFrom_componentAggregate h sign blocks success ledger history raw) leaves

private noncomputable def hSignedLetterTotalLinear
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letter : BK05SignedPhaseLetter (-Real.pi / 4))
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace :=
  let execute (sign : BK05WordPolarity) (atom : BK05PhaseAtom (-Real.pi / 4)) :=
    match atom with
    | .h => success.comp (signedHRawLinear sign)
    | .k => success.comp (signedKRawLinear sign)
    | .phase => hRetryStoppingTotalLinear h (hPhaseTarget sign) success (8 * blocks) 0
  match letter with
  | .positive atom => execute .normal atom
  | .negative atom => execute .inverse atom

private theorem runHSignedLetter_componentAggregate
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letter : BK05SignedPhaseLetter (-Real.pi / 4))
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (leaves : List BK05WordRawLeaf) :
    success (wordRawLiveAggregate (runHSignedLetter h blocks letter leaves)) +
      wordRawStoppedAggregate (runHSignedLetter h blocks letter leaves) =
        hSignedLetterTotalLinear h blocks letter success
          (wordRawLiveAggregate leaves) + wordRawStoppedAggregate leaves := by
  cases letter <;> rename_i atom <;> cases atom <;>
    simp only [runHSignedLetter, hSignedLetterTotalLinear] <;>
    first
    | simpa [signedHRawLinear, signedHTransport] using
        runDeterministic_componentAggregate success (signedHTransport .normal) leaves
    | simpa [signedKRawLinear, signedKTransport] using
        runDeterministic_componentAggregate success (signedKTransport .normal) leaves
    | simpa using runHPhaseStopping_componentAggregate h .normal blocks success leaves
    | simpa [signedHRawLinear, signedHTransport] using
        runDeterministic_componentAggregate success (signedHTransport .inverse) leaves
    | simpa [signedKRawLinear, signedKTransport] using
        runDeterministic_componentAggregate success (signedKTransport .inverse) leaves
    | simpa using runHPhaseStopping_componentAggregate h .inverse blocks success leaves

private noncomputable def hPhysicalLettersTotalLinear
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 4)) →
      (Operator QubitSpace →ₗ[Complex] Operator QubitSpace) →
        Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | [], success => success
  | letter :: tail, success =>
      hSignedLetterTotalLinear h blocks letter
        (hPhysicalLettersTotalLinear h blocks tail success)

private theorem runHPhysicalLetters_componentAggregate
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
      (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
      (leaves : List BK05WordRawLeaf),
      success (wordRawLiveAggregate (runHPhysicalLetters h blocks letters leaves)) +
        wordRawStoppedAggregate (runHPhysicalLetters h blocks letters leaves) =
          hPhysicalLettersTotalLinear h blocks letters success
            (wordRawLiveAggregate leaves) + wordRawStoppedAggregate leaves := by
  intro letters
  induction letters with
  | nil =>
      intro success leaves
      simp [runHPhysicalLetters, hPhysicalLettersTotalLinear]
  | cons letter tail ih =>
      intro success leaves
      calc
        success (wordRawLiveAggregate
            (runHPhysicalLetters h blocks (letter :: tail) leaves)) +
            wordRawStoppedAggregate
              (runHPhysicalLetters h blocks (letter :: tail) leaves) =
            hPhysicalLettersTotalLinear h blocks tail success
              (wordRawLiveAggregate (runHSignedLetter h blocks letter leaves)) +
                wordRawStoppedAggregate (runHSignedLetter h blocks letter leaves) := by
              simpa [runHPhysicalLetters] using
                ih success (runHSignedLetter h blocks letter leaves)
        _ = hSignedLetterTotalLinear h blocks letter
              (hPhysicalLettersTotalLinear h blocks tail success)
                (wordRawLiveAggregate leaves) + wordRawStoppedAggregate leaves :=
              runHSignedLetter_componentAggregate h blocks letter
                (hPhysicalLettersTotalLinear h blocks tail success) leaves
        _ = hPhysicalLettersTotalLinear h blocks (letter :: tail) success
              (wordRawLiveAggregate leaves) + wordRawStoppedAggregate leaves := by
              rfl

private noncomputable def hSignedWordTotalLinear
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace :=
  hPhysicalLettersTotalLinear h blocks letters.reverse success

private theorem runHSignedWord_componentAggregate
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (leaves : List BK05WordRawLeaf) :
    success (wordRawLiveAggregate (runHSignedWord h blocks letters leaves)) +
      wordRawStoppedAggregate (runHSignedWord h blocks letters leaves) =
        hSignedWordTotalLinear h blocks letters success
          (wordRawLiveAggregate leaves) + wordRawStoppedAggregate leaves := by
  simpa [runHSignedWord, hSignedWordTotalLinear] using
    runHPhysicalLetters_componentAggregate h blocks letters.reverse success leaves

private theorem runHSignedWord_live_aggregate
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) :
    wordRawAggregate (runHSignedWord h blocks letters
      [⟨.live, history, ledger, raw⟩]) =
        hSignedWordTotalLinear h blocks letters LinearMap.id raw := by
  calc
    wordRawAggregate (runHSignedWord h blocks letters
        [⟨.live, history, ledger, raw⟩]) =
        LinearMap.id (wordRawLiveAggregate (runHSignedWord h blocks letters
          [⟨.live, history, ledger, raw⟩])) +
          wordRawStoppedAggregate (runHSignedWord h blocks letters
            [⟨.live, history, ledger, raw⟩]) := by
              rw [wordRawAggregate_partition]
              rfl
    _ = hSignedWordTotalLinear h blocks letters LinearMap.id
          (wordRawLiveAggregate [⟨.live, history, ledger, raw⟩]) +
            wordRawStoppedAggregate [⟨.live, history, ledger, raw⟩] :=
          runHSignedWord_componentAggregate h blocks letters LinearMap.id
            [⟨.live, history, ledger, raw⟩]
    _ = hSignedWordTotalLinear h blocks letters LinearMap.id raw := by
          simp [wordRawLiveAggregate, wordRawStoppedAggregate,
            wordRawAggregateOfStatus, wordRawStatusMatches]

private theorem hSignedLetterTotalLinear_positive
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letter : BK05SignedPhaseLetter (-Real.pi / 4))
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (hsuccess : ∀ raw : Operator QubitSpace,
      LinearMap.IsPositive raw → LinearMap.IsPositive (success raw)) :
    ∀ raw : Operator QubitSpace, LinearMap.IsPositive raw →
      LinearMap.IsPositive (hSignedLetterTotalLinear h blocks letter success raw) := by
  intro raw hraw
  cases letter with
  | positive atom =>
      cases atom with
      | h =>
          simpa only [hSignedLetterTotalLinear, LinearMap.comp_apply] using
            hsuccess _ (signedHRawLinear_positive .normal raw hraw)
      | k =>
          simpa only [hSignedLetterTotalLinear, LinearMap.comp_apply] using
            hsuccess _ (signedKRawLinear_positive .normal raw hraw)
      | phase =>
          simpa only [hSignedLetterTotalLinear] using
            hRetryStoppingTotalLinear_positive h (hPhaseTarget .normal) success hsuccess
              (8 * blocks) 0 raw hraw
  | negative atom =>
      cases atom with
      | h =>
          simpa only [hSignedLetterTotalLinear, LinearMap.comp_apply] using
            hsuccess _ (signedHRawLinear_positive .inverse raw hraw)
      | k =>
          simpa only [hSignedLetterTotalLinear, LinearMap.comp_apply] using
            hsuccess _ (signedKRawLinear_positive .inverse raw hraw)
      | phase =>
          simpa only [hSignedLetterTotalLinear] using
            hRetryStoppingTotalLinear_positive h (hPhaseTarget .inverse) success hsuccess
              (8 * blocks) 0 raw hraw

private theorem hSignedLetterTotalLinear_trace
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letter : BK05SignedPhaseLetter (-Real.pi / 4))
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (hsuccess : ∀ raw : Operator QubitSpace,
      LinearMap.trace Complex QubitSpace (success raw) =
        LinearMap.trace Complex QubitSpace raw) :
    ∀ raw : Operator QubitSpace,
      LinearMap.trace Complex QubitSpace
        (hSignedLetterTotalLinear h blocks letter success raw) =
          LinearMap.trace Complex QubitSpace raw := by
  intro raw
  cases letter with
  | positive atom =>
      cases atom with
      | h =>
          simpa only [hSignedLetterTotalLinear, LinearMap.comp_apply] using
            (hsuccess _).trans (signedHRawLinear_trace .normal raw)
      | k =>
          simpa only [hSignedLetterTotalLinear, LinearMap.comp_apply] using
            (hsuccess _).trans (signedKRawLinear_trace .normal raw)
      | phase =>
          simpa only [hSignedLetterTotalLinear] using
            hRetryStoppingTotalLinear_trace h (hPhaseTarget .normal) success hsuccess
              (8 * blocks) 0 raw
  | negative atom =>
      cases atom with
      | h =>
          simpa only [hSignedLetterTotalLinear, LinearMap.comp_apply] using
            (hsuccess _).trans (signedHRawLinear_trace .inverse raw)
      | k =>
          simpa only [hSignedLetterTotalLinear, LinearMap.comp_apply] using
            (hsuccess _).trans (signedKRawLinear_trace .inverse raw)
      | phase =>
          simpa only [hSignedLetterTotalLinear] using
            hRetryStoppingTotalLinear_trace h (hPhaseTarget .inverse) success hsuccess
              (8 * blocks) 0 raw

private theorem hPhysicalLettersTotalLinear_positive
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
      (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace),
      (∀ raw : Operator QubitSpace,
        LinearMap.IsPositive raw → LinearMap.IsPositive (success raw)) →
        ∀ raw : Operator QubitSpace, LinearMap.IsPositive raw →
          LinearMap.IsPositive (hPhysicalLettersTotalLinear h blocks letters success raw) := by
  intro letters
  induction letters with
  | nil =>
      intro success hsuccess raw hraw
      exact hsuccess raw hraw
  | cons letter tail ih =>
      intro success hsuccess raw hraw
      exact hSignedLetterTotalLinear_positive h blocks letter
        (hPhysicalLettersTotalLinear h blocks tail success)
        (ih success hsuccess) raw hraw

private theorem hPhysicalLettersTotalLinear_trace
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
      (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace),
      (∀ raw : Operator QubitSpace,
        LinearMap.trace Complex QubitSpace (success raw) =
          LinearMap.trace Complex QubitSpace raw) →
        ∀ raw : Operator QubitSpace,
          LinearMap.trace Complex QubitSpace
            (hPhysicalLettersTotalLinear h blocks letters success raw) =
              LinearMap.trace Complex QubitSpace raw := by
  intro letters
  induction letters with
  | nil =>
      intro success hsuccess raw
      exact hsuccess raw
  | cons letter tail ih =>
      intro success hsuccess raw
      exact hSignedLetterTotalLinear_trace h blocks letter
        (hPhysicalLettersTotalLinear h blocks tail success)
        (ih success hsuccess) raw

private theorem hSignedWordTotalLinear_positive
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (raw : Operator QubitSpace) (hraw : LinearMap.IsPositive raw) :
    LinearMap.IsPositive (hSignedWordTotalLinear h blocks letters LinearMap.id raw) := by
  exact hPhysicalLettersTotalLinear_positive h blocks letters.reverse LinearMap.id
    (fun _ hpositive => hpositive) raw hraw

private theorem hSignedWordTotalLinear_trace
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (raw : Operator QubitSpace) :
    LinearMap.trace Complex QubitSpace
      (hSignedWordTotalLinear h blocks letters LinearMap.id raw) =
        LinearMap.trace Complex QubitSpace raw := by
  exact hPhysicalLettersTotalLinear_trace h blocks letters.reverse LinearMap.id
    (fun raw => rfl) raw

private theorem hSignedWordTotalLinear_mass
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (raw : Operator QubitSpace) :
    (LinearMap.trace Complex QubitSpace
      (hSignedWordTotalLinear h blocks letters LinearMap.id raw)).re =
        (LinearMap.trace Complex QubitSpace raw).re := by
  exact congrArg Complex.re (hSignedWordTotalLinear_trace h blocks letters raw)

private theorem wordRawMass_eq_aggregate_trace (leaves : List BK05WordRawLeaf) :
    wordRawMass leaves = (LinearMap.trace Complex QubitSpace
      (wordRawAggregate leaves)).re := by
  induction leaves with
  | nil => simp [wordRawMass, wordRawAggregate]
  | cons leaf leaves ih =>
      change (LinearMap.trace Complex QubitSpace leaf.raw).re + wordRawMass leaves = _
      rw [ih]
      change (LinearMap.trace Complex QubitSpace leaf.raw).re +
          (LinearMap.trace Complex QubitSpace (wordRawAggregate leaves)).re =
        (LinearMap.trace Complex QubitSpace
          (leaf.raw + wordRawAggregate leaves)).re
      rw [map_add]
      simp only [Complex.add_re]

private theorem runHSignedWord_live_mass
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) :
    wordRawMass (runHSignedWord h blocks letters [⟨.live, history, ledger, raw⟩]) =
      (LinearMap.trace Complex QubitSpace raw).re := by
  rw [wordRawMass_eq_aggregate_trace,
    runHSignedWord_live_aggregate h blocks letters history ledger raw,
    hSignedWordTotalLinear_mass]

/- Task 5d4g: H signed-word ideal action and source stability. -/

/- The two component maps keep executable target-hit prefixes distinct from
the phase-exhausted leaves that must remain in the literal output family. -/
private noncomputable def hWordLiveLinear
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 4)) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | [] => LinearMap.id
  | letter :: tail =>
      let tailLive := hWordLiveLinear h blocks tail
      match letter with
      | .positive .h => (signedHRawLinear .normal).comp tailLive
      | .positive .k => (signedKRawLinear .normal).comp tailLive
      | .positive .phase =>
          (hRetryTargetHitLinear h (hPhaseTarget .normal) (8 * blocks) 0).comp tailLive
      | .negative .h => (signedHRawLinear .inverse).comp tailLive
      | .negative .k => (signedKRawLinear .inverse).comp tailLive
      | .negative .phase =>
          (hRetryTargetHitLinear h (hPhaseTarget .inverse) (8 * blocks) 0).comp tailLive

private noncomputable def hWordPhaseStoppedLinear
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 4)) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | [] => 0
  | letter :: tail =>
      let tailLive := hWordLiveLinear h blocks tail
      match letter with
      | .positive .h => hWordPhaseStoppedLinear h blocks tail
      | .positive .k => hWordPhaseStoppedLinear h blocks tail
      | .positive .phase =>
          (hRetryPhaseExhaustedLinear h (hPhaseTarget .normal) (8 * blocks) 0).comp
            tailLive + hWordPhaseStoppedLinear h blocks tail
      | .negative .h => hWordPhaseStoppedLinear h blocks tail
      | .negative .k => hWordPhaseStoppedLinear h blocks tail
      | .negative .phase =>
          (hRetryPhaseExhaustedLinear h (hPhaseTarget .inverse) (8 * blocks) 0).comp
            tailLive + hWordPhaseStoppedLinear h blocks tail

private theorem stoppingBind_live_component
    (continuation : List Bool → ResourceLedger BK05ResourceToken →
      Operator QubitSpace → List BK05WordRawLeaf)
    (carrier : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (hcontinuation : ∀ history ledger raw,
      wordRawLiveAggregate (continuation history ledger raw) = carrier raw) :
    ∀ leaves : List BK05WordRawLeaf,
      wordRawLiveAggregate (stoppingBind leaves continuation) =
        carrier (wordRawLiveAggregate leaves) := by
  intro leaves
  induction leaves with
  | nil =>
      simp [stoppingBind, wordRawLiveAggregate, wordRawAggregateOfStatus]
  | cons leaf leaves ih =>
      cases leaf with
      | mk status history ledger raw =>
          cases status
          · change wordRawLiveAggregate
                (continuation history ledger raw ++ stoppingBind leaves continuation) =
              carrier (raw + wordRawLiveAggregate leaves)
            rw [wordRawLiveAggregate_append, hcontinuation history ledger raw, ih, map_add]
          · simpa [stoppingBind, stoppingStep, wordRawLiveAggregate,
              wordRawAggregateOfStatus, wordRawStatusMatches] using ih
          · simpa [stoppingBind, stoppingStep, wordRawLiveAggregate,
              wordRawAggregateOfStatus, wordRawStatusMatches] using ih

private theorem stoppingBind_phaseStopped_component
    (continuation : List Bool → ResourceLedger BK05ResourceToken →
      Operator QubitSpace → List BK05WordRawLeaf)
    (carrier : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (hcontinuation : ∀ history ledger raw,
      wordRawAggregateOfStatus .stoppedPhaseExhausted
        (continuation history ledger raw) = carrier raw) :
    ∀ leaves : List BK05WordRawLeaf,
      wordRawAggregateOfStatus .stoppedPhaseExhausted
        (stoppingBind leaves continuation) =
          carrier (wordRawLiveAggregate leaves) +
            wordRawAggregateOfStatus .stoppedPhaseExhausted leaves := by
  intro leaves
  induction leaves with
  | nil =>
      simp [stoppingBind, wordRawLiveAggregate, wordRawAggregateOfStatus]
  | cons leaf leaves ih =>
      cases leaf with
      | mk status history ledger raw =>
          cases status
          · change wordRawAggregateOfStatus .stoppedPhaseExhausted
                (continuation history ledger raw ++ stoppingBind leaves continuation) =
              carrier (raw + wordRawLiveAggregate leaves) +
                wordRawAggregateOfStatus .stoppedPhaseExhausted leaves
            rw [wordRawAggregateOfStatus_append,
              hcontinuation history ledger raw, ih, map_add]
            abel
          · rw [stoppingBind_phaseExhausted_cons,
              wordRawAggregateOfStatus_append, ih]
            simp [wordRawAggregateOfStatus, wordRawStatusMatches,
              wordRawLiveAggregate]
            abel
          · rw [stoppingBind_tPairExhausted_cons,
              wordRawAggregateOfStatus_append, ih]
            simp [wordRawAggregateOfStatus, wordRawStatusMatches,
              wordRawLiveAggregate]

private theorem deterministicContinuation_live_component
    (U : UnitaryTransport QubitSpace QubitSpace)
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) :
    wordRawLiveAggregate (deterministicContinuation U history ledger raw) =
      U.conjOperatorLinearMap raw := by
  simp [deterministicContinuation, deterministicLiveLeaf, wordRawLiveAggregate,
    wordRawAggregateOfStatus, wordRawStatusMatches]

private theorem deterministicContinuation_phaseStopped_component
    (U : UnitaryTransport QubitSpace QubitSpace)
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) :
    wordRawAggregateOfStatus .stoppedPhaseExhausted
      (deterministicContinuation U history ledger raw) = 0 := by
  simp [deterministicContinuation, deterministicLiveLeaf, wordRawAggregateOfStatus,
    wordRawStatusMatches]

private theorem runDeterministic_live_component
    (U : UnitaryTransport QubitSpace QubitSpace) (leaves : List BK05WordRawLeaf) :
    wordRawLiveAggregate (runDeterministic U leaves) =
      U.conjOperatorLinearMap (wordRawLiveAggregate leaves) := by
  exact stoppingBind_live_component (deterministicContinuation U) U.conjOperatorLinearMap
    (deterministicContinuation_live_component U) leaves

private theorem runDeterministic_phaseStopped_component
    (U : UnitaryTransport QubitSpace QubitSpace) (leaves : List BK05WordRawLeaf) :
    wordRawAggregateOfStatus .stoppedPhaseExhausted (runDeterministic U leaves) =
      wordRawAggregateOfStatus .stoppedPhaseExhausted leaves := by
  simpa [runDeterministic] using
    stoppingBind_phaseStopped_component (deterministicContinuation U) (0 :
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
      (deterministicContinuation_phaseStopped_component U) leaves

private theorem runHPhaseFrom_live_component
    (h : DensityOperator QubitSpace) (sign : BK05WordPolarity) (blocks : Nat)
    (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
    (raw : Operator QubitSpace) :
    wordRawLiveAggregate (runHPhaseFrom h sign blocks ledger history raw) =
      hRetryTargetHitLinear h (hPhaseTarget sign) (8 * blocks) 0 raw := by
  unfold runHPhaseFrom
  rw [importRawLeaves_liveAggregate]
  exact (hRetryTargetHitLinear_apply h (hPhaseTarget sign) (8 * blocks)
    0 ledger history raw).symm

private theorem runHPhaseFrom_phaseStopped_component
    (h : DensityOperator QubitSpace) (sign : BK05WordPolarity) (blocks : Nat)
    (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
    (raw : Operator QubitSpace) :
    wordRawAggregateOfStatus .stoppedPhaseExhausted
      (runHPhaseFrom h sign blocks ledger history raw) =
        hRetryPhaseExhaustedLinear h (hPhaseTarget sign) (8 * blocks) 0 raw := by
  unfold runHPhaseFrom
  rw [importRawLeaves_phaseExhaustedAggregate]
  exact (hRetryPhaseExhaustedLinear_apply h (hPhaseTarget sign) (8 * blocks)
    0 ledger history raw).symm

private theorem runHSignedLetter_live_component
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letter : BK05SignedPhaseLetter (-Real.pi / 4)) (leaves : List BK05WordRawLeaf) :
    wordRawLiveAggregate (runHSignedLetter h blocks letter leaves) =
      match letter with
      | .positive .h => signedHRawLinear .normal (wordRawLiveAggregate leaves)
      | .positive .k => signedKRawLinear .normal (wordRawLiveAggregate leaves)
      | .positive .phase =>
          hRetryTargetHitLinear h (hPhaseTarget .normal) (8 * blocks) 0
            (wordRawLiveAggregate leaves)
      | .negative .h => signedHRawLinear .inverse (wordRawLiveAggregate leaves)
      | .negative .k => signedKRawLinear .inverse (wordRawLiveAggregate leaves)
      | .negative .phase =>
          hRetryTargetHitLinear h (hPhaseTarget .inverse) (8 * blocks) 0
            (wordRawLiveAggregate leaves) := by
  cases letter <;> rename_i atom <;> cases atom <;>
    simp only [runHSignedLetter] <;>
    first
    | simpa [signedHRawLinear, signedHTransport] using
        runDeterministic_live_component (signedHTransport .normal) leaves
    | simpa [signedKRawLinear, signedKTransport] using
        runDeterministic_live_component (signedKTransport .normal) leaves
    | exact stoppingBind_live_component
        (fun history ledger raw => runHPhaseFrom h .normal blocks ledger history raw)
        (hRetryTargetHitLinear h (hPhaseTarget .normal) (8 * blocks) 0)
        (fun history ledger raw =>
          runHPhaseFrom_live_component h .normal blocks ledger history raw) leaves
    | simpa [signedHRawLinear, signedHTransport] using
        runDeterministic_live_component (signedHTransport .inverse) leaves
    | simpa [signedKRawLinear, signedKTransport] using
        runDeterministic_live_component (signedKTransport .inverse) leaves
    | exact stoppingBind_live_component
        (fun history ledger raw => runHPhaseFrom h .inverse blocks ledger history raw)
        (hRetryTargetHitLinear h (hPhaseTarget .inverse) (8 * blocks) 0)
        (fun history ledger raw =>
          runHPhaseFrom_live_component h .inverse blocks ledger history raw) leaves

private theorem runHSignedLetter_phaseStopped_component
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letter : BK05SignedPhaseLetter (-Real.pi / 4)) (leaves : List BK05WordRawLeaf) :
    wordRawAggregateOfStatus .stoppedPhaseExhausted
      (runHSignedLetter h blocks letter leaves) =
      match letter with
      | .positive .h => wordRawAggregateOfStatus .stoppedPhaseExhausted leaves
      | .positive .k => wordRawAggregateOfStatus .stoppedPhaseExhausted leaves
      | .positive .phase =>
          hRetryPhaseExhaustedLinear h (hPhaseTarget .normal) (8 * blocks) 0
            (wordRawLiveAggregate leaves) +
              wordRawAggregateOfStatus .stoppedPhaseExhausted leaves
      | .negative .h => wordRawAggregateOfStatus .stoppedPhaseExhausted leaves
      | .negative .k => wordRawAggregateOfStatus .stoppedPhaseExhausted leaves
      | .negative .phase =>
          hRetryPhaseExhaustedLinear h (hPhaseTarget .inverse) (8 * blocks) 0
            (wordRawLiveAggregate leaves) +
              wordRawAggregateOfStatus .stoppedPhaseExhausted leaves := by
  cases letter <;> rename_i atom <;> cases atom <;>
    simp only [runHSignedLetter] <;>
    first
    | exact runDeterministic_phaseStopped_component (signedHTransport .normal) leaves
    | exact runDeterministic_phaseStopped_component (signedKTransport .normal) leaves
    | exact stoppingBind_phaseStopped_component
        (fun history ledger raw => runHPhaseFrom h .normal blocks ledger history raw)
        (hRetryPhaseExhaustedLinear h (hPhaseTarget .normal) (8 * blocks) 0)
        (fun history ledger raw =>
          runHPhaseFrom_phaseStopped_component h .normal blocks ledger history raw) leaves
    | exact runDeterministic_phaseStopped_component (signedHTransport .inverse) leaves
    | exact runDeterministic_phaseStopped_component (signedKTransport .inverse) leaves
    | exact stoppingBind_phaseStopped_component
        (fun history ledger raw => runHPhaseFrom h .inverse blocks ledger history raw)
        (hRetryPhaseExhaustedLinear h (hPhaseTarget .inverse) (8 * blocks) 0)
        (fun history ledger raw =>
          runHPhaseFrom_phaseStopped_component h .inverse blocks ledger history raw) leaves

private theorem runHSignedWord_live_component
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) (leaves : List BK05WordRawLeaf) :
    wordRawAggregateOfStatus .live (runHSignedWord h blocks letters leaves) =
      hWordLiveLinear h blocks letters (wordRawAggregateOfStatus .live leaves) := by
  induction letters with
  | nil => rfl
  | cons head tail ih =>
      have htailLive :
          wordRawLiveAggregate (runHSignedWord h blocks tail leaves) =
            hWordLiveLinear h blocks tail (wordRawLiveAggregate leaves) := by
        simpa [wordRawLiveAggregate] using ih
      rw [runHSignedWord_cons]
      change wordRawLiveAggregate
          (runHSignedLetter h blocks head (runHSignedWord h blocks tail leaves)) =
        hWordLiveLinear h blocks (head :: tail) (wordRawLiveAggregate leaves)
      rw [runHSignedLetter_live_component, htailLive]
      cases head <;> rename_i atom <;> cases atom <;>
        rfl

private theorem runHSignedWord_phaseStopped_component
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) (leaves : List BK05WordRawLeaf) :
    wordRawAggregateOfStatus .stoppedPhaseExhausted
      (runHSignedWord h blocks letters leaves) =
        hWordPhaseStoppedLinear h blocks letters (wordRawAggregateOfStatus .live leaves) +
          wordRawAggregateOfStatus .stoppedPhaseExhausted leaves := by
  induction letters with
  | nil => simp [runHSignedWord, runHPhysicalLetters, hWordPhaseStoppedLinear]
  | cons head tail ih =>
      have htailLive :
          wordRawLiveAggregate (runHSignedWord h blocks tail leaves) =
            hWordLiveLinear h blocks tail (wordRawLiveAggregate leaves) := by
        simpa [wordRawLiveAggregate] using
          runHSignedWord_live_component h blocks tail leaves
      rw [runHSignedWord_cons, runHSignedLetter_phaseStopped_component, ih, htailLive]
      cases head <;> rename_i atom <;> cases atom <;>
        simp [hWordPhaseStoppedLinear, wordRawLiveAggregate, LinearMap.add_apply,
          LinearMap.comp_apply]
      all_goals abel

private theorem runHSignedWord_phaseStopped_retains
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) (leaves : List BK05WordRawLeaf)
    (leaf : BK05WordRawLeaf) (hmem : leaf ∈ leaves)
    (hstatus : leaf.status = .stoppedPhaseExhausted) :
    leaf ∈ runHSignedWord h blocks letters leaves :=
  runHSignedWord_retains_phaseExhausted h blocks letters leaves leaf hmem hstatus

private theorem hPhysicalLettersTotalLinear_append
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    ∀ (left right : List (BK05SignedPhaseLetter (-Real.pi / 4)))
      (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace),
      hPhysicalLettersTotalLinear h blocks (left ++ right) success =
        hPhysicalLettersTotalLinear h blocks left
          (hPhysicalLettersTotalLinear h blocks right success) := by
  intro left
  induction left with
  | nil =>
      intro right success
      rfl
  | cons letter tail ih =>
      intro right success
      simp only [List.cons_append, hPhysicalLettersTotalLinear]
      rw [ih]

private theorem hSignedWordTotalLinear_cons
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (head : BK05SignedPhaseLetter (-Real.pi / 4))
    (tail : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    hSignedWordTotalLinear h blocks (head :: tail) success =
      hSignedWordTotalLinear h blocks tail
        (hSignedLetterTotalLinear h blocks head success) := by
  simp only [hSignedWordTotalLinear, List.reverse_cons]
  rw [hPhysicalLettersTotalLinear_append]
  rfl

private theorem hWord_component_total_with_success
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
      (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
      (raw : Operator QubitSpace),
      success (hWordLiveLinear h blocks letters raw) +
        hWordPhaseStoppedLinear h blocks letters raw =
          hSignedWordTotalLinear h blocks letters success raw := by
  intro letters
  induction letters with
  | nil =>
      intro success raw
      simp [hWordLiveLinear, hWordPhaseStoppedLinear, hSignedWordTotalLinear,
        hPhysicalLettersTotalLinear]
  | cons head tail ih =>
      intro success raw
      rw [hSignedWordTotalLinear_cons]
      cases head with
      | positive atom =>
          cases atom with
          | h =>
              change success
                    (signedHRawLinear .normal (hWordLiveLinear h blocks tail raw)) +
                    hWordPhaseStoppedLinear h blocks tail raw =
                  hSignedWordTotalLinear h blocks tail
                    (success.comp (signedHRawLinear .normal)) raw
              simpa only [LinearMap.comp_apply] using
                ih (success.comp (signedHRawLinear .normal)) raw
          | k =>
              change success
                    (signedKRawLinear .normal (hWordLiveLinear h blocks tail raw)) +
                    hWordPhaseStoppedLinear h blocks tail raw =
                  hSignedWordTotalLinear h blocks tail
                    (success.comp (signedKRawLinear .normal)) raw
              simpa only [LinearMap.comp_apply] using
                ih (success.comp (signedKRawLinear .normal)) raw
          | phase =>
              change success
                    (hRetryTargetHitLinear h (hPhaseTarget .normal) (8 * blocks) 0
                      (hWordLiveLinear h blocks tail raw)) +
                    (hRetryPhaseExhaustedLinear h (hPhaseTarget .normal) (8 * blocks) 0
                      (hWordLiveLinear h blocks tail raw) +
                        hWordPhaseStoppedLinear h blocks tail raw) =
                  hSignedWordTotalLinear h blocks tail
                    (hRetryStoppingTotalLinear h (hPhaseTarget .normal) success
                      (8 * blocks) 0) raw
              calc
                success
                    (hRetryTargetHitLinear h (hPhaseTarget .normal) (8 * blocks) 0
                      (hWordLiveLinear h blocks tail raw)) +
                    (hRetryPhaseExhaustedLinear h (hPhaseTarget .normal) (8 * blocks) 0
                      (hWordLiveLinear h blocks tail raw) +
                        hWordPhaseStoppedLinear h blocks tail raw) =
                    hRetryStoppingTotalLinear h (hPhaseTarget .normal) success
                      (8 * blocks) 0 (hWordLiveLinear h blocks tail raw) +
                        hWordPhaseStoppedLinear h blocks tail raw := by
                          rw [hRetryStoppingTotalLinear_split, LinearMap.add_apply,
                            LinearMap.comp_apply]
                          abel
                _ = hSignedWordTotalLinear h blocks tail
                      (hRetryStoppingTotalLinear h (hPhaseTarget .normal) success
                        (8 * blocks) 0) raw :=
                    ih (hRetryStoppingTotalLinear h (hPhaseTarget .normal) success
                      (8 * blocks) 0) raw
      | negative atom =>
          cases atom with
          | h =>
              change success
                    (signedHRawLinear .inverse (hWordLiveLinear h blocks tail raw)) +
                    hWordPhaseStoppedLinear h blocks tail raw =
                  hSignedWordTotalLinear h blocks tail
                    (success.comp (signedHRawLinear .inverse)) raw
              simpa only [LinearMap.comp_apply] using
                ih (success.comp (signedHRawLinear .inverse)) raw
          | k =>
              change success
                    (signedKRawLinear .inverse (hWordLiveLinear h blocks tail raw)) +
                    hWordPhaseStoppedLinear h blocks tail raw =
                  hSignedWordTotalLinear h blocks tail
                    (success.comp (signedKRawLinear .inverse)) raw
              simpa only [LinearMap.comp_apply] using
                ih (success.comp (signedKRawLinear .inverse)) raw
          | phase =>
              change success
                    (hRetryTargetHitLinear h (hPhaseTarget .inverse) (8 * blocks) 0
                      (hWordLiveLinear h blocks tail raw)) +
                    (hRetryPhaseExhaustedLinear h (hPhaseTarget .inverse) (8 * blocks) 0
                      (hWordLiveLinear h blocks tail raw) +
                        hWordPhaseStoppedLinear h blocks tail raw) =
                  hSignedWordTotalLinear h blocks tail
                    (hRetryStoppingTotalLinear h (hPhaseTarget .inverse) success
                      (8 * blocks) 0) raw
              calc
                success
                    (hRetryTargetHitLinear h (hPhaseTarget .inverse) (8 * blocks) 0
                      (hWordLiveLinear h blocks tail raw)) +
                    (hRetryPhaseExhaustedLinear h (hPhaseTarget .inverse) (8 * blocks) 0
                      (hWordLiveLinear h blocks tail raw) +
                        hWordPhaseStoppedLinear h blocks tail raw) =
                    hRetryStoppingTotalLinear h (hPhaseTarget .inverse) success
                      (8 * blocks) 0 (hWordLiveLinear h blocks tail raw) +
                        hWordPhaseStoppedLinear h blocks tail raw := by
                          rw [hRetryStoppingTotalLinear_split, LinearMap.add_apply,
                            LinearMap.comp_apply]
                          abel
                _ = hSignedWordTotalLinear h blocks tail
                      (hRetryStoppingTotalLinear h (hPhaseTarget .inverse) success
                        (8 * blocks) 0) raw :=
                    ih (hRetryStoppingTotalLinear h (hPhaseTarget .inverse) success
                      (8 * blocks) 0) raw

private theorem hWord_components_total
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (raw : Operator QubitSpace) :
    hWordLiveLinear h blocks letters raw + hWordPhaseStoppedLinear h blocks letters raw =
      hSignedWordTotalLinear h blocks letters LinearMap.id raw := by
  simpa using hWord_component_total_with_success h blocks letters LinearMap.id raw

private theorem hWordLiveLinear_positive
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
      (raw : Operator QubitSpace),
      LinearMap.IsPositive raw →
        LinearMap.IsPositive (hWordLiveLinear h blocks letters raw) := by
  intro letters
  induction letters with
  | nil =>
      intro raw hraw
      simpa [hWordLiveLinear] using hraw
  | cons head tail ih =>
      intro raw hraw
      cases head with
      | positive atom =>
          cases atom with
          | h =>
              simpa [hWordLiveLinear, LinearMap.comp_apply] using
                signedHRawLinear_positive .normal _ (ih raw hraw)
          | k =>
              simpa [hWordLiveLinear, LinearMap.comp_apply] using
                signedKRawLinear_positive .normal _ (ih raw hraw)
          | phase =>
              simpa [hWordLiveLinear, LinearMap.comp_apply] using
                hRetryTargetHitLinear_positive h (hPhaseTarget .normal) (8 * blocks) 0 _
                  (ih raw hraw)
      | negative atom =>
          cases atom with
          | h =>
              simpa [hWordLiveLinear, LinearMap.comp_apply] using
                signedHRawLinear_positive .inverse _ (ih raw hraw)
          | k =>
              simpa [hWordLiveLinear, LinearMap.comp_apply] using
                signedKRawLinear_positive .inverse _ (ih raw hraw)
          | phase =>
              simpa [hWordLiveLinear, LinearMap.comp_apply] using
                hRetryTargetHitLinear_positive h (hPhaseTarget .inverse) (8 * blocks) 0 _
                  (ih raw hraw)

private theorem hWordPhaseStoppedLinear_positive
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
      (raw : Operator QubitSpace),
      LinearMap.IsPositive raw →
        LinearMap.IsPositive (hWordPhaseStoppedLinear h blocks letters raw) := by
  intro letters
  induction letters with
  | nil =>
      intro raw hraw
      simp [hWordPhaseStoppedLinear]
  | cons head tail ih =>
      intro raw hraw
      cases head with
      | positive atom =>
          cases atom with
          | h => simpa [hWordPhaseStoppedLinear] using ih raw hraw
          | k => simpa [hWordPhaseStoppedLinear] using ih raw hraw
          | phase =>
              simpa [hWordPhaseStoppedLinear, hWordLiveLinear, LinearMap.add_apply,
                LinearMap.comp_apply] using
                (hRetryPhaseExhaustedLinear_positive h (hPhaseTarget .normal)
                  (8 * blocks) 0 _ (hWordLiveLinear_positive h blocks tail raw hraw)).add
                  (ih raw hraw)
      | negative atom =>
          cases atom with
          | h => simpa [hWordPhaseStoppedLinear] using ih raw hraw
          | k => simpa [hWordPhaseStoppedLinear] using ih raw hraw
          | phase =>
              simpa [hWordPhaseStoppedLinear, hWordLiveLinear, LinearMap.add_apply,
                LinearMap.comp_apply] using
                (hRetryPhaseExhaustedLinear_positive h (hPhaseTarget .inverse)
                  (8 * blocks) 0 _ (hWordLiveLinear_positive h blocks tail raw hraw)).add
                  (ih raw hraw)

private theorem hWord_component_trace
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (raw : Operator QubitSpace) :
    LinearMap.trace Complex QubitSpace (hWordLiveLinear h blocks letters raw) +
      LinearMap.trace Complex QubitSpace (hWordPhaseStoppedLinear h blocks letters raw) =
        LinearMap.trace Complex QubitSpace raw := by
  calc
    LinearMap.trace Complex QubitSpace (hWordLiveLinear h blocks letters raw) +
        LinearMap.trace Complex QubitSpace (hWordPhaseStoppedLinear h blocks letters raw) =
        LinearMap.trace Complex QubitSpace
          (hWordLiveLinear h blocks letters raw + hWordPhaseStoppedLinear h blocks letters raw) := by
            rw [map_add]
    _ = LinearMap.trace Complex QubitSpace
          (hSignedWordTotalLinear h blocks letters LinearMap.id raw) := by
            rw [hWord_components_total]
    _ = LinearMap.trace Complex QubitSpace raw :=
      hSignedWordTotalLinear_trace h blocks letters raw

private theorem hWord_component_trace_nonneg
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (raw : Operator QubitSpace) (hraw : LinearMap.IsPositive raw) :
    0 ≤ (LinearMap.trace Complex QubitSpace (hWordLiveLinear h blocks letters raw)).re ∧
      0 ≤ (LinearMap.trace Complex QubitSpace
        (hWordPhaseStoppedLinear h blocks letters raw)).re := by
  constructor
  · exact (Complex.nonneg_iff.mp
      (hWordLiveLinear_positive h blocks letters raw hraw).trace_nonneg).1
  · exact (Complex.nonneg_iff.mp
      (hWordPhaseStoppedLinear_positive h blocks letters raw hraw).trace_nonneg).1

private theorem hWord_live_trace_le
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (raw : Operator QubitSpace) (hraw : LinearMap.IsPositive raw) :
    (LinearMap.trace Complex QubitSpace (hWordLiveLinear h blocks letters raw)).re ≤
      (LinearMap.trace Complex QubitSpace raw).re := by
  have hstopped := (hWord_component_trace_nonneg h blocks letters raw hraw).2
  have htrace := congrArg Complex.re (hWord_component_trace h blocks letters raw)
  simp only [Complex.add_re] at htrace
  linarith

/- Task 5d4g checkpoint 3: H signed-word ideal action and source stability. -/

/- Task 5d4g checkpoint 3A: fixed-angle H live ideal action. -/

/-- The fixed-angle state action underneath each ideal H-word letter. -/
private noncomputable def hFixedIdealLetterStateLinear :
    BK05SignedPhaseLetter (-Real.pi / 4) → Operator QubitSpace
  | .positive .h => (signedHTransport .normal).toLinearEquiv.toLinearMap
  | .positive .k => (signedKTransport .normal).toLinearEquiv.toLinearMap
  | .positive .phase => phaseCycleTargetAction 8 (hPhaseTarget .normal)
  | .negative .h => (signedHTransport .inverse).toLinearEquiv.toLinearMap
  | .negative .k => (signedKTransport .inverse).toLinearEquiv.toLinearMap
  | .negative .phase => phaseCycleTargetAction 8 (hPhaseTarget .inverse)

/-- The operator-space action induced by one fixed-angle ideal H-word letter. -/
private noncomputable def hFixedIdealLetterLinear :
    BK05SignedPhaseLetter (-Real.pi / 4) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | .positive .h => signedHRawLinear .normal
  | .positive .k => signedKRawLinear .normal
  | .positive .phase => phaseCycleTargetChannel 8 (hPhaseTarget .normal)
  | .negative .h => signedHRawLinear .inverse
  | .negative .k => signedKRawLinear .inverse
  | .negative .phase => phaseCycleTargetChannel 8 (hPhaseTarget .inverse)

/-- Each fixed-angle state action is exactly the evaluation of its signed
tagged letter.  The inverse phase branch retains the order-eight full-turn
route rather than replacing it by an angle-polymorphic shortcut. -/
private theorem hFixedIdealLetterStateLinear_eval
    (letter : BK05SignedPhaseLetter (-Real.pi / 4)) :
    hFixedIdealLetterStateLinear letter =
      Matrix.toEuclideanLin
        ((BK05SignedPhaseLetter.eval (-Real.pi / 4) letter :
          Matrix (Fin 2) (Fin 2) Complex)) := by
  cases letter with
  | positive atom =>
      cases atom with
      | h =>
          simpa [hFixedIdealLetterStateLinear, signedHLetter,
            BK05SignedPhaseLetter.eval, BK05PhaseAtom.eval] using
            signedHTransport_operator_eq_eval (-Real.pi / 4) .normal
      | k =>
          simpa [hFixedIdealLetterStateLinear, signedKLetter,
            BK05SignedPhaseLetter.eval, BK05PhaseAtom.eval] using
            signedKTransport_operator_eq_eval (-Real.pi / 4) .normal
      | phase =>
          apply LinearMap.ext
          intro psi
          change phaseCycleTargetAction 8 (1 : ZMod 8) psi =
            Matrix.toEuclideanLin
              ((phaseShiftGate (-Real.pi / 4) : UnitaryGate (Fin 2)) :
                Matrix (Fin 2) (Fin 2) Complex) psi
          rw [IdealResourceUniversality.hResource_targetAction_one]
          simpa only [OneQubitMagic.phaseShiftTransport_apply] using
            (phaseShiftGate_apply (-Real.pi / 4) psi).symm
  | negative atom =>
      cases atom with
      | h =>
          simpa [hFixedIdealLetterStateLinear, signedHLetter,
            BK05SignedPhaseLetter.eval, BK05PhaseAtom.eval] using
            signedHTransport_operator_eq_eval (-Real.pi / 4) .inverse
      | k =>
          simpa [hFixedIdealLetterStateLinear, signedKLetter,
            BK05SignedPhaseLetter.eval, BK05PhaseAtom.eval] using
            signedKTransport_operator_eq_eval (-Real.pi / 4) .inverse
      | phase =>
          apply LinearMap.ext
          intro psi
          change phaseCycleTargetAction 8 (-1 : ZMod 8) psi =
            Matrix.toEuclideanLin
              (((phaseShiftGate (-Real.pi / 4))⁻¹ : UnitaryGate (Fin 2)) :
                Matrix (Fin 2) (Fin 2) Complex) psi
          have hangle : -(-Real.pi / 4) = Real.pi / 4 := by ring
          rw [phaseCycleTargetAction_eight_neg_one, phaseShiftGate_inverse, hangle]
          simpa only [OneQubitMagic.phaseShiftTransport_apply] using
            (phaseShiftGate_apply (Real.pi / 4) psi).symm

private noncomputable def hFixedIdealWordLinear :
    List (BK05SignedPhaseLetter (-Real.pi / 4)) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | [] => LinearMap.id
  | letter :: tail => (hFixedIdealLetterLinear letter).comp (hFixedIdealWordLinear tail)

private theorem hFixedIdealWordLinear_positive :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
      (data : Operator QubitSpace),
      LinearMap.IsPositive data → LinearMap.IsPositive (hFixedIdealWordLinear letters data) := by
  intro letters
  induction letters with
  | nil =>
      intro data hdata
      simpa [hFixedIdealWordLinear] using hdata
  | cons letter tail ih =>
      intro data hdata
      cases letter with
      | positive atom =>
          cases atom with
          | h =>
              exact signedHRawLinear_positive .normal _ (ih data hdata)
          | k =>
              exact signedKRawLinear_positive .normal _ (ih data hdata)
          | phase =>
              simpa [hFixedIdealWordLinear, hFixedIdealLetterLinear,
                phaseCycleTargetChannel, LinearMap.comp_apply] using
                (OneQubitMagic.phaseShiftTransport
                  (phaseCycleAngle 8 * (hPhaseTarget .normal).val)).isPositive_conjOperator
                  (ih data hdata)
      | negative atom =>
          cases atom with
          | h =>
              exact signedHRawLinear_positive .inverse _ (ih data hdata)
          | k =>
              exact signedKRawLinear_positive .inverse _ (ih data hdata)
          | phase =>
              simpa [hFixedIdealWordLinear, hFixedIdealLetterLinear,
                phaseCycleTargetChannel, LinearMap.comp_apply] using
                (OneQubitMagic.phaseShiftTransport
                  (phaseCycleAngle 8 * (hPhaseTarget .inverse).val)).isPositive_conjOperator
                  (ih data hdata)

private theorem hFixedIdealLetterLinear_trace
    (letter : BK05SignedPhaseLetter (-Real.pi / 4))
    (data : Operator QubitSpace) :
    LinearMap.trace Complex QubitSpace (hFixedIdealLetterLinear letter data) =
      LinearMap.trace Complex QubitSpace data := by
  cases letter with
  | positive atom =>
      cases atom with
      | h => simpa [hFixedIdealLetterLinear] using signedHRawLinear_trace .normal data
      | k => simpa [hFixedIdealLetterLinear] using signedKRawLinear_trace .normal data
      | phase =>
          simpa [hFixedIdealLetterLinear] using
            phaseCycleTargetChannel_trace 8 (hPhaseTarget .normal) data
  | negative atom =>
      cases atom with
      | h => simpa [hFixedIdealLetterLinear] using signedHRawLinear_trace .inverse data
      | k => simpa [hFixedIdealLetterLinear] using signedKRawLinear_trace .inverse data
      | phase =>
          simpa [hFixedIdealLetterLinear] using
            phaseCycleTargetChannel_trace 8 (hPhaseTarget .inverse) data

private theorem hFixedIdealWordLinear_trace :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
      (data : Operator QubitSpace),
      LinearMap.trace Complex QubitSpace (hFixedIdealWordLinear letters data) =
        LinearMap.trace Complex QubitSpace data := by
  intro letters
  induction letters with
  | nil =>
      intro data
      rfl
  | cons letter tail ih =>
      intro data
      simpa [hFixedIdealWordLinear, LinearMap.comp_apply] using
        (hFixedIdealLetterLinear_trace letter
          (hFixedIdealWordLinear tail data)).trans (ih data)

private noncomputable def hWordLiveCoeff (blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 4)) → Complex
  | [] => 1
  | .positive .h :: tail => hWordLiveCoeff blocks tail
  | .positive .k :: tail => hWordLiveCoeff blocks tail
  | .positive .phase :: tail =>
      (hTargetHitCoeff (hPhaseTarget .normal) (8 * blocks) 0 : Complex) *
        hWordLiveCoeff blocks tail
  | .negative .h :: tail => hWordLiveCoeff blocks tail
  | .negative .k :: tail => hWordLiveCoeff blocks tail
  | .negative .phase :: tail =>
      (hTargetHitCoeff (hPhaseTarget .inverse) (8 * blocks) 0 : Complex) *
        hWordLiveCoeff blocks tail

private def hWordLiveProbability (blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 4)) → Real
  | [] => 1
  | .positive .h :: tail => hWordLiveProbability blocks tail
  | .positive .k :: tail => hWordLiveProbability blocks tail
  | .positive .phase :: tail =>
      hTargetHitCoeff (hPhaseTarget .normal) (8 * blocks) 0 *
        hWordLiveProbability blocks tail
  | .negative .h :: tail => hWordLiveProbability blocks tail
  | .negative .k :: tail => hWordLiveProbability blocks tail
  | .negative .phase :: tail =>
      hTargetHitCoeff (hPhaseTarget .inverse) (8 * blocks) 0 *
        hWordLiveProbability blocks tail

private theorem hWordLiveCoeff_eq_probability (blocks : Nat) :
    ∀ letters : List (BK05SignedPhaseLetter (-Real.pi / 4)),
      hWordLiveCoeff blocks letters =
        (hWordLiveProbability blocks letters : Complex) := by
  intro letters
  induction letters with
  | nil => simp [hWordLiveCoeff, hWordLiveProbability]
  | cons letter tail ih =>
      cases letter with
      | positive atom =>
          cases atom <;>
            simp [hWordLiveCoeff, hWordLiveProbability, ih]
      | negative atom =>
          cases atom <;>
            simp [hWordLiveCoeff, hWordLiveProbability, ih]

private theorem hWordLiveLinear_ideal_action
    (blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
      (data : Operator QubitSpace),
      LinearMap.IsPositive data →
        hWordLiveLinear hMagicState blocks letters data =
          hWordLiveCoeff blocks letters • hFixedIdealWordLinear letters data := by
  intro letters
  induction letters with
  | nil =>
      intro data hdata
      simp [hWordLiveLinear, hWordLiveCoeff, hFixedIdealWordLinear]
  | cons letter tail ih =>
      intro data hdata
      have htailPositive : LinearMap.IsPositive (hFixedIdealWordLinear tail data) :=
        hFixedIdealWordLinear_positive tail data hdata
      cases letter with
      | positive atom =>
          cases atom with
          | h =>
              change signedHRawLinear .normal
                    (hWordLiveLinear hMagicState blocks tail data) =
                  hWordLiveCoeff blocks tail • signedHRawLinear .normal
                    (hFixedIdealWordLinear tail data)
              rw [ih data hdata]
              exact (signedHRawLinear .normal).map_smul _ _
          | k =>
              change signedKRawLinear .normal
                    (hWordLiveLinear hMagicState blocks tail data) =
                  hWordLiveCoeff blocks tail • signedKRawLinear .normal
                    (hFixedIdealWordLinear tail data)
              rw [ih data hdata]
              exact (signedKRawLinear .normal).map_smul _ _
          | phase =>
              change hRetryTargetHitLinear hMagicState (hPhaseTarget .normal)
                    (8 * blocks) 0 (hWordLiveLinear hMagicState blocks tail data) =
                  ((hTargetHitCoeff (hPhaseTarget .normal) (8 * blocks) 0 : Complex) *
                    hWordLiveCoeff blocks tail) •
                    phaseCycleTargetChannel 8 (hPhaseTarget .normal)
                      (hFixedIdealWordLinear tail data)
              calc
                hRetryTargetHitLinear hMagicState (hPhaseTarget .normal) (8 * blocks) 0
                    (hWordLiveLinear hMagicState blocks tail data) =
                    hRetryTargetHitLinear hMagicState (hPhaseTarget .normal) (8 * blocks) 0
                      (hWordLiveCoeff blocks tail • hFixedIdealWordLinear tail data) := by
                        rw [ih data hdata]
                _ = hWordLiveCoeff blocks tail •
                    hRetryTargetHitLinear hMagicState (hPhaseTarget .normal) (8 * blocks) 0
                      (hFixedIdealWordLinear tail data) :=
                  (hRetryTargetHitLinear hMagicState (hPhaseTarget .normal)
                    (8 * blocks) 0).map_smul _ _
                _ = hWordLiveCoeff blocks tail •
                    rawAggregateOfKind .targetHit
                      (hRetry hMagicState (hPhaseTarget .normal) (8 * blocks) 0 0 []
                        (hFixedIdealWordLinear tail data)) := by
                          rw [hRetryTargetHitLinear_apply]
                _ = hWordLiveCoeff blocks tail •
                    ((hTargetHitCoeff (hPhaseTarget .normal) (8 * blocks) 0 : Complex) •
                      phaseCycleTargetChannel 8 (hPhaseTarget .normal)
                        (hFixedIdealWordLinear tail data)) := by
                          rw [hRetry_ideal_targetHit_action _ _ 0 [] _ htailPositive]
                _ = ((hTargetHitCoeff (hPhaseTarget .normal) (8 * blocks) 0 : Complex) *
                    hWordLiveCoeff blocks tail) •
                    phaseCycleTargetChannel 8 (hPhaseTarget .normal)
                      (hFixedIdealWordLinear tail data) := by
                        rw [smul_smul]
                        ring
      | negative atom =>
          cases atom with
          | h =>
              change signedHRawLinear .inverse
                    (hWordLiveLinear hMagicState blocks tail data) =
                  hWordLiveCoeff blocks tail • signedHRawLinear .inverse
                    (hFixedIdealWordLinear tail data)
              rw [ih data hdata]
              exact (signedHRawLinear .inverse).map_smul _ _
          | k =>
              change signedKRawLinear .inverse
                    (hWordLiveLinear hMagicState blocks tail data) =
                  hWordLiveCoeff blocks tail • signedKRawLinear .inverse
                    (hFixedIdealWordLinear tail data)
              rw [ih data hdata]
              exact (signedKRawLinear .inverse).map_smul _ _
          | phase =>
              change hRetryTargetHitLinear hMagicState (hPhaseTarget .inverse)
                    (8 * blocks) 0 (hWordLiveLinear hMagicState blocks tail data) =
                  ((hTargetHitCoeff (hPhaseTarget .inverse) (8 * blocks) 0 : Complex) *
                    hWordLiveCoeff blocks tail) •
                    phaseCycleTargetChannel 8 (hPhaseTarget .inverse)
                      (hFixedIdealWordLinear tail data)
              calc
                hRetryTargetHitLinear hMagicState (hPhaseTarget .inverse) (8 * blocks) 0
                    (hWordLiveLinear hMagicState blocks tail data) =
                    hRetryTargetHitLinear hMagicState (hPhaseTarget .inverse) (8 * blocks) 0
                      (hWordLiveCoeff blocks tail • hFixedIdealWordLinear tail data) := by
                        rw [ih data hdata]
                _ = hWordLiveCoeff blocks tail •
                    hRetryTargetHitLinear hMagicState (hPhaseTarget .inverse) (8 * blocks) 0
                      (hFixedIdealWordLinear tail data) :=
                  (hRetryTargetHitLinear hMagicState (hPhaseTarget .inverse)
                    (8 * blocks) 0).map_smul _ _
                _ = hWordLiveCoeff blocks tail •
                    rawAggregateOfKind .targetHit
                      (hRetry hMagicState (hPhaseTarget .inverse) (8 * blocks) 0 0 []
                        (hFixedIdealWordLinear tail data)) := by
                          rw [hRetryTargetHitLinear_apply]
                _ = hWordLiveCoeff blocks tail •
                    ((hTargetHitCoeff (hPhaseTarget .inverse) (8 * blocks) 0 : Complex) •
                      phaseCycleTargetChannel 8 (hPhaseTarget .inverse)
                        (hFixedIdealWordLinear tail data)) := by
                          rw [hRetry_ideal_targetHit_action _ _ 0 [] _ htailPositive]
                _ = ((hTargetHitCoeff (hPhaseTarget .inverse) (8 * blocks) 0 : Complex) *
                    hWordLiveCoeff blocks tail) •
                    phaseCycleTargetChannel 8 (hPhaseTarget .inverse)
                      (hFixedIdealWordLinear tail data) := by
                        rw [smul_smul]
                        ring

/- Task 5d4g checkpoint 3B: H signed-word ideal action and source stability. -/

/-- A source-list H-word continuation which executes its tail first and
retains each phase exhaustion beside the caller's success continuation. -/
private noncomputable def hWordStoppingTotalLinear
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 4)) →
      (Operator QubitSpace →ₗ[Complex] Operator QubitSpace) →
        Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | [], success => success
  | letter :: tail, success =>
      match letter with
      | .positive .h =>
          hWordStoppingTotalLinear h blocks tail
            (success.comp (signedHRawLinear .normal))
      | .positive .k =>
          hWordStoppingTotalLinear h blocks tail
            (success.comp (signedKRawLinear .normal))
      | .positive .phase =>
          hWordStoppingTotalLinear h blocks tail
            (hRetryStoppingTotalLinear h (hPhaseTarget .normal) success (8 * blocks) 0)
      | .negative .h =>
          hWordStoppingTotalLinear h blocks tail
            (success.comp (signedHRawLinear .inverse))
      | .negative .k =>
          hWordStoppingTotalLinear h blocks tail
            (success.comp (signedKRawLinear .inverse))
      | .negative .phase =>
          hWordStoppingTotalLinear h blocks tail
            (hRetryStoppingTotalLinear h (hPhaseTarget .inverse) success (8 * blocks) 0)

/-- The source-list continuation agrees with the existing reversed physical
execution aggregate. -/
private theorem hWordStoppingTotalLinear_eq_hSignedWordTotalLinear
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
      (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace),
      hWordStoppingTotalLinear h blocks letters success =
        hSignedWordTotalLinear h blocks letters success := by
  intro letters
  induction letters with
  | nil =>
      intro success
      rfl
  | cons head tail ih =>
      intro success
      rw [hSignedWordTotalLinear_cons]
      cases head <;> rename_i atom <;> cases atom <;>
        simpa [hWordStoppingTotalLinear, hSignedLetterTotalLinear] using ih _

/-- A continued word is exactly its live tail passed to success plus its
retained phase-stopped component. -/
private theorem hWordStoppingTotalLinear_components
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (raw : Operator QubitSpace) :
    hWordStoppingTotalLinear h blocks letters success raw =
      success (hWordLiveLinear h blocks letters raw) +
        hWordPhaseStoppedLinear h blocks letters raw := by
  rw [hWordStoppingTotalLinear_eq_hSignedWordTotalLinear]
  exact (hWord_component_total_with_success h blocks letters success raw).symm

private theorem hWordStoppingTotalLinear_success_difference
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (first second : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (raw : Operator QubitSpace) :
    hWordStoppingTotalLinear h blocks letters first raw -
        hWordStoppingTotalLinear h blocks letters second raw =
      first (hWordLiveLinear h blocks letters raw) -
        second (hWordLiveLinear h blocks letters raw) := by
  rw [hWordStoppingTotalLinear_components, hWordStoppingTotalLinear_components]
  abel

private theorem hWordStoppingTotalLinear_positive
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
      (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace),
      (∀ raw : Operator QubitSpace,
        LinearMap.IsPositive raw → LinearMap.IsPositive (success raw)) →
        ∀ raw : Operator QubitSpace, LinearMap.IsPositive raw →
          LinearMap.IsPositive (hWordStoppingTotalLinear h blocks letters success raw) := by
  intro letters
  induction letters with
  | nil =>
      intro success hsuccess raw hraw
      simpa [hWordStoppingTotalLinear] using hsuccess raw hraw
  | cons head tail ih =>
      intro success hsuccess raw hraw
      cases head <;> rename_i atom <;> cases atom <;>
        first
        | simpa [hWordStoppingTotalLinear, LinearMap.comp_apply] using
            ih (success.comp (signedHRawLinear .normal))
              (fun data hdata => hsuccess _
                (signedHRawLinear_positive .normal data hdata)) raw hraw
        | simpa [hWordStoppingTotalLinear, LinearMap.comp_apply] using
            ih (success.comp (signedKRawLinear .normal))
              (fun data hdata => hsuccess _
                (signedKRawLinear_positive .normal data hdata)) raw hraw
        | simpa [hWordStoppingTotalLinear] using
            ih (hRetryStoppingTotalLinear h (hPhaseTarget .normal) success
                (8 * blocks) 0)
              (fun data hdata => hRetryStoppingTotalLinear_positive h
                (hPhaseTarget .normal) success hsuccess (8 * blocks) 0 data hdata) raw hraw
        | simpa [hWordStoppingTotalLinear, LinearMap.comp_apply] using
            ih (success.comp (signedHRawLinear .inverse))
              (fun data hdata => hsuccess _
                (signedHRawLinear_positive .inverse data hdata)) raw hraw
        | simpa [hWordStoppingTotalLinear, LinearMap.comp_apply] using
            ih (success.comp (signedKRawLinear .inverse))
              (fun data hdata => hsuccess _
                (signedKRawLinear_positive .inverse data hdata)) raw hraw
        | simpa [hWordStoppingTotalLinear] using
            ih (hRetryStoppingTotalLinear h (hPhaseTarget .inverse) success
                (8 * blocks) 0)
              (fun data hdata => hRetryStoppingTotalLinear_positive h
                (hPhaseTarget .inverse) success hsuccess (8 * blocks) 0 data hdata) raw hraw

private theorem hWordStoppingTotalLinear_trace
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
      (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace),
      (∀ raw : Operator QubitSpace,
        LinearMap.trace Complex QubitSpace (success raw) =
          LinearMap.trace Complex QubitSpace raw) →
        ∀ raw : Operator QubitSpace,
          LinearMap.trace Complex QubitSpace
            (hWordStoppingTotalLinear h blocks letters success raw) =
              LinearMap.trace Complex QubitSpace raw := by
  intro letters
  induction letters with
  | nil =>
      intro success hsuccess raw
      simpa [hWordStoppingTotalLinear] using hsuccess raw
  | cons head tail ih =>
      intro success hsuccess raw
      cases head <;> rename_i atom <;> cases atom <;>
        first
        | simpa [hWordStoppingTotalLinear, LinearMap.comp_apply] using
            ih (success.comp (signedHRawLinear .normal))
              (fun data => (hsuccess _).trans (signedHRawLinear_trace .normal data)) raw
        | simpa [hWordStoppingTotalLinear, LinearMap.comp_apply] using
            ih (success.comp (signedKRawLinear .normal))
              (fun data => (hsuccess _).trans (signedKRawLinear_trace .normal data)) raw
        | simpa [hWordStoppingTotalLinear] using
            ih (hRetryStoppingTotalLinear h (hPhaseTarget .normal) success
                (8 * blocks) 0)
              (fun data => hRetryStoppingTotalLinear_trace h (hPhaseTarget .normal)
                success hsuccess (8 * blocks) 0 data) raw
        | simpa [hWordStoppingTotalLinear, LinearMap.comp_apply] using
            ih (success.comp (signedHRawLinear .inverse))
              (fun data => (hsuccess _).trans (signedHRawLinear_trace .inverse data)) raw
        | simpa [hWordStoppingTotalLinear, LinearMap.comp_apply] using
            ih (success.comp (signedKRawLinear .inverse))
              (fun data => (hsuccess _).trans (signedKRawLinear_trace .inverse data)) raw
        | simpa [hWordStoppingTotalLinear] using
            ih (hRetryStoppingTotalLinear h (hPhaseTarget .inverse) success
                (8 * blocks) 0)
              (fun data => hRetryStoppingTotalLinear_trace h (hPhaseTarget .inverse)
                success hsuccess (8 * blocks) 0 data) raw

private theorem hWordStoppingTotalLinear_stable
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
      (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace),
      (∀ raw : Operator QubitSpace,
        LinearMap.IsPositive raw → LinearMap.IsPositive (success raw)) →
      (∀ raw : Operator QubitSpace,
        LinearMap.trace Complex QubitSpace (success raw) =
          LinearMap.trace Complex QubitSpace raw) →
        ∀ (data : Operator QubitSpace), LinearMap.IsPositive data →
          traceNorm
            (hWordStoppingTotalLinear h blocks letters success data -
              hWordStoppingTotalLinear hMagicState blocks letters success data) ≤
            ((8 * blocks * BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) letters : Nat) : Real) *
              (LinearMap.trace Complex QubitSpace data).re *
                traceNorm (h.toOperator - hMagicState.toOperator) := by
  intro letters
  induction letters with
  | nil =>
      intro success hsuccessPositive hsuccessTrace data hdata
      have hzero : traceNorm (0 : Operator QubitSpace) = 0 :=
        (traceNorm_eq_zero_iff 0).mpr rfl
      simp [hWordStoppingTotalLinear, BK05SignedPhaseLetter.resourceCount, hzero]
  | cons head tail ih =>
      intro success hsuccessPositive hsuccessTrace data hdata
      cases head with
      | positive atom =>
          cases atom with
          | h =>
              simpa [hWordStoppingTotalLinear, BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using
                ih (success.comp (signedHRawLinear .normal))
                  (fun raw hraw => hsuccessPositive _
                    (signedHRawLinear_positive .normal raw hraw))
                  (fun raw => (hsuccessTrace _).trans
                    (signedHRawLinear_trace .normal raw)) data hdata
          | k =>
              simpa [hWordStoppingTotalLinear, BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using
                ih (success.comp (signedKRawLinear .normal))
                  (fun raw hraw => hsuccessPositive _
                    (signedKRawLinear_positive .normal raw hraw))
                  (fun raw => (hsuccessTrace _).trans
                    (signedKRawLinear_trace .normal raw)) data hdata
          | phase =>
              let actualSuccess := hRetryStoppingTotalLinear h
                (hPhaseTarget .normal) success (8 * blocks) 0
              let idealSuccess := hRetryStoppingTotalLinear hMagicState
                (hPhaseTarget .normal) success (8 * blocks) 0
              have htailLivePositive : LinearMap.IsPositive
                  (hWordLiveLinear h blocks tail data) :=
                hWordLiveLinear_positive h blocks tail data hdata
              have hactualSuccessPositive : ∀ raw : Operator QubitSpace,
                  LinearMap.IsPositive raw → LinearMap.IsPositive (actualSuccess raw) := by
                intro raw hraw
                exact hRetryStoppingTotalLinear_positive h (hPhaseTarget .normal) success
                  hsuccessPositive (8 * blocks) 0 raw hraw
              have hidealSuccessPositive : ∀ raw : Operator QubitSpace,
                  LinearMap.IsPositive raw → LinearMap.IsPositive (idealSuccess raw) := by
                intro raw hraw
                exact hRetryStoppingTotalLinear_positive hMagicState
                  (hPhaseTarget .normal) success hsuccessPositive (8 * blocks) 0 raw hraw
              have hidealSuccessTrace : ∀ raw : Operator QubitSpace,
                  LinearMap.trace Complex QubitSpace (idealSuccess raw) =
                    LinearMap.trace Complex QubitSpace raw := by
                intro raw
                exact hRetryStoppingTotalLinear_trace hMagicState (hPhaseTarget .normal)
                  success hsuccessTrace (8 * blocks) 0 raw
              have hcurrent :
                  traceNorm
                    (actualSuccess (hWordLiveLinear h blocks tail data) -
                      idealSuccess (hWordLiveLinear h blocks tail data)) ≤
                    ((8 * blocks : Nat) : Real) *
                      (LinearMap.trace Complex QubitSpace
                        (hWordLiveLinear h blocks tail data)).re *
                        traceNorm (h.toOperator - hMagicState.toOperator) := by
                  exact hRetryStoppingTotalLinear_stable h (hPhaseTarget .normal) success
                    hsuccessPositive hsuccessTrace (8 * blocks) 0
                    (hWordLiveLinear h blocks tail data) htailLivePositive
              have hcurrentInput :
                  traceNorm
                    (actualSuccess (hWordLiveLinear h blocks tail data) -
                      idealSuccess (hWordLiveLinear h blocks tail data)) ≤
                    ((8 * blocks : Nat) : Real) *
                      (LinearMap.trace Complex QubitSpace data).re *
                        traceNorm (h.toOperator - hMagicState.toOperator) := by
                  calc
                    traceNorm
                        (actualSuccess (hWordLiveLinear h blocks tail data) -
                          idealSuccess (hWordLiveLinear h blocks tail data)) ≤
                        ((8 * blocks : Nat) : Real) *
                          (LinearMap.trace Complex QubitSpace
                            (hWordLiveLinear h blocks tail data)).re *
                            traceNorm (h.toOperator - hMagicState.toOperator) := hcurrent
                    _ ≤ ((8 * blocks : Nat) : Real) *
                          (LinearMap.trace Complex QubitSpace data).re *
                            traceNorm (h.toOperator - hMagicState.toOperator) := by
                          exact mul_le_mul_of_nonneg_right
                            (mul_le_mul_of_nonneg_left
                              (hWord_live_trace_le h blocks tail data hdata) (by positivity))
                            (traceNorm_nonneg _)
              have htail := ih idealSuccess hidealSuccessPositive hidealSuccessTrace data hdata
              have htele :
                  hWordStoppingTotalLinear h blocks tail actualSuccess data -
                      hWordStoppingTotalLinear hMagicState blocks tail idealSuccess data =
                    (actualSuccess (hWordLiveLinear h blocks tail data) -
                      idealSuccess (hWordLiveLinear h blocks tail data)) +
                      (hWordStoppingTotalLinear h blocks tail idealSuccess data -
                        hWordStoppingTotalLinear hMagicState blocks tail idealSuccess data) := by
                calc
                  hWordStoppingTotalLinear h blocks tail actualSuccess data -
                      hWordStoppingTotalLinear hMagicState blocks tail idealSuccess data =
                    (hWordStoppingTotalLinear h blocks tail actualSuccess data -
                      hWordStoppingTotalLinear h blocks tail idealSuccess data) +
                      (hWordStoppingTotalLinear h blocks tail idealSuccess data -
                        hWordStoppingTotalLinear hMagicState blocks tail idealSuccess data) := by
                        abel
                  _ = (actualSuccess (hWordLiveLinear h blocks tail data) -
                      idealSuccess (hWordLiveLinear h blocks tail data)) +
                      (hWordStoppingTotalLinear h blocks tail idealSuccess data -
                        hWordStoppingTotalLinear hMagicState blocks tail idealSuccess data) := by
                        rw [hWordStoppingTotalLinear_success_difference]
              have hsum :
                  ((8 * blocks : Nat) : Real) *
                      (LinearMap.trace Complex QubitSpace data).re *
                        traceNorm (h.toOperator - hMagicState.toOperator) +
                    ((8 * blocks *
                      BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) tail : Nat) : Real) *
                      (LinearMap.trace Complex QubitSpace data).re *
                        traceNorm (h.toOperator - hMagicState.toOperator) =
                    ((8 * blocks *
                      (1 + BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) tail) : Nat) : Real) *
                      (LinearMap.trace Complex QubitSpace data).re *
                        traceNorm (h.toOperator - hMagicState.toOperator) := by
                push_cast
                ring
              have hphase :
                  traceNorm
                    (hWordStoppingTotalLinear h blocks tail actualSuccess data -
                      hWordStoppingTotalLinear hMagicState blocks tail idealSuccess data) ≤
                    ((8 * blocks *
                      (1 + BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) tail) : Nat) : Real) *
                      (LinearMap.trace Complex QubitSpace data).re *
                        traceNorm (h.toOperator - hMagicState.toOperator) := by
                rw [htele]
                calc
                  traceNorm
                      ((actualSuccess (hWordLiveLinear h blocks tail data) -
                        idealSuccess (hWordLiveLinear h blocks tail data)) +
                        (hWordStoppingTotalLinear h blocks tail idealSuccess data -
                          hWordStoppingTotalLinear hMagicState blocks tail idealSuccess data)) ≤
                      traceNorm
                        (actualSuccess (hWordLiveLinear h blocks tail data) -
                          idealSuccess (hWordLiveLinear h blocks tail data)) +
                        traceNorm
                          (hWordStoppingTotalLinear h blocks tail idealSuccess data -
                            hWordStoppingTotalLinear hMagicState blocks tail idealSuccess data) :=
                    traceNorm_add_le _ _
                  _ ≤ ((8 * blocks : Nat) : Real) *
                        (LinearMap.trace Complex QubitSpace data).re *
                          traceNorm (h.toOperator - hMagicState.toOperator) +
                      ((8 * blocks *
                        BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) tail : Nat) : Real) *
                        (LinearMap.trace Complex QubitSpace data).re *
                          traceNorm (h.toOperator - hMagicState.toOperator) :=
                    add_le_add hcurrentInput htail
                  _ = _ := hsum
              simpa [hWordStoppingTotalLinear, actualSuccess, idealSuccess,
                BK05SignedPhaseLetter.resourceCount, BK05SignedPhaseLetter.phaseCost,
                Nat.add_comm] using hphase
      | negative atom =>
          cases atom with
          | h =>
              simpa [hWordStoppingTotalLinear, BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using
                ih (success.comp (signedHRawLinear .inverse))
                  (fun raw hraw => hsuccessPositive _
                    (signedHRawLinear_positive .inverse raw hraw))
                  (fun raw => (hsuccessTrace _).trans
                    (signedHRawLinear_trace .inverse raw)) data hdata
          | k =>
              simpa [hWordStoppingTotalLinear, BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using
                ih (success.comp (signedKRawLinear .inverse))
                  (fun raw hraw => hsuccessPositive _
                    (signedKRawLinear_positive .inverse raw hraw))
                  (fun raw => (hsuccessTrace _).trans
                    (signedKRawLinear_trace .inverse raw)) data hdata
          | phase =>
              let actualSuccess := hRetryStoppingTotalLinear h
                (hPhaseTarget .inverse) success (8 * blocks) 0
              let idealSuccess := hRetryStoppingTotalLinear hMagicState
                (hPhaseTarget .inverse) success (8 * blocks) 0
              have htailLivePositive : LinearMap.IsPositive
                  (hWordLiveLinear h blocks tail data) :=
                hWordLiveLinear_positive h blocks tail data hdata
              have hactualSuccessPositive : ∀ raw : Operator QubitSpace,
                  LinearMap.IsPositive raw → LinearMap.IsPositive (actualSuccess raw) := by
                intro raw hraw
                exact hRetryStoppingTotalLinear_positive h (hPhaseTarget .inverse) success
                  hsuccessPositive (8 * blocks) 0 raw hraw
              have hidealSuccessPositive : ∀ raw : Operator QubitSpace,
                  LinearMap.IsPositive raw → LinearMap.IsPositive (idealSuccess raw) := by
                intro raw hraw
                exact hRetryStoppingTotalLinear_positive hMagicState
                  (hPhaseTarget .inverse) success hsuccessPositive (8 * blocks) 0 raw hraw
              have hidealSuccessTrace : ∀ raw : Operator QubitSpace,
                  LinearMap.trace Complex QubitSpace (idealSuccess raw) =
                    LinearMap.trace Complex QubitSpace raw := by
                intro raw
                exact hRetryStoppingTotalLinear_trace hMagicState (hPhaseTarget .inverse)
                  success hsuccessTrace (8 * blocks) 0 raw
              have hcurrent :
                  traceNorm
                    (actualSuccess (hWordLiveLinear h blocks tail data) -
                      idealSuccess (hWordLiveLinear h blocks tail data)) ≤
                    ((8 * blocks : Nat) : Real) *
                      (LinearMap.trace Complex QubitSpace
                        (hWordLiveLinear h blocks tail data)).re *
                        traceNorm (h.toOperator - hMagicState.toOperator) := by
                  exact hRetryStoppingTotalLinear_stable h (hPhaseTarget .inverse) success
                    hsuccessPositive hsuccessTrace (8 * blocks) 0
                    (hWordLiveLinear h blocks tail data) htailLivePositive
              have hcurrentInput :
                  traceNorm
                    (actualSuccess (hWordLiveLinear h blocks tail data) -
                      idealSuccess (hWordLiveLinear h blocks tail data)) ≤
                    ((8 * blocks : Nat) : Real) *
                      (LinearMap.trace Complex QubitSpace data).re *
                        traceNorm (h.toOperator - hMagicState.toOperator) := by
                  calc
                    traceNorm
                        (actualSuccess (hWordLiveLinear h blocks tail data) -
                          idealSuccess (hWordLiveLinear h blocks tail data)) ≤
                        ((8 * blocks : Nat) : Real) *
                          (LinearMap.trace Complex QubitSpace
                            (hWordLiveLinear h blocks tail data)).re *
                            traceNorm (h.toOperator - hMagicState.toOperator) := hcurrent
                    _ ≤ ((8 * blocks : Nat) : Real) *
                          (LinearMap.trace Complex QubitSpace data).re *
                            traceNorm (h.toOperator - hMagicState.toOperator) := by
                          exact mul_le_mul_of_nonneg_right
                            (mul_le_mul_of_nonneg_left
                              (hWord_live_trace_le h blocks tail data hdata) (by positivity))
                            (traceNorm_nonneg _)
              have htail := ih idealSuccess hidealSuccessPositive hidealSuccessTrace data hdata
              have htele :
                  hWordStoppingTotalLinear h blocks tail actualSuccess data -
                      hWordStoppingTotalLinear hMagicState blocks tail idealSuccess data =
                    (actualSuccess (hWordLiveLinear h blocks tail data) -
                      idealSuccess (hWordLiveLinear h blocks tail data)) +
                      (hWordStoppingTotalLinear h blocks tail idealSuccess data -
                        hWordStoppingTotalLinear hMagicState blocks tail idealSuccess data) := by
                calc
                  hWordStoppingTotalLinear h blocks tail actualSuccess data -
                      hWordStoppingTotalLinear hMagicState blocks tail idealSuccess data =
                    (hWordStoppingTotalLinear h blocks tail actualSuccess data -
                      hWordStoppingTotalLinear h blocks tail idealSuccess data) +
                      (hWordStoppingTotalLinear h blocks tail idealSuccess data -
                        hWordStoppingTotalLinear hMagicState blocks tail idealSuccess data) := by
                        abel
                  _ = (actualSuccess (hWordLiveLinear h blocks tail data) -
                      idealSuccess (hWordLiveLinear h blocks tail data)) +
                      (hWordStoppingTotalLinear h blocks tail idealSuccess data -
                        hWordStoppingTotalLinear hMagicState blocks tail idealSuccess data) := by
                        rw [hWordStoppingTotalLinear_success_difference]
              have hsum :
                  ((8 * blocks : Nat) : Real) *
                      (LinearMap.trace Complex QubitSpace data).re *
                        traceNorm (h.toOperator - hMagicState.toOperator) +
                    ((8 * blocks *
                      BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) tail : Nat) : Real) *
                      (LinearMap.trace Complex QubitSpace data).re *
                        traceNorm (h.toOperator - hMagicState.toOperator) =
                    ((8 * blocks *
                      (1 + BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) tail) : Nat) : Real) *
                      (LinearMap.trace Complex QubitSpace data).re *
                        traceNorm (h.toOperator - hMagicState.toOperator) := by
                push_cast
                ring
              have hphase :
                  traceNorm
                    (hWordStoppingTotalLinear h blocks tail actualSuccess data -
                      hWordStoppingTotalLinear hMagicState blocks tail idealSuccess data) ≤
                    ((8 * blocks *
                      (1 + BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) tail) : Nat) : Real) *
                      (LinearMap.trace Complex QubitSpace data).re *
                        traceNorm (h.toOperator - hMagicState.toOperator) := by
                rw [htele]
                calc
                  traceNorm
                      ((actualSuccess (hWordLiveLinear h blocks tail data) -
                        idealSuccess (hWordLiveLinear h blocks tail data)) +
                        (hWordStoppingTotalLinear h blocks tail idealSuccess data -
                          hWordStoppingTotalLinear hMagicState blocks tail idealSuccess data)) ≤
                      traceNorm
                        (actualSuccess (hWordLiveLinear h blocks tail data) -
                          idealSuccess (hWordLiveLinear h blocks tail data)) +
                        traceNorm
                          (hWordStoppingTotalLinear h blocks tail idealSuccess data -
                            hWordStoppingTotalLinear hMagicState blocks tail idealSuccess data) :=
                    traceNorm_add_le _ _
                  _ ≤ ((8 * blocks : Nat) : Real) *
                        (LinearMap.trace Complex QubitSpace data).re *
                          traceNorm (h.toOperator - hMagicState.toOperator) +
                      ((8 * blocks *
                        BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) tail : Nat) : Real) *
                        (LinearMap.trace Complex QubitSpace data).re *
                          traceNorm (h.toOperator - hMagicState.toOperator) :=
                    add_le_add hcurrentInput htail
                  _ = _ := hsum
              simpa [hWordStoppingTotalLinear, actualSuccess, idealSuccess,
                BK05SignedPhaseLetter.resourceCount, BK05SignedPhaseLetter.phaseCost,
                Nat.add_comm] using hphase

private theorem hWordStoppingTotalLinear_stable_id
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (data : Operator QubitSpace) (hdata : LinearMap.IsPositive data) :
    traceNorm
      (hWordStoppingTotalLinear h blocks letters LinearMap.id data -
        hWordStoppingTotalLinear hMagicState blocks letters LinearMap.id data) ≤
      ((8 * blocks * BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) letters : Nat) : Real) *
        (LinearMap.trace Complex QubitSpace data).re *
          traceNorm (h.toOperator - hMagicState.toOperator) := by
  exact hWordStoppingTotalLinear_stable h blocks letters LinearMap.id
    (fun _ hpositive => hpositive) (fun raw => rfl) data hdata

/-- The identity continuation is the complete retained-stopping word aggregate. -/
private theorem hSignedWordTotalLinear_stable_id
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (data : Operator QubitSpace) (hdata : LinearMap.IsPositive data) :
    traceNorm
      (hSignedWordTotalLinear h blocks letters LinearMap.id data -
        hSignedWordTotalLinear hMagicState blocks letters LinearMap.id data) ≤
      ((8 * blocks * BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) letters : Nat) : Real) *
        (LinearMap.trace Complex QubitSpace data).re *
          traceNorm (h.toOperator - hMagicState.toOperator) := by
  rw [← hWordStoppingTotalLinear_eq_hSignedWordTotalLinear h blocks letters LinearMap.id,
    ← hWordStoppingTotalLinear_eq_hSignedWordTotalLinear hMagicState blocks letters LinearMap.id]
  exact hWordStoppingTotalLinear_stable_id h blocks letters data hdata

/- Task 5d4g checkpoint 3C: H signed-word ideal action and source stability. -/

/- Task 5e: literal T signed-word execution. -/

private noncomputable def runTSignedLetter
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letter : BK05SignedPhaseLetter (-Real.pi / 6)) (leaves : List BK05WordRawLeaf) :
    List BK05WordRawLeaf :=
  let execute (sign : BK05WordPolarity) (atom : BK05PhaseAtom (-Real.pi / 6)) :=
    match atom with
    | .h => runDeterministic (signedHTransport sign) leaves
    | .k => runDeterministic (signedKTransport sign) leaves
    | .phase => stoppingBind leaves
        (fun history ledger raw => runTPhaseFrom t pairAttempts sign blocks ledger history raw)
  match letter with
  | .positive atom => execute .normal atom
  | .negative atom => execute .inverse atom

private noncomputable def runTPhysicalLetters
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 6)) → List BK05WordRawLeaf → List BK05WordRawLeaf
  | [], leaves => leaves
  | letter :: tail, leaves =>
      runTPhysicalLetters t pairAttempts blocks tail
        (runTSignedLetter t pairAttempts blocks letter leaves)

private theorem runTPhysicalLetters_append
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    ∀ (left right : List (BK05SignedPhaseLetter (-Real.pi / 6))) (leaves : List BK05WordRawLeaf),
      runTPhysicalLetters t pairAttempts blocks (left ++ right) leaves =
        runTPhysicalLetters t pairAttempts blocks right
          (runTPhysicalLetters t pairAttempts blocks left leaves) := by
  intro left
  induction left with
  | nil =>
      intro right leaves
      rfl
  | cons letter tail ih =>
      intro right leaves
      simp [runTPhysicalLetters, ih]

private theorem runTPhysicalLetters_nil
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (leaves : List BK05WordRawLeaf) :
    runTPhysicalLetters t pairAttempts blocks
      ([] : List (BK05SignedPhaseLetter (-Real.pi / 6))) leaves = leaves :=
  rfl

private theorem runTPhysicalLetters_cons
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letter : BK05SignedPhaseLetter (-Real.pi / 6))
    (tail : List (BK05SignedPhaseLetter (-Real.pi / 6)))
    (leaves : List BK05WordRawLeaf) :
    runTPhysicalLetters t pairAttempts blocks (letter :: tail) leaves =
      runTPhysicalLetters t pairAttempts blocks tail
        (runTSignedLetter t pairAttempts blocks letter leaves) :=
  rfl

private noncomputable def runTSignedWord
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
    (leaves : List BK05WordRawLeaf) : List BK05WordRawLeaf :=
  runTPhysicalLetters t pairAttempts blocks letters.reverse leaves

private theorem runTSignedWord_nil
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (leaves : List BK05WordRawLeaf) :
    runTSignedWord t pairAttempts blocks
      ([] : List (BK05SignedPhaseLetter (-Real.pi / 6))) leaves = leaves :=
  rfl

private theorem runTSignedWord_cons
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (head : BK05SignedPhaseLetter (-Real.pi / 6))
    (tail : List (BK05SignedPhaseLetter (-Real.pi / 6)))
    (leaves : List BK05WordRawLeaf) :
    runTSignedWord t pairAttempts blocks (head :: tail) leaves =
      runTSignedLetter t pairAttempts blocks head
        (runTSignedWord t pairAttempts blocks tail leaves) := by
  calc
    runTSignedWord t pairAttempts blocks (head :: tail) leaves =
        runTPhysicalLetters t pairAttempts blocks (tail.reverse ++ [head]) leaves := by
          simp [runTSignedWord]
    _ = runTSignedLetter t pairAttempts blocks head
          (runTPhysicalLetters t pairAttempts blocks tail.reverse leaves) := by
          rw [runTPhysicalLetters_append]
          rfl
    _ = runTSignedLetter t pairAttempts blocks head
          (runTSignedWord t pairAttempts blocks tail leaves) := by
      rfl

private theorem runTSignedLetter_retains_phaseExhausted
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letter : BK05SignedPhaseLetter (-Real.pi / 6)) (leaves : List BK05WordRawLeaf)
    (leaf : BK05WordRawLeaf) (hmem : leaf ∈ leaves)
    (hstatus : leaf.status = .stoppedPhaseExhausted) :
    leaf ∈ runTSignedLetter t pairAttempts blocks letter leaves := by
  cases letter <;> rename_i atom <;> cases atom <;>
    exact stoppingBind_retains_phaseExhausted leaves _ leaf hmem hstatus

private theorem runTSignedLetter_retains_tPairExhausted
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letter : BK05SignedPhaseLetter (-Real.pi / 6)) (leaves : List BK05WordRawLeaf)
    (leaf : BK05WordRawLeaf) (hmem : leaf ∈ leaves)
    (hstatus : leaf.status = .stoppedTPairExhausted) :
    leaf ∈ runTSignedLetter t pairAttempts blocks letter leaves := by
  cases letter <;> rename_i atom <;> cases atom <;>
    exact stoppingBind_retains_tPairExhausted leaves _ leaf hmem hstatus

private theorem runTPhysicalLetters_retains_phaseExhausted
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) (leaves : List BK05WordRawLeaf)
      (leaf : BK05WordRawLeaf),
      leaf ∈ leaves → leaf.status = .stoppedPhaseExhausted →
        leaf ∈ runTPhysicalLetters t pairAttempts blocks letters leaves := by
  intro letters
  induction letters with
  | nil =>
      intro leaves leaf hmem hstatus
      exact hmem
  | cons letter tail ih =>
      intro leaves leaf hmem hstatus
      exact ih (runTSignedLetter t pairAttempts blocks letter leaves) leaf
        (runTSignedLetter_retains_phaseExhausted t pairAttempts blocks letter leaves leaf hmem hstatus)
        hstatus

private theorem runTPhysicalLetters_retains_tPairExhausted
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) (leaves : List BK05WordRawLeaf)
      (leaf : BK05WordRawLeaf),
      leaf ∈ leaves → leaf.status = .stoppedTPairExhausted →
        leaf ∈ runTPhysicalLetters t pairAttempts blocks letters leaves := by
  intro letters
  induction letters with
  | nil =>
      intro leaves leaf hmem hstatus
      exact hmem
  | cons letter tail ih =>
      intro leaves leaf hmem hstatus
      exact ih (runTSignedLetter t pairAttempts blocks letter leaves) leaf
        (runTSignedLetter_retains_tPairExhausted t pairAttempts blocks letter leaves leaf hmem hstatus)
        hstatus

private theorem runTSignedWord_retains_phaseExhausted
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) (leaves : List BK05WordRawLeaf)
    (leaf : BK05WordRawLeaf) (hmem : leaf ∈ leaves)
    (hstatus : leaf.status = .stoppedPhaseExhausted) :
    leaf ∈ runTSignedWord t pairAttempts blocks letters leaves := by
  exact runTPhysicalLetters_retains_phaseExhausted t pairAttempts blocks letters.reverse leaves leaf
    hmem hstatus

private theorem runTSignedWord_retains_tPairExhausted
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) (leaves : List BK05WordRawLeaf)
    (leaf : BK05WordRawLeaf) (hmem : leaf ∈ leaves)
    (hstatus : leaf.status = .stoppedTPairExhausted) :
    leaf ∈ runTSignedWord t pairAttempts blocks letters leaves := by
  exact runTPhysicalLetters_retains_tPairExhausted t pairAttempts blocks letters.reverse leaves leaf
    hmem hstatus

/- Task 5e checkpoint 1: T signed-word execution. -/

/- Task 5e checkpoint 2A: T supplier/retry component semantics. -/

private noncomputable def tSupplyStoppingComponentLinear
    (t : DensityOperator QubitSpace) : Nat →
      (Operator QubitSpace →ₗ[Complex] Operator QubitSpace) →
      (Operator QubitSpace →ₗ[Complex] Operator QubitSpace) →
      (Operator QubitSpace →ₗ[Complex] Operator QubitSpace) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | 0, _, _, onPairExhausted => onPairExhausted
  | attempts + 1, nextTrue, nextFalse, onPairExhausted =>
      nextTrue.comp (phaseBranchRawLinear (tAcceptedPhaseRaw t) true) +
        nextFalse.comp (phaseBranchRawLinear (tAcceptedPhaseRaw t) false) +
        (tSupplyStoppingComponentLinear t attempts
          nextTrue nextFalse onPairExhausted).comp (tRejectedDataRawLinear t)

private def tSupplyStoppingComponentValue
    (nextTrue nextFalse onPairExhausted : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    List BK05TSupplyOutcome → Operator QubitSpace
  | [] => 0
  | .accepted _ _ data phaseToken :: outcomes =>
      nextTrue (phaseBranchRaw phaseToken data true) +
        nextFalse (phaseBranchRaw phaseToken data false) +
        tSupplyStoppingComponentValue nextTrue nextFalse onPairExhausted outcomes
  | .exhausted _ _ data :: outcomes =>
      onPairExhausted data +
        tSupplyStoppingComponentValue nextTrue nextFalse onPairExhausted outcomes

private theorem tSupplyStoppingComponentLinear_apply
    (t : DensityOperator QubitSpace)
    (nextTrue nextFalse onPairExhausted : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    ∀ (attempts : Nat) (ledger)
      (history : List Bool) (data : Operator QubitSpace),
      tSupplyStoppingComponentLinear t attempts nextTrue nextFalse onPairExhausted data =
        tSupplyStoppingComponentValue nextTrue nextFalse onPairExhausted
          (tSupply t attempts ledger history data) := by
  intro attempts
  induction attempts with
  | zero =>
      intro ledger history data
      simp [tSupply, tSupplyStoppingComponentLinear, tSupplyStoppingComponentValue]
  | succ attempts ih =>
      intro ledger history data
      let nextLedger := ledger + {.t, .t}
      simp only [tSupply, tSupplyStoppingComponentLinear, LinearMap.add_apply,
        LinearMap.comp_apply, phaseBranchRawLinear_apply, tSupplyStoppingComponentValue]
      rw [tRejectedDataRawLinear_apply,
        ih nextLedger (false :: history) (tRejectedDataRaw data t)]

private theorem tSupplyStoppingComponentLinear_positive
    (t : DensityOperator QubitSpace)
    (nextTrue nextFalse onPairExhausted : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (htrue : ∀ raw, LinearMap.IsPositive raw → LinearMap.IsPositive (nextTrue raw))
    (hfalse : ∀ raw, LinearMap.IsPositive raw → LinearMap.IsPositive (nextFalse raw))
    (hpair : ∀ raw, LinearMap.IsPositive raw → LinearMap.IsPositive (onPairExhausted raw)) :
    ∀ (attempts : Nat) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      LinearMap.IsPositive
        (tSupplyStoppingComponentLinear t attempts nextTrue nextFalse onPairExhausted data) := by
  intro attempts
  induction attempts with
  | zero =>
      intro data hdata
      simpa [tSupplyStoppingComponentLinear] using hpair data hdata
  | succ attempts ih =>
      intro data hdata
      have htail := ih (tRejectedDataRaw data t) (tRejectedDataRaw_positive data t hdata)
      have haccepted := tAcceptedPhaseRaw_positive t
      exact (LinearMap.IsPositive.add (LinearMap.IsPositive.add
          (htrue _ (phaseBranchRaw_positive _ _ haccepted hdata true))
          (hfalse _ (phaseBranchRaw_positive _ _ haccepted hdata false))) htail)

private noncomputable def tSupplyTargetHitLinear
    (t : DensityOperator QubitSpace) (attempts : Nat)
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace :=
  tSupplyStoppingComponentLinear t attempts nextTrue nextFalse
    (0 : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)

private noncomputable def tSupplyPhaseExhaustedLinear
    (t : DensityOperator QubitSpace) (attempts : Nat)
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace :=
  tSupplyStoppingComponentLinear t attempts nextTrue nextFalse
    (0 : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)

private noncomputable def tSupplyPairExhaustedLinear
    (t : DensityOperator QubitSpace) (attempts : Nat)
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace :=
  tSupplyStoppingComponentLinear t attempts nextTrue nextFalse LinearMap.id

private theorem tSupplyTargetHitLinear_positive
    (t : DensityOperator QubitSpace)
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (htrue : ∀ raw, LinearMap.IsPositive raw → LinearMap.IsPositive (nextTrue raw))
    (hfalse : ∀ raw, LinearMap.IsPositive raw → LinearMap.IsPositive (nextFalse raw)) :
    ∀ (attempts : Nat) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      LinearMap.IsPositive (tSupplyTargetHitLinear t attempts nextTrue nextFalse data) := by
  intro attempts data hdata
  exact tSupplyStoppingComponentLinear_positive t nextTrue nextFalse 0 htrue hfalse
    (fun _ _ => by simp) attempts data hdata

private theorem tSupplyPhaseExhaustedLinear_positive
    (t : DensityOperator QubitSpace)
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (htrue : ∀ raw, LinearMap.IsPositive raw → LinearMap.IsPositive (nextTrue raw))
    (hfalse : ∀ raw, LinearMap.IsPositive raw → LinearMap.IsPositive (nextFalse raw)) :
    ∀ (attempts : Nat) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      LinearMap.IsPositive (tSupplyPhaseExhaustedLinear t attempts nextTrue nextFalse data) := by
  intro attempts data hdata
  exact tSupplyStoppingComponentLinear_positive t nextTrue nextFalse 0 htrue hfalse
    (fun _ _ => by simp) attempts data hdata

private theorem tSupplyPairExhaustedLinear_positive
    (t : DensityOperator QubitSpace)
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (htrue : ∀ raw, LinearMap.IsPositive raw → LinearMap.IsPositive (nextTrue raw))
    (hfalse : ∀ raw, LinearMap.IsPositive raw → LinearMap.IsPositive (nextFalse raw)) :
    ∀ (attempts : Nat) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      LinearMap.IsPositive (tSupplyPairExhaustedLinear t attempts nextTrue nextFalse data) := by
  intro attempts data hdata
  exact tSupplyStoppingComponentLinear_positive t nextTrue nextFalse LinearMap.id htrue hfalse
    (fun _ hpositive => hpositive) attempts data hdata

private theorem tSupplyComponentLinear_sum
    (t : DensityOperator QubitSpace)
    (targetTrue targetFalse phaseTrue phaseFalse pairTrue pairFalse :
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    ∀ attempts,
      tSupplyTargetHitLinear t attempts targetTrue targetFalse +
        tSupplyPhaseExhaustedLinear t attempts phaseTrue phaseFalse +
        tSupplyPairExhaustedLinear t attempts pairTrue pairFalse =
          tSupplyAggregateLinear t attempts
            (targetTrue + phaseTrue + pairTrue) (targetFalse + phaseFalse + pairFalse) := by
  intro attempts
  induction attempts with
  | zero =>
      simp [tSupplyTargetHitLinear, tSupplyPhaseExhaustedLinear,
        tSupplyPairExhaustedLinear, tSupplyStoppingComponentLinear, tSupplyAggregateLinear]
  | succ attempts ih =>
      apply LinearMap.ext
      intro data
      have htail := congrArg (fun carrier :
          Operator QubitSpace →ₗ[Complex] Operator QubitSpace =>
            carrier (tRejectedDataRaw data t)) ih
      simp only [LinearMap.add_apply] at htail
      have htail' :
          tSupplyStoppingComponentLinear t attempts targetTrue targetFalse 0
              (tRejectedDataRaw data t) +
            tSupplyStoppingComponentLinear t attempts phaseTrue phaseFalse 0
              (tRejectedDataRaw data t) +
            tSupplyStoppingComponentLinear t attempts pairTrue pairFalse LinearMap.id
              (tRejectedDataRaw data t) =
              tSupplyAggregateLinear t attempts
                (targetTrue + phaseTrue + pairTrue) (targetFalse + phaseFalse + pairFalse)
                  (tRejectedDataRaw data t) := by
        simpa [tSupplyTargetHitLinear, tSupplyPhaseExhaustedLinear,
          tSupplyPairExhaustedLinear] using htail
      simp only [tSupplyTargetHitLinear, tSupplyPhaseExhaustedLinear,
        tSupplyPairExhaustedLinear, tSupplyStoppingComponentLinear,
        tSupplyAggregateLinear, LinearMap.add_apply, LinearMap.comp_apply,
        phaseBranchRawLinear_apply, tRejectedDataRawLinear_apply]
      calc
        _ = targetTrue (phaseBranchRaw (tAcceptedPhaseRaw t) data true) +
              phaseTrue (phaseBranchRaw (tAcceptedPhaseRaw t) data true) +
              pairTrue (phaseBranchRaw (tAcceptedPhaseRaw t) data true) +
            (targetFalse (phaseBranchRaw (tAcceptedPhaseRaw t) data false) +
              phaseFalse (phaseBranchRaw (tAcceptedPhaseRaw t) data false) +
              pairFalse (phaseBranchRaw (tAcceptedPhaseRaw t) data false)) +
            (tSupplyStoppingComponentLinear t attempts targetTrue targetFalse 0
                (tRejectedDataRaw data t) +
              tSupplyStoppingComponentLinear t attempts phaseTrue phaseFalse 0
                (tRejectedDataRaw data t) +
              tSupplyStoppingComponentLinear t attempts pairTrue pairFalse LinearMap.id
                (tRejectedDataRaw data t)) := by abel
        _ = _ := by rw [htail']

private noncomputable def tRetryTargetHitLinear
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12) :
    Nat → ZMod 12 → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | remaining, position =>
      if position = target then LinearMap.id else
        match remaining with
        | 0 => 0
        | nextRemaining + 1 =>
            tSupplyTargetHitLinear t pairAttempts
              (tRetryTargetHitLinear t pairAttempts target nextRemaining (position + 1))
              (tRetryTargetHitLinear t pairAttempts target nextRemaining (position - 1))

private noncomputable def tRetryPhaseExhaustedLinear
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12) :
    Nat → ZMod 12 → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | remaining, position =>
      if position = target then 0 else
        match remaining with
        | 0 => LinearMap.id
        | nextRemaining + 1 =>
            tSupplyPhaseExhaustedLinear t pairAttempts
              (tRetryPhaseExhaustedLinear t pairAttempts target nextRemaining (position + 1))
              (tRetryPhaseExhaustedLinear t pairAttempts target nextRemaining (position - 1))

private noncomputable def tRetryPairExhaustedLinear
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12) :
    Nat → ZMod 12 → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | remaining, position =>
      if position = target then 0 else
        match remaining with
        | 0 => 0
        | nextRemaining + 1 =>
            tSupplyPairExhaustedLinear t pairAttempts
              (tRetryPairExhaustedLinear t pairAttempts target nextRemaining (position + 1))
              (tRetryPairExhaustedLinear t pairAttempts target nextRemaining (position - 1))

private theorem tRetryComponentLinear_sum
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12) :
    ∀ (remaining : Nat) (position : ZMod 12),
      tRetryTargetHitLinear t pairAttempts target remaining position +
        tRetryPhaseExhaustedLinear t pairAttempts target remaining position +
        tRetryPairExhaustedLinear t pairAttempts target remaining position =
          tRetryAggregateLinear t pairAttempts target remaining position := by
  intro remaining
  induction remaining with
  | zero =>
      intro position
      apply LinearMap.ext
      intro data
      by_cases htarget : position = target <;>
        simp [tRetryTargetHitLinear, tRetryPhaseExhaustedLinear,
          tRetryPairExhaustedLinear, tRetryAggregateLinear, htarget]
  | succ remaining ih =>
      intro position
      apply LinearMap.ext
      intro data
      by_cases htarget : position = target
      · simp [tRetryTargetHitLinear, tRetryPhaseExhaustedLinear,
          tRetryPairExhaustedLinear, tRetryAggregateLinear, htarget]
      · simp only [tRetryTargetHitLinear, tRetryPhaseExhaustedLinear,
          tRetryPairExhaustedLinear, tRetryAggregateLinear, if_neg htarget]
        rw [tSupplyComponentLinear_sum,
          ih (position + 1), ih (position - 1)]

private theorem tRetryTargetHitLinear_positive
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12) :
    ∀ (remaining : Nat) (position : ZMod 12) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      LinearMap.IsPositive (tRetryTargetHitLinear t pairAttempts target remaining position data) := by
  intro remaining
  induction remaining with
  | zero =>
      intro position data hdata
      by_cases htarget : position = target
      · simpa [tRetryTargetHitLinear, htarget] using hdata
      · simp [tRetryTargetHitLinear, htarget]
  | succ remaining ih =>
      intro position data hdata
      by_cases htarget : position = target
      · simpa [tRetryTargetHitLinear, htarget] using hdata
      · simpa [tRetryTargetHitLinear, htarget] using
          tSupplyTargetHitLinear_positive t
            (tRetryTargetHitLinear t pairAttempts target remaining (position + 1))
            (tRetryTargetHitLinear t pairAttempts target remaining (position - 1))
            (fun raw hraw => ih (position + 1) raw hraw)
            (fun raw hraw => ih (position - 1) raw hraw)
            pairAttempts data hdata

private theorem tRetryPhaseExhaustedLinear_positive
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12) :
    ∀ (remaining : Nat) (position : ZMod 12) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      LinearMap.IsPositive
        (tRetryPhaseExhaustedLinear t pairAttempts target remaining position data) := by
  intro remaining
  induction remaining with
  | zero =>
      intro position data hdata
      by_cases htarget : position = target
      · simp [tRetryPhaseExhaustedLinear, htarget]
      · simpa [tRetryPhaseExhaustedLinear, htarget] using hdata
  | succ remaining ih =>
      intro position data hdata
      by_cases htarget : position = target
      · simp [tRetryPhaseExhaustedLinear, htarget]
      · simpa [tRetryPhaseExhaustedLinear, htarget] using
          tSupplyPhaseExhaustedLinear_positive t
            (tRetryPhaseExhaustedLinear t pairAttempts target remaining (position + 1))
            (tRetryPhaseExhaustedLinear t pairAttempts target remaining (position - 1))
            (fun raw hraw => ih (position + 1) raw hraw)
            (fun raw hraw => ih (position - 1) raw hraw)
            pairAttempts data hdata

private theorem tRetryPairExhaustedLinear_positive
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12) :
    ∀ (remaining : Nat) (position : ZMod 12) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      LinearMap.IsPositive
        (tRetryPairExhaustedLinear t pairAttempts target remaining position data) := by
  intro remaining
  induction remaining with
  | zero =>
      intro position data hdata
      simp [tRetryPairExhaustedLinear]
  | succ remaining ih =>
      intro position data hdata
      by_cases htarget : position = target
      · simp [tRetryPairExhaustedLinear, htarget]
      · simpa [tRetryPairExhaustedLinear, htarget] using
          tSupplyPairExhaustedLinear_positive t
            (tRetryPairExhaustedLinear t pairAttempts target remaining (position + 1))
            (tRetryPairExhaustedLinear t pairAttempts target remaining (position - 1))
            (fun raw hraw => ih (position + 1) raw hraw)
            (fun raw hraw => ih (position - 1) raw hraw)
            pairAttempts data hdata

private theorem tRetryTargetHitLinear_apply
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (remaining : Nat) :
    ∀ (position : ZMod 12) (ledger)
      (history : List Bool) (data : Operator QubitSpace),
      tRetryTargetHitLinear t pairAttempts target remaining position data =
        rawAggregateOfKind .targetHit
          (tRetry t pairAttempts target remaining position ledger history data) := by
  induction remaining with
  | zero =>
      intro position ledger history data
      by_cases htarget : position = target <;>
        simp [tRetryTargetHitLinear, tRetry, rawAggregateOfKind, rawAggregate, htarget]
  | succ remaining ih =>
      intro position ledger history data
      by_cases htarget : position = target
      · simp [tRetryTargetHitLinear, tRetry, rawAggregateOfKind, rawAggregate, htarget]
      · rw [tRetry, if_neg htarget]
        let continuation : BK05TSupplyOutcome → List BK05RawLeaf := fun supplied =>
          match supplied with
          | .accepted suppliedLedger suppliedHistory suppliedData phaseToken =>
              tRetry t pairAttempts target remaining (position + 1) suppliedLedger
                  (true :: suppliedHistory)
                  (phaseBranchRaw phaseToken suppliedData true)
                ++
              tRetry t pairAttempts target remaining (position - 1) suppliedLedger
                  (false :: suppliedHistory)
                  (phaseBranchRaw phaseToken suppliedData false)
          | .exhausted suppliedLedger suppliedHistory suppliedData =>
              [⟨.tPairExhausted, suppliedHistory, suppliedLedger, suppliedData⟩]
        let nextTrue := tRetryTargetHitLinear t pairAttempts target remaining (position + 1)
        let nextFalse := tRetryTargetHitLinear t pairAttempts target remaining (position - 1)
        have hvalue := tSupplyStoppingComponentLinear_apply t nextTrue nextFalse
          (0 : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
          pairAttempts ledger history data
        have hflat :
            rawAggregateOfKind .targetHit
                ((tSupply t pairAttempts ledger history data).flatMap continuation) =
              tSupplyStoppingComponentValue nextTrue nextFalse 0
                (tSupply t pairAttempts ledger history data) := by
          induction tSupply t pairAttempts ledger history data with
          | nil => simp [tSupplyStoppingComponentValue, rawAggregateOfKind, rawAggregate]
          | cons supplied outcomes ihout =>
              cases supplied with
              | accepted suppliedLedger suppliedHistory suppliedData phaseToken =>
                  rw [List.flatMap_cons, rawAggregateOfKind_append, rawAggregateOfKind_append,
                    ← ih (position + 1) suppliedLedger (true :: suppliedHistory)
                      (phaseBranchRaw phaseToken suppliedData true),
                    ← ih (position - 1) suppliedLedger (false :: suppliedHistory)
                      (phaseBranchRaw phaseToken suppliedData false), ihout]
                  simp [continuation, nextTrue, nextFalse, tSupplyStoppingComponentValue]
              | exhausted suppliedLedger suppliedHistory suppliedData =>
                  rw [List.flatMap_cons, rawAggregateOfKind_append, ihout]
                  simp [continuation, tSupplyStoppingComponentValue, rawAggregateOfKind, rawAggregate]
        have hcarrier :
            tSupplyTargetHitLinear t pairAttempts nextTrue nextFalse data =
              tSupplyStoppingComponentValue nextTrue nextFalse 0
                (tSupply t pairAttempts ledger history data) := by
          simpa [tSupplyTargetHitLinear] using hvalue
        simpa [tRetryTargetHitLinear, htarget, nextTrue, nextFalse] using
          hcarrier.trans hflat.symm

private theorem tRetryPhaseExhaustedLinear_apply
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (remaining : Nat) :
    ∀ (position : ZMod 12) (ledger)
      (history : List Bool) (data : Operator QubitSpace),
      tRetryPhaseExhaustedLinear t pairAttempts target remaining position data =
        rawAggregateOfKind .phaseExhausted
          (tRetry t pairAttempts target remaining position ledger history data) := by
  induction remaining with
  | zero =>
      intro position ledger history data
      by_cases htarget : position = target <;>
        simp [tRetryPhaseExhaustedLinear, tRetry, rawAggregateOfKind, rawAggregate, htarget]
  | succ remaining ih =>
      intro position ledger history data
      by_cases htarget : position = target
      · simp [tRetryPhaseExhaustedLinear, tRetry, rawAggregateOfKind, rawAggregate, htarget]
      · rw [tRetry, if_neg htarget]
        let continuation : BK05TSupplyOutcome → List BK05RawLeaf := fun supplied =>
          match supplied with
          | .accepted suppliedLedger suppliedHistory suppliedData phaseToken =>
              tRetry t pairAttempts target remaining (position + 1) suppliedLedger
                  (true :: suppliedHistory)
                  (phaseBranchRaw phaseToken suppliedData true)
                ++
              tRetry t pairAttempts target remaining (position - 1) suppliedLedger
                  (false :: suppliedHistory)
                  (phaseBranchRaw phaseToken suppliedData false)
          | .exhausted suppliedLedger suppliedHistory suppliedData =>
              [⟨.tPairExhausted, suppliedHistory, suppliedLedger, suppliedData⟩]
        let nextTrue :=
          tRetryPhaseExhaustedLinear t pairAttempts target remaining (position + 1)
        let nextFalse :=
          tRetryPhaseExhaustedLinear t pairAttempts target remaining (position - 1)
        have hvalue := tSupplyStoppingComponentLinear_apply t nextTrue nextFalse
          (0 : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
          pairAttempts ledger history data
        have hflat :
            rawAggregateOfKind .phaseExhausted
                ((tSupply t pairAttempts ledger history data).flatMap continuation) =
              tSupplyStoppingComponentValue nextTrue nextFalse 0
                (tSupply t pairAttempts ledger history data) := by
          induction tSupply t pairAttempts ledger history data with
          | nil => simp [tSupplyStoppingComponentValue, rawAggregateOfKind, rawAggregate]
          | cons supplied outcomes ihout =>
              cases supplied with
              | accepted suppliedLedger suppliedHistory suppliedData phaseToken =>
                  rw [List.flatMap_cons, rawAggregateOfKind_append, rawAggregateOfKind_append,
                    ← ih (position + 1) suppliedLedger (true :: suppliedHistory)
                      (phaseBranchRaw phaseToken suppliedData true),
                    ← ih (position - 1) suppliedLedger (false :: suppliedHistory)
                      (phaseBranchRaw phaseToken suppliedData false), ihout]
                  simp [continuation, nextTrue, nextFalse, tSupplyStoppingComponentValue]
              | exhausted suppliedLedger suppliedHistory suppliedData =>
                  rw [List.flatMap_cons, rawAggregateOfKind_append, ihout]
                  simp [continuation, tSupplyStoppingComponentValue, rawAggregateOfKind, rawAggregate]
        have hcarrier :
            tSupplyPhaseExhaustedLinear t pairAttempts nextTrue nextFalse data =
              tSupplyStoppingComponentValue nextTrue nextFalse 0
                (tSupply t pairAttempts ledger history data) := by
          simpa [tSupplyPhaseExhaustedLinear] using hvalue
        simpa [tRetryPhaseExhaustedLinear, htarget, nextTrue, nextFalse] using
          hcarrier.trans hflat.symm

private theorem tRetryPairExhaustedLinear_apply
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (remaining : Nat) :
    ∀ (position : ZMod 12) (ledger)
      (history : List Bool) (data : Operator QubitSpace),
      tRetryPairExhaustedLinear t pairAttempts target remaining position data =
        rawAggregateOfKind .tPairExhausted
          (tRetry t pairAttempts target remaining position ledger history data) := by
  induction remaining with
  | zero =>
      intro position ledger history data
      by_cases htarget : position = target <;>
        simp [tRetryPairExhaustedLinear, tRetry, rawAggregateOfKind, rawAggregate, htarget]
  | succ remaining ih =>
      intro position ledger history data
      by_cases htarget : position = target
      · simp [tRetryPairExhaustedLinear, tRetry, rawAggregateOfKind, rawAggregate, htarget]
      · rw [tRetry, if_neg htarget]
        let continuation : BK05TSupplyOutcome → List BK05RawLeaf := fun supplied =>
          match supplied with
          | .accepted suppliedLedger suppliedHistory suppliedData phaseToken =>
              tRetry t pairAttempts target remaining (position + 1) suppliedLedger
                  (true :: suppliedHistory)
                  (phaseBranchRaw phaseToken suppliedData true)
                ++
              tRetry t pairAttempts target remaining (position - 1) suppliedLedger
                  (false :: suppliedHistory)
                  (phaseBranchRaw phaseToken suppliedData false)
          | .exhausted suppliedLedger suppliedHistory suppliedData =>
              [⟨.tPairExhausted, suppliedHistory, suppliedLedger, suppliedData⟩]
        let nextTrue :=
          tRetryPairExhaustedLinear t pairAttempts target remaining (position + 1)
        let nextFalse :=
          tRetryPairExhaustedLinear t pairAttempts target remaining (position - 1)
        have hvalue := tSupplyStoppingComponentLinear_apply t nextTrue nextFalse
          LinearMap.id pairAttempts ledger history data
        have hflat :
            rawAggregateOfKind .tPairExhausted
                ((tSupply t pairAttempts ledger history data).flatMap continuation) =
              tSupplyStoppingComponentValue nextTrue nextFalse LinearMap.id
                (tSupply t pairAttempts ledger history data) := by
          induction tSupply t pairAttempts ledger history data with
          | nil => simp [tSupplyStoppingComponentValue, rawAggregateOfKind, rawAggregate]
          | cons supplied outcomes ihout =>
              cases supplied with
              | accepted suppliedLedger suppliedHistory suppliedData phaseToken =>
                  rw [List.flatMap_cons, rawAggregateOfKind_append, rawAggregateOfKind_append,
                    ← ih (position + 1) suppliedLedger (true :: suppliedHistory)
                      (phaseBranchRaw phaseToken suppliedData true),
                    ← ih (position - 1) suppliedLedger (false :: suppliedHistory)
                      (phaseBranchRaw phaseToken suppliedData false), ihout]
                  simp [continuation, nextTrue, nextFalse, tSupplyStoppingComponentValue]
              | exhausted suppliedLedger suppliedHistory suppliedData =>
                  rw [List.flatMap_cons, rawAggregateOfKind_append, ihout]
                  simp [continuation, tSupplyStoppingComponentValue, rawAggregateOfKind, rawAggregate]
        have hcarrier :
            tSupplyPairExhaustedLinear t pairAttempts nextTrue nextFalse data =
              tSupplyStoppingComponentValue nextTrue nextFalse LinearMap.id
                (tSupply t pairAttempts ledger history data) := by
          simpa [tSupplyPairExhaustedLinear] using hvalue
        simpa [tRetryPairExhaustedLinear, htarget, nextTrue, nextFalse] using
          hcarrier.trans hflat.symm

private theorem tRetryComponentLinear_total_apply
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (remaining : Nat) (position : ZMod 12) (ledger)
    (history : List Bool) (data : Operator QubitSpace) :
    (tRetryTargetHitLinear t pairAttempts target remaining position +
        tRetryPhaseExhaustedLinear t pairAttempts target remaining position +
        tRetryPairExhaustedLinear t pairAttempts target remaining position) data =
      rawAggregate (tRetry t pairAttempts target remaining position ledger history data) := by
  rw [tRetryComponentLinear_sum, tRetryAggregateLinear_apply]

private theorem tRetryComponentLinear_total_trace
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (remaining : Nat) (position : ZMod 12) (data : Operator QubitSpace) :
    LinearMap.trace Complex QubitSpace
        (tRetryTargetHitLinear t pairAttempts target remaining position data) +
      LinearMap.trace Complex QubitSpace
        (tRetryPhaseExhaustedLinear t pairAttempts target remaining position data) +
      LinearMap.trace Complex QubitSpace
        (tRetryPairExhaustedLinear t pairAttempts target remaining position data) =
        LinearMap.trace Complex QubitSpace data := by
  calc
    LinearMap.trace Complex QubitSpace
          (tRetryTargetHitLinear t pairAttempts target remaining position data) +
        LinearMap.trace Complex QubitSpace
          (tRetryPhaseExhaustedLinear t pairAttempts target remaining position data) +
        LinearMap.trace Complex QubitSpace
          (tRetryPairExhaustedLinear t pairAttempts target remaining position data) =
        LinearMap.trace Complex QubitSpace
          ((tRetryTargetHitLinear t pairAttempts target remaining position +
              tRetryPhaseExhaustedLinear t pairAttempts target remaining position +
              tRetryPairExhaustedLinear t pairAttempts target remaining position) data) := by
          rw [LinearMap.add_apply, LinearMap.add_apply, map_add, map_add]
    _ = LinearMap.trace Complex QubitSpace
          (tRetryAggregateLinear t pairAttempts target remaining position data) := by
          rw [tRetryComponentLinear_sum]
    _ = LinearMap.trace Complex QubitSpace data :=
      tRetryAggregateLinear_trace t pairAttempts target remaining position data

/- Task 5e checkpoint 2B: T signed-word component compilation. -/

private noncomputable def tWordLiveLinear
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 6)) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | [] => LinearMap.id
  | letter :: tail =>
      let tailLive := tWordLiveLinear t pairAttempts blocks tail
      match letter with
      | .positive .h => (signedHRawLinear .normal).comp tailLive
      | .positive .k => (signedKRawLinear .normal).comp tailLive
      | .positive .phase =>
          (tRetryTargetHitLinear t pairAttempts (tPhaseTarget .normal) (12 * blocks) 0).comp
            tailLive
      | .negative .h => (signedHRawLinear .inverse).comp tailLive
      | .negative .k => (signedKRawLinear .inverse).comp tailLive
      | .negative .phase =>
          (tRetryTargetHitLinear t pairAttempts (tPhaseTarget .inverse) (12 * blocks) 0).comp
            tailLive

private noncomputable def tWordPhaseStoppedLinear
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 6)) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | [] => 0
  | letter :: tail =>
      let tailLive := tWordLiveLinear t pairAttempts blocks tail
      match letter with
      | .positive .h => tWordPhaseStoppedLinear t pairAttempts blocks tail
      | .positive .k => tWordPhaseStoppedLinear t pairAttempts blocks tail
      | .positive .phase =>
          (tRetryPhaseExhaustedLinear t pairAttempts (tPhaseTarget .normal) (12 * blocks) 0).comp
            tailLive + tWordPhaseStoppedLinear t pairAttempts blocks tail
      | .negative .h => tWordPhaseStoppedLinear t pairAttempts blocks tail
      | .negative .k => tWordPhaseStoppedLinear t pairAttempts blocks tail
      | .negative .phase =>
          (tRetryPhaseExhaustedLinear t pairAttempts (tPhaseTarget .inverse) (12 * blocks) 0).comp
            tailLive + tWordPhaseStoppedLinear t pairAttempts blocks tail

private noncomputable def tWordPairStoppedLinear
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 6)) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | [] => 0
  | letter :: tail =>
      let tailLive := tWordLiveLinear t pairAttempts blocks tail
      match letter with
      | .positive .h => tWordPairStoppedLinear t pairAttempts blocks tail
      | .positive .k => tWordPairStoppedLinear t pairAttempts blocks tail
      | .positive .phase =>
          (tRetryPairExhaustedLinear t pairAttempts (tPhaseTarget .normal) (12 * blocks) 0).comp
            tailLive + tWordPairStoppedLinear t pairAttempts blocks tail
      | .negative .h => tWordPairStoppedLinear t pairAttempts blocks tail
      | .negative .k => tWordPairStoppedLinear t pairAttempts blocks tail
      | .negative .phase =>
          (tRetryPairExhaustedLinear t pairAttempts (tPhaseTarget .inverse) (12 * blocks) 0).comp
            tailLive + tWordPairStoppedLinear t pairAttempts blocks tail

private theorem stoppingBind_tPairStopped_component
    (continuation)
    (carrier : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (hcontinuation : ∀ history ledger raw,
      wordRawAggregateOfStatus .stoppedTPairExhausted
        (continuation history ledger raw) = carrier raw) :
    ∀ leaves : List BK05WordRawLeaf,
      wordRawAggregateOfStatus .stoppedTPairExhausted
        (stoppingBind leaves continuation) =
          carrier (wordRawLiveAggregate leaves) +
            wordRawAggregateOfStatus .stoppedTPairExhausted leaves := by
  intro leaves
  induction leaves with
  | nil =>
      simp [stoppingBind, wordRawLiveAggregate, wordRawAggregateOfStatus]
  | cons leaf leaves ih =>
      cases leaf with
      | mk status history ledger raw =>
          cases status
          · change wordRawAggregateOfStatus .stoppedTPairExhausted
                (continuation history ledger raw ++ stoppingBind leaves continuation) =
              carrier (raw + wordRawLiveAggregate leaves) +
                wordRawAggregateOfStatus .stoppedTPairExhausted leaves
            rw [wordRawAggregateOfStatus_append,
              hcontinuation history ledger raw, ih, map_add]
            abel
          · rw [stoppingBind_phaseExhausted_cons,
              wordRawAggregateOfStatus_append, ih]
            simp [wordRawAggregateOfStatus, wordRawStatusMatches,
              wordRawLiveAggregate]
          · rw [stoppingBind_tPairExhausted_cons,
              wordRawAggregateOfStatus_append, ih]
            simp [wordRawAggregateOfStatus, wordRawStatusMatches,
              wordRawLiveAggregate]
            abel

private theorem deterministicContinuation_tPairStopped_component
    (U : UnitaryTransport QubitSpace QubitSpace)
    (history) (ledger) (raw : Operator QubitSpace) :
    wordRawAggregateOfStatus .stoppedTPairExhausted
      (deterministicContinuation U history ledger raw) = 0 := by
  simp [deterministicContinuation, deterministicLiveLeaf, wordRawAggregateOfStatus,
    wordRawStatusMatches]

private theorem runDeterministic_tPairStopped_component
    (U : UnitaryTransport QubitSpace QubitSpace) (leaves : List BK05WordRawLeaf) :
    wordRawAggregateOfStatus .stoppedTPairExhausted (runDeterministic U leaves) =
      wordRawAggregateOfStatus .stoppedTPairExhausted leaves := by
  simpa [runDeterministic] using
    stoppingBind_tPairStopped_component (deterministicContinuation U) (0 :
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
      (deterministicContinuation_tPairStopped_component U) leaves

private theorem runTPhaseFrom_live_component
    (t : DensityOperator QubitSpace) (pairAttempts : Nat)
    (sign : BK05WordPolarity) (blocks : Nat) (ledger)
    (history : List Bool) (raw : Operator QubitSpace) :
    wordRawLiveAggregate (runTPhaseFrom t pairAttempts sign blocks ledger history raw) =
      tRetryTargetHitLinear t pairAttempts (tPhaseTarget sign) (12 * blocks) 0 raw := by
  unfold runTPhaseFrom
  rw [importRawLeaves_liveAggregate]
  exact (tRetryTargetHitLinear_apply t pairAttempts (tPhaseTarget sign) (12 * blocks)
    0 ledger history raw).symm

private theorem runTPhaseFrom_phaseStopped_component
    (t : DensityOperator QubitSpace) (pairAttempts : Nat)
    (sign : BK05WordPolarity) (blocks : Nat) (ledger)
    (history : List Bool) (raw : Operator QubitSpace) :
    wordRawAggregateOfStatus .stoppedPhaseExhausted
      (runTPhaseFrom t pairAttempts sign blocks ledger history raw) =
        tRetryPhaseExhaustedLinear t pairAttempts (tPhaseTarget sign) (12 * blocks) 0 raw := by
  unfold runTPhaseFrom
  rw [importRawLeaves_phaseExhaustedAggregate]
  exact (tRetryPhaseExhaustedLinear_apply t pairAttempts (tPhaseTarget sign) (12 * blocks)
    0 ledger history raw).symm

private theorem runTPhaseFrom_tPairStopped_component
    (t : DensityOperator QubitSpace) (pairAttempts : Nat)
    (sign : BK05WordPolarity) (blocks : Nat) (ledger)
    (history : List Bool) (raw : Operator QubitSpace) :
    wordRawAggregateOfStatus .stoppedTPairExhausted
      (runTPhaseFrom t pairAttempts sign blocks ledger history raw) =
        tRetryPairExhaustedLinear t pairAttempts (tPhaseTarget sign) (12 * blocks) 0 raw := by
  unfold runTPhaseFrom
  rw [importRawLeaves_tPairExhaustedAggregate]
  exact (tRetryPairExhaustedLinear_apply t pairAttempts (tPhaseTarget sign) (12 * blocks)
    0 ledger history raw).symm

private theorem runTSignedLetter_live_component
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letter : BK05SignedPhaseLetter (-Real.pi / 6)) (leaves : List BK05WordRawLeaf) :
    wordRawLiveAggregate (runTSignedLetter t pairAttempts blocks letter leaves) =
      match letter with
      | .positive .h => signedHRawLinear .normal (wordRawLiveAggregate leaves)
      | .positive .k => signedKRawLinear .normal (wordRawLiveAggregate leaves)
      | .positive .phase =>
          tRetryTargetHitLinear t pairAttempts (tPhaseTarget .normal) (12 * blocks) 0
            (wordRawLiveAggregate leaves)
      | .negative .h => signedHRawLinear .inverse (wordRawLiveAggregate leaves)
      | .negative .k => signedKRawLinear .inverse (wordRawLiveAggregate leaves)
      | .negative .phase =>
          tRetryTargetHitLinear t pairAttempts (tPhaseTarget .inverse) (12 * blocks) 0
            (wordRawLiveAggregate leaves) := by
  cases letter <;> rename_i atom <;> cases atom <;>
    simp only [runTSignedLetter] <;>
    first
    | simpa [signedHRawLinear, signedHTransport] using
        runDeterministic_live_component (signedHTransport .normal) leaves
    | simpa [signedKRawLinear, signedKTransport] using
        runDeterministic_live_component (signedKTransport .normal) leaves
    | exact stoppingBind_live_component
        (fun history ledger raw => runTPhaseFrom t pairAttempts .normal blocks ledger history raw)
        (tRetryTargetHitLinear t pairAttempts (tPhaseTarget .normal) (12 * blocks) 0)
        (fun history ledger raw =>
          runTPhaseFrom_live_component t pairAttempts .normal blocks ledger history raw) leaves
    | simpa [signedHRawLinear, signedHTransport] using
        runDeterministic_live_component (signedHTransport .inverse) leaves
    | simpa [signedKRawLinear, signedKTransport] using
        runDeterministic_live_component (signedKTransport .inverse) leaves
    | exact stoppingBind_live_component
        (fun history ledger raw => runTPhaseFrom t pairAttempts .inverse blocks ledger history raw)
        (tRetryTargetHitLinear t pairAttempts (tPhaseTarget .inverse) (12 * blocks) 0)
        (fun history ledger raw =>
          runTPhaseFrom_live_component t pairAttempts .inverse blocks ledger history raw) leaves

private theorem runTSignedLetter_phaseStopped_component
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letter : BK05SignedPhaseLetter (-Real.pi / 6)) (leaves : List BK05WordRawLeaf) :
    wordRawAggregateOfStatus .stoppedPhaseExhausted
      (runTSignedLetter t pairAttempts blocks letter leaves) =
      match letter with
      | .positive .h => wordRawAggregateOfStatus .stoppedPhaseExhausted leaves
      | .positive .k => wordRawAggregateOfStatus .stoppedPhaseExhausted leaves
      | .positive .phase =>
          tRetryPhaseExhaustedLinear t pairAttempts (tPhaseTarget .normal) (12 * blocks) 0
            (wordRawLiveAggregate leaves) +
              wordRawAggregateOfStatus .stoppedPhaseExhausted leaves
      | .negative .h => wordRawAggregateOfStatus .stoppedPhaseExhausted leaves
      | .negative .k => wordRawAggregateOfStatus .stoppedPhaseExhausted leaves
      | .negative .phase =>
          tRetryPhaseExhaustedLinear t pairAttempts (tPhaseTarget .inverse) (12 * blocks) 0
            (wordRawLiveAggregate leaves) +
              wordRawAggregateOfStatus .stoppedPhaseExhausted leaves := by
  cases letter <;> rename_i atom <;> cases atom <;>
    simp only [runTSignedLetter] <;>
    first
    | exact runDeterministic_phaseStopped_component (signedHTransport .normal) leaves
    | exact runDeterministic_phaseStopped_component (signedKTransport .normal) leaves
    | exact stoppingBind_phaseStopped_component
        (fun history ledger raw => runTPhaseFrom t pairAttempts .normal blocks ledger history raw)
        (tRetryPhaseExhaustedLinear t pairAttempts (tPhaseTarget .normal) (12 * blocks) 0)
        (fun history ledger raw =>
          runTPhaseFrom_phaseStopped_component t pairAttempts .normal blocks ledger history raw)
          leaves
    | exact runDeterministic_phaseStopped_component (signedHTransport .inverse) leaves
    | exact runDeterministic_phaseStopped_component (signedKTransport .inverse) leaves
    | exact stoppingBind_phaseStopped_component
        (fun history ledger raw => runTPhaseFrom t pairAttempts .inverse blocks ledger history raw)
        (tRetryPhaseExhaustedLinear t pairAttempts (tPhaseTarget .inverse) (12 * blocks) 0)
        (fun history ledger raw =>
          runTPhaseFrom_phaseStopped_component t pairAttempts .inverse blocks ledger history raw)
          leaves

private theorem runTSignedLetter_tPairStopped_component
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letter : BK05SignedPhaseLetter (-Real.pi / 6)) (leaves : List BK05WordRawLeaf) :
    wordRawAggregateOfStatus .stoppedTPairExhausted
      (runTSignedLetter t pairAttempts blocks letter leaves) =
      match letter with
      | .positive .h => wordRawAggregateOfStatus .stoppedTPairExhausted leaves
      | .positive .k => wordRawAggregateOfStatus .stoppedTPairExhausted leaves
      | .positive .phase =>
          tRetryPairExhaustedLinear t pairAttempts (tPhaseTarget .normal) (12 * blocks) 0
            (wordRawLiveAggregate leaves) +
              wordRawAggregateOfStatus .stoppedTPairExhausted leaves
      | .negative .h => wordRawAggregateOfStatus .stoppedTPairExhausted leaves
      | .negative .k => wordRawAggregateOfStatus .stoppedTPairExhausted leaves
      | .negative .phase =>
          tRetryPairExhaustedLinear t pairAttempts (tPhaseTarget .inverse) (12 * blocks) 0
            (wordRawLiveAggregate leaves) +
              wordRawAggregateOfStatus .stoppedTPairExhausted leaves := by
  cases letter <;> rename_i atom <;> cases atom <;>
    simp only [runTSignedLetter] <;>
    first
    | exact runDeterministic_tPairStopped_component (signedHTransport .normal) leaves
    | exact runDeterministic_tPairStopped_component (signedKTransport .normal) leaves
    | exact stoppingBind_tPairStopped_component
        (fun history ledger raw => runTPhaseFrom t pairAttempts .normal blocks ledger history raw)
        (tRetryPairExhaustedLinear t pairAttempts (tPhaseTarget .normal) (12 * blocks) 0)
        (fun history ledger raw =>
          runTPhaseFrom_tPairStopped_component t pairAttempts .normal blocks ledger history raw)
          leaves
    | exact runDeterministic_tPairStopped_component (signedHTransport .inverse) leaves
    | exact runDeterministic_tPairStopped_component (signedKTransport .inverse) leaves
    | exact stoppingBind_tPairStopped_component
        (fun history ledger raw => runTPhaseFrom t pairAttempts .inverse blocks ledger history raw)
        (tRetryPairExhaustedLinear t pairAttempts (tPhaseTarget .inverse) (12 * blocks) 0)
        (fun history ledger raw =>
          runTPhaseFrom_tPairStopped_component t pairAttempts .inverse blocks ledger history raw)
          leaves

private theorem runTSignedWord_live_component
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) (leaves : List BK05WordRawLeaf) :
    wordRawAggregateOfStatus .live (runTSignedWord t pairAttempts blocks letters leaves) =
      tWordLiveLinear t pairAttempts blocks letters (wordRawAggregateOfStatus .live leaves) := by
  induction letters with
  | nil => rfl
  | cons head tail ih =>
      have htailLive :
          wordRawLiveAggregate (runTSignedWord t pairAttempts blocks tail leaves) =
            tWordLiveLinear t pairAttempts blocks tail (wordRawLiveAggregate leaves) := by
        simpa [wordRawLiveAggregate] using ih
      rw [runTSignedWord_cons]
      change wordRawLiveAggregate
          (runTSignedLetter t pairAttempts blocks head
            (runTSignedWord t pairAttempts blocks tail leaves)) =
        tWordLiveLinear t pairAttempts blocks (head :: tail) (wordRawLiveAggregate leaves)
      rw [runTSignedLetter_live_component, htailLive]
      cases head <;> rename_i atom <;> cases atom <;> rfl

private theorem runTSignedWord_phaseStopped_component
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) (leaves : List BK05WordRawLeaf) :
    wordRawAggregateOfStatus .stoppedPhaseExhausted
      (runTSignedWord t pairAttempts blocks letters leaves) =
        tWordPhaseStoppedLinear t pairAttempts blocks letters (wordRawLiveAggregate leaves) +
          wordRawAggregateOfStatus .stoppedPhaseExhausted leaves := by
  induction letters with
  | nil => simp [runTSignedWord, runTPhysicalLetters, tWordPhaseStoppedLinear]
  | cons head tail ih =>
      have htailLive :
          wordRawLiveAggregate (runTSignedWord t pairAttempts blocks tail leaves) =
            tWordLiveLinear t pairAttempts blocks tail (wordRawLiveAggregate leaves) := by
        simpa [wordRawLiveAggregate] using
          runTSignedWord_live_component t pairAttempts blocks tail leaves
      rw [runTSignedWord_cons, runTSignedLetter_phaseStopped_component, ih, htailLive]
      cases head <;> rename_i atom <;> cases atom <;>
        simp [tWordPhaseStoppedLinear, wordRawLiveAggregate, LinearMap.add_apply,
          LinearMap.comp_apply]
      all_goals abel

private theorem runTSignedWord_tPairStopped_component
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) (leaves : List BK05WordRawLeaf) :
    wordRawAggregateOfStatus .stoppedTPairExhausted
      (runTSignedWord t pairAttempts blocks letters leaves) =
        tWordPairStoppedLinear t pairAttempts blocks letters (wordRawLiveAggregate leaves) +
          wordRawAggregateOfStatus .stoppedTPairExhausted leaves := by
  induction letters with
  | nil => simp [runTSignedWord, runTPhysicalLetters, tWordPairStoppedLinear]
  | cons head tail ih =>
      have htailLive :
          wordRawLiveAggregate (runTSignedWord t pairAttempts blocks tail leaves) =
            tWordLiveLinear t pairAttempts blocks tail (wordRawLiveAggregate leaves) := by
        simpa [wordRawLiveAggregate] using
          runTSignedWord_live_component t pairAttempts blocks tail leaves
      rw [runTSignedWord_cons, runTSignedLetter_tPairStopped_component, ih, htailLive]
      cases head <;> rename_i atom <;> cases atom <;>
        simp [tWordPairStoppedLinear, wordRawLiveAggregate, LinearMap.add_apply,
          LinearMap.comp_apply]
      all_goals abel

private noncomputable def tWordTotalLinear
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace :=
  tWordLiveLinear t pairAttempts blocks letters +
    tWordPhaseStoppedLinear t pairAttempts blocks letters +
    tWordPairStoppedLinear t pairAttempts blocks letters

private theorem tWordComponents_total
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) :
    tWordTotalLinear t pairAttempts blocks letters =
      tWordLiveLinear t pairAttempts blocks letters +
        tWordPhaseStoppedLinear t pairAttempts blocks letters +
        tWordPairStoppedLinear t pairAttempts blocks letters :=
  rfl

private theorem tWordPhaseComponents_total
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (sign : BK05WordPolarity) (tail : List (BK05SignedPhaseLetter (-Real.pi / 6))) :
    (tRetryTargetHitLinear t pairAttempts (tPhaseTarget sign) (12 * blocks) 0).comp
          (tWordLiveLinear t pairAttempts blocks tail) +
        (tRetryPhaseExhaustedLinear t pairAttempts (tPhaseTarget sign) (12 * blocks) 0).comp
          (tWordLiveLinear t pairAttempts blocks tail) +
        (tRetryPairExhaustedLinear t pairAttempts (tPhaseTarget sign) (12 * blocks) 0).comp
          (tWordLiveLinear t pairAttempts blocks tail) =
      (tRetryAggregateLinear t pairAttempts (tPhaseTarget sign) (12 * blocks) 0).comp
        (tWordLiveLinear t pairAttempts blocks tail) := by
  apply LinearMap.ext
  intro raw
  simpa only [LinearMap.add_apply, LinearMap.comp_apply] using
    congrArg (fun carrier : Operator QubitSpace →ₗ[Complex] Operator QubitSpace =>
      carrier (tWordLiveLinear t pairAttempts blocks tail raw))
      (tRetryComponentLinear_sum t pairAttempts (tPhaseTarget sign) (12 * blocks) 0)

private theorem runTSignedWord_component_total
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) (leaves : List BK05WordRawLeaf) :
    wordRawAggregate (runTSignedWord t pairAttempts blocks letters leaves) =
      tWordTotalLinear t pairAttempts blocks letters (wordRawLiveAggregate leaves) +
        wordRawAggregateOfStatus .stoppedPhaseExhausted leaves +
        wordRawAggregateOfStatus .stoppedTPairExhausted leaves := by
  rw [wordRawAggregate_partition, wordRawStoppedAggregate]
  simp only [wordRawLiveAggregate]
  rw [runTSignedWord_live_component, runTSignedWord_phaseStopped_component,
    runTSignedWord_tPairStopped_component, tWordComponents_total,
    LinearMap.add_apply, LinearMap.add_apply]
  simp only [wordRawLiveAggregate]
  abel

private theorem tWordLiveLinear_positive
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
      (raw : Operator QubitSpace),
      LinearMap.IsPositive raw →
        LinearMap.IsPositive (tWordLiveLinear t pairAttempts blocks letters raw) := by
  intro letters
  induction letters with
  | nil =>
      intro raw hraw
      simpa [tWordLiveLinear] using hraw
  | cons head tail ih =>
      intro raw hraw
      cases head with
      | positive atom =>
          cases atom with
          | h =>
              simpa [tWordLiveLinear, LinearMap.comp_apply] using
                signedHRawLinear_positive .normal _ (ih raw hraw)
          | k =>
              simpa [tWordLiveLinear, LinearMap.comp_apply] using
                signedKRawLinear_positive .normal _ (ih raw hraw)
          | phase =>
              simpa [tWordLiveLinear, LinearMap.comp_apply] using
                tRetryTargetHitLinear_positive t pairAttempts (tPhaseTarget .normal)
                  (12 * blocks) 0 _ (ih raw hraw)
      | negative atom =>
          cases atom with
          | h =>
              simpa [tWordLiveLinear, LinearMap.comp_apply] using
                signedHRawLinear_positive .inverse _ (ih raw hraw)
          | k =>
              simpa [tWordLiveLinear, LinearMap.comp_apply] using
                signedKRawLinear_positive .inverse _ (ih raw hraw)
          | phase =>
              simpa [tWordLiveLinear, LinearMap.comp_apply] using
                tRetryTargetHitLinear_positive t pairAttempts (tPhaseTarget .inverse)
                  (12 * blocks) 0 _ (ih raw hraw)

private theorem tWordPhaseStoppedLinear_positive
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
      (raw : Operator QubitSpace),
      LinearMap.IsPositive raw →
        LinearMap.IsPositive (tWordPhaseStoppedLinear t pairAttempts blocks letters raw) := by
  intro letters
  induction letters with
  | nil =>
      intro raw hraw
      simp [tWordPhaseStoppedLinear]
  | cons head tail ih =>
      intro raw hraw
      cases head with
      | positive atom =>
          cases atom with
          | h => simpa [tWordPhaseStoppedLinear] using ih raw hraw
          | k => simpa [tWordPhaseStoppedLinear] using ih raw hraw
          | phase =>
              simpa [tWordPhaseStoppedLinear, tWordLiveLinear, LinearMap.add_apply,
                LinearMap.comp_apply] using
                (tRetryPhaseExhaustedLinear_positive t pairAttempts (tPhaseTarget .normal)
                  (12 * blocks) 0 _
                  (tWordLiveLinear_positive t pairAttempts blocks tail raw hraw)).add
                  (ih raw hraw)
      | negative atom =>
          cases atom with
          | h => simpa [tWordPhaseStoppedLinear] using ih raw hraw
          | k => simpa [tWordPhaseStoppedLinear] using ih raw hraw
          | phase =>
              simpa [tWordPhaseStoppedLinear, tWordLiveLinear, LinearMap.add_apply,
                LinearMap.comp_apply] using
                (tRetryPhaseExhaustedLinear_positive t pairAttempts (tPhaseTarget .inverse)
                  (12 * blocks) 0 _
                  (tWordLiveLinear_positive t pairAttempts blocks tail raw hraw)).add
                  (ih raw hraw)

private theorem tWordPairStoppedLinear_positive
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
      (raw : Operator QubitSpace),
      LinearMap.IsPositive raw →
        LinearMap.IsPositive (tWordPairStoppedLinear t pairAttempts blocks letters raw) := by
  intro letters
  induction letters with
  | nil =>
      intro raw hraw
      simp [tWordPairStoppedLinear]
  | cons head tail ih =>
      intro raw hraw
      cases head with
      | positive atom =>
          cases atom with
          | h => simpa [tWordPairStoppedLinear] using ih raw hraw
          | k => simpa [tWordPairStoppedLinear] using ih raw hraw
          | phase =>
              simpa [tWordPairStoppedLinear, tWordLiveLinear, LinearMap.add_apply,
                LinearMap.comp_apply] using
                (tRetryPairExhaustedLinear_positive t pairAttempts (tPhaseTarget .normal)
                  (12 * blocks) 0 _
                  (tWordLiveLinear_positive t pairAttempts blocks tail raw hraw)).add
                  (ih raw hraw)
      | negative atom =>
          cases atom with
          | h => simpa [tWordPairStoppedLinear] using ih raw hraw
          | k => simpa [tWordPairStoppedLinear] using ih raw hraw
          | phase =>
              simpa [tWordPairStoppedLinear, tWordLiveLinear, LinearMap.add_apply,
                LinearMap.comp_apply] using
                (tRetryPairExhaustedLinear_positive t pairAttempts (tPhaseTarget .inverse)
                  (12 * blocks) 0 _
                  (tWordLiveLinear_positive t pairAttempts blocks tail raw hraw)).add
                  (ih raw hraw)

private theorem tWordComponent_trace
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
      (raw : Operator QubitSpace),
      LinearMap.trace Complex QubitSpace
          (tWordLiveLinear t pairAttempts blocks letters raw) +
        LinearMap.trace Complex QubitSpace
          (tWordPhaseStoppedLinear t pairAttempts blocks letters raw) +
        LinearMap.trace Complex QubitSpace
          (tWordPairStoppedLinear t pairAttempts blocks letters raw) =
          LinearMap.trace Complex QubitSpace raw := by
  intro letters
  induction letters with
  | nil =>
      intro raw
      simp [tWordLiveLinear, tWordPhaseStoppedLinear, tWordPairStoppedLinear]
  | cons head tail ih =>
      intro raw
      cases head with
      | positive atom =>
          cases atom with
          | h =>
              simp only [tWordLiveLinear, tWordPhaseStoppedLinear, tWordPairStoppedLinear,
                LinearMap.comp_apply]
              rw [signedHRawLinear_trace]
              exact ih raw
          | k =>
              simp only [tWordLiveLinear, tWordPhaseStoppedLinear, tWordPairStoppedLinear,
                LinearMap.comp_apply]
              rw [signedKRawLinear_trace]
              exact ih raw
          | phase =>
              simp only [tWordLiveLinear, tWordPhaseStoppedLinear, tWordPairStoppedLinear,
                LinearMap.add_apply, LinearMap.comp_apply]
              rw [map_add, map_add]
              calc
                _ = (LinearMap.trace Complex QubitSpace
                      (tRetryTargetHitLinear t pairAttempts (tPhaseTarget .normal)
                        (12 * blocks) 0 (tWordLiveLinear t pairAttempts blocks tail raw)) +
                    LinearMap.trace Complex QubitSpace
                      (tRetryPhaseExhaustedLinear t pairAttempts (tPhaseTarget .normal)
                        (12 * blocks) 0 (tWordLiveLinear t pairAttempts blocks tail raw)) +
                    LinearMap.trace Complex QubitSpace
                      (tRetryPairExhaustedLinear t pairAttempts (tPhaseTarget .normal)
                        (12 * blocks) 0 (tWordLiveLinear t pairAttempts blocks tail raw))) +
                    (LinearMap.trace Complex QubitSpace
                      (tWordPhaseStoppedLinear t pairAttempts blocks tail raw) +
                    LinearMap.trace Complex QubitSpace
                      (tWordPairStoppedLinear t pairAttempts blocks tail raw)) := by abel
                _ = _ := by
                  rw [tRetryComponentLinear_total_trace]
                  simpa only [add_assoc] using ih raw
      | negative atom =>
          cases atom with
          | h =>
              simp only [tWordLiveLinear, tWordPhaseStoppedLinear, tWordPairStoppedLinear,
                LinearMap.comp_apply]
              rw [signedHRawLinear_trace]
              exact ih raw
          | k =>
              simp only [tWordLiveLinear, tWordPhaseStoppedLinear, tWordPairStoppedLinear,
                LinearMap.comp_apply]
              rw [signedKRawLinear_trace]
              exact ih raw
          | phase =>
              simp only [tWordLiveLinear, tWordPhaseStoppedLinear, tWordPairStoppedLinear,
                LinearMap.add_apply, LinearMap.comp_apply]
              rw [map_add, map_add]
              calc
                _ = (LinearMap.trace Complex QubitSpace
                      (tRetryTargetHitLinear t pairAttempts (tPhaseTarget .inverse)
                        (12 * blocks) 0 (tWordLiveLinear t pairAttempts blocks tail raw)) +
                    LinearMap.trace Complex QubitSpace
                      (tRetryPhaseExhaustedLinear t pairAttempts (tPhaseTarget .inverse)
                        (12 * blocks) 0 (tWordLiveLinear t pairAttempts blocks tail raw)) +
                    LinearMap.trace Complex QubitSpace
                      (tRetryPairExhaustedLinear t pairAttempts (tPhaseTarget .inverse)
                        (12 * blocks) 0 (tWordLiveLinear t pairAttempts blocks tail raw))) +
                    (LinearMap.trace Complex QubitSpace
                      (tWordPhaseStoppedLinear t pairAttempts blocks tail raw) +
                    LinearMap.trace Complex QubitSpace
                      (tWordPairStoppedLinear t pairAttempts blocks tail raw)) := by abel
                _ = _ := by
                  rw [tRetryComponentLinear_total_trace]
                  simpa only [add_assoc] using ih raw

private theorem tWordComponent_trace_nonneg
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
    (raw : Operator QubitSpace) (hraw : LinearMap.IsPositive raw) :
    0 ≤ (LinearMap.trace Complex QubitSpace
      (tWordLiveLinear t pairAttempts blocks letters raw)).re ∧
      0 ≤ (LinearMap.trace Complex QubitSpace
        (tWordPhaseStoppedLinear t pairAttempts blocks letters raw)).re ∧
      0 ≤ (LinearMap.trace Complex QubitSpace
        (tWordPairStoppedLinear t pairAttempts blocks letters raw)).re := by
  refine ⟨?_, ?_, ?_⟩
  · exact (Complex.nonneg_iff.mp
      (tWordLiveLinear_positive t pairAttempts blocks letters raw hraw).trace_nonneg).1
  · exact (Complex.nonneg_iff.mp
      (tWordPhaseStoppedLinear_positive t pairAttempts blocks letters raw hraw).trace_nonneg).1
  · exact (Complex.nonneg_iff.mp
      (tWordPairStoppedLinear_positive t pairAttempts blocks letters raw hraw).trace_nonneg).1

private theorem tWord_live_trace_le
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
    (raw : Operator QubitSpace) (hraw : LinearMap.IsPositive raw) :
    (LinearMap.trace Complex QubitSpace
      (tWordLiveLinear t pairAttempts blocks letters raw)).re ≤
      (LinearMap.trace Complex QubitSpace raw).re := by
  have hstopped := (tWordComponent_trace_nonneg t pairAttempts blocks letters raw hraw).2
  have htrace := congrArg Complex.re (tWordComponent_trace t pairAttempts blocks letters raw)
  simp only [Complex.add_re] at htrace
  linarith

/- Task 5e checkpoint 2C: T signed-word ideal action and source stability. -/

/-- The literal T target-hit coefficient.  The target guard precedes the
budget guard because a retry already at its target succeeds without consuming
another supplied pair. -/
private def tTargetHitCoeff (pairAttempts : Nat) (target : ZMod 12) :
    Nat → ZMod 12 → Real
  | remaining, position =>
      if position = target then 1 else
        match remaining with
        | 0 => 0
        | nextRemaining + 1 =>
            ((1 - (1 / 3 : Real) ^ pairAttempts) / 2) *
              (tTargetHitCoeff pairAttempts target nextRemaining (position + 1) +
                tTargetHitCoeff pairAttempts target nextRemaining (position - 1))

private theorem tTargetHitCoeff_target
    (pairAttempts : Nat) (target : ZMod 12) (remaining : Nat) :
    tTargetHitCoeff pairAttempts target remaining target = 1 := by
  cases remaining <;> simp [tTargetHitCoeff]

private theorem tTargetHitCoeff_zero_pairAttempts_of_ne
    (target : ZMod 12) : ∀ (remaining : Nat) (position : ZMod 12),
    position ≠ target → tTargetHitCoeff 0 target remaining position = 0 := by
  intro remaining
  induction remaining with
  | zero =>
      intro position hposition
      simp [tTargetHitCoeff, hposition]
  | succ remaining ih =>
      intro position hposition
      simp [tTargetHitCoeff, hposition]

/-- At the ideal T source, one accepted supplier branch has its literal
`2/3` preparation weight and `1/2` injection-coin weight, hence exactly
`1/3` of the corresponding signed phase action. -/
private theorem tMagicAcceptedPhaseRaw_branch_ideal_action
    (data : Operator QubitSpace) (hdata : LinearMap.IsPositive data) (coin : Bool) :
    phaseBranchRaw (tAcceptedPhaseRaw tMagicState) data coin =
      (1 / 3 : Complex) •
        (OneQubitMagic.phaseShiftTransport
          (oneShotSignedAngle (-Real.pi / 6) coin)).conjOperator data := by
  rw [tMagicAcceptedPhaseRaw_eq, phaseBranchRaw_resource_smul,
    phaseBranchRaw_ideal_action (-Real.pi / 6) data hdata coin]
  rw [smul_smul]
  norm_num

private theorem phaseCycleTargetChannel_zero_twelve (data : Operator QubitSpace) :
    phaseCycleTargetChannel 12 (0 : ZMod 12) data = data := by
  unfold phaseCycleTargetChannel
  simp only [ZMod.val_zero, Nat.cast_zero, mul_zero]
  change (OneQubitMagic.phaseShiftTransport 0).conjOperator data = data
  unfold UnitaryTransport.conjOperator
  apply LinearMap.ext
  intro psi
  change OneQubitMagic.phaseShiftOperator 0
      (data (OneQubitMagic.phaseShiftOperator (-0) psi)) = data psi
  rw [OneQubitMagic.phaseShiftOperator_zero]
  simp

private theorem phaseCycleTargetChannel_twelve_add_one
    (residue : ZMod 12) (data : Operator QubitSpace) :
    phaseCycleTargetChannel 12 residue
        ((OneQubitMagic.phaseShiftTransport (-Real.pi / 6)).conjOperator data) =
      phaseCycleTargetChannel 12 (residue + 1) data := by
  unfold phaseCycleTargetChannel
  change (OneQubitMagic.phaseShiftTransport
      (phaseCycleAngle 12 * residue.val)).conjOperator
        ((OneQubitMagic.phaseShiftTransport
          (-Real.pi / 6)).conjOperator data) =
    (OneQubitMagic.phaseShiftTransport
      (phaseCycleAngle 12 * (residue + 1).val)).conjOperator data
  rw [phaseShiftTransport_conjOperator_add]
  apply phaseShiftTransport_conjOperator_eq_of_operator_eq
  rw [phaseCycleAngle_twelve]
  by_cases hnowrap : residue.val + 1 < 12
  · have hval : (residue + 1).val = residue.val + 1 :=
      ZMod.val_add_of_lt hnowrap
    rw [hval]
    push_cast
    congr 1
    ring
  · have hresidue : residue.val = 11 := by
      have hlt := residue.val_lt
      omega
    have hval : (residue + 1).val = 0 := by
      have hone : (1 : ZMod 12).val = 1 := ZMod.val_one'' (by norm_num)
      rw [ZMod.val_add, hone, hresidue]
    rw [hresidue, hval]
    norm_num
    convert phaseShiftOperator_add_full_turn 0 (-1) using 1 <;>
      try { congr 1 <;> ring } <;> simp

private theorem phaseCycleTargetChannel_twelve_sub_one
    (residue : ZMod 12) (data : Operator QubitSpace) :
    phaseCycleTargetChannel 12 residue
        ((OneQubitMagic.phaseShiftTransport (Real.pi / 6)).conjOperator data) =
      phaseCycleTargetChannel 12 (residue - 1) data := by
  unfold phaseCycleTargetChannel
  change (OneQubitMagic.phaseShiftTransport
      (phaseCycleAngle 12 * residue.val)).conjOperator
        ((OneQubitMagic.phaseShiftTransport
          (Real.pi / 6)).conjOperator data) =
    (OneQubitMagic.phaseShiftTransport
      (phaseCycleAngle 12 * (residue - 1).val)).conjOperator data
  rw [phaseShiftTransport_conjOperator_add]
  apply phaseShiftTransport_conjOperator_eq_of_operator_eq
  rw [phaseCycleAngle_twelve]
  by_cases hzero : residue = 0
  · subst residue
    simp only [ZMod.val_zero, zero_sub, ZMod.val_neg_one, Nat.cast_zero,
      Nat.cast_ofNat]
    have hperiod := phaseShiftOperator_add_full_turn (-11 * Real.pi / 6) 1
    convert hperiod using 1 <;> try { congr 1 <;> ring } <;> simp
  · have hpositive : 1 ≤ residue.val := (ZMod.val_pos.mpr hzero)
    have hval : (residue - 1).val = residue.val - 1 := by
      have hone : (1 : ZMod 12).val = 1 := by decide
      simpa only [hone] using
        (ZMod.val_sub (a := residue) (b := (1 : ZMod 12))
          (by rw [hone]; exact hpositive))
    rw [hval]
    push_cast [hpositive]
    congr 1
    ring

private theorem tPhaseTargetChannel_true_step
    (sign : BK05WordPolarity) (position : ZMod 12) (data : Operator QubitSpace) :
    phaseCycleTargetChannel 12 (tPhaseTarget sign - (position + 1))
        ((OneQubitMagic.phaseShiftTransport
          (oneShotSignedAngle (-Real.pi / 6) true)).conjOperator data) =
      phaseCycleTargetChannel 12 (tPhaseTarget sign - position) data := by
  have hresidue :
      tPhaseTarget sign - (position + 1) + 1 = tPhaseTarget sign - position := by
    module
  simpa [oneShotSignedAngle, hresidue] using
    phaseCycleTargetChannel_twelve_add_one
      (tPhaseTarget sign - (position + 1)) data

private theorem tPhaseTargetChannel_false_step
    (sign : BK05WordPolarity) (position : ZMod 12) (data : Operator QubitSpace) :
    phaseCycleTargetChannel 12 (tPhaseTarget sign - (position - 1))
        ((OneQubitMagic.phaseShiftTransport
          (oneShotSignedAngle (-Real.pi / 6) false)).conjOperator data) =
      phaseCycleTargetChannel 12 (tPhaseTarget sign - position) data := by
  have hresidue :
      tPhaseTarget sign - (position - 1) - 1 = tPhaseTarget sign - position := by
    module
  rw [show oneShotSignedAngle (-Real.pi / 6) false = Real.pi / 6 by
    simp [oneShotSignedAngle]
    ring]
  simpa [hresidue] using phaseCycleTargetChannel_twelve_sub_one
    (tPhaseTarget sign - (position - 1)) data

/-- The ideal bounded supplier realizes the geometric accepted-pair factor
on any two continuations which implement the same final action after their
respective signed injection branches. -/
private theorem tSupplyTargetHitLinear_ideal_action
    (nextTrue nextFalse action : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (trueCoeff falseCoeff : Real)
    (htrue : ∀ raw, LinearMap.IsPositive raw →
      nextTrue
          ((OneQubitMagic.phaseShiftTransport
            (oneShotSignedAngle (-Real.pi / 6) true)).conjOperator raw) =
        (trueCoeff : Complex) • action raw)
    (hfalse : ∀ raw, LinearMap.IsPositive raw →
      nextFalse
          ((OneQubitMagic.phaseShiftTransport
            (oneShotSignedAngle (-Real.pi / 6) false)).conjOperator raw) =
        (falseCoeff : Complex) • action raw) :
    ∀ (attempts : Nat) (data : Operator QubitSpace), LinearMap.IsPositive data →
      tSupplyTargetHitLinear tMagicState attempts nextTrue nextFalse data =
        ((((1 - (1 / 3 : Real) ^ attempts) / 2) *
          (trueCoeff + falseCoeff) : Real) : Complex) • action data := by
  intro attempts
  induction attempts with
  | zero =>
      intro data hdata
      simp [tSupplyTargetHitLinear, tSupplyStoppingComponentLinear]
  | succ attempts ih =>
      intro data hdata
      change nextTrue (phaseBranchRaw (tAcceptedPhaseRaw tMagicState) data true) +
          nextFalse (phaseBranchRaw (tAcceptedPhaseRaw tMagicState) data false) +
          tSupplyTargetHitLinear tMagicState attempts nextTrue nextFalse
            (tRejectedDataRaw data tMagicState) = _
      rw [tMagicAcceptedPhaseRaw_branch_ideal_action data hdata true,
        tMagicAcceptedPhaseRaw_branch_ideal_action data hdata false,
        tMagicRejectedDataRaw_eq]
      rw [nextTrue.map_smul, nextFalse.map_smul,
        (tSupplyTargetHitLinear tMagicState attempts nextTrue nextFalse).map_smul]
      rw [htrue data hdata, hfalse data hdata, ih data hdata]
      simp only [smul_smul, ← add_smul]
      congr 1
      push_cast
      ring

/-- The live target-hit component of the ideal T retry is the exact relative
order-twelve phase action, multiplied by the literal bounded-supplier
coefficient. -/
private theorem tRetryTargetHitLinear_ideal_action_relative
    (pairAttempts : Nat) (sign : BK05WordPolarity) :
    ∀ (remaining : Nat) (position : ZMod 12) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      tRetryTargetHitLinear tMagicState pairAttempts (tPhaseTarget sign)
          remaining position data =
        (tTargetHitCoeff pairAttempts (tPhaseTarget sign) remaining position : Complex) •
          phaseCycleTargetChannel 12 (tPhaseTarget sign - position) data := by
  intro remaining
  induction remaining with
  | zero =>
      intro position data hdata
      by_cases hposition : position = tPhaseTarget sign
      · subst position
        simp [tRetryTargetHitLinear, tTargetHitCoeff,
          phaseCycleTargetChannel_zero_twelve]
      · simp [tRetryTargetHitLinear, tTargetHitCoeff, hposition]
  | succ remaining ih =>
      intro position data hdata
      by_cases hposition : position = tPhaseTarget sign
      · subst position
        simp [tRetryTargetHitLinear, tTargetHitCoeff,
          phaseCycleTargetChannel_zero_twelve]
      · let nextTrue := tRetryTargetHitLinear tMagicState pairAttempts
          (tPhaseTarget sign) remaining (position + 1)
        let nextFalse := tRetryTargetHitLinear tMagicState pairAttempts
          (tPhaseTarget sign) remaining (position - 1)
        let action := phaseCycleTargetChannel 12 (tPhaseTarget sign - position)
        let trueCoeff :=
          tTargetHitCoeff pairAttempts (tPhaseTarget sign) remaining (position + 1)
        let falseCoeff :=
          tTargetHitCoeff pairAttempts (tPhaseTarget sign) remaining (position - 1)
        have htrue : ∀ raw, LinearMap.IsPositive raw →
            nextTrue
                ((OneQubitMagic.phaseShiftTransport
                  (oneShotSignedAngle (-Real.pi / 6) true)).conjOperator raw) =
              (trueCoeff : Complex) • action raw := by
          intro raw hraw
          rw [show nextTrue
              ((OneQubitMagic.phaseShiftTransport
                (oneShotSignedAngle (-Real.pi / 6) true)).conjOperator raw) =
              (trueCoeff : Complex) •
                phaseCycleTargetChannel 12
                  (tPhaseTarget sign - (position + 1))
                    ((OneQubitMagic.phaseShiftTransport
                      (oneShotSignedAngle (-Real.pi / 6) true)).conjOperator raw) by
                exact ih (position + 1) _
                  ((OneQubitMagic.phaseShiftTransport
                    (oneShotSignedAngle (-Real.pi / 6) true)).isPositive_conjOperator hraw)]
          rw [tPhaseTargetChannel_true_step]
        have hfalse : ∀ raw, LinearMap.IsPositive raw →
            nextFalse
                ((OneQubitMagic.phaseShiftTransport
                  (oneShotSignedAngle (-Real.pi / 6) false)).conjOperator raw) =
              (falseCoeff : Complex) • action raw := by
          intro raw hraw
          rw [show nextFalse
              ((OneQubitMagic.phaseShiftTransport
                (oneShotSignedAngle (-Real.pi / 6) false)).conjOperator raw) =
              (falseCoeff : Complex) •
                phaseCycleTargetChannel 12
                  (tPhaseTarget sign - (position - 1))
                    ((OneQubitMagic.phaseShiftTransport
                      (oneShotSignedAngle (-Real.pi / 6) false)).conjOperator raw) by
                exact ih (position - 1) _
                  ((OneQubitMagic.phaseShiftTransport
                    (oneShotSignedAngle (-Real.pi / 6) false)).isPositive_conjOperator hraw)]
          rw [tPhaseTargetChannel_false_step]
        have hsupply := tSupplyTargetHitLinear_ideal_action
          nextTrue nextFalse action trueCoeff falseCoeff htrue hfalse
          pairAttempts data hdata
        simpa [tRetryTargetHitLinear, tTargetHitCoeff, hposition, nextTrue,
          nextFalse, action, trueCoeff, falseCoeff] using hsupply

/-- The literal target-hit leaf aggregate agrees with the exact ideal
order-twelve action; supplier-exhausted and phase-exhausted leaves remain in
their separate components. -/
private theorem tRetry_ideal_targetHit_action
    (pairAttempts : Nat) (sign : BK05WordPolarity) (remaining : Nat)
    (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
    (data : Operator QubitSpace) (hdata : LinearMap.IsPositive data) :
    rawAggregateOfKind .targetHit
        (tRetry tMagicState pairAttempts (tPhaseTarget sign) remaining 0
          ledger history data) =
      (tTargetHitCoeff pairAttempts (tPhaseTarget sign) remaining 0 : Complex) •
        phaseCycleTargetChannel 12 (tPhaseTarget sign) data := by
  rw [← tRetryTargetHitLinear_apply tMagicState pairAttempts (tPhaseTarget sign)
    remaining 0 ledger history data]
  simpa using tRetryTargetHitLinear_ideal_action_relative pairAttempts sign
    remaining 0 data hdata

/-- The fixed-angle state action underneath each ideal T-word letter. -/
private noncomputable def tFixedIdealLetterStateLinear :
    BK05SignedPhaseLetter (-Real.pi / 6) → Operator QubitSpace
  | .positive .h => (signedHTransport .normal).toLinearEquiv.toLinearMap
  | .positive .k => (signedKTransport .normal).toLinearEquiv.toLinearMap
  | .positive .phase => phaseCycleTargetAction 12 (tPhaseTarget .normal)
  | .negative .h => (signedHTransport .inverse).toLinearEquiv.toLinearMap
  | .negative .k => (signedKTransport .inverse).toLinearEquiv.toLinearMap
  | .negative .phase => phaseCycleTargetAction 12 (tPhaseTarget .inverse)

/-- The operator-space action induced by one fixed-angle ideal T-word letter. -/
private noncomputable def tFixedIdealLetterLinear :
    BK05SignedPhaseLetter (-Real.pi / 6) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | .positive .h => signedHRawLinear .normal
  | .positive .k => signedKRawLinear .normal
  | .positive .phase => phaseCycleTargetChannel 12 (tPhaseTarget .normal)
  | .negative .h => signedHRawLinear .inverse
  | .negative .k => signedKRawLinear .inverse
  | .negative .phase => phaseCycleTargetChannel 12 (tPhaseTarget .inverse)

private theorem tFixedIdealLetterStateLinear_eval
    (letter : BK05SignedPhaseLetter (-Real.pi / 6)) :
    tFixedIdealLetterStateLinear letter =
      Matrix.toEuclideanLin
        ((BK05SignedPhaseLetter.eval (-Real.pi / 6) letter :
          Matrix (Fin 2) (Fin 2) Complex)) := by
  cases letter with
  | positive atom =>
      cases atom with
      | h =>
          simpa [tFixedIdealLetterStateLinear, signedHLetter,
            BK05SignedPhaseLetter.eval, BK05PhaseAtom.eval] using
            signedHTransport_operator_eq_eval (-Real.pi / 6) .normal
      | k =>
          simpa [tFixedIdealLetterStateLinear, signedKLetter,
            BK05SignedPhaseLetter.eval, BK05PhaseAtom.eval] using
            signedKTransport_operator_eq_eval (-Real.pi / 6) .normal
      | phase =>
          apply LinearMap.ext
          intro psi
          change phaseCycleTargetAction 12 (1 : ZMod 12) psi =
            Matrix.toEuclideanLin
              ((phaseShiftGate (-Real.pi / 6) : UnitaryGate (Fin 2)) :
                Matrix (Fin 2) (Fin 2) Complex) psi
          rw [IdealResourceUniversality.tResource_targetAction_one]
          simpa only [OneQubitMagic.phaseShiftTransport_apply] using
            (phaseShiftGate_apply (-Real.pi / 6) psi).symm
  | negative atom =>
      cases atom with
      | h =>
          simpa [tFixedIdealLetterStateLinear, signedHLetter,
            BK05SignedPhaseLetter.eval, BK05PhaseAtom.eval] using
            signedHTransport_operator_eq_eval (-Real.pi / 6) .inverse
      | k =>
          simpa [tFixedIdealLetterStateLinear, signedKLetter,
            BK05SignedPhaseLetter.eval, BK05PhaseAtom.eval] using
            signedKTransport_operator_eq_eval (-Real.pi / 6) .inverse
      | phase =>
          apply LinearMap.ext
          intro psi
          change phaseCycleTargetAction 12 (-1 : ZMod 12) psi =
            Matrix.toEuclideanLin
              (((phaseShiftGate (-Real.pi / 6))⁻¹ : UnitaryGate (Fin 2)) :
                Matrix (Fin 2) (Fin 2) Complex) psi
          have hangle : -(-Real.pi / 6) = Real.pi / 6 := by ring
          rw [phaseCycleTargetAction_twelve_neg_one, phaseShiftGate_inverse, hangle]
          simpa only [OneQubitMagic.phaseShiftTransport_apply] using
            (phaseShiftGate_apply (Real.pi / 6) psi).symm

private noncomputable def tFixedIdealWordLinear :
    List (BK05SignedPhaseLetter (-Real.pi / 6)) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | [] => LinearMap.id
  | letter :: tail => (tFixedIdealLetterLinear letter).comp (tFixedIdealWordLinear tail)

private theorem tFixedIdealWordLinear_positive :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
      (data : Operator QubitSpace),
      LinearMap.IsPositive data → LinearMap.IsPositive (tFixedIdealWordLinear letters data) := by
  intro letters
  induction letters with
  | nil =>
      intro data hdata
      simpa [tFixedIdealWordLinear] using hdata
  | cons letter tail ih =>
      intro data hdata
      cases letter with
      | positive atom =>
          cases atom with
          | h =>
              exact signedHRawLinear_positive .normal _ (ih data hdata)
          | k =>
              exact signedKRawLinear_positive .normal _ (ih data hdata)
          | phase =>
              simpa [tFixedIdealWordLinear, tFixedIdealLetterLinear,
                phaseCycleTargetChannel, LinearMap.comp_apply] using
                (OneQubitMagic.phaseShiftTransport
                  (phaseCycleAngle 12 * (tPhaseTarget .normal).val)).isPositive_conjOperator
                  (ih data hdata)
      | negative atom =>
          cases atom with
          | h =>
              exact signedHRawLinear_positive .inverse _ (ih data hdata)
          | k =>
              exact signedKRawLinear_positive .inverse _ (ih data hdata)
          | phase =>
              simpa [tFixedIdealWordLinear, tFixedIdealLetterLinear,
                phaseCycleTargetChannel, LinearMap.comp_apply] using
                (OneQubitMagic.phaseShiftTransport
                  (phaseCycleAngle 12 * (tPhaseTarget .inverse).val)).isPositive_conjOperator
                  (ih data hdata)

private theorem tFixedIdealLetterLinear_trace
    (letter : BK05SignedPhaseLetter (-Real.pi / 6))
    (data : Operator QubitSpace) :
    LinearMap.trace Complex QubitSpace (tFixedIdealLetterLinear letter data) =
      LinearMap.trace Complex QubitSpace data := by
  cases letter with
  | positive atom =>
      cases atom with
      | h => simpa [tFixedIdealLetterLinear] using signedHRawLinear_trace .normal data
      | k => simpa [tFixedIdealLetterLinear] using signedKRawLinear_trace .normal data
      | phase =>
          simpa [tFixedIdealLetterLinear] using
            phaseCycleTargetChannel_trace 12 (tPhaseTarget .normal) data
  | negative atom =>
      cases atom with
      | h => simpa [tFixedIdealLetterLinear] using signedHRawLinear_trace .inverse data
      | k => simpa [tFixedIdealLetterLinear] using signedKRawLinear_trace .inverse data
      | phase =>
          simpa [tFixedIdealLetterLinear] using
            phaseCycleTargetChannel_trace 12 (tPhaseTarget .inverse) data

private theorem tFixedIdealWordLinear_trace :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
      (data : Operator QubitSpace),
      LinearMap.trace Complex QubitSpace (tFixedIdealWordLinear letters data) =
        LinearMap.trace Complex QubitSpace data := by
  intro letters
  induction letters with
  | nil =>
      intro data
      rfl
  | cons letter tail ih =>
      intro data
      simpa [tFixedIdealWordLinear, LinearMap.comp_apply] using
        (tFixedIdealLetterLinear_trace letter
          (tFixedIdealWordLinear tail data)).trans (ih data)

private noncomputable def tWordLiveCoeff (pairAttempts blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 6)) → Complex
  | [] => 1
  | .positive .h :: tail => tWordLiveCoeff pairAttempts blocks tail
  | .positive .k :: tail => tWordLiveCoeff pairAttempts blocks tail
  | .positive .phase :: tail =>
      (tTargetHitCoeff pairAttempts (tPhaseTarget .normal) (12 * blocks) 0 : Complex) *
        tWordLiveCoeff pairAttempts blocks tail
  | .negative .h :: tail => tWordLiveCoeff pairAttempts blocks tail
  | .negative .k :: tail => tWordLiveCoeff pairAttempts blocks tail
  | .negative .phase :: tail =>
      (tTargetHitCoeff pairAttempts (tPhaseTarget .inverse) (12 * blocks) 0 : Complex) *
        tWordLiveCoeff pairAttempts blocks tail

private def tWordLiveProbability (pairAttempts blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 6)) → Real
  | [] => 1
  | .positive .h :: tail => tWordLiveProbability pairAttempts blocks tail
  | .positive .k :: tail => tWordLiveProbability pairAttempts blocks tail
  | .positive .phase :: tail =>
      tTargetHitCoeff pairAttempts (tPhaseTarget .normal) (12 * blocks) 0 *
        tWordLiveProbability pairAttempts blocks tail
  | .negative .h :: tail => tWordLiveProbability pairAttempts blocks tail
  | .negative .k :: tail => tWordLiveProbability pairAttempts blocks tail
  | .negative .phase :: tail =>
      tTargetHitCoeff pairAttempts (tPhaseTarget .inverse) (12 * blocks) 0 *
        tWordLiveProbability pairAttempts blocks tail

private theorem tWordLiveCoeff_eq_probability (pairAttempts blocks : Nat) :
    ∀ letters : List (BK05SignedPhaseLetter (-Real.pi / 6)),
      tWordLiveCoeff pairAttempts blocks letters =
        (tWordLiveProbability pairAttempts blocks letters : Complex) := by
  intro letters
  induction letters with
  | nil => simp [tWordLiveCoeff, tWordLiveProbability]
  | cons letter tail ih =>
      cases letter with
      | positive atom =>
          cases atom <;>
            simp [tWordLiveCoeff, tWordLiveProbability, ih]
      | negative atom =>
          cases atom <;>
            simp [tWordLiveCoeff, tWordLiveProbability, ih]

private theorem tWordLiveLinear_ideal_action
    (pairAttempts blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
      (data : Operator QubitSpace),
      LinearMap.IsPositive data →
        tWordLiveLinear tMagicState pairAttempts blocks letters data =
          tWordLiveCoeff pairAttempts blocks letters •
            tFixedIdealWordLinear letters data := by
  intro letters
  induction letters with
  | nil =>
      intro data hdata
      simp [tWordLiveLinear, tWordLiveCoeff, tFixedIdealWordLinear]
  | cons letter tail ih =>
      intro data hdata
      have htailPositive : LinearMap.IsPositive (tFixedIdealWordLinear tail data) :=
        tFixedIdealWordLinear_positive tail data hdata
      cases letter with
      | positive atom =>
          cases atom with
          | h =>
              change signedHRawLinear .normal
                    (tWordLiveLinear tMagicState pairAttempts blocks tail data) =
                  tWordLiveCoeff pairAttempts blocks tail •
                    signedHRawLinear .normal (tFixedIdealWordLinear tail data)
              rw [ih data hdata]
              exact (signedHRawLinear .normal).map_smul _ _
          | k =>
              change signedKRawLinear .normal
                    (tWordLiveLinear tMagicState pairAttempts blocks tail data) =
                  tWordLiveCoeff pairAttempts blocks tail •
                    signedKRawLinear .normal (tFixedIdealWordLinear tail data)
              rw [ih data hdata]
              exact (signedKRawLinear .normal).map_smul _ _
          | phase =>
              change tRetryTargetHitLinear tMagicState pairAttempts (tPhaseTarget .normal)
                    (12 * blocks) 0
                    (tWordLiveLinear tMagicState pairAttempts blocks tail data) =
                  ((tTargetHitCoeff pairAttempts (tPhaseTarget .normal)
                      (12 * blocks) 0 : Complex) *
                    tWordLiveCoeff pairAttempts blocks tail) •
                    phaseCycleTargetChannel 12 (tPhaseTarget .normal)
                      (tFixedIdealWordLinear tail data)
              calc
                _ = tRetryTargetHitLinear tMagicState pairAttempts (tPhaseTarget .normal)
                      (12 * blocks) 0
                      (tWordLiveCoeff pairAttempts blocks tail •
                        tFixedIdealWordLinear tail data) := by rw [ih data hdata]
                _ = tWordLiveCoeff pairAttempts blocks tail •
                    tRetryTargetHitLinear tMagicState pairAttempts (tPhaseTarget .normal)
                      (12 * blocks) 0 (tFixedIdealWordLinear tail data) :=
                  (tRetryTargetHitLinear tMagicState pairAttempts (tPhaseTarget .normal)
                    (12 * blocks) 0).map_smul _ _
                _ = tWordLiveCoeff pairAttempts blocks tail •
                    ((tTargetHitCoeff pairAttempts (tPhaseTarget .normal)
                        (12 * blocks) 0 : Complex) •
                      phaseCycleTargetChannel 12 (tPhaseTarget .normal)
                        (tFixedIdealWordLinear tail data)) := by
                          rw [show tRetryTargetHitLinear tMagicState pairAttempts
                              (tPhaseTarget .normal) (12 * blocks) 0
                              (tFixedIdealWordLinear tail data) =
                            (tTargetHitCoeff pairAttempts (tPhaseTarget .normal)
                                (12 * blocks) 0 : Complex) •
                              phaseCycleTargetChannel 12 (tPhaseTarget .normal)
                                (tFixedIdealWordLinear tail data) by
                            simpa using tRetryTargetHitLinear_ideal_action_relative
                              pairAttempts .normal (12 * blocks) 0
                              (tFixedIdealWordLinear tail data) htailPositive]
                _ = _ := by rw [smul_smul]; congr 1; ring

      | negative atom =>
          cases atom with
          | h =>
              change signedHRawLinear .inverse
                    (tWordLiveLinear tMagicState pairAttempts blocks tail data) =
                  tWordLiveCoeff pairAttempts blocks tail •
                    signedHRawLinear .inverse (tFixedIdealWordLinear tail data)
              rw [ih data hdata]
              exact (signedHRawLinear .inverse).map_smul _ _
          | k =>
              change signedKRawLinear .inverse
                    (tWordLiveLinear tMagicState pairAttempts blocks tail data) =
                  tWordLiveCoeff pairAttempts blocks tail •
                    signedKRawLinear .inverse (tFixedIdealWordLinear tail data)
              rw [ih data hdata]
              exact (signedKRawLinear .inverse).map_smul _ _
          | phase =>
              change tRetryTargetHitLinear tMagicState pairAttempts (tPhaseTarget .inverse)
                    (12 * blocks) 0
                    (tWordLiveLinear tMagicState pairAttempts blocks tail data) =
                  ((tTargetHitCoeff pairAttempts (tPhaseTarget .inverse)
                      (12 * blocks) 0 : Complex) *
                    tWordLiveCoeff pairAttempts blocks tail) •
                    phaseCycleTargetChannel 12 (tPhaseTarget .inverse)
                      (tFixedIdealWordLinear tail data)
              calc
                _ = tRetryTargetHitLinear tMagicState pairAttempts (tPhaseTarget .inverse)
                      (12 * blocks) 0
                      (tWordLiveCoeff pairAttempts blocks tail •
                        tFixedIdealWordLinear tail data) := by rw [ih data hdata]
                _ = tWordLiveCoeff pairAttempts blocks tail •
                    tRetryTargetHitLinear tMagicState pairAttempts (tPhaseTarget .inverse)
                      (12 * blocks) 0 (tFixedIdealWordLinear tail data) :=
                  (tRetryTargetHitLinear tMagicState pairAttempts (tPhaseTarget .inverse)
                    (12 * blocks) 0).map_smul _ _
                _ = tWordLiveCoeff pairAttempts blocks tail •
                    ((tTargetHitCoeff pairAttempts (tPhaseTarget .inverse)
                        (12 * blocks) 0 : Complex) •
                      phaseCycleTargetChannel 12 (tPhaseTarget .inverse)
                        (tFixedIdealWordLinear tail data)) := by
                          rw [show tRetryTargetHitLinear tMagicState pairAttempts
                              (tPhaseTarget .inverse) (12 * blocks) 0
                              (tFixedIdealWordLinear tail data) =
                            (tTargetHitCoeff pairAttempts (tPhaseTarget .inverse)
                                (12 * blocks) 0 : Complex) •
                              phaseCycleTargetChannel 12 (tPhaseTarget .inverse)
                                (tFixedIdealWordLinear tail data) by
                            simpa using tRetryTargetHitLinear_ideal_action_relative
                              pairAttempts .inverse (12 * blocks) 0
                              (tFixedIdealWordLinear tail data) htailPositive]
                _ = _ := by rw [smul_smul]; congr 1; ring

private theorem tSupplyTargetHitLinear_comp
    (t : DensityOperator QubitSpace) (attempts : Nat)
    (success nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    success.comp (tSupplyTargetHitLinear t attempts nextTrue nextFalse) =
      tSupplyTargetHitLinear t attempts (success.comp nextTrue) (success.comp nextFalse) := by
  induction attempts with
  | zero =>
      apply LinearMap.ext
      intro data
      simp [tSupplyTargetHitLinear, tSupplyStoppingComponentLinear]
  | succ attempts ih =>
      apply LinearMap.ext
      intro data
      simp only [tSupplyTargetHitLinear, tSupplyStoppingComponentLinear,
        LinearMap.comp_apply, LinearMap.add_apply, phaseBranchRawLinear_apply,
        tRejectedDataRawLinear_apply]
      rw [map_add, map_add]
      have htail := congrArg (fun carrier :
          Operator QubitSpace →ₗ[Complex] Operator QubitSpace =>
        carrier (tRejectedDataRaw data t)) ih
      change success (nextTrue (phaseBranchRaw (tAcceptedPhaseRaw t) data true)) +
          success (nextFalse (phaseBranchRaw (tAcceptedPhaseRaw t) data false)) +
          success (tSupplyTargetHitLinear t attempts nextTrue nextFalse
            (tRejectedDataRaw data t)) =
        success (nextTrue (phaseBranchRaw (tAcceptedPhaseRaw t) data true)) +
          success (nextFalse (phaseBranchRaw (tAcceptedPhaseRaw t) data false)) +
          tSupplyTargetHitLinear t attempts (success.comp nextTrue) (success.comp nextFalse)
            (tRejectedDataRaw data t)
      rw [show success (tSupplyTargetHitLinear t attempts nextTrue nextFalse
            (tRejectedDataRaw data t)) =
          tSupplyTargetHitLinear t attempts (success.comp nextTrue) (success.comp nextFalse)
            (tRejectedDataRaw data t) by
        simpa only [LinearMap.comp_apply] using htail]

/-- The complete retry applies `success` only to target hits and retains both
phase-budget and fresh-pair exhaustion unchanged. -/
private noncomputable def tRetryStoppingTotalLinear
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    Nat → ZMod 12 → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | remaining, position =>
      if position = target then success else
        match remaining with
        | 0 => LinearMap.id
        | nextRemaining + 1 =>
            tSupplyAggregateLinear t pairAttempts
              (tRetryStoppingTotalLinear t pairAttempts target success
                nextRemaining (position + 1))
              (tRetryStoppingTotalLinear t pairAttempts target success
                nextRemaining (position - 1))

private theorem tRetryStoppingTotalLinear_components
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    ∀ (remaining : Nat) (position : ZMod 12),
      tRetryStoppingTotalLinear t pairAttempts target success remaining position =
        success.comp
            (tRetryTargetHitLinear t pairAttempts target remaining position) +
          tRetryPhaseExhaustedLinear t pairAttempts target remaining position +
          tRetryPairExhaustedLinear t pairAttempts target remaining position := by
  intro remaining
  induction remaining with
  | zero =>
      intro position
      apply LinearMap.ext
      intro data
      by_cases htarget : position = target <;>
        simp [tRetryStoppingTotalLinear, tRetryTargetHitLinear,
          tRetryPhaseExhaustedLinear, tRetryPairExhaustedLinear, htarget]
  | succ remaining ih =>
      intro position
      by_cases htarget : position = target
      · apply LinearMap.ext
        intro data
        simp [tRetryStoppingTotalLinear, tRetryTargetHitLinear,
          tRetryPhaseExhaustedLinear, tRetryPairExhaustedLinear, htarget]
      · simp only [tRetryStoppingTotalLinear, tRetryTargetHitLinear,
          tRetryPhaseExhaustedLinear, tRetryPairExhaustedLinear, if_neg htarget]
        rw [ih (position + 1), ih (position - 1)]
        rw [← tSupplyComponentLinear_sum t
          (success.comp
            (tRetryTargetHitLinear t pairAttempts target remaining (position + 1)))
          (success.comp
            (tRetryTargetHitLinear t pairAttempts target remaining (position - 1)))
          (tRetryPhaseExhaustedLinear t pairAttempts target remaining (position + 1))
          (tRetryPhaseExhaustedLinear t pairAttempts target remaining (position - 1))
          (tRetryPairExhaustedLinear t pairAttempts target remaining (position + 1))
          (tRetryPairExhaustedLinear t pairAttempts target remaining (position - 1))
          pairAttempts]
        rw [← tSupplyTargetHitLinear_comp]

private theorem tRetryStoppingTotalLinear_apply
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (remaining : Nat) (position : ZMod 12)
    (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
    (data : Operator QubitSpace) :
    tRetryStoppingTotalLinear t pairAttempts target success remaining position data =
      success (rawAggregateOfKind .targetHit
        (tRetry t pairAttempts target remaining position ledger history data)) +
      rawAggregateOfKind .phaseExhausted
        (tRetry t pairAttempts target remaining position ledger history data) +
      rawAggregateOfKind .tPairExhausted
        (tRetry t pairAttempts target remaining position ledger history data) := by
  rw [tRetryStoppingTotalLinear_components, LinearMap.add_apply, LinearMap.add_apply,
    LinearMap.comp_apply,
    tRetryTargetHitLinear_apply t pairAttempts target remaining position ledger history data,
    tRetryPhaseExhaustedLinear_apply t pairAttempts target remaining position ledger history data,
    tRetryPairExhaustedLinear_apply t pairAttempts target remaining position ledger history data]

private theorem tRetryStoppingTotalLinear_positive
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (hsuccess : ∀ data : Operator QubitSpace,
      LinearMap.IsPositive data → LinearMap.IsPositive (success data))
    (remaining : Nat) (position : ZMod 12) (data : Operator QubitSpace)
    (hdata : LinearMap.IsPositive data) :
    LinearMap.IsPositive
      (tRetryStoppingTotalLinear t pairAttempts target success remaining position data) := by
  rw [tRetryStoppingTotalLinear_components, LinearMap.add_apply, LinearMap.add_apply,
    LinearMap.comp_apply]
  exact ((hsuccess _
    (tRetryTargetHitLinear_positive t pairAttempts target remaining position data hdata)).add
      (tRetryPhaseExhaustedLinear_positive t pairAttempts target remaining position data hdata)).add
        (tRetryPairExhaustedLinear_positive t pairAttempts target remaining position data hdata)

private theorem tRetryStoppingTotalLinear_trace
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (hsuccess : ∀ data : Operator QubitSpace,
      LinearMap.trace Complex QubitSpace (success data) =
        LinearMap.trace Complex QubitSpace data)
    (remaining : Nat) (position : ZMod 12) (data : Operator QubitSpace) :
    LinearMap.trace Complex QubitSpace
        (tRetryStoppingTotalLinear t pairAttempts target success remaining position data) =
      LinearMap.trace Complex QubitSpace data := by
  rw [tRetryStoppingTotalLinear_components, LinearMap.add_apply, LinearMap.add_apply,
    LinearMap.comp_apply, map_add, map_add, hsuccess]
  exact tRetryComponentLinear_total_trace t pairAttempts target remaining position data

private theorem tRetryStoppingTotalLinear_id
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (remaining : Nat) (position : ZMod 12) :
    tRetryStoppingTotalLinear t pairAttempts target LinearMap.id remaining position =
      tRetryAggregateLinear t pairAttempts target remaining position := by
  rw [tRetryStoppingTotalLinear_components]
  simpa using tRetryComponentLinear_sum t pairAttempts target remaining position

private theorem tRetryStoppingTotalLinear_stable
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (hsuccessPositive : ∀ data : Operator QubitSpace,
      LinearMap.IsPositive data → LinearMap.IsPositive (success data))
    (hsuccessTrace : ∀ data : Operator QubitSpace,
      LinearMap.trace Complex QubitSpace (success data) =
        LinearMap.trace Complex QubitSpace data)
    (remaining : Nat) :
    ∀ (position : ZMod 12) (data : Operator QubitSpace),
      LinearMap.IsPositive data →
      traceNorm
        (tRetryStoppingTotalLinear t pairAttempts target success remaining position data -
          tRetryStoppingTotalLinear tMagicState pairAttempts target success
            remaining position data) ≤
        (2 * pairAttempts * remaining : Real) *
          (LinearMap.trace Complex QubitSpace data).re *
            traceNorm (t.toOperator - tMagicState.toOperator) := by
  induction remaining with
  | zero =>
      intro position data hdata
      have hzero : traceNorm (0 : Operator QubitSpace) = 0 :=
        (traceNorm_eq_zero_iff 0).mpr rfl
      simp [tRetryStoppingTotalLinear, hzero]
  | succ remaining ih =>
      intro position data hdata
      by_cases htarget : position = target
      · have hright : 0 ≤ (2 * pairAttempts * (remaining + 1) : Real) *
            (LinearMap.trace Complex QubitSpace data).re *
              traceNorm (t.toOperator - tMagicState.toOperator) := by
          have hdataTrace : 0 ≤ (LinearMap.trace Complex QubitSpace data).re :=
            (Complex.nonneg_iff.mp hdata.trace_nonneg).1
          exact mul_nonneg (mul_nonneg (by positivity) hdataTrace) (traceNorm_nonneg _)
        have hzero : traceNorm (0 : Operator QubitSpace) = 0 :=
          (traceNorm_eq_zero_iff 0).mpr rfl
        simpa [tRetryStoppingTotalLinear, htarget, hzero] using hright
      · let nextTrueActual :=
          tRetryStoppingTotalLinear t pairAttempts target success remaining (position + 1)
        let nextFalseActual :=
          tRetryStoppingTotalLinear t pairAttempts target success remaining (position - 1)
        let nextTrueIdeal :=
          tRetryStoppingTotalLinear tMagicState pairAttempts target success
            remaining (position + 1)
        let nextFalseIdeal :=
          tRetryStoppingTotalLinear tMagicState pairAttempts target success
            remaining (position - 1)
        have hnextTrueActualPositive : ∀ raw, LinearMap.IsPositive raw →
            LinearMap.IsPositive (nextTrueActual raw) := by
          intro raw hraw
          exact tRetryStoppingTotalLinear_positive t pairAttempts target success
            hsuccessPositive remaining (position + 1) raw hraw
        have hnextFalseActualPositive : ∀ raw, LinearMap.IsPositive raw →
            LinearMap.IsPositive (nextFalseActual raw) := by
          intro raw hraw
          exact tRetryStoppingTotalLinear_positive t pairAttempts target success
            hsuccessPositive remaining (position - 1) raw hraw
        have hnextTrueActualTrace : ∀ raw,
            LinearMap.trace Complex QubitSpace (nextTrueActual raw) =
              LinearMap.trace Complex QubitSpace raw := by
          intro raw
          exact tRetryStoppingTotalLinear_trace t pairAttempts target success
            hsuccessTrace remaining (position + 1) raw
        have hnextFalseActualTrace : ∀ raw,
            LinearMap.trace Complex QubitSpace (nextFalseActual raw) =
              LinearMap.trace Complex QubitSpace raw := by
          intro raw
          exact tRetryStoppingTotalLinear_trace t pairAttempts target success
            hsuccessTrace remaining (position - 1) raw
        have hsource :
            traceNorm
              (tSupplyAggregateLinear t pairAttempts nextTrueActual nextFalseActual data -
                tSupplyAggregateLinear tMagicState pairAttempts
                  nextTrueActual nextFalseActual data) ≤
              (2 * pairAttempts : Real) *
                (LinearMap.trace Complex QubitSpace data).re *
                  traceNorm (t.toOperator - tMagicState.toOperator) := by
          exact tSupplyAggregateLinear_source_stable t nextTrueActual nextFalseActual
            hnextTrueActualPositive hnextFalseActualPositive
            hnextTrueActualTrace hnextFalseActualTrace pairAttempts data hdata
        have hcontinuation :
            traceNorm
              (tSupplyAggregateLinear tMagicState pairAttempts
                  nextTrueActual nextFalseActual data -
                tSupplyAggregateLinear tMagicState pairAttempts
                  nextTrueIdeal nextFalseIdeal data) ≤
              (2 * pairAttempts * remaining : Real) *
                (LinearMap.trace Complex QubitSpace data).re *
                  traceNorm (t.toOperator - tMagicState.toOperator) := by
          exact tSupplyAggregateLinear_continuation_stable tMagicState
            nextTrueActual nextFalseActual nextTrueIdeal nextFalseIdeal
            (2 * pairAttempts * remaining : Real)
            (traceNorm (t.toOperator - tMagicState.toOperator))
            (by positivity) (traceNorm_nonneg _)
            (fun raw hraw => ih (position + 1) raw hraw)
            (fun raw hraw => ih (position - 1) raw hraw)
            pairAttempts data hdata
        have hactual :
            tRetryStoppingTotalLinear t pairAttempts target success
                (remaining + 1) position data =
              tSupplyAggregateLinear t pairAttempts nextTrueActual nextFalseActual data := by
          simp [tRetryStoppingTotalLinear, htarget, nextTrueActual, nextFalseActual]
        have hideal :
            tRetryStoppingTotalLinear tMagicState pairAttempts target success
                (remaining + 1) position data =
              tSupplyAggregateLinear tMagicState pairAttempts nextTrueIdeal nextFalseIdeal data := by
          simp [tRetryStoppingTotalLinear, htarget, nextTrueIdeal, nextFalseIdeal]
        rw [hactual, hideal]
        have htele :
            tSupplyAggregateLinear t pairAttempts nextTrueActual nextFalseActual data -
                tSupplyAggregateLinear tMagicState pairAttempts
                  nextTrueIdeal nextFalseIdeal data =
              (tSupplyAggregateLinear t pairAttempts nextTrueActual nextFalseActual data -
                tSupplyAggregateLinear tMagicState pairAttempts
                  nextTrueActual nextFalseActual data) +
              (tSupplyAggregateLinear tMagicState pairAttempts
                  nextTrueActual nextFalseActual data -
                tSupplyAggregateLinear tMagicState pairAttempts
                  nextTrueIdeal nextFalseIdeal data) := by
          module
        rw [htele]
        calc
          traceNorm
              ((tSupplyAggregateLinear t pairAttempts nextTrueActual nextFalseActual data -
                  tSupplyAggregateLinear tMagicState pairAttempts
                    nextTrueActual nextFalseActual data) +
                (tSupplyAggregateLinear tMagicState pairAttempts
                    nextTrueActual nextFalseActual data -
                  tSupplyAggregateLinear tMagicState pairAttempts
                    nextTrueIdeal nextFalseIdeal data)) ≤
              traceNorm
                (tSupplyAggregateLinear t pairAttempts nextTrueActual nextFalseActual data -
                  tSupplyAggregateLinear tMagicState pairAttempts
                    nextTrueActual nextFalseActual data) +
                traceNorm
                  (tSupplyAggregateLinear tMagicState pairAttempts
                    nextTrueActual nextFalseActual data -
                  tSupplyAggregateLinear tMagicState pairAttempts
                    nextTrueIdeal nextFalseIdeal data) := traceNorm_add_le _ _
          _ ≤ (2 * pairAttempts : Real) *
                (LinearMap.trace Complex QubitSpace data).re *
                  traceNorm (t.toOperator - tMagicState.toOperator) +
              (2 * pairAttempts * remaining : Real) *
                (LinearMap.trace Complex QubitSpace data).re *
                  traceNorm (t.toOperator - tMagicState.toOperator) :=
            add_le_add hsource hcontinuation
          _ = (2 * (pairAttempts : Real) * ((remaining + 1 : Nat) : Real)) *
                (LinearMap.trace Complex QubitSpace data).re *
                  traceNorm (t.toOperator - tMagicState.toOperator) := by
            norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
            ring

/-- Tail-first T-word execution with an arbitrary success continuation.  Both
phase-budget and fresh-pair exhaustion remain terminal outputs. -/
private noncomputable def tWordStoppingTotalLinear
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 6)) →
      (Operator QubitSpace →ₗ[Complex] Operator QubitSpace) →
        Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | [], success => success
  | letter :: tail, success =>
      match letter with
      | .positive .h =>
          tWordStoppingTotalLinear t pairAttempts blocks tail
            (success.comp (signedHRawLinear .normal))
      | .positive .k =>
          tWordStoppingTotalLinear t pairAttempts blocks tail
            (success.comp (signedKRawLinear .normal))
      | .positive .phase =>
          tWordStoppingTotalLinear t pairAttempts blocks tail
            (tRetryStoppingTotalLinear t pairAttempts (tPhaseTarget .normal) success
              (12 * blocks) 0)
      | .negative .h =>
          tWordStoppingTotalLinear t pairAttempts blocks tail
            (success.comp (signedHRawLinear .inverse))
      | .negative .k =>
          tWordStoppingTotalLinear t pairAttempts blocks tail
            (success.comp (signedKRawLinear .inverse))
      | .negative .phase =>
          tWordStoppingTotalLinear t pairAttempts blocks tail
            (tRetryStoppingTotalLinear t pairAttempts (tPhaseTarget .inverse) success
              (12 * blocks) 0)

private theorem tWordStoppingTotalLinear_components
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
      (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
      (raw : Operator QubitSpace),
      tWordStoppingTotalLinear t pairAttempts blocks letters success raw =
        success (tWordLiveLinear t pairAttempts blocks letters raw) +
          tWordPhaseStoppedLinear t pairAttempts blocks letters raw +
          tWordPairStoppedLinear t pairAttempts blocks letters raw := by
  intro letters
  induction letters with
  | nil =>
      intro success raw
      simp [tWordStoppingTotalLinear, tWordLiveLinear,
        tWordPhaseStoppedLinear, tWordPairStoppedLinear]
  | cons head tail ih =>
      intro success raw
      cases head with
      | positive atom =>
          cases atom with
          | h =>
              simpa [tWordStoppingTotalLinear, tWordLiveLinear,
                tWordPhaseStoppedLinear, tWordPairStoppedLinear,
                LinearMap.comp_apply] using
                ih (success.comp (signedHRawLinear .normal)) raw
          | k =>
              simpa [tWordStoppingTotalLinear, tWordLiveLinear,
                tWordPhaseStoppedLinear, tWordPairStoppedLinear,
                LinearMap.comp_apply] using
                ih (success.comp (signedKRawLinear .normal)) raw
          | phase =>
              rw [tWordStoppingTotalLinear, ih]
              rw [tRetryStoppingTotalLinear_components]
              simp only [tWordLiveLinear, tWordPhaseStoppedLinear,
                tWordPairStoppedLinear, LinearMap.add_apply, LinearMap.comp_apply]
              abel
      | negative atom =>
          cases atom with
          | h =>
              simpa [tWordStoppingTotalLinear, tWordLiveLinear,
                tWordPhaseStoppedLinear, tWordPairStoppedLinear,
                LinearMap.comp_apply] using
                ih (success.comp (signedHRawLinear .inverse)) raw
          | k =>
              simpa [tWordStoppingTotalLinear, tWordLiveLinear,
                tWordPhaseStoppedLinear, tWordPairStoppedLinear,
                LinearMap.comp_apply] using
                ih (success.comp (signedKRawLinear .inverse)) raw
          | phase =>
              rw [tWordStoppingTotalLinear, ih]
              rw [tRetryStoppingTotalLinear_components]
              simp only [tWordLiveLinear, tWordPhaseStoppedLinear,
                tWordPairStoppedLinear, LinearMap.add_apply, LinearMap.comp_apply]
              abel

private theorem tWordStoppingTotalLinear_success_difference
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
    (first second : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (raw : Operator QubitSpace) :
    tWordStoppingTotalLinear t pairAttempts blocks letters first raw -
        tWordStoppingTotalLinear t pairAttempts blocks letters second raw =
      first (tWordLiveLinear t pairAttempts blocks letters raw) -
        second (tWordLiveLinear t pairAttempts blocks letters raw) := by
  rw [tWordStoppingTotalLinear_components, tWordStoppingTotalLinear_components]
  abel

private theorem tWordStoppingTotalLinear_positive
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
      (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace),
      (∀ raw : Operator QubitSpace,
        LinearMap.IsPositive raw → LinearMap.IsPositive (success raw)) →
        ∀ raw : Operator QubitSpace, LinearMap.IsPositive raw →
          LinearMap.IsPositive
            (tWordStoppingTotalLinear t pairAttempts blocks letters success raw) := by
  intro letters
  induction letters with
  | nil =>
      intro success hsuccess raw hraw
      simpa [tWordStoppingTotalLinear] using hsuccess raw hraw
  | cons head tail ih =>
      intro success hsuccess raw hraw
      cases head <;> rename_i atom <;> cases atom <;>
        first
        | simpa [tWordStoppingTotalLinear, LinearMap.comp_apply] using
            ih (success.comp (signedHRawLinear .normal))
              (fun data hdata => hsuccess _
                (signedHRawLinear_positive .normal data hdata)) raw hraw
        | simpa [tWordStoppingTotalLinear, LinearMap.comp_apply] using
            ih (success.comp (signedKRawLinear .normal))
              (fun data hdata => hsuccess _
                (signedKRawLinear_positive .normal data hdata)) raw hraw
        | simpa [tWordStoppingTotalLinear] using
            ih (tRetryStoppingTotalLinear t pairAttempts (tPhaseTarget .normal) success
                (12 * blocks) 0)
              (fun data hdata => tRetryStoppingTotalLinear_positive t pairAttempts
                (tPhaseTarget .normal) success hsuccess (12 * blocks) 0 data hdata) raw hraw
        | simpa [tWordStoppingTotalLinear, LinearMap.comp_apply] using
            ih (success.comp (signedHRawLinear .inverse))
              (fun data hdata => hsuccess _
                (signedHRawLinear_positive .inverse data hdata)) raw hraw
        | simpa [tWordStoppingTotalLinear, LinearMap.comp_apply] using
            ih (success.comp (signedKRawLinear .inverse))
              (fun data hdata => hsuccess _
                (signedKRawLinear_positive .inverse data hdata)) raw hraw
        | simpa [tWordStoppingTotalLinear] using
            ih (tRetryStoppingTotalLinear t pairAttempts (tPhaseTarget .inverse) success
                (12 * blocks) 0)
              (fun data hdata => tRetryStoppingTotalLinear_positive t pairAttempts
                (tPhaseTarget .inverse) success hsuccess (12 * blocks) 0 data hdata) raw hraw

private theorem tWordStoppingTotalLinear_trace
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
      (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace),
      (∀ raw : Operator QubitSpace,
        LinearMap.trace Complex QubitSpace (success raw) =
          LinearMap.trace Complex QubitSpace raw) →
        ∀ raw : Operator QubitSpace,
          LinearMap.trace Complex QubitSpace
              (tWordStoppingTotalLinear t pairAttempts blocks letters success raw) =
            LinearMap.trace Complex QubitSpace raw := by
  intro letters
  induction letters with
  | nil =>
      intro success hsuccess raw
      simpa [tWordStoppingTotalLinear] using hsuccess raw
  | cons head tail ih =>
      intro success hsuccess raw
      cases head <;> rename_i atom <;> cases atom <;>
        first
        | simpa [tWordStoppingTotalLinear, LinearMap.comp_apply] using
            ih (success.comp (signedHRawLinear .normal))
              (fun data => (hsuccess _).trans (signedHRawLinear_trace .normal data)) raw
        | simpa [tWordStoppingTotalLinear, LinearMap.comp_apply] using
            ih (success.comp (signedKRawLinear .normal))
              (fun data => (hsuccess _).trans (signedKRawLinear_trace .normal data)) raw
        | simpa [tWordStoppingTotalLinear] using
            ih (tRetryStoppingTotalLinear t pairAttempts (tPhaseTarget .normal) success
                (12 * blocks) 0)
              (fun data => tRetryStoppingTotalLinear_trace t pairAttempts
                (tPhaseTarget .normal) success hsuccess (12 * blocks) 0 data) raw
        | simpa [tWordStoppingTotalLinear, LinearMap.comp_apply] using
            ih (success.comp (signedHRawLinear .inverse))
              (fun data => (hsuccess _).trans (signedHRawLinear_trace .inverse data)) raw
        | simpa [tWordStoppingTotalLinear, LinearMap.comp_apply] using
            ih (success.comp (signedKRawLinear .inverse))
              (fun data => (hsuccess _).trans (signedKRawLinear_trace .inverse data)) raw
        | simpa [tWordStoppingTotalLinear] using
            ih (tRetryStoppingTotalLinear t pairAttempts (tPhaseTarget .inverse) success
                (12 * blocks) 0)
              (fun data => tRetryStoppingTotalLinear_trace t pairAttempts
                (tPhaseTarget .inverse) success hsuccess (12 * blocks) 0 data) raw

private theorem tWordStoppingTotalLinear_stable
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
      (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace),
      (∀ raw : Operator QubitSpace,
        LinearMap.IsPositive raw → LinearMap.IsPositive (success raw)) →
      (∀ raw : Operator QubitSpace,
        LinearMap.trace Complex QubitSpace (success raw) =
          LinearMap.trace Complex QubitSpace raw) →
        ∀ (data : Operator QubitSpace), LinearMap.IsPositive data →
          traceNorm
            (tWordStoppingTotalLinear t pairAttempts blocks letters success data -
              tWordStoppingTotalLinear tMagicState pairAttempts blocks letters success data) ≤
            ((2 * pairAttempts * 12 * blocks *
                BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) letters : Nat) : Real) *
              (LinearMap.trace Complex QubitSpace data).re *
                traceNorm (t.toOperator - tMagicState.toOperator) := by
  intro letters
  induction letters with
  | nil =>
      intro success hsuccessPositive hsuccessTrace data hdata
      have hzero : traceNorm (0 : Operator QubitSpace) = 0 :=
        (traceNorm_eq_zero_iff 0).mpr rfl
      simp [tWordStoppingTotalLinear, BK05SignedPhaseLetter.resourceCount, hzero]
  | cons head tail ih =>
      intro success hsuccessPositive hsuccessTrace data hdata
      have hphase (sign : BK05WordPolarity) :
          traceNorm
            (tWordStoppingTotalLinear t pairAttempts blocks tail
                (tRetryStoppingTotalLinear t pairAttempts (tPhaseTarget sign) success
                  (12 * blocks) 0) data -
              tWordStoppingTotalLinear tMagicState pairAttempts blocks tail
                (tRetryStoppingTotalLinear tMagicState pairAttempts (tPhaseTarget sign) success
                  (12 * blocks) 0) data) ≤
            ((2 * pairAttempts * 12 * blocks *
                (1 + BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) tail) : Nat) : Real) *
              (LinearMap.trace Complex QubitSpace data).re *
                traceNorm (t.toOperator - tMagicState.toOperator) := by
        let actualSuccess := tRetryStoppingTotalLinear t pairAttempts
          (tPhaseTarget sign) success (12 * blocks) 0
        let idealSuccess := tRetryStoppingTotalLinear tMagicState pairAttempts
          (tPhaseTarget sign) success (12 * blocks) 0
        have htailLivePositive : LinearMap.IsPositive
            (tWordLiveLinear t pairAttempts blocks tail data) :=
          tWordLiveLinear_positive t pairAttempts blocks tail data hdata
        have hidealSuccessPositive : ∀ raw : Operator QubitSpace,
            LinearMap.IsPositive raw → LinearMap.IsPositive (idealSuccess raw) := by
          intro raw hraw
          exact tRetryStoppingTotalLinear_positive tMagicState pairAttempts
            (tPhaseTarget sign) success hsuccessPositive (12 * blocks) 0 raw hraw
        have hidealSuccessTrace : ∀ raw : Operator QubitSpace,
            LinearMap.trace Complex QubitSpace (idealSuccess raw) =
              LinearMap.trace Complex QubitSpace raw := by
          intro raw
          exact tRetryStoppingTotalLinear_trace tMagicState pairAttempts
            (tPhaseTarget sign) success hsuccessTrace (12 * blocks) 0 raw
        have hcurrent :
            traceNorm
              (actualSuccess (tWordLiveLinear t pairAttempts blocks tail data) -
                idealSuccess (tWordLiveLinear t pairAttempts blocks tail data)) ≤
              (2 * (pairAttempts : Real) * (12 * (blocks : Real))) *
                (LinearMap.trace Complex QubitSpace
                  (tWordLiveLinear t pairAttempts blocks tail data)).re *
                  traceNorm (t.toOperator - tMagicState.toOperator) := by
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using
            tRetryStoppingTotalLinear_stable t pairAttempts (tPhaseTarget sign) success
              hsuccessPositive hsuccessTrace (12 * blocks) 0
              (tWordLiveLinear t pairAttempts blocks tail data) htailLivePositive
        have hcurrentInput :
            traceNorm
              (actualSuccess (tWordLiveLinear t pairAttempts blocks tail data) -
                idealSuccess (tWordLiveLinear t pairAttempts blocks tail data)) ≤
              (2 * (pairAttempts : Real) * (12 * (blocks : Real))) *
                (LinearMap.trace Complex QubitSpace data).re *
                  traceNorm (t.toOperator - tMagicState.toOperator) := by
          calc
            traceNorm
                (actualSuccess (tWordLiveLinear t pairAttempts blocks tail data) -
                  idealSuccess (tWordLiveLinear t pairAttempts blocks tail data)) ≤
                (2 * (pairAttempts : Real) * (12 * (blocks : Real))) *
                  (LinearMap.trace Complex QubitSpace
                    (tWordLiveLinear t pairAttempts blocks tail data)).re *
                    traceNorm (t.toOperator - tMagicState.toOperator) := hcurrent
            _ ≤ (2 * (pairAttempts : Real) * (12 * (blocks : Real))) *
                  (LinearMap.trace Complex QubitSpace data).re *
                    traceNorm (t.toOperator - tMagicState.toOperator) := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left
                    (tWord_live_trace_le t pairAttempts blocks tail data hdata)
                    (by positivity))
                  (traceNorm_nonneg _)
        have htail := ih idealSuccess hidealSuccessPositive hidealSuccessTrace data hdata
        have htele :
            tWordStoppingTotalLinear t pairAttempts blocks tail actualSuccess data -
                tWordStoppingTotalLinear tMagicState pairAttempts blocks tail idealSuccess data =
              (actualSuccess (tWordLiveLinear t pairAttempts blocks tail data) -
                idealSuccess (tWordLiveLinear t pairAttempts blocks tail data)) +
              (tWordStoppingTotalLinear t pairAttempts blocks tail idealSuccess data -
                tWordStoppingTotalLinear tMagicState pairAttempts blocks tail idealSuccess data) := by
          calc
            tWordStoppingTotalLinear t pairAttempts blocks tail actualSuccess data -
                tWordStoppingTotalLinear tMagicState pairAttempts blocks tail idealSuccess data =
              (tWordStoppingTotalLinear t pairAttempts blocks tail actualSuccess data -
                tWordStoppingTotalLinear t pairAttempts blocks tail idealSuccess data) +
              (tWordStoppingTotalLinear t pairAttempts blocks tail idealSuccess data -
                tWordStoppingTotalLinear tMagicState pairAttempts blocks tail idealSuccess data) := by
                  abel
            _ = (actualSuccess (tWordLiveLinear t pairAttempts blocks tail data) -
                idealSuccess (tWordLiveLinear t pairAttempts blocks tail data)) +
              (tWordStoppingTotalLinear t pairAttempts blocks tail idealSuccess data -
                tWordStoppingTotalLinear tMagicState pairAttempts blocks tail idealSuccess data) := by
                  rw [tWordStoppingTotalLinear_success_difference]
        have hsum :
            (2 * (pairAttempts : Real) * (12 * (blocks : Real))) *
                (LinearMap.trace Complex QubitSpace data).re *
                  traceNorm (t.toOperator - tMagicState.toOperator) +
              ((2 * pairAttempts * 12 * blocks *
                BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) tail : Nat) : Real) *
                (LinearMap.trace Complex QubitSpace data).re *
                  traceNorm (t.toOperator - tMagicState.toOperator) =
              ((2 * pairAttempts * 12 * blocks *
                (1 + BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) tail) : Nat) : Real) *
                (LinearMap.trace Complex QubitSpace data).re *
                  traceNorm (t.toOperator - tMagicState.toOperator) := by
          push_cast
          ring
        change traceNorm
            (tWordStoppingTotalLinear t pairAttempts blocks tail actualSuccess data -
              tWordStoppingTotalLinear tMagicState pairAttempts blocks tail idealSuccess data) ≤ _
        rw [htele]
        calc
          traceNorm
              ((actualSuccess (tWordLiveLinear t pairAttempts blocks tail data) -
                idealSuccess (tWordLiveLinear t pairAttempts blocks tail data)) +
                (tWordStoppingTotalLinear t pairAttempts blocks tail idealSuccess data -
                  tWordStoppingTotalLinear tMagicState pairAttempts blocks tail idealSuccess data)) ≤
              traceNorm
                  (actualSuccess (tWordLiveLinear t pairAttempts blocks tail data) -
                    idealSuccess (tWordLiveLinear t pairAttempts blocks tail data)) +
                traceNorm
                  (tWordStoppingTotalLinear t pairAttempts blocks tail idealSuccess data -
                    tWordStoppingTotalLinear tMagicState pairAttempts blocks tail idealSuccess data) :=
            traceNorm_add_le _ _
          _ ≤ (2 * (pairAttempts : Real) * (12 * (blocks : Real))) *
                (LinearMap.trace Complex QubitSpace data).re *
                  traceNorm (t.toOperator - tMagicState.toOperator) +
              ((2 * pairAttempts * 12 * blocks *
                BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) tail : Nat) : Real) *
                (LinearMap.trace Complex QubitSpace data).re *
                  traceNorm (t.toOperator - tMagicState.toOperator) :=
            add_le_add hcurrentInput htail
          _ = _ := hsum
      cases head with
      | positive atom =>
          cases atom with
          | h =>
              simpa [tWordStoppingTotalLinear, BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using
                ih (success.comp (signedHRawLinear .normal))
                  (fun raw hraw => hsuccessPositive _
                    (signedHRawLinear_positive .normal raw hraw))
                  (fun raw => (hsuccessTrace _).trans
                    (signedHRawLinear_trace .normal raw)) data hdata
          | k =>
              simpa [tWordStoppingTotalLinear, BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using
                ih (success.comp (signedKRawLinear .normal))
                  (fun raw hraw => hsuccessPositive _
                    (signedKRawLinear_positive .normal raw hraw))
                  (fun raw => (hsuccessTrace _).trans
                    (signedKRawLinear_trace .normal raw)) data hdata
          | phase =>
              simpa [tWordStoppingTotalLinear, BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost, Nat.add_comm] using hphase .normal
      | negative atom =>
          cases atom with
          | h =>
              simpa [tWordStoppingTotalLinear, BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using
                ih (success.comp (signedHRawLinear .inverse))
                  (fun raw hraw => hsuccessPositive _
                    (signedHRawLinear_positive .inverse raw hraw))
                  (fun raw => (hsuccessTrace _).trans
                    (signedHRawLinear_trace .inverse raw)) data hdata
          | k =>
              simpa [tWordStoppingTotalLinear, BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using
                ih (success.comp (signedKRawLinear .inverse))
                  (fun raw hraw => hsuccessPositive _
                    (signedKRawLinear_positive .inverse raw hraw))
                  (fun raw => (hsuccessTrace _).trans
                    (signedKRawLinear_trace .inverse raw)) data hdata
          | phase =>
              simpa [tWordStoppingTotalLinear, BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost, Nat.add_comm] using hphase .inverse

private theorem tWordStoppingTotalLinear_stable_id
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
    (data : Operator QubitSpace) (hdata : LinearMap.IsPositive data) :
    traceNorm
      (tWordStoppingTotalLinear t pairAttempts blocks letters LinearMap.id data -
        tWordStoppingTotalLinear tMagicState pairAttempts blocks letters LinearMap.id data) ≤
      ((2 * pairAttempts * 12 * blocks *
          BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) letters : Nat) : Real) *
        (LinearMap.trace Complex QubitSpace data).re *
          traceNorm (t.toOperator - tMagicState.toOperator) := by
  exact tWordStoppingTotalLinear_stable t pairAttempts blocks letters LinearMap.id
    (fun _ hpositive => hpositive) (fun raw => rfl) data hdata

private theorem tWordStoppingTotalLinear_id
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) :
    tWordStoppingTotalLinear t pairAttempts blocks letters LinearMap.id =
      tWordTotalLinear t pairAttempts blocks letters := by
  apply LinearMap.ext
  intro raw
  rw [tWordStoppingTotalLinear_components]
  rfl

/-- The complete retained-stopping T-word aggregate obeys the exact BK05
source count: two fresh magic states per pair attempt and twelve phase steps
per block for each phase letter. -/
private theorem tSignedWordTotalLinear_stable_id
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
    (data : Operator QubitSpace) (hdata : LinearMap.IsPositive data) :
    traceNorm
      (tWordTotalLinear t pairAttempts blocks letters data -
        tWordTotalLinear tMagicState pairAttempts blocks letters data) ≤
      ((2 * pairAttempts * 12 * blocks *
          BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) letters : Nat) : Real) *
        (LinearMap.trace Complex QubitSpace data).re *
          traceNorm (t.toOperator - tMagicState.toOperator) := by
  rw [← tWordStoppingTotalLinear_id t pairAttempts blocks letters,
    ← tWordStoppingTotalLinear_id tMagicState pairAttempts blocks letters]
  exact tWordStoppingTotalLinear_stable_id t pairAttempts blocks letters data hdata

/- End T one-qubit acceptance interface. -/

/- Task 5f: entanglement-safe selected-wire and finite-register compiler. -/

/-- Exact coordinates separating one selected register wire from every other
wire.  This is a unitary factorization, so no marginal or product-state
assumption is introduced. -/
private noncomputable def selectedWireFactorization
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] (wire : Wire) :
    UnitaryTransport (QubitRegister Wire)
      (CompositeSystem QubitSpace (QubitRegister (OtherWires wire))) := by
  let sourceBasis := EuclideanSpace.basisFun (Bitstring Wire) Complex
  let selectedBasis := EuclideanSpace.basisFun (Fin 2) Complex
  let restBasis := EuclideanSpace.basisFun
    (Bitstring (OtherWires wire)) Complex
  let targetBasis := selectedBasis.tensorProduct restBasis
  let U := sourceBasis.equiv targetBasis (singleQubitIndexEquiv wire)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

private theorem selectedWireFactorization_apply_basis
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] (wire : Wire)
    (bits : Bitstring Wire) :
    selectedWireFactorization wire
        (EuclideanSpace.basisFun (Bitstring Wire) Complex bits) =
      (EuclideanSpace.basisFun (Fin 2) Complex
          (splitAtWire wire bits).1) ⊗ₜ[Complex]
        (EuclideanSpace.basisFun (Bitstring (OtherWires wire)) Complex
          (splitAtWire wire bits).2) := by
  dsimp [selectedWireFactorization]
  rw [OrthonormalBasis.equiv_apply_basis]
  rw [OrthonormalBasis.tensorProduct_apply']
  simp [singleQubitIndexEquiv]

/-- Sequential composition of two finite physical Kraus recipes. -/
private noncomputable def krausSeq
    {ι κ H K L : Type} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
    (E : FiniteKrausFamily ι H K) (D : FiniteKrausFamily κ K L) :
    FiniteKrausFamily (ι × κ) H L where
  operator index := (D.operator index.2).comp (E.operator index.1)

private theorem krausSeq_inducedMap_apply
    {ι κ H K L : Type} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
    (E : FiniteKrausFamily ι H K) (D : FiniteKrausFamily κ K L)
    (A : Operator H) :
    (krausSeq E D).inducedMap A = D.inducedMap (E.inducedMap A) := by
  classical
  apply LinearMap.ext
  intro x
  simp only [FiniteKrausFamily.inducedMap_apply, krausSeq,
    LinearMap.adjoint_comp, LinearMap.comp_apply, LinearMap.sum_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_sum]

private theorem krausSeq_complete
    {ι κ H K L : Type} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
    {E : FiniteKrausFamily ι H K} {D : FiniteKrausFamily κ K L}
    (hE : E.Complete) (hD : D.Complete) : (krausSeq E D).Complete := by
  apply FiniteKrausFamily.complete_of_inducedMap_trace_preserving
  intro A
  rw [krausSeq_inducedMap_apply,
    D.inducedMap_trace_preserving hD,
    E.inducedMap_trace_preserving hE]

private theorem tensorMap_sum_left_kraus
    {κ : Type v} {H R : Type u} [Fintype κ]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
    (A : κ → Operator H) (B : Operator R) :
    TensorProduct.map (∑ i, A i) B = ∑ i, TensorProduct.map (A i) B := by
  classical
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [Finset.sum_insert hi, TensorProduct.map_add_left, ih]

/-- Act with each local Kraus operator on the selected tensor factor and with
the identity on an arbitrary, potentially entangled reference factor. -/
private noncomputable def tensorIdKraus
    {κ H : Type} [Fintype κ]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (E : FiniteKrausFamily κ H H)
    (R : Type) [NormedAddCommGroup R] [InnerProductSpace Complex R]
    [FiniteQuantumSystem R] :
    FiniteKrausFamily κ (CompositeSystem H R) (CompositeSystem H R) where
  operator i := TensorProduct.map (E.operator i) (1 : Operator R)

private theorem tensorIdKraus_complete
    {κ H R : Type} [Fintype κ]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
    {E : FiniteKrausFamily κ H H} (hE : E.Complete) :
    (tensorIdKraus E R).Complete := by
  classical
  rw [FiniteKrausFamily.Complete]
  calc
    (∑ i, (LinearMap.adjoint ((tensorIdKraus E R).operator i)).comp
        ((tensorIdKraus E R).operator i)) =
        ∑ i, TensorProduct.map
          ((LinearMap.adjoint (E.operator i)).comp (E.operator i))
          (1 : Operator R) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [tensorIdKraus]
      rw [TensorProduct.adjoint_map, LinearMap.adjoint_one,
        ← TensorProduct.map_comp]
      congr 1
    _ = TensorProduct.map
        (∑ i, (LinearMap.adjoint (E.operator i)).comp (E.operator i))
        (1 : Operator R) := by
      rw [tensorMap_sum_left_kraus]
    _ = TensorProduct.map (1 : Operator H) (1 : Operator R) := by rw [hE]
    _ = 1 := TensorProduct.map_one

private noncomputable def selectedWireKraus
    {κ : Type} [Fintype κ] {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) (E : FiniteKrausFamily κ QubitSpace QubitSpace) :
    FiniteKrausFamily κ (QubitRegister Wire) (QubitRegister Wire) :=
  (tensorIdKraus E (QubitRegister (OtherWires wire))).unitaryTransport
    (selectedWireFactorization wire).symm
    (selectedWireFactorization wire).symm

private theorem selectedWireKraus_complete
    {κ : Type} [Fintype κ] {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) {E : FiniteKrausFamily κ QubitSpace QubitSpace}
    (hE : E.Complete) : (selectedWireKraus wire E).Complete := by
  exact (tensorIdKraus E (QubitRegister (OtherWires wire))).unitaryTransport_complete
    (selectedWireFactorization wire).symm
    (selectedWireFactorization wire).symm
    (tensorIdKraus_complete hE)

private theorem selectedWireKraus_inducedMap_apply
    {κ : Type} [Fintype κ] {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) (E : FiniteKrausFamily κ QubitSpace QubitSpace)
    (A : Operator (QubitRegister Wire)) :
    (selectedWireKraus wire E).inducedMap A =
      (selectedWireFactorization wire).symm.conjOperator
        ((tensorIdKraus E (QubitRegister (OtherWires wire))).inducedMap
          ((selectedWireFactorization wire).conjOperator A)) := by
  exact FiniteKrausFamily.unitaryTransport_inducedMap_apply
      (tensorIdKraus E (QubitRegister (OtherWires wire)))
      (selectedWireFactorization wire).symm
      (selectedWireFactorization wire).symm A

private theorem selectedWireFactorization_symm_apply_basis
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] (wire : Wire)
    (selected : Fin 2) (rest : Bitstring (OtherWires wire)) :
    (selectedWireFactorization wire).toLinearEquiv.symm
        ((EuclideanSpace.basisFun (Fin 2) Complex selected) ⊗ₜ[Complex]
          (EuclideanSpace.basisFun (Bitstring (OtherWires wire)) Complex rest)) =
      EuclideanSpace.basisFun (Bitstring Wire) Complex
        ((singleQubitIndexEquiv wire).symm (selected, rest)) := by
  apply (selectedWireFactorization wire).toLinearEquiv.injective
  rw [selectedWireFactorization_apply_basis]
  have hsplit : splitAtWire wire (mergeAtWire wire (selected, rest)) =
      (selected, rest) :=
    (singleQubitIndexEquiv wire).apply_symm_apply (selected, rest)
  simpa [singleQubitIndexEquiv, hsplit]

@[simp]
private theorem splitAtWire_mergeAtWire_private
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] (wire : Wire)
    (bits : Fin 2 × Bitstring (OtherWires wire)) :
    splitAtWire wire (mergeAtWire wire bits) = bits :=
  (singleQubitIndexEquiv wire).apply_symm_apply bits

set_option maxRecDepth 4000 in
/-- The exact operator obtained by acting on the selected tensor factor is
the existing concrete selected-wire matrix lift. -/
private theorem selectedWire_gateOperator_eq_singleQubitLift
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) (gate : UnitaryGate (Fin 2)) :
    (selectedWireFactorization wire).symm.conjOperator
        (TensorProduct.map
          (Matrix.toEuclideanLin
            (gate : Matrix (Fin 2) (Fin 2) Complex))
          (1 : Operator (QubitRegister (OtherWires wire)))) =
      Matrix.toEuclideanLin
        (singleQubitLift wire gate :
          Matrix (Bitstring Wire) (Bitstring Wire) Complex) := by
  apply (EuclideanSpace.basisFun (Bitstring Wire) Complex).toBasis.ext
  intro bits
  change (selectedWireFactorization wire).toLinearEquiv.symm
      ((TensorProduct.map
          (Matrix.toEuclideanLin
            (gate : Matrix (Fin 2) (Fin 2) Complex))
          (1 : Operator (QubitRegister (OtherWires wire))))
        ((selectedWireFactorization wire)
          (EuclideanSpace.basisFun (Bitstring Wire) Complex bits))) = _
  rw [selectedWireFactorization_apply_basis, TensorProduct.map_tmul]
  simp only [Module.End.one_apply, Matrix.toEuclideanLin_eq_toLin,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_toBasis]
  rw [← congrFun (OrthonormalBasis.coe_toBasis
    (EuclideanSpace.basisFun (Fin 2) Complex)) (splitAtWire wire bits).1]
  rw [EuclideanSpace.basisFun_toBasis]
  rw [Matrix.toLin_self]
  rw [TensorProduct.sum_tmul]
  simp_rw [← TensorProduct.smul_tmul']
  have hselectedBasis (selected : Fin 2) :
      (PiLp.basisFun 2 Complex (Fin 2)) selected =
        EuclideanSpace.basisFun (Fin 2) Complex selected :=
    congrFun (OrthonormalBasis.coe_toBasis
      (EuclideanSpace.basisFun (Fin 2) Complex)) selected
  simp_rw [hselectedBasis]
  simp only [map_sum, map_smul,
    selectedWireFactorization_symm_apply_basis]
  change (∑ selected : Fin 2,
      (gate : Matrix (Fin 2) (Fin 2) Complex) selected
          (splitAtWire wire bits).1 •
        EuclideanSpace.basisFun (Bitstring Wire) Complex
          ((singleQubitIndexEquiv wire).symm
            (selected, (splitAtWire wire bits).2))) = _
  simp only [singleQubitLift, singleQubitLiftMatrix,
    Matrix.toEuclideanLin_eq_toLin, Matrix.toLin_self]
  let globalTerm := fun output : Bitstring Wire =>
    (singleQubitLiftMatrix wire
        (gate : Matrix (Fin 2) (Fin 2) Complex)) output bits •
      (PiLp.basisFun 2 Complex (Bitstring Wire)) output
  change (∑ selected : Fin 2,
      (gate : Matrix (Fin 2) (Fin 2) Complex) selected
          (splitAtWire wire bits).1 •
        EuclideanSpace.basisFun (Bitstring Wire) Complex
          ((singleQubitIndexEquiv wire).symm
            (selected, (splitAtWire wire bits).2))) =
    ∑ output : Bitstring Wire, globalTerm output
  have hsum : (∑ output : Bitstring Wire, globalTerm output) =
      ∑ pair : Fin 2 × Bitstring (OtherWires wire),
        globalTerm ((singleQubitIndexEquiv wire).symm pair) := by
    apply Fintype.sum_equiv (singleQubitIndexEquiv wire)
    intro output
    simp
  rw [hsum, Fintype.sum_prod_type]
  simp [globalTerm, singleQubitLiftMatrix, Matrix.reindex_apply,
    Matrix.kronecker_apply, Matrix.one_apply, singleQubitIndexEquiv,
    splitAtWire_mergeAtWire_private]

/-- A literal one-outcome Kraus recipe for a unitary one-qubit gate. -/
private noncomputable def unitaryGateKraus (gate : UnitaryGate (Fin 2)) :
    FiniteKrausFamily Unit QubitSpace QubitSpace where
  operator _ := Matrix.toEuclideanLin
    (gate : Matrix (Fin 2) (Fin 2) Complex)

private theorem unitaryGateKraus_complete (gate : UnitaryGate (Fin 2)) :
    (unitaryGateKraus gate).Complete := by
  rw [FiniteKrausFamily.Complete]
  simp only [Fintype.sum_unique, unitaryGateKraus]
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [← Matrix.toLpLin_mul_same]
  rw [← Matrix.star_eq_conjTranspose, gate.property.1]
  simpa only [Module.End.one_eq_id] using
    (Matrix.toLpLin_one (R := Complex) (n := Fin 2) 2)

private theorem unitaryGateKraus_inducedMap_eq_transport
    (gate : UnitaryGate (Fin 2))
    (U : UnitaryTransport QubitSpace QubitSpace)
    (hU : U.toLinearEquiv.toLinearMap =
      Matrix.toEuclideanLin
        (gate : Matrix (Fin 2) (Fin 2) Complex)) :
    (unitaryGateKraus gate).inducedMap = U.conjOperatorLinearMap := by
  apply LinearMap.ext
  intro A
  rw [FiniteKrausFamily.inducedMap_apply, Fintype.sum_unique]
  change
    (Matrix.toEuclideanLin
        (gate : Matrix (Fin 2) (Fin 2) Complex)).comp
      (A.comp (LinearMap.adjoint
        (Matrix.toEuclideanLin
          (gate : Matrix (Fin 2) (Fin 2) Complex)))) =
      U.toLinearEquiv.toLinearMap.comp
        (A.comp U.toLinearEquiv.symm.toLinearMap)
  rw [← U.adjoint_toLinearMap, hU]

private theorem unitaryTransport_trans_conjOperator
    {H K L : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
    (U : UnitaryTransport H K) (V : UnitaryTransport K L)
    (A : Operator H) :
    (U.trans V).conjOperator A = V.conjOperator (U.conjOperator A) := by
  ext x
  rfl

private noncomputable def hFixedIdealLetterTransport :
    BK05SignedPhaseLetter (-Real.pi / 4) →
      UnitaryTransport QubitSpace QubitSpace
  | .positive .h => signedHTransport .normal
  | .positive .k => signedKTransport .normal
  | .positive .phase =>
      OneQubitMagic.phaseShiftTransport
        (phaseCycleAngle 8 * (hPhaseTarget .normal).val)
  | .negative .h => signedHTransport .inverse
  | .negative .k => signedKTransport .inverse
  | .negative .phase =>
      OneQubitMagic.phaseShiftTransport
        (phaseCycleAngle 8 * (hPhaseTarget .inverse).val)

private theorem hFixedIdealLetterTransport_conjOperatorLinearMap
    (letter : BK05SignedPhaseLetter (-Real.pi / 4)) :
    (hFixedIdealLetterTransport letter).conjOperatorLinearMap =
      hFixedIdealLetterLinear letter := by
  cases letter with
  | positive atom => cases atom <;> rfl
  | negative atom => cases atom <;> rfl

private theorem hFixedIdealLetterTransport_eval
    (letter : BK05SignedPhaseLetter (-Real.pi / 4)) :
    (hFixedIdealLetterTransport letter).toLinearEquiv.toLinearMap =
      Matrix.toEuclideanLin
        ((letter.eval (-Real.pi / 4) : UnitaryGate (Fin 2)) :
          Matrix (Fin 2) (Fin 2) Complex) := by
  calc
    (hFixedIdealLetterTransport letter).toLinearEquiv.toLinearMap =
        hFixedIdealLetterStateLinear letter := by
      cases letter with
      | positive atom => cases atom <;> rfl
      | negative atom => cases atom <;> rfl
    _ = _ := hFixedIdealLetterStateLinear_eval letter

private noncomputable def tFixedIdealLetterTransport :
    BK05SignedPhaseLetter (-Real.pi / 6) →
      UnitaryTransport QubitSpace QubitSpace
  | .positive .h => signedHTransport .normal
  | .positive .k => signedKTransport .normal
  | .positive .phase =>
      OneQubitMagic.phaseShiftTransport
        (phaseCycleAngle 12 * (tPhaseTarget .normal).val)
  | .negative .h => signedHTransport .inverse
  | .negative .k => signedKTransport .inverse
  | .negative .phase =>
      OneQubitMagic.phaseShiftTransport
        (phaseCycleAngle 12 * (tPhaseTarget .inverse).val)

private theorem tFixedIdealLetterTransport_conjOperatorLinearMap
    (letter : BK05SignedPhaseLetter (-Real.pi / 6)) :
    (tFixedIdealLetterTransport letter).conjOperatorLinearMap =
      tFixedIdealLetterLinear letter := by
  cases letter with
  | positive atom => cases atom <;> rfl
  | negative atom => cases atom <;> rfl

private theorem tFixedIdealLetterTransport_eval
    (letter : BK05SignedPhaseLetter (-Real.pi / 6)) :
    (tFixedIdealLetterTransport letter).toLinearEquiv.toLinearMap =
      Matrix.toEuclideanLin
        ((letter.eval (-Real.pi / 6) : UnitaryGate (Fin 2)) :
          Matrix (Fin 2) (Fin 2) Complex) := by
  calc
    (tFixedIdealLetterTransport letter).toLinearEquiv.toLinearMap =
        tFixedIdealLetterStateLinear letter := by
      cases letter with
      | positive atom => cases atom <;> rfl
      | negative atom => cases atom <;> rfl
    _ = _ := tFixedIdealLetterStateLinear_eval letter

private noncomputable def hFixedIdealWordTransport :
    List (BK05SignedPhaseLetter (-Real.pi / 4)) →
      UnitaryTransport QubitSpace QubitSpace
  | [] => UnitaryTransport.identity QubitSpace
  | letter :: tail =>
      (hFixedIdealWordTransport tail).trans (hFixedIdealLetterTransport letter)

private theorem hFixedIdealWordTransport_conjOperatorLinearMap :
    ∀ letters : List (BK05SignedPhaseLetter (-Real.pi / 4)),
      (hFixedIdealWordTransport letters).conjOperatorLinearMap =
        hFixedIdealWordLinear letters := by
  intro letters
  induction letters with
  | nil =>
      apply LinearMap.ext
      intro A
      rfl
  | cons letter tail ih =>
      apply LinearMap.ext
      intro A
      change
        ((hFixedIdealWordTransport tail).trans
          (hFixedIdealLetterTransport letter)).conjOperator A =
        hFixedIdealLetterLinear letter (hFixedIdealWordLinear tail A)
      rw [unitaryTransport_trans_conjOperator]
      have ihA := LinearMap.congr_fun ih A
      change (hFixedIdealWordTransport tail).conjOperator A =
        hFixedIdealWordLinear tail A at ihA
      rw [ihA]
      exact LinearMap.congr_fun
        (hFixedIdealLetterTransport_conjOperatorLinearMap letter) _

private theorem hFixedIdealWordTransport_eval :
    ∀ letters : List (BK05SignedPhaseLetter (-Real.pi / 4)),
      (hFixedIdealWordTransport letters).toLinearEquiv.toLinearMap =
        Matrix.toEuclideanLin
          ((BK05SignedPhaseLetter.evalList (-Real.pi / 4) letters :
              UnitaryGate (Fin 2)) : Matrix (Fin 2) (Fin 2) Complex) := by
  intro letters
  induction letters with
  | nil =>
      apply LinearMap.ext
      intro x
      simp [hFixedIdealWordTransport, BK05SignedPhaseLetter.evalList,
        UnitaryTransport.identity]
  | cons letter tail ih =>
      apply LinearMap.ext
      intro x
      change hFixedIdealLetterTransport letter
          (hFixedIdealWordTransport tail x) =
        Matrix.toEuclideanLin
          (((letter.eval (-Real.pi / 4) : UnitaryGate (Fin 2)) :
              Matrix (Fin 2) (Fin 2) Complex) *
            ((BK05SignedPhaseLetter.evalList (-Real.pi / 4) tail :
              UnitaryGate (Fin 2)) : Matrix (Fin 2) (Fin 2) Complex)) x
      have hletter := LinearMap.congr_fun
        (hFixedIdealLetterTransport_eval letter)
          (hFixedIdealWordTransport tail x)
      change hFixedIdealLetterTransport letter
          (hFixedIdealWordTransport tail x) =
        Matrix.toEuclideanLin
          ((letter.eval (-Real.pi / 4) : UnitaryGate (Fin 2)) :
            Matrix (Fin 2) (Fin 2) Complex)
          (hFixedIdealWordTransport tail x) at hletter
      rw [hletter]
      have ihx := LinearMap.congr_fun ih x
      change hFixedIdealWordTransport tail x =
        Matrix.toEuclideanLin
          ((BK05SignedPhaseLetter.evalList (-Real.pi / 4) tail :
            UnitaryGate (Fin 2)) : Matrix (Fin 2) (Fin 2) Complex) x at ihx
      rw [ihx]
      change
        (Matrix.toLpLin 2 2
          ((letter.eval (-Real.pi / 4) : Matrix (Fin 2) (Fin 2) Complex))
          ((Matrix.toLpLin 2 2
            (BK05SignedPhaseLetter.evalList (-Real.pi / 4) tail :
              Matrix (Fin 2) (Fin 2) Complex)) x)) = _
      rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]

private noncomputable def tFixedIdealWordTransport :
    List (BK05SignedPhaseLetter (-Real.pi / 6)) →
      UnitaryTransport QubitSpace QubitSpace
  | [] => UnitaryTransport.identity QubitSpace
  | letter :: tail =>
      (tFixedIdealWordTransport tail).trans (tFixedIdealLetterTransport letter)

private theorem tFixedIdealWordTransport_conjOperatorLinearMap :
    ∀ letters : List (BK05SignedPhaseLetter (-Real.pi / 6)),
      (tFixedIdealWordTransport letters).conjOperatorLinearMap =
        tFixedIdealWordLinear letters := by
  intro letters
  induction letters with
  | nil =>
      apply LinearMap.ext
      intro A
      rfl
  | cons letter tail ih =>
      apply LinearMap.ext
      intro A
      change
        ((tFixedIdealWordTransport tail).trans
          (tFixedIdealLetterTransport letter)).conjOperator A =
        tFixedIdealLetterLinear letter (tFixedIdealWordLinear tail A)
      rw [unitaryTransport_trans_conjOperator]
      have ihA := LinearMap.congr_fun ih A
      change (tFixedIdealWordTransport tail).conjOperator A =
        tFixedIdealWordLinear tail A at ihA
      rw [ihA]
      exact LinearMap.congr_fun
        (tFixedIdealLetterTransport_conjOperatorLinearMap letter) _

private theorem tFixedIdealWordTransport_eval :
    ∀ letters : List (BK05SignedPhaseLetter (-Real.pi / 6)),
      (tFixedIdealWordTransport letters).toLinearEquiv.toLinearMap =
        Matrix.toEuclideanLin
          ((BK05SignedPhaseLetter.evalList (-Real.pi / 6) letters :
              UnitaryGate (Fin 2)) : Matrix (Fin 2) (Fin 2) Complex) := by
  intro letters
  induction letters with
  | nil =>
      apply LinearMap.ext
      intro x
      simp [tFixedIdealWordTransport, BK05SignedPhaseLetter.evalList,
        UnitaryTransport.identity]
  | cons letter tail ih =>
      apply LinearMap.ext
      intro x
      change tFixedIdealLetterTransport letter
          (tFixedIdealWordTransport tail x) =
        Matrix.toEuclideanLin
          (((letter.eval (-Real.pi / 6) : UnitaryGate (Fin 2)) :
              Matrix (Fin 2) (Fin 2) Complex) *
            ((BK05SignedPhaseLetter.evalList (-Real.pi / 6) tail :
              UnitaryGate (Fin 2)) : Matrix (Fin 2) (Fin 2) Complex)) x
      have hletter := LinearMap.congr_fun
        (tFixedIdealLetterTransport_eval letter)
          (tFixedIdealWordTransport tail x)
      change tFixedIdealLetterTransport letter
          (tFixedIdealWordTransport tail x) =
        Matrix.toEuclideanLin
          ((letter.eval (-Real.pi / 6) : UnitaryGate (Fin 2)) :
            Matrix (Fin 2) (Fin 2) Complex)
          (tFixedIdealWordTransport tail x) at hletter
      rw [hletter]
      have ihx := LinearMap.congr_fun ih x
      change tFixedIdealWordTransport tail x =
        Matrix.toEuclideanLin
          ((BK05SignedPhaseLetter.evalList (-Real.pi / 6) tail :
            UnitaryGate (Fin 2)) : Matrix (Fin 2) (Fin 2) Complex) x at ihx
      rw [ihx]
      change
        (Matrix.toLpLin 2 2
          ((letter.eval (-Real.pi / 6) : Matrix (Fin 2) (Fin 2) Complex))
          ((Matrix.toLpLin 2 2
            (BK05SignedPhaseLetter.evalList (-Real.pi / 6) tail :
              Matrix (Fin 2) (Fin 2) Complex)) x)) = _
      rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]

private theorem selectedWireKraus_unitary_operator
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) (gate : UnitaryGate (Fin 2)) :
    (selectedWireKraus wire (unitaryGateKraus gate)).operator () =
      Matrix.toEuclideanLin
        (singleQubitLift wire gate :
          Matrix (Bitstring Wire) (Bitstring Wire) Complex) := by
  change (selectedWireFactorization wire).symm.conjOperator
      (TensorProduct.map
        (Matrix.toEuclideanLin
          (gate : Matrix (Fin 2) (Fin 2) Complex))
        (1 : Operator (QubitRegister (OtherWires wire)))) = _
  exact selectedWire_gateOperator_eq_singleQubitLift wire gate

/-- A selected-wire unitary Kraus recipe acts by the exact concrete register
lift on every input operator, including operators entangled across the
selected/complement factorization. -/
private theorem selectedWireKraus_unitary_action
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) (gate : UnitaryGate (Fin 2))
    (A : Operator (QubitRegister Wire)) :
    (selectedWireKraus wire (unitaryGateKraus gate)).inducedMap A =
      (Matrix.toEuclideanLin
        (singleQubitLift wire gate :
          Matrix (Bitstring Wire) (Bitstring Wire) Complex)).comp
        (A.comp (LinearMap.adjoint
          (Matrix.toEuclideanLin
            (singleQubitLift wire gate :
              Matrix (Bitstring Wire) (Bitstring Wire) Complex)))) := by
  rw [FiniteKrausFamily.inducedMap_apply]
  rw [Fintype.sum_unique, selectedWireKraus_unitary_operator]

/- A channel representation is chosen only to expose its physical finite
Kraus branches.  Completeness and the induced-map equation below are the
theorems returned by Choi--Kraus, not stored assumptions. -/
private noncomputable def channelKrausSize
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Phi : QuantumChannel H K) : Nat :=
  Classical.choose Phi.exists_finiteKrausFamily_representation

private noncomputable def channelKraus
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Phi : QuantumChannel H K) :
    FiniteKrausFamily (Fin (channelKrausSize Phi)) H K :=
  Classical.choose
    (Classical.choose_spec Phi.exists_finiteKrausFamily_representation)

private theorem channelKraus_complete
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Phi : QuantumChannel H K) : (channelKraus Phi).Complete :=
  (Classical.choose_spec
    (Classical.choose_spec Phi.exists_finiteKrausFamily_representation)).1

private theorem channelKraus_inducedMap_eq
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Phi : QuantumChannel H K) :
    (channelKraus Phi).inducedMap = Phi.toLinearMap :=
  (Classical.choose_spec
    (Classical.choose_spec Phi.exists_finiteKrausFamily_representation)).2

private theorem channelKraus_inducedMap_apply
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Phi : QuantumChannel H K) (A : Operator H) :
    (channelKraus Phi).inducedMap A = Phi A := by
  exact LinearMap.congr_fun (channelKraus_inducedMap_eq Phi) A

private theorem prepareRightKraus_inducedMap_apply
    {H K : Type}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) (A : Operator H) :
    (ThermalEncoding.prepareRightKraus H K sigma).inducedMap A =
      TensorProduct.map A sigma.toOperator := by
  simpa [ThermalEncoding.prepareRight] using
    ThermalEncoding.prepareRight_apply H K sigma A

/- Extend a finite Kraus recipe on the right tensor factor while leaving an
arbitrary left factor (which may be correlated with a later reference)
untouched. -/
private noncomputable def idTensorKraus
    {kappa K L : Type} [Fintype kappa]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
    (E : FiniteKrausFamily kappa K L)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] :
    FiniteKrausFamily kappa (CompositeSystem H K) (CompositeSystem H L) where
  operator i := TensorProduct.map (1 : Operator H) (E.operator i)

private theorem tensorMap_sum_right_kraus
    {kappa H K : Type} [Fintype kappa]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (A : Operator H) (B : kappa -> Operator K) :
    TensorProduct.map A (∑ i, B i) =
      ∑ i, TensorProduct.map A (B i) := by
  classical
  induction (Finset.univ : Finset kappa) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [Finset.sum_insert hi, TensorProduct.map_add_right, ih]

private theorem idTensorKraus_complete
    {kappa H K L : Type} [Fintype kappa]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
    {E : FiniteKrausFamily kappa K L} (hE : E.Complete) :
    (idTensorKraus E H).Complete := by
  classical
  rw [FiniteKrausFamily.Complete]
  calc
    (∑ i,
        (LinearMap.adjoint ((idTensorKraus E H).operator i)).comp
          ((idTensorKraus E H).operator i)) =
        ∑ i, TensorProduct.map (1 : Operator H)
          ((LinearMap.adjoint (E.operator i)).comp (E.operator i)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [idTensorKraus]
      rw [TensorProduct.adjoint_map, LinearMap.adjoint_one,
        <- TensorProduct.map_comp]
      congr 1
    _ = TensorProduct.map (1 : Operator H)
        (∑ i, (LinearMap.adjoint (E.operator i)).comp (E.operator i)) := by
      rw [tensorMap_sum_right_kraus]
    _ = TensorProduct.map (1 : Operator H) (1 : Operator K) := by rw [hE]
    _ = 1 := TensorProduct.map_one

private theorem idTensorKraus_inducedMap_tensor
    {kappa H K L : Type} [Fintype kappa]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
    (E : FiniteKrausFamily kappa K L) (A : Operator H) (B : Operator K) :
    (idTensorKraus E H).inducedMap (TensorProduct.map A B) =
      TensorProduct.map A (E.inducedMap B) := by
  classical
  rw [FiniteKrausFamily.inducedMap_apply,
    FiniteKrausFamily.inducedMap_apply, tensorMap_sum_right_kraus]
  apply Finset.sum_congr rfl
  intro i _
  simp only [idTensorKraus]
  rw [TensorProduct.adjoint_map, LinearMap.adjoint_one]
  simp only [<- TensorProduct.map_comp]
  congr 1

/- A literal observed ZZ branch is one physical projector branch.  It is not
claimed complete in isolation; completeness is recovered only after all
terminal branches are assembled. -/
private noncomputable def phaseBranchKraus (coin : Bool) :
    FiniteKrausFamily Unit TwoQubit.TwoQubitSpace TwoQubit.TwoQubitSpace where
  operator _ := jointStabilizerProjector zzMeasurement.checks
    zzMeasurement.commute (observedRetrySyndrome coin)

private theorem phaseBranchKraus_inducedMap_apply (coin : Bool)
    (A : Operator TwoQubit.TwoQubitSpace) :
    (phaseBranchKraus coin).inducedMap A = observedBranchLinear coin A := by
  rw [FiniteKrausFamily.inducedMap_apply, Fintype.sum_unique,
    observedBranchLinear_apply]
  change _ = (jointStabilizerInstrument zzMeasurement.checks
    zzMeasurement.commute).branchOperator (observedRetrySyndrome coin) A
  rw [jointStabilizerInstrument_branchOperator]
  simp only [phaseBranchKraus, jointStabilizerProjector_adjoint]
  rfl

private noncomputable def hPhaseDensity (h : DensityOperator QubitSpace) :
    DensityOperator QubitSpace :=
  (QuantumChannel.unitaryConj hResourceTransport).mapDensity h

private theorem hPhaseDensity_toOperator (h : DensityOperator QubitSpace) :
    (hPhaseDensity h).toOperator = hPhaseRaw h :=
  rfl

/- The H injection branch is the actual density preparation, coordinate
transport, selected ZZ projector, and XOR/discard postprocess in sequence. -/
private noncomputable def hStepKraus (h : DensityOperator QubitSpace)
    (coin : Bool) :=
  krausSeq (ThermalEncoding.prepareRightKraus
      QubitSpace QubitSpace (hPhaseDensity h))
    (krausSeq
      (channelKraus (QuantumChannel.unitaryConj
        TwoQubit.tensorRegisterTransport))
      (krausSeq (phaseBranchKraus coin) (channelKraus oneShotPostprocess)))

private theorem hStepKraus_inducedMap_apply
    (h : DensityOperator QubitSpace) (coin : Bool)
    (data : Operator QubitSpace) :
    (hStepKraus h coin).inducedMap data = hStepRaw h coin data := by
  rw [hStepKraus, krausSeq_inducedMap_apply, krausSeq_inducedMap_apply,
    krausSeq_inducedMap_apply, prepareRightKraus_inducedMap_apply,
    channelKraus_inducedMap_apply, channelKraus_inducedMap_apply,
    phaseBranchKraus_inducedMap_apply]
  rfl

private theorem hStepLinear_completelyPositive
    (h : DensityOperator QubitSpace) (coin : Bool) :
    CompletelyPositive (phaseBranchRawLinear (hPhaseRaw h) coin) := by
  rw [show phaseBranchRawLinear (hPhaseRaw h) coin =
      (hStepKraus h coin).inducedMap by
    apply LinearMap.ext
    intro data
    rw [hStepKraus_inducedMap_apply]
    rfl]
  exact (hStepKraus h coin).inducedMap_completelyPositive

/- The two source T states are prepared as an honest density before the
source-pair measurement.  The accepted projector remains inside the later
injection recipe, so its unnormalised (possibly zero) output is never
normalized or re-prepared. -/
private noncomputable def tPairDensity (t : DensityOperator QubitSpace) :
    DensityOperator TwoQubit.TwoQubitSpace :=
  (QuantumChannel.unitaryConj TwoQubit.tensorRegisterTransport).mapDensity
    (DensityOperator.tensorDensity t t)

private theorem tPairDensity_toOperator (t : DensityOperator QubitSpace) :
    (tPairDensity t).toOperator = tPairInputRaw t :=
  rfl

/- One accepted source-pair outcome, its actual XOR/discard and Hadamard
postprocess, and the subsequent selected phase-injection outcome form one
Kraus recipe.  In particular, `tAcceptedPhaseRaw` is only an intermediate
operator in the induced-map proof, never an input density. -/
private noncomputable def tAcceptedStepKraus
    (t : DensityOperator QubitSpace) (coin : Bool) :=
  krausSeq
    (ThermalEncoding.prepareRightKraus
      QubitSpace TwoQubit.TwoQubitSpace (tPairDensity t))
    (krausSeq
      (idTensorKraus (phaseBranchKraus true) QubitSpace)
      (krausSeq
        (idTensorKraus (channelKraus oneShotPostprocess) QubitSpace)
        (krausSeq
          (idTensorKraus
            (channelKraus (QuantumChannel.unitaryConj hadamardTransport))
            QubitSpace)
          (krausSeq
            (channelKraus (QuantumChannel.unitaryConj
              TwoQubit.tensorRegisterTransport))
            (krausSeq (phaseBranchKraus coin)
              (channelKraus oneShotPostprocess))))))

set_option maxRecDepth 4000 in
private theorem tAcceptedStepKraus_inducedMap_apply
    (t : DensityOperator QubitSpace) (coin : Bool)
    (data : Operator QubitSpace) :
    (tAcceptedStepKraus t coin).inducedMap data =
      phaseBranchRaw (tAcceptedPhaseRaw t) data coin := by
  rw [tAcceptedStepKraus, krausSeq_inducedMap_apply,
    krausSeq_inducedMap_apply, krausSeq_inducedMap_apply,
    krausSeq_inducedMap_apply, krausSeq_inducedMap_apply,
    krausSeq_inducedMap_apply, prepareRightKraus_inducedMap_apply,
    idTensorKraus_inducedMap_tensor, phaseBranchKraus_inducedMap_apply,
    idTensorKraus_inducedMap_tensor, channelKraus_inducedMap_apply,
    idTensorKraus_inducedMap_tensor, channelKraus_inducedMap_apply,
    channelKraus_inducedMap_apply, phaseBranchKraus_inducedMap_apply,
    channelKraus_inducedMap_apply]
  rfl

private theorem tAcceptedStepLinear_completelyPositive
    (t : DensityOperator QubitSpace) (coin : Bool) :
    CompletelyPositive (phaseBranchRawLinear (tAcceptedPhaseRaw t) coin) := by
  rw [show phaseBranchRawLinear (tAcceptedPhaseRaw t) coin =
      (tAcceptedStepKraus t coin).inducedMap by
    apply LinearMap.ext
    intro data
    exact (tAcceptedStepKraus_inducedMap_apply t coin data).symm]
  exact (tAcceptedStepKraus t coin).inducedMap_completelyPositive

/- The supplier's rejection branch keeps the full source pair through the
selected projector and then discards that entire pair through the actual
partial-trace channel before another attempt. -/
private noncomputable def tRejectStepKraus (t : DensityOperator QubitSpace) :=
  krausSeq
    (ThermalEncoding.prepareRightKraus
      QubitSpace TwoQubit.TwoQubitSpace (tPairDensity t))
    (krausSeq
      (idTensorKraus (phaseBranchKraus false) QubitSpace)
      (channelKraus
        (partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace)))

private theorem tRejectStepKraus_inducedMap_apply
    (t : DensityOperator QubitSpace) (data : Operator QubitSpace) :
    (tRejectStepKraus t).inducedMap data = tRejectedDataRaw data t := by
  rw [tRejectStepKraus, krausSeq_inducedMap_apply,
    krausSeq_inducedMap_apply, prepareRightKraus_inducedMap_apply,
    idTensorKraus_inducedMap_tensor, phaseBranchKraus_inducedMap_apply,
    channelKraus_inducedMap_apply]
  rfl

private theorem tRejectStepLinear_completelyPositive
    (t : DensityOperator QubitSpace) :
    CompletelyPositive (tRejectedDataRawLinear t) := by
  rw [show tRejectedDataRawLinear t = (tRejectStepKraus t).inducedMap by
    apply LinearMap.ext
    intro data
    exact (tRejectStepKraus_inducedMap_apply t data).symm]
  exact (tRejectStepKraus t).inducedMap_completelyPositive

/- Complete positivity is propagated through the already accepted literal
retry/component recursions.  These closure lemmas add no semantic fields;
they merely keep the physical Kraus evidence available until the terminal
families are assembled. -/
private theorem completelyPositive_zero_local
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    CompletelyPositive
      (0 : Operator H →ₗ[Complex] Operator K) := by
  intro n M hM
  constructor
  · intro i j
    simp [OperatorMatrix.map]
  · intro x
    simp [OperatorMatrix.map]

private theorem completelyPositive_id_local
    {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H] :
    CompletelyPositive
      (LinearMap.id : Operator H →ₗ[Complex] Operator H) :=
  (QuantumChannel.id H).completely_positive

private theorem completelyPositive_add_local
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {Phi Psi : Operator H →ₗ[Complex] Operator K}
    (hPhi : CompletelyPositive Phi) (hPsi : CompletelyPositive Psi) :
    CompletelyPositive (Phi + Psi) := by
  intro n M hM
  constructor
  · intro i j
    simp only [OperatorMatrix.map, LinearMap.add_apply, map_add]
    exact congrArg₂ (fun A B => A + B)
      ((hPhi n M hM).1 i j) ((hPsi n M hM).1 i j)
  · intro x
    have hp := (hPhi n M hM).2 x
    have hq := (hPsi n M hM).2 x
    simpa only [OperatorMatrix.map, LinearMap.add_apply, inner_add_left,
      Complex.add_re, Finset.sum_add_distrib] using add_nonneg hp hq

private theorem completelyPositive_comp_local
    {H K L : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
    {Phi : Operator H →ₗ[Complex] Operator K}
    {Psi : Operator K →ₗ[Complex] Operator L}
    (hPhi : CompletelyPositive Phi) (hPsi : CompletelyPositive Psi) :
    CompletelyPositive (Psi.comp Phi) := by
  intro n M hM
  exact hPsi n (OperatorMatrix.map Phi M) (hPhi n M hM)

private theorem signedHRawLinear_completelyPositive
    (sign : BK05WordPolarity) : CompletelyPositive (signedHRawLinear sign) := by
  cases sign <;> exact hadamardTransport.completelyPositive_conjOperator

private theorem signedKRawLinear_completelyPositive
    (sign : BK05WordPolarity) : CompletelyPositive (signedKRawLinear sign) := by
  cases sign with
  | normal => exact phaseTransport.completelyPositive_conjOperator
  | inverse => exact phaseTransport.symm.completelyPositive_conjOperator

private theorem phaseCycleTargetChannel_completelyPositive
    (q : Nat) (target : ZMod q) :
    CompletelyPositive (phaseCycleTargetChannel q target) := by
  simpa [phaseCycleTargetChannel] using
    (OneQubitMagic.phaseShiftTransport
      (phaseCycleAngle q * target.val)).completelyPositive_conjOperator

private theorem hFixedIdealLetterLinear_completelyPositive
    (letter : BK05SignedPhaseLetter (-Real.pi / 4)) :
    CompletelyPositive (hFixedIdealLetterLinear letter) := by
  cases letter with
  | positive atom =>
      cases atom with
      | h => exact signedHRawLinear_completelyPositive .normal
      | k => exact signedKRawLinear_completelyPositive .normal
      | phase => exact phaseCycleTargetChannel_completelyPositive 8 (hPhaseTarget .normal)
  | negative atom =>
      cases atom with
      | h => exact signedHRawLinear_completelyPositive .inverse
      | k => exact signedKRawLinear_completelyPositive .inverse
      | phase => exact phaseCycleTargetChannel_completelyPositive 8 (hPhaseTarget .inverse)

private theorem hFixedIdealWordLinear_completelyPositive :
    ∀ letters : List (BK05SignedPhaseLetter (-Real.pi / 4)),
      CompletelyPositive (hFixedIdealWordLinear letters) := by
  intro letters
  induction letters with
  | nil =>
      simpa [hFixedIdealWordLinear] using
        (completelyPositive_id_local (H := QubitSpace))
  | cons letter tail ih =>
      simpa [hFixedIdealWordLinear] using
        completelyPositive_comp_local ih
          (hFixedIdealLetterLinear_completelyPositive letter)

private theorem tFixedIdealLetterLinear_completelyPositive
    (letter : BK05SignedPhaseLetter (-Real.pi / 6)) :
    CompletelyPositive (tFixedIdealLetterLinear letter) := by
  cases letter with
  | positive atom =>
      cases atom with
      | h => exact signedHRawLinear_completelyPositive .normal
      | k => exact signedKRawLinear_completelyPositive .normal
      | phase => exact phaseCycleTargetChannel_completelyPositive 12 (tPhaseTarget .normal)
  | negative atom =>
      cases atom with
      | h => exact signedHRawLinear_completelyPositive .inverse
      | k => exact signedKRawLinear_completelyPositive .inverse
      | phase => exact phaseCycleTargetChannel_completelyPositive 12 (tPhaseTarget .inverse)

private theorem tFixedIdealWordLinear_completelyPositive :
    ∀ letters : List (BK05SignedPhaseLetter (-Real.pi / 6)),
      CompletelyPositive (tFixedIdealWordLinear letters) := by
  intro letters
  induction letters with
  | nil =>
      simpa [tFixedIdealWordLinear] using
        (completelyPositive_id_local (H := QubitSpace))
  | cons letter tail ih =>
      simpa [tFixedIdealWordLinear] using
        completelyPositive_comp_local ih
          (tFixedIdealLetterLinear_completelyPositive letter)

private noncomputable def hFixedIdealWordChannel
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) :
    QuantumChannel QubitSpace QubitSpace where
  toLinearMap := hFixedIdealWordLinear letters
  completely_positive := hFixedIdealWordLinear_completelyPositive letters
  trace_preserving := hFixedIdealWordLinear_trace letters

private noncomputable def tFixedIdealWordChannel
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) :
    QuantumChannel QubitSpace QubitSpace where
  toLinearMap := tFixedIdealWordLinear letters
  completely_positive := tFixedIdealWordLinear_completelyPositive letters
  trace_preserving := tFixedIdealWordLinear_trace letters

private noncomputable def hIdealWordKraus
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) :=
  channelKraus (hFixedIdealWordChannel letters)

private theorem hIdealWordKraus_complete
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) :
    (hIdealWordKraus letters).Complete :=
  channelKraus_complete (hFixedIdealWordChannel letters)

private theorem hIdealWordKraus_inducedMap_eq
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) :
    (hIdealWordKraus letters).inducedMap = hFixedIdealWordLinear letters :=
  channelKraus_inducedMap_eq (hFixedIdealWordChannel letters)

private noncomputable def tIdealWordKraus
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) :=
  channelKraus (tFixedIdealWordChannel letters)

private theorem tIdealWordKraus_complete
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) :
    (tIdealWordKraus letters).Complete :=
  channelKraus_complete (tFixedIdealWordChannel letters)

private theorem tIdealWordKraus_inducedMap_eq
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) :
    (tIdealWordKraus letters).inducedMap = tFixedIdealWordLinear letters :=
  channelKraus_inducedMap_eq (tFixedIdealWordChannel letters)

private theorem hIdealWordKraus_eq_unitaryGateKraus
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) :
    (hIdealWordKraus letters).inducedMap =
      (unitaryGateKraus
        (BK05SignedPhaseLetter.evalList (-Real.pi / 4) letters)).inducedMap := by
  rw [hIdealWordKraus_inducedMap_eq]
  rw [← hFixedIdealWordTransport_conjOperatorLinearMap letters]
  exact (unitaryGateKraus_inducedMap_eq_transport
    (BK05SignedPhaseLetter.evalList (-Real.pi / 4) letters)
    (hFixedIdealWordTransport letters)
    (hFixedIdealWordTransport_eval letters)).symm

private theorem tIdealWordKraus_eq_unitaryGateKraus
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) :
    (tIdealWordKraus letters).inducedMap =
      (unitaryGateKraus
        (BK05SignedPhaseLetter.evalList (-Real.pi / 6) letters)).inducedMap := by
  rw [tIdealWordKraus_inducedMap_eq]
  rw [← tFixedIdealWordTransport_conjOperatorLinearMap letters]
  exact (unitaryGateKraus_inducedMap_eq_transport
    (BK05SignedPhaseLetter.evalList (-Real.pi / 6) letters)
    (tFixedIdealWordTransport letters)
    (tFixedIdealWordTransport_eval letters)).symm

private theorem hRetryTargetHitLinear_completelyPositive
    (h : DensityOperator QubitSpace) (target : ZMod 8) :
    forall (remaining : Nat) (position : ZMod 8),
      CompletelyPositive (hRetryTargetHitLinear h target remaining position) := by
  intro remaining
  induction remaining with
  | zero =>
      intro position
      by_cases htarget : position = target
      · simpa [hRetryTargetHitLinear, htarget] using
          (completelyPositive_id_local (H := QubitSpace))
      · simpa [hRetryTargetHitLinear, htarget] using
          (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
  | succ remaining ih =>
      intro position
      by_cases htarget : position = target
      · simpa [hRetryTargetHitLinear, htarget] using
          (completelyPositive_id_local (H := QubitSpace))
      · simpa [hRetryTargetHitLinear, htarget] using
          completelyPositive_add_local
            (completelyPositive_comp_local (hStepLinear_completelyPositive h true)
              (ih (position + 1)))
            (completelyPositive_comp_local (hStepLinear_completelyPositive h false)
              (ih (position - 1)))

private theorem hRetryPhaseExhaustedLinear_completelyPositive
    (h : DensityOperator QubitSpace) (target : ZMod 8) :
    forall (remaining : Nat) (position : ZMod 8),
      CompletelyPositive
        (hRetryPhaseExhaustedLinear h target remaining position) := by
  intro remaining
  induction remaining with
  | zero =>
      intro position
      by_cases htarget : position = target
      · simpa [hRetryPhaseExhaustedLinear, htarget] using
          (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
      · simpa [hRetryPhaseExhaustedLinear, htarget] using
          (completelyPositive_id_local (H := QubitSpace))
  | succ remaining ih =>
      intro position
      by_cases htarget : position = target
      · simpa [hRetryPhaseExhaustedLinear, htarget] using
          (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
      · simpa [hRetryPhaseExhaustedLinear, htarget] using
          completelyPositive_add_local
            (completelyPositive_comp_local (hStepLinear_completelyPositive h true)
              (ih (position + 1)))
            (completelyPositive_comp_local (hStepLinear_completelyPositive h false)
              (ih (position - 1)))

private theorem hWordLiveLinear_completelyPositive
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    forall letters : List (BK05SignedPhaseLetter (-Real.pi / 4)),
      CompletelyPositive (hWordLiveLinear h blocks letters) := by
  intro letters
  induction letters with
  | nil =>
      simpa [hWordLiveLinear] using
        (completelyPositive_id_local (H := QubitSpace))
  | cons head tail ih =>
      cases head <;> rename_i atom <;> cases atom <;>
        simp only [hWordLiveLinear]
      · exact completelyPositive_comp_local ih
          (signedHRawLinear_completelyPositive .normal)
      · exact completelyPositive_comp_local ih
          (signedKRawLinear_completelyPositive .normal)
      · exact completelyPositive_comp_local ih
          (hRetryTargetHitLinear_completelyPositive h
            (hPhaseTarget .normal) (8 * blocks) 0)
      · exact completelyPositive_comp_local ih
          (signedHRawLinear_completelyPositive .inverse)
      · exact completelyPositive_comp_local ih
          (signedKRawLinear_completelyPositive .inverse)
      · exact completelyPositive_comp_local ih
          (hRetryTargetHitLinear_completelyPositive h
            (hPhaseTarget .inverse) (8 * blocks) 0)

private theorem hWordPhaseStoppedLinear_completelyPositive
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    forall letters : List (BK05SignedPhaseLetter (-Real.pi / 4)),
      CompletelyPositive (hWordPhaseStoppedLinear h blocks letters) := by
  intro letters
  induction letters with
  | nil =>
      simpa [hWordPhaseStoppedLinear] using
        (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
  | cons head tail ih =>
      have hlive := hWordLiveLinear_completelyPositive h blocks tail
      cases head <;> rename_i atom <;> cases atom <;>
        simp only [hWordPhaseStoppedLinear]
      · exact ih
      · exact ih
      · exact completelyPositive_add_local
          (completelyPositive_comp_local hlive
            (hRetryPhaseExhaustedLinear_completelyPositive h
              (hPhaseTarget .normal) (8 * blocks) 0)) ih
      · exact ih
      · exact ih
      · exact completelyPositive_add_local
          (completelyPositive_comp_local hlive
            (hRetryPhaseExhaustedLinear_completelyPositive h
              (hPhaseTarget .inverse) (8 * blocks) 0)) ih

private theorem tSupplyStoppingComponentLinear_completelyPositive
    (t : DensityOperator QubitSpace)
    (nextTrue nextFalse onPairExhausted :
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (htrue : CompletelyPositive nextTrue)
    (hfalse : CompletelyPositive nextFalse)
    (hpair : CompletelyPositive onPairExhausted) :
    forall attempts : Nat,
      CompletelyPositive
        (tSupplyStoppingComponentLinear t attempts
          nextTrue nextFalse onPairExhausted) := by
  intro attempts
  induction attempts with
  | zero => simpa [tSupplyStoppingComponentLinear] using hpair
  | succ attempts ih =>
      simpa [tSupplyStoppingComponentLinear] using
        completelyPositive_add_local
          (completelyPositive_add_local
            (completelyPositive_comp_local
              (tAcceptedStepLinear_completelyPositive t true) htrue)
            (completelyPositive_comp_local
              (tAcceptedStepLinear_completelyPositive t false) hfalse))
          (completelyPositive_comp_local
            (tRejectStepLinear_completelyPositive t) ih)

private theorem tRetryTargetHitLinear_completelyPositive
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12) :
    forall (remaining : Nat) (position : ZMod 12),
      CompletelyPositive
        (tRetryTargetHitLinear t pairAttempts target remaining position) := by
  intro remaining
  induction remaining with
  | zero =>
      intro position
      by_cases htarget : position = target
      · simpa [tRetryTargetHitLinear, htarget] using
          (completelyPositive_id_local (H := QubitSpace))
      · simpa [tRetryTargetHitLinear, htarget] using
          (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
  | succ remaining ih =>
      intro position
      by_cases htarget : position = target
      · simpa [tRetryTargetHitLinear, htarget] using
          (completelyPositive_id_local (H := QubitSpace))
      · simpa [tRetryTargetHitLinear, tSupplyTargetHitLinear,
          tSupplyStoppingComponentLinear, htarget] using
          tSupplyStoppingComponentLinear_completelyPositive t
            (tRetryTargetHitLinear t pairAttempts target remaining (position + 1))
            (tRetryTargetHitLinear t pairAttempts target remaining (position - 1))
            (0 : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
            (ih (position + 1)) (ih (position - 1))
            (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
            pairAttempts

private theorem tRetryPhaseExhaustedLinear_completelyPositive
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12) :
    forall (remaining : Nat) (position : ZMod 12),
      CompletelyPositive
        (tRetryPhaseExhaustedLinear t pairAttempts target remaining position) := by
  intro remaining
  induction remaining with
  | zero =>
      intro position
      by_cases htarget : position = target
      · simpa [tRetryPhaseExhaustedLinear, htarget] using
          (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
      · simpa [tRetryPhaseExhaustedLinear, htarget] using
          (completelyPositive_id_local (H := QubitSpace))
  | succ remaining ih =>
      intro position
      by_cases htarget : position = target
      · simpa [tRetryPhaseExhaustedLinear, htarget] using
          (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
      · simpa [tRetryPhaseExhaustedLinear, tSupplyPhaseExhaustedLinear,
          tSupplyStoppingComponentLinear, htarget] using
          tSupplyStoppingComponentLinear_completelyPositive t
            (tRetryPhaseExhaustedLinear t pairAttempts target remaining (position + 1))
            (tRetryPhaseExhaustedLinear t pairAttempts target remaining (position - 1))
            (0 : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
            (ih (position + 1)) (ih (position - 1))
            (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
            pairAttempts

private theorem tRetryPairExhaustedLinear_completelyPositive
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12) :
    forall (remaining : Nat) (position : ZMod 12),
      CompletelyPositive
        (tRetryPairExhaustedLinear t pairAttempts target remaining position) := by
  intro remaining
  induction remaining with
  | zero =>
      intro position
      simpa [tRetryPairExhaustedLinear] using
        (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
  | succ remaining ih =>
      intro position
      by_cases htarget : position = target
      · simpa [tRetryPairExhaustedLinear, htarget] using
          (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
      · simpa [tRetryPairExhaustedLinear, tSupplyPairExhaustedLinear,
          tSupplyStoppingComponentLinear, htarget] using
          tSupplyStoppingComponentLinear_completelyPositive t
            (tRetryPairExhaustedLinear t pairAttempts target remaining (position + 1))
            (tRetryPairExhaustedLinear t pairAttempts target remaining (position - 1))
            (LinearMap.id : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
            (ih (position + 1)) (ih (position - 1))
            (completelyPositive_id_local (H := QubitSpace)) pairAttempts

private theorem tWordLiveLinear_completelyPositive
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    forall letters : List (BK05SignedPhaseLetter (-Real.pi / 6)),
      CompletelyPositive (tWordLiveLinear t pairAttempts blocks letters) := by
  intro letters
  induction letters with
  | nil =>
      simpa [tWordLiveLinear] using
        (completelyPositive_id_local (H := QubitSpace))
  | cons head tail ih =>
      cases head <;> rename_i atom <;> cases atom <;>
        simp only [tWordLiveLinear]
      · exact completelyPositive_comp_local ih
          (signedHRawLinear_completelyPositive .normal)
      · exact completelyPositive_comp_local ih
          (signedKRawLinear_completelyPositive .normal)
      · exact completelyPositive_comp_local ih
          (tRetryTargetHitLinear_completelyPositive t pairAttempts
            (tPhaseTarget .normal) (12 * blocks) 0)
      · exact completelyPositive_comp_local ih
          (signedHRawLinear_completelyPositive .inverse)
      · exact completelyPositive_comp_local ih
          (signedKRawLinear_completelyPositive .inverse)
      · exact completelyPositive_comp_local ih
          (tRetryTargetHitLinear_completelyPositive t pairAttempts
            (tPhaseTarget .inverse) (12 * blocks) 0)

private theorem tWordPhaseStoppedLinear_completelyPositive
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    forall letters : List (BK05SignedPhaseLetter (-Real.pi / 6)),
      CompletelyPositive
        (tWordPhaseStoppedLinear t pairAttempts blocks letters) := by
  intro letters
  induction letters with
  | nil =>
      simpa [tWordPhaseStoppedLinear] using
        (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
  | cons head tail ih =>
      have hlive := tWordLiveLinear_completelyPositive t pairAttempts blocks tail
      cases head <;> rename_i atom <;> cases atom <;>
        simp only [tWordPhaseStoppedLinear]
      · exact ih
      · exact ih
      · exact completelyPositive_add_local
          (completelyPositive_comp_local hlive
            (tRetryPhaseExhaustedLinear_completelyPositive t pairAttempts
              (tPhaseTarget .normal) (12 * blocks) 0)) ih
      · exact ih
      · exact ih
      · exact completelyPositive_add_local
          (completelyPositive_comp_local hlive
            (tRetryPhaseExhaustedLinear_completelyPositive t pairAttempts
              (tPhaseTarget .inverse) (12 * blocks) 0)) ih

private theorem tWordPairStoppedLinear_completelyPositive
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    forall letters : List (BK05SignedPhaseLetter (-Real.pi / 6)),
      CompletelyPositive
        (tWordPairStoppedLinear t pairAttempts blocks letters) := by
  intro letters
  induction letters with
  | nil =>
      simpa [tWordPairStoppedLinear] using
        (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
  | cons head tail ih =>
      have hlive := tWordLiveLinear_completelyPositive t pairAttempts blocks tail
      cases head <;> rename_i atom <;> cases atom <;>
        simp only [tWordPairStoppedLinear]
      · exact ih
      · exact ih
      · exact completelyPositive_add_local
          (completelyPositive_comp_local hlive
            (tRetryPairExhaustedLinear_completelyPositive t pairAttempts
              (tPhaseTarget .normal) (12 * blocks) 0)) ih
      · exact ih
      · exact ih
      · exact completelyPositive_add_local
          (completelyPositive_comp_local hlive
            (tRetryPairExhaustedLinear_completelyPositive t pairAttempts
              (tPhaseTarget .inverse) (12 * blocks) 0)) ih

/- Choi--Kraus now turns each proven CP status component into a finite
physical family.  A distinguished zero branch is retained for every status,
so algebraically impossible outcomes are represented rather than filtered. -/
private theorem exists_cpKraus
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Phi : Operator H →ₗ[Complex] Operator K)
    (hPhi : CompletelyPositive Phi) :
    ∃ m : Nat, ∃ E : FiniteKrausFamily (Fin m) H K,
      E.inducedMap = Phi := by
  exact exists_finiteKrausFamily_of_stdChoiMatrix_posSemidef Phi
    (stdChoiMatrix_posSemidef_of_completelyPositive Phi hPhi)

private noncomputable def cpKrausSize
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Phi : Operator H →ₗ[Complex] Operator K)
    (hPhi : CompletelyPositive Phi) : Nat :=
  Classical.choose (exists_cpKraus Phi hPhi)

private noncomputable def cpKraus
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Phi : Operator H →ₗ[Complex] Operator K)
    (hPhi : CompletelyPositive Phi) :
    FiniteKrausFamily (Fin (cpKrausSize Phi hPhi)) H K :=
  Classical.choose (Classical.choose_spec (exists_cpKraus Phi hPhi))

private theorem cpKraus_inducedMap_eq
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Phi : Operator H →ₗ[Complex] Operator K)
    (hPhi : CompletelyPositive Phi) :
    (cpKraus Phi hPhi).inducedMap = Phi :=
  Classical.choose_spec (Classical.choose_spec (exists_cpKraus Phi hPhi))

private noncomputable def paddedKraus
    {kappa H K : Type u} [Fintype kappa]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (E : FiniteKrausFamily kappa H K) :
    FiniteKrausFamily (Option kappa) H K where
  operator
    | none => 0
    | some i => E.operator i

private theorem paddedKraus_inducedMap_eq
    {kappa H K : Type u} [Fintype kappa]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (E : FiniteKrausFamily kappa H K) :
    (paddedKraus E).inducedMap = E.inducedMap := by
  apply LinearMap.ext
  intro A
  rw [FiniteKrausFamily.inducedMap_apply, Fintype.sum_option,
    FiniteKrausFamily.inducedMap_apply]
  simp [paddedKraus]

private noncomputable def krausSum
    {iota kappa H K : Type u} [Fintype iota] [Fintype kappa]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (E : FiniteKrausFamily iota H K) (F : FiniteKrausFamily kappa H K) :
    FiniteKrausFamily (Sum iota kappa) H K where
  operator
    | .inl i => E.operator i
    | .inr j => F.operator j

private theorem krausSum_inducedMap_eq
    {iota kappa H K : Type u} [Fintype iota] [Fintype kappa]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (E : FiniteKrausFamily iota H K) (F : FiniteKrausFamily kappa H K) :
    (krausSum E F).inducedMap = E.inducedMap + F.inducedMap := by
  apply LinearMap.ext
  intro A
  rw [LinearMap.add_apply, FiniteKrausFamily.inducedMap_apply,
    Fintype.sum_sum_type,
    FiniteKrausFamily.inducedMap_apply, FiniteKrausFamily.inducedMap_apply]
  rfl

private abbrev BK05TerminalIndex (liveSize phaseSize pairSize : Nat) :=
  Sum (Option (Fin liveSize))
    (Sum (Option (Fin phaseSize)) (Option (Fin pairSize)))

private def terminalStatus {liveSize phaseSize pairSize : Nat} :
    BK05TerminalIndex liveSize phaseSize pairSize → BK05WordLeafStatus
  | .inl _ => .live
  | .inr (.inl _) => .stoppedPhaseExhausted
  | .inr (.inr _) => .stoppedTPairExhausted

private noncomputable def terminalKraus
    (live phase pair : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (hlive : CompletelyPositive live)
    (hphase : CompletelyPositive phase)
    (hpair : CompletelyPositive pair) :
    FiniteKrausFamily
      (BK05TerminalIndex (cpKrausSize live hlive)
        (cpKrausSize phase hphase) (cpKrausSize pair hpair))
      QubitSpace QubitSpace :=
  krausSum (paddedKraus (cpKraus live hlive))
    (krausSum (paddedKraus (cpKraus phase hphase))
      (paddedKraus (cpKraus pair hpair)))

private theorem terminalKraus_inducedMap_eq
    (live phase pair : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (hlive : CompletelyPositive live)
    (hphase : CompletelyPositive phase)
    (hpair : CompletelyPositive pair) :
    (terminalKraus live phase pair hlive hphase hpair).inducedMap =
      live + phase + pair := by
  rw [terminalKraus, krausSum_inducedMap_eq, krausSum_inducedMap_eq,
    paddedKraus_inducedMap_eq, paddedKraus_inducedMap_eq,
    paddedKraus_inducedMap_eq, cpKraus_inducedMap_eq,
    cpKraus_inducedMap_eq, cpKraus_inducedMap_eq]
  exact (add_assoc live phase pair).symm

/-- The complete terminal family follows from the literal component trace
identity; completeness is proved, never supplied by the compiler caller. -/
private theorem completeTerminalFamily
    (live phase pair : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (hlive : CompletelyPositive live)
    (hphase : CompletelyPositive phase)
    (hpair : CompletelyPositive pair)
    (htrace : ∀ A : Operator QubitSpace,
      LinearMap.trace Complex QubitSpace ((live + phase + pair) A) =
        LinearMap.trace Complex QubitSpace A) :
    (terminalKraus live phase pair hlive hphase hpair).Complete := by
  apply FiniteKrausFamily.complete_of_inducedMap_trace_preserving
  intro A
  rw [LinearMap.congr_fun
    (terminalKraus_inducedMap_eq live phase pair hlive hphase hpair) A]
  exact htrace A

/-- Both stopping labels have literal (possibly zero) Kraus indices, so a
zero-probability physical outcome is retained rather than postselected away. -/
private theorem retainsFailureLeaves
    (live phase pair : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (hlive : CompletelyPositive live)
    (hphase : CompletelyPositive phase)
    (hpair : CompletelyPositive pair) :
    (∃ i : BK05TerminalIndex (cpKrausSize live hlive)
        (cpKrausSize phase hphase) (cpKrausSize pair hpair),
      terminalStatus i = BK05WordLeafStatus.stoppedPhaseExhausted) ∧
      (∃ i : BK05TerminalIndex (cpKrausSize live hlive)
          (cpKrausSize phase hphase) (cpKrausSize pair hpair),
        terminalStatus i = BK05WordLeafStatus.stoppedTPairExhausted) := by
  exact ⟨⟨Sum.inr (Sum.inl none), rfl⟩,
    ⟨Sum.inr (Sum.inr none), rfl⟩⟩

/- The two accepted one-qubit routes now expose their literal terminal status
components as complete finite Kraus families.  The H route has a genuine zero
T-pair-stopping component, retained as a padded physical branch. -/
private noncomputable def hTerminalKraus
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) :=
  terminalKraus
    (hWordLiveLinear h blocks letters)
    (hWordPhaseStoppedLinear h blocks letters)
    (0 : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (hWordLiveLinear_completelyPositive h blocks letters)
    (hWordPhaseStoppedLinear_completelyPositive h blocks letters)
    (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))

private theorem hTerminalKraus_complete
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) :
    (hTerminalKraus h blocks letters).Complete := by
  apply completeTerminalFamily
  intro A
  simpa only [LinearMap.add_apply, LinearMap.zero_apply, add_zero, map_add] using
    hWord_component_trace h blocks letters A

private theorem hTerminalKraus_inducedMap_eq
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) :
    (hTerminalKraus h blocks letters).inducedMap =
      hSignedWordTotalLinear h blocks letters LinearMap.id := by
  rw [hTerminalKraus, terminalKraus_inducedMap_eq]
  apply LinearMap.ext
  intro A
  simpa only [LinearMap.add_apply, LinearMap.zero_apply, add_zero] using
    hWord_components_total h blocks letters A

private noncomputable def tTerminalKraus
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) :=
  terminalKraus
    (tWordLiveLinear t pairAttempts blocks letters)
    (tWordPhaseStoppedLinear t pairAttempts blocks letters)
    (tWordPairStoppedLinear t pairAttempts blocks letters)
    (tWordLiveLinear_completelyPositive t pairAttempts blocks letters)
    (tWordPhaseStoppedLinear_completelyPositive t pairAttempts blocks letters)
    (tWordPairStoppedLinear_completelyPositive t pairAttempts blocks letters)

private theorem tTerminalKraus_complete
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) :
    (tTerminalKraus t pairAttempts blocks letters).Complete := by
  apply completeTerminalFamily
  intro A
  simpa only [LinearMap.add_apply, map_add] using
    tWordComponent_trace t pairAttempts blocks letters A

private theorem tTerminalKraus_inducedMap_eq
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) :
    (tTerminalKraus t pairAttempts blocks letters).inducedMap =
      tWordTotalLinear t pairAttempts blocks letters := by
  rw [tTerminalKraus, terminalKraus_inducedMap_eq]
  exact (tWordComponents_total t pairAttempts blocks letters).symm

/- The selected-wire robustness estimate below uses a finite matrix-unit
expansion.  These elementary bounds keep the argument dimension-explicit and
avoid inferring an ancilla-safe estimate from a one-qubit marginal. -/

private theorem traceNorm_rankOne_le_general
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (x y : H) :
    traceNorm (InnerProductSpace.rankOne Complex x y).toLinearMap ≤
      ‖x‖ * ‖y‖ := by
  change ‖tracePairing (InnerProductSpace.rankOne Complex x y).toLinearMap‖ ≤
    ‖x‖ * ‖y‖
  apply (tracePairing
    (InnerProductSpace.rankOne Complex x y).toLinearMap).opNorm_le_bound
  · positivity
  · intro B
    rw [show tracePairing
        (InnerProductSpace.rankOne Complex x y).toLinearMap B =
          inner Complex y (B x) by
      change LinearMap.trace Complex H
          (B.toLinearMap *
            (InnerProductSpace.rankOne Complex x y).toLinearMap) = _
      rw [show B.toLinearMap *
          (InnerProductSpace.rankOne Complex x y).toLinearMap =
          (InnerProductSpace.rankOne Complex (B x) y).toLinearMap by
        ext z
        simp]
      exact InnerProductSpace.trace_rankOne (B x) y]
    calc
      ‖inner Complex y (B x)‖ ≤ ‖y‖ * ‖B x‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (‖B‖ * ‖x‖) := by
        gcongr
        exact B.le_opNorm x
      _ = (‖x‖ * ‖y‖) * ‖B‖ := by ring

private theorem rankOne_eq_polarization
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    (x y : H) :
    (InnerProductSpace.rankOne Complex x y).toLinearMap =
      (2 : Complex)⁻¹ •
          (InnerProductSpace.rankOne Complex (x + y) (x + y)).toLinearMap +
        Complex.I • ((2 : Complex)⁻¹ •
          (InnerProductSpace.rankOne Complex (x + Complex.I • y)
            (x + Complex.I • y)).toLinearMap) -
        ((1 + Complex.I) * (2 : Complex)⁻¹) •
          ((InnerProductSpace.rankOne Complex x x).toLinearMap +
            (InnerProductSpace.rankOne Complex y y).toLinearMap) := by
  ext z
  have hIhalf : Complex.I * (2 : Complex)⁻¹ * Complex.I =
      -(2 : Complex)⁻¹ := by
    calc
      Complex.I * (2 : Complex)⁻¹ * Complex.I =
          (2 : Complex)⁻¹ * (Complex.I * Complex.I) := by ring
      _ = -(2 : Complex)⁻¹ := by rw [Complex.I_mul_I]; ring
  have hIhalf_mul (a : Complex) :
      Complex.I * ((2 : Complex)⁻¹ * (Complex.I * a)) =
        -(2 : Complex)⁻¹ * a := by
    calc
      Complex.I * ((2 : Complex)⁻¹ * (Complex.I * a)) =
          (Complex.I * (2 : Complex)⁻¹ * Complex.I) * a := by ring
      _ = -(2 : Complex)⁻¹ * a := by rw [hIhalf]
  simp [InnerProductSpace.rankOne_apply, Complex.conj_I]
  simp only [smul_smul]
  rw [hIhalf_mul (inner Complex y z), hIhalf_mul (inner Complex x z),
    hIhalf_mul (Complex.I * inner Complex y z)]
  module

private theorem operator_matrixUnit_expansion_prod
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {beta : Type} [Fintype beta]
    (b : OrthonormalBasis beta Complex H) (A : Operator H) :
    A = ∑ index : beta × beta,
      b.repr (A (b index.2)) index.1 •
        (InnerProductSpace.rankOne Complex
          (b index.1) (b index.2)).toLinearMap := by
  classical
  rw [Fintype.sum_prod_type]
  apply (Module.Basis.ext b.toBasis)
  intro k
  change A (b k) = (∑ i, ∑ j,
    b.repr (A (b j)) i •
      (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap) (b k)
  rw [← OrthonormalBasis.sum_repr' b (A (b k))]
  have hinner : ∀ j, inner Complex (b j) (b k) = if j = k then 1 else 0 :=
    fun j => (orthonormal_iff_ite.mp b.orthonormal) j k
  simp [InnerProductSpace.rankOne_apply, hinner,
    OrthonormalBasis.repr_apply_apply]

private theorem matrixCoefficient_norm_le_traceNorm
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {beta : Type} [Fintype beta]
    (b : OrthonormalBasis beta Complex H) (A : Operator H) (i j : beta) :
    ‖b.repr (A (b j)) i‖ ≤ traceNorm A := by
  let B : H →L[Complex] H :=
    InnerProductSpace.rankOne Complex (b j) (b i)
  have hpair := (tracePairing A).le_opNorm B
  have hB : ‖B‖ = 1 := by
    simp [B, b.orthonormal.norm_eq_one]
  have heval : tracePairing A B = b.repr (A (b j)) i := by
    change LinearMap.trace Complex H
        ((InnerProductSpace.rankOne Complex (b j) (b i)).toLinearMap * A) = _
    rw [show
      (InnerProductSpace.rankOne Complex (b j) (b i)).toLinearMap * A =
        (InnerProductSpace.rankOne Complex (b j)
          ((LinearMap.adjoint A) (b i))).toLinearMap by
      ext z
      change inner Complex (b i) (A z) • b j =
        inner Complex ((LinearMap.adjoint A) (b i)) z • b j
      rw [LinearMap.adjoint_inner_left]]
    rw [InnerProductSpace.trace_rankOne, LinearMap.adjoint_inner_left]
    exact (b.repr_apply_apply (A (b j)) i).symm
  rw [heval, hB, mul_one] at hpair
  exact hpair

private theorem tensorIdKraus_inducedMap_tensor
    {kappa H R : Type} [Fintype kappa]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
    (E : FiniteKrausFamily kappa H H) (A : Operator H) (B : Operator R) :
    (tensorIdKraus E R).inducedMap (TensorProduct.map A B) =
      TensorProduct.map (E.inducedMap A) B := by
  classical
  rw [FiniteKrausFamily.inducedMap_apply,
    FiniteKrausFamily.inducedMap_apply, tensorMap_sum_left_kraus]
  apply Finset.sum_congr rfl
  intro i _
  simp only [tensorIdKraus]
  rw [TensorProduct.adjoint_map, LinearMap.adjoint_one]
  simp only [← TensorProduct.map_comp]
  congr 1

private theorem tensorMap_rankOne_local
    {H R : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
    (x y : H) (r s : R) :
    TensorProduct.map (InnerProductSpace.rankOne Complex x y).toLinearMap
        (InnerProductSpace.rankOne Complex r s).toLinearMap =
      (InnerProductSpace.rankOne Complex (x ⊗ₜ[Complex] r)
        (y ⊗ₜ[Complex] s)).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul h k =>
      change ((inner Complex y h) • x) ⊗ₜ[Complex]
          ((inner Complex s k) • r) =
        (inner Complex (y ⊗ₜ[Complex] s) (h ⊗ₜ[Complex] k)) •
          (x ⊗ₜ[Complex] r)
      rw [TensorProduct.inner_tmul, TensorProduct.smul_tmul, smul_smul,
        TensorProduct.tmul_smul]
  | add z w hz hw => simp [map_add, hz, hw]

/- Polarization upgrades a positive-input estimate to every matrix unit.  The
constant is deliberately coarse: finiteness and ancilla safety matter here,
whereas the distillation schedules later make the source error arbitrarily
small. -/
private theorem linearMap_rankOne_le_sixteen
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (D : Operator H →ₗ[Complex] Operator K) (epsilon : Real)
    (hepsilon : 0 ≤ epsilon)
    (hbound : ∀ z : H,
      traceNorm (D (InnerProductSpace.rankOne Complex z z).toLinearMap) ≤
        epsilon * ‖z‖ ^ 2)
    (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    traceNorm (D (InnerProductSpace.rankOne Complex x y).toLinearMap) ≤
      16 * epsilon := by
  let P : H → Operator H := fun z =>
    (InnerProductSpace.rankOne Complex z z).toLinearMap
  let half : Complex := (2 : Complex)⁻¹
  let diagonalCoeff : Complex := (1 + Complex.I) * half
  have hhalf : ‖half‖ ≤ 1 := by
    dsimp [half]
    norm_num [Complex.norm_def]
  have hdiagonalCoeff : ‖diagonalCoeff‖ ≤ 2 := by
    dsimp [diagonalCoeff, half]
    calc
      ‖(1 + Complex.I) * (2 : Complex)⁻¹‖ ≤
          ‖(1 + Complex.I)‖ * ‖(2 : Complex)⁻¹‖ := norm_mul_le _ _
      _ ≤ 2 * 1 := by
        gcongr
        · calc
            ‖(1 + Complex.I : Complex)‖ ≤ ‖(1 : Complex)‖ + ‖Complex.I‖ :=
              norm_add_le _ _
            _ = 2 := by norm_num [Complex.norm_def]
      _ = 2 := by norm_num
  have hxy : ‖x + y‖ ^ 2 ≤ 4 := by
    have hnorm : ‖x + y‖ ≤ 2 := by
      calc
        ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le _ _
        _ = 2 := by rw [hx, hy]; norm_num
    nlinarith [norm_nonneg (x + y)]
  have hxyI : ‖x + Complex.I • y‖ ^ 2 ≤ 4 := by
    have hnorm : ‖x + Complex.I • y‖ ≤ 2 := by
      calc
        ‖x + Complex.I • y‖ ≤ ‖x‖ + ‖Complex.I • y‖ := norm_add_le _ _
        _ = 2 := by
          rw [norm_smul, hx, hy]
          norm_num [Complex.norm_def]
    nlinarith [norm_nonneg (x + Complex.I • y)]
  have hplus : traceNorm (D (P (x + y))) ≤ 4 * epsilon := by
    calc
      traceNorm (D (P (x + y))) ≤ epsilon * ‖x + y‖ ^ 2 := hbound _
      _ ≤ epsilon * 4 := mul_le_mul_of_nonneg_left hxy hepsilon
      _ = 4 * epsilon := by ring
  have hphase : traceNorm (D (P (x + Complex.I • y))) ≤ 4 * epsilon := by
    calc
      traceNorm (D (P (x + Complex.I • y))) ≤
          epsilon * ‖x + Complex.I • y‖ ^ 2 := hbound _
      _ ≤ epsilon * 4 := mul_le_mul_of_nonneg_left hxyI hepsilon
      _ = 4 * epsilon := by ring
  have hxBound : traceNorm (D (P x)) ≤ epsilon := by
    simpa [hx] using hbound x
  have hyBound : traceNorm (D (P y)) ≤ epsilon := by
    simpa [hy] using hbound y
  have hfirst : traceNorm (half • D (P (x + y))) ≤ 4 * epsilon := by
    rw [traceNorm_smul]
    calc
      ‖half‖ * traceNorm (D (P (x + y))) ≤ 1 * (4 * epsilon) :=
        mul_le_mul hhalf hplus (traceNorm_nonneg _) (by norm_num)
      _ = 4 * epsilon := by ring
  have hsecond :
      traceNorm (Complex.I • (half • D (P (x + Complex.I • y)))) ≤
        4 * epsilon := by
    rw [traceNorm_smul]
    have hnormI : ‖Complex.I‖ = 1 := by norm_num [Complex.norm_def]
    rw [hnormI, one_mul]
    rw [traceNorm_smul]
    calc
      ‖half‖ * traceNorm (D (P (x + Complex.I • y))) ≤ 1 * (4 * epsilon) :=
        mul_le_mul hhalf hphase (traceNorm_nonneg _) (by norm_num)
      _ = 4 * epsilon := by ring
  have hdiagonalSum : traceNorm (D (P x) + D (P y)) ≤ 2 * epsilon := by
    calc
      traceNorm (D (P x) + D (P y)) ≤
          traceNorm (D (P x)) + traceNorm (D (P y)) := traceNorm_add_le _ _
      _ ≤ epsilon + epsilon := add_le_add hxBound hyBound
      _ = 2 * epsilon := by ring
  have hthird :
      traceNorm (diagonalCoeff • (D (P x) + D (P y))) ≤ 4 * epsilon := by
    rw [traceNorm_smul]
    calc
      ‖diagonalCoeff‖ * traceNorm (D (P x) + D (P y)) ≤
          2 * (2 * epsilon) :=
        mul_le_mul hdiagonalCoeff hdiagonalSum (traceNorm_nonneg _) (by norm_num)
      _ = 4 * epsilon := by ring
  rw [rankOne_eq_polarization]
  change traceNorm
      (D (half • P (x + y) +
        Complex.I • (half • P (x + Complex.I • y)) -
        diagonalCoeff • (P x + P y))) ≤ 16 * epsilon
  rw [D.map_sub, D.map_add, D.map_smul, D.map_smul, D.map_smul,
    D.map_smul, D.map_add]
  have htriangle :
      traceNorm
          (half • D (P (x + y)) +
            Complex.I • (half • D (P (x + Complex.I • y))) -
            diagonalCoeff • (D (P x) + D (P y))) ≤
        traceNorm (half • D (P (x + y))) +
          traceNorm (Complex.I • (half • D (P (x + Complex.I • y)))) +
          traceNorm (diagonalCoeff • (D (P x) + D (P y))) := by
    calc
      traceNorm
          (half • D (P (x + y)) +
            Complex.I • (half • D (P (x + Complex.I • y))) -
            diagonalCoeff • (D (P x) + D (P y))) ≤
          traceNorm
              (half • D (P (x + y)) +
                Complex.I • (half • D (P (x + Complex.I • y)))) +
            traceNorm (-(diagonalCoeff • (D (P x) + D (P y)))) := by
              simpa only [sub_eq_add_neg] using
                traceNorm_add_le
                  (half • D (P (x + y)) +
                    Complex.I • (half • D (P (x + Complex.I • y))))
                  (-(diagonalCoeff • (D (P x) + D (P y))))
      _ = traceNorm
              (half • D (P (x + y)) +
                Complex.I • (half • D (P (x + Complex.I • y)))) +
            traceNorm (diagonalCoeff • (D (P x) + D (P y))) := by
              rw [traceNorm_neg]
      _ ≤ _ := by
        gcongr
        exact traceNorm_add_le (half • D (P (x + y)))
          (Complex.I • (half • D (P (x + Complex.I • y))))
  calc
    _ ≤ traceNorm (half • D (P (x + y))) +
          traceNorm (Complex.I • (half • D (P (x + Complex.I • y)))) +
          traceNorm (diagonalCoeff • (D (P x) + D (P y))) := htriangle
    _ ≤ 4 * epsilon + 4 * epsilon + 4 * epsilon :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ ≤ 16 * epsilon := by nlinarith

private theorem traceNorm_tensor_basisUnit_le_card
    {H R : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
    {beta gamma : Type} [Fintype beta] [Fintype gamma]
    (bH : OrthonormalBasis beta Complex H)
    (bR : OrthonormalBasis gamma Complex R)
    (A : Operator H) (r s : gamma) :
    traceNorm (TensorProduct.map A
      (InnerProductSpace.rankOne Complex (bR r) (bR s)).toLinearMap) ≤
      (Fintype.card (beta × beta) : Real) * traceNorm A := by
  classical
  let restUnit :=
    (InnerProductSpace.rankOne Complex (bR r) (bR s)).toLinearMap
  let summand : beta × beta → Operator H := fun index =>
    bH.repr (A (bH index.2)) index.1 •
      (InnerProductSpace.rankOne Complex (bH index.1) (bH index.2)).toLinearMap
  have hexpand : A = ∑ index : beta × beta, summand index := by
    simpa [summand] using operator_matrixUnit_expansion_prod bH A
  calc
    traceNorm (TensorProduct.map A restUnit) =
        traceNorm (TensorProduct.map (∑ index : beta × beta, summand index)
          restUnit) := by rw [hexpand]
    _ = traceNorm (∑ index : beta × beta,
        TensorProduct.map (summand index) restUnit) := by
      exact congrArg traceNorm (tensorMap_sum_left_kraus summand restUnit)
    _ = traceNorm (∑ index : beta × beta,
        bH.repr (A (bH index.2)) index.1 •
          (InnerProductSpace.rankOne Complex
            (bH index.1 ⊗ₜ[Complex] bR r)
            (bH index.2 ⊗ₜ[Complex] bR s)).toLinearMap) := by
      congr 1
      apply Finset.sum_congr rfl
      intro index _
      simp only [summand, restUnit, TensorProduct.map_smul_left]
      rw [tensorMap_rankOne_local]
    _ ≤ ∑ index : beta × beta,
          traceNorm
            (bH.repr (A (bH index.2)) index.1 •
              (InnerProductSpace.rankOne Complex
                (bH index.1 ⊗ₜ[Complex] bR r)
                (bH index.2 ⊗ₜ[Complex] bR s)).toLinearMap) := by
      simpa using traceNorm_sum_le (Finset.univ : Finset (beta × beta))
        (fun index =>
          bH.repr (A (bH index.2)) index.1 •
            (InnerProductSpace.rankOne Complex
              (bH index.1 ⊗ₜ[Complex] bR r)
              (bH index.2 ⊗ₜ[Complex] bR s)).toLinearMap)
    _ ≤ ∑ _index : beta × beta, traceNorm A := by
      apply Finset.sum_le_sum
      intro index _
      rw [traceNorm_smul]
      have hrank : traceNorm
          (InnerProductSpace.rankOne Complex
            (bH index.1 ⊗ₜ[Complex] bR r)
            (bH index.2 ⊗ₜ[Complex] bR s)).toLinearMap ≤ 1 := by
        calc
          traceNorm
              (InnerProductSpace.rankOne Complex
                (bH index.1 ⊗ₜ[Complex] bR r)
                (bH index.2 ⊗ₜ[Complex] bR s)).toLinearMap ≤
              ‖bH index.1 ⊗ₜ[Complex] bR r‖ *
                ‖bH index.2 ⊗ₜ[Complex] bR s‖ :=
            traceNorm_rankOne_le_general _ _
          _ = 1 := by
            simp [bH.orthonormal.norm_eq_one, bR.orthonormal.norm_eq_one]
      calc
        ‖bH.repr (A (bH index.2)) index.1‖ *
            traceNorm
              (InnerProductSpace.rankOne Complex
                (bH index.1 ⊗ₜ[Complex] bR r)
                (bH index.2 ⊗ₜ[Complex] bR s)).toLinearMap ≤
            traceNorm A * 1 :=
          mul_le_mul
            (matrixCoefficient_norm_le_traceNorm bH A index.1 index.2)
            hrank (traceNorm_nonneg _) (traceNorm_nonneg A)
        _ = traceNorm A := mul_one _
    _ = (Fintype.card (beta × beta) : Real) * traceNorm A := by simp

/- Expanding in a product matrix-unit basis turns a local channel estimate into
an estimate against an arbitrary, possibly entangled reference.  The finite
dimension factor is intentionally explicit and coarse; the compiler later
chooses the distillation accuracy below the resulting finite budget. -/
private theorem tensorIdKraus_difference_le
    {kappa lambda H R : Type}
    [Fintype kappa] [Fintype lambda]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
    {beta gamma : Type} [Fintype beta] [Fintype gamma]
    (bH : OrthonormalBasis beta Complex H)
    (bR : OrthonormalBasis gamma Complex R)
    (E : FiniteKrausFamily kappa H H)
    (F : FiniteKrausFamily lambda H H)
    (epsilon : Real)
    (hlocal : forall i j : beta,
      traceNorm
          (E.inducedMap
              (InnerProductSpace.rankOne Complex (bH i) (bH j)).toLinearMap -
            F.inducedMap
              (InnerProductSpace.rankOne Complex (bH i) (bH j)).toLinearMap) <=
        epsilon)
    (A : Operator (CompositeSystem H R)) :
    traceNorm
        ((tensorIdKraus E R).inducedMap A -
          (tensorIdKraus F R).inducedMap A) <=
      (Fintype.card ((beta × gamma) × (beta × gamma)) : Real) *
        ((Fintype.card (beta × beta) : Real) * epsilon * traceNorm A) := by
  classical
  let b := bH.tensorProduct bR
  let D : Operator (CompositeSystem H R) →ₗ[Complex]
      Operator (CompositeSystem H R) :=
    (tensorIdKraus E R).inducedMap - (tensorIdKraus F R).inducedMap
  let summand : (beta × gamma) × (beta × gamma) ->
      Operator (CompositeSystem H R) := fun index =>
    b.repr (A (b index.2)) index.1 •
      (InnerProductSpace.rankOne Complex
        (b index.1) (b index.2)).toLinearMap
  have hexpand : A = ∑ index : (beta × gamma) × (beta × gamma),
      summand index := by
    simpa [summand] using operator_matrixUnit_expansion_prod b A
  have hmap : D A = ∑ index : (beta × gamma) × (beta × gamma),
      D (summand index) := by
    rw [hexpand, map_sum]
  have hunit (index : (beta × gamma) × (beta × gamma)) :
      D ((InnerProductSpace.rankOne Complex
          (b index.1) (b index.2)).toLinearMap) =
        TensorProduct.map
          (E.inducedMap
              (InnerProductSpace.rankOne Complex
                (bH index.1.1) (bH index.2.1)).toLinearMap -
            F.inducedMap
              (InnerProductSpace.rankOne Complex
                (bH index.1.1) (bH index.2.1)).toLinearMap)
          (InnerProductSpace.rankOne Complex
            (bR index.1.2) (bR index.2.2)).toLinearMap := by
    change
      (tensorIdKraus E R).inducedMap
          ((InnerProductSpace.rankOne Complex
            (b index.1) (b index.2)).toLinearMap) -
        (tensorIdKraus F R).inducedMap
          ((InnerProductSpace.rankOne Complex
            (b index.1) (b index.2)).toLinearMap) = _
    simp only [b, OrthonormalBasis.tensorProduct_apply']
    rw [← tensorMap_rankOne_local, tensorIdKraus_inducedMap_tensor,
      tensorIdKraus_inducedMap_tensor]
    let localUnit := (InnerProductSpace.rankOne Complex
      (bH index.1.1) (bH index.2.1)).toLinearMap
    let restUnit := (InnerProductSpace.rankOne Complex
      (bR index.1.2) (bR index.2.2)).toLinearMap
    have hneg : TensorProduct.map (-F.inducedMap localUnit) restUnit =
        -TensorProduct.map (F.inducedMap localUnit) restUnit := by
      calc
        TensorProduct.map (-F.inducedMap localUnit) restUnit =
            TensorProduct.map
              ((-1 : Complex) • F.inducedMap localUnit) restUnit := by
          rw [neg_one_smul]
        _ = (-1 : Complex) •
            TensorProduct.map (F.inducedMap localUnit) restUnit :=
          TensorProduct.map_smul_left _ _ _
        _ = -TensorProduct.map (F.inducedMap localUnit) restUnit := by
          exact neg_one_smul (R := Complex)
            (TensorProduct.map (F.inducedMap localUnit) restUnit :
              Operator (CompositeSystem H R))
    calc
      TensorProduct.map (E.inducedMap localUnit) restUnit -
          TensorProduct.map (F.inducedMap localUnit) restUnit =
          TensorProduct.map (E.inducedMap localUnit) restUnit +
            TensorProduct.map (-F.inducedMap localUnit) restUnit := by
        rw [sub_eq_add_neg]
        exact congrArg
          (fun X => TensorProduct.map (E.inducedMap localUnit) restUnit + X)
          hneg.symm
      _ = TensorProduct.map
          (E.inducedMap localUnit + -F.inducedMap localUnit) restUnit :=
        (TensorProduct.map_add_left _ _ _).symm
      _ = TensorProduct.map
          (E.inducedMap localUnit - F.inducedMap localUnit) restUnit := by
        rw [sub_eq_add_neg]
  have hunitBound (index : (beta × gamma) × (beta × gamma)) :
      traceNorm
          (D ((InnerProductSpace.rankOne Complex
            (b index.1) (b index.2)).toLinearMap)) <=
        (Fintype.card (beta × beta) : Real) * epsilon := by
    rw [hunit index]
    exact (traceNorm_tensor_basisUnit_le_card bH bR
      (E.inducedMap
          (InnerProductSpace.rankOne Complex
            (bH index.1.1) (bH index.2.1)).toLinearMap -
        F.inducedMap
          (InnerProductSpace.rankOne Complex
            (bH index.1.1) (bH index.2.1)).toLinearMap)
      index.1.2 index.2.2).trans
        (mul_le_mul_of_nonneg_left
          (hlocal index.1.1 index.2.1) (by positivity))
  change traceNorm (D A) <= _
  rw [hmap]
  calc
    traceNorm (∑ index : (beta × gamma) × (beta × gamma),
        D (summand index)) <=
        ∑ index : (beta × gamma) × (beta × gamma),
          traceNorm (D (summand index)) := by
      simpa using traceNorm_sum_le
        (Finset.univ : Finset ((beta × gamma) × (beta × gamma)))
        (fun index => D (summand index))
    _ <= ∑ _index : (beta × gamma) × (beta × gamma),
        traceNorm A * ((Fintype.card (beta × beta) : Real) * epsilon) := by
      apply Finset.sum_le_sum
      intro index _
      rw [show summand index =
          b.repr (A (b index.2)) index.1 •
            (InnerProductSpace.rankOne Complex
              (b index.1) (b index.2)).toLinearMap by rfl,
        map_smul, traceNorm_smul]
      exact mul_le_mul
        (matrixCoefficient_norm_le_traceNorm b A index.1 index.2)
        (hunitBound index) (traceNorm_nonneg _)
        (traceNorm_nonneg A)
    _ = (Fintype.card ((beta × gamma) × (beta × gamma)) : Real) *
        ((Fintype.card (beta × beta) : Real) * epsilon * traceNorm A) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

private theorem tensorIdKraus_difference_density_le
    {kappa lambda H R : Type}
    [Fintype kappa] [Fintype lambda]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
    [Nontrivial (CompositeSystem H R)]
    {beta gamma : Type} [Fintype beta] [Fintype gamma]
    (bH : OrthonormalBasis beta Complex H)
    (bR : OrthonormalBasis gamma Complex R)
    (E : FiniteKrausFamily kappa H H)
    (F : FiniteKrausFamily lambda H H)
    (epsilon : Real)
    (hlocal : forall i j : beta,
      traceNorm
          (E.inducedMap
              (InnerProductSpace.rankOne Complex (bH i) (bH j)).toLinearMap -
            F.inducedMap
              (InnerProductSpace.rankOne Complex (bH i) (bH j)).toLinearMap) <=
        epsilon)
    (rho : DensityOperator (CompositeSystem H R)) :
    traceNorm
        ((tensorIdKraus E R).inducedMap rho.toOperator -
          (tensorIdKraus F R).inducedMap rho.toOperator) <=
      (Fintype.card ((beta × gamma) × (beta × gamma)) : Real) *
        ((Fintype.card (beta × beta) : Real) * epsilon) := by
  simpa [rho.traceNorm_eq_one] using
    tensorIdKraus_difference_le bH bR E F epsilon hlocal rho.toOperator

/- The factorization is unitary, so the preceding tensor estimate applies to
every register density operator, including inputs entangled across the chosen
wire and its complement. -/
private theorem selectedWireKraus_difference_density_le
    {kappa lambda Wire gamma : Type}
    [Fintype kappa] [Fintype lambda]
    [Fintype Wire] [DecidableEq Wire] [Fintype gamma]
    (wire : Wire)
    (bR : OrthonormalBasis gamma Complex
      (QubitRegister (OtherWires wire)))
    (E : FiniteKrausFamily kappa QubitSpace QubitSpace)
    (F : FiniteKrausFamily lambda QubitSpace QubitSpace)
    (hE : E.Complete) (hF : F.Complete)
    (epsilon : Real)
    (hlocal : forall i j : Fin 2,
      traceNorm
          (E.inducedMap
              (InnerProductSpace.rankOne Complex
                (EuclideanSpace.basisFun (Fin 2) Complex i)
                (EuclideanSpace.basisFun (Fin 2) Complex j)).toLinearMap -
            F.inducedMap
              (InnerProductSpace.rankOne Complex
                (EuclideanSpace.basisFun (Fin 2) Complex i)
                (EuclideanSpace.basisFun (Fin 2) Complex j)).toLinearMap) <=
        epsilon)
    (rho : DensityOperator (QubitRegister Wire)) :
    traceNorm
        ((selectedWireKraus wire E).inducedMap rho.toOperator -
          (selectedWireKraus wire F).inducedMap rho.toOperator) <=
      (Fintype.card
          (((Fin 2) × gamma) × ((Fin 2) × gamma)) : Real) *
        ((Fintype.card ((Fin 2) × (Fin 2)) : Real) * epsilon) := by
  let U := selectedWireFactorization wire
  let rhoFactored : DensityOperator
      (CompositeSystem QubitSpace (QubitRegister (OtherWires wire))) :=
    U.conjDensity rho
  let Phi := QuantumChannel.unitaryConj U.symm
  have hposE : LinearMap.IsPositive
      ((tensorIdKraus E (QubitRegister (OtherWires wire))).inducedMap
        rhoFactored.toOperator) := by
    exact ((tensorIdKraus E
      (QubitRegister (OtherWires wire))).toQuantumChannel
        (tensorIdKraus_complete hE)).map_positive rhoFactored.positive
  have hposF : LinearMap.IsPositive
      ((tensorIdKraus F (QubitRegister (OtherWires wire))).inducedMap
        rhoFactored.toOperator) := by
    exact ((tensorIdKraus F
      (QubitRegister (OtherWires wire))).toQuantumChannel
        (tensorIdKraus_complete hF)).map_positive rhoFactored.positive
  have hsym :
      ((tensorIdKraus E (QubitRegister (OtherWires wire))).inducedMap
          rhoFactored.toOperator -
        (tensorIdKraus F (QubitRegister (OtherWires wire))).inducedMap
          rhoFactored.toOperator).IsSymmetric :=
    hposE.isSymmetric.sub hposF.isSymmetric
  rw [selectedWireKraus_inducedMap_apply,
    selectedWireKraus_inducedMap_apply]
  change traceNorm
      (Phi
          ((tensorIdKraus E (QubitRegister (OtherWires wire))).inducedMap
            rhoFactored.toOperator) -
        Phi
          ((tensorIdKraus F (QubitRegister (OtherWires wire))).inducedMap
            rhoFactored.toOperator)) <= _
  rw [← map_sub]
  calc
    traceNorm
        (Phi
          ((tensorIdKraus E (QubitRegister (OtherWires wire))).inducedMap
              rhoFactored.toOperator -
            (tensorIdKraus F (QubitRegister (OtherWires wire))).inducedMap
              rhoFactored.toOperator)) <=
        traceNorm
          ((tensorIdKraus E (QubitRegister (OtherWires wire))).inducedMap
              rhoFactored.toOperator -
            (tensorIdKraus F (QubitRegister (OtherWires wire))).inducedMap
              rhoFactored.toOperator) :=
      Phi.traceNorm_apply_le_of_isSymmetric _ hsym
    _ <= _ := tensorIdKraus_difference_density_le
      (EuclideanSpace.basisFun (Fin 2) Complex) bR E F epsilon hlocal rhoFactored

private theorem rawMass_eq_aggregate_trace_local (leaves : List BK05RawLeaf) :
    rawMass leaves =
      (LinearMap.trace Complex QubitSpace (rawAggregate leaves)).re := by
  induction leaves with
  | nil => simp [rawMass, rawAggregate]
  | cons leaf leaves ih =>
      change (LinearMap.trace Complex QubitSpace leaf.raw).re + rawMass leaves = _
      rw [ih]
      change (LinearMap.trace Complex QubitSpace leaf.raw).re +
          (LinearMap.trace Complex QubitSpace (rawAggregate leaves)).re =
        (LinearMap.trace Complex QubitSpace
          (leaf.raw + rawAggregate leaves)).re
      rw [map_add]
      rfl

private theorem rawMassOfKind_eq_aggregate_trace_local
    (kind : BK05RawLeafKind) (leaves : List BK05RawLeaf) :
    rawMassOfKind kind leaves =
      (LinearMap.trace Complex QubitSpace
        (rawAggregateOfKind kind leaves)).re := by
  exact rawMass_eq_aggregate_trace_local
    (leaves.filter fun leaf => leaf.kind == kind)

private theorem hRetryPhaseExhaustedLinear_trace_le_tail
    (blocks : Nat) (sign : BK05WordPolarity)
    (data : Operator QubitSpace) (hdata : LinearMap.IsPositive data) :
    (LinearMap.trace Complex QubitSpace
      (hRetryPhaseExhaustedLinear hMagicState (hPhaseTarget sign)
        (8 * blocks) 0 data)).re <=
      (255 / 256 : Real) ^ blocks *
        (LinearMap.trace Complex QubitSpace data).re := by
  rw [hRetryPhaseExhaustedLinear_apply hMagicState (hPhaseTarget sign)
    (8 * blocks) 0 0 [] data]
  rw [← rawMassOfKind_eq_aggregate_trace_local]
  rw [hRetry_phaseExhausted_mass_eq_coeff (hPhaseTarget sign)
    (8 * blocks) 0 0 [] data hdata]
  exact mul_le_mul_of_nonneg_right
    (hExhaustionCoeff_blocks_le (hPhaseTarget sign) 0 blocks)
    (Complex.nonneg_iff.mp hdata.trace_nonneg).1

private theorem tRetryPhaseExhaustedLinear_trace_le_tail
    (pairAttempts blocks : Nat) (sign : BK05WordPolarity)
    (data : Operator QubitSpace) (hdata : LinearMap.IsPositive data) :
    (LinearMap.trace Complex QubitSpace
      (tRetryPhaseExhaustedLinear tMagicState pairAttempts (tPhaseTarget sign)
        (12 * blocks) 0 data)).re <=
      (4095 / 4096 : Real) ^ blocks *
        (LinearMap.trace Complex QubitSpace data).re := by
  rw [tRetryPhaseExhaustedLinear_apply tMagicState pairAttempts
    (tPhaseTarget sign) (12 * blocks) 0 0 [] data]
  rw [← rawMassOfKind_eq_aggregate_trace_local]
  rw [tRetry_phaseExhausted_mass_eq_coeff pairAttempts (tPhaseTarget sign)
    (12 * blocks) 0 0 [] data hdata]
  exact mul_le_mul_of_nonneg_right
    (tPhaseExhaustionCoeff_blocks_le pairAttempts (tPhaseTarget sign) 0 blocks)
    (Complex.nonneg_iff.mp hdata.trace_nonneg).1

private theorem tRetryPairExhaustedLinear_trace_le_tail
    (pairAttempts blocks : Nat) (sign : BK05WordPolarity)
    (data : Operator QubitSpace) (hdata : LinearMap.IsPositive data) :
    (LinearMap.trace Complex QubitSpace
      (tRetryPairExhaustedLinear tMagicState pairAttempts (tPhaseTarget sign)
        (12 * blocks) 0 data)).re <=
      (12 * blocks : Real) * (1 / 3 : Real) ^ pairAttempts *
        (LinearMap.trace Complex QubitSpace data).re := by
  rw [tRetryPairExhaustedLinear_apply tMagicState pairAttempts
    (tPhaseTarget sign) (12 * blocks) 0 0 [] data]
  rw [← rawMassOfKind_eq_aggregate_trace_local]
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    tRetry_pairExhaustion_mass_le pairAttempts (tPhaseTarget sign)
      (12 * blocks) 0 0 [] data hdata

private theorem hWordPhaseStoppedLinear_trace_le
    (blocks : Nat) :
    forall (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
      (data : Operator QubitSpace),
      LinearMap.IsPositive data ->
      (LinearMap.trace Complex QubitSpace
        (hWordPhaseStoppedLinear hMagicState blocks letters data)).re <=
        (BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) letters : Real) *
          (255 / 256 : Real) ^ blocks *
          (LinearMap.trace Complex QubitSpace data).re := by
  intro letters
  induction letters with
  | nil =>
      intro data hdata
      simp [hWordPhaseStoppedLinear, BK05SignedPhaseLetter.resourceCount]
  | cons head tail ih =>
      intro data hdata
      have hlivePositive :=
        hWordLiveLinear_positive hMagicState blocks tail data hdata
      have hliveTrace := hWord_live_trace_le hMagicState blocks tail data hdata
      have htailNonneg : 0 <= (255 / 256 : Real) ^ blocks :=
        pow_nonneg (by norm_num) _
      have phaseCase (sign : BK05WordPolarity) :
          (LinearMap.trace Complex QubitSpace
            (hRetryPhaseExhaustedLinear hMagicState (hPhaseTarget sign)
              (8 * blocks) 0
              (hWordLiveLinear hMagicState blocks tail data))).re +
            (LinearMap.trace Complex QubitSpace
              (hWordPhaseStoppedLinear hMagicState blocks tail data)).re <=
          ((1 + BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) tail : Nat) : Real) *
            (255 / 256 : Real) ^ blocks *
            (LinearMap.trace Complex QubitSpace data).re := by
        have hsite := hRetryPhaseExhaustedLinear_trace_le_tail blocks sign
          (hWordLiveLinear hMagicState blocks tail data) hlivePositive
        have hsite' :
            (LinearMap.trace Complex QubitSpace
              (hRetryPhaseExhaustedLinear hMagicState (hPhaseTarget sign)
                (8 * blocks) 0
                (hWordLiveLinear hMagicState blocks tail data))).re <=
              (255 / 256 : Real) ^ blocks *
                (LinearMap.trace Complex QubitSpace data).re :=
          hsite.trans (mul_le_mul_of_nonneg_left hliveTrace htailNonneg)
        calc
          _ <= (255 / 256 : Real) ^ blocks *
                (LinearMap.trace Complex QubitSpace data).re +
              (BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) tail : Real) *
                (255 / 256 : Real) ^ blocks *
                (LinearMap.trace Complex QubitSpace data).re :=
            add_le_add hsite' (ih data hdata)
          _ = _ := by push_cast; ring
      cases head with
      | positive atom =>
          cases atom with
          | h =>
              simpa [hWordPhaseStoppedLinear,
                BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using ih data hdata
          | k =>
              simpa [hWordPhaseStoppedLinear,
                BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using ih data hdata
          | phase =>
              simpa only [hWordPhaseStoppedLinear, LinearMap.add_apply,
                LinearMap.comp_apply, map_add, Complex.add_re,
                BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using phaseCase .normal
      | negative atom =>
          cases atom with
          | h =>
              simpa [hWordPhaseStoppedLinear,
                BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using ih data hdata
          | k =>
              simpa [hWordPhaseStoppedLinear,
                BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using ih data hdata
          | phase =>
              simpa only [hWordPhaseStoppedLinear, LinearMap.add_apply,
                LinearMap.comp_apply, map_add, Complex.add_re,
                BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using phaseCase .inverse

private theorem tWordPhaseStoppedLinear_trace_le
    (pairAttempts blocks : Nat) :
    forall (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
      (data : Operator QubitSpace),
      LinearMap.IsPositive data ->
      (LinearMap.trace Complex QubitSpace
        (tWordPhaseStoppedLinear tMagicState pairAttempts blocks letters data)).re <=
        (BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) letters : Real) *
          (4095 / 4096 : Real) ^ blocks *
          (LinearMap.trace Complex QubitSpace data).re := by
  intro letters
  induction letters with
  | nil =>
      intro data hdata
      simp [tWordPhaseStoppedLinear, BK05SignedPhaseLetter.resourceCount]
  | cons head tail ih =>
      intro data hdata
      have hlivePositive :=
        tWordLiveLinear_positive tMagicState pairAttempts blocks tail data hdata
      have hliveTrace :=
        tWord_live_trace_le tMagicState pairAttempts blocks tail data hdata
      have htailNonneg : 0 <= (4095 / 4096 : Real) ^ blocks :=
        pow_nonneg (by norm_num) _
      have phaseCase (sign : BK05WordPolarity) :
          (LinearMap.trace Complex QubitSpace
            (tRetryPhaseExhaustedLinear tMagicState pairAttempts (tPhaseTarget sign)
              (12 * blocks) 0
              (tWordLiveLinear tMagicState pairAttempts blocks tail data))).re +
            (LinearMap.trace Complex QubitSpace
              (tWordPhaseStoppedLinear tMagicState pairAttempts blocks tail data)).re <=
          ((1 + BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) tail : Nat) : Real) *
            (4095 / 4096 : Real) ^ blocks *
            (LinearMap.trace Complex QubitSpace data).re := by
        have hsite := tRetryPhaseExhaustedLinear_trace_le_tail pairAttempts blocks sign
          (tWordLiveLinear tMagicState pairAttempts blocks tail data) hlivePositive
        have hsite' := hsite.trans
          (mul_le_mul_of_nonneg_left hliveTrace htailNonneg)
        calc
          _ <= (4095 / 4096 : Real) ^ blocks *
                (LinearMap.trace Complex QubitSpace data).re +
              (BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) tail : Real) *
                (4095 / 4096 : Real) ^ blocks *
                (LinearMap.trace Complex QubitSpace data).re :=
            add_le_add hsite' (ih data hdata)
          _ = _ := by push_cast; ring
      cases head with
      | positive atom =>
          cases atom with
          | h => simpa [tWordPhaseStoppedLinear,
              BK05SignedPhaseLetter.resourceCount,
              BK05SignedPhaseLetter.phaseCost] using ih data hdata
          | k => simpa [tWordPhaseStoppedLinear,
              BK05SignedPhaseLetter.resourceCount,
              BK05SignedPhaseLetter.phaseCost] using ih data hdata
          | phase =>
              simpa only [tWordPhaseStoppedLinear, LinearMap.add_apply,
                LinearMap.comp_apply, map_add, Complex.add_re,
                BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using phaseCase .normal
      | negative atom =>
          cases atom with
          | h => simpa [tWordPhaseStoppedLinear,
              BK05SignedPhaseLetter.resourceCount,
              BK05SignedPhaseLetter.phaseCost] using ih data hdata
          | k => simpa [tWordPhaseStoppedLinear,
              BK05SignedPhaseLetter.resourceCount,
              BK05SignedPhaseLetter.phaseCost] using ih data hdata
          | phase =>
              simpa only [tWordPhaseStoppedLinear, LinearMap.add_apply,
                LinearMap.comp_apply, map_add, Complex.add_re,
                BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using phaseCase .inverse

private theorem tWordPairStoppedLinear_trace_le
    (pairAttempts blocks : Nat) :
    forall (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
      (data : Operator QubitSpace),
      LinearMap.IsPositive data ->
      (LinearMap.trace Complex QubitSpace
        (tWordPairStoppedLinear tMagicState pairAttempts blocks letters data)).re <=
        (BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) letters : Real) *
          ((12 * blocks : Real) * (1 / 3 : Real) ^ pairAttempts) *
          (LinearMap.trace Complex QubitSpace data).re := by
  intro letters
  induction letters with
  | nil =>
      intro data hdata
      simp [tWordPairStoppedLinear, BK05SignedPhaseLetter.resourceCount]
  | cons head tail ih =>
      intro data hdata
      have hlivePositive :=
        tWordLiveLinear_positive tMagicState pairAttempts blocks tail data hdata
      have hliveTrace :=
        tWord_live_trace_le tMagicState pairAttempts blocks tail data hdata
      have htailNonneg :
          0 <= (12 * blocks : Real) * (1 / 3 : Real) ^ pairAttempts :=
        mul_nonneg (by positivity) (pow_nonneg (by norm_num) _)
      have phaseCase (sign : BK05WordPolarity) :
          (LinearMap.trace Complex QubitSpace
            (tRetryPairExhaustedLinear tMagicState pairAttempts (tPhaseTarget sign)
              (12 * blocks) 0
              (tWordLiveLinear tMagicState pairAttempts blocks tail data))).re +
            (LinearMap.trace Complex QubitSpace
              (tWordPairStoppedLinear tMagicState pairAttempts blocks tail data)).re <=
          ((1 + BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) tail : Nat) : Real) *
            ((12 * blocks : Real) * (1 / 3 : Real) ^ pairAttempts) *
            (LinearMap.trace Complex QubitSpace data).re := by
        have hsite := tRetryPairExhaustedLinear_trace_le_tail pairAttempts blocks sign
          (tWordLiveLinear tMagicState pairAttempts blocks tail data) hlivePositive
        have hsite' := hsite.trans
          (mul_le_mul_of_nonneg_left hliveTrace htailNonneg)
        calc
          _ <= ((12 * blocks : Real) * (1 / 3 : Real) ^ pairAttempts) *
                (LinearMap.trace Complex QubitSpace data).re +
              (BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) tail : Real) *
                ((12 * blocks : Real) * (1 / 3 : Real) ^ pairAttempts) *
                (LinearMap.trace Complex QubitSpace data).re :=
            add_le_add hsite' (ih data hdata)
          _ = _ := by push_cast; ring
      cases head with
      | positive atom =>
          cases atom with
          | h => simpa [tWordPairStoppedLinear,
              BK05SignedPhaseLetter.resourceCount,
              BK05SignedPhaseLetter.phaseCost] using ih data hdata
          | k => simpa [tWordPairStoppedLinear,
              BK05SignedPhaseLetter.resourceCount,
              BK05SignedPhaseLetter.phaseCost] using ih data hdata
          | phase =>
              simpa only [tWordPairStoppedLinear, LinearMap.add_apply,
                LinearMap.comp_apply, map_add, Complex.add_re,
                BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using phaseCase .normal
      | negative atom =>
          cases atom with
          | h => simpa [tWordPairStoppedLinear,
              BK05SignedPhaseLetter.resourceCount,
              BK05SignedPhaseLetter.phaseCost] using ih data hdata
          | k => simpa [tWordPairStoppedLinear,
              BK05SignedPhaseLetter.resourceCount,
              BK05SignedPhaseLetter.phaseCost] using ih data hdata
          | phase =>
              simpa only [tWordPairStoppedLinear, LinearMap.add_apply,
                LinearMap.comp_apply, map_add, Complex.add_re,
                BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using phaseCase .inverse

/- A retained stopping branch is not postselection: its positive trace is part
of the physical output.  When the complementary live branch is a real multiple
of a trace-one ideal state, the complete output is within twice the retained
stopping mass of that ideal state. -/
private theorem retainedStopping_traceNorm_le_twice
    (live stopped ideal : Operator QubitSpace) (probability delta : Real)
    (hlive : live = (probability : Complex) • ideal)
    (hstopped : LinearMap.IsPositive stopped)
    (hideal : LinearMap.IsPositive ideal)
    (htotalTrace :
      LinearMap.trace Complex QubitSpace live +
          LinearMap.trace Complex QubitSpace stopped = 1)
    (hidealTrace : LinearMap.trace Complex QubitSpace ideal = 1)
    (hstoppedTrace :
      (LinearMap.trace Complex QubitSpace stopped).re ≤ delta) :
    traceNorm (live + stopped - ideal) ≤ 2 * delta := by
  have hliveTrace :
      (LinearMap.trace Complex QubitSpace live).re = probability := by
    rw [hlive, map_smul, hidealTrace]
    norm_num
  have hstoppedTraceEq :
      (LinearMap.trace Complex QubitSpace stopped).re = 1 - probability := by
    have hreal := congrArg Complex.re htotalTrace
    simp only [Complex.add_re, Complex.one_re] at hreal
    rw [hliveTrace] at hreal
    linarith
  have hcomplement : 0 ≤ 1 - probability := by
    rw [← hstoppedTraceEq]
    exact (Complex.nonneg_iff.mp hstopped.trace_nonneg).1
  have hstoppedNorm : traceNorm stopped = 1 - probability := by
    rw [traceNorm_eq_re_trace_of_positive stopped hstopped, hstoppedTraceEq]
  have hidealNorm : traceNorm ideal = 1 := by
    rw [traceNorm_eq_re_trace_of_positive ideal hideal, hidealTrace]
    norm_num
  have hscaledIdealNorm :
      traceNorm (((1 - probability : Real) : Complex) • ideal) =
        1 - probability := by
    rw [traceNorm_smul, hidealNorm, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hcomplement]
  have hrewrite :
      live + stopped - ideal =
        stopped - (((1 - probability : Real) : Complex) • ideal) := by
    rw [hlive]
    module
  rw [hrewrite]
  calc
    traceNorm (stopped - (((1 - probability : Real) : Complex) • ideal)) ≤
        traceNorm stopped +
          traceNorm (((1 - probability : Real) : Complex) • ideal) := by
      simpa [sub_eq_add_neg, traceNorm_neg] using
        traceNorm_add_le stopped
          (-(((1 - probability : Real) : Complex) • ideal))
    _ = 2 * (1 - probability) := by
      rw [hstoppedNorm, hscaledIdealNorm]
      ring
    _ ≤ 2 * delta := by
      nlinarith [hstoppedTraceEq.symm.trans_le hstoppedTrace]

private theorem hMagicWord_retained_traceNorm_le
    (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (rho : DensityOperator QubitSpace) :
    traceNorm
        (hSignedWordTotalLinear hMagicState blocks letters LinearMap.id
            rho.toOperator -
          hFixedIdealWordLinear letters rho.toOperator) ≤
      2 *
        ((BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) letters : Real) *
          (255 / 256 : Real) ^ blocks) := by
  have hlive :
      hWordLiveLinear hMagicState blocks letters rho.toOperator =
        (hWordLiveProbability blocks letters : Complex) •
          hFixedIdealWordLinear letters rho.toOperator := by
    simpa only [hWordLiveCoeff_eq_probability] using
      hWordLiveLinear_ideal_action blocks letters rho.toOperator rho.positive
  have htrace :
      LinearMap.trace Complex QubitSpace
            (hWordLiveLinear hMagicState blocks letters rho.toOperator) +
          LinearMap.trace Complex QubitSpace
            (hWordPhaseStoppedLinear hMagicState blocks letters rho.toOperator) = 1 := by
    simpa only [rho.trace_one] using
      hWord_component_trace hMagicState blocks letters rho.toOperator
  have hidealTrace :
      LinearMap.trace Complex QubitSpace
          (hFixedIdealWordLinear letters rho.toOperator) = 1 := by
    rw [hFixedIdealWordLinear_trace, rho.trace_one]
  have hstoppedTrace :
      (LinearMap.trace Complex QubitSpace
        (hWordPhaseStoppedLinear hMagicState blocks letters rho.toOperator)).re ≤
        (BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) letters : Real) *
          (255 / 256 : Real) ^ blocks := by
    simpa only [rho.trace_one, Complex.one_re, mul_one] using
      hWordPhaseStoppedLinear_trace_le blocks letters rho.toOperator rho.positive
  have hbound := retainedStopping_traceNorm_le_twice
    (hWordLiveLinear hMagicState blocks letters rho.toOperator)
    (hWordPhaseStoppedLinear hMagicState blocks letters rho.toOperator)
    (hFixedIdealWordLinear letters rho.toOperator)
    (hWordLiveProbability blocks letters)
    ((BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) letters : Real) *
      (255 / 256 : Real) ^ blocks)
    hlive
    (hWordPhaseStoppedLinear_positive hMagicState blocks letters
      rho.toOperator rho.positive)
    (hFixedIdealWordLinear_positive letters rho.toOperator rho.positive)
    htrace hidealTrace hstoppedTrace
  rw [hWord_components_total] at hbound
  exact hbound

private theorem tMagicWord_retained_traceNorm_le
    (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
    (rho : DensityOperator QubitSpace) :
    traceNorm
        (tWordTotalLinear tMagicState pairAttempts blocks letters rho.toOperator -
          tFixedIdealWordLinear letters rho.toOperator) ≤
      2 *
        ((BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) letters : Real) *
            (4095 / 4096 : Real) ^ blocks +
          (BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) letters : Real) *
            ((12 * blocks : Real) * (1 / 3 : Real) ^ pairAttempts)) := by
  let stopped :=
    tWordPhaseStoppedLinear tMagicState pairAttempts blocks letters rho.toOperator +
      tWordPairStoppedLinear tMagicState pairAttempts blocks letters rho.toOperator
  have hlive :
      tWordLiveLinear tMagicState pairAttempts blocks letters rho.toOperator =
        (tWordLiveProbability pairAttempts blocks letters : Complex) •
          tFixedIdealWordLinear letters rho.toOperator := by
    simpa only [tWordLiveCoeff_eq_probability] using
      tWordLiveLinear_ideal_action pairAttempts blocks letters
        rho.toOperator rho.positive
  have htrace :
      LinearMap.trace Complex QubitSpace
            (tWordLiveLinear tMagicState pairAttempts blocks letters rho.toOperator) +
          LinearMap.trace Complex QubitSpace stopped = 1 := by
    dsimp only [stopped]
    rw [map_add]
    simpa only [rho.trace_one, add_assoc] using
      tWordComponent_trace tMagicState pairAttempts blocks letters rho.toOperator
  have hidealTrace :
      LinearMap.trace Complex QubitSpace
          (tFixedIdealWordLinear letters rho.toOperator) = 1 := by
    rw [tFixedIdealWordLinear_trace, rho.trace_one]
  have hphase := tWordPhaseStoppedLinear_trace_le pairAttempts blocks letters
    rho.toOperator rho.positive
  have hpair := tWordPairStoppedLinear_trace_le pairAttempts blocks letters
    rho.toOperator rho.positive
  have hstoppedTrace :
      (LinearMap.trace Complex QubitSpace stopped).re ≤
        (BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) letters : Real) *
            (4095 / 4096 : Real) ^ blocks +
          (BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) letters : Real) *
            ((12 * blocks : Real) * (1 / 3 : Real) ^ pairAttempts) := by
    dsimp only [stopped]
    rw [map_add, Complex.add_re]
    simpa only [rho.trace_one, Complex.one_re, mul_one] using add_le_add hphase hpair
  have hbound := retainedStopping_traceNorm_le_twice
    (tWordLiveLinear tMagicState pairAttempts blocks letters rho.toOperator)
    stopped
    (tFixedIdealWordLinear letters rho.toOperator)
    (tWordLiveProbability pairAttempts blocks letters)
    ((BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) letters : Real) *
        (4095 / 4096 : Real) ^ blocks +
      (BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) letters : Real) *
        ((12 * blocks : Real) * (1 / 3 : Real) ^ pairAttempts))
    hlive
    ((tWordPhaseStoppedLinear_positive tMagicState pairAttempts blocks letters
      rho.toOperator rho.positive).add
      (tWordPairStoppedLinear_positive tMagicState pairAttempts blocks letters
        rho.toOperator rho.positive))
    (tFixedIdealWordLinear_positive letters rho.toOperator rho.positive)
    htrace hidealTrace hstoppedTrace
  change traceNorm
      ((tWordLiveLinear tMagicState pairAttempts blocks letters +
          tWordPhaseStoppedLinear tMagicState pairAttempts blocks letters +
          tWordPairStoppedLinear tMagicState pairAttempts blocks letters)
          rho.toOperator -
        tFixedIdealWordLinear letters rho.toOperator) ≤ _
  simpa only [tWordTotalLinear, LinearMap.add_apply, stopped, add_assoc] using hbound

private noncomputable def hWordErrorBudget
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) : Real :=
  ((8 * blocks * BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) letters : Nat) : Real) *
      traceNorm (h.toOperator - hMagicState.toOperator) +
    2 * ((BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) letters : Real) *
      (255 / 256 : Real) ^ blocks)

private noncomputable def tWordErrorBudget
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) : Real :=
  ((2 * pairAttempts * 12 * blocks *
      BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) letters : Nat) : Real) *
      traceNorm (t.toOperator - tMagicState.toOperator) +
    2 *
      ((BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) letters : Real) *
          (4095 / 4096 : Real) ^ blocks +
        (BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) letters : Real) *
          ((12 * blocks : Real) * (1 / 3 : Real) ^ pairAttempts))

private theorem hWordErrorBudget_nonneg
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) :
    0 ≤ hWordErrorBudget h blocks letters := by
  unfold hWordErrorBudget
  apply add_nonneg
  · exact mul_nonneg (by positivity) (traceNorm_nonneg _)
  · exact mul_nonneg (by norm_num)
      (mul_nonneg (by positivity) (pow_nonneg (by norm_num) _))

private theorem tWordErrorBudget_nonneg
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) :
    0 ≤ tWordErrorBudget t pairAttempts blocks letters := by
  unfold tWordErrorBudget
  apply add_nonneg
  · exact mul_nonneg (by positivity) (traceNorm_nonneg _)
  · exact mul_nonneg (by norm_num) (add_nonneg
      (mul_nonneg (by positivity) (pow_nonneg (by norm_num) _))
      (mul_nonneg (by positivity)
        (mul_nonneg (by positivity) (pow_nonneg (by norm_num) _))))

private theorem hWord_actual_aggregate_traceNorm_le
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (rho : DensityOperator QubitSpace) :
    traceNorm
        (hSignedWordTotalLinear h blocks letters LinearMap.id rho.toOperator -
          hFixedIdealWordLinear letters rho.toOperator) ≤
      hWordErrorBudget h blocks letters := by
  have hstable := hSignedWordTotalLinear_stable_id h blocks letters
    rho.toOperator rho.positive
  simp only [rho.trace_one, Complex.one_re, mul_one] at hstable
  have hideal := hMagicWord_retained_traceNorm_le blocks letters rho
  have hrewrite :
      hSignedWordTotalLinear h blocks letters LinearMap.id rho.toOperator -
          hFixedIdealWordLinear letters rho.toOperator =
        (hSignedWordTotalLinear h blocks letters LinearMap.id rho.toOperator -
          hSignedWordTotalLinear hMagicState blocks letters LinearMap.id rho.toOperator) +
        (hSignedWordTotalLinear hMagicState blocks letters LinearMap.id rho.toOperator -
          hFixedIdealWordLinear letters rho.toOperator) := by
    module
  rw [hrewrite]
  exact (traceNorm_add_le _ _).trans
    (by simpa [hWordErrorBudget] using add_le_add hstable hideal)

private theorem tWord_actual_aggregate_traceNorm_le
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
    (rho : DensityOperator QubitSpace) :
    traceNorm
        (tWordTotalLinear t pairAttempts blocks letters rho.toOperator -
          tFixedIdealWordLinear letters rho.toOperator) ≤
      tWordErrorBudget t pairAttempts blocks letters := by
  have hstable := tSignedWordTotalLinear_stable_id t pairAttempts blocks letters
    rho.toOperator rho.positive
  simp only [rho.trace_one, Complex.one_re, mul_one] at hstable
  have hideal := tMagicWord_retained_traceNorm_le pairAttempts blocks letters rho
  have hrewrite :
      tWordTotalLinear t pairAttempts blocks letters rho.toOperator -
          tFixedIdealWordLinear letters rho.toOperator =
        (tWordTotalLinear t pairAttempts blocks letters rho.toOperator -
          tWordTotalLinear tMagicState pairAttempts blocks letters rho.toOperator) +
        (tWordTotalLinear tMagicState pairAttempts blocks letters rho.toOperator -
          tFixedIdealWordLinear letters rho.toOperator) := by
    module
  rw [hrewrite]
  exact (traceNorm_add_le _ _).trans
    (by simpa [tWordErrorBudget] using add_le_add hstable hideal)

private theorem linearMap_rankOne_self_le_of_density
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (D : Operator H →ₗ[Complex] Operator K) (epsilon : Real)
    (hepsilon : 0 ≤ epsilon)
    (hbound : ∀ rho : DensityOperator H,
      traceNorm (D rho.toOperator) ≤ epsilon)
    (z : H) :
    traceNorm (D (InnerProductSpace.rankOne Complex z z).toLinearMap) ≤
      epsilon * ‖z‖ ^ 2 := by
  by_cases hz : z = 0
  · subst z
    have hrank :
        (InnerProductSpace.rankOne Complex (0 : H) 0).toLinearMap =
          (0 : Operator H) := by
      ext x
      change inner Complex (0 : H) x • (0 : H) = 0
      rw [inner_zero_left, smul_zero]
    rw [hrank, map_zero]
    have htrace : traceNorm (0 : Operator K) = 0 :=
      (traceNorm_eq_zero_iff (0 : Operator K)).2 rfl
    rw [htrace, norm_zero, zero_pow (by norm_num : (2 : Nat) ≠ 0), mul_zero]
  · let rho : DensityOperator H := DensityOperator.pureOfNonzero z hz
    have hinner : inner Complex z z ≠ 0 := inner_self_ne_zero.mpr hz
    have hrank :
        (InnerProductSpace.rankOne Complex z z).toLinearMap =
          inner Complex z z • rho.toOperator := by
      change (InnerProductSpace.rankOne Complex z z).toLinearMap =
        inner Complex z z •
          ((inner Complex z z)⁻¹ •
            (InnerProductSpace.rankOne Complex z z).toLinearMap)
      rw [smul_smul, mul_inv_cancel₀ hinner, one_smul]
    rw [hrank, map_smul, traceNorm_smul]
    calc
      ‖inner Complex z z‖ * traceNorm (D rho.toOperator) ≤
          ‖inner Complex z z‖ * epsilon :=
        mul_le_mul_of_nonneg_left (hbound rho) (norm_nonneg _)
      _ = epsilon * ‖z‖ ^ 2 := by
        rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm]
        ring

private theorem hTerminalKraus_matrixUnit_le
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (i j : Fin 2) :
    traceNorm
        ((hTerminalKraus h blocks letters).inducedMap
            (InnerProductSpace.rankOne Complex
              (EuclideanSpace.basisFun (Fin 2) Complex i)
              (EuclideanSpace.basisFun (Fin 2) Complex j)).toLinearMap -
          (hIdealWordKraus letters).inducedMap
            (InnerProductSpace.rankOne Complex
              (EuclideanSpace.basisFun (Fin 2) Complex i)
              (EuclideanSpace.basisFun (Fin 2) Complex j)).toLinearMap) ≤
      16 * hWordErrorBudget h blocks letters := by
  let D : Operator QubitSpace →ₗ[Complex] Operator QubitSpace :=
    (hTerminalKraus h blocks letters).inducedMap -
      (hIdealWordKraus letters).inducedMap
  have hdensity : ∀ rho : DensityOperator QubitSpace,
      traceNorm (D rho.toOperator) ≤ hWordErrorBudget h blocks letters := by
    intro rho
    change traceNorm
        ((hTerminalKraus h blocks letters).inducedMap rho.toOperator -
          (hIdealWordKraus letters).inducedMap rho.toOperator) ≤ _
    rw [LinearMap.congr_fun (hTerminalKraus_inducedMap_eq h blocks letters),
      LinearMap.congr_fun (hIdealWordKraus_inducedMap_eq letters)]
    exact hWord_actual_aggregate_traceNorm_le h blocks letters rho
  change traceNorm
      (D (InnerProductSpace.rankOne Complex
        (EuclideanSpace.basisFun (Fin 2) Complex i)
        (EuclideanSpace.basisFun (Fin 2) Complex j)).toLinearMap) ≤ _
  exact linearMap_rankOne_le_sixteen D (hWordErrorBudget h blocks letters)
    (hWordErrorBudget_nonneg h blocks letters)
    (linearMap_rankOne_self_le_of_density D (hWordErrorBudget h blocks letters)
      (hWordErrorBudget_nonneg h blocks letters) hdensity)
    (EuclideanSpace.basisFun (Fin 2) Complex i)
    (EuclideanSpace.basisFun (Fin 2) Complex j)
    (by simp) (by simp)

private theorem tTerminalKraus_matrixUnit_le
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
    (i j : Fin 2) :
    traceNorm
        ((tTerminalKraus t pairAttempts blocks letters).inducedMap
            (InnerProductSpace.rankOne Complex
              (EuclideanSpace.basisFun (Fin 2) Complex i)
              (EuclideanSpace.basisFun (Fin 2) Complex j)).toLinearMap -
          (tIdealWordKraus letters).inducedMap
            (InnerProductSpace.rankOne Complex
              (EuclideanSpace.basisFun (Fin 2) Complex i)
              (EuclideanSpace.basisFun (Fin 2) Complex j)).toLinearMap) ≤
      16 * tWordErrorBudget t pairAttempts blocks letters := by
  let D : Operator QubitSpace →ₗ[Complex] Operator QubitSpace :=
    (tTerminalKraus t pairAttempts blocks letters).inducedMap -
      (tIdealWordKraus letters).inducedMap
  have hdensity : ∀ rho : DensityOperator QubitSpace,
      traceNorm (D rho.toOperator) ≤
        tWordErrorBudget t pairAttempts blocks letters := by
    intro rho
    change traceNorm
        ((tTerminalKraus t pairAttempts blocks letters).inducedMap rho.toOperator -
          (tIdealWordKraus letters).inducedMap rho.toOperator) ≤ _
    rw [LinearMap.congr_fun
        (tTerminalKraus_inducedMap_eq t pairAttempts blocks letters),
      LinearMap.congr_fun (tIdealWordKraus_inducedMap_eq letters)]
    exact tWord_actual_aggregate_traceNorm_le t pairAttempts blocks letters rho
  change traceNorm
      (D (InnerProductSpace.rankOne Complex
        (EuclideanSpace.basisFun (Fin 2) Complex i)
        (EuclideanSpace.basisFun (Fin 2) Complex j)).toLinearMap) ≤ _
  exact linearMap_rankOne_le_sixteen D
    (tWordErrorBudget t pairAttempts blocks letters)
    (tWordErrorBudget_nonneg t pairAttempts blocks letters)
    (linearMap_rankOne_self_le_of_density D
      (tWordErrorBudget t pairAttempts blocks letters)
      (tWordErrorBudget_nonneg t pairAttempts blocks letters) hdensity)
    (EuclideanSpace.basisFun (Fin 2) Complex i)
    (EuclideanSpace.basisFun (Fin 2) Complex j)
    (by simp) (by simp)

private theorem hSelectedWire_actual_aggregate_traceNorm_le
    {Wire gamma : Type} [Fintype Wire] [DecidableEq Wire] [Fintype gamma]
    (wire : Wire)
    (bR : OrthonormalBasis gamma Complex (QubitRegister (OtherWires wire)))
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (rho : DensityOperator (QubitRegister Wire)) :
    traceNorm
        ((selectedWireKraus wire (hTerminalKraus h blocks letters)).inducedMap
            rho.toOperator -
          (selectedWireKraus wire (hIdealWordKraus letters)).inducedMap
            rho.toOperator) ≤
      (Fintype.card ((((Fin 2) × gamma) × ((Fin 2) × gamma))) : Real) *
        ((Fintype.card ((Fin 2) × (Fin 2)) : Real) *
          (16 * hWordErrorBudget h blocks letters)) := by
  exact selectedWireKraus_difference_density_le wire bR
    (hTerminalKraus h blocks letters) (hIdealWordKraus letters)
    (hTerminalKraus_complete h blocks letters)
    (hIdealWordKraus_complete letters)
    (16 * hWordErrorBudget h blocks letters)
    (hTerminalKraus_matrixUnit_le h blocks letters) rho

private theorem tSelectedWire_actual_aggregate_traceNorm_le
    {Wire gamma : Type} [Fintype Wire] [DecidableEq Wire] [Fintype gamma]
    (wire : Wire)
    (bR : OrthonormalBasis gamma Complex (QubitRegister (OtherWires wire)))
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
    (rho : DensityOperator (QubitRegister Wire)) :
    traceNorm
        ((selectedWireKraus wire
            (tTerminalKraus t pairAttempts blocks letters)).inducedMap
            rho.toOperator -
          (selectedWireKraus wire (tIdealWordKraus letters)).inducedMap
            rho.toOperator) ≤
      (Fintype.card ((((Fin 2) × gamma) × ((Fin 2) × gamma))) : Real) *
        ((Fintype.card ((Fin 2) × (Fin 2)) : Real) *
          (16 * tWordErrorBudget t pairAttempts blocks letters)) := by
  exact selectedWireKraus_difference_density_le wire bR
    (tTerminalKraus t pairAttempts blocks letters) (tIdealWordKraus letters)
    (tTerminalKraus_complete t pairAttempts blocks letters)
    (tIdealWordKraus_complete letters)
    (16 * tWordErrorBudget t pairAttempts blocks letters)
    (tTerminalKraus_matrixUnit_le t pairAttempts blocks letters) rho

private theorem selectedWireKraus_inducedMap_density_eq_of_inducedMap_eq
    {kappa lambda Wire : Type}
    [Fintype kappa] [Fintype lambda]
    [Fintype Wire] [DecidableEq Wire]
    (wire : Wire)
    (E : FiniteKrausFamily kappa QubitSpace QubitSpace)
    (F : FiniteKrausFamily lambda QubitSpace QubitSpace)
    (hE : E.Complete) (hF : F.Complete)
    (hmap : E.inducedMap = F.inducedMap)
    (rho : DensityOperator (QubitRegister Wire)) :
    (selectedWireKraus wire E).inducedMap rho.toOperator =
      (selectedWireKraus wire F).inducedMap rho.toOperator := by
  let bR := EuclideanSpace.basisFun
    (Bitstring (OtherWires wire)) Complex
  have hlocal : ∀ i j : Fin 2,
      traceNorm
          (E.inducedMap
              (InnerProductSpace.rankOne Complex
                (EuclideanSpace.basisFun (Fin 2) Complex i)
                (EuclideanSpace.basisFun (Fin 2) Complex j)).toLinearMap -
            F.inducedMap
              (InnerProductSpace.rankOne Complex
                (EuclideanSpace.basisFun (Fin 2) Complex i)
                (EuclideanSpace.basisFun (Fin 2) Complex j)).toLinearMap) ≤ 0 := by
    intro i j
    rw [hmap, sub_self]
    have hzero : traceNorm (0 : Operator QubitSpace) = 0 :=
      (traceNorm_eq_zero_iff (0 : Operator QubitSpace)).2 rfl
    rw [hzero]
  have hbound := selectedWireKraus_difference_density_le wire bR E F hE hF
    0 hlocal rho
  have hzero :
      traceNorm
          ((selectedWireKraus wire E).inducedMap rho.toOperator -
            (selectedWireKraus wire F).inducedMap rho.toOperator) = 0 := by
    apply le_antisymm
    · simpa using hbound
    · exact traceNorm_nonneg _
  exact sub_eq_zero.mp ((traceNorm_eq_zero_iff _).mp hzero)

private theorem hIdealWord_selectedWire_unitary_action
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (rho : DensityOperator (QubitRegister Wire)) :
    (selectedWireKraus wire (hIdealWordKraus letters)).inducedMap rho.toOperator =
      (Matrix.toEuclideanLin
        (singleQubitLift wire
          (BK05SignedPhaseLetter.evalList (-Real.pi / 4) letters) :
          Matrix (Bitstring Wire) (Bitstring Wire) Complex)).comp
        (rho.toOperator.comp (LinearMap.adjoint
          (Matrix.toEuclideanLin
            (singleQubitLift wire
              (BK05SignedPhaseLetter.evalList (-Real.pi / 4) letters) :
              Matrix (Bitstring Wire) (Bitstring Wire) Complex)))) := by
  calc
    (selectedWireKraus wire (hIdealWordKraus letters)).inducedMap rho.toOperator =
        (selectedWireKraus wire
          (unitaryGateKraus
            (BK05SignedPhaseLetter.evalList (-Real.pi / 4) letters))).inducedMap
          rho.toOperator :=
      selectedWireKraus_inducedMap_density_eq_of_inducedMap_eq wire
        (hIdealWordKraus letters)
        (unitaryGateKraus
          (BK05SignedPhaseLetter.evalList (-Real.pi / 4) letters))
        (hIdealWordKraus_complete letters)
        (unitaryGateKraus_complete _)
        (hIdealWordKraus_eq_unitaryGateKraus letters) rho
    _ = _ := selectedWireKraus_unitary_action wire
      (BK05SignedPhaseLetter.evalList (-Real.pi / 4) letters) rho.toOperator

private theorem tIdealWord_selectedWire_unitary_action
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
    (rho : DensityOperator (QubitRegister Wire)) :
    (selectedWireKraus wire (tIdealWordKraus letters)).inducedMap rho.toOperator =
      (Matrix.toEuclideanLin
        (singleQubitLift wire
          (BK05SignedPhaseLetter.evalList (-Real.pi / 6) letters) :
          Matrix (Bitstring Wire) (Bitstring Wire) Complex)).comp
        (rho.toOperator.comp (LinearMap.adjoint
          (Matrix.toEuclideanLin
            (singleQubitLift wire
              (BK05SignedPhaseLetter.evalList (-Real.pi / 6) letters) :
              Matrix (Bitstring Wire) (Bitstring Wire) Complex)))) := by
  calc
    (selectedWireKraus wire (tIdealWordKraus letters)).inducedMap rho.toOperator =
        (selectedWireKraus wire
          (unitaryGateKraus
            (BK05SignedPhaseLetter.evalList (-Real.pi / 6) letters))).inducedMap
          rho.toOperator :=
      selectedWireKraus_inducedMap_density_eq_of_inducedMap_eq wire
        (tIdealWordKraus letters)
        (unitaryGateKraus
          (BK05SignedPhaseLetter.evalList (-Real.pi / 6) letters))
        (tIdealWordKraus_complete letters)
        (unitaryGateKraus_complete _)
        (tIdealWordKraus_eq_unitaryGateKraus letters) rho
    _ = _ := selectedWireKraus_unitary_action wire
      (BK05SignedPhaseLetter.evalList (-Real.pi / 6) letters) rho.toOperator

/- A register leaf is actual branch data: status, history, computed resource
ledger, and the unnormalised register operator. -/
private structure BK05RegisterRawLeaf
    (Wire : Type) [Fintype Wire] [DecidableEq Wire] where
  status : BK05WordLeafStatus
  history : List Bool
  ledger : ResourceLedger BK05ResourceToken
  raw : Operator (QubitRegister Wire)

/- The compiler stores only finite physical branch data.  Completeness,
weights, ledger equations, and approximation guarantees remain external
theorems rather than conclusion-shaped fields. -/
private structure BK05CompiledAggregate
    (Wire : Type) [Fintype Wire] [DecidableEq Wire] where
  Branch : Type
  [branchFintype : Fintype Branch]
  family : FiniteKrausFamily Branch (QubitRegister Wire) (QubitRegister Wire)
  status : Branch → BK05WordLeafStatus
  ledger : Branch → ResourceLedger BK05ResourceToken

private instance BK05CompiledAggregate.instBranchFintype
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (compiled : BK05CompiledAggregate Wire) : Fintype compiled.Branch :=
  compiled.branchFintype

private noncomputable def BK05CompiledAggregate.aggregateRaw
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (compiled : BK05CompiledAggregate Wire)
    (rho : DensityOperator (QubitRegister Wire)) :
    Operator (QubitRegister Wire) :=
  compiled.family.inducedMap rho.toOperator

private noncomputable def BK05CompiledAggregate.rawLeaf
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (compiled : BK05CompiledAggregate Wire)
    (rho : DensityOperator (QubitRegister Wire))
    (branch : compiled.Branch) : BK05RegisterRawLeaf Wire where
  status := compiled.status branch
  history := []
  ledger := compiled.ledger branch
  raw := (compiled.family.operator branch).comp
    (rho.toOperator.comp (LinearMap.adjoint (compiled.family.operator branch)))

private noncomputable def BK05CompiledAggregate.rawLeaves
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (compiled : BK05CompiledAggregate Wire)
    (rho : DensityOperator (QubitRegister Wire)) :
    Multiset (BK05RegisterRawLeaf Wire) :=
  (Finset.univ : Finset compiled.Branch).1.map (compiled.rawLeaf rho)

private noncomputable def BK05CompiledAggregate.computedLedgers
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (compiled : BK05CompiledAggregate Wire) :
    Multiset (ResourceLedger BK05ResourceToken) :=
  (Finset.univ : Finset compiled.Branch).1.map compiled.ledger

private noncomputable def BK05CompiledAggregate.totalWeight
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (compiled : BK05CompiledAggregate Wire)
    (rho : DensityOperator (QubitRegister Wire)) : Real :=
  (LinearMap.trace Complex (QubitRegister Wire)
    (compiled.aggregateRaw rho)).re

private theorem BK05CompiledAggregate.rawLeaves_aggregate
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (compiled : BK05CompiledAggregate Wire)
    (rho : DensityOperator (QubitRegister Wire)) :
    ((compiled.rawLeaves rho).map BK05RegisterRawLeaf.raw).sum =
      compiled.aggregateRaw rho := by
  classical
  simp [BK05CompiledAggregate.rawLeaves, BK05CompiledAggregate.rawLeaf,
    BK05CompiledAggregate.aggregateRaw, FiniteKrausFamily.inducedMap_apply]

private theorem compiledAggregate_ledgers_eq_computed
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (compiled : BK05CompiledAggregate Wire)
    (rho : DensityOperator (QubitRegister Wire)) :
    (compiled.rawLeaves rho).map BK05RegisterRawLeaf.ledger =
      compiled.computedLedgers := by
  classical
  simp [BK05CompiledAggregate.rawLeaves, BK05CompiledAggregate.rawLeaf,
    BK05CompiledAggregate.computedLedgers, Multiset.map_map]
  rfl

private theorem compiledAggregate_totalWeight_eq_one
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (compiled : BK05CompiledAggregate Wire)
    (hcomplete : compiled.family.Complete)
    (rho : DensityOperator (QubitRegister Wire)) :
    compiled.totalWeight rho = 1 := by
  unfold BK05CompiledAggregate.totalWeight BK05CompiledAggregate.aggregateRaw
  rw [compiled.family.inducedMap_trace_preserving hcomplete, rho.trace_one]
  norm_num

private inductive BK05WordCompilation where
  | h (resource : DensityOperator QubitSpace) (blocks : Nat)
      (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
  | t (resource : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
      (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))

private noncomputable def BK05WordCompilation.targetGate :
    BK05WordCompilation → UnitaryGate (Fin 2)
  | .h _ _ letters => BK05SignedPhaseLetter.evalList (-Real.pi / 4) letters
  | .t _ _ _ letters => BK05SignedPhaseLetter.evalList (-Real.pi / 6) letters

private noncomputable def BK05WordCompilation.localErrorBudget :
    BK05WordCompilation → Real
  | .h resource blocks letters => hWordErrorBudget resource blocks letters
  | .t resource pairAttempts blocks letters =>
      tWordErrorBudget resource pairAttempts blocks letters

private def BK05WordCompilation.computedLedger :
    BK05WordCompilation → ResourceLedger BK05ResourceToken
  | .h _ blocks letters =>
      Multiset.replicate
        (8 * blocks * BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) letters) .h
  | .t _ pairAttempts blocks letters =>
      Multiset.replicate
        (2 * pairAttempts * 12 * blocks *
          BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) letters) .t

private noncomputable def compileWord
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) : BK05WordCompilation → BK05CompiledAggregate Wire
  | .h resource blocks letters =>
      { Branch := BK05TerminalIndex
          (cpKrausSize (hWordLiveLinear resource blocks letters)
            (hWordLiveLinear_completelyPositive resource blocks letters))
          (cpKrausSize (hWordPhaseStoppedLinear resource blocks letters)
            (hWordPhaseStoppedLinear_completelyPositive resource blocks letters))
          (cpKrausSize (0 : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
            (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace)))
        branchFintype := inferInstance
        family := selectedWireKraus wire (hTerminalKraus resource blocks letters)
        status := terminalStatus
        ledger := fun _ =>
          BK05WordCompilation.computedLedger (.h resource blocks letters) }
  | .t resource pairAttempts blocks letters =>
      { Branch := BK05TerminalIndex
          (cpKrausSize (tWordLiveLinear resource pairAttempts blocks letters)
            (tWordLiveLinear_completelyPositive resource pairAttempts blocks letters))
          (cpKrausSize (tWordPhaseStoppedLinear resource pairAttempts blocks letters)
            (tWordPhaseStoppedLinear_completelyPositive resource pairAttempts blocks letters))
          (cpKrausSize (tWordPairStoppedLinear resource pairAttempts blocks letters)
            (tWordPairStoppedLinear_completelyPositive resource pairAttempts blocks letters))
        branchFintype := inferInstance
        family := selectedWireKraus wire
          (tTerminalKraus resource pairAttempts blocks letters)
        status := terminalStatus
        ledger := fun _ =>
          BK05WordCompilation.computedLedger
            (.t resource pairAttempts blocks letters) }

private theorem compileWord_complete
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) (spec : BK05WordCompilation) :
    (compileWord wire spec).family.Complete := by
  cases spec with
  | h resource blocks letters =>
      exact selectedWireKraus_complete wire
        (hTerminalKraus_complete resource blocks letters)
  | t resource pairAttempts blocks letters =>
      exact selectedWireKraus_complete wire
        (tTerminalKraus_complete resource pairAttempts blocks letters)

private theorem compileWord_totalWeight
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) (spec : BK05WordCompilation)
    (rho : DensityOperator (QubitRegister Wire)) :
    (compileWord wire spec).totalWeight rho = 1 :=
  compiledAggregate_totalWeight_eq_one (compileWord wire spec)
    (compileWord_complete wire spec) rho

private theorem compileWord_retainsFailureLeaves
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) (spec : BK05WordCompilation) :
    (∃ branch : (compileWord wire spec).Branch,
        (compileWord wire spec).status branch = .stoppedPhaseExhausted) ∧
      (∃ branch : (compileWord wire spec).Branch,
        (compileWord wire spec).status branch = .stoppedTPairExhausted) := by
  cases spec with
  | h resource blocks letters =>
      simpa [compileWord] using retainsFailureLeaves
        (hWordLiveLinear resource blocks letters)
        (hWordPhaseStoppedLinear resource blocks letters)
        (0 : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
        (hWordLiveLinear_completelyPositive resource blocks letters)
        (hWordPhaseStoppedLinear_completelyPositive resource blocks letters)
        (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
  | t resource pairAttempts blocks letters =>
      simpa [compileWord] using retainsFailureLeaves
        (tWordLiveLinear resource pairAttempts blocks letters)
        (tWordPhaseStoppedLinear resource pairAttempts blocks letters)
        (tWordPairStoppedLinear resource pairAttempts blocks letters)
        (tWordLiveLinear_completelyPositive resource pairAttempts blocks letters)
        (tWordPhaseStoppedLinear_completelyPositive resource pairAttempts blocks letters)
        (tWordPairStoppedLinear_completelyPositive resource pairAttempts blocks letters)

private noncomputable def selectedWireErrorScale
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) : Real :=
  (Fintype.card
      ((((Fin 2) × Bitstring (OtherWires wire)) ×
        ((Fin 2) × Bitstring (OtherWires wire)))) : Real) *
    ((Fintype.card ((Fin 2) × (Fin 2)) : Real) * 16)

private theorem selectedWireErrorScale_nonneg
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) : 0 ≤ selectedWireErrorScale wire := by
  unfold selectedWireErrorScale
  positivity

private noncomputable def compileWordRegisterErrorBound
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) (spec : BK05WordCompilation) : Real :=
  selectedWireErrorScale wire * spec.localErrorBudget

set_option maxRecDepth 4096 in
private theorem compileWord_actual_aggregate_trace_bound
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) (spec : BK05WordCompilation)
    (rho : DensityOperator (QubitRegister Wire)) :
    traceNorm
        ((compileWord wire spec).aggregateRaw rho -
          (Matrix.toEuclideanLin
            (singleQubitLift wire spec.targetGate :
              Matrix (Bitstring Wire) (Bitstring Wire) Complex)).comp
            (rho.toOperator.comp (LinearMap.adjoint
              (Matrix.toEuclideanLin
                (singleQubitLift wire spec.targetGate :
                  Matrix (Bitstring Wire) (Bitstring Wire) Complex))))) ≤
      compileWordRegisterErrorBound wire spec := by
  let bR := EuclideanSpace.basisFun
    (Bitstring (OtherWires wire)) Complex
  cases spec with
  | h resource blocks letters =>
      have hbound := hSelectedWire_actual_aggregate_traceNorm_le wire bR
        resource blocks letters rho
      rw [hIdealWord_selectedWire_unitary_action wire letters rho] at hbound
      change traceNorm
        ((selectedWireKraus wire
            (hTerminalKraus resource blocks letters)).inducedMap
            rho.toOperator - _) ≤
          selectedWireErrorScale wire *
            hWordErrorBudget resource blocks letters
      simpa only [selectedWireErrorScale, BK05WordCompilation.targetGate, mul_assoc] using hbound
  | t resource pairAttempts blocks letters =>
      have hbound := tSelectedWire_actual_aggregate_traceNorm_le wire bR
        resource pairAttempts blocks letters rho
      rw [tIdealWord_selectedWire_unitary_action wire letters rho] at hbound
      change traceNorm
        ((selectedWireKraus wire
            (tTerminalKraus resource pairAttempts blocks letters)).inducedMap
            rho.toOperator - _) ≤
          selectedWireErrorScale wire *
            tWordErrorBudget resource pairAttempts blocks letters
      simpa only [selectedWireErrorScale, BK05WordCompilation.targetGate, mul_assoc] using hbound

/- A terminal status composes in execution order: a stopped prefix remains
stopped, while a live prefix exposes the status of the suffix. -/
private def BK05WordLeafStatus.thenStatus :
    BK05WordLeafStatus → BK05WordLeafStatus → BK05WordLeafStatus
  | .live, suffix => suffix
  | .stoppedPhaseExhausted, _ => .stoppedPhaseExhausted
  | .stoppedTPairExhausted, _ => .stoppedTPairExhausted

/- Sequential composition preserves the literal product branch space and
adds the two structurally computed ledgers. -/
private noncomputable def BK05CompiledAggregate.seq
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (first second : BK05CompiledAggregate Wire) :
    BK05CompiledAggregate Wire where
  Branch := first.Branch × second.Branch
  branchFintype := inferInstance
  family := krausSeq first.family second.family
  status branch := (first.status branch.1).thenStatus (second.status branch.2)
  ledger branch := first.ledger branch.1 + second.ledger branch.2

private theorem BK05CompiledAggregate.seq_complete
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    {first second : BK05CompiledAggregate Wire}
    (hfirst : first.family.Complete) (hsecond : second.family.Complete) :
    (first.seq second).family.Complete :=
  krausSeq_complete hfirst hsecond

private theorem BK05CompiledAggregate.seq_aggregateRaw
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (first second : BK05CompiledAggregate Wire)
    (rho : DensityOperator (QubitRegister Wire)) :
    (first.seq second).aggregateRaw rho =
      second.family.inducedMap (first.aggregateRaw rho) := by
  change
    (krausSeq first.family second.family).inducedMap rho.toOperator =
      second.family.inducedMap (first.family.inducedMap rho.toOperator)
  exact krausSeq_inducedMap_apply first.family second.family rho.toOperator

private theorem BK05CompiledAggregate.seq_totalWeight
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (first second : BK05CompiledAggregate Wire)
    (hfirst : first.family.Complete) (hsecond : second.family.Complete)
    (rho : DensityOperator (QubitRegister Wire)) :
    (first.seq second).totalWeight rho = 1 :=
  compiledAggregate_totalWeight_eq_one (first.seq second)
    (first.seq_complete hfirst hsecond) rho

/- A one-outcome finite Kraus family for an exact finite-dimensional unitary. -/
private noncomputable def finiteUnitaryKraus
    {n : Type} [Fintype n] [DecidableEq n]
    (gate : UnitaryGate n) :
    FiniteKrausFamily Unit (EuclideanSpace Complex n)
      (EuclideanSpace Complex n) where
  operator _ := Matrix.toEuclideanLin
    (gate : Matrix n n Complex)

private theorem finiteUnitaryKraus_complete
    {n : Type} [Fintype n] [DecidableEq n]
    (gate : UnitaryGate n) :
    (finiteUnitaryKraus gate).Complete := by
  rw [FiniteKrausFamily.Complete]
  simp only [Fintype.sum_unique, finiteUnitaryKraus]
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [← Matrix.toLpLin_mul_same]
  rw [← Matrix.star_eq_conjTranspose, gate.property.1]
  simpa only [Module.End.one_eq_id] using
    (Matrix.toLpLin_one (R := Complex) (n := n) 2)

private theorem finiteUnitaryKraus_inducedMap_apply
    {n : Type} [Fintype n] [DecidableEq n]
    (gate : UnitaryGate n)
    (A : Operator (EuclideanSpace Complex n)) :
    (finiteUnitaryKraus gate).inducedMap A =
      (Matrix.toEuclideanLin
        (gate : Matrix n n Complex)).comp
        (A.comp (LinearMap.adjoint
          (Matrix.toEuclideanLin
            (gate : Matrix n n Complex)))) := by
  rw [FiniteKrausFamily.inducedMap_apply, Fintype.sum_unique]
  rfl

/- Register specialization; its carrier remains the concrete bitstring basis. -/
private noncomputable def registerUnitaryKraus
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (gate : UnitaryGate (Bitstring Wire)) :
    FiniteKrausFamily Unit (QubitRegister Wire) (QubitRegister Wire) :=
  finiteUnitaryKraus gate

private theorem registerUnitaryKraus_complete
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (gate : UnitaryGate (Bitstring Wire)) :
    (registerUnitaryKraus gate).Complete :=
  finiteUnitaryKraus_complete gate

private theorem registerUnitaryKraus_inducedMap_apply
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (gate : UnitaryGate (Bitstring Wire))
    (A : Operator (QubitRegister Wire)) :
    (registerUnitaryKraus gate).inducedMap A =
      (Matrix.toEuclideanLin
        (gate : Matrix (Bitstring Wire) (Bitstring Wire) Complex)).comp
        (A.comp (LinearMap.adjoint
          (Matrix.toEuclideanLin
            (gate : Matrix (Bitstring Wire) (Bitstring Wire) Complex)))) :=
  finiteUnitaryKraus_inducedMap_apply gate A

/- The elementwise matrix norm used by the generated-subgroup topology
controls the ordinary operator norm after the explicit finite basis
expansion.  The coarse cardinality factor is harmless because density gives
an arbitrarily small executable word. -/
private theorem operatorNorm_toEuclideanLin_le_card_mul_entrywise
    {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n Complex) :
    operatorNorm (Matrix.toEuclideanLin M) ≤
      (Fintype.card (n × n) : Real) * ‖M‖ := by
  classical
  let b := EuclideanSpace.basisFun n Complex
  have hexpand := operator_matrixUnit_expansion_prod b
    (Matrix.toEuclideanLin M)
  rw [hexpand]
  change ‖LinearMap.toContinuousLinearMap
      (∑ index : n × n,
        b.repr ((Matrix.toEuclideanLin M) (b index.2)) index.1 •
          (InnerProductSpace.rankOne Complex
            (b index.1) (b index.2)).toLinearMap)‖ ≤ _
  rw [map_sum]
  calc
    ‖∑ index : n × n,
        LinearMap.toContinuousLinearMap
          (b.repr ((Matrix.toEuclideanLin M) (b index.2)) index.1 •
            (InnerProductSpace.rankOne Complex
              (b index.1) (b index.2)).toLinearMap)‖ ≤
        ∑ index : n × n,
          ‖LinearMap.toContinuousLinearMap
            (b.repr ((Matrix.toEuclideanLin M) (b index.2)) index.1 •
              (InnerProductSpace.rankOne Complex
                (b index.1) (b index.2)).toLinearMap)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _index : n × n, ‖M‖ := by
      apply Finset.sum_le_sum
      intro index _
      simp only [map_smul, norm_smul]
      have hcoeff :
          b.repr ((Matrix.toEuclideanLin M) (b index.2)) index.1 =
            M index.1 index.2 := by
        change b.toBasis.repr
            ((Matrix.toEuclideanLin M) (b.toBasis index.2)) index.1 = _
        rw [← LinearMap.toMatrix_apply]
        rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
        exact congrFun (congrFun
          (LinearMap.toMatrix_toLin b.toBasis b.toBasis M) index.1) index.2
      rw [hcoeff]
      calc
        ‖M index.1 index.2‖ *
            ‖LinearMap.toContinuousLinearMap
              (InnerProductSpace.rankOne Complex
                (b index.1) (b index.2)).toLinearMap‖ =
            ‖M index.1 index.2‖ := by
          change ‖M index.1 index.2‖ *
              ‖InnerProductSpace.rankOne Complex
                (b index.1) (b index.2)‖ = _
          simp [b]
        _ ≤ ‖M‖ := Matrix.norm_entry_le_entrywise_sup_norm M
    _ = (Fintype.card (n × n) : Real) * ‖M‖ := by simp

private theorem finiteUnitary_operatorNorm_le_one
    {n : Type} [Fintype n] [DecidableEq n]
    (gate : UnitaryGate n) :
    operatorNorm (Matrix.toEuclideanLin
      (gate : Matrix n n Complex)) ≤ 1 := by
  let U : Operator (EuclideanSpace Complex n) :=
    Matrix.toEuclideanLin (gate : Matrix n n Complex)
  have hcomplete := finiteUnitaryKraus_complete gate
  have hlinear : (LinearMap.adjoint U).comp U = 1 := by
    simpa [FiniteKrausFamily.Complete, finiteUnitaryKraus, U] using hcomplete
  have hcontinuous :
      (LinearMap.toContinuousLinearMap U).adjoint ∘L
          LinearMap.toContinuousLinearMap U = 1 := by
    rw [← LinearMap.adjoint_toContinuousLinearMap]
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun f : Operator (EuclideanSpace Complex n) => f x) hlinear
  have hnorm (x : EuclideanSpace Complex n) :
      ‖LinearMap.toContinuousLinearMap U x‖ = ‖x‖ :=
    (LinearMap.toContinuousLinearMap U).norm_map_iff_adjoint_comp_self.mpr
      hcontinuous x
  change ‖LinearMap.toContinuousLinearMap U‖ ≤ 1
  apply (LinearMap.toContinuousLinearMap U).opNorm_le_bound (by norm_num)
  intro x
  rw [hnorm]
  simp

private theorem operatorNorm_adjoint_eq
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (A : Operator H) :
    operatorNorm (LinearMap.adjoint A) = operatorNorm A := by
  unfold operatorNorm
  rw [LinearMap.adjoint_toContinuousLinearMap]
  exact ContinuousLinearMap.adjoint.norm_map _

private theorem finiteUnitaryKraus_globalPhase_inducedMap_eq
    {n : Type} [Fintype n] [DecidableEq n]
    {left right : UnitaryGate n}
    (hphase : GlobalPhaseEquivalent left right)
    (A : Operator (EuclideanSpace Complex n)) :
    (finiteUnitaryKraus left).inducedMap A =
      (finiteUnitaryKraus right).inducedMap A := by
  rcases hphase with ⟨scalar, hscalarNorm, hmatrix⟩
  have hscalar : scalar * star scalar = 1 := by
    rw [mul_comm]
    change (starRingEnd Complex) scalar * scalar = 1
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm, hscalarNorm]
    norm_num
  have hscalar' : star scalar * scalar = 1 := by
    rw [mul_comm, hscalar]
  rw [finiteUnitaryKraus_inducedMap_apply,
    finiteUnitaryKraus_inducedMap_apply]
  have hoperator :
      Matrix.toEuclideanLin (right : Matrix n n Complex) =
        scalar • Matrix.toEuclideanLin (left : Matrix n n Complex) := by
    rw [← map_smul]
    exact congrArg Matrix.toEuclideanLin hmatrix
  rw [hoperator]
  have hadjoint :
      LinearMap.adjoint
          (scalar • Matrix.toEuclideanLin (left : Matrix n n Complex)) =
        star scalar • LinearMap.adjoint
          (Matrix.toEuclideanLin (left : Matrix n n Complex)) := by
    change star
        (scalar • Matrix.toEuclideanLin (left : Matrix n n Complex)) = _
    rw [star_smul]
    rfl
  rw [hadjoint]
  ext x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_smul]
  rw [hscalar', one_smul]

/- Entrywise approximation of two finite unitary matrices gives a uniform
trace-norm bound on their density conjugations.  This is the explicit
matrix-to-channel term required before composing the physical compiler with
projective density. -/
private theorem finiteUnitaryKraus_difference_traceNorm_le
    {n : Type} [Fintype n] [DecidableEq n]
    (left right : UnitaryGate n)
    (A : Operator (EuclideanSpace Complex n)) :
    traceNorm
        ((finiteUnitaryKraus left).inducedMap A -
          (finiteUnitaryKraus right).inducedMap A) ≤
      2 * (Fintype.card (n × n) : Real) *
        ‖(left : Matrix n n Complex) - (right : Matrix n n Complex)‖ *
          traceNorm A := by
  let L : Operator (EuclideanSpace Complex n) :=
    Matrix.toEuclideanLin (left : Matrix n n Complex)
  let R : Operator (EuclideanSpace Complex n) :=
    Matrix.toEuclideanLin (right : Matrix n n Complex)
  let D : Operator (EuclideanSpace Complex n) := L - R
  let bound : Real := (Fintype.card (n × n) : Real) *
    ‖(left : Matrix n n Complex) - (right : Matrix n n Complex)‖
  have hbound : 0 ≤ bound := by
    dsimp only [bound]
    positivity
  have hD : D = Matrix.toEuclideanLin
      ((left : Matrix n n Complex) - (right : Matrix n n Complex)) := by
    dsimp only [D, L, R]
    rw [map_sub]
  have hDnorm : operatorNorm D ≤ bound := by
    rw [hD]
    exact operatorNorm_toEuclideanLin_le_card_mul_entrywise _
  have hLnorm : operatorNorm L ≤ 1 := by
    exact finiteUnitary_operatorNorm_le_one left
  have hRnorm : operatorNorm R ≤ 1 := by
    exact finiteUnitary_operatorNorm_le_one right
  have hAdjLnorm : operatorNorm (LinearMap.adjoint L) ≤ 1 := by
    rw [operatorNorm_adjoint_eq]
    exact hLnorm
  have hAdjDnorm : operatorNorm (LinearMap.adjoint D) ≤ bound := by
    rw [operatorNorm_adjoint_eq]
    exact hDnorm
  have htermLeft :
      traceNorm (D * A * LinearMap.adjoint L) ≤ bound * traceNorm A := by
    calc
      traceNorm (D * A * LinearMap.adjoint L) ≤
          operatorNorm (LinearMap.adjoint L) * traceNorm (D * A) :=
        traceNorm_mul_right_le (D * A) (LinearMap.adjoint L)
      _ ≤ 1 * (operatorNorm D * traceNorm A) :=
        mul_le_mul hAdjLnorm (traceNorm_mul_left_le D A)
          (traceNorm_nonneg _) (by norm_num)
      _ ≤ 1 * (bound * traceNorm A) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hDnorm (traceNorm_nonneg A))
          (by norm_num)
      _ = bound * traceNorm A := one_mul _
  have htermRight :
      traceNorm (R * A * LinearMap.adjoint D) ≤ bound * traceNorm A := by
    calc
      traceNorm (R * A * LinearMap.adjoint D) ≤
          operatorNorm (LinearMap.adjoint D) * traceNorm (R * A) :=
        traceNorm_mul_right_le (R * A) (LinearMap.adjoint D)
      _ ≤ bound * (operatorNorm R * traceNorm A) :=
        mul_le_mul hAdjDnorm (traceNorm_mul_left_le R A)
          (traceNorm_nonneg _) hbound
      _ ≤ bound * (1 * traceNorm A) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hRnorm (traceNorm_nonneg A)) hbound
      _ = bound * traceNorm A := by ring
  rw [finiteUnitaryKraus_inducedMap_apply,
    finiteUnitaryKraus_inducedMap_apply]
  change traceNorm
      (L * A * LinearMap.adjoint L - R * A * LinearMap.adjoint R) ≤ _
  have hdecompose :
      L * A * LinearMap.adjoint L - R * A * LinearMap.adjoint R =
        D * A * LinearMap.adjoint L + R * A * LinearMap.adjoint D := by
    dsimp only [D]
    rw [map_sub]
    noncomm_ring
  rw [hdecompose]
  calc
    traceNorm
        (D * A * LinearMap.adjoint L + R * A * LinearMap.adjoint D) ≤
        traceNorm (D * A * LinearMap.adjoint L) +
          traceNorm (R * A * LinearMap.adjoint D) :=
      traceNorm_add_le _ _
    _ ≤ bound * traceNorm A + bound * traceNorm A :=
      add_le_add htermLeft htermRight
    _ = 2 * (Fintype.card (n × n) : Real) *
        ‖(left : Matrix n n Complex) - (right : Matrix n n Complex)‖ *
          traceNorm A := by
      dsimp only [bound]
      ring

private theorem finiteUnitaryKraus_mul_inducedMap
    {n : Type} [Fintype n] [DecidableEq n]
    (first second : UnitaryGate n)
    (A : Operator (EuclideanSpace Complex n)) :
    (finiteUnitaryKraus (second * first)).inducedMap A =
      (finiteUnitaryKraus second).inducedMap
        ((finiteUnitaryKraus first).inducedMap A) := by
  rw [finiteUnitaryKraus_inducedMap_apply,
    finiteUnitaryKraus_inducedMap_apply,
    finiteUnitaryKraus_inducedMap_apply]
  change
    Matrix.toEuclideanLin
          ((second : Matrix n n Complex) * (first : Matrix n n Complex)) *
        A *
          LinearMap.adjoint
            (Matrix.toEuclideanLin
              ((second : Matrix n n Complex) * (first : Matrix n n Complex))) =
      Matrix.toEuclideanLin (second : Matrix n n Complex) *
        (Matrix.toEuclideanLin (first : Matrix n n Complex) * A *
          LinearMap.adjoint
            (Matrix.toEuclideanLin (first : Matrix n n Complex))) *
        LinearMap.adjoint
          (Matrix.toEuclideanLin (second : Matrix n n Complex))
  rw [Matrix.toLpLin_mul_same, LinearMap.adjoint_comp]
  change
    (Matrix.toEuclideanLin (second : Matrix n n Complex) *
        Matrix.toEuclideanLin (first : Matrix n n Complex)) * A *
        (LinearMap.adjoint
            (Matrix.toEuclideanLin (first : Matrix n n Complex)) *
          LinearMap.adjoint
            (Matrix.toEuclideanLin (second : Matrix n n Complex))) = _
  simp only [mul_assoc]

/- Exact Clifford/register gates use the same finite aggregate carrier as
physical word compilations, with one live branch and an empty ledger. -/
private noncomputable def exactGateAggregate
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (gate : UnitaryGate (Bitstring Wire)) : BK05CompiledAggregate Wire where
  Branch := Unit
  branchFintype := inferInstance
  family := registerUnitaryKraus gate
  status _ := .live
  ledger _ := 0

private theorem exactGateAggregate_complete
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (gate : UnitaryGate (Bitstring Wire)) :
    (exactGateAggregate gate).family.Complete :=
  registerUnitaryKraus_complete gate

private theorem exactGateAggregate_totalWeight
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (gate : UnitaryGate (Bitstring Wire))
    (rho : DensityOperator (QubitRegister Wire)) :
    (exactGateAggregate gate).totalWeight rho = 1 :=
  compiledAggregate_totalWeight_eq_one (exactGateAggregate gate)
    (exactGateAggregate_complete gate) rho

private theorem exactGateAggregate_globalPhase_aggregateRaw_eq
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    {left right : UnitaryGate (Bitstring Wire)}
    (hphase : GlobalPhaseEquivalent left right)
    (rho : DensityOperator (QubitRegister Wire)) :
    (exactGateAggregate left).aggregateRaw rho =
      (exactGateAggregate right).aggregateRaw rho := by
  change (finiteUnitaryKraus left).inducedMap rho.toOperator =
    (finiteUnitaryKraus right).inducedMap rho.toOperator
  exact finiteUnitaryKraus_globalPhase_inducedMap_eq hphase rho.toOperator

/- A physical finite-register program contains only executable word recipes,
exact XOR gates, and sequential syntax.  Approximation and completeness are
proved outside this data type. -/
private inductive BK05PhysicalRegisterCircuit
    (Wire : Type) [Fintype Wire] [DecidableEq Wire] where
  | identity : BK05PhysicalRegisterCircuit Wire
  | word (wire : Wire) (spec : BK05WordCompilation) :
      BK05PhysicalRegisterCircuit Wire
  | xor (control target : Wire) (hdistinct : control ≠ target) :
      BK05PhysicalRegisterCircuit Wire
  | compose (first second : BK05PhysicalRegisterCircuit Wire) :
      BK05PhysicalRegisterCircuit Wire

private noncomputable def BK05PhysicalRegisterCircuit.targetCircuit
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    BK05PhysicalRegisterCircuit Wire → FiniteRegisterCircuit Wire
  | .identity => .identity
  | .word wire spec => .oneQubit wire spec.targetGate
  | .xor control target hdistinct => .xor control target hdistinct
  | .compose first second =>
      .compose first.targetCircuit second.targetCircuit

/- Every physical word contributes its source and finite-stopping budget;
exact register gates contribute zero and sequential programs add budgets. -/
private noncomputable def BK05PhysicalRegisterCircuit.errorBudget
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    BK05PhysicalRegisterCircuit Wire → Real
  | .identity => 0
  | .word wire spec => compileWordRegisterErrorBound wire spec
  | .xor _ _ _ => 0
  | .compose first second => first.errorBudget + second.errorBudget

private noncomputable def compileFiniteRegisterCircuit
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    BK05PhysicalRegisterCircuit Wire → BK05CompiledAggregate Wire
  | .identity => exactGateAggregate 1
  | .word wire spec => compileWord wire spec
  | .xor control target hdistinct =>
      exactGateAggregate (registerXorGate control target hdistinct)
  | .compose first second =>
      (compileFiniteRegisterCircuit first).seq
        (compileFiniteRegisterCircuit second)

/- The ideal companion is built by the same syntax and execution order as
the physical compiler, but replaces every noisy word by its exact selected-
wire unitary.  This avoids assuming a semantic bridge as external data. -/
private noncomputable def BK05PhysicalRegisterCircuit.idealAggregate
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    BK05PhysicalRegisterCircuit Wire → BK05CompiledAggregate Wire
  | .identity => exactGateAggregate 1
  | .word wire spec => exactGateAggregate (singleQubitLift wire spec.targetGate)
  | .xor control target hdistinct =>
      exactGateAggregate (registerXorGate control target hdistinct)
  | .compose first second => first.idealAggregate.seq second.idealAggregate

private theorem compileFiniteRegisterCircuit_complete
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    ∀ physical : BK05PhysicalRegisterCircuit Wire,
      (compileFiniteRegisterCircuit physical).family.Complete := by
  intro physical
  induction physical with
  | identity => exact exactGateAggregate_complete 1
  | word wire spec => exact compileWord_complete wire spec
  | xor control target hdistinct =>
      exact exactGateAggregate_complete (registerXorGate control target hdistinct)
  | compose first second hfirst hsecond =>
      exact BK05CompiledAggregate.seq_complete hfirst hsecond

private theorem BK05PhysicalRegisterCircuit.idealAggregate_complete
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    ∀ physical : BK05PhysicalRegisterCircuit Wire,
      physical.idealAggregate.family.Complete := by
  intro physical
  induction physical with
  | identity => exact exactGateAggregate_complete 1
  | word wire spec =>
      exact exactGateAggregate_complete (singleQubitLift wire spec.targetGate)
  | xor control target hdistinct =>
      exact exactGateAggregate_complete (registerXorGate control target hdistinct)
  | compose first second hfirst hsecond =>
      exact BK05CompiledAggregate.seq_complete hfirst hsecond

private theorem BK05PhysicalRegisterCircuit.idealAggregate_inducedMap_eq
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    ∀ (physical : BK05PhysicalRegisterCircuit Wire)
      (A : Operator (QubitRegister Wire)),
      physical.idealAggregate.family.inducedMap A =
        (registerUnitaryKraus physical.targetCircuit.unitary).inducedMap A := by
  intro physical
  induction physical with
  | identity =>
      intro A
      rfl
  | word wire spec =>
      intro A
      rfl
  | xor control target hdistinct =>
      intro A
      rfl
  | compose first second ihFirst ihSecond =>
      intro A
      change (krausSeq first.idealAggregate.family
          second.idealAggregate.family).inducedMap A = _
      rw [krausSeq_inducedMap_apply]
      change second.idealAggregate.family.inducedMap
          (first.idealAggregate.family.inducedMap A) = _
      rw [ihFirst, ihSecond]
      simpa [BK05PhysicalRegisterCircuit.targetCircuit,
        FiniteRegisterCircuit.unitary_compose, registerUnitaryKraus] using
        (finiteUnitaryKraus_mul_inducedMap
          first.targetCircuit.unitary second.targetCircuit.unitary A).symm

private theorem BK05PhysicalRegisterCircuit.idealAggregate_aggregateRaw_eq
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (physical : BK05PhysicalRegisterCircuit Wire)
    (rho : DensityOperator (QubitRegister Wire)) :
    physical.idealAggregate.aggregateRaw rho =
      (exactGateAggregate physical.targetCircuit.unitary).aggregateRaw rho := by
  exact physical.idealAggregate_inducedMap_eq rho.toOperator

private theorem compileFiniteRegisterCircuit_totalWeight
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (physical : BK05PhysicalRegisterCircuit Wire)
    (rho : DensityOperator (QubitRegister Wire)) :
    (compileFiniteRegisterCircuit physical).totalWeight rho = 1 :=
  compiledAggregate_totalWeight_eq_one (compileFiniteRegisterCircuit physical)
    (compileFiniteRegisterCircuit_complete physical) rho

/- Sequential complete aggregates accumulate uniform density-input errors.
The second ideal channel contracts the first-stage discrepancy, so no
dimension- or branch-dependent amplification is introduced here. -/
private theorem BK05CompiledAggregate.seq_trace_bound
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (first second idealFirst idealSecond : BK05CompiledAggregate Wire)
    (hfirst : first.family.Complete)
    (hsecond : second.family.Complete)
    (hidealFirst : idealFirst.family.Complete)
    (hidealSecond : idealSecond.family.Complete)
    (epsilonFirst epsilonSecond : Real)
    (hFirst : ∀ rho : DensityOperator (QubitRegister Wire),
      traceNorm (first.aggregateRaw rho - idealFirst.aggregateRaw rho) ≤
        epsilonFirst)
    (hSecond : ∀ rho : DensityOperator (QubitRegister Wire),
      traceNorm (second.aggregateRaw rho - idealSecond.aggregateRaw rho) ≤
        epsilonSecond)
    (rho : DensityOperator (QubitRegister Wire)) :
    traceNorm
        ((first.seq second).aggregateRaw rho -
          (idealFirst.seq idealSecond).aggregateRaw rho) ≤
      epsilonFirst + epsilonSecond := by
  let actualFirst := (first.family.toQuantumChannel hfirst).mapDensity rho
  let exactFirst := (idealFirst.family.toQuantumChannel hidealFirst).mapDensity rho
  have hSecondActual := hSecond actualFirst
  have hContract :=
    (idealSecond.family.toQuantumChannel hidealSecond).traceNorm_density_sub_le
      actualFirst exactFirst
  have hContractFirst :
      traceNorm
          (idealSecond.aggregateRaw actualFirst -
            idealSecond.aggregateRaw exactFirst) ≤ epsilonFirst := by
    exact hContract.trans (hFirst rho)
  rw [BK05CompiledAggregate.seq_aggregateRaw,
    BK05CompiledAggregate.seq_aggregateRaw]
  change traceNorm
      (second.aggregateRaw actualFirst -
        idealSecond.aggregateRaw exactFirst) ≤ _
  calc
    traceNorm
        (second.aggregateRaw actualFirst -
          idealSecond.aggregateRaw exactFirst) =
        traceNorm
          ((second.aggregateRaw actualFirst -
              idealSecond.aggregateRaw actualFirst) +
            (idealSecond.aggregateRaw actualFirst -
              idealSecond.aggregateRaw exactFirst)) := by
          congr 1
          abel
    _ ≤ traceNorm
          (second.aggregateRaw actualFirst -
            idealSecond.aggregateRaw actualFirst) +
        traceNorm
          (idealSecond.aggregateRaw actualFirst -
            idealSecond.aggregateRaw exactFirst) :=
      traceNorm_add_le _ _
    _ ≤ epsilonSecond + epsilonFirst :=
      add_le_add hSecondActual hContractFirst
    _ = epsilonFirst + epsilonSecond := by ring

/- The structurally computed error budget bounds the complete unconditioned
aggregate against the exact unitary denoted by the finite physical program. -/
private theorem compileFiniteRegisterCircuit_actual_trace_bound
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    ∀ (physical : BK05PhysicalRegisterCircuit Wire)
      (rho : DensityOperator (QubitRegister Wire)),
      traceNorm
          ((compileFiniteRegisterCircuit physical).aggregateRaw rho -
            physical.idealAggregate.aggregateRaw rho) ≤
        physical.errorBudget := by
  intro physical
  induction physical with
  | identity =>
      intro rho
      change traceNorm
        ((registerUnitaryKraus 1).inducedMap rho.toOperator -
          (registerUnitaryKraus 1).inducedMap rho.toOperator) ≤ 0
      rw [sub_self]
      exact le_of_eq ((traceNorm_eq_zero_iff _).2 rfl)
  | word wire spec =>
      intro rho
      change traceNorm ((compileWord wire spec).aggregateRaw rho -
        (registerUnitaryKraus (singleQubitLift wire spec.targetGate)).inducedMap
          rho.toOperator) ≤ compileWordRegisterErrorBound wire spec
      rw [registerUnitaryKraus_inducedMap_apply]
      exact compileWord_actual_aggregate_trace_bound wire spec rho
  | xor control target hdistinct =>
      intro rho
      change traceNorm
        ((registerUnitaryKraus (registerXorGate control target hdistinct)).inducedMap
            rho.toOperator -
          (registerUnitaryKraus (registerXorGate control target hdistinct)).inducedMap
            rho.toOperator) ≤ 0
      rw [sub_self]
      exact le_of_eq ((traceNorm_eq_zero_iff _).2 rfl)
  | compose first second ihFirst ihSecond =>
      intro rho
      have hbound := BK05CompiledAggregate.seq_trace_bound
        (compileFiniteRegisterCircuit first)
        (compileFiniteRegisterCircuit second)
        first.idealAggregate second.idealAggregate
        (compileFiniteRegisterCircuit_complete first)
        (compileFiniteRegisterCircuit_complete second)
        first.idealAggregate_complete second.idealAggregate_complete
        first.errorBudget second.errorBudget ihFirst ihSecond rho
      exact hbound

/- A concrete generator of the finite-register route: either one displayed
one-qubit H/K/phase atom on a selected wire or one exact XOR. -/
private inductive BK05RegisterAtom
    (theta : Real) (Wire : Type) [Fintype Wire] [DecidableEq Wire] where
  | oneQubit (wire : Wire) (atom : BK05PhaseAtom theta) :
      BK05RegisterAtom theta Wire
  | xor (control target : Wire) (hdistinct : control ≠ target) :
      BK05RegisterAtom theta Wire

private noncomputable def BK05RegisterAtom.eval
    {theta : Real} {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    BK05RegisterAtom theta Wire → UnitaryGate (Bitstring Wire)
  | .oneQubit wire atom => singleQubitLift wire (atom.eval theta)
  | .xor control target hdistinct => registerXorGate control target hdistinct

private theorem exists_registerAtom_eq_of_mem
    (theta : Real) {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (gate : UnitaryGate (Bitstring Wire))
    (hgate : gate ∈
      finiteRegisterGenerators (Wire := Wire) (cliffordPhaseGenerators theta)) :
    ∃ atom : BK05RegisterAtom theta Wire, atom.eval = gate := by
  rcases hgate with hlocal | hxor
  · rcases hlocal with ⟨wire, sourceGate, hsource, rfl⟩
    rcases exists_phaseAtom_eq_of_mem theta sourceGate hsource with
      ⟨atom, hatom⟩
    exact ⟨.oneQubit wire atom, congrArg (singleQubitLift wire) hatom⟩
  · rcases hxor with ⟨control, target, hdistinct, rfl⟩
    exact ⟨.xor control target hdistinct, rfl⟩

/- A finite algebraic word over the actual finite-register generator set. -/
private inductive BK05RegisterWord
    (theta : Real) (Wire : Type) [Fintype Wire] [DecidableEq Wire] where
  | one : BK05RegisterWord theta Wire
  | atom (gate : BK05RegisterAtom theta Wire) : BK05RegisterWord theta Wire
  | mul (left right : BK05RegisterWord theta Wire) : BK05RegisterWord theta Wire
  | inverse (word : BK05RegisterWord theta Wire) : BK05RegisterWord theta Wire

private noncomputable def BK05RegisterWord.eval
    {theta : Real} {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    BK05RegisterWord theta Wire → UnitaryGate (Bitstring Wire)
  | .one => 1
  | .atom registerAtom => registerAtom.eval
  | .mul left right => left.eval * right.eval
  | .inverse word => word.eval⁻¹

private theorem generatedFiniteRegister_exists_word
    (theta : Real) {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    {gate : UnitaryGate (Bitstring Wire)}
    (hgate : gate ∈ generatedUnitarySubgroup
      (finiteRegisterGenerators (Wire := Wire)
        (cliffordPhaseGenerators theta))) :
    ∃ word : BK05RegisterWord theta Wire, word.eval = gate := by
  change gate ∈ Subgroup.closure
    (finiteRegisterGenerators (Wire := Wire) (cliffordPhaseGenerators theta))
    at hgate
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hgate
  · intro sourceGate hsourceGate
    rcases exists_registerAtom_eq_of_mem theta sourceGate hsourceGate with
      ⟨registerAtom, hatom⟩
    exact ⟨.atom registerAtom, hatom⟩
  · exact ⟨.one, rfl⟩
  · intro left right _ _ hleft hright
    rcases hleft with ⟨leftWord, rfl⟩
    rcases hright with ⟨rightWord, rfl⟩
    exact ⟨.mul leftWord rightWord, rfl⟩
  · intro sourceGate _ hsourceGate
    rcases hsourceGate with ⟨word, rfl⟩
    exact ⟨.inverse word, rfl⟩

/- Projective density on one-qubit atoms lifts to an actual finite register
word close to a phase-equivalent representative of the requested circuit. -/
private theorem projectivelyGeneratedDense_exists_registerWord_matrix_close
    (theta : Real) {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (hdense : ProjectivelyGeneratedDense (cliffordPhaseGenerators theta))
    (circuit : FiniteRegisterCircuit Wire) (ε : Real) (hε : 0 < ε) :
    ∃ representative : UnitaryGate (Bitstring Wire),
      GlobalPhaseEquivalent circuit.unitary representative ∧
      ∃ word : BK05RegisterWord theta Wire,
        ‖(word.eval : Matrix (Bitstring Wire) (Bitstring Wire) Complex) -
          (representative : Matrix (Bitstring Wire) (Bitstring Wire) Complex)‖ < ε := by
  rcases finiteRegisterCircuit_has_projectiveClosureRepresentative
    (cliffordPhaseGenerators theta) hdense circuit with
    ⟨representative, hclosure, hphase⟩
  change representative ∈ closure
    (generatedUnitarySubgroup
      (finiteRegisterGenerators (Wire := Wire)
        (cliffordPhaseGenerators theta)) :
      Set (UnitaryGate (Bitstring Wire))) at hclosure
  rcases (Metric.mem_closure_iff.mp hclosure) ε hε with
    ⟨candidate, hcandidate, hdist⟩
  rcases generatedFiniteRegister_exists_word theta hcandidate with
    ⟨word, hword⟩
  refine ⟨representative, hphase, word, ?_⟩
  rw [← hword] at hdist
  calc
    ‖(word.eval : Matrix (Bitstring Wire) (Bitstring Wire) Complex) -
        (representative : Matrix (Bitstring Wire) (Bitstring Wire) Complex)‖ =
      ‖(representative : Matrix (Bitstring Wire) (Bitstring Wire) Complex) -
        (word.eval : Matrix (Bitstring Wire) (Bitstring Wire) Complex)‖ :=
      norm_sub_rev _ _
    _ = dist representative word.eval := by
      rw [Subtype.dist_eq, dist_eq_norm]
    _ < ε := hdist

private theorem registerXorBitstringEquiv_inv
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (control target : Wire) (hdistinct : control ≠ target) :
    (registerXorBitstringEquiv control target hdistinct)⁻¹ =
      registerXorBitstringEquiv control target hdistinct := by
  apply Equiv.ext
  intro bits
  rfl

private theorem registerXorGate_inv
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (control target : Wire) (hdistinct : control ≠ target) :
    (registerXorGate control target hdistinct)⁻¹ =
      registerXorGate control target hdistinct := by
  apply Subtype.ext
  change
    ((registerXorBitstringEquiv control target hdistinct).permMatrix Complex).conjTranspose =
      (registerXorBitstringEquiv control target hdistinct).permMatrix Complex
  rw [Matrix.conjTranspose_permMatrix, registerXorBitstringEquiv_inv]

private noncomputable def BK05RegisterWord.orientedEval
    {theta : Real} {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (word : BK05RegisterWord theta Wire) :
    BK05WordPolarity → UnitaryGate (Bitstring Wire)
  | .normal => word.eval
  | .inverse => word.eval⁻¹

private def BK05SignedPhaseLetter.ofPolarity
    {theta : Real} (atom : BK05PhaseAtom theta) :
    BK05WordPolarity → BK05SignedPhaseLetter theta
  | .normal => .positive atom
  | .inverse => .negative atom

/- Compile a register word through one actual H-type resource per selected
one-qubit atom.  Products are reversed at syntax level to preserve execution
order, exactly as for the earlier ideal word compiler. -/
private noncomputable def BK05RegisterWord.compileH
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (resource : DensityOperator QubitSpace) (blocks : Nat) :
    BK05RegisterWord (-Real.pi / 4) Wire → BK05WordPolarity →
      BK05PhysicalRegisterCircuit Wire
  | .one, _ => .identity
  | .atom (.oneQubit wire phaseAtom), polarity =>
      .word wire (.h resource blocks
        [BK05SignedPhaseLetter.ofPolarity phaseAtom polarity])
  | .atom (.xor control target hdistinct), _ =>
      .xor control target hdistinct
  | .mul left right, .normal =>
      .compose (right.compileH resource blocks .normal)
        (left.compileH resource blocks .normal)
  | .mul left right, .inverse =>
      .compose (left.compileH resource blocks .inverse)
        (right.compileH resource blocks .inverse)
  | .inverse word, polarity => word.compileH resource blocks polarity.flip

private noncomputable def BK05RegisterWord.compileT
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (resource : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    BK05RegisterWord (-Real.pi / 6) Wire → BK05WordPolarity →
      BK05PhysicalRegisterCircuit Wire
  | .one, _ => .identity
  | .atom (.oneQubit wire phaseAtom), polarity =>
      .word wire (.t resource pairAttempts blocks
        [BK05SignedPhaseLetter.ofPolarity phaseAtom polarity])
  | .atom (.xor control target hdistinct), _ =>
      .xor control target hdistinct
  | .mul left right, .normal =>
      .compose (right.compileT resource pairAttempts blocks .normal)
        (left.compileT resource pairAttempts blocks .normal)
  | .mul left right, .inverse =>
      .compose (left.compileT resource pairAttempts blocks .inverse)
        (right.compileT resource pairAttempts blocks .inverse)
  | .inverse word, polarity =>
      word.compileT resource pairAttempts blocks polarity.flip

private theorem BK05RegisterWord.compileH_target_unitary
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (resource : DensityOperator QubitSpace) (blocks : Nat) :
    ∀ (word : BK05RegisterWord (-Real.pi / 4) Wire)
      (polarity : BK05WordPolarity),
      (word.compileH resource blocks polarity).targetCircuit.unitary =
        word.orientedEval polarity := by
  intro word
  induction word with
  | one =>
      intro polarity
      cases polarity <;>
        simp [BK05RegisterWord.compileH,
          BK05PhysicalRegisterCircuit.targetCircuit,
          BK05RegisterWord.orientedEval, BK05RegisterWord.eval]
  | atom registerAtom =>
      intro polarity
      cases registerAtom with
      | oneQubit wire sourceAtom =>
          cases polarity with
          | normal =>
              simp [BK05RegisterWord.compileH,
                BK05PhysicalRegisterCircuit.targetCircuit,
                BK05WordCompilation.targetGate,
                BK05SignedPhaseLetter.evalList,
                BK05SignedPhaseLetter.ofPolarity,
                BK05RegisterWord.orientedEval, BK05RegisterWord.eval,
                BK05RegisterAtom.eval, BK05SignedPhaseLetter.eval]
          | inverse =>
              simpa [BK05RegisterWord.compileH,
                BK05PhysicalRegisterCircuit.targetCircuit,
                BK05WordCompilation.targetGate,
                BK05SignedPhaseLetter.evalList,
                BK05SignedPhaseLetter.ofPolarity,
                BK05RegisterWord.orientedEval, BK05RegisterWord.eval,
                BK05RegisterAtom.eval, BK05SignedPhaseLetter.eval] using
                  singleQubitLift_inv wire
                    (BK05PhaseAtom.eval (-Real.pi / 4) sourceAtom)
      | xor control target hdistinct =>
          cases polarity with
          | normal =>
              simp [BK05RegisterWord.compileH,
                BK05PhysicalRegisterCircuit.targetCircuit,
                BK05RegisterWord.orientedEval, BK05RegisterWord.eval,
                BK05RegisterAtom.eval]
          | inverse =>
              simpa [BK05RegisterWord.compileH,
                BK05PhysicalRegisterCircuit.targetCircuit,
                BK05RegisterWord.orientedEval, BK05RegisterWord.eval,
                BK05RegisterAtom.eval] using
                  (registerXorGate_inv control target hdistinct).symm
  | mul left right ihLeft ihRight =>
      intro polarity
      cases polarity with
      | normal =>
          simp only [BK05RegisterWord.compileH,
            BK05PhysicalRegisterCircuit.targetCircuit,
            FiniteRegisterCircuit.unitary_compose,
            BK05RegisterWord.orientedEval, BK05RegisterWord.eval]
          rw [ihLeft .normal, ihRight .normal]
          rfl
      | inverse =>
          simp only [BK05RegisterWord.compileH,
            BK05PhysicalRegisterCircuit.targetCircuit,
            FiniteRegisterCircuit.unitary_compose,
            BK05RegisterWord.orientedEval, BK05RegisterWord.eval]
          rw [ihRight .inverse, ihLeft .inverse]
          exact (mul_inv_rev _ _).symm
  | inverse word ih =>
      intro polarity
      cases polarity with
      | normal =>
          simpa [BK05RegisterWord.compileH, BK05RegisterWord.orientedEval,
            BK05RegisterWord.eval, BK05WordPolarity.flip] using ih .inverse
      | inverse =>
          simpa [BK05RegisterWord.compileH, BK05RegisterWord.orientedEval,
            BK05RegisterWord.eval, BK05WordPolarity.flip] using ih .normal

private theorem BK05RegisterWord.compileT_target_unitary
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (resource : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    ∀ (word : BK05RegisterWord (-Real.pi / 6) Wire)
      (polarity : BK05WordPolarity),
      (word.compileT resource pairAttempts blocks polarity).targetCircuit.unitary =
        word.orientedEval polarity := by
  intro word
  induction word with
  | one =>
      intro polarity
      cases polarity <;>
        simp [BK05RegisterWord.compileT,
          BK05PhysicalRegisterCircuit.targetCircuit,
          BK05RegisterWord.orientedEval, BK05RegisterWord.eval]
  | atom registerAtom =>
      intro polarity
      cases registerAtom with
      | oneQubit wire sourceAtom =>
          cases polarity with
          | normal =>
              simp [BK05RegisterWord.compileT,
                BK05PhysicalRegisterCircuit.targetCircuit,
                BK05WordCompilation.targetGate,
                BK05SignedPhaseLetter.evalList,
                BK05SignedPhaseLetter.ofPolarity,
                BK05RegisterWord.orientedEval, BK05RegisterWord.eval,
                BK05RegisterAtom.eval, BK05SignedPhaseLetter.eval]
          | inverse =>
              simpa [BK05RegisterWord.compileT,
                BK05PhysicalRegisterCircuit.targetCircuit,
                BK05WordCompilation.targetGate,
                BK05SignedPhaseLetter.evalList,
                BK05SignedPhaseLetter.ofPolarity,
                BK05RegisterWord.orientedEval, BK05RegisterWord.eval,
                BK05RegisterAtom.eval, BK05SignedPhaseLetter.eval] using
                  singleQubitLift_inv wire
                    (BK05PhaseAtom.eval (-Real.pi / 6) sourceAtom)
      | xor control target hdistinct =>
          cases polarity with
          | normal =>
              simp [BK05RegisterWord.compileT,
                BK05PhysicalRegisterCircuit.targetCircuit,
                BK05RegisterWord.orientedEval, BK05RegisterWord.eval,
                BK05RegisterAtom.eval]
          | inverse =>
              simpa [BK05RegisterWord.compileT,
                BK05PhysicalRegisterCircuit.targetCircuit,
                BK05RegisterWord.orientedEval, BK05RegisterWord.eval,
                BK05RegisterAtom.eval] using
                  (registerXorGate_inv control target hdistinct).symm
  | mul left right ihLeft ihRight =>
      intro polarity
      cases polarity with
      | normal =>
          simp only [BK05RegisterWord.compileT,
            BK05PhysicalRegisterCircuit.targetCircuit,
            FiniteRegisterCircuit.unitary_compose,
            BK05RegisterWord.orientedEval, BK05RegisterWord.eval]
          rw [ihLeft .normal, ihRight .normal]
          rfl
      | inverse =>
          simp only [BK05RegisterWord.compileT,
            BK05PhysicalRegisterCircuit.targetCircuit,
            FiniteRegisterCircuit.unitary_compose,
            BK05RegisterWord.orientedEval, BK05RegisterWord.eval]
          rw [ihRight .inverse, ihLeft .inverse]
          exact (mul_inv_rev _ _).symm
  | inverse word ih =>
      intro polarity
      cases polarity with
      | normal =>
          simpa [BK05RegisterWord.compileT, BK05RegisterWord.orientedEval,
            BK05RegisterWord.eval, BK05WordPolarity.flip] using ih .inverse
      | inverse =>
          simpa [BK05RegisterWord.compileT, BK05RegisterWord.orientedEval,
            BK05RegisterWord.eval, BK05WordPolarity.flip] using ih .normal

/- Physical register syntax is source-certified only when each noisy word uses
an actual output of the corresponding finite BK05/BK15 schedule.  This is an
inductive provenance judgment, not a caller-supplied approximation claim. -/
private inductive BK05PhysicalRegisterCircuit.SourceCertified
    (rho : DensityOperator QubitSpace)
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    BK05PhysicalRegisterCircuit Wire → Prop where
  | identity : SourceCertified rho .identity
  | hWord (wire : Wire) (rounds blocks : Nat)
      (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) :
      SourceCertified rho
        (.word wire (.h
          (BK15.Threshold.bk15AcceptedRunHOutput rho rounds) blocks letters))
  | tWord (wire : Wire)
      (hthreshold : tInitialError rho < BK05T.bk05TThreshold)
      (rounds pairAttempts blocks : Nat)
      (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) :
      SourceCertified rho
        (.word wire (.t
          (BK05TSemanticSchedule.rootOutput
            (bk05TCompleteSemanticSchedule rho hthreshold rounds))
          pairAttempts blocks letters))
  | xor (control target : Wire) (hdistinct : control ≠ target) :
      SourceCertified rho (.xor control target hdistinct)
  | compose {first second : BK05PhysicalRegisterCircuit Wire}
      (hfirst : SourceCertified rho first)
      (hsecond : SourceCertified rho second) :
      SourceCertified rho (.compose first second)

/- A nonnegative multiple of a geometric tail can be made smaller than any
positive tolerance.  This is the only asymptotic choice used below; every
chosen compiler is still finite. -/
private theorem exists_nat_scaled_pow_lt
    (scale ratio epsilon : Real)
    (hscale : 0 ≤ scale) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hepsilon : 0 < epsilon) :
    ∃ n : Nat, scale * ratio ^ n < epsilon := by
  have hpow : Filter.Tendsto (fun n : Nat => ratio ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio1
  have hscaled : Filter.Tendsto (fun n : Nat => scale * ratio ^ n)
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul hpow)
  rcases Metric.tendsto_atTop.mp hscaled epsilon hepsilon with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  have hdist := hN N le_rfl
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (mul_nonneg hscale (pow_nonneg hratio0 N))] at hdist
  exact hdist

/- One H-route register atom has a finite, source-certified implementation at
arbitrarily small aggregate error.  Clifford and XOR atoms are exact; the
phase atom chooses both a finite stopping depth and an actual BK15 output. -/
private theorem exists_h_registerAtom_compiler
    (rho : DensityOperator QubitSpace)
    (hfidelity : BK15.Threshold.FStar < hFidelity rho)
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (registerAtom : BK05RegisterAtom (-Real.pi / 4) Wire)
    (polarity : BK05WordPolarity)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ physical : BK05PhysicalRegisterCircuit Wire,
      physical.SourceCertified rho ∧
      physical.targetCircuit.unitary =
        (BK05RegisterWord.atom registerAtom).orientedEval polarity ∧
      physical.errorBudget < epsilon := by
  cases registerAtom with
  | xor control target hdistinct =>
      refine ⟨.xor control target hdistinct,
        .xor control target hdistinct, ?_, ?_⟩
      · cases polarity with
        | normal => rfl
        | inverse =>
            exact (registerXorGate_inv control target hdistinct).symm
      · simpa [BK05PhysicalRegisterCircuit.errorBudget] using hepsilon
  | oneQubit wire sourceAtom =>
      cases sourceAtom with
      | h =>
          let resource := BK15.Threshold.bk15AcceptedRunHOutput rho 0
          let physical :=
            (BK05RegisterWord.atom
              (BK05RegisterAtom.oneQubit wire
                (BK05PhaseAtom.h : BK05PhaseAtom (-Real.pi / 4)))).compileH
              resource 0 polarity
          refine ⟨physical, ?_, ?_, ?_⟩
          · cases polarity <;>
              exact BK05PhysicalRegisterCircuit.SourceCertified.hWord wire 0 0 _
          · exact BK05RegisterWord.compileH_target_unitary resource 0 _ polarity
          · cases polarity <;>
              simpa [physical, BK05RegisterWord.compileH,
                BK05PhysicalRegisterCircuit.errorBudget,
                compileWordRegisterErrorBound,
                BK05WordCompilation.localErrorBudget, hWordErrorBudget,
                BK05SignedPhaseLetter.ofPolarity,
                BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using hepsilon
      | k =>
          let resource := BK15.Threshold.bk15AcceptedRunHOutput rho 0
          let physical :=
            (BK05RegisterWord.atom
              (BK05RegisterAtom.oneQubit wire
                (BK05PhaseAtom.k : BK05PhaseAtom (-Real.pi / 4)))).compileH
              resource 0 polarity
          refine ⟨physical, ?_, ?_, ?_⟩
          · cases polarity <;>
              exact BK05PhysicalRegisterCircuit.SourceCertified.hWord wire 0 0 _
          · exact BK05RegisterWord.compileH_target_unitary resource 0 _ polarity
          · cases polarity <;>
              simpa [physical, BK05RegisterWord.compileH,
                BK05PhysicalRegisterCircuit.errorBudget,
                compileWordRegisterErrorBound,
                BK05WordCompilation.localErrorBudget, hWordErrorBudget,
                BK05SignedPhaseLetter.ofPolarity,
                BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using hepsilon
      | phase =>
          let scale := selectedWireErrorScale wire
          have hscale : 0 ≤ scale := selectedWireErrorScale_nonneg wire
          rcases exists_nat_scaled_pow_lt (2 * scale) (255 / 256) (epsilon / 2)
            (mul_nonneg (by norm_num) hscale) (by norm_num) (by norm_num)
            (by linarith) with ⟨blocks, htail⟩
          let coefficient : Real := scale * (8 * blocks : Nat)
          have hcoefficient : 0 ≤ coefficient := by
            dsimp only [coefficient]
            positivity
          let eta : Real := epsilon / (2 * (coefficient + 1))
          have heta : 0 < eta := by
            dsimp only [eta]
            positivity
          rcases bk15HProducesTraceCloseResource rho hfidelity eta heta with
            ⟨rounds, hresource, _⟩
          let resource := BK15.Threshold.bk15AcceptedRunHOutput rho rounds
          let physical :=
            (BK05RegisterWord.atom
              (BK05RegisterAtom.oneQubit wire
                (BK05PhaseAtom.phase : BK05PhaseAtom (-Real.pi / 4)))).compileH
              resource blocks polarity
          have hsource :
              coefficient * traceNorm (resource.toOperator - hMagicState.toOperator) <
                epsilon / 2 := by
            have hle : coefficient *
                  traceNorm (resource.toOperator - hMagicState.toOperator) ≤
                (coefficient + 1) *
                  traceNorm (resource.toOperator - hMagicState.toOperator) := by
              exact mul_le_mul_of_nonneg_right (by linarith)
                (traceNorm_nonneg _)
            have hlt :
                (coefficient + 1) *
                    traceNorm (resource.toOperator - hMagicState.toOperator) <
                  (coefficient + 1) * eta :=
              mul_lt_mul_of_pos_left hresource (by linarith)
            have heq : (coefficient + 1) * eta = epsilon / 2 := by
              dsimp only [eta]
              field_simp
            exact hle.trans_lt (hlt.trans_eq heq)
          refine ⟨physical, ?_, ?_, ?_⟩
          · cases polarity <;>
              exact BK05PhysicalRegisterCircuit.SourceCertified.hWord
                wire rounds blocks _
          · exact BK05RegisterWord.compileH_target_unitary
              resource blocks _ polarity
          · cases polarity <;>
              simp only [physical, BK05RegisterWord.compileH,
                BK05PhysicalRegisterCircuit.errorBudget,
                compileWordRegisterErrorBound,
                BK05WordCompilation.localErrorBudget, hWordErrorBudget,
                BK05SignedPhaseLetter.ofPolarity,
                BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost, Nat.cast_one, mul_one,
                Nat.mul_one] <;>
              dsimp only [coefficient, scale] at hsource htail ⊢ <;>
              norm_num [Nat.cast_mul, Nat.cast_add] at hsource htail ⊢ <;>
              nlinarith

/- The T-route analogue also chooses a finite fresh-pair retry budget.  Its
two geometric stopping tails and source-state perturbation are each assigned
one third of the requested local tolerance. -/
private theorem exists_t_registerAtom_compiler
    (rho : DensityOperator QubitSpace)
    (hfidelity : BK05T.bk05TFidelityThreshold < tFidelity rho)
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (registerAtom : BK05RegisterAtom (-Real.pi / 6) Wire)
    (polarity : BK05WordPolarity)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ physical : BK05PhysicalRegisterCircuit Wire,
      physical.SourceCertified rho ∧
      physical.targetCircuit.unitary =
        (BK05RegisterWord.atom registerAtom).orientedEval polarity ∧
      physical.errorBudget < epsilon := by
  let hthreshold : tInitialError rho < BK05T.bk05TThreshold :=
    (BK05T.bk05TFidelityError_lt_threshold_iff rho).mpr hfidelity
  cases registerAtom with
  | xor control target hdistinct =>
      refine ⟨.xor control target hdistinct,
        .xor control target hdistinct, ?_, ?_⟩
      · cases polarity with
        | normal => rfl
        | inverse =>
            exact (registerXorGate_inv control target hdistinct).symm
      · simpa [BK05PhysicalRegisterCircuit.errorBudget] using hepsilon
  | oneQubit wire sourceAtom =>
      cases sourceAtom with
      | h =>
          let resource := BK05TSemanticSchedule.rootOutput
            (bk05TCompleteSemanticSchedule rho hthreshold 0)
          let physical :=
            (BK05RegisterWord.atom
              (BK05RegisterAtom.oneQubit wire
                (BK05PhaseAtom.h : BK05PhaseAtom (-Real.pi / 6)))).compileT
              resource 0 0 polarity
          refine ⟨physical, ?_, ?_, ?_⟩
          · cases polarity <;>
              exact BK05PhysicalRegisterCircuit.SourceCertified.tWord
                wire hthreshold 0 0 0 _
          · exact BK05RegisterWord.compileT_target_unitary resource 0 0 _ polarity
          · cases polarity <;>
              simpa [physical, BK05RegisterWord.compileT,
                BK05PhysicalRegisterCircuit.errorBudget,
                compileWordRegisterErrorBound,
                BK05WordCompilation.localErrorBudget, tWordErrorBudget,
                BK05SignedPhaseLetter.ofPolarity,
                BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using hepsilon
      | k =>
          let resource := BK05TSemanticSchedule.rootOutput
            (bk05TCompleteSemanticSchedule rho hthreshold 0)
          let physical :=
            (BK05RegisterWord.atom
              (BK05RegisterAtom.oneQubit wire
                (BK05PhaseAtom.k : BK05PhaseAtom (-Real.pi / 6)))).compileT
              resource 0 0 polarity
          refine ⟨physical, ?_, ?_, ?_⟩
          · cases polarity <;>
              exact BK05PhysicalRegisterCircuit.SourceCertified.tWord
                wire hthreshold 0 0 0 _
          · exact BK05RegisterWord.compileT_target_unitary resource 0 0 _ polarity
          · cases polarity <;>
              simpa [physical, BK05RegisterWord.compileT,
                BK05PhysicalRegisterCircuit.errorBudget,
                compileWordRegisterErrorBound,
                BK05WordCompilation.localErrorBudget, tWordErrorBudget,
                BK05SignedPhaseLetter.ofPolarity,
                BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost] using hepsilon
      | phase =>
          let scale := selectedWireErrorScale wire
          have hscale : 0 ≤ scale := selectedWireErrorScale_nonneg wire
          rcases exists_nat_scaled_pow_lt (2 * scale) (4095 / 4096)
            (epsilon / 3) (mul_nonneg (by norm_num) hscale)
            (by norm_num) (by norm_num) (by linarith) with
            ⟨blocks, hphaseTail⟩
          rcases exists_nat_scaled_pow_lt
            (2 * scale * (12 * blocks : Nat)) (1 / 3) (epsilon / 3)
            (by positivity) (by norm_num) (by norm_num) (by linarith) with
            ⟨pairAttempts, hpairTail⟩
          let coefficient : Real :=
            scale * (2 * pairAttempts * 12 * blocks : Nat)
          have hcoefficient : 0 ≤ coefficient := by
            dsimp only [coefficient]
            positivity
          let eta : Real := epsilon / (3 * (coefficient + 1))
          have heta : 0 < eta := by
            dsimp only [eta]
            positivity
          rcases bk05TProducesTraceCloseResource rho hfidelity eta heta with
            ⟨rounds, hresource, _⟩
          let resource := BK05TSemanticSchedule.rootOutput
            (bk05TCompleteSemanticSchedule rho hthreshold rounds)
          let physical :=
            (BK05RegisterWord.atom
              (BK05RegisterAtom.oneQubit wire
                (BK05PhaseAtom.phase : BK05PhaseAtom (-Real.pi / 6)))).compileT
              resource pairAttempts blocks polarity
          have hsource :
              coefficient * traceNorm (resource.toOperator - tMagicState.toOperator) <
                epsilon / 3 := by
            have hle : coefficient *
                  traceNorm (resource.toOperator - tMagicState.toOperator) ≤
                (coefficient + 1) *
                  traceNorm (resource.toOperator - tMagicState.toOperator) := by
              exact mul_le_mul_of_nonneg_right (by linarith)
                (traceNorm_nonneg _)
            have hlt :
                (coefficient + 1) *
                    traceNorm (resource.toOperator - tMagicState.toOperator) <
                  (coefficient + 1) * eta :=
              mul_lt_mul_of_pos_left hresource (by linarith)
            have heq : (coefficient + 1) * eta = epsilon / 3 := by
              dsimp only [eta]
              field_simp
            exact hle.trans_lt (hlt.trans_eq heq)
          refine ⟨physical, ?_, ?_, ?_⟩
          · cases polarity <;>
              exact BK05PhysicalRegisterCircuit.SourceCertified.tWord
                wire hthreshold rounds pairAttempts blocks _
          · exact BK05RegisterWord.compileT_target_unitary
              resource pairAttempts blocks _ polarity
          · cases polarity <;>
              simp only [physical, BK05RegisterWord.compileT,
                BK05PhysicalRegisterCircuit.errorBudget,
                compileWordRegisterErrorBound,
                BK05WordCompilation.localErrorBudget, tWordErrorBudget,
                BK05SignedPhaseLetter.ofPolarity,
                BK05SignedPhaseLetter.resourceCount,
                BK05SignedPhaseLetter.phaseCost, Nat.cast_one, mul_one,
                Nat.mul_one] <;>
              dsimp only [coefficient, scale]
                at hsource hphaseTail hpairTail ⊢ <;>
              norm_num [Nat.cast_mul, Nat.cast_add]
                at hsource hphaseTail hpairTail ⊢ <;>
              nlinarith

/- Structural words compose the independently finite atom implementations.
Execution order is encoded by `BK05PhysicalRegisterCircuit.compose`; an
inverse pass reverses multiplication rather than assuming an inverse channel. -/
private theorem exists_h_registerWord_compiler
    (rho : DensityOperator QubitSpace)
    (hfidelity : BK15.Threshold.FStar < hFidelity rho)
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    ∀ (word : BK05RegisterWord (-Real.pi / 4) Wire)
      (polarity : BK05WordPolarity)
      (epsilon : Real), 0 < epsilon →
      ∃ physical : BK05PhysicalRegisterCircuit Wire,
        physical.SourceCertified rho ∧
        physical.targetCircuit.unitary = word.orientedEval polarity ∧
        physical.errorBudget < epsilon := by
  intro word
  induction word with
  | one =>
      intro polarity epsilon hepsilon
      refine ⟨.identity, .identity, ?_, ?_⟩
      · cases polarity <;>
          simp [BK05PhysicalRegisterCircuit.targetCircuit,
            BK05RegisterWord.orientedEval, BK05RegisterWord.eval]
      · simpa [BK05PhysicalRegisterCircuit.errorBudget] using hepsilon
  | atom registerAtom =>
      intro polarity epsilon hepsilon
      exact exists_h_registerAtom_compiler rho hfidelity registerAtom polarity
        epsilon hepsilon
  | mul left right ihLeft ihRight =>
      intro polarity epsilon hepsilon
      have hhalf : 0 < epsilon / 2 := by linarith
      cases polarity with
      | normal =>
          rcases ihRight .normal (epsilon / 2) hhalf with
            ⟨physicalRight, hsourceRight, htargetRight, herrorRight⟩
          rcases ihLeft .normal (epsilon / 2) hhalf with
            ⟨physicalLeft, hsourceLeft, htargetLeft, herrorLeft⟩
          refine ⟨.compose physicalRight physicalLeft,
            .compose hsourceRight hsourceLeft, ?_, ?_⟩
          · simp only [BK05PhysicalRegisterCircuit.targetCircuit,
              FiniteRegisterCircuit.unitary_compose,
              BK05RegisterWord.orientedEval, BK05RegisterWord.eval]
            rw [htargetLeft, htargetRight]
            simp [BK05RegisterWord.orientedEval]
          · simp only [BK05PhysicalRegisterCircuit.errorBudget]
            linarith
      | inverse =>
          rcases ihLeft .inverse (epsilon / 2) hhalf with
            ⟨physicalLeft, hsourceLeft, htargetLeft, herrorLeft⟩
          rcases ihRight .inverse (epsilon / 2) hhalf with
            ⟨physicalRight, hsourceRight, htargetRight, herrorRight⟩
          refine ⟨.compose physicalLeft physicalRight,
            .compose hsourceLeft hsourceRight, ?_, ?_⟩
          · simp only [BK05PhysicalRegisterCircuit.targetCircuit,
              FiniteRegisterCircuit.unitary_compose,
              BK05RegisterWord.orientedEval, BK05RegisterWord.eval]
            rw [htargetRight, htargetLeft]
            exact (mul_inv_rev _ _).symm
          · simp only [BK05PhysicalRegisterCircuit.errorBudget]
            linarith
  | inverse word ih =>
      intro polarity epsilon hepsilon
      rcases ih polarity.flip epsilon hepsilon with
        ⟨physical, hsource, htarget, herror⟩
      refine ⟨physical, hsource, ?_, herror⟩
      cases polarity <;>
        simpa [BK05RegisterWord.orientedEval, BK05RegisterWord.eval,
          BK05WordPolarity.flip] using htarget

private theorem exists_t_registerWord_compiler
    (rho : DensityOperator QubitSpace)
    (hfidelity : BK05T.bk05TFidelityThreshold < tFidelity rho)
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    ∀ (word : BK05RegisterWord (-Real.pi / 6) Wire)
      (polarity : BK05WordPolarity)
      (epsilon : Real), 0 < epsilon →
      ∃ physical : BK05PhysicalRegisterCircuit Wire,
        physical.SourceCertified rho ∧
        physical.targetCircuit.unitary = word.orientedEval polarity ∧
        physical.errorBudget < epsilon := by
  intro word
  induction word with
  | one =>
      intro polarity epsilon hepsilon
      refine ⟨.identity, .identity, ?_, ?_⟩
      · cases polarity <;>
          simp [BK05PhysicalRegisterCircuit.targetCircuit,
            BK05RegisterWord.orientedEval, BK05RegisterWord.eval]
      · simpa [BK05PhysicalRegisterCircuit.errorBudget] using hepsilon
  | atom registerAtom =>
      intro polarity epsilon hepsilon
      exact exists_t_registerAtom_compiler rho hfidelity registerAtom polarity
        epsilon hepsilon
  | mul left right ihLeft ihRight =>
      intro polarity epsilon hepsilon
      have hhalf : 0 < epsilon / 2 := by linarith
      cases polarity with
      | normal =>
          rcases ihRight .normal (epsilon / 2) hhalf with
            ⟨physicalRight, hsourceRight, htargetRight, herrorRight⟩
          rcases ihLeft .normal (epsilon / 2) hhalf with
            ⟨physicalLeft, hsourceLeft, htargetLeft, herrorLeft⟩
          refine ⟨.compose physicalRight physicalLeft,
            .compose hsourceRight hsourceLeft, ?_, ?_⟩
          · simp only [BK05PhysicalRegisterCircuit.targetCircuit,
              FiniteRegisterCircuit.unitary_compose,
              BK05RegisterWord.orientedEval, BK05RegisterWord.eval]
            rw [htargetLeft, htargetRight]
            simp [BK05RegisterWord.orientedEval]
          · simp only [BK05PhysicalRegisterCircuit.errorBudget]
            linarith
      | inverse =>
          rcases ihLeft .inverse (epsilon / 2) hhalf with
            ⟨physicalLeft, hsourceLeft, htargetLeft, herrorLeft⟩
          rcases ihRight .inverse (epsilon / 2) hhalf with
            ⟨physicalRight, hsourceRight, htargetRight, herrorRight⟩
          refine ⟨.compose physicalLeft physicalRight,
            .compose hsourceLeft hsourceRight, ?_, ?_⟩
          · simp only [BK05PhysicalRegisterCircuit.targetCircuit,
              FiniteRegisterCircuit.unitary_compose,
              BK05RegisterWord.orientedEval, BK05RegisterWord.eval]
            rw [htargetRight, htargetLeft]
            exact (mul_inv_rev _ _).symm
          · simp only [BK05PhysicalRegisterCircuit.errorBudget]
            linarith
  | inverse word ih =>
      intro polarity epsilon hepsilon
      rcases ih polarity.flip epsilon hepsilon with
        ⟨physical, hsource, htarget, herror⟩
      refine ⟨physical, hsource, ?_, herror⟩
      cases polarity <;>
        simpa [BK05RegisterWord.orientedEval, BK05RegisterWord.eval,
          BK05WordPolarity.flip] using htarget

private theorem compileFiniteRegisterCircuit_branch_nonempty
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    ∀ physical : BK05PhysicalRegisterCircuit Wire,
      Nonempty (compileFiniteRegisterCircuit physical).Branch := by
  intro physical
  induction physical with
  | identity => exact ⟨()⟩
  | word wire spec =>
      cases spec <;> exact ⟨Sum.inl none⟩
  | xor control target hdistinct => exact ⟨()⟩
  | compose first second hfirst hsecond =>
      rcases hfirst with ⟨firstBranch⟩
      rcases hsecond with ⟨secondBranch⟩
      exact ⟨(firstBranch, secondBranch)⟩

/- Failure labels from the first physical stage survive every later stage:
the compiler never conditions on or deletes a stopped branch. -/
private theorem compileFiniteRegisterCircuit_compose_retainsFailureLeaves
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (first second : BK05PhysicalRegisterCircuit Wire)
    (hfirst :
      (∃ branch : (compileFiniteRegisterCircuit first).Branch,
        (compileFiniteRegisterCircuit first).status branch =
          .stoppedPhaseExhausted) ∧
      (∃ branch : (compileFiniteRegisterCircuit first).Branch,
        (compileFiniteRegisterCircuit first).status branch =
          .stoppedTPairExhausted)) :
    (∃ branch : (compileFiniteRegisterCircuit (.compose first second)).Branch,
      (compileFiniteRegisterCircuit (.compose first second)).status branch =
        .stoppedPhaseExhausted) ∧
    (∃ branch : (compileFiniteRegisterCircuit (.compose first second)).Branch,
      (compileFiniteRegisterCircuit (.compose first second)).status branch =
        .stoppedTPairExhausted) := by
  rcases hfirst with ⟨⟨phaseBranch, hphase⟩, ⟨pairBranch, hpair⟩⟩
  rcases compileFiniteRegisterCircuit_branch_nonempty second with
    ⟨secondBranch⟩
  constructor
  · refine ⟨(phaseBranch, secondBranch), ?_⟩
    change
      ((compileFiniteRegisterCircuit first).status phaseBranch).thenStatus
          ((compileFiniteRegisterCircuit second).status secondBranch) =
        .stoppedPhaseExhausted
    rw [hphase]
    rfl
  · refine ⟨(pairBranch, secondBranch), ?_⟩
    change
      ((compileFiniteRegisterCircuit first).status pairBranch).thenStatus
          ((compileFiniteRegisterCircuit second).status secondBranch) =
        .stoppedTPairExhausted
    rw [hpair]
    rfl

private theorem compiledAggregate_unconditioned_aggregate_traceNorm_lt
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (physical : BK05PhysicalRegisterCircuit Wire)
    (precision : Real) (hbudget : physical.errorBudget < precision)
    (input : DensityOperator (QubitRegister Wire)) :
    traceNorm
        ((compileFiniteRegisterCircuit physical).aggregateRaw input -
          physical.idealAggregate.aggregateRaw input) < precision :=
  (compileFiniteRegisterCircuit_actual_trace_bound physical input).trans_lt hbudget

private theorem compiledAggregate_target_traceNorm_lt
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (physical : BK05PhysicalRegisterCircuit Wire)
    (circuit : FiniteRegisterCircuit Wire)
    (representative : UnitaryGate (Bitstring Wire))
    (precision : Real)
    (hphase : GlobalPhaseEquivalent circuit.unitary representative)
    (hphysical : physical.errorBudget < precision / 2)
    (hmatrix :
      2 * (Fintype.card (Bitstring Wire × Bitstring Wire) : Real) *
          ‖(physical.targetCircuit.unitary :
              Matrix (Bitstring Wire) (Bitstring Wire) Complex) -
            (representative :
              Matrix (Bitstring Wire) (Bitstring Wire) Complex)‖ <
        precision / 2)
    (input : DensityOperator (QubitRegister Wire)) :
    traceNorm
        ((compileFiniteRegisterCircuit physical).aggregateRaw input -
          (exactGateAggregate circuit.unitary).aggregateRaw input) < precision := by
  have hactual := compiledAggregate_unconditioned_aggregate_traceNorm_lt
    physical (precision / 2) hphysical input
  have hphaseChannel :=
    exactGateAggregate_globalPhase_aggregateRaw_eq hphase input
  have hmatrixLe :
      traceNorm
          ((exactGateAggregate physical.targetCircuit.unitary).aggregateRaw input -
            (exactGateAggregate representative).aggregateRaw input) ≤
        2 * (Fintype.card (Bitstring Wire × Bitstring Wire) : Real) *
          ‖(physical.targetCircuit.unitary :
              Matrix (Bitstring Wire) (Bitstring Wire) Complex) -
            (representative :
              Matrix (Bitstring Wire) (Bitstring Wire) Complex)‖ := by
    have hbound := finiteUnitaryKraus_difference_traceNorm_le
      physical.targetCircuit.unitary representative input.toOperator
    rw [input.traceNorm_eq_one, mul_one] at hbound
    exact hbound
  have hmatrixChannel :
      traceNorm
          (physical.idealAggregate.aggregateRaw input -
            (exactGateAggregate representative).aggregateRaw input) <
        precision / 2 := by
    rw [physical.idealAggregate_aggregateRaw_eq]
    exact hmatrixLe.trans_lt hmatrix
  rw [hphaseChannel]
  calc
    traceNorm
        ((compileFiniteRegisterCircuit physical).aggregateRaw input -
          (exactGateAggregate representative).aggregateRaw input) =
        traceNorm
          (((compileFiniteRegisterCircuit physical).aggregateRaw input -
              physical.idealAggregate.aggregateRaw input) +
            (physical.idealAggregate.aggregateRaw input -
              (exactGateAggregate representative).aggregateRaw input)) := by
      congr 1
      abel
    _ ≤ traceNorm
          ((compileFiniteRegisterCircuit physical).aggregateRaw input -
            physical.idealAggregate.aggregateRaw input) +
        traceNorm
          (physical.idealAggregate.aggregateRaw input -
            (exactGateAggregate representative).aggregateRaw input) :=
      traceNorm_add_le _ _
    _ < precision / 2 + precision / 2 := add_lt_add hactual hmatrixChannel
    _ = precision := by ring

private theorem finite_card_scaled_error_lt_half
    (dimension : Nat) (precision error : Real)
    (hprecision : 0 < precision)
    (herror :
      error < precision / (4 * ((dimension : Real) + 1))) :
    2 * (dimension : Real) * error < precision / 2 := by
  let delta : Real := precision / (4 * ((dimension : Real) + 1))
  have hdimension : 0 ≤ (dimension : Real) := by positivity
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hweak :
      2 * (dimension : Real) * error ≤
        2 * (dimension : Real) * delta :=
    mul_le_mul_of_nonneg_left herror.le (by positivity)
  have hstrict :
      2 * (dimension : Real) * delta <
        2 * ((dimension : Real) + 1) * delta := by
    nlinarith
  have heq :
      2 * ((dimension : Real) + 1) * delta = precision / 2 := by
    dsimp only [delta]
    field_simp
    ring
  exact hweak.trans_lt (hstrict.trans_eq heq)

/- A single actual phase word can be chosen uniformly for either sign.  These
explicit parameter witnesses are used only to add a cancelling phase pair,
ensuring the final aggregate visibly retains both stopping labels even when a
dense algebraic approximation happens to contain no phase atom. -/
private theorem exists_h_phase_parameters
    (rho : DensityOperator QubitSpace)
    (hfidelity : BK15.Threshold.FStar < hFidelity rho)
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ (rounds blocks : Nat),
      ∀ polarity : BK05WordPolarity,
        ((BK05RegisterWord.atom
          (BK05RegisterAtom.oneQubit wire
            (BK05PhaseAtom.phase : BK05PhaseAtom (-Real.pi / 4)))).compileH
          (BK15.Threshold.bk15AcceptedRunHOutput rho rounds) blocks polarity).errorBudget <
            epsilon := by
  let scale := selectedWireErrorScale wire
  have hscale : 0 ≤ scale := selectedWireErrorScale_nonneg wire
  rcases exists_nat_scaled_pow_lt (2 * scale) (255 / 256) (epsilon / 2)
    (mul_nonneg (by norm_num) hscale) (by norm_num) (by norm_num)
    (by linarith) with ⟨blocks, htail⟩
  let coefficient : Real := scale * (8 * blocks : Nat)
  have hcoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient]
    positivity
  let eta : Real := epsilon / (2 * (coefficient + 1))
  have heta : 0 < eta := by
    dsimp only [eta]
    positivity
  rcases bk15HProducesTraceCloseResource rho hfidelity eta heta with
    ⟨rounds, hresource, _⟩
  have hsource :
      coefficient * traceNorm
          ((BK15.Threshold.bk15AcceptedRunHOutput rho rounds).toOperator -
            hMagicState.toOperator) < epsilon / 2 := by
    have hle : coefficient * traceNorm
          ((BK15.Threshold.bk15AcceptedRunHOutput rho rounds).toOperator -
            hMagicState.toOperator) ≤
        (coefficient + 1) * traceNorm
          ((BK15.Threshold.bk15AcceptedRunHOutput rho rounds).toOperator -
            hMagicState.toOperator) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (traceNorm_nonneg _)
    have hlt :
        (coefficient + 1) * traceNorm
            ((BK15.Threshold.bk15AcceptedRunHOutput rho rounds).toOperator -
              hMagicState.toOperator) <
          (coefficient + 1) * eta :=
      mul_lt_mul_of_pos_left hresource (by linarith)
    have heq : (coefficient + 1) * eta = epsilon / 2 := by
      dsimp only [eta]
      field_simp
    exact hle.trans_lt (hlt.trans_eq heq)
  refine ⟨rounds, blocks, ?_⟩
  intro polarity
  cases polarity <;>
    simp only [BK05RegisterWord.compileH,
      BK05PhysicalRegisterCircuit.errorBudget,
      compileWordRegisterErrorBound,
      BK05WordCompilation.localErrorBudget, hWordErrorBudget,
      BK05SignedPhaseLetter.ofPolarity,
      BK05SignedPhaseLetter.resourceCount,
      BK05SignedPhaseLetter.phaseCost, Nat.cast_one, mul_one, Nat.mul_one] <;>
    dsimp only [coefficient, scale] at hsource htail ⊢ <;>
    norm_num [Nat.cast_mul, Nat.cast_add] at hsource htail ⊢ <;>
    nlinarith

private theorem exists_t_phase_parameters
    (rho : DensityOperator QubitSpace)
    (hfidelity : BK05T.bk05TFidelityThreshold < tFidelity rho)
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ (rounds pairAttempts blocks : Nat),
      ∀ polarity : BK05WordPolarity,
        ((BK05RegisterWord.atom
          (BK05RegisterAtom.oneQubit wire
            (BK05PhaseAtom.phase : BK05PhaseAtom (-Real.pi / 6)))).compileT
          (BK05TSemanticSchedule.rootOutput
            (bk05TCompleteSemanticSchedule rho
              ((BK05T.bk05TFidelityError_lt_threshold_iff rho).mpr hfidelity)
              rounds)) pairAttempts blocks polarity).errorBudget < epsilon := by
  let scale := selectedWireErrorScale wire
  have hscale : 0 ≤ scale := selectedWireErrorScale_nonneg wire
  rcases exists_nat_scaled_pow_lt (2 * scale) (4095 / 4096) (epsilon / 3)
    (mul_nonneg (by norm_num) hscale) (by norm_num) (by norm_num)
    (by linarith) with ⟨blocks, hphaseTail⟩
  rcases exists_nat_scaled_pow_lt
    (2 * scale * (12 * blocks : Nat)) (1 / 3) (epsilon / 3)
    (by positivity) (by norm_num) (by norm_num) (by linarith) with
    ⟨pairAttempts, hpairTail⟩
  let coefficient : Real :=
    scale * (2 * pairAttempts * 12 * blocks : Nat)
  have hcoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient]
    positivity
  let eta : Real := epsilon / (3 * (coefficient + 1))
  have heta : 0 < eta := by
    dsimp only [eta]
    positivity
  rcases bk05TProducesTraceCloseResource rho hfidelity eta heta with
    ⟨rounds, hresource, _⟩
  let resource := BK05TSemanticSchedule.rootOutput
    (bk05TCompleteSemanticSchedule rho
      ((BK05T.bk05TFidelityError_lt_threshold_iff rho).mpr hfidelity) rounds)
  have hsource :
      coefficient * traceNorm (resource.toOperator - tMagicState.toOperator) <
        epsilon / 3 := by
    have hle : coefficient *
          traceNorm (resource.toOperator - tMagicState.toOperator) ≤
        (coefficient + 1) *
          traceNorm (resource.toOperator - tMagicState.toOperator) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (traceNorm_nonneg _)
    have hlt :
        (coefficient + 1) *
            traceNorm (resource.toOperator - tMagicState.toOperator) <
          (coefficient + 1) * eta :=
      mul_lt_mul_of_pos_left hresource (by linarith)
    have heq : (coefficient + 1) * eta = epsilon / 3 := by
      dsimp only [eta]
      field_simp
    exact hle.trans_lt (hlt.trans_eq heq)
  refine ⟨rounds, pairAttempts, blocks, ?_⟩
  intro polarity
  cases polarity <;>
    simp only [BK05RegisterWord.compileT,
      BK05PhysicalRegisterCircuit.errorBudget,
      compileWordRegisterErrorBound,
      BK05WordCompilation.localErrorBudget, tWordErrorBudget,
      BK05SignedPhaseLetter.ofPolarity,
      BK05SignedPhaseLetter.resourceCount,
      BK05SignedPhaseLetter.phaseCost, Nat.cast_one, mul_one, Nat.mul_one] <;>
    dsimp only [resource, coefficient, scale]
      at hsource hphaseTail hpairTail ⊢ <;>
    norm_num [Nat.cast_mul, Nat.cast_add]
      at hsource hphaseTail hpairTail ⊢ <;>
    nlinarith

/- The public universality predicate packages only observable finite data and
proved properties: a phase-equivalent finite target, an actual source-backed
complete aggregate, computed ledgers, retained stopping leaves, and a uniform
unconditioned trace-norm bound for every register density. -/
private def BK05OperationalApproximation
    (rho : DensityOperator QubitSpace)
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (circuit : FiniteRegisterCircuit Wire) (precision : Real) : Prop :=
  ∃ (representative : UnitaryGate (Bitstring Wire))
      (physical : BK05PhysicalRegisterCircuit Wire),
    GlobalPhaseEquivalent circuit.unitary representative ∧
    ‖(physical.targetCircuit.unitary :
        Matrix (Bitstring Wire) (Bitstring Wire) Complex) -
      (representative : Matrix (Bitstring Wire) (Bitstring Wire) Complex)‖ <
        precision ∧
    physical.SourceCertified rho ∧
    (compileFiniteRegisterCircuit physical).family.Complete ∧
    (∀ input : DensityOperator (QubitRegister Wire),
      (compileFiniteRegisterCircuit physical).totalWeight input = 1) ∧
    (∀ input : DensityOperator (QubitRegister Wire),
      ((compileFiniteRegisterCircuit physical).rawLeaves input).map
          BK05RegisterRawLeaf.ledger =
        (compileFiniteRegisterCircuit physical).computedLedgers) ∧
    ((∃ branch : (compileFiniteRegisterCircuit physical).Branch,
        (compileFiniteRegisterCircuit physical).status branch =
          .stoppedPhaseExhausted) ∧
      (∃ branch : (compileFiniteRegisterCircuit physical).Branch,
        (compileFiniteRegisterCircuit physical).status branch =
          .stoppedTPairExhausted)) ∧
    (∀ input : DensityOperator (QubitRegister Wire),
      traceNorm
          ((compileFiniteRegisterCircuit physical).aggregateRaw input -
            physical.idealAggregate.aggregateRaw input) < precision) ∧
    ∀ input : DensityOperator (QubitRegister Wire),
      traceNorm
          ((compileFiniteRegisterCircuit physical).aggregateRaw input -
            (exactGateAggregate circuit.unitary).aggregateRaw input) < precision

private theorem hRoute_operationalApproximation
    (rho : DensityOperator QubitSpace)
    (hfidelity : BK15.Threshold.FStar < hFidelity rho)
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] [Nonempty Wire]
    (circuit : FiniteRegisterCircuit Wire)
    (precision : Real) (hprecision : 0 < precision) :
    BK05OperationalApproximation rho circuit precision := by
  have hroute : IdealResourceUniversality.IdealHResourceRoute := by
    simpa [IdealResourceUniversality.IdealMagicResourceRoute] using
      (IdealResourceUniversality.idealMagicResources_extendAdaptiveIdealClifford
        IdealResourceUniversality.IdealMagicResource.h)
  rcases hroute with
    ⟨_, _, _, _, _, _, _, _, _, hdense, _⟩
  have hdense' :
      ProjectivelyGeneratedDense (cliffordPhaseGenerators (-Real.pi / 4)) := by
    simpa [IdealResourceUniversality.hResourceGenerators] using hdense
  let matrixPrecision : Real :=
    precision /
      (4 * ((Fintype.card (Bitstring Wire × Bitstring Wire) : Real) + 1))
  have hmatrixPrecision : 0 < matrixPrecision := by
    dsimp only [matrixPrecision]
    positivity
  rcases projectivelyGeneratedDense_exists_registerWord_matrix_close
    (-Real.pi / 4) hdense' circuit matrixPrecision hmatrixPrecision with
    ⟨representative, hphase, word, hmatrix⟩
  have hquarter : 0 < precision / 4 := by linarith
  have heighth : 0 < precision / 8 := by linarith
  rcases exists_h_registerWord_compiler rho hfidelity word .normal
    (precision / 4) hquarter with
    ⟨mainPhysical, hmainSource, hmainTarget, hmainError⟩
  let wire : Wire := Classical.choice (inferInstance : Nonempty Wire)
  rcases exists_h_phase_parameters rho hfidelity wire (precision / 8) heighth with
    ⟨rounds, blocks, hphaseError⟩
  let resource := BK15.Threshold.bk15AcceptedRunHOutput rho rounds
  let phaseWord : BK05RegisterWord (-Real.pi / 4) Wire :=
    .atom (.oneQubit wire .phase)
  let phasePhysical := phaseWord.compileH resource blocks .normal
  let inversePhysical := phaseWord.compileH resource blocks .inverse
  let dummyPhysical : BK05PhysicalRegisterCircuit Wire :=
    .compose phasePhysical inversePhysical
  let physical : BK05PhysicalRegisterCircuit Wire :=
    .compose dummyPhysical mainPhysical
  have hphasePhysicalError : phasePhysical.errorBudget < precision / 8 := by
    exact hphaseError .normal
  have hinversePhysicalError : inversePhysical.errorBudget < precision / 8 := by
    exact hphaseError .inverse
  have hdummyError : dummyPhysical.errorBudget < precision / 4 := by
    dsimp only [dummyPhysical, BK05PhysicalRegisterCircuit.errorBudget]
    linarith
  have hphysicalError : physical.errorBudget < precision / 2 := by
    dsimp only [physical, BK05PhysicalRegisterCircuit.errorBudget]
    linarith
  have hphaseTarget : phasePhysical.targetCircuit.unitary = phaseWord.eval := by
    simpa [phasePhysical, BK05RegisterWord.orientedEval] using
      BK05RegisterWord.compileH_target_unitary resource blocks phaseWord .normal
  have hinverseTarget : inversePhysical.targetCircuit.unitary = phaseWord.eval⁻¹ := by
    simpa [inversePhysical, BK05RegisterWord.orientedEval] using
      BK05RegisterWord.compileH_target_unitary resource blocks phaseWord .inverse
  have hdummyTarget : dummyPhysical.targetCircuit.unitary = 1 := by
    dsimp only [dummyPhysical, BK05PhysicalRegisterCircuit.targetCircuit,
      FiniteRegisterCircuit.unitary_compose]
    rw [hinverseTarget, hphaseTarget]
    exact inv_mul_cancel phaseWord.eval
  have hphysicalTarget : physical.targetCircuit.unitary = word.eval := by
    dsimp only [physical, BK05PhysicalRegisterCircuit.targetCircuit,
      FiniteRegisterCircuit.unitary_compose]
    rw [hmainTarget, hdummyTarget]
    simp [BK05RegisterWord.orientedEval]
  have hmatrixPhysical :
      ‖(physical.targetCircuit.unitary :
          Matrix (Bitstring Wire) (Bitstring Wire) Complex) -
        (representative :
          Matrix (Bitstring Wire) (Bitstring Wire) Complex)‖ <
        matrixPrecision := by
    rw [hphysicalTarget]
    exact hmatrix
  have hmatrixBudget :
      2 * (Fintype.card (Bitstring Wire × Bitstring Wire) : Real) *
          ‖(physical.targetCircuit.unitary :
              Matrix (Bitstring Wire) (Bitstring Wire) Complex) -
            (representative :
              Matrix (Bitstring Wire) (Bitstring Wire) Complex)‖ <
        precision / 2 := by
    exact finite_card_scaled_error_lt_half
      (Fintype.card (Bitstring Wire × Bitstring Wire)) precision _
      hprecision hmatrixPhysical
  have hphaseSource : phasePhysical.SourceCertified rho := by
    exact BK05PhysicalRegisterCircuit.SourceCertified.hWord
      wire rounds blocks _
  have hinverseSource : inversePhysical.SourceCertified rho := by
    exact BK05PhysicalRegisterCircuit.SourceCertified.hWord
      wire rounds blocks _
  have hdummySource : dummyPhysical.SourceCertified rho :=
    .compose hphaseSource hinverseSource
  have hphysicalSource : physical.SourceCertified rho :=
    .compose hdummySource hmainSource
  have hphaseRetains :
      (∃ branch : (compileFiniteRegisterCircuit phasePhysical).Branch,
        (compileFiniteRegisterCircuit phasePhysical).status branch =
          .stoppedPhaseExhausted) ∧
      (∃ branch : (compileFiniteRegisterCircuit phasePhysical).Branch,
        (compileFiniteRegisterCircuit phasePhysical).status branch =
          .stoppedTPairExhausted) := by
    exact compileWord_retainsFailureLeaves wire
        (.h resource blocks
          [BK05SignedPhaseLetter.positive
            (BK05PhaseAtom.phase : BK05PhaseAtom (-Real.pi / 4))])
  have hdummyRetains :=
    compileFiniteRegisterCircuit_compose_retainsFailureLeaves
      phasePhysical inversePhysical hphaseRetains
  have hphysicalRetains :=
    compileFiniteRegisterCircuit_compose_retainsFailureLeaves
      dummyPhysical mainPhysical hdummyRetains
  refine ⟨representative, physical, hphase, ?_, hphysicalSource,
    compileFiniteRegisterCircuit_complete physical, ?_, ?_, hphysicalRetains,
    ?_, ?_⟩
  · exact hmatrixPhysical.trans (by
      dsimp only [matrixPrecision]
      apply div_lt_self hprecision
      have hcard : 0 ≤
          (Fintype.card (Bitstring Wire × Bitstring Wire) : Real) := by
        positivity
      linarith)
  · intro input
    exact compileFiniteRegisterCircuit_totalWeight physical input
  · intro input
    exact compiledAggregate_ledgers_eq_computed
      (compileFiniteRegisterCircuit physical) input
  · intro input
    exact (compiledAggregate_unconditioned_aggregate_traceNorm_lt
      physical (precision / 2) hphysicalError input).trans (by linarith)
  · intro input
    exact compiledAggregate_target_traceNorm_lt physical circuit representative
      precision hphase hphysicalError hmatrixBudget input

private theorem tRoute_operationalApproximation
    (rho : DensityOperator QubitSpace)
    (hfidelity : BK05T.bk05TFidelityThreshold < tFidelity rho)
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] [Nonempty Wire]
    (circuit : FiniteRegisterCircuit Wire)
    (precision : Real) (hprecision : 0 < precision) :
    BK05OperationalApproximation rho circuit precision := by
  have hroute : IdealResourceUniversality.IdealTResourceRoute := by
    simpa [IdealResourceUniversality.IdealMagicResourceRoute] using
      (IdealResourceUniversality.idealMagicResources_extendAdaptiveIdealClifford
        IdealResourceUniversality.IdealMagicResource.t)
  have hdense : ProjectivelyGeneratedDense
      IdealResourceUniversality.tResourceGenerators := by
    unfold IdealResourceUniversality.IdealTResourceRoute at hroute
    aesop
  have hdense' :
      ProjectivelyGeneratedDense (cliffordPhaseGenerators (-Real.pi / 6)) := by
    simpa [IdealResourceUniversality.tResourceGenerators] using hdense
  let matrixPrecision : Real :=
    precision /
      (4 * ((Fintype.card (Bitstring Wire × Bitstring Wire) : Real) + 1))
  have hmatrixPrecision : 0 < matrixPrecision := by
    dsimp only [matrixPrecision]
    positivity
  rcases projectivelyGeneratedDense_exists_registerWord_matrix_close
    (-Real.pi / 6) hdense' circuit matrixPrecision hmatrixPrecision with
    ⟨representative, hphase, word, hmatrix⟩
  have hquarter : 0 < precision / 4 := by linarith
  have heighth : 0 < precision / 8 := by linarith
  rcases exists_t_registerWord_compiler rho hfidelity word .normal
    (precision / 4) hquarter with
    ⟨mainPhysical, hmainSource, hmainTarget, hmainError⟩
  let wire : Wire := Classical.choice (inferInstance : Nonempty Wire)
  rcases exists_t_phase_parameters rho hfidelity wire (precision / 8) heighth with
    ⟨rounds, pairAttempts, blocks, hphaseError⟩
  let hthreshold : tInitialError rho < BK05T.bk05TThreshold :=
    (BK05T.bk05TFidelityError_lt_threshold_iff rho).mpr hfidelity
  let resource := BK05TSemanticSchedule.rootOutput
    (bk05TCompleteSemanticSchedule rho hthreshold rounds)
  let phaseWord : BK05RegisterWord (-Real.pi / 6) Wire :=
    .atom (.oneQubit wire .phase)
  let phasePhysical :=
    phaseWord.compileT resource pairAttempts blocks .normal
  let inversePhysical :=
    phaseWord.compileT resource pairAttempts blocks .inverse
  let dummyPhysical : BK05PhysicalRegisterCircuit Wire :=
    .compose phasePhysical inversePhysical
  let physical : BK05PhysicalRegisterCircuit Wire :=
    .compose dummyPhysical mainPhysical
  have hphasePhysicalError : phasePhysical.errorBudget < precision / 8 := by
    exact hphaseError .normal
  have hinversePhysicalError : inversePhysical.errorBudget < precision / 8 := by
    exact hphaseError .inverse
  have hdummyError : dummyPhysical.errorBudget < precision / 4 := by
    dsimp only [dummyPhysical, BK05PhysicalRegisterCircuit.errorBudget]
    linarith
  have hphysicalError : physical.errorBudget < precision / 2 := by
    dsimp only [physical, BK05PhysicalRegisterCircuit.errorBudget]
    linarith
  have hphaseTarget : phasePhysical.targetCircuit.unitary = phaseWord.eval := by
    simpa [phasePhysical, BK05RegisterWord.orientedEval] using
      BK05RegisterWord.compileT_target_unitary
        resource pairAttempts blocks phaseWord .normal
  have hinverseTarget : inversePhysical.targetCircuit.unitary = phaseWord.eval⁻¹ := by
    simpa [inversePhysical, BK05RegisterWord.orientedEval] using
      BK05RegisterWord.compileT_target_unitary
        resource pairAttempts blocks phaseWord .inverse
  have hdummyTarget : dummyPhysical.targetCircuit.unitary = 1 := by
    dsimp only [dummyPhysical, BK05PhysicalRegisterCircuit.targetCircuit,
      FiniteRegisterCircuit.unitary_compose]
    rw [hinverseTarget, hphaseTarget]
    exact inv_mul_cancel phaseWord.eval
  have hphysicalTarget : physical.targetCircuit.unitary = word.eval := by
    dsimp only [physical, BK05PhysicalRegisterCircuit.targetCircuit,
      FiniteRegisterCircuit.unitary_compose]
    rw [hmainTarget, hdummyTarget]
    simp [BK05RegisterWord.orientedEval]
  have hmatrixPhysical :
      ‖(physical.targetCircuit.unitary :
          Matrix (Bitstring Wire) (Bitstring Wire) Complex) -
        (representative :
          Matrix (Bitstring Wire) (Bitstring Wire) Complex)‖ <
        matrixPrecision := by
    rw [hphysicalTarget]
    exact hmatrix
  have hmatrixBudget :
      2 * (Fintype.card (Bitstring Wire × Bitstring Wire) : Real) *
          ‖(physical.targetCircuit.unitary :
              Matrix (Bitstring Wire) (Bitstring Wire) Complex) -
            (representative :
              Matrix (Bitstring Wire) (Bitstring Wire) Complex)‖ <
        precision / 2 := by
    exact finite_card_scaled_error_lt_half
      (Fintype.card (Bitstring Wire × Bitstring Wire)) precision _
      hprecision hmatrixPhysical
  have hphaseSource : phasePhysical.SourceCertified rho := by
    exact BK05PhysicalRegisterCircuit.SourceCertified.tWord
      wire hthreshold rounds pairAttempts blocks _
  have hinverseSource : inversePhysical.SourceCertified rho := by
    exact BK05PhysicalRegisterCircuit.SourceCertified.tWord
      wire hthreshold rounds pairAttempts blocks _
  have hdummySource : dummyPhysical.SourceCertified rho :=
    .compose hphaseSource hinverseSource
  have hphysicalSource : physical.SourceCertified rho :=
    .compose hdummySource hmainSource
  have hphaseRetains :
      (∃ branch : (compileFiniteRegisterCircuit phasePhysical).Branch,
        (compileFiniteRegisterCircuit phasePhysical).status branch =
          .stoppedPhaseExhausted) ∧
      (∃ branch : (compileFiniteRegisterCircuit phasePhysical).Branch,
        (compileFiniteRegisterCircuit phasePhysical).status branch =
          .stoppedTPairExhausted) := by
    exact compileWord_retainsFailureLeaves wire
        (.t resource pairAttempts blocks
          [BK05SignedPhaseLetter.positive
            (BK05PhaseAtom.phase : BK05PhaseAtom (-Real.pi / 6))])
  have hdummyRetains :=
    compileFiniteRegisterCircuit_compose_retainsFailureLeaves
      phasePhysical inversePhysical hphaseRetains
  have hphysicalRetains :=
    compileFiniteRegisterCircuit_compose_retainsFailureLeaves
      dummyPhysical mainPhysical hdummyRetains
  refine ⟨representative, physical, hphase, ?_, hphysicalSource,
    compileFiniteRegisterCircuit_complete physical, ?_, ?_, hphysicalRetains,
    ?_, ?_⟩
  · exact hmatrixPhysical.trans (by
      dsimp only [matrixPrecision]
      apply div_lt_self hprecision
      have hcard : 0 ≤
          (Fintype.card (Bitstring Wire × Bitstring Wire) : Real) := by
        positivity
      linarith)
  · intro input
    exact compileFiniteRegisterCircuit_totalWeight physical input
  · intro input
    exact compiledAggregate_ledgers_eq_computed
      (compileFiniteRegisterCircuit physical) input
  · intro input
    exact (compiledAggregate_unconditioned_aggregate_traceNorm_lt
      physical (precision / 2) hphysicalError input).trans (by linarith)
  · intro input
    exact compiledAggregate_target_traceNorm_lt physical circuit representative
      precision hphase hphysicalError hmatrixBudget input

/-- Operational adaptive ideal-Clifford universality supplied by the noisy
one-qubit resource `rho`: every nonempty finite qubit register circuit has, at
every positive precision, a finite source-certified complete implementation
with explicit unconditioned branch data and retained stopping outcomes. -/
def BK05AdaptiveUniversal (rho : DensityOperator QubitSpace) : Prop :=
  ∀ {Wire : Type} [Fintype Wire] [DecidableEq Wire] [Nonempty Wire]
    (circuit : FiniteRegisterCircuit Wire) (precision : Real),
    0 < precision → BK05OperationalApproximation rho circuit precision

/-- **BK05, Theorems 1–2.**  A one-qubit state above either the BK05 T-type
square-root fidelity threshold or the BK15 H-type square-root fidelity
threshold supplies universal adaptive ideal-Clifford computation.  The proof
uses the actual finite purification outputs and a complete, unconditioned
finite-register compiler; no success branch is postselected. -/
theorem bk05_magicState_fidelity_thresholds_imply_universality
    (rho : DensityOperator QubitSpace)
    (hthreshold :
      BK05T.bk05TFidelityThreshold < OneQubitMagic.tFidelity rho ∨
      BK15.Threshold.FStar < OneQubitMagic.hFidelity rho) :
    BK05AdaptiveUniversal rho := by
  intro Wire _ _ _ circuit precision hprecision
  rcases hthreshold with ht | hh
  · exact tRoute_operationalApproximation rho ht circuit precision hprecision
  · exact hRoute_operationalApproximation rho hh circuit precision hprecision

/- End entanglement-safe finite-register compiler. -/
end Distillation
end QEC
