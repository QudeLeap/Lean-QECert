import QEC.Distillation.Universality.FiniteRegisterUniversality
import QEC.Distillation.Universality.HAngleUniversality
import QEC.Distillation.Universality.HResourcePhase
import QEC.Distillation.Injection.PhaseInjection
import QEC.Distillation.Universality.TPhaseGeneratedUniversality
import QEC.Distillation.Universality.TResourcePhase
/-!
# The combined BK05 ideal-resource universality bridge

This module closes the internal ideal-resource route from BK05 Section III.
It composes the concrete H- and T-resource preparations, the physical stopped
phase-injection traces and their ledgers, the two proved projective-density
theorems, and the finite-register circuit lift.  No success, density, or
universality conclusion is accepted as a premise.

The result is internal support for the later noisy-threshold theorem.  It does
not prove either noisy distillation recurrence or the public T-or-H threshold
statement.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace IdealResourceUniversality

open QEC.Semantics
open QEC.Semantics.Qubit
open GeneratedUniversality
open OneQubitMagic
open PhaseInjection
open FiniteRegisterUniversality
open FiniteRegisterUniversality.FiniteRegisterCircuit
open scoped BigOperators

private theorem densityOperator_ext_toOperator {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {rho sigma : DensityOperator H} (h : rho.toOperator = sigma.toOperator) :
    rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl

private theorem rankOne_global_phase
    (z : Complex) (psi : QubitSpace) (hz : z * star z = 1) :
    (InnerProductSpace.rankOne Complex (z • psi) (z • psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  ext x b
  change (inner Complex (z • psi) x) * (z • psi) b =
    (inner Complex psi x) * psi b
  simp only [PiLp.smul_apply, inner_smul_left, smul_eq_mul]
  calc
    (star z * inner Complex psi x) * (z * psi b) =
        (z * star z) * inner Complex psi x * psi b := by ring
    _ = inner Complex psi x * psi b := by rw [hz]; ring

/-- The concrete one-qubit generators supplied by the ideal H-resource route. -/
def hResourceGenerators : Set (UnitaryGate (Fin 2)) :=
  cliffordPhaseGenerators (-Real.pi / 4)

/-- The concrete one-qubit generators supplied by the ideal T-resource route. -/
def tResourceGenerators : Set (UnitaryGate (Fin 2)) :=
  cliffordPhaseGenerators (-Real.pi / 6)

/-- The fresh-pair ledger token is the shared ideal T magic-state density. -/
theorem sourceTPreparationResource_eq_tMagicState :
    sourceTDensity = tMagicState :=
  sourceTDensity_eq_tMagicState

/-- The already-constructed H-route words give projective generated density. -/
theorem hResource_projectivelyGeneratedDense :
    ProjectivelyGeneratedDense hResourceGenerators := by
  simpa [hResourceGenerators] using
    (projectivelyGeneratedDense_of_irrational_axis_words
      (cliffordPhaseGenerators (-Real.pi / 4))
      hAngleAxis hAngleConjugateAxis hAngle hAngleWord hAngleConjugateWord
      hAngleWord_mem_generated hAngleWord_eq_axisCircle
      hAngleConjugateWord_mem_generated hAngleConjugateWord_eq_axisCircle
      hAngle_div_two_pi_irrational hAngleAxis_nonparallel)

/-- The already-constructed T-route words give projective generated density. -/
theorem tResource_projectivelyGeneratedDense :
    ProjectivelyGeneratedDense tResourceGenerators := by
  simpa [tResourceGenerators, tResourcePhaseAngle] using
    (projectivelyGeneratedDense_of_irrational_axis_words
      (cliffordPhaseGenerators tResourcePhaseAngle)
      tResourceAxis tResourceConjugateAxis tResourceAxisAngle
      tResourceAxisWord tResourceConjugateWord
      tResourceAxisWord_mem_generated tResourceAxisWord_eq_axisCircle
      tResourceConjugateWord_mem_generated tResourceConjugateWord_eq_axisCircle
      tResourceAxisAngle_irrational tResourceAxes_nonparallel)

/-- Residue one of the order-eight retry cycle is exactly the `-pi/4` phase. -/
theorem hResource_targetAction_one :
    phaseCycleTargetAction 8 (1 : ZMod 8) =
      phaseShiftOperator (-Real.pi / 4) := by
  change phaseEightTargetAction (1 : ZMod 8) =
    phaseShiftOperator (-Real.pi / 4)
  rw [phaseEightTargetAction_eq]
  have hval : (1 : ZMod 8).val = 1 := ZMod.val_one'' (by norm_num)
  rw [hval, Nat.cast_one, mul_one]

/-- Residue one of the order-twelve retry cycle is exactly the `-pi/6` phase. -/
theorem tResource_targetAction_one :
    phaseCycleTargetAction 12 (1 : ZMod 12) =
      phaseShiftOperator (-Real.pi / 6) := by
  change phaseTwelveTargetAction (1 : ZMod 12) =
    phaseShiftOperator (-Real.pi / 6)
  rw [phaseTwelveTargetAction_eq]
  have hval : (1 : ZMod 12).val = 1 := ZMod.val_one'' (by norm_num)
  rw [hval, Nat.cast_one, mul_one]

/--
An accepted fresh-pair preparation trace, indexed by the number of rejected
two-T attempts preceding its accepted attempt.
-/
structure SourceTPreparationAcceptedTrace where
  rejectedAttempts : Nat

namespace SourceTPreparationAcceptedTrace

/-- Total fresh two-T attempts consumed by this accepted trace. -/
def attemptCount (trace : SourceTPreparationAcceptedTrace) : Nat :=
  trace.rejectedAttempts + 1

/-- The product of actual rejected and accepted Born weights for this trace. -/
noncomputable def weight (trace : SourceTPreparationAcceptedTrace) : Real :=
  sourceTAttempt.rejectedWeight ^ trace.rejectedAttempts *
    sourceTAttempt.acceptedWeight

/-- Every attempt debits a fresh pair of the concrete source-T density. -/
noncomputable def ledger (trace : SourceTPreparationAcceptedTrace) :
    AdaptiveIdealClifford.ResourceLedger (DensityOperator QubitSpace) :=
  Multiset.replicate (trace.attemptCount * sourceTAttempt.resourceCount)
    sourceTDensity

/-- The exact geometric weight of an accepted trace after its rejections. -/
theorem weight_eq (trace : SourceTPreparationAcceptedTrace) :
    trace.weight = (1 / 3 : Real) ^ trace.rejectedAttempts * (2 / 3) := by
  rw [weight, sourceTAttempt_rejected_weight, sourceTAttempt_accepted_weight]

/-- The trace ledger contains two fresh source-T states per actual attempt. -/
theorem ledger_eq (trace : SourceTPreparationAcceptedTrace) :
    trace.ledger = Multiset.replicate (2 * trace.attemptCount) sourceTDensity := by
  simp [ledger, sourceTAttempt_resource_count, Nat.mul_comm]

end SourceTPreparationAcceptedTrace

/-- The total concrete source-T ledger after a specified number of attempts. -/
noncomputable def sourceTPreparationLedger (attemptCount : Nat) :
    AdaptiveIdealClifford.ResourceLedger (DensityOperator QubitSpace) :=
  Multiset.replicate (attemptCount * sourceTAttempt.resourceCount) sourceTDensity

/-- Every repeated preparation attempt consumes exactly two fresh source-T states. -/
theorem sourceTPreparationLedger_eq (attemptCount : Nat) :
    sourceTPreparationLedger attemptCount =
      Multiset.replicate (2 * attemptCount) sourceTDensity := by
  simp [sourceTPreparationLedger, sourceTAttempt_resource_count, Nat.mul_comm]

/--
Total accepted mass within a finite fresh-pair attempt budget.  Each summand is
an actual stopped trace with some rejected attempts followed by acceptance.
-/
noncomputable def sourceTPreparationHitMass (attemptBudget : Nat) : Real :=
  ∑ rejectedAttempts ∈ Finset.range attemptBudget,
    (SourceTPreparationAcceptedTrace.mk rejectedAttempts).weight

/-- The finite fresh-pair preparation mass has the exact geometric form. -/
theorem sourceTPreparationHitMass_eq_one_sub_pow (attemptBudget : Nat) :
    sourceTPreparationHitMass attemptBudget =
      1 - (1 / 3 : Real) ^ attemptBudget := by
  induction attemptBudget with
  | zero => simp [sourceTPreparationHitMass]
  | succ attemptBudget ih =>
      rw [sourceTPreparationHitMass, Finset.sum_range_succ]
      rw [← sourceTPreparationHitMass, ih,
        SourceTPreparationAcceptedTrace.weight_eq]
      ring

/-- The all-rejected branch mass within a finite fresh-pair attempt budget. -/
noncomputable def sourceTPreparationMissMass (attemptBudget : Nat) : Real :=
  sourceTAttempt.rejectedWeight ^ attemptBudget

/-- The fresh-pair preparation tail is exactly geometric. -/
theorem sourceTPreparationMissMass_eq_pow (attemptBudget : Nat) :
    sourceTPreparationMissMass attemptBudget = (1 / 3 : Real) ^ attemptBudget := by
  rw [sourceTPreparationMissMass, sourceTAttempt_rejected_weight]

/-- Accepted mass and the all-rejected tail exhaust the finite preparation tree. -/
theorem sourceTPreparationHitMass_add_missMass (attemptBudget : Nat) :
    sourceTPreparationHitMass attemptBudget +
      sourceTPreparationMissMass attemptBudget = 1 := by
  rw [sourceTPreparationHitMass_eq_one_sub_pow,
    sourceTPreparationMissMass_eq_pow]
  ring

/-- The geometric all-rejected tail vanishes with the attempt budget. -/
theorem sourceTPreparationMissMass_tendsto_zero :
    Filter.Tendsto sourceTPreparationMissMass Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun attempts : Nat =>
      (1 / 3 : Real) ^ attempts) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  exact hpow.congr' (Filter.Eventually.of_forall fun attempts =>
    (sourceTPreparationMissMass_eq_pow attempts).symm)

/-- Repeating rejected source-T attempts with fresh pairs succeeds almost surely. -/
theorem sourceTPreparationHitMass_probability_one :
    Filter.Tendsto sourceTPreparationHitMass Filter.atTop (nhds 1) := by
  have hpow : Filter.Tendsto (fun attempts : Nat =>
      (1 / 3 : Real) ^ attempts) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hone : Filter.Tendsto (fun _ : Nat => (1 : Real))
      Filter.atTop (nhds 1) := tendsto_const_nhds
  have hclosed : Filter.Tendsto (fun attempts : Nat =>
      1 - (1 / 3 : Real) ^ attempts) Filter.atTop (nhds 1) := by
    simpa only [sub_zero] using (hone.sub hpow)
  exact hclosed.congr' (Filter.Eventually.of_forall fun attempts =>
    (sourceTPreparationHitMass_eq_one_sub_pow attempts).symm)

private theorem sourceTGlobalPhase_mul_conj :
    sourceTGlobalPhase * star sourceTGlobalPhase = 1 := by
  rw [mul_comm]
  change (starRingEnd Complex) sourceTGlobalPhase * sourceTGlobalPhase = 1
  rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm,
    sourceTGlobalPhase_norm]
  norm_num

/--
The actual accepted source-T density is sent by XOR, discard, and Hadamard to
the exact phase-state density consumed by the subsequent injection circuit.
-/
theorem sourceTAcceptedBranch_to_phaseStateDensity :
    (QuantumChannel.unitaryConj hadamardTransport).mapDensity
        ((QuantumChannel.comp TwoQubit.secondQubitDiscard
          (QuantumChannel.unitaryConj TwoQubit.xorTransport)).mapDensity
            sourceTEvenBranch) =
      phaseStateDensity (-Real.pi / 6) := by
  rw [sourceTEvenBranch_xor_discard]
  apply densityOperator_ext_toOperator
  have hweight : 0 < sourceTEvenWeight := by
    rw [sourceTEvenWeight_eq_two_thirds]
    norm_num
  have hfirst :
      TwoQubit.zzEvenBranchFirstQubit sourceTTwoQubitState hweight =
        sourceTEvenFirstQubit := by
    rfl
  have hnorm : ‖sourceTEvenFirstQubit‖ = 1 := by
    rw [← hfirst]
    exact TwoQubit.zzEvenBranchFirstQubit_norm sourceTTwoQubitState hweight
  have hinput :
      (TwoQubit.zzEvenBranchFirstDensity sourceTTwoQubitState
        hweight).toOperator =
        (InnerProductSpace.rankOne Complex sourceTEvenFirstQubit
          sourceTEvenFirstQubit).toLinearMap := by
    dsimp only [TwoQubit.zzEvenBranchFirstDensity]
    rw [DensityOperator.pureOfNonzero_toOperator,
      hfirst, inner_self_eq_norm_sq_to_K, hnorm]
    norm_num
  rw [QuantumChannel.mapDensity_toOperator, QuantumChannel.unitaryConj_apply,
    hinput, QuditSubsystem.conjOperator_rankOne,
    phaseStateDensity_toOperator]
  change (InnerProductSpace.rankOne Complex
      (hadamardOperator sourceTEvenFirstQubit)
      (hadamardOperator sourceTEvenFirstQubit)).toLinearMap = _
  rw [sourceTEvenOutput_global_phase]
  exact rankOne_global_phase sourceTGlobalPhase
    (phaseState (-Real.pi / 6)) sourceTGlobalPhase_mul_conj

/-- A visited H-route block trace has the exact target output density. -/
theorem hResource_stoppingOutputDensity_target {blocks : Nat}
    (trace : PhaseRetry.BlockTrace 8 blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hvisit : PhaseRetry.traceVisitsTarget
      (0 : ZMod 8) (1 : ZMod 8) blocks trace) :
    phaseInjectionStoppingOutputDensity
        (0 : ZMod 8) (1 : ZMod 8) trace psi hpsi =
      phaseCycleTargetOutputDensity 8 (1 : ZMod 8) psi hpsi := by
  simpa [phaseCycleTargetOutputDensity, sourceInputDensity] using
    (phaseInjectionStoppingOutputDensity_target_of_visit
      (target := (1 : ZMod 8)) trace psi hpsi hvisit)

/-- A visited T-route block trace has the exact target output density. -/
theorem tResource_stoppingOutputDensity_target {blocks : Nat}
    (trace : PhaseRetry.BlockTrace 12 blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hvisit : PhaseRetry.traceVisitsTarget
      (0 : ZMod 12) (1 : ZMod 12) blocks trace) :
    phaseInjectionStoppingOutputDensity
        (0 : ZMod 12) (1 : ZMod 12) trace psi hpsi =
      phaseCycleTargetOutputDensity 12 (1 : ZMod 12) psi hpsi := by
  simpa [phaseCycleTargetOutputDensity, sourceInputDensity] using
    (phaseInjectionStoppingOutputDensity_target_of_visit
      (target := (1 : ZMod 12)) trace psi hpsi hvisit)

/-- Every explicit finite-register circuit is approximable along the H route. -/
theorem idealHResource_finiteRegisterCircuit_approximates
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (circuit : FiniteRegisterCircuit Wire)
    (precision : Real) (hprecision : 0 < precision) :
    ApproximatesModuloPhase
      (finiteRegisterGenerators (Wire := Wire) hResourceGenerators)
      circuit.unitary precision :=
  finiteRegisterCircuit_approximates_of_projectivelyGeneratedDense
    hResourceGenerators hResource_projectivelyGeneratedDense
    circuit precision hprecision

/-- Every explicit finite-register circuit is approximable along the T route. -/
theorem idealTResource_finiteRegisterCircuit_approximates
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (circuit : FiniteRegisterCircuit Wire)
    (precision : Real) (hprecision : 0 < precision) :
    ApproximatesModuloPhase
      (finiteRegisterGenerators (Wire := Wire) tResourceGenerators)
      circuit.unitary precision :=
  finiteRegisterCircuit_approximates_of_projectivelyGeneratedDense
    tResourceGenerators tResource_projectivelyGeneratedDense
    circuit precision hprecision

/--
The complete ideal-H route: actual H-density conversion, concrete phase-state
consumption and stopped retry semantics, almost-sure target hit, exact target
action, projective density, and finite-register circuit approximation.
-/
def IdealHResourceRoute : Prop :=
  hResourceTransport.conjDensity hMagicState =
      phaseStateDensity (-Real.pi / 4) ∧
  (phaseStateResourceUse (-Real.pi / 4)).ledger = {(-Real.pi / 4)} ∧
  (∀ (psi : QubitSpace) (hpsi : ‖psi‖ = 1),
    (phaseStateResourceUse (-Real.pi / 4)).run (sourceInputDensity psi hpsi) =
      injectionInputDensity psi (-Real.pi / 4) hpsi) ∧
  (∀ (psi : QubitSpace) (hpsi : ‖psi‖ = 1) (coin : Bool),
    oneShotMeasurementWeight psi (-Real.pi / 4) hpsi coin = (1 / 2 : Real)) ∧
  (∀ (psi : QubitSpace) (hpsi : ‖psi‖ = 1) (coin : Bool),
    oneShotAttempt psi (-Real.pi / 4) hpsi coin =
      oneShotAttemptGlobalPhase (-Real.pi / 4) coin •
        phaseShiftOperator (oneShotAttemptAngle (-Real.pi / 4) coin) psi) ∧
  (∀ (psi : QubitSpace) (hpsi : ‖psi‖ = 1),
    Filter.Tendsto (fun blocks =>
      phaseInjectionStoppingHitMass (blocks := blocks)
        (0 : ZMod 8) (1 : ZMod 8) psi hpsi)
      Filter.atTop (nhds 1)) ∧
  (∀ (blocks : Nat) (trace : PhaseRetry.BlockTrace 8 blocks)
      (psi : QubitSpace) (hpsi : ‖psi‖ = 1),
    ∃ attempts ≤ 8 * blocks,
      phaseInjectionStoppingLedger
          (0 : ZMod 8) (1 : ZMod 8) trace psi hpsi =
        Multiset.replicate attempts (-Real.pi / 4)) ∧
  (∀ {blocks : Nat} (trace : PhaseRetry.BlockTrace 8 blocks)
      (psi : QubitSpace) (hpsi : ‖psi‖ = 1),
    PhaseRetry.traceVisitsTarget (0 : ZMod 8) (1 : ZMod 8) blocks trace →
      phaseInjectionStoppingOutputDensity
          (0 : ZMod 8) (1 : ZMod 8) trace psi hpsi =
        phaseCycleTargetOutputDensity 8 (1 : ZMod 8) psi hpsi) ∧
  phaseCycleTargetAction 8 (1 : ZMod 8) =
      phaseShiftOperator (-Real.pi / 4) ∧
  ProjectivelyGeneratedDense hResourceGenerators ∧
  ∀ {Wire : Type} [Fintype Wire] [DecidableEq Wire]
      (circuit : FiniteRegisterCircuit Wire)
      (precision : Real), 0 < precision →
    ApproximatesModuloPhase
      (finiteRegisterGenerators (Wire := Wire) hResourceGenerators)
      circuit.unitary precision

/-- The ideal H resource constructs every component of `IdealHResourceRoute`. -/
theorem idealHResourceRoute : IdealHResourceRoute := by
  refine ⟨hResourceTransport_hMagicState, phaseStateResourceUse_ledger _, ?_, ?_,
    ?_, ?_, ?_, ?_, hResource_targetAction_one,
    hResource_projectivelyGeneratedDense, ?_⟩
  · intro psi hpsi
    exact phaseStateResourceUse_run_eq_injectionInputDensity psi _ hpsi
  · intro psi hpsi coin
    exact oneShotMeasurementWeight_fair psi _ hpsi coin
  · intro psi hpsi coin
    exact oneShotAttempt_action psi _ hpsi coin
  · intro psi hpsi
    exact phaseInjectionStoppingHitMass_eight_probability_one
      (0 : ZMod 8) (1 : ZMod 8) psi hpsi
  · intro blocks trace psi hpsi
    simpa [phaseCycleAngle_eight] using
      (phaseInjectionStoppingLedger_bound
        (0 : ZMod 8) (1 : ZMod 8) trace psi hpsi)
  · intro blocks trace psi hpsi hvisit
    exact hResource_stoppingOutputDensity_target trace psi hpsi hvisit
  · intro Wire _ _ circuit precision hprecision
    exact idealHResource_finiteRegisterCircuit_approximates
      circuit precision hprecision

/--
The complete ideal-T route: the actual two-resource accepted/rejected attempt,
its `2/3` accepted phase-state output, concrete stopped retry semantics,
projective density, and finite-register circuit approximation.
-/
def IdealTResourceRoute : Prop :=
  sourceTAttempt.resourceCount = 2 ∧
  sourceTDensity = tMagicState ∧
  sourceTAttempt.acceptedWeight = 2 / 3 ∧
  sourceTAttempt.rejectedWeight = 1 / 3 ∧
  sourceTOutcomeAction .accepted = .emitAccepted ∧
  sourceTOutcomeAction .rejected = .retryWithFreshPair ∧
  (∀ attemptBudget,
    sourceTPreparationHitMass attemptBudget +
      sourceTPreparationMissMass attemptBudget = 1) ∧
  (∀ attemptBudget,
    sourceTPreparationMissMass attemptBudget = (1 / 3 : Real) ^ attemptBudget) ∧
  Filter.Tendsto sourceTPreparationMissMass Filter.atTop (nhds 0) ∧
  Filter.Tendsto sourceTPreparationHitMass Filter.atTop (nhds 1) ∧
  (∀ attemptCount,
    sourceTPreparationLedger attemptCount =
      Multiset.replicate (2 * attemptCount) sourceTDensity) ∧
  (∀ trace : SourceTPreparationAcceptedTrace,
    trace.weight = (1 / 3 : Real) ^ trace.rejectedAttempts * (2 / 3)) ∧
  (∀ trace : SourceTPreparationAcceptedTrace,
    trace.ledger = Multiset.replicate (2 * trace.attemptCount) sourceTDensity) ∧
  (QuantumChannel.unitaryConj hadamardTransport).mapDensity
        ((QuantumChannel.comp TwoQubit.secondQubitDiscard
          (QuantumChannel.unitaryConj TwoQubit.xorTransport)).mapDensity
            sourceTEvenBranch) =
      phaseStateDensity (-Real.pi / 6) ∧
  hadamardOperator sourceTEvenFirstQubit =
      sourceTGlobalPhase • phaseState (-Real.pi / 6) ∧
  ‖sourceTGlobalPhase‖ = 1 ∧
  (phaseStateResourceUse (-Real.pi / 6)).ledger = {(-Real.pi / 6)} ∧
  (∀ (psi : QubitSpace) (hpsi : ‖psi‖ = 1),
    (phaseStateResourceUse (-Real.pi / 6)).run (sourceInputDensity psi hpsi) =
      injectionInputDensity psi (-Real.pi / 6) hpsi) ∧
  (∀ (psi : QubitSpace) (hpsi : ‖psi‖ = 1) (coin : Bool),
    oneShotMeasurementWeight psi (-Real.pi / 6) hpsi coin = (1 / 2 : Real)) ∧
  (∀ (psi : QubitSpace) (hpsi : ‖psi‖ = 1) (coin : Bool),
    oneShotAttempt psi (-Real.pi / 6) hpsi coin =
      oneShotAttemptGlobalPhase (-Real.pi / 6) coin •
        phaseShiftOperator (oneShotAttemptAngle (-Real.pi / 6) coin) psi) ∧
  (∀ (psi : QubitSpace) (hpsi : ‖psi‖ = 1),
    Filter.Tendsto (fun blocks =>
      phaseInjectionStoppingHitMass (blocks := blocks)
        (0 : ZMod 12) (1 : ZMod 12) psi hpsi)
      Filter.atTop (nhds 1)) ∧
  (∀ (blocks : Nat) (trace : PhaseRetry.BlockTrace 12 blocks)
      (psi : QubitSpace) (hpsi : ‖psi‖ = 1),
    ∃ attempts ≤ 12 * blocks,
      phaseInjectionStoppingLedger
          (0 : ZMod 12) (1 : ZMod 12) trace psi hpsi =
        Multiset.replicate attempts (-Real.pi / 6)) ∧
  (∀ {blocks : Nat} (trace : PhaseRetry.BlockTrace 12 blocks)
      (psi : QubitSpace) (hpsi : ‖psi‖ = 1),
    PhaseRetry.traceVisitsTarget (0 : ZMod 12) (1 : ZMod 12) blocks trace →
      phaseInjectionStoppingOutputDensity
          (0 : ZMod 12) (1 : ZMod 12) trace psi hpsi =
        phaseCycleTargetOutputDensity 12 (1 : ZMod 12) psi hpsi) ∧
  phaseCycleTargetAction 12 (1 : ZMod 12) =
      phaseShiftOperator (-Real.pi / 6) ∧
  ProjectivelyGeneratedDense tResourceGenerators ∧
  ∀ {Wire : Type} [Fintype Wire] [DecidableEq Wire]
      (circuit : FiniteRegisterCircuit Wire)
      (precision : Real), 0 < precision →
    ApproximatesModuloPhase
      (finiteRegisterGenerators (Wire := Wire) tResourceGenerators)
      circuit.unitary precision

/-- The ideal T resource constructs every component of `IdealTResourceRoute`. -/
theorem idealTResourceRoute : IdealTResourceRoute := by
  refine ⟨sourceTAttempt_resource_count,
    sourceTPreparationResource_eq_tMagicState, sourceTAttempt_accepted_weight,
    sourceTAttempt_rejected_weight, sourceTAccepted_emits_output,
    sourceTRejected_retries_with_fresh_pair,
    sourceTPreparationHitMass_add_missMass,
    sourceTPreparationMissMass_eq_pow,
    sourceTPreparationMissMass_tendsto_zero,
    sourceTPreparationHitMass_probability_one,
    sourceTPreparationLedger_eq,
    SourceTPreparationAcceptedTrace.weight_eq,
    SourceTPreparationAcceptedTrace.ledger_eq,
    sourceTAcceptedBranch_to_phaseStateDensity,
    sourceTEvenOutput_global_phase, sourceTGlobalPhase_norm,
    phaseStateResourceUse_ledger _, ?_, ?_, ?_, ?_, ?_, ?_,
    tResource_targetAction_one, tResource_projectivelyGeneratedDense, ?_⟩
  · intro psi hpsi
    exact phaseStateResourceUse_run_eq_injectionInputDensity psi _ hpsi
  · intro psi hpsi coin
    exact oneShotMeasurementWeight_fair psi _ hpsi coin
  · intro psi hpsi coin
    exact oneShotAttempt_action psi _ hpsi coin
  · intro psi hpsi
    exact phaseInjectionStoppingHitMass_twelve_probability_one
      (0 : ZMod 12) (1 : ZMod 12) psi hpsi
  · intro blocks trace psi hpsi
    simpa [phaseCycleAngle_twelve] using
      (phaseInjectionStoppingLedger_bound
        (0 : ZMod 12) (1 : ZMod 12) trace psi hpsi)
  · intro blocks trace psi hpsi hvisit
    exact tResource_stoppingOutputDensity_target trace psi hpsi hvisit
  · intro Wire _ _ circuit precision hprecision
    exact idealTResource_finiteRegisterCircuit_approximates
      circuit precision hprecision

/-- The stronger package proving both exact ideal-resource routes. -/
theorem idealMagicResourceRoutes :
    IdealHResourceRoute ∧ IdealTResourceRoute :=
  ⟨idealHResourceRoute, idealTResourceRoute⟩

/-- The two alternative ideal magic resources admitted by the BK05 bridge. -/
inductive IdealMagicResource
  | h
  | t
deriving DecidableEq

/-- The concrete one-qubit generators associated with the selected resource. -/
def idealMagicResourceGenerators :
    IdealMagicResource → Set (UnitaryGate (Fin 2))
  | .h => hResourceGenerators
  | .t => tResourceGenerators

/--
The exact route and universality predicate for either selected ideal resource.
It is transparent by cases and contains no assumed route field.
-/
def IdealMagicResourceRoute : IdealMagicResource → Prop
  | .h => IdealHResourceRoute
  | .t => IdealTResourceRoute

/--
The exact internal BK05 bridge consumed downstream.  For either resource
choice, it constructs the corresponding adaptive phase-injection and
finite-register universality route by consuming the two proved route theorems
in the respective cases.
-/
theorem idealMagicResources_extendAdaptiveIdealClifford :
    ∀ resource, IdealMagicResourceRoute resource := by
  intro resource
  cases resource with
  | h => exact idealHResourceRoute
  | t => exact idealTResourceRoute

end IdealResourceUniversality
end Distillation
end QEC
