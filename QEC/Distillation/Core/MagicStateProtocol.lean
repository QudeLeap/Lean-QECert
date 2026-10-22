import QEC.Semantics.Channels.Core
import QEC.Semantics.Entropy.Convexity
/-!
# QEC.Distillation.MagicStateProtocol

Finite-dimensional magic-state protocol semantics with explicit accepted and
rejected conditional states over an existing CPTP quantum channel.
-/

universe u

namespace QEC
namespace Distillation

open Semantics
open scoped BigOperators

private theorem densityOperator_ext {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
    {rho sigma : DensityOperator H}
    (h : rho.toOperator = sigma.toOperator) :
    rho = sigma := by
  cases rho with
  | mk rho hpos htrace =>
      cases sigma with
      | mk sigma hpos' htrace' =>
          dsimp at h
          cases h
          rfl

/-- An indexed family of noisy input resource states. -/
abbrev ResourceInput (count : Nat) (Resource : Type u)
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource] :=
  Fin count → DensityOperator Resource

/--
Independent-input data retain separate per-resource rates and the
route-supplied admissibility relation that interprets them.
-/
structure IndependentInputErrorModel (count : Nat) (Resource : Type u)
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource] where
  rate : Fin count → ℝ
  rate_nonneg : ∀ i, 0 ≤ rate i
  rate_le_one : ∀ i, rate i ≤ 1
  admissible : (Fin count → ℝ) → ResourceInput count Resource → Prop

/-- Adversarial inputs are controlled by an explicit weight bound. -/
structure AdversarialWeightInputErrorModel (count : Nat) (Resource : Type u)
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource] where
  weight : ResourceInput count Resource → Nat
  maxWeight : Nat

/--
Local-stochastic data retain one rate and the route-supplied admissibility
relation that gives that rate its probabilistic meaning.
-/
structure LocalStochasticInputErrorModel (count : Nat) (Resource : Type u)
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource] where
  rate : ℝ
  rate_nonneg : 0 ≤ rate
  rate_le_one : rate ≤ 1
  admissible : ℝ → ResourceInput count Resource → Prop

/-- The three supported input-error regimes remain distinct constructors. -/
inductive InputErrorModel (count : Nat) (Resource : Type u)
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource] where
  | independent (model : IndependentInputErrorModel count Resource)
  | adversarialWeight (model : AdversarialWeightInputErrorModel count Resource)
  | localStochastic (model : LocalStochasticInputErrorModel count Resource)

namespace InputErrorModel

variable {count : Nat} {Resource : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]

/-- Interpret the selected input-error regime on one indexed resource family. -/
def Permits (model : InputErrorModel count Resource)
    (inputs : ResourceInput count Resource) : Prop :=
  match model with
  | .independent model => model.admissible model.rate inputs
  | .adversarialWeight model => model.weight inputs ≤ model.maxWeight
  | .localStochastic model => model.admissible model.rate inputs

@[simp]
theorem permits_independent
    (model : IndependentInputErrorModel count Resource)
    (inputs : ResourceInput count Resource) :
    Permits (.independent model) inputs ↔ model.admissible model.rate inputs :=
  Iff.rfl

@[simp]
theorem permits_adversarialWeight
    (model : AdversarialWeightInputErrorModel count Resource)
    (inputs : ResourceInput count Resource) :
    Permits (.adversarialWeight model) inputs ↔
      model.weight inputs ≤ model.maxWeight :=
  Iff.rfl

@[simp]
theorem permits_localStochastic
    (model : LocalStochasticInputErrorModel count Resource)
    (inputs : ResourceInput count Resource) :
    Permits (.localStochastic model) inputs ↔
      model.admissible model.rate inputs :=
  Iff.rfl

end InputErrorModel

/-- The two protocol outcomes required by the shared distillation interface. -/
inductive DistillationOutcome
  | accepted
  | rejected
deriving DecidableEq

instance : Fintype DistillationOutcome where
  elems := {.accepted, .rejected}
  complete := by intro outcome; cases outcome <;> simp

/-- The probability assigned to one binary protocol outcome. -/
def outcomeWeight (successProbability : ℝ) : DistillationOutcome → ℝ
  | .accepted => successProbability
  | .rejected => 1 - successProbability

theorem outcomeWeight_nonneg {successProbability : ℝ}
    (h0 : 0 ≤ successProbability) (h1 : successProbability ≤ 1)
    (outcome : DistillationOutcome) :
    0 ≤ outcomeWeight successProbability outcome := by
  cases outcome with
  | accepted => exact h0
  | rejected =>
      simpa [outcomeWeight] using sub_nonneg.mpr h1

theorem outcomeWeight_sum (successProbability : ℝ) :
    ∑ outcome : DistillationOutcome, outcomeWeight successProbability outcome = 1 := by
  rw [show (Finset.univ : Finset DistillationOutcome) =
      {DistillationOutcome.accepted, DistillationOutcome.rejected} by decide]
  simp [outcomeWeight]

/-- Index the normalized accepted and rejected conditional output states. -/
def branchState {Output : Type u}
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output]
    (acceptedOutput rejectedOutput : DensityOperator Output) :
    DistillationOutcome → DensityOperator Output
  | .accepted => acceptedOutput
  | .rejected => rejectedOutput

/-- The normalized binary mixture reconstructed from the two protocol branches. -/
noncomputable def outcomeMixture {Output : Type u}
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output]
    (successProbability : ℝ) (h0 : 0 ≤ successProbability)
    (h1 : successProbability ≤ 1)
    (acceptedOutput rejectedOutput : DensityOperator Output) :
    DensityOperator Output :=
  DensityOperator.convexCombination Finset.univ
    (outcomeWeight successProbability)
    (branchState acceptedOutput rejectedOutput)
    (by
      intro outcome _houtcome
      exact outcomeWeight_nonneg h0 h1 outcome)
    (by
      simpa using outcomeWeight_sum successProbability)

/-- If both conditional branches are the same state, their mixture is that state. -/
theorem outcomeMixture_self {Output : Type u}
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output]
    (successProbability : ℝ) (h0 : 0 ≤ successProbability)
    (h1 : successProbability ≤ 1) (rho : DensityOperator Output) :
    outcomeMixture successProbability h0 h1 rho rho = rho := by
  apply densityOperator_ext
  simp [outcomeMixture, DensityOperator.convexCombinationOperator,
    branchState, outcomeWeight,
    show (Finset.univ : Finset DistillationOutcome) =
      {DistillationOutcome.accepted, DistillationOutcome.rejected} by decide]

/--
One execution of a finite-resource distillation protocol.

The complete operation remains an existing CPTP quantum channel.  Accepted and
rejected conditional states are normalized separately, and their weighted
mixture is required to reconstruct the channel output on the prepared input.
-/
structure DistillationRun (Resource Input Output : Type u)
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource]
    [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
    [FiniteQuantumSystem Input]
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output] where
  resourceCount : Nat
  noisyInput : Fin resourceCount → DensityOperator Resource
  prepareInput :
    (Fin resourceCount → DensityOperator Resource) → DensityOperator Input
  operation : QuantumChannel Input Output
  successProbability : ℝ
  success_nonneg : 0 ≤ successProbability
  success_le_one : successProbability ≤ 1
  acceptedOutput : DensityOperator Output
  rejectedOutput : DensityOperator Output
  output_decomposition :
    operation.mapDensity (prepareInput noisyInput) =
      outcomeMixture successProbability success_nonneg success_le_one
        acceptedOutput rejectedOutput

namespace DistillationRun

variable {Resource Input Output : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
variable [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
variable [FiniteQuantumSystem Input]
variable [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
variable [FiniteQuantumSystem Output]

/-- The complete normalized channel output before outcome handling. -/
noncomputable def rawOutput (run : DistillationRun Resource Input Output) :
    DensityOperator Output :=
  run.operation.mapDensity (run.prepareInput run.noisyInput)

/-- The probability of the rejected branch. -/
def rejectionProbability (run : DistillationRun Resource Input Output) : ℝ :=
  1 - run.successProbability

/-- The accepted/rejected probability function exposed to protocol clients. -/
def outcomeProbability (run : DistillationRun Resource Input Output) :
    DistillationOutcome → ℝ :=
  outcomeWeight run.successProbability

/-- The normalized conditional output selected by an outcome. -/
def conditionalOutput (run : DistillationRun Resource Input Output) :
    DistillationOutcome → DensityOperator Output :=
  branchState run.acceptedOutput run.rejectedOutput

@[simp]
theorem accepted_probability (run : DistillationRun Resource Input Output) :
    run.outcomeProbability .accepted = run.successProbability :=
  rfl

@[simp]
theorem rejected_probability (run : DistillationRun Resource Input Output) :
    run.outcomeProbability .rejected = run.rejectionProbability :=
  rfl

theorem outcomeProbability_nonneg
    (run : DistillationRun Resource Input Output)
    (outcome : DistillationOutcome) :
    0 ≤ run.outcomeProbability outcome :=
  outcomeWeight_nonneg run.success_nonneg run.success_le_one outcome

theorem outcomeProbability_sum (run : DistillationRun Resource Input Output) :
    run.outcomeProbability .accepted + run.outcomeProbability .rejected = 1 := by
  simp [outcomeProbability, outcomeWeight]

@[simp]
theorem accepted_conditionalOutput
    (run : DistillationRun Resource Input Output) :
    run.conditionalOutput .accepted = run.acceptedOutput :=
  rfl

@[simp]
theorem rejected_conditionalOutput
    (run : DistillationRun Resource Input Output) :
    run.conditionalOutput .rejected = run.rejectedOutput :=
  rfl

theorem conditionalOutput_trace
    (run : DistillationRun Resource Input Output)
    (outcome : DistillationOutcome) :
    LinearMap.trace Complex Output (run.conditionalOutput outcome).toOperator = 1 :=
  (run.conditionalOutput outcome).trace_one

theorem rawOutput_eq_outcomeMixture
    (run : DistillationRun Resource Input Output) :
    run.rawOutput =
      outcomeMixture run.successProbability run.success_nonneg run.success_le_one
        run.acceptedOutput run.rejectedOutput :=
  run.output_decomposition

end DistillationRun

/--
Outcome handling remains explicit: postselection reports the accepted branch,
whereas active correction applies a supplied decoder to the complete raw
output.
-/
inductive ProtocolBehavior (Output : Type u)
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output] where
  | postselected
  | activeCorrection (decoder : QuantumChannel Output Output)

namespace DistillationRun

variable {Resource Input Output : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
variable [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
variable [FiniteQuantumSystem Input]
variable [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
variable [FiniteQuantumSystem Output]

/-- The output exposed by the selected postselection or correction behavior. -/
noncomputable def reportedOutput
    (run : DistillationRun Resource Input Output) :
    ProtocolBehavior Output → DensityOperator Output
  | .postselected => run.acceptedOutput
  | .activeCorrection decoder => decoder.mapDensity run.rawOutput

@[simp]
theorem reportedOutput_postselected
    (run : DistillationRun Resource Input Output) :
    run.reportedOutput .postselected = run.acceptedOutput :=
  rfl

@[simp]
theorem reportedOutput_activeCorrection
    (run : DistillationRun Resource Input Output)
    (decoder : QuantumChannel Output Output) :
    run.reportedOutput (.activeCorrection decoder) =
      decoder.mapDensity run.rawOutput :=
  rfl

end DistillationRun

/--
A magic-state distillation protocol adds its permitted input regime, outcome
handling, ideal resource state, and a nonnegative output-error functional to
one proof-relevant run.
-/
structure MagicStateDistillationProtocol (Resource Input Output : Type u)
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource]
    [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
    [FiniteQuantumSystem Input]
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output] where
  run : DistillationRun Resource Input Output
  inputErrorModel : InputErrorModel run.resourceCount Resource
  inputPermitted : inputErrorModel.Permits run.noisyInput
  behavior : ProtocolBehavior Output
  idealOutput : DensityOperator Output
  outputError : DensityOperator Output → DensityOperator Output → ℝ
  outputError_nonneg : ∀ rho sigma, 0 ≤ outputError rho sigma

namespace MagicStateDistillationProtocol

variable {Resource Input Output : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
variable [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
variable [FiniteQuantumSystem Input]
variable [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
variable [FiniteQuantumSystem Output]

/-- Error of the accepted conditional output relative to the ideal resource. -/
def successfulOutputError
    (protocol : MagicStateDistillationProtocol Resource Input Output) : ℝ :=
  protocol.outputError protocol.run.acceptedOutput protocol.idealOutput

/-- Error of the behavior-dependent reported output relative to the ideal resource. -/
noncomputable def reportedOutputError
    (protocol : MagicStateDistillationProtocol Resource Input Output) : ℝ :=
  protocol.outputError
    (protocol.run.reportedOutput protocol.behavior) protocol.idealOutput

theorem successfulOutputError_nonneg
    (protocol : MagicStateDistillationProtocol Resource Input Output) :
    0 ≤ protocol.successfulOutputError :=
  protocol.outputError_nonneg _ _

theorem reportedOutputError_nonneg
    (protocol : MagicStateDistillationProtocol Resource Input Output) :
    0 ≤ protocol.reportedOutputError :=
  protocol.outputError_nonneg _ _

/-- The protocol's noisy resource family is permitted by its selected model. -/
theorem inputModel_permits
    (protocol : MagicStateDistillationProtocol Resource Input Output) :
    protocol.inputErrorModel.Permits protocol.run.noisyInput :=
  protocol.inputPermitted

end MagicStateDistillationProtocol

end Distillation

namespace Semantics
namespace QuantumChannel

variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
variable [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
variable [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L]
variable [FiniteQuantumSystem L]

/-- Mapping a density through a composite channel is sequential mapping. -/
theorem comp_mapDensity (Psi : QuantumChannel K L) (Phi : QuantumChannel H K)
    (rho : DensityOperator H) :
    (QuantumChannel.comp Psi Phi).mapDensity rho =
      Psi.mapDensity (Phi.mapDensity rho) := by
  rfl

end QuantumChannel
end Semantics

namespace Distillation

open Semantics

/-- Quantum channels preserve the binary conditional-state mixture. -/
theorem mapDensity_outcomeMixture {Output Output' : Type u}
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output]
    [NormedAddCommGroup Output'] [InnerProductSpace Complex Output']
    [FiniteQuantumSystem Output']
    (channel : QuantumChannel Output Output')
    (successProbability : ℝ) (h0 : 0 ≤ successProbability)
    (h1 : successProbability ≤ 1)
    (acceptedOutput rejectedOutput : DensityOperator Output) :
    channel.mapDensity
        (outcomeMixture successProbability h0 h1
          acceptedOutput rejectedOutput) =
      outcomeMixture successProbability h0 h1
        (channel.mapDensity acceptedOutput)
        (channel.mapDensity rejectedOutput) := by
  apply densityOperator_ext
  simp [outcomeMixture, DensityOperator.convexCombinationOperator,
    branchState, outcomeWeight,
    show (Finset.univ : Finset DistillationOutcome) =
      {DistillationOutcome.accepted, DistillationOutcome.rejected} by decide]

namespace DistillationRun

variable {Resource Input Output : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
variable [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
variable [FiniteQuantumSystem Input]
variable [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
variable [FiniteQuantumSystem Output]

/-- Compose an output channel after a run while preserving its branch probabilities. -/
noncomputable def postprocess {Output' : Type u}
    [NormedAddCommGroup Output'] [InnerProductSpace Complex Output']
    [FiniteQuantumSystem Output']
    (run : DistillationRun Resource Input Output)
    (channel : QuantumChannel Output Output') :
    DistillationRun Resource Input Output' where
  resourceCount := run.resourceCount
  noisyInput := run.noisyInput
  prepareInput := run.prepareInput
  operation := QuantumChannel.comp channel run.operation
  successProbability := run.successProbability
  success_nonneg := run.success_nonneg
  success_le_one := run.success_le_one
  acceptedOutput := channel.mapDensity run.acceptedOutput
  rejectedOutput := channel.mapDensity run.rejectedOutput
  output_decomposition := by
    rw [Semantics.QuantumChannel.comp_mapDensity]
    rw [run.output_decomposition]
    exact mapDensity_outcomeMixture channel run.successProbability
      run.success_nonneg run.success_le_one run.acceptedOutput run.rejectedOutput

@[simp]
theorem postprocess_successProbability {Output' : Type u}
    [NormedAddCommGroup Output'] [InnerProductSpace Complex Output']
    [FiniteQuantumSystem Output']
    (run : DistillationRun Resource Input Output)
    (channel : QuantumChannel Output Output') :
    (run.postprocess channel).successProbability = run.successProbability :=
  rfl

@[simp]
theorem postprocess_conditionalOutput {Output' : Type u}
    [NormedAddCommGroup Output'] [InnerProductSpace Complex Output']
    [FiniteQuantumSystem Output']
    (run : DistillationRun Resource Input Output)
    (channel : QuantumChannel Output Output')
    (outcome : DistillationOutcome) :
    (run.postprocess channel).conditionalOutput outcome =
      channel.mapDensity (run.conditionalOutput outcome) := by
  cases outcome <;> rfl

theorem postprocess_rawOutput {Output' : Type u}
    [NormedAddCommGroup Output'] [InnerProductSpace Complex Output']
    [FiniteQuantumSystem Output']
    (run : DistillationRun Resource Input Output)
    (channel : QuantumChannel Output Output') :
    (run.postprocess channel).rawOutput =
      channel.mapDensity run.rawOutput := by
  rfl

end DistillationRun

end Distillation
end QEC
