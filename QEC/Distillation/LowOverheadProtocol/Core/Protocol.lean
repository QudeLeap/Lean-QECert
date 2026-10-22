import QEC.Distillation.LowOverheadProtocol.Core.OutputHandoff
import QEC.Distillation.Core.DependentBatch
/-!
# HH18 protocol aggregate

This thin aggregate packages the already-constructed physical endpoint,
decoder, normalized run, decoded-error bridge, and one-level accounting route.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Protocol

open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators

universe u

attribute [local instance 100] Fintype.ofFinite

local instance instProtocolClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic

/-- The complete one-level physical HH18 construction through the existing
`MagicStateDistillationProtocol` interface.  Its run is the resource-consuming
CPTP decoded run above; no output channel or success/error bound is supplied
by a caller. -/
noncomputable def hh18MagicStateDistillationProtocol
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    MagicStateDistillationProtocol QubitSpace PhysicalRegister LogicalRegister where
  run := resourceDecodedRun (noisyResources epsilon)
  inputErrorModel := .independent (independentInputModel epsilon)
  inputPermitted := noisyResources_permitted epsilon
  behavior := .postselected
  idealOutput := idealLogicalTOutput
  outputError := hh18OutputTraceError
  outputError_nonneg := hh18OutputTraceError_nonneg

theorem hh18MagicStateDistillationProtocol_successfulOutputError
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (hh18MagicStateDistillationProtocol epsilon).successfulOutputError =
      hh18OutputTraceError
        (resourceDecodedRun (noisyResources epsilon)).acceptedOutput
        idealLogicalTOutput :=
  rfl

/-! ## Physical next-input handoff -/

/-- Phase transports compose by addition at the operator level.  This is the
abstract inverse-transport algebra used below, independent of any mixture. -/
private theorem phaseShiftTransport_conjOperator_add
    (alpha beta : Real) (data : Operator QubitSpace) :
    (phaseShiftTransport beta).conjOperator
        ((phaseShiftTransport alpha).conjOperator data) =
      (phaseShiftTransport (alpha + beta)).conjOperator data := by
  unfold UnitaryTransport.conjOperator
  apply LinearMap.ext
  intro psi
  change phaseShiftOperator beta
      (phaseShiftOperator alpha
        (data (phaseShiftOperator (-alpha)
          (phaseShiftOperator (-beta) psi)))) =
    phaseShiftOperator (alpha + beta)
      (data (phaseShiftOperator (-(alpha + beta)) psi))
  have houter (x : QubitSpace) :
      phaseShiftOperator beta (phaseShiftOperator alpha x) =
        phaseShiftOperator (alpha + beta) x := by
    rw [← Module.End.mul_apply, phaseShiftOperator_add, add_comm]
  have hinner (x : QubitSpace) :
      phaseShiftOperator (-alpha) (phaseShiftOperator (-beta) x) =
        phaseShiftOperator (-(alpha + beta)) x := by
    rw [← Module.End.mul_apply, phaseShiftOperator_add]
    congr 1
    ring
  rw [houter, hinner]

private theorem phaseShiftTransport_conjDensity_add
    (alpha beta : Real) (rho : DensityOperator QubitSpace) :
    (phaseShiftTransport beta).conjDensity
        ((phaseShiftTransport alpha).conjDensity rho) =
      (phaseShiftTransport (alpha + beta)).conjDensity rho := by
  apply DensityOperator.ext_toOperator
  simp only [UnitaryTransport.conjDensity_toOperator]
  exact phaseShiftTransport_conjOperator_add alpha beta rho.toOperator

private theorem phaseShiftTransport_zero_conjDensity
    (rho : DensityOperator QubitSpace) :
    (phaseShiftTransport 0).conjDensity rho = rho := by
  apply DensityOperator.ext_toOperator
  rw [UnitaryTransport.conjDensity_toOperator]
  apply LinearMap.ext
  intro psi
  change phaseShiftOperator 0 (rho.toOperator (phaseShiftOperator (-0) psi)) =
    rho.toOperator psi
  simp

private theorem inverse_phaseShiftTransport_rotateTInvResource
    (rho : DensityOperator QubitSpace) :
    (phaseShiftTransport (-Real.pi / 2)).conjDensity (rotateTInvResource rho) = rho := by
  unfold rotateTInvResource
  rw [phaseShiftTransport_conjDensity_add]
  have hangle : Real.pi / 2 + (-Real.pi / 2) = 0 := by
    ring
  rw [hangle]
  exact phaseShiftTransport_zero_conjDensity rho

/-- The cubic upper envelope is small enough for the native HH18 input domain. -/
def hh18NextInputSmallDomain (epsilon : HH18NoisyInput.DiagonalErrorRate) : Prop :=
  (2 * residualCubicCoefficient) * epsilon.1 ^ 3 ≤ 1 / 2

/-- The physically reached raw Born rate, now certified in HH18's native
`[0, 1/2]` diagonal-input domain. -/
noncomputable def hh18NextInputErrorRate
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18NextInputSmallDomain epsilon) : HH18NoisyInput.DiagonalErrorRate :=
  ⟨hh18NextInputRawError epsilon,
    hh18NextInputRawError_nonneg epsilon,
    (hh18NextInputRawError_le_cubic epsilon).trans hsmall⟩

/-- The reached HH18 input rate inherits its cubic bound by directly composing
the decoded trace bridge with the accepted-residual endpoint bound. -/
theorem hh18NextInputErrorRate_le_cubic
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18NextInputSmallDomain epsilon) :
    (hh18NextInputErrorRate epsilon hsmall).1 ≤
      (2 * residualCubicCoefficient) * epsilon.1 ^ 3 := by
  change hh18NextInputRawError epsilon ≤
    (2 * residualCubicCoefficient) * epsilon.1 ^ 3
  calc
    hh18NextInputRawError epsilon ≤
        hh18OutputTraceError
          (resourceDecodedRun (noisyResources epsilon)).acceptedOutput
          idealLogicalTOutput := hh18NextInputRawError_le_outputTrace epsilon
    _ ≤ 2 * acceptedResidualError epsilon :=
      acceptedOutputTraceError_le_two_mul_acceptedResidual epsilon
    _ ≤ 2 * (residualCubicCoefficient * epsilon.1 ^ 3) := by
      exact mul_le_mul_of_nonneg_left (acceptedResidualError_le_cubic epsilon) (by norm_num)
    _ = (2 * residualCubicCoefficient) * epsilon.1 ^ 3 := by ring

private theorem aBasisErrorParameter_nextInputErrorRate
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18NextInputSmallDomain epsilon) :
    aBasisErrorParameter (hh18NextInputErrorRate epsilon hsmall) =
      hh18NextInputRawParameter epsilon := by
  rfl

/-- The literal physical next input obtained from an actual normalized
accepted logical output. -/
noncomputable def hh18AcceptedRunOutputAsNextInput
    (run : DistillationRun QubitSpace PhysicalRegister LogicalRegister) :
    DensityOperator QubitSpace :=
  (phaseShiftTransport (-Real.pi / 2)).conjDensity
    (aBasisDephasing.mapDensity
      (hh18LogicalOutputTransport.conjDensity
        run.acceptedOutput))

/-- The literal physical next input: inverse phase transport of the A-basis
dephasing of the transported accepted logical output. -/
noncomputable def hh18AcceptedOutputAsNextInput
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : DensityOperator QubitSpace :=
  hh18AcceptedRunOutputAsNextInput (resourceDecodedRun (noisyResources epsilon))

/-- The literal physical next input is the existing noisy `T†` resource at
the reached raw Born error rate, under its derived cubic smallness proof. -/
theorem hh18AcceptedOutputAsNextInput_eq_noisyTInvResource
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18NextInputSmallDomain epsilon) :
    hh18AcceptedOutputAsNextInput epsilon =
      HH18NoisyInput.noisyTInvResource (hh18NextInputErrorRate epsilon hsmall) := by
  change (phaseShiftTransport (-Real.pi / 2)).conjDensity
      (hh18NextInputDephasedOutput epsilon) = _
  rw [hh18NextInputDephasedOutput_eq_diagonalAResource]
  rw [← aBasisErrorParameter_nextInputErrorRate epsilon hsmall]
  rw [← rotateTInvResource_noisy]
  exact inverse_phaseShiftTransport_rotateTInvResource _

/-! ## One-level dependent flagged-batch consumer -/

/-! The expected-yield sum is first reduced abstractly to an explicitly named
finite support.  Concrete HH18 accounting only instantiates this lemma, so it
never unfolds or compares the `PhysicalErrorWord` enumeration. -/
private theorem expectedAcceptedPorts_eq_explicit_selected_mass
    {Port Outcome : Type u} [Fintype Port] [Fintype Outcome]
    (batch : DependentBatch.FiniteFlaggedBatch Port Outcome)
    (support : Finset Outcome) (selected : Outcome → Prop) [DecidablePred selected]
    (mass : ℝ)
    (hsupport : (Finset.univ : Finset Outcome) = support)
    (hcount : ∀ outcome, DependentBatch.acceptedPortCount batch outcome =
      if selected outcome then 1 else 0)
    (hmass : mass = support.sum fun outcome =>
      if selected outcome then batch.weight outcome else 0) :
    DependentBatch.expectedAcceptedPorts batch = mass := by
  unfold DependentBatch.expectedAcceptedPorts
  rw [hsupport]
  calc
    (∑ outcome ∈ support, batch.weight outcome *
        (DependentBatch.acceptedPortCount batch outcome : ℝ)) =
        support.sum (fun outcome =>
          if selected outcome then batch.weight outcome else 0) := by
      apply Finset.sum_congr rfl
      intro outcome _
      rw [hcount outcome]
      by_cases hselected : selected outcome <;> simp [hselected]
    _ = mass := hmass.symm

/-- The actual fifteen input slots of one HH18 block. -/
abbrev BatchInputSlot := Fin resourceCount

/-- The single logical output port of the fixed `[[15,1,3]]` HH18 block. -/
abbrev BatchOutputPort := Fin 1

/-! ## Arbitrary-depth pre-yield physical recursion -/

/-- A fixed over-envelope scale derived solely from the compiled HH18 cubic
coefficient. -/
noncomputable def hh18IterationScale : ℝ :=
  2 * residualCubicCoefficient + 30

private theorem residualCubicCoefficient_nonneg :
    0 ≤ residualCubicCoefficient := by
  unfold residualCubicCoefficient
  positivity

theorem hh18IterationScale_pos : 0 < hh18IterationScale := by
  unfold hh18IterationScale
  nlinarith [residualCubicCoefficient_nonneg]

private theorem hh18IterationScale_nonneg : 0 ≤ hh18IterationScale :=
  hh18IterationScale_pos.le

private theorem hh18IterationScale_one_le : 1 ≤ hh18IterationScale := by
  unfold hh18IterationScale
  nlinarith [residualCubicCoefficient_nonneg]

/-- The endpoint coefficient is dominated by the square of the fixed scale. -/
theorem two_mul_residualCubicCoefficient_le_iterationScale_sq :
    2 * residualCubicCoefficient ≤ hh18IterationScale ^ 2 := by
  calc
    2 * residualCubicCoefficient ≤ hh18IterationScale := by
      unfold hh18IterationScale
      linarith
    _ = hh18IterationScale * 1 := by ring
    _ ≤ hh18IterationScale * hh18IterationScale :=
      mul_le_mul_of_nonneg_left hh18IterationScale_one_le hh18IterationScale_nonneg
    _ = hh18IterationScale ^ 2 := by ring

/-- Initial scaled smallness from which every successor's physical domain is
derived internally. -/
def hh18InitialSmallDomain (epsilon : HH18NoisyInput.DiagonalErrorRate) : Prop :=
  hh18IterationScale * epsilon.1 ≤ 1 / 2

/-- A private recursive state stores exactly the rate and its derived scaled
smallness invariant; no recurrence evidence is supplied by callers. -/
private structure HH18IterationState where
  rate : HH18NoisyInput.DiagonalErrorRate
  scaled_small : hh18IterationScale * rate.1 ≤ 1 / 2

private theorem hh18IterationScale_sq_le_cube :
    hh18IterationScale ^ 2 ≤ hh18IterationScale ^ 3 := by
  calc
    hh18IterationScale ^ 2 = hh18IterationScale ^ 2 * 1 := by ring
    _ ≤ hh18IterationScale ^ 2 * hh18IterationScale :=
      mul_le_mul_of_nonneg_left hh18IterationScale_one_le
        (sq_nonneg hh18IterationScale)
    _ = hh18IterationScale ^ 3 := by ring

private theorem scaled_cube_le_half (state : HH18IterationState) :
    hh18IterationScale ^ 2 * state.rate.1 ^ 3 ≤ 1 / 2 := by
  have hrate : 0 ≤ state.rate.1 := state.rate.property.1
  have hscaled_cube :
      (hh18IterationScale * state.rate.1) ^ 3 ≤ (1 / 2 : ℝ) ^ 3 :=
    pow_le_pow_left₀
      (mul_nonneg hh18IterationScale_nonneg hrate) state.scaled_small 3
  calc
    hh18IterationScale ^ 2 * state.rate.1 ^ 3 ≤
        hh18IterationScale ^ 3 * state.rate.1 ^ 3 :=
      mul_le_mul_of_nonneg_right hh18IterationScale_sq_le_cube
        (pow_nonneg hrate 3)
    _ = (hh18IterationScale * state.rate.1) ^ 3 := by ring
    _ ≤ (1 / 2 : ℝ) ^ 3 := hscaled_cube
    _ ≤ 1 / 2 := by norm_num

private theorem hh18IterationNextSmall (state : HH18IterationState) :
    hh18NextInputSmallDomain state.rate := by
  unfold hh18NextInputSmallDomain
  calc
    (2 * residualCubicCoefficient) * state.rate.1 ^ 3 ≤
        hh18IterationScale ^ 2 * state.rate.1 ^ 3 :=
      mul_le_mul_of_nonneg_right
        two_mul_residualCubicCoefficient_le_iterationScale_sq
        (pow_nonneg state.rate.property.1 3)
    _ ≤ 1 / 2 := scaled_cube_le_half state

private theorem hh18IterationNextScaledSmall (state : HH18IterationState) :
    hh18IterationScale *
        (hh18NextInputErrorRate state.rate (hh18IterationNextSmall state)).1 ≤ 1 / 2 := by
  have hnext := hh18NextInputErrorRate_le_cubic state.rate
    (hh18IterationNextSmall state)
  have hscaled_cube :
      (hh18IterationScale * state.rate.1) ^ 3 ≤ (1 / 2 : ℝ) ^ 3 :=
    pow_le_pow_left₀
      (mul_nonneg hh18IterationScale_nonneg state.rate.property.1)
      state.scaled_small 3
  calc
    hh18IterationScale *
        (hh18NextInputErrorRate state.rate (hh18IterationNextSmall state)).1 ≤
        hh18IterationScale *
          ((2 * residualCubicCoefficient) * state.rate.1 ^ 3) :=
      mul_le_mul_of_nonneg_left hnext hh18IterationScale_nonneg
    _ ≤ hh18IterationScale *
          (hh18IterationScale ^ 2 * state.rate.1 ^ 3) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          two_mul_residualCubicCoefficient_le_iterationScale_sq
          (pow_nonneg state.rate.property.1 3))
        hh18IterationScale_nonneg
    _ = (hh18IterationScale * state.rate.1) ^ 3 := by ring
    _ ≤ (1 / 2 : ℝ) ^ 3 := hscaled_cube
    _ ≤ 1 / 2 := by norm_num

private noncomputable def hh18IterationState
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) : Nat → HH18IterationState
  | 0 => ⟨epsilon, hsmall⟩
  | depth + 1 =>
      let previous := hh18IterationState epsilon hsmall depth
      ⟨hh18NextInputErrorRate previous.rate (hh18IterationNextSmall previous),
        hh18IterationNextScaledSmall previous⟩

/-- The actual recursively reached HH18 diagonal error rate.  Each successor
is the compiled physical next-input rate, with smallness proved from the
private state's invariant rather than supplied as a sequence. -/
noncomputable def hh18ErrorIteration
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    HH18NoisyInput.DiagonalErrorRate :=
  (hh18IterationState epsilon hsmall depth).rate

private theorem hh18ErrorIteration_zero
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) :
    hh18ErrorIteration epsilon hsmall 0 = epsilon := by
  rfl

private theorem hh18ErrorIteration_succ
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18ErrorIteration epsilon hsmall (depth + 1) =
      hh18NextInputErrorRate (hh18ErrorIteration epsilon hsmall depth)
        (hh18IterationNextSmall (hh18IterationState epsilon hsmall depth)) := by
  rfl

/-- The actual resource-decoded HH18 run at one recursively reached stage.
Its input is the literal compiled diagonal resource family, not a surrogate
rate-only run. -/
noncomputable def hh18ActualStageRun
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :=
  resourceDecodedRun (noisyResources (hh18ErrorIteration epsilon hsmall depth))

/-- An actual stage run retains exactly its physical accepted Born mass. -/
theorem hh18ActualStageRun_successProbability
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    (hh18ActualStageRun epsilon hsmall depth).successProbability =
      rawSuccessMass (hh18ErrorIteration epsilon hsmall depth) := by
  change endpointWeight
      (noisyResources (hh18ErrorIteration epsilon hsmall depth)) .accepted = _
  exact endpointWeight_accepted_eq_rawSuccessMass _

/-- The separate cubic over-envelope for the actual physical iteration. -/
noncomputable def hh18CubicErrorEnvelope
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : Nat → ℝ
  | 0 => epsilon.1
  | depth + 1 =>
      hh18IterationScale ^ 2 * (hh18CubicErrorEnvelope epsilon depth) ^ 3

private theorem hh18CubicErrorEnvelope_nonneg
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat) :
    0 ≤ hh18CubicErrorEnvelope epsilon depth := by
  induction depth with
  | zero =>
      exact epsilon.property.1
  | succ depth ih =>
      change 0 ≤ hh18IterationScale ^ 2 *
        (hh18CubicErrorEnvelope epsilon depth) ^ 3
      exact mul_nonneg (sq_nonneg hh18IterationScale) (pow_nonneg ih 3)

theorem hh18CubicErrorEnvelope_closed_form
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat) :
    hh18IterationScale * hh18CubicErrorEnvelope epsilon depth =
      (hh18IterationScale * epsilon.1) ^ (3 ^ depth) := by
  induction depth with
  | zero =>
      simp [hh18CubicErrorEnvelope]
  | succ depth ih =>
      calc
        hh18IterationScale * hh18CubicErrorEnvelope epsilon (depth + 1) =
            (hh18IterationScale * hh18CubicErrorEnvelope epsilon depth) ^ 3 := by
          simp only [hh18CubicErrorEnvelope]
          ring
        _ = ((hh18IterationScale * epsilon.1) ^ (3 ^ depth)) ^ 3 := by
          rw [ih]
        _ = (hh18IterationScale * epsilon.1) ^ (3 ^ (depth + 1)) := by
          rw [← pow_mul]
          congr 1

theorem hh18ErrorIteration_le_cubicEnvelope
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    (hh18ErrorIteration epsilon hsmall depth).1 ≤
      hh18CubicErrorEnvelope epsilon depth := by
  induction depth with
  | zero =>
      rw [hh18ErrorIteration_zero]
      rfl
  | succ depth ih =>
      rw [hh18ErrorIteration_succ]
      calc
        (hh18NextInputErrorRate (hh18ErrorIteration epsilon hsmall depth)
            (hh18IterationNextSmall (hh18IterationState epsilon hsmall depth))).1 ≤
            (2 * residualCubicCoefficient) *
              (hh18ErrorIteration epsilon hsmall depth).1 ^ 3 :=
          hh18NextInputErrorRate_le_cubic _ _
        _ ≤ hh18IterationScale ^ 2 *
              (hh18ErrorIteration epsilon hsmall depth).1 ^ 3 :=
          mul_le_mul_of_nonneg_right
            two_mul_residualCubicCoefficient_le_iterationScale_sq
            (pow_nonneg (hh18ErrorIteration epsilon hsmall depth).property.1 3)
        _ ≤ hh18IterationScale ^ 2 * (hh18CubicErrorEnvelope epsilon depth) ^ 3 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀
              (hh18ErrorIteration epsilon hsmall depth).property.1 ih 3)
            (sq_nonneg hh18IterationScale)
        _ = hh18CubicErrorEnvelope epsilon (depth + 1) := by rfl

/-- Literal depth-indexed physical input slots. -/
abbrev hh18DepthInputSlots (depth : Nat) := Fin depth → BatchInputSlot

/-- Literal depth-indexed logical output slots. -/
abbrev hh18DepthOutputSlots (depth : Nat) := Fin depth → BatchOutputPort

theorem hh18DepthInputSlots_card (depth : Nat) :
    Fintype.card (hh18DepthInputSlots depth) = 15 ^ depth := by
  simp [hh18DepthInputSlots, resourceCount_eq_fifteen]

theorem hh18DepthOutputSlots_card (depth : Nat) :
    Fintype.card (hh18DepthOutputSlots depth) = 1 ^ depth := by
  simp [hh18DepthOutputSlots]

/-- The public cubic envelope recovers the private iterator invariant without
referring to its hidden implementation state. -/
theorem iteration_scaled_small (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18IterationScale * (hh18ErrorIteration epsilon hsmall depth).1 ≤ 1 / 2 := by
  have hscale : 0 ≤ hh18IterationScale := hh18IterationScale_pos.le
  have hrate : 0 ≤ (hh18ErrorIteration epsilon hsmall depth).1 :=
    (hh18ErrorIteration epsilon hsmall depth).property.1
  have henvelope := hh18ErrorIteration_le_cubicEnvelope epsilon hsmall depth
  have hbase : 0 ≤ hh18IterationScale * epsilon.1 :=
    mul_nonneg hscale epsilon.property.1
  calc
    hh18IterationScale * (hh18ErrorIteration epsilon hsmall depth).1 ≤
        hh18IterationScale * hh18CubicErrorEnvelope epsilon depth :=
      mul_le_mul_of_nonneg_left henvelope hscale
    _ = (hh18IterationScale * epsilon.1) ^ (3 ^ depth) :=
      hh18CubicErrorEnvelope_closed_form epsilon depth
    _ ≤ (1 / 2 : ℝ) ^ (3 ^ depth) :=
      pow_le_pow_left₀ hbase hsmall _
    _ ≤ (1 / 2 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (a := (1 / 2 : ℝ)) (m := 1) (n := 3 ^ depth)
        (by norm_num) (by norm_num)
        (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3))
    _ = (1 / 2 : ℝ) := by norm_num

/-- The actual next reached rate contracts by a factor of four.  The
successor is exposed only by definitional reduction; its smallness proof is
proof-irrelevant. -/
theorem iteration_next_le_quarter (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    (hh18ErrorIteration epsilon hsmall (depth + 1)).1 ≤
      (hh18ErrorIteration epsilon hsmall depth).1 / 4 := by
  have hrate : 0 ≤ (hh18ErrorIteration epsilon hsmall depth).1 :=
    (hh18ErrorIteration epsilon hsmall depth).property.1
  have hscaled := iteration_scaled_small epsilon hsmall depth
  have hscale_sq :
      (hh18IterationScale * (hh18ErrorIteration epsilon hsmall depth).1) ^ 2 ≤
        (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_left₀
      (mul_nonneg hh18IterationScale_pos.le hrate) hscaled 2
  have hnextsmall :
      hh18NextInputSmallDomain (hh18ErrorIteration epsilon hsmall depth) := by
    unfold hh18NextInputSmallDomain
    calc
      (2 * residualCubicCoefficient) *
          (hh18ErrorIteration epsilon hsmall depth).1 ^ 3 ≤
          hh18IterationScale ^ 2 *
            (hh18ErrorIteration epsilon hsmall depth).1 ^ 3 :=
        mul_le_mul_of_nonneg_right
          two_mul_residualCubicCoefficient_le_iterationScale_sq (pow_nonneg hrate 3)
      _ = (hh18ErrorIteration epsilon hsmall depth).1 *
            (hh18IterationScale * (hh18ErrorIteration epsilon hsmall depth).1) ^ 2 := by
        ring
      _ ≤ (hh18ErrorIteration epsilon hsmall depth).1 * (1 / 2 : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hscale_sq hrate
      _ ≤ 1 / 2 := by
        nlinarith [(hh18ErrorIteration epsilon hsmall depth).property.2]
  change (hh18NextInputErrorRate (hh18ErrorIteration epsilon hsmall depth) hnextsmall).1 ≤ _
  calc
    (hh18NextInputErrorRate (hh18ErrorIteration epsilon hsmall depth) hnextsmall).1 ≤
        (2 * residualCubicCoefficient) *
          (hh18ErrorIteration epsilon hsmall depth).1 ^ 3 :=
      hh18NextInputErrorRate_le_cubic _ hnextsmall
    _ ≤ hh18IterationScale ^ 2 *
          (hh18ErrorIteration epsilon hsmall depth).1 ^ 3 :=
      mul_le_mul_of_nonneg_right
        two_mul_residualCubicCoefficient_le_iterationScale_sq (pow_nonneg hrate 3)
    _ = (hh18ErrorIteration epsilon hsmall depth).1 *
          (hh18IterationScale * (hh18ErrorIteration epsilon hsmall depth).1) ^ 2 := by
      ring
    _ ≤ (hh18ErrorIteration epsilon hsmall depth).1 * (1 / 2 : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hscale_sq hrate
    _ = (hh18ErrorIteration epsilon hsmall depth).1 / 4 := by ring

/-- The contractive actual rates have a finite geometric tail bound. -/
theorem iteration_rate_sum_with_tail_le (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    (∑ stage : Fin depth, (hh18ErrorIteration epsilon hsmall stage.1).1) +
      (4 / 3 : ℝ) * (hh18ErrorIteration epsilon hsmall depth).1 ≤
        (4 / 3 : ℝ) * epsilon.1 := by
  induction depth with
  | zero =>
      change 0 + (4 / 3 : ℝ) * epsilon.1 ≤ (4 / 3 : ℝ) * epsilon.1
      linarith
  | succ depth ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hnext := iteration_next_le_quarter epsilon hsmall depth
      nlinarith

/-- Summing only the finite actual stages is no larger than the same geometric
tail budget. -/
theorem iteration_rate_sum_le (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    ∑ stage : Fin depth, (hh18ErrorIteration epsilon hsmall stage.1).1 ≤
      (4 / 3 : ℝ) * epsilon.1 := by
  calc
    ∑ stage : Fin depth, (hh18ErrorIteration epsilon hsmall stage.1).1 ≤
        (∑ stage : Fin depth, (hh18ErrorIteration epsilon hsmall stage.1).1) +
          (4 / 3 : ℝ) * (hh18ErrorIteration epsilon hsmall depth).1 := by
      exact le_add_of_nonneg_right
        (mul_nonneg (by norm_num) (hh18ErrorIteration epsilon hsmall depth).property.1)
    _ ≤ (4 / 3 : ℝ) * epsilon.1 :=
      iteration_rate_sum_with_tail_le epsilon hsmall depth

private theorem iteration_scale_thirty_le : 30 ≤ hh18IterationScale := by
  have hcoefficient : 0 ≤ residualCubicCoefficient := by
    unfold residualCubicCoefficient
    positivity
  unfold hh18IterationScale
  linarith

/-- The actual all-zero branch and Bernoulli's inequality give the literal
one-block loss estimate at every reached rate. -/
theorem stage_success_one_sub_fifteen_rate_le
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    1 - 15 * (hh18ErrorIteration epsilon hsmall depth).1 ≤
      rawSuccessMass (hh18ErrorIteration epsilon hsmall depth) := by
  have hrate : 0 ≤ (hh18ErrorIteration epsilon hsmall depth).1 :=
    (hh18ErrorIteration epsilon hsmall depth).property.1
  calc
    1 - 15 * (hh18ErrorIteration epsilon hsmall depth).1 ≤
        (1 - (hh18ErrorIteration epsilon hsmall depth).1) ^ 15 := by
      have hbernoulli := one_add_mul_sub_le_pow
        (a := 1 - (hh18ErrorIteration epsilon hsmall depth).1)
        (by linarith [(hh18ErrorIteration epsilon hsmall depth).property.2]) 15
      calc
        1 - 15 * (hh18ErrorIteration epsilon hsmall depth).1 =
            1 + 15 * ((1 - (hh18ErrorIteration epsilon hsmall depth).1) - 1) := by ring
        _ ≤ (1 - (hh18ErrorIteration epsilon hsmall depth).1) ^ 15 := hbernoulli
    _ = (1 - (hh18ErrorIteration epsilon hsmall depth).1) ^ resourceCount := by
      rw [resourceCount_eq_fifteen]
    _ ≤ rawSuccessMass (hh18ErrorIteration epsilon hsmall depth) :=
      rawSuccessMass_allZeroWord_le _

/-- Abstract finite product-versus-loss-sum accounting. -/
theorem finite_one_sub_sum_le_product {ι : Type*} (s : Finset ι)
    (loss : ι → ℝ) (hlossNonneg : ∀ i ∈ s, 0 ≤ loss i)
    (hlossLeOne : ∀ i ∈ s, loss i ≤ 1) :
    1 - ∑ i ∈ s, loss i ≤ ∏ i ∈ s, (1 - loss i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hsumNonneg : 0 ≤ ∑ i ∈ s, loss i :=
        Finset.sum_nonneg fun i hi =>
          hlossNonneg i (Finset.mem_insert_of_mem hi)
      have hrest :
          1 - ∑ i ∈ s, loss i ≤ ∏ i ∈ s, (1 - loss i) :=
        ih (fun i hi => hlossNonneg i (Finset.mem_insert_of_mem hi))
          (fun i hi => hlossLeOne i (Finset.mem_insert_of_mem hi))
      calc
        1 - (loss a + ∑ i ∈ s, loss i) ≤
            (1 - loss a) * (1 - ∑ i ∈ s, loss i) := by
          nlinarith [hlossNonneg a (Finset.mem_insert_self a s)]
        _ ≤ (1 - loss a) * ∏ i ∈ s, (1 - loss i) :=
          mul_le_mul_of_nonneg_left hrest (by
            linarith [hlossLeOne a (Finset.mem_insert_self a s)])

/-- The finite product of actual one-block masses for separately pooled fresh
layers.  This is an accounting factor, not a global all-block success event. -/
noncomputable def hh18DepthYieldFactor
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) : NNReal := by
  classical
  exact ⟨∏ stage : Fin depth,
    rawSuccessMass (hh18ErrorIteration epsilon hsmall stage.1),
    Finset.prod_nonneg fun stage _ => (rawSuccessMass_pos _).le⟩

/-- The finite yield product is the product of the success probabilities of
the actual independently indexed stage runs.  This is accounting for fresh
resources, not an assertion of a joint all-stage event. -/
theorem hh18DepthYieldFactor_eq_actualStageSuccessProduct
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    (hh18DepthYieldFactor epsilon hsmall depth : ℝ) =
      ∏ stage : Fin depth,
        (hh18ActualStageRun epsilon hsmall stage.1).successProbability := by
  classical
  change (∏ stage : Fin depth,
    rawSuccessMass (hh18ErrorIteration epsilon hsmall stage.1)) = _
  apply Finset.prod_congr rfl
  intro stage _
  exact (hh18ActualStageRun_successProbability epsilon hsmall stage.1).symm

theorem hh18DepthYieldFactor_pos
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    0 < (hh18DepthYieldFactor epsilon hsmall depth : ℝ) := by
  classical
  change 0 < ∏ stage : Fin depth,
    rawSuccessMass (hh18ErrorIteration epsilon hsmall stage.1)
  exact Finset.prod_pos fun stage _ => rawSuccessMass_pos _

/-- Every finite actual fresh-layer accounting product is at least one half. -/
theorem hh18DepthYieldFactor_lower_bound
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    (1 : ℝ) / 2 ≤ (hh18DepthYieldFactor epsilon hsmall depth : ℝ) := by
  classical
  let loss : Fin depth → ℝ := fun stage =>
    15 * (hh18ErrorIteration epsilon hsmall stage.1).1
  have hlossNonneg (stage : Fin depth) : 0 ≤ loss stage := by
    exact mul_nonneg (by norm_num) (hh18ErrorIteration epsilon hsmall stage.1).property.1
  have hlossLeOne (stage : Fin depth) : loss stage ≤ 1 := by
    have hstage := iteration_scaled_small epsilon hsmall stage.1
    have hthirtyRate :
        30 * (hh18ErrorIteration epsilon hsmall stage.1).1 ≤
          hh18IterationScale * (hh18ErrorIteration epsilon hsmall stage.1).1 :=
      mul_le_mul_of_nonneg_right iteration_scale_thirty_le
        (hh18ErrorIteration epsilon hsmall stage.1).property.1
    dsimp [loss]
    linarith
  have hsumRate := iteration_rate_sum_le epsilon hsmall depth
  have hinitialRate : 30 * epsilon.1 ≤ hh18IterationScale * epsilon.1 :=
    mul_le_mul_of_nonneg_right iteration_scale_thirty_le epsilon.property.1
  have hthirtyEpsilon : 30 * epsilon.1 ≤ 1 / 2 :=
    hinitialRate.trans hsmall
  have hepsilon : epsilon.1 ≤ (1 : ℝ) / 60 := by
    linarith
  have hsumLoss : ∑ stage : Fin depth, loss stage ≤ 1 / 2 := by
    dsimp [loss]
    rw [← Finset.mul_sum]
    calc
      15 * ∑ stage : Fin depth,
          (hh18ErrorIteration epsilon hsmall stage.1).1 ≤
          15 * ((4 / 3 : ℝ) * epsilon.1) :=
        mul_le_mul_of_nonneg_left hsumRate (by norm_num)
      _ ≤ 1 / 2 := by linarith
  have hproductLower :
      1 - ∑ stage : Fin depth, loss stage ≤
        ∏ stage : Fin depth,
          rawSuccessMass (hh18ErrorIteration epsilon hsmall stage.1) := by
    calc
      1 - ∑ stage : Fin depth, loss stage ≤
          ∏ stage : Fin depth, (1 - loss stage) := by
        simpa using (finite_one_sub_sum_le_product Finset.univ loss
          (fun stage _ => hlossNonneg stage)
          (fun stage _ => hlossLeOne stage))
      _ ≤ ∏ stage : Fin depth,
          rawSuccessMass (hh18ErrorIteration epsilon hsmall stage.1) := by
        refine Finset.prod_le_prod ?_ ?_
        · intro stage _
          linarith [hlossLeOne stage]
        · intro stage _
          dsimp [loss]
          exact stage_success_one_sub_fifteen_rate_le epsilon hsmall stage.1
  change (1 : ℝ) / 2 ≤ ∏ stage : Fin depth,
    rawSuccessMass (hh18ErrorIteration epsilon hsmall stage.1)
  linarith

/-- The literal finite-slot cost of the separately pooled fresh layers. -/
noncomputable def hh18DepthSuccessfulOutputCost
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) : ℝ :=
  DependentBatch.typedSuccessfulOutputCost (hh18DepthInputSlots depth)
    (hh18DepthOutputSlots depth) (hh18DepthYieldFactor epsilon hsmall depth)

theorem hh18DepthSuccessfulOutputCost_eq
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18DepthSuccessfulOutputCost epsilon hsmall depth =
      (15 : ℝ) ^ depth / (hh18DepthYieldFactor epsilon hsmall depth : ℝ) := by
  unfold hh18DepthSuccessfulOutputCost
  unfold DependentBatch.typedSuccessfulOutputCost
  unfold DependentBatch.typedInputOutputRatio
  rw [hh18DepthInputSlots_card, hh18DepthOutputSlots_card]
  simp only [Nat.cast_pow, Nat.cast_one, one_pow, div_one]
  norm_num

theorem hh18DepthSuccessfulOutputCost_pos
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    0 < hh18DepthSuccessfulOutputCost epsilon hsmall depth := by
  rw [hh18DepthSuccessfulOutputCost_eq]
  exact div_pos (by positivity) (hh18DepthYieldFactor_pos epsilon hsmall depth)

theorem hh18DepthSuccessfulOutputCost_le_constant_mul_pow
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18DepthSuccessfulOutputCost epsilon hsmall depth ≤ 2 * (15 : ℝ) ^ depth := by
  rw [hh18DepthSuccessfulOutputCost_eq]
  have hratioNonneg : 0 ≤ (15 : ℝ) ^ depth := by positivity
  have hyieldHalf : (1 : ℝ) / 2 ≤
      (hh18DepthYieldFactor epsilon hsmall depth : ℝ) :=
    hh18DepthYieldFactor_lower_bound epsilon hsmall depth
  calc
    (15 : ℝ) ^ depth / (hh18DepthYieldFactor epsilon hsmall depth : ℝ) ≤
        (15 : ℝ) ^ depth / ((1 : ℝ) / 2) :=
      div_le_div_of_nonneg_left hratioNonneg (by norm_num) hyieldHalf
    _ = 2 * (15 : ℝ) ^ depth := by ring

/-- Every successor uses the fixed one-output transpose route from the actual
fifteen parent resources to the next child input positions. -/
def hh18DepthSuccessorRouting (_depth : Nat) :
    Fin resourceCount × BatchOutputPort ≃ BatchOutputPort × Fin resourceCount :=
  DependentBatch.transposeRouting resourceCount 1

/-- The physical family supplied to the HH18 block at a reached depth. -/
noncomputable def hh18DepthStageResource
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    ResourceInput resourceCount QubitSpace :=
  noisyResources (hh18ErrorIteration epsilon hsmall depth)

theorem hh18DepthStageResource_eq_noisyResources
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18DepthStageResource epsilon hsmall depth =
      noisyResources (hh18ErrorIteration epsilon hsmall depth) := by
  rfl

/-- The next physical input family is literally the inverse-phase/dephased
accepted output of the preceding actual HH18 stage. -/
theorem hh18DepthStageResource_succ
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18DepthStageResource epsilon hsmall (depth + 1) =
      fun _ => hh18AcceptedOutputAsNextInput (hh18ErrorIteration epsilon hsmall depth) := by
  funext slot
  change HH18NoisyInput.noisyTInvResource
      (hh18ErrorIteration epsilon hsmall (depth + 1)) =
    hh18AcceptedOutputAsNextInput (hh18ErrorIteration epsilon hsmall depth)
  rw [hh18ErrorIteration_succ]
  have hnext : hh18NextInputSmallDomain
      (hh18ErrorIteration epsilon hsmall depth) :=
    hh18IterationNextSmall (hh18IterationState epsilon hsmall depth)
  simpa only using
    (hh18AcceptedOutputAsNextInput_eq_noisyTInvResource
      (hh18ErrorIteration epsilon hsmall depth) hnext).symm

/-- The routed input slot of the unique next child block.  Its source is one
output port of a designated fresh parent run. -/
def hh18DepthRoutedChildInputSlot (depth : Nat)
    (port : BatchOutputPort) (parent : Fin resourceCount) :
    BatchOutputPort × Fin resourceCount :=
  hh18DepthSuccessorRouting depth
    (DependentBatch.childInputSlot port parent)

@[simp] theorem hh18DepthRoutedChildInputSlot_apply (depth : Nat)
    (port : BatchOutputPort) (parent : Fin resourceCount) :
    hh18DepthRoutedChildInputSlot depth port parent = (port, parent) :=
  rfl

/-- Routing is injective within the fixed child, so its fifteen inputs use
distinct indexed parent executions. -/
theorem hh18DepthRoutedChildInputSlot_injective (depth : Nat)
    (port : BatchOutputPort) :
    Function.Injective (hh18DepthRoutedChildInputSlot depth port) := by
  intro left right hroute
  apply DependentBatch.childInputSlot_injective port
  apply (hh18DepthSuccessorRouting depth).injective
  exact hroute

/-- An indexed fresh parent run at one physical HH18 stage.  The index records
resource provenance only; it asserts no independence between executions. -/
noncomputable def hh18DepthFreshParentRun
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat)
    (_parent : Fin resourceCount) :=
  hh18ActualStageRun epsilon hsmall depth

/-- The actual accepted parent output, transported and dephased into the
physical resource consumed by the routed child input. -/
noncomputable def hh18DepthFreshParentAcceptedNextInput
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat)
    (source : BatchOutputPort × Fin resourceCount) : DensityOperator QubitSpace :=
  hh18AcceptedRunOutputAsNextInput
    (hh18DepthFreshParentRun epsilon hsmall depth source.2)

theorem hh18DepthFreshParentAcceptedNextInput_eq_handoff
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat)
    (source : BatchOutputPort × Fin resourceCount) :
    hh18DepthFreshParentAcceptedNextInput epsilon hsmall depth source =
      hh18AcceptedOutputAsNextInput (hh18ErrorIteration epsilon hsmall depth) := by
  rfl

/-- The actual child resources are the transported accepted outputs of the
fifteen routed, distinct fresh parent runs. -/
noncomputable def hh18DepthRoutedChildResources
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    ResourceInput resourceCount QubitSpace :=
  fun parent => hh18DepthFreshParentAcceptedNextInput epsilon hsmall depth
    (hh18DepthRoutedChildInputSlot depth 0 parent)

/-- The routed actual child resources are exactly the compiled next-stage
resource family, by the existing physical accepted-output handoff. -/
theorem hh18DepthRoutedChildResources_eq_stageResource_succ
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18DepthRoutedChildResources epsilon hsmall depth =
      hh18DepthStageResource epsilon hsmall (depth + 1) := by
  funext parent
  unfold hh18DepthRoutedChildResources
  rw [hh18DepthFreshParentAcceptedNextInput_eq_handoff]
  rw [hh18DepthStageResource_succ]

/-- The next child execution consumes the actual routed parent-output
resources. -/
noncomputable def hh18DepthRoutedChildRun
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :=
  resourceDecodedRun (hh18DepthRoutedChildResources epsilon hsmall depth)

/-- At every finite depth, the child run built from routed fresh parent
outputs is the actual next-stage HH18 run. -/
theorem hh18DepthRoutedChildRun_eq_actualStageRun_succ
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18DepthRoutedChildRun epsilon hsmall depth =
      hh18ActualStageRun epsilon hsmall (depth + 1) := by
  unfold hh18DepthRoutedChildRun hh18ActualStageRun
  rw [hh18DepthRoutedChildResources_eq_stageResource_succ]
  rfl

/-- The one-level protocol's literal physical error-word distribution, exposed
as a flagged one-port batch.  Its accepted flag is the actual HH18 syndrome
predicate for that word; it makes no global claim about simultaneous success
of other blocks. -/
noncomputable def oneLevelFlaggedBatch
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    DependentBatch.FiniteFlaggedBatch BatchOutputPort PhysicalErrorWord where
  weight := HH18NoisyInput.errorWordWeight epsilon
  weight_nonneg := HH18NoisyInput.errorWordWeight_nonneg epsilon
  total_weight := by
    simpa using HH18NoisyInput.errorWordWeight_sum (ι := PhysicalSite) epsilon
  accepted := fun error _ => decide (HH18SyndromeDecoding.Accepts error)

/-- A physical error word accepts the unique port exactly when the real HH18
stabilizer measurement accepts that word. -/
theorem oneLevelFlaggedBatch_acceptedPortCount
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (error : PhysicalErrorWord) :
    DependentBatch.acceptedPortCount (oneLevelFlaggedBatch epsilon) error =
      if HH18SyndromeDecoding.Accepts error then 1 else 0 := by
  classical
  unfold DependentBatch.acceptedPortCount
  by_cases haccept : HH18SyndromeDecoding.Accepts error <;>
    simp [oneLevelFlaggedBatch, haccept]

/-- The expected accepted-port yield of the actual flagged batch. -/
noncomputable def oneLevelExpectedYield
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  DependentBatch.expectedAcceptedPorts (oneLevelFlaggedBatch epsilon)

/-- The batch accounting yield is exactly the actual HH18 accepted Born mass. -/
theorem oneLevelExpectedYield_eq_success
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    oneLevelExpectedYield epsilon = endpointWeight (noisyResources epsilon) .accepted := by
  calc
    oneLevelExpectedYield epsilon = rawSuccessMass epsilon := by
      unfold oneLevelExpectedYield
      exact expectedAcceptedPorts_eq_explicit_selected_mass
        (oneLevelFlaggedBatch epsilon) physicalErrorWords HH18SyndromeDecoding.Accepts
        (rawSuccessMass epsilon) (by rfl)
        (oneLevelFlaggedBatch_acceptedPortCount epsilon) (by rfl)
    _ = endpointWeight (noisyResources epsilon) .accepted :=
      (endpointWeight_accepted_eq_rawSuccessMass epsilon).symm

/-- The actual expected one-block yield is positive, because it is exactly
the positive accepted Born mass proved from the zero-error physical branch. -/
theorem oneLevelExpectedYield_pos
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    0 < oneLevelExpectedYield epsilon := by
  rw [oneLevelExpectedYield_eq_success]
  exact endpointWeight_accepted_pos epsilon

/-- The nonnegative yield factor consumed by the existing typed-cost adapter. -/
noncomputable def oneLevelYieldFactor
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : NNReal :=
  ⟨oneLevelExpectedYield epsilon, (oneLevelExpectedYield_pos epsilon).le⟩

/-- Actual finite successful-output cost for one HH18 block: the finite input
slot ratio divided by its measured expected accepted-port yield. -/
noncomputable def oneLevelSuccessfulOutputCost
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  DependentBatch.typedSuccessfulOutputCost BatchInputSlot BatchOutputPort
    (oneLevelYieldFactor epsilon)

/-- The finite input/output ratio used by this actual one-level consumer is
derived from its slot types, rather than stored as protocol metadata. -/
noncomputable def oneLevelInputOutputRatio : ℝ :=
  DependentBatch.typedInputOutputRatio BatchInputSlot BatchOutputPort

theorem oneLevelInputOutputRatio_eq_fifteen : oneLevelInputOutputRatio = 15 := by
  unfold oneLevelInputOutputRatio DependentBatch.typedInputOutputRatio
  simp [resourceCount_eq_fifteen]

/-- The actual successful-output cost is finite and is computed from the
fifteen physical slots and the measured success probability. -/
theorem oneLevelSuccessfulOutputCost_eq_fifteen_div_success
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    oneLevelSuccessfulOutputCost epsilon =
      15 / endpointWeight (noisyResources epsilon) .accepted := by
  unfold oneLevelSuccessfulOutputCost DependentBatch.typedSuccessfulOutputCost
  change oneLevelInputOutputRatio / (oneLevelYieldFactor epsilon : ℝ) = _
  rw [oneLevelInputOutputRatio_eq_fifteen]
  change 15 / oneLevelExpectedYield epsilon = _
  rw [oneLevelExpectedYield_eq_success]

theorem oneLevelSuccessfulOutputCost_pos
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    0 < oneLevelSuccessfulOutputCost epsilon := by
  rw [oneLevelSuccessfulOutputCost_eq_fifteen_div_success]
  exact div_pos (by norm_num) (endpointWeight_accepted_pos epsilon)

/-- The one-level HH18 physical protocol as a genuine #458 family with the
unique logical output as its family index. -/
noncomputable def hh18OneLevelProtocolFamily
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    DistillationProtocolFamily QubitSpace PhysicalRegister LogicalRegister PUnit where
  targetError := fun _ =>
    (2 * residualCubicCoefficient) * epsilon.1 ^ 3
  protocol := fun _ => hh18MagicStateDistillationProtocol epsilon
  outputResourceCount := fun _ => 1
  outputResourceCount_pos := by
    intro _
    exact Nat.zero_lt_succ 0
  successfulOutputError_le_targetError := by
    intro _
    rw [hh18MagicStateDistillationProtocol_successfulOutputError]
    calc
      hh18OutputTraceError
          (resourceDecodedRun (noisyResources epsilon)).acceptedOutput
          idealLogicalTOutput ≤ 2 * acceptedResidualError epsilon :=
        acceptedOutputTraceError_le_two_mul_acceptedResidual epsilon
      _ ≤ 2 * (residualCubicCoefficient * epsilon.1 ^ 3) :=
        mul_le_mul_of_nonneg_left
          (acceptedResidualError_le_cubic epsilon) (by norm_num)
      _ = (2 * residualCubicCoefficient) * epsilon.1 ^ 3 := by
        exact (mul_assoc _ _ _).symm

/-- The #458 target is the explicit cubic bound derived from the actual
accepted decoded output, not the protocol error repeated as a definition. -/
theorem hh18OneLevelProtocolFamily_targetError
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (hh18OneLevelProtocolFamily epsilon).targetError PUnit.unit =
      (2 * residualCubicCoefficient) * epsilon.1 ^ 3 :=
  rfl

/-- The family index exposes the actual resource-consuming HH18 protocol. -/
theorem hh18OneLevelProtocolFamily_protocol
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (hh18OneLevelProtocolFamily epsilon).protocol PUnit.unit =
      hh18MagicStateDistillationProtocol epsilon :=
  rfl

/-- The family protocol's run is the literal resource-decoded physical run. -/
theorem hh18OneLevelProtocolFamily_run
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    ((hh18OneLevelProtocolFamily epsilon).protocol PUnit.unit).run =
      resourceDecodedRun (noisyResources epsilon) :=
  rfl

/-- The #458 family stores the actual physical HH18 accepted Born mass. -/
theorem hh18OneLevelProtocolFamily_successProbability
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    ((hh18OneLevelProtocolFamily epsilon).protocol PUnit.unit).run.successProbability =
      rawSuccessMass epsilon := by
  change endpointWeight (noisyResources epsilon) .accepted = rawSuccessMass epsilon
  exact endpointWeight_accepted_eq_rawSuccessMass epsilon

/-- The finite one-level slot cost is exactly the corresponding #458 family
successful-output cost. -/
theorem oneLevelSuccessfulOutputCost_eq_oneLevelProtocolFamily
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    oneLevelSuccessfulOutputCost epsilon =
      (hh18OneLevelProtocolFamily epsilon).successfulOutputCost PUnit.unit := by
  unfold oneLevelSuccessfulOutputCost
  refine DependentBatch.typedSuccessfulOutputCost_eq_distillationProtocolFamily_successfulOutputCost
    (hh18OneLevelProtocolFamily epsilon) PUnit.unit BatchInputSlot BatchOutputPort
    (oneLevelYieldFactor epsilon) ?_ ?_ ?_
  · change Fintype.card (Fin resourceCount) = resourceCount
    simp
  · change Fintype.card (Fin 1) = 1
    simp
  · change oneLevelExpectedYield epsilon =
      ((hh18OneLevelProtocolFamily epsilon).protocol PUnit.unit).run.successProbability
    rw [oneLevelExpectedYield_eq_success,
      hh18OneLevelProtocolFamily_successProbability]
    exact endpointWeight_accepted_eq_rawSuccessMass epsilon

/-- A finite collection of whole physical HH18 blocks.  This records no
cross-block independence: accounting uses only finite linearity of the
individual measured distributions. -/
noncomputable def oneLevelFlaggedPool
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (count : Nat) :
    Fin count → DependentBatch.FiniteFlaggedBatch BatchOutputPort PhysicalErrorWord :=
  fun _ => oneLevelFlaggedBatch epsilon

/-- Pooled expected yield is the sum of actual block yields, with no
all-blocks-success event introduced. -/
theorem oneLevelPooledExpectedYield
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (count : Nat) :
    DependentBatch.pooledExpectedAcceptedPorts count
      (oneLevelFlaggedPool epsilon count) =
        (count : ℝ) * endpointWeight (noisyResources epsilon) .accepted := by
  unfold DependentBatch.pooledExpectedAcceptedPorts oneLevelFlaggedPool
  change (∑ _ : Fin count, oneLevelExpectedYield epsilon) = _
  rw [oneLevelExpectedYield_eq_success]
  simp [mul_comm]

/-- The physical parent-output grid for the first genuine HH18 composition
step: fifteen independently produced one-port block outputs. -/
abbrev depthTwoParentOutputSlots := Fin resourceCount × BatchOutputPort

/-- The child block's fifteen input positions, presented after finite routing. -/
abbrev depthTwoChildInputSlots := BatchOutputPort × Fin resourceCount

/-- The first composition routing is the adapter's literal transpose, so the
sole child receives one output from each distinct parent block. -/
def depthTwoRouting : depthTwoParentOutputSlots ≃ depthTwoChildInputSlots :=
  DependentBatch.transposeRouting resourceCount 1

@[simp] theorem depthTwoRouting_apply
    (parent : Fin resourceCount) (port : BatchOutputPort) :
    depthTwoRouting (parent, port) = (port, parent) :=
  rfl

/-- Each routed child input has a distinct parent source; this is the concrete
no-duplicate resource routing fact needed before a subsequent physical layer
can consume these outputs. -/
theorem depthTwoChildInputSlot_injective (port : BatchOutputPort) :
    Function.Injective (fun parent : Fin resourceCount =>
      depthTwoRouting (DependentBatch.childInputSlot port parent)) := by
  intro left right hroute
  apply DependentBatch.childInputSlot_injective port
  apply depthTwoRouting.injective
  exact hroute

/-- The finite actual layer-yield product gains exactly the next stage's
measured accepted mass. -/
theorem hh18DepthYieldFactor_succ
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    (hh18DepthYieldFactor epsilon hsmall (depth + 1) : ℝ) =
      (hh18DepthYieldFactor epsilon hsmall depth : ℝ) *
        rawSuccessMass (hh18ErrorIteration epsilon hsmall depth) := by
  classical
  change (∏ stage : Fin (depth + 1),
    rawSuccessMass (hh18ErrorIteration epsilon hsmall stage.1)) =
      (∏ stage : Fin depth,
        rawSuccessMass (hh18ErrorIteration epsilon hsmall stage.1)) *
          rawSuccessMass (hh18ErrorIteration epsilon hsmall depth)
  simpa using (Fin.prod_univ_castSucc
    (fun stage : Fin (depth + 1) =>
      rawSuccessMass (hh18ErrorIteration epsilon hsmall stage.1)))

/-- The restart factor is the success probability of the actual final stage
run, as identified by the physical stage-run invariant. -/
theorem hh18DepthYieldFactor_succ_actualStageRun
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    (hh18DepthYieldFactor epsilon hsmall (depth + 1) : ℝ) =
      (hh18DepthYieldFactor epsilon hsmall depth : ℝ) *
        (hh18ActualStageRun epsilon hsmall depth).successProbability := by
  rw [hh18DepthYieldFactor_succ,
    hh18ActualStageRun_successProbability]

/-- The depth-one accounting factor is the actual one-level yield factor. -/
theorem hh18DepthYieldFactor_one_eq_oneLevelYieldFactor
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) :
    (hh18DepthYieldFactor epsilon hsmall 1 : ℝ) =
      (oneLevelYieldFactor epsilon : ℝ) := by
  change (∏ stage : Fin 1,
    rawSuccessMass (hh18ErrorIteration epsilon hsmall stage.1)) =
      oneLevelExpectedYield epsilon
  rw [Fin.prod_univ_one]
  change rawSuccessMass epsilon = oneLevelExpectedYield epsilon
  rw [oneLevelExpectedYield_eq_success,
    endpointWeight_accepted_eq_rawSuccessMass]

/-- At depth one, the literal depth accounting cost is the actual one-level
successful-output cost. -/
theorem hh18DepthSuccessfulOutputCost_one_eq_oneLevelSuccessfulOutputCost
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) :
    hh18DepthSuccessfulOutputCost epsilon hsmall 1 =
      oneLevelSuccessfulOutputCost epsilon := by
  rw [hh18DepthSuccessfulOutputCost_eq,
    oneLevelSuccessfulOutputCost_eq_fifteen_div_success]
  have hyield :
      (hh18DepthYieldFactor epsilon hsmall 1 : ℝ) =
        endpointWeight (noisyResources epsilon) .accepted := by
    calc
      (hh18DepthYieldFactor epsilon hsmall 1 : ℝ) =
          (oneLevelYieldFactor epsilon : ℝ) :=
        hh18DepthYieldFactor_one_eq_oneLevelYieldFactor epsilon hsmall
      _ = oneLevelExpectedYield epsilon := rfl
      _ = endpointWeight (noisyResources epsilon) .accepted :=
        oneLevelExpectedYield_eq_success epsilon
  rw [hyield]
  norm_num

/-- Source-neutral depth-one handoff for downstream accounting: the derived
finite depth cost is the actual #458 one-level family cost. -/
theorem hh18DepthSuccessfulOutputCost_one_eq_oneLevelProtocolFamily
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) :
    hh18DepthSuccessfulOutputCost epsilon hsmall 1 =
      (hh18OneLevelProtocolFamily epsilon).successfulOutputCost PUnit.unit := by
  calc
    hh18DepthSuccessfulOutputCost epsilon hsmall 1 =
        oneLevelSuccessfulOutputCost epsilon :=
      hh18DepthSuccessfulOutputCost_one_eq_oneLevelSuccessfulOutputCost epsilon hsmall
    _ = (hh18OneLevelProtocolFamily epsilon).successfulOutputCost PUnit.unit :=
      oneLevelSuccessfulOutputCost_eq_oneLevelProtocolFamily epsilon

/-- Restarting one fresh HH18 layer multiplies the actual successful-output
cost by fifteen and divides by that layer's measured accepted mass. -/
theorem hh18DepthSuccessfulOutputCost_succ
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18DepthSuccessfulOutputCost epsilon hsmall (depth + 1) =
      15 * hh18DepthSuccessfulOutputCost epsilon hsmall depth /
        rawSuccessMass (hh18ErrorIteration epsilon hsmall depth) := by
  rw [← hh18ActualStageRun_successProbability epsilon hsmall depth]
  rw [hh18DepthSuccessfulOutputCost_eq,
    hh18DepthSuccessfulOutputCost_eq,
    hh18DepthYieldFactor_succ_actualStageRun]
  have hyield : (hh18DepthYieldFactor epsilon hsmall depth : ℝ) ≠ 0 :=
    ne_of_gt (hh18DepthYieldFactor_pos epsilon hsmall depth)
  have hsuccess : (hh18ActualStageRun epsilon hsmall depth).successProbability ≠ 0 :=
    ne_of_gt (by
      rw [hh18ActualStageRun_successProbability]
      exact rawSuccessMass_pos _)
  rw [pow_succ]
  field_simp [hyield, hsuccess]

/-- The actual physical input slots at a natural HH18 recursion depth. -/
abbrev hh18DepthScheduleInputSlots (depth : Nat) := hh18DepthInputSlots depth

/-- The actual logical output slots at a natural HH18 recursion depth. -/
abbrev hh18DepthScheduleOutputSlots (depth : Nat) := hh18DepthOutputSlots depth

/-- The compiled cubic envelope is the schedule's finite target error. -/
abbrev hh18DepthScheduleTargetError
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat) : ℝ :=
  hh18CubicErrorEnvelope epsilon depth

/-- The reached physical diagonal error at a natural recursion depth. -/
abbrev hh18DepthScheduleActualOutputError
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) : ℝ :=
  (hh18ErrorIteration epsilon hsmall depth).1

/-- The finite actual fresh-layer accounting yield at one schedule depth. -/
abbrev hh18DepthScheduleYieldFactor
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) : NNReal :=
  hh18DepthYieldFactor epsilon hsmall depth

/-- The literal fixed-block logarithmic exponent determined by the cubic
recursion and fifteen-to-one slot ratio. -/
noncomputable def hh18DepthScheduleGamma : ℝ :=
  Real.log 15 / Real.log 3

/-- The positive logarithmic growth base derived from the initial scaled
physical error. -/
noncomputable def hh18DepthScheduleLogGrowthBase
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  -Real.log (hh18IterationScale * epsilon.1)

/-- The finite coefficient derived from the actual yield lower bound and the
initial scaled error; it is not supplied as schedule metadata. -/
noncomputable def hh18DepthScheduleCostCoefficient
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  2 / Real.rpow (hh18DepthScheduleLogGrowthBase epsilon)
    hh18DepthScheduleGamma

private theorem hh18DepthSchedule_residualCoefficient_nonneg :
    0 ≤ residualCubicCoefficient := by
  unfold residualCubicCoefficient
  positivity

private theorem hh18DepthScheduleScale_one_le : 1 ≤ hh18IterationScale := by
  unfold hh18IterationScale
  nlinarith [hh18DepthSchedule_residualCoefficient_nonneg]

/-- The actual finite input-slot count is exactly fifteen to the schedule
depth. -/
theorem hh18DepthScheduleInputSlots_card (depth : Nat) :
    Fintype.card (hh18DepthScheduleInputSlots depth) = 15 ^ depth :=
  hh18DepthInputSlots_card depth

/-- The actual finite output-slot count is exactly one to the schedule
depth. -/
theorem hh18DepthScheduleOutputSlots_card (depth : Nat) :
    Fintype.card (hh18DepthScheduleOutputSlots depth) = 1 ^ depth :=
  hh18DepthOutputSlots_card depth

/-- A positive initial physical rate makes every compiled target positive. -/
theorem hh18DepthSchedule_targetError_pos
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (depth : Nat) :
    0 < hh18DepthScheduleTargetError epsilon depth := by
  have hscaled : 0 < hh18IterationScale *
      hh18DepthScheduleTargetError epsilon depth := by
    rw [hh18CubicErrorEnvelope_closed_form]
    exact pow_pos (mul_pos hh18IterationScale_pos hepsilon) _
  rcases (mul_pos_iff.mp hscaled) with hpositive | hnegative
  · exact hpositive.2
  · exact False.elim ((not_lt_of_ge hh18IterationScale_pos.le) hnegative.1)

/-- Initial scaled smallness makes every compiled target strictly below one. -/
theorem hh18DepthSchedule_targetError_lt_one
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18DepthScheduleTargetError epsilon depth < 1 := by
  have hbaseNonneg : 0 ≤ hh18IterationScale * epsilon.1 :=
    mul_nonneg hh18IterationScale_pos.le hepsilon.le
  have hpower :
      (hh18IterationScale * epsilon.1) ^ (3 ^ depth) ≤ (1 / 2 : ℝ) := by
    calc
      (hh18IterationScale * epsilon.1) ^ (3 ^ depth) ≤
          (1 / 2 : ℝ) ^ (3 ^ depth) :=
        pow_le_pow_left₀ hbaseNonneg hsmall _
      _ ≤ (1 / 2 : ℝ) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (one_le_pow₀ (by norm_num : (1 : Nat) ≤ 3))
      _ = (1 / 2 : ℝ) := by norm_num
  have hscaled : hh18IterationScale *
      hh18DepthScheduleTargetError epsilon depth ≤ 1 / 2 := by
    rw [hh18CubicErrorEnvelope_closed_form]
    exact hpower
  have htargetPos := hh18DepthSchedule_targetError_pos epsilon hepsilon depth
  have htarget_le_scaled : hh18DepthScheduleTargetError epsilon depth ≤
      hh18IterationScale * hh18DepthScheduleTargetError epsilon depth := by
    nlinarith [hh18DepthScheduleScale_one_le]
  linarith

/-- The recursively reached actual error is bounded by the schedule target. -/
theorem hh18DepthSchedule_actualOutputError_le_targetError
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18DepthScheduleActualOutputError epsilon hsmall depth ≤
      hh18DepthScheduleTargetError epsilon depth :=
  hh18ErrorIteration_le_cubicEnvelope epsilon hsmall depth

/-- Every finite actual schedule yield is strictly positive. -/
theorem hh18DepthSchedule_yield_pos
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    0 < (hh18DepthScheduleYieldFactor epsilon hsmall depth : ℝ) :=
  hh18DepthYieldFactor_pos epsilon hsmall depth

/-- The typed finite-slot cost has its exact actual fifteen-to-one form. -/
theorem hh18DepthScheduleSuccessfulOutputCost_eq
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    DependentBatch.typedSuccessfulOutputCost
      (hh18DepthScheduleInputSlots depth)
      (hh18DepthScheduleOutputSlots depth)
      (hh18DepthScheduleYieldFactor epsilon hsmall depth) =
        (15 : ℝ) ^ depth /
          (hh18DepthScheduleYieldFactor epsilon hsmall depth : ℝ) :=
  hh18DepthSuccessfulOutputCost_eq epsilon hsmall depth

/-- The fixed-block exponent is positive and is exactly `log 15 / log 3`. -/
theorem hh18DepthScheduleGamma_pos : 0 < hh18DepthScheduleGamma := by
  unfold hh18DepthScheduleGamma
  exact div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 15))
    (Real.log_pos (by norm_num : (1 : ℝ) < 3))

/-- The initial scaled physical error supplies a strictly positive logarithmic
growth base. -/
theorem hh18DepthScheduleLogGrowthBase_pos
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : hh18InitialSmallDomain epsilon) :
    0 < hh18DepthScheduleLogGrowthBase epsilon := by
  unfold hh18DepthScheduleLogGrowthBase
  apply neg_pos.mpr
  apply Real.log_neg
  · exact mul_pos hh18IterationScale_pos hepsilon
  · exact hsmall.trans_lt (by norm_num)

/-- The cost coefficient is positive because it is derived by dividing the
actual yield bound by a positive real power of the initial log base. -/
theorem hh18DepthScheduleCostCoefficient_pos
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : hh18InitialSmallDomain epsilon) :
    0 < hh18DepthScheduleCostCoefficient epsilon := by
  unfold hh18DepthScheduleCostCoefficient
  exact div_pos (by norm_num)
    (Real.rpow_pos_of_pos
      (hh18DepthScheduleLogGrowthBase_pos epsilon hepsilon hsmall) _)

/-- The real-power form of the fixed cubic exponent is exactly the literal
fifteen-to-one slot ratio at every finite depth. -/
theorem hh18DepthSchedule_rpow_three_pow_eq_fifteen_pow (depth : Nat) :
    Real.rpow ((3 : ℝ) ^ depth) hh18DepthScheduleGamma =
      (15 : ℝ) ^ depth := by
  calc
    Real.rpow ((3 : ℝ) ^ depth) hh18DepthScheduleGamma =
        Real.exp (Real.log ((3 : ℝ) ^ depth) * hh18DepthScheduleGamma) := by
      exact Real.rpow_def_of_pos (by positivity) _
    _ = Real.exp ((depth : ℝ) * Real.log 15) := by
      unfold hh18DepthScheduleGamma
      congr 1
      rw [Real.log_pow]
      field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 3))]
    _ = Real.rpow 15 (depth : ℝ) := by
      symm
      calc
        Real.rpow 15 (depth : ℝ) = Real.exp (Real.log 15 * (depth : ℝ)) :=
          Real.rpow_def_of_pos (by norm_num) _
        _ = Real.exp ((depth : ℝ) * Real.log 15) :=
          congrArg Real.exp (mul_comm _ _)
    _ = (15 : ℝ) ^ depth := Real.rpow_natCast _ _

/-- The initial log base multiplied by the literal cubic depth is no larger
than the logarithm of the reciprocal compiled target. -/
theorem hh18DepthSchedule_threePow_mul_logGrowthBase_le_log
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (depth : Nat) :
    (3 : ℝ) ^ depth * hh18DepthScheduleLogGrowthBase epsilon ≤
      Real.log (1 / hh18DepthScheduleTargetError epsilon depth) := by
  have hscalePos : 0 < hh18IterationScale := hh18IterationScale_pos
  have hbasePos : 0 < hh18IterationScale * epsilon.1 :=
    mul_pos hscalePos hepsilon
  have htargetPos : 0 < hh18DepthScheduleTargetError epsilon depth :=
    hh18DepthSchedule_targetError_pos epsilon hepsilon depth
  have hpowPos : 0 < (hh18IterationScale * epsilon.1) ^ (3 ^ depth) :=
    pow_pos hbasePos _
  have hreciprocal :
      1 / hh18DepthScheduleTargetError epsilon depth =
        hh18IterationScale /
          (hh18IterationScale * epsilon.1) ^ (3 ^ depth) := by
    field_simp [ne_of_gt htargetPos, ne_of_gt hpowPos]
    simpa [mul_comm] using
      (hh18CubicErrorEnvelope_closed_form epsilon depth).symm
  have hlogForm :
      Real.log (1 / hh18DepthScheduleTargetError epsilon depth) =
        Real.log hh18IterationScale +
          (3 : ℝ) ^ depth * hh18DepthScheduleLogGrowthBase epsilon := by
    rw [hreciprocal, Real.log_div (ne_of_gt hscalePos) (ne_of_gt hpowPos),
      Real.log_pow]
    push_cast
    unfold hh18DepthScheduleLogGrowthBase
    ring
  have hscaleLogNonneg : 0 ≤ Real.log hh18IterationScale :=
    Real.log_nonneg hh18DepthScheduleScale_one_le
  rw [hlogForm]
  linarith

/-- The literal successful-output cost is bounded by twice the fixed-block
real-power form. -/
theorem hh18DepthScheduleSuccessfulOutputCost_le_two_rpow
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    DependentBatch.typedSuccessfulOutputCost
      (hh18DepthScheduleInputSlots depth)
      (hh18DepthScheduleOutputSlots depth)
      (hh18DepthScheduleYieldFactor epsilon hsmall depth) ≤
        2 * Real.rpow ((3 : ℝ) ^ depth) hh18DepthScheduleGamma := by
  rw [hh18DepthSchedule_rpow_three_pow_eq_fifteen_pow]
  exact hh18DepthSuccessfulOutputCost_le_constant_mul_pow epsilon hsmall depth

/-- The actual finite-depth HH18 cost is bounded by the real-rpow of the
compiled cubic-target logarithm with its derived coefficient. -/
theorem hh18DepthScheduleSuccessfulOutputCost_le_cubicEnvelope_polylog
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    DependentBatch.typedSuccessfulOutputCost
      (hh18DepthScheduleInputSlots depth)
      (hh18DepthScheduleOutputSlots depth)
      (hh18DepthScheduleYieldFactor epsilon hsmall depth) ≤
        hh18DepthScheduleCostCoefficient epsilon *
          Real.rpow
            (Real.log (1 / hh18DepthScheduleTargetError epsilon depth))
            hh18DepthScheduleGamma := by
  have hbasePos : 0 < hh18DepthScheduleLogGrowthBase epsilon :=
    hh18DepthScheduleLogGrowthBase_pos epsilon hepsilon hsmall
  have hexponentPos : 0 < hh18DepthScheduleGamma :=
    hh18DepthScheduleGamma_pos
  have hlog :
      (3 : ℝ) ^ depth * hh18DepthScheduleLogGrowthBase epsilon ≤
        Real.log (1 / hh18DepthScheduleTargetError epsilon depth) :=
    hh18DepthSchedule_threePow_mul_logGrowthBase_le_log epsilon hepsilon
      depth
  have hpowComparison :
      Real.rpow ((3 : ℝ) ^ depth * hh18DepthScheduleLogGrowthBase epsilon)
          hh18DepthScheduleGamma ≤
        Real.rpow (Real.log (1 / hh18DepthScheduleTargetError epsilon depth))
          hh18DepthScheduleGamma :=
    Real.rpow_le_rpow
      (mul_nonneg (by positivity) hbasePos.le) hlog hexponentPos.le
  have hfactorization :
      Real.rpow ((3 : ℝ) ^ depth * hh18DepthScheduleLogGrowthBase epsilon)
          hh18DepthScheduleGamma =
        Real.rpow ((3 : ℝ) ^ depth) hh18DepthScheduleGamma *
          Real.rpow (hh18DepthScheduleLogGrowthBase epsilon)
            hh18DepthScheduleGamma :=
    Real.mul_rpow (by positivity) hbasePos.le
  have hbaseRpowPos :
      0 < Real.rpow (hh18DepthScheduleLogGrowthBase epsilon)
        hh18DepthScheduleGamma :=
    Real.rpow_pos_of_pos hbasePos _
  rw [hfactorization] at hpowComparison
  have htwiceComparison :
      2 * Real.rpow ((3 : ℝ) ^ depth) hh18DepthScheduleGamma *
          Real.rpow (hh18DepthScheduleLogGrowthBase epsilon)
            hh18DepthScheduleGamma ≤
        2 * Real.rpow
          (Real.log (1 / hh18DepthScheduleTargetError epsilon depth))
          hh18DepthScheduleGamma := by
    calc
      2 * Real.rpow ((3 : ℝ) ^ depth) hh18DepthScheduleGamma *
          Real.rpow (hh18DepthScheduleLogGrowthBase epsilon)
            hh18DepthScheduleGamma =
          2 * (Real.rpow ((3 : ℝ) ^ depth) hh18DepthScheduleGamma *
            Real.rpow (hh18DepthScheduleLogGrowthBase epsilon)
              hh18DepthScheduleGamma) := by ring
      _ ≤ 2 * Real.rpow
          (Real.log (1 / hh18DepthScheduleTargetError epsilon depth))
          hh18DepthScheduleGamma :=
        mul_le_mul_of_nonneg_left hpowComparison (by norm_num)
  calc
    DependentBatch.typedSuccessfulOutputCost
        (hh18DepthScheduleInputSlots depth)
        (hh18DepthScheduleOutputSlots depth)
        (hh18DepthScheduleYieldFactor epsilon hsmall depth) ≤
        2 * Real.rpow ((3 : ℝ) ^ depth) hh18DepthScheduleGamma :=
      hh18DepthScheduleSuccessfulOutputCost_le_two_rpow epsilon hsmall depth
    _ =
        (2 * Real.rpow ((3 : ℝ) ^ depth) hh18DepthScheduleGamma *
          Real.rpow (hh18DepthScheduleLogGrowthBase epsilon)
            hh18DepthScheduleGamma) /
          Real.rpow (hh18DepthScheduleLogGrowthBase epsilon)
            hh18DepthScheduleGamma := by
      field_simp [ne_of_gt hbaseRpowPos]
    _ ≤
        (2 * Real.rpow
          (Real.log (1 / hh18DepthScheduleTargetError epsilon depth))
          hh18DepthScheduleGamma) /
          Real.rpow (hh18DepthScheduleLogGrowthBase epsilon)
            hh18DepthScheduleGamma :=
      div_le_div_of_nonneg_right htwiceComparison hbaseRpowPos.le
    _ = hh18DepthScheduleCostCoefficient epsilon *
          Real.rpow
            (Real.log (1 / hh18DepthScheduleTargetError epsilon depth))
            hh18DepthScheduleGamma := by
      unfold hh18DepthScheduleCostCoefficient
      field_simp [ne_of_gt hbaseRpowPos]

/-- Every positive target is beaten by a finite compiled cubic-envelope
depth. -/
theorem hh18DepthSchedule_targetError_exists_lt
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : hh18InitialSmallDomain epsilon)
    (target : ℝ) (htarget : 0 < target) :
    ∃ depth : Nat, hh18DepthScheduleTargetError epsilon depth < target := by
  have hscalePos : 0 < hh18IterationScale := hh18IterationScale_pos
  have hbaseNonneg : 0 ≤ hh18IterationScale * epsilon.1 :=
    mul_nonneg hscalePos.le hepsilon.le
  have hbaseLtOne : hh18IterationScale * epsilon.1 < 1 :=
    hsmall.trans_lt (by norm_num)
  have nat_le_three_pow : ∀ n : Nat, n ≤ 3 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          n + 1 ≤ 3 ^ n + 1 := Nat.add_le_add_right ih 1
          _ ≤ 3 ^ n + 3 ^ n :=
            Nat.add_le_add_left (Nat.one_le_pow n 3 (by norm_num)) _
          _ = 3 ^ n * 2 := by ring
          _ ≤ 3 ^ n * 3 := Nat.mul_le_mul_left _ (by omega)
          _ = 3 ^ (n + 1) := by
            rw [pow_succ]
  obtain ⟨n, hpower⟩ := exists_pow_lt_of_lt_one
    (x := hh18IterationScale * target)
    (y := hh18IterationScale * epsilon.1)
    (mul_pos hscalePos htarget) hbaseLtOne
  have hnat : n ≤ 3 ^ n := nat_le_three_pow n
  have hscaledPower :
      (hh18IterationScale * epsilon.1) ^ (3 ^ n) <
        hh18IterationScale * target :=
    (pow_le_pow_of_le_one hbaseNonneg hbaseLtOne.le hnat).trans_lt hpower
  have hscaledTarget :
      hh18IterationScale * hh18DepthScheduleTargetError epsilon n <
        hh18IterationScale * target := by
    rw [hh18CubicErrorEnvelope_closed_form]
    exact hscaledPower
  exact ⟨n, lt_of_mul_lt_mul_left hscaledTarget hscalePos.le⟩

/-- The actual physically reached errors are cofinal below every positive
target, by the compiled envelope comparison. -/
theorem hh18DepthSchedule_actualOutputError_exists_le
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : hh18InitialSmallDomain epsilon)
    (target : ℝ) (htarget : 0 < target) :
    ∃ depth : Nat,
      hh18DepthScheduleActualOutputError epsilon hsmall depth ≤ target := by
  obtain ⟨depth, hdepth⟩ :=
    hh18DepthSchedule_targetError_exists_lt epsilon hepsilon hsmall target htarget
  exact ⟨depth, (hh18DepthSchedule_actualOutputError_le_targetError
    epsilon hsmall depth).trans hdepth.le⟩

/-- The typed schedule satisfies the source-neutral finite-slot cost
predicate with the derived fixed-block exponent and coefficient. -/
theorem hh18DepthSchedule_typedPolylogCostBound
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : hh18InitialSmallDomain epsilon) :
    DependentBatch.typedPolylogCostBound hh18DepthScheduleInputSlots
      hh18DepthScheduleOutputSlots (hh18DepthScheduleTargetError epsilon)
      (hh18DepthScheduleYieldFactor epsilon hsmall)
      hh18DepthScheduleGamma (hh18DepthScheduleCostCoefficient epsilon) := by
  refine ⟨(hh18DepthScheduleCostCoefficient_pos epsilon hepsilon hsmall).le, ?_⟩
  intro depth _ _
  refine ⟨hh18DepthSchedule_yield_pos epsilon hsmall depth, ?_⟩
  exact hh18DepthScheduleSuccessfulOutputCost_le_cubicEnvelope_polylog
    epsilon hepsilon hsmall depth

/-- The actual natural-depth HH18 schedule instantiates the physical
expected-yield overhead interface using only its separately proved finite
physical, error, yield, and cost facts. -/
theorem hh18DepthSchedule_physicalPolylogarithmicExpectedYieldOverhead
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : hh18InitialSmallDomain epsilon) :
    DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
      hh18DepthScheduleInputSlots hh18DepthScheduleOutputSlots
      (hh18DepthScheduleTargetError epsilon)
      (hh18DepthScheduleActualOutputError epsilon hsmall)
      (hh18DepthScheduleYieldFactor epsilon hsmall)
      hh18DepthScheduleGamma (hh18DepthScheduleCostCoefficient epsilon) := by
  rcases hh18DepthSchedule_typedPolylogCostBound epsilon hepsilon hsmall with
    ⟨hcoefficient, hcost⟩
  refine ⟨hcoefficient, ?_⟩
  intro depth htargetPos htargetLtOne
  obtain ⟨hyield, hcostBound⟩ := hcost depth htargetPos htargetLtOne
  exact ⟨hh18DepthSchedule_actualOutputError_le_targetError epsilon hsmall depth,
    hyield, hcostBound⟩

/-- The physical next stage is exactly the accepted output transported into
the next input family. -/
theorem hh18DepthSchedule_stageResource_succ
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18DepthStageResource epsilon hsmall (depth + 1) =
      fun _ => hh18AcceptedOutputAsNextInput
        (hh18ErrorIteration epsilon hsmall depth) :=
  hh18DepthStageResource_succ epsilon hsmall depth

end HH18Protocol
end Distillation
end QEC
