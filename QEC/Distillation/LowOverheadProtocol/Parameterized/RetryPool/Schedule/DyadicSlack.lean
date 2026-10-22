import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Schedule.FirstMoment
import QEC.Distillation.LowOverheadProtocol.Parameterized.SuccessResidual

/-!
# Parameterized HH18 decoded retry-pool dyadic slack

This internal layer fixes the source-derived dyadic denominator for one finite
pool.  It derives the corresponding natural attempt count and combines the
actual finite shortage bound with the one-block accepted mass estimate.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

local instance instDecodedRetryPoolDyadicSlackClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The source-derived denominator at one finite pooling stage. -/
def decodedRetryPoolDyadicDenominator (stage : Nat) : Nat :=
  2 ^ (stage + 3)

/-- Exact natural ceiling division, used only with a positive denominator. -/
def decodedRetryPoolCeilDiv (numerator denominator : Nat) : Nat :=
  (numerator + denominator - 1) / denominator

/-- The actual number of finite trials needed to request `required` accepted
blocks using the derived dyadic slack denominator. -/
def decodedRetryPoolDyadicAttempts (stage required : Nat) : Nat :=
  decodedRetryPoolCeilDiv
    (decodedRetryPoolDyadicDenominator stage * required)
    (decodedRetryPoolDyadicDenominator stage - 1)

private theorem decodedRetryPoolDyadicDenominator_ge_eight (stage : Nat) :
    8 ≤ decodedRetryPoolDyadicDenominator stage := by
  unfold decodedRetryPoolDyadicDenominator
  calc
    8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (stage + 3) := by
      apply Nat.pow_le_pow_right (by norm_num)
      omega

private theorem decodedRetryPoolDyadicDenominator_sub_one_pos (stage : Nat) :
    0 < decodedRetryPoolDyadicDenominator stage - 1 := by
  have hden := decodedRetryPoolDyadicDenominator_ge_eight stage
  omega

/-- The exact ceiling-division formula rounds the numerator up by at most one
denominator interval. -/
private theorem decodedRetryPoolCeilDiv_numerator_le
    (numerator denominator : Nat) (hdenominator : 0 < denominator) :
    numerator ≤ denominator * decodedRetryPoolCeilDiv numerator denominator := by
  unfold decodedRetryPoolCeilDiv
  have hmod : (numerator + denominator - 1) % denominator < denominator :=
    Nat.mod_lt _ hdenominator
  have hdecomposition := Nat.mod_add_div (numerator + denominator - 1) denominator
  omega

/-- Requested accepted blocks never exceed the derived finite attempt count. -/
theorem decodedRetryPoolRequired_le_dyadicAttempts (stage required : Nat) :
    required ≤ decodedRetryPoolDyadicAttempts stage required := by
  unfold decodedRetryPoolDyadicAttempts decodedRetryPoolCeilDiv
  apply (Nat.le_div_iff_mul_le
    (decodedRetryPoolDyadicDenominator_sub_one_pos stage)).2
  calc
    required * (decodedRetryPoolDyadicDenominator stage - 1) ≤
        required * decodedRetryPoolDyadicDenominator stage :=
      Nat.mul_le_mul_left required (Nat.sub_le _ _)
    _ = decodedRetryPoolDyadicDenominator stage * required := Nat.mul_comm _ _
    _ ≤ decodedRetryPoolDyadicDenominator stage * required +
        (decodedRetryPoolDyadicDenominator stage - 1) - 1 :=
      by
        have hroom : 1 ≤ decodedRetryPoolDyadicDenominator stage - 1 := by
          have hdenominator := decodedRetryPoolDyadicDenominator_ge_eight stage
          omega
        omega

/-- The derived attempt count is controlled by the denominator times the
finite shortage slack that appears in the Markov bound. -/
theorem decodedRetryPoolDyadicAttempts_le_denominator_mul_shortageSlack
    (stage required : Nat) :
    decodedRetryPoolDyadicAttempts stage required ≤
      decodedRetryPoolDyadicDenominator stage *
        (decodedRetryPoolDyadicAttempts stage required - required + 1) := by
  let denominator := decodedRetryPoolDyadicDenominator stage
  let attempts := decodedRetryPoolDyadicAttempts stage required
  have hrequired : required ≤ attempts :=
    decodedRetryPoolRequired_le_dyadicAttempts stage required
  have hceil : denominator * required ≤ (denominator - 1) * attempts := by
    simpa [attempts, decodedRetryPoolDyadicAttempts, denominator] using
      (decodedRetryPoolCeilDiv_numerator_le
        (decodedRetryPoolDyadicDenominator stage * required)
        (decodedRetryPoolDyadicDenominator stage - 1)
        (decodedRetryPoolDyadicDenominator_sub_one_pos stage))
  have hdenominator : 0 < denominator := by
    have hbound : 8 ≤ denominator := by
      simpa [denominator] using decodedRetryPoolDyadicDenominator_ge_eight stage
    omega
  have hmul : (denominator - 1) * attempts + attempts = denominator * attempts := by
    calc
      (denominator - 1) * attempts + attempts =
          ((denominator - 1) + 1) * attempts := by rw [Nat.add_mul, one_mul]
      _ = denominator * attempts := by rw [Nat.sub_add_cancel hdenominator]
  have hceiling : denominator * required + attempts ≤ denominator * attempts := by
    calc
      denominator * required + attempts ≤ (denominator - 1) * attempts + attempts :=
        Nat.add_le_add_right hceil _
      _ = denominator * attempts := hmul
  have hsplit : denominator * attempts =
      denominator * required + denominator * (attempts - required) := by
    calc
      denominator * attempts =
          denominator * (required + (attempts - required)) := by
        rw [Nat.add_sub_of_le hrequired]
      _ = denominator * required + denominator * (attempts - required) :=
        Nat.mul_add _ _ _
  have hstrong : attempts ≤ denominator * (attempts - required) := by
    rw [hsplit] at hceiling
    exact Nat.le_of_add_le_add_left hceiling
  calc
    attempts ≤ denominator * (attempts - required) := hstrong
    _ ≤ denominator * (attempts - required + 1) :=
      Nat.mul_le_mul_left denominator (Nat.le_succ _)

/-- The actual finite raw resource carrier has exactly one physical-site slot
for every derived retry attempt. -/
theorem decodedRetryPoolDyadicRawResourceSlots_card
    (stage required m w : Nat) :
    Fintype.card (Fin (decodedRetryPoolDyadicAttempts stage required) × PhysicalSite m w) =
      decodedRetryPoolDyadicAttempts stage required * physicalInputCount m w := by
  simp [physicalInputCount]

/-- The selected output carrier has exactly one logical-site slot for every
requested accepted block. -/
theorem decodedRetryPoolDyadicOutputSlots_card (required m w : Nat) :
    Fintype.card (Fin required × LogicalSite m w) = required * logicalOutputCount m w := by
  simp [logicalOutputCount]

/-- The actual rejected one-block mass is bounded by the physical input count
times the supplied diagonal rate. -/
theorem decodedRetryPoolRejectedMass_le_physicalInputCount_mul_rate
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    1 - acceptedBernoulliMass w r m epsilon ≤
      (physicalInputCount m w : ℝ) * epsilon.1 := by
  have hrate : 0 ≤ epsilon.1 := epsilon.property.1
  calc
    1 - acceptedBernoulliMass w r m epsilon ≤
        1 - (1 - epsilon.1) ^ physicalInputCount m w := by
      exact sub_le_sub_left (acceptedBernoulliMass_allZeroWord_le h epsilon) 1
    _ ≤ (physicalInputCount m w : ℝ) * epsilon.1 := by
      have hbernoulli := one_add_mul_sub_le_pow
        (a := 1 - epsilon.1) (by linarith [epsilon.property.2])
        (physicalInputCount m w)
      nlinarith

/-- The actual decoded retry-pool shortage on the source-derived dyadic number
of attempts is bounded by the derived dyadic physical slack. -/
theorem decodedRetryPoolDyadicShortageMass_le_noisyResources
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0))
    (stage required : Nat) :
    decodedRetryPoolShortageMass h hdegree
        (decodedRetryPoolDyadicAttempts stage required) required
        (tensorPowerProductInput
          (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit
          (decodedRetryPoolDyadicAttempts stage required)) ≤
      (decodedRetryPoolDyadicDenominator stage : ℝ) *
        physicalInputCount m w * epsilon.1 := by
  let attempts := decodedRetryPoolDyadicAttempts stage required
  let denominator := decodedRetryPoolDyadicDenominator stage
  let physicalSlack : ℝ := (physicalInputCount m w : ℝ) * epsilon.1
  have hrequired : required ≤ attempts :=
    decodedRetryPoolRequired_le_dyadicAttempts stage required
  have hratio : attempts ≤ denominator * (attempts - required + 1) := by
    simpa [attempts, denominator] using
      decodedRetryPoolDyadicAttempts_le_denominator_mul_shortageSlack stage required
  have hmarkov := decodedRetryPoolShortageMass_markov_le_noisyResources
    h hdegree epsilon rhoUnit attempts required hrequired
  have hrejected : 1 - acceptedBernoulliMass w r m epsilon ≤ physicalSlack := by
    simpa [physicalSlack] using
      decodedRetryPoolRejectedMass_le_physicalInputCount_mul_rate h epsilon
  have hphysicalSlack : 0 ≤ physicalSlack := by
    exact mul_nonneg (Nat.cast_nonneg _) epsilon.property.1
  have hratioReal : (attempts : ℝ) ≤
      ((denominator * (attempts - required + 1) : Nat) : ℝ) := by
    exact_mod_cast hratio
  have hthresholdPosNat : 0 < attempts - required + 1 := by omega
  have hthresholdPos : 0 < ((attempts - required + 1 : Nat) : ℝ) := by
    exact_mod_cast hthresholdPosNat
  have hscaled : ((attempts - required + 1 : Nat) : ℝ) *
      decodedRetryPoolShortageMass h hdegree attempts required
        (tensorPowerProductInput
          (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit attempts) ≤
      ((attempts - required + 1 : Nat) : ℝ) *
        ((denominator : ℝ) * physicalSlack) := by
    calc
      _ ≤ (attempts : ℝ) * (1 - acceptedBernoulliMass w r m epsilon) := hmarkov
      _ ≤ (attempts : ℝ) * physicalSlack :=
        mul_le_mul_of_nonneg_left hrejected (Nat.cast_nonneg _)
      _ ≤ ((denominator * (attempts - required + 1) : Nat) : ℝ) * physicalSlack :=
        mul_le_mul_of_nonneg_right hratioReal hphysicalSlack
      _ = ((attempts - required + 1 : Nat) : ℝ) *
          ((denominator : ℝ) * physicalSlack) := by
        push_cast
        ring
  exact le_of_mul_le_mul_left
    (by simpa [attempts, denominator, physicalSlack, mul_assoc] using hscaled)
    hthresholdPos

/-- The complementary actual enough mass inherits the source-derived dyadic
lower bound from the finite shortage estimate. -/
theorem decodedRetryPoolDyadicEnoughMass_noisyResources_lower_bound
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0))
    (stage required : Nat) :
    1 - (decodedRetryPoolDyadicDenominator stage : ℝ) *
        physicalInputCount m w * epsilon.1 ≤
      decodedRetryPoolEnoughMass h hdegree
        (decodedRetryPoolDyadicAttempts stage required) required
        (tensorPowerProductInput
          (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit
          (decodedRetryPoolDyadicAttempts stage required)) := by
  have hshortage := decodedRetryPoolDyadicShortageMass_le_noisyResources
    h hdegree epsilon rhoUnit stage required
  have hpartition := decodedRetryPoolEnoughMass_add_decodedRetryPoolShortageMass
    h hdegree (decodedRetryPoolDyadicAttempts stage required) required
    (tensorPowerProductInput
      (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit
      (decodedRetryPoolDyadicAttempts stage required))
  linarith

end HH18Parameterized
end Distillation
end QEC
