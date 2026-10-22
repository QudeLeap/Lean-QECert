import QEC.Distillation.Core.MagicStateProtocol
/-!
# QEC.Distillation.Overhead

Source-neutral accounting semantics for families of magic-state
distillation protocols.
-/

universe u

namespace QEC.Distillation

open Semantics

/--
A family of distillation protocols with a target error and a positive output
resource count at each index.
-/
structure DistillationProtocolFamily
    (Resource Input Output Index : Type u)
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource]
    [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
    [FiniteQuantumSystem Input]
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output] where
  targetError : Index → ℝ
  protocol : (index : Index) →
    MagicStateDistillationProtocol Resource Input Output
  outputResourceCount : Index → Nat
  outputResourceCount_pos : ∀ index, 0 < outputResourceCount index
  successfulOutputError_le_targetError : ∀ index,
    (protocol index).successfulOutputError ≤ targetError index

namespace DistillationProtocolFamily

variable {Resource Input Output Index : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
variable [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
variable [FiniteQuantumSystem Input]
variable [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
variable [FiniteQuantumSystem Output]

/-- Every target error is nonnegative because it bounds a nonnegative error. -/
theorem targetError_nonneg
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index) :
    0 ≤ family.targetError index := by
  calc
    0 ≤ (family.protocol index).successfulOutputError :=
      (family.protocol index).successfulOutputError_nonneg
    _ ≤ family.targetError index :=
      family.successfulOutputError_le_targetError index

/-- The input count is the resource count of the indexed protocol run. -/
def inputResourceCount
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index) : Nat :=
  (family.protocol index).run.resourceCount

/-- Direct input resources consumed per protocol output. -/
noncomputable def inputOutputRatio
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index) : ℝ :=
  family.inputResourceCount index / family.outputResourceCount index

/-- Input resources consumed per successful protocol output. -/
noncomputable def successfulOutputCost
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index) : ℝ :=
  family.inputResourceCount index /
    (family.outputResourceCount index *
      (family.protocol index).run.successProbability)

/-- The direct input-output ratio is nonnegative. -/
theorem inputOutputRatio_nonneg
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index) :
    0 ≤ family.inputOutputRatio index := by
  exact div_nonneg (Nat.cast_nonneg _)
    (le_of_lt (Nat.cast_pos.mpr (family.outputResourceCount_pos index)))

/-- The successful-output cost is nonnegative, including at zero success. -/
theorem successfulOutputCost_nonneg
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index) :
    0 ≤ family.successfulOutputCost index := by
  refine div_nonneg (Nat.cast_nonneg _) ?_
  exact mul_nonneg
    (le_of_lt (Nat.cast_pos.mpr (family.outputResourceCount_pos index)))
    (family.protocol index).run.success_nonneg

/-- Successful-output cost is the direct ratio divided by success probability. -/
theorem successfulOutputCost_eq_inputOutputRatio_div_successProbability
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index) :
    family.successfulOutputCost index =
      family.inputOutputRatio index /
        (family.protocol index).run.successProbability := by
  simp only [successfulOutputCost, inputOutputRatio, div_div]

/-- Positive success makes the successful-output-cost denominator positive. -/
theorem successfulOutputCost_denominator_pos
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index)
    (hsuccess : 0 < (family.protocol index).run.successProbability) :
    0 < (family.outputResourceCount index : ℝ) *
      (family.protocol index).run.successProbability := by
  exact mul_pos
    (Nat.cast_pos.mpr (family.outputResourceCount_pos index)) hsuccess

/-- Positive success makes direct input-output ratio no larger than successful-output cost. -/
theorem inputOutputRatio_le_successfulOutputCost
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index)
    (hsuccess : 0 < (family.protocol index).run.successProbability) :
    family.inputOutputRatio index ≤ family.successfulOutputCost index := by
  rw [family.successfulOutputCost_eq_inputOutputRatio_div_successProbability index]
  exact (le_div_iff₀ hsuccess).2
    (mul_le_of_le_one_right (family.inputOutputRatio_nonneg index)
      (family.protocol index).run.success_le_one)

end DistillationProtocolFamily

/-- A supplied upper bound on successful-output cost at one family index. -/
def SuccessfulOutputCostBound
    {Resource Input Output Index : Type u}
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource]
    [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
    [FiniteQuantumSystem Input]
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output]
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index) (bound : ℝ) : Prop :=
  0 < (family.protocol index).run.successProbability ∧
    family.successfulOutputCost index ≤ bound

/-- A polylogarithmic successful-output-cost comparison within one fixed family. -/
def PolylogarithmicOverhead
    {Resource Input Output Index : Type u}
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource]
    [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
    [FiniteQuantumSystem Input]
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output]
    (family : DistillationProtocolFamily Resource Input Output Index)
    (gamma coefficient : ℝ) : Prop :=
  0 ≤ coefficient ∧ ∀ index,
    0 < family.targetError index → family.targetError index < 1 →
    0 < (family.protocol index).run.successProbability ∧
      family.successfulOutputCost index ≤ coefficient *
        (Real.log (1 / family.targetError index)) ^ gamma

/-- A uniform direct input-output-ratio comparison within one fixed family. -/
def BoundedInputOutputRatio
    {Resource Input Output Index : Type u}
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource]
    [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
    [FiniteQuantumSystem Input]
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output]
    (family : DistillationProtocolFamily Resource Input Output Index)
    (bound : ℝ) : Prop :=
  0 ≤ bound ∧ ∀ index,
    0 < family.targetError index → family.targetError index < 1 →
    family.inputOutputRatio index ≤ bound

/-- A nonnegative space-overhead measurement, distinct from resource cost. -/
structure SpaceOverhead where
  value : ℝ
  value_nonneg : 0 ≤ value

/-- A nonnegative circuit-time measurement, distinct from resource cost. -/
structure CircuitTimeOverhead where
  value : ℝ
  value_nonneg : 0 ≤ value

/-- A nonnegative decoder-complexity measurement, distinct from resource cost. -/
structure DecoderComplexityOverhead where
  value : ℝ
  value_nonneg : 0 ≤ value

end QEC.Distillation
