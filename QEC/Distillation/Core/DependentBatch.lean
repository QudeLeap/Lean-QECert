import QEC.Distillation.Core.Overhead
/-!
# Dependent flagged batches

Source-neutral finite routing and accounting primitives for a multi-output
distillation block.  A child port receives one port from each distinct parent
block; this preserves the within-child product layout without asserting that
different child ports, or different parent blocks, are independent.
-/

noncomputable section

namespace QEC.Distillation.DependentBatch

open Semantics
open scoped BigOperators

universe u v

/-- Swap a parent-block coordinate and a child-port coordinate. -/
def parentPortTranspose (Parent : Type u) (Port : Type v) :
    Parent × Port ≃ Port × Parent where
  toFun := fun pair => (pair.2, pair.1)
  invFun := fun pair => (pair.2, pair.1)
  left_inv := by
    intro pair
    rfl
  right_inv := by
    intro pair
    rfl

/-- The literal finite routing grid used by an `n`-input, `k`-output block. -/
def transposeRouting (n k : Nat) : Fin n × Fin k ≃ Fin k × Fin n :=
  parentPortTranspose (Fin n) (Fin k)

@[simp] theorem transposeRouting_apply {n k : Nat}
    (parent : Fin n) (port : Fin k) :
    transposeRouting n k (parent, port) = (port, parent) :=
  rfl

/-- Port `j` of every parent block is the input supplied to child block `j`. -/
def childInputSlot {Parent Port : Type*} (port : Port) (parent : Parent) :
    Parent × Port :=
  (parent, port)

/-- Inputs inside one child block come from distinct parent blocks. -/
theorem childInputSlot_injective {Parent Port : Type*} (port : Port) :
    Function.Injective (childInputSlot port : Parent → Parent × Port) := by
  intro left right h
  simpa [childInputSlot] using congrArg Prod.fst h

@[simp] theorem transposeRouting_childInputSlot {n k : Nat}
    (parent : Fin n) (port : Fin k) :
    transposeRouting n k (childInputSlot port parent) = (port, parent) :=
  rfl

/-- A finite flagged batch records an actual outcome distribution and which
ports each outcome accepts.  It deliberately contains no recurrence, success
bound, cost bound, or independence conclusion. -/
structure FiniteFlaggedBatch (Port : Type u) (Outcome : Type v)
    [Fintype Port] [Fintype Outcome] where
  weight : Outcome → ℝ
  weight_nonneg : ∀ outcome, 0 ≤ weight outcome
  total_weight : ∑ outcome, weight outcome = 1
  accepted : Outcome → Port → Bool

/-- The number of accepted ports in one concrete batch outcome. -/
def acceptedPortCount {Port : Type u} {Outcome : Type v}
    [Fintype Port] [Fintype Outcome]
    (batch : FiniteFlaggedBatch Port Outcome) (outcome : Outcome) : Nat :=
  (Finset.univ.filter fun port => batch.accepted outcome port = true).card

/-- Expected accepted-port count, defined by finite linearity rather than any
assumption about correlations between distinct ports. -/
noncomputable def expectedAcceptedPorts {Port : Type u} {Outcome : Type v}
    [Fintype Port] [Fintype Outcome]
    (batch : FiniteFlaggedBatch Port Outcome) : ℝ :=
  ∑ outcome, batch.weight outcome * acceptedPortCount batch outcome

/-- Pooling is a finite collection of whole grids.  Independence of grids, when
available, is a later theorem hypothesis rather than a field of this adapter. -/
noncomputable def pooledExpectedAcceptedPorts {Port : Type u} {Outcome : Type v}
    [Fintype Port] [Fintype Outcome] (count : Nat)
    (pool : Fin count → FiniteFlaggedBatch Port Outcome) : ℝ :=
  ∑ grid, expectedAcceptedPorts (pool grid)

/-- Pool accounting is exactly the finite sum of the individual grid yields. -/
theorem pooledExpectedAcceptedPorts_eq_sum {Port : Type u} {Outcome : Type v}
    [Fintype Port] [Fintype Outcome] (count : Nat)
    (pool : Fin count → FiniteFlaggedBatch Port Outcome) :
    pooledExpectedAcceptedPorts count pool =
      ∑ grid, expectedAcceptedPorts (pool grid) :=
  rfl

/-- The direct input-output ratio of actual finite slot types.  The counts are
derived from `Fintype.card`, rather than stored as independent metadata. -/
noncomputable def typedInputOutputRatio (InputSlots OutputSlots : Type*)
    [Fintype InputSlots] [Fintype OutputSlots] : ℝ :=
  (Fintype.card InputSlots : ℝ) / Fintype.card OutputSlots

/-- The successful-output cost of actual finite slot types and an explicitly
nonnegative accounting yield factor. -/
noncomputable def typedSuccessfulOutputCost (InputSlots OutputSlots : Type*)
    [Fintype InputSlots] [Fintype OutputSlots] (yieldFactor : NNReal) : ℝ :=
  typedInputOutputRatio InputSlots OutputSlots / yieldFactor

/-- A source-neutral finite-depth polylogarithmic comparison for actual slot
types that may depend on the schedule index.  Slot counts are always derived
from their `Fintype.card`s by `typedSuccessfulOutputCost`; no count, error, or
cost theorem is stored as family metadata. -/
def typedPolylogCostBound {Index : Type*}
    (InputSlots OutputSlots : Index → Type*)
    [∀ index, Fintype (InputSlots index)]
    [∀ index, Fintype (OutputSlots index)]
    (targetError : Index → ℝ) (yieldFactor : Index → NNReal)
    (gamma coefficient : ℝ) : Prop :=
  0 ≤ coefficient ∧ ∀ index,
    0 < targetError index → targetError index < 1 →
      0 < (yieldFactor index : ℝ) ∧
        typedSuccessfulOutputCost (InputSlots index) (OutputSlots index)
          (yieldFactor index) ≤ coefficient *
            Real.rpow (Real.log (1 / targetError index)) gamma

/-- A level-indexed successful-output overhead comparison for physical
multi-output protocols.  The slot types and expected-yield factor may vary
with the level, so this deliberately does not coerce the construction into
the fixed-register binary-run interface of `DistillationProtocolFamily`.
Both the reached output error and the cost are derived functions supplied by
the concrete physical construction, not fields of a family record. -/
def physicalPolylogarithmicExpectedYieldOverhead {Index : Type*}
    (InputSlots OutputSlots : Index → Type*)
    [∀ index, Fintype (InputSlots index)]
    [∀ index, Fintype (OutputSlots index)]
    (targetError actualOutputError : Index → ℝ) (yieldFactor : Index → NNReal)
    (gamma coefficient : ℝ) : Prop :=
  0 ≤ coefficient ∧ ∀ index,
    0 < targetError index → targetError index < 1 →
      actualOutputError index ≤ targetError index ∧
        0 < (yieldFactor index : ℝ) ∧
          typedSuccessfulOutputCost (InputSlots index) (OutputSlots index)
            (yieldFactor index) ≤ coefficient *
              Real.rpow (Real.log (1 / targetError index)) gamma

/-- A typed finite-slot cost agrees with the #458 family cost when its actual
input and output slot cardinalities and its yield factor have been separately
identified with that family index. -/
theorem typedSuccessfulOutputCost_eq_distillationProtocolFamily_successfulOutputCost
    {Resource Input Output Index : Type u}
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource]
    [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
    [FiniteQuantumSystem Input]
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output]
    (family : DistillationProtocolFamily Resource Input Output Index) (index : Index)
    (InputSlots OutputSlots : Type*) [Fintype InputSlots] [Fintype OutputSlots]
    (yieldFactor : NNReal)
    (hinput : Fintype.card InputSlots = family.inputResourceCount index)
    (houtput : Fintype.card OutputSlots = family.outputResourceCount index)
    (hyield : (yieldFactor : ℝ) =
      (family.protocol index).run.successProbability) :
    typedSuccessfulOutputCost InputSlots OutputSlots yieldFactor =
      family.successfulOutputCost index := by
  unfold typedSuccessfulOutputCost typedInputOutputRatio
  rw [hinput, houtput, hyield, div_div]
  rfl

end QEC.Distillation.DependentBatch
