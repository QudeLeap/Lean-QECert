import QEC.Distillation.LowOverheadProtocol.Parameterized.DecodedInstrumentConditional
import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Core
import QEC.Semantics.Instruments.TensorPower.ConditionedBranchOperator
import QEC.Semantics.Instruments.Registers.ProductDensity
/-!
# Accepted product output of the parameterized HH18 decoded retry pool

For an actual enough-accepted history, the physical retry-pool branch is its
full observed-history Born mass times the flattened product of the genuine
normalized accepted decoded output.  Discarded trials contribute their actual
Born weights through the partial trace; no sibling-independence premise is
used.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

/-- Every deterministic retry-pool selector slot contains an actually
accepted decoded outcome. -/
theorem decodedRetryPoolAcceptedSelector_eq_accepted
    (attempts : Nat)
    (history : tensorPowerHistory DistillationOutcome attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices decodedRetryPoolAccepts attempts history).card)
    (slot : Fin required) :
    tensorPowerHistoryAt DistillationOutcome attempts history
        (tensorPowerAcceptedSelector decodedRetryPoolAccepts attempts history
          required hrequired slot) = .accepted := by
  simpa [decodedRetryPoolAccepts] using
    (tensorPowerAcceptedSelector_satisfies decodedRetryPoolAccepts attempts
      history required hrequired slot)

/-- The fixed output density requested from an enough retry pool: one genuine
normalized accepted decoded block for every selected slot, flattened to the
literal slot/logical-port register. -/
noncomputable def decodedRetryPoolAcceptedProductDensity
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (required : Nat) :
    DensityOperator (QubitRegister (Fin required × LogicalSite m w)) :=
  tensorPowerRegisterProductDensity (LogicalSite m w)
    (resourceDecodedRun h hdegree
      (noisyResources m w epsilon)).acceptedOutput
    rhoUnit required

/-- An enough-history physical retry-pool branch matrix entry is exactly its
full observed-history Born product times the corresponding entry of the fixed
accepted product density. -/
theorem
    decodedRetryPool_enoughBranch_matrixEntry_eq_bornProduct_mul_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (attempts required : Nat)
    (history : tensorPowerHistory DistillationOutcome attempts)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices decodedRetryPoolAccepts attempts history).card)
    (left right : Bitstring (Fin required × LogicalSite m w)) :
    inner Complex
        (EuclideanSpace.basisFun
          (Bitstring (Fin required × LogicalSite m w)) Complex left)
        ((decodedRetryPoolInstrument h hdegree attempts required).branchOperator
          ⟨history, PUnit.unit⟩
          (tensorPowerProductInput
            (prepareMeasuredResources m w (noisyResources m w epsilon))
            rhoUnit attempts).toOperator
          (EuclideanSpace.basisFun
            (Bitstring (Fin required × LogicalSite m w)) Complex right)) =
      (tensorPowerBornProduct (decodedInstrument h hdegree)
        (prepareMeasuredResources m w (noisyResources m w epsilon)) attempts
        history : Complex) *
      inner Complex
        (EuclideanSpace.basisFun
          (Bitstring (Fin required × LogicalSite m w)) Complex left)
        ((decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
          required).toOperator
          (EuclideanSpace.basisFun
            (Bitstring (Fin required × LogicalSite m w)) Complex right)) := by
  have hselectedEntry (slot : Fin required) :
      inner Complex
          (EuclideanSpace.basisFun (Bitstring (LogicalSite m w)) Complex
            (fun port => left (slot, port)))
          ((decodedInstrument h hdegree).branchOperator
            (tensorPowerHistoryAt DistillationOutcome attempts history
              (tensorPowerAcceptedSelector decodedRetryPoolAccepts attempts history
                required hrequired slot))
            (prepareMeasuredResources m w
              (noisyResources m w epsilon)).toOperator
            (EuclideanSpace.basisFun (Bitstring (LogicalSite m w)) Complex
              (fun port => right (slot, port)))) =
        ((decodedInstrument h hdegree).bornWeight .accepted
          (prepareMeasuredResources m w
            (noisyResources m w epsilon)) : Complex) *
        inner Complex
          (EuclideanSpace.basisFun (Bitstring (LogicalSite m w)) Complex
            (fun port => left (slot, port)))
          ((resourceDecodedRun h hdegree
            (noisyResources m w epsilon)).acceptedOutput.toOperator
            (EuclideanSpace.basisFun (Bitstring (LogicalSite m w)) Complex
              (fun port => right (slot, port)))) := by
    rw [decodedRetryPoolAcceptedSelector_eq_accepted attempts history required
      hrequired slot]
    rw [decodedInstrument_bornWeight_prepareMeasuredResources]
    rw [decodedInstrument_branchOperator_prepareMeasuredResources]
    simp
  have hselectedProduct :
      (∏ slot : Fin required,
        inner Complex
          (EuclideanSpace.basisFun (Bitstring (LogicalSite m w)) Complex
            (fun port => left (slot, port)))
          ((decodedInstrument h hdegree).branchOperator
            (tensorPowerHistoryAt DistillationOutcome attempts history
              (tensorPowerAcceptedSelector decodedRetryPoolAccepts attempts history
                required hrequired slot))
            (prepareMeasuredResources m w
              (noisyResources m w epsilon)).toOperator
            (EuclideanSpace.basisFun (Bitstring (LogicalSite m w)) Complex
              (fun port => right (slot, port))))) =
        (∏ _slot : Fin required,
          ((decodedInstrument h hdegree).bornWeight .accepted
            (prepareMeasuredResources m w
              (noisyResources m w epsilon)) : Complex)) *
        ∏ slot : Fin required,
          inner Complex
            (EuclideanSpace.basisFun (Bitstring (LogicalSite m w)) Complex
              (fun port => left (slot, port)))
            ((resourceDecodedRun h hdegree
              (noisyResources m w epsilon)).acceptedOutput.toOperator
              (EuclideanSpace.basisFun (Bitstring (LogicalSite m w)) Complex
                (fun port => right (slot, port)))) := by
    calc
      _ = ∏ slot : Fin required,
          (((decodedInstrument h hdegree).bornWeight .accepted
            (prepareMeasuredResources m w
              (noisyResources m w epsilon)) : Complex) *
          inner Complex
            (EuclideanSpace.basisFun (Bitstring (LogicalSite m w)) Complex
              (fun port => left (slot, port)))
            ((resourceDecodedRun h hdegree
              (noisyResources m w epsilon)).acceptedOutput.toOperator
              (EuclideanSpace.basisFun (Bitstring (LogicalSite m w)) Complex
                (fun port => right (slot, port))))) := by
            apply Finset.prod_congr rfl
            intro slot _
            exact hselectedEntry slot
      _ = _ := Finset.prod_mul_distrib
  have hweightSplit :
      (∏ trial : Fin attempts,
        ((decodedInstrument h hdegree).bornWeight
          (tensorPowerHistoryAt DistillationOutcome attempts history trial)
          (prepareMeasuredResources m w
            (noisyResources m w epsilon)) : Complex)) =
        (∏ _slot : Fin required,
          ((decodedInstrument h hdegree).bornWeight .accepted
            (prepareMeasuredResources m w
              (noisyResources m w epsilon)) : Complex)) *
        ∏ trial : tensorPowerUnselectedTrial decodedRetryPoolAccepts attempts
            history required hrequired,
          ((decodedInstrument h hdegree).bornWeight
            (tensorPowerHistoryAt DistillationOutcome attempts history trial.1)
            (prepareMeasuredResources m w
              (noisyResources m w epsilon)) : Complex) := by
    calc
      _ =
          (∏ slot : Fin required,
            ((decodedInstrument h hdegree).bornWeight
              (tensorPowerHistoryAt DistillationOutcome attempts history
                (tensorPowerAcceptedSelector decodedRetryPoolAccepts attempts
                  history required hrequired slot))
              (prepareMeasuredResources m w
                (noisyResources m w epsilon)) : Complex)) *
          ∏ trial : tensorPowerUnselectedTrial decodedRetryPoolAccepts attempts
              history required hrequired,
            ((decodedInstrument h hdegree).bornWeight
              (tensorPowerHistoryAt DistillationOutcome attempts history trial.1)
              (prepareMeasuredResources m w
                (noisyResources m w epsilon)) : Complex) :=
        tensorPower_prod_eq_selected_mul_unselected decodedRetryPoolAccepts
          attempts history required hrequired
          (fun trial =>
            ((decodedInstrument h hdegree).bornWeight
              (tensorPowerHistoryAt DistillationOutcome attempts history trial)
              (prepareMeasuredResources m w
                (noisyResources m w epsilon)) : Complex))
      _ = _ := by
        congr 1
        apply Finset.prod_congr rfl
        intro slot _
        rw [decodedRetryPoolAcceptedSelector_eq_accepted attempts history required
          hrequired slot]
  have hbornProduct :
      (tensorPowerBornProduct (decodedInstrument h hdegree)
        (prepareMeasuredResources m w (noisyResources m w epsilon)) attempts
        history : Complex) =
      ∏ trial : Fin attempts,
        ((decodedInstrument h hdegree).bornWeight
          (tensorPowerHistoryAt DistillationOutcome attempts history trial)
          (prepareMeasuredResources m w
            (noisyResources m w epsilon)) : Complex) := by
    rw [tensorPowerBornProduct_eq_prod]
    push_cast
    rfl
  simp only [decodedRetryPoolInstrument]
  rw [tensorPowerHistoryConditionedInstrument_branchOperator_of_enough
    (decodedInstrument h hdegree) decodedRetryPoolAccepts attempts required
    (decodedRetryPoolShortageState m w required) history hrequired]
  rw [tensorPowerSelectedPartialTraceChannel_productInputBranch_matrixEntry
    (LogicalSite m w) (decodedInstrument h hdegree) decodedRetryPoolAccepts
    attempts history required hrequired
    (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit left
    right]
  rw [hselectedProduct]
  rw [decodedRetryPoolAcceptedProductDensity,
    tensorPowerRegisterProductDensity_matrixEntry]
  rw [hbornProduct, hweightSplit]
  ring

/-- Operator form of the enough-history identity: the complete physical pool
branch is its actual history Born product times the fixed accepted product
density. -/
theorem decodedRetryPool_enoughBranch_eq_bornProduct_smul_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (attempts required : Nat)
    (history : tensorPowerHistory DistillationOutcome attempts)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices decodedRetryPoolAccepts attempts history).card) :
    (decodedRetryPoolInstrument h hdegree attempts required).branchOperator
        ⟨history, PUnit.unit⟩
        (tensorPowerProductInput
          (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit
          attempts).toOperator =
      (tensorPowerBornProduct (decodedInstrument h hdegree)
        (prepareMeasuredResources m w (noisyResources m w epsilon)) attempts
        history : Complex) •
      (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
        required).toOperator := by
  let basis := EuclideanSpace.basisFun
    (Bitstring (Fin required × LogicalSite m w)) Complex
  apply basis.toBasis.ext
  intro right
  change
    (decodedRetryPoolInstrument h hdegree attempts required).branchOperator
        ⟨history, PUnit.unit⟩
        (tensorPowerProductInput
          (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit
          attempts).toOperator (basis right) =
      (((tensorPowerBornProduct (decodedInstrument h hdegree)
        (prepareMeasuredResources m w (noisyResources m w epsilon)) attempts
        history : Complex) •
      (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
        required).toOperator) (basis right))
  rw [← basis.sum_repr'
    ((decodedRetryPoolInstrument h hdegree attempts required).branchOperator
      ⟨history, PUnit.unit⟩
      (tensorPowerProductInput
        (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit
        attempts).toOperator (basis right))]
  rw [← basis.sum_repr'
    (((tensorPowerBornProduct (decodedInstrument h hdegree)
      (prepareMeasuredResources m w (noisyResources m w epsilon)) attempts
      history : Complex) •
      (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
        required).toOperator) (basis right))]
  apply Finset.sum_congr rfl
  intro left _
  have hentry :=
    decodedRetryPool_enoughBranch_matrixEntry_eq_bornProduct_mul_acceptedProduct
      h hdegree epsilon rhoUnit attempts required history hrequired left right
  simpa only [basis, LinearMap.smul_apply, inner_smul_right] using
    congrArg (fun coefficient : Complex => coefficient • basis left) hentry

end HH18Parameterized
end Distillation
end QEC
