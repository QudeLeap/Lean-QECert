import QEC.Semantics.Instruments.TensorPower.ChannelProduct
import QEC.Semantics.Entropy.Purification
/-!
# Functorial tensor-power channels on product inputs

The chosen finite Kraus construction of a tensor-power channel is equal, on
every genuine recursive product input, to applying the one-factor channel and
then recursively tensoring the result.  This module records that statement at
the density-operator level and derives the corresponding composition law for
two complete one-factor channels.  No assertion is made about arbitrary
product structure of an input state.
-/

universe u v w x y

namespace QEC
namespace Semantics

noncomputable section

namespace FiniteInstrument

open scoped BigOperators TensorProduct

variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L]
  [FiniteQuantumSystem L]

/-- The homogeneous tensor-power channel generated from one channel. -/
noncomputable def quantumChannelTensorPower
    (channel : QuantumChannel H K) (attempts : Nat) :
    QuantumChannel (tensorPowerCarrier H attempts)
      (tensorPowerCarrier K attempts) :=
  (((channel.toFiniteInstrument).tensorPower attempts).kraus.toQuantumChannel
    ((channel.toFiniteInstrument).tensorPower_complete
      channel.toFiniteInstrument_complete attempts))

/-- A tensor-power channel maps a genuine recursive product density
factorwise. -/
theorem quantumChannelTensorPower_mapDensity_product
    (channel : QuantumChannel H K)
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (sigmaUnit : DensityOperator (tensorPowerCarrier K 0))
    (hunit : sigmaUnit.toOperator = rhoUnit.toOperator)
    (attempts : Nat) :
    (quantumChannelTensorPower channel attempts).mapDensity
        (tensorPowerProductInput rho rhoUnit attempts) =
      tensorPowerProductInput (channel.mapDensity rho) sigmaUnit attempts := by
  exact quantumChannelTensorPower_mapDensity_productInput_eq
    channel rho rhoUnit sigmaUnit hunit attempts

/-- On a genuine recursive product input, composing two tensor-power channels
is exactly the tensor power of the one-factor channel composition. -/
theorem quantumChannelTensorPower_comp_mapDensity_product
    (first : QuantumChannel H K) (second : QuantumChannel K L)
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (sigmaUnit : DensityOperator (tensorPowerCarrier K 0))
    (tauUnit : DensityOperator (tensorPowerCarrier L 0))
    (hsigma : sigmaUnit.toOperator = rhoUnit.toOperator)
    (htau : tauUnit.toOperator = sigmaUnit.toOperator)
    (attempts : Nat) :
    (quantumChannelTensorPower second attempts).mapDensity
        ((quantumChannelTensorPower first attempts).mapDensity
          (tensorPowerProductInput rho rhoUnit attempts)) =
      tensorPowerProductInput
        ((QuantumChannel.comp second first).mapDensity rho)
        tauUnit attempts := by
  rw [quantumChannelTensorPower_mapDensity_product
    first rho rhoUnit sigmaUnit hsigma attempts]
  rw [quantumChannelTensorPower_mapDensity_product
    second (first.mapDensity rho) sigmaUnit tauUnit htau attempts]
  rfl

/-- Map a recursive tensor history pointwise. -/
def tensorPowerHistoryMap {beta gamma : Type u} (mapIndex : beta → gamma) :
    ∀ attempts, tensorPowerHistory beta attempts →
      tensorPowerHistory gamma attempts
  | 0, _ => PUnit.unit
  | attempts + 1, history =>
      (mapIndex history.1,
        tensorPowerHistoryMap mapIndex attempts history.2)

/-- Pointwise history mapping commutes with evaluation at an actual tensor
coordinate. -/
@[simp] theorem tensorPowerHistoryAt_map
    {beta gamma : Type u} (mapIndex : beta → gamma) :
    ∀ attempts (history : tensorPowerHistory beta attempts)
      (trial : Fin attempts),
      tensorPowerHistoryAt gamma attempts
          (tensorPowerHistoryMap mapIndex attempts history) trial =
        mapIndex (tensorPowerHistoryAt beta attempts history trial) := by
  intro attempts
  induction attempts with
  | zero =>
      intro history trial
      exact Fin.elim0 trial
  | succ attempts ih =>
      intro history trial
      rcases history with ⟨head, tail⟩
      refine Fin.cases ?_ ?_ trial
      · rfl
      · intro tailTrial
        exact ih tail tailTrial

private theorem tensorMap_sum_sum
    {kappa : Type v} {kappaTwo : Type x}
    [Fintype kappa] [Fintype kappaTwo]
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [FiniteQuantumSystem B]
    (left : kappa → Operator A) (right : kappaTwo → Operator B) :
    TensorProduct.map (∑ i, left i) (∑ j, right j) =
      ∑ i, ∑ j, TensorProduct.map (left i) (right j) := by
  classical
  have hleft (indices : Finset kappa) :
      TensorProduct.map (∑ i ∈ indices, left i) (∑ j, right j) =
        ∑ i ∈ indices, TensorProduct.map (left i) (∑ j, right j) := by
    induction indices using Finset.induction_on with
    | empty => simp
    | @insert index indices hindex ih =>
        simp [Finset.sum_insert hindex, TensorProduct.map_add_left, ih]
  have hright (i : kappa) (indices : Finset kappaTwo) :
      TensorProduct.map (left i) (∑ j ∈ indices, right j) =
        ∑ j ∈ indices, TensorProduct.map (left i) (right j) := by
    induction indices using Finset.induction_on with
    | empty => simp
    | @insert index indices hindex ih =>
        simp [Finset.sum_insert hindex, TensorProduct.map_add_right, ih]
  calc
    TensorProduct.map (∑ i, left i) (∑ j, right j) =
        ∑ i, TensorProduct.map (left i) (∑ j, right j) := by
          simpa using hleft Finset.univ
    _ = ∑ i, ∑ j, TensorProduct.map (left i) (right j) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa using hright i Finset.univ

/-- The induced map of a tensor instrument acts factorwise on a literal
tensor-product operator. -/
theorem tensor_inducedMap_tensorMap
    {kappa : Type v} {omega : Type w}
    {kappaTwo : Type x} {omegaTwo : Type y}
    [Fintype kappa] [Fintype kappaTwo] [Fintype omega] [Fintype omegaTwo]
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D]
    [FiniteQuantumSystem D]
    (first : FiniteInstrument kappa omega A B)
    (second : FiniteInstrument kappaTwo omegaTwo C D)
    (left : Operator A) (right : Operator C) :
    (first.tensor second).kraus.inducedMap
        (TensorProduct.map left right) =
      TensorProduct.map (first.kraus.inducedMap left)
        (second.kraus.inducedMap right) := by
  rw [FiniteKrausFamily.inducedMap_apply,
    FiniteKrausFamily.inducedMap_apply,
    FiniteKrausFamily.inducedMap_apply]
  rw [Fintype.sum_prod_type, tensorMap_sum_sum]
  apply Finset.sum_congr rfl
  intro firstIndex _
  apply Finset.sum_congr rfl
  intro secondIndex _
  exact rawBranchOperator_tensor_product first second left right
    firstIndex secondIndex

/-- If one channel sends computational matrix units to scalar multiples of
computational matrix units, its homogeneous tensor power does the same with
the product of the actual per-coordinate scalars. -/
theorem quantumChannelTensorPower_rankOne_basis
    {beta gamma : Type u} [Fintype beta] [Fintype gamma]
    (channel : QuantumChannel H K)
    (sourceBasis : OrthonormalBasis beta Complex H)
    (targetBasis : OrthonormalBasis gamma Complex K)
    (mapIndex : beta → gamma)
    (coefficient : beta → beta → Complex)
    (haction : ∀ left right,
      channel
          (InnerProductSpace.rankOne Complex
            (sourceBasis left) (sourceBasis right)).toLinearMap =
        coefficient left right •
          (InnerProductSpace.rankOne Complex
            (targetBasis (mapIndex left))
            (targetBasis (mapIndex right))).toLinearMap) :
    ∀ attempts
      (left right : tensorPowerHistory beta attempts),
      quantumChannelTensorPower channel attempts
          (InnerProductSpace.rankOne Complex
            (tensorPowerBasis sourceBasis attempts left)
            (tensorPowerBasis sourceBasis attempts right)).toLinearMap =
        (∏ trial : Fin attempts,
          coefficient
            (tensorPowerHistoryAt beta attempts left trial)
            (tensorPowerHistoryAt beta attempts right trial)) •
          (InnerProductSpace.rankOne Complex
            (tensorPowerBasis targetBasis attempts
              (tensorPowerHistoryMap mapIndex attempts left))
            (tensorPowerBasis targetBasis attempts
              (tensorPowerHistoryMap mapIndex attempts right))).toLinearMap := by
  intro attempts
  induction attempts with
  | zero =>
      intro left right
      cases left
      cases right
      simp only [quantumChannelTensorPower, FiniteKrausFamily.toQuantumChannel_apply]
      change tensorUnitInstrument.{u, 0, 0}.kraus.inducedMap
        (InnerProductSpace.rankOne Complex
          (tensorPowerBasis sourceBasis 0 PUnit.unit)
          (tensorPowerBasis sourceBasis 0 PUnit.unit)).toLinearMap = _
      rw [FiniteKrausFamily.inducedMap_apply]
      simp only [tensorUnitInstrument, Fintype.sum_unique, LinearMap.adjoint_one,
        Module.End.one_eq_id, LinearMap.adjoint_id, LinearMap.id_comp, LinearMap.comp_id,
        Fin.prod_univ_zero, one_smul]
      rfl
  | succ attempts ih =>
      rintro ⟨leftHead, leftTail⟩ ⟨rightHead, rightTail⟩
      simp only [quantumChannelTensorPower,
        FiniteKrausFamily.toQuantumChannel_apply]
      rw [tensorPowerBasis_succ_apply, tensorPowerBasis_succ_apply]
      rw [← DensityOperator.tensorMap_rankOne]
      change
        (channel.toFiniteInstrument.tensor
          (channel.toFiniteInstrument.tensorPower attempts)).kraus.inducedMap
            (TensorProduct.map
              (InnerProductSpace.rankOne Complex
                (sourceBasis leftHead) (sourceBasis rightHead)).toLinearMap
              (InnerProductSpace.rankOne Complex
                (tensorPowerBasis sourceBasis attempts leftTail)
                (tensorPowerBasis sourceBasis attempts rightTail)).toLinearMap) = _
      refine (tensor_inducedMap_tensorMap
        channel.toFiniteInstrument
        (channel.toFiniteInstrument.tensorPower attempts) _ _).trans ?_
      rw [QuantumChannel.toFiniteInstrument_inducedMap_apply]
      rw [haction leftHead rightHead]
      change TensorProduct.map
          (coefficient leftHead rightHead •
            (InnerProductSpace.rankOne Complex
              (targetBasis (mapIndex leftHead))
              (targetBasis (mapIndex rightHead))).toLinearMap)
          (quantumChannelTensorPower channel attempts
            (InnerProductSpace.rankOne Complex
              (tensorPowerBasis sourceBasis attempts leftTail)
              (tensorPowerBasis sourceBasis attempts rightTail)).toLinearMap) = _
      rw [ih leftTail rightTail]
      rw [TensorProduct.map_smul_left, TensorProduct.map_smul_right,
        smul_smul]
      rw [DensityOperator.tensorMap_rankOne]
      rw [Fin.prod_univ_succ]
      simp only [tensorPowerHistoryAt, Fin.cases_zero, Fin.cases_succ,
        tensorPowerHistoryMap]
      erw [tensorPowerBasis_succ_apply, tensorPowerBasis_succ_apply]

end FiniteInstrument

end
end Semantics
end QEC
