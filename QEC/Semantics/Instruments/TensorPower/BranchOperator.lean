import QEC.Semantics.Instruments.TensorPower.Basis
import QEC.Semantics.Instruments.TensorPower.BornMass
/-!
# Branch operators of finite tensor-power instruments

This internal layer factors literal observed branch operators on actual
tensor-product inputs.  It is an operator identity derived from the finite
Kraus families; it introduces no probabilistic independence assumption.
-/

universe u v w x y

namespace QEC
namespace Semantics

open Classical
open scoped BigOperators ComplexOrder TensorProduct

noncomputable section

namespace FiniteInstrument

variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

/-- The recursively tensorized product of one observed branch operator per
history entry, with the literal depth-zero tensor-unit operator retained. -/
noncomputable def tensorPowerBranchOperatorProduct
    (branch : Ω → Operator K)
    (unit : Operator (tensorPowerCarrier K 0)) :
    (attempts : Nat) → tensorPowerHistory Ω attempts →
      Operator (tensorPowerCarrier K attempts)
  | 0, _ => unit
  | attempts + 1, history =>
      TensorProduct.map (branch history.1)
        (tensorPowerBranchOperatorProduct branch unit attempts history.2)

/-- The recursively factored computational matrix entry of a tensorized
branch-operator product.  This is an algebraic product over actual trials,
not a probabilistic independence premise. -/
noncomputable def tensorPowerBranchOperatorMatrixEntryProduct
    {β : Type y} [Fintype β] (basis : OrthonormalBasis β Complex K)
    (branch : Ω → Operator K)
    (unit : Operator (tensorPowerCarrier K 0)) :
    (attempts : Nat) → tensorPowerHistory Ω attempts →
      tensorPowerHistory β attempts → tensorPowerHistory β attempts → Complex
  | 0, _, left, right =>
      inner Complex (tensorPowerBasis basis 0 left)
        (unit (tensorPowerBasis basis 0 right))
  | attempts + 1, history, left, right =>
      inner Complex (basis left.1) (branch history.1 (basis right.1)) *
        tensorPowerBranchOperatorMatrixEntryProduct basis branch unit attempts
          history.2 left.2 right.2

omit [Fintype Ω] in
/-- Computational matrix entries of the literal recursively tensorized
branch operator factor exactly over its actual tensor factors. -/
theorem tensorPowerBranchOperatorProduct_matrixEntry
    {β : Type y} [Fintype β] (basis : OrthonormalBasis β Complex K)
    (branch : Ω → Operator K)
    (unit : Operator (tensorPowerCarrier K 0)) :
    ∀ (attempts : Nat) (history : tensorPowerHistory Ω attempts)
      (left right : tensorPowerHistory β attempts),
      inner Complex (tensorPowerBasis basis attempts left)
          (tensorPowerBranchOperatorProduct branch unit attempts history
            (tensorPowerBasis basis attempts right)) =
        tensorPowerBranchOperatorMatrixEntryProduct basis branch unit attempts
          history left right := by
  intro attempts
  induction attempts with
  | zero =>
      intro history left right
      rfl
  | succ attempts ih =>
      rintro ⟨outcome, tailHistory⟩ ⟨leftHead, leftTail⟩
        ⟨rightHead, rightTail⟩
      change inner Complex
        ((basis.tensorProduct (tensorPowerBasis basis attempts)) (leftHead, leftTail))
        ((TensorProduct.map (branch outcome)
          (tensorPowerBranchOperatorProduct branch unit attempts tailHistory))
          ((basis.tensorProduct (tensorPowerBasis basis attempts)) (rightHead, rightTail))) =
        inner Complex (basis leftHead) (branch outcome (basis rightHead)) *
          tensorPowerBranchOperatorMatrixEntryProduct basis branch unit attempts
            tailHistory leftTail rightTail
      rw [OrthonormalBasis.tensorProduct_apply, OrthonormalBasis.tensorProduct_apply]
      rw [TensorProduct.map_tmul, TensorProduct.inner_tmul]
      rw [ih tailHistory leftTail rightTail]

omit [Fintype Ω] in
/-- The recursive matrix-entry product is equivalently the finite product of
the actual trial entries, multiplied by the literal tensor-unit entry. -/
theorem tensorPowerBranchOperatorMatrixEntryProduct_eq_prod
    {β : Type y} [Fintype β] (basis : OrthonormalBasis β Complex K)
    (branch : Ω → Operator K)
    (unit : Operator (tensorPowerCarrier K 0)) :
    ∀ (attempts : Nat) (history : tensorPowerHistory Ω attempts)
      (left right : tensorPowerHistory β attempts),
      tensorPowerBranchOperatorMatrixEntryProduct basis branch unit attempts
          history left right =
        inner Complex (tensorPowerBasis basis 0 PUnit.unit)
            (unit (tensorPowerBasis basis 0 PUnit.unit)) *
          ∏ trial : Fin attempts,
            inner Complex
              (basis (tensorPowerHistoryAt β attempts left trial))
              (branch (tensorPowerHistoryAt Ω attempts history trial)
                (basis (tensorPowerHistoryAt β attempts right trial))) := by
  intro attempts
  induction attempts with
  | zero =>
      intro history left right
      cases history
      cases left
      cases right
      simp [tensorPowerBranchOperatorMatrixEntryProduct]
  | succ attempts ih =>
      rintro ⟨outcome, tailHistory⟩ ⟨leftHead, leftTail⟩
        ⟨rightHead, rightTail⟩
      rw [Fin.prod_univ_succ]
      simp only [tensorPowerBranchOperatorMatrixEntryProduct,
        tensorPowerHistoryAt, Fin.cases_zero, Fin.cases_succ]
      rw [ih tailHistory leftTail rightTail]
      ring

/-- The sum of computational diagonal entries of one actual observed branch
is its complex Born weight. -/
theorem branchOperator_matrixEntry_sum_eq_bornWeight
    {β : Type y} [Fintype β] (basis : OrthonormalBasis β Complex K)
    (I : FiniteInstrument κ Ω H K) (outcome : Ω) (rho : DensityOperator H) :
    (∑ index : β,
        inner Complex (basis index)
          (I.branchOperator outcome rho.toOperator (basis index))) =
      (I.bornWeight outcome rho : Complex) := by
  calc
    (∑ index : β,
        inner Complex (basis index)
          (I.branchOperator outcome rho.toOperator (basis index))) =
        LinearMap.trace Complex K
          (I.branchOperator outcome rho.toOperator) :=
      (LinearMap.trace_eq_sum_inner
        (I.branchOperator outcome rho.toOperator) basis).symm
    _ = (I.bornWeight outcome rho : Complex) :=
      I.trace_branchOperator_eq_bornWeight outcome rho

section Tensor

variable {κ' : Type x} [Fintype κ']
variable {Ω' : Type y} [Fintype Ω']
variable {R S : Type u}
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]

private theorem tensorProduct_map_sum_sum
    (left : κ → Operator K) (right : κ' → Operator S) :
    TensorProduct.map (∑ i, left i) (∑ j, right j) =
      ∑ i, ∑ j, TensorProduct.map (left i) (right j) := by
  classical
  have hleft (indices : Finset κ) :
      TensorProduct.map (∑ i ∈ indices, left i) (∑ j, right j) =
        ∑ i ∈ indices, TensorProduct.map (left i) (∑ j, right j) := by
    induction indices using Finset.induction_on with
    | empty => simp
    | insert i indices hi ih =>
        simp [Finset.sum_insert hi, TensorProduct.map_add_left, ih]
  have hright (i : κ) (indices : Finset κ') :
      TensorProduct.map (left i) (∑ j ∈ indices, right j) =
        ∑ j ∈ indices, TensorProduct.map (left i) (right j) := by
    induction indices using Finset.induction_on with
    | empty => simp
    | insert j indices hj ih =>
        simp [Finset.sum_insert hj, TensorProduct.map_add_right, ih]
  calc
    TensorProduct.map (∑ i, left i) (∑ j, right j) =
        ∑ i, TensorProduct.map (left i) (∑ j, right j) := by
          simpa using hleft Finset.univ
    _ = ∑ i, ∑ j, TensorProduct.map (left i) (right j) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa using hright i Finset.univ

/-- A literal tensor-product raw Kraus branch factors as the tensor product
of the two component raw branch operators. -/
theorem rawBranchOperator_tensor_product
    (I : FiniteInstrument κ Ω H K) (J : FiniteInstrument κ' Ω' R S)
    (A : Operator H) (B : Operator R) (leftIndex : κ) (rightIndex : κ') :
    (I.tensor J).rawBranchOperator (leftIndex, rightIndex)
        (TensorProduct.map A B) =
      TensorProduct.map (I.rawBranchOperator leftIndex A)
        (J.rawBranchOperator rightIndex B) := by
  simp only [rawBranchOperator, tensor]
  rw [TensorProduct.adjoint_map, ← TensorProduct.map_comp,
    ← TensorProduct.map_comp]

/-- An observed tensor-product branch operator factors exactly on a literal
tensor-product input operator. -/
theorem branchOperator_tensor_product
    (I : FiniteInstrument κ Ω H K) (J : FiniteInstrument κ' Ω' R S)
    (A : Operator H) (B : Operator R)
    (leftOutcome : Ω) (rightOutcome : Ω') :
    (I.tensor J).branchOperator (leftOutcome, rightOutcome)
        (TensorProduct.map A B) =
      TensorProduct.map (I.branchOperator leftOutcome A)
        (J.branchOperator rightOutcome B) := by
  classical
  unfold branchOperator
  rw [Fintype.sum_prod_type, tensorProduct_map_sum_sum]
  apply Finset.sum_congr rfl
  intro leftIndex _
  apply Finset.sum_congr rfl
  intro rightIndex _
  by_cases hleft : I.observe leftIndex = leftOutcome
  · by_cases hright : J.observe rightIndex = rightOutcome
    · have hobserve :
          (I.tensor J).observe (leftIndex, rightIndex) =
            (leftOutcome, rightOutcome) := by
          exact Prod.ext hleft hright
      rw [if_pos hobserve, if_pos hleft, if_pos hright]
      simpa only [rawBranchOperator] using
        rawBranchOperator_tensor_product I J A B leftIndex rightIndex
    · have hobserve :
          (I.tensor J).observe (leftIndex, rightIndex) ≠
            (leftOutcome, rightOutcome) := by
          intro heq
          exact hright (congrArg Prod.snd heq)
      simp [hobserve, hleft, hright]
  · have hobserve :
        (I.tensor J).observe (leftIndex, rightIndex) ≠
          (leftOutcome, rightOutcome) := by
        intro heq
        exact hleft (congrArg Prod.fst heq)
    simp [hobserve, hleft]

end Tensor

section DependentBind

variable {κ₂ : Ω → Type x} [∀ outcome, Fintype (κ₂ outcome)]
variable {L : Type u}
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

/-- When every second-stage observation is the unique `PUnit` value, the
retained first observed branch is sent through the complete second raw Kraus
map selected by that first outcome. -/
theorem bindDependent_branchOperator_punit
    (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument (κ₂ outcome) PUnit K L)
    (outcome : Ω) (A : Operator H) :
    (I.bindDependent J).branchOperator ⟨outcome, PUnit.unit⟩ A =
      (J outcome).kraus.inducedMap (I.branchOperator outcome A) := by
  classical
  unfold branchOperator
  rw [Fintype.sum_sigma, map_sum]
  apply Finset.sum_congr rfl
  intro firstIndex _
  by_cases hfirst : I.observe firstIndex = outcome
  · rw [if_pos hfirst]
    subst outcome
    rw [FiniteKrausFamily.inducedMap_apply]
    apply Finset.sum_congr rfl
    intro secondIndex _
    simp only [bindDependent, if_true, LinearMap.adjoint_comp]
    ext vector
    simp [LinearMap.comp_apply]
  · have hobserve (secondIndex : κ₂ (I.observe firstIndex)) :
        (I.bindDependent J).observe ⟨firstIndex, secondIndex⟩ ≠
          ⟨outcome, PUnit.unit⟩ := by
        intro heq
        exact hfirst (congrArg Sigma.fst heq)
    simp [hfirst, hobserve]

end DependentBind

section UnitFirstBind

variable {κ' : Type x} [Fintype κ']
variable {L : Type u}
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

/-- If the first instrument has only the unit observation, retaining a
second-stage outcome applies that second observed branch to the complete
first-stage Kraus map. -/
theorem bindDependent_branchOperator_fst_punit
    (I : FiniteInstrument κ PUnit H K)
    (J : FiniteInstrument κ' Ω K L) (outcome : Ω) (A : Operator H) :
    (I.bindDependent (fun _ => J)).branchOperator
        ⟨PUnit.unit, outcome⟩ A =
      J.branchOperator outcome (I.kraus.inducedMap A) := by
  classical
  unfold branchOperator
  rw [Fintype.sum_sigma, FiniteKrausFamily.inducedMap_apply]
  ext vector
  simp only [bindDependent, LinearMap.adjoint_comp, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro secondIndex _
  by_cases hsecond : J.observe secondIndex = outcome
  · simp [hsecond, Finset.sum_apply]
  · simp [hsecond]

/-- Running a physical channel before an observed finite instrument evaluates
the latter's Born weight on the channel's actual output density. -/
theorem toFiniteInstrument_bindDependent_bornWeight
    (Phi : QuantumChannel H K) (J : FiniteInstrument κ' Ω K L)
    (outcome : Ω) (rho : DensityOperator H) :
    (Phi.toFiniteInstrument.bindDependent (fun _ => J)).bornWeight
        ⟨PUnit.unit, outcome⟩ rho =
      J.bornWeight outcome (Phi.mapDensity rho) := by
  unfold bornWeight
  rw [bindDependent_branchOperator_fst_punit]
  rw [QuantumChannel.toFiniteInstrument_inducedMap_apply]
  rfl

end UnitFirstBind

/-- Every observed tensor-power branch operator factors recursively on the
actual recursively tensorized product input density. -/
theorem branchOperator_tensorPower_productInput
    (I : FiniteInstrument κ Ω H K) (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0)) :
    ∀ (attempts : Nat) (history : tensorPowerHistory Ω attempts),
      (I.tensorPower attempts).branchOperator history
          (tensorPowerProductInput rho rhoUnit attempts).toOperator =
        tensorPowerBranchOperatorProduct
          (fun outcome => I.branchOperator outcome rho.toOperator)
          rhoUnit.toOperator attempts history := by
  intro attempts
  induction attempts with
  | zero =>
      intro history
      cases history
      change tensorUnitInstrument.branchOperator PUnit.unit rhoUnit.toOperator =
        rhoUnit.toOperator
      simp [tensorUnitInstrument, branchOperator, Module.End.one_eq_id]
  | succ attempts ih =>
      rintro ⟨head, tail⟩
      change
        (I.tensor (I.tensorPower attempts)).branchOperator (head, tail)
            (DensityOperator.tensorDensity rho
              (tensorPowerProductInput rho rhoUnit attempts)).toOperator =
          TensorProduct.map (I.branchOperator head rho.toOperator)
            (tensorPowerBranchOperatorProduct
              (fun outcome => I.branchOperator outcome rho.toOperator)
              rhoUnit.toOperator attempts tail)
      rw [DensityOperator.tensorDensity_toOperator,
        branchOperator_tensor_product, ih tail]

end FiniteInstrument

end
end Semantics
end QEC
