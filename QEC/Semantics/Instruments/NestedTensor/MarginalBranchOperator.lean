import QEC.Semantics.Instruments.NestedTensor.Power
import QEC.Semantics.Instruments.NestedTensor.MarginalBornMass
import QEC.Semantics.Instruments.TensorPower.MarginalBranchOperator
/-!
# Operator-valued marginals of nested tensor-power branches

This layer recursively sums every observed sibling history outside one
selected nested leaf and physically traces the output to that leaf.  The
result is the base observed branch applied to the true unnormalized input
leaf operator.  No branch is normalized and no product input is assumed.
-/

universe u v w

namespace QEC
namespace Semantics

open Classical
open scoped BigOperators

noncomputable section

namespace FiniteInstrument

variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

/-- The CPTP operation retaining one base leaf from a recursively nested
tensor carrier. -/
noncomputable def nestedTensorCoordinateOperator
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (branches : Nat) :
    (depth : Nat) -> nestedTensorPath branches depth ->
      QuantumChannel (nestedTensorCarrier H branches depth) H
  | 0, _ => QuantumChannel.id H
  | depth + 1, path =>
      QuantumChannel.comp
        (tensorPowerCoordinateOperator branches path.2)
        (nestedTensorCoordinateOperator
          (tensorPowerCarrier H branches) branches depth path.1)

/-- Retaining a nested leaf of an observed nested tensor branch is exactly
the base branch applied to the true unnormalized input-leaf operator after
all off-path histories have been summed. -/
theorem nestedTensor_coordinateOperator_branchOperator_sum_eq
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (branches : Nat) :
    ∀ (depth : Nat) (A : Operator (nestedTensorCarrier H branches depth))
      (path : nestedTensorPath branches depth) (outcome : Omega),
      nestedTensorCoordinateOperator K branches depth path
          (∑ history : nestedTensorHistory Omega branches depth,
            if nestedTensorHistoryAt Omega branches depth history path = outcome then
              (nestedTensorPower I branches depth).branchOperator history A
            else 0) =
        I.branchOperator outcome
          (nestedTensorCoordinateOperator H branches depth path A) := by
  intro depth
  induction depth generalizing kappa Omega H K with
  | zero =>
      intro A path outcome
      have hpath : path = PUnit.unit := PUnit.ext _ _
      subst path
      change (∑ history : Omega,
        if history = outcome then I.branchOperator history A else 0) =
          I.branchOperator outcome A
      erw [Fintype.sum_eq_single outcome]
      · exact if_pos rfl
      · intro other hother
        exact if_neg hother
  | succ depth ih =>
      intro A path outcome
      rcases path with ⟨pathPrefix, trial⟩
      let prefixInput :=
        nestedTensorCoordinateOperator
          (tensorPowerCarrier H branches) branches depth pathPrefix A
      have hregroup :
          (∑ history : nestedTensorHistory
              (tensorPowerHistory Omega branches) branches depth,
            if tensorPowerHistoryAt Omega branches
                (nestedTensorHistoryAt
                  (tensorPowerHistory Omega branches) branches depth
                  history pathPrefix) trial = outcome then
              (nestedTensorPower (I.tensorPower branches) branches depth).branchOperator
                history A
            else 0) =
            ∑ layer : tensorPowerHistory Omega branches,
              if tensorPowerHistoryAt Omega branches layer trial = outcome then
                ∑ history : nestedTensorHistory
                    (tensorPowerHistory Omega branches) branches depth,
                  if nestedTensorHistoryAt
                      (tensorPowerHistory Omega branches) branches depth
                      history pathPrefix = layer then
                    (nestedTensorPower (I.tensorPower branches) branches depth).branchOperator
                      history A
                  else 0
              else 0 := by
        calc
          _ = ∑ history : nestedTensorHistory
                (tensorPowerHistory Omega branches) branches depth,
              ∑ layer : tensorPowerHistory Omega branches,
                if tensorPowerHistoryAt Omega branches layer trial = outcome ∧
                    nestedTensorHistoryAt
                      (tensorPowerHistory Omega branches) branches depth
                      history pathPrefix = layer then
                  (nestedTensorPower (I.tensorPower branches) branches depth).branchOperator
                    history A
                else 0 := by
              apply Finset.sum_congr rfl
              intro history _
              rw [Fintype.sum_eq_single
                (nestedTensorHistoryAt
                  (tensorPowerHistory Omega branches) branches depth
                  history pathPrefix)]
              · simp
              · intro layer hne
                simp [hne.symm]
          _ = ∑ layer : tensorPowerHistory Omega branches,
                ∑ history : nestedTensorHistory
                    (tensorPowerHistory Omega branches) branches depth,
                  if tensorPowerHistoryAt Omega branches layer trial = outcome ∧
                      nestedTensorHistoryAt
                        (tensorPowerHistory Omega branches) branches depth
                        history pathPrefix = layer then
                    (nestedTensorPower (I.tensorPower branches) branches depth).branchOperator
                      history A
                  else 0 := by
              rw [Finset.sum_comm]
          _ = _ := by
              apply Finset.sum_congr rfl
              intro layer _
              by_cases hlayer :
                  tensorPowerHistoryAt Omega branches layer trial = outcome
              · simp [hlayer]
              · simp [hlayer]
      have hprefix :
          nestedTensorCoordinateOperator
              (tensorPowerCarrier K branches) branches depth pathPrefix
              (∑ layer : tensorPowerHistory Omega branches,
                if tensorPowerHistoryAt Omega branches layer trial = outcome then
                  ∑ history : nestedTensorHistory
                      (tensorPowerHistory Omega branches) branches depth,
                    if nestedTensorHistoryAt
                        (tensorPowerHistory Omega branches) branches depth
                        history pathPrefix = layer then
                      (nestedTensorPower (I.tensorPower branches) branches depth).branchOperator
                        history A
                    else 0
                else 0) =
            ∑ layer : tensorPowerHistory Omega branches,
              if tensorPowerHistoryAt Omega branches layer trial = outcome then
                (I.tensorPower branches).branchOperator layer prefixInput
              else 0 := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro layer _
        by_cases hlayer :
            tensorPowerHistoryAt Omega branches layer trial = outcome
        · rw [if_pos hlayer, if_pos hlayer]
          simpa [prefixInput] using
            (ih
              (I := I.tensorPower branches)
              (hI := I.tensorPower_complete hI branches)
              (A := A) (path := pathPrefix) (outcome := layer))
        · simp [hlayer]
      change
        tensorPowerCoordinateOperator branches trial
          (nestedTensorCoordinateOperator
            (tensorPowerCarrier K branches) branches depth pathPrefix
            (∑ history : nestedTensorHistory
                (tensorPowerHistory Omega branches) branches depth,
              if tensorPowerHistoryAt Omega branches
                  (nestedTensorHistoryAt
                    (tensorPowerHistory Omega branches) branches depth
                    history pathPrefix) trial = outcome then
                (nestedTensorPower (I.tensorPower branches) branches depth).branchOperator
                  history A
              else 0)) =
          I.branchOperator outcome
            (tensorPowerCoordinateOperator branches trial prefixInput)
      rw [hregroup, hprefix]
      exact tensorPower_coordinateOperator_branchOperator_sum_eq
        I hI branches prefixInput trial outcome

/-- The operator selected recursively above is the true density marginal when
the input operator itself is a density operator. -/
theorem nestedTensorCoordinateOperator_mapDensity
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (branches : Nat) :
    ∀ (depth : Nat) (rho : DensityOperator (nestedTensorCarrier H branches depth))
      (path : nestedTensorPath branches depth),
      (nestedTensorCoordinateOperator H branches depth path).mapDensity rho =
        nestedTensorInputMarginal H branches depth rho path := by
  intro depth
  induction depth generalizing H with
  | zero =>
      intro rho path
      have hpath : path = PUnit.unit := PUnit.ext _ _
      subst path
      rfl
  | succ depth ih =>
      intro rho path
      rcases path with ⟨pathPrefix, trial⟩
      change
        (tensorPowerCoordinateOperator branches trial).mapDensity
            ((nestedTensorCoordinateOperator
              (tensorPowerCarrier H branches) branches depth pathPrefix).mapDensity rho) =
          tensorPowerInputMarginal branches
            (nestedTensorInputMarginal (tensorPowerCarrier H branches)
              branches depth rho pathPrefix) trial
      rw [ih]
      exact tensorPowerCoordinateOperator_mapDensity branches _ trial

end FiniteInstrument

end
end Semantics
end QEC
