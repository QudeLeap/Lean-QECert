import QEC.Semantics.Instruments.Tensor.MarginalChannel
import QEC.Semantics.Instruments.Registers.Marginal
/-!
# Operator-valued marginals of tensor-power instrument branches

Summing every observed sibling outcome and then tracing to one selected output
coordinate gives the selected local branch applied to the true input
marginal.  The input operator may be correlated across tensor factors.  This
is the unnormalized operator identity needed to iterate physical branch
arguments without conditioning on sibling outcomes.
-/

universe u v w x y

namespace QEC
namespace Semantics

open Classical
open scoped BigOperators

noncomputable section

namespace FiniteInstrument

variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Type x} [Fintype kappaTwo]
variable {Xi : Type y} [Fintype Xi]
variable {H K R S : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]

/-- Retain exactly the raw Kraus indices belonging to one observed outcome.
This auxiliary instrument need not be complete. -/
private noncomputable def outcomeBranchInstrument
    (I : FiniteInstrument kappa Omega H K) (outcome : Omega) :
    FiniteInstrument kappa Omega H K where
  kraus :=
    { operator := fun index =>
        if I.observe index = outcome then I.kraus.operator index else 0 }
  observe := fun _ => outcome

private theorem outcomeBranchInstrument_inducedMap
    (I : FiniteInstrument kappa Omega H K) (outcome : Omega)
    (A : Operator H) :
    (outcomeBranchInstrument I outcome).kraus.inducedMap A =
      I.branchOperator outcome A := by
  classical
  rw [FiniteKrausFamily.inducedMap_apply]
  unfold branchOperator outcomeBranchInstrument
  apply Finset.sum_congr rfl
  intro index _
  by_cases hindex : I.observe index = outcome
  · simp [hindex]
  · simp [hindex]

private theorem outcomeBranchInstrument_tensor_branchOperator
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S)
    (outcome leftOutcome : Omega) (rightOutcome : Xi)
    (A : Operator (CompositeSystem H R)) :
    ((outcomeBranchInstrument I outcome).tensor J).branchOperator
        (leftOutcome, rightOutcome) A =
      if leftOutcome = outcome then
        (I.tensor J).branchOperator (outcome, rightOutcome) A
      else 0 := by
  classical
  by_cases houtcome : leftOutcome = outcome
  · subst leftOutcome
    rw [if_pos rfl]
    unfold branchOperator
    apply Finset.sum_congr rfl
    rintro ⟨leftIndex, rightIndex⟩ _
    by_cases hleft : I.observe leftIndex = outcome
    · simp [outcomeBranchInstrument, FiniteInstrument.tensor, hleft]
    · simp [outcomeBranchInstrument, FiniteInstrument.tensor, hleft]
  · rw [if_neg houtcome]
    unfold branchOperator
    apply Finset.sum_eq_zero
    rintro ⟨leftIndex, rightIndex⟩ _
    by_cases hleft : I.observe leftIndex = outcome
    · have hreverse : outcome ≠ leftOutcome := by
        exact fun equality => houtcome equality.symm
      simp [outcomeBranchInstrument, FiniteInstrument.tensor, hreverse]
    · simp [outcomeBranchInstrument, FiniteInstrument.tensor, hleft]

private theorem tensor_outcomeBranchInstrument_branchOperator
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S)
    (outcome rightOutcome : Xi) (leftOutcome : Omega)
    (A : Operator (CompositeSystem H R)) :
    (I.tensor (outcomeBranchInstrument J outcome)).branchOperator
        (leftOutcome, rightOutcome) A =
      if rightOutcome = outcome then
        (I.tensor J).branchOperator (leftOutcome, outcome) A
      else 0 := by
  classical
  by_cases houtcome : rightOutcome = outcome
  · subst rightOutcome
    rw [if_pos rfl]
    unfold branchOperator
    apply Finset.sum_congr rfl
    rintro ⟨leftIndex, rightIndex⟩ _
    by_cases hright : J.observe rightIndex = outcome
    · simp [outcomeBranchInstrument, FiniteInstrument.tensor, hright]
    · simp [outcomeBranchInstrument, FiniteInstrument.tensor, hright]
  · rw [if_neg houtcome]
    unfold branchOperator
    apply Finset.sum_eq_zero
    rintro ⟨leftIndex, rightIndex⟩ _
    by_cases hright : J.observe rightIndex = outcome
    · have hreverse : outcome ≠ rightOutcome := by
        exact fun equality => houtcome equality.symm
      simp [outcomeBranchInstrument, FiniteInstrument.tensor, hreverse]
    · simp [outcomeBranchInstrument, FiniteInstrument.tensor, hright]

private theorem outcomeBranchInstrument_tensor_inducedMap
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S)
    (outcome : Omega) (A : Operator (CompositeSystem H R)) :
    ((outcomeBranchInstrument I outcome).tensor J).kraus.inducedMap A =
      ∑ rightOutcome : Xi,
        (I.tensor J).branchOperator (outcome, rightOutcome) A := by
  classical
  rw [← FiniteInstrument.sum_branchOperator_eq_inducedMap
    ((outcomeBranchInstrument I outcome).tensor J) A]
  rw [Fintype.sum_prod_type]
  calc
    (∑ leftOutcome : Omega, ∑ rightOutcome : Xi,
        ((outcomeBranchInstrument I outcome).tensor J).branchOperator
          (leftOutcome, rightOutcome) A) =
        ∑ leftOutcome : Omega,
          if leftOutcome = outcome then
            ∑ rightOutcome : Xi,
              (I.tensor J).branchOperator (outcome, rightOutcome) A
          else 0 := by
            apply Finset.sum_congr rfl
            intro leftOutcome _
            by_cases hleft : leftOutcome = outcome
            · rw [if_pos hleft]
              apply Finset.sum_congr rfl
              intro rightOutcome _
              simpa [hleft] using
                outcomeBranchInstrument_tensor_branchOperator
                  I J outcome leftOutcome rightOutcome A
            · rw [if_neg hleft]
              apply Finset.sum_eq_zero
              intro rightOutcome _
              rw [outcomeBranchInstrument_tensor_branchOperator]
              simp [hleft]
    _ = _ := by simp

private theorem tensor_outcomeBranchInstrument_inducedMap
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S)
    (outcome : Xi) (A : Operator (CompositeSystem H R)) :
    (I.tensor (outcomeBranchInstrument J outcome)).kraus.inducedMap A =
      ∑ leftOutcome : Omega,
        (I.tensor J).branchOperator (leftOutcome, outcome) A := by
  classical
  rw [← FiniteInstrument.sum_branchOperator_eq_inducedMap
    (I.tensor (outcomeBranchInstrument J outcome)) A]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  calc
    (∑ rightOutcome : Xi, ∑ leftOutcome : Omega,
        (I.tensor (outcomeBranchInstrument J outcome)).branchOperator
          (leftOutcome, rightOutcome) A) =
        ∑ rightOutcome : Xi,
          if rightOutcome = outcome then
            ∑ leftOutcome : Omega,
              (I.tensor J).branchOperator (leftOutcome, outcome) A
          else 0 := by
            apply Finset.sum_congr rfl
            intro rightOutcome _
            by_cases hright : rightOutcome = outcome
            · rw [if_pos hright]
              apply Finset.sum_congr rfl
              intro leftOutcome _
              simpa [hright] using
                tensor_outcomeBranchInstrument_branchOperator
                  I J outcome rightOutcome leftOutcome A
            · rw [if_neg hright]
              apply Finset.sum_eq_zero
              intro leftOutcome _
              rw [tensor_outcomeBranchInstrument_branchOperator]
              simp [hright]
    _ = _ := by simp

/-- Summing every right observed outcome and tracing out its output leaves the
selected left branch on the true left input marginal. -/
theorem tensor_branchOperator_fst_sum_partialTraceRight
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S) (hJ : J.kraus.Complete)
    (outcome : Omega) (A : Operator (CompositeSystem H R)) :
    partialTraceRightRaw K S
        (∑ rightOutcome : Xi,
          (I.tensor J).branchOperator (outcome, rightOutcome) A) =
      I.branchOperator outcome (partialTraceRightRaw H R A) := by
  rw [← outcomeBranchInstrument_tensor_inducedMap I J outcome A]
  rw [tensor_inducedMap_partialTraceRight
    (outcomeBranchInstrument I outcome) J hJ]
  exact outcomeBranchInstrument_inducedMap I outcome _

/-- Summing every left observed outcome and tracing out its output leaves the
selected right branch on the true right input marginal. -/
theorem tensor_branchOperator_snd_sum_partialTraceLeft
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (J : FiniteInstrument kappaTwo Xi R S)
    (outcome : Xi) (A : Operator (CompositeSystem H R)) :
    FiniteMatrixEntropy.partialTraceLeftRaw K S
        (∑ leftOutcome : Omega,
          (I.tensor J).branchOperator (leftOutcome, outcome) A) =
      J.branchOperator outcome
        (FiniteMatrixEntropy.partialTraceLeftRaw H R A) := by
  rw [← tensor_outcomeBranchInstrument_inducedMap I J outcome A]
  rw [tensor_inducedMap_partialTraceLeft
    I (outcomeBranchInstrument J outcome) hI]
  exact outcomeBranchInstrument_inducedMap J outcome _

/-- For an arbitrary operator on a recursive tensor-power carrier, summing
all observed histories off one selected coordinate and physically tracing to
that output coordinate gives the local observed branch applied to the true
input-coordinate operator. -/
theorem tensorPower_coordinateOperator_branchOperator_sum_eq
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete) :
    ∀ (attempts : Nat)
      (A : Operator (tensorPowerCarrier H attempts))
      (trial : Fin attempts) (outcome : Omega),
      tensorPowerCoordinateOperator attempts trial
          (∑ history : tensorPowerHistory Omega attempts,
            if tensorPowerHistoryAt Omega attempts history trial = outcome then
              (I.tensorPower attempts).branchOperator history A
            else 0) =
        I.branchOperator outcome
          (tensorPowerCoordinateOperator attempts trial A) := by
  intro attempts
  induction attempts with
  | zero =>
      intro A trial
      exact Fin.elim0 trial
  | succ attempts ih =>
      intro A trial outcome
      refine Fin.cases ?_ ?_ trial
      · have hsum :
          (∑ history : Omega × tensorPowerHistory Omega attempts,
              if history.1 = outcome then
                (I.tensor (I.tensorPower attempts)).branchOperator history A
              else 0) =
            ∑ tail : tensorPowerHistory Omega attempts,
              (I.tensor (I.tensorPower attempts)).branchOperator
                (outcome, tail) A := by
            rw [Fintype.sum_prod_type]
            rw [Finset.sum_eq_single outcome]
            · apply Finset.sum_congr rfl
              intro tail _
              exact if_pos rfl
            · intro x _ hx
              apply Finset.sum_eq_zero
              intro tail _
              exact if_neg hx
            · intro hout
              exact (hout (Finset.mem_univ _)).elim
        change partialTraceRightRaw K (tensorPowerCarrier K attempts)
            (∑ history : Omega × tensorPowerHistory Omega attempts,
              if history.1 = outcome then
                (I.tensor (I.tensorPower attempts)).branchOperator history A
              else 0) =
          I.branchOperator outcome
            (partialTraceRightRaw H (tensorPowerCarrier H attempts) A)
        rw [hsum]
        exact tensor_branchOperator_fst_sum_partialTraceRight
          I (I.tensorPower attempts) (I.tensorPower_complete hI attempts)
          outcome A
      · intro tailTrial
        let tailInput := FiniteMatrixEntropy.partialTraceLeftRaw
          H (tensorPowerCarrier H attempts) A
        have hsum :
          (∑ history : Omega × tensorPowerHistory Omega attempts,
              if tensorPowerHistoryAt Omega attempts history.2 tailTrial = outcome then
                (I.tensor (I.tensorPower attempts)).branchOperator history A
              else 0) =
            ∑ tail : tensorPowerHistory Omega attempts,
              if tensorPowerHistoryAt Omega attempts tail tailTrial = outcome then
                ∑ head : Omega,
                  (I.tensor (I.tensorPower attempts)).branchOperator (head, tail) A
              else 0 := by
            rw [Fintype.sum_prod_type, Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro tail _
            by_cases htail :
                tensorPowerHistoryAt Omega attempts tail tailTrial = outcome
            · simp [htail]
            · simp [htail]
        have hmarginal :
          FiniteMatrixEntropy.partialTraceLeftRaw K
              (tensorPowerCarrier K attempts)
              (∑ tail : tensorPowerHistory Omega attempts,
                if tensorPowerHistoryAt Omega attempts tail tailTrial = outcome then
                  ∑ head : Omega,
                    (I.tensor (I.tensorPower attempts)).branchOperator
                      (head, tail) A
                else 0) =
            ∑ tail : tensorPowerHistory Omega attempts,
              if tensorPowerHistoryAt Omega attempts tail tailTrial = outcome then
                (I.tensorPower attempts).branchOperator tail tailInput
              else 0 := by
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro tail _
            by_cases htail :
                tensorPowerHistoryAt Omega attempts tail tailTrial = outcome
            · rw [if_pos htail, if_pos htail]
              exact tensor_branchOperator_snd_sum_partialTraceLeft
                I hI (I.tensorPower attempts) tail A
            · simp [htail]
        change tensorPowerCoordinateOperator attempts tailTrial
            (FiniteMatrixEntropy.partialTraceLeftRaw K
              (tensorPowerCarrier K attempts)
              (∑ history : Omega × tensorPowerHistory Omega attempts,
                if tensorPowerHistoryAt Omega attempts history.2 tailTrial = outcome then
                  (I.tensor (I.tensorPower attempts)).branchOperator history A
                else 0)) =
          I.branchOperator outcome
            (tensorPowerCoordinateOperator attempts tailTrial tailInput)
        rw [hsum, hmarginal]
        exact ih tailInput tailTrial outcome

end FiniteInstrument

end
end Semantics
end QEC
