import QEC.Semantics.Instruments.TensorPower.BornMass
import QEC.Semantics.Entropy.MatrixRelative
import QEC.Semantics.Entropy.Purification
/-!
# Marginal Born masses of tensor-product finite instruments

Running complete finite instruments on two tensor factors does not require the
input density to factor.  This module proves that summing every outcome on one
factor leaves the other instrument's Born distribution evaluated on the
actual partial-trace marginal.  It is the finite-dimensional no-signalling
identity needed for correlated union bounds.
-/

universe u v w x y

namespace QEC
namespace Semantics

open Classical
open scoped BigOperators TensorProduct

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

private theorem tensorMap_sum_right
    (A : Operator H) (B : kappaTwo -> Operator R) :
    (∑ index, TensorProduct.map A (B index)) =
      TensorProduct.map A (∑ index, B index) := by
  classical
  induction (Finset.univ : Finset kappaTwo) using Finset.induction_on with
  | empty => simp
  | @insert index indices hindex ih =>
      simp [Finset.sum_insert hindex, TensorProduct.map_add_right, ih]

private theorem tensorMap_sum_left
    (A : kappa -> Operator H) (B : Operator R) :
    (∑ index, TensorProduct.map (A index) B) =
      TensorProduct.map (∑ index, A index) B := by
  classical
  induction (Finset.univ : Finset kappa) using Finset.induction_on with
  | empty => simp
  | @insert index indices hindex ih =>
      simp [Finset.sum_insert hindex, TensorProduct.map_add_left, ih]

/-- Summing the raw branches of a complete instrument on the right tensor
factor leaves the left raw branch evaluated on the actual right-partial-trace
marginal.  The bipartite input may be correlated. -/
theorem tensor_rawBornWeight_fst_sum_eq_partialTraceRight
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S) (hJ : J.kraus.Complete)
    (leftIndex : kappa) (rho : DensityOperator (CompositeSystem H R)) :
    (∑ rightIndex : kappaTwo,
      (I.tensor J).rawBornWeight (leftIndex, rightIndex) rho) =
      I.rawBornWeight leftIndex (partialTraceRightRaw_mapDensity H R rho) := by
  let leftEffect : Operator H :=
    (LinearMap.adjoint (I.kraus.operator leftIndex)).comp
      (I.kraus.operator leftIndex)
  let rightEffect : kappaTwo -> Operator R := fun rightIndex =>
    (LinearMap.adjoint (J.kraus.operator rightIndex)).comp
      (J.kraus.operator rightIndex)
  let basisR : OrthonormalBasis
      (ULift.{u} (Fin (Module.finrank Complex R))) Complex R :=
    (stdOrthonormalBasis Complex R).reindex Equiv.ulift.symm
  unfold rawBornWeight rawBranchOperator
  rw [← Complex.re_sum]
  apply congrArg Complex.re
  calc
    (∑ rightIndex : kappaTwo,
        LinearMap.trace Complex (CompositeSystem K S)
          (((I.tensor J).kraus.operator (leftIndex, rightIndex)).comp
            (rho.toOperator.comp
              (LinearMap.adjoint
                ((I.tensor J).kraus.operator (leftIndex, rightIndex)))))) =
        ∑ rightIndex : kappaTwo,
          LinearMap.trace Complex (CompositeSystem H R)
            (rho.toOperator.comp
              ((LinearMap.adjoint
                ((I.tensor J).kraus.operator (leftIndex, rightIndex))).comp
                ((I.tensor J).kraus.operator (leftIndex, rightIndex)))) := by
      apply Finset.sum_congr rfl
      intro rightIndex _
      simpa [LinearMap.comp_assoc] using
        (LinearMap.trace_comp_cycle
          (R := Complex) (M := CompositeSystem H R)
          (N := CompositeSystem H R) (P := CompositeSystem K S)
          (f := rho.toOperator)
          (g := (I.tensor J).kraus.operator (leftIndex, rightIndex))
          (h := LinearMap.adjoint
            ((I.tensor J).kraus.operator (leftIndex, rightIndex))))
    _ = ∑ rightIndex : kappaTwo,
        LinearMap.trace Complex (CompositeSystem H R)
          (rho.toOperator.comp
            (TensorProduct.map leftEffect (rightEffect rightIndex))) := by
      apply Finset.sum_congr rfl
      intro rightIndex _
      congr 2
      simp only [FiniteInstrument.tensor, TensorProduct.adjoint_map]
      rw [← TensorProduct.map_comp]
    _ = LinearMap.trace Complex (CompositeSystem H R)
        (rho.toOperator.comp
          (∑ rightIndex : kappaTwo,
            TensorProduct.map leftEffect (rightEffect rightIndex))) := by
      rw [← map_sum]
      congr 2
      ext vector
      simp [LinearMap.comp_apply]
    _ = LinearMap.trace Complex (CompositeSystem H R)
        (rho.toOperator.comp
          (TensorProduct.map leftEffect
            (∑ rightIndex : kappaTwo, rightEffect rightIndex))) := by
      rw [tensorMap_sum_right]
    _ = LinearMap.trace Complex (CompositeSystem H R)
        (rho.toOperator.comp
          (TensorProduct.map leftEffect (LinearMap.id : Operator R))) := by
      rw [show (∑ rightIndex : kappaTwo, rightEffect rightIndex) =
          (1 : Operator R) by exact hJ]
      rfl
    _ = LinearMap.trace Complex H
        (((partialTraceRightRaw H R) rho.toOperator).comp leftEffect) := by
      symm
      exact FiniteMatrixEntropy.partialTraceRightRaw_trace_pairing
        basisR rho.toOperator leftEffect
    _ = LinearMap.trace Complex K
        ((I.kraus.operator leftIndex).comp
          (((partialTraceRightRaw H R) rho.toOperator).comp
            (LinearMap.adjoint (I.kraus.operator leftIndex)))) := by
      simpa [leftEffect, LinearMap.comp_assoc] using
        (LinearMap.trace_comp_cycle
          (R := Complex) (M := H) (N := H) (P := K)
          (f := (partialTraceRightRaw H R) rho.toOperator)
          (g := I.kraus.operator leftIndex)
          (h := LinearMap.adjoint (I.kraus.operator leftIndex))).symm

/-- Summing every visible right-factor outcome of a tensor instrument gives
the left visible Born mass on the true partial-trace marginal.  No product
input or independence premise is used. -/
theorem tensor_bornWeight_fst_sum_eq_partialTraceRight
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S) (hJ : J.kraus.Complete)
    (leftOutcome : Omega) (rho : DensityOperator (CompositeSystem H R)) :
    (∑ rightOutcome : Xi,
      (I.tensor J).bornWeight (leftOutcome, rightOutcome) rho) =
      I.bornWeight leftOutcome (partialTraceRightRaw_mapDensity H R rho) := by
  classical
  simp_rw [bornWeight_eq_sum_rawBornWeight]
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  calc
    _ =
      ∑ leftIndex : kappa,
        if I.observe leftIndex = leftOutcome then
          ∑ rightIndex : kappaTwo,
            (I.tensor J).rawBornWeight (leftIndex, rightIndex) rho
        else 0 := by
      apply Finset.sum_congr rfl
      intro leftIndex _
      by_cases hleft : I.observe leftIndex = leftOutcome
      · rw [if_pos hleft]
        apply Finset.sum_congr rfl
        intro rightIndex _
        simp [FiniteInstrument.tensor, hleft]
      · rw [if_neg hleft]
        apply Finset.sum_eq_zero
        intro rightIndex _
        apply Finset.sum_eq_zero
        intro rightOutcome _
        simp [FiniteInstrument.tensor, hleft]
    _ = ∑ leftIndex : kappa,
        if I.observe leftIndex = leftOutcome then
          I.rawBornWeight leftIndex
            (partialTraceRightRaw_mapDensity H R rho)
        else 0 := by
      apply Finset.sum_congr rfl
      intro leftIndex _
      by_cases hleft : I.observe leftIndex = leftOutcome
      · rw [if_pos hleft, if_pos hleft,
          tensor_rawBornWeight_fst_sum_eq_partialTraceRight I J hJ]
      · simp [hleft]
    _ = _ := rfl

/-- Summing the raw branches of a complete instrument on the left tensor
factor leaves the right raw branch evaluated on the actual left-partial-trace
marginal.  The bipartite input may be correlated. -/
theorem tensor_rawBornWeight_snd_sum_eq_leftMarginal
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (J : FiniteInstrument kappaTwo Xi R S)
    (rightIndex : kappaTwo) (rho : DensityOperator (CompositeSystem H R)) :
    (∑ leftIndex : kappa,
      (I.tensor J).rawBornWeight (leftIndex, rightIndex) rho) =
      J.rawBornWeight rightIndex (DensityOperator.leftMarginal rho) := by
  let leftEffect : kappa -> Operator H := fun leftIndex =>
    (LinearMap.adjoint (I.kraus.operator leftIndex)).comp
      (I.kraus.operator leftIndex)
  let rightEffect : Operator R :=
    (LinearMap.adjoint (J.kraus.operator rightIndex)).comp
      (J.kraus.operator rightIndex)
  unfold rawBornWeight rawBranchOperator
  rw [← Complex.re_sum]
  apply congrArg Complex.re
  calc
    (∑ leftIndex : kappa,
        LinearMap.trace Complex (CompositeSystem K S)
          (((I.tensor J).kraus.operator (leftIndex, rightIndex)).comp
            (rho.toOperator.comp
              (LinearMap.adjoint
                ((I.tensor J).kraus.operator (leftIndex, rightIndex)))))) =
        ∑ leftIndex : kappa,
          LinearMap.trace Complex (CompositeSystem H R)
            (rho.toOperator.comp
              ((LinearMap.adjoint
                ((I.tensor J).kraus.operator (leftIndex, rightIndex))).comp
                ((I.tensor J).kraus.operator (leftIndex, rightIndex)))) := by
      apply Finset.sum_congr rfl
      intro leftIndex _
      simpa [LinearMap.comp_assoc] using
        (LinearMap.trace_comp_cycle
          (R := Complex) (M := CompositeSystem H R)
          (N := CompositeSystem H R) (P := CompositeSystem K S)
          (f := rho.toOperator)
          (g := (I.tensor J).kraus.operator (leftIndex, rightIndex))
          (h := LinearMap.adjoint
            ((I.tensor J).kraus.operator (leftIndex, rightIndex))))
    _ = ∑ leftIndex : kappa,
        LinearMap.trace Complex (CompositeSystem H R)
          (rho.toOperator.comp
            (TensorProduct.map (leftEffect leftIndex) rightEffect)) := by
      apply Finset.sum_congr rfl
      intro leftIndex _
      congr 2
      simp only [FiniteInstrument.tensor, TensorProduct.adjoint_map]
      rw [← TensorProduct.map_comp]
    _ = LinearMap.trace Complex (CompositeSystem H R)
        (rho.toOperator.comp
          (∑ leftIndex : kappa,
            TensorProduct.map (leftEffect leftIndex) rightEffect)) := by
      rw [← map_sum]
      congr 2
      ext vector
      simp [LinearMap.comp_apply]
    _ = LinearMap.trace Complex (CompositeSystem H R)
        (rho.toOperator.comp
          (TensorProduct.map (∑ leftIndex : kappa, leftEffect leftIndex)
            rightEffect)) := by
      rw [tensorMap_sum_left]
    _ = LinearMap.trace Complex (CompositeSystem H R)
        (rho.toOperator.comp
          (TensorProduct.map (LinearMap.id : Operator H) rightEffect)) := by
      rw [show (∑ leftIndex : kappa, leftEffect leftIndex) =
          (1 : Operator H) by exact hI]
      rfl
    _ = LinearMap.trace Complex R
        ((FiniteMatrixEntropy.partialTraceLeftRaw H R rho.toOperator).comp
          rightEffect) := by
      symm
      exact FiniteMatrixEntropy.partialTraceLeftRaw_trace_pairing
        rho.toOperator rightEffect
    _ = LinearMap.trace Complex S
        ((J.kraus.operator rightIndex).comp
          ((DensityOperator.leftMarginal rho).toOperator.comp
            (LinearMap.adjoint (J.kraus.operator rightIndex)))) := by
      have hleft : (DensityOperator.leftMarginal rho).toOperator =
          FiniteMatrixEntropy.partialTraceLeftRaw H R rho.toOperator := rfl
      rw [← hleft]
      simpa only [rightEffect, LinearMap.comp_assoc] using
        (LinearMap.trace_comp_cycle
          (R := Complex) (M := R) (N := R) (P := S)
          (f := (DensityOperator.leftMarginal rho).toOperator)
          (g := J.kraus.operator rightIndex)
          (h := LinearMap.adjoint (J.kraus.operator rightIndex))).symm

/-- Summing every visible left-factor outcome of a tensor instrument gives
the right visible Born mass on the true left-partial-trace marginal. -/
theorem tensor_bornWeight_snd_sum_eq_leftMarginal
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (J : FiniteInstrument kappaTwo Xi R S)
    (rightOutcome : Xi) (rho : DensityOperator (CompositeSystem H R)) :
    (∑ leftOutcome : Omega,
      (I.tensor J).bornWeight (leftOutcome, rightOutcome) rho) =
      J.bornWeight rightOutcome (DensityOperator.leftMarginal rho) := by
  classical
  simp_rw [bornWeight_eq_sum_rawBornWeight]
  rw [Finset.sum_comm, Fintype.sum_prod_type, Finset.sum_comm]
  calc
    _ = ∑ rightIndex : kappaTwo,
        if J.observe rightIndex = rightOutcome then
          ∑ leftIndex : kappa,
            (I.tensor J).rawBornWeight (leftIndex, rightIndex) rho
        else 0 := by
      apply Finset.sum_congr rfl
      intro rightIndex _
      by_cases hright : J.observe rightIndex = rightOutcome
      · rw [if_pos hright]
        apply Finset.sum_congr rfl
        intro leftIndex _
        simp [FiniteInstrument.tensor, hright]
      · rw [if_neg hright]
        apply Finset.sum_eq_zero
        intro leftIndex _
        apply Finset.sum_eq_zero
        intro leftOutcome _
        simp [FiniteInstrument.tensor, hright]
    _ = ∑ rightIndex : kappaTwo,
        if J.observe rightIndex = rightOutcome then
          J.rawBornWeight rightIndex (DensityOperator.leftMarginal rho)
        else 0 := by
      apply Finset.sum_congr rfl
      intro rightIndex _
      by_cases hright : J.observe rightIndex = rightOutcome
      · rw [if_pos hright, if_pos hright,
          tensor_rawBornWeight_snd_sum_eq_leftMarginal I hI J]
      · simp [hright]
    _ = _ := rfl

/-- The actual one-factor marginal of an arbitrary density on the canonical
right-nested tensor-power carrier.  This definition follows the selected
coordinate: coordinate zero traces out the tail, while a successor coordinate
first traces out the head and then recurses through the tail. -/
noncomputable def tensorPowerInputMarginal :
    (attempts : Nat) -> DensityOperator (tensorPowerCarrier H attempts) ->
      Fin attempts -> DensityOperator H
  | 0, _, trial => Fin.elim0 trial
  | attempts + 1, rho, trial =>
      Fin.cases
        (partialTraceRightRaw_mapDensity H (tensorPowerCarrier H attempts) rho)
        (fun tailTrial => tensorPowerInputMarginal attempts
          (DensityOperator.leftMarginal rho) tailTrial)
        trial

/-- For an arbitrary, possibly correlated tensor-power input, summing every
observed history except one selected coordinate gives exactly the base
instrument's Born mass on that coordinate's true reduced density. -/
theorem tensorPower_bornWeight_coordinate_sum_eq
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete) :
    ∀ (attempts : Nat)
      (rho : DensityOperator (tensorPowerCarrier H attempts))
      (trial : Fin attempts) (outcome : Omega),
      (∑ history : tensorPowerHistory Omega attempts,
        if tensorPowerHistoryAt Omega attempts history trial = outcome then
          (I.tensorPower attempts).bornWeight history rho
        else 0) =
        I.bornWeight outcome (tensorPowerInputMarginal attempts rho trial) := by
  intro attempts
  induction attempts with
  | zero =>
      intro rho trial
      exact Fin.elim0 trial
  | succ attempts ih =>
      intro rho trial outcome
      refine Fin.cases ?_ ?_ trial
      · change
          (∑ history : Omega × tensorPowerHistory Omega attempts,
            if history.1 = outcome then
              (I.tensor (I.tensorPower attempts)).bornWeight history rho
            else 0) =
            I.bornWeight outcome
              (partialTraceRightRaw_mapDensity H
                (tensorPowerCarrier H attempts) rho)
        rw [Fintype.sum_prod_type]
        calc
          _ = ∑ head : Omega,
              if head = outcome then
                ∑ tail : tensorPowerHistory Omega attempts,
                  (I.tensor (I.tensorPower attempts)).bornWeight (head, tail) rho
              else 0 := by
            apply Finset.sum_congr rfl
            intro head _
            by_cases hhead : head = outcome
            · simp [hhead]
            · simp [hhead]
          _ = ∑ head : Omega,
              if head = outcome then
                I.bornWeight head
                  (partialTraceRightRaw_mapDensity H
                    (tensorPowerCarrier H attempts) rho)
              else 0 := by
            apply Finset.sum_congr rfl
            intro head _
            by_cases hhead : head = outcome
            · rw [if_pos hhead, if_pos hhead,
                tensor_bornWeight_fst_sum_eq_partialTraceRight I
                  (I.tensorPower attempts) (I.tensorPower_complete hI attempts)]
            · simp [hhead]
          _ = _ := by simp
      · intro tailTrial
        change
          (∑ history : Omega × tensorPowerHistory Omega attempts,
            if tensorPowerHistoryAt Omega attempts history.2 tailTrial = outcome then
              (I.tensor (I.tensorPower attempts)).bornWeight history rho
            else 0) =
            I.bornWeight outcome
              (tensorPowerInputMarginal attempts
                (DensityOperator.leftMarginal rho) tailTrial)
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        calc
          _ = ∑ tail : tensorPowerHistory Omega attempts,
              if tensorPowerHistoryAt Omega attempts tail tailTrial = outcome then
                ∑ head : Omega,
                  (I.tensor (I.tensorPower attempts)).bornWeight (head, tail) rho
              else 0 := by
            apply Finset.sum_congr rfl
            intro tail _
            by_cases htail :
                tensorPowerHistoryAt Omega attempts tail tailTrial = outcome
            · simp [htail]
            · simp [htail]
          _ = ∑ tail : tensorPowerHistory Omega attempts,
              if tensorPowerHistoryAt Omega attempts tail tailTrial = outcome then
                (I.tensorPower attempts).bornWeight tail
                  (DensityOperator.leftMarginal rho)
              else 0 := by
            apply Finset.sum_congr rfl
            intro tail _
            by_cases htail :
                tensorPowerHistoryAt Omega attempts tail tailTrial = outcome
            · rw [if_pos htail, if_pos htail,
                tensor_bornWeight_snd_sum_eq_leftMarginal I hI]
            · simp [htail]
          _ = _ := ih (DensityOperator.leftMarginal rho) tailTrial outcome

/-- The Born mass of a failure event on one selected coordinate is exactly
the base-instrument failure mass on that coordinate's true marginal. -/
theorem tensorPower_bornWeight_coordinate_failure_sum_eq
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (fails : Omega -> Prop) [DecidablePred fails]
    (attempts : Nat) (rho : DensityOperator (tensorPowerCarrier H attempts))
    (trial : Fin attempts) :
    (∑ history ∈ Finset.univ.filter (fun history : tensorPowerHistory Omega attempts =>
        fails (tensorPowerHistoryAt Omega attempts history trial)),
      (I.tensorPower attempts).bornWeight history rho) =
      ∑ outcome ∈ Finset.univ.filter fails,
        I.bornWeight outcome (tensorPowerInputMarginal attempts rho trial) := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter]
  calc
    (∑ history : tensorPowerHistory Omega attempts,
        if fails (tensorPowerHistoryAt Omega attempts history trial) then
          (I.tensorPower attempts).bornWeight history rho
        else 0) =
        ∑ outcome : Omega,
          if fails outcome then
            ∑ history : tensorPowerHistory Omega attempts,
              if tensorPowerHistoryAt Omega attempts history trial = outcome then
                (I.tensorPower attempts).bornWeight history rho
              else 0
          else 0 := by
      symm
      calc
        _ = ∑ outcome : Omega, ∑ history : tensorPowerHistory Omega attempts,
            if fails outcome then
              if tensorPowerHistoryAt Omega attempts history trial = outcome then
                (I.tensorPower attempts).bornWeight history rho
              else 0
            else 0 := by
          apply Finset.sum_congr rfl
          intro outcome _
          by_cases houtcome : fails outcome <;> simp [houtcome]
        _ = ∑ history : tensorPowerHistory Omega attempts, ∑ outcome : Omega,
            if fails outcome then
              if tensorPowerHistoryAt Omega attempts history trial = outcome then
                (I.tensorPower attempts).bornWeight history rho
              else 0
            else 0 := by
          rw [Finset.sum_comm]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro history _
          calc
            (∑ outcome : Omega,
                if fails outcome then
                  if tensorPowerHistoryAt Omega attempts history trial = outcome then
                    (I.tensorPower attempts).bornWeight history rho
                  else 0
                else 0) =
                ∑ outcome : Omega,
                  if tensorPowerHistoryAt Omega attempts history trial = outcome then
                    if fails outcome then
                      (I.tensorPower attempts).bornWeight history rho
                    else 0
                  else 0 := by
              apply Finset.sum_congr rfl
              intro outcome _
              by_cases heq :
                  tensorPowerHistoryAt Omega attempts history trial = outcome
              <;> simp [heq]
            _ = _ := by simp
    _ = ∑ outcome : Omega,
        if fails outcome then
          I.bornWeight outcome (tensorPowerInputMarginal attempts rho trial)
        else 0 := by
      apply Finset.sum_congr rfl
      intro outcome _
      by_cases houtcome : fails outcome
      · rw [if_pos houtcome, if_pos houtcome,
          tensorPower_bornWeight_coordinate_sum_eq I hI]
      · simp [houtcome]

/-- A finite weighted union bound for tensor-power outcomes.  Failure of any
coordinate is charged to the sum of its true marginal failure masses; no
factorization or independence of the joint input is assumed. -/
theorem tensorPower_bornWeight_any_coordinate_failure_le
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (fails : Omega -> Prop) [DecidablePred fails]
    (attempts : Nat) (rho : DensityOperator (tensorPowerCarrier H attempts)) :
    (∑ history ∈ Finset.univ.filter (fun history : tensorPowerHistory Omega attempts =>
        ∃ trial : Fin attempts,
          fails (tensorPowerHistoryAt Omega attempts history trial)),
      (I.tensorPower attempts).bornWeight history rho) <=
      ∑ trial : Fin attempts,
        ∑ outcome ∈ Finset.univ.filter fails,
          I.bornWeight outcome (tensorPowerInputMarginal attempts rho trial) := by
  classical
  rw [Finset.sum_filter]
  calc
    (∑ history : tensorPowerHistory Omega attempts,
        if (∃ trial : Fin attempts,
              fails (tensorPowerHistoryAt Omega attempts history trial)) then
          (I.tensorPower attempts).bornWeight history rho
        else 0) <=
        ∑ history : tensorPowerHistory Omega attempts,
          ∑ trial : Fin attempts,
            if fails (tensorPowerHistoryAt Omega attempts history trial) then
              (I.tensorPower attempts).bornWeight history rho
            else 0 := by
      apply Finset.sum_le_sum
      intro history _
      by_cases hfailure : ∃ trial : Fin attempts,
          fails (tensorPowerHistoryAt Omega attempts history trial)
      · rw [if_pos hfailure]
        obtain ⟨trial, htrial⟩ := hfailure
        simpa [htrial] using
          (Finset.single_le_sum
            (s := (Finset.univ : Finset (Fin attempts)))
            (f := fun other : Fin attempts =>
              if fails (tensorPowerHistoryAt Omega attempts history other) then
                (I.tensorPower attempts).bornWeight history rho
              else 0)
            (fun other _ => by
              by_cases hother :
                  fails (tensorPowerHistoryAt Omega attempts history other)
              · simpa [hother] using
                  (I.tensorPower attempts).bornWeight_nonneg history rho
              · simp [hother])
            (Finset.mem_univ trial))
      · rw [if_neg hfailure]
        exact Finset.sum_nonneg fun trial _ => by
          by_cases htrial : fails (tensorPowerHistoryAt Omega attempts history trial)
          · simpa [htrial] using
              (I.tensorPower attempts).bornWeight_nonneg history rho
          · simp [htrial]
    _ = ∑ trial : Fin attempts,
        ∑ history : tensorPowerHistory Omega attempts,
          if fails (tensorPowerHistoryAt Omega attempts history trial) then
            (I.tensorPower attempts).bornWeight history rho
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ trial : Fin attempts,
        ∑ outcome ∈ Finset.univ.filter fails,
          I.bornWeight outcome (tensorPowerInputMarginal attempts rho trial) := by
      apply Finset.sum_congr rfl
      intro trial _
      rw [← Finset.sum_filter]
      exact tensorPower_bornWeight_coordinate_failure_sum_eq
        I hI fails attempts rho trial

end FiniteInstrument

end
end Semantics
end QEC
