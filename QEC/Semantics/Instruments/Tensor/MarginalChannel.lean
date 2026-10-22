import QEC.Semantics.Instruments.Tensor.MarginalBornMass
/-!
# Marginals of local tensor channels

Complete local finite instruments cannot signal between tensor factors.  This
module states that fact at the density-operator level: after applying both
local channels to an arbitrary, possibly correlated input, either output
marginal is the corresponding local channel applied to the true input
marginal.
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

private theorem tensorMap_sum_sum
    (a : kappa -> Operator H) (b : kappaTwo -> Operator R) :
    TensorProduct.map (∑ i, a i) (∑ j, b j) =
      ∑ i, ∑ j, TensorProduct.map (a i) (b j) := by
  classical
  have hleft (indices : Finset kappa) :
      TensorProduct.map (∑ i ∈ indices, a i) (∑ j, b j) =
        ∑ i ∈ indices, TensorProduct.map (a i) (∑ j, b j) := by
    induction indices using Finset.induction_on with
    | empty => simp
    | @insert index indices hindex ih =>
        simp [Finset.sum_insert hindex, TensorProduct.map_add_left, ih]
  have hright (i : kappa) (indices : Finset kappaTwo) :
      TensorProduct.map (a i) (∑ j ∈ indices, b j) =
        ∑ j ∈ indices, TensorProduct.map (a i) (b j) := by
    induction indices using Finset.induction_on with
    | empty => simp
    | @insert index indices hindex ih =>
        simp [Finset.sum_insert hindex, TensorProduct.map_add_right, ih]
  calc
    TensorProduct.map (∑ i, a i) (∑ j, b j) =
        ∑ i, TensorProduct.map (a i) (∑ j, b j) := by
      simpa using hleft Finset.univ
    _ = ∑ i, ∑ j, TensorProduct.map (a i) (b j) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa using hright i Finset.univ

/-- Tracing out the complete right local instrument after a tensor operation
leaves the left induced map acting on the actual input marginal. -/
theorem tensor_inducedMap_partialTraceRight
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S) (hJ : J.kraus.Complete)
    (A : Operator (CompositeSystem H R)) :
    partialTraceRightRaw K S ((I.tensor J).kraus.inducedMap A) =
      I.kraus.inducedMap (partialTraceRightRaw H R A) := by
  let leftEffect : kappa -> Operator H := fun leftIndex =>
    (LinearMap.adjoint (I.kraus.operator leftIndex)).comp
      ((LinearMap.id : Operator K).comp (I.kraus.operator leftIndex))
  let rightEffect : kappaTwo -> Operator R := fun rightIndex =>
    (LinearMap.adjoint (J.kraus.operator rightIndex)).comp
      (J.kraus.operator rightIndex)
  let basisS : OrthonormalBasis
      (ULift.{u} (Fin (Module.finrank Complex S))) Complex S :=
    (stdOrthonormalBasis Complex S).reindex Equiv.ulift.symm
  apply operator_ext_of_trace_comp_right_eq
  intro X
  let testedLeftEffect : kappa -> Operator H := fun leftIndex =>
    (LinearMap.adjoint (I.kraus.operator leftIndex)).comp
      (X.comp (I.kraus.operator leftIndex))
  calc
    LinearMap.trace Complex K
        (X.comp (partialTraceRightRaw K S ((I.tensor J).kraus.inducedMap A))) =
      LinearMap.trace Complex K
        ((partialTraceRightRaw K S ((I.tensor J).kraus.inducedMap A)).comp X) :=
      (LinearMap.trace_comp_comm' X _).symm
    _ = LinearMap.trace Complex (CompositeSystem K S)
        (((I.tensor J).kraus.inducedMap A).comp
          (TensorProduct.map X (LinearMap.id : Operator S))) :=
      FiniteMatrixEntropy.partialTraceRightRaw_trace_pairing
        basisS ((I.tensor J).kraus.inducedMap A) X
    _ = ∑ leftIndex : kappa, ∑ rightIndex : kappaTwo,
        LinearMap.trace Complex (CompositeSystem H R)
          (A.comp (TensorProduct.map
            (testedLeftEffect leftIndex) (rightEffect rightIndex))) := by
      rw [FiniteKrausFamily.inducedMap_apply, Fintype.sum_prod_type]
      have hcomp :
          ((∑ leftIndex : kappa, ∑ rightIndex : kappaTwo,
              ((I.tensor J).kraus.operator (leftIndex, rightIndex)).comp
                (A.comp (LinearMap.adjoint
                  ((I.tensor J).kraus.operator (leftIndex, rightIndex))))) ).comp
              (TensorProduct.map X (LinearMap.id : Operator S)) =
            ∑ leftIndex : kappa, ∑ rightIndex : kappaTwo,
              (((I.tensor J).kraus.operator (leftIndex, rightIndex)).comp
                (A.comp (LinearMap.adjoint
                  ((I.tensor J).kraus.operator (leftIndex, rightIndex))))).comp
                (TensorProduct.map X (LinearMap.id : Operator S)) := by
        ext vector
        simp [LinearMap.comp_apply]
      rw [hcomp, map_sum]
      apply Finset.sum_congr rfl
      intro leftIndex _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro rightIndex _
      let localOperator :=
        TensorProduct.map (I.kraus.operator leftIndex)
          (J.kraus.operator rightIndex)
      have hcycle := LinearMap.trace_comp_cycle
        (R := Complex) (M := CompositeSystem H R)
        (N := CompositeSystem H R) (P := CompositeSystem K S)
        (f := A) (g := localOperator)
        (h := (LinearMap.adjoint localOperator).comp
          (TensorProduct.map X (LinearMap.id : Operator S)))
      calc
        LinearMap.trace Complex (CompositeSystem K S)
            ((localOperator.comp
              (A.comp (LinearMap.adjoint localOperator))).comp
                (TensorProduct.map X (LinearMap.id : Operator S))) =
          LinearMap.trace Complex (CompositeSystem H R)
            (A.comp (((LinearMap.adjoint localOperator).comp
              (TensorProduct.map X (LinearMap.id : Operator S))).comp
                localOperator)) := by
          simpa [LinearMap.comp_assoc] using hcycle
        _ = _ := by
          congr 2
          simp only [localOperator, TensorProduct.adjoint_map]
          rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
          rfl
    _ = LinearMap.trace Complex (CompositeSystem H R)
        (A.comp (TensorProduct.map (∑ leftIndex, testedLeftEffect leftIndex)
          (∑ rightIndex, rightEffect rightIndex))) := by
      rw [tensorMap_sum_sum]
      have hcomp :
          A.comp (∑ leftIndex : kappa, ∑ rightIndex : kappaTwo,
              TensorProduct.map (testedLeftEffect leftIndex)
                (rightEffect rightIndex)) =
            ∑ leftIndex : kappa, ∑ rightIndex : kappaTwo,
              A.comp (TensorProduct.map (testedLeftEffect leftIndex)
                (rightEffect rightIndex)) := by
        ext vector
        simp [LinearMap.comp_apply]
      rw [hcomp, map_sum]
      apply Finset.sum_congr rfl
      intro leftIndex _
      rw [map_sum]
    _ = LinearMap.trace Complex (CompositeSystem H R)
        (A.comp (TensorProduct.map (∑ leftIndex, testedLeftEffect leftIndex)
          (LinearMap.id : Operator R))) := by
      rw [show (∑ rightIndex, rightEffect rightIndex) = (1 : Operator R) by
        exact hJ]
      rfl
    _ = LinearMap.trace Complex H
        ((partialTraceRightRaw H R A).comp
          (∑ leftIndex, testedLeftEffect leftIndex)) := by
      symm
      let basisR : OrthonormalBasis
          (ULift.{u} (Fin (Module.finrank Complex R))) Complex R :=
        (stdOrthonormalBasis Complex R).reindex Equiv.ulift.symm
      exact FiniteMatrixEntropy.partialTraceRightRaw_trace_pairing
        basisR A (∑ leftIndex, testedLeftEffect leftIndex)
    _ = LinearMap.trace Complex K
        ((I.kraus.inducedMap (partialTraceRightRaw H R A)).comp X) := by
      rw [FiniteKrausFamily.inducedMap_apply]
      have hcomp :
          (∑ leftIndex : kappa,
              (I.kraus.operator leftIndex).comp
                ((partialTraceRightRaw H R A).comp
                  (LinearMap.adjoint (I.kraus.operator leftIndex)))).comp X =
            ∑ leftIndex : kappa,
              ((I.kraus.operator leftIndex).comp
                ((partialTraceRightRaw H R A).comp
                  (LinearMap.adjoint (I.kraus.operator leftIndex)))).comp X := by
        ext vector
        simp [LinearMap.comp_apply]
      rw [hcomp, map_sum]
      have hdistribute :
          (partialTraceRightRaw H R A).comp
              (∑ leftIndex, testedLeftEffect leftIndex) =
            ∑ leftIndex,
              (partialTraceRightRaw H R A).comp
                (testedLeftEffect leftIndex) := by
        ext vector
        simp [LinearMap.comp_apply]
      rw [hdistribute, map_sum]
      apply Finset.sum_congr rfl
      intro leftIndex _
      simpa [testedLeftEffect, LinearMap.comp_assoc] using
        (LinearMap.trace_comp_cycle
          (R := Complex) (M := H) (N := H) (P := K)
          (f := partialTraceRightRaw H R A)
          (g := I.kraus.operator leftIndex)
          (h := (LinearMap.adjoint (I.kraus.operator leftIndex)).comp X)).symm
    _ = LinearMap.trace Complex K
        (X.comp (I.kraus.inducedMap (partialTraceRightRaw H R A))) :=
      LinearMap.trace_comp_comm' _ _

/-- Density-operator form of `tensor_inducedMap_partialTraceRight`. -/
theorem tensor_channel_mapDensity_partialTraceRight
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S)
    (hI : I.kraus.Complete) (hJ : J.kraus.Complete)
    (rho : DensityOperator (CompositeSystem H R)) :
    partialTraceRightRaw_mapDensity K S
        (((I.tensor J).kraus.toQuantumChannel
          (I.tensor_complete J hI hJ)).mapDensity rho) =
      (I.kraus.toQuantumChannel hI).mapDensity
        (partialTraceRightRaw_mapDensity H R rho) := by
  apply DensityOperator.ext_toOperator
  simp only [partialTraceRightRaw_mapDensity_toOperator,
    QuantumChannel.mapDensity_toOperator,
    FiniteKrausFamily.toQuantumChannel_apply]
  exact tensor_inducedMap_partialTraceRight I J hJ rho.toOperator

/-- Tracing out the complete left local instrument after a tensor operation
leaves the right induced map acting on the actual input marginal. -/
theorem tensor_inducedMap_partialTraceLeft
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S) (hI : I.kraus.Complete)
    (A : Operator (CompositeSystem H R)) :
    FiniteMatrixEntropy.partialTraceLeftRaw K S
        ((I.tensor J).kraus.inducedMap A) =
      J.kraus.inducedMap
        (FiniteMatrixEntropy.partialTraceLeftRaw H R A) := by
  let leftEffect : kappa -> Operator H := fun leftIndex =>
    (LinearMap.adjoint (I.kraus.operator leftIndex)).comp
      (I.kraus.operator leftIndex)
  let rightEffect : kappaTwo -> Operator R := fun rightIndex =>
    (LinearMap.adjoint (J.kraus.operator rightIndex)).comp
      ((LinearMap.id : Operator S).comp (J.kraus.operator rightIndex))
  apply operator_ext_of_trace_comp_right_eq
  intro Y
  let testedRightEffect : kappaTwo -> Operator R := fun rightIndex =>
    (LinearMap.adjoint (J.kraus.operator rightIndex)).comp
      (Y.comp (J.kraus.operator rightIndex))
  calc
    LinearMap.trace Complex S
        (Y.comp (FiniteMatrixEntropy.partialTraceLeftRaw K S
          ((I.tensor J).kraus.inducedMap A))) =
      LinearMap.trace Complex S
        ((FiniteMatrixEntropy.partialTraceLeftRaw K S
          ((I.tensor J).kraus.inducedMap A)).comp Y) :=
      (LinearMap.trace_comp_comm' Y _).symm
    _ = LinearMap.trace Complex (CompositeSystem K S)
        (((I.tensor J).kraus.inducedMap A).comp
          (TensorProduct.map (LinearMap.id : Operator K) Y)) :=
      FiniteMatrixEntropy.partialTraceLeftRaw_trace_pairing
        ((I.tensor J).kraus.inducedMap A) Y
    _ = ∑ leftIndex : kappa, ∑ rightIndex : kappaTwo,
        LinearMap.trace Complex (CompositeSystem H R)
          (A.comp (TensorProduct.map
            (leftEffect leftIndex) (testedRightEffect rightIndex))) := by
      rw [FiniteKrausFamily.inducedMap_apply, Fintype.sum_prod_type]
      have hcomp :
          ((∑ leftIndex : kappa, ∑ rightIndex : kappaTwo,
              ((I.tensor J).kraus.operator (leftIndex, rightIndex)).comp
                (A.comp (LinearMap.adjoint
                  ((I.tensor J).kraus.operator (leftIndex, rightIndex))))) ).comp
              (TensorProduct.map (LinearMap.id : Operator K) Y) =
            ∑ leftIndex : kappa, ∑ rightIndex : kappaTwo,
              (((I.tensor J).kraus.operator (leftIndex, rightIndex)).comp
                (A.comp (LinearMap.adjoint
                  ((I.tensor J).kraus.operator (leftIndex, rightIndex))))).comp
                (TensorProduct.map (LinearMap.id : Operator K) Y) := by
        ext vector
        simp [LinearMap.comp_apply]
      rw [hcomp, map_sum]
      apply Finset.sum_congr rfl
      intro leftIndex _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro rightIndex _
      let localOperator :=
        TensorProduct.map (I.kraus.operator leftIndex)
          (J.kraus.operator rightIndex)
      have hcycle := LinearMap.trace_comp_cycle
        (R := Complex) (M := CompositeSystem H R)
        (N := CompositeSystem H R) (P := CompositeSystem K S)
        (f := A) (g := localOperator)
        (h := (LinearMap.adjoint localOperator).comp
          (TensorProduct.map (LinearMap.id : Operator K) Y))
      calc
        LinearMap.trace Complex (CompositeSystem K S)
            ((localOperator.comp
              (A.comp (LinearMap.adjoint localOperator))).comp
                (TensorProduct.map (LinearMap.id : Operator K) Y)) =
          LinearMap.trace Complex (CompositeSystem H R)
            (A.comp (((LinearMap.adjoint localOperator).comp
              (TensorProduct.map (LinearMap.id : Operator K) Y)).comp
                localOperator)) := by
          simpa [LinearMap.comp_assoc] using hcycle
        _ = _ := by
          congr 2
          simp only [localOperator, TensorProduct.adjoint_map]
          rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
          rfl
    _ = LinearMap.trace Complex (CompositeSystem H R)
        (A.comp (TensorProduct.map (∑ leftIndex, leftEffect leftIndex)
          (∑ rightIndex, testedRightEffect rightIndex))) := by
      rw [tensorMap_sum_sum]
      have hcomp :
          A.comp (∑ leftIndex : kappa, ∑ rightIndex : kappaTwo,
              TensorProduct.map (leftEffect leftIndex)
                (testedRightEffect rightIndex)) =
            ∑ leftIndex : kappa, ∑ rightIndex : kappaTwo,
              A.comp (TensorProduct.map (leftEffect leftIndex)
                (testedRightEffect rightIndex)) := by
        ext vector
        simp [LinearMap.comp_apply]
      rw [hcomp, map_sum]
      apply Finset.sum_congr rfl
      intro leftIndex _
      rw [map_sum]
    _ = LinearMap.trace Complex (CompositeSystem H R)
        (A.comp (TensorProduct.map (LinearMap.id : Operator H)
          (∑ rightIndex, testedRightEffect rightIndex))) := by
      rw [show (∑ leftIndex, leftEffect leftIndex) = (1 : Operator H) by
        exact hI]
      rfl
    _ = LinearMap.trace Complex R
        ((FiniteMatrixEntropy.partialTraceLeftRaw H R A).comp
          (∑ rightIndex, testedRightEffect rightIndex)) := by
      symm
      exact FiniteMatrixEntropy.partialTraceLeftRaw_trace_pairing
        A (∑ rightIndex, testedRightEffect rightIndex)
    _ = LinearMap.trace Complex S
        ((J.kraus.inducedMap
          (FiniteMatrixEntropy.partialTraceLeftRaw H R A)).comp Y) := by
      rw [FiniteKrausFamily.inducedMap_apply]
      have hcomp :
          (∑ rightIndex : kappaTwo,
              (J.kraus.operator rightIndex).comp
                ((FiniteMatrixEntropy.partialTraceLeftRaw H R A).comp
                  (LinearMap.adjoint (J.kraus.operator rightIndex)))).comp Y =
            ∑ rightIndex : kappaTwo,
              ((J.kraus.operator rightIndex).comp
                ((FiniteMatrixEntropy.partialTraceLeftRaw H R A).comp
                  (LinearMap.adjoint (J.kraus.operator rightIndex)))).comp Y := by
        ext vector
        simp [LinearMap.comp_apply]
      rw [hcomp, map_sum]
      have hdistribute :
          (FiniteMatrixEntropy.partialTraceLeftRaw H R A).comp
              (∑ rightIndex, testedRightEffect rightIndex) =
            ∑ rightIndex,
              (FiniteMatrixEntropy.partialTraceLeftRaw H R A).comp
                (testedRightEffect rightIndex) := by
        ext vector
        simp [LinearMap.comp_apply]
      rw [hdistribute, map_sum]
      apply Finset.sum_congr rfl
      intro rightIndex _
      simpa [testedRightEffect, LinearMap.comp_assoc] using
        (LinearMap.trace_comp_cycle
          (R := Complex) (M := R) (N := R) (P := S)
          (f := FiniteMatrixEntropy.partialTraceLeftRaw H R A)
          (g := J.kraus.operator rightIndex)
          (h := (LinearMap.adjoint (J.kraus.operator rightIndex)).comp Y)).symm
    _ = LinearMap.trace Complex S
        (Y.comp (J.kraus.inducedMap
          (FiniteMatrixEntropy.partialTraceLeftRaw H R A))) :=
      LinearMap.trace_comp_comm' _ _

/-- Density-operator form of `tensor_inducedMap_partialTraceLeft`. -/
theorem tensor_channel_mapDensity_leftMarginal
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S)
    (hI : I.kraus.Complete) (hJ : J.kraus.Complete)
    (rho : DensityOperator (CompositeSystem H R)) :
    DensityOperator.leftMarginal
        (((I.tensor J).kraus.toQuantumChannel
          (I.tensor_complete J hI hJ)).mapDensity rho) =
      (J.kraus.toQuantumChannel hJ).mapDensity
        (DensityOperator.leftMarginal rho) := by
  apply DensityOperator.ext_toOperator
  change FiniteMatrixEntropy.partialTraceLeftRaw K S
      ((I.tensor J).kraus.inducedMap rho.toOperator) =
    J.kraus.inducedMap
      (FiniteMatrixEntropy.partialTraceLeftRaw H R rho.toOperator)
  exact tensor_inducedMap_partialTraceLeft I J hI rho.toOperator

/-- A homogeneous tensor channel maps every true coordinate marginal by its
one-factor channel, even when the tensor-power input is correlated. -/
theorem tensorPower_channel_mapDensity_coordinate_marginal
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete) :
    ∀ (attempts : Nat)
      (rho : DensityOperator (tensorPowerCarrier H attempts))
      (trial : Fin attempts),
      tensorPowerInputMarginal attempts
          (((I.tensorPower attempts).kraus.toQuantumChannel
            (I.tensorPower_complete hI attempts)).mapDensity rho) trial =
        (I.kraus.toQuantumChannel hI).mapDensity
          (tensorPowerInputMarginal attempts rho trial) := by
  intro attempts
  induction attempts with
  | zero =>
      intro rho trial
      exact Fin.elim0 trial
  | succ attempts ih =>
      intro rho trial
      refine Fin.cases ?_ ?_ trial
      · exact tensor_channel_mapDensity_partialTraceRight
          I (I.tensorPower attempts) hI
          (I.tensorPower_complete hI attempts) rho
      · intro tailTrial
        change tensorPowerInputMarginal attempts
            (DensityOperator.leftMarginal
              (((I.tensorPower (attempts + 1)).kraus.toQuantumChannel
                (I.tensorPower_complete hI (attempts + 1))).mapDensity rho)) tailTrial =
          (I.kraus.toQuantumChannel hI).mapDensity
            (tensorPowerInputMarginal attempts
              (DensityOperator.leftMarginal rho) tailTrial)
        have hmarginal := tensor_channel_mapDensity_leftMarginal
          I (I.tensorPower attempts) hI
            (I.tensorPower_complete hI attempts) rho
        change DensityOperator.leftMarginal
            (((I.tensor (I.tensorPower attempts)).kraus.toQuantumChannel
              (I.tensor_complete (I.tensorPower attempts) hI
                (I.tensorPower_complete hI attempts))).mapDensity rho) =
          ((I.tensorPower attempts).kraus.toQuantumChannel
            (I.tensorPower_complete hI attempts)).mapDensity
              (DensityOperator.leftMarginal rho) at hmarginal
        change tensorPowerInputMarginal attempts
            (DensityOperator.leftMarginal
              (((I.tensor (I.tensorPower attempts)).kraus.toQuantumChannel
                (I.tensor_complete (I.tensorPower attempts) hI
                  (I.tensorPower_complete hI attempts))).mapDensity rho)) tailTrial =
          (I.kraus.toQuantumChannel hI).mapDensity
            (tensorPowerInputMarginal attempts
              (DensityOperator.leftMarginal rho) tailTrial)
        rw [hmarginal]
        exact ih (DensityOperator.leftMarginal rho) tailTrial

end FiniteInstrument

end
end Semantics
end QEC
