import QEC.Semantics.Instruments.TensorPower.BornMass
/-!
# Sequential finite-instrument Born-mass marginals

This source-neutral layer proves that a complete dependent successor
instrument preserves the Born mass of every observed predecessor outcome.
The statement is purely about actual Kraus branches and trace preservation;
it adds no independence, conditional-state, or probability hypothesis.
-/

universe u v w x y

namespace QEC
namespace Semantics

open scoped BigOperators ComplexOrder

noncomputable section

namespace FiniteInstrument

variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Omega -> Type x} [forall outcome, Fintype (kappaTwo outcome)]
variable {Xi : Omega -> Type y} [forall outcome, Fintype (Xi outcome)]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

section FixedRawIndex

variable {kappaPrime : Type x} [Fintype kappaPrime]

/-- Summing a complete outcome-selected successor with a fixed raw index type
preserves the predecessor raw branch mass. -/
theorem rawBornWeight_bind_sum_general
    (I : FiniteInstrument kappa Omega H K)
    (J : (outcome : Omega) -> FiniteInstrument kappaPrime (Xi outcome) K L)
    (hJ : forall outcome, (J outcome).kraus.Complete) (rho : DensityOperator H)
    (firstIndex : kappa) :
    (∑ secondIndex : kappaPrime,
      (I.bind J).rawBornWeight (firstIndex, secondIndex) rho) =
        I.rawBornWeight firstIndex rho := by
  unfold rawBornWeight
  rw [← Complex.re_sum, ← map_sum]
  have hraw :
      (∑ secondIndex : kappaPrime,
        (I.bind J).rawBranchOperator (firstIndex, secondIndex) rho.toOperator) =
          (J (I.observe firstIndex)).kraus.inducedMap
            (I.rawBranchOperator firstIndex rho.toOperator) := by
    rw [FiniteKrausFamily.inducedMap_apply]
    apply Finset.sum_congr rfl
    intro secondIndex _
    simp [rawBranchOperator, bind_kraus_operator,
      LinearMap.adjoint_comp, LinearMap.comp_assoc]
  rw [hraw]
  exact congrArg Complex.re
    ((J (I.observe firstIndex)).kraus.inducedMap_trace_preserving
      (hJ (I.observe firstIndex)) _)

/-- Summing every observed fixed-raw-index successor outcome above a fixed
predecessor outcome recovers exactly the predecessor Born mass. -/
theorem bind_bornWeight_fst_sum
    (I : FiniteInstrument kappa Omega H K)
    (J : (outcome : Omega) -> FiniteInstrument kappaPrime (Xi outcome) K L)
    (hJ : forall outcome, (J outcome).kraus.Complete)
    (outcome : Omega) (rho : DensityOperator H) :
    (∑ secondOutcome : Xi outcome,
      (I.bind J).bornWeight ⟨outcome, secondOutcome⟩ rho) =
        I.bornWeight outcome rho := by
  classical
  simp_rw [bornWeight_eq_sum_rawBornWeight]
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  calc
    _ = ∑ firstIndex : kappa,
        if I.observe firstIndex = outcome then
          ∑ secondIndex : kappaPrime,
            (I.bind J).rawBornWeight (firstIndex, secondIndex) rho
        else 0 := by
      apply Finset.sum_congr rfl
      intro firstIndex _
      by_cases hfirst : I.observe firstIndex = outcome
      · subst outcome
        simp [bind]
      · simp only [if_neg hfirst]
        apply Finset.sum_eq_zero
        intro secondIndex _
        apply Finset.sum_eq_zero
        intro secondOutcome _
        rw [if_neg]
        intro heq
        exact hfirst (congrArg Sigma.fst heq)
    _ = ∑ firstIndex : kappa,
        if I.observe firstIndex = outcome then I.rawBornWeight firstIndex rho else 0 := by
      apply Finset.sum_congr rfl
      intro firstIndex _
      by_cases hfirst : I.observe firstIndex = outcome
      · rw [if_pos hfirst,
          rawBornWeight_bind_sum_general I J hJ rho firstIndex,
          if_pos hfirst]
      · simp [hfirst]

/-- Filtering a complete fixed-raw-index bind by a predicate on the retained
predecessor observation preserves exactly the corresponding filtered Born
mass.  The successor outcomes are all summed, so no independence premise is
needed. -/
theorem bind_bornWeight_fst_filter_sum
    (I : FiniteInstrument kappa Omega H K)
    (J : (outcome : Omega) -> FiniteInstrument kappaPrime (Xi outcome) K L)
    (hJ : forall outcome, (J outcome).kraus.Complete)
    (predicate : Omega -> Prop) [DecidablePred predicate]
    (rho : DensityOperator H) :
    (∑ outcome ∈ Finset.univ.filter
        (fun outcome : Sigma Xi => predicate outcome.1),
      (I.bind J).bornWeight outcome rho) =
      ∑ outcome ∈ Finset.univ.filter predicate, I.bornWeight outcome rho := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases houtcome : predicate outcome
  · simp only [houtcome, if_true]
    exact bind_bornWeight_fst_sum I J hJ outcome rho
  · simp [houtcome]

end FixedRawIndex

/-- Summing a complete dependent successor over its actual raw Kraus fibre
preserves the predecessor raw branch mass. -/
theorem rawBornWeight_bindDependent_sum_general
    (I : FiniteInstrument kappa Omega H K)
    (J : (outcome : Omega) -> FiniteInstrument (kappaTwo outcome) (Xi outcome) K L)
    (hJ : forall outcome, (J outcome).kraus.Complete) (rho : DensityOperator H)
    (firstIndex : kappa) :
    (∑ secondIndex : kappaTwo (I.observe firstIndex),
      (I.bindDependent J).rawBornWeight ⟨firstIndex, secondIndex⟩ rho) =
        I.rawBornWeight firstIndex rho := by
  unfold rawBornWeight
  rw [← Complex.re_sum, ← map_sum]
  have hraw :
      (∑ secondIndex : kappaTwo (I.observe firstIndex),
        (I.bindDependent J).rawBranchOperator ⟨firstIndex, secondIndex⟩ rho.toOperator) =
          (J (I.observe firstIndex)).kraus.inducedMap
            (I.rawBranchOperator firstIndex rho.toOperator) := by
    rw [FiniteKrausFamily.inducedMap_apply]
    apply Finset.sum_congr rfl
    intro secondIndex _
    simp [rawBranchOperator, bindDependent_kraus_operator,
      LinearMap.adjoint_comp, LinearMap.comp_assoc]
  rw [hraw]
  exact congrArg Complex.re
    ((J (I.observe firstIndex)).kraus.inducedMap_trace_preserving
      (hJ (I.observe firstIndex)) _)

/-- Summing every observed successor outcome above a fixed predecessor
outcome recovers exactly that predecessor's Born mass. -/
theorem bindDependent_bornWeight_fst_sum
    (I : FiniteInstrument kappa Omega H K)
    (J : (outcome : Omega) -> FiniteInstrument (kappaTwo outcome) (Xi outcome) K L)
    (hJ : forall outcome, (J outcome).kraus.Complete)
    (outcome : Omega) (rho : DensityOperator H) :
    (∑ secondOutcome : Xi outcome,
      (I.bindDependent J).bornWeight ⟨outcome, secondOutcome⟩ rho) =
        I.bornWeight outcome rho := by
  classical
  simp_rw [bornWeight_eq_sum_rawBornWeight]
  rw [Finset.sum_comm, Fintype.sum_sigma]
  calc
    _ = ∑ firstIndex : kappa,
        if I.observe firstIndex = outcome then
          ∑ secondIndex : kappaTwo (I.observe firstIndex),
            (I.bindDependent J).rawBornWeight ⟨firstIndex, secondIndex⟩ rho
        else 0 := by
      apply Finset.sum_congr rfl
      intro firstIndex _
      by_cases hfirst : I.observe firstIndex = outcome
      · subst outcome
        simp [bindDependent_observe]
      · simp only [if_neg hfirst]
        apply Finset.sum_eq_zero
        intro secondIndex _
        apply Finset.sum_eq_zero
        intro secondOutcome _
        rw [if_neg]
        intro heq
        exact hfirst (congrArg Sigma.fst heq)
    _ = ∑ firstIndex : kappa,
        if I.observe firstIndex = outcome then I.rawBornWeight firstIndex rho else 0 := by
      apply Finset.sum_congr rfl
      intro firstIndex _
      by_cases hfirst : I.observe firstIndex = outcome
      · rw [if_pos hfirst,
          rawBornWeight_bindDependent_sum_general I J hJ rho firstIndex,
          if_pos hfirst]
      · simp [hfirst]

end FiniteInstrument

end
end Semantics
end QEC
