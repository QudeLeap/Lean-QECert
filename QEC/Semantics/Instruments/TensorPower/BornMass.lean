import QEC.Semantics.Instruments.TensorPower.ConditionedChannel
/-!
# Born masses of finite tensor-power instrument histories

This internal API derives raw-branch weights from the actual Kraus operators,
factors them on recursively tensorized independent inputs, regroups them into
observable histories, and partitions those observed histories into enough and
shortage events.  It stores neither probabilities nor independence laws.
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

/-- The positive operator contributed by one literal raw Kraus branch. -/
noncomputable def rawBranchOperator (I : FiniteInstrument κ Ω H K) (index : κ)
    (A : Operator H) : Operator K :=
  (I.kraus.operator index).comp
    (A.comp (LinearMap.adjoint (I.kraus.operator index)))

@[simp] theorem rawBranchOperator_apply (I : FiniteInstrument κ Ω H K) (index : κ)
    (A : Operator H) :
    I.rawBranchOperator index A =
      (I.kraus.operator index).comp
        (A.comp (LinearMap.adjoint (I.kraus.operator index))) :=
  rfl

/-- Literal raw Kraus branches preserve positivity of their input. -/
theorem rawBranchOperator_positive (I : FiniteInstrument κ Ω H K) (index : κ)
    {A : Operator H} (hA : LinearMap.IsPositive A) :
    LinearMap.IsPositive (I.rawBranchOperator index A) := by
  simpa [LinearMap.comp_assoc] using
    hA.adjoint_conj (LinearMap.adjoint (I.kraus.operator index))

/-- The real Born mass of one actual raw Kraus index. -/
noncomputable def rawBornWeight (I : FiniteInstrument κ Ω H K) (index : κ)
    (rho : DensityOperator H) : ℝ :=
  Complex.re (LinearMap.trace Complex K (I.rawBranchOperator index rho.toOperator))

/-- Positivity makes each raw branch trace the corresponding real mass. -/
theorem trace_rawBranchOperator_eq_rawBornWeight
    (I : FiniteInstrument κ Ω H K) (index : κ) (rho : DensityOperator H) :
    LinearMap.trace Complex K (I.rawBranchOperator index rho.toOperator) =
      (I.rawBornWeight index rho : Complex) := by
  have htrace := (I.rawBranchOperator_positive index rho.positive).trace_nonneg
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    exact (Complex.nonneg_iff.mp htrace).2.symm

/-- Raw Born weights are nonnegative because their literal branch operators are positive. -/
theorem rawBornWeight_nonneg (I : FiniteInstrument κ Ω H K) (index : κ)
    (rho : DensityOperator H) :
    0 ≤ I.rawBornWeight index rho :=
  (Complex.nonneg_iff.mp
    (I.rawBranchOperator_positive index rho.positive).trace_nonneg).1

/-- An observed Born weight is exactly the finite regrouping of its raw branches. -/
theorem bornWeight_eq_sum_rawBornWeight (I : FiniteInstrument κ Ω H K)
    (outcome : Ω) (rho : DensityOperator H) :
    I.bornWeight outcome rho =
      ∑ index : κ, if I.observe index = outcome then I.rawBornWeight index rho else 0 := by
  unfold bornWeight branchOperator rawBornWeight rawBranchOperator
  rw [map_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro index _
  by_cases hindex : I.observe index = outcome
  · simp [hindex]
  · simp [hindex]

section Tensor

variable {κ' : Type x} [Fintype κ']
variable {Ω' : Type y} [Fintype Ω']
variable {R S : Type u}
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]

/-- Literal raw Kraus masses factor over a tensor-product density input. -/
theorem rawBornWeight_tensor (I : FiniteInstrument κ Ω H K)
    (J : FiniteInstrument κ' Ω' R S) (rho : DensityOperator H)
    (sigma : DensityOperator R) (leftIndex : κ) (rightIndex : κ') :
    (I.tensor J).rawBornWeight (leftIndex, rightIndex)
        (DensityOperator.tensorDensity rho sigma) =
      I.rawBornWeight leftIndex rho * J.rawBornWeight rightIndex sigma := by
  have hbranch :
      (I.tensor J).rawBranchOperator (leftIndex, rightIndex)
          (DensityOperator.tensorDensity rho sigma).toOperator =
        TensorProduct.map
          (I.rawBranchOperator leftIndex rho.toOperator)
          (J.rawBranchOperator rightIndex sigma.toOperator) := by
    simp only [rawBranchOperator, tensor, DensityOperator.tensorDensity_toOperator]
    rw [TensorProduct.adjoint_map, ← TensorProduct.map_comp, ← TensorProduct.map_comp]
  unfold rawBornWeight
  rw [hbranch, LinearMap.trace_tensorProduct',
    I.trace_rawBranchOperator_eq_rawBornWeight,
    J.trace_rawBranchOperator_eq_rawBornWeight]
  norm_num

/-- An observed tensor-product Born weight factors into the two observed
Born weights by regrouping its literal raw tensor branches. -/
theorem bornWeight_tensor (I : FiniteInstrument κ Ω H K)
    (J : FiniteInstrument κ' Ω' R S) (rho : DensityOperator H)
    (sigma : DensityOperator R) (leftOutcome : Ω) (rightOutcome : Ω') :
    (I.tensor J).bornWeight (leftOutcome, rightOutcome)
        (DensityOperator.tensorDensity rho sigma) =
      I.bornWeight leftOutcome rho * J.bornWeight rightOutcome sigma := by
  rw [bornWeight_eq_sum_rawBornWeight (I.tensor J) (leftOutcome, rightOutcome)
      (DensityOperator.tensorDensity rho sigma),
    bornWeight_eq_sum_rawBornWeight I leftOutcome rho,
    bornWeight_eq_sum_rawBornWeight J rightOutcome sigma,
    Fintype.sum_prod_type]
  calc
    _ = ∑ leftIndex : κ, ∑ rightIndex : κ',
        (if I.observe leftIndex = leftOutcome then I.rawBornWeight leftIndex rho else 0) *
          (if J.observe rightIndex = rightOutcome then J.rawBornWeight rightIndex sigma else 0) := by
      apply Finset.sum_congr rfl
      intro leftIndex _
      apply Finset.sum_congr rfl
      intro rightIndex _
      by_cases hleft : I.observe leftIndex = leftOutcome
      · by_cases hright : J.observe rightIndex = rightOutcome
        · rw [if_pos (by simp [FiniteInstrument.tensor, hleft, hright])]
          rw [rawBornWeight_tensor I J rho sigma leftIndex rightIndex]
          simp [hleft, hright]
        · simp [FiniteInstrument.tensor, hleft, hright]
      · simp [FiniteInstrument.tensor, hleft]
    _ = ∑ leftIndex : κ,
        (if I.observe leftIndex = leftOutcome then I.rawBornWeight leftIndex rho else 0) *
          ∑ rightIndex : κ',
            if J.observe rightIndex = rightOutcome then J.rawBornWeight rightIndex sigma else 0 := by
      apply Finset.sum_congr rfl
      intro leftIndex _
      rw [Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_mul]

end Tensor

/-- A recursively tensorized product input with an explicit ordinary density at depth zero. -/
noncomputable def tensorPowerProductInput (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0)) :
    (attempts : Nat) → DensityOperator (tensorPowerCarrier H attempts)
  | 0 => rhoUnit
  | attempts + 1 => DensityOperator.tensorDensity rho
      (tensorPowerProductInput rho rhoUnit attempts)

/-- The recursively factored raw mass of a literal tensor-power raw history. -/
noncomputable def tensorPowerRawBornProduct (I : FiniteInstrument κ Ω H K)
    (rho : DensityOperator H) :
    (attempts : Nat) → tensorPowerHistory κ attempts → ℝ
  | 0, _ => 1
  | attempts + 1, history =>
      I.rawBornWeight history.1 rho * tensorPowerRawBornProduct I rho attempts history.2

/-- Literal tensor-power raw weights equal their recursively factored products. -/
theorem rawBornWeight_tensorPower (I : FiniteInstrument κ Ω H K)
    (rho : DensityOperator H) (rhoUnit : DensityOperator (tensorPowerCarrier H 0)) :
    ∀ (attempts : Nat) (history : tensorPowerHistory κ attempts),
      (I.tensorPower attempts).rawBornWeight history
          (tensorPowerProductInput rho rhoUnit attempts) =
        tensorPowerRawBornProduct I rho attempts history
  | 0, history => by
      cases history
      have hunit :
          (1 : Operator (tensorPowerCarrier K 0)).comp
              (rhoUnit.toOperator.comp (1 : Operator (tensorPowerCarrier K 0))) =
            rhoUnit.toOperator := by
        ext vector
        simp
      simp [tensorPower, tensorPowerProductInput, tensorPowerRawBornProduct,
        rawBornWeight, rawBranchOperator, tensorUnitInstrument, hunit, rhoUnit.trace_one]
  | attempts + 1, ⟨head, tail⟩ => by
      change
        (I.tensor (I.tensorPower attempts)).rawBornWeight (head, tail)
            (DensityOperator.tensorDensity rho
              (tensorPowerProductInput rho rhoUnit attempts)) =
          I.rawBornWeight head rho * tensorPowerRawBornProduct I rho attempts tail
      rw [rawBornWeight_tensor I (I.tensorPower attempts) rho
        (tensorPowerProductInput rho rhoUnit attempts) head tail,
        rawBornWeight_tensorPower I rho rhoUnit attempts tail]

/-- The recursively factored observed mass of a tensor-power outcome history. -/
noncomputable def tensorPowerBornProduct (I : FiniteInstrument κ Ω H K)
    (rho : DensityOperator H) :
    (attempts : Nat) → tensorPowerHistory Ω attempts → ℝ
  | 0, _ => 1
  | attempts + 1, history =>
      I.bornWeight history.1 rho * tensorPowerBornProduct I rho attempts history.2

/-- Observed tensor-power Born weights factor recursively on the actual
recursively tensorized input. -/
theorem bornWeight_tensorPower (I : FiniteInstrument κ Ω H K)
    (rho : DensityOperator H) (rhoUnit : DensityOperator (tensorPowerCarrier H 0)) :
    ∀ (attempts : Nat) (history : tensorPowerHistory Ω attempts),
      (I.tensorPower attempts).bornWeight history
          (tensorPowerProductInput rho rhoUnit attempts) =
        tensorPowerBornProduct I rho attempts history
  | 0, history => by
      cases history
      change tensorUnitInstrument.bornWeight PUnit.unit rhoUnit = 1
      simpa only [Fintype.sum_unique] using
        (tensorUnitInstrument.sum_bornWeight_eq_one tensorUnitInstrument_complete rhoUnit)
  | attempts + 1, ⟨head, tail⟩ => by
      change
        (I.tensor (I.tensorPower attempts)).bornWeight (head, tail)
            (DensityOperator.tensorDensity rho
              (tensorPowerProductInput rho rhoUnit attempts)) =
          I.bornWeight head rho * tensorPowerBornProduct I rho attempts tail
      rw [bornWeight_tensor I (I.tensorPower attempts) rho
        (tensorPowerProductInput rho rhoUnit attempts) head tail,
        bornWeight_tensorPower I rho rhoUnit attempts tail]

/-- Observable tensor-power history mass is the finite regrouping of literal raw products. -/
theorem tensorPower_bornWeight_eq_sum_rawBornProduct
    (I : FiniteInstrument κ Ω H K) (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0)) (attempts : Nat)
    (outcome : tensorPowerHistory Ω attempts) :
    (I.tensorPower attempts).bornWeight outcome
        (tensorPowerProductInput rho rhoUnit attempts) =
      ∑ rawHistory : tensorPowerHistory κ attempts,
        if (I.tensorPower attempts).observe rawHistory = outcome then
          tensorPowerRawBornProduct I rho attempts rawHistory
        else 0 := by
  rw [bornWeight_eq_sum_rawBornWeight]
  apply Finset.sum_congr rfl
  intro rawHistory _
  by_cases hhistory : (I.tensorPower attempts).observe rawHistory = outcome
  · simp only [if_pos hhistory]
    rw [rawBornWeight_tensorPower]
  · simp [hhistory]

/-- The finite observed-history mass of histories with enough accepted trials. -/
noncomputable def tensorPowerEnoughMass (I : FiniteInstrument κ Ω H K)
    (accepts : Ω → Prop) [DecidablePred accepts] (attempts required : Nat)
    (rho : DensityOperator (tensorPowerCarrier H attempts)) : ℝ :=
  ∑ history ∈ Finset.univ.filter
      (fun history => required ≤ (tensorPowerAcceptedIndices accepts attempts history).card),
    (I.tensorPower attempts).bornWeight history rho

/-- The finite observed-history mass of histories short of the requested acceptance count. -/
noncomputable def tensorPowerShortageMass (I : FiniteInstrument κ Ω H K)
    (accepts : Ω → Prop) [DecidablePred accepts] (attempts required : Nat)
    (rho : DensityOperator (tensorPowerCarrier H attempts)) : ℝ :=
  ∑ history ∈ Finset.univ.filter
      (fun history => (tensorPowerAcceptedIndices accepts attempts history).card < required),
    (I.tensorPower attempts).bornWeight history rho

/-- Enough-history mass is nonnegative because it is a finite observed Born sum. -/
theorem tensorPowerEnoughMass_nonneg (I : FiniteInstrument κ Ω H K)
    (accepts : Ω → Prop) [DecidablePred accepts] (attempts required : Nat)
    (rho : DensityOperator (tensorPowerCarrier H attempts)) :
    0 ≤ I.tensorPowerEnoughMass accepts attempts required rho := by
  unfold tensorPowerEnoughMass
  exact Finset.sum_nonneg fun history _ =>
    (I.tensorPower attempts).bornWeight_nonneg history rho

/-- Shortage-history mass is nonnegative because it is a finite observed Born sum. -/
theorem tensorPowerShortageMass_nonneg (I : FiniteInstrument κ Ω H K)
    (accepts : Ω → Prop) [DecidablePred accepts] (attempts required : Nat)
    (rho : DensityOperator (tensorPowerCarrier H attempts)) :
    0 ≤ I.tensorPowerShortageMass accepts attempts required rho := by
  unfold tensorPowerShortageMass
  exact Finset.sum_nonneg fun history _ =>
    (I.tensorPower attempts).bornWeight_nonneg history rho

/-- Completeness partitions all actual observed histories into enough and shortage mass. -/
theorem tensorPowerEnoughMass_add_tensorPowerShortageMass
    (I : FiniteInstrument κ Ω H K) (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts required : Nat) (rho : DensityOperator (tensorPowerCarrier H attempts))
    (hI : I.kraus.Complete) :
    I.tensorPowerEnoughMass accepts attempts required rho +
        I.tensorPowerShortageMass accepts attempts required rho = 1 := by
  unfold tensorPowerEnoughMass tensorPowerShortageMass
  calc
    _ = ∑ history : tensorPowerHistory Ω attempts,
        (I.tensorPower attempts).bornWeight history rho := by
          simpa only [not_le] using
            Finset.sum_filter_add_sum_filter_not
              (s := (Finset.univ : Finset (tensorPowerHistory Ω attempts)))
              (p := fun history =>
                required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
              (f := fun history => (I.tensorPower attempts).bornWeight history rho)
    _ = 1 := by
          simpa using I.tensorPower_sum_bornWeight_eq_one hI attempts rho

section DependentMass

variable {κ₂ : Ω → Type x} [∀ outcome, Fintype (κ₂ outcome)]
variable {L : Type u}
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

/-- Summing a CPTP dependent second stage over its actual raw fibre preserves each first raw mass. -/
theorem rawBornWeight_bindDependent_sum (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument (κ₂ outcome) PUnit K L)
    (hJ : ∀ outcome, (J outcome).kraus.Complete) (rho : DensityOperator H)
    (firstIndex : κ) :
    ∑ secondIndex : κ₂ (I.observe firstIndex),
      (I.bindDependent J).rawBornWeight ⟨firstIndex, secondIndex⟩ rho =
        I.rawBornWeight firstIndex rho := by
  unfold rawBornWeight
  rw [← Complex.re_sum, ← map_sum]
  have hraw :
      ∑ secondIndex : κ₂ (I.observe firstIndex),
        (I.bindDependent J).rawBranchOperator ⟨firstIndex, secondIndex⟩ rho.toOperator =
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

/-- Aggregating the unit-observed second stage recovers the original first observed Born mass. -/
theorem bindDependent_bornWeight_punit (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument (κ₂ outcome) PUnit K L)
    (hJ : ∀ outcome, (J outcome).kraus.Complete) (outcome : Ω)
    (rho : DensityOperator H) :
    (I.bindDependent J).bornWeight ⟨outcome, PUnit.unit⟩ rho =
      I.bornWeight outcome rho := by
  classical
  have hobserve (firstIndex : κ) (secondIndex : κ₂ (I.observe firstIndex)) :
      (I.bindDependent J).observe ⟨firstIndex, secondIndex⟩ =
          ⟨outcome, PUnit.unit⟩ ↔ I.observe firstIndex = outcome := by
    constructor
    · intro h
      exact congrArg Sigma.fst h
    · intro h
      subst outcome
      rw [bindDependent_observe]
  rw [bornWeight_eq_sum_rawBornWeight, Fintype.sum_sigma]
  calc
    _ = ∑ firstIndex : κ,
        if I.observe firstIndex = outcome then
          ∑ secondIndex : κ₂ (I.observe firstIndex),
            (I.bindDependent J).rawBornWeight ⟨firstIndex, secondIndex⟩ rho
        else 0 := by
          apply Finset.sum_congr rfl
          intro firstIndex _
          by_cases hfirst : I.observe firstIndex = outcome
          · rw [if_pos hfirst]
            apply Finset.sum_congr rfl
            intro secondIndex _
            rw [if_pos ((hobserve firstIndex secondIndex).2 hfirst)]
          · rw [if_neg hfirst]
            apply Finset.sum_eq_zero
            intro secondIndex _
            rw [if_neg fun h => hfirst ((hobserve firstIndex secondIndex).1 h)]
    _ = ∑ firstIndex : κ,
        if I.observe firstIndex = outcome then I.rawBornWeight firstIndex rho else 0 := by
          apply Finset.sum_congr rfl
          intro firstIndex _
          by_cases hfirst : I.observe firstIndex = outcome
          · rw [if_pos hfirst, rawBornWeight_bindDependent_sum I J hJ rho firstIndex, if_pos hfirst]
          · simp [hfirst]
    _ = I.bornWeight outcome rho :=
      (bornWeight_eq_sum_rawBornWeight I outcome rho).symm

end DependentMass

/-- The total selected-or-replacement instrument preserves each actual first observed history mass. -/
theorem tensorPowerHistoryConditionedInstrument_bornWeight_eq_tensorPower_bornWeight
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts required : Nat)
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι)))
    (history : tensorPowerHistory Ω attempts)
    (rho : DensityOperator (tensorPowerCarrier H attempts)) :
    (tensorPowerHistoryConditionedInstrument I accepts attempts required shortageState).bornWeight
        ⟨history, PUnit.unit⟩ rho =
      (I.tensorPower attempts).bornWeight history rho := by
  change
    ((I.tensorPower attempts).bindDependent
      (fun observedHistory => QuantumChannel.toFiniteInstrument
        (tensorPowerHistoryConditionedChannel accepts attempts observedHistory required ι
          shortageState))).bornWeight ⟨history, PUnit.unit⟩ rho =
      (I.tensorPower attempts).bornWeight history rho
  exact bindDependent_bornWeight_punit (I.tensorPower attempts)
    (fun observedHistory => QuantumChannel.toFiniteInstrument
      (tensorPowerHistoryConditionedChannel accepts attempts observedHistory required ι
        shortageState))
    (fun observedHistory => QuantumChannel.toFiniteInstrument_complete
      (tensorPowerHistoryConditionedChannel accepts attempts observedHistory required ι
        shortageState))
    history rho

end FiniteInstrument

end
end Semantics
end QEC
