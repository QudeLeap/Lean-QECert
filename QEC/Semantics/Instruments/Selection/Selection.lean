import QEC.Semantics.Instruments.Sequential.Composition
/-!
# Finite selection from tensor-power instrument histories

This module gives a canonical finite-trial view of the observed outcomes of a
homogeneous tensor power. It only selects finite indices satisfying a supplied
predicate; it neither constructs a discard channel nor assigns probabilities
or costs.
-/

universe u v w

namespace QEC
namespace Semantics

noncomputable section

namespace FiniteInstrument

/-- Read one trial from the canonical right-nested tensor-power history. -/
def tensorPowerHistoryAt (α : Type v) : (attempts : Nat) →
    tensorPowerHistory α attempts → Fin attempts → α
  | 0, _, trial => Fin.elim0 trial
  | attempts + 1, history, trial =>
      Fin.cases history.1
        (fun tailTrial => tensorPowerHistoryAt α attempts history.2 tailTrial) trial

/-- Rebuild the canonical right-nested tensor-power history from indexed trials. -/
def tensorPowerHistoryOf (α : Type v) : (attempts : Nat) →
    (Fin attempts → α) → tensorPowerHistory α attempts
  | 0, _ => PUnit.unit
  | attempts + 1, trials =>
      (trials 0, tensorPowerHistoryOf α attempts fun trial => trials trial.succ)

theorem tensorPowerHistoryAt_of (α : Type v) :
    ∀ (attempts : Nat) (trials : Fin attempts → α),
      tensorPowerHistoryAt α attempts (tensorPowerHistoryOf α attempts trials) = trials
  | 0, _ => by
      funext trial
      exact Fin.elim0 trial
  | attempts + 1, trials => by
      funext trial
      refine Fin.cases ?_ ?_ trial
      · simp [tensorPowerHistoryAt, tensorPowerHistoryOf]
      · intro tailTrial
        simpa [tensorPowerHistoryAt, tensorPowerHistoryOf] using
          congrFun (tensorPowerHistoryAt_of α attempts fun trial => trials trial.succ) tailTrial

theorem tensorPowerHistoryOf_at (α : Type v) :
    ∀ (attempts : Nat) (history : tensorPowerHistory α attempts),
      tensorPowerHistoryOf α attempts (tensorPowerHistoryAt α attempts history) = history
  | 0, history => by
      change PUnit.unit = history
      exact PUnit.ext _ _
  | attempts + 1, history => by
      rcases history with ⟨head, tail⟩
      change
        (head,
          tensorPowerHistoryOf α attempts (tensorPowerHistoryAt α attempts tail)) =
            (head, tail)
      rw [tensorPowerHistoryOf_at α attempts tail]

/-- Canonically identify a tensor-power history with its finite trial function. -/
def tensorPowerHistoryEquiv (α : Type v) (attempts : Nat) :
    tensorPowerHistory α attempts ≃ (Fin attempts → α) where
  toFun := tensorPowerHistoryAt α attempts
  invFun := tensorPowerHistoryOf α attempts
  left_inv := tensorPowerHistoryOf_at α attempts
  right_inv := tensorPowerHistoryAt_of α attempts

/-- The actual observed outcome at one finite trial of a tensor-power instrument. -/
def tensorPowerObservedHistoryAt
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (I : FiniteInstrument κ Ω H K) (attempts : Nat)
    (rawHistory : tensorPowerHistory κ attempts) (trial : Fin attempts) : Ω :=
  tensorPowerHistoryAt Ω attempts ((I.tensorPower attempts).observe rawHistory) trial

/-- The finite trial indices whose observed history values satisfy `accepts`. -/
def tensorPowerAcceptedIndices {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts) : Finset (Fin attempts) :=
  Finset.univ.filter fun trial => accepts (tensorPowerHistoryAt α attempts history trial)

@[simp]
theorem mem_tensorPowerAcceptedIndices {α : Type v} (accepts : α → Prop)
    [DecidablePred accepts] (attempts : Nat) (history : tensorPowerHistory α attempts)
    (trial : Fin attempts) :
    trial ∈ tensorPowerAcceptedIndices accepts attempts history ↔
      accepts (tensorPowerHistoryAt α attempts history trial) := by
  simp [tensorPowerAcceptedIndices]

/-- Accepted finite trial indices for the actual observed tensor-power history. -/
def tensorPowerObservedAcceptedIndices
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (I : FiniteInstrument κ Ω H K) (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts : Nat) (rawHistory : tensorPowerHistory κ attempts) : Finset (Fin attempts) :=
  tensorPowerAcceptedIndices accepts attempts ((I.tensorPower attempts).observe rawHistory)

@[simp]
theorem mem_tensorPowerObservedAcceptedIndices
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (I : FiniteInstrument κ Ω H K) (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts : Nat) (rawHistory : tensorPowerHistory κ attempts) (trial : Fin attempts) :
    trial ∈ tensorPowerObservedAcceptedIndices I accepts attempts rawHistory ↔
      accepts (tensorPowerObservedHistoryAt I attempts rawHistory trial) := by
  simp [tensorPowerObservedAcceptedIndices, tensorPowerObservedHistoryAt]

/-- The deterministic increasing selection of a requested number of accepted trials. -/
noncomputable def tensorPowerAcceptedSelector {α : Type v} (accepts : α → Prop)
    [DecidablePred accepts] (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat) (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card) :
    Fin required ↪o Fin attempts :=
  (tensorPowerAcceptedIndices accepts attempts history).orderEmbOfCardLe hrequired

theorem tensorPowerAcceptedSelector_mem {α : Type v} (accepts : α → Prop)
    [DecidablePred accepts] (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat) (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (slot : Fin required) :
    tensorPowerAcceptedSelector accepts attempts history required hrequired slot ∈
      tensorPowerAcceptedIndices accepts attempts history :=
  Finset.orderEmbOfCardLe_mem _ _ _

theorem tensorPowerAcceptedSelector_satisfies {α : Type v} (accepts : α → Prop)
    [DecidablePred accepts] (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat) (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (slot : Fin required) :
    accepts
      (tensorPowerHistoryAt α attempts history
        (tensorPowerAcceptedSelector accepts attempts history required hrequired slot)) :=
  (mem_tensorPowerAcceptedIndices accepts attempts history _).mp
    (tensorPowerAcceptedSelector_mem accepts attempts history required hrequired slot)

theorem tensorPowerAcceptedSelector_injective {α : Type v} (accepts : α → Prop)
    [DecidablePred accepts] (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat) (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card) :
    Function.Injective (tensorPowerAcceptedSelector accepts attempts history required hrequired) :=
  (tensorPowerAcceptedSelector accepts attempts history required hrequired).injective

theorem tensorPowerAcceptedSelector_ne_of_ne {α : Type v} (accepts : α → Prop)
    [DecidablePred accepts] (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat) (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    {first second : Fin required} (hne : first ≠ second) :
    tensorPowerAcceptedSelector accepts attempts history required hrequired first ≠
      tensorPowerAcceptedSelector accepts attempts history required hrequired second :=
  (tensorPowerAcceptedSelector_injective accepts attempts history required hrequired).ne hne

/--
The deterministic selector, made total only by returning `none` when the
finite accepted set is too small.
-/
noncomputable def tensorPowerAcceptedSelectorOption {α : Type v} (accepts : α → Prop)
    [DecidablePred accepts] (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat) : Option (Fin required ↪o Fin attempts) :=
  if hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card then
    some (tensorPowerAcceptedSelector accepts attempts history required hrequired)
  else
    none

theorem tensorPowerAcceptedSelectorOption_eq_none_iff {α : Type v} (accepts : α → Prop)
    [DecidablePred accepts] (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat) :
    tensorPowerAcceptedSelectorOption accepts attempts history required = none ↔
      (tensorPowerAcceptedIndices accepts attempts history).card < required := by
  by_cases hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card
  · have hnot : ¬ (tensorPowerAcceptedIndices accepts attempts history).card < required :=
      Nat.not_lt_of_ge hrequired
    simp [tensorPowerAcceptedSelectorOption, hrequired, hnot]
  · have hshort : (tensorPowerAcceptedIndices accepts attempts history).card < required :=
      Nat.lt_of_not_ge hrequired
    simp [tensorPowerAcceptedSelectorOption, hrequired, hshort]

/--
The finite shortage condition is exactly the absence of any injective full
selection whose trial indices are all accepted.
-/
theorem tensorPowerAccepted_shortage_iff_no_full_selection {α : Type v}
    (accepts : α → Prop) [DecidablePred accepts] (attempts : Nat)
    (history : tensorPowerHistory α attempts) (required : Nat) :
    (tensorPowerAcceptedIndices accepts attempts history).card < required ↔
      ¬ ∃ selection : Fin required → Fin attempts,
        Function.Injective selection ∧
          ∀ slot, selection slot ∈ tensorPowerAcceptedIndices accepts attempts history := by
  constructor
  · intro hshort hselection
    rcases hselection with ⟨selection, hInjective, hAccepted⟩
    let selected : Fin required → {trial // trial ∈ tensorPowerAcceptedIndices accepts attempts history} :=
      fun slot => ⟨selection slot, hAccepted slot⟩
    have hSelectedInjective : Function.Injective selected := by
      intro first second heq
      apply hInjective
      exact Subtype.ext_iff.mp heq
    have hcard : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card := by
      simpa only [Fintype.card_fin, Fintype.card_coe] using
        Fintype.card_le_of_injective selected hSelectedInjective
    exact (Nat.not_le_of_lt hshort) hcard
  · intro hnone
    by_contra hnot
    have hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card :=
      Nat.le_of_not_lt hnot
    apply hnone
    refine ⟨tensorPowerAcceptedSelector accepts attempts history required hrequired, ?_, ?_⟩
    · exact tensorPowerAcceptedSelector_injective accepts attempts history required hrequired
    · intro slot
      exact tensorPowerAcceptedSelector_mem accepts attempts history required hrequired slot

end FiniteInstrument

end
end Semantics
end QEC
