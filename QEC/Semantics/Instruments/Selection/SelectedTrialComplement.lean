import QEC.Semantics.Instruments.Selection.SelectedSubsystemOperator
/-!
# Trial complement of a selected tensor-power subsystem

The selected coordinate subsystem retains every local coordinate of each
chosen trial.  Its coordinate complement is therefore exactly the product of
the unselected trial subtype with the local coordinate type.  This module
records that equivalence and how the full selected/complement history
equivalence reads both classes of trials.
-/

universe u v

namespace QEC
namespace Semantics

open Classical
open scoped BigOperators

noncomputable section

namespace FiniteInstrument

/-- The finite image of the deterministic accepted-trial selector. -/
noncomputable def tensorPowerSelectedTrials
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card) :
    Finset (Fin attempts) :=
  Finset.univ.map
    (tensorPowerAcceptedSelector accepts attempts history required hrequired).toEmbedding

/-- Membership in the selected-trial image is exactly having a requested
slot mapped to that trial. -/
theorem mem_tensorPowerSelectedTrials_iff
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (trial : Fin attempts) :
    trial ∈ tensorPowerSelectedTrials accepts attempts history required hrequired ↔
      ∃ slot : Fin required,
        tensorPowerAcceptedSelector accepts attempts history required hrequired slot =
          trial := by
  simp [tensorPowerSelectedTrials]

/-- A flattened trial/port coordinate is selected exactly when its trial is
in the deterministic selected-trial image. -/
theorem tensorPowerSelectedSubsystem_coordinate_mem_iff_trial_mem
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (coordinate : Fin attempts × ι) :
    coordinate ∈
        (tensorPowerSelectedSubsystem accepts attempts history required hrequired
          ι).selected ↔
      coordinate.1 ∈
        tensorPowerSelectedTrials accepts attempts history required hrequired := by
  rw [mem_tensorPowerSelectedSubsystem_iff,
    mem_tensorPowerSelectedTrials_iff]
  constructor
  · rintro ⟨⟨slot, port⟩, heq⟩
    exact ⟨slot, congrArg Prod.fst heq⟩
  · rintro ⟨slot, htrial⟩
    refine ⟨(slot, coordinate.2), ?_⟩
    exact Prod.ext htrial rfl

/-- The subtype of actual trials not used by the requested accepted selector. -/
abbrev tensorPowerUnselectedTrial
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card) : Type :=
  {trial : Fin attempts //
    trial ∉ tensorPowerSelectedTrials accepts attempts history required hrequired}

/-- Unselected trial/local-coordinate pairs are exactly the complement
coordinates of the selected tensor-power subsystem. -/
noncomputable def tensorPowerSelectedComplementCoordinateEquiv
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    (tensorPowerUnselectedTrial accepts attempts history required hrequired × ι) ≃
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired
        ι).ComplementCoordinates := by
  apply Equiv.ofBijective
    (fun coordinate =>
      ⟨(coordinate.1.1, coordinate.2), by
        intro hmem
        exact coordinate.1.2
          ((tensorPowerSelectedSubsystem_coordinate_mem_iff_trial_mem accepts
            attempts history required hrequired ι _).mp hmem)⟩)
  constructor
  · rintro ⟨firstTrial, firstPort⟩ ⟨secondTrial, secondPort⟩ heq
    have hpairs : (firstTrial.1, firstPort) = (secondTrial.1, secondPort) :=
      congrArg Subtype.val heq
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hpairs)
    · exact congrArg (fun pair : Fin attempts × ι => pair.2) hpairs
  · intro coordinate
    have hunselected : coordinate.1.1 ∉
        tensorPowerSelectedTrials accepts attempts history required hrequired := by
      intro htrial
      exact coordinate.2
        ((tensorPowerSelectedSubsystem_coordinate_mem_iff_trial_mem accepts
          attempts history required hrequired ι coordinate.1).mpr htrial)
    refine ⟨(⟨coordinate.1.1, hunselected⟩, coordinate.1.2), ?_⟩
    apply Subtype.ext
    rfl

/-- The complement-coordinate equivalence has the underlying flattened
trial/port pair. -/
@[simp] theorem tensorPowerSelectedComplementCoordinateEquiv_apply_val
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (trial : tensorPowerUnselectedTrial accepts attempts history required hrequired)
    (port : ι) :
    ((tensorPowerSelectedComplementCoordinateEquiv accepts attempts history required
      hrequired ι (trial, port) :
        (tensorPowerSelectedSubsystem accepts attempts history required hrequired
          ι).ComplementCoordinates) : Fin attempts × ι) =
      (trial.1, port) :=
  rfl

/-- A complement bitstring is exactly one local bitstring for every
unselected trial. -/
noncomputable def tensorPowerSelectedComplementTrialBitstringEquiv
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Qubit.Bitstring
        (tensorPowerSelectedSubsystem accepts attempts history required hrequired
          ι).ComplementCoordinates ≃
      (tensorPowerUnselectedTrial accepts attempts history required hrequired →
        Qubit.Bitstring ι) where
  toFun := fun bits trial port =>
    bits (tensorPowerSelectedComplementCoordinateEquiv accepts attempts history
      required hrequired ι (trial, port))
  invFun := fun bits coordinate =>
    bits ((tensorPowerSelectedComplementCoordinateEquiv accepts attempts history
      required hrequired ι).symm coordinate).1
      ((tensorPowerSelectedComplementCoordinateEquiv accepts attempts history
        required hrequired ι).symm coordinate).2
  left_inv := by
    intro bits
    funext coordinate
    simp
  right_inv := by
    intro bits
    funext trial port
    simp

/-- The requested selected slots together with the unselected-trial subtype
partition every actual trial exactly once. -/
noncomputable def tensorPowerSelectedAndUnselectedTrialEquiv
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card) :
    (Fin required ⊕
      tensorPowerUnselectedTrial accepts attempts history required hrequired) ≃
        Fin attempts := by
  apply Equiv.ofBijective
    (Sum.elim
      (tensorPowerAcceptedSelector accepts attempts history required hrequired)
      Subtype.val)
  constructor
  · intro first second heq
    cases first with
    | inl firstSlot =>
        cases second with
        | inl secondSlot =>
            exact congrArg Sum.inl
              ((tensorPowerAcceptedSelector accepts attempts history required
                hrequired).injective heq)
        | inr secondTrial =>
            exact (secondTrial.2
              ((mem_tensorPowerSelectedTrials_iff accepts attempts history required
                hrequired secondTrial.1).mpr ⟨firstSlot, heq⟩)).elim
    | inr firstTrial =>
        cases second with
        | inl secondSlot =>
            exact (firstTrial.2
              ((mem_tensorPowerSelectedTrials_iff accepts attempts history required
                hrequired firstTrial.1).mpr ⟨secondSlot, heq.symm⟩)).elim
        | inr secondTrial =>
            exact congrArg Sum.inr (Subtype.ext heq)
  · intro trial
    by_cases htrial : trial ∈
        tensorPowerSelectedTrials accepts attempts history required hrequired
    · rcases (mem_tensorPowerSelectedTrials_iff accepts attempts history required
        hrequired trial).mp htrial with ⟨slot, hslot⟩
      exact ⟨Sum.inl slot, hslot⟩
    · exact ⟨Sum.inr ⟨trial, htrial⟩, rfl⟩

/-- Every finite product over actual trials splits into its selector-image
product and its unselected-trial product. -/
theorem tensorPower_prod_eq_selected_mul_unselected
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (f : Fin attempts → Complex) :
    (∏ trial : Fin attempts, f trial) =
      (∏ slot : Fin required,
        f (tensorPowerAcceptedSelector accepts attempts history required hrequired
          slot)) *
      ∏ trial : tensorPowerUnselectedTrial accepts attempts history required
          hrequired,
        f trial.1 := by
  let splitEquiv := tensorPowerSelectedAndUnselectedTrialEquiv accepts attempts
    history required hrequired
  calc
    (∏ trial : Fin attempts, f trial) =
        ∏ index : Fin required ⊕
            tensorPowerUnselectedTrial accepts attempts history required hrequired,
          f (splitEquiv index) := by
      exact (Fintype.prod_equiv splitEquiv
        (fun index => f (splitEquiv index)) f (fun _ => rfl)).symm
    _ = _ := by
      rw [Fintype.prod_sum_type]
      rfl

/-- Summing a product of trial-local diagonal factors over the literal
complement bitstrings equals the product of the corresponding local sums. -/
theorem tensorPower_sum_complement_prod_unselected
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (g : tensorPowerUnselectedTrial accepts attempts history required hrequired →
      Qubit.Bitstring ι → Complex) :
    (∑ complement : Qubit.Bitstring
        (tensorPowerSelectedSubsystem accepts attempts history required hrequired
          ι).ComplementCoordinates,
      ∏ trial : tensorPowerUnselectedTrial accepts attempts history required
          hrequired,
        g trial
          (tensorPowerSelectedComplementTrialBitstringEquiv accepts attempts history
            required hrequired ι complement trial)) =
      ∏ trial : tensorPowerUnselectedTrial accepts attempts history required
          hrequired,
        ∑ bits : Qubit.Bitstring ι, g trial bits := by
  let complementEquiv :=
    tensorPowerSelectedComplementTrialBitstringEquiv accepts attempts history
      required hrequired ι
  calc
    (∑ complement : Qubit.Bitstring
        (tensorPowerSelectedSubsystem accepts attempts history required hrequired
          ι).ComplementCoordinates,
      ∏ trial : tensorPowerUnselectedTrial accepts attempts history required
          hrequired,
        g trial (complementEquiv complement trial)) =
        ∑ assignment :
            (tensorPowerUnselectedTrial accepts attempts history required hrequired →
              Qubit.Bitstring ι),
          ∏ trial : tensorPowerUnselectedTrial accepts attempts history required
              hrequired,
            g trial (assignment trial) := by
      apply Fintype.sum_equiv complementEquiv
      intro complement
      rfl
    _ = _ := by
      simpa using (Fintype.prod_sum g).symm

/-- Reconstructing a full history from selected/complement labels reads the
selected label on every actual selector image trial. -/
theorem tensorPowerSelectedHistoryBitstringEquiv_symm_at_selected
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (selected : Qubit.Bitstring (Fin required × ι))
    (complement : Qubit.Bitstring
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired
        ι).ComplementCoordinates)
    (slot : Fin required) (port : ι) :
    tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
        ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts history required
          hrequired ι).symm (selected, complement))
        (tensorPowerAcceptedSelector accepts attempts history required hrequired slot)
        port =
      selected (slot, port) := by
  have hselected := congrFun
    (tensorPowerSelectedOutputBitstring_equiv_symm accepts attempts history required
      hrequired ι selected complement) (slot, port)
  simp only [tensorPowerSelectedOutputBitstring,
    tensorPowerSelectedBitstringEquiv, FiniteSubsystem.splitBitstring,
    tensorPowerSelectedCoordinateEmbedding] at hselected
  exact hselected

/-- Reconstructing a full history from selected/complement labels reads the
corresponding local complement bitstring on every unselected trial. -/
theorem tensorPowerSelectedHistoryBitstringEquiv_symm_at_unselected
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (selected : Qubit.Bitstring (Fin required × ι))
    (complement : Qubit.Bitstring
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired
        ι).ComplementCoordinates)
    (trial : tensorPowerUnselectedTrial accepts attempts history required hrequired)
    (port : ι) :
    tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
        ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts history required
          hrequired ι).symm (selected, complement)) trial.1 port =
      tensorPowerSelectedComplementTrialBitstringEquiv accepts attempts history
        required hrequired ι complement trial port := by
  have hcomplement := congrFun
    (tensorPowerSelectedComplementBitstring_equiv_symm accepts attempts history
      required hrequired ι selected complement)
    (tensorPowerSelectedComplementCoordinateEquiv accepts attempts history required
      hrequired ι (trial, port))
  simpa [tensorPowerSelectedComplementBitstring,
    tensorPowerSelectedComplementTrialBitstringEquiv,
    FiniteSubsystem.splitBitstring] using hcomplement

/-- Reconstructing a full history from selected/complement labels reads the
whole selected local bitstring on an actual selector-image trial. -/
theorem tensorPowerSelectedHistoryBitstringEquiv_symm_historyAt_selected
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (selected : Qubit.Bitstring (Fin required × ι))
    (complement : Qubit.Bitstring
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired
        ι).ComplementCoordinates)
    (slot : Fin required) :
    tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
        ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts history required
          hrequired ι).symm (selected, complement))
        (tensorPowerAcceptedSelector accepts attempts history required hrequired slot) =
      fun port => selected (slot, port) := by
  funext port
  exact tensorPowerSelectedHistoryBitstringEquiv_symm_at_selected accepts attempts
    history required hrequired ι selected complement slot port

/-- Reconstructing a full history from selected/complement labels reads the
whole corresponding local complement bitstring on every unselected trial. -/
theorem tensorPowerSelectedHistoryBitstringEquiv_symm_historyAt_unselected
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (selected : Qubit.Bitstring (Fin required × ι))
    (complement : Qubit.Bitstring
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired
        ι).ComplementCoordinates)
    (trial : tensorPowerUnselectedTrial accepts attempts history required hrequired) :
    tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
        ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts history required
          hrequired ι).symm (selected, complement)) trial.1 =
      tensorPowerSelectedComplementTrialBitstringEquiv accepts attempts history
        required hrequired ι complement trial := by
  funext port
  exact tensorPowerSelectedHistoryBitstringEquiv_symm_at_unselected accepts attempts
    history required hrequired ι selected complement trial port

end FiniteInstrument

end
end Semantics
end QEC
