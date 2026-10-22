import QEC.Semantics.Instruments.Selection.SelectedTrialComplement
/-!
# Selected and unselected trial products

This module factors a product over reconstructed tensor-power histories into
the deterministic selector image and the literal complement trials.  The same
complement label occurs on the left and right, as required by a partial trace.
-/

universe u v

namespace QEC
namespace Semantics

open Classical
open scoped BigOperators

noncomputable section

namespace FiniteInstrument

/-- Summing a trialwise product over one shared complement label factors into
the selected trial entries and independent diagonal sums for the unselected
trials. -/
theorem tensorPower_sum_complement_prod_eq_selected_mul_unselected_sums
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (entry : Fin attempts → Qubit.Bitstring ι → Qubit.Bitstring ι → Complex)
    (left right : Qubit.Bitstring (Fin required × ι)) :
    (∑ complement : Qubit.Bitstring
        (tensorPowerSelectedSubsystem accepts attempts history required hrequired
          ι).ComplementCoordinates,
      ∏ trial : Fin attempts,
        entry trial
          (tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
            ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts history
              required hrequired ι).symm (left, complement)) trial)
          (tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
            ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts history
              required hrequired ι).symm (right, complement)) trial)) =
      (∏ slot : Fin required,
        entry
          (tensorPowerAcceptedSelector accepts attempts history required hrequired
            slot)
          (fun port => left (slot, port))
          (fun port => right (slot, port))) *
      ∏ trial : tensorPowerUnselectedTrial accepts attempts history required
          hrequired,
        ∑ bits : Qubit.Bitstring ι, entry trial.1 bits bits := by
  calc
    (∑ complement : Qubit.Bitstring
        (tensorPowerSelectedSubsystem accepts attempts history required hrequired
          ι).ComplementCoordinates,
      ∏ trial : Fin attempts,
        entry trial
          (tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
            ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts history
              required hrequired ι).symm (left, complement)) trial)
          (tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
            ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts history
              required hrequired ι).symm (right, complement)) trial)) =
        ∑ complement : Qubit.Bitstring
            (tensorPowerSelectedSubsystem accepts attempts history required
              hrequired ι).ComplementCoordinates,
          ((∏ slot : Fin required,
            entry
              (tensorPowerAcceptedSelector accepts attempts history required
                hrequired slot)
              (fun port => left (slot, port))
              (fun port => right (slot, port))) *
          ∏ trial : tensorPowerUnselectedTrial accepts attempts history required
              hrequired,
            entry trial.1
              (tensorPowerSelectedComplementTrialBitstringEquiv accepts attempts
                history required hrequired ι complement trial)
              (tensorPowerSelectedComplementTrialBitstringEquiv accepts attempts
                history required hrequired ι complement trial)) := by
      apply Finset.sum_congr rfl
      intro complement _
      rw [tensorPower_prod_eq_selected_mul_unselected accepts attempts history
        required hrequired]
      congr 1
      · apply Finset.prod_congr rfl
        intro slot _
        rw [tensorPowerSelectedHistoryBitstringEquiv_symm_historyAt_selected
          accepts attempts history required hrequired ι left complement slot]
        rw [tensorPowerSelectedHistoryBitstringEquiv_symm_historyAt_selected
          accepts attempts history required hrequired ι right complement slot]
      · apply Finset.prod_congr rfl
        intro trial _
        rw [tensorPowerSelectedHistoryBitstringEquiv_symm_historyAt_unselected
          accepts attempts history required hrequired ι left complement trial]
        rw [tensorPowerSelectedHistoryBitstringEquiv_symm_historyAt_unselected
          accepts attempts history required hrequired ι right complement trial]
    _ =
        (∏ slot : Fin required,
          entry
            (tensorPowerAcceptedSelector accepts attempts history required
              hrequired slot)
            (fun port => left (slot, port))
            (fun port => right (slot, port))) *
        (∑ complement : Qubit.Bitstring
            (tensorPowerSelectedSubsystem accepts attempts history required
              hrequired ι).ComplementCoordinates,
          ∏ trial : tensorPowerUnselectedTrial accepts attempts history required
              hrequired,
            entry trial.1
              (tensorPowerSelectedComplementTrialBitstringEquiv accepts attempts
                history required hrequired ι complement trial)
              (tensorPowerSelectedComplementTrialBitstringEquiv accepts attempts
                history required hrequired ι complement trial)) := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [tensorPower_sum_complement_prod_unselected accepts attempts history
        required hrequired ι (fun trial bits => entry trial.1 bits bits)]

end FiniteInstrument

end
end Semantics
end QEC
