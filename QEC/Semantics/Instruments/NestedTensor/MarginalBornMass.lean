import QEC.Semantics.Instruments.NestedTensor.Power
import QEC.Semantics.Instruments.Tensor.MarginalBornMass
/-!
# Marginal Born masses of nested tensor-power instruments

This module recursively sums every sibling history outside one selected leaf
of a nested tensor power.  The remaining Born mass is exactly the base
instrument evaluated on that leaf's true input marginal.  Consequently a
failure on any nested leaf is bounded by the sum of its true marginal failure
masses.  No product input or independence premise is used.
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

/-- The true base-system marginal selected by one leaf path of an arbitrary
density on a recursively nested tensor carrier. -/
noncomputable def nestedTensorInputMarginal
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] :
    (branches depth : Nat) -> DensityOperator (nestedTensorCarrier H branches depth) ->
      nestedTensorPath branches depth -> DensityOperator H
  | _, 0, rho, _ => rho
  | branches, depth + 1, rho, path =>
      tensorPowerInputMarginal branches
        (nestedTensorInputMarginal (tensorPowerCarrier H branches)
          branches depth rho path.1)
        path.2

/-- Summing every nested history off one selected path gives exactly the
base-instrument failure mass on that path's true marginal. -/
theorem nestedTensorPower_bornWeight_path_failure_sum_eq
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (fails : Omega -> Prop) [DecidablePred fails] (branches : Nat) :
    ∀ (depth : Nat)
      (rho : DensityOperator (nestedTensorCarrier H branches depth))
      (path : nestedTensorPath branches depth),
      (∑ history ∈ Finset.univ.filter
          (fun history : nestedTensorHistory Omega branches depth =>
            fails (nestedTensorHistoryAt Omega branches depth history path)),
        (nestedTensorPower I branches depth).bornWeight history rho) =
        ∑ outcome ∈ Finset.univ.filter fails,
          I.bornWeight outcome
            (nestedTensorInputMarginal H branches depth rho path) := by
  intro depth
  induction depth generalizing kappa Omega H K with
  | zero =>
      intro rho path
      have hpath : path = PUnit.unit := PUnit.ext _ _
      subst path
      rfl
  | succ depth ih =>
      intro rho path
      rcases path with ⟨pathPrefix, trial⟩
      change
        (∑ history ∈ Finset.univ.filter
            (fun history : nestedTensorHistory
                (tensorPowerHistory Omega branches) branches depth =>
              fails
                (tensorPowerHistoryAt Omega branches
                  (nestedTensorHistoryAt (tensorPowerHistory Omega branches)
                    branches depth history pathPrefix) trial)),
          (nestedTensorPower (I.tensorPower branches) branches depth).bornWeight
            history rho) =
          ∑ outcome ∈ Finset.univ.filter fails,
            I.bornWeight outcome
              (tensorPowerInputMarginal branches
                (nestedTensorInputMarginal
                  (tensorPowerCarrier H branches)
                  branches depth rho pathPrefix) trial)
      rw [ih
        (I := I.tensorPower branches)
        (hI := I.tensorPower_complete hI branches)
        (fails := fun layer =>
          fails (tensorPowerHistoryAt Omega branches layer trial))
        (rho := rho) (path := pathPrefix)]
      exact tensorPower_bornWeight_coordinate_failure_sum_eq
        I hI fails branches
          (nestedTensorInputMarginal (tensorPowerCarrier H branches)
            branches depth rho pathPrefix) trial

/-- A finite weighted union bound over all actual leaves of a nested tensor
power.  Each leaf is charged to its true marginal failure mass, so the nested
input may be arbitrarily correlated. -/
theorem nestedTensorPower_bornWeight_any_path_failure_le
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (fails : Omega -> Prop) [DecidablePred fails]
    (branches depth : Nat)
    (rho : DensityOperator (nestedTensorCarrier H branches depth)) :
    (∑ history ∈ Finset.univ.filter
        (fun history : nestedTensorHistory Omega branches depth =>
          ∃ path : nestedTensorPath branches depth,
            fails (nestedTensorHistoryAt Omega branches depth history path)),
      (nestedTensorPower I branches depth).bornWeight history rho) ≤
      ∑ path : nestedTensorPath branches depth,
        ∑ outcome ∈ Finset.univ.filter fails,
          I.bornWeight outcome
            (nestedTensorInputMarginal H branches depth rho path) := by
  classical
  rw [Finset.sum_filter]
  calc
    (∑ history : nestedTensorHistory Omega branches depth,
        if (∃ path : nestedTensorPath branches depth,
              fails (nestedTensorHistoryAt Omega branches depth history path)) then
          (nestedTensorPower I branches depth).bornWeight history rho
        else 0) ≤
        ∑ history : nestedTensorHistory Omega branches depth,
          ∑ path : nestedTensorPath branches depth,
            if fails (nestedTensorHistoryAt Omega branches depth history path) then
              (nestedTensorPower I branches depth).bornWeight history rho
            else 0 := by
      apply Finset.sum_le_sum
      intro history _
      by_cases hfailure :
          ∃ path : nestedTensorPath branches depth,
            fails (nestedTensorHistoryAt Omega branches depth history path)
      · rw [if_pos hfailure]
        obtain ⟨path, hpath⟩ := hfailure
        simpa [hpath] using
          (Finset.single_le_sum
            (s := (Finset.univ : Finset (nestedTensorPath branches depth)))
            (f := fun other : nestedTensorPath branches depth =>
              if fails (nestedTensorHistoryAt Omega branches depth history other) then
                (nestedTensorPower I branches depth).bornWeight history rho
              else 0)
            (fun other _ => by
              by_cases hother :
                  fails (nestedTensorHistoryAt Omega branches depth history other)
              · simpa [hother] using
                  (nestedTensorPower I branches depth).bornWeight_nonneg history rho
              · simp [hother])
            (Finset.mem_univ path))
      · rw [if_neg hfailure]
        exact Finset.sum_nonneg fun path _ => by
          by_cases hpath :
              fails (nestedTensorHistoryAt Omega branches depth history path)
          · simpa [hpath] using
              (nestedTensorPower I branches depth).bornWeight_nonneg history rho
          · simp [hpath]
    _ = ∑ path : nestedTensorPath branches depth,
        ∑ history : nestedTensorHistory Omega branches depth,
          if fails (nestedTensorHistoryAt Omega branches depth history path) then
            (nestedTensorPower I branches depth).bornWeight history rho
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ path : nestedTensorPath branches depth,
        ∑ outcome ∈ Finset.univ.filter fails,
          I.bornWeight outcome
            (nestedTensorInputMarginal H branches depth rho path) := by
      apply Finset.sum_congr rfl
      intro path _
      rw [← Finset.sum_filter]
      exact nestedTensorPower_bornWeight_path_failure_sum_eq
        I hI fails branches depth rho path

end FiniteInstrument

end
end Semantics
end QEC
