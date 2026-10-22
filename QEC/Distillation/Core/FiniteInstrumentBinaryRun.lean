import QEC.Distillation.Core.MagicStateProtocol
import QEC.Semantics.Instruments.Core
noncomputable section

namespace QEC
namespace Semantics
namespace FiniteInstrument

open Distillation
open scoped BigOperators

universe u v w

variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
variable [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
variable [FiniteQuantumSystem K]

private theorem densityOperator_ext {rho sigma : DensityOperator K}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho with
  | mk rho hpos htrace =>
      cases sigma with
      | mk sigma hpos' htrace' =>
          dsimp at h
          cases h
          rfl

/-- Coarsen actual finite observations through a computable binary event. -/
def binaryCoarsen (I : FiniteInstrument kappa Omega H K)
    (accepts : Omega -> Bool) :
    FiniteInstrument kappa DistillationOutcome H K where
  kraus := I.kraus
  observe := fun index =>
    if accepts (I.observe index) then .accepted else .rejected

@[simp] theorem binaryCoarsen_kraus
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool) :
    (I.binaryCoarsen accepts).kraus = I.kraus :=
  rfl

theorem binaryCoarsen_complete
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (hI : I.kraus.Complete) :
    (I.binaryCoarsen accepts).kraus.Complete :=
  hI

theorem binaryCoarsen_branchOperator_accepted
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (A : Operator H) :
    (I.binaryCoarsen accepts).branchOperator .accepted A =
      ∑ outcome ∈ Finset.univ.filter (fun outcome => accepts outcome),
        I.branchOperator outcome A := by
  classical
  unfold binaryCoarsen branchOperator
  rw [Finset.sum_comm]
  simp

theorem binaryCoarsen_branchOperator_rejected
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (A : Operator H) :
    (I.binaryCoarsen accepts).branchOperator .rejected A =
      ∑ outcome ∈ Finset.univ.filter (fun outcome => !accepts outcome),
        I.branchOperator outcome A := by
  classical
  unfold binaryCoarsen branchOperator
  rw [Finset.sum_comm]
  simp

theorem binaryCoarsen_bornWeight_accepted
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (rho : DensityOperator H) :
    (I.binaryCoarsen accepts).bornWeight .accepted rho =
      ∑ outcome ∈ Finset.univ.filter (fun outcome => accepts outcome),
        I.bornWeight outcome rho := by
  unfold bornWeight
  rw [binaryCoarsen_branchOperator_accepted]
  simp

theorem binaryCoarsen_bornWeight_rejected
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (rho : DensityOperator H) :
    (I.binaryCoarsen accepts).bornWeight .rejected rho =
      ∑ outcome ∈ Finset.univ.filter (fun outcome => !accepts outcome),
        I.bornWeight outcome rho := by
  unfold bornWeight
  rw [binaryCoarsen_branchOperator_rejected]
  simp

/-- Complete a zero-mass branch only at the total run interface. -/
def binaryCoarsenCompletion
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (rho : DensityOperator H) (fallback : DensityOperator K)
    (outcome : DistillationOutcome) : DensityOperator K :=
  if hpos : 0 < (I.binaryCoarsen accepts).bornWeight outcome rho then
    (I.binaryCoarsen accepts).conditionalDensity outcome rho hpos
  else fallback

/-- Weighting a completed coarsened branch recovers its actual raw branch. -/
theorem binaryCoarsen_bornWeight_smul_completion_toOperator
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (rho : DensityOperator H) (fallback : DensityOperator K)
    (outcome : DistillationOutcome) :
    ((I.binaryCoarsen accepts).bornWeight outcome rho : Complex) •
        (binaryCoarsenCompletion I accepts rho fallback outcome).toOperator =
      (I.binaryCoarsen accepts).branchOperator outcome rho.toOperator := by
  by_cases hpos : 0 < (I.binaryCoarsen accepts).bornWeight outcome rho
  · rw [binaryCoarsenCompletion, dif_pos hpos]
    exact (I.binaryCoarsen accepts).bornWeight_smul_conditionalDensity_toOperator
      outcome rho hpos
  · rw [binaryCoarsenCompletion, dif_neg hpos]
    have hzero : (I.binaryCoarsen accepts).bornWeight outcome rho = 0 :=
      le_antisymm (not_lt.mp hpos)
        ((I.binaryCoarsen accepts).bornWeight_nonneg outcome rho)
    rw [hzero,
      (I.binaryCoarsen accepts).branchOperator_eq_zero_of_bornWeight_eq_zero
        outcome rho hzero]
    simp

theorem binaryCoarsen_accepted_le_one
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (hI : I.kraus.Complete) (rho : DensityOperator H) :
    (I.binaryCoarsen accepts).bornWeight .accepted rho <= 1 := by
  have hsum := (I.binaryCoarsen accepts).sum_bornWeight_eq_one
    (binaryCoarsen_complete I accepts hI) rho
  rw [show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide] at hsum
  have hsum' :
      (I.binaryCoarsen accepts).bornWeight .accepted rho +
        (I.binaryCoarsen accepts).bornWeight .rejected rho = 1 := by
    simpa using hsum
  have hreject :=
    (I.binaryCoarsen accepts).bornWeight_nonneg .rejected rho
  linarith

theorem binaryCoarsen_rejected_eq_one_sub_accepted
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (hI : I.kraus.Complete) (rho : DensityOperator H) :
    (I.binaryCoarsen accepts).bornWeight .rejected rho =
      1 - (I.binaryCoarsen accepts).bornWeight .accepted rho := by
  have hsum := (I.binaryCoarsen accepts).sum_bornWeight_eq_one
    (binaryCoarsen_complete I accepts hI) rho
  rw [show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide] at hsum
  have hsum' :
      (I.binaryCoarsen accepts).bornWeight .accepted rho +
        (I.binaryCoarsen accepts).bornWeight .rejected rho = 1 := by
    simpa using hsum
  linarith

/-- The actual coarsened physical channel decomposes into its completed binary
branches; no success probability or conditional state is supplied by a caller. -/
theorem binaryCoarsen_output_decomposition
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (hI : I.kraus.Complete) (rho : DensityOperator H)
    (fallback : DensityOperator K) :
    ((I.binaryCoarsen accepts).kraus.toQuantumChannel
        (binaryCoarsen_complete I accepts hI)).mapDensity rho =
      outcomeMixture
        ((I.binaryCoarsen accepts).bornWeight .accepted rho)
        ((I.binaryCoarsen accepts).bornWeight_nonneg .accepted rho)
        (binaryCoarsen_accepted_le_one I accepts hI rho)
        (binaryCoarsenCompletion I accepts rho fallback .accepted)
        (binaryCoarsenCompletion I accepts rho fallback .rejected) := by
  apply densityOperator_ext
  rw [← (I.binaryCoarsen accepts).sum_branchOperator_eq_mapDensity_toOperator
    (binaryCoarsen_complete I accepts hI) rho]
  rw [show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide]
  have hreject := binaryCoarsen_rejected_eq_one_sub_accepted
    I accepts hI rho
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [← binaryCoarsen_bornWeight_smul_completion_toOperator
      I accepts rho fallback .accepted,
    ← binaryCoarsen_bornWeight_smul_completion_toOperator
      I accepts rho fallback .rejected]
  change _ =
    ∑ outcome ∈ (Finset.univ : Finset DistillationOutcome),
      (outcomeWeight
        ((I.binaryCoarsen accepts).bornWeight .accepted rho) outcome : Complex) •
        (branchState
          (binaryCoarsenCompletion I accepts rho fallback .accepted)
          (binaryCoarsenCompletion I accepts rho fallback .rejected)
          outcome).toOperator
  rw [show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [outcomeWeight, branchState, ← hreject]

variable {Resource : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]

/-- Turn an actual complete finite instrument and a computable event into a
genuine binary distillation run. -/
def binaryDistillationRun
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (hI : I.kraus.Complete) (resourceCount : Nat)
    (noisyInput : Fin resourceCount -> DensityOperator Resource)
    (prepareInput :
      (Fin resourceCount -> DensityOperator Resource) -> DensityOperator H)
    (fallback : DensityOperator K) :
    DistillationRun Resource H K where
  resourceCount := resourceCount
  noisyInput := noisyInput
  prepareInput := prepareInput
  operation := (I.binaryCoarsen accepts).kraus.toQuantumChannel
    (binaryCoarsen_complete I accepts hI)
  successProbability :=
    (I.binaryCoarsen accepts).bornWeight .accepted (prepareInput noisyInput)
  success_nonneg :=
    (I.binaryCoarsen accepts).bornWeight_nonneg .accepted (prepareInput noisyInput)
  success_le_one :=
    binaryCoarsen_accepted_le_one I accepts hI (prepareInput noisyInput)
  acceptedOutput := binaryCoarsenCompletion I accepts
    (prepareInput noisyInput) fallback .accepted
  rejectedOutput := binaryCoarsenCompletion I accepts
    (prepareInput noisyInput) fallback .rejected
  output_decomposition :=
    binaryCoarsen_output_decomposition I accepts hI (prepareInput noisyInput) fallback

@[simp] theorem binaryDistillationRun_successProbability
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (hI : I.kraus.Complete) (resourceCount : Nat)
    (noisyInput : Fin resourceCount -> DensityOperator Resource)
    (prepareInput :
      (Fin resourceCount -> DensityOperator Resource) -> DensityOperator H)
    (fallback : DensityOperator K) :
    (binaryDistillationRun I accepts hI resourceCount noisyInput prepareInput
      fallback).successProbability =
      (I.binaryCoarsen accepts).bornWeight .accepted
        (prepareInput noisyInput) :=
  rfl

end FiniteInstrument
end Semantics
end QEC
