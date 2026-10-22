import QEC.Distillation.LowOverheadProtocol.Parameterized.Syndrome

/-!
# Parameterized HH18 coarse syndrome postselection

This layer observes the actual finite joint stabilizer instrument of an
admissible HH18 punctured Reed--Muller block only as accepted versus rejected:
the all-positive syndrome is accepted and every other syndrome is rejected.
It preserves the literal raw branches, derives their Born-weight laws from
Kraus completeness, and normalizes only behind a positive Born-weight
witness.  It deliberately stops before decoding, error recurrence, or a
success lower bound.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

universe u

/-- Coarse-grain a visible HH18 syndrome: only the all-positive syndrome is
accepted. -/
def syndromeOutcome (w r m : Nat) (syndrome : Syndrome w r m) :
    DistillationOutcome :=
  if syndrome = HH18PuncturedReedMuller.allPositiveSyndrome w r m then
    .accepted
  else
    .rejected

/-- The coarse accepted outcome is exactly the all-positive syndrome. -/
theorem syndromeOutcome_accepted_iff (w r m : Nat) (syndrome : Syndrome w r m) :
    syndromeOutcome w r m syndrome = .accepted ↔
      syndrome = HH18PuncturedReedMuller.allPositiveSyndrome w r m := by
  simp [syndromeOutcome]

/-- The coarse rejected outcome is exactly every non-all-positive syndrome. -/
theorem syndromeOutcome_rejected_iff (w r m : Nat) (syndrome : Syndrome w r m) :
    syndromeOutcome w r m syndrome = .rejected ↔
      syndrome ≠ HH18PuncturedReedMuller.allPositiveSyndrome w r m := by
  simp [syndromeOutcome]

/-- The actual complete joint HH18 measurement, observed only through its
accepted/rejected distinction. -/
noncomputable def postselectionInstrument {w r m : Nat} (h : Admissible w r m) :
    FiniteInstrument (Syndrome w r m) DistillationOutcome
      (PhysicalRegister m w) (PhysicalRegister m w) where
  kraus := (fullSyndromeInstrument h).kraus
  observe := syndromeOutcome w r m

/-- Coarse-graining retains completeness of the real finite joint-projector
Kraus family. -/
theorem postselectionInstrument_complete {w r m : Nat} (h : Admissible w r m) :
    (postselectionInstrument h).kraus.Complete :=
  fullSyndromeInstrument_complete h

/-- The literal unnormalized physical branch retained by one coarse outcome. -/
noncomputable def rawPostselectionBranch {w r m : Nat} (h : Admissible w r m)
    (outcome : DistillationOutcome) (input : Operator (PhysicalRegister m w)) :
    Operator (PhysicalRegister m w) :=
  (postselectionInstrument h).branchOperator outcome input

/-- The raw coarse endpoint on a normalized physical density input. -/
noncomputable def rawPostselectionEndpoint {w r m : Nat} (h : Admissible w r m)
    (outcome : DistillationOutcome) (rho : DensityOperator (PhysicalRegister m w)) :
    Operator (PhysicalRegister m w) :=
  rawPostselectionBranch h outcome rho.toOperator

/-- The actual Born weight of one parameterized coarse outcome. -/
noncomputable def postselectionWeight {w r m : Nat} (h : Admissible w r m)
    (outcome : DistillationOutcome) (rho : DensityOperator (PhysicalRegister m w)) :
    Real :=
  (postselectionInstrument h).bornWeight outcome rho

/-- Every coarse Born weight is nonnegative because it is derived from a
positive physical Kraus branch. -/
theorem postselectionWeight_nonneg {w r m : Nat} (h : Admissible w r m)
    (outcome : DistillationOutcome) (rho : DensityOperator (PhysicalRegister m w)) :
    0 ≤ postselectionWeight h outcome rho :=
  (postselectionInstrument h).bornWeight_nonneg outcome rho

/-- Accepted and rejected Born weights exhaust the actual complete joint
measurement. -/
theorem postselectionWeight_sum {w r m : Nat} (h : Admissible w r m)
    (rho : DensityOperator (PhysicalRegister m w)) :
    postselectionWeight h .accepted rho + postselectionWeight h .rejected rho = 1 := by
  have hsum := (postselectionInstrument h).sum_bornWeight_eq_one
    (postselectionInstrument_complete h) rho
  rw [show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide] at hsum
  simpa [postselectionWeight] using hsum

/-- A zero actual Born weight leaves the literal raw endpoint at zero. -/
theorem rawPostselectionEndpoint_eq_zero_of_weight_eq_zero {w r m : Nat}
    (h : Admissible w r m) (outcome : DistillationOutcome)
    (rho : DensityOperator (PhysicalRegister m w))
    (hzero : postselectionWeight h outcome rho = 0) :
    rawPostselectionEndpoint h outcome rho = 0 := by
  simpa [rawPostselectionEndpoint, rawPostselectionBranch, postselectionWeight] using
    ((postselectionInstrument h).branchOperator_eq_zero_of_bornWeight_eq_zero
      outcome rho hzero)

/-- Normalize a coarse endpoint only under its actual strictly positive Born
weight witness. -/
noncomputable def postselectionConditional {w r m : Nat} (h : Admissible w r m)
    (rho : DensityOperator (PhysicalRegister m w)) (outcome : DistillationOutcome)
    (hpositive : 0 < postselectionWeight h outcome rho) :
    DensityOperator (PhysicalRegister m w) :=
  (postselectionInstrument h).conditionalDensity outcome rho hpositive

/-- The positive conditional endpoint is inverse-Born-weight scaling of the
literal raw endpoint. -/
@[simp] theorem postselectionConditional_toOperator {w r m : Nat}
    (h : Admissible w r m) (rho : DensityOperator (PhysicalRegister m w))
    (outcome : DistillationOutcome)
    (hpositive : 0 < postselectionWeight h outcome rho) :
    (postselectionConditional h rho outcome hpositive).toOperator =
      ((postselectionWeight h outcome rho : Complex)⁻¹) •
        rawPostselectionEndpoint h outcome rho :=
  rfl

/-- Reweighting a positive conditional endpoint recovers the literal raw
physical branch. -/
theorem postselectionWeight_smul_conditional_toOperator {w r m : Nat}
    (h : Admissible w r m) (rho : DensityOperator (PhysicalRegister m w))
    (outcome : DistillationOutcome)
    (hpositive : 0 < postselectionWeight h outcome rho) :
    (postselectionWeight h outcome rho : Complex) •
        (postselectionConditional h rho outcome hpositive).toOperator =
      rawPostselectionEndpoint h outcome rho := by
  simpa [postselectionWeight, postselectionConditional,
    rawPostselectionEndpoint, rawPostselectionBranch] using
      ((postselectionInstrument h).bornWeight_smul_conditionalDensity_toOperator
        outcome rho hpositive)

/-- The unnormalized all-positive endpoint of one injected physical-error
branch. -/
noncomputable def rawAcceptedEndpoint {w r m : Nat} (h : Admissible w r m)
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w) :
    Operator (PhysicalRegister m w) :=
  rawSyndromeBranch h error outcomes
    (HH18PuncturedReedMuller.allPositiveSyndrome w r m)

/-- The unnormalized sum of every non-all-positive endpoint. -/
noncomputable def rawRejectedEndpoint {w r m : Nat} (h : Admissible w r m)
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w) :
    Operator (PhysicalRegister m w) :=
  ∑ syndrome : Syndrome w r m,
    if syndrome = HH18PuncturedReedMuller.allPositiveSyndrome w r m then
      0
    else
      rawSyndromeBranch h error outcomes syndrome

/-- Coarse acceptance retains exactly the all-positive raw syndrome endpoint. -/
theorem rawPostselectionBranch_accepted_eq_rawAcceptedEndpoint {w r m : Nat}
    (h : Admissible w r m) (error : PhysicalErrorWord m w)
    (outcomes : InjectionOutcomeWord m w) :
    rawPostselectionBranch h .accepted (injectedBranchOperator h error outcomes) =
      rawAcceptedEndpoint h error outcomes := by
  classical
  unfold rawPostselectionBranch postselectionInstrument rawAcceptedEndpoint
    rawSyndromeBranch fullSyndromeInstrument
  simp only [FiniteInstrument.branchOperator_apply]
  apply Finset.sum_congr rfl
  intro syndrome _hsyndrome
  by_cases hsyndrome : syndrome =
      HH18PuncturedReedMuller.allPositiveSyndrome w r m
  · subst syndrome
    simp [syndromeOutcome]
  · simp [syndromeOutcome, hsyndrome]

/-- Coarse rejection retains exactly the sum of all non-all-positive raw
syndrome endpoints. -/
theorem rawPostselectionBranch_rejected_eq_rawRejectedEndpoint {w r m : Nat}
    (h : Admissible w r m) (error : PhysicalErrorWord m w)
    (outcomes : InjectionOutcomeWord m w) :
    rawPostselectionBranch h .rejected (injectedBranchOperator h error outcomes) =
      rawRejectedEndpoint h error outcomes := by
  classical
  unfold rawPostselectionBranch postselectionInstrument rawRejectedEndpoint
    rawSyndromeBranch fullSyndromeInstrument
  simp only [FiniteInstrument.branchOperator_apply]
  apply Finset.sum_congr rfl
  intro syndrome _hsyndrome
  by_cases hsyndrome : syndrome =
      HH18PuncturedReedMuller.allPositiveSyndrome w r m
  · subst syndrome
    simp [syndromeOutcome]
  · simp [syndromeOutcome, hsyndrome]
    symm
    erw [Fintype.sum_eq_single syndrome]
    · exact if_pos rfl
    · intro other hother
      exact if_neg hother

/-- An accepted physical-error word retains its complete raw operator at the
accepted coarse endpoint. -/
theorem rawAcceptedEndpoint_of_accepts {w r m : Nat} (h : Admissible w r m)
    (hdegree : 3 * r < m) (error : PhysicalErrorWord m w)
    (outcomes : InjectionOutcomeWord m w) (haccept : Accepts w r m error) :
    rawAcceptedEndpoint h error outcomes = errorBranchOperator h hdegree error := by
  rw [rawAcceptedEndpoint, rawSyndromeBranch_eq h hdegree]
  exact if_pos haccept.symm

/-- A rejected physical-error word has a literal zero accepted raw endpoint. -/
theorem rawAcceptedEndpoint_of_rejects {w r m : Nat} (h : Admissible w r m)
    (hdegree : 3 * r < m) (error : PhysicalErrorWord m w)
    (outcomes : InjectionOutcomeWord m w) (hreject : ¬ Accepts w r m error) :
    rawAcceptedEndpoint h error outcomes = 0 := by
  rw [rawAcceptedEndpoint, rawSyndromeBranch_eq h hdegree]
  exact if_neg (fun heq => hreject heq.symm)

/-- An accepted physical-error word contributes no raw mass to the rejected
coarse endpoint. -/
theorem rawRejectedEndpoint_of_accepts {w r m : Nat} (h : Admissible w r m)
    (hdegree : 3 * r < m) (error : PhysicalErrorWord m w)
    (outcomes : InjectionOutcomeWord m w) (haccept : Accepts w r m error) :
    rawRejectedEndpoint h error outcomes = 0 := by
  classical
  unfold rawRejectedEndpoint
  apply Finset.sum_eq_zero
  intro syndrome _hsyndrome
  rw [rawSyndromeBranch_eq h hdegree]
  by_cases hallPositive : syndrome =
      HH18PuncturedReedMuller.allPositiveSyndrome w r m
  · simp [hallPositive]
  · have hnonmatching : syndrome ≠ measuredSyndrome w r m error := by
      intro hmatch
      apply hallPositive
      rw [hmatch, haccept]
    simp [hallPositive, hnonmatching]

/-- A rejected physical-error word retains its complete raw operator in the
rejected coarse endpoint. -/
theorem rawRejectedEndpoint_of_rejects {w r m : Nat} (h : Admissible w r m)
    (hdegree : 3 * r < m) (error : PhysicalErrorWord m w)
    (outcomes : InjectionOutcomeWord m w) (hreject : ¬ Accepts w r m error) :
    rawRejectedEndpoint h error outcomes = errorBranchOperator h hdegree error := by
  classical
  have hnontrivial : measuredSyndrome w r m error ≠
      HH18PuncturedReedMuller.allPositiveSyndrome w r m := hreject
  rw [rawRejectedEndpoint, Fintype.sum_eq_single (measuredSyndrome w r m error)]
  · rw [if_neg hnontrivial, rawSyndromeBranch_eq h hdegree, if_pos rfl]
  · intro syndrome hne
    rw [rawSyndromeBranch_eq h hdegree]
    simp [hne]

end HH18Parameterized
end Distillation
end QEC
