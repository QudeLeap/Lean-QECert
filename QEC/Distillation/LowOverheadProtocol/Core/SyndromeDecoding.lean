import QEC.Distillation.LowOverheadProtocol.Core.SitewisePhaseInjection

/-!
# HH18 syndrome branches and the correctable accepted decode

This module feeds the concrete finite corrected-injection branch into the
actual `[[15,1,3]]` check family from `HH18PuncturedReedMuller`.  Every error
word determines its visible joint syndrome through the symplectic syndrome
bit, and the literal joint measurement branch is retained as an unnormalized
operator.  The accepted and rejected endpoints are only finite sums of those
raw branches.

For the bounded correctable route, an accepted pure `Z` word of weight at most
one is forced to be zero by the actual dual minimum distance three.  Only then
is the existing carrier equivalence inverted, recovering the logical `T`
output already established by the physical `T`-inverse theorem.  No total
decoder or later protocol layer is introduced here.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18SyndromeDecoding

open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

universe u

/-- The physical sites of the concrete HH18 `[[15,1,3]]` block. -/
abbrev PhysicalSite := HH18PuncturedReedMuller.PhysicalSite 4 0

/-- The one-qubit logical register selected by the concrete puncture. -/
abbrev LogicalSite := HH18PuncturedReedMuller.LogicalSite 4 0

/-- The physical Hilbert space measured by the actual HH18 checks. -/
abbrev PhysicalRegister := QubitRegister PhysicalSite

/-- The logical Hilbert space recovered on the accepted correctable route. -/
abbrev LogicalRegister := QubitRegister LogicalSite

/-- The same physical error words used by the noisy input and sitewise injection. -/
abbrev PhysicalErrorWord := HH18NoisyInput.PhysicalErrorWord 4 0

/-- The visible local injection outcomes already tensorized in Phase 5. -/
abbrev InjectionOutcomeWord := HH18SitewisePhaseInjection.InjectionOutcomeWord

/-- The actual oriented finite Z-check/X-check index supplied by #759. -/
abbrev CheckIndex :=
  Sum (HH18PuncturedReedMuller.ZCheckIndex 0 1 4)
    (HH18PuncturedReedMuller.XCheckIndex 0 1 4)

/-- The full visible HH18 joint syndrome. -/
abbrev Syndrome := JointSyndrome CheckIndex

/-- The concrete pure-Z Pauli represented by one physical resource-error word. -/
def errorPauli (error : PhysicalErrorWord) : Binary PhysicalSite :=
  cssZCheck error

/-- The deterministic signed outcome of every actual HH18 check on one error word. -/
def measuredSyndrome (error : PhysicalErrorWord) : Syndrome :=
  fun check =>
    if stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (errorPauli error) = 0 then
      StabilizerOutcome.positive
    else
      StabilizerOutcome.negative

/-- HH18 accepts exactly when the measured syndrome is all-positive. -/
def Accepts (error : PhysicalErrorWord) : Prop :=
  measuredSyndrome error =
    HH18PuncturedReedMuller.allPositiveSyndrome 0 1 4

/-- All-positive visible outcomes are exactly a zero symplectic syndrome. -/
theorem accepts_iff_zero_syndrome (error : PhysicalErrorWord) :
    Accepts error ↔
      stabilizerSyndrome
        (HH18PuncturedReedMuller.checkGenerator 0 1 4)
        (errorPauli error) = 0 := by
  constructor
  · intro haccept
    funext check
    change stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (errorPauli error) = 0
    have hcheck := congrFun haccept check
    change (if stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (errorPauli error) = 0 then StabilizerOutcome.positive
      else StabilizerOutcome.negative) = StabilizerOutcome.positive at hcheck
    by_cases hbit : stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (errorPauli error) = 0
    · exact hbit
    · simp [hbit] at hcheck
  · intro hzero
    funext check
    change (if stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (errorPauli error) = 0 then StabilizerOutcome.positive
      else StabilizerOutcome.negative) = StabilizerOutcome.positive
    have hcheck : stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (errorPauli error) = 0 := by
      exact congrFun hzero check
    simp [hcheck]

/-- The ideal physical error word has the all-positive HH18 syndrome. -/
theorem accepts_zero : Accepts (0 : PhysicalErrorWord) := by
  apply (accepts_iff_zero_syndrome 0).2
  funext check
  apply (stabilizerSyndromeBit_eq_zero_iff_commutes _ _).2
  simp [errorPauli, PauliSymplectic.cssZCheck, PauliSymplectic.Commutes,
    symplecticForm]

/-- The literal full joint-syndrome instrument of the real HH18 check family. -/
def fullSyndromeInstrument :
    FiniteInstrument Syndrome Syndrome PhysicalRegister PhysicalRegister :=
  jointStabilizerInstrument
    (HH18PuncturedReedMuller.checkGenerator 0 1 4)
    (HH18PuncturedReedMuller.checkGenerator_commutes
      HH18NoisyInput.hh18_15_1_0_admissible)

/-- Rank-one operator of the concrete physical error branch. -/
noncomputable def errorBranchOperator (error : PhysicalErrorWord) :
    Operator PhysicalRegister :=
  (InnerProductSpace.rankOne Complex
    (HH18NoisyInput.hh18PhysicalTInvErrorBranch error)
    (HH18NoisyInput.hh18PhysicalTInvErrorBranch error)).toLinearMap

/-- Rank-one operator produced by the actual sitewise corrected injection. -/
noncomputable def injectedBranchOperator
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) :
    Operator PhysicalRegister :=
  (InnerProductSpace.rankOne Complex
    (HH18SitewisePhaseInjection.sitewiseCorrectedTInvAttempt error outcomes
      HH18NoisyInput.hh18EncodedLogicalPlusInput)
    (HH18SitewisePhaseInjection.sitewiseCorrectedTInvAttempt error outcomes
      HH18NoisyInput.hh18EncodedLogicalPlusInput)).toLinearMap

/-- Sitewise phase cancellation identifies the injected operator with its Z-error branch. -/
theorem injectedBranchOperator_eq_errorBranchOperator
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) :
    injectedBranchOperator error outcomes = errorBranchOperator error := by
  exact HH18SitewisePhaseInjection.sitewiseCorrectedTInvAttempt_rankOne
    error outcomes

private theorem checkGenerator_toHermitian_eq (check : CheckIndex) :
    toHermitianQubitOperator
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check) =
      toQubitOperator
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check) := by
  cases check <;>
    simp [HH18PuncturedReedMuller.checkGenerator,
      binaryCSSParityCheckGenerators, toHermitianQubitOperator,
      hermitianPhaseScalar, binaryOverlapCount, binaryOverlapSupport,
      cssXCheck, cssZCheck, xSupport, zSupport]

private theorem idealBranch_mem_encodedCarrier :
    HH18NoisyInput.hh18PhysicalTInvBranch ∈
      HH18NoisyInput.hh18_15_1_0_encodedCode.code.carrier := by
  rw [HH18NoisyInput.hh18PhysicalTInvBranch_eq_logicalT]
  exact HH18NoisyInput.hh18_15_1_0_encodedCode.encode_mem _

private theorem idealBranch_mem_cssCarrier :
    HH18NoisyInput.hh18PhysicalTInvBranch ∈
      (HH18PuncturedReedMuller.cssCode
        HH18NoisyInput.hh18_15_1_0_admissible).stabilizer.code.carrier := by
  simpa only [HH18NoisyInput.hh18_15_1_0_encodedCode,
    HH18PuncturedReedMuller.encodedCode_code] using
      idealBranch_mem_encodedCarrier

private theorem idealBranch_check_fixed (check : CheckIndex) :
    toQubitOperator
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        HH18NoisyInput.hh18PhysicalTInvBranch =
      HH18NoisyInput.hh18PhysicalTInvBranch := by
  exact (HH18PuncturedReedMuller.mem_cssCarrier_iff_checkGenerator_fixed
    HH18NoisyInput.hh18_15_1_0_admissible
    HH18NoisyInput.hh18PhysicalTInvBranch).1
      idealBranch_mem_cssCarrier check

/-- The concrete Z-error branch has exactly its derived signed check eigenvalues. -/
theorem errorBranch_check_eigen (error : PhysicalErrorWord)
    (check : CheckIndex) :
    toHermitianQubitOperator
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (HH18NoisyInput.hh18PhysicalTInvErrorBranch error) =
      (measuredSyndrome error check).sign •
        HH18NoisyInput.hh18PhysicalTInvErrorBranch error := by
  have hfixed := idealBranch_check_fixed check
  rw [checkGenerator_toHermitian_eq]
  change
    toQubitOperator (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (toQubitOperator (cssZCheck error)
          HH18NoisyInput.hh18PhysicalTInvBranch) =
      (measuredSyndrome error check).sign •
        toQubitOperator (cssZCheck error)
          HH18NoisyInput.hh18PhysicalTInvBranch
  by_cases hbit : stabilizerSyndromeBit
      (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
      (errorPauli error) = 0
  · have herrorCheck : Commutes (errorPauli error)
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check) :=
      (stabilizerSyndromeBit_eq_zero_iff_commutes
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (errorPauli error)).1 hbit
    have hcheckError : Commutes
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (errorPauli error) :=
      (commutes_comm
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (errorPauli error)).2 herrorCheck
    have hcomm := toQubitOperator_commute_of_commutes
      (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
      (errorPauli error) hcheckError
    have happ := LinearMap.congr_fun hcomm
      HH18NoisyInput.hh18PhysicalTInvBranch
    simp only [Module.End.mul_apply] at happ
    rw [hfixed] at happ
    rw [measuredSyndrome, if_pos hbit]
    simp only [StabilizerOutcome.sign, one_smul]
    simpa only [errorPauli] using happ
  · have hbitOne : stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (errorPauli error) = 1 :=
      zmod_two_eq_one_of_ne_zero hbit
    have herrorCheck : ¬ Commutes (errorPauli error)
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check) :=
      (stabilizerSyndromeBit_eq_one_iff_not_commutes
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (errorPauli error)).1 hbitOne
    have hcheckError : ¬ Commutes
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (errorPauli error) := by
      intro hcomm
      exact herrorCheck ((commutes_comm
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (errorPauli error)).1 hcomm)
    have hanti := toQubitOperator_anticommute_of_not_commutes
      (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
      (errorPauli error) hcheckError
    have happ := LinearMap.congr_fun hanti
      HH18NoisyInput.hh18PhysicalTInvBranch
    simp only [LinearMap.neg_apply, Module.End.mul_apply] at happ
    rw [hfixed] at happ
    rw [measuredSyndrome, if_neg hbit]
    simp only [StabilizerOutcome.sign, neg_one_smul]
    simpa only [errorPauli] using happ

/-- The matching real joint-syndrome projector fixes the concrete error branch. -/
theorem matchingSyndromeProjector_errorBranch
    (error : PhysicalErrorWord) :
    jointStabilizerProjector
        (HH18PuncturedReedMuller.checkGenerator 0 1 4)
        (HH18PuncturedReedMuller.checkGenerator_commutes
          HH18NoisyInput.hh18_15_1_0_admissible)
        (measuredSyndrome error)
        (HH18NoisyInput.hh18PhysicalTInvErrorBranch error) =
      HH18NoisyInput.hh18PhysicalTInvErrorBranch error := by
  apply (jointStabilizerProjector_fixed_iff
    (HH18PuncturedReedMuller.checkGenerator 0 1 4)
    (HH18PuncturedReedMuller.checkGenerator_commutes
      HH18NoisyInput.hh18_15_1_0_admissible)
    (measuredSyndrome error)
    (HH18NoisyInput.hh18PhysicalTInvErrorBranch error)).2
  exact errorBranch_check_eigen error

/-- Every nonmatching full syndrome gives the literal zero vector branch. -/
theorem nonmatchingSyndromeProjector_errorBranch
    (error : PhysicalErrorWord) (syndrome : Syndrome)
    (hne : syndrome ≠ measuredSyndrome error) :
    jointStabilizerProjector
        (HH18PuncturedReedMuller.checkGenerator 0 1 4)
        (HH18PuncturedReedMuller.checkGenerator_commutes
          HH18NoisyInput.hh18_15_1_0_admissible)
        syndrome (HH18NoisyInput.hh18PhysicalTInvErrorBranch error) = 0 := by
  have hmul := jointStabilizerProjector_mul_of_ne
    (HH18PuncturedReedMuller.checkGenerator 0 1 4)
    (HH18PuncturedReedMuller.checkGenerator_commutes
      HH18NoisyInput.hh18_15_1_0_admissible)
    syndrome (measuredSyndrome error) hne
  have happ := LinearMap.congr_fun hmul
    (HH18NoisyInput.hh18PhysicalTInvErrorBranch error)
  rw [Module.End.mul_apply, matchingSyndromeProjector_errorBranch] at happ
  simpa using happ

private theorem sandwich_rankOne {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (L : H →ₗ[Complex] K) (psi : H) :
    L.comp ((InnerProductSpace.rankOne Complex psi psi).toLinearMap.comp
      (LinearMap.adjoint L)) =
      (InnerProductSpace.rankOne Complex (L psi) (L psi)).toLinearMap := by
  ext x
  simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    LinearMap.adjoint_inner_right]

private theorem selfAdjoint_sandwich_rankOne
    (L : Operator PhysicalRegister) (hL : LinearMap.adjoint L = L)
    (psi : PhysicalRegister) :
    L.comp ((InnerProductSpace.rankOne Complex psi psi).toLinearMap.comp L) =
      (InnerProductSpace.rankOne Complex (L psi) (L psi)).toLinearMap := by
  have h := sandwich_rankOne L psi
  rw [hL] at h
  exact h

/-- The literal full-instrument branch of the sitewise injected operator. -/
noncomputable def rawSyndromeBranch
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord)
    (syndrome : Syndrome) : Operator PhysicalRegister :=
  fullSyndromeInstrument.branchOperator syndrome
    (injectedBranchOperator error outcomes)

/-- The full instrument selects precisely the syndrome derived from the Z-error word. -/
theorem rawSyndromeBranch_eq
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord)
    (syndrome : Syndrome) :
    rawSyndromeBranch error outcomes syndrome =
      if syndrome = measuredSyndrome error then
        errorBranchOperator error
      else
        0 := by
  rw [rawSyndromeBranch, injectedBranchOperator_eq_errorBranchOperator,
    fullSyndromeInstrument, jointStabilizerInstrument_branchOperator]
  simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
  rw [errorBranchOperator]
  rw [selfAdjoint_sandwich_rankOne _
    (jointStabilizerProjector_adjoint
      (HH18PuncturedReedMuller.checkGenerator 0 1 4)
      (HH18PuncturedReedMuller.checkGenerator_commutes
        HH18NoisyInput.hh18_15_1_0_admissible)
      syndrome)]
  by_cases hmatch : syndrome = measuredSyndrome error
  · subst syndrome
    rw [matchingSyndromeProjector_errorBranch]
    simp
  · rw [nonmatchingSyndromeProjector_errorBranch error syndrome hmatch,
      if_neg hmatch]
    exact congrArg ContinuousLinearMap.toLinearMap
      (InnerProductSpace.rankOne_eq_zero.mpr (Or.inl rfl))

/-- The unnormalized all-positive endpoint of one injected error word. -/
noncomputable def rawAcceptedEndpoint
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) :
    Operator PhysicalRegister :=
  rawSyndromeBranch error outcomes
    (HH18PuncturedReedMuller.allPositiveSyndrome 0 1 4)

/-- The unnormalized sum of every non-all-positive endpoint. -/
noncomputable def rawRejectedEndpoint
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) :
    Operator PhysicalRegister :=
  ∑ syndrome : Syndrome,
    if syndrome = HH18PuncturedReedMuller.allPositiveSyndrome 0 1 4 then
      0
    else
      rawSyndromeBranch error outcomes syndrome

/-- An accepted error word retains its complete raw operator at the accepted endpoint. -/
theorem rawAcceptedEndpoint_of_accepts
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord)
    (haccept : Accepts error) :
    rawAcceptedEndpoint error outcomes = errorBranchOperator error := by
  rw [rawAcceptedEndpoint, rawSyndromeBranch_eq]
  exact if_pos haccept.symm

/-- A rejected error word has a literal zero accepted raw endpoint. -/
theorem rawAcceptedEndpoint_of_rejects
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord)
    (hreject : ¬ Accepts error) :
    rawAcceptedEndpoint error outcomes = 0 := by
  rw [rawAcceptedEndpoint, rawSyndromeBranch_eq]
  exact if_neg (fun heq => hreject heq.symm)

/-- An accepted error word contributes no raw mass to the rejected endpoint. -/
theorem rawRejectedEndpoint_of_accepts
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord)
    (haccept : Accepts error) :
    rawRejectedEndpoint error outcomes = 0 := by
  classical
  unfold rawRejectedEndpoint
  apply Finset.sum_eq_zero
  intro syndrome _hsyndrome
  rw [rawSyndromeBranch_eq]
  by_cases hallPositive : syndrome =
      HH18PuncturedReedMuller.allPositiveSyndrome 0 1 4
  · simp [hallPositive]
  · have hnonmatching : syndrome ≠ measuredSyndrome error := by
      intro hmatch
      apply hallPositive
      rw [hmatch, haccept]
    simp [hallPositive, hnonmatching]

/-- A rejected error word retains its complete raw operator in the rejected sum. -/
theorem rawRejectedEndpoint_of_rejects
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord)
    (hreject : ¬ Accepts error) :
    rawRejectedEndpoint error outcomes = errorBranchOperator error := by
  classical
  have hnontrivial : measuredSyndrome error ≠
      HH18PuncturedReedMuller.allPositiveSyndrome 0 1 4 := hreject
  rw [rawRejectedEndpoint, Fintype.sum_eq_single (measuredSyndrome error)]
  · rw [if_neg hnontrivial, rawSyndromeBranch_eq, if_pos rfl]
  · intro syndrome hne
    rw [rawSyndromeBranch_eq]
    simp [hne]

private theorem hh18PureZMinimumDistance :
    MinimumDistance (HH18PuncturedReedMuller.xCode 0 1 4).dual 3 := by
  have hcarrier :
      (shortenedReedMullerCode 1 4 0).dual.carrier =
        (puncturedReedMullerCode 2 4 0).carrier := by
    simpa using
      (shortenedReedMullerCode_dual_eq_punctured_of_lt_of_le
        (m := 4) (r := 2) (w := 0) (by omega) (by omega))
  have hminimum := puncturedReedMullerCode_minimumDistance
    (m := 4) (r := 2) (w := 0) (by omega)
  have htail : binomialTail (4 - 2) 0 = 3 := by native_decide
  rcases hminimum with ⟨word, hword, hwordNonzero, hwordWeight, hleast⟩
  refine ⟨word, ?_, hwordNonzero, ?_, ?_⟩
  · rw [HH18PuncturedReedMuller.xCode_eq_shortened, hcarrier]
    exact hword
  · simpa only [htail] using hwordWeight
  · intro candidate hcandidate hcandidateNonzero
    have hcandidatePunctured :
        candidate ∈ (puncturedReedMullerCode 2 4 0).carrier := by
      rw [← hcarrier]
      simpa only [HH18PuncturedReedMuller.xCode_eq_shortened] using hcandidate
    simpa only [htail] using
      hleast candidate hcandidatePunctured hcandidateNonzero

/-- Any pure-Z error below the HH18 distance-three threshold with zero
measured syndrome is the zero word. -/
theorem acceptedError_eq_zero_of_hammingWeight_lt_three (error : PhysicalErrorWord)
    (hweight : HammingWeight error < 3) (haccept : Accepts error) :
    error = 0 := by
  by_contra herror
  obtain ⟨x, hx, hnotCommutes⟩ :=
    exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
      (HH18PuncturedReedMuller.xCode 0 1 4)
      hh18PureZMinimumDistance herror hweight
  have hzero := (accepts_iff_zero_syndrome error).1 haccept
  have hnormalizer : InStabilizerNormalizer
      (HH18PuncturedReedMuller.checkGenerator 0 1 4)
      (errorPauli error) :=
    (stabilizerSyndrome_map_properties
      (HH18PuncturedReedMuller.checkGenerator 0 1 4)
      (errorPauli error) (errorPauli error) (errorPauli error)).1.mp hzero
  have hgenerated : GeneratedStabilizer
      (HH18PuncturedReedMuller.checkGenerator 0 1 4) (cssXCheck x) := by
    change GeneratedStabilizer
      (binaryCSSParityCheckGenerators
        (HH18PuncturedReedMuller.zParityCheck 0 1 4)
        (HH18PuncturedReedMuller.xParityCheck 0 1 4))
      (cssXCheck x)
    apply binaryCSSParityCheckGenerators_generate_cssXCheck
    simpa only [HH18PuncturedReedMuller.xCode] using hx
  exact hnotCommutes (by
    simpa only [errorPauli] using hnormalizer (cssXCheck x) hgenerated)

/-- A correctable pure-Z word with zero measured syndrome is the zero word. -/
theorem correctableAcceptedError_eq_zero (error : PhysicalErrorWord)
    (hweight : HammingWeight error ≤ 1) (haccept : Accepts error) :
    error = 0 :=
  acceptedError_eq_zero_of_hammingWeight_lt_three error (by omega) haccept

/-- Every nonzero accepted HH18 diagonal-error word has physical weight at
least three.  This is the distance input for the cubic error recurrence. -/
theorem accepted_nonzero_hammingWeight_ge_three (error : PhysicalErrorWord)
    (herror : error ≠ 0) (haccept : Accepts error) :
    3 ≤ HammingWeight error := by
  by_contra hlt
  have hweight : HammingWeight error < 3 := by omega
  exact herror (acceptedError_eq_zero_of_hammingWeight_lt_three error hweight haccept)

private theorem zeroErrorBranch_eq_ideal :
    HH18NoisyInput.hh18PhysicalTInvErrorBranch (0 : PhysicalErrorWord) =
      HH18NoisyInput.hh18PhysicalTInvBranch := by
  rw [HH18NoisyInput.hh18PhysicalTInvErrorBranch,
    HH18NoisyInput.zErrorOperator]
  change toQubitOperator (binaryOne (ι := PhysicalSite))
      HH18NoisyInput.hh18PhysicalTInvBranch =
    HH18NoisyInput.hh18PhysicalTInvBranch
  rw [toQubitOperator_one]
  rfl

/-- The accepted correctable branch, now certified as an element of the real carrier. -/
noncomputable def correctableAcceptedCarrierState
    (error : PhysicalErrorWord) (hweight : HammingWeight error ≤ 1)
    (haccept : Accepts error) :
    HH18NoisyInput.hh18_15_1_0_encodedCode.code.carrier :=
  ⟨HH18NoisyInput.hh18PhysicalTInvErrorBranch error, by
    have hzero := correctableAcceptedError_eq_zero error hweight haccept
    subst error
    rw [zeroErrorBranch_eq_ideal]
    exact idealBranch_mem_encodedCarrier⟩

/-- Inverse encoding applied only to the certified accepted carrier branch. -/
noncomputable def decodedCorrectableAcceptedOutput
    (error : PhysicalErrorWord) (hweight : HammingWeight error ≤ 1)
    (haccept : Accepts error) : LogicalRegister :=
  HH18NoisyInput.hh18_15_1_0_encodedCode.encoding.symm
    (correctableAcceptedCarrierState error hweight haccept)

/-- The correctable zero-syndrome route decodes to the established logical-T output. -/
theorem decodedCorrectableAcceptedOutput_eq_logicalT
    (error : PhysicalErrorWord) (hweight : HammingWeight error ≤ 1)
    (haccept : Accepts error) :
    decodedCorrectableAcceptedOutput error hweight haccept =
      HH18PuncturedReedMuller.logicalT 0 4
        HH18NoisyInput.hh18LogicalPlusInput := by
  unfold decodedCorrectableAcceptedOutput
  apply HH18NoisyInput.hh18_15_1_0_encodedCode.encoding.injective
  rw [HH18NoisyInput.hh18_15_1_0_encodedCode.encoding.apply_symm_apply]
  apply Subtype.ext
  change HH18NoisyInput.hh18PhysicalTInvErrorBranch error =
    HH18NoisyInput.hh18_15_1_0_encodedCode.encode
      (HH18PuncturedReedMuller.logicalT 0 4
        HH18NoisyInput.hh18LogicalPlusInput)
  rw [correctableAcceptedError_eq_zero error hweight haccept,
    zeroErrorBranch_eq_ideal,
    HH18NoisyInput.hh18PhysicalTInvBranch_eq_logicalT]

end HH18SyndromeDecoding
end Distillation
end QEC
