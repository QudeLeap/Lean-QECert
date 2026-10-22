import QEC.Distillation.LowOverheadProtocol.Parameterized.SitewiseInjection

/-!
# Parameterized HH18 joint-syndrome detection

This layer applies the actual finite joint stabilizer measurement of an
admissible HH18 punctured Reed--Muller block to the sitewise injected physical
branch.  It derives the accepted-error detection threshold from the dual
minimum distance of the constructed `xCode`; it does not coarse-grain,
normalize, or decode any branch.
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

/-- The oriented finite Z-check/X-check index of an HH18 block. -/
abbrev CheckIndex (w r m : Nat) :=
  Sum (HH18PuncturedReedMuller.ZCheckIndex w r m)
    (HH18PuncturedReedMuller.XCheckIndex w r m)

/-- A full visible joint syndrome of the actual HH18 check family. -/
abbrev Syndrome (w r m : Nat) := JointSyndrome (CheckIndex w r m)

/-- The pure-Z Pauli represented by one physical resource-error word. -/
def errorPauli {m w : Nat} (error : PhysicalErrorWord m w) :
    Binary (PhysicalSite m w) :=
  cssZCheck error

/-- The deterministic signed outcome of every actual HH18 check on one
physical error word. -/
def measuredSyndrome (w r m : Nat) (error : PhysicalErrorWord m w) :
    Syndrome w r m :=
  fun check =>
    if stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator w r m check)
        (errorPauli error) = 0 then
      StabilizerOutcome.positive
    else
      StabilizerOutcome.negative

/-- An error word is accepted precisely when its full measured syndrome is
all-positive. -/
def Accepts (w r m : Nat) (error : PhysicalErrorWord m w) : Prop :=
  measuredSyndrome w r m error =
    HH18PuncturedReedMuller.allPositiveSyndrome w r m

/-- All-positive visible outcomes are exactly a zero symplectic syndrome. -/
theorem accepts_iff_zero_syndrome (w r m : Nat) (error : PhysicalErrorWord m w) :
    Accepts w r m error ↔
      stabilizerSyndrome
        (HH18PuncturedReedMuller.checkGenerator w r m)
        (errorPauli error) = 0 := by
  constructor
  · intro haccept
    funext check
    change stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator w r m check)
        (errorPauli error) = 0
    have hcheck := congrFun haccept check
    change (if stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator w r m check)
        (errorPauli error) = 0 then StabilizerOutcome.positive
      else StabilizerOutcome.negative) = StabilizerOutcome.positive at hcheck
    by_cases hbit : stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator w r m check)
        (errorPauli error) = 0
    · exact hbit
    · simp [hbit] at hcheck
  · intro hzero
    funext check
    change (if stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator w r m check)
        (errorPauli error) = 0 then StabilizerOutcome.positive
      else StabilizerOutcome.negative) = StabilizerOutcome.positive
    have hcheck : stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator w r m check)
        (errorPauli error) = 0 := by
      exact congrFun hzero check
    simp [hcheck]

/-- The ideal physical error word has the all-positive HH18 syndrome. -/
theorem accepts_zero (w r m : Nat) :
    Accepts w r m (0 : PhysicalErrorWord m w) := by
  apply (accepts_iff_zero_syndrome w r m 0).2
  funext check
  apply (stabilizerSyndromeBit_eq_zero_iff_commutes _ _).2
  simp [errorPauli, PauliSymplectic.cssZCheck, PauliSymplectic.Commutes,
    symplecticForm]

/-- The literal full joint-syndrome instrument of the actual parameterized
HH18 check family. -/
def fullSyndromeInstrument {w r m : Nat} (h : Admissible w r m) :
    FiniteInstrument (Syndrome w r m) (Syndrome w r m)
      (PhysicalRegister m w) (PhysicalRegister m w) :=
  jointStabilizerInstrument
    (HH18PuncturedReedMuller.checkGenerator w r m)
    (HH18PuncturedReedMuller.checkGenerator_commutes h)

/-- Completeness is derived from the actual finite joint-projector resolution. -/
theorem fullSyndromeInstrument_complete {w r m : Nat} (h : Admissible w r m) :
    (fullSyndromeInstrument h).kraus.Complete :=
  jointStabilizerKrausFamily_complete
    (HH18PuncturedReedMuller.checkGenerator w r m)
    (HH18PuncturedReedMuller.checkGenerator_commutes h)

/-- Rank-one operator of the actual physical Pauli-error branch. -/
noncomputable def errorBranchOperator {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) : Operator (PhysicalRegister m w) :=
  (InnerProductSpace.rankOne Complex
    (HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree))
    (HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree))).toLinearMap

/-- Rank-one operator produced by the actual sitewise corrected injection. -/
noncomputable def injectedBranchOperator {w r m : Nat}
    (h : Admissible w r m) (error : PhysicalErrorWord m w)
    (outcomes : InjectionOutcomeWord m w) :
    Operator (PhysicalRegister m w) :=
  (InnerProductSpace.rankOne Complex
    (sitewiseCorrectedTInvAttempt error outcomes (encodedLogicalPlus h))
    (sitewiseCorrectedTInvAttempt error outcomes (encodedLogicalPlus h))).toLinearMap

/-- Sitewise phase cancellation identifies the injected operator with its
actual Pauli-error branch. -/
theorem injectedBranchOperator_eq_errorBranchOperator {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w) :
    injectedBranchOperator h error outcomes =
      errorBranchOperator h hdegree error := by
  exact sitewiseCorrectedTInvAttempt_rankOne h hdegree error outcomes

private theorem checkGenerator_toHermitian_eq {w r m : Nat}
    (check : CheckIndex w r m) :
    toHermitianQubitOperator
        (HH18PuncturedReedMuller.checkGenerator w r m check) =
      toQubitOperator
        (HH18PuncturedReedMuller.checkGenerator w r m check) := by
  cases check <;>
    simp [HH18PuncturedReedMuller.checkGenerator,
      binaryCSSParityCheckGenerators, toHermitianQubitOperator,
      hermitianPhaseScalar, binaryOverlapCount, binaryOverlapSupport,
      cssXCheck, cssZCheck, xSupport, zSupport]

private theorem idealBranch_mem_encodedCarrier {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    physicalTInvBranch h hdegree ∈
      (HH18PuncturedReedMuller.encodedCode h).code.carrier := by
  rw [physicalTInvBranch_eq_logicalT h hdegree]
  exact (HH18PuncturedReedMuller.encodedCode h).encode_mem _

private theorem idealBranch_mem_cssCarrier {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    physicalTInvBranch h hdegree ∈
      (HH18PuncturedReedMuller.cssCode h).stabilizer.code.carrier := by
  simpa only [HH18PuncturedReedMuller.encodedCode_code] using
    idealBranch_mem_encodedCarrier h hdegree

private theorem idealBranch_check_fixed {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (check : CheckIndex w r m) :
    toQubitOperator
        (HH18PuncturedReedMuller.checkGenerator w r m check)
        (physicalTInvBranch h hdegree) =
      physicalTInvBranch h hdegree := by
  exact (HH18PuncturedReedMuller.mem_cssCarrier_iff_checkGenerator_fixed
    h (physicalTInvBranch h hdegree)).1
      (idealBranch_mem_cssCarrier h hdegree) check

/-- The actual Pauli-error branch has exactly its derived signed check
eigenvalues. -/
theorem errorBranch_check_eigen {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) (check : CheckIndex w r m) :
    toHermitianQubitOperator
        (HH18PuncturedReedMuller.checkGenerator w r m check)
        (HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree)) =
      (measuredSyndrome w r m error check).sign •
        HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree) := by
  have hfixed := idealBranch_check_fixed h hdegree check
  rw [checkGenerator_toHermitian_eq]
  change
    toQubitOperator (HH18PuncturedReedMuller.checkGenerator w r m check)
        (toQubitOperator (cssZCheck error) (physicalTInvBranch h hdegree)) =
      (measuredSyndrome w r m error check).sign •
        toQubitOperator (cssZCheck error) (physicalTInvBranch h hdegree)
  by_cases hbit : stabilizerSyndromeBit
      (HH18PuncturedReedMuller.checkGenerator w r m check)
      (errorPauli error) = 0
  · have herrorCheck : Commutes (errorPauli error)
        (HH18PuncturedReedMuller.checkGenerator w r m check) :=
      (stabilizerSyndromeBit_eq_zero_iff_commutes
        (HH18PuncturedReedMuller.checkGenerator w r m check)
        (errorPauli error)).1 hbit
    have hcheckError : Commutes
        (HH18PuncturedReedMuller.checkGenerator w r m check)
        (errorPauli error) :=
      (commutes_comm
        (HH18PuncturedReedMuller.checkGenerator w r m check)
        (errorPauli error)).2 herrorCheck
    have hcomm := toQubitOperator_commute_of_commutes
      (HH18PuncturedReedMuller.checkGenerator w r m check)
      (errorPauli error) hcheckError
    have happ := LinearMap.congr_fun hcomm (physicalTInvBranch h hdegree)
    simp only [Module.End.mul_apply] at happ
    rw [hfixed] at happ
    rw [measuredSyndrome, if_pos hbit]
    simp only [StabilizerOutcome.sign, one_smul]
    simpa only [errorPauli] using happ
  · have hbitOne : stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator w r m check)
        (errorPauli error) = 1 :=
      zmod_two_eq_one_of_ne_zero hbit
    have herrorCheck : ¬ Commutes (errorPauli error)
        (HH18PuncturedReedMuller.checkGenerator w r m check) :=
      (stabilizerSyndromeBit_eq_one_iff_not_commutes
        (HH18PuncturedReedMuller.checkGenerator w r m check)
        (errorPauli error)).1 hbitOne
    have hcheckError : ¬ Commutes
        (HH18PuncturedReedMuller.checkGenerator w r m check)
        (errorPauli error) := by
      intro hcomm
      exact herrorCheck ((commutes_comm
        (HH18PuncturedReedMuller.checkGenerator w r m check)
        (errorPauli error)).1 hcomm)
    have hanti := toQubitOperator_anticommute_of_not_commutes
      (HH18PuncturedReedMuller.checkGenerator w r m check)
      (errorPauli error) hcheckError
    have happ := LinearMap.congr_fun hanti (physicalTInvBranch h hdegree)
    simp only [LinearMap.neg_apply, Module.End.mul_apply] at happ
    rw [hfixed] at happ
    rw [measuredSyndrome, if_neg hbit]
    simp only [StabilizerOutcome.sign, neg_one_smul]
    simpa only [errorPauli] using happ

/-- The matching joint-syndrome projector fixes the actual physical error branch. -/
theorem matchingSyndromeProjector_errorBranch {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) :
    jointStabilizerProjector
        (HH18PuncturedReedMuller.checkGenerator w r m)
        (HH18PuncturedReedMuller.checkGenerator_commutes h)
        (measuredSyndrome w r m error)
        (HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree)) =
      HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree) := by
  apply (jointStabilizerProjector_fixed_iff
    (HH18PuncturedReedMuller.checkGenerator w r m)
    (HH18PuncturedReedMuller.checkGenerator_commutes h)
    (measuredSyndrome w r m error)
    (HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree))).2
  exact errorBranch_check_eigen h hdegree error

/-- Every nonmatching full syndrome gives the literal zero vector branch. -/
theorem nonmatchingSyndromeProjector_errorBranch {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) (syndrome : Syndrome w r m)
    (hne : syndrome ≠ measuredSyndrome w r m error) :
    jointStabilizerProjector
        (HH18PuncturedReedMuller.checkGenerator w r m)
        (HH18PuncturedReedMuller.checkGenerator_commutes h)
        syndrome
        (HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree)) = 0 := by
  have hmul := jointStabilizerProjector_mul_of_ne
    (HH18PuncturedReedMuller.checkGenerator w r m)
    (HH18PuncturedReedMuller.checkGenerator_commutes h)
    syndrome (measuredSyndrome w r m error) hne
  have happ := LinearMap.congr_fun hmul
    (HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree))
  rw [Module.End.mul_apply,
    matchingSyndromeProjector_errorBranch h hdegree error] at happ
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

private theorem selfAdjoint_sandwich_rankOne {m w : Nat}
    (L : Operator (PhysicalRegister m w)) (hL : LinearMap.adjoint L = L)
    (psi : PhysicalRegister m w) :
    L.comp ((InnerProductSpace.rankOne Complex psi psi).toLinearMap.comp L) =
      (InnerProductSpace.rankOne Complex (L psi) (L psi)).toLinearMap := by
  have h := sandwich_rankOne L psi
  rw [hL] at h
  exact h

/-- The literal full-instrument branch of the sitewise injected operator. -/
noncomputable def rawSyndromeBranch {w r m : Nat}
    (h : Admissible w r m) (error : PhysicalErrorWord m w)
    (outcomes : InjectionOutcomeWord m w)
    (syndrome : Syndrome w r m) : Operator (PhysicalRegister m w) :=
  (fullSyndromeInstrument h).branchOperator syndrome
    (injectedBranchOperator h error outcomes)

/-- The full instrument selects precisely the syndrome derived from the
physical Pauli-error word. -/
theorem rawSyndromeBranch_eq {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w)
    (syndrome : Syndrome w r m) :
    rawSyndromeBranch h error outcomes syndrome =
      if syndrome = measuredSyndrome w r m error then
        errorBranchOperator h hdegree error
      else
        0 := by
  rw [rawSyndromeBranch,
    injectedBranchOperator_eq_errorBranchOperator h hdegree error outcomes,
    fullSyndromeInstrument, jointStabilizerInstrument_branchOperator]
  simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
  rw [errorBranchOperator]
  rw [selfAdjoint_sandwich_rankOne _
    (jointStabilizerProjector_adjoint
      (HH18PuncturedReedMuller.checkGenerator w r m)
      (HH18PuncturedReedMuller.checkGenerator_commutes h)
      syndrome)]
  by_cases hmatch : syndrome = measuredSyndrome w r m error
  · subst syndrome
    rw [matchingSyndromeProjector_errorBranch h hdegree error]
    simp
  · rw [nonmatchingSyndromeProjector_errorBranch h hdegree error syndrome hmatch,
      if_neg hmatch]
    exact congrArg ContinuousLinearMap.toLinearMap
      (InnerProductSpace.rankOne_eq_zero.mpr (Or.inl rfl))

private theorem pureZMinimumDistance {w r m : Nat}
    (h : Admissible w r m) :
    MinimumDistance (HH18PuncturedReedMuller.xCode w r m).dual
      (codeDistance r w) := by
  have hcomplementDegree : m - (m - r - 1) - 1 = r := by
    have hdegree := h.2.2
    omega
  have hcomplementTail : m - (m - r - 1) = r + 1 := by
    have hdegree := h.2.2
    omega
  have hcomplementLt : m - r - 1 < m := by
    have hdegree := h.2.2
    omega
  have hcut : w ≤ m - (m - r - 1) - 1 := by
    have hwindow := h.2.1
    omega
  have hnoKernel : w < m - (m - r - 1) := by
    have hwindow := h.2.1
    omega
  have hcarrier :
      (shortenedReedMullerCode r m w).dual.carrier =
        (puncturedReedMullerCode (m - r - 1) m w).carrier := by
    simpa only [hcomplementDegree] using
      (shortenedReedMullerCode_dual_eq_punctured_of_lt_of_le
        (r := m - r - 1) (m := m) (w := w) hcomplementLt hcut)
  have hminimum := puncturedReedMullerCode_minimumDistance
    (r := m - r - 1) (m := m) (w := w) hnoKernel
  rcases hminimum with ⟨word, hword, hwordNonzero, hwordWeight, hleast⟩
  refine ⟨word, ?_, hwordNonzero, ?_, ?_⟩
  · rw [HH18PuncturedReedMuller.xCode_eq_shortened, hcarrier]
    exact hword
  · simpa only [hcomplementTail, codeDistance] using hwordWeight
  · intro candidate hcandidate hcandidateNonzero
    have hcandidatePunctured :
        candidate ∈ (puncturedReedMullerCode (m - r - 1) m w).carrier := by
      rw [← hcarrier]
      simpa only [HH18PuncturedReedMuller.xCode_eq_shortened] using hcandidate
    simpa only [hcomplementTail, codeDistance] using
      hleast candidate hcandidatePunctured hcandidateNonzero

/-- An accepted pure-Z error below the actual `xCode` dual distance is zero. -/
theorem acceptedError_eq_zero_of_hammingWeight_lt_codeDistance {w r m : Nat}
    (h : Admissible w r m) (error : PhysicalErrorWord m w)
    (hweight : HammingWeight error < codeDistance r w)
    (haccept : Accepts w r m error) :
    error = 0 := by
  by_contra herror
  obtain ⟨x, hx, hnotCommutes⟩ :=
    exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
      (HH18PuncturedReedMuller.xCode w r m)
      (pureZMinimumDistance h) herror hweight
  have hzero := (accepts_iff_zero_syndrome w r m error).1 haccept
  have hnormalizer : InStabilizerNormalizer
      (HH18PuncturedReedMuller.checkGenerator w r m)
      (errorPauli error) :=
    (stabilizerSyndrome_map_properties
      (HH18PuncturedReedMuller.checkGenerator w r m)
      (errorPauli error) (errorPauli error) (errorPauli error)).1.mp hzero
  have hgenerated : GeneratedStabilizer
      (HH18PuncturedReedMuller.checkGenerator w r m) (cssXCheck x) := by
    change GeneratedStabilizer
      (binaryCSSParityCheckGenerators
        (HH18PuncturedReedMuller.zParityCheck w r m)
        (HH18PuncturedReedMuller.xParityCheck w r m))
      (cssXCheck x)
    apply binaryCSSParityCheckGenerators_generate_cssXCheck
    simpa only [HH18PuncturedReedMuller.xCode] using hx
  exact hnotCommutes (by
    simpa only [errorPauli] using hnormalizer (cssXCheck x) hgenerated)

/-- Every nonzero accepted diagonal-error word has weight at least the actual
distance derived from the constructed parameterized `xCode`. -/
theorem accepted_nonzero_hammingWeight_ge_codeDistance {w r m : Nat}
    (h : Admissible w r m) (error : PhysicalErrorWord m w)
    (herror : error ≠ 0) (haccept : Accepts w r m error) :
    codeDistance r w ≤ HammingWeight error := by
  by_contra hlt
  have hweight : HammingWeight error < codeDistance r w := by omega
  exact herror
    (acceptedError_eq_zero_of_hammingWeight_lt_codeDistance h error hweight haccept)

end HH18Parameterized
end Distillation
end QEC
