import QEC.Distillation.LowOverheadProtocol.Core.PhaseInjection

/-!
# HH18 finite-register phase-injection covariance

This module tensorizes the established one-qubit corrected phase-injection
actions over the actual fifteen physical sites of the HH18 block.  A complete
Boolean outcome word supplies the measured branch at every site, while the
existing binary resource-error word selects the ideal or Pauli-`Z`-errored
one-qubit resource there.

The lift is defined by finite computational-basis coordinates.  Its only
vector-level ambiguity is the literal product of the one-shot branch scalars;
the final rank-one equality removes that scalar.  No later protocol layer is
constructed here.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18SitewisePhaseInjection

open Coding Semantics
open Semantics.Qubit
open scoped BigOperators

/-- The actual fifteen physical coordinates of the `m = 4`, `w = 0` HH18 block. -/
abbrev PhysicalSite := HH18PuncturedReedMuller.PhysicalSite 4 0

/-- The resource-error labels already used by the concrete HH18 noisy input. -/
abbrev PhysicalErrorWord := HH18NoisyInput.PhysicalErrorWord 4 0

/-- One visible corrected-injection measurement outcome at every physical site. -/
abbrev InjectionOutcomeWord := PhysicalSite -> Bool

/-- The phase-state angle selected by one coordinate of the actual error word. -/
def tInvResourceAngle (error : ZMod 2) : Real :=
  if error = 0 then HH18PhaseInjection.tInvIdealAngle
  else HH18PhaseInjection.tInvErrorAngle

/-- The already proved corrected one-qubit attempt selected by a binary resource error. -/
noncomputable def correctedTInvAttempt (error : ZMod 2) (psi : QubitSpace)
    (hpsi : ‖psi‖ = 1) (coin : Bool) : QubitSpace :=
  if error = 0 then
    HH18PhaseInjection.correctedIdealTInvAttempt psi hpsi coin
  else
    HH18PhaseInjection.correctedErroredTInvAttempt psi hpsi coin

/-- Binary error selection specializes the accepted ideal/error covariance theorem. -/
theorem correctedTInvAttempt_action (error : ZMod 2) (psi : QubitSpace)
    (hpsi : ‖psi‖ = 1) (coin : Bool) :
    correctedTInvAttempt error psi hpsi coin =
      PhaseInjection.oneShotAttemptGlobalPhase
          (tInvResourceAngle error) coin •
        (if error = 0 then
          OneQubitMagic.phaseShiftOperator
            HH18PhaseInjection.tInvIdealAngle psi
        else
          pauliZ (OneQubitMagic.phaseShiftOperator
            HH18PhaseInjection.tInvIdealAngle psi)) := by
  by_cases herror : error = 0
  · subst error
    simpa [correctedTInvAttempt, tInvResourceAngle] using
      (HH18PhaseInjection.correctedIdealTInvAttempt_action psi hpsi coin)
  · have herror_one : error = 1 :=
      PauliSymplectic.zmod_two_eq_one_of_ne_zero herror
    subst error
    simpa [correctedTInvAttempt, tInvResourceAngle] using
      (HH18PhaseInjection.correctedErroredTInvAttempt_action psi hpsi coin)

/-- The diagonal entry of one actual corrected attempt on a normalized basis state. -/
noncomputable def correctedTInvBasisAmplitude
    (error : ZMod 2) (coin : Bool) (bit : Fin 2) : Complex :=
  correctedTInvAttempt error
    (EuclideanSpace.basisFun (Fin 2) Complex bit)
    ((EuclideanSpace.basisFun (Fin 2) Complex).norm_eq_one bit)
    coin bit

/-- Each local diagonal entry is its measured scalar, resource-error sign, and ideal `T†` phase. -/
theorem correctedTInvBasisAmplitude_eq
    (error : ZMod 2) (coin : Bool) (bit : Fin 2) :
    correctedTInvBasisAmplitude error coin bit =
      PhaseInjection.oneShotAttemptGlobalPhase
          (tInvResourceAngle error) coin *
        (if error = 0 then 1 else zPhase bit) *
          OneQubitMagic.phaseAmplitude
            (HH18PhaseInjection.tInvIdealAngle * bit.val) := by
  unfold correctedTInvBasisAmplitude
  rw [correctedTInvAttempt_action]
  simp only [PiLp.smul_apply, smul_eq_mul]
  by_cases herror : error = 0
  · subst error
    fin_cases bit <;>
      simp [tInvResourceAngle, EuclideanSpace.basisFun_apply]
  · have herror_one : error = 1 :=
      PauliSymplectic.zmod_two_eq_one_of_ne_zero herror
    subst error
    fin_cases bit <;>
      simp [tInvResourceAngle, EuclideanSpace.basisFun_apply] <;> ring

/-- The sole register-wide vector scalar: the finite product of actual branch scalars. -/
noncomputable def sitewiseTInvGlobalPhase
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) : Complex :=
  ∏ i, PhaseInjection.oneShotAttemptGlobalPhase
    (tInvResourceAngle (error i)) (outcomes i)

/-- The finite diagonal tensor lift of the corrected one-qubit attempts. -/
noncomputable def sitewiseCorrectedTInvAttempt
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord)
    (psi : QubitRegister PhysicalSite) : QubitRegister PhysicalSite :=
  WithLp.toLp 2 fun bits =>
    (∏ i, correctedTInvBasisAmplitude (error i) (outcomes i) (bits i)) *
      psi bits

private theorem errorPhaseProduct_eq_zSupportPhase
    (error : PhysicalErrorWord) (bits : Bitstring PhysicalSite) :
    (∏ i, if error i = 0 then 1 else zPhase (bits i)) =
      Qubit.zSupportPhase (PauliSymplectic.binarySupport error) bits := by
  classical
  rw [Qubit.zSupportPhase, PauliSymplectic.binarySupport,
    Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _hi
  by_cases herror : error i = 0 <;> simp [herror]

private theorem bitValueSum_eq_hammingWeight (bits : Bitstring PhysicalSite) :
    (∑ i, (bits i).val) =
      HammingWeight (PauliSymplectic.bitstringWordEquiv PhysicalSite bits) := by
  classical
  simp only [HammingWeight, hammingSupport, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _hi
  change (bits i).val = if bits i ≠ 0 then 1 else 0
  by_cases hi : bits i = 0
  · rw [if_neg (not_ne_iff.mpr hi)]
    simp [hi]
  · rw [if_pos hi]
    have hval0 : (bits i).val ≠ 0 := by
      intro hval
      apply hi
      apply Fin.ext
      simpa using hval
    have hpos : 0 < (bits i).val := Nat.pos_of_ne_zero hval0
    have hlt : (bits i).val < 2 := (bits i).isLt
    omega

private theorem phaseAmplitudeProduct_eq_hammingWeight
    (bits : Bitstring PhysicalSite) :
    (∏ i, OneQubitMagic.phaseAmplitude
      (HH18PhaseInjection.tInvIdealAngle * (bits i).val)) =
      OneQubitMagic.phaseAmplitude
        (HH18PhaseInjection.tInvIdealAngle *
          (HammingWeight
            (PauliSymplectic.bitstringWordEquiv PhysicalSite bits) : Real)) := by
  classical
  have hcombine (s : Finset PhysicalSite) :
      (∏ i ∈ s, OneQubitMagic.phaseAmplitude
        (HH18PhaseInjection.tInvIdealAngle * (bits i).val)) =
        OneQubitMagic.phaseAmplitude
          (∑ i ∈ s, HH18PhaseInjection.tInvIdealAngle * (bits i).val) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simp only [Finset.prod_insert hi, Finset.sum_insert hi, ih,
          OneQubitMagic.phaseAmplitude_add]
  rw [show (∏ i, OneQubitMagic.phaseAmplitude
      (HH18PhaseInjection.tInvIdealAngle * (bits i).val)) =
      OneQubitMagic.phaseAmplitude
        (∑ i, HH18PhaseInjection.tInvIdealAngle * (bits i).val) by
        simpa using hcombine Finset.univ]
  congr 1
  rw [← bitValueSum_eq_hammingWeight bits]
  push_cast
  rw [Finset.mul_sum]

/-- The concrete binary Pauli error acts by the corresponding support-phase product. -/
theorem zErrorOperator_apply (error : PhysicalErrorWord)
    (psi : QubitRegister PhysicalSite) (bits : Bitstring PhysicalSite) :
    HH18NoisyInput.zErrorOperator error psi bits =
      Qubit.zSupportPhase (PauliSymplectic.binarySupport error) bits * psi bits := by
  rw [HH18NoisyInput.zErrorOperator,
    PauliSymplectic.toQubitOperator_apply]
  simp [PauliSymplectic.xSupport, PauliSymplectic.zSupport]

/-- The inverse physical HH18 transport has the negative all-site phase coordinates. -/
theorem physicalTInv_apply (psi : QubitRegister PhysicalSite)
    (bits : Bitstring PhysicalSite) :
    HH18PuncturedReedMuller.physicalTInv 0 4 psi bits =
      OneQubitMagic.phaseAmplitude
          (HH18PhaseInjection.tInvIdealAngle *
            (HammingWeight
              (PauliSymplectic.bitstringWordEquiv PhysicalSite bits) : Real)) *
        psi bits := by
  have hinverse :
      HH18PuncturedReedMuller.physicalT 0 4
          (HH18PuncturedReedMuller.physicalTInv 0 4 psi) = psi := by
    change (HH18PuncturedReedMuller.physicalT 0 4).toLinearEquiv
      ((HH18PuncturedReedMuller.physicalT 0 4).toLinearEquiv.symm psi) = psi
    exact (HH18PuncturedReedMuller.physicalT 0 4).toLinearEquiv.apply_symm_apply psi
  have hcoordinate :=
    congrArg (fun state : QubitRegister PhysicalSite => state bits) hinverse
  rw [HH18PuncturedReedMuller.physicalT_eq_allSiteT] at hcoordinate
  change Triorthogonal.allSiteT
      (HH18PuncturedReedMuller.physicalTInv 0 4 psi) bits = psi bits
    at hcoordinate
  rw [Triorthogonal.allSiteT_apply] at hcoordinate
  calc
    HH18PuncturedReedMuller.physicalTInv 0 4 psi bits =
        OneQubitMagic.phaseAmplitude
            (HH18PhaseInjection.tInvIdealAngle *
              (HammingWeight
                (PauliSymplectic.bitstringWordEquiv PhysicalSite bits) : Real)) *
          (OneQubitMagic.phaseAmplitude
              (Real.pi / 4 *
                (HammingWeight
                  (PauliSymplectic.bitstringWordEquiv PhysicalSite bits) : Real)) *
            HH18PuncturedReedMuller.physicalTInv 0 4 psi bits) := by
              rw [← mul_assoc, ← OneQubitMagic.phaseAmplitude_add]
              have hangle :
                  HH18PhaseInjection.tInvIdealAngle *
                        (HammingWeight
                          (PauliSymplectic.bitstringWordEquiv PhysicalSite bits) : Real) +
                      Real.pi / 4 *
                        (HammingWeight
                          (PauliSymplectic.bitstringWordEquiv PhysicalSite bits) : Real) =
                    0 := by
                unfold HH18PhaseInjection.tInvIdealAngle
                ring
              rw [hangle, OneQubitMagic.phaseAmplitude_zero, one_mul]
    _ = OneQubitMagic.phaseAmplitude
          (HH18PhaseInjection.tInvIdealAngle *
            (HammingWeight
              (PauliSymplectic.bitstringWordEquiv PhysicalSite bits) : Real)) *
        psi bits := by rw [hcoordinate]

/-- Coordinate formula for the full tensor lift before identifying the HH18 target branch. -/
theorem sitewiseCorrectedTInvAttempt_apply
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord)
    (psi : QubitRegister PhysicalSite) (bits : Bitstring PhysicalSite) :
    sitewiseCorrectedTInvAttempt error outcomes psi bits =
      sitewiseTInvGlobalPhase error outcomes *
        Qubit.zSupportPhase (PauliSymplectic.binarySupport error) bits *
          OneQubitMagic.phaseAmplitude
            (HH18PhaseInjection.tInvIdealAngle *
              (HammingWeight
                (PauliSymplectic.bitstringWordEquiv PhysicalSite bits) : Real)) *
            psi bits := by
  classical
  change
    (∏ i, correctedTInvBasisAmplitude (error i) (outcomes i) (bits i)) *
      psi bits = _
  simp_rw [correctedTInvBasisAmplitude_eq]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    errorPhaseProduct_eq_zSupportPhase,
    phaseAmplitudeProduct_eq_hammingWeight]
  simp only [sitewiseTInvGlobalPhase]

/-- The actual finite corrected-injection register is the existing physical error branch, up to its explicit scalar. -/
theorem sitewiseCorrectedTInvAttempt_eq_zErrorOperator
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) :
    sitewiseCorrectedTInvAttempt error outcomes
        HH18NoisyInput.hh18EncodedLogicalPlusInput =
      sitewiseTInvGlobalPhase error outcomes •
        HH18NoisyInput.zErrorOperator error
          HH18NoisyInput.hh18PhysicalTInvBranch := by
  ext bits
  rw [sitewiseCorrectedTInvAttempt_apply]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [zErrorOperator_apply, HH18NoisyInput.hh18PhysicalTInvBranch,
    physicalTInv_apply]
  ring

/-- Named form of the same equality using the target family from `HH18NoisyInput`. -/
theorem sitewiseCorrectedTInvAttempt_eq_errorBranch
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) :
    sitewiseCorrectedTInvAttempt error outcomes
        HH18NoisyInput.hh18EncodedLogicalPlusInput =
      sitewiseTInvGlobalPhase error outcomes •
        HH18NoisyInput.hh18PhysicalTInvErrorBranch error := by
  simpa only [HH18NoisyInput.hh18PhysicalTInvErrorBranch] using
    sitewiseCorrectedTInvAttempt_eq_zErrorOperator error outcomes

private theorem oneShotAttemptGlobalPhase_mul_conj
    (theta : Real) (coin : Bool) :
    PhaseInjection.oneShotAttemptGlobalPhase theta coin *
      star (PhaseInjection.oneShotAttemptGlobalPhase theta coin) = 1 := by
  cases coin
  · simp only [PhaseInjection.oneShotAttemptGlobalPhase,
      PhaseInjection.observedRetryOutcome,
      PhaseInjection.sourceOutcomeGlobalPhase]
    exact OneQubitMagic.phaseAmplitude_mul_conj theta
  · simp [PhaseInjection.oneShotAttemptGlobalPhase,
      PhaseInjection.observedRetryOutcome,
      PhaseInjection.sourceOutcomeGlobalPhase]

/-- The explicit finite product scalar has unit modulus. -/
theorem sitewiseTInvGlobalPhase_mul_conj
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) :
    sitewiseTInvGlobalPhase error outcomes *
      star (sitewiseTInvGlobalPhase error outcomes) = 1 := by
  classical
  unfold sitewiseTInvGlobalPhase
  rw [star_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _hi
  exact oneShotAttemptGlobalPhase_mul_conj
    (tInvResourceAngle (error i)) (outcomes i)

private theorem rankOne_global_phase
    (z : Complex) (psi : QubitRegister PhysicalSite)
    (hz : z * star z = 1) :
    (InnerProductSpace.rankOne Complex (z • psi) (z • psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  ext x bits
  change
    ((InnerProductSpace.rankOne Complex (z • psi) (z • psi)).toLinearMap x) bits =
      ((InnerProductSpace.rankOne Complex psi psi).toLinearMap x) bits
  change (inner Complex (z • psi) x) * (z • psi) bits =
    (inner Complex psi x) * psi bits
  simp only [PiLp.smul_apply, inner_smul_left, smul_eq_mul]
  calc
    (star z * inner Complex psi x) * (z * psi bits) =
        (z * star z) * inner Complex psi x * psi bits := by ring
    _ = inner Complex psi x * psi bits := by rw [hz]; ring

/-- The finite branch scalar cancels exactly in the rank-one pure-density operator. -/
theorem sitewiseCorrectedTInvAttempt_rankOne
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) :
    (InnerProductSpace.rankOne Complex
      (sitewiseCorrectedTInvAttempt error outcomes
        HH18NoisyInput.hh18EncodedLogicalPlusInput)
      (sitewiseCorrectedTInvAttempt error outcomes
        HH18NoisyInput.hh18EncodedLogicalPlusInput)).toLinearMap =
    (InnerProductSpace.rankOne Complex
      (HH18NoisyInput.hh18PhysicalTInvErrorBranch error)
      (HH18NoisyInput.hh18PhysicalTInvErrorBranch error)).toLinearMap := by
  rw [sitewiseCorrectedTInvAttempt_eq_errorBranch]
  exact rankOne_global_phase
    (sitewiseTInvGlobalPhase error outcomes)
    (HH18NoisyInput.hh18PhysicalTInvErrorBranch error)
    (sitewiseTInvGlobalPhase_mul_conj error outcomes)

end HH18SitewisePhaseInjection
end Distillation
end QEC
