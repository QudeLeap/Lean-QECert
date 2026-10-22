import QEC.Distillation.LowOverheadProtocol.Parameterized.Preparation
import QEC.Distillation.LowOverheadProtocol.Core.PhaseInjection

/-!
# Parameterized HH18 sitewise phase injection

The established one-qubit corrected `T†` injection is tensorized over the
actual finite physical-site type of a parameterized HH18 block.  The result is
identified, branch by branch and up to its explicit global phase, with the
physical Pauli-`Z` error branch of the constructed transversal target.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

/-- One visible corrected-injection measurement outcome at every physical site. -/
abbrev InjectionOutcomeWord (m w : Nat) := PhysicalSite m w → Bool

/-- The phase-state angle selected by one binary resource error. -/
def tInvResourceAngle (error : ZMod 2) : Real :=
  if error = 0 then HH18PhaseInjection.tInvIdealAngle
  else HH18PhaseInjection.tInvErrorAngle

/-- The established corrected one-qubit injection attempt selected by a
binary resource error. -/
noncomputable def correctedTInvAttempt (error : ZMod 2) (psi : QubitSpace)
    (hpsi : ‖psi‖ = 1) (coin : Bool) : QubitSpace :=
  if error = 0 then
    HH18PhaseInjection.correctedIdealTInvAttempt psi hpsi coin
  else
    HH18PhaseInjection.correctedErroredTInvAttempt psi hpsi coin

/-- Binary error selection specializes the established ideal/error covariance
of the one-qubit corrected injection circuit. -/
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

/-- Each local diagonal entry is its measured scalar, resource-error sign,
and ideal `T†` phase. -/
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
      simp [tInvResourceAngle, EuclideanSpace.basisFun_apply]

/-- The sole register-wide vector scalar: the finite product of actual branch
scalars on the physical-site type. -/
noncomputable def sitewiseTInvGlobalPhase {m w : Nat}
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w) : Complex :=
  ∏ i, PhaseInjection.oneShotAttemptGlobalPhase
    (tInvResourceAngle (error i)) (outcomes i)

/-- The finite diagonal tensor lift of the corrected one-qubit attempts. -/
noncomputable def sitewiseCorrectedTInvAttempt {m w : Nat}
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w)
    (psi : PhysicalRegister m w) : PhysicalRegister m w :=
  WithLp.toLp 2 fun bits =>
    (∏ i, correctedTInvBasisAmplitude (error i) (outcomes i) (bits i)) *
      psi bits

private theorem errorPhaseProduct_eq_zSupportPhase {m w : Nat}
    (error : PhysicalErrorWord m w) (bits : Bitstring (PhysicalSite m w)) :
    (∏ i, if error i = 0 then 1 else zPhase (bits i)) =
      Qubit.zSupportPhase (PauliSymplectic.binarySupport error) bits := by
  classical
  rw [Qubit.zSupportPhase, PauliSymplectic.binarySupport,
    Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _hi
  by_cases herror : error i = 0 <;> simp [herror]

private theorem bitValueSum_eq_hammingWeight {m w : Nat}
    (bits : Bitstring (PhysicalSite m w)) :
    (∑ i, (bits i).val) =
      HammingWeight
        (PauliSymplectic.bitstringWordEquiv (PhysicalSite m w) bits) := by
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

private theorem phaseAmplitudeProduct_eq_hammingWeight {m w : Nat}
    (bits : Bitstring (PhysicalSite m w)) :
    (∏ i, OneQubitMagic.phaseAmplitude
      (HH18PhaseInjection.tInvIdealAngle * (bits i).val)) =
      OneQubitMagic.phaseAmplitude
        (HH18PhaseInjection.tInvIdealAngle *
          (HammingWeight
            (PauliSymplectic.bitstringWordEquiv (PhysicalSite m w) bits) : Real)) := by
  classical
  have hcombine (s : Finset (PhysicalSite m w)) :
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
theorem zErrorOperator_apply {m w : Nat} (error : PhysicalErrorWord m w)
    (psi : PhysicalRegister m w) (bits : Bitstring (PhysicalSite m w)) :
    HH18NoisyInput.zErrorOperator error psi bits =
      Qubit.zSupportPhase (PauliSymplectic.binarySupport error) bits * psi bits := by
  rw [HH18NoisyInput.zErrorOperator,
    PauliSymplectic.toQubitOperator_apply]
  simp [PauliSymplectic.xSupport, PauliSymplectic.zSupport]

/-- The inverse physical HH18 transport has the negative all-site phase
coordinates on every finite physical-site type. -/
theorem physicalTInv_apply (m w : Nat) (psi : PhysicalRegister m w)
    (bits : Bitstring (PhysicalSite m w)) :
    HH18PuncturedReedMuller.physicalTInv w m psi bits =
      OneQubitMagic.phaseAmplitude
          (HH18PhaseInjection.tInvIdealAngle *
            (HammingWeight
              (PauliSymplectic.bitstringWordEquiv (PhysicalSite m w) bits) : Real)) *
        psi bits := by
  have hinverse :
      HH18PuncturedReedMuller.physicalT w m
          (HH18PuncturedReedMuller.physicalTInv w m psi) = psi := by
    change (HH18PuncturedReedMuller.physicalT w m).toLinearEquiv
      ((HH18PuncturedReedMuller.physicalT w m).toLinearEquiv.symm psi) = psi
    exact (HH18PuncturedReedMuller.physicalT w m).toLinearEquiv.apply_symm_apply psi
  have hcoordinate :=
    congrArg (fun state : PhysicalRegister m w => state bits) hinverse
  rw [HH18PuncturedReedMuller.physicalT_eq_allSiteT] at hcoordinate
  change Triorthogonal.allSiteT
      (HH18PuncturedReedMuller.physicalTInv w m psi) bits = psi bits
    at hcoordinate
  rw [Triorthogonal.allSiteT_apply] at hcoordinate
  calc
    HH18PuncturedReedMuller.physicalTInv w m psi bits =
        OneQubitMagic.phaseAmplitude
            (HH18PhaseInjection.tInvIdealAngle *
              (HammingWeight
                (PauliSymplectic.bitstringWordEquiv (PhysicalSite m w) bits) : Real)) *
          (OneQubitMagic.phaseAmplitude
              (Real.pi / 4 *
                (HammingWeight
                  (PauliSymplectic.bitstringWordEquiv (PhysicalSite m w) bits) : Real)) *
            HH18PuncturedReedMuller.physicalTInv w m psi bits) := by
              rw [← mul_assoc, ← OneQubitMagic.phaseAmplitude_add]
              have hangle :
                  HH18PhaseInjection.tInvIdealAngle *
                        (HammingWeight
                          (PauliSymplectic.bitstringWordEquiv (PhysicalSite m w) bits) : Real) +
                      Real.pi / 4 *
                        (HammingWeight
                          (PauliSymplectic.bitstringWordEquiv (PhysicalSite m w) bits) : Real) =
                    0 := by
                unfold HH18PhaseInjection.tInvIdealAngle
                ring
              rw [hangle, OneQubitMagic.phaseAmplitude_zero, one_mul]
    _ = OneQubitMagic.phaseAmplitude
          (HH18PhaseInjection.tInvIdealAngle *
            (HammingWeight
              (PauliSymplectic.bitstringWordEquiv (PhysicalSite m w) bits) : Real)) *
        psi bits := by rw [hcoordinate]

/-- Coordinate formula for the full tensor lift before identifying the HH18
target branch. -/
theorem sitewiseCorrectedTInvAttempt_apply {m w : Nat}
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w)
    (psi : PhysicalRegister m w) (bits : Bitstring (PhysicalSite m w)) :
    sitewiseCorrectedTInvAttempt error outcomes psi bits =
      sitewiseTInvGlobalPhase error outcomes *
        Qubit.zSupportPhase (PauliSymplectic.binarySupport error) bits *
          OneQubitMagic.phaseAmplitude
            (HH18PhaseInjection.tInvIdealAngle *
              (HammingWeight
                (PauliSymplectic.bitstringWordEquiv (PhysicalSite m w) bits) : Real)) *
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

/-- The actual finite corrected injection is the constructed physical
error branch, up to its explicit global phase. -/
theorem sitewiseCorrectedTInvAttempt_eq_zErrorOperator {w r m : Nat}
    (h : Coding.PuncturedReedMuller.Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w) :
    sitewiseCorrectedTInvAttempt error outcomes (encodedLogicalPlus h) =
      sitewiseTInvGlobalPhase error outcomes •
        HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree) := by
  ext bits
  rw [sitewiseCorrectedTInvAttempt_apply]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [zErrorOperator_apply, physicalTInvBranch, physicalTInv_apply]
  ring

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
theorem sitewiseTInvGlobalPhase_mul_conj {m w : Nat}
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w) :
    sitewiseTInvGlobalPhase error outcomes *
      star (sitewiseTInvGlobalPhase error outcomes) = 1 := by
  classical
  unfold sitewiseTInvGlobalPhase
  rw [star_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _hi
  exact oneShotAttemptGlobalPhase_mul_conj
    (tInvResourceAngle (error i)) (outcomes i)

private theorem rankOne_global_phase {m w : Nat}
    (z : Complex) (psi : PhysicalRegister m w) (hz : z * star z = 1) :
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

/-- The finite branch scalar cancels exactly in the rank-one pure-density
operator of the actual parameterized injection branch. -/
theorem sitewiseCorrectedTInvAttempt_rankOne {w r m : Nat}
    (h : Coding.PuncturedReedMuller.Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w) :
    (InnerProductSpace.rankOne Complex
      (sitewiseCorrectedTInvAttempt error outcomes (encodedLogicalPlus h))
      (sitewiseCorrectedTInvAttempt error outcomes (encodedLogicalPlus h))).toLinearMap =
      (InnerProductSpace.rankOne Complex
        (HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree))
        (HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree))).toLinearMap := by
  rw [sitewiseCorrectedTInvAttempt_eq_zErrorOperator h hdegree]
  exact rankOne_global_phase
    (sitewiseTInvGlobalPhase error outcomes)
    (HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree))
    (sitewiseTInvGlobalPhase_mul_conj error outcomes)

end HH18Parameterized
end Distillation
end QEC
