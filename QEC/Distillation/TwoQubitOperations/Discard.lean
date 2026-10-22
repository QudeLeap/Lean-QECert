import QEC.Distillation.TwoQubitOperations.ParityBranches
import QEC.Semantics.ErrorCorrection.QuditSubsystem
noncomputable section

namespace QEC
namespace Distillation
namespace TwoQubit

open Semantics Semantics.Qubit
open scoped InnerProductSpace TensorProduct

noncomputable def secondQubitDiscard :
    QuantumChannel TwoQubitSpace QubitSpace :=
  QuantumChannel.comp
    (partialTraceRightRaw_cptp QubitSpace QubitSpace)
    (QuantumChannel.unitaryConj tensorRegisterTransport.symm)

@[simp] theorem secondQubitDiscard_apply (A : Operator TwoQubitSpace) :
    secondQubitDiscard A =
      partialTraceRightRaw QubitSpace QubitSpace
        (tensorRegisterTransport.symm.conjOperator A) :=
  rfl

def zzEvenBranchFirstQubit
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    QubitSpace :=
  WithLp.toLp 2 (fun a =>
    zzEvenBranchState psi h
      (pairBitstring (a, controlledXBit a 0)))

def zzOddBranchFirstQubit
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi) :
    QubitSpace :=
  WithLp.toLp 2 (fun a =>
    zzOddBranchState psi h
      (pairBitstring (a, controlledXBit a 1)))

private theorem xorTransport_apply_coordinate
    (psi : TwoQubitSpace) (bits : Bitstring (Fin 2)) :
    xorTransport psi bits = psi (xorBitstring bits) := by
  have hinner := xorTransport.map_inner
    (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex
      (xorBitstring bits)) psi
  change
    inner Complex
        (xorTransport
          (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex
            (xorBitstring bits)))
        (xorTransport psi) =
      inner Complex
        (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex
          (xorBitstring bits))
        psi at hinner
  rw [xorTransport_apply_basis, xorBitstring_involutive] at hinner
  rw [EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner

private theorem tensorRegisterTransport_apply_tmul_coordinate
    (x y : QubitSpace) (bits : Bitstring (Fin 2)) :
    tensorRegisterTransport (x ⊗ₜ[Complex] y) bits =
      x (bits 0) * y (bits 1) := by
  have hinner := tensorRegisterTransport.map_inner
    (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
      EuclideanSpace.basisFun (Fin 2) Complex (bits 1))
    (x ⊗ₜ[Complex] y)
  change
    inner Complex
        (tensorRegisterTransport
          (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex (bits 1)))
        (tensorRegisterTransport (x ⊗ₜ[Complex] y)) =
      inner Complex
        (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
          EuclideanSpace.basisFun (Fin 2) Complex (bits 1))
        (x ⊗ₜ[Complex] y) at hinner
  rw [tensorRegisterTransport_apply_basis] at hinner
  have hp : pairBitstring (bits 0, bits 1) = bits := by
    simpa only [splitBitstring] using pair_splitBitstring bits
  rw [hp] at hinner
  rw [EuclideanSpace.basisFun_inner, TensorProduct.inner_tmul,
    EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner

private theorem zzEvenBranchState_apply_of_ne
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi)
    (bits : Bitstring (Fin 2)) (hbits : bits 0 ≠ bits 1) :
    zzEvenBranchState psi h bits = 0 := by
  have hfixed := congrArg
    (fun state : TwoQubitSpace => state bits)
    (zzEvenProjector_branchState psi h)
  unfold zzEvenProjector at hfixed
  simp only [LinearMap.smul_apply, LinearMap.add_apply,
    Module.End.one_apply] at hfixed
  generalize hfirst : bits 0 = firstBit at hfixed hbits
  generalize hsecond : bits 1 = secondBit at hfixed hbits
  fin_cases firstBit <;> fin_cases secondBit <;>
    simp_all [zPhase]

private theorem zzOddBranchState_apply_of_eq
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi)
    (bits : Bitstring (Fin 2)) (hbits : bits 0 = bits 1) :
    zzOddBranchState psi h bits = 0 := by
  have hfixed := congrArg
    (fun state : TwoQubitSpace => state bits)
    (zzOddProjector_branchState psi h)
  have hphase : zPhase (bits 0) * zPhase (bits 1) = 1 := by
    rw [← hbits]
    generalize bits 0 = bit
    fin_cases bit <;> norm_num [zPhase]
  simp only [zzOddProjector, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.one_apply] at hfixed
  change (2 : Complex)⁻¹ *
      (zzOddBranchState psi h bits -
        zzOperator (zzOddBranchState psi h) bits) =
    zzOddBranchState psi h bits at hfixed
  rw [zzOperator_apply, hphase, one_mul, sub_self, mul_zero] at hfixed
  exact hfixed.symm

theorem xorTransport_zzEvenBranchState_factorized
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    tensorRegisterTransport.symm
        (xorTransport (zzEvenBranchState psi h)) =
      zzEvenBranchFirstQubit psi h ⊗ₜ[Complex]
        EuclideanSpace.basisFun (Fin 2) Complex 0 := by
  apply tensorRegisterTransport.toLinearEquiv.injective
  change tensorRegisterTransport.toLinearEquiv
      (tensorRegisterTransport.toLinearEquiv.symm
        (xorTransport (zzEvenBranchState psi h))) =
    _
  rw [tensorRegisterTransport.toLinearEquiv.apply_symm_apply]
  ext bits
  rw [xorTransport_apply_coordinate]
  rw [tensorRegisterTransport_apply_tmul_coordinate]
  generalize hfirst : bits 0 = firstBit
  generalize hsecond : bits 1 = secondBit
  fin_cases firstBit <;> fin_cases secondBit <;>
    simp_all [zzEvenBranchFirstQubit, xorBitstring, controlledXBit,
      zzEvenBranchState_apply_of_ne]

theorem xorTransport_zzOddBranchState_factorized
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi) :
    tensorRegisterTransport.symm
        (xorTransport (zzOddBranchState psi h)) =
      zzOddBranchFirstQubit psi h ⊗ₜ[Complex]
        EuclideanSpace.basisFun (Fin 2) Complex 1 := by
  apply tensorRegisterTransport.toLinearEquiv.injective
  change tensorRegisterTransport.toLinearEquiv
      (tensorRegisterTransport.toLinearEquiv.symm
        (xorTransport (zzOddBranchState psi h))) =
    _
  rw [tensorRegisterTransport.toLinearEquiv.apply_symm_apply]
  ext bits
  rw [xorTransport_apply_coordinate]
  rw [tensorRegisterTransport_apply_tmul_coordinate]
  generalize hfirst : bits 0 = firstBit
  generalize hsecond : bits 1 = secondBit
  fin_cases firstBit <;> fin_cases secondBit <;>
    simp_all [zzOddBranchFirstQubit, xorBitstring, controlledXBit,
      zzOddBranchState_apply_of_eq]

private theorem firstQubit_norm_of_factorized
    (branchState : TwoQubitSpace) (firstQubit : QubitSpace)
    (target : Fin 2)
    (hfactorized :
      tensorRegisterTransport.symm (xorTransport branchState) =
        firstQubit ⊗ₜ[Complex]
          EuclideanSpace.basisFun (Fin 2) Complex target)
    (hbranchState_norm : ‖branchState‖ = 1) :
    ‖firstQubit‖ = 1 := by
  calc
    ‖firstQubit‖ =
        ‖firstQubit ⊗ₜ[Complex]
          EuclideanSpace.basisFun (Fin 2) Complex target‖ := by
            simp
    _ = ‖tensorRegisterTransport.symm
          (xorTransport branchState)‖ :=
      congrArg norm hfactorized.symm
    _ = ‖xorTransport branchState‖ := by
      change
        ‖tensorRegisterTransport.symm.toLinearIsometryEquiv
          (xorTransport branchState)‖ = _
      rw [tensorRegisterTransport.symm.toLinearIsometryEquiv.norm_map]
    _ = ‖branchState‖ := by
      change ‖xorTransport.toLinearIsometryEquiv branchState‖ = _
      rw [xorTransport.toLinearIsometryEquiv.norm_map]
    _ = 1 := hbranchState_norm

@[simp] theorem zzEvenBranchFirstQubit_norm
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    ‖zzEvenBranchFirstQubit psi h‖ = 1 :=
  firstQubit_norm_of_factorized
    (zzEvenBranchState psi h)
    (zzEvenBranchFirstQubit psi h)
    0
    (xorTransport_zzEvenBranchState_factorized psi h)
    (zzEvenBranchState_norm psi h)

@[simp] theorem zzOddBranchFirstQubit_norm
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi) :
    ‖zzOddBranchFirstQubit psi h‖ = 1 :=
  firstQubit_norm_of_factorized
    (zzOddBranchState psi h)
    (zzOddBranchFirstQubit psi h)
    1
    (xorTransport_zzOddBranchState_factorized psi h)
    (zzOddBranchState_norm psi h)

private theorem qubitState_ne_zero_of_norm_one
    (state : QubitSpace) (hstate : ‖state‖ = 1) :
    state ≠ 0 := by
  intro hzero
  rw [hzero, norm_zero] at hstate
  norm_num at hstate

noncomputable def zzEvenBranchFirstDensity
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    DensityOperator QubitSpace :=
  DensityOperator.pureOfNonzero
    (zzEvenBranchFirstQubit psi h)
    (qubitState_ne_zero_of_norm_one
      (zzEvenBranchFirstQubit psi h)
      (zzEvenBranchFirstQubit_norm psi h))

noncomputable def zzOddBranchFirstDensity
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi) :
    DensityOperator QubitSpace :=
  DensityOperator.pureOfNonzero
    (zzOddBranchFirstQubit psi h)
    (qubitState_ne_zero_of_norm_one
      (zzOddBranchFirstQubit psi h)
      (zzOddBranchFirstQubit_norm psi h))

private theorem densityOperator_ext_toOperator
    {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) :
    rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl

private theorem pureOfNonzero_toOperator_of_norm_one
    (state : QubitSpace) (hstate : state ≠ 0)
    (hnorm : ‖state‖ = 1) :
    (DensityOperator.pureOfNonzero state hstate).toOperator =
      (InnerProductSpace.rankOne Complex state state).toLinearMap := by
  rw [DensityOperator.pureOfNonzero_toOperator]
  rw [inner_self_eq_norm_sq_to_K, hnorm]
  norm_num

private theorem zzEvenBranchFirstDensity_toOperator
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    (zzEvenBranchFirstDensity psi h).toOperator =
      (InnerProductSpace.rankOne Complex
        (zzEvenBranchFirstQubit psi h)
        (zzEvenBranchFirstQubit psi h)).toLinearMap := by
  rw [zzEvenBranchFirstDensity]
  exact pureOfNonzero_toOperator_of_norm_one
    (zzEvenBranchFirstQubit psi h)
    (qubitState_ne_zero_of_norm_one
      (zzEvenBranchFirstQubit psi h)
      (zzEvenBranchFirstQubit_norm psi h))
    (zzEvenBranchFirstQubit_norm psi h)

private theorem zzOddBranchFirstDensity_toOperator
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi) :
    (zzOddBranchFirstDensity psi h).toOperator =
      (InnerProductSpace.rankOne Complex
        (zzOddBranchFirstQubit psi h)
        (zzOddBranchFirstQubit psi h)).toLinearMap := by
  rw [zzOddBranchFirstDensity]
  exact pureOfNonzero_toOperator_of_norm_one
    (zzOddBranchFirstQubit psi h)
    (qubitState_ne_zero_of_norm_one
      (zzOddBranchFirstQubit psi h)
      (zzOddBranchFirstQubit_norm psi h))
    (zzOddBranchFirstQubit_norm psi h)

private theorem secondQubitDiscard_rankOne_xor_of_factorized
    (branchState : TwoQubitSpace) (firstQubit : QubitSpace)
    (target : Fin 2)
    (hfactorized :
      tensorRegisterTransport.symm (xorTransport branchState) =
        firstQubit ⊗ₜ[Complex]
          EuclideanSpace.basisFun (Fin 2) Complex target) :
    (QuantumChannel.comp secondQubitDiscard
      (QuantumChannel.unitaryConj xorTransport))
        (InnerProductSpace.rankOne Complex
          branchState branchState).toLinearMap =
      (InnerProductSpace.rankOne Complex
        firstQubit firstQubit).toLinearMap := by
  rw [QuantumChannel.comp_apply, QuantumChannel.unitaryConj_apply]
  rw [QuditSubsystem.conjOperator_rankOne]
  rw [secondQubitDiscard_apply]
  rw [QuditSubsystem.conjOperator_rankOne]
  rw [hfactorized]
  rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  simp

theorem secondQubitDiscard_mapDensity_xor_zzEvenBranchDensity
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    (QuantumChannel.comp secondQubitDiscard
      (QuantumChannel.unitaryConj xorTransport)).mapDensity
        (zzEvenBranchDensity psi h) =
      zzEvenBranchFirstDensity psi h := by
  apply densityOperator_ext_toOperator
  rw [QuantumChannel.mapDensity_toOperator]
  rw [zzEvenBranchDensity_toOperator]
  rw [secondQubitDiscard_rankOne_xor_of_factorized
    (zzEvenBranchState psi h)
    (zzEvenBranchFirstQubit psi h)
    0
    (xorTransport_zzEvenBranchState_factorized psi h)]
  exact (zzEvenBranchFirstDensity_toOperator psi h).symm

theorem secondQubitDiscard_mapDensity_xor_zzOddBranchDensity
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi) :
    (QuantumChannel.comp secondQubitDiscard
      (QuantumChannel.unitaryConj xorTransport)).mapDensity
        (zzOddBranchDensity psi h) =
      zzOddBranchFirstDensity psi h := by
  apply densityOperator_ext_toOperator
  rw [QuantumChannel.mapDensity_toOperator]
  rw [zzOddBranchDensity_toOperator]
  rw [secondQubitDiscard_rankOne_xor_of_factorized
    (zzOddBranchState psi h)
    (zzOddBranchFirstQubit psi h)
    1
    (xorTransport_zzOddBranchState_factorized psi h)]
  exact (zzOddBranchFirstDensity_toOperator psi h).symm

end TwoQubit
end Distillation
end QEC
