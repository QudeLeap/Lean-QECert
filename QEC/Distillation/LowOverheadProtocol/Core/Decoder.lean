import QEC.Distillation.LowOverheadProtocol.Core.PhysicalTypes
import QEC.Semantics.Core.OperatorTraceNorm
import QEC.Semantics.Entropy.Purification
/-!
# HH18 total decoder and ideal output

The decoder is a complete finite-Kraus channel: inverse encoding on the actual
carrier with a neutral fallback on its orthogonal complement.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Protocol

open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

def ambientEncodingIsometry : LogicalRegister →ₗᵢ[Complex] PhysicalRegister :=
  HH18NoisyInput.hh18_15_1_0_encodedCode.code.carrier.subtypeₗᵢ.comp
    HH18NoisyInput.hh18_15_1_0_encodedCode.encoding.toLinearIsometry

@[simp] theorem ambientEncodingIsometry_apply (psi : LogicalRegister) :
    ambientEncodingIsometry psi =
      (HH18NoisyInput.hh18_15_1_0_encodedCode.encoding psi : PhysicalRegister) :=
  rfl

/-- Coherent inverse encoding on the actual HH18 code carrier. -/
def codeDecoderBranch : PhysicalRegister →ₗ[Complex] LogicalRegister :=
  LinearMap.adjoint ambientEncodingIsometry.toLinearMap

@[simp] theorem codeDecoderBranch_encoded (psi : LogicalRegister) :
    codeDecoderBranch (ambientEncodingIsometry psi) = psi := by
  change LinearMap.adjoint ambientEncodingIsometry.toLinearMap
    (ambientEncodingIsometry.toLinearMap psi) = psi
  exact LinearMap.congr_fun ambientEncodingIsometry.adjoint_comp_self' psi

theorem adjoint_codeDecoderBranch : LinearMap.adjoint codeDecoderBranch =
    ambientEncodingIsometry.toLinearMap := by
  rw [codeDecoderBranch, LinearMap.adjoint_adjoint]

/-- Projector onto the carrier which is decoded coherently. -/
def decoderCodeProjector : Operator PhysicalRegister :=
  (LinearMap.adjoint codeDecoderBranch).comp codeDecoderBranch

@[simp] theorem decoderCodeProjector_encoded (psi : LogicalRegister) :
    decoderCodeProjector (ambientEncodingIsometry psi) = ambientEncodingIsometry psi := by
  change LinearMap.adjoint codeDecoderBranch
    (codeDecoderBranch (ambientEncodingIsometry psi)) = ambientEncodingIsometry psi
  rw [codeDecoderBranch_encoded, adjoint_codeDecoderBranch]
  rfl

theorem codeDecoderBranch_comp_adjoint :
    codeDecoderBranch.comp (LinearMap.adjoint codeDecoderBranch) = 1 := by
  rw [adjoint_codeDecoderBranch, codeDecoderBranch]
  exact ambientEncodingIsometry.adjoint_comp_self'

theorem decoderCodeProjector_idempotent :
    decoderCodeProjector.comp decoderCodeProjector = decoderCodeProjector := by
  rw [decoderCodeProjector]
  calc
    ((LinearMap.adjoint codeDecoderBranch).comp codeDecoderBranch).comp
        ((LinearMap.adjoint codeDecoderBranch).comp codeDecoderBranch) =
      (LinearMap.adjoint codeDecoderBranch).comp
        ((codeDecoderBranch.comp (LinearMap.adjoint codeDecoderBranch)).comp
          codeDecoderBranch) := by
            ext psi
            rfl
    _ = (LinearMap.adjoint codeDecoderBranch).comp
          ((1 : Operator LogicalRegister).comp codeDecoderBranch) := by
            rw [codeDecoderBranch_comp_adjoint]
    _ = (LinearMap.adjoint codeDecoderBranch).comp codeDecoderBranch := by
      ext psi
      rfl

theorem decoderCodeProjector_adjoint :
    LinearMap.adjoint decoderCodeProjector = decoderCodeProjector := by
  simp [decoderCodeProjector, LinearMap.adjoint_comp]

/-- Orthogonal complement routed through the total-decoder fallback. -/
def decoderComplementProjector : Operator PhysicalRegister := 1 - decoderCodeProjector

theorem decoderComplementProjector_adjoint :
    LinearMap.adjoint decoderComplementProjector = decoderComplementProjector := by
  simp [decoderComplementProjector, decoderCodeProjector_adjoint]

theorem decoderComplementProjector_idempotent :
    decoderComplementProjector.comp decoderComplementProjector = decoderComplementProjector := by
  ext psi
  have hprojector := LinearMap.congr_fun decoderCodeProjector_idempotent psi
  simp only [decoderComplementProjector, LinearMap.comp_apply,
    LinearMap.sub_apply, Module.End.one_apply, map_sub] at hprojector ⊢
  rw [hprojector]
  abel_nf

@[simp] theorem decoderComplementProjector_encoded (psi : LogicalRegister) :
    decoderComplementProjector (ambientEncodingIsometry psi) = 0 := by
  simp only [decoderComplementProjector, LinearMap.sub_apply, Module.End.one_apply]
  rw [decoderCodeProjector_encoded]
  abel_nf

/-- Neutral logical fallback used only when an input is off the HH18 carrier. -/
noncomputable def decoderFallbackState : LogicalRegister :=
  EuclideanSpace.basisFun (Bitstring (HH18PuncturedReedMuller.LogicalSite 4 0)) Complex
    (fun _ => 0)

theorem decoderFallbackState_inner_self :
    inner Complex decoderFallbackState decoderFallbackState = 1 := by
  simp [decoderFallbackState]

private theorem decoderFallbackState_normSq : ‖decoderFallbackState‖ ^ 2 = 1 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex), decoderFallbackState_inner_self]
  norm_num

private noncomputable def decoderPhysicalBasis :=
  stdOrthonormalBasis Complex PhysicalRegister

/-- One finite complement branch sends a projected basis component to the
neutral logical fallback. -/
def complementDecoderBranch
    (i : Fin (Module.finrank Complex PhysicalRegister)) :
    PhysicalRegister →ₗ[Complex] LogicalRegister :=
  (InnerProductSpace.rankOne Complex decoderFallbackState
    (decoderComplementProjector (decoderPhysicalBasis i))).toLinearMap

theorem complementDecoderBranch_adjoint_comp
    (i : Fin (Module.finrank Complex PhysicalRegister)) :
    (LinearMap.adjoint (complementDecoderBranch i)).comp (complementDecoderBranch i) =
      (InnerProductSpace.rankOne Complex
        (decoderComplementProjector (decoderPhysicalBasis i))
        (decoderComplementProjector (decoderPhysicalBasis i))).toLinearMap := by
  have hadjoint : LinearMap.adjoint
      ((InnerProductSpace.rankOne Complex decoderFallbackState
        (decoderComplementProjector (decoderPhysicalBasis i))).toLinearMap) =
      (InnerProductSpace.rankOne Complex
        (decoderComplementProjector (decoderPhysicalBasis i))
        decoderFallbackState).toLinearMap := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex decoderFallbackState
      (decoderComplementProjector (decoderPhysicalBasis i))).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  apply LinearMap.ext
  intro psi
  simp only [complementDecoderBranch]
  rw [hadjoint]
  have hnormSq : (↑‖decoderFallbackState‖ : Complex) ^ 2 = 1 := by
    norm_cast
    exact decoderFallbackState_normSq
  simp [LinearMap.comp_apply, hnormSq]

theorem sum_complementDecoderBranch_adjoint_comp :
    ∑ i : Fin (Module.finrank Complex PhysicalRegister),
      (LinearMap.adjoint (complementDecoderBranch i)).comp (complementDecoderBranch i) =
        decoderComplementProjector := by
  simp_rw [complementDecoderBranch_adjoint_comp]
  calc
    (∑ i, (InnerProductSpace.rankOne Complex
      (decoderComplementProjector (decoderPhysicalBasis i))
      (decoderComplementProjector (decoderPhysicalBasis i))).toLinearMap) =
      decoderComplementProjector.comp (LinearMap.adjoint decoderComplementProjector) := by
        apply LinearMap.ext
        intro psi
        simp only [LinearMap.sum_apply, LinearMap.comp_apply]
        rw [← decoderPhysicalBasis.sum_repr'
          (LinearMap.adjoint decoderComplementProjector psi)]
        simp only [map_sum, map_smul]
        apply Finset.sum_congr rfl
        intro i _
        rw [LinearMap.adjoint_inner_right]
        rfl
    _ = decoderComplementProjector.comp decoderComplementProjector := by
      rw [decoderComplementProjector_adjoint]
    _ = decoderComplementProjector := decoderComplementProjector_idempotent

/-- Finite Kraus completion of inverse encoding to a physical, total HH18
decoder. -/
def decoderKrausFamily :
    FiniteKrausFamily (Sum Unit (Fin (Module.finrank Complex PhysicalRegister)))
      PhysicalRegister LogicalRegister where
  operator
    | .inl _ => codeDecoderBranch
    | .inr i => complementDecoderBranch i

theorem decoderKrausFamily_complete : decoderKrausFamily.Complete := by
  rw [FiniteKrausFamily.Complete, Fintype.sum_sum_type]
  change (∑ _ : Unit, decoderCodeProjector) +
      (∑ i : Fin (Module.finrank Complex PhysicalRegister),
        (LinearMap.adjoint (complementDecoderBranch i)).comp (complementDecoderBranch i)) = 1
  rw [Fintype.sum_unique, sum_complementDecoderBranch_adjoint_comp]
  simp [decoderComplementProjector]

/-- The actual CPTP HH18 decoder: inverse encoding on the code carrier and a
neutral finite-Kraus fallback off it. -/
noncomputable def decoderChannel : QuantumChannel PhysicalRegister LogicalRegister :=
  decoderKrausFamily.toQuantumChannel decoderKrausFamily_complete

private theorem sandwich_rankOne {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (L : H →ₗ[Complex] K) (psi : H) :
    L.comp ((InnerProductSpace.rankOne Complex psi psi).toLinearMap.comp
      (LinearMap.adjoint L)) =
      (InnerProductSpace.rankOne Complex (L psi) (L psi)).toLinearMap := by
  ext x
  simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    LinearMap.adjoint_inner_right]

theorem decoderChannel_rankOne_encoded (psi : LogicalRegister) :
    decoderChannel (InnerProductSpace.rankOne Complex
      (ambientEncodingIsometry psi) (ambientEncodingIsometry psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  rw [decoderChannel, FiniteKrausFamily.toQuantumChannel_apply_sum,
    Fintype.sum_sum_type]
  simp only [decoderKrausFamily]
  simp_rw [sandwich_rankOne]
  rw [Fintype.sum_unique]
  simp only [codeDecoderBranch_encoded]
  have hcomplement : ∀ i, complementDecoderBranch i (ambientEncodingIsometry psi) = 0 := by
    intro i
    have hinner : inner Complex (decoderComplementProjector (decoderPhysicalBasis i))
        (ambientEncodingIsometry psi) = 0 := by
      rw [← LinearMap.adjoint_inner_right, decoderComplementProjector_adjoint,
        decoderComplementProjector_encoded]
      simp
    change inner Complex (decoderComplementProjector (decoderPhysicalBasis i))
      (ambientEncodingIsometry psi) • decoderFallbackState = 0
    rw [hinner]
    simp
  simp_rw [hcomplement]
  simp
/-- The source-selected logical ideal is the actual #759 logical `T` action
on its logical plus input, in the physical `T-dagger` orientation. -/
noncomputable def idealLogicalTOutputState : LogicalRegister :=
  HH18PuncturedReedMuller.logicalT 0 4 HH18NoisyInput.hh18LogicalPlusInput

private theorem idealLogicalTOutputState_normSq : ‖idealLogicalTOutputState‖ ^ 2 = 1 := by
  have hnorm : ‖idealLogicalTOutputState‖ = 1 := by
    change ‖(HH18PuncturedReedMuller.logicalT 0 4).toLinearIsometryEquiv
      HH18NoisyInput.hh18LogicalPlusInput‖ = 1
    rw [(HH18PuncturedReedMuller.logicalT 0 4).toLinearIsometryEquiv.norm_map]
    exact hh18LogicalPlusInput_norm
  rw [hnorm]
  norm_num

/-- Ideal logical output density used by the real postselected protocol
package. -/
noncomputable def idealLogicalTOutput : DensityOperator LogicalRegister :=
  DensityOperator.pureDensity idealLogicalTOutputState idealLogicalTOutputState_normSq

/-- State-dependent trace-norm error of the decoded physical output relative
to its source-selected logical `T` target. -/
noncomputable def hh18OutputTraceError
    (rho sigma : DensityOperator LogicalRegister) : ℝ :=
  traceNorm (rho.toOperator - sigma.toOperator)

theorem hh18OutputTraceError_nonneg
    (rho sigma : DensityOperator LogicalRegister) :
    0 ≤ hh18OutputTraceError rho sigma :=
  traceNorm_nonneg _

end HH18Protocol
end Distillation
end QEC
