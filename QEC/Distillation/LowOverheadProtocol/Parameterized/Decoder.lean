import QEC.Distillation.LowOverheadProtocol.Parameterized.Types
import QEC.Semantics.Core.OperatorTraceNorm
import QEC.Semantics.Entropy.Purification
/-!
# Parameterized HH18 total decoder and ideal output

For every admissible HH18 punctured Reed--Muller block, this module builds a
total finite-Kraus decoder. It applies coherent inverse encoding on the actual
`encodedCode h` carrier and sends only the carrier's orthogonal complement to a
neutral logical fallback. The fallback completes a CPTP channel; it is not an
accepted-history assertion. The module also records the actual logical-`T`
ideal density for the inverse physical-`T` orientation.
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

/-- The actual logical-to-ambient physical carrier isometry of an admissible
parameterized HH18 code. -/
def ambientEncodingIsometry {w r m : Nat} (h : Admissible w r m) :
    LogicalRegister m w →ₗᵢ[Complex] PhysicalRegister m w :=
  (HH18PuncturedReedMuller.encodedCode h).code.carrier.subtypeₗᵢ.comp
    (HH18PuncturedReedMuller.encodedCode h).encoding.toLinearIsometry

@[simp] theorem ambientEncodingIsometry_apply {w r m : Nat}
    (h : Admissible w r m) (psi : LogicalRegister m w) :
    ambientEncodingIsometry h psi =
      ((HH18PuncturedReedMuller.encodedCode h).encoding psi : PhysicalRegister m w) :=
  rfl

/-- Coherent inverse encoding on the actual parameterized HH18 carrier. -/
def codeDecoderBranch {w r m : Nat} (h : Admissible w r m) :
    PhysicalRegister m w →ₗ[Complex] LogicalRegister m w :=
  LinearMap.adjoint (ambientEncodingIsometry h).toLinearMap

@[simp] theorem codeDecoderBranch_encoded {w r m : Nat}
    (h : Admissible w r m) (psi : LogicalRegister m w) :
    codeDecoderBranch h (ambientEncodingIsometry h psi) = psi := by
  change LinearMap.adjoint (ambientEncodingIsometry h).toLinearMap
    ((ambientEncodingIsometry h).toLinearMap psi) = psi
  exact LinearMap.congr_fun (ambientEncodingIsometry h).adjoint_comp_self' psi

theorem adjoint_codeDecoderBranch {w r m : Nat} (h : Admissible w r m) :
    LinearMap.adjoint (codeDecoderBranch h) = (ambientEncodingIsometry h).toLinearMap := by
  rw [codeDecoderBranch, LinearMap.adjoint_adjoint]

/-- Projector onto the code carrier decoded coherently. -/
def decoderCodeProjector {w r m : Nat} (h : Admissible w r m) :
    Operator (PhysicalRegister m w) :=
  (LinearMap.adjoint (codeDecoderBranch h)).comp (codeDecoderBranch h)

@[simp] theorem decoderCodeProjector_encoded {w r m : Nat}
    (h : Admissible w r m) (psi : LogicalRegister m w) :
    decoderCodeProjector h (ambientEncodingIsometry h psi) = ambientEncodingIsometry h psi := by
  change LinearMap.adjoint (codeDecoderBranch h)
    (codeDecoderBranch h (ambientEncodingIsometry h psi)) = ambientEncodingIsometry h psi
  rw [codeDecoderBranch_encoded, adjoint_codeDecoderBranch]
  rfl

theorem codeDecoderBranch_comp_adjoint {w r m : Nat} (h : Admissible w r m) :
    (codeDecoderBranch h).comp (LinearMap.adjoint (codeDecoderBranch h)) = 1 := by
  rw [adjoint_codeDecoderBranch, codeDecoderBranch]
  exact (ambientEncodingIsometry h).adjoint_comp_self'

theorem decoderCodeProjector_idempotent {w r m : Nat} (h : Admissible w r m) :
    (decoderCodeProjector h).comp (decoderCodeProjector h) = decoderCodeProjector h := by
  rw [decoderCodeProjector]
  calc
    ((LinearMap.adjoint (codeDecoderBranch h)).comp (codeDecoderBranch h)).comp
        ((LinearMap.adjoint (codeDecoderBranch h)).comp (codeDecoderBranch h)) =
      (LinearMap.adjoint (codeDecoderBranch h)).comp
        (((codeDecoderBranch h).comp (LinearMap.adjoint (codeDecoderBranch h))).comp
          (codeDecoderBranch h)) := by
            ext psi
            rfl
    _ = (LinearMap.adjoint (codeDecoderBranch h)).comp
          ((1 : Operator (LogicalRegister m w)).comp (codeDecoderBranch h)) := by
            rw [codeDecoderBranch_comp_adjoint]
    _ = (LinearMap.adjoint (codeDecoderBranch h)).comp (codeDecoderBranch h) := by
      ext psi
      rfl

theorem decoderCodeProjector_adjoint {w r m : Nat} (h : Admissible w r m) :
    LinearMap.adjoint (decoderCodeProjector h) = decoderCodeProjector h := by
  simp [decoderCodeProjector, LinearMap.adjoint_comp]

/-- The orthogonal complement routed only through the total-channel fallback. -/
def decoderComplementProjector {w r m : Nat} (h : Admissible w r m) :
    Operator (PhysicalRegister m w) :=
  1 - decoderCodeProjector h

theorem decoderComplementProjector_adjoint {w r m : Nat} (h : Admissible w r m) :
    LinearMap.adjoint (decoderComplementProjector h) = decoderComplementProjector h := by
  simp [decoderComplementProjector, decoderCodeProjector_adjoint]

theorem decoderComplementProjector_idempotent {w r m : Nat} (h : Admissible w r m) :
    (decoderComplementProjector h).comp (decoderComplementProjector h) =
      decoderComplementProjector h := by
  ext psi
  have hprojector := LinearMap.congr_fun (decoderCodeProjector_idempotent h) psi
  simp only [decoderComplementProjector, LinearMap.comp_apply,
    LinearMap.sub_apply, Module.End.one_apply, map_sub] at hprojector ⊢
  rw [hprojector]
  abel_nf

@[simp] theorem decoderComplementProjector_encoded {w r m : Nat}
    (h : Admissible w r m) (psi : LogicalRegister m w) :
    decoderComplementProjector h (ambientEncodingIsometry h psi) = 0 := by
  simp only [decoderComplementProjector, LinearMap.sub_apply, Module.End.one_apply]
  rw [decoderCodeProjector_encoded]
  abel_nf

/-- A neutral logical fallback used solely to complete the decoder off the
code carrier. -/
noncomputable def decoderFallbackState (m w : Nat) : LogicalRegister m w :=
  EuclideanSpace.basisFun (Bitstring (LogicalSite m w)) Complex (fun _ => 0)

theorem decoderFallbackState_inner_self (m w : Nat) :
    inner Complex (decoderFallbackState m w) (decoderFallbackState m w) = 1 := by
  simp [decoderFallbackState]

private theorem decoderFallbackState_normSq (m w : Nat) :
    ‖decoderFallbackState m w‖ ^ 2 = 1 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
    decoderFallbackState_inner_self]
  norm_num

private noncomputable def decoderPhysicalBasis (m w : Nat) :=
  stdOrthonormalBasis Complex (PhysicalRegister m w)

/-- One finite fallback branch sends a projected physical basis component to
the neutral logical fallback. -/
def complementDecoderBranch {w r m : Nat} (h : Admissible w r m)
    (i : Fin (Module.finrank Complex (PhysicalRegister m w))) :
    PhysicalRegister m w →ₗ[Complex] LogicalRegister m w :=
  (InnerProductSpace.rankOne Complex (decoderFallbackState m w)
    (decoderComplementProjector h (decoderPhysicalBasis m w i))).toLinearMap

theorem complementDecoderBranch_adjoint_comp {w r m : Nat} (h : Admissible w r m)
    (i : Fin (Module.finrank Complex (PhysicalRegister m w))) :
    (LinearMap.adjoint (complementDecoderBranch h i)).comp (complementDecoderBranch h i) =
      (InnerProductSpace.rankOne Complex
        (decoderComplementProjector h (decoderPhysicalBasis m w i))
        (decoderComplementProjector h (decoderPhysicalBasis m w i))).toLinearMap := by
  have hadjoint : LinearMap.adjoint
      ((InnerProductSpace.rankOne Complex (decoderFallbackState m w)
        (decoderComplementProjector h (decoderPhysicalBasis m w i))).toLinearMap) =
      (InnerProductSpace.rankOne Complex
        (decoderComplementProjector h (decoderPhysicalBasis m w i))
        (decoderFallbackState m w)).toLinearMap := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex (decoderFallbackState m w)
      (decoderComplementProjector h (decoderPhysicalBasis m w i))).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  apply LinearMap.ext
  intro psi
  simp only [complementDecoderBranch]
  rw [hadjoint]
  have hnormSq : (↑‖decoderFallbackState m w‖ : Complex) ^ 2 = 1 := by
    norm_cast
    exact decoderFallbackState_normSq m w
  simp [LinearMap.comp_apply, hnormSq]

theorem sum_complementDecoderBranch_adjoint_comp {w r m : Nat}
    (h : Admissible w r m) :
    ∑ i : Fin (Module.finrank Complex (PhysicalRegister m w)),
      (LinearMap.adjoint (complementDecoderBranch h i)).comp (complementDecoderBranch h i) =
        decoderComplementProjector h := by
  simp_rw [complementDecoderBranch_adjoint_comp]
  calc
    (∑ i, (InnerProductSpace.rankOne Complex
      (decoderComplementProjector h (decoderPhysicalBasis m w i))
      (decoderComplementProjector h (decoderPhysicalBasis m w i))).toLinearMap) =
      (decoderComplementProjector h).comp
        (LinearMap.adjoint (decoderComplementProjector h)) := by
        apply LinearMap.ext
        intro psi
        simp only [LinearMap.sum_apply, LinearMap.comp_apply]
        rw [← (decoderPhysicalBasis m w).sum_repr'
          (LinearMap.adjoint (decoderComplementProjector h) psi)]
        simp only [map_sum, map_smul]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [LinearMap.adjoint_inner_right]
        rfl
    _ = (decoderComplementProjector h).comp (decoderComplementProjector h) := by
      rw [decoderComplementProjector_adjoint]
    _ = decoderComplementProjector h := decoderComplementProjector_idempotent h

/-- Finite Kraus completion of inverse encoding to a total parameterized
decoder. -/
def decoderKrausFamily {w r m : Nat} (h : Admissible w r m) :
    FiniteKrausFamily
      (Sum Unit (Fin (Module.finrank Complex (PhysicalRegister m w))))
      (PhysicalRegister m w) (LogicalRegister m w) where
  operator
    | .inl _ => codeDecoderBranch h
    | .inr i => complementDecoderBranch h i

theorem decoderKrausFamily_complete {w r m : Nat} (h : Admissible w r m) :
    (decoderKrausFamily h).Complete := by
  rw [FiniteKrausFamily.Complete, Fintype.sum_sum_type]
  change (∑ _ : Unit, decoderCodeProjector h) +
      (∑ i : Fin (Module.finrank Complex (PhysicalRegister m w)),
        (LinearMap.adjoint (complementDecoderBranch h i)).comp
          (complementDecoderBranch h i)) = 1
  rw [Fintype.sum_unique, sum_complementDecoderBranch_adjoint_comp]
  simp [decoderComplementProjector]

/-- The actual CPTP parameterized HH18 decoder: inverse encoding on the code
carrier and a neutral finite-Kraus fallback off it. -/
noncomputable def decoderChannel {w r m : Nat} (h : Admissible w r m) :
    QuantumChannel (PhysicalRegister m w) (LogicalRegister m w) :=
  (decoderKrausFamily h).toQuantumChannel (decoderKrausFamily_complete h)

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

/-- The total decoder agrees with coherent inverse encoding on every encoded
rank-one input. -/
theorem decoderChannel_rankOne_encoded {w r m : Nat} (h : Admissible w r m)
    (psi : LogicalRegister m w) :
    decoderChannel h (InnerProductSpace.rankOne Complex
      (ambientEncodingIsometry h psi) (ambientEncodingIsometry h psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  rw [decoderChannel, FiniteKrausFamily.toQuantumChannel_apply_sum,
    Fintype.sum_sum_type]
  simp only [decoderKrausFamily]
  simp_rw [sandwich_rankOne]
  rw [Fintype.sum_unique]
  simp only [codeDecoderBranch_encoded]
  have hcomplement : ∀ i, complementDecoderBranch h i
      (ambientEncodingIsometry h psi) = 0 := by
    intro i
    have hinner : inner Complex
        (decoderComplementProjector h (decoderPhysicalBasis m w i))
        (ambientEncodingIsometry h psi) = 0 := by
      rw [← LinearMap.adjoint_inner_right, decoderComplementProjector_adjoint,
        decoderComplementProjector_encoded]
      simp
    change inner Complex (decoderComplementProjector h (decoderPhysicalBasis m w i))
      (ambientEncodingIsometry h psi) • decoderFallbackState m w = 0
    rw [hinner]
    simp
  simp_rw [hcomplement]
  simp

/-- The source-selected logical ideal is the actual HH18 logical `T` applied
to the logical-plus seed, in the inverse physical-`T` orientation. -/
noncomputable def idealLogicalTOutputState (m w : Nat) : LogicalRegister m w :=
  HH18PuncturedReedMuller.logicalT w m (logicalPlus m w)

private theorem idealLogicalTOutputState_normSq (m w : Nat) :
    ‖idealLogicalTOutputState m w‖ ^ 2 = 1 := by
  have hnorm : ‖idealLogicalTOutputState m w‖ = 1 := by
    change ‖(HH18PuncturedReedMuller.logicalT w m).toLinearIsometryEquiv
      (logicalPlus m w)‖ = 1
    rw [(HH18PuncturedReedMuller.logicalT w m).toLinearIsometryEquiv.norm_map]
    exact logicalPlus_norm m w
  rw [hnorm]
  norm_num

/-- Ideal logical output density for the actual inverse-physical-`T` route. -/
noncomputable def idealLogicalTOutput (m w : Nat) :
    DensityOperator (LogicalRegister m w) :=
  DensityOperator.pureDensity (idealLogicalTOutputState m w)
    (idealLogicalTOutputState_normSq m w)

/-- Decoding the actual error-free inverse physical-`T` rank-one branch
returns the parameterized logical-`T` ideal density. -/
theorem decoderChannel_rankOne_physicalTInv_eq_idealLogicalTOutput {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    decoderChannel h (InnerProductSpace.rankOne Complex
      (physicalTInvBranch h hdegree) (physicalTInvBranch h hdegree)).toLinearMap =
      (idealLogicalTOutput m w).toOperator := by
  rw [physicalTInvBranch_eq_logicalT h hdegree]
  change decoderChannel h (InnerProductSpace.rankOne Complex
    (ambientEncodingIsometry h (idealLogicalTOutputState m w))
    (ambientEncodingIsometry h (idealLogicalTOutputState m w))).toLinearMap = _
  rw [decoderChannel_rankOne_encoded]
  rfl

/-- State-dependent trace-norm error of a decoded parameterized logical output
relative to its actual logical-`T` target. -/
noncomputable def outputTraceError {m w : Nat}
    (rho sigma : DensityOperator (LogicalRegister m w)) : Real :=
  traceNorm (rho.toOperator - sigma.toOperator)

theorem outputTraceError_nonneg {m w : Nat}
    (rho sigma : DensityOperator (LogicalRegister m w)) :
    0 ≤ outputTraceError rho sigma :=
  traceNorm_nonneg _

end HH18Parameterized
end Distillation
end QEC
