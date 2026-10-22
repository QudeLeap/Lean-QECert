import QEC.Bounds.GeometricLocalityTradeoff.Model
import QEC.Semantics.ErrorCorrection.QuditNoInformation
import QEC.Semantics.ErrorCorrection.ReferenceDecoupling
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed

/-!
# BPT commuting-projector disentangling

This module develops the finite-dimensional ingredients of BPT's
Disentangling Lemma.  It works with the canonical nonbinary finite-qudit
factorization and concrete erasure channels from `QuditSubsystem`.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/-- Concrete BPT-region erasure recoverability for the model's actual code. -/
def RegionErasureRecoverable (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Prop :=
  (M.regionSubsystem region).ErasureRecoverableFromRegister M.codeSpace

/--
Concrete recovery from a BPT model region makes every local finite-qudit
effect information-free on the actual common-projector code.  This is the
recovery-to-no-information half of the finite-qudit bridge, specialized only
through the model's concrete region/subsystem bridge.
-/
theorem regionErasureRecoverable_implies_noInformationOn
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcorrectable : M.RegionErasureRecoverable region) :
    Semantics.QuditSubsystem.NoInformationOn M.codeSpace (M.regionSubsystem region) := by
  exact ((M.regionSubsystem region).noInformationOn_iff_exists_erasureRecovery
    M.codeSpace L.localDimension_positive).mpr hcorrectable

/--
The two correctability hypotheses of the BPT lemma yield the two independent
no-information statements used first to collapse boundary sectors and later to
invoke the no-cloning argument on the residual middle factor.
-/
theorem region_and_externalBoundary_noInformationOn_of_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hregion : M.RegionErasureRecoverable region)
    (hexternal : M.RegionErasureRecoverable (M.externalBoundary region)) :
    Semantics.QuditSubsystem.NoInformationOn M.codeSpace (M.regionSubsystem region) ∧
      Semantics.QuditSubsystem.NoInformationOn M.codeSpace
        (M.regionSubsystem (M.externalBoundary region)) :=
  ⟨M.regionErasureRecoverable_implies_noInformationOn region hregion,
    M.regionErasureRecoverable_implies_noInformationOn (M.externalBoundary region) hexternal⟩

/--
The concrete code projector is a projection onto precisely its declared code
carrier.  This supplies the finite-dimensional trace/rank identity needed by
the no-cloning closure: a normalized code projector has entropy zero only when
the remaining logical factor is one-dimensional.
-/
theorem codeSpace_projector_isProj (M : BPTCommutingProjectorModel L kappa) :
    LinearMap.IsProj M.codeSpace.carrier M.fullCodeProjector := by
  constructor
  · intro vector
    exact M.codeSpace.projector_mem_carrier vector
  · intro vector hvector
    exact M.codeSpace.projector_eq_self_of_mem hvector

/--
The trace of the actual full code projector is the finite complex dimension of
the code carrier.  Its target use is the final no-cloning step after the two
residual complementary erasures have decoupled the logical reference.
-/
theorem trace_fullCodeProjector_eq_finrank_codeSpace
    (M : BPTCommutingProjectorModel L kappa) :
    LinearMap.trace Complex L.Register M.fullCodeProjector =
      (Module.finrank Complex M.codeSpace.carrier : Complex) := by
  exact M.codeSpace_projector_isProj.trace

/--
The normalized finite code projector is a concrete density operator whenever
the code carrier is nonzero.  It is the canonical logical mixed state used to
purify the entire code for the residual two-factor no-cloning argument.
-/
noncomputable def normalizedCodeProjectorDensity
    (M : BPTCommutingProjectorModel L kappa) (hcode : M.codeSpace.carrier ≠ ⊥) :
    Semantics.DensityOperator L.Register where
  toOperator :=
    ((Module.finrank Complex M.codeSpace.carrier : Complex)⁻¹) • M.fullCodeProjector
  positive := by
    have hprojector : M.fullCodeProjector.IsSymmetricProjection := by
      constructor
      · change M.fullCodeProjector.comp M.fullCodeProjector = M.fullCodeProjector
        exact M.fullCodeProjector_idempotent
      · exact (LinearMap.isSymmetric_iff_isSelfAdjoint M.fullCodeProjector).mpr
          M.fullCodeProjector_adjoint_eq_self
    have hdim_nonneg : 0 ≤ (Module.finrank Complex M.codeSpace.carrier : Complex) := by
      exact_mod_cast Nat.zero_le (Module.finrank Complex M.codeSpace.carrier)
    exact hprojector.isPositive.smul_of_nonneg ((inv_nonneg).2 hdim_nonneg)
  trace_one := by
    have hdimNat : Module.finrank Complex M.codeSpace.carrier ≠ 0 := by
      intro hzero
      apply hcode
      exact Submodule.finrank_eq_zero.mp hzero
    have hdim : (Module.finrank Complex M.codeSpace.carrier : Complex) ≠ 0 := by
      exact_mod_cast hdimNat
    rw [map_smul, M.trace_fullCodeProjector_eq_finrank_codeSpace]
    exact inv_mul_cancel₀ hdim

/--
The normalized code-projector density is supported on the actual BPT code.
This is the support premise consumed by recovery-to-reference decoupling.
-/
theorem normalizedCodeProjectorDensity_supportedOn
    (M : BPTCommutingProjectorModel L kappa) (hcode : M.codeSpace.carrier ≠ ⊥) :
    Semantics.DensityOperator.SupportedOn M.codeSpace
      (M.normalizedCodeProjectorDensity hcode) := by
  intro vector
  dsimp only [normalizedCodeProjectorDensity, LinearMap.smul_apply]
  exact M.codeSpace.carrier.smul_mem _ (M.codeSpace.projector_mem_carrier vector)

/--
For the normalized whole-code state, concrete recovery from a BPT region
decouples that region from an arbitrary purifying reference.  This is the
recovery-to-reference input for the source no-cloning step: applying it to
both residual complementary factors forces the logical reference to be pure.
-/
theorem normalizedCodeProjector_selectedReference_factorizes_of_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hcorrectable : M.RegionErasureRecoverable region)
    (Ref : Type) [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref]
    [Semantics.FiniteQuantumSystem Ref]
    (purification : Semantics.DensityOperator.FinitePurification
      (M.normalizedCodeProjectorDensity hcode) Ref) :
    (M.regionSubsystem region).selectedReferenceMarginal Ref
      (Semantics.DensityOperator.pureDensity purification.vector purification.normSq_one) =
      Semantics.DensityOperator.tensorDensity
        ((M.regionSubsystem region).selectedPartialTraceFromRegister.mapDensity
          (M.normalizedCodeProjectorDensity hcode))
        (Semantics.DensityOperator.leftMarginal
          (Semantics.DensityOperator.pureDensity purification.vector purification.normSq_one)) := by
  rcases hcorrectable with ⟨recovery, hrecovery⟩
  exact (M.regionSubsystem region).erasureRecovery_implies_selectedReferenceMarginal_factorizes
    M.codeSpace recovery hrecovery (M.normalizedCodeProjectorDensity hcode)
    (M.normalizedCodeProjectorDensity_supportedOn hcode) Ref purification

/--
Both BPT recoverability hypotheses give independent reference-decoupling
factorizations for the same normalized full-code purification.  The first
factorization is for `M`; the second is for `partialPlus M`.  Their residual
counterparts are the two decouplings used by the source no-cloning argument.
-/
theorem normalizedCodeProjector_region_and_externalBoundary_reference_factorize
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hregion : M.RegionErasureRecoverable region)
    (hexternal : M.RegionErasureRecoverable (M.externalBoundary region))
    (Ref : Type) [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref]
    [Semantics.FiniteQuantumSystem Ref]
    (purification : Semantics.DensityOperator.FinitePurification
      (M.normalizedCodeProjectorDensity hcode) Ref) :
    ((M.regionSubsystem region).selectedReferenceMarginal Ref
      (Semantics.DensityOperator.pureDensity purification.vector purification.normSq_one) =
      Semantics.DensityOperator.tensorDensity
        ((M.regionSubsystem region).selectedPartialTraceFromRegister.mapDensity
          (M.normalizedCodeProjectorDensity hcode))
        (Semantics.DensityOperator.leftMarginal
          (Semantics.DensityOperator.pureDensity purification.vector purification.normSq_one))) ∧
    ((M.regionSubsystem (M.externalBoundary region)).selectedReferenceMarginal Ref
      (Semantics.DensityOperator.pureDensity purification.vector purification.normSq_one) =
      Semantics.DensityOperator.tensorDensity
        ((M.regionSubsystem (M.externalBoundary region)).selectedPartialTraceFromRegister.mapDensity
          (M.normalizedCodeProjectorDensity hcode))
        (Semantics.DensityOperator.leftMarginal
          (Semantics.DensityOperator.pureDensity purification.vector purification.normSq_one))) :=
  ⟨M.normalizedCodeProjector_selectedReference_factorizes_of_recoverable region hcode
      hregion Ref purification,
    M.normalizedCodeProjector_selectedReference_factorizes_of_recoverable
      (M.externalBoundary region) hcode hexternal Ref purification⟩

/-- A global unitary acts only on a BPT region when its underlying operator is a local extension. -/
def UnitarySupportedOn (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) (U : Semantics.UnitaryTransport L.Register L.Register) : Prop :=
  (M.regionSubsystem region).OperatorSupportedOnRegister U.toLinearEquiv.toLinearMap

/-- Compose two global unitary transports, applying `U` first and `V` second. -/
noncomputable def thenUnitary
    (U V : Semantics.UnitaryTransport L.Register L.Register) :
    Semantics.UnitaryTransport L.Register L.Register where
  toLinearEquiv := U.toLinearEquiv.trans V.toLinearEquiv
  map_inner := by
    intro x y
    change inner Complex (V (U x)) (V (U y)) = inner Complex x y
    rw [V.map_inner, U.map_inner]

/--
Support on a fixed region is closed under composition of unitary transports.
The local representatives compose in the same order as the global maps, so the
eventual BPT boundary unitary can be assembled from its two algebraic block
units and its final pure-state disentangler.
-/
theorem unitarySupportedOn_then
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {U V : Semantics.UnitaryTransport L.Register L.Register}
    (hU : M.UnitarySupportedOn region U) (hV : M.UnitarySupportedOn region V) :
    M.UnitarySupportedOn region (thenUnitary U V) := by
  rcases hU with ⟨localU, hlocalU⟩
  rcases hV with ⟨localV, hlocalV⟩
  refine ⟨localV.comp localU, ?_⟩
  change (M.regionSubsystem region).extendLocalToRegister (localV.comp localU) =
    V.toLinearEquiv.toLinearMap.comp U.toLinearEquiv.toLinearMap
  rw [← localExtension_comp, hlocalV, hlocalU]

/-- Compose arbitrary finite-dimensional unitary transports, applying `U` then `V`. -/
noncomputable def composeUnitaryTransport
    {H K J : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (U : Semantics.UnitaryTransport H K) (V : Semantics.UnitaryTransport K J) :
    Semantics.UnitaryTransport H J where
  toLinearEquiv := U.toLinearEquiv.trans V.toLinearEquiv
  map_inner := by
    intro x y
    change inner Complex (V (U x)) (V (U y)) = inner Complex x y
    rw [V.map_inner, U.map_inner]

/-- A composed transport applies its first coordinate change before its second. -/
@[simp]
theorem composeUnitaryTransport_apply
    {H K J : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (U : Semantics.UnitaryTransport H K) (V : Semantics.UnitaryTransport K J) (vector : H) :
    composeUnitaryTransport U V vector = V (U vector) :=
  rfl

/-- The linear equivalence inside a composed transport has the same pointwise action. -/
@[simp]
theorem composeUnitaryTransport_toLinearEquiv_apply
    {H K J : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (U : Semantics.UnitaryTransport H K) (V : Semantics.UnitaryTransport K J) (vector : H) :
    (composeUnitaryTransport U V).toLinearEquiv vector = V.toLinearEquiv (U.toLinearEquiv vector) :=
  rfl

/-- Unitary conjugation along a composite transport is successive conjugation. -/
theorem composeUnitaryTransport_conjOperator
    {H K J : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (U : Semantics.UnitaryTransport H K) (V : Semantics.UnitaryTransport K J)
    (A : Semantics.Operator H) :
    (composeUnitaryTransport U V).conjOperator A = V.conjOperator (U.conjOperator A) := by
  ext x
  simp [composeUnitaryTransport, Semantics.UnitaryTransport.conjOperator]

/-- Finite-dimensional unitary transports are determined by their linear equivalence. -/
theorem unitaryTransport_ext
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    {U V : Semantics.UnitaryTransport H K}
    (h : U.toLinearEquiv = V.toLinearEquiv) : U = V := by
  cases U
  cases V
  cases h
  rfl

/-- Tensor a unitary transport on the right with an untouched finite system. -/
noncomputable def unitaryRTensor
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (J : Type u)
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J] :
    Semantics.UnitaryTransport (Semantics.CompositeSystem H J) (Semantics.CompositeSystem K J) := by
  let e := U.toLinearIsometryEquiv.rTensor J
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := e.inner_map_map }

/-- Tensor a unitary transport on the left with an untouched finite system. -/
noncomputable def unitaryLTensor
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (I : Type u) [NormedAddCommGroup I] [InnerProductSpace Complex I]
    [Semantics.FiniteQuantumSystem I] (U : Semantics.UnitaryTransport H K) :
    Semantics.UnitaryTransport (Semantics.CompositeSystem I H) (Semantics.CompositeSystem I K) := by
  let e := U.toLinearIsometryEquiv.lTensor I
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := e.inner_map_map }

/-- Right tensoring applies the transported unitary only to the left tensor factor. -/
@[simp]
theorem unitaryRTensor_apply_tmul
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (J : Type u)
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (h : H) (j : J) :
    unitaryRTensor U J (h ⊗ₜ[Complex] j) = U h ⊗ₜ[Complex] j :=
  rfl

/-- The explicit linear-equivalence view of a right tensor transport has the same action. -/
@[simp]
theorem unitaryRTensor_toLinearEquiv_apply_tmul
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (J : Type u)
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (h : H) (j : J) :
    (unitaryRTensor U J).toLinearEquiv (h ⊗ₜ[Complex] j) =
      U.toLinearEquiv h ⊗ₜ[Complex] j :=
  rfl

/-- Left tensoring applies the transported unitary only to the right tensor factor. -/
@[simp]
theorem unitaryLTensor_apply_tmul
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (I : Type u) [NormedAddCommGroup I] [InnerProductSpace Complex I]
    [Semantics.FiniteQuantumSystem I] (U : Semantics.UnitaryTransport H K)
    (i : I) (h : H) :
    unitaryLTensor I U (i ⊗ₜ[Complex] h) = i ⊗ₜ[Complex] U h :=
  rfl

/-- The explicit linear-equivalence view of a left tensor transport has the same action. -/
@[simp]
theorem unitaryLTensor_toLinearEquiv_apply_tmul
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (I : Type u) [NormedAddCommGroup I] [InnerProductSpace Complex I]
    [Semantics.FiniteQuantumSystem I] (U : Semantics.UnitaryTransport H K)
    (i : I) (h : H) :
    (unitaryLTensor I U).toLinearEquiv (i ⊗ₜ[Complex] h) =
      i ⊗ₜ[Complex] U.toLinearEquiv h :=
  rfl

/-- Extend a unitary on a selected qudit subsystem by the identity on its complement. -/
noncomputable def extendLocalUnitaryToRegister
    {ι : Type u} [Fintype ι] [DecidableEq ι] (q : ι → Nat)
    (S : Semantics.QuditSubsystem q)
    (U : Semantics.UnitaryTransport S.selectedSystem S.selectedSystem) :
    Semantics.UnitaryTransport (Semantics.Qudit.QuditRegister q)
      (Semantics.Qudit.QuditRegister q) :=
  composeUnitaryTransport
    (composeUnitaryTransport S.registerFactorization
      (unitaryRTensor U S.complementSystem))
    S.registerFactorization.symm

/-- The global lift has exactly the concrete local-extension operator as its linear map. -/
theorem extendLocalUnitaryToRegister_toLinearMap_eq
    {ι : Type u} [Fintype ι] [DecidableEq ι] (q : ι → Nat)
    (S : Semantics.QuditSubsystem q)
    (U : Semantics.UnitaryTransport S.selectedSystem S.selectedSystem) :
    (extendLocalUnitaryToRegister q S U).toLinearEquiv.toLinearMap =
      S.extendLocalToRegister U.toLinearEquiv.toLinearMap := by
  rfl

/-- The register lift of a selected-system unitary is supported on that selected subsystem. -/
theorem extendLocalUnitaryToRegister_supportedOnRegister
    {ι : Type u} [Fintype ι] [DecidableEq ι] (q : ι → Nat)
    (S : Semantics.QuditSubsystem q)
    (U : Semantics.UnitaryTransport S.selectedSystem S.selectedSystem) :
    S.OperatorSupportedOnRegister
      (extendLocalUnitaryToRegister q S U).toLinearEquiv.toLinearMap := by
  refine ⟨U.toLinearEquiv.toLinearMap, ?_⟩
  exact extendLocalUnitaryToRegister_toLinearMap_eq q S U

/-- Extend a unitary on a finite-dimensional submodule by an ambient unitary. -/
noncomputable def extendSubmoduleUnitary
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (S : Submodule Complex H)
    (U : Semantics.UnitaryTransport S S) :
    Semantics.UnitaryTransport H H := by
  let L : S →ₗᵢ[Complex] H := S.subtypeₗᵢ.comp U.toLinearIsometryEquiv.toLinearIsometry
  let T : H →ₗᵢ[Complex] H := L.extend
  have hTsurj : Function.Surjective T := by
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := Complex)
      (V := H) (V₂ := H) rfl).mp T.injective
  let E : H ≃ₗᵢ[Complex] H := LinearIsometryEquiv.ofSurjective T hTsurj
  exact
    { toLinearEquiv := E.toLinearEquiv
      map_inner := fun x y => E.inner_map_map x y }

/-- The ambient extension agrees with the prescribed unitary on its submodule. -/
theorem extendSubmoduleUnitary_apply_subtype
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (S : Submodule Complex H)
    (U : Semantics.UnitaryTransport S S) (s : S) :
    extendSubmoduleUnitary S U (s : H) = (U s : S) := by
  let L : S →ₗᵢ[Complex] H := S.subtypeₗᵢ.comp U.toLinearIsometryEquiv.toLinearIsometry
  let T : H →ₗᵢ[Complex] H := L.extend
  have hTsurj : Function.Surjective T := by
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := Complex)
      (V := H) (V₂ := H) rfl).mp T.injective
  let E : H ≃ₗᵢ[Complex] H := LinearIsometryEquiv.ofSurjective T hTsurj
  change E (s : H) = (U s : S)
  calc
    E (s : H) = T (s : H) := rfl
    _ = L s := by rw [← LinearIsometry.extend_apply L s]
    _ = (U s : S) := rfl

/-- Package a finite-dimensional linear isometry equivalence as a unitary transport. -/
noncomputable def unitaryTransportOfLinearIsometryEquiv
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K] (E : H ≃ₗᵢ[Complex] K) :
    Semantics.UnitaryTransport H K :=
  { toLinearEquiv := E.toLinearEquiv
    map_inner := fun x y => E.inner_map_map x y }

/-- Extend a unitary transported through an isometric active embedding to its ambient space. -/
noncomputable def extendAlongLinearIsometryUnitary
    {A H : Type u} [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [Semantics.FiniteQuantumSystem A] [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (J : A →ₗᵢ[Complex] H)
    (U : Semantics.UnitaryTransport A A) :
    Semantics.UnitaryTransport H H := by
  let E : A ≃ₗᵢ[Complex] J.range := J.equivRange
  let EJ : Semantics.UnitaryTransport A J.range := unitaryTransportOfLinearIsometryEquiv E
  let Urange : Semantics.UnitaryTransport J.range J.range :=
    composeUnitaryTransport (composeUnitaryTransport EJ.symm U) EJ
  exact extendSubmoduleUnitary J.range Urange

/-- The ambient lift agrees with the active unitary on the image of its isometric embedding. -/
theorem extendAlongLinearIsometryUnitary_apply
    {A H : Type u} [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [Semantics.FiniteQuantumSystem A] [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (J : A →ₗᵢ[Complex] H)
    (U : Semantics.UnitaryTransport A A) (x : A) :
    extendAlongLinearIsometryUnitary J U (J x) = J (U x) := by
  let E : A ≃ₗᵢ[Complex] J.range := J.equivRange
  let EJ : Semantics.UnitaryTransport A J.range := unitaryTransportOfLinearIsometryEquiv E
  let Urange : Semantics.UnitaryTransport J.range J.range :=
    composeUnitaryTransport (composeUnitaryTransport EJ.symm U) EJ
  let s : J.range := E x
  have hs : (s : H) = J x := rfl
  calc
    extendAlongLinearIsometryUnitary J U (J x) =
        extendAlongLinearIsometryUnitary J U (s : H) := by rw [hs]
    _ = (Urange s : J.range) := extendSubmoduleUnitary_apply_subtype J.range Urange s
    _ = (E (U x) : J.range) := by
      have hback : EJ.symm s = x := by
        change E.symm s = x
        change E.symm (E x) = x
        exact E.symm_apply_apply x
      change J (U (EJ.symm s)) = J (U x)
      rw [hback]
    _ = J (U x) := rfl

/-- Transport a unitary on a coordinate space back to the original space. -/
noncomputable def conjugateUnitaryTransport
    {A B : Type u} [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [Semantics.FiniteQuantumSystem A] [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B] (T : Semantics.UnitaryTransport A B)
    (U : Semantics.UnitaryTransport B B) :
    Semantics.UnitaryTransport A A :=
  composeUnitaryTransport (composeUnitaryTransport T U) T.symm

/-- The coordinate conjugate applies the transport, local unitary, and inverse transport in order. -/
theorem conjugateUnitaryTransport_apply
    {A B : Type u} [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [Semantics.FiniteQuantumSystem A] [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B] (T : Semantics.UnitaryTransport A B)
    (U : Semantics.UnitaryTransport B B) (x : A) :
    conjugateUnitaryTransport T U x = T.symm (U (T x)) := by
  simp [conjugateUnitaryTransport, composeUnitaryTransport_apply]

/-- Conjugating a coordinate pullback recovers the original coordinate unitary. -/
theorem conj_conjugateUnitaryTransport_toLinearMap
    {A B : Type u} [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [Semantics.FiniteQuantumSystem A] [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B] (T : Semantics.UnitaryTransport A B)
    (U : Semantics.UnitaryTransport B B) :
    T.conjOperator (conjugateUnitaryTransport T U).toLinearEquiv.toLinearMap =
      U.toLinearEquiv.toLinearMap := by
  ext x
  simp [conjugateUnitaryTransport, composeUnitaryTransport,
    Semantics.UnitaryTransport.conjOperator]

/--
Right absorption by a sector embedding, together with commutation,
reconstructs an operator from its two-sided active-sector compression.
-/
theorem embedding_compression_of_right_absorption
    {S H : Type u} [NormedAddCommGroup S] [InnerProductSpace Complex S]
    [Semantics.FiniteQuantumSystem S] [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (J : S →ₗ[Complex] H)
    (R : Semantics.Operator H)
    (hcommute : Commute R (J.comp (LinearMap.adjoint J)))
    (hactive : R * (J.comp (LinearMap.adjoint J)) = R) :
    R = J.comp (((LinearMap.adjoint J).comp
      (R.comp J)).comp (LinearMap.adjoint J)) := by
  let sector : Semantics.Operator H := J.comp (LinearMap.adjoint J)
  have hleft : sector * R = R := by
    calc
      sector * R = R * sector := hcommute.eq.symm
      _ = R := hactive
  have hdouble : R = sector * R * sector := by
    calc
      R = sector * R := hleft.symm
      _ = sector * (R * sector) := by rw [hactive]
      _ = sector * R * sector := (mul_assoc sector R sector).symm
  change R = J.comp (((LinearMap.adjoint J).comp
    (R.comp J)).comp (LinearMap.adjoint J))
  calc
    R = sector * R * sector := hdouble
    _ = (J.comp (LinearMap.adjoint J)) * R *
        (J.comp (LinearMap.adjoint J)) := by rfl
    _ = J.comp (((LinearMap.adjoint J).comp
        (R.comp J)).comp (LinearMap.adjoint J)) := by
      simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]

/--
An ambient unitary that intertwines a sector embedding conjugates a two-sided
sector compression exactly by the corresponding active unitary.
-/
theorem unitaryTransport_conj_embedding_compression_of_intertwines
    {S H : Type u} [NormedAddCommGroup S] [InnerProductSpace Complex S]
    [Semantics.FiniteQuantumSystem S] [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (J : S →ₗ[Complex] H)
    (E : Semantics.UnitaryTransport H H) (U : Semantics.UnitaryTransport S S)
    (hintertwines : E.toLinearEquiv.toLinearMap.comp J =
      J.comp U.toLinearEquiv.toLinearMap) (P : Semantics.Operator S) :
    E.conjOperator (J.comp (P.comp (LinearMap.adjoint J))) =
      J.comp ((U.conjOperator P).comp (LinearMap.adjoint J)) := by
  have hright : (LinearMap.adjoint J).comp E.toLinearEquiv.symm.toLinearMap =
      U.toLinearEquiv.symm.toLinearMap.comp (LinearMap.adjoint J) := by
    have hadjoint := congrArg LinearMap.adjoint hintertwines
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp,
      Semantics.UnitaryTransport.adjoint_toLinearMap,
      Semantics.UnitaryTransport.adjoint_toLinearMap] at hadjoint
    simpa [Semantics.UnitaryTransport.symm_toLinearEquiv] using hadjoint
  unfold Semantics.UnitaryTransport.conjOperator
  calc
    E.toLinearEquiv.toLinearMap.comp
        ((J.comp (P.comp (LinearMap.adjoint J))).comp
          E.toLinearEquiv.symm.toLinearMap) =
        (E.toLinearEquiv.toLinearMap.comp J).comp
          (P.comp ((LinearMap.adjoint J).comp E.toLinearEquiv.symm.toLinearMap)) := by
      simp only [LinearMap.comp_assoc]
    _ = (J.comp U.toLinearEquiv.toLinearMap).comp
          (P.comp (U.toLinearEquiv.symm.toLinearMap.comp
            (LinearMap.adjoint J))) := by
      rw [hintertwines, hright]
    _ = J.comp ((U.toLinearEquiv.toLinearMap.comp
          (P.comp U.toLinearEquiv.symm.toLinearMap)).comp
            (LinearMap.adjoint J)) := by
      simp only [LinearMap.comp_assoc]

/-- An isometric linear lift preserves the symmetric-projection property. -/
theorem isSymmetricProjection_isometric_lift
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K)
    (hJ : (LinearMap.adjoint J).comp J = (1 : Semantics.Operator H))
    (P : Semantics.Operator H) (hP : P.IsSymmetricProjection) :
    (J.comp (P.comp (LinearMap.adjoint J))).IsSymmetricProjection := by
  constructor
  · change (J.comp (P.comp (LinearMap.adjoint J))).comp
        (J.comp (P.comp (LinearMap.adjoint J))) = J.comp (P.comp (LinearMap.adjoint J))
    ext x
    simp only [LinearMap.comp_apply]
    have hJ_apply : LinearMap.adjoint J (J (P (LinearMap.adjoint J x))) =
        P (LinearMap.adjoint J x) := by
      simpa only [Module.End.one_apply, LinearMap.comp_apply] using
        congrArg (fun A : Semantics.Operator H => A (P (LinearMap.adjoint J x))) hJ
    rw [hJ_apply]
    exact congrArg J (congrArg (fun A : Semantics.Operator H => A (LinearMap.adjoint J x))
      hP.isIdempotentElem.eq)
  · simpa only [LinearMap.comp_assoc] using hP.isSymmetric.conj_adjoint J

/-- Lifting a rank-one self-projector along an isometric embedding is rank one at the image. -/
theorem isometric_lift_rankOne_self
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K)
    (hJ : (LinearMap.adjoint J).comp J = (1 : Semantics.Operator H))
    (v : H) :
    J.comp ((InnerProductSpace.rankOne Complex v v).toLinearMap.comp
      (LinearMap.adjoint J)) =
      (InnerProductSpace.rankOne Complex (J v) (J v)).toLinearMap := by
  ext z
  simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    LinearMap.adjoint_inner_right]

/-- A finite-dimensional linear isometry is a left inverse to its adjoint. -/
theorem linearIsometry_adjoint_comp_self
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗᵢ[Complex] K) :
    (LinearMap.adjoint J.toLinearMap).comp J.toLinearMap = (1 : Semantics.Operator H) := by
  simpa only [Module.End.one_eq_id] using J.adjoint_comp_self'

/-- The canonical associator as a unitary transport between three tensor factors. -/
noncomputable def tensorAssociatorUnitary
    (H K J : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J] :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem (Semantics.CompositeSystem H K) J)
      (Semantics.CompositeSystem H (Semantics.CompositeSystem K J)) := by
  let e := TensorProduct.assocIsometry Complex H K J
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := e.inner_map_map }

/-- The tensor product of two submodule inclusions is an isometric active-sector embedding. -/
noncomputable def submoduleTensorEmbedding
    {B C : Type u} [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B] [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C] (SB : Submodule Complex B) (SC : Submodule Complex C) :
    Semantics.CompositeSystem SB SC →ₗᵢ[Complex] Semantics.CompositeSystem B C :=
  TensorProduct.mapIsometry SB.subtypeₗᵢ SC.subtypeₗᵢ

/-- Put the active `NB tensor WC` factor between its two spectator factors. -/
noncomputable def activeSectorCoordinateTransport
    {B C WB NB WC NC : Type u} [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B] [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C] [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC] (SB : Submodule Complex B) (SC : Submodule Complex C)
    (UB : Semantics.UnitaryTransport SB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport SC (Semantics.CompositeSystem WC NC)) :
    Semantics.UnitaryTransport (Semantics.CompositeSystem SB SC)
      (Semantics.CompositeSystem WB
        (Semantics.CompositeSystem (Semantics.CompositeSystem NB WC) NC)) :=
  composeUnitaryTransport
    (composeUnitaryTransport
      (unitaryRTensor UB SC)
      (unitaryLTensor (Semantics.CompositeSystem WB NB) UC))
    (composeUnitaryTransport
      (tensorAssociatorUnitary WB NB (Semantics.CompositeSystem WC NC))
      (unitaryLTensor WB (tensorAssociatorUnitary NB WC NC).symm))

/--
Extend an active `NB tensor WC` unitary to the ambient physical `B tensor C`
space, with its action prescribed on the chosen sector after retaining the
`WB` and `NC` factors.
-/
noncomputable def activeSectorPhysicalUnitary
    {B C WB NB WC NC : Type u} [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B] [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C] [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC] (SB : Submodule Complex B) (SC : Submodule Complex C)
    (UB : Semantics.UnitaryTransport SB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport SC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    Semantics.UnitaryTransport (Semantics.CompositeSystem B C)
      (Semantics.CompositeSystem B C) := by
  let T := activeSectorCoordinateTransport SB SC UB UC
  let V := unitaryLTensor WB (unitaryRTensor U NC)
  exact extendAlongLinearIsometryUnitary (submoduleTensorEmbedding SB SC)
    (conjugateUnitaryTransport T V)

/-- The physical sector lift agrees with its coordinate action on the active subspace. -/
theorem activeSectorPhysicalUnitary_apply_embedding
    {B C WB NB WC NC : Type u} [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B] [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C] [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC] (SB : Submodule Complex B) (SC : Submodule Complex C)
    (UB : Semantics.UnitaryTransport SB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport SC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) (x : Semantics.CompositeSystem SB SC) :
    activeSectorPhysicalUnitary SB SC UB UC U
        (submoduleTensorEmbedding SB SC x) =
      submoduleTensorEmbedding SB SC
        (conjugateUnitaryTransport (activeSectorCoordinateTransport SB SC UB UC)
          (unitaryLTensor WB (unitaryRTensor U NC)) x) := by
  exact extendAlongLinearIsometryUnitary_apply (submoduleTensorEmbedding SB SC)
    (conjugateUnitaryTransport (activeSectorCoordinateTransport SB SC UB UC)
      (unitaryLTensor WB (unitaryRTensor U NC))) x

/--
The physical active-sector unitary intertwines the sector embedding with its
prescribed coordinate action.  This is the operator form needed to conjugate
the reconstructed code block; no identity-on-the-orthogonal-complement claim
is used.
-/
theorem activeSectorPhysicalUnitary_intertwines_embedding
    {B C WB NB WC NC : Type u} [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B] [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C] [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC] (SB : Submodule Complex B) (SC : Submodule Complex C)
    (UB : Semantics.UnitaryTransport SB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport SC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    (activeSectorPhysicalUnitary SB SC UB UC U).toLinearEquiv.toLinearMap.comp
        (submoduleTensorEmbedding SB SC).toLinearMap =
      (submoduleTensorEmbedding SB SC).toLinearMap.comp
        (conjugateUnitaryTransport
          (activeSectorCoordinateTransport SB SC UB UC)
          (unitaryLTensor WB (unitaryRTensor U NC))).toLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro x
  change activeSectorPhysicalUnitary SB SC UB UC U
      (submoduleTensorEmbedding SB SC x) =
    submoduleTensorEmbedding SB SC
      (conjugateUnitaryTransport
        (activeSectorCoordinateTransport SB SC UB UC)
        (unitaryLTensor WB (unitaryRTensor U NC)) x)
  exact activeSectorPhysicalUnitary_apply_embedding SB SC UB UC U x

/--
Conjugating a compressed active-sector operator by the physical lift is
exactly conjugation by its prescribed active coordinate unitary.  In
particular, arbitrary choices made by the ambient extension are invisible on
operators reconstructed through the sector embedding.
-/
theorem activeSectorPhysicalUnitary_conj_embedding_compression
    {B C WB NB WC NC : Type u} [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B] [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C] [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC] (SB : Submodule Complex B) (SC : Submodule Complex C)
    (UB : Semantics.UnitaryTransport SB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport SC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC))
    (P : Semantics.Operator (Semantics.CompositeSystem SB SC)) :
    (activeSectorPhysicalUnitary SB SC UB UC U).conjOperator
        ((submoduleTensorEmbedding SB SC).toLinearMap.comp
          (P.comp (LinearMap.adjoint (submoduleTensorEmbedding SB SC).toLinearMap))) =
      (submoduleTensorEmbedding SB SC).toLinearMap.comp
        (((conjugateUnitaryTransport
          (activeSectorCoordinateTransport SB SC UB UC)
          (unitaryLTensor WB (unitaryRTensor U NC))).conjOperator P).comp
          (LinearMap.adjoint (submoduleTensorEmbedding SB SC).toLinearMap)) := by
  apply unitaryTransport_conj_embedding_compression_of_intertwines
  exact activeSectorPhysicalUnitary_intertwines_embedding SB SC UB UC U

/-- Factoring a register exposes the local extension as a tensor with the complement identity. -/
theorem registerFactorization_conj_extendLocalToRegister
    {ι : Type u} [Fintype ι] [DecidableEq ι] (q : ι → Nat)
    (S : Semantics.QuditSubsystem q) (P : Semantics.Operator S.selectedSystem) :
    S.registerFactorization.conjOperator (S.extendLocalToRegister P) =
      TensorProduct.map P (1 : Semantics.Operator S.complementSystem) := by
  unfold Semantics.QuditSubsystem.extendLocalToRegister
    Semantics.QuditSubsystem.extendLocal
  rw [S.registerFactorization.conjOperator_symm_conjOperator]
  rfl

/--
Right tensoring transports the left operator by conjugation and leaves the
right identity unchanged.  This is the `AB` half of the common-coordinate
support calculation.
-/
theorem unitaryRTensor_conj_tensorMap_left
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (J : Type u)
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (A : Semantics.Operator H) :
    (unitaryRTensor U J).conjOperator
        (TensorProduct.map A (1 : Semantics.Operator J)) =
      TensorProduct.map (U.conjOperator A) (1 : Semantics.Operator J) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul h j =>
      simp [unitaryRTensor, Semantics.UnitaryTransport.conjOperator]
  | add x y hx hy => simp [map_add, hx, hy]

/-- Right tensoring transports a right operator while preserving a left identity. -/
theorem unitaryRTensor_conj_tensorMap_right
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (J : Type u)
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (A : Semantics.Operator J) :
    (unitaryRTensor U J).conjOperator
        (TensorProduct.map (1 : Semantics.Operator H) A) =
      TensorProduct.map (1 : Semantics.Operator K) A := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul h j =>
      simp [unitaryRTensor, Semantics.UnitaryTransport.conjOperator]
  | add x y hx hy => simp [map_add, hx, hy]

/--
Left tensoring leaves the left operator and identity extension unchanged.
This is the complementary `CD` support calculation.
-/
theorem unitaryLTensor_conj_tensorMap_right
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (I : Type u) [NormedAddCommGroup I] [InnerProductSpace Complex I]
    [Semantics.FiniteQuantumSystem I] (U : Semantics.UnitaryTransport H K)
    (A : Semantics.Operator I) :
    (unitaryLTensor I U).conjOperator
        (TensorProduct.map A (1 : Semantics.Operator H)) =
      TensorProduct.map A (1 : Semantics.Operator K) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul i h =>
      simp [unitaryLTensor, Semantics.UnitaryTransport.conjOperator]
  | add x y hx hy => simp [map_add, hx, hy]

/-- Left tensoring transports a right operator while preserving a left identity. -/
theorem unitaryLTensor_conj_tensorMap_left
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (I : Type u) [NormedAddCommGroup I] [InnerProductSpace Complex I]
    [Semantics.FiniteQuantumSystem I] (U : Semantics.UnitaryTransport H K)
    (A : Semantics.Operator H) :
    (unitaryLTensor I U).conjOperator
        (TensorProduct.map (1 : Semantics.Operator I) A) =
      TensorProduct.map (1 : Semantics.Operator I) (U.conjOperator A) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul i h =>
      simp [unitaryLTensor, Semantics.UnitaryTransport.conjOperator]
  | add x y hx hy => simp [map_add, hx, hy]

/-- The canonical associator sends a pure left-associated tensor to the right-associated form. -/
@[simp]
theorem tensorAssociatorUnitary_apply_tmul
    (H K J : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (h : H) (k : K) (j : J) :
    tensorAssociatorUnitary H K J ((h ⊗ₜ[Complex] k) ⊗ₜ[Complex] j) =
      h ⊗ₜ[Complex] (k ⊗ₜ[Complex] j) := by
  rfl

/-- The inverse associator restores a pure right-associated tensor. -/
@[simp]
theorem tensorAssociatorUnitary_symm_apply_tmul
    (H K J : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (h : H) (k : K) (j : J) :
    (tensorAssociatorUnitary H K J).symm (h ⊗ₜ[Complex] (k ⊗ₜ[Complex] j)) =
      (h ⊗ₜ[Complex] k) ⊗ₜ[Complex] j := by
  rfl

/-- The explicit linear equivalence of the associator has the same pure-tensor action. -/
@[simp]
theorem tensorAssociatorUnitary_toLinearEquiv_apply_tmul
    (H K J : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (h : H) (k : K) (j : J) :
    (tensorAssociatorUnitary H K J).toLinearEquiv ((h ⊗ₜ[Complex] k) ⊗ₜ[Complex] j) =
      h ⊗ₜ[Complex] (k ⊗ₜ[Complex] j) :=
  rfl

/-- The explicit linear equivalence of the inverse associator restores pure tensors. -/
@[simp]
theorem tensorAssociatorUnitary_symm_toLinearEquiv_apply_tmul
    (H K J : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (h : H) (k : K) (j : J) :
    (tensorAssociatorUnitary H K J).symm.toLinearEquiv
        (h ⊗ₜ[Complex] (k ⊗ₜ[Complex] j)) =
      (h ⊗ₜ[Complex] k) ⊗ₜ[Complex] j :=
  rfl

/-- Associator conjugation preserves the three individual tensor operator factors. -/
theorem tensorAssociatorUnitary_conj_tensorMap
    {H K J : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (A : Semantics.Operator H) (B : Semantics.Operator K) (C : Semantics.Operator J) :
    (tensorAssociatorUnitary H K J).conjOperator
        (TensorProduct.map (TensorProduct.map A B) C) =
      TensorProduct.map A (TensorProduct.map B C) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul hk j =>
      induction j using TensorProduct.induction_on with
      | zero => simp
      | tmul h k =>
          simp [tensorAssociatorUnitary, Semantics.UnitaryTransport.conjOperator]
      | add x y hx hy =>
          simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  | add x y hx hy => simp [map_add, hx, hy]

/-- The inverse associator transports a three-factor operator back to left association. -/
theorem tensorAssociatorUnitary_symm_conj_tensorMap
    {H K J : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (A : Semantics.Operator H) (B : Semantics.Operator K) (C : Semantics.Operator J) :
    (tensorAssociatorUnitary H K J).symm.conjOperator
        (TensorProduct.map A (TensorProduct.map B C)) =
      TensorProduct.map (TensorProduct.map A B) C := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul h kj =>
      induction h using TensorProduct.induction_on with
      | zero => simp
      | tmul k j =>
          simp [tensorAssociatorUnitary, Semantics.UnitaryTransport.conjOperator]
      | add x y hx hy =>
          simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hx hy
  | add x y hx hy => simp [map_add, hx, hy]

/-- Swap two finite tensor factors as a unitary coordinate transport. -/
noncomputable def tensorSwapUnitary
    (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K] :
    Semantics.UnitaryTransport (Semantics.CompositeSystem H K)
      (Semantics.CompositeSystem K H) := by
  let e := TensorProduct.commIsometry Complex H K
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := e.inner_map_map }

/-- The concrete tensor swap exchanges pure tensors. -/
@[simp]
theorem tensorSwapUnitary_apply_tmul
    (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (h : H) (k : K) :
    tensorSwapUnitary H K (h ⊗ₜ[Complex] k) = k ⊗ₜ[Complex] h :=
  rfl

/-- The explicit linear equivalence underlying the tensor swap exchanges pure tensors. -/
@[simp]
theorem tensorSwapUnitary_toLinearEquiv_apply_tmul
    (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (h : H) (k : K) :
    (tensorSwapUnitary H K).toLinearEquiv (h ⊗ₜ[Complex] k) = k ⊗ₜ[Complex] h :=
  rfl

/-- Swapping two factors exchanges the two tensor-product operator factors. -/
theorem tensorSwapUnitary_conj_tensorMap
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (A : Semantics.Operator H) (B : Semantics.Operator K) :
    (tensorSwapUnitary H K).conjOperator (TensorProduct.map A B) =
      TensorProduct.map B A := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul h k =>
      simp [tensorSwapUnitary, Semantics.UnitaryTransport.conjOperator]
  | add x y hx hy => simp [map_add, hx, hy]

/--
Embed an overlap vector on the right of a fixed left vector.  Matrix elements
of an `A tensor B` operator against these maps are the generators of its
interaction algebra on `B`.
-/
noncomputable def overlapLeftEmbedding
    (A B : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (a : A) : B →ₗ[Complex] Semantics.CompositeSystem A B :=
  TensorProduct.mk Complex A B a

@[simp]
theorem overlapLeftEmbedding_apply
    (A B : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (a : A) (b : B) :
    overlapLeftEmbedding A B a b = a ⊗ₜ[Complex] b :=
  rfl

/--
Embed an overlap vector on the left of a fixed right vector.  These maps give
the coefficient operators of a `B tensor C` operator on the same overlap.
-/
noncomputable def overlapRightEmbedding
    (B C : Type u)
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (c : C) : B →ₗ[Complex] Semantics.CompositeSystem B C :=
  (TensorProduct.mk Complex B C).flip c

@[simp]
theorem overlapRightEmbedding_apply
    (B C : Type u)
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (c : C) (b : B) :
    overlapRightEmbedding B C c b = b ⊗ₜ[Complex] c :=
  rfl

/-- Contracting a left embedding against a pure tensor gives its ordinary matrix element. -/
theorem adjoint_overlapLeftEmbedding_apply_tmul
    (A B : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (a a' : A) (b : B) :
    LinearMap.adjoint (overlapLeftEmbedding A B a) (a' ⊗ₜ[Complex] b) =
      (inner Complex a a') • b := by
  apply (ext_iff_inner_left Complex).mpr
  intro test
  rw [LinearMap.adjoint_inner_right]
  simp [overlapLeftEmbedding, TensorProduct.inner_tmul, inner_smul_right, mul_comm]

/-- Contracting a right embedding against a pure tensor gives its ordinary matrix element. -/
theorem adjoint_overlapRightEmbedding_apply_tmul
    (B C : Type u)
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (c c' : C) (b : B) :
    LinearMap.adjoint (overlapRightEmbedding B C c) (b ⊗ₜ[Complex] c') =
      (inner Complex c c') • b := by
  apply (ext_iff_inner_left Complex).mpr
  intro test
  rw [LinearMap.adjoint_inner_right]
  simp [overlapRightEmbedding, TensorProduct.inner_tmul, inner_smul_right, mul_comm]

/--
The fixed-right-factor embedding is an isometry exactly when its chosen
right-factor vector has unit norm.  This elementary contraction identity is
the reconstruction mechanism for a BV03 tensor block: after the interaction
coefficients have been shown to act as `L tensor 1`, contracting the inert
factor produces the left block operator without making any spectral choice.
-/
theorem adjoint_overlapRightEmbedding_comp_overlapRightEmbedding
    (A B : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (b b' : B) :
    (LinearMap.adjoint (overlapRightEmbedding A B b)).comp
      (overlapRightEmbedding A B b') =
        (inner Complex b b') • (1 : Semantics.Operator A) := by
  apply LinearMap.ext
  intro a
  change LinearMap.adjoint (overlapRightEmbedding A B b) (a ⊗ₜ[Complex] b') = _
  rw [adjoint_overlapRightEmbedding_apply_tmul]
  simp

/-- Contract an `A tensor B` operator against a fixed normalized `B` vector. -/
noncomputable def rightTensorCompression
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (eta : B) (T : Semantics.Operator (Semantics.CompositeSystem A B)) :
    Semantics.Operator A :=
  (LinearMap.adjoint (overlapRightEmbedding A B eta)).comp
    (T.comp (overlapRightEmbedding A B eta))

/--
Compressing a literal `T tensor 1` block by a unit vector on the inert factor
recovers `T`.  The next reconstruction theorem uses this to define the left
projector in the BV03 block from the transported overlap projector itself.
-/
theorem rightTensorCompression_tensorMap_left
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (T : Semantics.Operator A) (eta : B) (heta : ‖eta‖ = 1) :
    rightTensorCompression eta (TensorProduct.map T (1 : Semantics.Operator B)) = T := by
  apply LinearMap.ext
  intro a
  change LinearMap.adjoint (overlapRightEmbedding A B eta)
      ((TensorProduct.map T (1 : Semantics.Operator B))
        (overlapRightEmbedding A B eta a)) = T a
  change LinearMap.adjoint (overlapRightEmbedding A B eta) (T a ⊗ₜ[Complex] eta) = T a
  rw [adjoint_overlapRightEmbedding_apply_tmul]
  rw [inner_self_eq_norm_sq_to_K, heta]
  norm_num

/--
Reassociating `A tensor (W tensor N)` and then fixing the `A` factor is the
same map as first fixing `A` inside `A tensor W` and tensoring with `N`.
This naturality identity lets the coefficient reconstruction below keep the
full operator equality in its source parenthesization.
-/
theorem tensorAssociatorUnitary_symm_comp_overlapLeftEmbedding
    (A W N : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (a : A) :
    (tensorAssociatorUnitary A W N).symm.toLinearEquiv.toLinearMap.comp
      (overlapLeftEmbedding A (Semantics.CompositeSystem W N) a) =
        TensorProduct.map (overlapLeftEmbedding A W a) (1 : Semantics.Operator N) := by
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul w n => rfl
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

/--
Taking adjoints of the preceding naturality equation moves the associator to
the other side of the coefficient sandwich.  This is the exact identity used
to factor a reconstructed overlap projector as `P_left tensor 1`.
-/
theorem adjoint_overlapLeftEmbedding_comp_tensorAssociatorUnitary
    (A W N : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (a : A) :
    (LinearMap.adjoint (overlapLeftEmbedding A (Semantics.CompositeSystem W N) a)).comp
      (tensorAssociatorUnitary A W N).toLinearEquiv.toLinearMap =
        TensorProduct.map (LinearMap.adjoint (overlapLeftEmbedding A W a))
          (1 : Semantics.Operator N) := by
  have h := congrArg LinearMap.adjoint
    (tensorAssociatorUnitary_symm_comp_overlapLeftEmbedding A W N a)
  have hunit :
      LinearMap.adjoint (tensorAssociatorUnitary A W N).symm.toLinearEquiv.toLinearMap =
        (tensorAssociatorUnitary A W N).toLinearEquiv.toLinearMap := by
    simpa [Semantics.UnitaryTransport.symm_toLinearEquiv] using
      (Semantics.UnitaryTransport.adjoint_toLinearMap (tensorAssociatorUnitary A W N).symm)
  rw [LinearMap.adjoint_comp] at h
  rw [hunit] at h
  simpa only [TensorProduct.adjoint_map, LinearMap.adjoint_one] using h

/--
The associator sends the nested embedding of a `W` vector with fixed exterior
coordinates to the corresponding embedding in `A tensor (W tensor N)`.
This is the common coordinate identity which makes tensor-factor compression
commute with taking a left interaction coefficient.
-/
theorem tensorAssociatorUnitary_comp_nestedOverlapEmbeddings
    (A W N : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (a : A) (eta : N) :
    (tensorAssociatorUnitary A W N).toLinearEquiv.toLinearMap.comp
      ((overlapRightEmbedding (Semantics.CompositeSystem A W) N eta).comp
        (overlapLeftEmbedding A W a)) =
      (overlapLeftEmbedding A (Semantics.CompositeSystem W N) a).comp
        (overlapRightEmbedding W N eta) := by
  apply LinearMap.ext
  intro w
  rfl

/--
Extend an `A tensor W` operator by the identity on `N`, expressed back in the
source association `A tensor (W tensor N)`.
-/
noncomputable def rightTensorExtensionAfterLeft
    (A W N : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (T : Semantics.Operator (Semantics.CompositeSystem A W)) :
    Semantics.Operator (Semantics.CompositeSystem A (Semantics.CompositeSystem W N)) :=
  (tensorAssociatorUnitary A W N).conjOperator
    (TensorProduct.map T (1 : Semantics.Operator N))

/--
The `B`-coefficient of an `A tensor B` operator.  The source proof calls the
star algebra generated by these coefficients the left interaction algebra.
-/
noncomputable def leftInteractionCoefficient
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B)) (a a' : A) :
    Semantics.Operator B :=
  (LinearMap.adjoint (overlapLeftEmbedding A B a)).comp
    (P.comp (overlapLeftEmbedding A B a'))

/-- The left interaction coefficient of the zero overlap operator is zero. -/
theorem leftInteractionCoefficient_zero
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (a a' : A) :
    leftInteractionCoefficient (0 : Semantics.Operator (Semantics.CompositeSystem A B)) a a' = 0 := by
  simp [leftInteractionCoefficient]

/--
Tensoring a unitary on the overlap factor carries a fixed-left embedding to
the corresponding embedding before transport.  This makes the coefficient
calculation for an isotypic block an equality of operators, not merely an
equality of matrix elements.
-/
theorem unitaryLTensor_symm_comp_overlapLeftEmbedding
    {A H K : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (a : A) :
    (unitaryLTensor A U).symm.toLinearEquiv.toLinearMap.comp
      (overlapLeftEmbedding A K a) =
        (overlapLeftEmbedding A H a).comp U.symm.toLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro vector
  rfl

/-- Taking adjoints gives the companion fixed-left coefficient identity. -/
theorem adjoint_overlapLeftEmbedding_comp_unitaryLTensor
    {A H K : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (a : A) :
    (LinearMap.adjoint (overlapLeftEmbedding A K a)).comp
      (unitaryLTensor A U).toLinearEquiv.toLinearMap =
        U.toLinearEquiv.toLinearMap.comp
          (LinearMap.adjoint (overlapLeftEmbedding A H a)) := by
  have h := congrArg LinearMap.adjoint
    (unitaryLTensor_symm_comp_overlapLeftEmbedding (A := A) U a)
  simp only [LinearMap.adjoint_comp] at h
  have hleft :
      LinearMap.adjoint (unitaryLTensor A U).symm.toLinearEquiv.toLinearMap =
        (unitaryLTensor A U).toLinearEquiv.toLinearMap := by
    simpa [Semantics.UnitaryTransport.symm_toLinearEquiv] using
      (Semantics.UnitaryTransport.adjoint_toLinearMap (unitaryLTensor A U).symm)
  have hright :
      LinearMap.adjoint U.symm.toLinearEquiv.toLinearMap = U.toLinearEquiv.toLinearMap := by
    simpa [Semantics.UnitaryTransport.symm_toLinearEquiv] using
      (Semantics.UnitaryTransport.adjoint_toLinearMap U.symm)
  rw [hleft, hright] at h
  simpa only using h

/--
Left interaction coefficients commute with tensoring a unitary transport on
the overlap factor.  It transports the coefficient by the same unitary.
-/
theorem leftInteractionCoefficient_unitaryLTensor_conjOperator
    {A H K : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K)
    (T : Semantics.Operator (Semantics.CompositeSystem A H)) (a a' : A) :
    leftInteractionCoefficient ((unitaryLTensor A U).conjOperator T) a a' =
      U.conjOperator (leftInteractionCoefficient T a a') := by
  have htensorSymm :
      (unitaryLTensor A U).toLinearEquiv.symm.toLinearMap =
        (unitaryLTensor A U).symm.toLinearEquiv.toLinearMap := by
    rfl
  have hUSymm : U.toLinearEquiv.symm.toLinearMap = U.symm.toLinearEquiv.toLinearMap := by
    rfl
  unfold leftInteractionCoefficient Semantics.UnitaryTransport.conjOperator
  rw [htensorSymm, hUSymm]
  calc
    _ = ((LinearMap.adjoint (overlapLeftEmbedding A K a)).comp
          (unitaryLTensor A U).toLinearEquiv.toLinearMap).comp
        (T.comp ((unitaryLTensor A U).symm.toLinearEquiv.toLinearMap.comp
          (overlapLeftEmbedding A K a'))) := by
          simp only [LinearMap.comp_assoc]
    _ = (U.toLinearEquiv.toLinearMap.comp
          (LinearMap.adjoint (overlapLeftEmbedding A H a))).comp
        (T.comp ((overlapLeftEmbedding A H a').comp U.symm.toLinearEquiv.toLinearMap)) := by
          rw [adjoint_overlapLeftEmbedding_comp_unitaryLTensor U a,
            unitaryLTensor_symm_comp_overlapLeftEmbedding (A := A) U a']
    _ = U.toLinearEquiv.toLinearMap.comp
        (((LinearMap.adjoint (overlapLeftEmbedding A H a)).comp
          (T.comp (overlapLeftEmbedding A H a'))).comp U.symm.toLinearEquiv.toLinearMap) := by
          simp only [LinearMap.comp_assoc]

/--
The `A`-coefficients of a left block extended by an inert right tensor factor
are exactly the original coefficients tensored with the identity.  This is the
operator-level form of the source notation `Pi_{AB'} tensor 1_{B''}`.
-/
theorem leftInteractionCoefficient_rightTensorExtensionAfterLeft
    (A W N : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (T : Semantics.Operator (Semantics.CompositeSystem A W)) (a a' : A) :
    leftInteractionCoefficient (rightTensorExtensionAfterLeft A W N T) a a' =
      TensorProduct.map (leftInteractionCoefficient T a a')
        (1 : Semantics.Operator N) := by
  unfold leftInteractionCoefficient rightTensorExtensionAfterLeft
    Semantics.UnitaryTransport.conjOperator
  change
    (LinearMap.adjoint (overlapLeftEmbedding A (Semantics.CompositeSystem W N) a)).comp
        (((tensorAssociatorUnitary A W N).toLinearEquiv.toLinearMap.comp
          ((TensorProduct.map T (1 : Semantics.Operator N)).comp
            (tensorAssociatorUnitary A W N).toLinearEquiv.symm.toLinearMap)).comp
          (overlapLeftEmbedding A (Semantics.CompositeSystem W N) a')) =
      TensorProduct.map
        ((LinearMap.adjoint (overlapLeftEmbedding A W a)).comp
          (T.comp (overlapLeftEmbedding A W a')))
        (1 : Semantics.Operator N)
  have hright :
      (tensorAssociatorUnitary A W N).toLinearEquiv.symm.toLinearMap.comp
        (overlapLeftEmbedding A (Semantics.CompositeSystem W N) a') =
          TensorProduct.map (overlapLeftEmbedding A W a') (1 : Semantics.Operator N) := by
    change (tensorAssociatorUnitary A W N).symm.toLinearEquiv.toLinearMap.comp
      (overlapLeftEmbedding A (Semantics.CompositeSystem W N) a') = _
    exact tensorAssociatorUnitary_symm_comp_overlapLeftEmbedding A W N a'
  calc
    _ = ((LinearMap.adjoint (overlapLeftEmbedding A (Semantics.CompositeSystem W N) a)).comp
          (tensorAssociatorUnitary A W N).toLinearEquiv.toLinearMap).comp
        ((TensorProduct.map T (1 : Semantics.Operator N)).comp
          ((tensorAssociatorUnitary A W N).toLinearEquiv.symm.toLinearMap.comp
            (overlapLeftEmbedding A (Semantics.CompositeSystem W N) a'))) := by
          simp only [LinearMap.comp_assoc]
    _ = (TensorProduct.map (LinearMap.adjoint (overlapLeftEmbedding A W a))
          (1 : Semantics.Operator N)).comp
        ((TensorProduct.map T (1 : Semantics.Operator N)).comp
          (TensorProduct.map (overlapLeftEmbedding A W a')
            (1 : Semantics.Operator N))) := by
          rw [adjoint_overlapLeftEmbedding_comp_tensorAssociatorUnitary A W N a, hright]
    _ = TensorProduct.map
        ((LinearMap.adjoint (overlapLeftEmbedding A W a)).comp
          (T.comp (overlapLeftEmbedding A W a')))
        (1 : Semantics.Operator N) := by
          rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
          rfl

/--
Taking a left interaction coefficient commutes with contracting the inert
factor after reassociation.  This identifies the coefficient of the recovered
left block with the normalized contraction of the displayed `L tensor 1`
coefficient, which is the key reconstruction step in the BV03 block proof.
-/
theorem leftInteractionCoefficient_rightTensorCompression_tensorAssociator
    (A W N : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (T : Semantics.Operator (Semantics.CompositeSystem A (Semantics.CompositeSystem W N)))
    (eta : N) (a a' : A) :
    leftInteractionCoefficient
      (rightTensorCompression eta ((tensorAssociatorUnitary A W N).symm.conjOperator T)) a a' =
      rightTensorCompression eta (leftInteractionCoefficient T a a') := by
  have hleft :
      (LinearMap.adjoint (overlapLeftEmbedding A W a)).comp
        ((LinearMap.adjoint
          (overlapRightEmbedding (Semantics.CompositeSystem A W) N eta)).comp
          (tensorAssociatorUnitary A W N).symm.toLinearEquiv.toLinearMap) =
        (LinearMap.adjoint (overlapRightEmbedding W N eta)).comp
          (LinearMap.adjoint
            (overlapLeftEmbedding A (Semantics.CompositeSystem W N) a)) := by
    have h := congrArg LinearMap.adjoint
      (tensorAssociatorUnitary_comp_nestedOverlapEmbeddings A W N a eta)
    simp only [LinearMap.adjoint_comp] at h
    have hunit :
        LinearMap.adjoint (tensorAssociatorUnitary A W N).toLinearEquiv.toLinearMap =
          (tensorAssociatorUnitary A W N).symm.toLinearEquiv.toLinearMap := by
      simpa [Semantics.UnitaryTransport.symm_toLinearEquiv] using
        (Semantics.UnitaryTransport.adjoint_toLinearMap (tensorAssociatorUnitary A W N))
    rw [hunit] at h
    simpa only [LinearMap.comp_assoc] using h
  have hdouble :
      (tensorAssociatorUnitary A W N).symm.toLinearEquiv.symm.toLinearMap =
        (tensorAssociatorUnitary A W N).toLinearEquiv.toLinearMap := by
    rfl
  unfold leftInteractionCoefficient rightTensorCompression
    Semantics.UnitaryTransport.conjOperator
  calc
    _ = (((LinearMap.adjoint (overlapLeftEmbedding A W a)).comp
          ((LinearMap.adjoint
            (overlapRightEmbedding (Semantics.CompositeSystem A W) N eta)).comp
            (tensorAssociatorUnitary A W N).symm.toLinearEquiv.toLinearMap)).comp T).comp
        ((tensorAssociatorUnitary A W N).toLinearEquiv.toLinearMap.comp
          ((overlapRightEmbedding (Semantics.CompositeSystem A W) N eta).comp
            (overlapLeftEmbedding A W a'))) := by
          rw [hdouble]
          simp only [LinearMap.comp_assoc]
    _ = (((LinearMap.adjoint (overlapRightEmbedding W N eta)).comp
          (LinearMap.adjoint
            (overlapLeftEmbedding A (Semantics.CompositeSystem W N) a))).comp T).comp
        ((overlapLeftEmbedding A (Semantics.CompositeSystem W N) a').comp
          (overlapRightEmbedding W N eta)) := by
          rw [hleft, tensorAssociatorUnitary_comp_nestedOverlapEmbeddings A W N a' eta]
    _ = _ := by
          simp only [LinearMap.comp_assoc]

/--
The `B`-coefficient of a `B tensor C` operator.  These generate the right
interaction algebra and are compared with the left coefficients below.
-/
noncomputable def rightInteractionCoefficient
    {B C : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C)) (c c' : C) :
    Semantics.Operator B :=
  (LinearMap.adjoint (overlapRightEmbedding B C c)).comp
    (Q.comp (overlapRightEmbedding B C c'))

/-- The right interaction coefficient of the zero overlap operator is zero. -/
theorem rightInteractionCoefficient_zero
    {B C : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (c c' : C) :
    rightInteractionCoefficient (0 : Semantics.Operator (Semantics.CompositeSystem B C)) c c' = 0 := by
  simp [rightInteractionCoefficient]

/-- Compress a right overlap operator along a Hilbert-space inclusion. -/
noncomputable def overlapRightCompression
    {H B C : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C)) (inclusion : H →ₗ[Complex] B) :
    Semantics.Operator (Semantics.CompositeSystem H C) :=
  (TensorProduct.map (LinearMap.adjoint inclusion) (1 : Semantics.Operator C)).comp
    (Q.comp (TensorProduct.map inclusion (1 : Semantics.Operator C)))

/-- Tensoring a unitary on the overlap factor carries fixed-right embeddings through it. -/
theorem unitaryRTensor_symm_comp_overlapRightEmbedding
    {H K C : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H K) (c : C) :
    (unitaryRTensor U C).symm.toLinearEquiv.toLinearMap.comp
      (overlapRightEmbedding K C c) =
        (overlapRightEmbedding H C c).comp U.symm.toLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro vector
  rfl

/-- Taking adjoints gives the companion fixed-right coefficient identity. -/
theorem adjoint_overlapRightEmbedding_comp_unitaryRTensor
    {H K C : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H K) (c : C) :
    (LinearMap.adjoint (overlapRightEmbedding K C c)).comp
      (unitaryRTensor U C).toLinearEquiv.toLinearMap =
        U.toLinearEquiv.toLinearMap.comp
          (LinearMap.adjoint (overlapRightEmbedding H C c)) := by
  have h := congrArg LinearMap.adjoint
    (unitaryRTensor_symm_comp_overlapRightEmbedding U c)
  simp only [LinearMap.adjoint_comp] at h
  have hleft :
      LinearMap.adjoint (unitaryRTensor U C).symm.toLinearEquiv.toLinearMap =
        (unitaryRTensor U C).toLinearEquiv.toLinearMap := by
    simpa [Semantics.UnitaryTransport.symm_toLinearEquiv] using
      (Semantics.UnitaryTransport.adjoint_toLinearMap (unitaryRTensor U C).symm)
  have hright :
      LinearMap.adjoint U.symm.toLinearEquiv.toLinearMap = U.toLinearEquiv.toLinearMap := by
    simpa [Semantics.UnitaryTransport.symm_toLinearEquiv] using
      (Semantics.UnitaryTransport.adjoint_toLinearMap U.symm)
  rw [hleft, hright] at h
  simpa only using h

/-- Right interaction coefficients commute with a unitary transport on the overlap factor. -/
theorem rightInteractionCoefficient_unitaryRTensor_conjOperator
    {H K C : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H K)
    (T : Semantics.Operator (Semantics.CompositeSystem H C)) (c c' : C) :
    rightInteractionCoefficient ((unitaryRTensor U C).conjOperator T) c c' =
      U.conjOperator (rightInteractionCoefficient T c c') := by
  have htensorSymm :
      (unitaryRTensor U C).toLinearEquiv.symm.toLinearMap =
        (unitaryRTensor U C).symm.toLinearEquiv.toLinearMap := by
    rfl
  have hUSymm : U.toLinearEquiv.symm.toLinearMap = U.symm.toLinearEquiv.toLinearMap := by
    rfl
  unfold rightInteractionCoefficient Semantics.UnitaryTransport.conjOperator
  rw [htensorSymm, hUSymm]
  calc
    _ = ((LinearMap.adjoint (overlapRightEmbedding K C c)).comp
          (unitaryRTensor U C).toLinearEquiv.toLinearMap).comp
        (T.comp ((unitaryRTensor U C).symm.toLinearEquiv.toLinearMap.comp
          (overlapRightEmbedding K C c'))) := by
          simp only [LinearMap.comp_assoc]
    _ = (U.toLinearEquiv.toLinearMap.comp
          (LinearMap.adjoint (overlapRightEmbedding H C c))).comp
        (T.comp ((overlapRightEmbedding H C c').comp U.symm.toLinearEquiv.toLinearMap)) := by
          rw [adjoint_overlapRightEmbedding_comp_unitaryRTensor U c,
            unitaryRTensor_symm_comp_overlapRightEmbedding U c']
    _ = U.toLinearEquiv.toLinearMap.comp
        (((LinearMap.adjoint (overlapRightEmbedding H C c)).comp
          (T.comp (overlapRightEmbedding H C c'))).comp U.symm.toLinearEquiv.toLinearMap) := by
          simp only [LinearMap.comp_assoc]

/-- A right tensor action intertwines with the left overlap embedding. -/
theorem tensorMap_right_comp_overlapLeftEmbedding
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (a : A) (Z : Semantics.Operator B) :
    (TensorProduct.map (1 : Semantics.Operator A) Z).comp (overlapLeftEmbedding A B a) =
      (overlapLeftEmbedding A B a).comp Z := by
  apply LinearMap.ext
  intro vector
  simp [overlapLeftEmbedding]

/-- Taking adjoints gives the left-coefficient pull-through identity. -/
theorem adjoint_overlapLeftEmbedding_comp_tensorMap_right
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (a : A) (Z : Semantics.Operator B) :
    (LinearMap.adjoint (overlapLeftEmbedding A B a)).comp
      (TensorProduct.map (1 : Semantics.Operator A) Z) =
      Z.comp (LinearMap.adjoint (overlapLeftEmbedding A B a)) := by
  have h := tensorMap_right_comp_overlapLeftEmbedding (a := a) (Z := LinearMap.adjoint Z)
  have hadjoint := congrArg LinearMap.adjoint h
  simpa [LinearMap.adjoint_comp] using hadjoint

/-- A left tensor action intertwines with the right overlap embedding. -/
theorem tensorMap_left_comp_overlapRightEmbedding
    {B C : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (c : C) (Z : Semantics.Operator B) :
    (TensorProduct.map Z (1 : Semantics.Operator C)).comp (overlapRightEmbedding B C c) =
      (overlapRightEmbedding B C c).comp Z := by
  apply LinearMap.ext
  intro vector
  simp [overlapRightEmbedding]

/-- Taking adjoints gives the right-coefficient pull-through identity. -/
theorem adjoint_overlapRightEmbedding_comp_tensorMap_left
    {B C : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (c : C) (Z : Semantics.Operator B) :
    (LinearMap.adjoint (overlapRightEmbedding B C c)).comp
      (TensorProduct.map Z (1 : Semantics.Operator C)) =
      Z.comp (LinearMap.adjoint (overlapRightEmbedding B C c)) := by
  have h := tensorMap_left_comp_overlapRightEmbedding (c := c) (Z := LinearMap.adjoint Z)
  have hadjoint := congrArg LinearMap.adjoint h
  simpa [LinearMap.adjoint_comp] using hadjoint

/--
The left interaction coefficients determine an operator on `A tensor B`.
This is the coefficientwise reconstruction principle used to turn the
isotypic `B' tensor B''` actions back into an equality of the source
projectors, rather than leaving the block factorization at matrix-element
level.
-/
theorem operator_eq_of_leftInteractionCoefficients_eq
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P Q : Semantics.Operator (Semantics.CompositeSystem A B))
    (hcoefficients : ∀ a a' : A,
      leftInteractionCoefficient P a a' = leftInteractionCoefficient Q a a') :
    P = Q := by
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul left right =>
      apply TensorProduct.ext_iff_inner_left.mpr
      intro testLeft testRight
      change inner Complex
          (overlapLeftEmbedding A B testLeft testRight)
          (P (overlapLeftEmbedding A B left right)) =
        inner Complex
          (overlapLeftEmbedding A B testLeft testRight)
          (Q (overlapLeftEmbedding A B left right))
      calc
        inner Complex
            (overlapLeftEmbedding A B testLeft testRight)
            (P (overlapLeftEmbedding A B left right)) =
            inner Complex testRight
              (leftInteractionCoefficient P testLeft left right) := by
                change inner Complex
                    (overlapLeftEmbedding A B testLeft testRight)
                    (P (overlapLeftEmbedding A B left right)) =
                  inner Complex testRight
                    (LinearMap.adjoint (overlapLeftEmbedding A B testLeft)
                      (P (overlapLeftEmbedding A B left right)))
                exact (LinearMap.adjoint_inner_right
                  (overlapLeftEmbedding A B testLeft) testRight
                  (P (overlapLeftEmbedding A B left right))).symm
        _ = inner Complex testRight
              (leftInteractionCoefficient Q testLeft left right) := by
                rw [hcoefficients]
        _ = inner Complex
            (overlapLeftEmbedding A B testLeft testRight)
            (Q (overlapLeftEmbedding A B left right)) := by
                change inner Complex testRight
                    (LinearMap.adjoint (overlapLeftEmbedding A B testLeft)
                      (Q (overlapLeftEmbedding A B left right))) =
                  inner Complex
                    (overlapLeftEmbedding A B testLeft testRight)
                    (Q (overlapLeftEmbedding A B left right))
                exact LinearMap.adjoint_inner_right
                  (overlapLeftEmbedding A B testLeft) testRight
                  (Q (overlapLeftEmbedding A B left right))
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

/--
BV03 left-block reconstruction.  If every left interaction coefficient of an
operator on `A tensor (W tensor N)` is an operator on `W` tensored with the
identity on `N`, then contracting a unit vector of `N` constructs the unique
left block and recovers the full operator as that block tensored with `1_N`.
This is the first operator equality behind the source tensor-block
factorization, rather than a statement only about its coefficient algebra.
-/
theorem exists_rightTensorExtensionAfterLeft_of_leftInteractionCoefficients_tensor
    (A W N : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (T : Semantics.Operator (Semantics.CompositeSystem A (Semantics.CompositeSystem W N)))
    (eta : N) (heta : ‖eta‖ = 1)
    (hcoefficients : ∀ a a' : A, ∃ R : Semantics.Operator W,
      leftInteractionCoefficient T a a' =
        TensorProduct.map R (1 : Semantics.Operator N)) :
    ∃ Tleft : Semantics.Operator (Semantics.CompositeSystem A W),
      T = rightTensorExtensionAfterLeft A W N Tleft := by
  let Tleft : Semantics.Operator (Semantics.CompositeSystem A W) :=
    rightTensorCompression eta ((tensorAssociatorUnitary A W N).symm.conjOperator T)
  refine ⟨Tleft, ?_⟩
  apply operator_eq_of_leftInteractionCoefficients_eq
  intro a a'
  rcases hcoefficients a a' with ⟨R, hR⟩
  rw [leftInteractionCoefficient_rightTensorExtensionAfterLeft]
  dsimp [Tleft]
  rw [leftInteractionCoefficient_rightTensorCompression_tensorAssociator]
  rw [hR]
  rw [rightTensorCompression_tensorMap_left R eta heta]

/-- The fixed-left-factor embedding is an isometry for a normalized vector. -/
theorem adjoint_overlapLeftEmbedding_comp_overlapLeftEmbedding
    (A B : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (a a' : A) :
    (LinearMap.adjoint (overlapLeftEmbedding A B a)).comp
      (overlapLeftEmbedding A B a') =
        (inner Complex a a') • (1 : Semantics.Operator B) := by
  apply LinearMap.ext
  intro b
  change LinearMap.adjoint (overlapLeftEmbedding A B a) (a' ⊗ₜ[Complex] b) = _
  rw [adjoint_overlapLeftEmbedding_apply_tmul]
  simp

/-- Contract an `A tensor B` operator against a fixed normalized left vector. -/
noncomputable def leftTensorCompression
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (eta : A) (T : Semantics.Operator (Semantics.CompositeSystem A B)) :
    Semantics.Operator B :=
  (LinearMap.adjoint (overlapLeftEmbedding A B eta)).comp
    (T.comp (overlapLeftEmbedding A B eta))

/-- Compressing `1 tensor T` by a unit left vector recovers `T`. -/
theorem leftTensorCompression_tensorMap_right
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (T : Semantics.Operator B) (eta : A) (heta : ‖eta‖ = 1) :
    leftTensorCompression eta (TensorProduct.map (1 : Semantics.Operator A) T) = T := by
  apply LinearMap.ext
  intro b
  change LinearMap.adjoint (overlapLeftEmbedding A B eta)
      ((TensorProduct.map (1 : Semantics.Operator A) T)
        (overlapLeftEmbedding A B eta b)) = T b
  change LinearMap.adjoint (overlapLeftEmbedding A B eta) (eta ⊗ₜ[Complex] T b) = T b
  rw [adjoint_overlapLeftEmbedding_apply_tmul]
  rw [inner_self_eq_norm_sq_to_K, heta]
  norm_num

/-- Every nontrivial complex normed space contains a normalized vector. -/
theorem exists_normalized_vector_of_nontrivial
    {H : Type u} [NormedAddCommGroup H] [NormedSpace Complex H] [Nontrivial H] :
    ∃ eta : H, ‖eta‖ = 1 := by
  obtain ⟨vector, hvector⟩ := exists_ne (0 : H)
  refine ⟨(‖vector‖ : Complex)⁻¹ • vector, ?_⟩
  have hnorm : ‖vector‖ ≠ 0 := norm_ne_zero_iff.mpr hvector
  rw [norm_smul]
  simp [Complex.norm_real, abs_of_nonneg (norm_nonneg vector), hnorm]

/-- Reassociation carries a fixed right embedding through an untouched left factor. -/
theorem tensorAssociatorUnitary_comp_overlapRightEmbedding
    (W N C : Type u)
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (c : C) :
    (tensorAssociatorUnitary W N C).toLinearEquiv.toLinearMap.comp
      (overlapRightEmbedding (Semantics.CompositeSystem W N) C c) =
        TensorProduct.map (1 : Semantics.Operator W)
          (overlapRightEmbedding N C c) := by
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul w n => rfl
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

/-- Taking adjoints gives the companion right-coefficient associator identity. -/
theorem adjoint_overlapRightEmbedding_comp_tensorAssociatorUnitary_symm
    (W N C : Type u)
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (c : C) :
    (LinearMap.adjoint
      (overlapRightEmbedding (Semantics.CompositeSystem W N) C c)).comp
      (tensorAssociatorUnitary W N C).symm.toLinearEquiv.toLinearMap =
        TensorProduct.map (1 : Semantics.Operator W)
          (LinearMap.adjoint (overlapRightEmbedding N C c)) := by
  have h := congrArg LinearMap.adjoint
    (tensorAssociatorUnitary_comp_overlapRightEmbedding W N C c)
  have hunit :
      LinearMap.adjoint (tensorAssociatorUnitary W N C).toLinearEquiv.toLinearMap =
        (tensorAssociatorUnitary W N C).symm.toLinearEquiv.toLinearMap := by
    simpa [Semantics.UnitaryTransport.symm_toLinearEquiv] using
      (Semantics.UnitaryTransport.adjoint_toLinearMap (tensorAssociatorUnitary W N C))
  rw [LinearMap.adjoint_comp] at h
  rw [hunit] at h
  simpa only [TensorProduct.adjoint_map, LinearMap.adjoint_one] using h

/-- Reassociation identifies the nested right embeddings used by right coefficients. -/
theorem tensorAssociatorUnitary_symm_comp_nestedOverlapRightEmbeddings
    (W N C : Type u)
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (eta : W) (c : C) :
    (tensorAssociatorUnitary W N C).symm.toLinearEquiv.toLinearMap.comp
      ((overlapLeftEmbedding W (Semantics.CompositeSystem N C) eta).comp
        (overlapRightEmbedding N C c)) =
      (overlapRightEmbedding (Semantics.CompositeSystem W N) C c).comp
        (overlapLeftEmbedding W N eta) := by
  apply LinearMap.ext
  intro vector
  rfl

/-- Extend an `N tensor C` operator by the identity on `W`, in left association. -/
noncomputable def leftTensorExtensionBeforeRight
    (W N C : Type u)
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (T : Semantics.Operator (Semantics.CompositeSystem N C)) :
    Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem W N) C) :=
  (tensorAssociatorUnitary W N C).symm.conjOperator
    (TensorProduct.map (1 : Semantics.Operator W) T)

/-- The right coefficients of `1_W tensor T` are `1_W tensor` the right coefficients of `T`. -/
theorem rightInteractionCoefficient_leftTensorExtensionBeforeRight
    (W N C : Type u)
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (T : Semantics.Operator (Semantics.CompositeSystem N C)) (c c' : C) :
    rightInteractionCoefficient (leftTensorExtensionBeforeRight W N C T) c c' =
      TensorProduct.map (1 : Semantics.Operator W)
        (rightInteractionCoefficient T c c') := by
  unfold rightInteractionCoefficient leftTensorExtensionBeforeRight
    Semantics.UnitaryTransport.conjOperator
  change
    (LinearMap.adjoint
      (overlapRightEmbedding (Semantics.CompositeSystem W N) C c)).comp
      (((tensorAssociatorUnitary W N C).symm.toLinearEquiv.toLinearMap.comp
        ((TensorProduct.map (1 : Semantics.Operator W) T).comp
          (tensorAssociatorUnitary W N C).symm.toLinearEquiv.symm.toLinearMap)).comp
        (overlapRightEmbedding (Semantics.CompositeSystem W N) C c')) =
      TensorProduct.map (1 : Semantics.Operator W)
        ((LinearMap.adjoint (overlapRightEmbedding N C c)).comp
          (T.comp (overlapRightEmbedding N C c')))
  have hright :
      (tensorAssociatorUnitary W N C).symm.toLinearEquiv.symm.toLinearMap.comp
        (overlapRightEmbedding (Semantics.CompositeSystem W N) C c') =
          TensorProduct.map (1 : Semantics.Operator W)
            (overlapRightEmbedding N C c') := by
    change (tensorAssociatorUnitary W N C).toLinearEquiv.toLinearMap.comp
      (overlapRightEmbedding (Semantics.CompositeSystem W N) C c') = _
    exact tensorAssociatorUnitary_comp_overlapRightEmbedding W N C c'
  calc
    _ = ((LinearMap.adjoint
      (overlapRightEmbedding (Semantics.CompositeSystem W N) C c)).comp
        (tensorAssociatorUnitary W N C).symm.toLinearEquiv.toLinearMap).comp
      ((TensorProduct.map (1 : Semantics.Operator W) T).comp
        ((tensorAssociatorUnitary W N C).symm.toLinearEquiv.symm.toLinearMap.comp
          (overlapRightEmbedding (Semantics.CompositeSystem W N) C c'))) := by
        simp only [LinearMap.comp_assoc]
    _ = (TensorProduct.map (1 : Semantics.Operator W)
          (LinearMap.adjoint (overlapRightEmbedding N C c))).comp
        ((TensorProduct.map (1 : Semantics.Operator W) T).comp
          (TensorProduct.map (1 : Semantics.Operator W)
            (overlapRightEmbedding N C c'))) := by
          rw [adjoint_overlapRightEmbedding_comp_tensorAssociatorUnitary_symm W N C c,
            hright]
    _ = TensorProduct.map (1 : Semantics.Operator W)
        ((LinearMap.adjoint (overlapRightEmbedding N C c)).comp
          (T.comp (overlapRightEmbedding N C c'))) := by
          rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
          rfl

/-- Right coefficients commute with left-factor compression after reassociation. -/
theorem rightInteractionCoefficient_leftTensorCompression_tensorAssociator
    (W N C : Type u)
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (T : Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem W N) C))
    (eta : W) (c c' : C) :
    rightInteractionCoefficient
      (leftTensorCompression eta ((tensorAssociatorUnitary W N C).conjOperator T)) c c' =
      leftTensorCompression eta (rightInteractionCoefficient T c c') := by
  have hleft :
      (LinearMap.adjoint (overlapRightEmbedding N C c)).comp
        ((LinearMap.adjoint
          (overlapLeftEmbedding W (Semantics.CompositeSystem N C) eta)).comp
          (tensorAssociatorUnitary W N C).toLinearEquiv.toLinearMap) =
        (LinearMap.adjoint (overlapLeftEmbedding W N eta)).comp
          (LinearMap.adjoint
            (overlapRightEmbedding (Semantics.CompositeSystem W N) C c)) := by
    have h := congrArg LinearMap.adjoint
      (tensorAssociatorUnitary_symm_comp_nestedOverlapRightEmbeddings W N C eta c)
    simp only [LinearMap.adjoint_comp] at h
    have hunit :
        LinearMap.adjoint (tensorAssociatorUnitary W N C).symm.toLinearEquiv.toLinearMap =
          (tensorAssociatorUnitary W N C).toLinearEquiv.toLinearMap := by
      simpa [Semantics.UnitaryTransport.symm_toLinearEquiv] using
        (Semantics.UnitaryTransport.adjoint_toLinearMap (tensorAssociatorUnitary W N C).symm)
    rw [hunit] at h
    simpa only [LinearMap.comp_assoc] using h
  have hdouble :
      (tensorAssociatorUnitary W N C).toLinearEquiv.symm.toLinearMap =
        (tensorAssociatorUnitary W N C).symm.toLinearEquiv.toLinearMap := by
    rfl
  unfold rightInteractionCoefficient leftTensorCompression
    Semantics.UnitaryTransport.conjOperator
  calc
    _ = (((LinearMap.adjoint (overlapRightEmbedding N C c)).comp
      ((LinearMap.adjoint
        (overlapLeftEmbedding W (Semantics.CompositeSystem N C) eta)).comp
        (tensorAssociatorUnitary W N C).toLinearEquiv.toLinearMap)).comp T).comp
      ((tensorAssociatorUnitary W N C).symm.toLinearEquiv.toLinearMap.comp
        ((overlapLeftEmbedding W (Semantics.CompositeSystem N C) eta).comp
          (overlapRightEmbedding N C c'))) := by
          rw [hdouble]
          simp only [LinearMap.comp_assoc]
    _ = (((LinearMap.adjoint (overlapLeftEmbedding W N eta)).comp
      (LinearMap.adjoint
        (overlapRightEmbedding (Semantics.CompositeSystem W N) C c))).comp T).comp
      ((overlapRightEmbedding (Semantics.CompositeSystem W N) C c').comp
        (overlapLeftEmbedding W N eta)) := by
          rw [hleft,
            tensorAssociatorUnitary_symm_comp_nestedOverlapRightEmbeddings W N C eta c']
    _ = _ := by
          simp only [LinearMap.comp_assoc]

/--
Right interaction coefficients also determine an overlap operator.  This is
the `B tensor C` counterpart of left-coefficient reconstruction and is used to
turn a reducing interaction sector into commutation with the actual right
projector.
-/
theorem operator_eq_of_rightInteractionCoefficients_eq
    {B C : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hcoefficients : ∀ c c' : C,
      rightInteractionCoefficient P c c' = rightInteractionCoefficient Q c c') :
    P = Q := by
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul left right =>
      apply TensorProduct.ext_iff_inner_left.mpr
      intro testLeft testRight
      change inner Complex
          (overlapRightEmbedding B C testRight testLeft)
          (P (overlapRightEmbedding B C right left)) =
        inner Complex
          (overlapRightEmbedding B C testRight testLeft)
          (Q (overlapRightEmbedding B C right left))
      calc
        inner Complex
            (overlapRightEmbedding B C testRight testLeft)
            (P (overlapRightEmbedding B C right left)) =
            inner Complex testLeft
              (rightInteractionCoefficient P testRight right left) := by
                change inner Complex
                    (overlapRightEmbedding B C testRight testLeft)
                    (P (overlapRightEmbedding B C right left)) =
                  inner Complex testLeft
                    (LinearMap.adjoint (overlapRightEmbedding B C testRight)
                      (P (overlapRightEmbedding B C right left)))
                exact (LinearMap.adjoint_inner_right
                  (overlapRightEmbedding B C testRight) testLeft
                  (P (overlapRightEmbedding B C right left))).symm
        _ = inner Complex testLeft
              (rightInteractionCoefficient Q testRight right left) := by
                rw [hcoefficients]
        _ = inner Complex
            (overlapRightEmbedding B C testRight testLeft)
            (Q (overlapRightEmbedding B C right left)) := by
                change inner Complex testLeft
                    (LinearMap.adjoint (overlapRightEmbedding B C testRight)
                      (Q (overlapRightEmbedding B C right left))) =
                  inner Complex
                    (overlapRightEmbedding B C testRight testLeft)
                    (Q (overlapRightEmbedding B C right left))
                exact LinearMap.adjoint_inner_right
                  (overlapRightEmbedding B C testRight) testLeft
                  (Q (overlapRightEmbedding B C right left))
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

/--
BV03 right-block reconstruction.  Right coefficients which are identity on the
simple factor determine an actual `1_W tensor T_right` overlap operator.
-/
theorem exists_leftTensorExtensionBeforeRight_of_rightInteractionCoefficients_tensor
    (W N C : Type u)
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (T : Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem W N) C))
    (eta : W) (heta : ‖eta‖ = 1)
    (hcoefficients : ∀ c c' : C, ∃ R : Semantics.Operator N,
      rightInteractionCoefficient T c c' =
        TensorProduct.map (1 : Semantics.Operator W) R) :
    ∃ Tright : Semantics.Operator (Semantics.CompositeSystem N C),
      T = leftTensorExtensionBeforeRight W N C Tright := by
  let Tright : Semantics.Operator (Semantics.CompositeSystem N C) :=
    leftTensorCompression eta ((tensorAssociatorUnitary W N C).conjOperator T)
  refine ⟨Tright, ?_⟩
  apply operator_eq_of_rightInteractionCoefficients_eq
  intro c c'
  rcases hcoefficients c c' with ⟨R, hR⟩
  rw [rightInteractionCoefficient_leftTensorExtensionBeforeRight]
  dsimp [Tright]
  rw [rightInteractionCoefficient_leftTensorCompression_tensorAssociator]
  rw [hR]
  rw [leftTensorCompression_tensorMap_right R eta heta]

/-- A right tensor extension is pulled through a left interaction coefficient. -/
theorem leftInteractionCoefficient_mul_rightTensor
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Z : Semantics.Operator B) (a a' : A) :
    leftInteractionCoefficient (P * TensorProduct.map (1 : Semantics.Operator A) Z) a a' =
      leftInteractionCoefficient P a a' * Z := by
  unfold leftInteractionCoefficient
  simp only [Module.End.mul_eq_comp]
  rw [LinearMap.comp_assoc, tensorMap_right_comp_overlapLeftEmbedding]
  simp only [LinearMap.comp_assoc]

/-- A left tensor extension is pulled through a left interaction coefficient. -/
theorem leftInteractionCoefficient_leftTensor_mul
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Z : Semantics.Operator B) (a a' : A) :
    leftInteractionCoefficient (TensorProduct.map (1 : Semantics.Operator A) Z * P) a a' =
      Z * leftInteractionCoefficient P a a' := by
  unfold leftInteractionCoefficient
  simp only [Module.End.mul_eq_comp]
  rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc,
    adjoint_overlapLeftEmbedding_comp_tensorMap_right]
  simp only [LinearMap.comp_assoc]

/-- A left tensor extension is pulled through a right interaction coefficient. -/
theorem rightInteractionCoefficient_leftTensor_mul
    {B C : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (Z : Semantics.Operator B) (c c' : C) :
    rightInteractionCoefficient (TensorProduct.map Z (1 : Semantics.Operator C) * Q) c c' =
      Z * rightInteractionCoefficient Q c c' := by
  unfold rightInteractionCoefficient
  simp only [Module.End.mul_eq_comp]
  rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc,
    adjoint_overlapRightEmbedding_comp_tensorMap_left]
  simp only [LinearMap.comp_assoc]

/-- A right tensor extension is pulled through a right interaction coefficient. -/
theorem rightInteractionCoefficient_mul_leftTensor
    {B C : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (Z : Semantics.Operator B) (c c' : C) :
    rightInteractionCoefficient (Q * TensorProduct.map Z (1 : Semantics.Operator C)) c c' =
      rightInteractionCoefficient Q c c' * Z := by
  unfold rightInteractionCoefficient
  simp only [Module.End.mul_eq_comp]
  rw [LinearMap.comp_assoc, tensorMap_left_comp_overlapRightEmbedding]
  simp only [LinearMap.comp_assoc]

/--
Commuting with every left interaction coefficient is equivalent to commuting
with the full left overlap operator after lifting the overlap operator by the
identity on the exterior factor.
-/
theorem commute_leftOverlap_of_commute_leftInteractionCoefficients
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B)) (Z : Semantics.Operator B)
    (hcommute : ∀ a a' : A, Commute Z (leftInteractionCoefficient P a a')) :
    Commute P (TensorProduct.map (1 : Semantics.Operator A) Z) := by
  change P * TensorProduct.map (1 : Semantics.Operator A) Z =
    TensorProduct.map (1 : Semantics.Operator A) Z * P
  apply operator_eq_of_leftInteractionCoefficients_eq
  intro a a'
  rw [leftInteractionCoefficient_mul_rightTensor,
    leftInteractionCoefficient_leftTensor_mul]
  exact (hcommute a a').eq.symm

/--
Commuting with every right interaction coefficient is equivalent to commuting
with the full right overlap operator after lifting the overlap operator by the
identity on the exterior factor.
-/
theorem commute_rightOverlap_of_commute_rightInteractionCoefficients
    {B C : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C)) (Z : Semantics.Operator B)
    (hcommute : ∀ c c' : C, Commute Z (rightInteractionCoefficient Q c c')) :
    Commute Q (TensorProduct.map Z (1 : Semantics.Operator C)) := by
  change Q * TensorProduct.map Z (1 : Semantics.Operator C) =
    TensorProduct.map Z (1 : Semantics.Operator C) * Q
  apply operator_eq_of_rightInteractionCoefficients_eq
  intro c c'
  rw [rightInteractionCoefficient_mul_leftTensor,
    rightInteractionCoefficient_leftTensor_mul]
  exact (hcommute c c').eq.symm

/-- Lift an `A tensor B` operator to the left-associated triple tensor product. -/
noncomputable def overlapLiftLeft
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B)) :
    Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem A B) C) :=
  TensorProduct.map P (1 : Semantics.Operator C)

/--
Fixing a normalized exterior vector is a left inverse to the first overlap
lift.  The BPT first-cut use is to reflect self-adjointness of the transported
`MC` projector back to its local representative.
-/
theorem overlapLiftLeft_injective_of_unit_vector
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (eta : C) (heta : ‖eta‖ = 1) :
    Function.Injective (overlapLiftLeft (C := C) :
      Semantics.Operator (Semantics.CompositeSystem A B) →
        Semantics.Operator (Semantics.CompositeSystem
          (Semantics.CompositeSystem A B) C)) := by
  intro P Q hPQ
  calc
    P = rightTensorCompression eta (overlapLiftLeft (C := C) P) := by
      symm
      simpa [overlapLiftLeft] using rightTensorCompression_tensorMap_left P eta heta
    _ = rightTensorCompression eta (overlapLiftLeft (C := C) Q) := congrArg _ hPQ
    _ = Q := by
      simpa [overlapLiftLeft] using rightTensorCompression_tensorMap_left Q eta heta

/-- Lift a `B tensor C` operator to the same left-associated triple tensor product. -/
noncomputable def overlapLiftRight
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C)) :
    Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem A B) C) :=
  (tensorAssociatorUnitary A B C).symm.conjOperator
    (TensorProduct.map (1 : Semantics.Operator A) Q)

/--
Embed the overlap system into a triple tensor product with fixed exterior
vectors.  Sandwiching a commuting pair of overlap lifts by these maps is the
concrete bridge from global commutation to coefficient commutation.
-/
noncomputable def overlapTripleEmbedding
    (A B C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (a : A) (c : C) : B →ₗ[Complex]
      Semantics.CompositeSystem (Semantics.CompositeSystem A B) C :=
  (overlapRightEmbedding (Semantics.CompositeSystem A B) C c).comp
    (overlapLeftEmbedding A B a)

@[simp]
theorem overlapTripleEmbedding_apply
    (A B C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (a : A) (c : C) (b : B) :
    overlapTripleEmbedding A B C a c b = (a ⊗ₜ[Complex] b) ⊗ₜ[Complex] c := by
  rfl

@[simp]
theorem overlapLiftLeft_apply_tmul
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (a : A) (b : B) (c : C) :
    overlapLiftLeft (C := C) P ((a ⊗ₜ[Complex] b) ⊗ₜ[Complex] c) =
      P (a ⊗ₜ[Complex] b) ⊗ₜ[Complex] c := by
  rfl

@[simp]
theorem overlapLiftRight_apply_tmul
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (a : A) (b : B) (c : C) :
    overlapLiftRight (A := A) Q ((a ⊗ₜ[Complex] b) ⊗ₜ[Complex] c) =
      (tensorAssociatorUnitary A B C).symm (a ⊗ₜ[Complex] Q (b ⊗ₜ[Complex] c)) := by
  simp [overlapLiftRight, Semantics.UnitaryTransport.conjOperator]

/-- The right overlap lift acts inside the `BC` slot of a triple embedding. -/
@[simp]
theorem overlapLiftRight_apply_tripleEmbedding
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (a : A) (b : B) (c : C) :
    overlapLiftRight (A := A) Q (overlapTripleEmbedding A B C a c b) =
      (tensorAssociatorUnitary A B C).symm (a ⊗ₜ[Complex] Q (b ⊗ₜ[Complex] c)) := by
  simpa using overlapLiftRight_apply_tmul (A := A) Q a b c

/-- The left overlap lift acts inside the `AB` slot after the canonical reassociation. -/
@[simp]
theorem overlapLiftLeft_apply_associator_symm_tmul
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (a : A) (b : B) (c : C) :
    overlapLiftLeft (C := C) P
        ((tensorAssociatorUnitary A B C).symm (a ⊗ₜ[Complex] (b ⊗ₜ[Complex] c))) =
      P (a ⊗ₜ[Complex] b) ⊗ₜ[Complex] c := by
  rw [tensorAssociatorUnitary_symm_apply_tmul]
  rfl

/--
Compressing a left overlap lift after reassociation acts by the left
coefficient on the `B` part and by the ordinary right contraction on `C`.
-/
theorem leftOverlapCompression_through_reassociation
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (a a' : A) (c : C) (middle : Semantics.CompositeSystem B C) :
    LinearMap.adjoint (overlapTripleEmbedding A B C a c)
        (overlapLiftLeft (C := C) P
          ((tensorAssociatorUnitary A B C).symm (a' ⊗ₜ[Complex] middle))) =
      leftInteractionCoefficient P a a'
        (LinearMap.adjoint (overlapRightEmbedding B C c) middle) := by
  induction middle using TensorProduct.induction_on with
  | zero =>
      simp [leftInteractionCoefficient, overlapTripleEmbedding,
        LinearMap.adjoint_comp, LinearMap.comp_apply]
  | tmul middleB middleC =>
      rw [overlapLiftLeft_apply_associator_symm_tmul]
      simp [leftInteractionCoefficient, overlapTripleEmbedding,
        LinearMap.adjoint_comp, LinearMap.comp_apply,
        adjoint_overlapLeftEmbedding_apply_tmul,
        adjoint_overlapRightEmbedding_apply_tmul]
  | add x y hx hy =>
      simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy

/-- Pointwise form of the left-then-right triple compression calculation. -/
theorem overlapTripleCompression_left_then_right_apply
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (a a' : A) (c c' : C) (b : B) :
    (LinearMap.adjoint (overlapTripleEmbedding A B C a c)).comp
      ((overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q).comp
        (overlapTripleEmbedding A B C a' c')) b =
      (leftInteractionCoefficient P a a' * rightInteractionCoefficient Q c c') b := by
  simp only [LinearMap.comp_apply, Module.End.mul_apply]
  rw [overlapLiftRight_apply_tripleEmbedding]
  simpa [leftInteractionCoefficient, rightInteractionCoefficient, LinearMap.comp_apply] using
    leftOverlapCompression_through_reassociation P a a' c
      (Q (b ⊗ₜ[Complex] c'))

/-- Operator form of the left-then-right triple compression calculation. -/
theorem overlapTripleCompression_left_then_right
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (a a' : A) (c c' : C) :
    (LinearMap.adjoint (overlapTripleEmbedding A B C a c)).comp
      ((overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q).comp
        (overlapTripleEmbedding A B C a' c')) =
      leftInteractionCoefficient P a a' * rightInteractionCoefficient Q c c' := by
  apply LinearMap.ext
  intro b
  exact overlapTripleCompression_left_then_right_apply P Q a a' c c' b

/--
Contracting a reassociated `A tensor (B tensor C)` vector against a triple
embedding separates its `A` matrix element from the remaining `C`
contraction.  This is the reverse-order counterpart of the preceding
left-then-right calculation.
-/
theorem adjoint_overlapTripleEmbedding_apply_associator_symm
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (a a' : A) (c : C) (middle : Semantics.CompositeSystem B C) :
    LinearMap.adjoint (overlapTripleEmbedding A B C a c)
        ((tensorAssociatorUnitary A B C).symm (a' ⊗ₜ[Complex] middle)) =
      (inner Complex a a') • LinearMap.adjoint (overlapRightEmbedding B C c) middle := by
  induction middle using TensorProduct.induction_on with
  | zero =>
      simp [overlapTripleEmbedding, LinearMap.adjoint_comp, LinearMap.comp_apply]
  | tmul middleB middleC =>
      rw [tensorAssociatorUnitary_symm_apply_tmul]
      simp [overlapTripleEmbedding, LinearMap.adjoint_comp, LinearMap.comp_apply,
        adjoint_overlapLeftEmbedding_apply_tmul,
        adjoint_overlapRightEmbedding_apply_tmul, smul_smul, mul_comm]
  | add x y hx hy =>
      simpa only [TensorProduct.tmul_add, map_add, smul_add] using congrArg₂ (· + ·) hx hy

/--
Compressing a right overlap lift after the left-associated embedding acts by
the right coefficient on the `B` part and by the ordinary left contraction on
`A`.  This is the reverse-order companion to
`leftOverlapCompression_through_reassociation`.
-/
theorem rightOverlapCompression_through_left
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (a : A) (c c' : C) (middle : Semantics.CompositeSystem A B) :
    LinearMap.adjoint (overlapTripleEmbedding A B C a c)
        (overlapLiftRight (A := A) Q (middle ⊗ₜ[Complex] c')) =
      rightInteractionCoefficient Q c c'
        (LinearMap.adjoint (overlapLeftEmbedding A B a) middle) := by
  induction middle using TensorProduct.induction_on with
  | zero =>
      simp [rightInteractionCoefficient, overlapTripleEmbedding,
        LinearMap.adjoint_comp, LinearMap.comp_apply]
  | tmul middleA middleB =>
      rw [overlapLiftRight_apply_tmul]
      rw [adjoint_overlapTripleEmbedding_apply_associator_symm]
      simp [rightInteractionCoefficient, LinearMap.adjoint_comp, LinearMap.comp_apply,
        adjoint_overlapLeftEmbedding_apply_tmul]
  | add x y hx hy =>
      simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hx hy

/-- Pointwise form of the right-then-left triple compression calculation. -/
theorem overlapTripleCompression_right_then_left_apply
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (a a' : A) (c c' : C) (b : B) :
    (LinearMap.adjoint (overlapTripleEmbedding A B C a c)).comp
      ((overlapLiftRight (A := A) Q * overlapLiftLeft (C := C) P).comp
        (overlapTripleEmbedding A B C a' c')) b =
      (rightInteractionCoefficient Q c c' * leftInteractionCoefficient P a a') b := by
  simp only [LinearMap.comp_apply, Module.End.mul_apply]
  change LinearMap.adjoint (overlapTripleEmbedding A B C a c)
      (overlapLiftRight (A := A) Q
        (overlapLiftLeft (C := C) P ((a' ⊗ₜ[Complex] b) ⊗ₜ[Complex] c'))) =
    rightInteractionCoefficient Q c c' (leftInteractionCoefficient P a a' b)
  rw [overlapLiftLeft_apply_tmul]
  simpa [leftInteractionCoefficient, rightInteractionCoefficient, LinearMap.comp_apply] using
    rightOverlapCompression_through_left Q a c c' (P (a' ⊗ₜ[Complex] b))

/-- Operator form of the right-then-left triple compression calculation. -/
theorem overlapTripleCompression_right_then_left
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (a a' : A) (c c' : C) :
    (LinearMap.adjoint (overlapTripleEmbedding A B C a c)).comp
      ((overlapLiftRight (A := A) Q * overlapLiftLeft (C := C) P).comp
        (overlapTripleEmbedding A B C a' c')) =
      rightInteractionCoefficient Q c c' * leftInteractionCoefficient P a a' := by
  apply LinearMap.ext
  intro b
  exact overlapTripleCompression_right_then_left_apply P Q a a' c c' b

/--
Commutation of the two overlapping lifts gives commutation of every left and
right interaction coefficient.  This is the concrete finite-dimensional
interaction-algebra consequence used by the BPT tensor-block theorem.
-/
theorem leftInteractionCoefficient_commute_rightInteractionCoefficient
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (a a' : A) (c c' : C) :
    Commute (leftInteractionCoefficient P a a') (rightInteractionCoefficient Q c c') := by
  change leftInteractionCoefficient P a a' * rightInteractionCoefficient Q c c' =
    rightInteractionCoefficient Q c c' * leftInteractionCoefficient P a a'
  rw [← overlapTripleCompression_left_then_right P Q a a' c c', hcommute.eq,
    overlapTripleCompression_right_then_left P Q a a' c c']

/--
The star algebra generated by the left coefficient operators on the overlap.
It is deliberately a genuine `StarSubalgebra`: star closure is required for
the orthogonal finite-dimensional decomposition used in the BPT argument.
-/
noncomputable def leftInteractionAlgebra
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B)) :
    StarSubalgebra Complex (Semantics.Operator B) :=
  StarAlgebra.adjoin Complex
    {coefficient | ∃ a a' : A, coefficient = leftInteractionCoefficient P a a'}

/-- The star algebra generated by the right coefficient operators on the overlap. -/
noncomputable def rightInteractionAlgebra
    {B C : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C)) :
    StarSubalgebra Complex (Semantics.Operator B) :=
  StarAlgebra.adjoin Complex
    {coefficient | ∃ c c' : C, coefficient = rightInteractionCoefficient Q c c'}

/--
For a self-adjoint left projector, taking the adjoint of a left interaction
coefficient just exchanges its two exterior matrix-element vectors.  Thus the
displayed coefficient family is already star closed, as required in the
finite-dimensional interaction-algebra argument.
-/
theorem adjoint_leftInteractionCoefficient_of_selfAdjoint
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (hselfAdjoint : LinearMap.adjoint P = P) (a a' : A) :
    LinearMap.adjoint (leftInteractionCoefficient P a a') =
      leftInteractionCoefficient P a' a := by
  simp [leftInteractionCoefficient, LinearMap.adjoint_comp, hselfAdjoint,
    LinearMap.comp_assoc]

/--
When the overlapping lifts commute and the left operator is self-adjoint, the
right interaction algebra lies in the star-centralizer of the displayed left
coefficient family.  This upgrades the pointwise sandwich commutation to the
commuting finite-dimensional *-algebras used in the block factorization.
-/
theorem rightInteractionAlgebra_le_leftCoefficientCentralizer
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q)) :
    rightInteractionAlgebra Q ≤ StarSubalgebra.centralizer Complex
      ({coefficient | ∃ a a' : A, coefficient = leftInteractionCoefficient P a a'} :
        Set (Semantics.Operator B)) := by
  rw [rightInteractionAlgebra]
  apply StarAlgebra.adjoin_le
  rintro coefficient ⟨c, c', rfl⟩
  refine (StarSubalgebra.mem_centralizer_iff Complex).mpr ?_
  intro leftCoefficient hleftCoefficient
  rcases hleftCoefficient with ⟨a, a', rfl⟩
  constructor
  · exact (leftInteractionCoefficient_commute_rightInteractionCoefficient
      P Q hcommute a a' c c').eq
  · rw [LinearMap.star_eq_adjoint,
      adjoint_leftInteractionCoefficient_of_selfAdjoint P hselfAdjoint]
    exact (leftInteractionCoefficient_commute_rightInteractionCoefficient
      P Q hcommute a' a c c').eq

/--
The two generated interaction algebras commute elementwise.  The first
centralizer inclusion handles arbitrary right words, while star closure of
that algebra supplies the second centralizer condition for arbitrary left
words.  This is the algebraic input to `commuting_overlap_block_factorization`.
-/
theorem interactionAlgebras_commute
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    {left right : Semantics.Operator B}
    (hleft : left ∈ leftInteractionAlgebra P)
    (hright : right ∈ rightInteractionAlgebra Q) :
    Commute left right := by
  have hrightCentral := rightInteractionAlgebra_le_leftCoefficientCentralizer
    P Q hselfAdjoint hcommute
  have hleftCentral : leftInteractionAlgebra P ≤ StarSubalgebra.centralizer Complex
      (rightInteractionAlgebra Q : Set (Semantics.Operator B)) := by
    rw [leftInteractionAlgebra]
    apply StarAlgebra.adjoin_le
    rintro coefficient ⟨a, a', rfl⟩
    refine (StarSubalgebra.mem_centralizer_iff Complex).mpr ?_
    intro rightCoefficient hrightCoefficient
    constructor
    · have hcentral := ((StarSubalgebra.mem_centralizer_iff Complex).mp
        (hrightCentral hrightCoefficient))
        (leftInteractionCoefficient P a a') ⟨a, a', rfl⟩
      exact hcentral.1.symm
    · have hcentral := ((StarSubalgebra.mem_centralizer_iff Complex).mp
        (hrightCentral (StarMemClass.star_mem hrightCoefficient)))
        (leftInteractionCoefficient P a a') ⟨a, a', rfl⟩
      exact hcentral.1.symm
  exact ((StarSubalgebra.mem_centralizer_iff Complex).mp
    (hleftCentral hleft) right hright).1.symm

/--
Regard an ordinary overlap operator as an endomorphism of the left interaction
algebra module when it commutes with every algebra element.  The target use is
to restrict each right interaction coefficient to the fully invariant
isotypic sectors of the left algebra.
-/
def commutingOperatorAsModuleEnd
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (T : Semantics.Operator B)
    (hcommute : ∀ operator : S, Commute (operator : Semantics.Operator B) T) :
    Module.End S B where
  toFun := T
  map_add' := T.map_add
  map_smul' := by
    intro operator vector
    change T ((operator : Semantics.Operator B) vector) =
      (operator : Semantics.Operator B) (T vector)
    exact congrArg (fun map => map vector) (hcommute operator).eq.symm

/--
Every right interaction coefficient preserves every left-isotypic component.
The proof turns it into an `S`-module endomorphism using the commuting
interaction algebras, then uses full invariance of an isotypic component.
This is the direct-sum/block-diagonal step in the BV03 decomposition.
-/
theorem rightInteractionCoefficient_preserves_leftIsotypicComponent
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (W : Submodule (leftInteractionAlgebra P) B) [IsSimpleModule (leftInteractionAlgebra P) W]
    (c c' : C) {vector : B}
    (hvector : vector ∈ isotypicComponent (leftInteractionAlgebra P) B W) :
    rightInteractionCoefficient Q c c' vector ∈
      isotypicComponent (leftInteractionAlgebra P) B W := by
  let rightCoefficient := rightInteractionCoefficient Q c c'
  let rightEnd : Module.End (leftInteractionAlgebra P) B :=
    commutingOperatorAsModuleEnd (leftInteractionAlgebra P) rightCoefficient (by
      intro operator
      exact interactionAlgebras_commute P Q hselfAdjoint hcommute operator.property
        (by
          apply StarAlgebra.subset_adjoin
          exact ⟨c, c', rfl⟩))
  have hfullyInvariant : (isotypicComponent (leftInteractionAlgebra P) B W).IsFullyInvariant :=
    Submodule.IsFullyInvariant.isotypicComponent (leftInteractionAlgebra P) B W
  change rightEnd vector ∈ isotypicComponent (leftInteractionAlgebra P) B W
  exact hfullyInvariant rightEnd hvector

/-- Every displayed left coefficient belongs to its concrete interaction algebra. -/
theorem leftInteractionCoefficient_mem_leftInteractionAlgebra
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B)) (a a' : A) :
    leftInteractionCoefficient P a a' ∈ leftInteractionAlgebra P := by
  apply StarAlgebra.subset_adjoin
  exact ⟨a, a', rfl⟩

/-- Every displayed right coefficient belongs to its concrete interaction algebra. -/
theorem rightInteractionCoefficient_mem_rightInteractionAlgebra
    {B C : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C)) (c c' : C) :
    rightInteractionCoefficient Q c c' ∈ rightInteractionAlgebra Q := by
  apply StarAlgebra.subset_adjoin
  exact ⟨c, c', rfl⟩

/--
An adjoint-closed finite operator family preserves the orthogonal complement
of each of its invariant subspaces.  This is the Hilbert-space input behind
semisimplicity of a finite interaction algebra representation.
-/
theorem orthogonalComplement_invariant_of_adjoint_closed
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (operators : Set (Semantics.Operator B))
    (hadjoint : ∀ ⦃operator : Semantics.Operator B⦄,
      operator ∈ operators → LinearMap.adjoint operator ∈ operators)
    {W : Submodule Complex B}
    (hinvariant : ∀ ⦃operator : Semantics.Operator B⦄,
      operator ∈ operators → ∀ ⦃vector : B⦄, vector ∈ W → operator vector ∈ W) :
    ∀ ⦃operator : Semantics.Operator B⦄,
      operator ∈ operators → ∀ ⦃vector : B⦄, vector ∈ Wᗮ → operator vector ∈ Wᗮ := by
  intro operator hoperator vector hvector
  rw [Submodule.mem_orthogonal]
  intro witness hwitness
  rw [← LinearMap.adjoint_inner_left]
  have hadjointWitness : LinearMap.adjoint operator witness ∈ W :=
    hinvariant (operator := LinearMap.adjoint operator) (hadjoint hoperator) hwitness
  exact (Submodule.mem_orthogonal W vector).mp hvector
    (LinearMap.adjoint operator witness) hadjointWitness

/--
If an operator reduces a finite-dimensional Hilbert subspace, then it commutes
with that subspace's orthogonal projector.  This turns the representation-
theoretic isotypic summands below into honest local sector projectors, which is
the form needed by the correctability/no-information argument.
-/
theorem starProjection_commute_of_invariant_of_orthogonalInvariant
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (W : Submodule Complex B) (T : Semantics.Operator B)
    (hW : ∀ ⦃vector : B⦄, vector ∈ W → T vector ∈ W)
    (hWperp : ∀ ⦃vector : B⦄, vector ∈ Wᗮ → T vector ∈ Wᗮ) :
    Commute W.starProjection.toLinearMap T := by
  apply LinearMap.ext
  intro vector
  change W.starProjection (T vector) = T (W.starProjection vector)
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact hW (W.starProjection_apply_mem vector)
  · rw [← map_sub]
    exact hWperp (Submodule.sub_starProjection_mem_orthogonal vector)

/--
The concrete action of a complex operator star algebra is compatible with the
ambient complex scalar action.  This instance is needed at declaration sites
where `restrictScalars` turns an algebra submodule into an ordinary Hilbert
subspace for the BV03 sector projectors.
-/
instance starSubalgebraComplexScalarTower
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B)) :
    IsScalarTower Complex S B where
  smul_assoc scalar operator vector := by
    change ((scalar • (operator : Semantics.Operator B)) : Semantics.Operator B) vector =
      scalar • (operator : Semantics.Operator B) vector
    simp

/-- Complex scalars commute with the concrete action of a star subalgebra. -/
instance starSubalgebraComplexSMulCommClass
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B)) :
    SMulCommClass S Complex B where
  smul_comm operator scalar vector := by
    change (operator : Semantics.Operator B) (scalar • vector) =
      scalar • (operator : Semantics.Operator B) vector
    exact (operator : Semantics.Operator B).map_smul scalar vector

/--
The orthogonal projector onto a submodule of a concrete star algebra commutes
with every algebra element.  The star closure supplies invariance of the
orthogonal complement, so this is a reducing, rather than merely invariant,
sector.  It is the local projector used to collapse BV03 isotypic labels by
correctability.
-/
theorem starProjection_commute_starSubalgebraSubmodule
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B)) (W : Submodule S B) (T : S) :
    Commute (W.restrictScalars Complex).starProjection.toLinearMap
      (T : Semantics.Operator B) := by
  letI : IsScalarTower Complex S B := by
    constructor
    intro scalar operator vector
    change ((scalar • (operator : Semantics.Operator B)) : Semantics.Operator B) vector =
      scalar • (operator : Semantics.Operator B) vector
    simp
  apply starProjection_commute_of_invariant_of_orthogonalInvariant
    (W.restrictScalars Complex) (T : Semantics.Operator B)
  · intro vector hvector
    exact W.smul_mem T hvector
  · refine orthogonalComplement_invariant_of_adjoint_closed
      (operators := (S : Set (Semantics.Operator B))) ?_ ?_ T.property
    · intro operator hoperator
      change LinearMap.adjoint operator ∈ S
      rw [← LinearMap.star_eq_adjoint]
      exact StarMemClass.star_mem hoperator
    · intro operator hoperator vector hvector
      exact W.smul_mem ⟨operator, hoperator⟩ hvector

/--
If a second concrete star algebra commutes with the first one, the orthogonal
projector onto any fully invariant first-algebra submodule also commutes with
the second algebra.  The key point is that every second-algebra element is a
first-algebra module endomorphism, while star closure makes its adjoint preserve
the same submodule.  This is the reducing-sector form of the BV03 commutant
argument.
-/
theorem starProjection_commute_of_fullyInvariant_of_commutingStarSubalgebras
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S R : StarSubalgebra Complex (Semantics.Operator B)) (W : Submodule S B)
    (hfullyInvariant : W.IsFullyInvariant)
    (hcommute : ∀ left : S, ∀ right : R,
      Commute (left : Semantics.Operator B) (right : Semantics.Operator B))
    (T : R) :
    Commute (W.restrictScalars Complex).starProjection.toLinearMap
      (T : Semantics.Operator B) := by
  letI : IsScalarTower Complex S B := by
    constructor
    intro scalar operator vector
    change ((scalar • (operator : Semantics.Operator B)) : Semantics.Operator B) vector =
      scalar • (operator : Semantics.Operator B) vector
    simp
  have hinvariant : ∀ ⦃operator : Semantics.Operator B⦄,
      operator ∈ (R : Set (Semantics.Operator B)) → ∀ ⦃vector : B⦄,
        vector ∈ W.restrictScalars Complex → operator vector ∈ W.restrictScalars Complex := by
    intro operator hoperator vector hvector
    let operatorEnd : Module.End S B :=
      commutingOperatorAsModuleEnd S operator (by
        intro left
        exact hcommute left ⟨operator, hoperator⟩)
    exact hfullyInvariant operatorEnd hvector
  apply starProjection_commute_of_invariant_of_orthogonalInvariant
    (W.restrictScalars Complex) (T : Semantics.Operator B)
  · intro vector hvector
    exact hinvariant (operator := (T : Semantics.Operator B)) T.property hvector
  · refine orthogonalComplement_invariant_of_adjoint_closed
      (operators := (R : Set (Semantics.Operator B))) ?_ hinvariant T.property
    intro operator hoperator
    change LinearMap.adjoint operator ∈ R
    rw [← LinearMap.star_eq_adjoint]
    exact StarMemClass.star_mem hoperator

/--
Every submodule of a concrete complex operator star algebra carries the
underlying complex-vector-space structure by restriction along the algebra
map.  Keeping this instance at the operator-algebra boundary makes the
finite-dimensional isotypic statements below well typed at their declaration
sites, rather than only inside their proof bodies.
-/
instance starSubalgebraSubmoduleComplexModule
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B)) (W : Submodule S B) :
    Module Complex W :=
  Module.compHom W (algebraMap Complex S)

/--
The carrier inclusion of a star-subalgebra submodule is complex-linear for the
restricted scalar structure above.  It lets finite dimensionality descend from
the ambient finite Hilbert space without introducing a second scalar-tower
instance on that ambient representation.
-/
def starSubalgebraSubmoduleComplexInclusion
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B)) (W : Submodule S B) :
    W →ₗ[Complex] B where
  toFun := Subtype.val
  map_add' := fun _ _ => rfl
  map_smul' := by
    intro scalar vector
    change ((algebraMap Complex S scalar : S) • (vector : W) : B) = scalar • (vector : B)
    change ((algebraMap Complex (Semantics.Operator B) scalar : Semantics.Operator B) : B →ₗ[Complex] B)
      vector = scalar • (vector : B)
    simp

/--
The orthogonal complement of an invariant submodule is itself an invariant
submodule for a finite overlap star algebra.  This is the concrete bridge from
adjoint closure to semisimplicity: no abstract semisimplicity hypothesis is
introduced for the interaction algebra.
-/
noncomputable def starSubalgebraOrthogonalComplement
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) : Submodule S B := by
  letI : IsScalarTower Complex S B := by
    constructor
    intro scalar operator vector
    change ((scalar • (operator : Semantics.Operator B)) : Semantics.Operator B) vector =
      scalar • (operator : Semantics.Operator B) vector
    simp
  let W0 : Submodule Complex B := W.restrictScalars Complex
  refine
    { carrier := W0ᗮ
      zero_mem' := (W0ᗮ).zero_mem
      add_mem' := fun left right => (W0ᗮ).add_mem left right
      smul_mem' := ?_ }
  intro operator vector hvector
  change (operator : Semantics.Operator B) vector ∈ W0ᗮ
  refine orthogonalComplement_invariant_of_adjoint_closed (B := B)
    (operators := (S : Set (Semantics.Operator B))) ?_ ?_ operator.property hvector
  · intro member hmember
    change LinearMap.adjoint member ∈ S
    rw [← LinearMap.star_eq_adjoint]
    exact StarMemClass.star_mem hmember
  · intro member hmember witness hwitness
    exact W.smul_mem ⟨member, hmember⟩ hwitness

/--
Every finite-dimensional representation of a concrete star subalgebra of
operators is semisimple.  The proof constructs complements as the invariant
orthogonal complements above.  Its target use is the isotypic decomposition
inside `commuting_overlap_block_factorization`.
-/
theorem starSubalgebra_module_isSemisimple
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B)) :
    IsSemisimpleModule S B := by
  refine (isSemisimpleModule_iff S B).mpr ?_
  constructor
  intro W
  letI : IsScalarTower Complex S B := by
    constructor
    intro scalar operator vector
    change ((scalar • (operator : Semantics.Operator B)) : Semantics.Operator B) vector =
      scalar • (operator : Semantics.Operator B) vector
    simp
  let W0 : Submodule Complex B := W.restrictScalars Complex
  let Wperp := starSubalgebraOrthogonalComplement S W
  refine ⟨Wperp, ?_⟩
  constructor
  · rw [disjoint_iff]
    apply le_antisymm
    · intro vector hvector
      exact (Submodule.orthogonal_disjoint W0).le_bot ⟨hvector.1, hvector.2⟩
    · exact bot_le
  · rw [codisjoint_iff]
    apply top_unique
    intro vector _
    have hsum : vector ∈ W0 ⊔ W0ᗮ := by
      rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection]
      trivial
    rcases Submodule.mem_sup.mp hsum with ⟨left, hleft, right, hright, rfl⟩
    exact Submodule.add_mem_sup hleft hright

/--
The isotypic components of a finite overlap interaction algebra form an
internal direct sum of the overlap module.  This is the direct-sum part of the
BV03 boundary decomposition; its index is representation-theoretic, not the
unrelated joint spectrum of the two global projectors.
-/
theorem starSubalgebra_isotypicComponents_isInternal
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B)) :
    DirectSum.IsInternal (fun component : isotypicComponents S B => component.1) := by
  classical
  letI : IsSemisimpleModule S B := starSubalgebra_module_isSemisimple S
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (sSupIndep_iff _).mp (sSupIndep_isotypicComponents S B)
  · exact (sSup_eq_iSup' _).symm.trans (sSup_isotypicComponents S B)

/--
On an isotypic finite block, every endomorphism commuting with the interaction
algebra is a matrix acting only on the multiplicity coordinate.  Schur's lemma
makes each matrix entry scalar on the simple factor.  This is the right-factor
half of the tensor-block equality in `commuting_overlap_block_factorization`.
-/
theorem isotypic_commutant_matrix_factorization
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) [IsSimpleModule S W]
    (n : Nat) (T : Module.End S (Fin n → W)) :
    ∃ matrix : Matrix (Fin n) (Fin n) Complex,
      ∀ (vector : Fin n → W) (row : Fin n),
        T vector row = ∑ column, matrix row column • vector column := by
  letI complexModule : Module Complex W := starSubalgebraSubmoduleComplexModule S W
  letI scalarTower : IsScalarTower Complex S W := by
    constructor
    intro scalar operator vector
    change ((algebraMap Complex S scalar) * operator) • vector =
      (algebraMap Complex S scalar) • (operator • vector)
    exact mul_smul _ _ _
  letI smulComm : SMulCommClass S Complex W := by
    constructor
    intro operator scalar vector
    apply Subtype.ext
    change (operator : Semantics.Operator B) (scalar • (vector : B)) =
      scalar • (operator : Semantics.Operator B) vector
    exact (operator : Semantics.Operator B).map_smul scalar vector
  letI endAlgebra : Algebra Complex (Module.End S W) :=
    @Module.End.instAlgebra Complex S W _ _ _ complexModule
      (inferInstance : Module S W) smulComm (inferInstance : SMul Complex S) scalarTower
  letI finiteDimensional : FiniteDimensional Complex W :=
    FiniteDimensional.of_injective (starSubalgebraSubmoduleComplexInclusion S W)
      Subtype.coe_injective
  let entries : Matrix (Fin n) (Fin n) (Module.End S W) :=
    endVecRingEquivMatrixEnd (Fin n) S W T
  have hscalar : ∀ row column, ∃ scalar : Complex,
      algebraMap Complex (Module.End S W) scalar = entries row column := by
    intro row column
    exact (@IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed S W Complex
      (inferInstance : Field Complex) (inferInstance : Ring S)
      (inferInstance : Algebra Complex S) (inferInstance : AddCommGroup W)
      complexModule (inferInstance : Module S W) scalarTower
      (inferInstance : IsSimpleModule S W) finiteDimensional
      (inferInstance : IsAlgClosed Complex)).2 _
  choose matrix hmatrix using hscalar
  refine ⟨matrix, ?_⟩
  intro vector row
  have hentries : (endVecRingEquivMatrixEnd (Fin n) S W).symm entries = T := by
    simpa only [entries] using
      (endVecRingEquivMatrixEnd (Fin n) S W).symm_apply_apply T
  calc
    T vector row = ((endVecRingEquivMatrixEnd (Fin n) S W).symm entries) vector row := by
      rw [hentries]
    _ = ∑ column, entries row column (vector column) := rfl
    _ = ∑ column, matrix row column • vector column := by
      apply Finset.sum_congr rfl
      intro column _
      have hentry := congrArg
        (fun operator : Module.End S W => operator (vector column))
        (hmatrix row column).symm
      simpa using hentry

/--
Taking adjoints preserves an intertwining equation for finite-dimensional
star representations.  Mathematically, applying `adjoint` to the relation for
`star r` reverses its two factors and involutivity returns `r`.  Its target use
is the polar part of the BV03 block construction: an intertwiner between two
sector copies has an adjoint which intertwines in the reverse direction.
-/
theorem adjoint_intertwines_of_star
    {R H K : Type u} [InvolutiveStar R]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteDimensional Complex H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteDimensional Complex K]
    (rhoH : R → Module.End Complex H) (rhoK : R → Module.End Complex K)
    (hH : ∀ r, LinearMap.adjoint (rhoH r) = rhoH (star r))
    (hK : ∀ r, LinearMap.adjoint (rhoK r) = rhoK (star r))
    (f : H →ₗ[Complex] K)
    (hintertwines : ∀ r, f.comp (rhoH r) = (rhoK r).comp f)
    (r : R) :
    f.adjoint.comp (rhoK r) = (rhoH r).comp f.adjoint := by
  have h := congrArg LinearMap.adjoint (hintertwines (star r))
  rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, hH, hK] at h
  simpa only [star_star] using h.symm

/--
The positive Gram operator of a star-intertwiner lies in the commutant of the
source action.  Consequently its finite-dimensional polar support and the
resulting partial isometry remain inside a single interaction-algebra sector.
This supplies the unitary-intertwiner step needed to turn the isotypic matrix
description into the actual BV03 tensor-block decomposition.
-/
theorem gram_commutes_of_star_intertwines
    {R H K : Type u} [InvolutiveStar R]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteDimensional Complex H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteDimensional Complex K]
    (rhoH : R → Module.End Complex H) (rhoK : R → Module.End Complex K)
    (hH : ∀ r, LinearMap.adjoint (rhoH r) = rhoH (star r))
    (hK : ∀ r, LinearMap.adjoint (rhoK r) = rhoK (star r))
    (f : H →ₗ[Complex] K)
    (hintertwines : ∀ r, f.comp (rhoH r) = (rhoK r).comp f)
    (r : R) :
    Commute (f.adjoint.comp f) (rhoH r) := by
  have hadjoint := adjoint_intertwines_of_star rhoH rhoK hH hK f hintertwines r
  change (f.adjoint.comp f).comp (rhoH r) =
    (rhoH r).comp (f.adjoint.comp f)
  calc
    (f.adjoint.comp f).comp (rhoH r) =
        f.adjoint.comp (f.comp (rhoH r)) := by rw [LinearMap.comp_assoc]
    _ = f.adjoint.comp ((rhoK r).comp f) := by rw [hintertwines r]
    _ = (f.adjoint.comp (rhoK r)).comp f := by rw [← LinearMap.comp_assoc]
    _ = ((rhoH r).comp f.adjoint).comp f := by rw [hadjoint]
    _ = (rhoH r).comp (f.adjoint.comp f) := by rw [LinearMap.comp_assoc]

/--
Polar-normalize an invertible intertwiner of finite-dimensional star
representations.  The Gram operator belongs to the source commutant, so its
positive square root does too; dividing by that square root therefore produces
an honest unitary intertwiner rather than only a linear isomorphism.  This is
used immediately below to make the BV03 isotypic coordinate equivalence
compatible with the Hilbert-space tensor-block transport.
-/
private theorem unitary_star_intertwiner_of_linearEquiv
    {R H K : Type u} [InvolutiveStar R]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteDimensional Complex H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteDimensional Complex K]
    (rhoH : R → Module.End Complex H) (rhoK : R → Module.End Complex K)
    (hH : ∀ r, LinearMap.adjoint (rhoH r) = rhoH (star r))
    (hK : ∀ r, LinearMap.adjoint (rhoK r) = rhoK (star r))
    (e : H ≃ₗ[Complex] K)
    (hintertwines : ∀ r, e.toLinearMap.comp (rhoH r) = (rhoK r).comp e.toLinearMap) :
    ∃ U : Semantics.UnitaryTransport H K,
      ∀ r, U.toLinearEquiv.toLinearMap.comp (rhoH r) =
        (rhoK r).comp U.toLinearEquiv.toLinearMap := by
  let f : H →L[Complex] K := e.toContinuousLinearEquiv.toContinuousLinearMap
  let G : H →L[Complex] H := f.adjoint.comp f
  have hf_intertwines : ∀ r, f.toLinearMap.comp (rhoH r) =
      (rhoK r).comp f.toLinearMap := by
    intro r
    simpa [f] using hintertwines r
  have hf_injective : Function.Injective f := by
    intro x y hxy
    exact e.injective hxy
  have hG_injective : Function.Injective G :=
    (f.adjoint_comp_self_injective_iff).mpr hf_injective
  let gEquiv : H ≃ₗ[Complex] H := LinearEquiv.ofBijective G.toLinearMap
    ⟨hG_injective, LinearMap.injective_iff_surjective.mp hG_injective⟩
  let gContinuous : H ≃L[Complex] H := gEquiv.toContinuousLinearEquiv
  have hgContinuous : gContinuous.toContinuousLinearMap = G := by
    ext x
    rfl
  have hG_unit : IsUnit G := by
    refine ⟨gContinuous.toUnit, ?_⟩
    exact hgContinuous.symm
  have hG_nonneg : 0 ≤ G :=
    (ContinuousLinearMap.nonneg_iff_isPositive G).mpr
      (ContinuousLinearMap.isPositive_adjoint_comp_self f)
  have hG_commutes : ∀ r, Commute G (LinearMap.toContinuousLinearMap (rhoH r)) := by
    intro r
    have hlinear := gram_commutes_of_star_intertwines rhoH rhoK hH hK
      f.toLinearMap hf_intertwines r
    rw [ContinuousLinearMap.adjoint_toLinearMap] at hlinear
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun operator : Module.End Complex H => operator x) hlinear.eq
  let p : H →L[Complex] H := CFC.sqrt G
  have hp_sq : p.comp p = G := by
    change p * p = G
    simpa [p] using CFC.sqrt_mul_sqrt_self G hG_nonneg
  have hp_self : p.adjoint = p := by
    change star p = p
    exact (CFC.sqrt_nonneg G).isSelfAdjoint
  have hp_commutes : ∀ r, Commute p (LinearMap.toContinuousLinearMap (rhoH r)) := by
    intro r
    simpa [p, CFC.sqrt_eq_cfc] using (hG_commutes r).cfc_nnreal NNReal.sqrt
  have hp_unit : IsUnit p := (CFC.isUnit_sqrt_iff G hG_nonneg).mpr hG_unit
  rcases hp_unit with ⟨pUnit, hpUnit⟩
  let pInv : H →L[Complex] H := (↑(pUnit⁻¹) : H →L[Complex] H)
  have hp_mul_pInv : p.comp pInv = 1 := by
    simpa [pInv, ContinuousLinearMap.mul_def, hpUnit] using pUnit.val_inv
  have hpInv_adjoint_comp_p : pInv.adjoint.comp p = 1 := by
    have h := congrArg ContinuousLinearMap.adjoint hp_mul_pInv
    simpa [ContinuousLinearMap.adjoint_comp, hp_self, ContinuousLinearMap.adjoint_one] using h
  have hpInv_commutes : ∀ r, Commute pInv (LinearMap.toContinuousLinearMap (rhoH r)) := by
    intro r
    have hunit : Commute (↑pUnit : H →L[Complex] H)
        (LinearMap.toContinuousLinearMap (rhoH r)) := by
      simpa [hpUnit] using hp_commutes r
    simpa [pInv] using hunit.units_inv_left
  let pEquiv : H ≃L[Complex] H := ContinuousLinearEquiv.unitsEquiv Complex H pUnit
  let uEquiv : H ≃L[Complex] K := pEquiv.symm.trans e.toContinuousLinearEquiv
  have hu_eq : uEquiv.toContinuousLinearMap = f.comp pInv := by
    ext x
    rfl
  have hu_adjoint_comp :
      uEquiv.toContinuousLinearMap.adjoint.comp uEquiv.toContinuousLinearMap = 1 := by
    rw [hu_eq, ContinuousLinearMap.adjoint_comp]
    ext x
    change pInv.adjoint (f.adjoint (f (pInv x))) = x
    calc
      pInv.adjoint (f.adjoint (f (pInv x))) = pInv.adjoint (G (pInv x)) := rfl
      _ = pInv.adjoint ((p.comp p) (pInv x)) := by rw [hp_sq]
      _ = ((pInv.adjoint.comp p).comp (p.comp pInv)) x := by rfl
      _ = x := by simp [hpInv_adjoint_comp_p, hp_mul_pInv]
  have hu_inner : ∀ x y : H,
      inner Complex (uEquiv x) (uEquiv y) = inner Complex x y := by
    simpa using
      (uEquiv.toContinuousLinearMap.inner_map_map_iff_adjoint_comp_self).mpr hu_adjoint_comp
  let U : Semantics.UnitaryTransport H K :=
    { toLinearEquiv := uEquiv.toLinearEquiv
      map_inner := by
        intro x y
        simpa using hu_inner x y }
  refine ⟨U, ?_⟩
  have hu_linear : uEquiv.toLinearEquiv.toLinearMap =
      f.toLinearMap.comp pInv.toLinearMap := by
    exact congrArg ContinuousLinearMap.toLinearMap hu_eq
  have hpInv_linear_commutes : ∀ r, Commute pInv.toLinearMap (rhoH r) := by
    intro r
    change pInv.toLinearMap.comp (rhoH r) = (rhoH r).comp pInv.toLinearMap
    apply LinearMap.ext
    intro x
    simpa using congrArg (fun operator : H →L[Complex] H => operator x) (hpInv_commutes r).eq
  intro r
  change uEquiv.toLinearEquiv.toLinearMap.comp (rhoH r) =
    (rhoK r).comp uEquiv.toLinearEquiv.toLinearMap
  rw [hu_linear]
  calc
    (f.toLinearMap.comp pInv.toLinearMap).comp (rhoH r) =
        f.toLinearMap.comp (pInv.toLinearMap.comp (rhoH r)) := by
      rw [LinearMap.comp_assoc]
    _ = f.toLinearMap.comp ((rhoH r).comp pInv.toLinearMap) := by
      exact congrArg (fun operator : Module.End Complex H => f.toLinearMap.comp operator)
        (hpInv_linear_commutes r).eq
    _ = (f.toLinearMap.comp (rhoH r)).comp pInv.toLinearMap := by
      rw [← LinearMap.comp_assoc]
    _ = ((rhoK r).comp f.toLinearMap).comp pInv.toLinearMap := by
      rw [hf_intertwines r]
    _ = (rhoK r).comp (f.toLinearMap.comp pInv.toLinearMap) := by
      rw [LinearMap.comp_assoc]

/-- The left interaction algebra action on one Hilbert isotypic component. -/
noncomputable def isotypicLeftAction
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (component : isotypicComponents S B) (operator : S) :
    Semantics.Operator (component.1.restrictScalars Complex) where
  toFun := fun vector => operator • vector
  map_add' := by
    intro left right
    exact smul_add operator left right
  map_smul' := by
    intro scalar vector
    exact smul_comm operator scalar vector

/--
Restrict an overlap operator to one left-isotypic component by its Hilbert
compression.  Sector invariance below identifies this compression with the
actual block of the overlap projector used in the BV03 decomposition.
-/
noncomputable def overlapProjectorOnIsotypicComponent
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    Semantics.Operator
      (Semantics.CompositeSystem A (component.1.restrictScalars Complex)) :=
  let inclusion := (component.1.restrictScalars Complex).subtype
  (TensorProduct.map (1 : Semantics.Operator A) (LinearMap.adjoint inclusion)).comp
    (P.comp (TensorProduct.map (1 : Semantics.Operator A) inclusion))

/-- A right tensor map carries fixed-left embeddings through the same right map. -/
theorem tensorMap_right_comp_overlapLeftEmbedding_hom
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (a : A) (Z : B →ₗ[Complex] C) :
    (TensorProduct.map (1 : Semantics.Operator A) Z).comp
      (overlapLeftEmbedding A B a) =
        (overlapLeftEmbedding A C a).comp Z := by
  apply LinearMap.ext
  intro vector
  rfl

/-- The adjoint form of fixed-left embedding naturality. -/
theorem adjoint_overlapLeftEmbedding_comp_tensorMap_right_adjoint_hom
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (a : A) (Z : B →ₗ[Complex] C) :
    (LinearMap.adjoint (overlapLeftEmbedding A B a)).comp
      (TensorProduct.map (1 : Semantics.Operator A) (LinearMap.adjoint Z)) =
        (LinearMap.adjoint Z).comp (LinearMap.adjoint (overlapLeftEmbedding A C a)) := by
  have h := congrArg LinearMap.adjoint
    (tensorMap_right_comp_overlapLeftEmbedding_hom (A := A) a Z)
  simpa only [LinearMap.adjoint_comp, TensorProduct.adjoint_map,
    LinearMap.adjoint_one] using h

/-- A left tensor map carries fixed-right embeddings through the same left map. -/
theorem tensorMap_left_comp_overlapRightEmbedding_hom
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (c : C) (Z : A →ₗ[Complex] B) :
    (TensorProduct.map Z (1 : Semantics.Operator C)).comp
      (overlapRightEmbedding A C c) =
        (overlapRightEmbedding B C c).comp Z := by
  apply LinearMap.ext
  intro vector
  rfl

/-- The adjoint form of fixed-right embedding naturality. -/
theorem adjoint_overlapRightEmbedding_comp_tensorMap_left_adjoint_hom
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (c : C) (Z : A →ₗ[Complex] B) :
    (LinearMap.adjoint (overlapRightEmbedding A C c)).comp
      (TensorProduct.map (LinearMap.adjoint Z) (1 : Semantics.Operator C)) =
        (LinearMap.adjoint Z).comp (LinearMap.adjoint (overlapRightEmbedding B C c)) := by
  have h := congrArg LinearMap.adjoint
    (tensorMap_left_comp_overlapRightEmbedding_hom (C := C) c Z)
  simpa only [LinearMap.adjoint_comp, TensorProduct.adjoint_map,
    LinearMap.adjoint_one] using h

/-- Right interaction coefficients commute with Hilbert-space compression. -/
theorem rightInteractionCoefficient_overlapRightCompression
    {H B C : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C)) (inclusion : H →ₗ[Complex] B)
    (c c' : C) :
    rightInteractionCoefficient (overlapRightCompression Q inclusion) c c' =
      (LinearMap.adjoint inclusion).comp
        ((rightInteractionCoefficient Q c c').comp inclusion) := by
  unfold rightInteractionCoefficient overlapRightCompression
  calc
    _ = ((LinearMap.adjoint (overlapRightEmbedding H C c)).comp
        (TensorProduct.map (LinearMap.adjoint inclusion) (1 : Semantics.Operator C))).comp
      (Q.comp ((TensorProduct.map inclusion (1 : Semantics.Operator C)).comp
        (overlapRightEmbedding H C c'))) := by
          simp only [LinearMap.comp_assoc]
    _ = ((LinearMap.adjoint inclusion).comp
      (LinearMap.adjoint (overlapRightEmbedding B C c))).comp
      (Q.comp ((overlapRightEmbedding B C c').comp inclusion)) := by
          rw [adjoint_overlapRightEmbedding_comp_tensorMap_left_adjoint_hom (C := C) c inclusion,
            tensorMap_left_comp_overlapRightEmbedding_hom (C := C) c' inclusion]
    _ = (LinearMap.adjoint inclusion).comp
        ((rightInteractionCoefficient Q c c').comp inclusion) := by
          simp only [rightInteractionCoefficient, LinearMap.comp_assoc]

/-- The adjoint of a finite-dimensional subspace inclusion is its inverse on that subspace. -/
theorem adjoint_submoduleSubtype_apply_subtype
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (p : Submodule Complex H) (vector : p) :
    LinearMap.adjoint p.subtype (p.subtype vector) = vector := by
  apply (ext_iff_inner_left Complex).mpr
  intro test
  rw [LinearMap.adjoint_inner_right]
  rfl

/--
The compressed overlap block has precisely the restricted left interaction
coefficient.  This turns the source interaction algebra into an equality of
actual block operators, which the unitary tensor coordinates reconstruct
below.
-/
theorem leftInteractionCoefficient_overlapProjectorOnIsotypicComponent
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (component : isotypicComponents (leftInteractionAlgebra P) B) (a a' : A) :
    leftInteractionCoefficient (overlapProjectorOnIsotypicComponent P component) a a' =
      isotypicLeftAction (leftInteractionAlgebra P) component
        ⟨leftInteractionCoefficient P a a',
          leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩ := by
  let inclusion := (component.1.restrictScalars Complex).subtype
  let coefficient : leftInteractionAlgebra P :=
    ⟨leftInteractionCoefficient P a a',
      leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩
  have haction :
      inclusion.comp
        (isotypicLeftAction (leftInteractionAlgebra P) component coefficient) =
        (coefficient : Semantics.Operator B).comp inclusion := by
    rfl
  unfold leftInteractionCoefficient overlapProjectorOnIsotypicComponent
  change
    (LinearMap.adjoint
      (overlapLeftEmbedding A (component.1.restrictScalars Complex) a)).comp
      (((TensorProduct.map (1 : Semantics.Operator A) (LinearMap.adjoint inclusion)).comp
        (P.comp (TensorProduct.map (1 : Semantics.Operator A) inclusion))).comp
          (overlapLeftEmbedding A (component.1.restrictScalars Complex) a')) =
      isotypicLeftAction (leftInteractionAlgebra P) component coefficient
  calc
    _ = ((LinearMap.adjoint (overlapLeftEmbedding A (component.1.restrictScalars Complex) a)).comp
          (TensorProduct.map (1 : Semantics.Operator A) (LinearMap.adjoint inclusion))).comp
        (P.comp ((TensorProduct.map (1 : Semantics.Operator A) inclusion).comp
          (overlapLeftEmbedding A (component.1.restrictScalars Complex) a'))) := by
          simp only [LinearMap.comp_assoc]
    _ = ((LinearMap.adjoint inclusion).comp
          (LinearMap.adjoint (overlapLeftEmbedding A B a))).comp
        (P.comp ((overlapLeftEmbedding A B a').comp inclusion)) := by
          rw [adjoint_overlapLeftEmbedding_comp_tensorMap_right_adjoint_hom (A := A) a inclusion,
            tensorMap_right_comp_overlapLeftEmbedding_hom (A := A) a' inclusion]
    _ = (LinearMap.adjoint inclusion).comp
        ((leftInteractionCoefficient P a a').comp inclusion) := by
          simp only [leftInteractionCoefficient, LinearMap.comp_assoc]
    _ = isotypicLeftAction (leftInteractionAlgebra P) component coefficient := by
          apply LinearMap.ext
          intro vector
          have hactionApply :
              inclusion
                (isotypicLeftAction (leftInteractionAlgebra P) component coefficient vector) =
              (leftInteractionCoefficient P a a') (inclusion vector) := by
            exact congrArg (fun map => map vector) haction
          change LinearMap.adjoint inclusion
              ((leftInteractionCoefficient P a a') (inclusion vector)) =
            isotypicLeftAction (leftInteractionAlgebra P) component coefficient vector
          calc
            LinearMap.adjoint inclusion
                ((leftInteractionCoefficient P a a') (inclusion vector)) =
                LinearMap.adjoint inclusion
                  (inclusion
                    (isotypicLeftAction (leftInteractionAlgebra P) component coefficient vector)) := by
                      exact congrArg (LinearMap.adjoint inclusion) hactionApply.symm
            _ = isotypicLeftAction (leftInteractionAlgebra P) component coefficient vector := by
                  exact adjoint_submoduleSubtype_apply_subtype
                    (component.1.restrictScalars Complex)
                    (isotypicLeftAction (leftInteractionAlgebra P) component coefficient vector)

/-- The diagonal left interaction action on the finite multiplicity Hilbert space. -/
noncomputable def isotypicLeftActionOnCopies
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (operator : S) :
    Semantics.Operator (PiLp 2 (fun _ : Fin n => W.restrictScalars Complex)) where
  toFun := fun vector => operator • vector
  map_add' := by
    intro left right
    exact smul_add operator left right
  map_smul' := by
    intro scalar vector
    exact smul_comm operator scalar vector

/-- The star relation for the interaction-algebra action on one isotypic sector. -/
theorem isotypicLeftAction_adjoint
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (component : isotypicComponents S B) (operator : S) :
    LinearMap.adjoint (isotypicLeftAction S component operator) =
      isotypicLeftAction S component (star operator) := by
  refine ((LinearMap.eq_adjoint_iff
    (isotypicLeftAction S component (star operator))
    (isotypicLeftAction S component operator)).mpr ?_).symm
  intro left right
  change inner Complex (((star operator : S) : Semantics.Operator B) (left : B)) (right : B) =
    inner Complex (left : B) ((operator : Semantics.Operator B) (right : B))
  have hstar : LinearMap.adjoint ((star operator : S) : Semantics.Operator B) =
      (operator : Semantics.Operator B) := by
    rw [← LinearMap.star_eq_adjoint]
    change (↑(star (star operator) : S) : Semantics.Operator B) =
      (operator : Semantics.Operator B)
    simp
  rw [← hstar]
  exact (LinearMap.adjoint_inner_right ((star operator : S) : Semantics.Operator B)
    (left : B) (right : B)).symm

/-- The diagonal copy action retains the same star relation. -/
theorem isotypicLeftActionOnCopies_adjoint
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (operator : S) :
    LinearMap.adjoint (isotypicLeftActionOnCopies S W n operator) =
      isotypicLeftActionOnCopies S W n (star operator) := by
  refine ((LinearMap.eq_adjoint_iff
    (isotypicLeftActionOnCopies S W n (star operator))
    (isotypicLeftActionOnCopies S W n operator)).mpr ?_).symm
  intro left right
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro index _
  change inner Complex (((star operator : S) : Semantics.Operator B)
      ((left index : W.restrictScalars Complex) : B))
      ((right index : W.restrictScalars Complex) : B) =
    inner Complex ((left index : W.restrictScalars Complex) : B)
      ((operator : Semantics.Operator B)
        ((right index : W.restrictScalars Complex) : B))
  have hstar : LinearMap.adjoint ((star operator : S) : Semantics.Operator B) =
      (operator : Semantics.Operator B) := by
    rw [← LinearMap.star_eq_adjoint]
    change (↑(star (star operator) : S) : Semantics.Operator B) =
      (operator : Semantics.Operator B)
    simp
  rw [← hstar]
  exact (LinearMap.adjoint_inner_right ((star operator : S) : Semantics.Operator B)
    ((left index : W.restrictScalars Complex) : B)
    ((right index : W.restrictScalars Complex) : B)).symm

/--
The isotypic coordinate equivalence can be chosen unitary while retaining its
exact left-interaction-algebra intertwining equation.  The underlying
`S`-linear equivalence is polar-normalized through its positive Gram operator;
the resulting transport is the boundary-coordinate unitary used by the BV03
overlap block equality below.
-/
theorem isotypic_star_unitary_intertwiner
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (component : isotypicComponents S B) (n : Nat) (W : Submodule S B)
    (e : component.1 ≃ₗ[S] (Fin n → W)) :
    ∃ U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (PiLp 2 (fun _ : Fin n => W.restrictScalars Complex)),
      ∀ operator : S,
        U.toLinearEquiv.toLinearMap.comp (isotypicLeftAction S component operator) =
          (isotypicLeftActionOnCopies S W n operator).comp U.toLinearEquiv.toLinearMap := by
  have hH := fun operator : S => isotypicLeftAction_adjoint S component operator
  have hK := fun operator : S => isotypicLeftActionOnCopies_adjoint S W n operator
  let componentTransport : (component.1.restrictScalars Complex) ≃ₗ[S] component.1 :=
    Submodule.restrictScalarsEquiv (S := Complex) (R := S) (M := B) component.1
  let factorTransport : W ≃ₗ[S] W.restrictScalars Complex :=
    (Submodule.restrictScalarsEquiv (S := Complex) (R := S) (M := B) W).symm
  let piFactorTransport : (Fin n → W) ≃ₗ[S] (Fin n → W.restrictScalars Complex) :=
    LinearEquiv.piCongrRight (fun _ => factorTransport)
  let e0 : (component.1.restrictScalars Complex) ≃ₗ[S]
      (Fin n → W.restrictScalars Complex) :=
    componentTransport.trans (e.trans piFactorTransport)
  let rawEquiv : (PiLp 2 (fun _ : Fin n => W.restrictScalars Complex)) ≃ₗ[Complex]
      (Fin n → W.restrictScalars Complex) :=
    (PiLp.continuousLinearEquiv 2 Complex
      (fun _ : Fin n => W.restrictScalars Complex)).toLinearEquiv
  let eHilbert : (component.1.restrictScalars Complex) ≃ₗ[Complex]
      (PiLp 2 (fun _ : Fin n => W.restrictScalars Complex)) :=
    (e0.restrictScalars Complex).trans rawEquiv.symm
  have he_intertwines : ∀ operator : S,
      eHilbert.toLinearMap.comp (isotypicLeftAction S component operator) =
        (isotypicLeftActionOnCopies S W n operator).comp eHilbert.toLinearMap := by
    intro operator
    apply LinearMap.ext
    intro vector
    ext index
    dsimp [eHilbert, rawEquiv, isotypicLeftAction, isotypicLeftActionOnCopies]
    change (e0 (operator • vector) index : B) =
      ((operator : Semantics.Operator B) (e0 vector index : B))
    rw [e0.map_smul]
    rfl
  exact unitary_star_intertwiner_of_linearEquiv
    (isotypicLeftAction S component) (isotypicLeftActionOnCopies S W n) hH hK eHilbert
    he_intertwines

/-- The left interaction action restricted to the simple module factor. -/
noncomputable def isotypicLeftActionOnSimple
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (operator : S) :
    Semantics.Operator (W.restrictScalars Complex) where
  toFun := fun vector => operator • vector
  map_add' := by
    intro left right
    exact smul_add operator left right
  map_smul' := by
    intro scalar vector
    exact smul_comm operator scalar vector

/-- The literal tensor-factor action on the `W tensor C^n` isotypic block. -/
noncomputable def isotypicTensorLeftAction
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (operator : S) :
    Semantics.Operator
      (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)) :=
  TensorProduct.map (isotypicLeftActionOnSimple S W operator)
    (1 : Semantics.Operator (EuclideanSpace Complex (Fin n)))

/--
The canonical linear coordinates identifying a finite copy space with a simple
factor tensored with its multiplicity Hilbert space.  The next theorem proves
that these coordinates intertwine the displayed left interaction action; the
polar normalization below promotes them to a unitary transport.
-/
noncomputable def isotypicCopyTensorCoordinates
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) :
    (PiLp 2 (fun _ : Fin n => W.restrictScalars Complex)) ≃ₗ[Complex]
      (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)) :=
  let W0 := W.restrictScalars Complex
  let coordinates : (PiLp 2 (fun _ : Fin n => W0)) ≃ₗ[Complex]
      (Fin n → W0) :=
    (PiLp.continuousLinearEquiv 2 Complex (fun _ : Fin n => W0)).toLinearEquiv
  let euclideanCoordinates : (EuclideanSpace Complex (Fin n)) ≃ₗ[Complex]
      (Fin n → Complex) :=
    (EuclideanSpace.equiv (Fin n) Complex).toLinearEquiv
  coordinates.trans
    ((TensorProduct.piScalarRight Complex Complex W0 (Fin n)).symm.trans
      (TensorProduct.congr (LinearEquiv.refl Complex W0) euclideanCoordinates.symm))

/-- The coordinate map sends a copy basis vector to its literal tensor basis vector. -/
theorem isotypicCopyTensorCoordinates_single
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (i : Fin n) (w : W.restrictScalars Complex) :
    isotypicCopyTensorCoordinates S W n (PiLp.single 2 i w) =
      w ⊗ₜ[Complex] EuclideanSpace.single i 1 := by
  change (TensorProduct.congr (LinearEquiv.refl Complex (W.restrictScalars Complex))
      ((EuclideanSpace.equiv (Fin n) Complex).toLinearEquiv.symm))
      ((TensorProduct.piScalarRight Complex Complex (W.restrictScalars Complex) (Fin n)).symm
        (Pi.single i w)) = _
  rw [TensorProduct.piScalarRight_symm_single]
  rw [TensorProduct.congr_tmul]
  rfl

/-- The diagonal copy action preserves individual finite copy vectors. -/
theorem isotypicLeftActionOnCopies_apply_single
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (operator : S) (i : Fin n)
    (w : W.restrictScalars Complex) :
    isotypicLeftActionOnCopies S W n operator (PiLp.single 2 i w) =
      PiLp.single 2 i (isotypicLeftActionOnSimple S W operator w) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [isotypicLeftActionOnCopies, isotypicLeftActionOnSimple]
  · simp [isotypicLeftActionOnCopies, isotypicLeftActionOnSimple, h]

/--
The canonical copy-to-tensor coordinates intertwine the diagonal left action
with the literal simple-factor tensor action.  This is the operator equality
that turns the isotypic module statement into the left half of the BV03 block.
-/
theorem isotypicCopyTensorCoordinates_intertwines
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (operator : S) :
    (isotypicCopyTensorCoordinates S W n).toLinearMap.comp
        (isotypicLeftActionOnCopies S W n operator) =
      (isotypicTensorLeftAction S W n operator).comp
        (isotypicCopyTensorCoordinates S W n).toLinearMap := by
  apply LinearMap.ext
  intro vector
  have hvector : (∑ i, PiLp.single 2 i (vector i)) = vector := by
    ext j
    simp
  rw [← hvector]
  simp only [LinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [isotypicLeftActionOnCopies_apply_single]
  change isotypicCopyTensorCoordinates S W n (PiLp.single 2 i
      (isotypicLeftActionOnSimple S W operator (vector i))) =
    isotypicTensorLeftAction S W n operator
      (isotypicCopyTensorCoordinates S W n (PiLp.single 2 i (vector i)))
  have hleft := isotypicCopyTensorCoordinates_single (B := B) S W n i
    (isotypicLeftActionOnSimple S W operator (vector i))
  have hright := isotypicCopyTensorCoordinates_single (B := B) S W n i (vector i)
  rw [hleft, hright]
  simp [isotypicTensorLeftAction]

/-- The finite multiplicity matrix acting on the Hilbert factor `C^n`. -/
noncomputable def isotypicMultiplicityMatrixOperator (n : Nat)
    (matrix : Matrix (Fin n) (Fin n) Complex) :
    Semantics.Operator (EuclideanSpace Complex (Fin n)) :=
  let coordinates : (EuclideanSpace Complex (Fin n)) ≃ₗ[Complex]
      (Fin n → Complex) :=
    (EuclideanSpace.equiv (Fin n) Complex).toLinearEquiv
  coordinates.symm.toLinearMap.comp
    ((Matrix.toLin' matrix).comp coordinates.toLinearMap)

/-- The matrix operator has the expected coordinate action. -/
theorem isotypicMultiplicityMatrixOperator_apply (n : Nat)
    (matrix : Matrix (Fin n) (Fin n) Complex)
    (vector : EuclideanSpace Complex (Fin n)) :
    isotypicMultiplicityMatrixOperator n matrix vector =
      (EuclideanSpace.equiv (Fin n) Complex).symm (Matrix.mulVec matrix vector) := by
  rfl

/-- The same scalar matrix acting on a finite direct sum of simple-factor copies. -/
noncomputable def isotypicMultiplicityMatrixActionOnCopies
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (matrix : Matrix (Fin n) (Fin n) Complex) :
    Semantics.Operator (PiLp 2 (fun _ : Fin n => W.restrictScalars Complex)) :=
  let W0 := W.restrictScalars Complex
  let coordinates : (PiLp 2 (fun _ : Fin n => W0)) ≃ₗ[Complex]
      (Fin n → W0) :=
    (PiLp.continuousLinearEquiv 2 Complex (fun _ : Fin n => W0)).toLinearEquiv
  let action : (Fin n → W0) →ₗ[Complex] (Fin n → W0) :=
    (endVecRingEquivMatrixEnd (Fin n) Complex W0).symm
      (fun row column => matrix row column • (1 : Module.End Complex W0))
  coordinates.symm.toLinearMap.comp (action.comp coordinates.toLinearMap)

/-- A multiplicity matrix sends a single copy vector to the corresponding row sum. -/
theorem isotypicMultiplicityMatrixActionOnCopies_single
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (matrix : Matrix (Fin n) (Fin n) Complex)
    (i : Fin n) (w : W.restrictScalars Complex) :
    isotypicMultiplicityMatrixActionOnCopies S W n matrix (PiLp.single 2 i w) =
      ∑ row, PiLp.single 2 row (matrix row i • w) := by
  apply (PiLp.continuousLinearEquiv 2 Complex
    (fun _ : Fin n => W.restrictScalars Complex)).injective
  funext row
  simp only [map_sum, Finset.sum_apply]
  change (∑ column, matrix row column • (Pi.single i w) column) =
    ∑ r, Pi.single r (matrix r i • w) row
  simp [Pi.single_apply]

/-- The multiplicity matrix sends a standard basis vector to its column. -/
theorem isotypicMultiplicityMatrixOperator_single (n : Nat)
    (matrix : Matrix (Fin n) (Fin n) Complex) (i : Fin n) :
    isotypicMultiplicityMatrixOperator n matrix (EuclideanSpace.single i 1) =
      ∑ row, matrix row i • EuclideanSpace.single row 1 := by
  rw [isotypicMultiplicityMatrixOperator_apply]
  apply (EuclideanSpace.equiv (Fin n) Complex).injective
  ext row
  simp [Pi.single_apply]

/--
Canonical copy-to-tensor coordinates carry a multiplicity matrix precisely to
the right tensor factor.  This is the concrete conversion from Schur's matrix
description of a commutant to `1 tensor matrixOperator`.
-/
theorem isotypicCopyTensorCoordinates_matrix_intertwines
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (matrix : Matrix (Fin n) (Fin n) Complex) :
    (isotypicCopyTensorCoordinates S W n).toLinearMap.comp
        (isotypicMultiplicityMatrixActionOnCopies S W n matrix) =
      (TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex))
        (isotypicMultiplicityMatrixOperator n matrix)).comp
        (isotypicCopyTensorCoordinates S W n).toLinearMap := by
  apply LinearMap.ext
  intro vector
  have hvector : (∑ i, PiLp.single 2 i (vector i)) = vector := by
    ext j
    simp
  rw [← hvector]
  simp only [LinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [isotypicMultiplicityMatrixActionOnCopies_single]
  simp only [map_sum]
  change (∑ row, isotypicCopyTensorCoordinates S W n
      (PiLp.single 2 row (matrix row i • vector i))) =
    (TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex))
      (isotypicMultiplicityMatrixOperator n matrix))
      (isotypicCopyTensorCoordinates S W n (PiLp.single 2 i (vector i)))
  simp_rw [isotypicCopyTensorCoordinates_single]
  rw [TensorProduct.map_tmul, isotypicMultiplicityMatrixOperator_single]
  rw [TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [TensorProduct.tmul_smul]
  rfl

/-- The simple factor written with its ambient complex Hilbert-space scalar structure. -/
noncomputable def isotypicSimpleFactorCoordinate
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B)) (W : Submodule S B) :
    W ≃ₗ[Complex] W.restrictScalars Complex where
  toFun := fun vector => ⟨vector, vector.property⟩
  invFun := fun vector => ⟨vector, vector.property⟩
  left_inv := by
    intro vector
    rfl
  right_inv := by
    intro vector
    rfl
  map_add' := by
    intro left right
    rfl
  map_smul' := by
    intro scalar vector
    rfl

/-- The complex factor coordinates still intertwine the original `S` action. -/
theorem isotypicSimpleFactorCoordinate_intertwines
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (operator : S) (vector : W) :
    isotypicSimpleFactorCoordinate S W (operator • vector) =
      isotypicLeftActionOnSimple S W operator (isotypicSimpleFactorCoordinate S W vector) := by
  rfl

/-- The pointwise left action on the algebraic multiplicity-copy coordinates. -/
noncomputable def isotypicLeftActionOnFunctionCopies
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (operator : S) :
    Module.End Complex (Fin n → W) where
  toFun := fun vector => operator • vector
  map_add' := by
    intro left right
    exact smul_add operator left right
  map_smul' := by
    intro scalar vector
    ext index
    change (operator : Semantics.Operator B) (scalar • (vector index : B)) =
      scalar • (operator : Semantics.Operator B) (vector index : B)
    exact (operator : Semantics.Operator B).map_smul scalar (vector index : B)

/--
The full algebraic-to-Hilbert tensor coordinate map for one simple isotypic
block.  It first changes the simple factor to its complex Hilbert structure,
then uses the canonical finite-copy tensor coordinates.
-/
noncomputable def isotypicSimpleCopyTensorCoordinates
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) :
    (Fin n → W) ≃ₗ[Complex]
      (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)) :=
  let piFactorTransport : (Fin n → W) ≃ₗ[Complex]
      (Fin n → W.restrictScalars Complex) :=
    LinearEquiv.piCongrRight (fun _ => isotypicSimpleFactorCoordinate S W)
  let rawEquiv : (PiLp 2 (fun _ : Fin n => W.restrictScalars Complex)) ≃ₗ[Complex]
      (Fin n → W.restrictScalars Complex) :=
    (PiLp.continuousLinearEquiv 2 Complex
      (fun _ : Fin n => W.restrictScalars Complex)).toLinearEquiv
  piFactorTransport.trans
    (rawEquiv.symm.trans (isotypicCopyTensorCoordinates S W n))

/-- A single algebraic copy basis vector maps to the matching tensor basis vector. -/
theorem isotypicSimpleCopyTensorCoordinates_single
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (i : Fin n) (w : W) :
    isotypicSimpleCopyTensorCoordinates S W n (Pi.single i w) =
      isotypicSimpleFactorCoordinate S W w ⊗ₜ[Complex] EuclideanSpace.single i 1 := by
  change isotypicCopyTensorCoordinates S W n
      (PiLp.single 2 i (isotypicSimpleFactorCoordinate S W w)) = _
  rw [isotypicCopyTensorCoordinates_single]

/-- The coordinate map has the explicit finite-copy expansion. -/
theorem isotypicSimpleCopyTensorCoordinates_apply
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (vector : Fin n → W) :
    isotypicSimpleCopyTensorCoordinates S W n vector =
      ∑ i, isotypicSimpleFactorCoordinate S W (vector i) ⊗ₜ[Complex]
        EuclideanSpace.single i 1 := by
  have hvector : (∑ i, Pi.single i (vector i)) = vector := Finset.univ_sum_single vector
  conv_lhs => rw [← hvector]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact isotypicSimpleCopyTensorCoordinates_single S W n i (vector i)

/-- The algebraic copy coordinates intertwine the left action with `actionOnW tensor 1`. -/
theorem isotypicSimpleCopyTensorCoordinates_intertwines
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (operator : S) :
    (isotypicSimpleCopyTensorCoordinates S W n).toLinearMap.comp
        (isotypicLeftActionOnFunctionCopies S W n operator) =
      (isotypicTensorLeftAction S W n operator).comp
        (isotypicSimpleCopyTensorCoordinates S W n).toLinearMap := by
  apply LinearMap.ext
  intro vector
  change isotypicSimpleCopyTensorCoordinates S W n (operator • vector) =
    isotypicTensorLeftAction S W n operator
      (isotypicSimpleCopyTensorCoordinates S W n vector)
  rw [isotypicSimpleCopyTensorCoordinates_apply,
    isotypicSimpleCopyTensorCoordinates_apply]
  simp only [map_sum, TensorProduct.map_tmul, Module.End.one_apply]
  apply Finset.sum_congr rfl
  intro i _
  change isotypicSimpleFactorCoordinate S W (operator • vector i) ⊗ₜ[Complex]
      EuclideanSpace.single i 1 =
    isotypicTensorLeftAction S W n operator
      (isotypicSimpleFactorCoordinate S W (vector i) ⊗ₜ[Complex]
        EuclideanSpace.single i 1)
  rw [isotypicSimpleFactorCoordinate_intertwines]
  simp [isotypicTensorLeftAction]

/--
Pull an operator in the commutant of the left tensor action back to an
`S`-linear endomorphism of the algebraic multiplicity copies.  This is the
bridge that makes the Schur matrix theorem apply to a transported right
interaction coefficient.
-/
noncomputable def isotypicTensorCommutantPullback
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat)
    (T : Semantics.Operator
      (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)))
    (hcommute : ∀ operator : S, Commute T (isotypicTensorLeftAction S W n operator)) :
    Module.End S (Fin n → W) := by
  let E := isotypicSimpleCopyTensorCoordinates S W n
  exact
    { toFun := fun vector => E.symm (T (E vector))
      map_add' := by
        intro left right
        simp
      map_smul' := by
        intro operator vector
        apply E.injective
        change E (E.symm (T (E (operator • vector)))) =
          E ((RingHom.id S) operator • E.symm (T (E vector)))
        have hE : E (operator • vector) =
            isotypicTensorLeftAction S W n operator (E vector) := by
          simpa [isotypicLeftActionOnFunctionCopies, LinearMap.comp_apply] using
            congrArg (fun map : (Fin n → W) →ₗ[Complex]
                (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)) =>
              map vector)
              (isotypicSimpleCopyTensorCoordinates_intertwines S W n operator)
        have hE' : E (operator • E.symm (T (E vector))) =
            isotypicTensorLeftAction S W n operator
              (T (E vector)) := by
          have hraw := congrArg (fun map : (Fin n → W) →ₗ[Complex]
                (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)) =>
              map (E.symm (T (E vector))))
              (isotypicSimpleCopyTensorCoordinates_intertwines S W n operator)
          change E (operator • E.symm (T (E vector))) =
            isotypicTensorLeftAction S W n operator
              (E (E.symm (T (E vector)))) at hraw
          rw [E.apply_symm_apply] at hraw
          exact hraw
        have htransport : T (E (operator • vector)) =
            E (operator • E.symm (T (E vector))) := by
          calc
          T (E (operator • vector)) =
              T (isotypicTensorLeftAction S W n operator (E vector)) := by rw [hE]
          _ = isotypicTensorLeftAction S W n operator (T (E vector)) := by
              exact congrArg
                (fun map : Semantics.Operator
                    (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)) =>
                  map (E vector))
                (hcommute operator).eq
          _ = E (operator • E.symm (T (E vector))) := hE'.symm
        simpa only [E.apply_symm_apply, RingHom.id_apply] using htransport }

/-- The scalar multiplicity matrix on algebraic finite copies of a simple factor. -/
noncomputable def isotypicMultiplicityMatrixActionOnFunctionCopies
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (matrix : Matrix (Fin n) (Fin n) Complex) :
    Module.End Complex (Fin n → W) :=
  (endVecRingEquivMatrixEnd (Fin n) Complex W).symm
    (fun row column => matrix row column • (1 : Module.End Complex W))

/-- The algebraic multiplicity action has the usual row-by-column matrix formula. -/
theorem isotypicMultiplicityMatrixActionOnFunctionCopies_apply
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (matrix : Matrix (Fin n) (Fin n) Complex)
    (vector : Fin n → W) (row : Fin n) :
    isotypicMultiplicityMatrixActionOnFunctionCopies S W n matrix vector row =
      ∑ column, matrix row column • vector column := by
  rfl

/-- A matrix sends one algebraic multiplicity basis vector to its matching column. -/
theorem isotypicMultiplicityMatrixActionOnFunctionCopies_single
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (matrix : Matrix (Fin n) (Fin n) Complex)
    (i : Fin n) (w : W) :
    isotypicMultiplicityMatrixActionOnFunctionCopies S W n matrix (Pi.single i w) =
      ∑ row, Pi.single row (matrix row i • w) := by
  funext row
  rw [isotypicMultiplicityMatrixActionOnFunctionCopies_apply]
  simp [Pi.single_apply]

/--
Algebraic multiplicity matrices become literal operators on the right tensor
factor under the simple-copy coordinates.
-/
theorem isotypicSimpleCopyTensorCoordinates_matrix_intertwines
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (matrix : Matrix (Fin n) (Fin n) Complex) :
    (isotypicSimpleCopyTensorCoordinates S W n).toLinearMap.comp
        (isotypicMultiplicityMatrixActionOnFunctionCopies S W n matrix) =
      (TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex))
        (isotypicMultiplicityMatrixOperator n matrix)).comp
        (isotypicSimpleCopyTensorCoordinates S W n).toLinearMap := by
  apply LinearMap.ext
  intro vector
  have hvector : (∑ i, Pi.single i (vector i)) = vector := Finset.univ_sum_single vector
  rw [← hvector]
  simp only [LinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [isotypicMultiplicityMatrixActionOnFunctionCopies_single]
  simp only [map_sum]
  change (∑ row, isotypicSimpleCopyTensorCoordinates S W n
      (Pi.single row (matrix row i • vector i))) =
    (TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex))
      (isotypicMultiplicityMatrixOperator n matrix))
      (isotypicSimpleCopyTensorCoordinates S W n (Pi.single i (vector i)))
  simp_rw [isotypicSimpleCopyTensorCoordinates_single]
  rw [TensorProduct.map_tmul, isotypicMultiplicityMatrixOperator_single]
  rw [TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [TensorProduct.tmul_smul]
  rfl

/--
An operator commuting with the left action on one finite simple isotypic block
is exactly `1 tensor R` after the concrete tensor coordinates.  This is the
right-factor equality required by the BV03 overlap decomposition.
-/
theorem isotypicTensor_commutant_matrix_factorization
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) [IsSimpleModule S W]
    (n : Nat)
    (T : Semantics.Operator
      (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)))
    (hcommute : ∀ operator : S, Commute T (isotypicTensorLeftAction S W n operator)) :
    ∃ matrix : Matrix (Fin n) (Fin n) Complex,
      T = TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex))
        (isotypicMultiplicityMatrixOperator n matrix) := by
  let Tpull := isotypicTensorCommutantPullback S W n T hcommute
  obtain ⟨matrix, hmatrix⟩ := isotypic_commutant_matrix_factorization S W n Tpull
  refine ⟨matrix, ?_⟩
  let E := isotypicSimpleCopyTensorCoordinates S W n
  let R := TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex))
    (isotypicMultiplicityMatrixOperator n matrix)
  have hpull : ∀ vector : Fin n → W,
      Tpull vector = isotypicMultiplicityMatrixActionOnFunctionCopies S W n matrix vector := by
    intro vector
    ext row
    rw [isotypicMultiplicityMatrixActionOnFunctionCopies_apply]
    exact congrArg Subtype.val (hmatrix vector row)
  have hcoordinates : ∀ vector : Fin n → W,
      E (isotypicMultiplicityMatrixActionOnFunctionCopies S W n matrix vector) = R (E vector) := by
    intro vector
    simpa [E, R, LinearMap.comp_apply] using
      congrArg (fun map : (Fin n → W) →ₗ[Complex]
          (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)) =>
        map vector)
        (isotypicSimpleCopyTensorCoordinates_matrix_intertwines S W n matrix)
  apply LinearMap.ext
  intro vector
  let preimage := E.symm vector
  calc
    T vector = E (Tpull preimage) := by
      change T vector = E (E.symm (T (E preimage)))
      rw [E.apply_symm_apply]
      rw [show E preimage = vector by simp [preimage]]
    _ = E (isotypicMultiplicityMatrixActionOnFunctionCopies S W n matrix preimage) := by
      rw [hpull preimage]
    _ = R (E preimage) := hcoordinates preimage
    _ = R vector := by rw [show E preimage = vector by simp [preimage]]

/-- The simple tensor-factor action respects the involution of the interaction algebra. -/
theorem isotypicLeftActionOnSimple_adjoint
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (operator : S) :
    LinearMap.adjoint (isotypicLeftActionOnSimple S W operator) =
      isotypicLeftActionOnSimple S W (star operator) := by
  refine ((LinearMap.eq_adjoint_iff
    (isotypicLeftActionOnSimple S W (star operator))
    (isotypicLeftActionOnSimple S W operator)).mpr ?_).symm
  intro left right
  change inner Complex (((star operator : S) : Semantics.Operator B) (left : B))
      (right : B) =
    inner Complex (left : B) ((operator : Semantics.Operator B) (right : B))
  have hstar : LinearMap.adjoint ((star operator : S) : Semantics.Operator B) =
      (operator : Semantics.Operator B) := by
    rw [← LinearMap.star_eq_adjoint]
    change (↑(star (star operator) : S) : Semantics.Operator B) =
      (operator : Semantics.Operator B)
    simp
  rw [← hstar]
  exact (LinearMap.adjoint_inner_right ((star operator : S) : Semantics.Operator B)
    (left : B) (right : B)).symm

/-- The literal tensor action has the corresponding tensor-product adjoint. -/
theorem isotypicTensorLeftAction_adjoint
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (operator : S) :
    LinearMap.adjoint (isotypicTensorLeftAction S W n operator) =
      isotypicTensorLeftAction S W n (star operator) := by
  simp [isotypicTensorLeftAction, isotypicLeftActionOnSimple_adjoint]

/--
Polar-normalize the canonical copy coordinates.  The resulting transport is
an actual unitary and conjugates every left interaction coefficient to an
operator of the form `actionOnW tensor 1`.
-/
theorem isotypic_copy_tensor_unitary_intertwiner
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) :
    ∃ U : Semantics.UnitaryTransport
      (PiLp 2 (fun _ : Fin n => W.restrictScalars Complex))
      (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)),
      ∀ operator : S,
        U.toLinearEquiv.toLinearMap.comp (isotypicLeftActionOnCopies S W n operator) =
          (isotypicTensorLeftAction S W n operator).comp U.toLinearEquiv.toLinearMap := by
  exact unitary_star_intertwiner_of_linearEquiv
    (isotypicLeftActionOnCopies S W n) (isotypicTensorLeftAction S W n)
    (fun operator => isotypicLeftActionOnCopies_adjoint S W n operator)
    (fun operator => isotypicTensorLeftAction_adjoint S W n operator)
    (isotypicCopyTensorCoordinates S W n)
    (fun operator => isotypicCopyTensorCoordinates_intertwines S W n operator)

/--
An intertwining equation identifies the corresponding conjugated operator.
This small algebraic step is used immediately to turn the unitary isotypic
coordinates into an equality of the actual overlap coefficient operators.
-/
theorem unitaryTransport_conjOperator_eq_of_intertwines
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (A : Semantics.Operator H)
    (B : Semantics.Operator K)
    (hintertwines : U.toLinearEquiv.toLinearMap.comp A =
      B.comp U.toLinearEquiv.toLinearMap) :
    U.conjOperator A = B := by
  apply LinearMap.ext
  intro vector
  change U.toLinearEquiv (A (U.toLinearEquiv.symm vector)) = B vector
  calc
    U.toLinearEquiv (A (U.toLinearEquiv.symm vector)) =
        B (U.toLinearEquiv (U.toLinearEquiv.symm vector)) := by
      exact congrArg (fun operator : H →ₗ[Complex] K =>
        operator (U.toLinearEquiv.symm vector)) hintertwines
    _ = B vector := by rw [U.toLinearEquiv.apply_symm_apply]

/--
The polar-normalized isotypic and copy coordinates compose to a unitary which
transports every element of the left interaction algebra to the literal left
tensor-factor action.  Both coefficient-side BV03 equations use this same
transport.
-/
theorem isotypic_tensor_unitary_intertwiner
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (component : isotypicComponents S B) (n : Nat) (W : Submodule S B)
    (e : component.1 ≃ₗ[S] (Fin n → W)) :
    ∃ U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)),
      ∀ operator : S,
        U.conjOperator (isotypicLeftAction S component operator) =
          isotypicTensorLeftAction S W n operator := by
  rcases isotypic_star_unitary_intertwiner S component n W e with ⟨Ucomponent, hcomponent⟩
  rcases isotypic_copy_tensor_unitary_intertwiner S W n with ⟨Ucopies, hcopies⟩
  let U := composeUnitaryTransport Ucomponent Ucopies
  refine ⟨U, ?_⟩
  intro operator
  apply unitaryTransport_conjOperator_eq_of_intertwines U
  change
    (Ucopies.toLinearEquiv.toLinearMap.comp Ucomponent.toLinearEquiv.toLinearMap).comp
        (isotypicLeftAction S component operator) =
      (isotypicTensorLeftAction S W n operator).comp
        (Ucopies.toLinearEquiv.toLinearMap.comp Ucomponent.toLinearEquiv.toLinearMap)
  calc
    (Ucopies.toLinearEquiv.toLinearMap.comp Ucomponent.toLinearEquiv.toLinearMap).comp
        (isotypicLeftAction S component operator) =
        Ucopies.toLinearEquiv.toLinearMap.comp
          (Ucomponent.toLinearEquiv.toLinearMap.comp
            (isotypicLeftAction S component operator)) := by
          rw [LinearMap.comp_assoc]
    _ = Ucopies.toLinearEquiv.toLinearMap.comp
          ((isotypicLeftActionOnCopies S W n operator).comp
            Ucomponent.toLinearEquiv.toLinearMap) := by
          rw [hcomponent operator]
    _ = (Ucopies.toLinearEquiv.toLinearMap.comp
          (isotypicLeftActionOnCopies S W n operator)).comp
            Ucomponent.toLinearEquiv.toLinearMap := by
          rw [← LinearMap.comp_assoc]
    _ = ((isotypicTensorLeftAction S W n operator).comp
          Ucopies.toLinearEquiv.toLinearMap).comp Ucomponent.toLinearEquiv.toLinearMap := by
          rw [hcopies operator]
    _ = (isotypicTensorLeftAction S W n operator).comp
          (Ucopies.toLinearEquiv.toLinearMap.comp Ucomponent.toLinearEquiv.toLinearMap) := by
      rw [LinearMap.comp_assoc]

/--
The finite multiplicity Hilbert space lifted to the ambient universe of the
overlap factor.  It is canonically `C^n`; the lift is only the universe
bookkeeping required by `CompositeSystem`'s same-universe interface.
-/
abbrev isotypicLiftedMultiplicity (n : Nat) : Type u :=
  EuclideanSpace Complex (ULift.{u} (Fin n))

/-- Reindex the ordinary `C^n` coordinate space along `Fin n ≃ ULift (Fin n)`. -/
noncomputable def isotypicMultiplicityLiftIsometry (n : Nat) :
    EuclideanSpace Complex (Fin n) ≃ₗᵢ[Complex]
      isotypicLiftedMultiplicity.{u} n :=
  LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex (Equiv.ulift).symm

/--
Tensoring the multiplicity reindexing with a simple factor gives an actual
unitary transport between the two tensor coordinate systems.
-/
noncomputable def isotypicMultiplicityLiftTensorUnitary
    (W : Type u) [NormedAddCommGroup W] [InnerProductSpace Complex W]
    [Semantics.FiniteQuantumSystem W] (n : Nat) :
    Semantics.UnitaryTransport
      (W ⊗[Complex] EuclideanSpace Complex (Fin n))
      (W ⊗[Complex] isotypicLiftedMultiplicity.{u} n) := by
  let e := (isotypicMultiplicityLiftIsometry.{u} n).lTensor W
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := e.inner_map_map }

/--
The lifted multiplicity coordinate change leaves a left tensor action intact
and carries its inert multiplicity identity to the lifted identity.
-/
theorem isotypicMultiplicityLiftTensorUnitary_conj_tensorMap_left
    (W : Type u) [NormedAddCommGroup W] [InnerProductSpace Complex W]
    [Semantics.FiniteQuantumSystem W] (n : Nat) (A : Semantics.Operator W) :
    (isotypicMultiplicityLiftTensorUnitary W n).conjOperator
      (TensorProduct.map A
        (1 : Semantics.Operator (EuclideanSpace Complex (Fin n)))) =
      TensorProduct.map A
        (1 : Semantics.Operator (isotypicLiftedMultiplicity.{u} n)) := by
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul w multiplicity =>
      simp [isotypicMultiplicityLiftTensorUnitary,
        isotypicMultiplicityLiftIsometry, Semantics.UnitaryTransport.conjOperator]
      have hcoordinate :
          (LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex (Equiv.ulift).symm)
              ((LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex Equiv.ulift)
                multiplicity) = multiplicity := by
        change (isotypicMultiplicityLiftIsometry.{u} n)
            ((isotypicMultiplicityLiftIsometry.{u} n).symm multiplicity) = multiplicity
        exact (isotypicMultiplicityLiftIsometry.{u} n).apply_symm_apply multiplicity
      exact congrArg (fun vector => A w ⊗ₜ[Complex] vector) hcoordinate
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

/-- Transport a multiplicity-side matrix along the canonical finite-coordinate lift. -/
noncomputable def isotypicMultiplicityLiftConjOperator
    (n : Nat) (R : Semantics.Operator (EuclideanSpace Complex (Fin n))) :
    Semantics.Operator (isotypicLiftedMultiplicity.{u} n) :=
  (isotypicMultiplicityLiftIsometry.{u} n).toLinearEquiv.toLinearMap.comp
    (R.comp (isotypicMultiplicityLiftIsometry.{u} n).toLinearEquiv.symm.toLinearMap)

/-- The multiplicity lift carries `1 tensor R` to `1 tensor` its lifted matrix. -/
theorem isotypicMultiplicityLiftTensorUnitary_conj_tensorMap_right
    (W : Type u) [NormedAddCommGroup W] [InnerProductSpace Complex W]
    [Semantics.FiniteQuantumSystem W] (n : Nat)
    (R : Semantics.Operator (EuclideanSpace Complex (Fin n))) :
    (isotypicMultiplicityLiftTensorUnitary W n).conjOperator
      (TensorProduct.map (1 : Semantics.Operator W) R) =
      TensorProduct.map (1 : Semantics.Operator W)
        (isotypicMultiplicityLiftConjOperator.{u} n R) := by
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul w multiplicity =>
      simp [isotypicMultiplicityLiftTensorUnitary,
        isotypicMultiplicityLiftConjOperator, isotypicMultiplicityLiftIsometry,
        Semantics.UnitaryTransport.conjOperator]
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

/-- A canonical normalized vector in the lifted nonzero multiplicity factor. -/
noncomputable def isotypicLiftedMultiplicityUnitVector (n : Nat) [NeZero n] :
    isotypicLiftedMultiplicity.{u} n :=
  EuclideanSpace.basisFun (ULift.{u} (Fin n)) Complex
    (ULift.up ⟨0, Nat.pos_of_neZero n⟩)

/-- The chosen lifted multiplicity coordinate is normalized. -/
theorem norm_isotypicLiftedMultiplicityUnitVector (n : Nat) [NeZero n] :
    ‖isotypicLiftedMultiplicityUnitVector.{u} n‖ = 1 := by
  simp [isotypicLiftedMultiplicityUnitVector]

/--
Restrict a right interaction coefficient to a left-isotypic component.  The
restriction is an honest module endomorphism: the commuting interaction
algebras make the coefficient `S`-linear, and full invariance of an isotypic
component supplies its codomain closure.
-/
noncomputable def rightInteractionCoefficientOnIsotypicComponent
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B) (c c' : C) :
    Module.End (leftInteractionAlgebra P) component.1 := by
  let coefficient := rightInteractionCoefficient Q c c'
  let coefficientEnd : Module.End (leftInteractionAlgebra P) B :=
    commutingOperatorAsModuleEnd (leftInteractionAlgebra P) coefficient (by
      intro operator
      exact interactionAlgebras_commute P Q hselfAdjoint hcommute operator.property
        (rightInteractionCoefficient_mem_rightInteractionAlgebra Q c c'))
  exact
    { toFun := fun vector =>
        ⟨coefficientEnd vector,
          (Submodule.IsFullyInvariant.of_mem_isotypicComponents component.2)
            coefficientEnd vector.property⟩
      map_add' := by
        intro left right
        apply Subtype.ext
        exact coefficientEnd.map_add left right
      map_smul' := by
        intro scalar vector
        apply Subtype.ext
        exact coefficientEnd.map_smul scalar vector }

/--
The same sector restriction regarded as a complex-linear Hilbert-space
operator.  It has no extra hypothesis: complex linearity is inherited from the
concrete right interaction coefficient on the overlap system.
-/
noncomputable def rightInteractionCoefficientOnIsotypicComponentOperator
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B) (c c' : C) :
    Semantics.Operator (component.1.restrictScalars Complex) := by
  let right := rightInteractionCoefficientOnIsotypicComponent P Q hselfAdjoint hcommute
    component c c'
  exact
    { toFun := fun vector => right vector
      map_add' := right.map_add
      map_smul' := by
        intro scalar vector
        apply Subtype.ext
        change rightInteractionCoefficient Q c c' (scalar • (vector : B)) =
          scalar • rightInteractionCoefficient Q c c' (vector : B)
        exact (rightInteractionCoefficient Q c c').map_smul scalar (vector : B) }

/-- The complex-linear restriction has exactly the existing `S`-module action. -/
theorem rightInteractionCoefficientOnIsotypicComponentOperator_apply
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B) (c c' : C)
    (vector : component.1.restrictScalars Complex) :
    rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
      component c c' vector =
      rightInteractionCoefficientOnIsotypicComponent P Q hselfAdjoint hcommute
        component c c' vector :=
  rfl

/-- The sector action is the concrete right coefficient after subtype inclusion. -/
theorem subtype_rightInteractionCoefficientOnIsotypicComponentOperator_apply
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B) (c c' : C)
    (vector : component.1.restrictScalars Complex) :
    (component.1.restrictScalars Complex).subtype
      (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
        component c c' vector) =
      rightInteractionCoefficient Q c c'
        ((component.1.restrictScalars Complex).subtype vector) := by
  rfl

/-- Compress the right overlap projector to the same left-isotypic sector. -/
noncomputable def overlapRightProjectorOnIsotypicComponent
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    Semantics.Operator
      (Semantics.CompositeSystem (component.1.restrictScalars Complex) C) :=
  overlapRightCompression Q (component.1.restrictScalars Complex).subtype

/--
The compressed right overlap block has precisely the restricted right
interaction coefficient on the same left-isotypic sector.
-/
theorem rightInteractionCoefficient_overlapRightProjectorOnIsotypicComponent
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B) (c c' : C) :
    rightInteractionCoefficient
      (overlapRightProjectorOnIsotypicComponent P Q component) c c' =
      rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
        component c c' := by
  let inclusion := (component.1.restrictScalars Complex).subtype
  let R := rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
    component c c'
  have haction : inclusion.comp R =
      (rightInteractionCoefficient Q c c').comp inclusion := by
    apply LinearMap.ext
    intro vector
    simpa [inclusion, R] using
      (subtype_rightInteractionCoefficientOnIsotypicComponentOperator_apply
        P Q hselfAdjoint hcommute component c c' vector)
  change rightInteractionCoefficient (overlapRightCompression Q inclusion) c c' = R
  calc
    _ = (LinearMap.adjoint inclusion).comp
        ((rightInteractionCoefficient Q c c').comp inclusion) :=
      rightInteractionCoefficient_overlapRightCompression Q inclusion c c'
    _ = (LinearMap.adjoint inclusion).comp (inclusion.comp R) := by
      rw [haction]
    _ = R := by
      apply LinearMap.ext
      intro vector
      change LinearMap.adjoint inclusion (inclusion (R vector)) = R vector
      exact adjoint_submoduleSubtype_apply_subtype
        (component.1.restrictScalars Complex) (R vector)

/--
The restricted right coefficient commutes with the full left interaction action
on its sector, by its already-proved `S`-linearity.
-/
theorem rightInteractionCoefficientOnIsotypicComponentOperator_commutes_leftAction
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B) (c c' : C)
    (operator : leftInteractionAlgebra P) :
    Commute
      (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
        component c c')
      (isotypicLeftAction (leftInteractionAlgebra P) component operator) := by
  let right := rightInteractionCoefficientOnIsotypicComponent P Q hselfAdjoint hcommute
    component c c'
  change
    (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
      component c c').comp (isotypicLeftAction (leftInteractionAlgebra P) component operator) =
    (isotypicLeftAction (leftInteractionAlgebra P) component operator).comp
      (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
        component c c')
  apply LinearMap.ext
  intro vector
  change right (operator • vector) = operator • right vector
  exact right.map_smul operator vector

/--
The concrete BV03 tensor-block equation on one left-isotypic sector.  The same
unitary sends every displayed left coefficient to `L tensor 1` and every
displayed right coefficient to `1 tensor R`; the latter is obtained by the
commutant matrix factorization, rather than by a joint spectral decomposition.
-/
theorem overlap_projector_tensor_block_coefficient_factorization
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B)
    (n : Nat) (W : Submodule (leftInteractionAlgebra P) B)
    (hW : IsSimpleModule (leftInteractionAlgebra P) W)
    (e : component.1 ≃ₗ[leftInteractionAlgebra P] (Fin n → W)) :
    ∃ U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)),
      (∀ a a' : A,
        U.conjOperator
          (isotypicLeftAction (leftInteractionAlgebra P) component
            ⟨leftInteractionCoefficient P a a',
              leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩) =
          isotypicTensorLeftAction (leftInteractionAlgebra P) W n
            ⟨leftInteractionCoefficient P a a',
              leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩) ∧
      (∀ c c' : C, ∃ R : Semantics.Operator (EuclideanSpace Complex (Fin n)),
        U.conjOperator
          (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
            component c c') =
          TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex)) R) := by
  letI : IsSimpleModule (leftInteractionAlgebra P) W := hW
  rcases isotypic_tensor_unitary_intertwiner (leftInteractionAlgebra P) component n W e with
    ⟨U, hU⟩
  refine ⟨U, ?_, ?_⟩
  · intro a a'
    exact hU ⟨leftInteractionCoefficient P a a',
      leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩
  · intro c c'
    let right : Semantics.Operator (component.1.restrictScalars Complex) :=
      rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
        component c c'
    have hright : ∀ operator : leftInteractionAlgebra P,
        Commute right (isotypicLeftAction (leftInteractionAlgebra P) component operator) := by
      intro operator
      simpa [right] using
        (rightInteractionCoefficientOnIsotypicComponentOperator_commutes_leftAction
          P Q hselfAdjoint hcommute component c c' operator)
    have htransport : ∀ operator : leftInteractionAlgebra P,
        Commute (U.conjOperator right)
          (isotypicTensorLeftAction (leftInteractionAlgebra P) W n operator) := by
      intro operator
      change
        (U.conjOperator right).comp
            (isotypicTensorLeftAction (leftInteractionAlgebra P) W n operator) =
          (isotypicTensorLeftAction (leftInteractionAlgebra P) W n operator).comp
            (U.conjOperator right)
      rw [← hU operator]
      calc
        (U.conjOperator right).comp
            (U.conjOperator (isotypicLeftAction (leftInteractionAlgebra P) component operator)) =
            U.conjOperator (right.comp
              (isotypicLeftAction (leftInteractionAlgebra P) component operator)) :=
          (Semantics.UnitaryTransport.conjOperator_comp U right
            (isotypicLeftAction (leftInteractionAlgebra P) component operator)).symm
        _ = U.conjOperator ((isotypicLeftAction (leftInteractionAlgebra P) component operator).comp
              right) := by
          exact congrArg U.conjOperator (hright operator).eq
        _ = (U.conjOperator (isotypicLeftAction (leftInteractionAlgebra P) component operator)).comp
              (U.conjOperator right) :=
          Semantics.UnitaryTransport.conjOperator_comp U
            (isotypicLeftAction (leftInteractionAlgebra P) component operator) right
    rcases isotypicTensor_commutant_matrix_factorization (leftInteractionAlgebra P) W n
      (U.conjOperator right) htransport with ⟨matrix, hmatrix⟩
    exact ⟨isotypicMultiplicityMatrixOperator n matrix, hmatrix⟩

/--
Lift the common isotypic unitary to the ambient multiplicity universe while
preserving both coefficient-side BV03 tensor actions.
-/
theorem overlap_projector_tensor_block_lifted_coefficient_factorization
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B)
    (n : Nat) (W : Submodule (leftInteractionAlgebra P) B)
    (hW : IsSimpleModule (leftInteractionAlgebra P) W)
    (e : component.1 ≃ₗ[leftInteractionAlgebra P] (Fin n → W)) :
    ∃ U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (W.restrictScalars Complex ⊗[Complex] isotypicLiftedMultiplicity.{u} n),
      (∀ a a' : A,
        U.conjOperator
          (isotypicLeftAction (leftInteractionAlgebra P) component
            ⟨leftInteractionCoefficient P a a',
              leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩) =
          TensorProduct.map
            (isotypicLeftActionOnSimple (leftInteractionAlgebra P) W
              ⟨leftInteractionCoefficient P a a',
                leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩)
            (1 : Semantics.Operator (isotypicLiftedMultiplicity.{u} n))) ∧
      (∀ c c' : C, ∃ R : Semantics.Operator (isotypicLiftedMultiplicity.{u} n),
        U.conjOperator
          (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
            component c c') =
          TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex)) R) := by
  letI : IsSimpleModule (leftInteractionAlgebra P) W := hW
  rcases overlap_projector_tensor_block_coefficient_factorization P Q hselfAdjoint hcommute
    component n W hW e with ⟨U0, hleft, hright⟩
  let V := isotypicMultiplicityLiftTensorUnitary (W.restrictScalars Complex) n
  let U := composeUnitaryTransport U0 V
  refine ⟨U, ?_, ?_⟩
  · intro a a'
    let coefficient : leftInteractionAlgebra P :=
      ⟨leftInteractionCoefficient P a a',
        leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩
    calc
      U.conjOperator
          (isotypicLeftAction (leftInteractionAlgebra P) component coefficient) =
          V.conjOperator
            (U0.conjOperator
              (isotypicLeftAction (leftInteractionAlgebra P) component coefficient)) := by
            exact composeUnitaryTransport_conjOperator U0 V
              (isotypicLeftAction (leftInteractionAlgebra P) component coefficient)
      _ = V.conjOperator
          (isotypicTensorLeftAction (leftInteractionAlgebra P) W n coefficient) := by
            rw [hleft a a']
      _ = TensorProduct.map
          (isotypicLeftActionOnSimple (leftInteractionAlgebra P) W coefficient)
          (1 : Semantics.Operator (isotypicLiftedMultiplicity.{u} n)) := by
            dsimp [V]
            simpa [isotypicTensorLeftAction] using
              (isotypicMultiplicityLiftTensorUnitary_conj_tensorMap_left
                (W.restrictScalars Complex) n
                (isotypicLeftActionOnSimple (leftInteractionAlgebra P) W coefficient))
  · intro c c'
    rcases hright c c' with ⟨R, hR⟩
    refine ⟨isotypicMultiplicityLiftConjOperator.{u} n R, ?_⟩
    calc
      U.conjOperator
          (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
            component c c') =
          V.conjOperator
            (U0.conjOperator
              (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
                component c c')) := by
            exact composeUnitaryTransport_conjOperator U0 V
              (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
                component c c')
      _ = V.conjOperator
          (TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex)) R) := by
            rw [hR]
      _ = TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex))
          (isotypicMultiplicityLiftConjOperator.{u} n R) := by
            dsimp [V]
            exact isotypicMultiplicityLiftTensorUnitary_conj_tensorMap_right
              (W.restrictScalars Complex) n R

/-- Reconstruct the left projector block from a fixed lifted coefficient transport. -/
theorem overlap_projector_leftBlock_of_lifted_coefficient_factorization
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (component : isotypicComponents (leftInteractionAlgebra P) B)
    (n : Nat) [NeZero n] (W : Submodule (leftInteractionAlgebra P) B)
    (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (W.restrictScalars Complex ⊗[Complex] isotypicLiftedMultiplicity.{u} n))
    (hleft : ∀ a a' : A,
      U.conjOperator
          (isotypicLeftAction (leftInteractionAlgebra P) component
            ⟨leftInteractionCoefficient P a a',
              leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩) =
        TensorProduct.map
          (isotypicLeftActionOnSimple (leftInteractionAlgebra P) W
            ⟨leftInteractionCoefficient P a a',
              leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩)
          (1 : Semantics.Operator (isotypicLiftedMultiplicity.{u} n))) :
    ∃ Pleft : Semantics.Operator (Semantics.CompositeSystem A (W.restrictScalars Complex)),
      (unitaryLTensor A U).conjOperator
          (overlapProjectorOnIsotypicComponent P component) =
        rightTensorExtensionAfterLeft A (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{u} n) Pleft := by
  let etaN := isotypicLiftedMultiplicityUnitVector.{u} n
  have hetaN : ‖etaN‖ = 1 := norm_isotypicLiftedMultiplicityUnitVector.{u} n
  have hcoefficients : ∀ a a' : A,
      ∃ R : Semantics.Operator (W.restrictScalars Complex),
        leftInteractionCoefficient
            ((unitaryLTensor A U).conjOperator
              (overlapProjectorOnIsotypicComponent P component)) a a' =
          TensorProduct.map R
            (1 : Semantics.Operator (isotypicLiftedMultiplicity.{u} n)) := by
    intro a a'
    let coefficient : leftInteractionAlgebra P :=
      ⟨leftInteractionCoefficient P a a',
        leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩
    refine ⟨isotypicLeftActionOnSimple (leftInteractionAlgebra P) W coefficient, ?_⟩
    calc
      leftInteractionCoefficient
          ((unitaryLTensor A U).conjOperator
            (overlapProjectorOnIsotypicComponent P component)) a a' =
          U.conjOperator
            (leftInteractionCoefficient
              (overlapProjectorOnIsotypicComponent P component) a a') :=
        leftInteractionCoefficient_unitaryLTensor_conjOperator U
          (overlapProjectorOnIsotypicComponent P component) a a'
      _ = U.conjOperator
          (isotypicLeftAction (leftInteractionAlgebra P) component coefficient) := by
            exact congrArg U.conjOperator
              (leftInteractionCoefficient_overlapProjectorOnIsotypicComponent P component a a')
      _ = TensorProduct.map
          (isotypicLeftActionOnSimple (leftInteractionAlgebra P) W coefficient)
          (1 : Semantics.Operator (isotypicLiftedMultiplicity.{u} n)) := hleft a a'
  exact exists_rightTensorExtensionAfterLeft_of_leftInteractionCoefficients_tensor
    A (W.restrictScalars Complex) (isotypicLiftedMultiplicity.{u} n)
    ((unitaryLTensor A U).conjOperator
      (overlapProjectorOnIsotypicComponent P component)) etaN hetaN hcoefficients

/-- Reconstruct the right projector block from the same lifted coefficient transport. -/
theorem overlap_projector_rightBlock_of_lifted_coefficient_factorization
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B)
    (n : Nat) [NeZero n] (W : Submodule (leftInteractionAlgebra P) B)
    (hW : IsSimpleModule (leftInteractionAlgebra P) W)
    (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (W.restrictScalars Complex ⊗[Complex] isotypicLiftedMultiplicity.{u} n))
    (hright : ∀ c c' : C, ∃ R : Semantics.Operator (isotypicLiftedMultiplicity.{u} n),
      U.conjOperator
          (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
            component c c') =
        TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex)) R) :
    ∃ Qright : Semantics.Operator
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{u} n) C),
      (unitaryRTensor U C).conjOperator
          (overlapRightProjectorOnIsotypicComponent P Q component) =
        leftTensorExtensionBeforeRight (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{u} n) C Qright := by
  letI : IsSimpleModule (leftInteractionAlgebra P) W := hW
  letI : Nontrivial (W.restrictScalars Complex) :=
    IsSimpleModule.nontrivial (leftInteractionAlgebra P) W
  rcases exists_normalized_vector_of_nontrivial
    (H := W.restrictScalars Complex) with ⟨etaW, hetaW⟩
  have hcoefficients : ∀ c c' : C,
      ∃ R : Semantics.Operator (isotypicLiftedMultiplicity.{u} n),
        rightInteractionCoefficient
            ((unitaryRTensor U C).conjOperator
              (overlapRightProjectorOnIsotypicComponent P Q component)) c c' =
          TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex)) R := by
    intro c c'
    rcases hright c c' with ⟨R, hR⟩
    refine ⟨R, ?_⟩
    calc
      rightInteractionCoefficient
          ((unitaryRTensor U C).conjOperator
            (overlapRightProjectorOnIsotypicComponent P Q component)) c c' =
          U.conjOperator
            (rightInteractionCoefficient
              (overlapRightProjectorOnIsotypicComponent P Q component) c c') :=
        rightInteractionCoefficient_unitaryRTensor_conjOperator U
          (overlapRightProjectorOnIsotypicComponent P Q component) c c'
      _ = U.conjOperator
          (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
            component c c') := by
            exact congrArg U.conjOperator
              (rightInteractionCoefficient_overlapRightProjectorOnIsotypicComponent
                P Q hselfAdjoint hcommute component c c')
      _ = TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex)) R := hR
  exact exists_leftTensorExtensionBeforeRight_of_rightInteractionCoefficients_tensor
    (W.restrictScalars Complex) (isotypicLiftedMultiplicity.{u} n) C
    ((unitaryRTensor U C).conjOperator
      (overlapRightProjectorOnIsotypicComponent P Q component)) etaW hetaW hcoefficients

/--
The concrete BV03 tensor-block equality on one left-isotypic sector.  The
same boundary unitary sends the compressed left overlap projector to
`P_left tensor 1` and the compressed right overlap projector to
`1 tensor Q_right`, with the displayed source parenthesizations retained.
-/
theorem overlap_projector_tensor_blocks_single_sector
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B)
    (n : Nat) [NeZero n] (W : Submodule (leftInteractionAlgebra P) B)
    (hW : IsSimpleModule (leftInteractionAlgebra P) W)
    (e : component.1 ≃ₗ[leftInteractionAlgebra P] (Fin n → W)) :
    ∃ (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
        (W.restrictScalars Complex ⊗[Complex] isotypicLiftedMultiplicity.{u} n))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem A (W.restrictScalars Complex)))
      (Qright : Semantics.Operator
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{u} n) C)),
      (unitaryLTensor A U).conjOperator
        (overlapProjectorOnIsotypicComponent P component) =
        rightTensorExtensionAfterLeft A (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{u} n) Pleft ∧
      (unitaryRTensor U C).conjOperator
        (overlapRightProjectorOnIsotypicComponent P Q component) =
        leftTensorExtensionBeforeRight (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{u} n) C Qright := by
  letI : IsSimpleModule (leftInteractionAlgebra P) W := hW
  rcases overlap_projector_tensor_block_lifted_coefficient_factorization
    P Q hselfAdjoint hcommute component n W hW e with ⟨U, hleft, hright⟩
  rcases overlap_projector_leftBlock_of_lifted_coefficient_factorization
    P component n W U hleft with ⟨Pleft, hPleft⟩
  rcases overlap_projector_rightBlock_of_lifted_coefficient_factorization
    P Q hselfAdjoint hcommute component n W hW U hright with ⟨Qright, hQright⟩
  exact ⟨U, Pleft, Qright, hPleft, hQright⟩

/--
The exact BV03 tensor-block conclusion for one isotypic sector.  This keeps the
two transported projector equalities bundled as a proposition so physical-cut
theorems can consume the generic block result without expanding the finite
Hilbert-space instance search at every lattice specialization.
-/
def OverlapProjectorTensorBlockFactorization
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (component : isotypicComponents (leftInteractionAlgebra P) B) : Prop :=
  ∃ (n : Nat) (hn : NeZero n) (W : Submodule (leftInteractionAlgebra P) B)
    (hW : IsSimpleModule (leftInteractionAlgebra P) W)
    (e : component.1 ≃ₗ[leftInteractionAlgebra P] (Fin n → W)),
    letI : NeZero n := hn
    ∃ (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
        (W.restrictScalars Complex ⊗[Complex] isotypicLiftedMultiplicity.{u} n))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem A (W.restrictScalars Complex)))
      (Qright : Semantics.Operator
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{u} n) C)),
      (unitaryLTensor A U).conjOperator
        (overlapProjectorOnIsotypicComponent P component) =
        rightTensorExtensionAfterLeft A (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{u} n) Pleft ∧
      (unitaryRTensor U C).conjOperator
        (overlapRightProjectorOnIsotypicComponent P Q component) =
        leftTensorExtensionBeforeRight (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{u} n) C Qright

/--
The finite-dimensional BV03 overlap decomposition in its concrete
interaction-algebra form.  The first conjunct is the direct sum of
left-isotypic boundary sectors.  In every sector an actual simple factor
`W` and a finite multiplicity coordinate are exhibited.  The two displayed
actions are the coefficient-level tensor-block equations: every left
coefficient acts only on `W`, while every right coefficient acts only by a
scalar matrix on the multiplicity coordinate.  These separate equations are
the input for reconstructing the two overlapping projectors blockwise; they
are stronger than a joint spectral decomposition of global projectors.
-/
theorem commuting_overlap_block_factorization
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q)) :
    DirectSum.IsInternal (fun component : isotypicComponents (leftInteractionAlgebra P) B =>
      component.1) ∧
      ∀ component : isotypicComponents (leftInteractionAlgebra P) B,
        ∃ (n : Nat) (_ : NeZero n) (W : Submodule (leftInteractionAlgebra P) B)
          (hW : IsSimpleModule (leftInteractionAlgebra P) W)
          (e : component.1 ≃ₗ[leftInteractionAlgebra P] (Fin n → W)),
          (∀ a a' : A, ∀ (vector : component.1) (row : Fin n),
            e ((⟨leftInteractionCoefficient P a a',
              leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩ :
                leftInteractionAlgebra P) • vector) row =
              (⟨leftInteractionCoefficient P a a',
                leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩ :
                  leftInteractionAlgebra P) • e vector row) ∧
          (∀ c c' : C, ∃ matrix : Matrix (Fin n) (Fin n) Complex,
            ∀ (vector : component.1) (row : Fin n),
              e (rightInteractionCoefficientOnIsotypicComponent P Q hselfAdjoint hcommute
                component c c' vector) row =
                ∑ column, matrix row column • e vector column) := by
  letI : IsSemisimpleModule (leftInteractionAlgebra P) B :=
    starSubalgebra_module_isSemisimple (leftInteractionAlgebra P)
  constructor
  · exact starSubalgebra_isotypicComponents_isInternal (leftInteractionAlgebra P)
  · intro component
    letI complexModule : Module Complex component.1 :=
      starSubalgebraSubmoduleComplexModule (leftInteractionAlgebra P) component.1
    letI scalarTower : IsScalarTower Complex (leftInteractionAlgebra P) component.1 := by
      constructor
      intro scalar operator vector
      change ((algebraMap Complex (leftInteractionAlgebra P) scalar) * operator) • vector =
        (algebraMap Complex (leftInteractionAlgebra P) scalar) • (operator • vector)
      exact mul_smul _ _ _
    letI finiteDimensional : FiniteDimensional Complex component.1 :=
      FiniteDimensional.of_injective
        (starSubalgebraSubmoduleComplexInclusion (leftInteractionAlgebra P) component.1)
        Subtype.coe_injective
    letI finiteModule : Module.Finite (leftInteractionAlgebra P) component.1 :=
      @Module.Finite.of_restrictScalars_finite Complex (leftInteractionAlgebra P) component.1
        (inferInstance : Semiring Complex)
        (inferInstance : Semiring (leftInteractionAlgebra P))
        (inferInstance : AddCommMonoid component.1)
        complexModule (inferInstance : Module (leftInteractionAlgebra P) component.1)
        (inferInstance : SMul Complex (leftInteractionAlgebra P)) scalarTower
        (inferInstance : Module.Finite Complex component.1)
    obtain ⟨n, hn, W, _hWle, hW, he⟩ :=
      (IsIsotypic.isotypicComponents component.2).submodule_linearEquiv_fun
    rcases he with ⟨e⟩
    refine ⟨n, hn, W, hW, e, ?_, ?_⟩
    · intro a a' vector row
      rw [e.map_smul]
      rfl
    · intro c c'
      let right := rightInteractionCoefficientOnIsotypicComponent P Q hselfAdjoint hcommute
        component c c'
      let T : Module.End (leftInteractionAlgebra P) (Fin n → W) :=
        e.toLinearMap.comp (right.comp e.symm.toLinearMap)
      letI : IsSimpleModule (leftInteractionAlgebra P) W := hW
      obtain ⟨matrix, hmatrix⟩ :=
        isotypic_commutant_matrix_factorization (leftInteractionAlgebra P) W n T
      refine ⟨matrix, ?_⟩
      intro vector row
      have htransport : e (right vector) = T (e vector) := by
        simp [T, right]
      calc
        e (right vector) row = T (e vector) row := by rw [htransport]
        _ = ∑ column, matrix row column • e vector column := hmatrix (e vector) row

/--
Specialize the finite BV03 decomposition to one chosen isotypic sector and
reconstruct its two actual transported projector blocks.  Both physical BPT
cuts use this corollary immediately, avoiding duplicated high-cost elaboration
of the same polar/intertwiner reconstruction.
-/
theorem overlapProjectorTensorBlockFactorization_of_commuting
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    OverlapProjectorTensorBlockFactorization P Q component := by
  rcases commuting_overlap_block_factorization P Q hselfAdjoint hcommute with ⟨_, hblocks⟩
  rcases hblocks component with ⟨n, hn, W, hW, e, _, _⟩
  letI : NeZero n := hn
  rcases overlap_projector_tensor_blocks_single_sector
    P Q hselfAdjoint hcommute component n W hW e with ⟨U, Pleft, Qright, hleft, hright⟩
  exact ⟨n, hn, W, hW, e, U, Pleft, Qright, hleft, hright⟩

/--
The direct-sum/isotypic part of the BV03 decomposition together with the
unitary tensor-factor coefficient equations on every summand.  Unlike a joint
spectral decomposition, each summand has one common transport carrying the
left interaction algebra to the first tensor factor and the commuting right
interaction algebra to the second.
-/
theorem commuting_overlap_tensor_block_coefficient_factorization
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q)) :
    DirectSum.IsInternal (fun component : isotypicComponents (leftInteractionAlgebra P) B =>
      component.1) ∧
      ∀ component : isotypicComponents (leftInteractionAlgebra P) B,
        ∃ (n : Nat) (_ : NeZero n) (W : Submodule (leftInteractionAlgebra P) B)
          (hW : IsSimpleModule (leftInteractionAlgebra P) W)
          (e : component.1 ≃ₗ[leftInteractionAlgebra P] (Fin n → W))
          (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
            (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n))),
          (∀ a a' : A,
            U.conjOperator
              (isotypicLeftAction (leftInteractionAlgebra P) component
                ⟨leftInteractionCoefficient P a a',
                  leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩) =
              isotypicTensorLeftAction (leftInteractionAlgebra P) W n
                ⟨leftInteractionCoefficient P a a',
                  leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩) ∧
          (∀ c c' : C, ∃ R : Semantics.Operator (EuclideanSpace Complex (Fin n)),
            U.conjOperator
              (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
                component c c') =
              TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex)) R) := by
  rcases commuting_overlap_block_factorization P Q hselfAdjoint hcommute with
    ⟨hInternal, hblocks⟩
  refine ⟨hInternal, ?_⟩
  intro component
  rcases hblocks component with ⟨n, hn, W, hW, e, _, _⟩
  rcases overlap_projector_tensor_block_coefficient_factorization P Q hselfAdjoint hcommute
    component n W hW e with ⟨U, hleft, hright⟩
  exact ⟨n, hn, W, hW, e, U, hleft, hright⟩

/--
The local orthogonal projector onto one left-interaction isotypic sector of an
overlap system.  Unlike a joint eigenspace projector, this is defined from the
interaction algebra of the left projector and is therefore the central sector
measurement in the BV03 decomposition.
-/
noncomputable def leftIsotypicSectorProjector
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    Semantics.Operator B := by
  letI : IsScalarTower Complex (leftInteractionAlgebra P) B := by
    constructor
    intro scalar operator vector
    change ((scalar • (operator : Semantics.Operator B)) : Semantics.Operator B) vector =
      scalar • (operator : Semantics.Operator B) vector
    simp
  exact (component.1.restrictScalars Complex).starProjection.toLinearMap

/-- Each left-isotypic sector operator is an orthogonal projector. -/
theorem leftIsotypicSectorProjector_isSymmetricProjection
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    (leftIsotypicSectorProjector P component).IsSymmetricProjection := by
  letI : IsScalarTower Complex (leftInteractionAlgebra P) B := by
    constructor
    intro scalar operator vector
    change ((scalar • (operator : Semantics.Operator B)) : Semantics.Operator B) vector =
      scalar • (operator : Semantics.Operator B) vector
    simp
  exact Submodule.isSymmetricProjection_starProjection _

/-- A vector in an isotypic component is fixed by its local sector projector. -/
theorem leftIsotypicSectorProjector_apply_eq_self_of_mem
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (component : isotypicComponents (leftInteractionAlgebra P) B)
    {vector : B} (hvector : vector ∈ component.1) :
    leftIsotypicSectorProjector P component vector = vector := by
  letI : IsScalarTower Complex (leftInteractionAlgebra P) B := by
    constructor
    intro scalar operator vector
    change ((scalar • (operator : Semantics.Operator B)) : Semantics.Operator B) vector =
      scalar • (operator : Semantics.Operator B) vector
    simp
  exact Submodule.starProjection_eq_self_iff.mpr hvector

/-- A left-interaction sector commutes with every displayed left coefficient. -/
theorem leftIsotypicSectorProjector_commute_leftInteractionCoefficient
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (component : isotypicComponents (leftInteractionAlgebra P) B) (a a' : A) :
    Commute (leftIsotypicSectorProjector P component)
      (leftInteractionCoefficient P a a') := by
  letI : IsScalarTower Complex (leftInteractionAlgebra P) B := by
    constructor
    intro scalar operator vector
    change ((scalar • (operator : Semantics.Operator B)) : Semantics.Operator B) vector =
      scalar • (operator : Semantics.Operator B) vector
    simp
  simpa [leftIsotypicSectorProjector] using
    (starProjection_commute_starSubalgebraSubmodule (leftInteractionAlgebra P) component.1
      ⟨leftInteractionCoefficient P a a',
        leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩)

/--
A left-interaction sector also commutes with every displayed right coefficient
of a commuting overlap projector.  This is what promotes the isotypic label to
a locally measurable code sector rather than an abstract module summand.
-/
theorem leftIsotypicSectorProjector_commute_rightInteractionCoefficient
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B) (c c' : C) :
    Commute (leftIsotypicSectorProjector P component)
      (rightInteractionCoefficient Q c c') := by
  letI : IsScalarTower Complex (leftInteractionAlgebra P) B := by
    constructor
    intro scalar operator vector
    change ((scalar • (operator : Semantics.Operator B)) : Semantics.Operator B) vector =
      scalar • (operator : Semantics.Operator B) vector
    simp
  simpa [leftIsotypicSectorProjector] using
    (starProjection_commute_of_fullyInvariant_of_commutingStarSubalgebras
      (leftInteractionAlgebra P) (rightInteractionAlgebra Q) component.1
      (Submodule.IsFullyInvariant.of_mem_isotypicComponents component.2)
      (fun left right => interactionAlgebras_commute P Q hselfAdjoint hcommute
        left.property right.property)
      ⟨rightInteractionCoefficient Q c c',
        rightInteractionCoefficient_mem_rightInteractionAlgebra Q c c'⟩)

/--
The physical lift of an isotypic sector commutes with both projectors of a
commuting overlap.  This is the exact local-sector statement consumed by the
correctability argument: measuring the sector label is an operation on the
overlap alone and preserves the whole commuting-projector code.
-/
theorem leftIsotypicSectorProjector_commutes_overlap
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    Commute P (TensorProduct.map (1 : Semantics.Operator A)
      (leftIsotypicSectorProjector P component)) ∧
    Commute Q (TensorProduct.map (leftIsotypicSectorProjector P component)
      (1 : Semantics.Operator C)) := by
  constructor
  · apply commute_leftOverlap_of_commute_leftInteractionCoefficients
    intro a a'
    exact leftIsotypicSectorProjector_commute_leftInteractionCoefficient
      P component a a'
  · apply commute_rightOverlap_of_commute_rightInteractionCoefficients
    intro c c'
    exact leftIsotypicSectorProjector_commute_rightInteractionCoefficient
      P Q hselfAdjoint hcommute component c c'

/--
Finite sector-collapse for the interaction-algebra decomposition.  If every
local sector is either absent from a nonzero projector or contains its entire
range, then exactly one isotypic sector is active.  The two hypotheses are
supplied later by external-boundary no-information and the proved local
commutation of `leftIsotypicSectorProjector`.
-/
theorem exists_unique_active_leftIsotypicSector
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B)) (F : Semantics.Operator B)
    (hF : F ≠ 0)
    (hcommute : ∀ component : isotypicComponents (leftInteractionAlgebra P) B,
      Commute F (leftIsotypicSectorProjector P component))
    (hsector : ∀ component : isotypicComponents (leftInteractionAlgebra P) B,
      F * leftIsotypicSectorProjector P component = 0 ∨
        F * leftIsotypicSectorProjector P component = F) :
    ∃ component : isotypicComponents (leftInteractionAlgebra P) B,
      F * leftIsotypicSectorProjector P component = F ∧
        ∀ other : isotypicComponents (leftInteractionAlgebra P) B, other ≠ component →
          F * leftIsotypicSectorProjector P other = 0 := by
  classical
  letI : IsSemisimpleModule (leftInteractionAlgebra P) B :=
    starSubalgebra_module_isSemisimple (leftInteractionAlgebra P)
  have hsome : ∃ component : isotypicComponents (leftInteractionAlgebra P) B,
      F * leftIsotypicSectorProjector P component = F := by
    by_contra hnone
    push_neg at hnone
    have hzero : ∀ component : isotypicComponents (leftInteractionAlgebra P) B,
        F * leftIsotypicSectorProjector P component = 0 := by
      intro component
      exact (hsector component).resolve_right (hnone component)
    apply hF
    apply LinearMap.ext
    intro vector
    change F vector = (0 : B)
    have htop : (⨆ component : isotypicComponents (leftInteractionAlgebra P) B,
        component.1) = ⊤ :=
      (sSup_eq_iSup' _).symm.trans
        (sSup_isotypicComponents (leftInteractionAlgebra P) B)
    have hvector : vector ∈ ⨆ component : isotypicComponents (leftInteractionAlgebra P) B,
        component.1 := by
      rw [htop]
      trivial
    refine Submodule.iSup_induction (fun component :
      isotypicComponents (leftInteractionAlgebra P) B => component.1)
      (motive := fun x : B => F x = 0) hvector ?_ ?_ ?_
    · intro component member hmember
      have hfixed := leftIsotypicSectorProjector_apply_eq_self_of_mem P component hmember
      change F member = (0 : B)
      calc
        F member = F (leftIsotypicSectorProjector P component member) := by rw [hfixed]
        _ = (F * leftIsotypicSectorProjector P component) member := rfl
        _ = (0 : B) := by rw [hzero component]; rfl
    · exact F.map_zero
    · intro left right hleft hright
      simpa [map_add, hleft, hright]
  rcases hsome with ⟨component, hcomponent⟩
  refine ⟨component, hcomponent, ?_⟩
  intro other hother
  rcases hsector other with hzero | hactive
  · exact hzero
  · exfalso
    apply hF
    apply LinearMap.ext
    intro vector
    have hcomponentFixed :
        leftIsotypicSectorProjector P component (F vector) = F vector := by
      calc
        leftIsotypicSectorProjector P component (F vector) =
            F (leftIsotypicSectorProjector P component vector) := by
              exact congrArg (fun operator => operator vector) (hcommute component).eq.symm
        _ = F vector := congrArg (fun operator => operator vector) hcomponent
    have hotherFixed : leftIsotypicSectorProjector P other (F vector) = F vector := by
      calc
        leftIsotypicSectorProjector P other (F vector) =
            F (leftIsotypicSectorProjector P other vector) := by
              exact congrArg (fun operator => operator vector) (hcommute other).eq.symm
        _ = F vector := congrArg (fun operator => operator vector) hactive
    have hcomponentMem : F vector ∈ component.1 := by
      exact Submodule.starProjection_eq_self_iff.mp hcomponentFixed
    have hotherMem : F vector ∈ other.1 := by
      exact Submodule.starProjection_eq_self_iff.mp hotherFixed
    have hdisjoint : Disjoint component.1 other.1 :=
      (sSupIndep_isotypicComponents (leftInteractionAlgebra P) B).pairwiseDisjoint
        component.2 other.2 (by
          intro heq
          apply hother
          exact Subtype.ext heq.symm)
    simpa using hdisjoint.le_bot ⟨hcomponentMem, hotherMem⟩

/--
If every ambient operator has scalar compression to a finite-dimensional code,
then that code has dimension at most one.  Mathematically, a rank-one probe
onto either member of a hypothetical independent pair would make the other
member a scalar multiple of it.  This is the rank-one engine used for the
source's `Pi_AB'` conclusion and, after both residual erasures are transported,
for the `Theta_{B''C'}` no-cloning conclusion (source lines 643-657).
-/
theorem finrank_carrier_le_one_of_all_scalar_compression
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (C : Semantics.QuantumCode H)
    (hscalar : ∀ A : Semantics.Operator H, ∃ scalar : Complex,
      C.projector * A * C.projector = scalar • C.projector) :
    Module.finrank Complex C.carrier ≤ 1 := by
  by_contra hle
  have hdim : 1 < Module.finrank Complex C.carrier := Nat.lt_of_not_ge hle
  have hpositive : 0 < Module.finrank Complex C.carrier := by omega
  rcases Module.finrank_pos_iff_exists_ne_zero.mp hpositive with ⟨x, hx⟩
  rcases exists_linearIndependent_pair_of_one_lt_finrank hdim hx with ⟨y, hxy⟩
  let A : Semantics.Operator H :=
    (InnerProductSpace.rankOne Complex (x : H) (x : H)).toLinearMap
  rcases hscalar A with ⟨scalar, hscalarA⟩
  have hpx : C.projector (x : H) = x := C.projector_eq_self_of_mem x.property
  have hpy : C.projector (y : H) = y := C.projector_eq_self_of_mem y.property
  have hxambient : (x : H) ≠ 0 := by
    intro hzero
    exact hx (Subtype.ext hzero)
  have hleftx : (C.projector * A * C.projector) (x : H) =
      (inner Complex (x : H) (x : H)) • (x : H) := by
    change C.projector (A (C.projector (x : H))) = _
    rw [hpx]
    simp [A, InnerProductSpace.rankOne_apply, hpx]
  have hrightx : (scalar • C.projector) (x : H) = scalar • (x : H) := by
    rw [LinearMap.smul_apply, hpx]
  have hxEq : (inner Complex (x : H) (x : H)) • (x : H) = scalar • (x : H) := by
    calc
      (inner Complex (x : H) (x : H)) • (x : H) =
          (C.projector * A * C.projector) (x : H) := hleftx.symm
      _ = (scalar • C.projector) (x : H) := congrArg (fun operator => operator (x : H)) hscalarA
      _ = scalar • (x : H) := hrightx
  have hscalarEq : inner Complex (x : H) (x : H) = scalar :=
    smul_left_injective Complex hxambient hxEq
  have hlefty : (C.projector * A * C.projector) (y : H) =
      (inner Complex (x : H) (y : H)) • (x : H) := by
    change C.projector (A (C.projector (y : H))) = _
    rw [hpy]
    simp [A, InnerProductSpace.rankOne_apply, hpx]
  have hrighty : (scalar • C.projector) (y : H) = scalar • (y : H) := by
    rw [LinearMap.smul_apply, hpy]
  have hyEq : (inner Complex (x : H) (y : H)) • (x : H) = scalar • (y : H) := by
    calc
      (inner Complex (x : H) (y : H)) • (x : H) =
          (C.projector * A * C.projector) (y : H) := hlefty.symm
      _ = (scalar • C.projector) (y : H) := congrArg (fun operator => operator (y : H)) hscalarA
      _ = scalar • (y : H) := hrighty
  have hinner : inner Complex (x : H) (x : H) ≠ 0 := inner_self_ne_zero.mpr hxambient
  have hyDependent :
      ((inner Complex (x : H) (y : H) / inner Complex (x : H) (x : H)) • x : C.carrier) = y := by
    apply Subtype.ext
    change (inner Complex (x : H) (y : H) / inner Complex (x : H) (x : H)) • (x : H) = (y : H)
    calc
      (inner Complex (x : H) (y : H) / inner Complex (x : H) (x : H)) • (x : H) =
          (inner Complex (x : H) (x : H))⁻¹ •
            ((inner Complex (x : H) (y : H)) • (x : H)) := by
              rw [div_eq_mul_inv, mul_comm, smul_smul]
      _ = (inner Complex (x : H) (x : H))⁻¹ •
            ((inner Complex (x : H) (x : H)) • (y : H)) := by rw [hyEq, ← hscalarEq]
      _ = (y : H) := by rw [smul_smul, inv_mul_cancel₀ hinner, one_smul]
  exact ((LinearIndependent.pair_iff' hx).mp hxy _ hyDependent)

/--
Relabel finite-qudit computational labels along a coordinate equivalence that
preserves the local dimension at every coordinate.  The map is deliberately
defined on the labels rather than by a dimension count: later BPT coordinate
changes retain the underlying lattice site and only change the proof carried
by its subtype.
-/
def quditLabelRelabel
    {I J : Type u} [Fintype I] [Fintype J]
    {q : I → Nat} {r : J → Nat} (e : I ≃ J)
    (hdim : ∀ i, q i = r (e i)) :
    Semantics.Qudit.Label q ≃ Semantics.Qudit.Label r where
  toFun := fun labels j =>
    Fin.cast ((hdim (e.symm j)).trans (congrArg r (e.apply_symm_apply j)))
      (labels (e.symm j))
  invFun := fun labels i => Fin.cast (hdim i).symm (labels (e i))
  left_inv := by
    intro labels
    funext i
    apply Fin.ext
    change (labels (e.symm (e i))).val = (labels i).val
    rw [e.symm_apply_apply]
  right_inv := by
    intro labels
    funext j
    apply Fin.ext
    change (labels (e (e.symm j))).val = (labels j).val
    rw [e.apply_symm_apply]

/--
The basis-preserving unitary associated to `quditLabelRelabel`.  Its target
use is purely coordinate bookkeeping: local operators are transported between
the source boundary coordinate system and the virtual `B`, `C`, or `D`
factor without changing their physical action.
-/
noncomputable def quditCoordinateRelabel
    {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {q : I → Nat} {r : J → Nat} (e : I ≃ J)
    (hdim : ∀ i, q i = r (e i)) :
    Semantics.UnitaryTransport (Semantics.Qudit.QuditRegister q)
      (Semantics.Qudit.QuditRegister r) := by
  let sourceBasis := EuclideanSpace.basisFun (Semantics.Qudit.Label q) Complex
  let targetBasis := EuclideanSpace.basisFun (Semantics.Qudit.Label r) Complex
  let U := sourceBasis.equiv targetBasis (quditLabelRelabel e hdim)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

/-- The coordinate relabeling sends every computational basis vector to its relabeled one. -/
theorem quditCoordinateRelabel_apply_basis
    {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {q : I → Nat} {r : J → Nat} (e : I ≃ J)
    (hdim : ∀ i, q i = r (e i)) (labels : Semantics.Qudit.Label q) :
    quditCoordinateRelabel e hdim
        (EuclideanSpace.basisFun (Semantics.Qudit.Label q) Complex labels) =
      EuclideanSpace.basisFun (Semantics.Qudit.Label r) Complex
        (quditLabelRelabel e hdim labels) := by
  dsimp [quditCoordinateRelabel]
  rw [OrthonormalBasis.equiv_apply_basis]

/-- The pure-factor/complement-projector operator, recombined into the full register. -/
noncomputable def pureFactorTensorComplementProjector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (phi : (M.regionSubsystem region).selectedSystem)
    (complementProjector : Semantics.Operator (M.regionSubsystem region).complementSystem) :
    Semantics.Operator L.Register :=
  (M.regionSubsystem region).registerFactorization.symm.conjOperator
    (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap complementProjector)

/--
Recombine a selected-factor operator with a literal complement-factor operator
on a concrete register.  The statement is kept local because D5 needs the
exact endpoint expression rather than a support-only reformulation.
-/
theorem quditSubsystem_extendLocalToRegister_mul_complementOperator
    (S : Semantics.QuditSubsystem L.localDimension)
    (A : Semantics.Operator S.selectedSystem) (P : Semantics.Operator S.complementSystem) :
    S.extendLocalToRegister A *
        (S.registerFactorization.symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator S.selectedSystem) P)) =
      S.registerFactorization.symm.conjOperator (TensorProduct.map A P) := by
  change (S.extendLocalToRegister A).comp
      (S.registerFactorization.symm.conjOperator
        (TensorProduct.map (1 : Semantics.Operator S.selectedSystem) P)) = _
  unfold Semantics.QuditSubsystem.extendLocalToRegister Semantics.QuditSubsystem.extendLocal
  rw [← S.registerFactorization.symm.conjOperator_comp]
  rw [← TensorProduct.map_comp]
  rw [Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]

/--
The target pure-factor operator is literally a selected rank-one extension
times its true complement operator.  This is the final D5 endpoint shape.
-/
theorem pureFactorTensorComplementProjector_eq_rankOne_mul_complementExtension
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (phi : (M.regionSubsystem region).selectedSystem)
    (complementProjector : Semantics.Operator (M.regionSubsystem region).complementSystem) :
    M.pureFactorTensorComplementProjector region phi complementProjector =
      (M.regionSubsystem region).extendLocalToRegister
        (InnerProductSpace.rankOne Complex phi phi).toLinearMap *
      ((M.regionSubsystem region).registerFactorization.symm.conjOperator
        (TensorProduct.map
          (1 : Semantics.Operator (M.regionSubsystem region).selectedSystem)
          complementProjector)) := by
  symm
  exact quditSubsystem_extendLocalToRegister_mul_complementOperator
    (M.regionSubsystem region)
    (InnerProductSpace.rankOne Complex phi phi).toLinearMap complementProjector


end BPTCommutingProjectorModel

end Bounds
end QEC

/-
Lean 4.30's library-suggestions indexer scans theorem types while serializing.
The generated BPT tensor signatures take minutes and hit its fixed heartbeat
limit. Excluding this namespace affects only metadata, not kernel checking.
-/
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "BPTCommutingProjectorModel"
