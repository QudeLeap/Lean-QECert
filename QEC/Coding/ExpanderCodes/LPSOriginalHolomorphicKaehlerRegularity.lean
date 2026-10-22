import QEC.Coding.ExpanderCodes.LPSOriginalHolomorphicNativeCovectors
import QEC.Coding.ExpanderCodes.LPSOriginalNativeHolomorphicExtension
import QEC.Coding.ExpanderCodes.LPSOriginalNativeH0

/-!
# LPSOriginalHolomorphicKaehlerRegularity

A proved complex-linear bijection from all analytic sections to the actual regular Kähler module.
This is a derived internal proof step on the existing original curve. The analytic/cusp interpretation
follows the Milne references in `LPSOriginalHolomorphicDifferentialComparison`. This package does not
prove good reduction, Frobenius/Weil, LPS spectral estimates or the arbitrary-field PK22 code family.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] LPSOriginalAffineKaehlerCompatibilityDictionary001
  LPSOriginalAffineKaehlerCompatibilityDictionary002
  LPSOriginalAffineKaehlerCompatibilityDictionary003
  LPSOriginalAffineKaehlerCompatibilityDictionary004
local notation "K" => lpsOriginalGeneratedFunctionField N hpos

/-- Transport every analytic section to the existing independently defined generic Kähler module. -/
def lpsOriginalHolomorphicToKaehlerLinearMap :
    LPSOriginalHolomorphicCovectorSections N hN →ₗ[ℂ] KaehlerDifferential ℂ K :=
  (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN).symm.toLinearMap.comp
    (lpsOriginalHolomorphicCovectorToClassLinearMap N hN)

/-- The transported Kähler differential has the original analytic section as its actual native class. -/
lemma lpsOriginalHolomorphicToKaehler_native
    (sigma : LPSOriginalHolomorphicCovectorSections N hN) :
    lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN
      (lpsOriginalHolomorphicToKaehlerLinearMap N hpos hN sigma) =
        lpsOriginalHolomorphicCovectorToClassLinearMap N hN sigma :=
  (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN).apply_symm_apply _

/-- All analytic sections have no poles and lie in the genuine two-affine-image regular submodule. -/
lemma lpsOriginalHolomorphicToKaehler_mem_regular
    (sigma : LPSOriginalHolomorphicCovectorSections N hN) :
    lpsOriginalHolomorphicToKaehlerLinearMap N hpos hN sigma ∈
      lpsOriginalNativeRegularKaehlerSubmodule N hpos := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  apply (lpsOriginalNativeRegularKaehlerSubmodule_mem_iff N hpos hN _).mpr
  intro x
  rw [lpsOriginalHolomorphicToKaehler_native]
  change 0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x)
    (lpsOriginalNativeCovectorToLocal N hN x
      (lpsOriginalCompactMeromorphicCovectorClass N hN
        (lpsOriginalHolomorphicCovectorToMeromorphicLinearMap N hN sigma)))
  rw [lpsOriginalNativeCovectorToLocal_class]
  change 0 ≤ meromorphicOrderAt (lpsOriginalHolomorphicCovectorChartCoefficient N hN sigma x)
    (chartAt ℂ x x)
  have ha := lpsOriginalHolomorphicCovectorChartCoefficient_analytic N hN sigma x
  exact ha.meromorphicAt.meromorphicOrderAt_nonneg_iff.mpr ⟨_, ha, Filter.EventuallyEq.rfl⟩

/-- The actual linear map from analytic sections to the independently defined regular submodule. -/
def lpsOriginalHolomorphicToRegularKaehlerLinearMap :
    LPSOriginalHolomorphicCovectorSections N hN →ₗ[ℂ]
      lpsOriginalNativeRegularKaehlerSubmodule N hpos :=
  (lpsOriginalHolomorphicToKaehlerLinearMap N hpos hN).codRestrict
    (lpsOriginalNativeRegularKaehlerSubmodule N hpos)
    (lpsOriginalHolomorphicToKaehler_mem_regular N hpos hN)

/-- The regular-submodule map is injective through actual native class uniqueness. -/
lemma lpsOriginalHolomorphicToRegularKaehler_injective :
    Function.Injective (lpsOriginalHolomorphicToRegularKaehlerLinearMap N hpos hN) := by
  intro sigma tau he
  have hk := congrArg Subtype.val he
  have hn := congrArg (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN) hk
  change lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN
      (lpsOriginalHolomorphicToKaehlerLinearMap N hpos hN sigma) =
      lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN
        (lpsOriginalHolomorphicToKaehlerLinearMap N hpos hN tau) at hn
  rw [lpsOriginalHolomorphicToKaehler_native, lpsOriginalHolomorphicToKaehler_native] at hn
  exact lpsOriginalHolomorphicCovectorToClass_injective N hN hn

/-- Repair any quotient representative of a regular Kähler differential to construct its analytic preimage. -/
lemma lpsOriginalHolomorphicToRegularKaehler_surjective :
    Function.Surjective (lpsOriginalHolomorphicToRegularKaehlerLinearMap N hpos hN) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let : AddCommGroup (LPSOriginalFilledMeromorphicCovectorRepresentatives N hN) :=
    (lpsOriginalFilledMeromorphicCovectorSubmodule N hN).addCommGroup
  intro omega
  let c := lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega.val
  obtain ⟨sigma, hsigma⟩ :=
    (lpsOriginalFilledMeromorphicCovectorZeroSubmodule N hN).mkQ_surjective c
  have hs : lpsOriginalCompactMeromorphicCovectorClass N hN sigma = c := hsigma
  have ho : ∀ x : LPSOriginalFilledCurve N,
      0 ≤ meromorphicOrderAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma.val x)
        (chartAt ℂ x x) := by
    intro x
    have hn := (lpsOriginalNativeRegularKaehlerSubmodule_mem_iff N hpos hN omega.val).mp
      omega.property x
    change 0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x)
      (lpsOriginalNativeCovectorToLocal N hN x c) at hn
    rw [← hs, lpsOriginalNativeCovectorToLocal_class] at hn
    exact hn
  let h : LPSOriginalHolomorphicCovectorSections N hN :=
    ⟨lpsOriginalNormalizedFilledCovector N hN sigma.val,
      lpsOriginalNormalizedFilledCovector_contMDiff N hN sigma.val sigma.property ho⟩
  have hh : lpsOriginalHolomorphicCovectorToClassLinearMap N hN h = c :=
    (lpsOriginalNormalizedMeromorphicCovector_class N hN sigma).symm.trans hs
  refine ⟨h, Subtype.ext ?_⟩
  apply (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN).injective
  change lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN
    (lpsOriginalHolomorphicToKaehlerLinearMap N hpos hN h) =
      lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega.val
  rw [lpsOriginalHolomorphicToKaehler_native]
  exact hh

/-- The proved linear bijection between all analytic sections and the actual regular Kähler submodule. -/
def lpsOriginalHolomorphicRegularKaehlerLinearEquiv :
    LPSOriginalHolomorphicCovectorSections N hN ≃ₗ[ℂ]
      lpsOriginalNativeRegularKaehlerSubmodule N hpos :=
  LinearEquiv.ofBijective (lpsOriginalHolomorphicToRegularKaehlerLinearMap N hpos hN)
    ⟨lpsOriginalHolomorphicToRegularKaehler_injective N hpos hN,
      lpsOriginalHolomorphicToRegularKaehler_surjective N hpos hN⟩

end
end QEC.Coding.TannerLiftedProduct
