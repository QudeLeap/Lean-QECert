import QEC.Coding.ExpanderCodes.LPSOriginalHolomorphicKaehlerRegularity

/-!
# LPSOriginalNativeDifferentialComparison

The genuine original algebraic differential H0 comparison with all analytic sections and cusp forms.
This is a derived internal proof step on the existing original curve. The analytic/cusp interpretation
follows the Milne references in `LPSOriginalHolomorphicDifferentialComparison`. This package does not
prove good reduction, Frobenius/Weil, LPS spectral estimates or the arbitrary-field PK22 code family.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
open CategoryTheory _root_.AlgebraicGeometry Opposite QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry MatrixGroups UpperHalfPlane ModularForm Modular
attribute [local instance] originalNativeGlobalComplexModule

/-- Constructed comparison of genuine original algebraic H0 with all analytic covectors. -/
def lpsOriginalNativeH0HolomorphicLinearEquiv :
    Γ(lpsOriginalComplexNormalDifferentialSheaf N hpos, ⊤) ≃ₗ[ℂ]
      LPSOriginalHolomorphicCovectorSections N hN :=
  (lpsOriginalNativeH0RegularCovectorLinearEquiv N hpos hN).trans
    (lpsOriginalHolomorphicRegularKaehlerLinearEquiv N hpos hN).symm

/-- Constructed original global differential / weight-two cusp-form comparison. -/
def lpsOriginalNativeH0CuspFormLinearEquiv :
    Γ(lpsOriginalComplexNormalDifferentialSheaf N hpos, ⊤) ≃ₗ[ℂ]
      CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact (lpsOriginalNativeH0HolomorphicLinearEquiv N hpos hN).trans
    (lpsOriginalFilledDifferentialLinearEquiv N hN).symm


end
end QEC.Coding.TannerLiftedProduct
