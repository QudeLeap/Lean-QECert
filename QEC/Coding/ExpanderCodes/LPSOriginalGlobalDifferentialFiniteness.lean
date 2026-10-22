import QEC.Coding.ExpanderCodes.LPSOriginalRegularDifferentialFiniteness

/-!
# LPSOriginalGlobalDifferentialFiniteness

Constructed finite-dimensionality closure for genuine original differential spaces.
Derived internal support for parent #449 and pinned PK22 ex:Xpq, main.tex484–486,
with the original-curve/Milne interpretation in LPSOriginalHolomorphicDifferentialComparison.
The actual two affine normalization differential lattices and their reciprocal scalar
transport feed the bounded Laurent-window argument over arbitrary coefficient fields.
This package does not prove good reduction, Frobenius/Weil, LPS spectral bounds,
or the exact arbitrary-finite-field/all-rate explicit quantum family. No public node changes.
-/

namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry Opposite QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry MatrixGroups UpperHalfPlane ModularForm Modular Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] originalNativeGlobalComplexModule
include hpos hN

lemma lpsOriginalNativeH0_finiteDimensional :
    FiniteDimensional ℂ Γ(lpsOriginalComplexNormalDifferentialSheaf N hpos, ⊤) := by
  let : FiniteDimensional ℂ (lpsOriginalNativeRegularKaehlerSubmodule N hpos) :=
    lpsOriginalRegularKaehler_finiteDimensional N hpos
  let e := lpsOriginalNativeH0RegularCovectorLinearEquiv N hpos hN
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

lemma lpsOriginalHolomorphicCovectors_finiteDimensional :
    FiniteDimensional ℂ (LPSOriginalHolomorphicCovectorSections N hN) := by
  let : FiniteDimensional ℂ (lpsOriginalNativeRegularKaehlerSubmodule N hpos) :=
    lpsOriginalRegularKaehler_finiteDimensional N hpos
  let e := lpsOriginalHolomorphicRegularKaehlerLinearEquiv N hpos hN
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

lemma lpsOriginalCuspForms_finiteDimensional :
    FiniteDimensional ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) := by
  let : FiniteDimensional ℂ Γ(lpsOriginalComplexNormalDifferentialSheaf N hpos, ⊤) :=
    lpsOriginalNativeH0_finiteDimensional N hpos hN
  let e := lpsOriginalNativeH0CuspFormLinearEquiv N hpos hN
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
end
end QEC.Coding.TannerLiftedProduct
