import QEC.Coding.AlgebraicGeometry.RiemannRoch.TwoChartFiniteDimensionalBridge
import QEC.Coding.ExpanderCodes.LPSOriginalNativeDifferentialComparison

/-!
# LPSOriginalRationalChartComparison

Constructed finite-dimensionality closure for genuine original differential spaces.
Derived internal support for parent #449 and pinned PK22 ex:Xpq, main.tex484–486,
with the original-curve/Milne interpretation in LPSOriginalHolomorphicDifferentialComparison.
The actual two affine normalization differential lattices and their reciprocal scalar
transport feed the bounded Laurent-window argument over arbitrary coefficient fields.
This package does not prove good reduction, Frobenius/Weil, LPS spectral bounds,
or the exact arbitrary-finite-field/all-rate explicit quantum family. No public node changes.
-/

open QEC.Coding.TannerLiftedProduct
open scoped Polynomial RatFunc
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
noncomputable section
local notation "P" => Polynomial ℂ
local notation "J" => FractionRing P

def lpsOriginalRatFuncToJ : RatFunc ℂ ≃ₐ[ℂ] J :=
  (IsLocalization.algEquiv (nonZeroDivisors P) (RatFunc ℂ) J).restrictScalars ℂ

lemma lpsOriginalRatFuncToJ_polynomial (p : P) :
    lpsOriginalRatFuncToJ (algebraMap P (RatFunc ℂ) p) = algebraMap P J p :=
  (IsLocalization.algEquiv (nonZeroDivisors P) (RatFunc ℂ) J).commutes p

lemma lpsOriginalRatFuncToJ_X :
    lpsOriginalRatFuncToJ RatFunc.X = algebraMap P J Polynomial.X := by
  rw [← RatFunc.algebraMap_X]
  exact lpsOriginalRatFuncToJ_polynomial Polynomial.X

lemma lpsOriginalRatFuncToJ_involution (f : RatFunc ℂ) :
    lpsOriginalRatFuncToJ (InverseAffinePlace.rationalInvolution ℂ f) =
      lpsOriginalComplexJFractionInversion (lpsOriginalRatFuncToJ f) := by
  have hp :
      (lpsOriginalRatFuncToJ.toRingHom.comp
        (InverseAffinePlace.rationalInvolution ℂ).toRingHom).comp
          (algebraMap P (RatFunc ℂ)) =
      (lpsOriginalComplexJFractionInversion.comp lpsOriginalRatFuncToJ.toRingHom).comp
        (algebraMap P (RatFunc ℂ)) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, RatFunc.algebraMap_C]
      change lpsOriginalRatFuncToJ
        (InverseAffinePlace.rationalInvolution ℂ (algebraMap ℂ (RatFunc ℂ) c)) =
          lpsOriginalComplexJFractionInversion
            (lpsOriginalRatFuncToJ (algebraMap ℂ (RatFunc ℂ) c))
      simp only [AlgEquiv.commutes, lpsOriginalComplexJFractionInversion_constant]
    · simp only [RingHom.comp_apply, RatFunc.algebraMap_X]
      change lpsOriginalRatFuncToJ (InverseAffinePlace.rationalInvolution ℂ RatFunc.X) =
        lpsOriginalComplexJFractionInversion (lpsOriginalRatFuncToJ RatFunc.X)
      rw [InverseAffinePlace.rationalInvolution_X, map_inv₀,
        lpsOriginalRatFuncToJ_X, lpsOriginalComplexJFractionInversion_X]
  have h : lpsOriginalRatFuncToJ.toRingHom.comp
      (InverseAffinePlace.rationalInvolution ℂ).toRingHom =
      lpsOriginalComplexJFractionInversion.comp lpsOriginalRatFuncToJ.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := P)
    intro p
    exact RingHom.congr_fun hp p
  exact RingHom.congr_fun h f

variable (N : ℕ) (hpos : 0 < N)
local instance : Algebra J LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local instance : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance : IsScalarTower P J K := .of_algebraMap_eq' rfl
local instance : IsScalarTower ℂ J K := .of_algebraMap_eq' rfl

@[reducible] def lpsOriginalRatFuncAlgebra : Algebra (RatFunc ℂ) K :=
  ((algebraMap J K).comp lpsOriginalRatFuncToJ.toRingHom).toAlgebra
local instance : Algebra (RatFunc ℂ) K := lpsOriginalRatFuncAlgebra N hpos

lemma lpsOriginalRatFuncPolynomialTower : IsScalarTower P (RatFunc ℂ) K := by
  apply IsScalarTower.of_algebraMap_eq
  intro p
  change algebraMap J K (algebraMap P J p) =
    algebraMap J K (lpsOriginalRatFuncToJ (algebraMap P (RatFunc ℂ) p))
  rw [lpsOriginalRatFuncToJ_polynomial]

lemma lpsOriginalRatFuncConstantTower : IsScalarTower ℂ (RatFunc ℂ) K := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change algebraMap J K (algebraMap ℂ J c) =
    algebraMap J K (lpsOriginalRatFuncToJ (algebraMap ℂ (RatFunc ℂ) c))
  rw [AlgEquiv.commutes]

variable [NeZero N]

lemma lpsOriginalRatFuncFunctionField : _root_.FunctionField ℂ K := by
  let : FiniteDimensional J K := lpsOriginalGeneratedFunctionField_finiteDimensional N hpos
  apply Module.Finite.of_equiv_equiv (A₁ := J) (B₁ := K)
    lpsOriginalRatFuncToJ.symm.toRingEquiv (RingEquiv.refl K)
  apply RingHom.ext
  intro x
  change algebraMap J K (lpsOriginalRatFuncToJ (lpsOriginalRatFuncToJ.symm x)) =
    algebraMap J K x
  rw [AlgEquiv.apply_symm_apply]

omit [NeZero N] in
lemma lpsOriginalInversePolynomialMap_eq :
    InverseAffinePlace.transportedPolynomialMap (k := ℂ) (F := K)
      (oldRationalAlgebra := lpsOriginalRatFuncAlgebra N hpos) =
      lpsOriginalReciprocalComplexFieldPolynomialMap N hpos := by
  apply RingHom.ext
  intro p
  change algebraMap J K
      (lpsOriginalRatFuncToJ
        (InverseAffinePlace.rationalInvolution ℂ (algebraMap P (RatFunc ℂ) p))) =
    algebraMap J K (lpsOriginalComplexJFractionInversion (algebraMap P J p))
  rw [lpsOriginalRatFuncToJ_involution, lpsOriginalRatFuncToJ_polynomial]
end
end QEC.Coding.TannerLiftedProduct
