import QEC.Coding.ExpanderCodes.LPSOriginalNativeDifferentialComparison

/-!
# LPSOriginalZeroDifferentialLattice

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
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "P" => Polynomial ℂ
local notation "J" => FractionRing P
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
attribute [local instance]
  LPSOriginalLocalKaehlerFinitenessDictionary001
  LPSOriginalLocalKaehlerFinitenessDictionary002
  LPSOriginalLocalKaehlerFinitenessDictionary003
  LPSOriginalLocalKaehlerFinitenessDictionary004
  LPSOriginalLocalKaehlerFinitenessDictionary005
  LPSOriginalLocalKaehlerFinitenessDictionary006
  LPSOriginalLocalKaehlerFinitenessDictionary007
  LPSOriginalLocalKaehlerFinitenessDictionary008
  LPSOriginalLocalKaehlerFinitenessDictionary009
  LPSOriginalLocalKaehlerFinitenessDictionary010
  LPSOriginalLocalKaehlerFinitenessDictionary011
  LPSOriginalLocalKaehlerFinitenessDictionary012
  LPSOriginalLocalKaehlerFinitenessDictionary013
  LPSOriginalLocalKaehlerFinitenessDictionary014
  LPSOriginalLocalKaehlerFinitenessDictionary015
  LPSOriginalLocalKaehlerFinitenessDictionary016
  LPSOriginalLocalKaehlerFinitenessDictionary017
  LPSOriginalLocalKaehlerFinitenessDictionary018

lemma lpsOriginalZeroNormalization_finite : Module.Finite P R :=
  IsIntegralClosure.finite (A := P) («K» := J) (L := K) R

lemma lpsOriginalZeroKaehler_finite : Module.Finite P (KaehlerDifferential ℂ R) := by
  let : Module.Finite P R := lpsOriginalZeroNormalization_finite N hpos
  let : Algebra.FiniteType ℂ R := lpsOriginalZeroChart_finiteType N hpos
  exact Module.Finite.trans R (KaehlerDifferential ℂ R)

def lpsOriginalZeroDifferentialCoefficientMap : KaehlerDifferential ℂ R →ₗ[P] K :=
  ((lpsOriginalGenericKaehlerCoefficientEquiv N hpos).restrictScalars P).toLinearMap.comp
    ((KaehlerDifferential.map ℂ ℂ R K).restrictScalars P)

lemma lpsOriginalZeroDifferentialCoefficientRange_finite :
    Module.Finite P (lpsOriginalZeroDifferentialCoefficientMap N hpos).range := by
  let : Module.Finite P (KaehlerDifferential ℂ R) := lpsOriginalZeroKaehler_finite N hpos
  exact Module.Finite.range _

lemma lpsOriginalRegularCoefficient_mem_zeroLattice
    (omega : lpsOriginalNativeRegularKaehlerSubmodule N hpos) :
    lpsOriginalGenericKaehlerCoefficientEquiv N hpos omega.val ∈
      (lpsOriginalZeroDifferentialCoefficientMap N hpos).range := by
  obtain ⟨eta, heta⟩ := omega.property.1
  exact ⟨eta, congrArg (lpsOriginalGenericKaehlerCoefficientEquiv N hpos) heta⟩
end
end QEC.Coding.TannerLiftedProduct
