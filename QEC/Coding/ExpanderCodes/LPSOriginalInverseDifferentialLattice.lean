import QEC.Coding.ExpanderCodes.LPSOriginalRationalChartComparison

/-!
# LPSOriginalInverseDifferentialLattice

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
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
attribute [local instance]
  LPSOriginalLocalKaehlerFinitenessDictionary027
  LPSOriginalLocalKaehlerFinitenessDictionary029
  LPSOriginalLocalKaehlerFinitenessDictionary031
  LPSOriginalLocalKaehlerFinitenessDictionary032
  LPSOriginalLocalKaehlerFinitenessDictionary033
  LPSOriginalLocalKaehlerFinitenessDictionary034
  LPSOriginalLocalKaehlerFinitenessDictionary035
  LPSOriginalLocalKaehlerFinitenessDictionary036
  LPSOriginalLocalKaehlerFinitenessDictionary037
  LPSOriginalLocalKaehlerFinitenessDictionary038
  LPSOriginalLocalKaehlerFinitenessDictionary039
  LPSOriginalLocalKaehlerFinitenessDictionary040
  LPSOriginalLocalKaehlerFinitenessDictionary041
  LPSOriginalLocalKaehlerFinitenessDictionary042
  LPSOriginalLocalKaehlerFinitenessDictionary043

local instance : Algebra P J := lpsOriginalReciprocalBaseCAlgebra
local instance : SMul P J := Algebra.toSMul
local instance : Module P J := Algebra.toModule
local instance : IsFractionRing P J := lpsOriginalReciprocalBaseC_isFractionRing
local instance : Algebra P K := (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).toAlgebra
local instance : SMul P K := Algebra.toSMul
local instance : Module P K := Algebra.toModule
local instance : IsScalarTower P J K := .of_algebraMap_eq' rfl
local instance : IsScalarTower ℂ P K := .of_algebraMap_eq fun c => by
  change algebraMap J K (algebraMap ℂ J c) =
    algebraMap J K (lpsOriginalComplexJFractionInversion (algebraMap ℂ J c))
  rw [lpsOriginalComplexJFractionInversion_constant]

local instance : SMulCommClass ℂ P R where
  smul_comm c p r := by simp only [Algebra.smul_def]; ring
local instance : SMul P (KaehlerDifferential ℂ R) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ R
local instance : Module P (KaehlerDifferential ℂ R) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ R
local instance : SMul R (KaehlerDifferential ℂ R) :=
  LPSOriginalLocalKaehlerFinitenessDictionary035 N hpos
local instance : Module R (KaehlerDifferential ℂ R) :=
  LPSOriginalLocalKaehlerFinitenessDictionary036 N hpos
local instance : MulAction R (KaehlerDifferential ℂ R) :=
  (LPSOriginalLocalKaehlerFinitenessDictionary036 N hpos).toMulAction
local instance : IsScalarTower P R (KaehlerDifferential ℂ R) :=
  KaehlerDifferential.isScalarTower_of_tower («R» := ℂ) (S := R) (R₁ := P) (R₂ := R)

lemma lpsOriginalInfinityNormalization_finite : Module.Finite P R :=
  IsIntegralClosure.finite (A := P) («K» := J) (L := K) R

lemma lpsOriginalInfinityKaehler_finite : Module.Finite P (KaehlerDifferential ℂ R) := by
  let : Module.Finite P R := lpsOriginalInfinityNormalization_finite N hpos
  let : Algebra.FiniteType ℂ R := lpsOriginalInfinityChart_finiteType N hpos
  exact Module.Finite.trans R (KaehlerDifferential ℂ R)

end
end QEC.Coding.TannerLiftedProduct

namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.TannerLiftedProduct
open scoped Polynomial RatFunc
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "P" => Polynomial ℂ
local notation "J" => FractionRing P
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
attribute [local instance]
  LPSOriginalLocalKaehlerFinitenessDictionary027
  LPSOriginalLocalKaehlerFinitenessDictionary029
  LPSOriginalLocalKaehlerFinitenessDictionary031
  LPSOriginalLocalKaehlerFinitenessDictionary032
  LPSOriginalLocalKaehlerFinitenessDictionary033
  LPSOriginalLocalKaehlerFinitenessDictionary034
  LPSOriginalLocalKaehlerFinitenessDictionary035
  LPSOriginalLocalKaehlerFinitenessDictionary036
  LPSOriginalLocalKaehlerFinitenessDictionary037
  LPSOriginalLocalKaehlerFinitenessDictionary038
  LPSOriginalLocalKaehlerFinitenessDictionary039
  LPSOriginalLocalKaehlerFinitenessDictionary040
@[reducible] def lpsOriginalInfinityPolynomialAlgebra : Algebra P R := by
  let : Algebra P K := (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).toAlgebra
  exact inferInstance
local instance : Algebra P R := lpsOriginalInfinityPolynomialAlgebra N hpos
local instance : Algebra (RatFunc ℂ) K :=
  InverseAffinePlace.transportedRationalAlgebra (k := ℂ) (F := K)
    (oldRationalAlgebra := lpsOriginalRatFuncAlgebra N hpos)
local instance : Algebra P K :=
  InverseAffinePlace.transportedPolynomialAlgebra (k := ℂ) (F := K)
    (oldRationalAlgebra := lpsOriginalRatFuncAlgebra N hpos)
local instance : SMul P K := Algebra.toSMul
local instance : Module P K := Algebra.toModule

local instance : SMulCommClass ℂ P R where
  smul_comm c p r := by simp only [Algebra.smul_def]; ring
local instance : SMul P (KaehlerDifferential ℂ R) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ R
local instance : Module P (KaehlerDifferential ℂ R) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ R
local instance : SMulCommClass ℂ K K where
  smul_comm c f g := by simp only [Algebra.smul_def]; ring
local instance : SMul K (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance lpsOriginalTransportedInverseOmegaKModule : Module K (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K

local instance : SMul R (KaehlerDifferential ℂ R) :=
  LPSOriginalLocalKaehlerFinitenessDictionary035 N hpos
local instance : Module R (KaehlerDifferential ℂ R) :=
  LPSOriginalLocalKaehlerFinitenessDictionary036 N hpos
local instance : MulAction R (KaehlerDifferential ℂ R) :=
  (LPSOriginalLocalKaehlerFinitenessDictionary036 N hpos).toMulAction

local instance : MulAction K (KaehlerDifferential ℂ K) :=
  (lpsOriginalTransportedInverseOmegaKModule N hpos).toMulAction
local instance : IsScalarTower R K (KaehlerDifferential ℂ K) :=
  KaehlerDifferential.isScalarTower_of_tower («R» := ℂ) (S := K) (R₁ := R) (R₂ := K)

def lpsOriginalTransportedInverseCoefficientMap : KaehlerDifferential ℂ R →ₗ[P] K where
  toFun := fun eta => lpsOriginalGenericKaehlerCoefficientEquiv N hpos
    (KaehlerDifferential.map ℂ ℂ R K eta)
  map_add' eta theta := by rw [map_add, map_add]
  map_smul' p eta := by
    change lpsOriginalGenericKaehlerCoefficientEquiv N hpos
      (KaehlerDifferential.map ℂ ℂ R K (p • eta)) =
        p • lpsOriginalGenericKaehlerCoefficientEquiv N hpos
          (KaehlerDifferential.map ℂ ℂ R K eta)
    rw [← IsScalarTower.algebraMap_smul R p eta, LinearMap.map_smul]
    rw [← IsScalarTower.algebraMap_smul K (algebraMap P R p)
      (KaehlerDifferential.map ℂ ℂ R K eta), LinearEquiv.map_smul]
    have hcoord : algebraMap R K (algebraMap P R p) =
        lpsOriginalReciprocalComplexFieldPolynomialMap N hpos p := rfl
    rw [hcoord]
    change lpsOriginalReciprocalComplexFieldPolynomialMap N hpos p * _ =
      InverseAffinePlace.transportedPolynomialMap (k := ℂ) (F := K)
        (oldRationalAlgebra := lpsOriginalRatFuncAlgebra N hpos) p * _
    rw [lpsOriginalInversePolynomialMap_eq]

lemma lpsOriginalTransportedInverseCoefficientRange_finite :
    Module.Finite P (lpsOriginalTransportedInverseCoefficientMap N hpos).range := by
  let : Module.Finite P (KaehlerDifferential ℂ R) := lpsOriginalInfinityKaehler_finite N hpos
  exact Module.Finite.range _

lemma lpsOriginalRegularCoefficient_mem_transportedInverseLattice
    (omega : lpsOriginalNativeRegularKaehlerSubmodule N hpos) :
    lpsOriginalGenericKaehlerCoefficientEquiv N hpos omega.val ∈
      (lpsOriginalTransportedInverseCoefficientMap N hpos).range := by
  obtain ⟨eta, heta⟩ := omega.property.2
  exact ⟨eta, congrArg (lpsOriginalGenericKaehlerCoefficientEquiv N hpos) heta⟩
end
end QEC.Coding.TannerLiftedProduct
