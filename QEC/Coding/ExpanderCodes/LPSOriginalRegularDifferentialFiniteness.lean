import QEC.Coding.ExpanderCodes.LPSOriginalRationalChartComparison
import QEC.Coding.ExpanderCodes.LPSOriginalZeroDifferentialLattice
import QEC.Coding.ExpanderCodes.LPSOriginalInverseDifferentialLattice

/-!
# LPSOriginalRegularDifferentialFiniteness

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
open scoped Polynomial RatFunc
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "P" => Polynomial ℂ
local notation "J" => FractionRing P
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
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
local instance : Algebra (RatFunc ℂ) K := lpsOriginalRatFuncAlgebra N hpos
local instance : IsScalarTower P (RatFunc ℂ) K := lpsOriginalRatFuncPolynomialTower N hpos
local instance : IsScalarTower ℂ (RatFunc ℂ) K := lpsOriginalRatFuncConstantTower N hpos
local instance : _root_.FunctionField ℂ K := lpsOriginalRatFuncFunctionField N hpos

local instance : SMulCommClass ℂ K K where
  smul_comm c f g := by simp only [Algebra.smul_def]; ring
local instance : SMul K (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance : Module K (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K

local instance : Algebra P I := lpsOriginalInfinityPolynomialAlgebra N hpos
local instance : SMulCommClass ℂ P I where
  smul_comm c p r := by simp only [Algebra.smul_def]; ring
local instance : SMul P (KaehlerDifferential ℂ I) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ I
local instance : Module P (KaehlerDifferential ℂ I) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ I

def lpsOriginalRegularCoefficientMap :
    lpsOriginalNativeRegularKaehlerSubmodule N hpos →ₗ[ℂ] K :=
  ((lpsOriginalGenericKaehlerCoefficientEquiv N hpos).restrictScalars ℂ).toLinearMap.comp
    (lpsOriginalNativeRegularKaehlerSubmodule N hpos).subtype

def lpsOriginalRegularCoefficientSubmodule : Submodule ℂ K :=
  (lpsOriginalRegularCoefficientMap N hpos).range

lemma lpsOriginalRegularCoefficientSubmodule_mem_zeroLattice
    (x : lpsOriginalRegularCoefficientSubmodule N hpos) :
    x.val ∈ (lpsOriginalZeroDifferentialCoefficientMap N hpos).range := by
  obtain ⟨omega, homega⟩ := x.property
  rw [← homega]
  exact lpsOriginalRegularCoefficient_mem_zeroLattice N hpos omega

lemma lpsOriginalRegularCoefficientSubmodule_finiteDimensional :
    FiniteDimensional ℂ (lpsOriginalRegularCoefficientSubmodule N hpos) := by
  classical
  let : Module.Finite P (lpsOriginalZeroDifferentialCoefficientMap N hpos).range :=
    lpsOriginalZeroDifferentialCoefficientRange_finite N hpos
  let b := Module.finBasis (RatFunc ℂ) K
  refine TwoChartFiniteDimensionalBridge.finiteDimensional_of_twoChart_denominator_certificates
    b (lpsOriginalRegularCoefficientSubmodule N hpos)
    (lpsOriginalZeroDifferentialCoefficientMap N hpos).range
    (lpsOriginalRegularCoefficientSubmodule_mem_zeroLattice N hpos) ?_
  dsimp only
  let : Algebra (RatFunc ℂ) K := InverseAffinePlace.transportedRationalAlgebra
    (k := ℂ) (F := K) (oldRationalAlgebra := lpsOriginalRatFuncAlgebra N hpos)
  let : Algebra P K := InverseAffinePlace.transportedPolynomialAlgebra
    (k := ℂ) (F := K) (oldRationalAlgebra := lpsOriginalRatFuncAlgebra N hpos)
  let : SMul P K := Algebra.toSMul
  let : Module P K := Algebra.toModule
  refine ⟨(lpsOriginalTransportedInverseCoefficientMap N hpos).range,
    lpsOriginalTransportedInverseCoefficientRange_finite N hpos, ?_⟩
  intro x
  obtain ⟨omega, homega⟩ := x.property
  rw [← homega]
  exact lpsOriginalRegularCoefficient_mem_transportedInverseLattice N hpos omega

lemma lpsOriginalRegularKaehler_finiteDimensional :
    FiniteDimensional ℂ (lpsOriginalNativeRegularKaehlerSubmodule N hpos) := by
  let : FiniteDimensional ℂ (lpsOriginalRegularCoefficientMap N hpos).range :=
    lpsOriginalRegularCoefficientSubmodule_finiteDimensional N hpos
  apply FiniteDimensional.of_injective (lpsOriginalRegularCoefficientMap N hpos).rangeRestrict
  intro x y h
  apply Subtype.ext
  apply (lpsOriginalGenericKaehlerCoefficientEquiv N hpos).injective
  exact congrArg Subtype.val h
end
end QEC.Coding.TannerLiftedProduct
