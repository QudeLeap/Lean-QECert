import QEC.Coding.ExpanderCodes.LPSOriginalArithmeticFunctionFieldComparison
import QEC.Coding.ExpanderCodes.LPSOriginalMeromorphicDifferentiation
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field

/-!
# Genuine generic original Kähler differentials

Use actual localization and the finite separable extension C(j,j_N)/C(j) to
identify its universal Kähler module with the coefficient of dj. The actual
meromorphic germ derivative realizes universal D and gives the injective generic
comparison and scalar-extended tensor equivalence.

This is internal proof closure for parent #449 and the original LPS route in
PK22 ex:Xpq (pinned main.tex484–486), following the actual meromorphic/differential
interpretation of the same modular curve in Milne, Modular Functions and Modular
Forms. N is positive and 4 divides N, including the actual theta levels.

This module does not prove global algebraic regularity/GAGA, normalization base
change, uniform good reduction, Frobenius/Weil estimates or the arbitrary-field
PK22 quantum family theorem. No public node changes status here.
-/

namespace QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section

section GenericDifferential
variable (N : ℕ) (hpos : 0 < N)
local instance : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ

local instance : Algebra P K :=
  ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance : Algebra ℂ K :=
  ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance : IsScalarTower P J K := IsScalarTower.of_algebraMap_eq' rfl
local instance : IsScalarTower ℂ J K := IsScalarTower.of_algebraMap_eq' rfl
local instance : IsScalarTower ℂ P K := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change algebraMap J K (algebraMap ℂ J c) =
    algebraMap J K (algebraMap P J (algebraMap ℂ P c))
  rw [IsScalarTower.algebraMap_apply ℂ P J]

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalGenericComplexConstant_value (c : ℂ) :
    (algebraMap ℂ K c).val = algebraMap ℂ LPSOriginalHolomorphicFractionField c := by
  change lpsOriginalJFractionEmbedding (algebraMap ℂ J c) = _
  rw [IsScalarTower.algebraMap_apply ℂ P J,
    lpsOriginalJFractionEmbedding_polynomial]
  simp only [lpsOriginalJHolomorphicEval, Polynomial.algebraMap_eq, Polynomial.aeval_C]
  exact (IsScalarTower.algebraMap_apply ℂ LPSOriginalHolomorphicRing
    LPSOriginalHolomorphicFractionField c).symm

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalGenericJCoordinate_value :
    (algebraMap P K Polynomial.X).val =
      algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
        lpsOriginalJHolomorphic := by
  change lpsOriginalJFractionEmbedding (algebraMap P J Polynomial.X) = _
  rw [lpsOriginalJFractionEmbedding_polynomial]
  simp only [lpsOriginalJHolomorphicEval, Polynomial.aeval_X]

variable [NeZero N]

/-- Actual localization followed by the finite char-zero separable original field extension is formally étale. -/
lemma lpsOriginalGenericPolynomial_formallyEtale : Algebra.FormallyEtale P K := by
  let : FiniteDimensional J K := lpsOriginalGeneratedFunctionField_finiteDimensional N hpos
  let : Algebra.IsSeparable J K := inferInstance
  let : Algebra.FormallyEtale J K := Algebra.FormallyEtale.of_isSeparable J K
  let : Algebra.FormallyEtale P J :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors P)
  exact Algebra.FormallyEtale.comp P J K

/-- The universal original Kähler module has genuine basis dj via polynomial/base-change differential theorems. -/
def lpsOriginalGenericKaehlerCoefficientEquiv : KaehlerDifferential ℂ K ≃ₗ[K] K := by
  let : Algebra.FormallyEtale P K := lpsOriginalGenericPolynomial_formallyEtale N hpos
  exact (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ P K).symm |>.trans
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K)
      (KaehlerDifferential.polynomialEquiv ℂ)).trans
        (TensorProduct.AlgebraTensorModule.rid P K K))

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalGenericKaehlerCoefficientEquiv_D_polynomial (p : Polynomial ℂ) :
    lpsOriginalGenericKaehlerCoefficientEquiv N hpos
      (KaehlerDifferential.D ℂ K (algebraMap P K p)) =
        algebraMap P K p.derivative := by
  let : Algebra.FormallyEtale P K := lpsOriginalGenericPolynomial_formallyEtale N hpos
  unfold lpsOriginalGenericKaehlerCoefficientEquiv
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    TensorProduct.AlgebraTensorModule.congr_tmul,
    KaehlerDifferential.polynomialEquiv_D,
    TensorProduct.AlgebraTensorModule.rid_tmul]
  simp only [LinearEquiv.refl_apply, Algebra.smul_def, mul_one]

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalGenericKaehlerCoefficientEquiv_D_j :
    lpsOriginalGenericKaehlerCoefficientEquiv N hpos
      (KaehlerDifferential.D ℂ K (algebraMap P K Polynomial.X)) = 1 := by
  rw [lpsOriginalGenericKaehlerCoefficientEquiv_D_polynomial,
    Polynomial.derivative_X, map_one]

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalGenericKaehler_D_j_ne_zero :
    KaehlerDifferential.D ℂ K (algebraMap P K Polynomial.X) ≠ 0 := by
  intro h
  have he := lpsOriginalGenericKaehlerCoefficientEquiv_D_j N hpos
  rw [h, map_zero] at he
  exact zero_ne_one he

/-- Every universal differential equals its actual coefficient times the universal dj. -/
lemma lpsOriginalGenericKaehler_expand (differentialForm : KaehlerDifferential ℂ K) :
    differentialForm = lpsOriginalGenericKaehlerCoefficientEquiv N hpos differentialForm •
      KaehlerDifferential.D ℂ K (algebraMap P K Polynomial.X) := by
  apply (lpsOriginalGenericKaehlerCoefficientEquiv N hpos).injective
  rw [map_smul, lpsOriginalGenericKaehlerCoefficientEquiv_D_j]
  simp

end GenericDifferential
end
end QEC.Coding.TannerLiftedProduct


namespace QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane TensorProduct
noncomputable section
section GenericMeromorphicDifferential
variable (N : ℕ) (hpos : 0 < N)
local instance : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ

local instance : Algebra P K :=
  ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance : Algebra ℂ K :=
  ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance : IsScalarTower P J K := IsScalarTower.of_algebraMap_eq' rfl
local instance : IsScalarTower ℂ J K := IsScalarTower.of_algebraMap_eq' rfl
local instance : IsScalarTower ℂ P K := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change algebraMap J K (algebraMap ℂ J c) =
    algebraMap J K (algebraMap P J (algebraMap ℂ P c))
  rw [IsScalarTower.algebraMap_apply ℂ P J]


local notation "M" => LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet

/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalGenericToMeromorphicGerm : K →ₐ[ℂ] M where
  toRingHom := lpsOriginalHolomorphicFractionToMeromorphicGerm.comp
    (lpsOriginalGeneratedFunctionField N hpos).val.toRingHom
  commutes' c := by
    change lpsOriginalHolomorphicFractionToMeromorphicGerm
      (algebraMap ℂ K c).val = algebraMap ℂ M c
    rw [lpsOriginalGenericComplexConstant_value,IsScalarTower.algebraMap_apply ℂ
      LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField,
      lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic,
      lpsOriginalHolomorphicToMeromorphicGerm_constant]

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalGenericToMeromorphicGerm_j :
    lpsOriginalGenericToMeromorphicGerm N hpos (algebraMap P K Polynomial.X) =
      lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic := by
  change lpsOriginalHolomorphicFractionToMeromorphicGerm
    (algebraMap P K Polynomial.X).val = _
  rw [lpsOriginalGenericJCoordinate_value,
    lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic]

local instance : Algebra K M := (lpsOriginalGenericToMeromorphicGerm N hpos).toAlgebra

/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalGenericMeromorphicDerivation : Derivation ℂ K M := by
  let φ := lpsOriginalGenericToMeromorphicGerm N hpos
  let D : K →ₗ[ℂ] M :=
    { toFun := fun f => lpsOriginalMeromorphicGermCoefficientDerivative
        UpperHalfPlane.upperHalfPlaneSet (φ f)
      map_add' := by
        intro f g
        rw [map_add,lpsOriginalMeromorphicGermCoefficientDerivative_add]
      map_smul' := by
        intro c f
        rw [map_smul]
        change lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
          (lpsOriginalMeromorphicGermComplexConstants UpperHalfPlane.upperHalfPlaneSet c * φ f) =
            lpsOriginalMeromorphicGermComplexConstants UpperHalfPlane.upperHalfPlaneSet c *
              lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet (φ f)
        rw [lpsOriginalMeromorphicGermCoefficientDerivative_mul,
          lpsOriginalMeromorphicGermCoefficientDerivative_constant,mul_zero,add_zero] }
  refine Derivation.mk' D ?_
  intro f g
  change lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
    (φ (f*g)) = φ f * lpsOriginalMeromorphicGermCoefficientDerivative
      UpperHalfPlane.upperHalfPlaneSet (φ g) + φ g *
        lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet (φ f)
  rw [map_mul,lpsOriginalMeromorphicGermCoefficientDerivative_mul]

/-- Realize universal differentials through actual representative differentiation, using its universal property. -/
def lpsOriginalGenericMeromorphicDifferentialMap : KaehlerDifferential ℂ K →ₗ[K] M :=
  (lpsOriginalGenericMeromorphicDerivation N hpos).liftKaehlerDifferential

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalGenericMeromorphicDifferentialMap_D (f : K) :
    lpsOriginalGenericMeromorphicDifferentialMap N hpos (KaehlerDifferential.D ℂ K f) =
      lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
        (lpsOriginalGenericToMeromorphicGerm N hpos f) := by
  rw [lpsOriginalGenericMeromorphicDifferentialMap,
    Derivation.liftKaehlerDifferential_comp_D]
  rfl

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalGenericMeromorphicDifferentialMap_D_j :
    lpsOriginalGenericMeromorphicDifferentialMap N hpos
      (KaehlerDifferential.D ℂ K (algebraMap P K Polynomial.X)) =
        lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
          (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic) := by
  rw [lpsOriginalGenericMeromorphicDifferentialMap_D,lpsOriginalGenericToMeromorphicGerm_j]

variable [NeZero N]

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalGenericMeromorphicDifferentialMap_expand
    (differentialForm : KaehlerDifferential ℂ K) :
    lpsOriginalGenericMeromorphicDifferentialMap N hpos differentialForm =
      lpsOriginalGenericToMeromorphicGerm N hpos
        (lpsOriginalGenericKaehlerCoefficientEquiv N hpos differentialForm) *
          lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
            (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic) := by
  conv_lhs => rw [lpsOriginalGenericKaehler_expand N hpos differentialForm]
  rw [map_smul, lpsOriginalGenericMeromorphicDifferentialMap_D_j]
  rfl

/-- Faithfulness and the actual nonzero j derivative make the entire generic comparison injective. -/
lemma lpsOriginalGenericMeromorphicDifferentialMap_injective :
    Function.Injective (lpsOriginalGenericMeromorphicDifferentialMap N hpos) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro differentialForm h
  rw [lpsOriginalGenericMeromorphicDifferentialMap_expand] at h
  have hc := (mul_eq_zero.mp h).resolve_right lpsOriginalJMeromorphicDerivative_ne_zero
  have hz : lpsOriginalGenericKaehlerCoefficientEquiv N hpos differentialForm = 0 :=
    (lpsOriginalGenericToMeromorphicGerm N hpos).injective (hc.trans (map_zero _).symm)
  exact (lpsOriginalGenericKaehlerCoefficientEquiv N hpos).injective
    (hz.trans (map_zero _).symm)


/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalGenericJDerivation : Derivation ℂ K K :=
  (lpsOriginalGenericKaehlerCoefficientEquiv N hpos).compDer (KaehlerDifferential.D ℂ K)

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalGenericJDerivation_j :
    lpsOriginalGenericJDerivation N hpos (algebraMap P K Polynomial.X) = 1 :=
  lpsOriginalGenericKaehlerCoefficientEquiv_D_j N hpos

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalGenericJDerivation_meromorphic (f : K) :
    lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
      (lpsOriginalGenericToMeromorphicGerm N hpos f) =
        lpsOriginalGenericToMeromorphicGerm N hpos (lpsOriginalGenericJDerivation N hpos f) *
          lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
            (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic) := by
  rw [← lpsOriginalGenericMeromorphicDifferentialMap_D,
    lpsOriginalGenericMeromorphicDifferentialMap_expand]
  rfl

/-- Scalar extension of genuine universal differentials realizes all upstairs meromorphic coefficients. -/
def lpsOriginalGenericMeromorphicDifferentialTensorEquiv :
    M ⊗[K] KaehlerDifferential ℂ K ≃ₗ[M] M :=
  ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl M M)
    (lpsOriginalGenericKaehlerCoefficientEquiv N hpos)).trans
      (TensorProduct.AlgebraTensorModule.rid K M M)).trans
        (LinearEquiv.smulOfNeZero M M
          (lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
            (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic))
          lpsOriginalJMeromorphicDerivative_ne_zero)

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalGenericMeromorphicDifferentialTensorEquiv_tmul
    (r : M) (differentialForm : KaehlerDifferential ℂ K) :
    lpsOriginalGenericMeromorphicDifferentialTensorEquiv N hpos (r ⊗ₜ differentialForm) =
      r * lpsOriginalGenericMeromorphicDifferentialMap N hpos differentialForm := by
  rw [lpsOriginalGenericMeromorphicDifferentialTensorEquiv,
    LinearEquiv.trans_apply,LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.congr_tmul,
    TensorProduct.AlgebraTensorModule.rid_tmul,
    lpsOriginalGenericMeromorphicDifferentialMap_expand]
  simp only [LinearEquiv.refl_apply, LinearEquiv.smulOfNeZero_apply, Algebra.smul_def]
  change lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
    (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic) *
      (lpsOriginalGenericToMeromorphicGerm N hpos
        (lpsOriginalGenericKaehlerCoefficientEquiv N hpos differentialForm) * r) = _
  ring

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalGenericMeromorphicDifferentialTensorEquiv_D
    (r : M) (f : K) :
    lpsOriginalGenericMeromorphicDifferentialTensorEquiv N hpos
      (r ⊗ₜ KaehlerDifferential.D ℂ K f) =
        r * lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
          (lpsOriginalGenericToMeromorphicGerm N hpos f) := by
  rw [lpsOriginalGenericMeromorphicDifferentialTensorEquiv_tmul,
    lpsOriginalGenericMeromorphicDifferentialMap_D]

end GenericMeromorphicDifferential
end
end QEC.Coding.TannerLiftedProduct
