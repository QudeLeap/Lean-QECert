import QEC.Coding.ExpanderCodes.LPSOriginalGenericDifferentialComparison
import QEC.Coding.ExpanderCodes.LPSOriginalCompactMeromorphicDifferentialComparison

/-!
# Original generic and all compact meromorphic differential comparison

Compare the SAME original generated field with ALL native compact meromorphic
covector germs. Preserve true complex constants, literal j/dj, actual pointwise
function multiplication, and universal D for every actual meromorphic function
representative, using faithful original upstairs restriction and actual chain rule.

This is internal proof closure for parent #449 and the original LPS route in
PK22 ex:Xpq (pinned main.tex484–486), following the actual meromorphic/differential
interpretation of the same modular curve in Milne, Modular Functions and Modular
Forms. N is positive and 4 divides N, including the actual theta levels.

This module does not prove global algebraic regularity/GAGA, normalization base
change, uniform good reduction, Frobenius/Weil estimates or the arbitrary-field
PK22 quantum family theorem. No public node changes status here.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane Manifold ContDiff TensorProduct
noncomputable section
section CompactGenericDifferential
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
local notation "M" => LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet
local instance : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance : Algebra ℂ L := ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict.comp
  (lpsOriginalFilledMeromorphicComplexConstants N hN)).toAlgebra

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalGeneratedCompactMeromorphic_restrict (f : K) :
    (lpsOriginalCompactToRestrictedMeromorphic N hN
      (lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN f)).val =
        lpsOriginalGenericToMeromorphicGerm N hpos f := by
  change (lpsOriginalCompactRestrictedMeromorphicEquiv N hN
    ((lpsOriginalCompactRestrictedMeromorphicEquiv N hN).symm
      (lpsOriginalGeneratedFullMeromorphicEquiv N hpos hN f))).val = _
  rw [RingEquiv.apply_symm_apply]
  exact lpsOriginalGeneratedFullMeromorphicEquiv_apply N hpos hN f

/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv : K ≃ₐ[ℂ] L where
  toRingEquiv := lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN
  commutes' c := by
    apply lpsOriginalCompactToRestrictedMeromorphic_injective N hN
    apply Subtype.ext
    change (lpsOriginalCompactToRestrictedMeromorphic N hN
      (lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN (algebraMap ℂ K c))).val =
      (lpsOriginalCompactToRestrictedMeromorphic N hN (algebraMap ℂ L c)).val
    rw [lpsOriginalGeneratedCompactMeromorphic_restrict]
    rw [(lpsOriginalGenericToMeromorphicGerm N hpos).commutes]
    change algebraMap ℂ M c =
      (lpsOriginalCompactToRestrictedMeromorphic N hN
        ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict
          (lpsOriginalFilledMeromorphicComplexConstants N hN c))).val
    rw [lpsOriginalCompactToRestrictedMeromorphic_apply]
    rfl


local instance : IsScalarTower ℂ J K := IsScalarTower.of_algebraMap_eq' rfl
local notation "V" => LPSOriginalFilledMeromorphicCovectorRepresentatives N hN
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
local instance : AddCommGroup V := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact (lpsOriginalFilledMeromorphicCovectorSubmodule N hN).addCommGroup

/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalGenericKaehlerComplexCoefficientEquiv : KaehlerDifferential ℂ K ≃ₗ[ℂ] K :=
  (lpsOriginalGenericKaehlerCoefficientEquiv N hpos).restrictScalars ℂ



/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalGenericCompactCoefficientToCovectorEquiv :
    K ≃ₗ[ℂ] LPSOriginalCompactMeromorphicCovectorGerms N hN := by
  let e₂ : K ≃ₗ[ℂ] L :=
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN).toLinearEquiv
  let e₃ : L ≃ₗ[ℂ] LPSOriginalCompactMeromorphicCovectorGerms N hN :=
    (lpsOriginalCompactMeromorphicCovectorLinearEquiv N hN).symm
  exact e₂.trans e₃


/-- Genuine universal differentials are complex-linearly equivalent to ALL native compact meromorphic covector germs. -/
def lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv :
    KaehlerDifferential ℂ K ≃ₗ[ℂ] LPSOriginalCompactMeromorphicCovectorGerms N hN :=
  (lpsOriginalGenericKaehlerComplexCoefficientEquiv N hpos).trans
    (lpsOriginalGenericCompactCoefficientToCovectorEquiv N hpos hN)

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_ratio
    (differentialForm : KaehlerDifferential ℂ K) :
    lpsOriginalCompactMeromorphicCovectorLinearEquiv N hN
      (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN differentialForm) =
        lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN
          (lpsOriginalGenericKaehlerCoefficientEquiv N hpos differentialForm) := by
  exact (lpsOriginalCompactMeromorphicCovectorLinearEquiv N hN).apply_symm_apply _


/-- For EVERY field element and EVERY actual representative, universal df maps to the actual manifold derivative dF. -/
lemma lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_D
    (f : K) (F : LPSOriginalFilledMeromorphicFunctionRing N hN)
    (hF : lpsOriginalCompactMeromorphicGermAlgHom N hN F =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f) :
    lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN
      (KaehlerDifferential.D ℂ K f) =
        lpsOriginalCompactMeromorphicCovectorClass N hN
          ⟨lpsOriginalFilledFunctionCovector N hN F.val,
            lpsOriginalFilledFunctionCovector_meromorphic N hN F.val F.property⟩ := by
  apply (lpsOriginalCompactMeromorphicCovectorLinearEquiv N hN).injective
  rw [lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_ratio,
    lpsOriginalCompactMeromorphicCovectorLinearEquiv_class]
  apply lpsOriginalCompactToRestrictedMeromorphic_injective N hN
  apply Subtype.ext
  change (lpsOriginalCompactToRestrictedMeromorphic N hN
    (lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN
      (lpsOriginalGenericKaehlerCoefficientEquiv N hpos (KaehlerDifferential.D ℂ K f)))).val = _
  rw [lpsOriginalGeneratedCompactMeromorphic_restrict]
  change lpsOriginalGenericToMeromorphicGerm N hpos
    (lpsOriginalGenericJDerivation N hpos f) = _
  have hrepr := congrArg (fun g : L => (lpsOriginalCompactToRestrictedMeromorphic N hN g).val) hF
  change (lpsOriginalCompactToRestrictedMeromorphic N hN
    ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict F)).val =
      (lpsOriginalCompactToRestrictedMeromorphic N hN
        (lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN f)).val at hrepr
  rw [lpsOriginalCompactToRestrictedMeromorphic_apply,
    lpsOriginalGeneratedCompactMeromorphic_restrict] at hrepr
  have hratio := lpsOriginalCompactMeromorphicCovectorRatioMap_D_restrict N hN F
  rw [hrepr,lpsOriginalGenericJDerivation_meromorphic] at hratio
  exact (mul_right_cancel₀ lpsOriginalJMeromorphicDerivative_ne_zero hratio).symm


/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv_j :
    lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN
      (algebraMap P K Polynomial.X) =
        lpsOriginalCompactMeromorphicGermAlgHom N hN
          ⟨lpsOriginalFilledJ N,lpsOriginalFilledChartMeromorphic_j N hN⟩ := by
  apply lpsOriginalCompactToRestrictedMeromorphic_injective N hN
  apply Subtype.ext
  change (lpsOriginalCompactToRestrictedMeromorphic N hN
    (lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN
      (algebraMap P K Polynomial.X))).val =
    (lpsOriginalCompactToRestrictedMeromorphic N hN
      ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict
        ⟨lpsOriginalFilledJ N,lpsOriginalFilledChartMeromorphic_j N hN⟩)).val
  rw [lpsOriginalGeneratedCompactMeromorphic_restrict,
    lpsOriginalGenericToMeromorphicGerm_j,lpsOriginalCompactToRestrictedMeromorphic_apply]
  rfl

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_D_j :
    lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN
      (KaehlerDifferential.D ℂ K (algebraMap P K Polynomial.X)) =
        lpsOriginalCompactMeromorphicCovectorClass N hN
          ⟨lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N),
            lpsOriginalFilledFunctionCovector_meromorphic N hN (lpsOriginalFilledJ N)
              (lpsOriginalFilledChartMeromorphic_j N hN)⟩ :=
  lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_D N hpos hN
    (algebraMap P K Polynomial.X) ⟨lpsOriginalFilledJ N,lpsOriginalFilledChartMeromorphic_j N hN⟩
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv_j N hpos hN).symm

/-- Generic scalar multiplication agrees with actual pointwise function multiplication of arbitrary native representatives. -/
lemma lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_functionTimes
    (f : K) (differentialForm : KaehlerDifferential ℂ K)
    (F : LPSOriginalFilledMeromorphicFunctionRing N hN)
    (sectionForm : LPSOriginalFilledMeromorphicCovectorRepresentatives N hN)
    (hF : lpsOriginalCompactMeromorphicGermAlgHom N hN F =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f)
    (hsection : lpsOriginalCompactMeromorphicCovectorClass N hN sectionForm =
      lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN differentialForm) :
    lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN (f • differentialForm) =
      lpsOriginalCompactMeromorphicCovectorClass N hN
        (lpsOriginalFilledMeromorphicFunctionTimesCovector N hN F sectionForm) := by
  apply (lpsOriginalCompactMeromorphicCovectorLinearEquiv N hN).injective
  rw [lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_ratio,
    map_smul,lpsOriginalCompactMeromorphicCovectorLinearEquiv_class,
    lpsOriginalCompactMeromorphicCovectorRatioMap_functionTimes,hF]
  have hs := congrArg (lpsOriginalCompactMeromorphicCovectorLinearEquiv N hN) hsection
  rw [lpsOriginalCompactMeromorphicCovectorLinearEquiv_class,
    lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_ratio] at hs
  rw [hs]
  change lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN
    (f * lpsOriginalGenericKaehlerCoefficientEquiv N hpos differentialForm) = _
  exact map_mul _ _ _

end CompactGenericDifferential
end
end QEC.Coding.TannerLiftedProduct
