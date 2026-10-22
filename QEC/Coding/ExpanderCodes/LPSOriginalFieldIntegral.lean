import QEC.Coding.ExpanderCodes.LPSOriginalNormalizedIntegral
import QEC.Coding.ExpanderCodes.LPSOriginalLocalMeromorphicOrder

/-!
# The actual original zero normalization is interior no-pole functions

For every element of the independently defined SAME C(j,jN), prove C[j]
integrality iff every actual filled interior chart-germ order is nonnegative.
The converse constructs a normalized representative and a genuine monic
annihilator, then transfers it through the actual C[j]-algebra equivalence.
The forward direction uses actual valuation integrality and analyticity of j.

Internal/API closure on PK22 ex:Xpq, pinned main.tex484–486, for parent #449.
This proves the zero-chart ring criterion; it does not establish global point
coverage/GAGA, reciprocal-chart equality, good reduction, Frobenius/Weil or
the arbitrary-finite-field explicit quantum family.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance lpsOriginalFieldIntegralDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "E" => lpsOriginalFilledMeromorphicRestrictionSubfield N hN
local instance lpsOriginalFieldIntegralDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance lpsOriginalFieldIntegralDictionary003 : Algebra P E := ((lpsOriginalFullMeromorphicJFractionEmbedding N hN).comp (algebraMap P J)).toAlgebra

def lpsOriginalGeneratedRestrictionPolynomialAlgEquiv : K ≃ₐ[P] E :=
  { lpsOriginalGeneratedFullMeromorphicEquiv N hpos hN with
    commutes' p := by apply Subtype.ext; rfl }

lemma lpsOriginalFieldJ_interior_order_nonnegative
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) (algebraMap P K Polynomial.X) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  rw [lpsOriginalFieldLocalOrder_value,lpsOriginalFieldToLocal_j]
  change 0 ≤ meromorphicOrderAt
    (lpsOriginalFilledJ N ∘ (lpsOriginalLocalChart N hN (Sum.inl x)).symm)
    (lpsOriginalLocalChartCenter N hN (Sum.inl x))
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let e := lpsOriginalFilledInteriorChart N hN x
  have hs := lpsOriginalFilledInteriorChart_mem N hN x
  have ha := lpsOriginalFilledJ_interior_analytic N hN x (e (Sum.inl x)) (e.map_source hs)
  exact ha.meromorphicAt.meromorphicOrderAt_nonneg_iff.mpr
    ⟨lpsOriginalFilledJ N ∘ e.symm,ha,Filter.EventuallyEq.rfl⟩

lemma lpsOriginalGeneratedRestriction_representative
    (f : K) (F : LPSOriginalFilledMeromorphicFunctionRing N hN)
    (hF : lpsOriginalCompactMeromorphicGermAlgHom N hN F =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f) :
    lpsOriginalGeneratedRestrictionPolynomialAlgEquiv N hpos hN f =
      lpsOriginalFilledMeromorphicRestriction N hN F.val F.property := by
  have he : (lpsOriginalCompactRestrictedMeromorphicEquiv N hN)
      (lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN f) =
      lpsOriginalGeneratedRestrictionPolynomialAlgEquiv N hpos hN f := by
    change (lpsOriginalCompactRestrictedMeromorphicEquiv N hN)
      ((lpsOriginalCompactRestrictedMeromorphicEquiv N hN).symm
        (lpsOriginalGeneratedRestrictionPolynomialAlgEquiv N hpos hN f)) = _
    exact RingEquiv.apply_symm_apply _ _
  rw [←he]
  change lpsOriginalCompactToRestrictedMeromorphic N hN
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f) = _
  rw [←hF]
  exact lpsOriginalCompactToRestrictedMeromorphic_apply N hN F

lemma lpsOriginalField_integral_iff_noInteriorPole (f : K) :
    IsIntegral P f ↔ ∀ x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ,
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f := by
  constructor
  · intro hi x
    exact lpsOriginalFieldLocalOrder_integral_nonnegative N hN hpos (Sum.inl x)
      (lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x) ⟨f,hi⟩
  · intro hno
    obtain ⟨F,hF⟩ := (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict_surjective
      (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f)
    have hn : letI := lpsOriginalFilledTopology N
        letI := lpsOriginalFilledChartedSpace N hN
        ∀ x : MulAction.orbitRel.Quotient
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ,
        0 ≤ meromorphicOrderAt (F.val ∘ (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N)).symm)
          (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N) (Sum.inl x)) := by
      let := lpsOriginalFilledTopology N
      let := lpsOriginalFilledChartedSpace N hN
      intro x
      have ho := hno x
      rw [lpsOriginalFieldLocalOrder_value,
        lpsOriginalFieldToLocal_representative N hN hpos (Sum.inl x) f F hF] at ho
      exact ho
    have hi := lpsOriginalFilledNoInteriorPole_integral N hN F.val F.property hn
    apply (isIntegral_algHom_iff (lpsOriginalGeneratedRestrictionPolynomialAlgEquiv N hpos hN).toAlgHom
      (lpsOriginalGeneratedRestrictionPolynomialAlgEquiv N hpos hN).injective).mp
    change IsIntegral P (lpsOriginalGeneratedRestrictionPolynomialAlgEquiv N hpos hN f)
    rwa [lpsOriginalGeneratedRestriction_representative N hpos hN f F hF]

end
end QEC.Coding.TannerLiftedProduct
