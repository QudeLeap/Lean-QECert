import QEC.Coding.ExpanderCodes.LPSOriginalReciprocalNumerator
import QEC.Coding.ExpanderCodes.LPSOriginalJPowerPoleClearing

/-!
# Original reciprocal normalization is exactly actual no-pole functions

For arbitrary elements of the SAME original C(j,j_N), prove integrality over C[1/j] exactly when actual local orders are nonnegative at interior j-nonzero points and at every cusp. Construct the clearing power, modular numerator and field equality, then transfer its constructed monic equation. The converse follows from actual inverse-j orders and valuation integrality.

Derived internal PK22 ex:Xpq closure, pinned main.tex484–486, for parent #449.
Reciprocal point coverage, global differential/sheaf comparison, good reduction,
Hecke/Frobenius/Weil and the public quantum-family theorem remain further work.
-/

namespace QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local instance lpsOriginalReciprocalTransferDictionary001 :
    Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => LPSOriginalHolomorphicRing
local notation "H" => LPSOriginalHolomorphicFractionField
local instance lpsOriginalReciprocalTransferDictionary002 : Algebra P K :=
  ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance lpsOriginalReciprocalTransferDictionary003 : Algebra ℂ K :=
  ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance lpsOriginalReciprocalTransferDictionary004 : IsScalarTower ℂ P K :=
  .of_algebraMap_eq' rfl

omit [NeZero N] in
/-- The existing reciprocal polynomial map commutes with inclusion into the actual holomorphic fraction field. -/
lemma lpsOriginalReciprocalPolynomial_field_embedding :
    (lpsOriginalGeneratedFunctionField N hpos).val.toRingHom.comp
      (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos) =
    Polynomial.eval₂RingHom ((algebraMap R H).comp (algebraMap ℂ R))
      (algebraMap R H lpsOriginalJHolomorphic)⁻¹ := by
  let ψ : K →+* H := (lpsOriginalGeneratedFunctionField N hpos).val.toRingHom
  let γ : ℂ →+* H := (algebraMap R H).comp (algebraMap ℂ R)
  have hzero : ψ.comp (algebraMap P K) =
      (algebraMap R H).comp lpsOriginalJHolomorphicEval.toRingHom := by
    apply RingHom.ext
    intro p
    exact lpsOriginalJFractionEmbedding_polynomial p
  have hscalar (c : ℂ) : ψ (algebraMap ℂ K c) = γ c := by
    have h := RingHom.congr_fun hzero (Polynomial.C c)
    change ψ (algebraMap P K (Polynomial.C c)) =
      algebraMap R H (Polynomial.aeval lpsOriginalJHolomorphic (Polynomial.C c)) at h
    rw [Polynomial.aeval_C] at h
    simpa only [γ, RingHom.comp_apply, Polynomial.C_eq_algebraMap,
      ←IsScalarTower.algebraMap_apply ℂ P K] using h
  have hj : ψ (algebraMap P K Polynomial.X) =
      algebraMap R H lpsOriginalJHolomorphic := by
    have h := RingHom.congr_fun hzero Polynomial.X
    change ψ (algebraMap P K Polynomial.X) =
      algebraMap R H (Polynomial.aeval lpsOriginalJHolomorphic Polynomial.X) at h
    simpa only [Polynomial.aeval_X] using h
  apply RingHom.ext
  intro p
  change ψ ((lpsOriginalReciprocalComplexFieldPolynomialMap N hpos) p) = _
  rw [lpsOriginalReciprocalFieldPolynomialMap_eval,
    Polynomial.hom_eval₂, map_inv₀, hj]
  have hγ : ψ.comp (algebraMap ℂ K) = γ := RingHom.ext hscalar
  rw [hγ]
  rfl

/-- A literal SAME-field E4 ratio is integral by the constructed reciprocal monic equation. -/
lemma lpsOriginalE4Ratio_reciprocal_integral
    (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) (f : K)
    (hratio : (lpsOriginalGeneratedFunctionField N hpos).val f =
      (algebraMap R H (lpsOriginalLevelFormHolomorphic N k A)) /
        (algebraMap R H (lpsOriginalE4PowerHolomorphic k))) :
    (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).IsIntegralElem f := by
  let ψ : K →+* H := (lpsOriginalGeneratedFunctionField N hpos).val.toRingHom
  apply RingHom.IsIntegralElem.of_map (g := ψ)
    (show Function.Injective ψ from Subtype.val_injective)
  rw [lpsOriginalReciprocalPolynomial_field_embedding]
  refine ⟨lpsOriginalReciprocalE4MonicEquation N k A,
    lpsOriginalReciprocalE4MonicEquation_monic N k A, ?_⟩
  rw [show ψ f = _ from hratio]
  exact lpsOriginalE4Ratio_reciprocal_field_root N k A

end
end QEC.Coding.TannerLiftedProduct


namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance lpsOriginalReciprocalCriterionDictionary001 :
    Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => LPSOriginalHolomorphicRing
local notation "H" => LPSOriginalHolomorphicFractionField
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local notation "C" => CuspOrbits
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
local instance lpsOriginalReciprocalCriterionDictionary002 : Algebra P K :=
  ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance lpsOriginalReciprocalCriterionDictionary003 : Algebra ℂ K :=
  ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance lpsOriginalReciprocalCriterionDictionary004 : IsScalarTower ℂ P K :=
  .of_algebraMap_eq' rfl

/-- Normalization retains the genuine compact meromorphic field class. -/
lemma lpsOriginalNormalizedFilledFunction_compact_germ
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    lpsOriginalCompactMeromorphicGermAlgHom N hN
      ⟨lpsOriginalNormalizedFilledFunction N hN F,
        lpsOriginalNormalizedFilledFunction_meromorphic N hN F hF⟩ =
      lpsOriginalCompactMeromorphicGermAlgHom N hN ⟨F,hF⟩ := by
  apply lpsOriginalCompactToRestrictedMeromorphic_injective N hN
  change lpsOriginalCompactToRestrictedMeromorphic N hN
    ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict _) =
      lpsOriginalCompactToRestrictedMeromorphic N hN
        ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict _)
  rw [lpsOriginalCompactToRestrictedMeromorphic_apply,
    lpsOriginalCompactToRestrictedMeromorphic_apply,
    lpsOriginalNormalizedFilledFunction_restriction N hN F hF]

/-- The constructed normalized product represents the SAME field element j-power times f. -/
lemma lpsOriginalReciprocalClearedRepresentative_compact_germ
    (f : K) (F : LPSOriginalFilledMeromorphicFunctionRing N hN)
    (hF : lpsOriginalCompactMeromorphicGermAlgHom N hN F =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f) (k : ℕ) :
    lpsOriginalCompactMeromorphicGermAlgHom N hN
      (lpsOriginalReciprocalClearedRepresentative N hN F.val F.property k) =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN
        ((algebraMap P K Polynomial.X)^k*f) := by
  change lpsOriginalCompactMeromorphicGermAlgHom N hN
    ((⟨lpsOriginalFilledJ N,lpsOriginalFilledChartMeromorphic_j N hN⟩ :
      LPSOriginalFilledMeromorphicFunctionRing N hN)^k *
      ⟨lpsOriginalNormalizedFilledFunction N hN F.val,
        lpsOriginalNormalizedFilledFunction_meromorphic N hN F.val F.property⟩) = _
  rw [map_mul, map_pow,
    lpsOriginalNormalizedFilledFunction_compact_germ N hN F.val F.property, hF,
    ←lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv_j N hpos hN]
  rw [map_mul, map_pow]

/-- Actual reciprocal-regular local orders construct an E4 numerator and prove SAME C[1/j] integrality. -/
lemma lpsOriginalField_reciprocal_integral_of_noPole
    (f : K)
    (hi : ∀ x : Q, lpsOriginalFilledJ N (Sum.inl x) ≠ 0 →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f)
    (hc : ∀ c : C, 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inr c) f) :
    (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).IsIntegralElem f := by
  obtain ⟨F,hF⟩ := (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict_surjective
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f)
  obtain ⟨k,hk⟩ := lpsOriginalField_j_power_clear_interior N hpos hN f hi
  have hcF : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ c : C, 0 ≤ meromorphicOrderAt
        (F.val ∘ (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N) (Sum.inr c)) := by
    let := lpsOriginalFilledTopology N
    let := lpsOriginalFilledChartedSpace N hN
    intro c
    have ho := hc c
    rw [lpsOriginalFieldLocalOrder_value,
      lpsOriginalFieldToLocal_representative N hN hpos (Sum.inr c) f F hF] at ho
    exact ho
  let G := lpsOriginalReciprocalClearedRepresentative N hN F.val F.property k
  have hG := lpsOriginalReciprocalClearedRepresentative_compact_germ
    N hpos hN f F hF k
  have hiG : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ x : Q, 0 ≤ meromorphicOrderAt
        (G.val ∘ (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N) (Sum.inl x)) := by
    let := lpsOriginalFilledTopology N
    let := lpsOriginalFilledChartedSpace N hN
    intro x
    have ho := hk x
    rw [lpsOriginalFieldLocalOrder_value,
      lpsOriginalFieldToLocal_representative N hN hpos (Sum.inl x)
        ((algebraMap P K Polynomial.X)^k*f) G hG] at ho
    exact ho
  let A := lpsOriginalReciprocalNumeratorModularForm N hN F.val F.property hcF k hiG
  have hnum := lpsOriginalReciprocalNumerator_germ_identity
    N hN F.val F.property hcF k hiG
  have hres := congrArg Subtype.val
    (lpsOriginalGeneratedRestriction_representative N hpos hN f F hF)
  change lpsOriginalHolomorphicFractionToMeromorphicGerm f.val =
    (lpsOriginalFilledMeromorphicRestriction N hN F.val F.property).val at hres
  have hB : algebraMap R H (lpsOriginalE4PowerHolomorphic k) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R H).ne
      (lpsOriginalE4PowerHolomorphic_ne_zero k)
  apply lpsOriginalE4Ratio_reciprocal_integral N hpos k A f
  apply (eq_div_iff hB).mpr
  apply lpsOriginalHolomorphicFractionToMeromorphicGerm_injective
  rw [map_mul, lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic,
    lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic]
  change lpsOriginalHolomorphicFractionToMeromorphicGerm f.val * _ = _
  rw [hres]
  exact (mul_comm _ _).trans hnum.symm

/-- At interior points where actual j is nonzero its inverse has nonnegative germ order. -/
lemma lpsOriginalFieldJ_inverse_interior_order_nonnegative
    (x : Q) (hx : lpsOriginalFilledJ N (Sum.inl x) ≠ 0) :
    0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x)
      (algebraMap P K Polynomial.X)⁻¹ := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let e := lpsOriginalFilledInteriorChart N hN x
  let z := e (Sum.inl x)
  have hs := lpsOriginalFilledInteriorChart_mem N hN x
  have ha := lpsOriginalFilledJ_interior_analytic N hN x z (e.map_source hs)
  have hz : lpsOriginalFilledJ N (e.symm z) ≠ 0 := by
    dsimp only [z]
    rwa [e.left_inv hs]
  have ho := (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero ha.meromorphicAt).mp
    ⟨_, hz, ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩
  rw [AddValuation.map_inv]
  have hj : lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x)
      (algebraMap P K Polynomial.X) = 0 := by
    rw [lpsOriginalFieldLocalOrder_value, lpsOriginalFieldToLocal_j]
    exact ho
  rw [hj, neg_zero]

/-- The actual negative width order of j makes its inverse regular at every original cusp. -/
lemma lpsOriginalFieldJ_inverse_cusp_order_nonnegative (c : C) :
    0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inr c)
      (algebraMap P K Polynomial.X)⁻¹ := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  have hj : lpsOriginalFieldLocalOrder N hN hpos (Sum.inr c)
      (algebraMap P K Polynomial.X) =
        (-(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c) : ℤ) : WithTop ℤ) := by
    rw [lpsOriginalFieldLocalOrder_value, lpsOriginalFieldToLocal_j]
    change meromorphicOrderAt
      (lpsOriginalFilledJ N ∘ (lpsOriginalFilledCuspChart N c).symm)
      (lpsOriginalFilledCuspChart N c (Sum.inr c)) = _
    rw [lpsOriginalFilledCuspChart_cusp]
    exact lpsOriginalFilledJ_cusp_order N c
  rw [AddValuation.map_inv, hj]
  simp

/-- SAME reciprocal-base integrality is equivalent to actual no-pole orders at interior j-nonzero points and all cusps. -/
lemma lpsOriginalField_reciprocal_integral_iff_noPole (f : K) :
    (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).IsIntegralElem f ↔
      (∀ x : Q, lpsOriginalFilledJ N (Sum.inl x) ≠ 0 →
        0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f) ∧
      (∀ c : C, 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inr c) f) := by
  constructor
  · intro hf
    have hp (x : LPSOriginalFilledCurve N)
        (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x
          (algebraMap P K Polynomial.X)⁻¹) :
        0 ≤ lpsOriginalFieldLocalOrder N hN hpos x f :=
      nonnegative_of_integral_map (lpsOriginalFieldLocalOrder N hN hpos x)
        (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos)
        (lpsOriginalReciprocalFieldPolynomialMap_order_nonnegative N hpos hN x hj) hf
    exact ⟨fun x hx => hp (Sum.inl x)
      (lpsOriginalFieldJ_inverse_interior_order_nonnegative N hpos hN x hx),
      fun c => hp (Sum.inr c)
        (lpsOriginalFieldJ_inverse_cusp_order_nonnegative N hpos hN c)⟩
  · rintro ⟨hi,hc⟩
    exact lpsOriginalField_reciprocal_integral_of_noPole N hpos hN f hi hc

end
end QEC.Coding.TannerLiftedProduct
