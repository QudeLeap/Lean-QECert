import QEC.Coding.ExpanderCodes.LPSOriginalFieldIntegral
import QEC.Coding.ExpanderCodes.LPSOriginalMeromorphicPoleClearing

/-!
# Finite interior fibres and negative orders in the original field

Faithful original polynomial-base inclusion makes j-a nonzero. At a genuine
interior point with j=a its actual analytic germ has positive finite order,
so its inverse is nonanalytic. Compact meromorphic nonanalytic loci bound
each interior j fibre and the negative interior orders of every original
field element. A sufficiently large natural power of a positive-order
element clears an arbitrary local negative order, also for all larger powers.

Derived internal closure on the PK22 ex:Xpq original LPS route, pinned
main.tex484–486. Raw cusp values are irrelevant to interior fibres, and raw
removable-singularity assignments need not themselves be analytic.
Parent #449 remains open; the public theorem and verified TeX are unchanged.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance lpsOriginalFiniteInteriorDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local instance lpsOriginalFiniteInteriorDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance lpsOriginalFiniteInteriorDictionary003 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance lpsOriginalFiniteInteriorDictionary004 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ

omit [NeZero N] in
lemma lpsOriginalFieldJ_sub_constant_ne_zero (a : ℂ) :
    algebraMap P K Polynomial.X - algebraMap ℂ K a ≠ 0 := by
  have hi : Function.Injective (algebraMap P K) :=
    (algebraMap J K).injective.comp (IsFractionRing.injective P J)
  have hc : algebraMap P K (Polynomial.C a) = algebraMap ℂ K a := rfl
  rw [←hc,←map_sub]
  exact fun hz => Polynomial.X_sub_C_ne_zero a (hi (hz.trans (map_zero _).symm))

lemma lpsOriginalFieldJ_sub_constant_order_pos (a : ℂ) (y : Q)
    (hy : lpsOriginalFilledJ N (Sum.inl y) = a) :
    0 < lpsOriginalFieldLocalOrder N hN hpos (Sum.inl y)
      (algebraMap P K Polynomial.X - algebraMap ℂ K a) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let e := lpsOriginalFilledInteriorChart N hN y
  let z := e (Sum.inl y)
  let f : ℂ → ℂ := fun w => lpsOriginalFilledJ N (e.symm w) - a
  have hs := lpsOriginalFilledInteriorChart_mem N hN y
  have ha : AnalyticAt ℂ f z :=
    (lpsOriginalFilledJ_interior_analytic N hN y z (e.map_source hs)).sub analyticAt_const
  have hv : f z = 0 := by dsimp only [f,z];rw [e.left_inv hs,hy,sub_self]
  rw [lpsOriginalFieldLocalOrder_value,map_sub,lpsOriginalFieldToLocal_j,
    lpsOriginalFieldToLocal_constant]
  change 0 < meromorphicOrderAt f z
  exact (tendsto_zero_iff_meromorphicOrderAt_pos ha.meromorphicAt).mp
    (by simpa only [hv] using ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

lemma lpsOriginalFieldLocalOrder_clear_power (x : LPSOriginalFilledCurve N) (a f : K)
    (ha : 0 < lpsOriginalFieldLocalOrder N hN hpos x a) (hane : a ≠ 0) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (a^m*f) := by
  let v := lpsOriginalFieldLocalOrder N hN hpos x
  by_cases hf : f = 0
  · refine ⟨0,fun m _ => ?_⟩
    simp only [hf,mul_zero,AddValuation.map_zero,le_top]
  have hfa := lpsOriginalFieldLocalOrder_ne_top N hN hpos x a hane
  have hff := lpsOriginalFieldLocalOrder_ne_top N hN hpos x f hf
  lift v a to ℤ using hfa with ka hka
  lift v f to ℤ using hff with kf hkf
  have ha' : 0 < v a := ha
  rw [←hka] at ha'
  have hap : 0 < ka := by exact_mod_cast ha'
  refine ⟨(-kf).toNat,fun m hm => ?_⟩
  have hmn : -kf ≤ (m : ℤ) := by omega
  have ham : (m : ℤ) ≤ (m : ℤ)*ka := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ ka by omega)
      (Int.natCast_nonneg m)
  have hi : 0 ≤ m • ka + kf := by rw [nsmul_eq_mul];omega
  change 0 ≤ v (a^m*f)
  rw [AddValuation.map_mul,AddValuation.map_pow,←hka,←hkf]
  exact_mod_cast hi

include hpos in
lemma lpsOriginalJFibre_inverse_not_analytic (a : ℂ) (y : Q)
    (hy : lpsOriginalFilledJ N (Sum.inl y) = a) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    ¬ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ((lpsOriginalFilledJ N - fun _ => a)⁻¹) (Sum.inl y) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let e := lpsOriginalFilledInteriorChart N hN y
  let z := e (Sum.inl y)
  let f : ℂ → ℂ := fun w => lpsOriginalFilledJ N (e.symm w) - a
  have hs := lpsOriginalFilledInteriorChart_mem N hN y
  have ha : AnalyticAt ℂ f z :=
    (lpsOriginalFilledJ_interior_analytic N hN y z (e.map_source hs)).sub analyticAt_const
  have hv : f z = 0 := by dsimp only [f,z];rw [e.left_inv hs,hy,sub_self]
  have hp : 0 < meromorphicOrderAt f z :=
    (tendsto_zero_iff_meromorphicOrderAt_pos ha.meromorphicAt).mp
      (by simpa only [hv] using ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hn := lpsOriginalFieldLocalOrder_ne_top N hN hpos (Sum.inl y)
    (algebraMap P K Polynomial.X - algebraMap ℂ K a) (lpsOriginalFieldJ_sub_constant_ne_zero N hpos a)
  rw [lpsOriginalFieldLocalOrder_value,map_sub,lpsOriginalFieldToLocal_j,
    lpsOriginalFieldToLocal_constant] at hn
  change meromorphicOrderAt f z ≠ ⊤ at hn
  lift meromorphicOrderAt f z to ℤ using hn with k hk
  have hkpos : 0 < k := by exact_mod_cast hp
  intro hbad
  have hchart : chartAt ℂ (Sum.inl y : LPSOriginalFilledCurve N) = e := rfl
  have hd := contMDiffAt_iff_source.mp hbad
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hd
  have hi : AnalyticAt ℂ f⁻¹ z := by
    have hc : ContDiffAt ℂ ω f⁻¹ z := by
      simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm,Set.range_id,Function.comp_def,id_eq,
        contDiffWithinAt_univ,hchart,Pi.inv_def,Pi.inv_apply,Pi.sub_apply,f,z,e] using hd
    exact hc.analyticAt
  have hnon : 0 ≤ meromorphicOrderAt f⁻¹ z :=
    hi.meromorphicAt.meromorphicOrderAt_nonneg_iff.mpr ⟨f⁻¹,hi,Filter.EventuallyEq.rfl⟩
  rw [meromorphicOrderAt_inv,←hk,←WithTop.LinearOrderedAddCommGroup.coe_neg] at hnon
  have : 0 ≤ -k := by exact_mod_cast hnon
  exact (not_le_of_gt (neg_neg_of_pos hkpos)) this

include hpos hN in
lemma lpsOriginalJFibre_finite (a : ℂ) :
    {y : Q | lpsOriginalFilledJ N (Sum.inl y) = a}.Finite := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  have hF := lpsOriginalFilledChartMeromorphic_inv N hN
    (lpsOriginalFilledChartMeromorphic_add N hN (lpsOriginalFilledChartMeromorphic_j N hN)
      (lpsOriginalFilledChartMeromorphic_neg N hN (lpsOriginalFilledChartMeromorphic_const N hN a)))
  have hbad := lpsOriginalFilledChartMeromorphic_finite_nonanalytic N hN _ hF
  exact (Set.Finite.preimage Sum.inl_injective.injOn hbad).subset
    (fun y hy => lpsOriginalJFibre_inverse_not_analytic N hpos hN a y hy)

end
end QEC.Coding.TannerLiftedProduct

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance lpsOriginalFiniteNegativeDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ

lemma lpsOriginalField_negativeInteriorOrders_finite (f : K) :
    {x : Q | lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f < 0}.Finite := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  obtain ⟨F,hF⟩ := (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict_surjective
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f)
  have hbad := lpsOriginalFilledChartMeromorphic_finite_nonanalytic N hN F.val F.property
  apply (Set.Finite.preimage Sum.inl_injective.injOn hbad).subset
  intro x hx
  change ¬ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F.val (Sum.inl x)
  intro ha
  have hd := contMDiffAt_iff_source.mp ha
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hd
  have hc : ContDiffAt ℂ ω (F.val ∘ (lpsOriginalLocalChart N hN (Sum.inl x)).symm)
      (lpsOriginalLocalChartCenter N hN (Sum.inl x)) := by
    simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm,Set.range_id,Function.comp_def,id_eq,
      contDiffWithinAt_univ,lpsOriginalLocalChart,lpsOriginalLocalChartCenter] using hd
  have hn : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f := by
    rw [lpsOriginalFieldLocalOrder_value,
      lpsOriginalFieldToLocal_representative N hN hpos (Sum.inl x) f F hF]
    exact hc.analyticAt.meromorphicAt.meromorphicOrderAt_nonneg_iff.mpr
      ⟨_,hc.analyticAt,Filter.EventuallyEq.rfl⟩
  exact (not_le_of_gt hx) hn

end
end QEC.Coding.TannerLiftedProduct
