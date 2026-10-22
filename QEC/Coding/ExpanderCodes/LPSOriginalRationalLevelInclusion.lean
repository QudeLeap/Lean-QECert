/-
Rational level inclusion for the same original modular function fields.

Finite original polynomial supports and the actual nome Taylor identity
construct rational coefficients and a nonzero denominator. A Q-linear
retraction is applied only to finite sums and rational-series convolution;
analytic uniqueness recovers the original holomorphic fraction identity.
The genuine rational inclusion then supplies the degree tower: relative
degree equals the integral Gamma0 index, the full filled fibre cardinality
over every interior point, and p+1 at a coprime prime extension.

These are derived internal APIs for the original analytic modular-curve route.
The pinned PK22 main.tex passages th:qLDPC (lines 231-238) and ex:Xpq
(lines 484-486) retain their scope. The asymptotically good qLDPC main
theorem, algebraic good reduction and finite-field spectral route remain
unproved by this slice.
-/

import QEC.Coding.ExpanderCodes.LPSOriginalFullFieldLevelPullback
import QEC.Coding.ExpanderCodes.LPSOriginalRationalModularEquation
import QEC.Coding.ExpanderCodes.LPSOriginalRationalFunctionField
import QEC.Coding.ExpanderCodes.LPSOriginalRelativeFunctionFieldDegree
import QEC.Coding.ExpanderCodes.LPSOriginalIntegerModularEquation

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

/-- Q-linearity commutes with genuine rational-series convolution, not arbitrary products. -/
lemma lpsOriginalRationalSeriesRetraction_mul_map
    (S : PowerSeries ℂ) (T : PowerSeries ℚ) :
    lpsOriginalRationalSeriesRetraction
      (S * PowerSeries.map (algebraMap ℚ ℂ) T) =
        lpsOriginalRationalSeriesRetraction S * T := by
  ext n
  simp only [lpsOriginalRationalSeriesRetraction, PowerSeries.coeff_mk,
    PowerSeries.coeff_mul, PowerSeries.coeff_map, eq_ratCast]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [mul_comm (S.coeff p.1), lpsOriginalRationalRetraction_rat_mul, mul_comm]

/-- Literal evaluation into the actual original holomorphic ring. -/
def lpsOriginalBivariateHolomorphicEval (M : ℕ) (hM : 0 < M) :
    Polynomial (Polynomial ℂ) →+* LPSOriginalHolomorphicRing :=
  Polynomial.eval₂RingHom lpsOriginalJHolomorphicEval.toRingHom
    (lpsOriginalJNHolomorphic M hM)

/-- Every element of the genuine original generated field has an actual polynomial fraction with nonzero evaluated denominator. -/
lemma lpsOriginalGeneratedFunctionField_bivariateFraction
    (M : ℕ) (hM : 0 < M) (x : LPSOriginalHolomorphicFractionField)
    (hx : x ∈ lpsOriginalGeneratedFunctionField M hM) :
    ∃ G H : Polynomial (Polynomial ℂ),
      lpsOriginalBivariateHolomorphicEval M hM H ≠ 0 ∧
      x = algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
          (lpsOriginalBivariateHolomorphicEval M hM G) /
        algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
          (lpsOriginalBivariateHolomorphicEval M hM H) := by
  classical
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let e := lpsOriginalBivariateHolomorphicEval M hM
  let ι := algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
  have hC (P : Polynomial ℂ) : e (Polynomial.C P) = lpsOriginalJHolomorphicEval P := by
    simp only [e, lpsOriginalBivariateHolomorphicEval, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C]
    rfl
  have hX : e Polynomial.X = lpsOriginalJNHolomorphic M hM := by
    simp only [e, lpsOriginalBivariateHolomorphicEval, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X]
  have hι := IsFractionRing.injective LPSOriginalHolomorphicRing
    LPSOriginalHolomorphicFractionField
  change x ∈ IntermediateField.adjoin (FractionRing (Polynomial ℂ))
    {lpsOriginalJNInFractionField M hM} at hx
  change ∃ G H : Polynomial (Polynomial ℂ), e H ≠ 0 ∧ x = ι (e G) / ι (e H)
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
      have he : x = lpsOriginalJNInFractionField M hM := Set.mem_singleton_iff.mp hx
      subst x
      refine ⟨Polynomial.X, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
      simp only [hX, map_one, div_one]
      rfl
  | algebraMap a =>
      obtain ⟨A, B, hB, hAB⟩ := IsFractionRing.div_surjective (Polynomial ℂ) a
      refine ⟨Polynomial.C A, Polynomial.C B, ?_, ?_⟩
      · rw [hC]
        exact fun h => (mem_nonZeroDivisors_iff_ne_zero.mp hB)
          (lpsOriginalJHolomorphicEval_injective (h.trans (map_zero _).symm))
      · change lpsOriginalJFractionEmbedding a = ι (e (Polynomial.C A)) / ι (e (Polynomial.C B))
        rw [hC, hC, ← hAB, map_div₀,
          lpsOriginalJFractionEmbedding_polynomial,
          lpsOriginalJFractionEmbedding_polynomial]
  | add x y hx hy ihx ihy =>
      obtain ⟨G, H, hH, rfl⟩ := ihx
      obtain ⟨A, B, hB, rfl⟩ := ihy
      refine ⟨G * B + A * H, H * B, ?_, ?_⟩
      · simpa only [map_mul] using mul_ne_zero hH hB
      · simp only [map_add, map_mul]
        have hH' : ι (e H) ≠ 0 := fun h => hH (hι (h.trans (map_zero ι).symm))
        have hB' : ι (e B) ≠ 0 := fun h => hB (hι (h.trans (map_zero ι).symm))
        change ι (e G) / ι (e H) + ι (e A) / ι (e B) =
          (ι (e G) * ι (e B) + ι (e A) * ι (e H)) / (ι (e H) * ι (e B))
        rw [div_add_div _ _ hH' hB', mul_comm (ι (e H)) (ι (e A))]
  | inv x hx ih =>
      obtain ⟨G, H, hH, rfl⟩ := ih
      by_cases hG : e G = 0
      · refine ⟨0, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
        simp only [hG, map_zero, zero_div, inv_zero]
      · refine ⟨H, G, hG, ?_⟩
        exact inv_div _ _
  | mul x y hx hy ihx ihy =>
      obtain ⟨G, H, hH, rfl⟩ := ihx
      obtain ⟨A, B, hB, rfl⟩ := ihy
      refine ⟨G * A, H * B, ?_, ?_⟩
      · simpa only [map_mul] using mul_ne_zero hH hB
      · simp only [map_mul]
        exact div_mul_div_comm _ _ _ _


lemma lpsOriginalClearedCusp_pullback_of_bound
    (M : ℕ) (hM : 0 < M) (B : ℕ)
    (P : Polynomial (Polynomial ℂ))
    (hB : lpsOriginalClearingBound M P ≤ B) (τ : ℍ) :
    lpsOriginalClearedCusp M B P (Function.Periodic.qParam 1 (τ : ℂ)) =
      (Function.Periodic.qParam 1 (τ : ℂ)) ^ B *
        P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
          (lpsOriginalJDilated M hM τ) := by
  classical
  simp only [lpsOriginalClearedCusp, Finset.sum_apply, Polynomial.eval₂_eq_sum,
    Polynomial.coe_evalRingHom, Polynomial.eval_eq_sum, Polynomial.sum_def,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  rw [lpsOriginalClearedMonomial_pullback M hM B i k
    ((lpsOriginalClearingBound_le M P hk hi).trans hB)]
  ring

/-- Zero nome germ plus constructed actual pullback forces actual holomorphic zero. -/
lemma lpsOriginalHolomorphic_zero_of_clearedNomeGerm
    (F : LPSOriginalHolomorphicRing) (G : ℂ → ℂ) (B : ℕ)
    (hg : G =ᶠ[𝓝 (0 : ℂ)] 0)
    (hp : ∀ τ : ℍ, G (Function.Periodic.qParam 1 (τ : ℂ)) =
      (Function.Periodic.qParam 1 (τ : ℂ)) ^ B * F.val τ) :
    F = 0 := by
  obtain ⟨s, hs, hopen, h0⟩ := eventually_nhds_iff.mp hg
  obtain ⟨τ, hτ⟩ : ∃ τ : ℍ, Function.Periodic.qParam 1 (τ : ℂ) ∈ s :=
    ((UpperHalfPlane.qParam_tendsto_atImInfty
      (by norm_num : (0 : ℝ) < 1)).eventually
        (hopen.mem_nhds h0)).exists
  have hnear : ∀ᶠ z : ℍ in 𝓝 τ,
      Function.Periodic.qParam 1 (z : ℂ) ∈ s :=
    ((Function.Periodic.continuous_qParam.comp
      UpperHalfPlane.continuous_coe).continuousAt.tendsto).eventually
        (hopen.mem_nhds hτ)
  have hzero : ∀ᶠ z : ℍ in 𝓝 τ, F.val z = 0 := by
    filter_upwards [hnear] with z hz
    have h := hs _ hz
    change G (Function.Periodic.qParam 1 (z : ℂ)) = 0 at h
    rw [hp] at h
    exact (mul_eq_zero.mp h).resolve_left
      (pow_ne_zero _ (Function.Periodic.qParam_ne_zero _))
  apply Subtype.ext
  exact UpperHalfPlane.eq_zero_of_frequently F.property
    ((hzero.filter_mono nhdsWithin_le_nhds).frequently)


lemma lpsOriginalBivariateHolomorphicEval_apply
    (M : ℕ) (hM : 0 < M) (P : Polynomial (Polynomial ℂ)) (τ : ℍ) :
    (lpsOriginalBivariateHolomorphicEval M hM P).val τ =
      P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
        (lpsOriginalJDilated M hM τ) := by
  let ev : LPSOriginalHolomorphicRing →+* ℂ :=
    { toFun f := f.val τ
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hc : ev.comp lpsOriginalJHolomorphicEval.toRingHom =
      Polynomial.evalRingHom (lpsOriginalJInvariant τ) := by
    apply RingHom.ext
    intro Q
    exact lpsOriginalJHolomorphicEval_apply Q τ
  have h := Polynomial.hom_eval₂ P lpsOriginalJHolomorphicEval.toRingHom ev
    (lpsOriginalJNHolomorphic M hM)
  rw [hc] at h
  exact h


lemma lpsOriginalClearedCusp_taylor_ne_zero_of_original_denominator
    (M : ℕ) (hM : 0 < M) (B : ℕ) (P : Polynomial (Polynomial ℂ))
    (hB : lpsOriginalClearingBound M P ≤ B)
    (hP : lpsOriginalBivariateHolomorphicEval M hM P ≠ 0) :
    lpsOriginalTaylorSeries (lpsOriginalClearedCusp M B P) ≠ 0 := by
  intro hz
  have hg : lpsOriginalClearedCusp M B P =ᶠ[𝓝 (0 : ℂ)] 0 :=
    (lpsOriginalTaylorSeries_zero_iff_germ
      (lpsOriginalClearedCusp_analytic M (Nat.ne_of_gt hM) B P)).mp hz
  apply hP
  apply lpsOriginalHolomorphic_zero_of_clearedNomeGerm
    (lpsOriginalBivariateHolomorphicEval M hM P)
    (lpsOriginalClearedCusp M B P) B hg
  intro τ
  rw [lpsOriginalBivariateHolomorphicEval_apply]
  exact lpsOriginalClearedCusp_pullback_of_bound M hM B P hB τ


lemma lpsOriginalRationalSeries_finiteFraction_descent
    {ι : Type*} [Fintype ι]
    (A U : PowerSeries ℚ) (T : ι → PowerSeries ℚ) (a b : ι → ℂ)
    (h : PowerSeries.map (algebraMap ℚ ℂ) A *
          (∑ i, PowerSeries.C (a i) * PowerSeries.map (algebraMap ℚ ℂ) (T i)) =
        PowerSeries.map (algebraMap ℚ ℂ) U *
          (∑ i, PowerSeries.C (b i) * PowerSeries.map (algebraMap ℚ ℂ) (T i)))
    (hS : (∑ i, PowerSeries.C (b i) *
      PowerSeries.map (algebraMap ℚ ℂ) (T i)) ≠ 0) :
    ∃ aq bq : ι → ℚ,
      A * (∑ i, PowerSeries.C (aq i) * T i) =
        U * (∑ i, PowerSeries.C (bq i) * T i) ∧
      (∑ i, PowerSeries.C (bq i) * T i) ≠ 0 := by
  classical
  let R : PowerSeries ℂ := ∑ i, PowerSeries.C (a i) *
    PowerSeries.map (algebraMap ℚ ℂ) (T i)
  let S : PowerSeries ℂ := ∑ i, PowerSeries.C (b i) *
    PowerSeries.map (algebraMap ℚ ℂ) (T i)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, S.coeff n ≠ 0 := by
    by_contra! hh
    apply hS
    change S = 0
    ext n
    simpa only [map_zero] using hh n
  let c : ℂ := (S.coeff n)⁻¹
  let aq : ι → ℚ := fun i => lpsOriginalRationalRetraction (c * a i)
  let bq : ι → ℚ := fun i => lpsOriginalRationalRetraction (c * b i)
  have transfer (v : ι → ℂ) :
      lpsOriginalRationalSeriesRetraction
          (PowerSeries.C c *
            (∑ i, PowerSeries.C (v i) *
              PowerSeries.map (algebraMap ℚ ℂ) (T i))) =
        ∑ i, PowerSeries.C (lpsOriginalRationalRetraction (c * v i)) * T i := by
    rw [Finset.mul_sum, lpsOriginalRationalSeriesRetraction_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← mul_assoc, ← map_mul, lpsOriginalRationalSeriesRetraction_C_mul_map]
  have hscaled :
      (PowerSeries.C c * R) * PowerSeries.map (algebraMap ℚ ℂ) A =
        (PowerSeries.C c * S) * PowerSeries.map (algebraMap ℚ ℂ) U := by
    have hc := congrArg (fun V : PowerSeries ℂ => PowerSeries.C c * V) h
    change PowerSeries.C c *
        (PowerSeries.map (algebraMap ℚ ℂ) A * R) =
      PowerSeries.C c *
        (PowerSeries.map (algebraMap ℚ ℂ) U * S) at hc
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hc
  have ht := congrArg lpsOriginalRationalSeriesRetraction hscaled
  rw [lpsOriginalRationalSeriesRetraction_mul_map,
    lpsOriginalRationalSeriesRetraction_mul_map] at ht
  have hR := transfer a
  have hB := transfer b
  change lpsOriginalRationalSeriesRetraction (PowerSeries.C c * R) =
    ∑ i, PowerSeries.C (aq i) * T i at hR
  change lpsOriginalRationalSeriesRetraction (PowerSeries.C c * S) =
    ∑ i, PowerSeries.C (bq i) * T i at hB
  rw [hR, hB] at ht
  refine ⟨aq, bq, by simpa only [mul_comm] using ht, ?_⟩
  intro hz
  have hcoef := congrArg (fun V : PowerSeries ℚ => V.coeff n) hB
  rw [hz, map_zero] at hcoef
  simp only [lpsOriginalRationalSeriesRetraction, PowerSeries.coeff_mk,
    PowerSeries.coeff_C_mul] at hcoef
  have hunit : c * S.coeff n = 1 := inv_mul_cancel₀ hn
  rw [hunit, lpsOriginalRationalRetraction_one] at hcoef
  exact one_ne_zero hcoef


/-- Finite rational coefficients evaluated at the original holomorphic j and jM. -/
def lpsOriginalRationalMonomialHolomorphicSum
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : 0 < M)
    (u v : ι → ℕ) (a : ι → ℚ) : LPSOriginalHolomorphicRing :=
  ∑ i, algebraMap ℚ LPSOriginalHolomorphicRing (a i) *
    lpsOriginalJHolomorphic ^ u i * lpsOriginalJNHolomorphic M hM ^ v i

lemma lpsOriginalRationalMonomialHolomorphicSum_apply
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : 0 < M)
    (u v : ι → ℕ) (a : ι → ℚ) (τ : ℍ) :
    (lpsOriginalRationalMonomialHolomorphicSum M hM u v a).val τ =
      ∑ i, (a i : ℂ) * lpsOriginalJInvariant τ ^ u i *
        lpsOriginalJDilated M hM τ ^ v i := by
  classical
  let ev : LPSOriginalHolomorphicRing →+* ℂ :=
    { toFun f := f.val τ
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  change ev (∑ i, algebraMap ℚ LPSOriginalHolomorphicRing (a i) *
    lpsOriginalJHolomorphic ^ u i * lpsOriginalJNHolomorphic M hM ^ v i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [map_mul, map_pow]
  rfl

/-- The same finite rational monomials after genuine cusp clearing. -/
def lpsOriginalFiniteClearedRationalSum
    {ι : Type*} [Fintype ι] (M B : ℕ) (u v : ι → ℕ) (a : ι → ℚ) : ℂ → ℂ :=
  ∑ i, fun q => (a i : ℂ) * lpsOriginalClearedMonomial M B (u i) (v i) q

lemma lpsOriginalFiniteClearedRationalSum_analytic
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : M ≠ 0)
    (B : ℕ) (u v : ι → ℕ) (a : ι → ℚ) :
    AnalyticAt ℂ (lpsOriginalFiniteClearedRationalSum M B u v a) 0 := by
  classical
  exact Finset.univ.analyticAt_sum fun i _hi =>
    analyticAt_const.mul (lpsOriginalClearedMonomial_analytic M hM B (u i) (v i))

lemma lpsOriginalFiniteClearedRationalSum_taylor
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : M ≠ 0)
    (B : ℕ) (u v : ι → ℕ) (a : ι → ℚ) :
    lpsOriginalTaylorSeries (lpsOriginalFiniteClearedRationalSum M B u v a) =
      PowerSeries.map (algebraMap ℚ ℂ)
        (∑ i, PowerSeries.C (a i) * lpsOriginalClearedFormalMonomial M hM B (u i) (v i)) := by
  classical
  unfold lpsOriginalFiniteClearedRationalSum
  rw [lpsOriginalTaylorSeries_sum Finset.univ
    (fun i => fun q => (a i : ℂ) * lpsOriginalClearedMonomial M B (u i) (v i) q)
    (fun i _hi => analyticAt_const.mul
      (lpsOriginalClearedMonomial_analytic M hM B (u i) (v i)))]
  simp only [map_sum, map_mul, PowerSeries.map_C]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [lpsOriginalTaylorSeries_const_mul, lpsOriginalClearedMonomial_taylor M hM]
  rfl

lemma lpsOriginalFiniteClearedRationalSum_pullback
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : 0 < M)
    (B : ℕ) (u v : ι → ℕ) (a : ι → ℚ)
    (hB : ∀ i, u i + M * v i ≤ B) (τ : ℍ) :
    lpsOriginalFiniteClearedRationalSum M B u v a
        (Function.Periodic.qParam 1 (τ : ℂ)) =
      (Function.Periodic.qParam 1 (τ : ℂ)) ^ B *
        (lpsOriginalRationalMonomialHolomorphicSum M hM u v a).val τ := by
  classical
  rw [lpsOriginalRationalMonomialHolomorphicSum_apply]
  simp only [lpsOriginalFiniteClearedRationalSum, Finset.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [lpsOriginalClearedMonomial_pullback M hM B (u i) (v i) (hB i)]
  ring

lemma lpsOriginalJHolomorphicEvalQ_C (a : ℚ) :
    lpsOriginalJHolomorphicEvalQ (Polynomial.C a) =
      algebraMap ℚ LPSOriginalHolomorphicRing a := by
  apply Subtype.ext
  funext τ
  rw [lpsOriginalJHolomorphicEvalQ_apply, Polynomial.eval₂_C]
  rfl

lemma lpsOriginalJHolomorphicEvalQ_X :
    lpsOriginalJHolomorphicEvalQ Polynomial.X = lpsOriginalJHolomorphic := by
  apply Subtype.ext
  funext τ
  rw [lpsOriginalJHolomorphicEvalQ_apply, Polynomial.eval₂_X]
  rfl

lemma lpsOriginalRationalMonomialHolomorphicSum_mem
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : 0 < M)
    (u v : ι → ℕ) (a : ι → ℚ) :
    algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
      (lpsOriginalRationalMonomialHolomorphicSum M hM u v a) ∈
        lpsOriginalGeneratedFunctionFieldQ M hM := by
  classical
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let F := lpsOriginalGeneratedFunctionFieldQ M hM
  let holoMap := algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
  have hpoly (P : Polynomial ℚ) : holoMap (lpsOriginalJHolomorphicEvalQ P) ∈ F := by
    rw [← lpsOriginalJFractionEmbeddingQ_polynomial]
    exact F.algebraMap_mem _
  have hj : holoMap lpsOriginalJHolomorphic ∈ F := by
    rw [← lpsOriginalJHolomorphicEvalQ_X]
    exact hpoly Polynomial.X
  have hJM : holoMap (lpsOriginalJNHolomorphic M hM) ∈ F := by
    exact IntermediateField.subset_adjoin (FractionRing (Polynomial ℚ)) _ (Set.mem_singleton _)
  change holoMap (∑ i, algebraMap ℚ LPSOriginalHolomorphicRing (a i) *
    lpsOriginalJHolomorphic ^ u i * lpsOriginalJNHolomorphic M hM ^ v i) ∈ F
  simp only [map_sum, map_mul, map_pow]
  apply F.sum_mem
  intro i _hi
  apply F.mul_mem
  · apply F.mul_mem
    · rw [← lpsOriginalJHolomorphicEvalQ_C]
      exact hpoly (Polynomial.C (a i))
    · exact pow_mem hj (u i)
  · exact pow_mem hJM (v i)

lemma lpsOriginalZeroGerm_of_puncturedDisk
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hz : ∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 → f q = 0) :
    f =ᶠ[𝓝 0] 0 := by
  have hsmall : ∀ᶠ q : ℂ in 𝓝 0, ‖q‖ < 1 :=
    (isOpen_lt (continuous_norm : Continuous (fun q : ℂ => ‖q‖))
      continuous_const).mem_nhds (by norm_num : ‖(0 : ℂ)‖ < 1)
  have hp : f =ᶠ[𝓝[≠] (0 : ℂ)] 0 := by
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with q hq hq0
    exact hz q hq hq0
  have h0 : f 0 = 0 := tendsto_nhds_unique_of_eventuallyEq
    (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) tendsto_const_nhds hp
  filter_upwards [hsmall] with q hq
  by_cases hq0 : q = 0
  · subst q
    exact h0
  · exact hz q hq hq0

lemma lpsOriginalFiniteClearedRationalSum_formal_ne_zero
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : 0 < M)
    (B : ℕ) (u v : ι → ℕ) (a : ι → ℚ)
    (hB : ∀ i, u i + M * v i ≤ B)
    (hs : (∑ i, PowerSeries.C (a i) *
      lpsOriginalClearedFormalMonomial M (Nat.ne_of_gt hM) B (u i) (v i)) ≠ 0) :
    lpsOriginalRationalMonomialHolomorphicSum M hM u v a ≠ 0 := by
  intro hz
  have hg : lpsOriginalFiniteClearedRationalSum M B u v a =ᶠ[𝓝 0] 0 := by
    apply lpsOriginalZeroGerm_of_puncturedDisk
      (lpsOriginalFiniteClearedRationalSum_analytic M (Nat.ne_of_gt hM) B u v a)
    intro q hq hq0
    let τ : ℍ := ⟨Function.Periodic.invQParam 1 q,
      Function.Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num) hq hq0⟩
    have hqτ : Function.Periodic.qParam 1 (τ : ℂ) = q :=
      Function.Periodic.qParam_right_inv (by norm_num) hq0
    rw [← hqτ, lpsOriginalFiniteClearedRationalSum_pullback M hM B u v a hB τ, hz]
    exact mul_zero _
  have ht := (lpsOriginalTaylorSeries_zero_iff_germ
    (lpsOriginalFiniteClearedRationalSum_analytic M (Nat.ne_of_gt hM) B u v a)).mpr hg
  rw [lpsOriginalFiniteClearedRationalSum_taylor M (Nat.ne_of_gt hM)] at ht
  apply hs
  exact PowerSeries.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
    (ht.trans (map_zero _).symm)

/-- Actual rational finite-series equation recovers the original jN in Q(j,jM). -/
lemma lpsOriginalJN_mem_Q_of_finiteRationalSeriesEquation
    {ι : Type*} [Fintype ι] (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (B : ℕ) (u v : ι → ℕ) (a b : ι → ℚ)
    (hB : ∀ i, u i + M * v i ≤ B)
    (h :
      PowerSeries.X ^ N * (∑ i, PowerSeries.C (a i) *
        lpsOriginalClearedFormalMonomial M (Nat.ne_of_gt hM) B (u i) (v i)) =
      PowerSeries.expand N (Nat.ne_of_gt hN) lpsOriginalJQSeries *
        (∑ i, PowerSeries.C (b i) *
          lpsOriginalClearedFormalMonomial M (Nat.ne_of_gt hM) B (u i) (v i)))
    (hb : (∑ i, PowerSeries.C (b i) *
      lpsOriginalClearedFormalMonomial M (Nat.ne_of_gt hM) B (u i) (v i)) ≠ 0) :
    lpsOriginalJNInFractionField N hN ∈ lpsOriginalGeneratedFunctionFieldQ M hM := by
  classical
  let Ga := lpsOriginalFiniteClearedRationalSum M B u v a
  let Gb := lpsOriginalFiniteClearedRationalSum M B u v b
  let Ha := lpsOriginalRationalMonomialHolomorphicSum M hM u v a
  let Hb := lpsOriginalRationalMonomialHolomorphicSum M hM u v b
  let KN : ℂ → ℂ := fun q => lpsOriginalJQCoefficient (q ^ N)
  have ha0 : AnalyticAt ℂ Ga 0 :=
    lpsOriginalFiniteClearedRationalSum_analytic M (Nat.ne_of_gt hM) B u v a
  have hb0 : AnalyticAt ℂ Gb 0 :=
    lpsOriginalFiniteClearedRationalSum_analytic M (Nat.ne_of_gt hM) B u v b
  have hKN : AnalyticAt ℂ KN 0 :=
    lpsOriginalJQCoefficient_analytic_zero.comp_of_eq
      (lpsOriginalPower_analytic N) (zero_pow (Nat.ne_of_gt hN))
  let D := KN * Gb - (fun q : ℂ => q ^ N) * Ga
  have hD : AnalyticAt ℂ D 0 := (hKN.mul hb0).sub ((lpsOriginalPower_analytic N).mul ha0)
  have hT : lpsOriginalTaylorSeries D = 0 := by
    rw [lpsOriginalTaylorSeries_sub (hKN.mul hb0) ((lpsOriginalPower_analytic N).mul ha0),
      lpsOriginalTaylorSeries_mul hKN hb0,
      lpsOriginalTaylorSeries_mul (lpsOriginalPower_analytic N) ha0,
      lpsOriginalTaylorSeries_qpow]
    change lpsOriginalTaylorSeries KN * lpsOriginalTaylorSeries
      (lpsOriginalFiniteClearedRationalSum M B u v b) -
        PowerSeries.X ^ N * lpsOriginalTaylorSeries
          (lpsOriginalFiniteClearedRationalSum M B u v a) = 0
    rw [lpsOriginalFiniteClearedRationalSum_taylor M (Nat.ne_of_gt hM),
      lpsOriginalFiniteClearedRationalSum_taylor M (Nat.ne_of_gt hM)]
    change lpsOriginalTaylorSeries (fun q => lpsOriginalJQCoefficient (q ^ N)) * _ - _ = 0
    rw [← lpsOriginalJQSeries_dilated_map N (Nat.ne_of_gt hN)]
    have hm := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) h
    simp only [map_mul, map_pow, PowerSeries.map_X] at hm
    exact sub_eq_zero.mpr hm.symm
  have hg := (lpsOriginalTaylorSeries_zero_iff_germ hD).mp hT
  have hz : lpsOriginalJNHolomorphic N hN * Hb - Ha = 0 := by
    apply lpsOriginalHolomorphic_zero_of_clearedNomeGerm
      (lpsOriginalJNHolomorphic N hN * Hb - Ha) D (B + N) hg
    intro τ
    change lpsOriginalJQCoefficient (Function.Periodic.qParam 1 (τ : ℂ) ^ N) *
      lpsOriginalFiniteClearedRationalSum M B u v b
        (Function.Periodic.qParam 1 (τ : ℂ)) -
      Function.Periodic.qParam 1 (τ : ℂ) ^ N *
        lpsOriginalFiniteClearedRationalSum M B u v a
          (Function.Periodic.qParam 1 (τ : ℂ)) = _
    rw [lpsOriginalFiniteClearedRationalSum_pullback M hM B u v b hB τ,
      lpsOriginalFiniteClearedRationalSum_pullback M hM B u v a hB τ,
      ← lpsOriginalJDilated_qParam_pullback N hN τ]
    change _ = Function.Periodic.qParam 1 (τ : ℂ) ^ (B + N) *
      (lpsOriginalJDilated N hN τ * Hb.val τ - Ha.val τ)
    rw [pow_add]
    ring
  have hHb : Hb ≠ 0 := lpsOriginalFiniteClearedRationalSum_formal_ne_zero
    M hM B u v b hB hb
  let holoMap := algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
  have hHb' : holoMap Hb ≠ 0 := fun he =>
    hHb (IsFractionRing.injective LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
      (he.trans (map_zero holoMap).symm))
  have hmul : lpsOriginalJNInFractionField N hN * holoMap Hb = holoMap Ha := by
    have he := congrArg holoMap (sub_eq_zero.mp hz)
    simpa only [map_mul, lpsOriginalJNInFractionField] using he
  rw [(eq_div_iff hHb').mpr hmul]
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (lpsOriginalGeneratedFunctionFieldQ M hM).div_mem
    (lpsOriginalRationalMonomialHolomorphicSum_mem M hM u v a)
    (lpsOriginalRationalMonomialHolomorphicSum_mem M hM u v b)

/-- Actual complex finite monomial sum with rational formal monomials underneath. -/
def lpsOriginalFiniteClearedComplexSum
    {ι : Type*} [Fintype ι] (M B : ℕ) (u v : ι → ℕ) (a : ι → ℂ) : ℂ → ℂ :=
  ∑ i, fun q => a i * lpsOriginalClearedMonomial M B (u i) (v i) q

lemma lpsOriginalFiniteClearedComplexSum_analytic
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : M ≠ 0)
    (B : ℕ) (u v : ι → ℕ) (a : ι → ℂ) :
    AnalyticAt ℂ (lpsOriginalFiniteClearedComplexSum M B u v a) 0 := by
  classical
  exact Finset.univ.analyticAt_sum fun i _hi =>
    analyticAt_const.mul (lpsOriginalClearedMonomial_analytic M hM B (u i) (v i))

lemma lpsOriginalFiniteClearedComplexSum_taylor
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : M ≠ 0)
    (B : ℕ) (u v : ι → ℕ) (a : ι → ℂ) :
    lpsOriginalTaylorSeries (lpsOriginalFiniteClearedComplexSum M B u v a) =
      ∑ i, PowerSeries.C (a i) * PowerSeries.map (algebraMap ℚ ℂ)
        (lpsOriginalClearedFormalMonomial M hM B (u i) (v i)) := by
  classical
  unfold lpsOriginalFiniteClearedComplexSum
  rw [lpsOriginalTaylorSeries_sum Finset.univ
    (fun i => fun q => a i * lpsOriginalClearedMonomial M B (u i) (v i) q)
    (fun i _hi => analyticAt_const.mul
      (lpsOriginalClearedMonomial_analytic M hM B (u i) (v i)))]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [lpsOriginalTaylorSeries_const_mul, lpsOriginalClearedMonomial_taylor M hM]

/-- Finite actual support indices of an original bivariate polynomial. -/
abbrev LPSOriginalBivariateSupport (P : Polynomial (Polynomial ℂ)) :=
  (k : P.support) × (P.coeff k.val).support

instance lpsOriginalBivariateSupport_fintype (P : Polynomial (Polynomial ℂ)) :
    Fintype (LPSOriginalBivariateSupport P) :=
  inferInstanceAs (Fintype ((k : P.support) × (P.coeff k.val).support))

lemma lpsOriginalClearedCusp_support_sum
    (M B : ℕ) (P : Polynomial (Polynomial ℂ)) :
    lpsOriginalClearedCusp M B P =
      ∑ s : LPSOriginalBivariateSupport P, fun q =>
        (P.coeff s.1.val).coeff s.2.val *
          lpsOriginalClearedMonomial M B s.2.val s.1.val q := by
  classical
  unfold lpsOriginalClearedCusp
  rw [Fintype.sum_sigma]
  change _ = ∑ k : P.support, ∑ i : (P.coeff k.val).support,
    fun q => (P.coeff k.val).coeff i.val * lpsOriginalClearedMonomial M B i.val k.val q
  have inner (k : P.support) :
      (∑ i : (P.coeff k.val).support, fun q =>
        (P.coeff k.val).coeff i.val * lpsOriginalClearedMonomial M B i.val k.val q) =
      ∑ i ∈ (P.coeff k.val).support, fun q =>
        (P.coeff k.val).coeff i * lpsOriginalClearedMonomial M B i k.val q :=
    Finset.sum_coe_sort (P.coeff k.val).support
      (fun i : ℕ => fun q : ℂ =>
        (P.coeff k.val).coeff i * lpsOriginalClearedMonomial M B i k.val q)
  simp_rw [inner]
  exact (Finset.sum_coe_sort P.support
    (fun k => ∑ i ∈ (P.coeff k).support, fun q =>
      (P.coeff k).coeff i * lpsOriginalClearedMonomial M B i k q)).symm

/-- Global original polynomial fraction identity produces its real cusp Taylor equation. -/
lemma lpsOriginalBivariateFraction_taylor_equation
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (G H : Polynomial (Polynomial ℂ)) (B : ℕ)
    (hG : lpsOriginalClearingBound M G ≤ B)
    (hH : lpsOriginalClearingBound M H ≤ B)
    (he : lpsOriginalJNHolomorphic N hN *
        lpsOriginalBivariateHolomorphicEval M hM H =
      lpsOriginalBivariateHolomorphicEval M hM G) :
    PowerSeries.map (algebraMap ℚ ℂ) (PowerSeries.X ^ N) *
        lpsOriginalTaylorSeries (lpsOriginalClearedCusp M B G) =
      PowerSeries.map (algebraMap ℚ ℂ)
          (PowerSeries.expand N (Nat.ne_of_gt hN) lpsOriginalJQSeries) *
        lpsOriginalTaylorSeries (lpsOriginalClearedCusp M B H) := by
  let KN : ℂ → ℂ := fun q => lpsOriginalJQCoefficient (q ^ N)
  let D := (fun q : ℂ => q ^ N) * lpsOriginalClearedCusp M B G -
    KN * lpsOriginalClearedCusp M B H
  have haG : AnalyticAt ℂ (lpsOriginalClearedCusp M B G) 0 := by
    rw [lpsOriginalClearedCusp_support_sum]
    exact lpsOriginalFiniteClearedComplexSum_analytic M (Nat.ne_of_gt hM) B
      (fun s : LPSOriginalBivariateSupport G => s.2.val)
      (fun s : LPSOriginalBivariateSupport G => s.1.val)
      (fun s : LPSOriginalBivariateSupport G => (G.coeff s.1.val).coeff s.2.val)
  have haH : AnalyticAt ℂ (lpsOriginalClearedCusp M B H) 0 := by
    rw [lpsOriginalClearedCusp_support_sum]
    exact lpsOriginalFiniteClearedComplexSum_analytic M (Nat.ne_of_gt hM) B
      (fun s : LPSOriginalBivariateSupport H => s.2.val)
      (fun s : LPSOriginalBivariateSupport H => s.1.val)
      (fun s : LPSOriginalBivariateSupport H => (H.coeff s.1.val).coeff s.2.val)
  have hKN : AnalyticAt ℂ KN 0 :=
    lpsOriginalJQCoefficient_analytic_zero.comp_of_eq
      (lpsOriginalPower_analytic N) (zero_pow (Nat.ne_of_gt hN))
  have haD : AnalyticAt ℂ D 0 :=
    ((lpsOriginalPower_analytic N).mul haG).sub (hKN.mul haH)
  have hg : D =ᶠ[𝓝 0] 0 := by
    apply lpsOriginalZeroGerm_of_puncturedDisk haD
    intro q hq hq0
    let τ : ℍ := ⟨Function.Periodic.invQParam 1 q,
      Function.Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num) hq hq0⟩
    have hqτ : Function.Periodic.qParam 1 (τ : ℂ) = q :=
      Function.Periodic.qParam_right_inv (by norm_num) hq0
    change q ^ N * lpsOriginalClearedCusp M B G q -
      lpsOriginalJQCoefficient (q ^ N) * lpsOriginalClearedCusp M B H q = 0
    rw [← hqτ,
      lpsOriginalClearedCusp_pullback_of_bound M hM B G hG τ,
      lpsOriginalClearedCusp_pullback_of_bound M hM B H hH τ,
      ← lpsOriginalJDilated_qParam_pullback N hN τ]
    have heτ := congrArg (fun F : LPSOriginalHolomorphicRing => F.val τ) he
    change lpsOriginalJDilated N hN τ *
      (lpsOriginalBivariateHolomorphicEval M hM H).val τ =
        (lpsOriginalBivariateHolomorphicEval M hM G).val τ at heτ
    rw [lpsOriginalBivariateHolomorphicEval_apply,
      lpsOriginalBivariateHolomorphicEval_apply] at heτ
    rw [← heτ]
    ring
  have ht := (lpsOriginalTaylorSeries_zero_iff_germ haD).mpr hg
  rw [lpsOriginalTaylorSeries_sub ((lpsOriginalPower_analytic N).mul haG) (hKN.mul haH),
    lpsOriginalTaylorSeries_mul (lpsOriginalPower_analytic N) haG,
    lpsOriginalTaylorSeries_mul hKN haH,
    lpsOriginalTaylorSeries_qpow] at ht
  simpa only [KN, map_pow, PowerSeries.map_X,
    lpsOriginalJQSeries_dilated_map] using sub_eq_zero.mp ht

/-- Constructed descent of the SAME original generator from its actual complex field. -/
lemma lpsOriginalJNInFractionField_mem_Q_of_mem_complex
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (hc : lpsOriginalJNInFractionField N hN ∈ lpsOriginalGeneratedFunctionField M hM) :
    lpsOriginalJNInFractionField N hN ∈ lpsOriginalGeneratedFunctionFieldQ M hM := by
  classical
  obtain ⟨G, H, hH, hfrac⟩ := lpsOriginalGeneratedFunctionField_bivariateFraction
    M hM (lpsOriginalJNInFractionField N hN) hc
  let holoMap := algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
  have hH' : holoMap (lpsOriginalBivariateHolomorphicEval M hM H) ≠ 0 := fun he =>
    hH (IsFractionRing.injective LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
      (he.trans (map_zero holoMap).symm))
  have he : lpsOriginalJNHolomorphic N hN *
      lpsOriginalBivariateHolomorphicEval M hM H =
      lpsOriginalBivariateHolomorphicEval M hM G := by
    apply IsFractionRing.injective LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
    change holoMap (_ * _) = holoMap _
    rw [map_mul]
    exact (eq_div_iff hH').mp hfrac
  let B := max (lpsOriginalClearingBound M G) (lpsOriginalClearingBound M H)
  have hGbound : lpsOriginalClearingBound M G ≤ B := le_max_left _ _
  have hHbound : lpsOriginalClearingBound M H ≤ B := le_max_right _ _
  let I := Sum (LPSOriginalBivariateSupport G) (LPSOriginalBivariateSupport H)
  let u : I → ℕ := Sum.elim (fun s => s.2.val) (fun s => s.2.val)
  let v : I → ℕ := Sum.elim (fun s => s.1.val) (fun s => s.1.val)
  let a : I → ℂ := Sum.elim (fun s => (G.coeff s.1.val).coeff s.2.val) (fun _ => 0)
  let b : I → ℂ := Sum.elim (fun _ => 0) (fun s => (H.coeff s.1.val).coeff s.2.val)
  have haeq : lpsOriginalFiniteClearedComplexSum M B u v a =
      lpsOriginalClearedCusp M B G := by
    unfold lpsOriginalFiniteClearedComplexSum
    change (∑ s : Sum (LPSOriginalBivariateSupport G) (LPSOriginalBivariateSupport H),
      fun q => a s * lpsOriginalClearedMonomial M B (u s) (v s) q) = _
    rw [Fintype.sum_sum_type, lpsOriginalClearedCusp_support_sum]
    simp only [a, u, v, Sum.elim_inl, Sum.elim_inr, zero_mul]
    funext q
    simp
  have hbeq : lpsOriginalFiniteClearedComplexSum M B u v b =
      lpsOriginalClearedCusp M B H := by
    unfold lpsOriginalFiniteClearedComplexSum
    change (∑ s : Sum (LPSOriginalBivariateSupport G) (LPSOriginalBivariateSupport H),
      fun q => b s * lpsOriginalClearedMonomial M B (u s) (v s) q) = _
    rw [Fintype.sum_sum_type, lpsOriginalClearedCusp_support_sum]
    simp only [b, u, v, Sum.elim_inl, Sum.elim_inr, zero_mul]
    funext q
    simp
  let T : I → PowerSeries ℚ := fun s =>
    lpsOriginalClearedFormalMonomial M (Nat.ne_of_gt hM) B (u s) (v s)
  have hrel := lpsOriginalBivariateFraction_taylor_equation N M hN hM G H B
    hGbound hHbound he
  rw [← haeq, ← hbeq,
    lpsOriginalFiniteClearedComplexSum_taylor M (Nat.ne_of_gt hM),
    lpsOriginalFiniteClearedComplexSum_taylor M (Nat.ne_of_gt hM)] at hrel
  have hden := lpsOriginalClearedCusp_taylor_ne_zero_of_original_denominator M hM B H
    hHbound hH
  rw [← hbeq, lpsOriginalFiniteClearedComplexSum_taylor M (Nat.ne_of_gt hM)] at hden
  obtain ⟨aq, bq, hab, hnonzero⟩ := lpsOriginalRationalSeries_finiteFraction_descent
    (PowerSeries.X ^ N) (PowerSeries.expand N (Nat.ne_of_gt hN) lpsOriginalJQSeries)
    T a b hrel hden
  apply lpsOriginalJN_mem_Q_of_finiteRationalSeriesEquation N M hN hM B u v aq bq
  · intro s
    cases s with
    | inl s => exact (lpsOriginalClearingBound_le M G s.1.property s.2.property).trans hGbound
    | inr s => exact (lpsOriginalClearingBound_le M H s.1.property s.2.property).trans hHbound
  · exact hab
  · exact hnonzero

/-- Same-original rational level inclusion, constructed from genuine complex pullback and rational descent. -/
lemma lpsOriginalGeneratedFunctionFieldQ_level_le
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N)
    (hposN : 0 < N) (hposM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGeneratedFunctionFieldQ N hposN ≤
      lpsOriginalGeneratedFunctionFieldQ M hposM := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  change IntermediateField.adjoin (FractionRing (Polynomial ℚ))
    {lpsOriginalJNInFractionField N hposN} ≤ _
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  have he := Set.mem_singleton_iff.mp hx
  subst x
  apply lpsOriginalJNInFractionField_mem_Q_of_mem_complex N M hposN hposM
  let := lpsOriginalJFractionEmbedding.toAlgebra
  exact lpsOriginalGeneratedFunctionField_level_le N M hNM hN hposN hposM
    (IntermediateField.subset_adjoin (FractionRing (Polynomial ℂ)) _
      (Set.mem_singleton _))
/-- The relative degree of the same original generated fields equals the actual integral congruence-subgroup relative index. -/
lemma lpsOriginalGeneratedFunctionFieldQ_relfinrank_eq
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N)
    (hposN : 0 < N) (hposM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGeneratedFunctionFieldQ N hposN).relfinrank
      (lpsOriginalGeneratedFunctionFieldQ M hposM) =
      ((CongruenceSubgroup.Gamma0 M).subgroupOf
        (CongruenceSubgroup.Gamma0 N)).index := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalGeneratedFunctionFieldQ_finiteDimensional N hposN
  let GN : Subgroup (GL (Fin 2) ℝ) :=
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
  let GM : Subgroup (GL (Fin 2) ℝ) :=
    (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))
  have hle : GM ≤ GN := Subgroup.map_mono (lpsGamma0_level_le N M hNM)
  have htop : GN ≤ 𝒮ℒ := (CongruenceSubgroup.Gamma0 N).map_le_range _
  have hG := Subgroup.relIndex_mul_relIndex GM GN 𝒮ℒ hle htop
  have hidx : GM.relIndex GN =
      ((CongruenceSubgroup.Gamma0 M).subgroupOf
        (CongruenceSubgroup.Gamma0 N)).index := by
    change ((CongruenceSubgroup.Gamma0 M).map (Matrix.SpecialLinearGroup.mapGL ℝ)).relIndex
      ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) = _
    exact Subgroup.relIndex_map_map_of_injective _ _ Matrix.SpecialLinearGroup.mapGL_injective
  rw [hidx] at hG
  have hF := IntermediateField.finrank_bot_mul_relfinrank
    (lpsOriginalGeneratedFunctionFieldQ_level_le N M hNM hN hposN hposM)
  rw [lpsOriginalGeneratedFunctionFieldQ_finrank_eq N hposN,
    lpsOriginalGeneratedFunctionFieldQ_finrank_eq M hposM] at hF
  change GN.relIndex 𝒮ℒ *
    (lpsOriginalGeneratedFunctionFieldQ N hposN).relfinrank
      (lpsOriginalGeneratedFunctionFieldQ M hposM) = GM.relIndex 𝒮ℒ at hF
  have hp : 0 < Module.finrank (FractionRing (Polynomial ℚ))
      (lpsOriginalGeneratedFunctionFieldQ N hposN) :=
    (Module.finrank_pos_iff_of_free (FractionRing (Polynomial ℚ))
      (lpsOriginalGeneratedFunctionFieldQ N hposN)).mpr inferInstance
  rw [lpsOriginalGeneratedFunctionFieldQ_finrank_eq N hposN] at hp
  change 0 < GN.relIndex 𝒮ℒ at hp
  apply Nat.eq_of_mul_eq_mul_left hp
  exact hF.trans (by simpa only [Nat.mul_comm] using hG.symm)

/-- The same original relative degree equals every full filled fibre cardinality over an interior point. -/
lemma lpsOriginalGeneratedFunctionFieldQ_relfinrank_filledFibre
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N)
    (hposN : 0 < N) (hposM : 0 < M)
    (y : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGeneratedFunctionFieldQ N hposN).relfinrank
      (lpsOriginalGeneratedFunctionFieldQ M hposM) =
      Nat.card {x : LPSOriginalFilledCurve M |
        lpsOriginalFilledForgetLevel N M hNM x = Sum.inl y} := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalGeneratedFunctionFieldQ_relfinrank_eq N M hNM hN hposN hposM]
  exact (lpsOriginalInteriorForgetLevel_fibre_card N M hNM hN y).symm.trans
    (Nat.card_congr (lpsOriginalFilledInteriorFibreEquiv N M hNM y))

/-- The same original coprime-prime function-field extension has degree p+1. -/
lemma lpsOriginalPrimeGeneratedFunctionFieldQ_relfinrank
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N) (hN : 4 ∣ N)
    (hposN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGeneratedFunctionFieldQ N hposN).relfinrank
      (lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hposN (Fact.out : p.Prime).pos)) = p+1 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalGeneratedFunctionFieldQ_relfinrank_eq N (N*p)
    (dvd_mul_right N p) hN hposN (Nat.mul_pos hposN (Fact.out : p.Prime).pos)]
  exact lpsHeckeIntersection_index N p hNp
end
end QEC.Coding.TannerLiftedProduct
