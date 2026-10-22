import QEC.Coding.AlgebraicGeometry.Towers.SourceNormalClosure
import QEC.Coding.AlgebraicGeometry.Towers.SourceSelectedPlaceOrder
import QEC.Coding.AlgebraicGeometry.Places.RatFuncPlaceClassification

/-!
# Restricting selected source places to the fixed rational base

The rational variable is sent to the literal fixed-base parameter `z` in a
source level.  At every selected source place, the restricted valuation is
normalized by `X-1`; rational-function place classification therefore
identifies it with the actual base place at `X=1`.

No assertion about the normal closure, divisor, genus, or asymptotics is made.
-/

open Polynomial
open scoped RatFunc WithZero
open MonoidWithZeroHom

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

/-- The literal fixed-base embedding into source level `m`, with the rational
variable sent to `z`. -/
noncomputable def sourceSelectedRatFuncEmbedding (m : ℕ) :
    RatFunc F256 →ₐ[F256] SourceField m :=
  (sourceGaloisBaseFieldEmbedding m).comp
    galoisBaseFieldEquivRatFunc.toAlgHom

/-- The rational variable maps to the actual source-level base parameter. -/
theorem sourceSelectedRatFuncEmbedding_X (m : ℕ) :
    sourceSelectedRatFuncEmbedding m RatFunc.X =
      sourceGaloisBaseParameter m := by
  simp [sourceSelectedRatFuncEmbedding, sourceGaloisBaseFieldEmbedding,
    galoisBaseFieldEquivRatFunc, sourceGaloisBaseParameter]

private noncomputable def sourceSelectedRestrictedBaseValuation
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    Valuation (RatFunc F256) ℤᵐ⁰ :=
  (sourceSelectedRationalPlace m index).place.valuation.comap
    (sourceSelectedRatFuncEmbedding m).toRingHom

private theorem sourceSelectedRestrictedBaseValuation_X_sub_one
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    sourceSelectedRestrictedBaseValuation m index (RatFunc.X - 1) =
      WithZero.exp (-1 : ℤ) := by
  let Q := (sourceSelectedRationalPlace m index).place
  have horder :=
    sourceSelectedRationalPlace_order_galoisBaseParameter_sub_one m index
  have hmap :
      sourceSelectedRatFuncEmbedding m (RatFunc.X - 1) =
        sourceGaloisBaseParameter m - 1 := by
    rw [map_sub, map_one, sourceSelectedRatFuncEmbedding_X]
  have hne : Q.valuation (sourceGaloisBaseParameter m - 1) ≠ 0 :=
    Q.valuation.ne_zero_iff.mpr
      (sourceGaloisBaseParameter_sub_one_ne_zero m)
  have hlog :
      WithZero.log (Q.valuation (sourceGaloisBaseParameter m - 1)) = -1 := by
    unfold GlobalPlace.order at horder
    linarith
  change Q.valuation
      (sourceSelectedRatFuncEmbedding m (RatFunc.X - 1)) = _
  rw [hmap, ← WithZero.exp_log hne, hlog]

private theorem sourceSelectedRestrictedBaseValuation_surjective
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    Function.Surjective (sourceSelectedRestrictedBaseValuation m index) := by
  intro γ
  by_cases hγ : γ = 0
  · subst γ
    exact ⟨0, map_zero _⟩
  · refine ⟨(RatFunc.X - 1) ^ (-WithZero.log γ), ?_⟩
    rw [map_zpow₀,
      sourceSelectedRestrictedBaseValuation_X_sub_one,
      ← WithZero.exp_zsmul]
    simp only [smul_eq_mul]
    rw [neg_mul_neg, mul_one, WithZero.exp_log hγ]

/-- The normalized place obtained by restricting a selected source place
along the literal `F256(X) → SourceField m`, `X ↦ z`, embedding. -/
noncomputable def sourceSelectedRestrictedBasePlace
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    GlobalPlace F256 (RatFunc F256) where
  valuation := sourceSelectedRestrictedBaseValuation m index
  normalized := sourceSelectedRestrictedBaseValuation_surjective m index

/-- The restricted place has simple order one at `X-1`. -/
theorem sourceSelectedRestrictedBasePlace_order_X_sub_one
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    (sourceSelectedRestrictedBasePlace m index).order
        (RatFunc.X - 1) = 1 := by
  unfold GlobalPlace.order sourceSelectedRestrictedBasePlace
  rw [sourceSelectedRestrictedBaseValuation_X_sub_one, WithZero.log_exp]
  norm_num

private theorem sourceRestrictedGlobalPlace_eq_of_valuation_eq
    {P Q : GlobalPlace F256 (RatFunc F256)}
    (hvaluation : P.valuation = Q.valuation) : P = Q := by
  cases P
  cases Q
  cases hvaluation
  rfl

/-- Every selected source valuation restricts to the actual fixed-base
rational place `X=1`. -/
theorem sourceSelectedRestrictedBasePlace_eq_baseOne
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    sourceSelectedRestrictedBasePlace m index =
      (baseRationalPlace (1 : BasePoint)).place := by
  let P := sourceSelectedRestrictedBasePlace m index
  let v := P.valuation
  have ht : v (RatFunc.X - 1) = WithZero.exp (-1 : ℤ) :=
    sourceSelectedRestrictedBaseValuation_X_sub_one m index
  have ht_lt : v (RatFunc.X - 1) < 1 := by
    rw [ht, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  letI : v.IsNontrivial := by
    rw [Valuation.isNontrivial_iff_exists_lt_one]
    refine ⟨RatFunc.X - 1, ?_, ht_lt⟩
    apply sub_ne_zero.mpr
    intro hX
    exact RatFunc.transcendental_X (hX ▸ isAlgebraic_one)
  letI : IsCyclic (valueGroup (MonoidWithZeroHom.ofClass v)) := inferInstance
  letI : Nontrivial (valueGroup (MonoidWithZeroHom.ofClass v)) := inferInstance
  letI : v.IsRankOneDiscrete :=
    Valuation.IsRankOneDiscrete.mk' v
  letI : v.IsTrivialOn F256 := P.trivialOnConstants
  have hX : v RatFunc.X ≤ 1 := by
    have hdecomp : (RatFunc.X : RatFunc F256) =
        (RatFunc.X - 1) + 1 := by ring
    rw [hdecomp]
    exact (v.map_add (RatFunc.X - 1) 1).trans
      (max_le (le_of_lt ht_lt) (by simp))
  obtain ⟨p, hp⟩ :=
    RatFunc.valuation_isEquiv_adic_of_valuation_X_le_one (v := v) hX
  have htAdic :
      p.valuation (RatFunc F256) (RatFunc.X - 1) < 1 :=
    hp.lt_one_iff_lt_one.mp ht_lt
  have hmem :
      (Polynomial.X - Polynomial.C (1 : F256)) ∈ p.asIdeal := by
    apply (p.valuation_lt_one_iff_mem (K := RatFunc F256)
      (Polynomial.X - Polynomial.C (1 : F256))).mp
    simpa only [map_sub, RatFunc.algebraMap_X, map_one,
      RatFunc.algebraMap_eq_C] using htAdic
  have hp_eq : p = baseHeightOnePoint (1 : BasePoint) := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    have hle : (baseHeightOnePoint (1 : BasePoint)).asIdeal ≤
        p.asIdeal := by
      rw [baseHeightOnePoint_asIdeal]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
    exact ((baseHeightOnePoint (1 : BasePoint)).isMaximal.eq_of_le
      p.isPrime.ne_top hle).symm
  have hvaluation :
      P.valuation =
        (GlobalPlace.rationalAdic
          (baseHeightOnePoint (1 : BasePoint))).valuation := by
    change v = _
    rw [← hp_eq]
    exact normalizedValuation_eq_of_isEquiv
      v (p.valuation (RatFunc F256)) P.normalized
      (p.valuation_surjective (RatFunc F256)) hp
  rw [baseRationalPlace_place_eq_rationalAdic]
  exact sourceRestrictedGlobalPlace_eq_of_valuation_eq hvaluation

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
