import QEC.Coding.AlgebraicGeometry.Towers.SourceRecursion
import QEC.Coding.AlgebraicGeometry.Towers.StepPlaceTransport
import QEC.Coding.AlgebraicGeometry.Places.InverseAffinePlace
import QEC.Coding.AlgebraicGeometry.Towers.FixedFieldArtinSchreier
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Orders of the recursive parameter on the basic rational fields

For every place of each rational coordinate field, the source recursion's
right-hand side is regular or has a normalized simple pole. Both the forward
coordinate and reciprocal successor coordinate are covered. These are the
basic inputs to Property (A), not an assertion about all higher tower fields.
-/

open IntermediateField
open scoped Polynomial RatFunc

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section


section SourceBasicRationalPlaces

open scoped BigOperators

private local instance sourceBasicRationalF256CharTwo : CharP F256 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2

/-- At any place of a rational function field, a pole of the rational
generator is simple.  Surjectivity of the normalized valuation forces its
order to divide the order of a uniformizer.  This supplies the infinity arm
of the source's basic rational edge without fixing the lower place in advance. -/
private theorem sourceBasicRationalPlace_order_X_of_pole
    {k : Type*} [_root_.Field k] [Finite k]
    (P : GlobalPlace k (RatFunc k))
    (hX : 1 < P.valuation RatFunc.X) :
    P.order RatFunc.X = -1 := by
  classical
  have hXne : P.valuation RatFunc.X ≠ 0 :=
    P.valuation.ne_zero_iff.mpr RatFunc.X_ne_zero
  have hmultiple : ∀ f : RatFunc k, f ≠ 0 →
      ∃ n : ℤ, P.order f = n * P.order RatFunc.X := by
    intro f
    induction f using RatFunc.induction_on with
    | f p q hq =>
      intro hf
      have hp : p ≠ 0 := by
        intro hp
        subst p
        simp at hf
      refine ⟨(p.natDegree : ℤ) - (q.natDegree : ℤ), ?_⟩
      unfold GlobalPlace.order
      rw [map_div₀, ← RatFunc.coePolynomial_eq_algebraMap,
        ← RatFunc.coePolynomial_eq_algebraMap,
        Polynomial.valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
          k (v := P.valuation) hX hp,
        Polynomial.valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
          k (v := P.valuation) hX hq,
        WithZero.log_div (pow_ne_zero _ hXne) (pow_ne_zero _ hXne)]
      simp only [WithZero.log_pow, nsmul_eq_mul]
      ring
  have hu : P.uniformizer ≠ 0 := by
    apply P.valuation.ne_zero_iff.mp
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  obtain ⟨n, hn⟩ := hmultiple P.uniformizer hu
  rw [P.order_uniformizer] at hn
  have hunit : P.order RatFunc.X = 1 ∨ P.order RatFunc.X = -1 :=
    Int.eq_one_or_neg_one_of_mul_eq_one (by
      simpa only [mul_comm] using hn.symm)
  have hpositive : 0 < WithZero.log (P.valuation RatFunc.X) := by
    simpa only [WithZero.log_one] using
      (WithZero.log_lt_log one_ne_zero hXne).mpr hX
  unfold GlobalPlace.order at hunit ⊢
  omega

/-- At every normalized place the rational generator is regular or has a
simple pole. This also supplies the `w` parameter of the initial additive
extension, without selecting only its infinity place. -/
theorem rationalPlace_order_X_dichotomy
    {k : Type*} [_root_.Field k] [Finite k]
    (P : GlobalPlace k (RatFunc k)) :
    P.order RatFunc.X = -1 ∨ 0 ≤ P.order RatFunc.X := by
  by_cases hX : P.valuation RatFunc.X ≤ 1
  · exact Or.inr ((P.regularAt_iff_order_nonnegative RatFunc.X_ne_zero).mp hX)
  · exact Or.inl (sourceBasicRationalPlace_order_X_of_pole P (lt_of_not_ge hX))

/-- The corresponding zero of a rational generator is also simple. -/
private theorem sourceBasicRationalPlace_order_X_of_zero
    {k : Type*} [_root_.Field k] [Finite k]
    (P : GlobalPlace k (RatFunc k))
    (hX : P.valuation RatFunc.X < 1) :
    P.order RatFunc.X = 1 := by
  let e := InverseAffinePlace.rationalInvolution k
  let Q := GlobalPlace.comapAlgEquiv e P
  have hQ : 1 < Q.valuation RatFunc.X := by
    change 1 < P.valuation (e RatFunc.X)
    rw [InverseAffinePlace.rationalInvolution_X, P.valuation.map_inv]
    exact (one_lt_inv₀ (pos_iff_ne_zero.mpr
      (P.valuation.ne_zero_iff.mpr RatFunc.X_ne_zero))).mpr hX
  have h := sourceBasicRationalPlace_order_X_of_pole Q hQ
  change (GlobalPlace.comapAlgEquiv e P).order RatFunc.X = -1 at h
  rw [GlobalPlace.comapAlgEquiv_order,
    InverseAffinePlace.rationalInvolution_X, P.order_inv] at h
  omega

/-- Each finite rational zero has the same normalization, after the literal
translation of the polynomial generator. -/
private theorem sourceBasicRationalPlace_order_X_sub_constant_of_zero
    {k : Type*} [_root_.Field k] [Finite k]
    (P : GlobalPlace k (RatFunc k)) (a : k)
    (hX : P.valuation (RatFunc.X - algebraMap k (RatFunc k) a) < 1) :
    P.order (RatFunc.X - algebraMap k (RatFunc k) a) = 1 := by
  let e : RatFunc k ≃ₐ[k] RatFunc k :=
    IsFractionRing.algEquivOfAlgEquiv (Polynomial.algEquivAevalXAddC (-a))
  have he : e RatFunc.X = RatFunc.X - algebraMap k (RatFunc k) a := by
    change IsFractionRing.algEquivOfAlgEquiv
      (Polynomial.algEquivAevalXAddC (-a))
      (algebraMap k[X] (RatFunc k) Polynomial.X) = _
    rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
    simp [Polynomial.algEquivAevalXAddC_apply, sub_eq_add_neg]
  let Q := GlobalPlace.comapAlgEquiv e P
  have hQ : Q.valuation RatFunc.X < 1 := by
    change P.valuation (e RatFunc.X) < 1
    rwa [he]
  have h := sourceBasicRationalPlace_order_X_of_zero Q hQ
  change (GlobalPlace.comapAlgEquiv e P).order RatFunc.X = 1 at h
  simpa only [GlobalPlace.comapAlgEquiv_order, he] using h

/-- Distinct rational linear factors cannot simultaneously vanish at one
place, since their difference is a nonzero constant. -/
private theorem sourceBasicRationalPlace_order_product
    {k ι : Type*} [_root_.Field k] [Finite k]
    (P : GlobalPlace k (RatFunc k)) (s : Finset ι) (a : ι → k)
    (ha : Function.Injective a) (hX : P.valuation RatFunc.X ≤ 1) :
    P.order (∏ j ∈ s, (RatFunc.X - algebraMap k (RatFunc k) (a j))) = 0 ∨
    P.order (∏ j ∈ s, (RatFunc.X - algebraMap k (RatFunc k) (a j))) = 1 := by
  classical
  let f : ι → RatFunc k := fun j => RatFunc.X - algebraMap k (RatFunc k) (a j)
  have hle (j : ι) : P.valuation (f j) ≤ 1 := by
    apply (P.valuation.map_sub _ _).trans
    apply max_le hX
    by_cases hj : a j = 0
    · simp [hj]
    · exact le_of_eq ((GlobalPlace.trivialOnConstants P).eq_one _ hj)
  by_cases hsmall : ∃ j ∈ s, P.valuation (f j) < 1
  · obtain ⟨j, hj, hjlt⟩ := hsmall
    have hother (b : ι) (_hb : b ∈ s) (h : b ≠ j) : P.valuation (f b) = 1 := by
      have hab : a j - a b ≠ 0 := sub_ne_zero.mpr (fun he => h (ha he.symm))
      have hc : P.valuation (algebraMap k (RatFunc k) (a j - a b)) = 1 :=
        (GlobalPlace.trivialOnConstants P).eq_one _ hab
      have heq : f b = f j + algebraMap k (RatFunc k) (a j - a b) := by
        simp only [f, map_sub]
        ring
      rw [heq, P.valuation.map_add_eq_of_lt_right (hjlt.trans_eq hc.symm), hc]
    have hv : P.valuation (∏ b ∈ s, f b) = P.valuation (f j) := by
      rw [map_prod]
      exact Finset.prod_eq_single_of_mem j hj hother
    right
    change -WithZero.log (P.valuation (∏ b ∈ s, f b)) = 1
    rw [hv]
    exact sourceBasicRationalPlace_order_X_sub_constant_of_zero P (a j) hjlt
  · left
    have hone (j : ι) (hj : j ∈ s) : P.valuation (f j) = 1 :=
      le_antisymm (hle j) (not_lt.mp (fun h => hsmall ⟨j, hj, h⟩))
    change -WithZero.log (P.valuation (∏ b ∈ s, f b)) = 0
    rw [map_prod, Finset.prod_eq_one hone, WithZero.log_one, neg_zero]

/-- The source's additive polynomial factors over its actual sixteen-element
constant subfield.  The factorization is derived from all finite-field roots. -/
private theorem sourceBasicRational_f16_factorization :
    (RatFunc.X : RatFunc F256) ^ 16 + RatFunc.X =
      ∏ a : F16, (RatFunc.X - algebraMap F256 (RatFunc F256) (f16Embedding a)) := by
  classical
  have hroots : (Polynomial.X ^ 16 - Polynomial.X : F16[X]).roots = Finset.univ.val := by
    simpa only [f16_card] using (FiniteField.roots_X_pow_card_sub_X F16)
  have hmonic : (Polynomial.X ^ 16 - Polynomial.X : F16[X]).Monic := by
    apply (Polynomial.monic_X_pow 16).sub_of_left
    simp only [Polynomial.degree_X, Polynomial.degree_X_pow]
    norm_num
  have hcard : (Polynomial.X ^ 16 - Polynomial.X : F16[X]).roots.card =
      (Polynomial.X ^ 16 - Polynomial.X : F16[X]).natDegree := by
    rw [hroots, Finset.card_val, Finset.card_univ, f16_card,
      FiniteField.X_pow_card_sub_X_natDegree_eq F16 (by norm_num)]
  have hp := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
  rw [hroots] at hp
  change (∏ a : F16, (Polynomial.X - Polynomial.C a)) =
    (Polynomial.X ^ 16 - Polynomial.X : F16[X]) at hp
  have he := congrArg (Polynomial.eval₂RingHom
    ((algebraMap F256 (RatFunc F256)).comp f16Embedding.toRingHom) RatFunc.X) hp.symm
  simp only [map_sub, map_pow, map_prod, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, RingHom.comp_apply,
    sub_eq_add_neg, CharTwo.neg_eq] at he ⊢
  exact he

/-- For every place of the basic rational field, the literal GS right-hand
side is regular or has a simple pole.  No place is selected in advance. -/
theorem sourceBasicRationalPlace_sourceStepRhs_order_dichotomy
    (P : GlobalPlace F256 (RatFunc F256)) :
    P.order (sourceStepRhs RatFunc.X) = -1 ∨
      0 ≤ P.order (sourceStepRhs RatFunc.X) := by
  classical
  by_cases hf : sourceStepRhs (RatFunc.X : RatFunc F256) = 0
  · right
    simp [hf, GlobalPlace.order]
  have hXne : (RatFunc.X : RatFunc F256) ≠ 0 := RatFunc.X_ne_zero
  have hdenne : (RatFunc.X : RatFunc F256) ^ 15 + 1 ≠ 0 := by
    intro hzero
    apply hf
    simp [sourceStepRhs, hzero]
  rcases lt_trichotomy (P.valuation RatFunc.X) 1 with hlt | heq | hgt
  · right
    apply (P.regularAt_iff_order_nonnegative hf).mp
    have hpow : P.valuation (RatFunc.X ^ 15) < 1 := by
      rw [map_pow]
      exact pow_lt_one₀ zero_le hlt (by norm_num)
    have hden : P.valuation (RatFunc.X ^ 15 + 1) = 1 := by
      rw [P.valuation.map_add_eq_of_lt_right (hpow.trans_eq (map_one _).symm), map_one]
    change P.valuation (RatFunc.X ^ 16 / (RatFunc.X ^ 15 + 1)) ≤ 1
    rw [map_div₀, hden, div_one, map_pow]
    exact pow_le_one₀ zero_le hlt.le
  · have hXorder : P.order RatFunc.X = 0 := by
      simp [GlobalPlace.order, heq]
    have hprod := sourceBasicRationalPlace_order_product P Finset.univ
      f16Embedding f16Embedding.injective heq.le
    rw [← sourceBasicRational_f16_factorization] at hprod
    have hfactor : (RatFunc.X : RatFunc F256) ^ 16 + RatFunc.X =
        RatFunc.X * (RatFunc.X ^ 15 + 1) := by ring
    rw [hfactor, P.order_mul hXne hdenne, hXorder, zero_add] at hprod
    have hRhs : P.order (sourceStepRhs RatFunc.X) =
        -P.order (RatFunc.X ^ 15 + 1) := by
      rw [sourceStepRhs, div_eq_mul_inv,
        P.order_mul (pow_ne_zero 16 hXne) (inv_ne_zero hdenne), P.order_inv]
      have hnum : P.order (RatFunc.X ^ 16) = 0 := by
        simp [GlobalPlace.order, map_pow, heq]
      rw [hnum, zero_add]
    rcases hprod with hzero | hone
    · right
      simp [hRhs, hzero]
    · left
      rw [hRhs, hone]
  · left
    exact sourceStepRhs_order P RatFunc.X
      (sourceBasicRationalPlace_order_X_of_pole P hgt)

/-- The basic forward input on the actual level-zero source field. -/
theorem sourceBasicSourceLevelZero_rhs_order_dichotomy
    (P : GlobalPlace F256 (SourceField 0)) :
    P.order (sourceStepRhs (sourceDistinguishedCoordinate 0)) = -1 ∨
      0 ≤ P.order (sourceStepRhs (sourceDistinguishedCoordinate 0)) := by
  exact sourceBasicRationalPlace_sourceStepRhs_order_dichotomy P

/-- The same basic input for the reciprocal rational coordinate, as used by
the reverse source equation.  Pullback retains the arbitrary supplied place. -/
theorem sourceBasicRationalPlace_sourceStepRhs_inv_order_dichotomy
    (P : GlobalPlace F256 (RatFunc F256)) :
    P.order (sourceStepRhs (RatFunc.X⁻¹)) = -1 ∨
      0 ≤ P.order (sourceStepRhs (RatFunc.X⁻¹)) := by
  let e := InverseAffinePlace.rationalInvolution F256
  have h := sourceBasicRationalPlace_sourceStepRhs_order_dichotomy
    (GlobalPlace.comapAlgEquiv e P)
  have he : e (sourceStepRhs RatFunc.X) = sourceStepRhs (RatFunc.X⁻¹) := by
    simp only [sourceStepRhs, map_div₀, map_pow, map_add, map_one,
      InverseAffinePlace.rationalInvolution_X, e]
  simpa only [GlobalPlace.comapAlgEquiv_order, he] using h

/-- An element with nonzero order cannot be algebraic over the finite
constant field: an algebraic simple extension is finite, and every nonzero
element of that finite field has valuation one. -/
private theorem sourceBasic_transcendental_of_order_ne_zero
    {K : Type*} [_root_.Field K] [Algebra F256 K]
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x ≠ 0) :
    Transcendental F256 x := by
  intro halg
  have hxne : x ≠ 0 := by
    intro hzero
    apply hx
    simp only [hzero, GlobalPlace.order, map_zero, WithZero.log_zero, neg_zero]
  letI : FiniteDimensional F256 F256⟮x⟯ :=
    IntermediateField.adjoin.finiteDimensional halg.isIntegral
  letI : Finite F256⟮x⟯ := Module.finite_of_finite F256
  have hgen : AdjoinSimple.gen F256 x ≠ 0 := by
    intro hzero
    have h := congrArg (algebraMap F256⟮x⟯ K) hzero
    rw [AdjoinSimple.algebraMap_gen, map_zero] at h
    exact hxne h
  have hv := FiniteField.valuation_algebraMap_eq_one P.valuation
    (AdjoinSimple.gen F256 x) hgen
  rw [AdjoinSimple.algebraMap_gen] at hv
  apply hx
  simp only [GlobalPlace.order, hv, WithZero.log_one, neg_zero]

/-- The coordinate at every actual source level is transcendental; this
uses its proved simple-pole place, not a rationality assumption. -/
theorem sourceBasicSourceCoordinate_transcendental (i : ℕ) :
    Transcendental F256 (sourceDistinguishedCoordinate i) := by
  apply sourceBasic_transcendental_of_order_ne_zero
    (sourceDistinguishedPlace i) (sourceDistinguishedCoordinate i)
  rw [sourceDistinguishedCoordinate_order]
  norm_num

/-- The rational RHS calculation transports to the literal rational
subfield generated by any transcendental coordinate. -/
theorem sourceBasicRationalSubfield_sourceStepRhs_order_dichotomy
    {K : Type*} [_root_.Field K] [Algebra F256 K]
    (x : K) (hx : Transcendental F256 x)
    (P : GlobalPlace F256 F256⟮x⟯) :
    P.order (sourceStepRhs (AdjoinSimple.gen F256 x)) = -1 ∨
      0 ≤ P.order (sourceStepRhs (AdjoinSimple.gen F256 x)) := by
  let e := RatFunc.algEquivOfTranscendental x hx
  have h := sourceBasicRationalPlace_sourceStepRhs_order_dichotomy
    (GlobalPlace.comapAlgEquiv e P)
  have hX : e RatFunc.X = AdjoinSimple.gen F256 x := by
    apply Subtype.ext
    exact RatFunc.algEquivOfTranscendental_X x hx
  have he : e (sourceStepRhs RatFunc.X) =
      sourceStepRhs (AdjoinSimple.gen F256 x) := by
    simp only [sourceStepRhs, map_div₀, map_pow, map_add, map_one, hX]
  simpa only [GlobalPlace.comapAlgEquiv_order, he] using h

/-- All lower places of the forward basic rational projection in the
source's Property-(A) pyramid have the simple-pole-or-regular RHS input.
This is a statement about F256(x_i), not the whole tower field F_i. -/
theorem sourceBasicForwardRational_rhs_order_dichotomy
    (i : ℕ)
    (P : GlobalPlace F256 F256⟮sourceDistinguishedCoordinate i⟯) :
    P.order (sourceStepRhs
      (AdjoinSimple.gen F256 (sourceDistinguishedCoordinate i))) = -1 ∨
      0 ≤ P.order (sourceStepRhs
        (AdjoinSimple.gen F256 (sourceDistinguishedCoordinate i))) :=
  sourceBasicRationalSubfield_sourceStepRhs_order_dichotomy
    (sourceDistinguishedCoordinate i)
    (sourceBasicSourceCoordinate_transcendental i) P

/-- All lower places of the reverse basic rational projection have the same
RHS input on the literal reciprocal successor coordinate.  The recursion's
reverse equation identifies this RHS with 1/(x_(i+1)^16+x_(i+1)).
No higher-window different formula is inferred here. -/
theorem sourceBasicReverseRational_rhs_order_dichotomy
    (i : ℕ)
    (P : GlobalPlace F256 F256⟮(sourceDistinguishedCoordinate (i + 1))⁻¹⟯) :
    P.order (sourceStepRhs
      (AdjoinSimple.gen F256 ((sourceDistinguishedCoordinate (i + 1))⁻¹))) = -1 ∨
      0 ≤ P.order (sourceStepRhs
        (AdjoinSimple.gen F256 ((sourceDistinguishedCoordinate (i + 1))⁻¹))) := by
  apply sourceBasicRationalSubfield_sourceStepRhs_order_dichotomy _ _ P
  intro halg
  exact sourceBasicSourceCoordinate_transcendental (i + 1)
    (IsAlgebraic.inv_iff.mp halg)

end SourceBasicRationalPlaces

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
