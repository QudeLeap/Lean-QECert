import QEC.Coding.AlgebraicGeometry.Places.ReciprocalPolynomialCoefficients
import QEC.Coding.ExpanderCodes.LPSOriginalHolomorphicIntegral
import QEC.Coding.ExpanderCodes.LPSOriginalHolomorphicFractionRoot
import QEC.Coding.ExpanderCodes.LPSOriginalNormalizationChartEvaluation

/-!
# Original E4 denominator reciprocal monic equation

The actual finite-coset equation has bounded inner degree and E4 denominator leading coefficient (-1)^r X^(kr). Sign normalization and inner reflection construct a monic equation over the reciprocal j coordinate. Homogenization proves its actual holomorphic fraction-field root.

Derived internal PK22 ex:Xpq closure, pinned main.tex484–486, for parent #449.
Reciprocal point coverage, global differential/sheaf comparison, good reduction,
Hecke/Frobenius/Weil and the public quantum-family theorem remain further work.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

/-- Every inner coefficient of the actual finite-coset equation has the genuine common degree bound. -/
lemma lpsOriginalMeromorphicRatioEquation_coeff_degree
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k)
    (n : ℕ) :
    ((lpsOriginalMeromorphicRatioEquation N k A B).coeff n).natDegree ≤
      k * Nat.card (LPSOriginalMeromorphicCosets N) := by
  classical
  unfold lpsOriginalMeromorphicRatioEquation
  rw [Polynomial.finsetSum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_map]
  apply Polynomial.natDegree_mul_le.trans
  simpa only [Polynomial.natDegree_C, add_zero] using
    (lpsOriginalMeromorphicRatioNormCoefficient_spec N k A B (i.val : ℂ)).1

/-- Restrict the genuine weight12k E4 cube power to the original level-N modular forms. -/
def lpsOriginalMeromorphicE4PowerAtLevel (N k : ℕ) :
    LPSOriginalMeromorphicLevelForm N k :=
  let D : ModularForm 𝒮ℒ ((k : ℤ)*12) :=
    (lpsOriginalE4CubePower k).mcast (by ring)
  let hle : (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
    intro g hg
    obtain ⟨γ, hγ, he⟩ := hg
    exact ⟨γ, he⟩
  { toFun := D
    slash_action_eq' g hg := D.slash_action_eq' g (hle hg)
    holo' := D.holo'
    bdd_at_cusps' hc := D.bdd_at_cusps' (hc.mono hle) }

/-- The restricted denominator retains the literal E4 cube-power values. -/
lemma lpsOriginalMeromorphicE4PowerAtLevel_apply (N k : ℕ) (τ : ℍ) :
    lpsOriginalMeromorphicE4PowerAtLevel N k τ =
      (ModularForm.E₄ τ^3)^k :=
  lpsOriginalE4CubePower_apply k τ

/-- Every actual SL2 coset translate of the E4 denominator has the same value. -/
lemma lpsOriginalRestrictedE4_coset (N k : ℕ)
    (q : LPSOriginalMeromorphicCosets N) (τ : ℍ) :
    SlashInvariantForm.quotientFunc
      (lpsOriginalMeromorphicE4PowerAtLevel N k) q τ =
      (ModularForm.E₄ τ^3)^k := by
  induction q using Quotient.inductionOn with
  | h g =>
    let D : ModularForm 𝒮ℒ ((k : ℤ)*12) :=
      (lpsOriginalE4CubePower k).mcast (by ring)
    change ((D : ℍ → ℂ) ∣[(k : ℤ)*12] g.val⁻¹) τ = _
    rw [SlashInvariantForm.slash_action_eqn D g.val⁻¹ (inv_mem g.property)]
    exact lpsOriginalE4CubePower_apply k τ

/-- The actual finite-coset product has the computed E4 denominator top coefficient. -/
lemma lpsOriginalE4DenominatorCosetPolynomial_coeff
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) (τ : ℍ) :
    (lpsOriginalMeromorphicRatioCosetPolynomial N k A
      (lpsOriginalMeromorphicE4PowerAtLevel N k) τ).coeff
      (Nat.card (LPSOriginalMeromorphicCosets N)) =
        (-1 : ℂ)^Nat.card (LPSOriginalMeromorphicCosets N) *
          (ModularForm.E₄ τ^3)^(k * Nat.card (LPSOriginalMeromorphicCosets N)) := by
  classical
  let := Fintype.ofFinite (LPSOriginalMeromorphicCosets N)
  let B := lpsOriginalMeromorphicE4PowerAtLevel N k
  let f := fun q : LPSOriginalMeromorphicCosets N =>
    Polynomial.C (SlashInvariantForm.quotientFunc A q τ) -
      Polynomial.X * Polynomial.C (SlashInvariantForm.quotientFunc B q τ)
  have hd (q : LPSOriginalMeromorphicCosets N) (_ : q ∈ Finset.univ) :
      (f q).natDegree ≤ 1 := by
    dsimp only [f]
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · exact Polynomial.natDegree_mul_le.trans (by simp)
  have hcoef (q : LPSOriginalMeromorphicCosets N) :
      (f q).coeff 1 = -(ModularForm.E₄ τ^3)^k := by
    dsimp only [f]
    rw [Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_X_mul]
    simp only [one_ne_zero, if_false, Polynomial.coeff_C_zero, zero_sub]
    rw [lpsOriginalRestrictedE4_coset]
  have hc := Polynomial.coeff_prod_of_natDegree_le (s := Finset.univ) f 1 hd
  change (∏ q : LPSOriginalMeromorphicCosets N, f q).coeff _ = _
  rw [Nat.card_eq_fintype_card]
  calc
    _ = ∏ q : LPSOriginalMeromorphicCosets N, (f q).coeff 1 := by
      simpa only [Finset.card_univ, mul_one] using hc
    _ = (-(ModularForm.E₄ τ^3)^k)^Fintype.card (LPSOriginalMeromorphicCosets N) := by
      simp only [hcoef, Finset.prod_const, Finset.card_univ]
    _ = _ := by rw [neg_eq_neg_one_mul, mul_pow, ← pow_mul]

/-- The recovered nested equation has top coefficient equal to the sign times the common j power. -/
lemma lpsOriginalE4DenominatorEquation_coeff
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) :
    (lpsOriginalMeromorphicRatioEquation N k A
      (lpsOriginalMeromorphicE4PowerAtLevel N k)).coeff
      (Nat.card (LPSOriginalMeromorphicCosets N)) =
        Polynomial.C ((-1 : ℂ)^Nat.card (LPSOriginalMeromorphicCosets N)) *
          Polynomial.X^(k * Nat.card (LPSOriginalMeromorphicCosets N)) := by
  apply lpsOriginalJPolynomialEvalHom_injective
  funext τ
  change Polynomial.eval (lpsOriginalJInvariant τ) _ =
    Polynomial.eval (lpsOriginalJInvariant τ)
      (Polynomial.C ((-1 : ℂ)^Nat.card (LPSOriginalMeromorphicCosets N)) *
        Polynomial.X^(k * Nat.card (LPSOriginalMeromorphicCosets N)))
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have h := congrArg (fun p : Polynomial ℂ => p.coeff (Nat.card (LPSOriginalMeromorphicCosets N)))
    (lpsOriginalMeromorphicRatioEquation_recovery N k A
      (lpsOriginalMeromorphicE4PowerAtLevel N k) τ)
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_map,
    lpsOriginalE4DenominatorCosetPolynomial_coeff,
    ← lpsOriginalDelta_j_power (k * Nat.card (LPSOriginalMeromorphicCosets N)) τ] at h
  apply mul_left_cancel₀ (pow_ne_zero (k * Nat.card (LPSOriginalMeromorphicCosets N))
    (ModularForm.discriminant_ne_zero τ))
  simpa only [Polynomial.coe_evalRingHom, mul_assoc, mul_left_comm] using h

/-- Normalize the actual E4 denominator equation by its nonzero scalar sign. -/
def lpsOriginalReciprocalE4NormalizedEquation
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) :
    Polynomial (Polynomial ℂ) :=
  Polynomial.C (Polynomial.C (((-1 : ℂ)^Nat.card (LPSOriginalMeromorphicCosets N))⁻¹)) *
    lpsOriginalMeromorphicRatioEquation N k A
      (lpsOriginalMeromorphicE4PowerAtLevel N k)

/-- Sign normalization preserves the actual common inner-degree bound. -/
lemma lpsOriginalReciprocalE4NormalizedEquation_coeff_degree
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) (n : ℕ) :
    ((lpsOriginalReciprocalE4NormalizedEquation N k A).coeff n).natDegree ≤
      k * Nat.card (LPSOriginalMeromorphicCosets N) := by
  rw [lpsOriginalReciprocalE4NormalizedEquation, Polynomial.coeff_C_mul]
  apply Polynomial.natDegree_mul_le.trans
  simpa only [Polynomial.natDegree_C, zero_add] using
    lpsOriginalMeromorphicRatioEquation_coeff_degree N k A
      (lpsOriginalMeromorphicE4PowerAtLevel N k) n

/-- Construct the reciprocal E4 equation by reflecting all normalized inner coefficients. -/
def lpsOriginalReciprocalE4MonicEquation
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) :
    Polynomial (Polynomial ℂ) :=
  QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients
    (k * Nat.card (LPSOriginalMeromorphicCosets N))
    (lpsOriginalReciprocalE4NormalizedEquation N k A)

/-- The constructed reciprocal equation is genuinely monic in the unchanged function variable. -/
lemma lpsOriginalReciprocalE4MonicEquation_monic
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) :
    (lpsOriginalReciprocalE4MonicEquation N k A).Monic := by
  apply QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_monic
    (k * Nat.card (LPSOriginalMeromorphicCosets N))
    (Nat.card (LPSOriginalMeromorphicCosets N))
  · unfold lpsOriginalReciprocalE4NormalizedEquation
    apply Polynomial.natDegree_mul_le.trans
    simpa only [Polynomial.natDegree_C, zero_add] using
      lpsOriginalMeromorphicRatioEquation_degree N k A
        (lpsOriginalMeromorphicE4PowerAtLevel N k)
  · rw [lpsOriginalReciprocalE4NormalizedEquation, Polynomial.coeff_C_mul,
      lpsOriginalE4DenominatorEquation_coeff, ← mul_assoc,
      ← Polynomial.C_mul, inv_mul_cancel₀, Polynomial.C_1, one_mul]
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

/-- A literal numerator-denominator relation at one point gives the actual coset equation root. -/
lemma lpsOriginalMeromorphicRatioEquation_root_at
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k)
    (τ : ℍ) (t : ℂ) (ht : A τ = B τ*t) :
    (lpsOriginalMeromorphicRatioEquation N k A B).eval₂
      (Polynomial.evalRingHom (lpsOriginalJInvariant τ)) t = 0 := by
  classical
  let := Fintype.ofFinite (LPSOriginalMeromorphicCosets N)
  have hc : (lpsOriginalMeromorphicRatioCosetPolynomial N k A B τ).eval t = 0 := by
    rw [lpsOriginalMeromorphicRatioCosetPolynomial_eval]
    simp only [lpsOriginalMeromorphicRatioNorm, ModularForm.mcast_apply,
      ModularForm.coe_norm, Finset.prod_apply]
    apply Finset.prod_eq_zero (Finset.mem_univ (⟦(1 : 𝒮ℒ)⟧))
    simp [SlashInvariantForm.quotientFunc_mk, ht, mul_comm]
  have h := congrArg (fun P : Polynomial ℂ => P.eval t)
    (lpsOriginalMeromorphicRatioEquation_recovery N k A B τ)
  rw [Polynomial.eval_mul, Polynomial.eval_C, hc, Polynomial.eval_map] at h
  exact (mul_eq_zero.mp h).resolve_left
    (pow_ne_zero _ (ModularForm.discriminant_ne_zero τ))

/-- At a genuine nonzero-j point the reflected monic equation annihilates the literal E4 ratio. -/
lemma lpsOriginalReciprocalE4MonicEquation_root_at
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k)
    (τ : ℍ) (t : ℂ) (hj : lpsOriginalJInvariant τ ≠ 0)
    (ht : A τ = (ModularForm.E₄ τ^3)^k*t) :
    (lpsOriginalReciprocalE4MonicEquation N k A).eval₂
      (Polynomial.evalRingHom (lpsOriginalJInvariant τ)⁻¹) t = 0 := by
  apply QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_root
    (k * Nat.card (LPSOriginalMeromorphicCosets N))
    (lpsOriginalReciprocalE4NormalizedEquation N k A)
    (lpsOriginalReciprocalE4NormalizedEquation_coeff_degree N k A)
    (lpsOriginalJInvariant τ) t hj
  rw [lpsOriginalReciprocalE4NormalizedEquation, Polynomial.eval₂_mul]
  have hr := lpsOriginalMeromorphicRatioEquation_root_at N k A
    (lpsOriginalMeromorphicE4PowerAtLevel N k) τ t
    (by rwa [lpsOriginalMeromorphicE4PowerAtLevel_apply])
  rw [hr, mul_zero]

end
end QEC.Coding.TannerLiftedProduct


namespace QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
local notation "R" => LPSOriginalHolomorphicRing
local notation "H" => LPSOriginalHolomorphicFractionField
local notation "P" => Polynomial ℂ

/-- Bundle the actual E4 cube power with its proved holomorphy. -/
def lpsOriginalE4PowerHolomorphic (k : ℕ) : R :=
  ⟨lpsOriginalE4CubePower k, ModularFormClass.holo (lpsOriginalE4CubePower k)⟩

/-- Bundle the actual level modular numerator with its proved holomorphy. -/
def lpsOriginalLevelFormHolomorphic (N k : ℕ)
    (A : LPSOriginalMeromorphicLevelForm N k) : R :=
  ⟨A, ModularFormClass.holo A⟩

/-- The bundled holomorphic denominator has the same actual E4 cube-power values. -/
lemma lpsOriginalE4PowerHolomorphic_apply (k : ℕ) (τ : ℍ) :
    (lpsOriginalE4PowerHolomorphic k).val τ = (ModularForm.E₄ τ^3)^k :=
  lpsOriginalE4CubePower_apply k τ

/-- The genuine qconstant1 proves that the E4 denominator is nonzero as a holomorphic function. -/
lemma lpsOriginalE4PowerHolomorphic_ne_zero (k : ℕ) :
    lpsOriginalE4PowerHolomorphic k ≠ 0 := by
  intro hz
  have he : lpsOriginalE4CubePower k = 0 := by
    ext τ
    exact congrArg (fun f : R => f.val τ) hz
  have hc := lpsOriginalE4CubePower_qconstant k
  rw [he] at hc
  simp only [FunLike.coe_zero, UpperHalfPlane.qExpansion_zero,
    map_zero, zero_ne_one] at hc

/-- The actual j coefficient map into the holomorphic fraction field is literal polynomial evaluation. -/
lemma lpsOriginalHolomorphicJFraction_coefficient :
    (algebraMap R H).comp lpsOriginalJHolomorphicEval.toRingHom =
      Polynomial.eval₂RingHom ((algebraMap R H).comp (algebraMap ℂ R))
        (algebraMap R H lpsOriginalJHolomorphic) := by
  apply RingHom.ext
  intro p
  change algebraMap R H (p.eval₂ (algebraMap ℂ R) lpsOriginalJHolomorphic) = _
  exact Polynomial.hom_eval₂ p (algebraMap ℂ R) (algebraMap R H)
    lpsOriginalJHolomorphic

/-- Homogenization proves the original coset equation root for the actual E4 fraction. -/
lemma lpsOriginalE4Ratio_original_field_root
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) :
    (lpsOriginalMeromorphicRatioEquation N k A
      (lpsOriginalMeromorphicE4PowerAtLevel N k)).eval₂
      ((algebraMap R H).comp lpsOriginalJHolomorphicEval.toRingHom)
      ((algebraMap R H (lpsOriginalLevelFormHolomorphic N k A)) /
        (algebraMap R H (lpsOriginalE4PowerHolomorphic k))) = 0 := by
  let Φ := lpsOriginalMeromorphicRatioEquation N k A
    (lpsOriginalMeromorphicE4PowerAtLevel N k)
  let p := Φ.map lpsOriginalJHolomorphicEval.toRingHom
  have hr := lpsOriginalHolomorphicFraction_root_of_pointEquations p
    (Nat.card (LPSOriginalMeromorphicCosets N))
    (Polynomial.natDegree_map_le.trans (lpsOriginalMeromorphicRatioEquation_degree N k A
      (lpsOriginalMeromorphicE4PowerAtLevel N k)))
    (lpsOriginalLevelFormHolomorphic N k A)
    (lpsOriginalE4PowerHolomorphic k)
    (lpsOriginalE4PowerHolomorphic_ne_zero k) ?_
  · dsimp only [p] at hr
    rw [Polynomial.eval₂_map] at hr
    exact hr
  · intro τ hb
    let e := lpsOriginalHolomorphicPointEvaluation τ
    have he : e.comp lpsOriginalJHolomorphicEval.toRingHom =
        Polynomial.evalRingHom (lpsOriginalJInvariant τ) := by
      apply RingHom.ext
      intro q
      exact lpsOriginalJHolomorphicEval_apply q τ
    dsimp only [p]
    rw [Polynomial.eval₂_map, he]
    apply lpsOriginalMeromorphicRatioEquation_root_at N k A
      (lpsOriginalMeromorphicE4PowerAtLevel N k) τ
    rw [lpsOriginalMeromorphicE4PowerAtLevel_apply,
      lpsOriginalE4PowerHolomorphic_apply]
    change A τ = (ModularForm.E₄ τ^3)^k * (A τ / (ModularForm.E₄ τ^3)^k)
    rw [mul_div_cancel₀]
    exact (lpsOriginalE4PowerHolomorphic_apply k τ) ▸ hb

/-- Inner reflection gives the constructed monic reciprocal-j root in the actual holomorphic fraction field. -/
lemma lpsOriginalE4Ratio_reciprocal_field_root
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) :
    (lpsOriginalReciprocalE4MonicEquation N k A).eval₂
      (Polynomial.eval₂RingHom ((algebraMap R H).comp (algebraMap ℂ R))
        (algebraMap R H lpsOriginalJHolomorphic)⁻¹)
      ((algebraMap R H (lpsOriginalLevelFormHolomorphic N k A)) /
        (algebraMap R H (lpsOriginalE4PowerHolomorphic k))) = 0 := by
  let j := algebraMap R H lpsOriginalJHolomorphic
  have hj : j ≠ 0 := by
    intro hz
    have he : lpsOriginalJHolomorphic = 0 :=
      (IsFractionRing.injective R H) (hz.trans (map_zero _).symm)
    have hx : lpsOriginalJHolomorphicEval Polynomial.X = 0 := by
      simpa only [lpsOriginalJHolomorphicEval, Polynomial.aeval_X] using he
    exact Polynomial.X_ne_zero ((lpsOriginalJHolomorphicEval_injective)
      (hx.trans (map_zero _).symm))
  apply QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_root_field
    ((algebraMap R H).comp (algebraMap ℂ R))
    (k * Nat.card (LPSOriginalMeromorphicCosets N))
    (lpsOriginalReciprocalE4NormalizedEquation N k A)
    (lpsOriginalReciprocalE4NormalizedEquation_coeff_degree N k A)
    j _ hj
  rw [lpsOriginalReciprocalE4NormalizedEquation, Polynomial.eval₂_mul]
  have hr := lpsOriginalE4Ratio_original_field_root N k A
  rw [lpsOriginalHolomorphicJFraction_coefficient] at hr
  rw [hr, mul_zero]

end
end QEC.Coding.TannerLiftedProduct
