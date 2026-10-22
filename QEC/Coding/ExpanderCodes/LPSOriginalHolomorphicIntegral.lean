import QEC.Coding.ExpanderCodes.LPSOriginalMeromorphicDegreeBound
import QEC.Coding.ExpanderCodes.LPSOriginalJNormalization
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Actual original holomorphic functions are integral over C[j]

The genuine Delta cusp clearing produces a same-weight modular-form ratio.
Every actual coset of the restricted Delta power has its literal Delta value.
The existing finite-coset equation therefore has nonzero constant top coefficient
(-1)^r. Normalize it to a monic polynomial and prove its actual root equation
and integrality over the SAME C[j], rather than only algebraicity over C(j).

Derived internal closure on the original PK22 ex:Xpq route, pinned main.tex
484–486, using the existing original Gamma0(N) modular-function proof.
Parent #449 remains open; the public arbitrary-field explicit-family theorem
and its verified TeX remain unchanged.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

lemma lpsOriginalRestrictedDelta_coset (N : ℕ) (k : ℕ)
    (q : LPSOriginalMeromorphicCosets N) (τ : ℍ) :
    SlashInvariantForm.quotientFunc (lpsOriginalMeromorphicDeltaPowerAtLevel N k) q τ =
      ModularForm.discriminant τ ^ k := by
  induction q using Quotient.inductionOn with
  | h g =>
    let D := (CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow k
    change ((D : ℍ → ℂ) ∣[(k : ℤ)*12] g.val⁻¹) τ = _
    rw [SlashInvariantForm.slash_action_eqn D g.val⁻¹ (inv_mem g.property)]
    simp only [D,ModularForm.coe_pow,Pi.pow_apply]
    rfl

lemma lpsOriginalDeltaDenominatorCosetPolynomial_coeff
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) (τ : ℍ) :
    (lpsOriginalMeromorphicRatioCosetPolynomial N k A
      (lpsOriginalMeromorphicDeltaPowerAtLevel N k) τ).coeff
      (Nat.card (LPSOriginalMeromorphicCosets N)) =
        (-1 : ℂ)^(Nat.card (LPSOriginalMeromorphicCosets N)) *
          ModularForm.discriminant τ^(k * Nat.card (LPSOriginalMeromorphicCosets N)) := by
  classical
  let := Fintype.ofFinite (LPSOriginalMeromorphicCosets N)
  let B := lpsOriginalMeromorphicDeltaPowerAtLevel N k
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
      (f q).coeff 1 = -ModularForm.discriminant τ^k := by
    dsimp only [f]
    rw [Polynomial.coeff_sub,Polynomial.coeff_C,Polynomial.coeff_X_mul]
    simp only [one_ne_zero,if_false,Polynomial.coeff_C_zero,zero_sub]
    rw [lpsOriginalRestrictedDelta_coset]
  have hc := Polynomial.coeff_prod_of_natDegree_le (s := Finset.univ) f 1 hd
  change (∏ q : LPSOriginalMeromorphicCosets N, f q).coeff _ = _
  rw [Nat.card_eq_fintype_card]
  calc
    _ = ∏ q : LPSOriginalMeromorphicCosets N, (f q).coeff 1 := by
      simpa only [Finset.card_univ,mul_one] using hc
    _ = (-ModularForm.discriminant τ^k)^Fintype.card (LPSOriginalMeromorphicCosets N) := by
      simp only [hcoef,Finset.prod_const,Finset.card_univ]
    _ = _ := by rw [neg_eq_neg_one_mul,mul_pow,← pow_mul]

lemma lpsOriginalDeltaDenominatorEquation_coeff
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) :
    (lpsOriginalMeromorphicRatioEquation N k A
      (lpsOriginalMeromorphicDeltaPowerAtLevel N k)).coeff
      (Nat.card (LPSOriginalMeromorphicCosets N)) =
        Polynomial.C ((-1 : ℂ)^Nat.card (LPSOriginalMeromorphicCosets N)) := by
  apply lpsOriginalJPolynomialEvalHom_injective
  funext τ
  change Polynomial.eval (lpsOriginalJInvariant τ) _ =
    Polynomial.eval (lpsOriginalJInvariant τ) (Polynomial.C _)
  rw [Polynomial.eval_C]
  have h := congrArg (fun p : Polynomial ℂ => p.coeff (Nat.card (LPSOriginalMeromorphicCosets N)))
    (lpsOriginalMeromorphicRatioEquation_recovery N k A
      (lpsOriginalMeromorphicDeltaPowerAtLevel N k) τ)
  rw [Polynomial.coeff_C_mul,Polynomial.coeff_map,
    lpsOriginalDeltaDenominatorCosetPolynomial_coeff] at h
  exact mul_left_cancel₀ (pow_ne_zero _ (ModularForm.discriminant_ne_zero τ))
    (h.trans (mul_comm _ _))

/-- Normalize the genuine Delta-denominator equation by its nonzero constant leading coefficient. -/
def lpsOriginalHolomorphicMonicEquation (N : ℕ) [NeZero N] (k : ℕ)
    (A : LPSOriginalMeromorphicLevelForm N k) : Polynomial (Polynomial ℂ) :=
  Polynomial.C (Polynomial.C (((-1 : ℂ)^Nat.card (LPSOriginalMeromorphicCosets N))⁻¹)) *
    lpsOriginalMeromorphicRatioEquation N k A (lpsOriginalMeromorphicDeltaPowerAtLevel N k)

lemma lpsOriginalHolomorphicMonicEquation_monic (N : ℕ) [NeZero N] (k : ℕ)
    (A : LPSOriginalMeromorphicLevelForm N k) :
    (lpsOriginalHolomorphicMonicEquation N k A).Monic := by
  let r := Nat.card (LPSOriginalMeromorphicCosets N)
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one r
  · unfold lpsOriginalHolomorphicMonicEquation
    apply Polynomial.natDegree_mul_le.trans
    simpa only [Polynomial.natDegree_C,zero_add,r] using
      (lpsOriginalMeromorphicRatioEquation_degree N k A (lpsOriginalMeromorphicDeltaPowerAtLevel N k))
  · rw [lpsOriginalHolomorphicMonicEquation,Polynomial.coeff_C_mul,
      lpsOriginalDeltaDenominatorEquation_coeff,← Polynomial.C_mul,inv_mul_cancel₀]
    · exact Polynomial.C_1
    · exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

lemma lpsOriginalHolomorphicMonicEquation_root (N : ℕ) [NeZero N] (k : ℕ)
    (A : LPSOriginalMeromorphicLevelForm N k) (f : ℍ → ℂ)
    (hf : ∀ τ, A τ = ModularForm.discriminant τ^k * f τ) (τ : ℍ) :
    (lpsOriginalHolomorphicMonicEquation N k A).eval₂
      (Polynomial.evalRingHom (lpsOriginalJInvariant τ)) (f τ) = 0 := by
  rw [lpsOriginalHolomorphicMonicEquation,Polynomial.eval₂_mul]
  have h := lpsOriginalMeromorphicRatioEquation_root N k A
    (lpsOriginalMeromorphicDeltaPowerAtLevel N k) f
    (fun τ => by rw [lpsOriginalMeromorphicDeltaPowerAtLevel_apply];exact hf τ) τ
  rw [h,mul_zero]

/-- Actual cusp clearing proves a monic SAME C[j] equation for each actual interior-holomorphic representative. -/
lemma lpsOriginalFilledHolomorphic_exists_monic_annihilator
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => F (Sum.inl ⟦τ⟧))) :
    ∃ Φ : Polynomial (Polynomial ℂ), Φ.Monic ∧ ∀ τ : ℍ,
      Φ.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ)) (F (Sum.inl ⟦τ⟧)) = 0 := by
  obtain ⟨k,hk⟩ := lpsOriginalFilledMeromorphic_exists_delta_cusp_bounded N hN F hF
  let A := lpsOriginalFilledFunctionDeltaModularForm N F k hhol hk
  exact ⟨lpsOriginalHolomorphicMonicEquation N k A,lpsOriginalHolomorphicMonicEquation_monic N k A,
    lpsOriginalHolomorphicMonicEquation_root N k A (fun τ => F (Sum.inl ⟦τ⟧)) (fun _ => rfl)⟩

/-- Literal restriction-field integrality over SAME C[j], not merely algebraicity over C(j). -/
lemma lpsOriginalFilledHolomorphic_integral
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => F (Sum.inl ⟦τ⟧))) :
    letI := ((lpsOriginalFullMeromorphicJFractionEmbedding N hN).comp
      (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))).toAlgebra
    IsIntegral (Polynomial ℂ) (lpsOriginalFilledMeromorphicRestriction N hN F hF) := by
  let := ((lpsOriginalFullMeromorphicJFractionEmbedding N hN).comp
    (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))).toAlgebra
  obtain ⟨Φ,hmonic,hroot⟩ := lpsOriginalFilledHolomorphic_exists_monic_annihilator N hN F hF hhol
  refine ⟨Φ,hmonic,?_⟩
  change Φ.eval₂ ((lpsOriginalFullMeromorphicJFractionEmbedding N hN).comp
    (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ))))
      (lpsOriginalFilledMeromorphicRestriction N hN F hF) = 0
  exact lpsOriginalFilledMeromorphic_nested_annihilator_germ N hN F hF Φ hroot

end
end QEC.Coding.TannerLiftedProduct
