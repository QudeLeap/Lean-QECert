import QEC.Coding.ExpanderCodes.LPSOriginalInfinityFiniteFibres

/-!
# Clear actual reciprocal poles away from a fibre

For arbitrary original field elements regular over a chosen actual coordinate fibre, construct a polynomial nonzero at that value which clears all other poles. Actual evaluation kernels provide positive-order factors; a finite product and common power give genuine same-field integrality.

Derived internal PK22 ex:Xpq closure, pinned main.tex484–486, for parent #449.
Global point injectivity, differential/sheaf comparison, good reduction,
Hecke/Frobenius/Weil and the public quantum-family theorem remain further work.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance LPSOriginalInfinityPoleClearingAwayDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN

omit [NeZero N] in
/-- The actual reciprocal polynomial map into the same original generated field is faithful. -/
lemma lpsOriginalReciprocalPolynomialMap_injective :
    Function.Injective (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos) := by
  let : Algebra P J := lpsOriginalReciprocalBaseCAlgebra
  let : IsFractionRing P J := lpsOriginalReciprocalBaseC_isFractionRing
  exact (algebraMap J K).injective.comp (IsFractionRing.injective P J)

/-- Construct a polynomial nonzero at a chosen fibre value that clears every other actual reciprocal pole. -/
lemma lpsOriginalField_reciprocal_polynomial_clear_away (f : K) (α : ℂ)
    (hα : ∀ x : S, lpsOriginalInfinityCoordinate N hpos hN x = α →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos x.val f) :
    ∃ H : P, H.eval α ≠ 0 ∧
      (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).IsIntegralElem
        (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos H*f) := by
  classical
  let φ := lpsOriginalReciprocalComplexFieldPolynomialMap N hpos
  let β := lpsOriginalInfinityCoordinate N hpos hN
  let bad := lpsOriginalField_negativeInfinityOrders_finite N hpos hN f
  let B := bad.toFinset
  let D : S → P := fun y => Polynomial.X - Polynomial.C (β y)
  let A : P := ∏ y ∈ B, D y
  have hAnz : A ≠ 0 := (Polynomial.monic_prod_X_sub_C β B).ne_zero
  have hi := lpsOriginalReciprocalPolynomialMap_injective N hpos
  have hAnzk : φ A ≠ 0 := fun hz => hAnz (hi (hz.trans (map_zero _).symm))
  have hnon (x : S) (p : P) : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x.val (φ p) :=
    lpsOriginalReciprocalFieldPolynomialMap_order_nonnegative N hpos hN x.val x.property p
  have hposA (y : S) (hy : y ∈ B) :
      0 < lpsOriginalFieldLocalOrder N hN hpos y.val (φ A) := by
    let Rest : P := ∏ x ∈ B.erase y, D x
    have hsplit : A = Rest * D y := (Finset.prod_erase_mul B D hy).symm
    have hp : 0 < lpsOriginalFieldLocalOrder N hN hpos y.val (φ (D y)) := by
      apply (lpsOriginalInfinityEvaluation_eq_zero_iff_order_pos N hpos hN
        y.val y.property (lpsOriginalInfinityPolynomialChartMap N hpos (D y))).mp
      rw [lpsOriginalInfinityEvaluation_polynomial]
      simp only [D,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,sub_self,β]
    rw [hsplit,map_mul,AddValuation.map_mul]
    exact lt_of_lt_of_le hp (le_add_of_nonneg_left (hnon y Rest))
  have hc : ∀ y : {y // y ∈ B}, ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos y.val.val ((φ A)^m*f) :=
    fun y => lpsOriginalFieldLocalOrder_clear_power N hpos hN y.val.val
      (φ A) f (hposA y.val y.property) hAnzk
  choose n hn using hc
  let m := B.attach.sup n
  have hAα : A.eval α ≠ 0 := by
    rw [Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro y hy
    simp only [D,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
    intro hz
    have hbad : lpsOriginalFieldLocalOrder N hN hpos y.val f < 0 :=
      (Set.Finite.mem_toFinset bad).mp hy
    exact (not_le_of_gt hbad) (hα y (sub_eq_zero.mp hz).symm)
  refine ⟨A^m,by simpa only [Polynomial.eval_pow] using pow_ne_zero m hAα,?_⟩
  apply (lpsOriginalField_reciprocal_integral_iff_regularPoints N hpos hN _).mpr
  intro x
  rw [map_pow]
  by_cases hx : x ∈ B
  · exact hn ⟨x,hx⟩ m (Finset.le_sup (Finset.mem_attach B ⟨x,hx⟩))
  · have hf : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x.val f := by
      apply le_of_not_gt
      intro hbad
      exact hx ((Set.Finite.mem_toFinset bad).mpr hbad)
    rw [AddValuation.map_mul,AddValuation.map_pow]
    exact add_nonneg (nsmul_nonneg (hnon x A) m) hf

end
end QEC.Coding.TannerLiftedProduct
