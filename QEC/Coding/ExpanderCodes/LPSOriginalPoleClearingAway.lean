import QEC.Coding.ExpanderCodes.LPSOriginalFiniteInteriorFibres

/-!
# Clear original poles while preserving a nonzero value at a chosen fibre

For arbitrary f in the SAME original C(j,jN), if f has no interior pole
over a, construct a polynomial H with H(a) nonzero and H(j)*f integral over
SAME C[j]. A finite product of genuine j-j(y) factors and a common exponent
clear all negative interior orders. The proved original integrality/no-pole
criterion then establishes integrality; no clearing polynomial is assumed.

Derived PK22 ex:Xpq closure for parent #449. Used by actual zero-chart
maximal-point coverage. Reciprocal-chart and public-family results remain
further mathematical obligations.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance lpsOriginalPoleAwayDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local instance lpsOriginalPoleAwayDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance lpsOriginalPoleAwayDictionary003 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance lpsOriginalPoleAwayDictionary004 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ

lemma lpsOriginalField_polynomial_clear_away (f : K) (α : ℂ)
    (hα : ∀ x : Q, lpsOriginalFilledJ N (Sum.inl x) = α →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f) :
    ∃ H : P, H.eval α ≠ 0 ∧ IsIntegral P (algebraMap P K H*f) := by
  classical
  let bad := lpsOriginalField_negativeInteriorOrders_finite N hpos hN f
  let B := bad.toFinset
  let D : Q → P := fun y => Polynomial.X - Polynomial.C (lpsOriginalFilledJ N (Sum.inl y))
  let A : P := ∏ y ∈ B, D y
  have hAnz : A ≠ 0 := (Polynomial.monic_prod_X_sub_C
    (fun y => lpsOriginalFilledJ N (Sum.inl y)) B).ne_zero
  have hi : Function.Injective (algebraMap P K) :=
    (algebraMap J K).injective.comp (IsFractionRing.injective P J)
  have hAnzk : algebraMap P K A ≠ 0 := fun hz => hAnz (hi (hz.trans (map_zero _).symm))
  have hnon (x : Q) (p : P) : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) (algebraMap P K p) :=
    lpsOriginalFieldLocalOrder_polynomial_nonnegative N hN hpos (Sum.inl x)
      (lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x) p
  have hposA (y : Q) (hy : y ∈ B) :
      0 < lpsOriginalFieldLocalOrder N hN hpos (Sum.inl y) (algebraMap P K A) := by
    let Rest : P := ∏ x ∈ B.erase y, D x
    have hsplit : A = Rest * D y := (Finset.prod_erase_mul B D hy).symm
    have hp : 0 < lpsOriginalFieldLocalOrder N hN hpos (Sum.inl y) (algebraMap P K (D y)) := by
      rw [show algebraMap P K (D y) = algebraMap P K Polynomial.X -
        algebraMap ℂ K (lpsOriginalFilledJ N (Sum.inl y)) by dsimp only [D];rw [map_sub];rfl]
      exact lpsOriginalFieldJ_sub_constant_order_pos N hpos hN _ y rfl
    rw [hsplit,map_mul,AddValuation.map_mul]
    exact lt_of_lt_of_le hp (le_add_of_nonneg_left (hnon y Rest))
  have hc : ∀ y : {y // y ∈ B}, ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl y.val) ((algebraMap P K A)^m*f) :=
    fun y => lpsOriginalFieldLocalOrder_clear_power N hpos hN (Sum.inl y.val)
      (algebraMap P K A) f (hposA y.val y.property) hAnzk
  choose n hn using hc
  let m := B.attach.sup n
  have hAα : A.eval α ≠ 0 := by
    rw [Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro y hy
    simp only [D,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
    intro hz
    have hbad : lpsOriginalFieldLocalOrder N hN hpos (Sum.inl y) f < 0 :=
      (Set.Finite.mem_toFinset bad).mp hy
    exact (not_le_of_gt hbad) (hα y (sub_eq_zero.mp hz).symm)
  refine ⟨A^m,by simpa only [Polynomial.eval_pow] using pow_ne_zero m hAα,?_⟩
  apply (lpsOriginalField_integral_iff_noInteriorPole N hpos hN _).mpr
  intro x
  rw [map_pow]
  by_cases hx : x ∈ B
  · exact hn ⟨x,hx⟩ m (Finset.le_sup (Finset.mem_attach B ⟨x,hx⟩))
  · have hf : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f := by
      apply le_of_not_gt
      intro hbad
      exact hx ((Set.Finite.mem_toFinset bad).mpr hbad)
    rw [AddValuation.map_mul,AddValuation.map_pow]
    exact add_nonneg (nsmul_nonneg (hnon x A) m) hf

end
end QEC.Coding.TannerLiftedProduct
