import QEC.Coding.ExpanderCodes.LPSOriginalFiniteInteriorFibres

/-!
# Actual j powers clear allowed interior poles

For every original field element regular away from interior j zeros, construct a common j power clearing all negative interior orders. The finite negative-order set, genuine positive j order and finite supremum produce the power; the zero-chart criterion proves the cleared element integral over C[j].

Derived internal PK22 ex:Xpq closure, pinned main.tex484–486, for parent #449.
Reciprocal point coverage, global differential/sheaf comparison, good reduction,
Hecke/Frobenius/Weil and the public quantum-family theorem remain further work.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance lpsOriginalJPowerClearingDictionary001 :
    Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local instance lpsOriginalJPowerClearingDictionary002 : Algebra P K :=
  ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance lpsOriginalJPowerClearingDictionary003 : Algebra ℂ K :=
  ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance lpsOriginalJPowerClearingDictionary004 : IsScalarTower ℂ P K :=
  .of_algebraMap_eq' rfl
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ

/-- Construct a common actual j power that clears every negative interior order supported at j zeros. -/
lemma lpsOriginalField_j_power_clear_interior (f : K)
    (hno : ∀ x : Q, lpsOriginalFilledJ N (Sum.inl x) ≠ 0 →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f) :
    ∃ k : ℕ, ∀ x : Q, 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x)
      ((algebraMap P K Polynomial.X)^k*f) := by
  classical
  let bad := lpsOriginalField_negativeInteriorOrders_finite N hpos hN f
  let B := bad.toFinset
  let j : K := algebraMap P K Polynomial.X
  have hj0 : j ≠ 0 := by
    simpa only [map_zero, sub_zero] using
      lpsOriginalFieldJ_sub_constant_ne_zero N hpos (0 : ℂ)
  have hposj (x : Q) (hx : x ∈ B) :
      0 < lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) j := by
    have hp : lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f < 0 :=
      (Set.Finite.mem_toFinset bad).mp hx
    have hz : lpsOriginalFilledJ N (Sum.inl x) = 0 := by
      by_contra hn
      exact (not_le_of_gt hp) (hno x hn)
    simpa only [map_zero, sub_zero] using
      lpsOriginalFieldJ_sub_constant_order_pos N hpos hN (0 : ℂ) x hz
  have hc : ∀ x : {x // x ∈ B}, ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x.val) (j^m*f) :=
    fun x => lpsOriginalFieldLocalOrder_clear_power N hpos hN
      (Sum.inl x.val) j f (hposj x.val x.property) hj0
  choose n hn using hc
  let k := B.attach.sup n
  refine ⟨k, fun x => ?_⟩
  by_cases hx : x ∈ B
  · exact hn ⟨x,hx⟩ k (Finset.le_sup (Finset.mem_attach B ⟨x,hx⟩))
  · have hf : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f := by
      apply le_of_not_gt
      intro hbad
      exact hx ((Set.Finite.mem_toFinset bad).mpr hbad)
    rw [AddValuation.map_mul, AddValuation.map_pow]
    exact add_nonneg (nsmul_nonneg
      (lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x) k) hf

/-- The constructed common j power makes the actual cleared element integral over the original zero base. -/
lemma lpsOriginalField_j_power_integral (f : K)
    (hno : ∀ x : Q, lpsOriginalFilledJ N (Sum.inl x) ≠ 0 →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f) :
    ∃ k : ℕ, IsIntegral P ((algebraMap P K Polynomial.X)^k*f) := by
  obtain ⟨k,hk⟩ := lpsOriginalField_j_power_clear_interior N hpos hN f hno
  exact ⟨k, (lpsOriginalField_integral_iff_noInteriorPole N hpos hN _).mpr hk⟩

end
end QEC.Coding.TannerLiftedProduct
