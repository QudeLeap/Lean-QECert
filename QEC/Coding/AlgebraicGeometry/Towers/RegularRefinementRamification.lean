import QEC.Coding.AlgebraicGeometry.Towers.RegularRefinement
import QEC.Coding.AlgebraicGeometry.Towers.QuadraticGlobalRegular

/-!
# Ramification of literal regular refinements

Each actual regular quadratic generator has unit different after localizing
at the contraction of the fixed final prime. Index transitivity then proves
index one along the whole finite chain.
-/

open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

variable (A F E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [_root_.Field F] [_root_.Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [Algebra F256 F] [Algebra F256 E] [IsScalarTower F256 F E]
    [IsDedekindDomain (integralClosure A E)] [Module.Finite A (integralClosure A E)]
    [IsFractionRing (integralClosure A E) E]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))

local notation "C" => IntermediateIntegralModels.Model A F E
local notation "P" => IntermediateIntegralModels.prime A F E Q
local notation "R" => heightOnePlace (k := F256) (K := E) Q

/-- Ambient regularity descends to the actual contracted integral-model
place, by the positive ramification scaling of its normalized order. -/
theorem intermediatePrime_order_nonnegative_of_ambient_regular
    (K : IntermediateField F E) (a : K) (ha : (a : E) ∈ (R).valuationRing) :
    0 ≤ (heightOnePlace (k := F256) (K := K) (P K)).order a := by
  by_cases ha0 : a = 0
  · simp [ha0, GlobalPlace.order]
  letI : Algebra (C K) E := ((algebraMap K E).comp (algebraMap (C K) K)).toAlgebra
  letI : IsScalarTower (C K) K E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (C K) (integralClosure A E) E := IsScalarTower.of_algebraMap_eq' rfl
  letI : Q.asIdeal.LiesOver (P K).asIdeal := ⟨rfl⟩
  have hscale := heightOnePlace_order_algebraMap (k := F256) (K := K) (L := E) (P K) Q a ha0
  have hpositive : 0 < (P K).asIdeal.ramificationIdx' Q.asIdeal :=
    Nat.pos_iff_ne_zero.mpr
      (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver Q.asIdeal (P K).ne_bot)
  have haE : (a : E) ≠ 0 := by
    have hne := (algebraMap K E).injective.ne ha0
    simp only [map_zero] at hne
    exact hne
  have hregular := ((R).regularAt_iff_order_nonnegative haE).mp ha
  change 0 ≤ (R).order (algebraMap K E a) at hregular
  rw [hscale] at hregular
  exact (mul_nonneg_iff_of_pos_left (Int.natCast_pos.mpr hpositive)).mp hregular

theorem RegularQuadraticEdge.ramificationIdx_eq_one
    {K L : IntermediateField F E} [Fact (K ≤ L)]
    (h : RegularQuadraticEdge R K L) : (P K).asIdeal.ramificationIdx' (P L).asIdeal = 1 := by
  obtain ⟨y, hy, ha, hL⟩ := h
  let a : K := ⟨y ^ 2 + y, ha⟩
  have hyL : y ∈ L := by
    rw [hL]
    exact (show F⟮y⟯ ≤ K ⊔ F⟮y⟯ from le_sup_right) (mem_adjoin_simple_self F y)
  let yL : L := ⟨y, hyL⟩
  have heq : yL ^ 2 + yL = algebraMap K L a := Subtype.ext rfl
  have hgen := adjoin_in_subfield_eq_top K L y hyL (by
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, ← hL])
  have hareg : 0 ≤ (heightOnePlace (k := F256) (K := K) (P K)).order a :=
    intermediatePrime_order_nonnegative_of_ambient_regular A F E Q K a
      ((R).valuationRing.add_mem _ _ ((R).valuationRing.pow_mem hy 2) hy)
  rcases literalQuadratic_finrank_eq_one_or_two a yL heq hgen with hdeg | hdeg
  · exact (ramificationIdx_and_weakDifferent_of_finrank_eq_one
      (C K) (C L) K L (P K) (P L) hdeg).1
  · exact quadraticLiteral_integralModel_ramificationIdx_eq_one
      A (C K) (C L) K L (P K) (P L) a yL heq hdeg hgen hareg

theorem RegularRefinement.ramificationIdx_eq_one
    {K L : IntermediateField F E} (h : RegularRefinement R K L) :
    letI : Fact (K ≤ L) := ⟨h.le R⟩
    (P K).asIdeal.ramificationIdx' (P L).asIdeal = 1 := by
  induction h with
  | refl =>
      letI : Fact (K ≤ K) := ⟨le_rfl⟩
      have hid : algebraMap (C K) (C K) = RingHom.id (C K) := by
        apply RingHom.ext
        intro x
        rfl
      have hmap : Ideal.map (algebraMap (C K) (C K)) (P K).asIdeal = (P K).asIdeal := by
        rw [hid, Ideal.map_id]
      have he := Ideal.ramificationIdx_map_self_eq_one (p := (P K).asIdeal)
        (by rw [hmap]; exact (P K).isPrime.ne_top) (by rw [hmap]; exact (P K).ne_bot)
      simp only [hmap] at he ⊢
      exact he
  | @tail L M hchain hstep ih =>
      letI : Fact (K ≤ L) := ⟨RegularRefinement.le R hchain⟩
      letI : Fact (L ≤ M) := ⟨hstep.le R⟩
      letI : Fact (K ≤ M) := ⟨(RegularRefinement.le R hchain).trans (hstep.le R)⟩
      rw [Ideal.ramificationIdx_algebra_tower' (P K).asIdeal (P L).asIdeal (P M).asIdeal,
        ih, hstep.ramificationIdx_eq_one A F E Q, one_mul]

/-- Removing the redundant bottom and top copies states index one on the
original actual integral closure, at the original supplied prime. -/
theorem RegularRefinement.integralClosure_ramificationIdx_eq_one
    [Module.IsTorsionFree A E]
    (h : RegularRefinement R (⊥ : IntermediateField F E) ⊤) :
    (Q.under A).asIdeal.ramificationIdx' Q.asIdeal = 1 := by
  let K : IntermediateField F E := ⊥
  let L : IntermediateField F E := ⊤
  let C₀ := C K
  let C₁ := C L
  let P₀ := P K
  let P₁ := P L
  let p := Q.under A
  letI : Fact (K ≤ L) := ⟨bot_le⟩
  letI : Module.IsTorsionFree A (integralClosure A E) := IsIntegralClosure.isTorsionFree A E
  letI : P₀.asIdeal.LiesOver p.asIdeal := by
    refine Ideal.LiesOver.mk ?_
    change Ideal.comap (algebraMap A (integralClosure A E)) Q.asIdeal =
      Ideal.comap (algebraMap A C₀) (Ideal.comap (algebraMap C₀ (integralClosure A E)) Q.asIdeal)
    rw [Ideal.comap_comap]
    rfl
  letI : Q.asIdeal.LiesOver P₁.asIdeal := ⟨rfl⟩
  letI : P₁.asIdeal.LiesOver p.asIdeal := by
    refine Ideal.LiesOver.mk ?_
    change Ideal.comap (algebraMap A (integralClosure A E)) Q.asIdeal =
      Ideal.comap (algebraMap A C₁) (Ideal.comap (algebraMap C₁ (integralClosure A E)) Q.asIdeal)
    rw [Ideal.comap_comap]
    rfl
  letI : Module.IsTorsionFree C₁ (integralClosure A E) :=
    Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  letI : Algebra C₁ E := ((algebraMap L E).comp (algebraMap C₁ L)).toAlgebra
  letI : IsScalarTower C₁ L E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower C₁ (integralClosure A E) E := IsScalarTower.of_algebraMap_eq' rfl
  have h₀ := (ramificationIdx_and_weakDifferent_of_finrank_eq_one
    A C₀ F K p P₀ IntermediateField.finrank_bot).1
  have h₁ := RegularRefinement.ramificationIdx_eq_one A F E Q h
  have htop := (ramificationIdx_and_weakDifferent_of_finrank_eq_one
    C₁ (integralClosure A E) L E P₁ Q IntermediateField.finrank_top).1
  change p.asIdeal.ramificationIdx' Q.asIdeal = 1
  rw [Ideal.ramificationIdx_algebra_tower' p.asIdeal P₁.asIdeal Q.asIdeal, htop, mul_one,
    Ideal.ramificationIdx_algebra_tower' p.asIdeal P₀.asIdeal P₁.asIdeal, h₀, h₁, one_mul]

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
