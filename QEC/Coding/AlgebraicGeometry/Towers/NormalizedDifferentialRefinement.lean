import QEC.Coding.AlgebraicGeometry.Differentials.DifferentialStepOrder
import QEC.Coding.AlgebraicGeometry.Towers.NormalizedCompositumEdges
import QEC.Coding.AlgebraicGeometry.Towers.QuadraticGlobalRegular

/-!
# Intrinsic differential orders along the normalized source chain

Every step uses the actual contracted places. Regular and redundant steps
have index one; at simple poles the displayed characteristic-two equation
identifies the differentials of the parameter and root. Consequently the
same source refinement also computes the intrinsic differential-order change.
-/

open IntermediateField QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

variable (A F E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [_root_.Field F] [_root_.Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [Algebra F256 F] [Algebra F256 E] [IsScalarTower F256 F E]
    [Algebra (RatFunc F256) F] [Algebra (RatFunc F256) E]
    [IsScalarTower F256 (RatFunc F256) F] [IsScalarTower F256 (RatFunc F256) E]
    [IsScalarTower (RatFunc F256) F E]
    [FiniteDimensional (RatFunc F256) F] [Algebra.IsSeparable (RatFunc F256) F]
    [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))

local notation "C" => IntermediateIntegralModels.Model A F E
local notation "P" => IntermediateIntegralModels.prime A F E Q

local instance intermediateRationalConstantTower (K : IntermediateField F E) :
    IsScalarTower F256 (RatFunc F256) K := IsScalarTower.of_algebraMap_eq' (by
  apply RingHom.ext
  intro c
  apply Subtype.ext
  exact IsScalarTower.algebraMap_apply F256 (RatFunc F256) E c)

local instance intermediateRationalRelativeTower (K L : IntermediateField F E) [Fact (K ≤ L)] :
    IsScalarTower (RatFunc F256) K L := IsScalarTower.of_algebraMap_eq' rfl

local instance intermediateConstantRelativeTower (K L : IntermediateField F E) [Fact (K ≤ L)] :
    IsScalarTower F256 K L := IsScalarTower.of_algebraMap_eq' rfl

local instance intermediateRationalFinite (K : IntermediateField F E) :
    FiniteDimensional (RatFunc F256) K := FiniteDimensional.trans (RatFunc F256) F K

local instance intermediateRationalSeparable (K : IntermediateField F E) :
    Algebra.IsSeparable (RatFunc F256) K := Algebra.IsSeparable.trans (RatFunc F256) F K

/-- The intrinsic order of the common rational differential generator at
an actual contracted intermediate place. -/
def intermediateDifferentialGeneratorOrder (K : IntermediateField F E) : ℤ :=
  differentialOrder (heightOnePlace (k := F256) (K := K) (P K))
    (functionFieldDifferentialGenerator (k := F256) (F := K))
    functionFieldDifferentialGenerator_ne_zero

local notation "g" => intermediateDifferentialGeneratorOrder A F E Q

omit [IsScalarTower F256 (RatFunc F256) F] in
theorem NormalizedEdge.differentialGeneratorOrder
    {K L : IntermediateField F E} [Fact (K ≤ L)]
    (h : NormalizedEdge A F E Q K L) :
    g L = ((P K).asIdeal.ramificationIdx' (P L).asIdeal : ℤ) * g K +
      2 * (((P K).asIdeal.ramificationIdx' (P L).asIdeal : ℤ) - 1) := by
  letI : FaithfulSMul (C K) (C L) :=
    Module.isTorsionFree_iff_faithfulSMul.mp inferInstance
  letI : NoZeroSMulDivisors (C K) (C L) := ⟨fun {_ _} h => smul_eq_zero.mp h⟩
  let Pk := heightOnePlace (k := F256) (K := K) (P K)
  let Pl := heightOnePlace (k := F256) (K := L) (P L)
  let e := (P K).asIdeal.ramificationIdx' (P L).asIdeal
  have horder (x : K) (hx : x ≠ 0) : Pl.order (algebraMap K L x) = (e : ℤ) * Pk.order x :=
    heightOnePlace_order_algebraMap (k := F256) (K := K) (L := L) (P K) (P L) x hx
  have hregular (he : e = 1) : g L = (e : ℤ) * g K + 2 * ((e : ℤ) - 1) := by
    rw [he]
    simp only [Nat.cast_one, one_mul, sub_self, mul_zero, add_zero]
    exact differentialGenerator_order_of_unramified_order_transport Pk Pl
      (fun x hx => by simpa only [he, Nat.cast_one, one_mul] using horder x hx)
  obtain ⟨a, y, hy, ha, hL⟩ := h
  have hyL : y ∈ L := by
    rw [← hL]
    exact mem_adjoin_simple_self K y
  let yL : L := ⟨y, hyL⟩
  have heq : yL ^ 2 + yL = algebraMap K L a := Subtype.ext hy
  have hgen := adjoin_in_subfield_eq_top K L y hyL hL
  rcases literalQuadratic_finrank_eq_one_or_two a yL heq hgen with hdeg | hdeg
  · exact hregular (ramificationIdx_and_weakDifferent_of_finrank_eq_one
      (C K) (C L) K L (P K) (P L) hdeg).1
  · rcases ha with hpole | hreg
    · have ha0 : a ≠ 0 := by
        intro hz
        simp [hz, GlobalPlace.order] at hpole
      have hepos : 0 < e := Nat.pos_iff_ne_zero.mpr
        (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver (P L).asIdeal (P K).ne_bot)
      have hele : e ≤ 2 := (Ideal.ramificationIdx_le_finrank (C L) K L (P L).asIdeal).trans_eq hdeg
      have hyorder := (Pk.artinSchreier_root_order_of_simplePole Pl a yL e
        hepos hele heq (horder a ha0) hpole).2
      letI : CharP F256 2 :=
        charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
      letI : CharP L 2 := charP_of_injective_algebraMap (algebraMap F256 L).injective 2
      exact differentialGenerator_order_of_quadratic_simplePole Pk Pl e horder a yL hpole hyorder heq
    · exact hregular (quadraticLiteral_integralModel_ramificationIdx_eq_one
        A (C K) (C L) K L (P K) (P L) a yL heq hdeg hgen hreg)

omit [IsScalarTower F256 (RatFunc F256) F] in
/-- Intrinsic differential-order change along the full actual normalized
chain. The correction composes by index transitivity. -/
theorem NormalizedRefinement.differentialGeneratorOrder
    {K L : IntermediateField F E} (h : NormalizedRefinement A F E Q K L) :
    letI : Fact (K ≤ L) := ⟨h.le A F E Q⟩
    g L = ((P K).asIdeal.ramificationIdx' (P L).asIdeal : ℤ) * g K +
      2 * (((P K).asIdeal.ramificationIdx' (P L).asIdeal : ℤ) - 1) := by
  induction h with
  | refl =>
      letI : Fact (K ≤ K) := ⟨le_rfl⟩
      exact NormalizedEdge.differentialGeneratorOrder A F E Q (normalizedEdge_refl A F E Q K)
  | @tail L M hchain hstep ih =>
      letI : Fact (K ≤ L) := ⟨NormalizedRefinement.le A F E Q hchain⟩
      letI : Fact (L ≤ M) := ⟨hstep.le A F E Q⟩
      letI : Fact (K ≤ M) :=
        ⟨(NormalizedRefinement.le A F E Q hchain).trans (hstep.le A F E Q)⟩
      rw [hstep.differentialGeneratorOrder A F E Q, ih,
        Ideal.ramificationIdx_algebra_tower' (P K).asIdeal (P L).asIdeal (P M).asIdeal,
        Nat.cast_mul]
      ring

/-- The full chain's order formula on the original lower fraction field
and upper integral closure, with the redundant lattice endpoints removed. -/
theorem NormalizedRefinement.integralClosure_differentialGeneratorOrder
    [FiniteDimensional (RatFunc F256) E] [Algebra.IsSeparable (RatFunc F256) E]
    [Module.IsTorsionFree A E] [IsDedekindDomain (integralClosure A E)]
    [IsFractionRing (integralClosure A E) E]
    (h : NormalizedRefinement A F E Q ⊥ ⊤) :
    differentialOrder (heightOnePlace (k := F256) (K := E) Q)
      (functionFieldDifferentialGenerator (k := F256) (F := E))
      functionFieldDifferentialGenerator_ne_zero =
    ((Q.under A).asIdeal.ramificationIdx' Q.asIdeal : ℤ) *
      differentialOrder (heightOnePlace (k := F256) (K := F) (Q.under A))
        (functionFieldDifferentialGenerator (k := F256) (F := F))
        functionFieldDifferentialGenerator_ne_zero +
      2 * (((Q.under A).asIdeal.ramificationIdx' Q.asIdeal : ℤ) - 1) := by
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
  letI : IsScalarTower F256 F K := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro c
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply F256 F E c)
  letI : IsScalarTower (RatFunc F256) F K := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro c
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply (RatFunc F256) F E c)
  letI : IsScalarTower F256 L E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (RatFunc F256) L E := IsScalarTower.of_algebraMap_eq' rfl
  have he₀ := (ramificationIdx_and_weakDifferent_of_finrank_eq_one
    A C₀ F K p P₀ IntermediateField.finrank_bot).1
  have hetop := (ramificationIdx_and_weakDifferent_of_finrank_eq_one
    C₁ (integralClosure A E) L E P₁ Q IntermediateField.finrank_top).1
  have h₀ := differentialGenerator_order_of_unramified_order_transport
    (heightOnePlace (k := F256) (K := F) p) (heightOnePlace (k := F256) (K := K) P₀)
    (fun x hx => by
      simpa only [he₀, Nat.cast_one, one_mul] using
        heightOnePlace_order_algebraMap (k := F256) (K := F) (L := K) p P₀ x hx)
  have htop := differentialGenerator_order_of_unramified_order_transport
    (heightOnePlace (k := F256) (K := L) P₁) (heightOnePlace (k := F256) (K := E) Q)
    (fun x hx => by
      simpa only [hetop, Nat.cast_one, one_mul] using
        heightOnePlace_order_algebraMap (k := F256) (K := L) (L := E) P₁ Q x hx)
  have hchain := NormalizedRefinement.differentialGeneratorOrder A F E Q h
  change g K = _ at h₀
  change _ = g L at htop
  have he : p.asIdeal.ramificationIdx' Q.asIdeal = P₀.asIdeal.ramificationIdx' P₁.asIdeal := by
    rw [Ideal.ramificationIdx_algebra_tower' p.asIdeal P₁.asIdeal Q.asIdeal, hetop, mul_one,
      Ideal.ramificationIdx_algebra_tower' p.asIdeal P₀.asIdeal P₁.asIdeal, he₀, one_mul]
  rw [htop, hchain, h₀, he]

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
