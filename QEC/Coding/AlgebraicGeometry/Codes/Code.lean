/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

import QEC.Coding.AlgebraicGeometry.Codes.Evaluation
import QEC.Coding.HypergraphProduct.Distance

/-!
# Elementary parameters and multiplication of AG evaluation codes

This module turns the genuine evaluation range into the
elementary AG-code conclusions needed by the Ngu24 source route.  The distance
bound is proved by subtracting the divisor of exactly the zero coordinates of
a nonzero evaluated word and invoking negative-degree vanishing.  The
coordinatewise product inclusion is proved by multiplying genuine
Riemann--Roch members and applying residue evaluation to their product.

No Riemann--Roch dimension formula, canonical-divisor duality, or parameter
bundle is used here.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped BigOperators Polynomial RatFunc WithZero

variable {k F ι : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Fintype ι]

/-- Componentwise multiplication of evaluation words. -/
def agWordStar (x y : Word k ι) : Word k ι := fun i => x i * y i

@[simp]
theorem agWordStar_apply (x y : Word k ι) (i : ι) :
    agWordStar x y i = x i * y i :=
  rfl

/-- The actual submodule spanned by componentwise products of words from two
codes.  It is deliberately a range-level construction, not stored code data. -/
def agStarProduct [Fintype k] (C D : LinearCode k ι) :
    Submodule k (Word k ι) :=
  Submodule.span k {w | ∃ x ∈ C.carrier, ∃ y ∈ D.carrier, agWordStar x y = w}

/-- A componentwise product of two codewords is a generator of their actual
star-product submodule. -/
theorem agWordStar_mem_agStarProduct [Fintype k] (C D : LinearCode k ι)
    {x y : Word k ι} (hx : x ∈ C.carrier) (hy : y ∈ D.carrier) :
    agWordStar x y ∈ agStarProduct C D :=
  Submodule.subset_span ⟨x, hx, y, hy, rfl⟩

private theorem evaluationRegularityOfMem (G : Divisor (GlobalPlace k F))
    (Q : ι → RationalPlace k F) (hG : ∀ i, G (Q i).place = 0)
    (f : GlobalPlace.riemannRochSubmodule G) (i : ι) :
    GlobalPlace.RegularAt (Q i).place (f : F) := by
  have hbound : (Q i).place.valuation (f : F) ≤ WithZero.exp (G (Q i).place) :=
    (GlobalPlace.mem_riemannRochSubmodule_iff G (f : F)).mp f.property (Q i).place
  rw [hG i] at hbound
  rw [WithZero.exp_zero] at hbound
  exact hbound

private theorem rational_evaluateRegular_mul (Q : RationalPlace k F)
    (f g : F) (hf : GlobalPlace.RegularAt Q.place f)
    (hg : GlobalPlace.RegularAt Q.place g)
    (hfg : GlobalPlace.RegularAt Q.place (f * g)) :
    Q.evaluateRegular (f * g) hfg =
      Q.evaluateRegular f hf * Q.evaluateRegular g hg := by
  let xf : GlobalPlace.valuationRing Q.place :=
    ⟨f, (GlobalPlace.mem_valuationRing_iff Q.place f).mpr hf⟩
  let xg : GlobalPlace.valuationRing Q.place :=
    ⟨g, (GlobalPlace.mem_valuationRing_iff Q.place g).mpr hg⟩
  let xfg : GlobalPlace.valuationRing Q.place :=
    ⟨f * g, (GlobalPlace.mem_valuationRing_iff Q.place (f * g)).mpr hfg⟩
  change Q.evaluate xfg = Q.evaluate xf * Q.evaluate xg
  have hmul : xfg = xf * xg := by
    rfl
  rw [hmul]
  exact Q.evaluate.map_mul xf xg

/-- Support-disjointness is preserved when two divisors are added. -/
theorem evaluationSupport_add (G H : Divisor (GlobalPlace k F))
    (Q : ι → RationalPlace k F) (hG : ∀ i, G (Q i).place = 0)
    (hH : ∀ i, H (Q i).place = 0) :
    ∀ i, (G + H) (Q i).place = 0 := by
  intro i
  rw [Finsupp.add_apply, hG i, hH i]
  rfl

/-- The all-ones word is in an evaluation code whenever the defining divisor
is coefficientwise nonnegative. -/
theorem agEvaluation_one_mem [Fintype k]
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hG : ∀ i, G (Q i).place = 0) (hGnonnegative : Divisor.Nonnegative G) :
    (1 : Word k ι) ∈ (agEvaluationCode G Q hG).carrier := by
  have hconstant : (1 : F) ∈ GlobalPlace.riemannRochSubmodule G := by
    rw [GlobalPlace.mem_riemannRochSubmodule_iff]
    intro P
    simpa using WithZero.exp_le_exp.mpr (hGnonnegative P)
  let f : GlobalPlace.riemannRochSubmodule G := ⟨1, hconstant⟩
  change (1 : Word k ι) ∈ (agEvaluationLinearMap G Q hG).range
  refine ⟨f, ?_⟩
  ext i
  rw [agEvaluationLinearMap_apply]
  change (Q i).evaluateRegular (1 : F) _ = 1
  simpa using (Q i).evaluateRegular_algebraMap (1 : k)

/-- The actual star-product submodule of two evaluation codes is contained in
the evaluation code for the sum divisor. -/
theorem starProduct_le_agEvaluationCode_add [Fintype k]
    (G H : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hG : ∀ i, G (Q i).place = 0)
    (hH : ∀ i, H (Q i).place = 0) :
    agStarProduct (agEvaluationCode G Q hG) (agEvaluationCode H Q hH) ≤
      (agEvaluationCode (G + H) Q (evaluationSupport_add G H Q hG hH)).carrier := by
  apply Submodule.span_le.mpr
  rintro w ⟨x, hx, y, hy, rfl⟩
  change x ∈ (agEvaluationLinearMap G Q hG).range at hx
  change y ∈ (agEvaluationLinearMap H Q hH).range at hy
  rcases hx with ⟨f, rfl⟩
  rcases hy with ⟨g, rfl⟩
  let hGH : ∀ i, (G + H) (Q i).place = 0 := evaluationSupport_add G H Q hG hH
  let fg : GlobalPlace.riemannRochSubmodule (G + H) :=
    ⟨(f : F) * (g : F),
      GlobalPlace.mul_mem_riemannRochSubmodule_add f.property g.property⟩
  change agWordStar (agEvaluationLinearMap G Q hG f)
      (agEvaluationLinearMap H Q hH g) ∈
        (agEvaluationLinearMap (G + H) Q hGH).range
  refine ⟨fg, ?_⟩
  ext i
  simp only [agEvaluationLinearMap_apply, agWordStar_apply]
  change (Q i).evaluateRegular ((f : F) * (g : F)) _ =
    (Q i).evaluateRegular (f : F) _ * (Q i).evaluateRegular (g : F) _
  exact rational_evaluateRegular_mul (Q i) (f : F) (g : F)
    (evaluationRegularityOfMem G Q hG f i)
    (evaluationRegularityOfMem H Q hH g i)
    (evaluationRegularityOfMem (G + H) Q hGH fg i)

/-- The elementary source-convention lower bound on the extended minimum
distance of the genuine evaluation code.  A negative divisor degree gives a
zero code and hence extended distance infinity; the bound consequently uses
the literal signed difference before converting it to a natural number. -/
theorem agEvaluation_distance_lower_bound
    [Fintype k] [DecidableEq k] [DecidableEq ι]
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0) :
    (Int.toNat ((Fintype.card ι : ℤ) -
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G) : WithTop Nat) ≤
      QEC.Coding.HypergraphProduct.extendedMinimumDistance (agEvaluationCode G Q hG) := by
  classical
  by_cases hdegree : 0 ≤ Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G
  · rw [QEC.Coding.HypergraphProduct.extendedMinimumDistance]
    apply QEC.Coding.HypergraphProduct.le_finitePredicateMinimum
    intro x hx
    change x ∈ (agEvaluationLinearMap G Q hG).range ∧ x ≠ 0 at hx
    rcases hx with ⟨hxrange, hxzero⟩
    rcases hxrange with ⟨f, rfl⟩
    let S : Finset ι := Finset.univ.filter fun i => agEvaluationLinearMap G Q hG f i = 0
    have hzeroOn : ∀ i, i ∈ S → agEvaluationLinearMap G Q hG f i = 0 := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hmem : (f : F) ∈
        GlobalPlace.riemannRochSubmodule (G - zeroCoordinateDivisor Q S) :=
      evaluationZeroOn_mem_riemannRochSubmodule_sub G Q hQ hG S f hzeroOn
    have hnotNegative : ¬ Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (G - zeroCoordinateDivisor Q S) < 0 := by
      intro hnegative
      have hbot := GlobalPlace.riemannRochSubmodule_eq_bot_of_negative_degree
        k F (G - zeroCoordinateDivisor Q S) hnegative
      have hfzero : (f : F) = 0 := by
        have hmemBot : (f : F) ∈ (⊥ : Submodule k F) := by
          rw [← hbot]
          exact hmem
        exact (Submodule.mem_bot k).mp hmemBot
      apply hxzero
      have hfsubtype : f = 0 := by
        apply Subtype.ext
        exact hfzero
      simpa [hfsubtype]
    have hzeroCardLe : (S.card : ℤ) ≤
        Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G := by
      by_contra hnot
      apply hnotNegative
      rw [Divisor.degree_sub, zeroCoordinateDivisor_degree_eq_card]
      omega
    have hzeroCardLeNat : S.card ≤ Int.toNat
        (Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G) := by
      omega
    have hnonzeroSupport :
        (Finset.univ.filter fun i : ι => ¬ agEvaluationLinearMap G Q hG f i = 0) =
          hammingSupport (agEvaluationLinearMap G Q hG f) := by
      ext i
      simp [hammingSupport]
    have hzeroCard : S.card =
        Fintype.card ι - HammingWeight (agEvaluationLinearMap G Q hG f) := by
      have hpartition := Finset.card_filter_add_card_filter_not
        (s := Finset.univ) (fun i : ι => agEvaluationLinearMap G Q hG f i = 0)
      rw [hnonzeroSupport, ← HammingWeight_eq_card_hammingSupport] at hpartition
      have hunivCard : (Finset.univ : Finset ι).card = Fintype.card ι := by
        simp
      rw [hunivCard] at hpartition
      exact Nat.eq_sub_of_add_eq hpartition
    have hweight : Fintype.card ι - Int.toNat
        (Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G) ≤
          HammingWeight (agEvaluationLinearMap G Q hG f) := by
      omega
    have hsigned : Int.toNat ((Fintype.card ι : ℤ) -
        Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G) =
        Fintype.card ι - Int.toNat
          (Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G) := by
      omega
    rw [hsigned]
    exact WithTop.coe_le_coe.mpr hweight
  · have hnegative : Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G < 0 :=
      lt_of_not_ge hdegree
    have hspace : GlobalPlace.riemannRochSubmodule G = ⊥ :=
      GlobalPlace.riemannRochSubmodule_eq_bot_of_negative_degree k F G hnegative
    have hcode : (agEvaluationCode G Q hG).carrier = ⊥ := by
      change (agEvaluationLinearMap G Q hG).range = ⊥
      apply le_antisymm
      · rintro x ⟨f, rfl⟩
        change agEvaluationLinearMap G Q hG f = 0
        have hfzero : (f : F) = 0 := by
          have hmemBot : (f : F) ∈ (⊥ : Submodule k F) := by
            rw [← hspace]
            exact f.property
          exact (Submodule.mem_bot k).mp hmemBot
        have hfsubtype : f = 0 := by
          apply Subtype.ext
          exact hfzero
        simpa [hfsubtype]
      · exact bot_le
    rw [(QEC.Coding.HypergraphProduct.extendedMinimumDistance_eq_top_iff _).mpr hcode]
    exact le_top

end QEC.Coding.AlgebraicGeometry
