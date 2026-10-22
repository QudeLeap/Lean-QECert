import QEC.Coding.AlgebraicGeometry.Towers.Step

import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral

/-!
# One source-facing Garcia--Stichtenoth recursion step

This file constructs the actual degree-sixteen step

`y^16 + y = x^16 / (x^15 + 1)`

at a normalized simple pole of `x`.  The reciprocal root is Eisenstein, gives
the next normalized simple pole, and generates an integral closure whose
different has exact exponent `30 = 2 * (16 - 1)`.  This is the local
weak-ramification calculation used by the Stichtenoth normal-closure tower.
No recursive tower, normal closure, genus, divisor, or asymptotic conclusion
is packaged here.
-/

open Polynomial

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {K : Type*} [Field K] [Algebra F256 K]

/-- The literal right-hand side in the source-facing recursion. -/
def sourceStepRhs (x : K) : K :=
  x ^ 16 / (x ^ 15 + 1)

private theorem sourceStep_coordinate_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) : x ≠ 0 := by
  intro hzero
  subst x
  simp [GlobalPlace.order] at hx

private theorem sourceStep_order_pow
    (P : GlobalPlace F256 K) (x : K) (n : ℕ) :
    P.order (x ^ n) = (n : ℤ) * P.order x := by
  unfold GlobalPlace.order
  rw [map_pow, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

private theorem sourceStep_valuation_eq_exp_neg_order
    (P : GlobalPlace F256 K) (y : K) (hy : y ≠ 0) :
    P.valuation y = WithZero.exp (-P.order y) := by
  unfold GlobalPlace.order
  rw [neg_neg]
  exact (WithZero.exp_log (P.valuation.ne_zero_iff.mpr hy)).symm

private theorem sourceStep_denominator_order
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    P.order (x ^ 15 + 1) = -15 := by
  have hx_ne := sourceStep_coordinate_ne_zero P x hx
  have hxpow_ne : x ^ 15 ≠ 0 := pow_ne_zero 15 hx_ne
  have hxpow_order : P.order (x ^ 15) = -15 := by
    rw [sourceStep_order_pow, hx]
    norm_num
  have hxpow_value : P.valuation (x ^ 15) = WithZero.exp (15 : ℤ) := by
    rw [sourceStep_valuation_eq_exp_neg_order P (x ^ 15) hxpow_ne,
      hxpow_order]
    norm_num
  have hlt : P.valuation 1 < P.valuation (x ^ 15) := by
    rw [map_one, hxpow_value, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  unfold GlobalPlace.order
  rw [P.valuation.map_add_eq_of_lt_left hlt, hxpow_value,
    WithZero.log_exp]

private theorem sourceStep_denominator_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    x ^ 15 + 1 ≠ 0 := by
  intro hzero
  have horder := sourceStep_denominator_order P x hx
  rw [hzero] at horder
  simp [GlobalPlace.order] at horder

/-- At a simple pole of `x`, the source recursion right-hand side again has
a normalized simple pole. -/
theorem sourceStepRhs_order
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    P.order (sourceStepRhs x) = -1 := by
  have hx_ne := sourceStep_coordinate_ne_zero P x hx
  have hden_ne := sourceStep_denominator_ne_zero P x hx
  rw [sourceStepRhs, div_eq_mul_inv,
    P.order_mul (pow_ne_zero 16 hx_ne) (inv_ne_zero hden_ne),
    P.order_inv, sourceStep_order_pow, hx,
    sourceStep_denominator_order P x hx]
  norm_num

private theorem sourceStepRhs_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepRhs x ≠ 0 := by
  rw [sourceStepRhs]
  exact div_ne_zero (pow_ne_zero 16 (sourceStep_coordinate_ne_zero P x hx))
    (sourceStep_denominator_ne_zero P x hx)

/-- The reciprocal of the source recursion right-hand side, as the actual
uniformizer in the lower valuation ring. -/
noncomputable def sourceStepUniformizer
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    P.valuationRing :=
  reciprocalUniformizer P (sourceStepRhs x) (sourceStepRhs_order P x hx)

@[simp]
theorem coe_sourceStepUniformizer
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepUniformizer P x hx : K) = (sourceStepRhs x)⁻¹ :=
  rfl

private theorem sourceStepUniformizer_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepUniformizer P x hx ≠ 0 := by
  rw [ne_eq, Subtype.ext_iff]
  exact inv_ne_zero (sourceStepRhs_ne_zero P x hx)

/-- The reciprocal Eisenstein polynomial
`W^16 + t W^15 + t`, where `t` is the inverse recursion right-hand side. -/
noncomputable def sourceStepReciprocalPolynomial
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    P.valuationRing[X] :=
  X ^ 16 + C (sourceStepUniformizer P x hx) * X ^ 15 +
    C (sourceStepUniformizer P x hx)

theorem sourceStepReciprocalPolynomial_monic
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepReciprocalPolynomial P x hx).Monic := by
  rw [sourceStepReciprocalPolynomial, add_assoc]
  exact Monic.add_of_left (monic_X_pow 16) (by
    calc
      (C (sourceStepUniformizer P x hx) * X ^ 15 +
          C (sourceStepUniformizer P x hx)).degree ≤ (15 : WithBot ℕ) := by
        apply degree_add_le_of_degree_le
        · exact degree_C_mul_X_pow_le 15 _
        · exact degree_C_le.trans (by norm_num)
      _ < ((X : P.valuationRing[X]) ^ 16).degree := by
        rw [degree_X_pow]
        norm_num)

@[simp]
theorem sourceStepReciprocalPolynomial_natDegree
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepReciprocalPolynomial P x hx).natDegree = 16 := by
  apply natDegree_eq_of_degree_eq_some
  rw [sourceStepReciprocalPolynomial, add_assoc,
    degree_add_eq_left_of_degree_lt]
  · exact degree_X_pow (R := P.valuationRing) 16
  · calc
      (C (sourceStepUniformizer P x hx) * X ^ 15 +
          C (sourceStepUniformizer P x hx)).degree ≤ (15 : WithBot ℕ) := by
        apply degree_add_le_of_degree_le
        · exact degree_C_mul_X_pow_le 15 _
        · exact degree_C_le.trans (by norm_num)
      _ < ((X : P.valuationRing[X]) ^ 16).degree := by
        rw [degree_X_pow]
        norm_num

theorem sourceStepReciprocalPolynomial_isEisenstein
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepReciprocalPolynomial P x hx).IsEisensteinAt
      (IsLocalRing.maximalIdeal P.valuationRing) := by
  have ht_mem : sourceStepUniformizer P x hx ∈
      IsLocalRing.maximalIdeal P.valuationRing := by
    rw [maximalIdeal_eq_span_reciprocalUniformizer P
      (sourceStepRhs x) (sourceStepRhs_order P x hx)]
    exact Ideal.mem_span_singleton_self _
  have ht_not_sq : sourceStepUniformizer P x hx ∉
      (IsLocalRing.maximalIdeal P.valuationRing) ^ 2 := by
    rw [maximalIdeal_eq_span_reciprocalUniformizer P
      (sourceStepRhs x) (sourceStepRhs_order P x hx),
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdvd
    obtain ⟨c, hc⟩ := hdvd
    have ht0 := sourceStepUniformizer_ne_zero P x hx
    have hone : (1 : P.valuationRing) = sourceStepUniformizer P x hx * c := by
      apply mul_left_cancel₀ ht0
      calc
        sourceStepUniformizer P x hx * 1 = sourceStepUniformizer P x hx := mul_one _
        _ = sourceStepUniformizer P x hx ^ 2 * c := hc
        _ = sourceStepUniformizer P x hx *
            (sourceStepUniformizer P x hx * c) := by rw [pow_two, mul_assoc]
    have hunit : IsUnit (sourceStepUniformizer P x hx) :=
      isUnit_iff_exists_inv.mpr ⟨c, hone.symm⟩
    have hnotunit : ¬IsUnit (sourceStepUniformizer P x hx) := by
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using ht_mem
    exact hnotunit hunit
  apply (sourceStepReciprocalPolynomial_monic P x hx).isEisensteinAt_of_mem_of_notMem
  · exact (IsLocalRing.maximalIdeal.isMaximal P.valuationRing).ne_top
  · intro n hn
    rw [sourceStepReciprocalPolynomial_natDegree] at hn
    by_cases hn0 : n = 0
    · subst n
      have hcoeff : (sourceStepReciprocalPolynomial P x hx).coeff 0 =
          sourceStepUniformizer P x hx := by
        simp only [sourceStepReciprocalPolynomial, coeff_add, coeff_X_pow,
          Polynomial.coeff_C_mul_X_pow, coeff_C_zero]
        norm_num
      rw [hcoeff]
      exact ht_mem
    by_cases hn15 : n = 15
    · subst n
      have hcoeff : (sourceStepReciprocalPolynomial P x hx).coeff 15 =
          sourceStepUniformizer P x hx := by
        simp only [sourceStepReciprocalPolynomial, coeff_add, coeff_X_pow,
          Polynomial.coeff_C_mul_X_pow, coeff_C]
        norm_num
      rw [hcoeff]
      exact ht_mem
    · have hn16 : n ≠ 16 := by omega
      simp only [sourceStepReciprocalPolynomial, coeff_add, coeff_X_pow,
        Polynomial.coeff_C_mul_X_pow, coeff_C, if_neg hn16,
        if_neg hn15, if_neg hn0, zero_add, Ideal.zero_mem]
  · have hcoeff : (sourceStepReciprocalPolynomial P x hx).coeff 0 =
        sourceStepUniformizer P x hx := by
      simp only [sourceStepReciprocalPolynomial, coeff_add, coeff_X_pow,
        Polynomial.coeff_C_mul_X_pow, coeff_C_zero]
      norm_num
    rw [hcoeff]
    exact ht_not_sq

/-- The reciprocal polynomial transported to the lower function field. -/
noncomputable def sourceStepPolynomial
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) : K[X] :=
  (sourceStepReciprocalPolynomial P x hx).map
    (algebraMap P.valuationRing K)

private theorem sourceStepPolynomial_eq_explicit
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepPolynomial P x hx =
      X ^ 16 + C (sourceStepRhs x)⁻¹ * X ^ 15 + C (sourceStepRhs x)⁻¹ := by
  simp [sourceStepPolynomial, sourceStepReciprocalPolynomial,
    sourceStepUniformizer, coe_reciprocalUniformizer]

theorem sourceStepPolynomial_monic
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepPolynomial P x hx).Monic :=
  (sourceStepReciprocalPolynomial_monic P x hx).map _

@[simp]
theorem sourceStepPolynomial_natDegree
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepPolynomial P x hx).natDegree = 16 := by
  rw [sourceStepPolynomial,
    (sourceStepReciprocalPolynomial_monic P x hx).natDegree_map,
    sourceStepReciprocalPolynomial_natDegree]

theorem sourceStepPolynomial_irreducible
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Irreducible (sourceStepPolynomial P x hx) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  have hirr : Irreducible (sourceStepReciprocalPolynomial P x hx) :=
    (sourceStepReciprocalPolynomial_isEisenstein P x hx).irreducible
      (IsLocalRing.maximalIdeal.isMaximal P.valuationRing).isPrime
      (sourceStepReciprocalPolynomial_monic P x hx).isPrimitive
      (by rw [sourceStepReciprocalPolynomial_natDegree]; norm_num)
  exact (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (K := K) (sourceStepReciprocalPolynomial_monic P x hx)).mp hirr

theorem sourceStepPolynomial_separable
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepPolynomial P x hx).Separable := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  rw [Polynomial.separable_iff_derivative_ne_zero
    (sourceStepPolynomial_irreducible P x hx)]
  have hderivative : (sourceStepPolynomial P x hx).derivative =
      C (sourceStepRhs x)⁻¹ * X ^ 14 := by
    rw [sourceStepPolynomial_eq_explicit]
    simp only [derivative_add, derivative_X_pow,
      derivative_C_mul_X_pow, derivative_C]
    reduce_mod_char!
    norm_num
  rw [hderivative]
  exact mul_ne_zero
    (C_ne_zero.mpr (inv_ne_zero (sourceStepRhs_ne_zero P x hx)))
    (pow_ne_zero _ X_ne_zero)

/-- The actual degree-sixteen source recursion field. -/
abbrev SourceStepField
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :=
  AdjoinRoot (sourceStepPolynomial P x hx)

noncomputable instance sourceStepPolynomialIrreducibleFact
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Fact (Irreducible (sourceStepPolynomial P x hx)) :=
  ⟨sourceStepPolynomial_irreducible P x hx⟩

noncomputable instance sourceStepConstantScalarTower
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsScalarTower F256 K (SourceStepField P x hx) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The literal embedding into one source recursion step. -/
noncomputable def sourceStepEmbedding
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    K →ₐ[F256] SourceStepField P x hx :=
  (Algebra.ofId K (SourceStepField P x hx)).restrictScalars F256

/-- The reciprocal root in one source recursion step. -/
noncomputable def sourceStepReciprocalRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    SourceStepField P x hx :=
  AdjoinRoot.root (sourceStepPolynomial P x hx)

private theorem sourceStep_eval2_trinomial
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (y : S) (a b : R) (m n : ℕ) :
    eval₂ f y (X ^ m + C a * X ^ n + C b) =
      y ^ m + f a * y ^ n + f b := by
  rw [eval₂_add, eval₂_add, eval₂_X_pow, eval₂_mul f y,
    eval₂_C, eval₂_X_pow, eval₂_C]

theorem sourceStepReciprocalRoot_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepReciprocalRoot P x hx ≠ 0 := by
  intro hzero
  have hroot := AdjoinRoot.eval₂_root (sourceStepPolynomial P x hx)
  change AdjoinRoot.root (sourceStepPolynomial P x hx) = 0 at hzero
  rw [hzero] at hroot
  have hpolyEval := congrArg
    (eval₂ (AdjoinRoot.of (sourceStepPolynomial P x hx)) 0)
    (sourceStepPolynomial_eq_explicit P x hx)
  have hexplicit :
      eval₂ (AdjoinRoot.of (sourceStepPolynomial P x hx)) 0
          (X ^ 16 + C (sourceStepRhs x)⁻¹ * X ^ 15 +
            C (sourceStepRhs x)⁻¹) = 0 :=
    hpolyEval.symm.trans hroot
  rw [sourceStep_eval2_trinomial
    (AdjoinRoot.of (sourceStepPolynomial P x hx)) 0
      (sourceStepRhs x)⁻¹ (sourceStepRhs x)⁻¹ 16 15] at hexplicit
  have hmap : AdjoinRoot.of (sourceStepPolynomial P x hx)
      (sourceStepRhs x)⁻¹ ≠ 0 := by
    simpa only [map_zero] using
      (AdjoinRoot.of (sourceStepPolynomial P x hx)).injective.ne
        (inv_ne_zero (sourceStepRhs_ne_zero P x hx))
  apply hmap
  simpa only [zero_pow (by norm_num : (16 : ℕ) ≠ 0),
    zero_pow (by norm_num : (15 : ℕ) ≠ 0), mul_zero, zero_add,
    add_zero] using hexplicit

theorem sourceStepReciprocalRoot_equation
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepReciprocalRoot P x hx ^ 16 +
        sourceStepEmbedding P x hx (sourceStepRhs x)⁻¹ *
          sourceStepReciprocalRoot P x hx ^ 15 +
        sourceStepEmbedding P x hx (sourceStepRhs x)⁻¹ = 0 := by
  have hroot := AdjoinRoot.eval₂_root (sourceStepPolynomial P x hx)
  have hpolyEval := congrArg
    (eval₂ (AdjoinRoot.of (sourceStepPolynomial P x hx))
      (AdjoinRoot.root (sourceStepPolynomial P x hx)))
    (sourceStepPolynomial_eq_explicit P x hx)
  have hexplicit :
      eval₂ (AdjoinRoot.of (sourceStepPolynomial P x hx))
          (AdjoinRoot.root (sourceStepPolynomial P x hx))
          (X ^ 16 + C (sourceStepRhs x)⁻¹ * X ^ 15 +
            C (sourceStepRhs x)⁻¹) = 0 :=
    hpolyEval.symm.trans hroot
  rw [sourceStep_eval2_trinomial
    (AdjoinRoot.of (sourceStepPolynomial P x hx))
      (AdjoinRoot.root (sourceStepPolynomial P x hx))
      (sourceStepRhs x)⁻¹ (sourceStepRhs x)⁻¹ 16 15] at hexplicit
  simpa [sourceStepEmbedding, sourceStepReciprocalRoot] using hexplicit

/-- The literal next coordinate, inverse to the reciprocal Eisenstein root. -/
noncomputable def sourceStepCoordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    SourceStepField P x hx :=
  (sourceStepReciprocalRoot P x hx)⁻¹

/-- One constructed step satisfies the source-facing recursion exactly. -/
theorem sourceStepCoordinate_equation
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepCoordinate P x hx ^ 16 + sourceStepCoordinate P x hx =
      sourceStepEmbedding P x hx (sourceStepRhs x) := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP (SourceStepField P x hx) 2 :=
    charP_of_injective_algebraMap
      (algebraMap K (SourceStepField P x hx)).injective 2
  let a := sourceStepEmbedding P x hx (sourceStepRhs x)
  let w := sourceStepReciprocalRoot P x hx
  have ha : a ≠ 0 := by
    have hport := (sourceStepEmbedding P x hx).injective.ne (sourceStepRhs_ne_zero P x hx)
    simp only [a, map_zero] at hport ⊢
    exact hport
  have hw : w ≠ 0 := sourceStepReciprocalRoot_ne_zero P x hx
  have hroot := sourceStepReciprocalRoot_equation P x hx
  rw [map_inv₀] at hroot
  change w ^ 16 + a⁻¹ * w ^ 15 + a⁻¹ = 0 at hroot
  field_simp [ha] at hroot
  change w⁻¹ ^ 16 + w⁻¹ = a
  field_simp [hw]
  have htwo : (2 : SourceStepField P x hx) = 0 :=
    CharP.cast_eq_zero (SourceStepField P x hx) 2
  linear_combination hroot - a * w ^ 16 * htwo

/-- The actual source step has degree sixteen. -/
theorem sourceStep_finrank
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Module.finrank K (SourceStepField P x hx) = 16 := by
  calc
    Module.finrank K (SourceStepField P x hx) =
        (AdjoinRoot.powerBasis
          (sourceStepPolynomial_monic P x hx).ne_zero).dim :=
      PowerBasis.finrank _
    _ = (sourceStepPolynomial P x hx).natDegree := rfl
    _ = 16 := sourceStepPolynomial_natDegree P x hx

noncomputable instance sourceStepFiniteDimensional
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    FiniteDimensional K (SourceStepField P x hx) :=
  (AdjoinRoot.powerBasis (sourceStepPolynomial_monic P x hx).ne_zero).finite

noncomputable instance sourceStep_isSeparable
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Algebra.IsSeparable K (SourceStepField P x hx) := by
  let w := sourceStepReciprocalRoot P x hx
  have hwsep : IsSeparable K w := by
    dsimp [w, sourceStepReciprocalRoot]
    rw [IsSeparable, AdjoinRoot.minpoly_root
      (sourceStepPolynomial_monic P x hx).ne_zero,
      (sourceStepPolynomial_monic P x hx).leadingCoeff, inv_one, C.map_one,
      mul_one]
    exact sourceStepPolynomial_separable P x hx
  letI : Algebra.IsSeparable K
      (IntermediateField.adjoin K ({w} : Set (SourceStepField P x hx))) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
      (F := K) (E := SourceStepField P x hx) (x := w)).mpr hwsep
  have hAlgebraAdjoin : Algebra.adjoin K
      ({w} : Set (SourceStepField P x hx)) = ⊤ := by
    have hport := (AdjoinRoot.powerBasis
      (sourceStepPolynomial_monic P x hx).ne_zero).adjoin_gen_eq_top
    simp only [w, sourceStepReciprocalRoot] at hport ⊢
    exact hport
  have hadjoin : IntermediateField.adjoin K
      ({w} : Set (SourceStepField P x hx)) = ⊤ := by
    apply top_unique
    intro y _
    exact (IntermediateField.algebra_adjoin_le_adjoin K
      ({w} : Set (SourceStepField P x hx))) (by
        rw [hAlgebraAdjoin]
        exact Set.mem_univ y)
  refine ⟨fun y => IntermediateField.isSeparable_of_mem_isSeparable
    (F := K) (E := SourceStepField P x hx)
    (L := IntermediateField.adjoin K ({w} : Set (SourceStepField P x hx))) ?_⟩
  rw [hadjoin]
  exact Set.mem_univ y

instance sourceStepValuationRingScalarTower
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsScalarTower P.valuationRing K (SourceStepField P x hx) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The actual integral closure of the lower valuation ring in one source
step. -/
abbrev SourceStepIntegralClosure
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :=
  integralClosure P.valuationRing (SourceStepField P x hx)

noncomputable instance sourceStepIntegralClosureIsTorsionFree
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Module.IsTorsionFree P.valuationRing
      (SourceStepIntegralClosure P x hx) := by
  letI : Module.IsTorsionFree P.valuationRing (SourceStepField P x hx) :=
    Module.IsTorsionFree.trans_faithfulSMul
      P.valuationRing K (SourceStepField P x hx)
  exact IsIntegralClosure.isTorsionFree
    P.valuationRing (SourceStepField P x hx)

noncomputable instance sourceStepIntegralClosureFinite
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Module.Finite P.valuationRing (SourceStepIntegralClosure P x hx) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite P.valuationRing K (SourceStepField P x hx)
    (SourceStepIntegralClosure P x hx)

noncomputable instance sourceStepIntegralClosureIsFractionRing
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsFractionRing (SourceStepIntegralClosure P x hx)
      (SourceStepField P x hx) :=
  integralClosure.isFractionRing_of_finite_extension K
    (SourceStepField P x hx)

noncomputable instance sourceStepIntegralClosureIsDedekindDomain
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsDedekindDomain (SourceStepIntegralClosure P x hx) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain P.valuationRing K
    (SourceStepField P x hx)

/-- The reciprocal root as an actual integral element. -/
noncomputable def sourceStepIntegralRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    SourceStepIntegralClosure P x hx := by
  refine ⟨sourceStepReciprocalRoot P x hx, ?_⟩
  refine ⟨sourceStepReciprocalPolynomial P x hx,
    sourceStepReciprocalPolynomial_monic P x hx, ?_⟩
  change eval₂
      ((AdjoinRoot.of (sourceStepPolynomial P x hx)).comp
        (algebraMap P.valuationRing K))
      (sourceStepReciprocalRoot P x hx)
      (sourceStepReciprocalPolynomial P x hx) = 0
  rw [← eval₂_map]
  exact AdjoinRoot.eval₂_root (sourceStepPolynomial P x hx)

@[simp]
theorem coe_sourceStepIntegralRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepIntegralRoot P x hx : SourceStepField P x hx) =
      sourceStepReciprocalRoot P x hx :=
  rfl

/-- The lower uniformizer embedded in the source-step integral closure. -/
noncomputable def sourceStepIntegralUniformizer
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    SourceStepIntegralClosure P x hx := by
  refine ⟨sourceStepEmbedding P x hx (sourceStepRhs x)⁻¹, ?_⟩
  change IsIntegral P.valuationRing
    (algebraMap P.valuationRing (SourceStepField P x hx)
      (sourceStepUniformizer P x hx))
  exact isIntegral_algebraMap

@[simp]
theorem coe_sourceStepIntegralUniformizer
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepIntegralUniformizer P x hx : SourceStepField P x hx) =
      sourceStepEmbedding P x hx (sourceStepRhs x)⁻¹ :=
  rfl

private theorem exists_sourceStepUpperIdeal
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    ∃ Q : Ideal (SourceStepIntegralClosure P x hx),
      Q.IsMaximal ∧ Q.LiesOver (IsLocalRing.maximalIdeal P.valuationRing) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := SourceStepIntegralClosure P x hx)
    (IsLocalRing.maximalIdeal P.valuationRing)

/-- A concrete upper prime above the lower simple-pole place. -/
noncomputable def sourceStepUpperIdeal
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Ideal (SourceStepIntegralClosure P x hx) :=
  Classical.choose (exists_sourceStepUpperIdeal P x hx)

private theorem sourceStepUpperIdeal_isMaximal
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepUpperIdeal P x hx).IsMaximal :=
  (Classical.choose_spec (exists_sourceStepUpperIdeal P x hx)).1

theorem sourceStepUpperIdeal_liesOver
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepUpperIdeal P x hx).LiesOver
      (IsLocalRing.maximalIdeal P.valuationRing) :=
  (Classical.choose_spec (exists_sourceStepUpperIdeal P x hx)).2

@[simp]
theorem algebraMap_sourceStepUniformizer
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    algebraMap P.valuationRing (SourceStepIntegralClosure P x hx)
        (sourceStepUniformizer P x hx) =
      sourceStepIntegralUniformizer P x hx := by
  rfl

theorem sourceStepIntegralUniformizer_mem_upperIdeal
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepIntegralUniformizer P x hx ∈ sourceStepUpperIdeal P x hx := by
  have hover := (sourceStepUpperIdeal_liesOver P x hx).over
  have hbase : sourceStepUniformizer P x hx ∈
      IsLocalRing.maximalIdeal P.valuationRing := by
    rw [maximalIdeal_eq_span_reciprocalUniformizer P
      (sourceStepRhs x) (sourceStepRhs_order P x hx)]
    exact Ideal.mem_span_singleton_self _
  change algebraMap P.valuationRing (SourceStepIntegralClosure P x hx)
      (sourceStepUniformizer P x hx) ∈ sourceStepUpperIdeal P x hx
  change sourceStepUniformizer P x hx ∈
    Ideal.under P.valuationRing (sourceStepUpperIdeal P x hx)
  rw [← hover]
  exact hbase

theorem sourceStepIntegralRoot_equation
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepIntegralRoot P x hx ^ 16 +
        sourceStepIntegralUniformizer P x hx *
          sourceStepIntegralRoot P x hx ^ 15 +
        sourceStepIntegralUniformizer P x hx = 0 := by
  apply Subtype.ext
  have hport := sourceStepReciprocalRoot_equation P x hx
  exact hport

theorem sourceStepIntegralRoot_mem_upperIdeal
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepIntegralRoot P x hx ∈ sourceStepUpperIdeal P x hx := by
  let Q := sourceStepUpperIdeal P x hx
  let w := sourceStepIntegralRoot P x hx
  let t := sourceStepIntegralUniformizer P x hx
  have ht : t ∈ Q := sourceStepIntegralUniformizer_mem_upperIdeal P x hx
  have hterm : t * w ^ 15 ∈ Q := Q.mul_mem_right _ ht
  have hrest : t * w ^ 15 + t ∈ Q := Q.add_mem hterm ht
  have heq : w ^ 16 + t * w ^ 15 + t = 0 :=
    sourceStepIntegralRoot_equation P x hx
  have hw16eq : w ^ 16 = -(t * w ^ 15 + t) := by
    linear_combination heq
  have hw16 : w ^ 16 ∈ Q := hw16eq.symm ▸ Q.neg_mem hrest
  exact (sourceStepUpperIdeal_isMaximal P x hx).isPrime.mem_of_pow_mem 16 hw16

theorem map_maximalIdeal_eq_span_sourceStepIntegralUniformizer
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Ideal.map (algebraMap P.valuationRing (SourceStepIntegralClosure P x hx))
        (IsLocalRing.maximalIdeal P.valuationRing) =
      Ideal.span ({sourceStepIntegralUniformizer P x hx} :
        Set (SourceStepIntegralClosure P x hx)) := by
  rw [maximalIdeal_eq_span_reciprocalUniformizer P
      (sourceStepRhs x) (sourceStepRhs_order P x hx),
    Ideal.map_span, Set.image_singleton]
  change Ideal.span
      ({algebraMap P.valuationRing (SourceStepIntegralClosure P x hx)
        (sourceStepUniformizer P x hx)} :
        Set (SourceStepIntegralClosure P x hx)) = _
  rw [algebraMap_sourceStepUniformizer]

theorem span_sourceStepIntegralUniformizer_le_upperIdeal_pow_sixteen
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Ideal.span ({sourceStepIntegralUniformizer P x hx} :
        Set (SourceStepIntegralClosure P x hx)) ≤
      (sourceStepUpperIdeal P x hx) ^ 16 := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  let Q := sourceStepUpperIdeal P x hx
  let w := sourceStepIntegralRoot P x hx
  let t := sourceStepIntegralUniformizer P x hx
  have ht : t ∈ Q := sourceStepIntegralUniformizer_mem_upperIdeal P x hx
  have hw : w ∈ Q := sourceStepIntegralRoot_mem_upperIdeal P x hx
  have hw16 : w ^ 16 ∈ Q ^ 16 := Ideal.pow_mem_pow hw 16
  have hw15 : w ^ 15 ∈ Q ^ 15 := Ideal.pow_mem_pow hw 15
  have hterm : t * w ^ 15 ∈ Q ^ 16 := by
    have hmul : t * w ^ 15 ∈ Q ^ 1 * Q ^ 15 :=
      Ideal.mul_mem_mul (by simpa only [pow_one] using ht) hw15
    simpa only [pow_one, ← pow_succ'] using hmul
  have hsum : w ^ 16 + t * w ^ 15 ∈ Q ^ 16 :=
    (Q ^ 16).add_mem hw16 hterm
  have heq : w ^ 16 + t * w ^ 15 + t = 0 :=
    sourceStepIntegralRoot_equation P x hx
  have hteq : t = -(w ^ 16 + t * w ^ 15) := by
    linear_combination heq
  change t ∈ Q ^ 16
  rw [hteq]
  exact (Q ^ 16).neg_mem hsum

/-- The chosen upper prime as a height-one prime. -/
noncomputable def sourceStepUpperHeightOne
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsDedekindDomain.HeightOneSpectrum (SourceStepIntegralClosure P x hx) :=
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  letI : (sourceStepUpperIdeal P x hx).LiesOver
      (IsLocalRing.maximalIdeal P.valuationRing) :=
    sourceStepUpperIdeal_liesOver P x hx
  { asIdeal := sourceStepUpperIdeal P x hx
    isPrime := (sourceStepUpperIdeal_isMaximal P x hx).isPrime
    ne_bot := Ideal.ne_bot_of_liesOver_of_ne_bot
      (IsDiscreteValuationRing.not_a_field P.valuationRing)
      (sourceStepUpperIdeal P x hx) }

theorem sourceStep_ramificationIdx_eq_sixteen
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx'
      (sourceStepUpperIdeal P x hx) = 16 := by
  let O := P.valuationRing
  let C := SourceStepIntegralClosure P x hx
  let L := SourceStepField P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let Q : Ideal C := sourceStepUpperIdeal P x hx
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  letI : Q.LiesOver m := sourceStepUpperIdeal_liesOver P x hx
  letI : Q.IsPrime := (sourceStepUpperIdeal_isMaximal P x hx).isPrime
  letI : NoZeroSMulDivisors O C := ⟨fun {_ _} h => smul_eq_zero.mp h⟩
  have hm0 : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap0 : Ideal.map (algebraMap O C) m ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm0
  have hmap_le : Ideal.map (algebraMap O C) m ≤ Q ^ 16 := by
    simpa only [O, C, m, Q,
      map_maximalIdeal_eq_span_sourceStepIntegralUniformizer] using
      span_sourceStepIntegralUniformizer_le_upperIdeal_pow_sixteen P x hx
  have hmult : multiplicity Q (Q ^ 16) ≤
      multiplicity Q (Ideal.map (algebraMap O C) m) :=
    (sourceStepUpperHeightOne P x hx).multiplicity_le_of_ideal_ge hmap_le hmap0
  have hQprime : Prime Q :=
    Ideal.prime_of_isPrime (sourceStepUpperHeightOne P x hx).ne_bot inferInstance
  have hlower : 16 ≤ m.ramificationIdx' Q := by
    calc
      16 = multiplicity Q (Q ^ 16) := by
        symm
        exact multiplicity_pow_self_of_prime hQprime 16
      _ ≤ multiplicity Q (Ideal.map (algebraMap O C) m) := hmult
      _ = m.ramificationIdx' Q :=
        (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
          hmap0 (inferInstance : Q.IsPrime)).symm
  have hupper : m.ramificationIdx' Q ≤ Module.finrank K L :=
    Ideal.ramificationIdx_le_finrank C K L Q
  have hfinrank : Module.finrank K L = 16 := sourceStep_finrank P x hx
  change m.ramificationIdx' Q = 16
  omega

theorem sourceStepIntegralRoot_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepIntegralRoot P x hx ≠ 0 := by
  intro hzero
  have hcoe := congrArg
    (fun y : SourceStepIntegralClosure P x hx =>
      (y : SourceStepField P x hx)) hzero
  simpa only [coe_sourceStepIntegralRoot, map_zero] using
    (sourceStepReciprocalRoot_ne_zero P x hx hcoe)

theorem sourceStepIntegralRoot_not_mem_upperIdeal_sq
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepIntegralRoot P x hx ∉ (sourceStepUpperIdeal P x hx) ^ 2 := by
  let O := P.valuationRing
  let C := SourceStepIntegralClosure P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let Q : Ideal C := sourceStepUpperIdeal P x hx
  let w : C := sourceStepIntegralRoot P x hx
  let t : C := sourceStepIntegralUniformizer P x hx
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  intro hw2
  change w ∈ Q ^ 2 at hw2
  have ht : t ∈ Q := sourceStepIntegralUniformizer_mem_upperIdeal P x hx
  have hw : w ∈ Q := sourceStepIntegralRoot_mem_upperIdeal P x hx
  have ht16 : t ∈ Q ^ 16 := by
    exact span_sourceStepIntegralUniformizer_le_upperIdeal_pow_sixteen P x hx
      (Ideal.mem_span_singleton_self t)
  have hw15 : w ^ 15 ∈ Q ^ 15 := Ideal.pow_mem_pow hw 15
  have hw16_17 : w ^ 16 ∈ Q ^ 17 := by
    have hmul : w * w ^ 15 ∈ Q ^ 2 * Q ^ 15 :=
      Ideal.mul_mem_mul hw2 hw15
    rw [show w * w ^ 15 = w ^ 16 by ring,
      show Q ^ 2 * Q ^ 15 = Q ^ 17 by
        rw [show 17 = 2 + 15 by norm_num, pow_add]] at hmul
    exact hmul
  have hterm17 : t * w ^ 15 ∈ Q ^ 17 := by
    have hbase : t * w ∈ Q ^ 16 * Q := Ideal.mul_mem_mul ht16 hw
    have hQpow : Q ^ 16 * Q = Q ^ 17 := by
      simpa only [show 17 = 16 + 1 by norm_num] using (pow_succ Q 16).symm
    rw [hQpow] at hbase
    have hmul := (Q ^ 17).mul_mem_right (w ^ 14) hbase
    convert hmul using 1 <;> ring
  have hsum : w ^ 16 + t * w ^ 15 ∈ Q ^ 17 :=
    (Q ^ 17).add_mem hw16_17 hterm17
  have heq : w ^ 16 + t * w ^ 15 + t = 0 :=
    sourceStepIntegralRoot_equation P x hx
  have hteq : t = -(w ^ 16 + t * w ^ 15) := by
    linear_combination heq
  have ht17 : t ∈ Q ^ 17 := by
    rw [hteq]
    exact (Q ^ 17).neg_mem hsum
  have hmap17 : Ideal.map (algebraMap O C) m ≤ Q ^ 17 := by
    rw [show Ideal.map (algebraMap O C) m = Ideal.span ({t} : Set C) by
      simpa only [O, C, m, t] using
        map_maximalIdeal_eq_span_sourceStepIntegralUniformizer P x hx,
      Ideal.span_le, Set.singleton_subset_iff]
    exact ht17
  have hm0 : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap0 : Ideal.map (algebraMap O C) m ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm0
  have hmult17 : multiplicity Q (Q ^ 17) ≤
      multiplicity Q (Ideal.map (algebraMap O C) m) :=
    (sourceStepUpperHeightOne P x hx).multiplicity_le_of_ideal_ge hmap17 hmap0
  have hQprime : Prime Q := Ideal.prime_of_isPrime
    (sourceStepUpperHeightOne P x hx).ne_bot
    (sourceStepUpperIdeal_isMaximal P x hx).isPrime
  have hleft : multiplicity Q (Q ^ 17) = 17 :=
    multiplicity_pow_self_of_prime hQprime 17
  have hright : multiplicity Q (Ideal.map (algebraMap O C) m) = 16 := by
    rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
      hmap0 (sourceStepUpperIdeal_isMaximal P x hx).isPrime]
    exact sourceStep_ramificationIdx_eq_sixteen P x hx
  omega

theorem sourceStepIntegralRoot_multiplicity
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    multiplicity (sourceStepUpperIdeal P x hx)
      (Ideal.span ({sourceStepIntegralRoot P x hx} :
        Set (SourceStepIntegralClosure P x hx))) = 1 := by
  let C := SourceStepIntegralClosure P x hx
  let Q : Ideal C := sourceStepUpperIdeal P x hx
  let w : C := sourceStepIntegralRoot P x hx
  let I : Ideal C := Ideal.span ({w} : Set C)
  have hI0 : I ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    simpa only [w] using sourceStepIntegralRoot_ne_zero P x hx
  have hle : Ideal.map (algebraMap C C) I ≤ Q ^ 1 := by
    rw [Algebra.algebraMap_self, Ideal.map_id, pow_one]
    exact Ideal.span_le.2 (Set.singleton_subset_iff.2
      (sourceStepIntegralRoot_mem_upperIdeal P x hx))
  have hnle : ¬Ideal.map (algebraMap C C) I ≤ Q ^ (1 + 1) := by
    rw [Algebra.algebraMap_self, Ideal.map_id, one_add_one_eq_two]
    intro h
    exact sourceStepIntegralRoot_not_mem_upperIdeal_sq P x hx
      (h (Ideal.mem_span_singleton_self w))
  have hram : I.ramificationIdx' Q = 1 := Ideal.ramificationIdx_spec hle hnle
  have hmap0 : Ideal.map (algebraMap C C) I ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hI0
  calc
    multiplicity Q I = multiplicity Q (Ideal.map (algebraMap C C) I) := by
      rw [Algebra.algebraMap_self, Ideal.map_id]
    _ = I.ramificationIdx' Q :=
      (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hmap0
        (sourceStepUpperIdeal_isMaximal P x hx).isPrime).symm
    _ = 1 := hram

/-- The normalized upper place of one source recursion step. -/
noncomputable def sourceStepAbovePlace
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    GlobalPlace F256 (SourceStepField P x hx) where
  valuation := (sourceStepUpperHeightOne P x hx).valuation
    (SourceStepField P x hx)
  normalized := (sourceStepUpperHeightOne P x hx).valuation_surjective
    (SourceStepField P x hx)

private theorem sourceStepAbovePlace_order_integral_eq_multiplicity
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    {y : SourceStepIntegralClosure P x hx} (hy : y ≠ 0) :
    (sourceStepAbovePlace P x hx).order
        (algebraMap (SourceStepIntegralClosure P x hx)
          (SourceStepField P x hx) y) =
      (multiplicity (sourceStepUpperIdeal P x hx) (Ideal.span {y}) : ℤ) := by
  unfold sourceStepAbovePlace GlobalPlace.order
  rw [(sourceStepUpperHeightOne P x hx).valuation_of_algebraMap,
    (sourceStepUpperHeightOne P x hx).intValuation_eq_exp_neg_multiplicity hy,
    WithZero.log_exp]
  simp only [sourceStepUpperHeightOne]
  ring

private theorem sourceStepAbovePlace_order_reciprocalRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepAbovePlace P x hx).order
      (sourceStepReciprocalRoot P x hx) = 1 := by
  change (sourceStepAbovePlace P x hx).order
    (algebraMap (SourceStepIntegralClosure P x hx)
      (SourceStepField P x hx) (sourceStepIntegralRoot P x hx)) = 1
  rw [sourceStepAbovePlace_order_integral_eq_multiplicity P x hx
      (sourceStepIntegralRoot_ne_zero P x hx),
    sourceStepIntegralRoot_multiplicity]
  norm_num

/-- The next source coordinate again has normalized order `-1`. -/
theorem sourceStepAbovePlace_order_coordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepAbovePlace P x hx).order (sourceStepCoordinate P x hx) = -1 := by
  rw [sourceStepCoordinate, GlobalPlace.order_inv,
    sourceStepAbovePlace_order_reciprocalRoot]

private theorem sourceStepReciprocalPolynomial_aeval_sourceStepReciprocalRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Polynomial.aeval (sourceStepReciprocalRoot P x hx)
        (sourceStepReciprocalPolynomial P x hx) = 0 := by
  rw [Polynomial.aeval_def]
  change eval₂
      ((AdjoinRoot.of (sourceStepPolynomial P x hx)).comp
        (algebraMap P.valuationRing K))
      (sourceStepReciprocalRoot P x hx)
      (sourceStepReciprocalPolynomial P x hx) = 0
  rw [← eval₂_map]
  exact AdjoinRoot.eval₂_root (sourceStepPolynomial P x hx)

private theorem sourceStep_minpoly_reciprocalRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    minpoly P.valuationRing (sourceStepReciprocalRoot P x hx) =
      sourceStepReciprocalPolynomial P x hx := by
  symm
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  letI : Module.IsTorsionFree P.valuationRing (SourceStepField P x hx) :=
    Module.IsTorsionFree.trans_faithfulSMul
      P.valuationRing K (SourceStepField P x hx)
  have hw_integral : IsIntegral P.valuationRing
      (sourceStepReciprocalRoot P x hx) := by
    have hport := (sourceStepIntegralRoot P x hx).property
    simp only [coe_sourceStepIntegralRoot] at hport ⊢
    exact hport
  have hmin_K : minpoly K (sourceStepReciprocalRoot P x hx) =
      sourceStepPolynomial P x hx := by
    simpa only [sourceStepReciprocalRoot, AdjoinRoot.powerBasis_gen] using
      AdjoinRoot.minpoly_powerBasis_gen_of_monic
        (sourceStepPolynomial_monic P x hx)
  have hmin_natDegree :
      (minpoly P.valuationRing
        (sourceStepReciprocalRoot P x hx)).natDegree = 16 := by
    calc
      (minpoly P.valuationRing
          (sourceStepReciprocalRoot P x hx)).natDegree =
          ((minpoly P.valuationRing
            (sourceStepReciprocalRoot P x hx)).map
              (algebraMap P.valuationRing K)).natDegree :=
        ((minpoly.monic hw_integral).natDegree_map _).symm
      _ = (minpoly K (sourceStepReciprocalRoot P x hx)).natDegree := by
        rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hw_integral]
      _ = (sourceStepPolynomial P x hx).natDegree := by rw [hmin_K]
      _ = 16 := sourceStepPolynomial_natDegree P x hx
  apply minpoly.IsIntegrallyClosed.unique_of_degree_le_degree_minpoly
  · exact sourceStepReciprocalPolynomial_monic P x hx
  · exact sourceStepReciprocalPolynomial_aeval_sourceStepReciprocalRoot P x hx
  · rw [degree_eq_natDegree
        (sourceStepReciprocalPolynomial_monic P x hx).ne_zero,
      degree_eq_natDegree (minpoly.ne_zero hw_integral),
      sourceStepReciprocalPolynomial_natDegree, hmin_natDegree]

private theorem sourceStep_minpoly_integralRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    minpoly P.valuationRing (sourceStepIntegralRoot P x hx) =
      sourceStepReciprocalPolynomial P x hx := by
  calc
    minpoly P.valuationRing (sourceStepIntegralRoot P x hx) =
        minpoly P.valuationRing
          (algebraMap (SourceStepIntegralClosure P x hx)
            (SourceStepField P x hx) (sourceStepIntegralRoot P x hx)) :=
      (minpoly.algebraMap_eq
        (IsFractionRing.injective (SourceStepIntegralClosure P x hx)
          (SourceStepField P x hx))
        (sourceStepIntegralRoot P x hx)).symm
    _ = minpoly P.valuationRing (sourceStepReciprocalRoot P x hx) := by
      congr 1
    _ = sourceStepReciprocalPolynomial P x hx :=
      sourceStep_minpoly_reciprocalRoot P x hx

theorem sourceStepIntegralClosure_adjoin_root_eq_top
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Algebra.adjoin P.valuationRing
        ({sourceStepIntegralRoot P x hx} :
          Set (SourceStepIntegralClosure P x hx)) = ⊤ := by
  let O := P.valuationRing
  let L := SourceStepField P x hx
  let C := SourceStepIntegralClosure P x hx
  let t : O := sourceStepUniformizer P x hx
  let w : C := sourceStepIntegralRoot P x hx
  let B : PowerBasis K L :=
    AdjoinRoot.powerBasis (sourceStepPolynomial_monic P x hx).ne_zero
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  have ht_irreducible : Irreducible t :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr (by
      simpa only [O, t, sourceStepUniformizer] using
        maximalIdeal_eq_span_reciprocalUniformizer P
          (sourceStepRhs x) (sourceStepRhs_order P x hx))
  have hB_integral : IsIntegral O B.gen := by
    have hport := (sourceStepIntegralRoot P x hx).property
    simp only [O, B, AdjoinRoot.powerBasis_gen, coe_sourceStepIntegralRoot] at hport ⊢
    exact hport
  apply top_unique
  intro z _
  have hz_integral : IsIntegral O (z : L) := z.property
  have hcleared := Algebra.discr_mul_isIntegral_mem_adjoin K
    hB_integral hz_integral
  have hdisc_integral : IsIntegral O (Algebra.discr K B.basis) := by
    apply Algebra.discr_isIntegral K
    intro i
    rw [B.basis_eq_pow]
    exact hB_integral.pow _
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hdisc_integral
  have hdisc_ne_zero : Algebra.discr K B.basis ≠ 0 :=
    (Algebra.discr_isUnit_of_basis K B.basis).ne_zero
  have ha_ne_zero : a ≠ 0 := by
    intro ha_zero
    apply hdisc_ne_zero
    rw [← ha, ha_zero, map_zero]
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha_ne_zero ht_irreducible
  rw [← ha, IsScalarTower.algebraMap_smul, hu] at hcleared
  have hcleared' := Subalgebra.smul_mem
    (Algebra.adjoin O ({B.gen} : Set L)) hcleared (↑(u⁻¹) : O)
  have ht_power : t ^ n • (z : L) ∈ Algebra.adjoin O ({B.gen} : Set L) := by
    simpa only [smul_smul, ← mul_assoc, Units.inv_mul, one_mul] using hcleared'
  have hminpoly_eisenstein :
      (minpoly O B.gen).IsEisensteinAt (Ideal.span ({t} : Set O)) := by
    have hE := sourceStepReciprocalPolynomial_isEisenstein P x hx
    rw [maximalIdeal_eq_span_reciprocalUniformizer P
      (sourceStepRhs x) (sourceStepRhs_order P x hx)] at hE
    have hminB : minpoly O B.gen = sourceStepReciprocalPolynomial P x hx := by
      have hport := sourceStep_minpoly_reciprocalRoot P x hx
      simp only [O, B, AdjoinRoot.powerBasis_gen] at hport ⊢
      exact hport
    rw [hminB]
    simpa only [O, t, sourceStepUniformizer] using hE
  have hz_adjoin : (z : L) ∈ Algebra.adjoin O ({B.gen} : Set L) :=
    mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
      (B := B) (irreducible_iff_prime.mp ht_irreducible) hB_integral
      hz_integral ht_power hminpoly_eisenstein
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz_adjoin
  obtain ⟨q, hq⟩ := hz_adjoin
  have hq_mem : Polynomial.aeval w q ∈ Algebra.adjoin O ({w} : Set C) :=
    Polynomial.aeval_mem_adjoin_singleton O w
  have hq_eq : Polynomial.aeval w q = z := by
    apply Subtype.ext
    have hmap := Polynomial.aeval_algHom_apply
      (IsScalarTower.toAlgHom O C L) w q
    change (IsScalarTower.toAlgHom O C L) (Polynomial.aeval w q) = (z : L)
    rw [← hmap]
    have hport := hq
    simp only [O, L, C, w, B, coe_sourceStepIntegralRoot, AdjoinRoot.powerBasis_gen] at hport ⊢
    exact hport
  rw [← hq_eq]
  exact hq_mem

private theorem sourceStep_aeval_derivative_minpoly
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Polynomial.aeval (sourceStepIntegralRoot P x hx)
        (derivative (minpoly P.valuationRing
          (sourceStepIntegralRoot P x hx))) =
      sourceStepIntegralUniformizer P x hx *
        sourceStepIntegralRoot P x hx ^ 14 := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP P.valuationRing 2 :=
    P.valuationRing.subtype.charP P.valuationRing.subtype_injective 2
  have hderivative :
      derivative (minpoly P.valuationRing (sourceStepIntegralRoot P x hx)) =
        C (sourceStepUniformizer P x hx) * X ^ 14 := by
    rw [sourceStep_minpoly_integralRoot,
      sourceStepReciprocalPolynomial]
    simp only [derivative_add, derivative_X_pow,
      derivative_C_mul_X_pow, derivative_C]
    reduce_mod_char!
    norm_num
  rw [hderivative]
  simp only [map_mul, aeval_C, aeval_X, map_pow,
    algebraMap_sourceStepUniformizer]

/-- The actual one-step different is generated by `t * W^14`. -/
theorem sourceStepDifferentIdeal_eq_span
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    differentIdeal P.valuationRing (SourceStepIntegralClosure P x hx) =
      Ideal.span
        ({sourceStepIntegralUniformizer P x hx *
            sourceStepIntegralRoot P x hx ^ 14} :
          Set (SourceStepIntegralClosure P x hx)) := by
  let O := P.valuationRing
  let C := SourceStepIntegralClosure P x hx
  let L := SourceStepField P x hx
  let w : C := sourceStepIntegralRoot P x hx
  let hfieldAdjoin : Algebra.adjoin K
      ({algebraMap C L w} : Set L) = ⊤ := by
    have hport := (AdjoinRoot.powerBasis
      (sourceStepPolynomial_monic P x hx).ne_zero).adjoin_gen_eq_top
    simp only [C, L, w, coe_sourceStepIntegralRoot, sourceStepReciprocalRoot, AdjoinRoot.powerBasis_gen] at hport ⊢
    exact hport
  have hconductor : conductor O w = ⊤ :=
    conductor_eq_top_of_adjoin_eq_top (by
      simpa only [O, C, w] using
        sourceStepIntegralClosure_adjoin_root_eq_top P x hx)
  have hdifferent := conductor_mul_differentIdeal O K L w hfieldAdjoin
  rw [hconductor, Ideal.top_mul,
    sourceStep_aeval_derivative_minpoly] at hdifferent
  simpa only [O, C, w] using hdifferent

/-- The source recursion step has exact weak different exponent
`30 = 2 * (16 - 1)`. -/
theorem sourceStepDifferentIdeal_multiplicity
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    multiplicity (sourceStepUpperIdeal P x hx)
        (differentIdeal P.valuationRing
          (SourceStepIntegralClosure P x hx)) = 30 := by
  let O := P.valuationRing
  let C := SourceStepIntegralClosure P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let Q : Ideal C := sourceStepUpperIdeal P x hx
  let t : C := sourceStepIntegralUniformizer P x hx
  let w : C := sourceStepIntegralRoot P x hx
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  have hm_ne_bot : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap_ne_bot : Ideal.map (algebraMap O C) m ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm_ne_bot
  have hmap : Ideal.map (algebraMap O C) m =
      Ideal.span ({t} : Set C) := by
    simpa only [O, C, m, t] using
      map_maximalIdeal_eq_span_sourceStepIntegralUniformizer P x hx
  have hQ_prime : Prime Q := Ideal.prime_of_isPrime
    (sourceStepUpperHeightOne P x hx).ne_bot
    (sourceStepUpperHeightOne P x hx).isPrime
  have ht_ne_bot : Ideal.span ({t} : Set C) ≠ ⊥ := by
    rw [← hmap]
    exact hmap_ne_bot
  have hw_ne_bot : Ideal.span ({w} : Set C) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    simpa only [w] using sourceStepIntegralRoot_ne_zero P x hx
  have ht_finite : FiniteMultiplicity Q (Ideal.span ({t} : Set C)) :=
    FiniteMultiplicity.of_prime_left hQ_prime ht_ne_bot
  have hw_finite : FiniteMultiplicity Q (Ideal.span ({w} : Set C)) :=
    FiniteMultiplicity.of_prime_left hQ_prime hw_ne_bot
  have hproduct_finite : FiniteMultiplicity Q
      (Ideal.span ({t} : Set C) * (Ideal.span ({w} : Set C)) ^ 14) :=
    hQ_prime.finiteMultiplicity_mul ht_finite (hw_finite.pow hQ_prime)
  have ht_multiplicity : multiplicity Q (Ideal.span ({t} : Set C)) = 16 := by
    calc
      multiplicity Q (Ideal.span ({t} : Set C)) =
          multiplicity Q (Ideal.map (algebraMap O C) m) := by rw [hmap]
      _ = m.ramificationIdx' Q :=
        (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
          hmap_ne_bot (sourceStepUpperHeightOne P x hx).isPrime).symm
      _ = 16 := by
        simpa only [O, C, m, Q] using
          sourceStep_ramificationIdx_eq_sixteen P x hx
  have hw_multiplicity : multiplicity Q (Ideal.span ({w} : Set C)) = 1 := by
    simpa only [C, Q, w] using sourceStepIntegralRoot_multiplicity P x hx
  have hdifferent : differentIdeal O C =
      Ideal.span ({t} : Set C) * (Ideal.span ({w} : Set C)) ^ 14 := by
    calc
      differentIdeal O C = Ideal.span ({t * w ^ 14} : Set C) := by
        simpa only [O, C, t, w] using sourceStepDifferentIdeal_eq_span P x hx
      _ = Ideal.span ({t} : Set C) * Ideal.span ({w ^ 14} : Set C) :=
        (Ideal.span_singleton_mul_span_singleton t (w ^ 14)).symm
      _ = Ideal.span ({t} : Set C) * (Ideal.span ({w} : Set C)) ^ 14 := by
        rw [Ideal.span_singleton_pow]
  change multiplicity Q (differentIdeal O C) = 30
  rw [hdifferent, multiplicity_mul hQ_prime hproduct_finite,
    hw_finite.multiplicity_pow hQ_prime,
    ht_multiplicity, hw_multiplicity]

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
