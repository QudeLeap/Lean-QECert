/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Derivations of the rational function field

For a module `M` over the rational function field `k⟮X⟯`, this module constructs
the quotient-rule `k`-derivation of `k⟮X⟯` with any prescribed value `m` at the
variable `X`, and proves that every `k`-derivation of `k⟮X⟯` into `M` is
determined by its value at `X`.  This is the rational-function layer of the
derivation-extension route to rank-one differentials; it stores no residue,
canonical-divisor, or Riemann--Roch conclusion.
-/

namespace QEC.Coding.AlgebraicGeometry

namespace RatFuncDerivation

open scoped RatFunc

variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M] [Module (RatFunc k) M]
variable [IsScalarTower k (RatFunc k) M]

/-- The formal-derivative value of a polynomial at the prescribed module
element: the derivative evaluated at `X`, acting on `m`. -/
noncomputable def polyValue (m : M) (p : Polynomial k) : M :=
  Polynomial.aeval (RatFunc.X : RatFunc k) p.derivative • m

@[simp]
theorem polyValue_add (m : M) (p q : Polynomial k) :
    polyValue (k := k) m (p + q) = polyValue (k := k) m p + polyValue (k := k) m q := by
  rw [polyValue, polyValue, polyValue, Polynomial.derivative_add, Polynomial.aeval_add, add_smul]

@[simp]
theorem polyValue_X (m : M) : polyValue (k := k) m Polynomial.X = m := by
  rw [polyValue, Polynomial.derivative_X, map_one]
  simp

@[simp]
theorem polyValue_C (m : M) (a : k) : polyValue (k := k) m (Polynomial.C a) = 0 := by
  rw [polyValue, Polynomial.derivative_C, map_zero]
  simp

/-- Leibniz's rule for the polynomial formal-derivative value. -/
theorem polyValue_mul (m : M) (a b : Polynomial k) :
    polyValue (k := k) m (a * b) =
        Polynomial.aeval (RatFunc.X : RatFunc k) a • polyValue (k := k) m b
      + Polynomial.aeval (RatFunc.X : RatFunc k) b • polyValue (k := k) m a := by
  rw [polyValue, polyValue, polyValue, Polynomial.derivative_mul, Polynomial.aeval_add,
    Polynomial.aeval_mul, Polynomial.aeval_mul, add_smul, mul_smul, mul_smul]
  rw [smul_comm (Polynomial.aeval (RatFunc.X : RatFunc k) (Polynomial.derivative a))]
  abel

/-- The quotient-rule value of the rational derivation on a fraction `p / q`,
expressed with the inverse of the denominator acting through the fraction-field
module structure. -/
noncomputable def quotientRuleValue (m : M) (p q : Polynomial k) : M :=
  ((algebraMap (Polynomial k) (RatFunc k) q)⁻¹ : RatFunc k) ^ 2 •
    (algebraMap (Polynomial k) (RatFunc k) q • polyValue (k := k) m p
      - algebraMap (Polynomial k) (RatFunc k) p • polyValue (k := k) m q)

/-- The zero-denominator convention needed for the `RatFunc.liftOn'` recursion. -/
@[simp]
theorem quotientRuleValue_zero_condition (m : M) (p : Polynomial k) :
    quotientRuleValue (k := k) m p 0 = quotientRuleValue (k := k) m 0 1 := by
  rw [quotientRuleValue, quotientRuleValue]
  simp only [map_zero, map_one, inv_zero, zero_pow, one_pow, inv_one, zero_smul, one_smul,
    sub_zero, smul_zero]
  rw [polyValue, Polynomial.derivative_zero, map_zero]
  simp

/-- Squaring cancels the squared inverse of a nonzero fraction-field scalar. -/
theorem sq_smul_inv_sq_smul_eq (s : RatFunc k) (hs : s ≠ 0) (m : M) :
    s ^ 2 • (s⁻¹ : RatFunc k) ^ 2 • m = m := by
  rw [smul_smul, ← mul_pow, mul_inv_cancel₀ hs, one_pow, one_smul]

/-- Scaling a quotient-rule value by the squared denominator clears the
inverse. -/
theorem quotientRuleValue_scaled (m : M) {p q : Polynomial k} (hq : q ≠ 0) :
    (algebraMap (Polynomial k) (RatFunc k) q) ^ 2 • quotientRuleValue (k := k) m p q
      = algebraMap (Polynomial k) (RatFunc k) q • polyValue (k := k) m p
        - algebraMap (Polynomial k) (RatFunc k) p • polyValue (k := k) m q := by
  rw [quotientRuleValue]
  exact sq_smul_inv_sq_smul_eq (k := k)
    (algebraMap (Polynomial k) (RatFunc k) q) (RatFunc.algebraMap_ne_zero hq) _

/-- Scaling by a squared product denominator splits off the complementary
square. -/
theorem smul_sq_mul_quotientRuleValue (m : M) {p q q' : Polynomial k} (hq : q ≠ 0) :
    (algebraMap (Polynomial k) (RatFunc k) (q * q')) ^ 2 •
        quotientRuleValue (k := k) m p q
      = (algebraMap (Polynomial k) (RatFunc k) q') ^ 2 •
        (algebraMap (Polynomial k) (RatFunc k) q • polyValue (k := k) m p
          - algebraMap (Polynomial k) (RatFunc k) p • polyValue (k := k) m q) := by
  rw [map_mul, mul_pow, mul_comm ((algebraMap (Polynomial k) (RatFunc k) q) ^ 2),
    ← smul_smul, quotientRuleValue_scaled (k := k) m hq]

/-- Scaling by a squared product denominator in the opposite factor order. -/
theorem smul_sq_mul_quotientRuleValue' (m : M) {p q q' : Polynomial k} (hq : q ≠ 0) :
    (algebraMap (Polynomial k) (RatFunc k) (q' * q)) ^ 2 •
        quotientRuleValue (k := k) m p q
      = (algebraMap (Polynomial k) (RatFunc k) q') ^ 2 •
        (algebraMap (Polynomial k) (RatFunc k) q • polyValue (k := k) m p
          - algebraMap (Polynomial k) (RatFunc k) p • polyValue (k := k) m q) := by
  rw [show q' * q = q * q' from mul_comm q' q]
  exact smul_sq_mul_quotientRuleValue (k := k) m hq

/-- The quotient rule is invariant under multiplying numerator and denominator
by a common nonzero factor. -/
theorem quotientRuleValue_mul (m : M) {p q a : Polynomial k} (hq : q ≠ 0) (ha : a ≠ 0) :
    quotientRuleValue (k := k) m (a * p) (a * q) = quotientRuleValue (k := k) m p q := by
  have hhaq : algebraMap (Polynomial k) (RatFunc k) (a * q) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (mul_ne_zero ha hq)
  apply ((hhaq.isUnit.pow 2).smul_left_cancel).mp
  rw [quotientRuleValue_scaled (k := k) m (mul_ne_zero ha hq),
    smul_sq_mul_quotientRuleValue' (k := k) m (q' := a) hq]
  rw [polyValue_mul (k := k) m a p, polyValue_mul (k := k) m a q]
  simp only [map_mul, map_add, RatFunc.aeval_X_left_eq_algebraMap]
  simp only [smul_add, smul_sub, add_smul, sub_smul, mul_smul]
  simp only [smul_smul]
  rw [show (algebraMap (Polynomial k) (RatFunc k) a) *
        ((algebraMap (Polynomial k) (RatFunc k) q) * (algebraMap (Polynomial k) (RatFunc k) a))
        = (algebraMap (Polynomial k) (RatFunc k) a) ^ 2 * (algebraMap (Polynomial k) (RatFunc k) q) by ring,
    show (algebraMap (Polynomial k) (RatFunc k) a) *
        ((algebraMap (Polynomial k) (RatFunc k) q) * (algebraMap (Polynomial k) (RatFunc k) p))
        = (algebraMap (Polynomial k) (RatFunc k) a) *
        ((algebraMap (Polynomial k) (RatFunc k) p) * (algebraMap (Polynomial k) (RatFunc k) q)) by ring,
    show (algebraMap (Polynomial k) (RatFunc k) a) *
        ((algebraMap (Polynomial k) (RatFunc k) p) * (algebraMap (Polynomial k) (RatFunc k) a))
        = (algebraMap (Polynomial k) (RatFunc k) a) ^ 2 * (algebraMap (Polynomial k) (RatFunc k) p) by ring]
  abel_nf

/-- The quotient rule is additive for the common-denominator sum. -/
theorem quotientRuleValue_add (m : M) {p p' q q' : Polynomial k} (hq : q ≠ 0)
    (hq' : q' ≠ 0) :
    quotientRuleValue (k := k) m p q + quotientRuleValue (k := k) m p' q'
      = quotientRuleValue (k := k) m (p * q' + p' * q) (q * q') := by
  have hqq' : algebraMap (Polynomial k) (RatFunc k) (q * q') ≠ 0 :=
    RatFunc.algebraMap_ne_zero (mul_ne_zero hq hq')
  apply ((hqq'.isUnit.pow 2).smul_left_cancel).mp
  rw [smul_add, smul_sq_mul_quotientRuleValue (k := k) m hq,
    smul_sq_mul_quotientRuleValue' (k := k) m (p := p') (q := q') (q' := q) hq',
    quotientRuleValue_scaled (k := k) m (mul_ne_zero hq hq')]
  rw [polyValue_add (k := k) m, polyValue_mul (k := k) m p q',
    polyValue_mul (k := k) m p' q, polyValue_mul (k := k) m q q']
  simp only [map_mul, map_add, RatFunc.aeval_X_left_eq_algebraMap]
  simp only [smul_add, smul_sub, add_smul, sub_smul, mul_smul]
  simp only [smul_smul]
  rw [show (algebraMap (Polynomial k) (RatFunc k) q) *
        ((algebraMap (Polynomial k) (RatFunc k) q') * (algebraMap (Polynomial k) (RatFunc k) q'))
        = (algebraMap (Polynomial k) (RatFunc k) q') ^ 2 * (algebraMap (Polynomial k) (RatFunc k) q) by ring,
    show (algebraMap (Polynomial k) (RatFunc k) q') ^ 2 * (algebraMap (Polynomial k) (RatFunc k) p)
        = (algebraMap (Polynomial k) (RatFunc k) p) *
        ((algebraMap (Polynomial k) (RatFunc k) q') * (algebraMap (Polynomial k) (RatFunc k) q')) by ring,
    show (algebraMap (Polynomial k) (RatFunc k) q) *
        ((algebraMap (Polynomial k) (RatFunc k) q') * (algebraMap (Polynomial k) (RatFunc k) p'))
        = (algebraMap (Polynomial k) (RatFunc k) p') *
        ((algebraMap (Polynomial k) (RatFunc k) q) * (algebraMap (Polynomial k) (RatFunc k) q')) by ring,
    show (algebraMap (Polynomial k) (RatFunc k) q) *
        ((algebraMap (Polynomial k) (RatFunc k) q') * (algebraMap (Polynomial k) (RatFunc k) q))
        = (algebraMap (Polynomial k) (RatFunc k) q) ^ 2 * (algebraMap (Polynomial k) (RatFunc k) q') by ring,
    show (algebraMap (Polynomial k) (RatFunc k) q) ^ 2 * (algebraMap (Polynomial k) (RatFunc k) p')
        = (algebraMap (Polynomial k) (RatFunc k) p') *
        ((algebraMap (Polynomial k) (RatFunc k) q) * (algebraMap (Polynomial k) (RatFunc k) q)) by ring,
    show (algebraMap (Polynomial k) (RatFunc k) q) *
        ((algebraMap (Polynomial k) (RatFunc k) q') * (algebraMap (Polynomial k) (RatFunc k) p))
        = (algebraMap (Polynomial k) (RatFunc k) p) *
        ((algebraMap (Polynomial k) (RatFunc k) q') * (algebraMap (Polynomial k) (RatFunc k) q)) by ring]
  abel_nf

/-- The `mk` fraction is the field quotient of its numerator and denominator. -/
theorem mk_eq_div (p q : Polynomial k) (hq : q ≠ 0) :
    RatFunc.mk p q = algebraMap (Polynomial k) (RatFunc k) p / algebraMap (Polynomial k) (RatFunc k) q := by
  rw [RatFunc.mk_eq_div' (p := p) (q := q)]
  rw [RatFunc.ofFractionRing_div]
  rw [show RatFunc.ofFractionRing (algebraMap (Polynomial k) (FractionRing (Polynomial k)) p)
        = algebraMap (Polynomial k) (RatFunc k) p from
    (RatFunc.mk_one' p).symm.trans (RatFunc.mk_one p)]
  rw [show RatFunc.ofFractionRing (algebraMap (Polynomial k) (FractionRing (Polynomial k)) q)
        = algebraMap (Polynomial k) (RatFunc k) q from
    (RatFunc.mk_one' q).symm.trans (RatFunc.mk_one q)]

/-- The sum of two `mk` fractions is the common-denominator fraction. -/
theorem mk_add (p q p' q' : Polynomial k) (hq : q ≠ 0) (hq' : q' ≠ 0) :
    RatFunc.mk p q + RatFunc.mk p' q' = RatFunc.mk (p * q' + p' * q) (q * q') := by
  rw [mk_eq_div (k := k) p q hq, mk_eq_div (k := k) p' q' hq',
    mk_eq_div (k := k) (p * q' + p' * q) (q * q') (mul_ne_zero hq hq')]
  rw [div_add_div (a := algebraMap (Polynomial k) (RatFunc k) p)
    (c := algebraMap (Polynomial k) (RatFunc k) p')
    (hb := RatFunc.algebraMap_ne_zero hq) (hd := RatFunc.algebraMap_ne_zero hq')]
  simp only [map_add, map_mul]
  ring_nf

/-- The product of two `mk` fractions is the product fraction. -/
theorem mk_mul (p q p' q' : Polynomial k) (hq : q ≠ 0) (hq' : q' ≠ 0) :
    RatFunc.mk p q * RatFunc.mk p' q' = RatFunc.mk (p * p') (q * q') := by
  rw [mk_eq_div (k := k) p q hq, mk_eq_div (k := k) p' q' hq',
    mk_eq_div (k := k) (p * p') (q * q') (mul_ne_zero hq hq')]
  rw [div_mul_div_comm]
  simp only [map_mul]

/-- The quotient rule satisfies Leibniz's product law. -/
theorem quotientRuleValue_leibniz (m : M) {p p' q q' : Polynomial k} (hq : q ≠ 0)
    (hq' : q' ≠ 0) :
    quotientRuleValue (k := k) m (p * p') (q * q')
      = RatFunc.mk p q • quotientRuleValue (k := k) m p' q'
        + RatFunc.mk p' q' • quotientRuleValue (k := k) m p q := by
  have hqq' : algebraMap (Polynomial k) (RatFunc k) (q * q') ≠ 0 :=
    RatFunc.algebraMap_ne_zero (mul_ne_zero hq hq')
  apply ((hqq'.isUnit.pow 2).smul_left_cancel).mp
  rw [quotientRuleValue_scaled (k := k) m (mul_ne_zero hq hq')]
  rw [polyValue_mul (k := k) m p p', polyValue_mul (k := k) m q q']
  rw [smul_add]
  rw [quotientRuleValue, quotientRuleValue]
  simp only [map_mul, map_add, RatFunc.aeval_X_left_eq_algebraMap]
  simp only [smul_add, smul_sub, add_smul, sub_smul, mul_smul]
  simp only [smul_smul]
  rw [show ((algebraMap (Polynomial k) (RatFunc k) q) * (algebraMap (Polynomial k) (RatFunc k) q')) ^ 2 *
        (RatFunc.mk p q * (((algebraMap (Polynomial k) (RatFunc k) q')⁻¹ : RatFunc k) ^ 2
          * (algebraMap (Polynomial k) (RatFunc k) q')))
        = (algebraMap (Polynomial k) (RatFunc k) p) *
          ((algebraMap (Polynomial k) (RatFunc k) q) * (algebraMap (Polynomial k) (RatFunc k) q')) by
      rw [mk_eq_div (k := k) p q hq]
      field_simp [RatFunc.algebraMap_ne_zero hq, RatFunc.algebraMap_ne_zero hq'],
    show ((algebraMap (Polynomial k) (RatFunc k) q) * (algebraMap (Polynomial k) (RatFunc k) q')) ^ 2 *
        (RatFunc.mk p q * (((algebraMap (Polynomial k) (RatFunc k) q')⁻¹ : RatFunc k) ^ 2
          * (algebraMap (Polynomial k) (RatFunc k) p')))
        = (algebraMap (Polynomial k) (RatFunc k) p) *
          ((algebraMap (Polynomial k) (RatFunc k) q) * (algebraMap (Polynomial k) (RatFunc k) p')) by
      rw [mk_eq_div (k := k) p q hq]
      field_simp [RatFunc.algebraMap_ne_zero hq, RatFunc.algebraMap_ne_zero hq'],
    show ((algebraMap (Polynomial k) (RatFunc k) q) * (algebraMap (Polynomial k) (RatFunc k) q')) ^ 2 *
        (RatFunc.mk p' q' * (((algebraMap (Polynomial k) (RatFunc k) q)⁻¹ : RatFunc k) ^ 2
          * (algebraMap (Polynomial k) (RatFunc k) q)))
        = (algebraMap (Polynomial k) (RatFunc k) p') *
          ((algebraMap (Polynomial k) (RatFunc k) q') * (algebraMap (Polynomial k) (RatFunc k) q)) by
      rw [mk_eq_div (k := k) p' q' hq']
      field_simp [RatFunc.algebraMap_ne_zero hq, RatFunc.algebraMap_ne_zero hq'],
    show ((algebraMap (Polynomial k) (RatFunc k) q) * (algebraMap (Polynomial k) (RatFunc k) q')) ^ 2 *
        (RatFunc.mk p' q' * (((algebraMap (Polynomial k) (RatFunc k) q)⁻¹ : RatFunc k) ^ 2
          * (algebraMap (Polynomial k) (RatFunc k) p)))
        = (algebraMap (Polynomial k) (RatFunc k) p') *
          ((algebraMap (Polynomial k) (RatFunc k) q') * (algebraMap (Polynomial k) (RatFunc k) p)) by
      rw [mk_eq_div (k := k) p' q' hq']
      field_simp [RatFunc.algebraMap_ne_zero hq, RatFunc.algebraMap_ne_zero hq'],
    show (algebraMap (Polynomial k) (RatFunc k) q) *
        ((algebraMap (Polynomial k) (RatFunc k) q') * (algebraMap (Polynomial k) (RatFunc k) p'))
        = (algebraMap (Polynomial k) (RatFunc k) p') *
        ((algebraMap (Polynomial k) (RatFunc k) q') * (algebraMap (Polynomial k) (RatFunc k) q)) by ring,
    show (algebraMap (Polynomial k) (RatFunc k) q) *
        ((algebraMap (Polynomial k) (RatFunc k) q') * (algebraMap (Polynomial k) (RatFunc k) p))
        = (algebraMap (Polynomial k) (RatFunc k) p) *
        ((algebraMap (Polynomial k) (RatFunc k) q) * (algebraMap (Polynomial k) (RatFunc k) q')) by ring,
    show (algebraMap (Polynomial k) (RatFunc k) p) *
        ((algebraMap (Polynomial k) (RatFunc k) p') * (algebraMap (Polynomial k) (RatFunc k) q'))
        = (algebraMap (Polynomial k) (RatFunc k) p') *
        ((algebraMap (Polynomial k) (RatFunc k) q') * (algebraMap (Polynomial k) (RatFunc k) p)) by ring,
    show (algebraMap (Polynomial k) (RatFunc k) p) *
        ((algebraMap (Polynomial k) (RatFunc k) p') * (algebraMap (Polynomial k) (RatFunc k) q))
        = (algebraMap (Polynomial k) (RatFunc k) p) *
        ((algebraMap (Polynomial k) (RatFunc k) q) * (algebraMap (Polynomial k) (RatFunc k) p')) by ring]
  abel_nf

/-- The quotient rule commutes with the `k`-scalar action on the module. -/
theorem quotientRuleValue_smul_C (m : M) (a : k) {p q : Polynomial k} (hq : q ≠ 0) :
    quotientRuleValue (k := k) m (Polynomial.C a * p) q
      = a • quotientRuleValue (k := k) m p q := by
  have hqscal : algebraMap (Polynomial k) (RatFunc k) q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  apply ((hqscal.isUnit.pow 2).smul_left_cancel).mp
  rw [quotientRuleValue_scaled (k := k) m hq, smul_comm, quotientRuleValue_scaled (k := k) m hq]
  rw [polyValue_mul (k := k) m (Polynomial.C a) p]
  rw [polyValue_C (k := k) m a]
  have hC : algebraMap (Polynomial k) (RatFunc k) (Polynomial.C a) = algebraMap k (RatFunc k) a := by
    rw [RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C]
  simp only [map_mul, smul_zero, add_zero, Polynomial.aeval_C, hC]
  rw [← algebraMap_smul (R := k) (A := RatFunc k)]
  simp only [smul_add, smul_sub, add_smul, sub_smul, mul_smul]
  simp only [smul_smul]
  rw [show (algebraMap (Polynomial k) (RatFunc k) q) * algebraMap k (RatFunc k) a
        = algebraMap k (RatFunc k) a * (algebraMap (Polynomial k) (RatFunc k) q) by
      ring]

/-- The underlying function of the rational derivation, defined by the
quotient rule on representatives. -/
noncomputable def rationalDerivationToFun (m : M) (x : RatFunc k) : M :=
  RatFunc.liftOn' x (quotientRuleValue (k := k) m)
    (fun {p q a} (hq : q ≠ 0) (ha : a ≠ 0) => quotientRuleValue_mul (k := k) m hq ha)

/-- Evaluating the rational derivation on a fraction applies the quotient
rule. -/
@[simp]
theorem rationalDerivationToFun_mk (m : M) (p q : Polynomial k) (hq : q ≠ 0) :
    rationalDerivationToFun (k := k) m (RatFunc.mk p q)
      = quotientRuleValue (k := k) m p q := by
  rw [rationalDerivationToFun, RatFunc.liftOn'_mk (p := p) (q := q)
    (f := quotientRuleValue (k := k) m)
    (f0 := quotientRuleValue_zero_condition (k := k) m)
    (H := fun {p q a} (hq : q ≠ 0) (ha : a ≠ 0) => quotientRuleValue_mul (k := k) m hq ha)]

/-- The quotient-rule rational derivation with prescribed value `m` at `X`. -/
noncomputable def rationalDerivation (m : M) : Derivation k (RatFunc k) M where
  toLinearMap :=
    { toFun := rationalDerivationToFun (k := k) m
      map_add' := by
        intro x y
        refine RatFunc.induction_on' x ?_
        intro p q hq
        refine RatFunc.induction_on' y ?_
        intro p' q' hq'
        rw [rationalDerivationToFun_mk (k := k) m p q hq,
          rationalDerivationToFun_mk (k := k) m p' q' hq',
          mk_add (k := k) p q p' q' hq hq',
          rationalDerivationToFun_mk (k := k) m (p * q' + p' * q) (q * q')
            (mul_ne_zero hq hq')]
        exact (quotientRuleValue_add (k := k) (p := p) (p' := p') (q := q) (q' := q') m hq hq').symm
      map_smul' := by
        intro a x
        refine RatFunc.induction_on' x ?_
        intro p q hq
        rw [show a • RatFunc.mk p q = RatFunc.mk (Polynomial.C a * p) q by
          rw [RatFunc.smul_eq_C_mul]
          rw [show RatFunc.C a = algebraMap (Polynomial k) (RatFunc k) (Polynomial.C a) by simp]
          rw [← RatFunc.mk_one (x := Polynomial.C a), mk_mul (k := k) (Polynomial.C a) 1 p q
            one_ne_zero hq]
          simp]
        rw [rationalDerivationToFun_mk (k := k) m (Polynomial.C a * p) q hq,
          rationalDerivationToFun_mk (k := k) m p q hq]
        exact quotientRuleValue_smul_C (k := k) m a hq }
  map_one_eq_zero' := by
    change rationalDerivationToFun (k := k) m 1 = 0
    rw [show (1 : RatFunc k) = RatFunc.mk 1 1 by
      rw [← map_one (algebraMap (Polynomial k) (RatFunc k))]
      exact (RatFunc.mk_one 1).symm]
    rw [rationalDerivationToFun_mk (k := k) m 1 1 one_ne_zero]
    unfold quotientRuleValue polyValue
    rw [Polynomial.derivative_one, map_zero]
    simp
  leibniz' := by
    intro x y
    refine RatFunc.induction_on' x ?_
    intro p q hq
    refine RatFunc.induction_on' y ?_
    intro p' q' hq'
    change rationalDerivationToFun (k := k) m (RatFunc.mk p q * RatFunc.mk p' q')
      = RatFunc.mk p q • rationalDerivationToFun (k := k) m (RatFunc.mk p' q')
        + RatFunc.mk p' q' • rationalDerivationToFun (k := k) m (RatFunc.mk p q)
    rw [rationalDerivationToFun_mk (k := k) m p q hq,
      rationalDerivationToFun_mk (k := k) m p' q' hq',
      mk_mul (k := k) p q p' q' hq hq',
      rationalDerivationToFun_mk (k := k) m (p * p') (q * q') (mul_ne_zero hq hq')]
    exact quotientRuleValue_leibniz (k := k) m hq hq'

@[simp]
theorem rationalDerivation_apply_X (m : M) : rationalDerivation (k := k) m RatFunc.X = m := by
  change rationalDerivationToFun (k := k) m RatFunc.X = m
  rw [show (RatFunc.X : RatFunc k) = RatFunc.mk Polynomial.X 1 from by
    simpa using (RatFunc.mk_one Polynomial.X).symm]
  rw [rationalDerivationToFun_mk (k := k) m Polynomial.X 1 one_ne_zero]
  unfold quotientRuleValue polyValue
  rw [Polynomial.derivative_X, Polynomial.derivative_one, map_one, map_zero]
  simp

/-- Every `k`-derivation of the rational function field vanishing at `X` is
zero. -/
theorem eq_zero_of_apply_X_eq_zero {D : Derivation k (RatFunc k) M} (hX : D RatFunc.X = 0) :
    D = 0 := by
  refine Derivation.ext ?_
  intro x
  refine RatFunc.induction_on' x ?_
  intro p q hq
  have hp : D (algebraMap (Polynomial k) (RatFunc k) p) = 0 := by
    rw [← RatFunc.aeval_X_left_eq_algebraMap]
    rw [Derivation.map_aeval, hX, smul_zero]
  have hq' : D (algebraMap (Polynomial k) (RatFunc k) q) = 0 := by
    rw [← RatFunc.aeval_X_left_eq_algebraMap]
    rw [Derivation.map_aeval, hX, smul_zero]
  have hxq : RatFunc.mk p q * algebraMap (Polynomial k) (RatFunc k) q
      = algebraMap (Polynomial k) (RatFunc k) p := by
    rw [mk_eq_div (k := k) p q hq]
    field_simp [RatFunc.algebraMap_ne_zero hq]
  have hDxq := D.leibniz (RatFunc.mk p q) (algebraMap (Polynomial k) (RatFunc k) q)
  rw [hxq] at hDxq
  simp only [hp, hq', smul_zero] at hDxq
  have hqscal : algebraMap (Polynomial k) (RatFunc k) q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  calc
    D (RatFunc.mk p q)
        = (algebraMap (Polynomial k) (RatFunc k) q)⁻¹ •
          ((algebraMap (Polynomial k) (RatFunc k) q) • D (RatFunc.mk p q)) := by
          rw [smul_smul, inv_mul_cancel₀ hqscal, one_smul]
    _ = (algebraMap (Polynomial k) (RatFunc k) q)⁻¹ • 0 := by
          rw [← (show 0 = (algebraMap (Polynomial k) (RatFunc k) q) • D (RatFunc.mk p q) by
            simpa using hDxq)]
    _ = 0 := by simp

/-- A rational derivation is determined by its value at `X`. -/
theorem rationalDerivation_eq_of_apply_X {D : Derivation k (RatFunc k) M} :
    rationalDerivation (k := k) (D RatFunc.X) = D := by
  have hsub : (rationalDerivation (k := k) (D RatFunc.X) - D) RatFunc.X = 0 := by
    simp [rationalDerivation_apply_X]
  have hzero := eq_zero_of_apply_X_eq_zero (k := k) hsub
  exact sub_eq_zero.mp hzero

/-- `k`-derivations of the rational function field into `M` are linearly
equivalent to their values at `X`. -/
noncomputable def rationalDerivationEquiv :
    Derivation k (RatFunc k) M ≃ₗ[RatFunc k] M where
  toFun := fun D => D RatFunc.X
  invFun := fun m => rationalDerivation (k := k) m
  left_inv := by
    intro D
    exact rationalDerivation_eq_of_apply_X (k := k)
  right_inv := by
    intro m
    exact rationalDerivation_apply_X (k := k) m
  map_add' := by
    intro D₁ D₂
    rfl
  map_smul' := by
    intro a D
    rfl

@[simp]
theorem rationalDerivationEquiv_apply (D : Derivation k (RatFunc k) M) :
    rationalDerivationEquiv (k := k) (M := M) D = D RatFunc.X :=
  rfl

@[simp]
theorem rationalDerivationEquiv_symm_apply (m : M) :
    (rationalDerivationEquiv (k := k) (M := M)).symm m = rationalDerivation (k := k) m :=
  rfl

/-- The rational derivation construction is linear in the prescribed value. -/
theorem rationalDerivation_smul (a : RatFunc k) (m : M) :
    rationalDerivation (k := k) (a • m) = a • rationalDerivation (k := k) m :=
  (rationalDerivationEquiv (k := k) (M := M)).symm.map_smul a m

/-- The rational derivation construction is additive in the prescribed
value. -/
theorem rationalDerivation_add (m n : M) :
    rationalDerivation (k := k) (m + n) = rationalDerivation (k := k) m
      + rationalDerivation (k := k) n :=
  (rationalDerivationEquiv (k := k) (M := M)).symm.map_add m n

end RatFuncDerivation

end QEC.Coding.AlgebraicGeometry
