import Mathlib.Algebra.Squarefree.Basic
import QEC.Coding.AlgebraicGeometry.Differentials.RatFuncDifferentialOrder

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Denominators of rational differentials with simple poles

This module turns the local simple-pole condition on `f dX` into concrete
constraints on the normalized numerator and denominator of `f : k(X)`.
Every finite-place order is at least `-1`, the infinity order is at least
`1`, the numerator degree is strictly smaller than the denominator degree,
and the denominator is squarefree.

The squarefreeness proof is valuation-theoretic: a squared irreducible factor
would give a finite-place order at most `-2`, contradicting the actual local
simple-pole bound.  No partial-fraction decomposition, residue theorem,
genus, duality, or Riemann--Roch identity is assumed here.
-/

open scoped Polynomial RatFunc WithZero

namespace QEC.Coding.AlgebraicGeometry
namespace Differential

open FunctionFieldDifferential

variable {k : Type*} [Field k] [Finite k]

/-- A globally simple-pole differential `f dX` forces `f` to have order at
least `-1` at every finite normalized rational place. -/
theorem rationalAdic_order_ge_neg_one_of_isGlobalSimplePole
    (f : RatFunc k) (hf : f ≠ 0)
    (homega : IsGlobalSimplePole
      (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k)))
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    -1 ≤ (GlobalPlace.rationalAdic p).order f := by
  have hsimple := homega (GlobalPlace.rationalAdic p)
  have horder :=
    (mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
      (k := k) (F := RatFunc k) (GlobalPlace.rationalAdic p)
      (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
      (smul_ne_zero hf
        (functionFieldDifferentialGenerator_ne_zero
          (k := k) (F := RatFunc k)))).mp hsimple
  rw [differentialOrder_smul_generator_rationalAdic
    (k := k) p f hf] at horder
  exact horder

/-- A globally simple-pole differential `f dX` forces `f` to vanish to order
at least one at the normalized rational place at infinity. -/
theorem rationalInfinity_order_ge_one_of_isGlobalSimplePole
    (f : RatFunc k) (hf : f ≠ 0)
    (homega : IsGlobalSimplePole
      (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))) :
    1 ≤ (GlobalPlace.rationalInfinity k).order f := by
  have hsimple := homega (GlobalPlace.rationalInfinity k)
  have horder :=
    (mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
      (k := k) (F := RatFunc k) (GlobalPlace.rationalInfinity k)
      (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
      (smul_ne_zero hf
        (functionFieldDifferentialGenerator_ne_zero
          (k := k) (F := RatFunc k)))).mp hsimple
  rw [differentialOrder_smul_generator_rationalInfinity
    (k := k) f hf] at horder
  omega

/-- The normalized numerator of a globally simple-pole rational differential
has strictly smaller degree than its denominator. -/
theorem ratFunc_num_degree_lt_denom_degree_of_isGlobalSimplePole
    (f : RatFunc k) (hf : f ≠ 0)
    (homega : IsGlobalSimplePole
      (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))) :
    f.num.degree < f.denom.degree := by
  have hinfinity : 1 ≤ (GlobalPlace.rationalInfinity k).order f :=
    rationalInfinity_order_ge_one_of_isGlobalSimplePole f hf homega
  rw [RationalBaseInfinityCancellation.rationalInfinity_order_eq_denomDegree_sub_numDegree
    k f hf] at hinfinity
  have hnat : f.num.natDegree < f.denom.natDegree := by
    omega
  rw [Polynomial.degree_eq_natDegree (RatFunc.num_ne_zero hf),
    Polynomial.degree_eq_natDegree (RatFunc.denom_ne_zero f)]
  exact WithBot.coe_lt_coe.mpr hnat

/-- The normalized denominator of a globally simple-pole rational
differential is squarefree. -/
theorem ratFunc_denom_squarefree_of_isGlobalSimplePole
    (f : RatFunc k) (hf : f ≠ 0)
    (homega : IsGlobalSimplePole
      (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))) :
    Squarefree f.denom := by
  refine (squarefree_iff_no_irreducibles (RatFunc.denom_ne_zero f)).mpr ?_
  intro q hq hqSqDvd
  have hqPrime : Prime q :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hq
  have hspanIsPrime : (Ideal.span ({q} : Set k[X])).IsPrime :=
    (Ideal.span_singleton_prime hq.ne_zero).mpr hqPrime
  have hspanNe : Ideal.span ({q} : Set k[X]) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr hq.ne_zero
  have hspanPrime : Prime (Ideal.span ({q} : Set k[X])) :=
    Ideal.prime_of_isPrime hspanNe hspanIsPrime
  let p : IsDedekindDomain.HeightOneSpectrum k[X] :=
    IsDedekindDomain.HeightOneSpectrum.ofPrime hspanPrime
  let P : GlobalPlace k (RatFunc k) := GlobalPlace.rationalAdic p
  have hdenIntValuation :
      p.intValuation f.denom ≤ WithZero.exp (-(2 : ℤ)) := by
    apply (p.intValuation_le_pow_iff_mem f.denom 2).mpr
    change f.denom ∈ (Ideal.span ({q} : Set k[X])) ^ 2
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simpa only [pow_two] using hqSqDvd
  have hdenIntValuationNe : p.intValuation f.denom ≠ 0 :=
    p.intValuation_ne_zero f.denom (RatFunc.denom_ne_zero f)
  have hdenLog : WithZero.log (p.intValuation f.denom) ≤ -2 := by
    rw [← WithZero.log_exp (-2 : ℤ)]
    exact (WithZero.log_le_log hdenIntValuationNe WithZero.exp_ne_zero).mpr
      hdenIntValuation
  have hdenOrder :
      2 ≤ P.order (algebraMap k[X] (RatFunc k) f.denom) := by
    change 2 ≤ -WithZero.log
      ((p.valuation (RatFunc k))
        (algebraMap k[X] (RatFunc k) f.denom))
    rw [p.valuation_of_algebraMap]
    omega
  have hqDvdDenom : q ∣ f.denom := by
    exact (dvd_mul_right q q).trans hqSqDvd
  have hqNotDvdNum : ¬q ∣ f.num := by
    intro hqDvdNum
    exact hq.not_isUnit
      ((RatFunc.isCoprime_num_denom f).isUnit_of_dvd'
        hqDvdNum hqDvdDenom)
  have hnumNotMem : f.num ∉ p.asIdeal := by
    change f.num ∉ Ideal.span ({q} : Set k[X])
    rw [Ideal.mem_span_singleton]
    exact hqNotDvdNum
  have hnumValuation :
      P.valuation (algebraMap k[X] (RatFunc k) f.num) = 1 := by
    change (p.valuation (RatFunc k))
      (algebraMap k[X] (RatFunc k) f.num) = 1
    exact (p.valuation_eq_one_iff_notMem (K := RatFunc k)).mpr hnumNotMem
  have hnumOrder :
      P.order (algebraMap k[X] (RatFunc k) f.num) = 0 := by
    unfold P GlobalPlace.order
    rw [hnumValuation]
    simp
  have hnumMapNe : algebraMap k[X] (RatFunc k) f.num ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hf)
  have hdenMapNe : algebraMap k[X] (RatFunc k) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f)
  have horderEq :
      P.order f =
        P.order (algebraMap k[X] (RatFunc k) f.num) -
          P.order (algebraMap k[X] (RatFunc k) f.denom) := by
    calc
      P.order f = P.order
          (algebraMap k[X] (RatFunc k) f.num /
            algebraMap k[X] (RatFunc k) f.denom) :=
        congrArg P.order (RatFunc.num_div_denom f).symm
      _ = P.order (algebraMap k[X] (RatFunc k) f.num) -
          P.order (algebraMap k[X] (RatFunc k) f.denom) := by
        rw [div_eq_mul_inv,
          P.order_mul hnumMapNe (inv_ne_zero hdenMapNe), P.order_inv]
        ring
  have horderLe : P.order f ≤ -2 := by
    rw [horderEq, hnumOrder]
    omega
  have horderGe : -1 ≤ P.order f :=
    rationalAdic_order_ge_neg_one_of_isGlobalSimplePole f hf homega p
  omega

end Differential
end QEC.Coding.AlgebraicGeometry
