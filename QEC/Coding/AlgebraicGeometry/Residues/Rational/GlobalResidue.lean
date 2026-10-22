import QEC.Coding.AlgebraicGeometry.Residues.Global.SimplePoleResidueLinear
import QEC.Coding.AlgebraicGeometry.Residues.Rational.SimpleFractionGlobalResidue
import QEC.Coding.AlgebraicGeometry.Residues.Rational.SquarefreePartialFraction

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# The global residue theorem for rational differentials

Every globally simple-pole differential on `k(X)` is a finite sum of proper
simple fractions.  Each summand has zero finite global traced-residue sum, so
additivity gives cancellation for the original differential.

The construction is symbolic: the normalized denominator is proved proper
and squarefree, then Mathlib's polynomial partial-fraction identity supplies
the summands.  No enumeration of the finite field or its rational functions
is used.  This module proves only the rational base case; it does not transport
the theorem through a finite function-field extension, prove duality, define
genus, or state Riemann--Roch.
-/

open scoped BigOperators Polynomial RatFunc

namespace QEC.Coding.AlgebraicGeometry
namespace Differential

open FunctionFieldDifferential

variable {k : Type*} [Field k] [Finite k]

private noncomputable def rationalPlaceOfIrreducible
    (q : k[X]) (hq : Irreducible q) :
    IsDedekindDomain.HeightOneSpectrum k[X] := by
  have hqPrime : Prime q :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hq
  have hspanIsPrime : (Ideal.span ({q} : Set k[X])).IsPrime :=
    (Ideal.span_singleton_prime hq.ne_zero).mpr hqPrime
  exact IsDedekindDomain.HeightOneSpectrum.ofPrime
    (Ideal.prime_of_isPrime
      (Ideal.span_singleton_eq_bot.not.mpr hq.ne_zero) hspanIsPrime)

private theorem rationalAdicPolynomial_rationalPlaceOfIrreducible
    (q : k[X]) (hqMonic : q.Monic) (hq : Irreducible q) :
    GlobalPlace.rationalAdicPolynomial
        (rationalPlaceOfIrreducible q hq) = q := by
  apply Polynomial.eq_of_monic_of_associated
    (GlobalPlace.rationalAdicPolynomial_monic
      (rationalPlaceOfIrreducible q hq)) hqMonic
  apply Ideal.span_singleton_eq_span_singleton.mp
  rw [← GlobalPlace.rationalAdic_asIdeal_eq_span]
  rfl

/-- The finite global traced-residue sum of every nonzero globally
simple-pole rational differential `f dX` vanishes. -/
theorem globalSimplePoleResidueSum_ratFunc
    (f : RatFunc k) (hf : f ≠ 0)
    (homega : IsGlobalSimplePole (k := k) (F := RatFunc k)
      (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))) :
    globalSimplePoleResidueSum (k := k) (F := RatFunc k)
        (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        homega = 0 := by
  classical
  have hdegree : f.num.degree < f.denom.degree :=
    ratFunc_num_degree_lt_denom_degree_of_isGlobalSimplePole f hf homega
  have hsquarefree : Squarefree f.denom :=
    ratFunc_denom_squarefree_of_isGlobalSimplePole f hf homega
  obtain ⟨s, r, hdata, hfSum⟩ :=
    exists_ratFunc_eq_sum_simpleFractions_of_squarefree
      f hdegree hsquarefree
  let place (q : k[X]) (hq : q ∈ s) :
      IsDedekindDomain.HeightOneSpectrum k[X] :=
    rationalPlaceOfIrreducible q (hdata q hq).2.1
  let term (q : k[X]) : Differential k (RatFunc k) :=
    if hq : q ∈ s then
      ((rationalAdicSimpleFractionAtSimplePole (place q hq) (r q) :
        simplePoleDifferentialLattice
          (GlobalPlace.rationalAdic (place q hq))) :
            Differential k (RatFunc k))
    else 0
  have hplacePolynomial (q : k[X]) (hq : q ∈ s) :
      GlobalPlace.rationalAdicPolynomial (place q hq) = q := by
    exact rationalAdicPolynomial_rationalPlaceOfIrreducible
      q (hdata q hq).1 (hdata q hq).2.1
  have hterm (q : k[X]) (hq : q ∈ s) :
      term q =
        (algebraMap k[X] (RatFunc k) (r q) /
          algebraMap k[X] (RatFunc k) q) •
            functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
    simp only [term, dif_pos hq,
      coe_rationalAdicSimpleFractionAtSimplePole]
    rw [hplacePolynomial q hq]
  have htermSimple (q : k[X]) :
      IsGlobalSimplePole (k := k) (F := RatFunc k) (term q) := by
    by_cases hq : q ∈ s
    · simpa only [term, dif_pos hq] using
        (rationalAdicSimpleFraction_isGlobalSimplePole
          (place q hq) (r q) (by
            rw [hplacePolynomial q hq]
            exact (hdata q hq).2.2))
    · simpa only [term, dif_neg hq] using
        (isGlobalSimplePole_zero (k := k) (F := RatFunc k))
  have htermResidue (q : k[X]) :
      globalSimplePoleResidueSum (k := k) (F := RatFunc k)
          (term q) (htermSimple q) = 0 := by
    by_cases hq : q ∈ s
    · simpa only [term, dif_pos hq] using
        (globalSimplePoleResidueSum_rationalAdicSimpleFraction
          (place q hq) (r q) (by
            rw [hplacePolynomial q hq]
            exact (hdata q hq).2.2))
    · simpa only [term, dif_neg hq] using
        (globalSimplePoleResidueSum_zero (k := k) (F := RatFunc k))
  have hsumDifferential :
      f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k) =
        ∑ q ∈ s, term q := by
    calc
      f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k) =
          (∑ q ∈ s,
            algebraMap k[X] (RatFunc k) (r q) /
              algebraMap k[X] (RatFunc k) q) •
                functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
            rw [← hfSum]
      _ = ∑ q ∈ s,
          (algebraMap k[X] (RatFunc k) (r q) /
            algebraMap k[X] (RatFunc k) q) •
              functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
            rw [Finset.sum_smul]
      _ = ∑ q ∈ s, term q := by
            apply Finset.sum_congr rfl
            intro q hq
            exact (hterm q hq).symm
  have hsumResidue :
      globalSimplePoleResidueSum (k := k) (F := RatFunc k)
          (∑ q ∈ s, term q)
          (IsGlobalSimplePole.finset_sum s term htermSimple) = 0 := by
    calc
      globalSimplePoleResidueSum (k := k) (F := RatFunc k)
          (∑ q ∈ s, term q)
          (IsGlobalSimplePole.finset_sum s term htermSimple) =
          ∑ q ∈ s, globalSimplePoleResidueSum (k := k) (F := RatFunc k)
            (term q) (htermSimple q) :=
        globalSimplePoleResidueSum_finset_sum s term htermSimple
      _ = 0 := Finset.sum_eq_zero (fun q _ => htermResidue q)
  simpa only [hsumDifferential] using hsumResidue

end Differential
end QEC.Coding.AlgebraicGeometry
