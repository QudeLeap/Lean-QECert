import QEC.Coding.AlgebraicGeometry.Trace.PrimaryTorsion.CyclicFactorTrace
import QEC.Coding.AlgebraicGeometry.Residues.Rational.AdicResidue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Primary trace on a polynomial cyclic quotient

This module extracts the largest power of an irreducible element dividing a
nonzero element, applies the symbolic cyclic-factor calculation, and then
identifies element multiplicity with the corresponding principal-ideal
multiplicity.  The rational-place corollary is the local cyclic summand needed
for the later Smith-diagonal trace calculation.

There is no Smith decomposition, residue comparison, duality, genus, or
Riemann--Roch theorem here.
-/

open scoped Polynomial

namespace QEC.Coding.AlgebraicGeometry

variable {R : Type*} [CommRing R]

/-- Multiplication by `r` on the cyclic quotient `R ⧸ (a)`. -/
noncomputable def cyclicQuotientMul (a r : R) :
    (R ⧸ Ideal.span {a}) →ₗ[R] (R ⧸ Ideal.span {a}) :=
  Algebra.lmul R (R ⧸ Ideal.span {a})
    (Ideal.Quotient.mk (Ideal.span {a}) r)

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- In a principal ideal domain, the multiplicity of an irreducible element
in a nonzero element agrees with the multiplicity of their principal ideals. -/
theorem multiplicity_span_singleton_eq (q a : R) (hq : Irreducible q)
    (ha : a ≠ 0) :
    multiplicity (Ideal.span {q}) (Ideal.span {a}) = multiplicity q a := by
  have hqprime : Prime q :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hq
  have hspanprime : Prime (Ideal.span {q}) := by
    rw [Ideal.prime_span_singleton_iff]
    exact hqprime
  have hspan_ne : Ideal.span {a} ≠ 0 :=
    Submodule.span_singleton_eq_bot.mp.mt ha
  have hfiniteElement : FiniteMultiplicity q a :=
    FiniteMultiplicity.of_not_isUnit hq.not_isUnit ha
  have hfiniteIdeal :
      FiniteMultiplicity (Ideal.span {q}) (Ideal.span {a}) :=
    FiniteMultiplicity.of_prime_left hspanprime hspan_ne
  apply Nat.cast_injective (R := ℕ∞)
  rw [← hfiniteIdeal.emultiplicity_eq_multiplicity,
    ← hfiniteElement.emultiplicity_eq_multiplicity,
    Ideal.emultiplicity_eq_emultiplicity_span]

private theorem primaryTorsionTrace_cyclicQuotient_of_eq_pow_mul
    [IsNoetherianRing R] (q : R) (hq : q ≠ 0)
    [hmax : (Ideal.span {q}).IsMaximal]
    (a r : R) (e : ℕ) (b : R) (hb : b ≠ 0)
    (hfactor : a = q ^ e * b) :
    primaryTorsionTrace (Ideal.span {q}) (cyclicQuotientMul a r) e =
      (e : R ⧸ Ideal.span {q}) *
        Ideal.Quotient.mk (Ideal.span {q}) r := by
  subst a
  exact primaryTorsionTrace_cyclicPowerFactorQuotient q hq e b hb r

/-- On `R ⧸ (a)`, the primary trace of multiplication by `r` at an
irreducible `q` is the multiplicity of `q` in `a`, times `r mod q`. -/
theorem primaryTorsionTrace_cyclicQuotient
    [IsNoetherianRing R] (q a r : R) (hq : Irreducible q)
    [hmax : (Ideal.span {q}).IsMaximal] (ha : a ≠ 0) :
    primaryTorsionTrace (Ideal.span {q}) (cyclicQuotientMul a r)
        (multiplicity q a) =
      (multiplicity q a : R ⧸ Ideal.span {q}) *
        Ideal.Quotient.mk (Ideal.span {q}) r := by
  obtain ⟨b, hfactor⟩ := pow_multiplicity_dvd q a
  have hb : b ≠ 0 := by
    intro hb
    apply ha
    rw [hfactor, hb, mul_zero]
  exact primaryTorsionTrace_cyclicQuotient_of_eq_pow_mul
    q hq.ne_zero a r (multiplicity q a) b hb hfactor

private theorem primaryTorsionTrace_cyclicQuotient_of_eq_span
    [IsNoetherianRing R] (P : Ideal R) [P.IsMaximal]
    (q a r : R) (hq : Irreducible q) (ha : a ≠ 0)
    (hP : P = Ideal.span {q}) :
    primaryTorsionTrace P (cyclicQuotientMul a r)
        (multiplicity P (Ideal.span {a})) =
      (multiplicity P (Ideal.span {a}) : R ⧸ P) *
        Ideal.Quotient.mk P r := by
  subst P
  rw [multiplicity_span_singleton_eq q a hq ha]
  exact primaryTorsionTrace_cyclicQuotient q a r hq ha

variable {k : Type*} [Field k] [Finite k]

/-- At a finite rational place, the primary trace on a polynomial cyclic
quotient is the principal-ideal multiplicity times the reduced multiplier. -/
theorem primaryTorsionTrace_rationalAdicPolynomialQuotient
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (a : k[X]) (ha : a ≠ 0) (r : k[X]) :
    primaryTorsionTrace p.asIdeal (cyclicQuotientMul a r)
        (multiplicity p.asIdeal (Ideal.span {a})) =
      (multiplicity p.asIdeal (Ideal.span {a}) : k[X] ⧸ p.asIdeal) *
        Ideal.Quotient.mk p.asIdeal r := by
  exact primaryTorsionTrace_cyclicQuotient_of_eq_span p.asIdeal
    (GlobalPlace.rationalAdicPolynomial p) a r
      (GlobalPlace.rationalAdicPolynomial_irreducible p) ha
        (GlobalPlace.rationalAdic_asIdeal_eq_span p)

end QEC.Coding.AlgebraicGeometry
