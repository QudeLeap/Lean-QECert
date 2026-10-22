/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

import Mathlib.NumberTheory.RatFunc.Ostrowski
import QEC.Coding.AlgebraicGeometry.Places.TwoChartGlobalPlace

/-!
# Classification of normalized places of a rational function field

Mathlib's Ostrowski theorem classifies rank-one discrete valuations of `k(X)`
up to equivalence.  A `GlobalPlace` is additionally normalized and surjective
onto `ℤᵐ⁰`; normalized valuation rigidity therefore upgrades the
classification to an actual equivalence of carriers.

This module only classifies places of the rational base field.  It does not
state a residue theorem or any Riemann--Roch identity.
-/

open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom

namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace

variable {k : Type*} [Field k] [Finite k]

/-- The normalized global place of `k(X)` attached to a height-one prime of
`k[X]`. -/
noncomputable def rationalAdic
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) : GlobalPlace k (RatFunc k) :=
  { valuation := p.valuation (RatFunc k)
    normalized := p.valuation_surjective (RatFunc k) }

/-- The normalized rational place indexed by infinity (`none`) or by a
height-one prime of `k[X]` (`some p`). -/
noncomputable def rationalPlaceOfOption :
    Option (IsDedekindDomain.HeightOneSpectrum k[X]) → GlobalPlace k (RatFunc k)
  | none => rationalInfinity k
  | some p => rationalAdic p

private theorem rationalPlaceOfOption_apply_none :
    rationalPlaceOfOption (k := k) none = rationalInfinity k := rfl

private theorem rationalPlaceOfOption_apply_some
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    rationalPlaceOfOption (k := k) (some p) = rationalAdic p := rfl

private theorem globalPlace_eq_of_valuation_eq
    {P Q : GlobalPlace k (RatFunc k)} (hvaluation : P.valuation = Q.valuation) : P = Q := by
  cases P
  cases Q
  cases hvaluation
  rfl

private theorem globalPlace_valuation_isNontrivial
    (P : GlobalPlace k (RatFunc k)) : P.valuation.IsNontrivial := by
  rw [Valuation.isNontrivial_iff_exists_lt_one]
  refine ⟨P.uniformizer, ?_, ?_⟩
  · apply P.valuation.ne_zero_iff.mp
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  · rw [P.valuation_uniformizer, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)

private theorem rationalPlaceOfOption_injective :
    Function.Injective (rationalPlaceOfOption (k := k)) := by
  classical
  intro P Q hPQ
  cases P with
  | none =>
      cases Q with
      | none => rfl
      | some q =>
          exfalso
          apply RatFunc.adicValuation_ne_inftyValuation q
          exact (congrArg
            (fun R : GlobalPlace k (RatFunc k) => R.valuation) hPQ).symm
  | some p =>
      cases Q with
      | none =>
          exfalso
          apply RatFunc.adicValuation_ne_inftyValuation p
          exact congrArg (fun R : GlobalPlace k (RatFunc k) => R.valuation) hPQ
      | some q =>
          congr 1
          apply IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
            (K := RatFunc k)
          exact Valuation.IsEquiv.of_eq
            (congrArg (fun R : GlobalPlace k (RatFunc k) => R.valuation) hPQ)

private theorem rationalPlaceOfOption_surjective :
    Function.Surjective (rationalPlaceOfOption (k := k)) := by
  classical
  intro P
  letI : P.valuation.IsNontrivial := globalPlace_valuation_isNontrivial P
  letI : IsCyclic (valueGroup (MonoidWithZeroHom.ofClass P.valuation)) := inferInstance
  letI : Nontrivial (valueGroup (MonoidWithZeroHom.ofClass P.valuation)) := inferInstance
  letI : P.valuation.IsRankOneDiscrete :=
    Valuation.IsRankOneDiscrete.mk' P.valuation
  letI : P.valuation.IsTrivialOn k := P.trivialOnConstants
  rcases RatFunc.valuation_isEquiv_infty_or_adic (v := P.valuation) with
    ⟨hInfinity, _⟩ | ⟨hadic, _⟩
  · refine ⟨none, ?_⟩
    apply globalPlace_eq_of_valuation_eq
    exact (normalizedValuation_eq_of_isEquiv
      P.valuation
      (RatFunc.inftyValuation k)
      P.normalized
      (rationalInfinity_surjective k)
      hInfinity).symm
  · obtain ⟨p, hp, _⟩ := hadic
    refine ⟨some p, ?_⟩
    apply globalPlace_eq_of_valuation_eq
    exact (normalizedValuation_eq_of_isEquiv
      P.valuation
      (p.valuation (RatFunc k))
      P.normalized
      (p.valuation_surjective (RatFunc k))
      hp).symm

/-- Normalized places of `k(X)` are exactly infinity together with the
height-one adic places of `k[X]`. -/
noncomputable def rationalPlaceEquiv :
    Option (IsDedekindDomain.HeightOneSpectrum k[X]) ≃ GlobalPlace k (RatFunc k) :=
  Equiv.ofBijective (rationalPlaceOfOption (k := k))
    ⟨rationalPlaceOfOption_injective, rationalPlaceOfOption_surjective⟩

@[simp]
theorem rationalPlaceEquiv_apply_none :
    rationalPlaceEquiv (k := k) none = rationalInfinity k := rfl

@[simp]
theorem rationalPlaceEquiv_apply_some
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    rationalPlaceEquiv (k := k) (some p) = rationalAdic p := rfl

end GlobalPlace
end QEC.Coding.AlgebraicGeometry
