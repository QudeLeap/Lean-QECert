import QEC.Coding.AlgebraicGeometry.Residues.Rational.AdicSimpleFractionResidue
import QEC.Coding.AlgebraicGeometry.Residues.Rational.InfinitySimpleFractionResidue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Global residue cancellation for a rational simple fraction

For a finite rational place cut out by a monic irreducible polynomial `q`,
this module proves that `(b / q) dX`, with `degree b < degree q`, is regular at
every other finite place and has at most a simple pole globally.  Its traced
residue at `q` is the next-to-leading coefficient of `b`, while its residue at
infinity is the negative of that coefficient, so its finite global residue sum
vanishes.

This is the single-denominator building block for the rational-function global
residue theorem.  It does not yet decompose every rational differential, move
residues through a finite function-field extension, prove duality, define
genus, or state Riemann--Roch.
-/

open scoped Polynomial RatFunc

namespace QEC.Coding.AlgebraicGeometry
namespace Differential

open FunctionFieldDifferential

variable {k : Type*} [Field k] [Finite k]

private theorem rationalAdicPolynomial_not_mem_of_ne
    (p q : IsDedekindDomain.HeightOneSpectrum k[X]) (hpq : p ≠ q) :
    GlobalPlace.rationalAdicPolynomial q ∉ p.asIdeal := by
  intro hmem
  apply hpq
  apply IsDedekindDomain.HeightOneSpectrum.ext
  have hle : q.asIdeal ≤ p.asIdeal := by
    rw [GlobalPlace.rationalAdic_asIdeal_eq_span q]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
  exact (q.isMaximal.eq_of_le p.isPrime.ne_top hle).symm

private theorem rationalAdicPolynomial_isUnit_of_ne
    (p q : IsDedekindDomain.HeightOneSpectrum k[X]) (hpq : p ≠ q) :
    IsUnit (GlobalPlace.rationalAdicPolynomialToValuationRing p
      (GlobalPlace.rationalAdicPolynomial q)) := by
  apply (Valuation.valuationSubring.integers
    (GlobalPlace.rationalAdic p).valuation).isUnit_iff_valuation_eq_one.mpr
  change (GlobalPlace.rationalAdic p).valuation
      ((GlobalPlace.rationalAdicPolynomialToValuationRing p
        (GlobalPlace.rationalAdicPolynomial q) :
          (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k) = 1
  rw [GlobalPlace.coe_rationalAdicPolynomialToValuationRing]
  exact (p.valuation_eq_one_iff_notMem (K := RatFunc k)).mpr
    (rationalAdicPolynomial_not_mem_of_ne p q hpq)

private noncomputable def rationalAdicSimpleFractionAwayCoefficient
    (p q : IsDedekindDomain.HeightOneSpectrum k[X]) (hpq : p ≠ q)
    (b : k[X]) : (GlobalPlace.rationalAdic p).valuationRing :=
  GlobalPlace.rationalAdicPolynomialToValuationRing p b *
    ↑((rationalAdicPolynomial_isUnit_of_ne p q hpq).unit⁻¹)

private theorem coe_rationalAdicSimpleFractionAwayCoefficient
    (p q : IsDedekindDomain.HeightOneSpectrum k[X]) (hpq : p ≠ q)
    (b : k[X]) :
    ((rationalAdicSimpleFractionAwayCoefficient p q hpq b :
      (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k) =
      algebraMap k[X] (RatFunc k) b /
        algebraMap k[X] (RatFunc k) (GlobalPlace.rationalAdicPolynomial q) := by
  unfold rationalAdicSimpleFractionAwayCoefficient
  rw [show
      (((GlobalPlace.rationalAdicPolynomialToValuationRing p b *
        ↑((rationalAdicPolynomial_isUnit_of_ne p q hpq).unit⁻¹) :
          (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k)) =
        ((GlobalPlace.rationalAdicPolynomialToValuationRing p b :
          (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k) *
          (((↑((rationalAdicPolynomial_isUnit_of_ne p q hpq).unit⁻¹) :
            (GlobalPlace.rationalAdic p).valuationRing)) : RatFunc k) by rfl]
  rw [GlobalPlace.coe_rationalAdicPolynomialToValuationRing]
  change algebraMap k[X] (RatFunc k) b *
      algebraMap (GlobalPlace.rationalAdic p).valuationRing (RatFunc k)
        (↑((rationalAdicPolynomial_isUnit_of_ne p q hpq).unit⁻¹) :
          (GlobalPlace.rationalAdic p).valuationRing) = _
  rw [map_units_inv (algebraMap
      (GlobalPlace.rationalAdic p).valuationRing (RatFunc k))
      (rationalAdicPolynomial_isUnit_of_ne p q hpq).unit,
    (rationalAdicPolynomial_isUnit_of_ne p q hpq).unit_spec]
  change algebraMap k[X] (RatFunc k) b *
      (((GlobalPlace.rationalAdicPolynomialToValuationRing p
        (GlobalPlace.rationalAdicPolynomial q) :
          (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k))⁻¹ = _
  rw [GlobalPlace.coe_rationalAdicPolynomialToValuationRing, div_eq_mul_inv]

private theorem functionFieldDifferentialGenerator_mem_rationalAdic
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    functionFieldDifferentialGenerator (k := k) (F := RatFunc k) ∈
      localDifferentialLattice (GlobalPlace.rationalAdic p) := by
  let x : (GlobalPlace.rationalAdic p).valuationRing :=
    GlobalPlace.rationalAdicPolynomialToValuationRing p Polynomial.X
  have hx := differential_mem_localDifferentialLattice
    (k := k) (F := RatFunc k) (GlobalPlace.rationalAdic p) x
  have hxValue : (x : RatFunc k) = RatFunc.X := by
    simp only [x, GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
      RatFunc.algebraMap_X]
  have hX : functionFieldDerivation (k := k) (F := RatFunc k) RatFunc.X = 1 := by
    simpa using
      (functionFieldDerivation_apply_X (k := k) (F := RatFunc k))
  rw [hxValue, differential_eq_functionFieldDerivation_smul_generator,
    hX] at hx
  simpa using hx

/-- A rational simple-fraction differential is regular at every finite place
different from its denominator place. -/
theorem rationalAdicSimpleFraction_mem_localDifferentialLattice_of_ne
    (p q : IsDedekindDomain.HeightOneSpectrum k[X]) (hpq : p ≠ q)
    (b : k[X]) :
    ((rationalAdicSimpleFractionAtSimplePole q b :
      simplePoleDifferentialLattice (GlobalPlace.rationalAdic q)) :
        Differential k (RatFunc k)) ∈
      localDifferentialLattice (GlobalPlace.rationalAdic p) := by
  have hregular := (localDifferentialLattice (k := k) (F := RatFunc k)
    (GlobalPlace.rationalAdic p)).smul_mem
      (rationalAdicSimpleFractionAwayCoefficient p q hpq b)
      (functionFieldDifferentialGenerator_mem_rationalAdic p)
  change
    ((rationalAdicSimpleFractionAwayCoefficient p q hpq b :
      (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) ∈
      localDifferentialLattice (GlobalPlace.rationalAdic p) at hregular
  simpa only [coe_rationalAdicSimpleFractionAtSimplePole,
    coe_rationalAdicSimpleFractionAwayCoefficient] using hregular

/-- A proper rational simple-fraction differential has at most a simple pole
at every normalized place of `k(X)`. -/
theorem rationalAdicSimpleFraction_isGlobalSimplePole
    (q : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X])
    (hb : b.degree < (GlobalPlace.rationalAdicPolynomial q).degree) :
    IsGlobalSimplePole (k := k) (F := RatFunc k)
      ((rationalAdicSimpleFractionAtSimplePole q b :
        simplePoleDifferentialLattice (GlobalPlace.rationalAdic q)) :
          Differential k (RatFunc k)) := by
  intro P
  obtain ⟨place, rfl⟩ := (GlobalPlace.rationalPlaceEquiv (k := k)).surjective P
  cases place with
  | none =>
      have hinfinity :=
        (rationalInfinitySimpleFractionAtSimplePole
          (GlobalPlace.rationalAdicPolynomial q) b
          (GlobalPlace.rationalAdicPolynomial_monic q) hb).property
      rw [GlobalPlace.rationalPlaceEquiv_apply_none,
        coe_rationalAdicSimpleFractionAtSimplePole]
      rw [coe_rationalInfinitySimpleFractionAtSimplePole] at hinfinity
      exact hinfinity
  | some p =>
      rw [GlobalPlace.rationalPlaceEquiv_apply_some]
      by_cases hpq : p = q
      · subst p
        exact (rationalAdicSimpleFractionAtSimplePole q b).property
      · exact localDifferentialLattice_le_simplePoleDifferentialLattice
          (k := k) (F := RatFunc k) (GlobalPlace.rationalAdic p)
          (rationalAdicSimpleFraction_mem_localDifferentialLattice_of_ne
            p q hpq b)

/-- The finite global traced-residue sum of a proper rational simple fraction
vanishes: its denominator-place residue cancels its infinity residue. -/
theorem globalSimplePoleResidueSum_rationalAdicSimpleFraction
    (q : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X])
    (hb : b.degree < (GlobalPlace.rationalAdicPolynomial q).degree) :
    globalSimplePoleResidueSum (k := k) (F := RatFunc k)
        ((rationalAdicSimpleFractionAtSimplePole q b :
          simplePoleDifferentialLattice (GlobalPlace.rationalAdic q)) :
            Differential k (RatFunc k))
        (rationalAdicSimpleFraction_isGlobalSimplePole q b hb) = 0 := by
  classical
  let omega : Differential k (RatFunc k) :=
    (rationalAdicSimpleFractionAtSimplePole q b :
      simplePoleDifferentialLattice (GlobalPlace.rationalAdic q))
  let homega : IsGlobalSimplePole (k := k) (F := RatFunc k) omega :=
    rationalAdicSimpleFraction_isGlobalSimplePole q b hb
  let c : k := b.coeff ((GlobalPlace.rationalAdicPolynomial q).natDegree - 1)
  let Pq : GlobalPlace k (RatFunc k) := GlobalPlace.rationalAdic q
  let Pinf : GlobalPlace k (RatFunc k) := GlobalPlace.rationalInfinity k
  have hne : Pq ≠ Pinf := by
    intro h
    have hoption : (some q : Option
        (IsDedekindDomain.HeightOneSpectrum k[X])) = none := by
      apply (GlobalPlace.rationalPlaceEquiv (k := k)).injective
      simpa only [Pq, Pinf, GlobalPlace.rationalPlaceEquiv_apply_some,
        GlobalPlace.rationalPlaceEquiv_apply_none] using h
    exact Option.some_ne_none q hoption
  have hat_q :
      globalSimplePoleResidue (k := k) (F := RatFunc k) omega homega Pq = c := by
    rw [globalSimplePoleResidue_apply]
    exact simplePoleTraceResidue_rationalAdicSimpleFraction q b hb
  have hat_infinity :
      globalSimplePoleResidue (k := k) (F := RatFunc k) omega homega Pinf = -c := by
    rw [globalSimplePoleResidue_apply]
    have hrepresentative : omega =
        (rationalInfinitySimpleFractionAtSimplePole
          (GlobalPlace.rationalAdicPolynomial q) b
          (GlobalPlace.rationalAdicPolynomial_monic q) hb :
            Differential k (RatFunc k)) := by
      dsimp only [omega]
      rw [coe_rationalAdicSimpleFractionAtSimplePole,
        coe_rationalInfinitySimpleFractionAtSimplePole]
    change simplePoleTraceResidue (k := k) (F := RatFunc k)
      Pinf omega (homega Pinf) = -c
    have hlocal : (⟨omega, homega Pinf⟩ : simplePoleDifferentialLattice Pinf) =
        rationalInfinitySimpleFractionAtSimplePole
          (GlobalPlace.rationalAdicPolynomial q) b
          (GlobalPlace.rationalAdicPolynomial_monic q) hb :=
      Subtype.ext hrepresentative
    have htrace := congrArg
      (fun w : simplePoleDifferentialLattice Pinf =>
        simplePoleTraceResidue (k := k) (F := RatFunc k) Pinf w w.property) hlocal
    exact htrace.trans (simplePoleTraceResidue_rationalInfinitySimpleFraction
      (GlobalPlace.rationalAdicPolynomial q) b
      (GlobalPlace.rationalAdicPolynomial_monic q) hb)
  have haway (p : IsDedekindDomain.HeightOneSpectrum k[X]) (hpq : p ≠ q) :
      globalSimplePoleResidue (k := k) (F := RatFunc k) omega homega
          (GlobalPlace.rationalAdic p) = 0 := by
    rw [globalSimplePoleResidue_apply]
    apply simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
      (k := k) (F := RatFunc k)
    exact rationalAdicSimpleFraction_mem_localDifferentialLattice_of_ne
      p q hpq b
  have hresidue :
      globalSimplePoleResidue (k := k) (F := RatFunc k) omega homega =
        Finsupp.single Pq c + Finsupp.single Pinf (-c) := by
    ext P
    obtain ⟨place, rfl⟩ :=
      (GlobalPlace.rationalPlaceEquiv (k := k)).surjective P
    cases place with
    | none =>
        simpa only [GlobalPlace.rationalPlaceEquiv_apply_none, Pinf,
          Finsupp.add_apply, Finsupp.single_apply, hne, if_false, if_true,
          zero_add] using hat_infinity
    | some p =>
        rw [GlobalPlace.rationalPlaceEquiv_apply_some]
        by_cases hpq : p = q
        · subst p
          simpa only [Pq, Finsupp.add_apply, Finsupp.single_apply,
            hne.symm, if_false, if_true, add_zero] using hat_q
        · have hp_ne_q : GlobalPlace.rationalAdic p ≠ Pq := by
            intro h
            apply hpq
            have hoption : (some p : Option
                (IsDedekindDomain.HeightOneSpectrum k[X])) = some q := by
              apply (GlobalPlace.rationalPlaceEquiv (k := k)).injective
              simpa only [Pq, GlobalPlace.rationalPlaceEquiv_apply_some] using h
            exact Option.some.inj hoption
          have hp_ne_inf : GlobalPlace.rationalAdic p ≠ Pinf := by
            intro h
            have hoption : (some p : Option
                (IsDedekindDomain.HeightOneSpectrum k[X])) = none := by
              apply (GlobalPlace.rationalPlaceEquiv (k := k)).injective
              simpa only [Pinf, GlobalPlace.rationalPlaceEquiv_apply_some,
                GlobalPlace.rationalPlaceEquiv_apply_none] using h
            exact Option.some_ne_none p hoption
          simpa only [Finsupp.add_apply, Finsupp.single_apply, hp_ne_q.symm,
            hp_ne_inf.symm, if_false, zero_add] using haway p hpq
  change (globalSimplePoleResidue (k := k) (F := RatFunc k)
    omega homega).sum (fun _ residue => residue) = 0
  rw [hresidue]
  rw [Finsupp.sum_single_add_single Pq Pinf c (-c)
    (fun _ residue => residue) hne (fun _ => rfl)]
  simp

end Differential
end QEC.Coding.AlgebraicGeometry
