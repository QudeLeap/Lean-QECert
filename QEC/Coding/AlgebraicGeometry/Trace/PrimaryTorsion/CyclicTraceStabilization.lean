import QEC.Coding.AlgebraicGeometry.Trace.PrimaryTorsion.PolynomialQuotientTrace

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Stabilization of primary trace on cyclic quotients

For a cyclic quotient whose defining element contains exactly `e` copies of a
prime `q`, the `(q)`-primary torsion filtration stabilizes at depth `e`.
Consequently all later primary grades have zero trace, so the finite primary
trace is unchanged at every larger depth.  Combining this stabilization with
the exact-depth cyclic calculation gives a depth-independent formula whenever
the chosen depth bounds the multiplicity.

The proof is symbolic: it cancels a common prime power and uses coprimality of
the remaining factor.  It does not enumerate quotient elements, perform a
Smith decomposition, or prove a residue, duality, genus, or Riemann--Roch
theorem.
-/

open scoped Polynomial

namespace QEC.Coding.AlgebraicGeometry

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- Once the exponent reaches the exact `q`-power in a cyclic quotient, the
`(q)`-primary torsion layer is stable. -/
theorem primaryTorsionLayer_cyclicPowerFactorQuotient_stable
    (q : R) (hq : Prime q) (e : ℕ) (b : R) (hb : ¬ q ∣ b)
    (j : ℕ) (hej : e ≤ j) :
    primaryTorsionLayer (Ideal.span {q})
        (R ⧸ Ideal.span {q ^ e * b}) j =
      primaryTorsionLayer (Ideal.span {q})
        (R ⧸ Ideal.span {q ^ e * b}) e := by
  apply le_antisymm
  · intro x hx
    rw [primaryTorsionLayer, Ideal.span_singleton_pow,
      Submodule.torsionBySet_ideal_span_singleton_eq,
      Submodule.mem_torsionBy_iff] at hx ⊢
    induction x using Quotient.inductionOn' with
    | _ r =>
        change Ideal.Quotient.mk (Ideal.span {q ^ e * b}) (q ^ j * r) = 0 at hx
        change Ideal.Quotient.mk (Ideal.span {q ^ e * b}) (q ^ e * r) = 0
        rw [Ideal.Quotient.eq_zero_iff_dvd] at hx ⊢
        obtain ⟨c, hc⟩ := hx
        have hpow : q ^ j = q ^ e * q ^ (j - e) := by
          rw [← pow_add, Nat.add_sub_of_le hej]
        have hcancel : q ^ (j - e) * r = b * c := by
          apply mul_left_cancel₀ (pow_ne_zero e hq.ne_zero)
          simpa only [hpow, mul_assoc] using hc
        have hcop : IsCoprime b (q ^ (j - e)) :=
          (hq.coprime_iff_not_dvd.mpr hb).symm.pow_right
        have hbdiv : b ∣ r :=
          hcop.dvd_of_dvd_mul_left ⟨c, hcancel⟩
        obtain ⟨d, hd⟩ := hbdiv
        refine ⟨d, ?_⟩
        rw [hd]
        ring
  · exact primaryTorsionLayer_mono (Ideal.span {q}) e j hej

private theorem primaryTorsionGrade_cyclicPowerFactorQuotient_subsingleton
    (q : R) (hq : Prime q) (e : ℕ) (b : R) (hb : ¬ q ∣ b)
    (i : ℕ) (hei : e ≤ i) :
    Subsingleton
      (primaryTorsionGrade (Ideal.span {q})
        (R ⧸ Ideal.span {q ^ e * b}) i) := by
  rw [Submodule.Quotient.subsingleton_iff]
  apply eq_top_iff.mpr
  intro x _hx
  change (x : R ⧸ Ideal.span {q ^ e * b}) ∈
    primaryTorsionLayer (Ideal.span {q})
      (R ⧸ Ideal.span {q ^ e * b}) i
  rw [primaryTorsionLayer_cyclicPowerFactorQuotient_stable
      q hq e b hb i hei,
    ← primaryTorsionLayer_cyclicPowerFactorQuotient_stable
      q hq e b hb (i + 1) (hei.trans (Nat.le_succ i))]
  exact x.property

/-- Every primary-grade trace after the exact `q`-multiplicity is zero. -/
theorem primaryTorsionGradeTrace_cyclicPowerFactorQuotient_eq_zero_of_le
    [IsNoetherianRing R] (q : R) (hq : Prime q)
    [hmax : (Ideal.span {q}).IsMaximal]
    (e : ℕ) (b : R) (hb : ¬ q ∣ b) (i : ℕ) (hei : e ≤ i)
    (r : R) :
    primaryTorsionGradeTrace (Ideal.span {q})
        (cyclicPowerFactorQuotientMul q e b r) i = 0 := by
  let p := Ideal.span {q}
  let M := R ⧸ Ideal.span {q ^ e * b}
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI := primaryTorsionGradeModule (M := M) p i
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p M i) :=
    primaryTorsionGradeFinite (M := M) p i
  letI : Subsingleton (primaryTorsionGrade p M i) :=
    primaryTorsionGrade_cyclicPowerFactorQuotient_subsingleton
      q hq e b hb i hei
  rw [primaryTorsionGradeTrace]
  have hend : primaryTorsionGradeEndomorphism p
      (cyclicPowerFactorQuotientMul q e b r) i = 0 :=
    Subsingleton.elim _ _
  rw [hend, map_zero]

private theorem primaryTorsionTrace_cyclicPowerFactorQuotient_stable
    [IsNoetherianRing R] (q : R) (hq : Prime q)
    [hmax : (Ideal.span {q}).IsMaximal]
    (e : ℕ) (b : R) (hb : ¬ q ∣ b) (r : R)
    (n : ℕ) (hen : e ≤ n) :
    primaryTorsionTrace (Ideal.span {q})
        (cyclicPowerFactorQuotientMul q e b r) n =
      primaryTorsionTrace (Ideal.span {q})
        (cyclicPowerFactorQuotientMul q e b r) e := by
  induction n, hen using Nat.le_induction with
  | base => rfl
  | succ n hen ih =>
      rw [primaryTorsionTrace, Finset.sum_range_succ,
        primaryTorsionGradeTrace_cyclicPowerFactorQuotient_eq_zero_of_le
          q hq e b hb n hen r,
        add_zero]
      exact ih

/-- At every depth bounding the multiplicity, the primary trace on a cyclic
quotient is the multiplicity times the reduced multiplier. -/
theorem primaryTorsionTrace_cyclicQuotient_of_multiplicity_le
    [IsNoetherianRing R] (q a r : R) (hq : Irreducible q)
    [hmax : (Ideal.span {q}).IsMaximal] (ha : a ≠ 0)
    (n : ℕ) (hqn : multiplicity q a ≤ n) :
    primaryTorsionTrace (Ideal.span {q}) (cyclicQuotientMul a r) n =
      (multiplicity q a : R ⧸ Ideal.span {q}) *
        Ideal.Quotient.mk (Ideal.span {q}) r := by
  have hfinite : FiniteMultiplicity q a :=
    FiniteMultiplicity.of_not_isUnit hq.not_isUnit ha
  obtain ⟨b, hfactor, hb⟩ := hfinite.exists_eq_pow_mul_and_not_dvd
  have hbne : b ≠ 0 := by
    intro hbzero
    apply ha
    rw [hfactor, hbzero, mul_zero]
  calc
    primaryTorsionTrace (Ideal.span {q})
        (cyclicQuotientMul a r) n =
      primaryTorsionTrace (Ideal.span {q})
        (cyclicPowerFactorQuotientMul q (multiplicity q a) b r)
          (multiplicity q a) := by
            conv_lhs => rw [hfactor]
            exact primaryTorsionTrace_cyclicPowerFactorQuotient_stable
              q hq.prime (multiplicity q a) b hb r n hqn
    _ = _ := primaryTorsionTrace_cyclicPowerFactorQuotient
      q hq.ne_zero (multiplicity q a) b hbne r

private theorem primaryTorsionTrace_cyclicQuotient_of_multiplicity_le_of_eq_span
    [IsNoetherianRing R] (P : Ideal R) [P.IsMaximal]
    (q a r : R) (hq : Irreducible q) (ha : a ≠ 0)
    (hP : P = Ideal.span {q}) (n : ℕ)
    (hPn : multiplicity P (Ideal.span {a}) ≤ n) :
    primaryTorsionTrace P (cyclicQuotientMul a r) n =
      (multiplicity P (Ideal.span {a}) : R ⧸ P) *
        Ideal.Quotient.mk P r := by
  subst P
  rw [multiplicity_span_singleton_eq q a hq ha] at hPn ⊢
  exact primaryTorsionTrace_cyclicQuotient_of_multiplicity_le
    q a r hq ha n hPn

variable {k : Type*} [Field k] [Finite k]

/-- At a finite rational place, the stabilized primary trace on a polynomial
cyclic quotient is the principal-ideal multiplicity times the reduced
multiplier. -/
theorem primaryTorsionTrace_rationalAdicPolynomialQuotient_of_multiplicity_le
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (a : k[X]) (ha : a ≠ 0) (r : k[X]) (n : ℕ)
    (hpn : multiplicity p.asIdeal (Ideal.span {a}) ≤ n) :
    primaryTorsionTrace p.asIdeal (cyclicQuotientMul a r) n =
      (multiplicity p.asIdeal (Ideal.span {a}) : k[X] ⧸ p.asIdeal) *
        Ideal.Quotient.mk p.asIdeal r := by
  exact primaryTorsionTrace_cyclicQuotient_of_multiplicity_le_of_eq_span
    p.asIdeal (GlobalPlace.rationalAdicPolynomial p) a r
      (GlobalPlace.rationalAdicPolynomial_irreducible p) ha
        (GlobalPlace.rationalAdic_asIdeal_eq_span p) n hpn

end QEC.Coding.AlgebraicGeometry
