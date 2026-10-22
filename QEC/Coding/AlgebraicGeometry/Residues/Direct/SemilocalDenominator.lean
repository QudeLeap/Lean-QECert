import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import QEC.Coding.AlgebraicGeometry.Residues.Direct.IntegralDifferentialResidue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Semilocal denominator clearing on the direct chart

An element of the function field which is regular at every prime factor over
one direct height-one polynomial prime admits one common integral multiple
whose polynomial multiplier is nonzero modulo that base prime.  The proof
starts with an arbitrary integral multiple, removes its exact power of the
base-prime generator, and checks integrality of the remaining multiple at
every height-one prime of the integral closure.

This is only a denominator-clearing statement.  It does not assert a residue
identity, a global residue theorem, duality, genus, or Riemann--Roch.
-/

namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalDenominator

open scoped Polynomial RatFunc nonZeroDivisors
open Submodule.IsPrincipal UniqueFactorizationMonoid

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]

noncomputable local instance : Algebra k F := AffinePlace.constantAlgebra k F

abbrev R : Type _ := k[X]
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F

local instance : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)

open DirectIntegralDifferentialResidue

/-- If `x` is regular at every actual upper factor over a direct base prime,
then one polynomial which is nonzero modulo the base prime sends `x` into the
direct integral closure. -/
theorem exists_directSemilocal_integral_multiple
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) (x : F)
    (hx : ∀ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      GlobalPlace.RegularAt
        (AffinePlace.globalPlace k F (directFactorPlace k F p P)) x) :
    ∃ a : R k, a ∉ p.asIdeal ∧ ∃ b : B k F,
      algebraMap (B k F) F b = algebraMap (R k) F a * x := by
  classical
  let q : R k := generator p.asIdeal
  have hq_prime : Prime q := by
    dsimp only [q]
    exact prime_generator_of_isPrime p.asIdeal p.ne_bot
  obtain ⟨y, hy_ne, hy_integral⟩ :=
    exists_integral_multiples (R k) (RatFunc k) ({x} : Finset F)
  have hyx_integral : IsIntegral (R k) (y • x) :=
    hy_integral x (by simp)
  let b₀ : B k F := IsIntegralClosure.mk' (B k F) (y • x) hyx_integral
  have hb₀ : algebraMap (B k F) F b₀ = y • x :=
    IsIntegralClosure.algebraMap_mk' (B k F) (y • x) hyx_integral
  obtain ⟨a, hya, hq_not_dvd_a⟩ :=
    (FiniteMultiplicity.of_prime_left hq_prime hy_ne).exists_eq_pow_mul_and_not_dvd
  have ha_not_mem : a ∉ p.asIdeal := by
    apply (mem_iff_generator_dvd p.asIdeal).not.mpr
    simpa only [q] using hq_not_dvd_a
  have hpmap : Ideal.map (algebraMap (R k) (B k F)) p.asIdeal ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot p.ne_bot
  have hax_range : algebraMap (R k) F a * x ∈
      Set.range (algebraMap (B k F) F) := by
    apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro Q
    by_cases hqQ : algebraMap (R k) (B k F) q ∈ Q.asIdeal
    · have hmap_le :
          Ideal.map (algebraMap (R k) (B k F)) p.asIdeal ≤ Q.asIdeal := by
        rw [← Ideal.span_singleton_generator p.asIdeal, Ideal.map_span,
          Set.image_singleton]
        exact Ideal.span_le.2 (Set.singleton_subset_iff.mpr hqQ)
      have hQ_normalized : Q.asIdeal ∈ normalizedFactors
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) :=
        (Ideal.mem_normalizedFactors_iff hpmap).2 ⟨Q.isPrime, hmap_le⟩
      have hQ_factor : Q.asIdeal ∈ factors
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) := by
        simpa only [factors_eq_normalizedFactors] using hQ_normalized
      let P : (factors
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset :=
        ⟨Q.asIdeal, Multiset.mem_toFinset.mpr hQ_factor⟩
      have hQ_over : Q.asIdeal ∈ p.asIdeal.primesOver (B k F) :=
        (Ideal.mem_primesOver_iff_mem_normalizedFactors
          (B k F) p.ne_bot).2 hQ_normalized
      letI : Q.asIdeal.LiesOver p.asIdeal := hQ_over.2
      have haQ : algebraMap (R k) (B k F) a ∉ Q.asIdeal := by
        intro haQ
        apply ha_not_mem
        exact (Ideal.mem_of_liesOver (P := Q.asIdeal) (p := p.asIdeal) a).mpr haQ
      have ha_val : Q.valuation F (algebraMap (R k) F a) = 1 := by
        have := (Q.valuation_eq_one_iff_notMem
          (K := F) (r := algebraMap (R k) (B k F) a)).2 haQ
        simpa only [IsScalarTower.algebraMap_apply (R k) (B k F) F] using this
      have hP_eq : directFactorPlace k F p P = Q := by
        apply IsDedekindDomain.HeightOneSpectrum.ext
        rfl
      have hxQ : Q.valuation F x ≤ 1 := by
        have hxP := hx P
        change (directFactorPlace k F p P).valuation F x ≤ 1 at hxP
        simpa only [hP_eq] using hxP
      calc
        Q.valuation F (algebraMap (R k) F a * x) =
            Q.valuation F (algebraMap (R k) F a) * Q.valuation F x := by
          rw [(Q.valuation F).map_mul]
        _ = Q.valuation F x := by rw [ha_val, one_mul]
        _ ≤ 1 := hxQ
    · have hq_val : Q.valuation F (algebraMap (R k) F q) = 1 := by
        have := (Q.valuation_eq_one_iff_notMem
          (K := F) (r := algebraMap (R k) (B k F) q)).2 hqQ
        simpa only [IsScalarTower.algebraMap_apply (R k) (B k F) F] using this
      have hyx_val : Q.valuation F (algebraMap (R k) F y * x) ≤ 1 := by
        have hb₀_val : Q.valuation F (algebraMap (B k F) F b₀) ≤ 1 := by
          rw [Q.valuation_of_algebraMap]
          exact Q.intValuation_le_one b₀
        rw [hb₀] at hb₀_val
        simpa only [Algebra.smul_def] using hb₀_val
      have hya_field : algebraMap (R k) F y =
          (algebraMap (R k) F q) ^ multiplicity q y *
            algebraMap (R k) F a := by
        simpa only [map_mul, map_pow] using
          congrArg (algebraMap (R k) F) hya
      calc
        Q.valuation F (algebraMap (R k) F a * x) =
            Q.valuation F
              ((algebraMap (R k) F q) ^ multiplicity q y *
                (algebraMap (R k) F a * x)) := by
          symm
          rw [(Q.valuation F).map_mul, (Q.valuation F).map_pow, hq_val,
            one_pow, one_mul]
        _ = Q.valuation F (algebraMap (R k) F y * x) := by
          apply congrArg (Q.valuation F)
          rw [hya_field]
          ring
        _ ≤ 1 := hyx_val
  rcases hax_range with ⟨b, hb⟩
  exact ⟨a, ha_not_mem, b, hb⟩

end QEC.Coding.AlgebraicGeometry.DirectSemilocalDenominator
