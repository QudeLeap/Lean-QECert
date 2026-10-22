import QEC.Coding.AlgebraicGeometry.Towers.QuadraticStep

import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral

/-!
# The local different of a quadratic Artin--Schreier step

This file continues the actual simple-pole quadratic construction.  It builds
an upper prime, proves total ramification of index two, normalizes the upper
place so the new Artin--Schreier coordinate again has order `-1`, and computes
the different from the derivative of `W² + t W + t`.

The resulting different exponent is exactly `2 = 2 * (2 - 1)`.  No
compositum, normal-closure, divisor, genus, or asymptotic statement is stored
here.
-/

open Polynomial

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {K : Type*} [Field K] [Algebra F256 K]

instance quadraticArtinSchreierValuationRingScalarTower
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    IsScalarTower P.valuationRing K (QuadraticArtinSchreierField P a ha) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The actual integral closure of the lower valuation ring in the quadratic
Artin--Schreier field. -/
abbrev QuadraticArtinSchreierIntegralClosure
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :=
  integralClosure P.valuationRing (QuadraticArtinSchreierField P a ha)

noncomputable instance quadraticArtinSchreierIntegralClosureIsTorsionFree
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Module.IsTorsionFree P.valuationRing
      (QuadraticArtinSchreierIntegralClosure P a ha) := by
  letI : Module.IsTorsionFree P.valuationRing
      (QuadraticArtinSchreierField P a ha) :=
    Module.IsTorsionFree.trans_faithfulSMul
      P.valuationRing K (QuadraticArtinSchreierField P a ha)
  exact IsIntegralClosure.isTorsionFree
    P.valuationRing (QuadraticArtinSchreierField P a ha)

noncomputable instance quadraticArtinSchreierIntegralClosureFinite
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Module.Finite P.valuationRing
      (QuadraticArtinSchreierIntegralClosure P a ha) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite P.valuationRing K
    (QuadraticArtinSchreierField P a ha)
    (QuadraticArtinSchreierIntegralClosure P a ha)

noncomputable instance quadraticArtinSchreierIntegralClosureIsFractionRing
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    IsFractionRing (QuadraticArtinSchreierIntegralClosure P a ha)
      (QuadraticArtinSchreierField P a ha) :=
  integralClosure.isFractionRing_of_finite_extension K
    (QuadraticArtinSchreierField P a ha)

noncomputable instance quadraticArtinSchreierIntegralClosureIsDedekindDomain
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    IsDedekindDomain (QuadraticArtinSchreierIntegralClosure P a ha) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain P.valuationRing K
    (QuadraticArtinSchreierField P a ha)

/-- The reciprocal root as an actual integral element. -/
noncomputable def quadraticArtinSchreierIntegralRoot
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    QuadraticArtinSchreierIntegralClosure P a ha := by
  refine ⟨quadraticArtinSchreierReciprocalRoot P a ha, ?_⟩
  refine ⟨quadraticArtinSchreierReciprocalPolynomial P a ha,
    quadraticArtinSchreierReciprocalPolynomial_monic P a ha, ?_⟩
  change eval₂
      ((AdjoinRoot.of (quadraticArtinSchreierPolynomial P a ha)).comp
        (algebraMap P.valuationRing K))
      (quadraticArtinSchreierReciprocalRoot P a ha)
      (quadraticArtinSchreierReciprocalPolynomial P a ha) = 0
  rw [← eval₂_map]
  exact AdjoinRoot.eval₂_root (quadraticArtinSchreierPolynomial P a ha)

@[simp]
theorem coe_quadraticArtinSchreierIntegralRoot
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    (quadraticArtinSchreierIntegralRoot P a ha :
        QuadraticArtinSchreierField P a ha) =
      quadraticArtinSchreierReciprocalRoot P a ha :=
  rfl

/-- The lower uniformizer embedded in the quadratic integral closure. -/
noncomputable def quadraticArtinSchreierIntegralUniformizer
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    QuadraticArtinSchreierIntegralClosure P a ha := by
  refine ⟨quadraticArtinSchreierEmbedding P a ha a⁻¹, ?_⟩
  change IsIntegral P.valuationRing
    (algebraMap P.valuationRing (QuadraticArtinSchreierField P a ha)
      (reciprocalUniformizer P a ha))
  exact isIntegral_algebraMap

@[simp]
theorem coe_quadraticArtinSchreierIntegralUniformizer
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    (quadraticArtinSchreierIntegralUniformizer P a ha :
        QuadraticArtinSchreierField P a ha) =
      quadraticArtinSchreierEmbedding P a ha a⁻¹ :=
  rfl

private theorem exists_quadraticArtinSchreierUpperIdeal
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    ∃ Q : Ideal (QuadraticArtinSchreierIntegralClosure P a ha),
      Q.IsMaximal ∧
        Q.LiesOver (IsLocalRing.maximalIdeal P.valuationRing) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := QuadraticArtinSchreierIntegralClosure P a ha)
    (IsLocalRing.maximalIdeal P.valuationRing)

/-- A concrete upper prime above the lower simple-pole place. -/
noncomputable def quadraticArtinSchreierUpperIdeal
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Ideal (QuadraticArtinSchreierIntegralClosure P a ha) :=
  Classical.choose (exists_quadraticArtinSchreierUpperIdeal P a ha)

private theorem quadraticArtinSchreierUpperIdeal_isMaximal
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    (quadraticArtinSchreierUpperIdeal P a ha).IsMaximal :=
  (Classical.choose_spec
    (exists_quadraticArtinSchreierUpperIdeal P a ha)).1

theorem quadraticArtinSchreierUpperIdeal_liesOver
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    (quadraticArtinSchreierUpperIdeal P a ha).LiesOver
      (IsLocalRing.maximalIdeal P.valuationRing) :=
  (Classical.choose_spec
    (exists_quadraticArtinSchreierUpperIdeal P a ha)).2

@[simp]
theorem algebraMap_quadraticArtinSchreierUniformizer
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    algebraMap P.valuationRing
        (QuadraticArtinSchreierIntegralClosure P a ha)
        (reciprocalUniformizer P a ha) =
      quadraticArtinSchreierIntegralUniformizer P a ha := by
  rfl

theorem quadraticArtinSchreierIntegralUniformizer_mem_upperIdeal
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    quadraticArtinSchreierIntegralUniformizer P a ha ∈
      quadraticArtinSchreierUpperIdeal P a ha := by
  have hover := (quadraticArtinSchreierUpperIdeal_liesOver P a ha).over
  have hbase : reciprocalUniformizer P a ha ∈
      IsLocalRing.maximalIdeal P.valuationRing := by
    rw [maximalIdeal_eq_span_reciprocalUniformizer P a ha]
    exact Ideal.mem_span_singleton_self _
  change algebraMap P.valuationRing
      (QuadraticArtinSchreierIntegralClosure P a ha)
      (reciprocalUniformizer P a ha) ∈
        quadraticArtinSchreierUpperIdeal P a ha
  change reciprocalUniformizer P a ha ∈
    Ideal.under P.valuationRing (quadraticArtinSchreierUpperIdeal P a ha)
  rw [← hover]
  exact hbase

theorem quadraticArtinSchreierIntegralRoot_equation
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    quadraticArtinSchreierIntegralRoot P a ha ^ 2 +
        quadraticArtinSchreierIntegralUniformizer P a ha *
          quadraticArtinSchreierIntegralRoot P a ha +
        quadraticArtinSchreierIntegralUniformizer P a ha = 0 := by
  apply Subtype.ext
  exact quadraticArtinSchreierReciprocalRoot_equation P a ha

theorem quadraticArtinSchreierIntegralRoot_mem_upperIdeal
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    quadraticArtinSchreierIntegralRoot P a ha ∈
      quadraticArtinSchreierUpperIdeal P a ha := by
  let Q := quadraticArtinSchreierUpperIdeal P a ha
  let w := quadraticArtinSchreierIntegralRoot P a ha
  let t := quadraticArtinSchreierIntegralUniformizer P a ha
  have ht : t ∈ Q :=
    quadraticArtinSchreierIntegralUniformizer_mem_upperIdeal P a ha
  have hterm : t * w ∈ Q := Q.mul_mem_right _ ht
  have hrest : t * w + t ∈ Q := Q.add_mem hterm ht
  have heq : w ^ 2 + t * w + t = 0 :=
    quadraticArtinSchreierIntegralRoot_equation P a ha
  have hw2eq : w ^ 2 = -(t * w + t) := by
    linear_combination heq
  have hw2 : w ^ 2 ∈ Q := hw2eq.symm ▸ Q.neg_mem hrest
  exact (quadraticArtinSchreierUpperIdeal_isMaximal P a ha).isPrime.mem_of_pow_mem
    2 hw2

theorem map_maximalIdeal_eq_span_quadraticArtinSchreierIntegralUniformizer
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Ideal.map
        (algebraMap P.valuationRing
          (QuadraticArtinSchreierIntegralClosure P a ha))
        (IsLocalRing.maximalIdeal P.valuationRing) =
      Ideal.span
        ({quadraticArtinSchreierIntegralUniformizer P a ha} :
          Set (QuadraticArtinSchreierIntegralClosure P a ha)) := by
  rw [maximalIdeal_eq_span_reciprocalUniformizer P a ha,
    Ideal.map_span, Set.image_singleton]
  rw [algebraMap_quadraticArtinSchreierUniformizer]

theorem span_quadraticArtinSchreierIntegralUniformizer_le_upperIdeal_sq
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Ideal.span
        ({quadraticArtinSchreierIntegralUniformizer P a ha} :
          Set (QuadraticArtinSchreierIntegralClosure P a ha)) ≤
      (quadraticArtinSchreierUpperIdeal P a ha) ^ 2 := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  let Q := quadraticArtinSchreierUpperIdeal P a ha
  let w := quadraticArtinSchreierIntegralRoot P a ha
  let t := quadraticArtinSchreierIntegralUniformizer P a ha
  have ht : t ∈ Q :=
    quadraticArtinSchreierIntegralUniformizer_mem_upperIdeal P a ha
  have hw : w ∈ Q := quadraticArtinSchreierIntegralRoot_mem_upperIdeal P a ha
  have hw2 : w ^ 2 ∈ Q ^ 2 := Ideal.pow_mem_pow hw 2
  have hterm : t * w ∈ Q ^ 2 := by
    have hmul : t * w ∈ Q * Q := Ideal.mul_mem_mul ht hw
    simpa only [pow_two] using hmul
  have hsum : w ^ 2 + t * w ∈ Q ^ 2 := (Q ^ 2).add_mem hw2 hterm
  have heq : w ^ 2 + t * w + t = 0 :=
    quadraticArtinSchreierIntegralRoot_equation P a ha
  have hteq : t = -(w ^ 2 + t * w) := by
    linear_combination heq
  change t ∈ Q ^ 2
  rw [hteq]
  exact (Q ^ 2).neg_mem hsum

/-- The chosen upper prime as a height-one prime. -/
noncomputable def quadraticArtinSchreierUpperHeightOne
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    IsDedekindDomain.HeightOneSpectrum
      (QuadraticArtinSchreierIntegralClosure P a ha) :=
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  letI : (quadraticArtinSchreierUpperIdeal P a ha).LiesOver
      (IsLocalRing.maximalIdeal P.valuationRing) :=
    quadraticArtinSchreierUpperIdeal_liesOver P a ha
  { asIdeal := quadraticArtinSchreierUpperIdeal P a ha
    isPrime := (quadraticArtinSchreierUpperIdeal_isMaximal P a ha).isPrime
    ne_bot := Ideal.ne_bot_of_liesOver_of_ne_bot
      (IsDiscreteValuationRing.not_a_field P.valuationRing)
      (quadraticArtinSchreierUpperIdeal P a ha) }

theorem quadraticArtinSchreier_ramificationIdx_eq_two
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    (IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx'
      (quadraticArtinSchreierUpperIdeal P a ha) = 2 := by
  let O := P.valuationRing
  let C := QuadraticArtinSchreierIntegralClosure P a ha
  let L := QuadraticArtinSchreierField P a ha
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let Q : Ideal C := quadraticArtinSchreierUpperIdeal P a ha
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  letI : Q.LiesOver m := quadraticArtinSchreierUpperIdeal_liesOver P a ha
  letI : Q.IsPrime :=
    (quadraticArtinSchreierUpperIdeal_isMaximal P a ha).isPrime
  letI : NoZeroSMulDivisors O C := ⟨fun {_ _} h => smul_eq_zero.mp h⟩
  have hm0 : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap0 : Ideal.map (algebraMap O C) m ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm0
  have hmap_le : Ideal.map (algebraMap O C) m ≤ Q ^ 2 := by
    rw [show Ideal.map (algebraMap O C) m = Ideal.span
      ({quadraticArtinSchreierIntegralUniformizer P a ha} : Set C) by
        simpa only [O, C, m] using
          map_maximalIdeal_eq_span_quadraticArtinSchreierIntegralUniformizer
            P a ha]
    exact span_quadraticArtinSchreierIntegralUniformizer_le_upperIdeal_sq P a ha
  have hmult : multiplicity Q (Q ^ 2) ≤
      multiplicity Q (Ideal.map (algebraMap O C) m) :=
    (quadraticArtinSchreierUpperHeightOne P a ha).multiplicity_le_of_ideal_ge
      hmap_le hmap0
  have hQprime : Prime Q :=
    Ideal.prime_of_isPrime
      (quadraticArtinSchreierUpperHeightOne P a ha).ne_bot inferInstance
  have hlower : 2 ≤ m.ramificationIdx' Q := by
    calc
      2 = multiplicity Q (Q ^ 2) := by
        symm
        exact multiplicity_pow_self_of_prime hQprime 2
      _ ≤ multiplicity Q (Ideal.map (algebraMap O C) m) := hmult
      _ = m.ramificationIdx' Q :=
        (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
          hmap0 (inferInstance : Q.IsPrime)).symm
  have hupper : m.ramificationIdx' Q ≤ Module.finrank K L :=
    Ideal.ramificationIdx_le_finrank C K L Q
  have hfinrank : Module.finrank K L = 2 :=
    quadraticArtinSchreier_finrank P a ha
  change m.ramificationIdx' Q = 2
  omega

theorem quadraticArtinSchreierIntegralRoot_ne_zero
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    quadraticArtinSchreierIntegralRoot P a ha ≠ 0 := by
  intro hzero
  have hcoe := congrArg
    (fun y : QuadraticArtinSchreierIntegralClosure P a ha =>
      (y : QuadraticArtinSchreierField P a ha)) hzero
  simpa only [coe_quadraticArtinSchreierIntegralRoot, map_zero] using
    (quadraticArtinSchreierReciprocalRoot_ne_zero P a ha hcoe)

theorem quadraticArtinSchreierIntegralRoot_not_mem_upperIdeal_sq
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    quadraticArtinSchreierIntegralRoot P a ha ∉
      (quadraticArtinSchreierUpperIdeal P a ha) ^ 2 := by
  let O := P.valuationRing
  let C := QuadraticArtinSchreierIntegralClosure P a ha
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let Q : Ideal C := quadraticArtinSchreierUpperIdeal P a ha
  let w : C := quadraticArtinSchreierIntegralRoot P a ha
  let t : C := quadraticArtinSchreierIntegralUniformizer P a ha
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  intro hw2
  change w ∈ Q ^ 2 at hw2
  have ht2 : t ∈ Q ^ 2 :=
    span_quadraticArtinSchreierIntegralUniformizer_le_upperIdeal_sq P a ha
      (Ideal.mem_span_singleton_self t)
  have hw : w ∈ Q := quadraticArtinSchreierIntegralRoot_mem_upperIdeal P a ha
  have hw3 : w ^ 2 ∈ Q ^ 3 := by
    have hmul : w * w ∈ Q ^ 2 * Q := Ideal.mul_mem_mul hw2 hw
    rw [show w * w = w ^ 2 by ring,
      show Q ^ 2 * Q = Q ^ 3 by
        rw [show 3 = 2 + 1 by norm_num, pow_add, pow_one]] at hmul
    exact hmul
  have hterm3 : t * w ∈ Q ^ 3 := by
    have hmul : t * w ∈ Q ^ 2 * Q := Ideal.mul_mem_mul ht2 hw
    rw [show Q ^ 2 * Q = Q ^ 3 by
      rw [show 3 = 2 + 1 by norm_num, pow_add, pow_one]] at hmul
    exact hmul
  have hsum : w ^ 2 + t * w ∈ Q ^ 3 :=
    (Q ^ 3).add_mem hw3 hterm3
  have heq : w ^ 2 + t * w + t = 0 :=
    quadraticArtinSchreierIntegralRoot_equation P a ha
  have hteq : t = -(w ^ 2 + t * w) := by
    linear_combination heq
  have ht3 : t ∈ Q ^ 3 := by
    rw [hteq]
    exact (Q ^ 3).neg_mem hsum
  have hmap3 : Ideal.map (algebraMap O C) m ≤ Q ^ 3 := by
    rw [show Ideal.map (algebraMap O C) m = Ideal.span ({t} : Set C) by
      simpa only [O, C, m, t] using
        map_maximalIdeal_eq_span_quadraticArtinSchreierIntegralUniformizer
          P a ha,
      Ideal.span_le, Set.singleton_subset_iff]
    exact ht3
  have hm0 : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap0 : Ideal.map (algebraMap O C) m ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm0
  have hmult3 : multiplicity Q (Q ^ 3) ≤
      multiplicity Q (Ideal.map (algebraMap O C) m) :=
    (quadraticArtinSchreierUpperHeightOne P a ha).multiplicity_le_of_ideal_ge
      hmap3 hmap0
  have hQprime : Prime Q := Ideal.prime_of_isPrime
    (quadraticArtinSchreierUpperHeightOne P a ha).ne_bot
    (quadraticArtinSchreierUpperIdeal_isMaximal P a ha).isPrime
  have hleft : multiplicity Q (Q ^ 3) = 3 :=
    multiplicity_pow_self_of_prime hQprime 3
  have hright : multiplicity Q (Ideal.map (algebraMap O C) m) = 2 := by
    rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
      hmap0 (quadraticArtinSchreierUpperIdeal_isMaximal P a ha).isPrime]
    exact quadraticArtinSchreier_ramificationIdx_eq_two P a ha
  omega

theorem quadraticArtinSchreierIntegralRoot_multiplicity
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    multiplicity (quadraticArtinSchreierUpperIdeal P a ha)
      (Ideal.span
        ({quadraticArtinSchreierIntegralRoot P a ha} :
          Set (QuadraticArtinSchreierIntegralClosure P a ha))) = 1 := by
  let C := QuadraticArtinSchreierIntegralClosure P a ha
  let Q : Ideal C := quadraticArtinSchreierUpperIdeal P a ha
  let w : C := quadraticArtinSchreierIntegralRoot P a ha
  let I : Ideal C := Ideal.span ({w} : Set C)
  have hI0 : I ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    simpa only [w] using quadraticArtinSchreierIntegralRoot_ne_zero P a ha
  have hle : Ideal.map (algebraMap C C) I ≤ Q ^ 1 := by
    rw [Algebra.algebraMap_self, Ideal.map_id, pow_one]
    exact Ideal.span_le.2 (Set.singleton_subset_iff.2
      (quadraticArtinSchreierIntegralRoot_mem_upperIdeal P a ha))
  have hnle : ¬Ideal.map (algebraMap C C) I ≤ Q ^ (1 + 1) := by
    rw [Algebra.algebraMap_self, Ideal.map_id, one_add_one_eq_two]
    intro h
    exact quadraticArtinSchreierIntegralRoot_not_mem_upperIdeal_sq P a ha
      (h (Ideal.mem_span_singleton_self w))
  have hram : I.ramificationIdx' Q = 1 := Ideal.ramificationIdx_spec hle hnle
  have hmap0 : Ideal.map (algebraMap C C) I ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hI0
  calc
    multiplicity Q I = multiplicity Q (Ideal.map (algebraMap C C) I) := by
      rw [Algebra.algebraMap_self, Ideal.map_id]
    _ = I.ramificationIdx' Q :=
      (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hmap0
        (quadraticArtinSchreierUpperIdeal_isMaximal P a ha).isPrime).symm
    _ = 1 := hram

/-- The normalized upper place of the quadratic Artin--Schreier step. -/
noncomputable def quadraticArtinSchreierAbovePlace
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    GlobalPlace F256 (QuadraticArtinSchreierField P a ha) where
  valuation := (quadraticArtinSchreierUpperHeightOne P a ha).valuation
    (QuadraticArtinSchreierField P a ha)
  normalized :=
    (quadraticArtinSchreierUpperHeightOne P a ha).valuation_surjective
      (QuadraticArtinSchreierField P a ha)

private theorem quadraticArtinSchreierAbovePlace_order_integral_eq_multiplicity
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1)
    {z : QuadraticArtinSchreierIntegralClosure P a ha} (hz : z ≠ 0) :
    (quadraticArtinSchreierAbovePlace P a ha).order
        (algebraMap (QuadraticArtinSchreierIntegralClosure P a ha)
          (QuadraticArtinSchreierField P a ha) z) =
      (multiplicity (quadraticArtinSchreierUpperIdeal P a ha)
        (Ideal.span {z}) : ℤ) := by
  unfold quadraticArtinSchreierAbovePlace GlobalPlace.order
  rw [(quadraticArtinSchreierUpperHeightOne P a ha).valuation_of_algebraMap,
    (quadraticArtinSchreierUpperHeightOne P a ha).intValuation_eq_exp_neg_multiplicity hz,
    WithZero.log_exp]
  simp only [quadraticArtinSchreierUpperHeightOne]
  ring

private theorem quadraticArtinSchreierAbovePlace_order_reciprocalRoot
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    (quadraticArtinSchreierAbovePlace P a ha).order
      (quadraticArtinSchreierReciprocalRoot P a ha) = 1 := by
  change (quadraticArtinSchreierAbovePlace P a ha).order
    (algebraMap (QuadraticArtinSchreierIntegralClosure P a ha)
      (QuadraticArtinSchreierField P a ha)
      (quadraticArtinSchreierIntegralRoot P a ha)) = 1
  rw [quadraticArtinSchreierAbovePlace_order_integral_eq_multiplicity
      P a ha (quadraticArtinSchreierIntegralRoot_ne_zero P a ha),
    quadraticArtinSchreierIntegralRoot_multiplicity]
  norm_num

/-- The new Artin--Schreier coordinate again has normalized order `-1`. -/
theorem quadraticArtinSchreierAbovePlace_order_coordinate
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    (quadraticArtinSchreierAbovePlace P a ha).order
      (quadraticArtinSchreierCoordinate P a ha) = -1 := by
  rw [quadraticArtinSchreierCoordinate, GlobalPlace.order_inv,
    quadraticArtinSchreierAbovePlace_order_reciprocalRoot]

private theorem quadraticArtinSchreierReciprocalPolynomial_aeval_root
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Polynomial.aeval (quadraticArtinSchreierReciprocalRoot P a ha)
        (quadraticArtinSchreierReciprocalPolynomial P a ha) = 0 := by
  rw [Polynomial.aeval_def]
  change eval₂
      ((AdjoinRoot.of (quadraticArtinSchreierPolynomial P a ha)).comp
        (algebraMap P.valuationRing K))
      (quadraticArtinSchreierReciprocalRoot P a ha)
      (quadraticArtinSchreierReciprocalPolynomial P a ha) = 0
  rw [← eval₂_map]
  exact AdjoinRoot.eval₂_root (quadraticArtinSchreierPolynomial P a ha)

private theorem quadraticArtinSchreier_minpoly_reciprocalRoot
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    minpoly P.valuationRing (quadraticArtinSchreierReciprocalRoot P a ha) =
      quadraticArtinSchreierReciprocalPolynomial P a ha := by
  symm
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  letI : Module.IsTorsionFree P.valuationRing
      (QuadraticArtinSchreierField P a ha) :=
    Module.IsTorsionFree.trans_faithfulSMul P.valuationRing K
      (QuadraticArtinSchreierField P a ha)
  have hw_integral : IsIntegral P.valuationRing
      (quadraticArtinSchreierReciprocalRoot P a ha) := by
    have hport := (quadraticArtinSchreierIntegralRoot P a ha).property
    simp only [coe_quadraticArtinSchreierIntegralRoot] at hport ⊢
    exact hport
  have hmin_K : minpoly K (quadraticArtinSchreierReciprocalRoot P a ha) =
      quadraticArtinSchreierPolynomial P a ha := by
    simpa only [quadraticArtinSchreierReciprocalRoot,
      AdjoinRoot.powerBasis_gen] using
      AdjoinRoot.minpoly_powerBasis_gen_of_monic
        (quadraticArtinSchreierPolynomial_monic P a ha)
  have hmin_natDegree :
      (minpoly P.valuationRing
        (quadraticArtinSchreierReciprocalRoot P a ha)).natDegree = 2 := by
    calc
      (minpoly P.valuationRing
          (quadraticArtinSchreierReciprocalRoot P a ha)).natDegree =
          ((minpoly P.valuationRing
            (quadraticArtinSchreierReciprocalRoot P a ha)).map
              (algebraMap P.valuationRing K)).natDegree :=
        ((minpoly.monic hw_integral).natDegree_map _).symm
      _ = (minpoly K
          (quadraticArtinSchreierReciprocalRoot P a ha)).natDegree := by
        rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hw_integral]
      _ = (quadraticArtinSchreierPolynomial P a ha).natDegree := by
        rw [hmin_K]
      _ = 2 := quadraticArtinSchreierPolynomial_natDegree P a ha
  apply minpoly.IsIntegrallyClosed.unique_of_degree_le_degree_minpoly
  · exact quadraticArtinSchreierReciprocalPolynomial_monic P a ha
  · exact quadraticArtinSchreierReciprocalPolynomial_aeval_root P a ha
  · rw [degree_eq_natDegree
        (quadraticArtinSchreierReciprocalPolynomial_monic P a ha).ne_zero,
      degree_eq_natDegree (minpoly.ne_zero hw_integral),
      quadraticArtinSchreierReciprocalPolynomial_natDegree, hmin_natDegree]

private theorem quadraticArtinSchreier_minpoly_integralRoot
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    minpoly P.valuationRing (quadraticArtinSchreierIntegralRoot P a ha) =
      quadraticArtinSchreierReciprocalPolynomial P a ha := by
  calc
    minpoly P.valuationRing (quadraticArtinSchreierIntegralRoot P a ha) =
        minpoly P.valuationRing
          (algebraMap (QuadraticArtinSchreierIntegralClosure P a ha)
            (QuadraticArtinSchreierField P a ha)
            (quadraticArtinSchreierIntegralRoot P a ha)) :=
      (minpoly.algebraMap_eq
        (IsFractionRing.injective
          (QuadraticArtinSchreierIntegralClosure P a ha)
          (QuadraticArtinSchreierField P a ha))
        (quadraticArtinSchreierIntegralRoot P a ha)).symm
    _ = minpoly P.valuationRing
        (quadraticArtinSchreierReciprocalRoot P a ha) := by
      congr 1
    _ = quadraticArtinSchreierReciprocalPolynomial P a ha :=
      quadraticArtinSchreier_minpoly_reciprocalRoot P a ha

theorem quadraticArtinSchreierIntegralClosure_adjoin_root_eq_top
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Algebra.adjoin P.valuationRing
        ({quadraticArtinSchreierIntegralRoot P a ha} :
          Set (QuadraticArtinSchreierIntegralClosure P a ha)) = ⊤ := by
  let O := P.valuationRing
  let L := QuadraticArtinSchreierField P a ha
  let C := QuadraticArtinSchreierIntegralClosure P a ha
  let t : O := reciprocalUniformizer P a ha
  let w : C := quadraticArtinSchreierIntegralRoot P a ha
  let B : PowerBasis K L :=
    AdjoinRoot.powerBasis
      (quadraticArtinSchreierPolynomial_monic P a ha).ne_zero
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  have ht_irreducible : Irreducible t :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr (by
      simpa only [O, t] using
        maximalIdeal_eq_span_reciprocalUniformizer P a ha)
  have hB_integral : IsIntegral O B.gen := by
    have hport := (quadraticArtinSchreierIntegralRoot P a ha).property
    simp only [O, B, AdjoinRoot.powerBasis_gen,
      coe_quadraticArtinSchreierIntegralRoot] at hport ⊢
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
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hdisc_integral
  have hdisc_ne_zero : Algebra.discr K B.basis ≠ 0 :=
    (Algebra.discr_isUnit_of_basis K B.basis).ne_zero
  have hb_ne_zero : b ≠ 0 := by
    intro hb_zero
    apply hdisc_ne_zero
    rw [← hb, hb_zero, map_zero]
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb_ne_zero ht_irreducible
  rw [← hb, IsScalarTower.algebraMap_smul, hu] at hcleared
  have hcleared' := Subalgebra.smul_mem
    (Algebra.adjoin O ({B.gen} : Set L)) hcleared (↑(u⁻¹) : O)
  have ht_power : t ^ n • (z : L) ∈ Algebra.adjoin O ({B.gen} : Set L) := by
    simpa only [smul_smul, ← mul_assoc, Units.inv_mul, one_mul] using hcleared'
  have hminpoly_eisenstein :
      (minpoly O B.gen).IsEisensteinAt (Ideal.span ({t} : Set O)) := by
    have hE := quadraticArtinSchreierReciprocalPolynomial_isEisenstein P a ha
    rw [maximalIdeal_eq_span_reciprocalUniformizer P a ha] at hE
    have hminB : minpoly O B.gen =
        quadraticArtinSchreierReciprocalPolynomial P a ha := by
      have hport := quadraticArtinSchreier_minpoly_reciprocalRoot P a ha
      simp only [O, B, AdjoinRoot.powerBasis_gen] at hport ⊢
      exact hport
    rw [hminB]
    simpa only [O, t] using hE
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
    simp only [O, L, C, w, B,
      coe_quadraticArtinSchreierIntegralRoot,
      AdjoinRoot.powerBasis_gen] at hq ⊢
    exact hq
  rw [← hq_eq]
  exact hq_mem

theorem quadraticArtinSchreier_aeval_derivative_minpoly
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Polynomial.aeval (quadraticArtinSchreierIntegralRoot P a ha)
        (derivative (minpoly P.valuationRing
          (quadraticArtinSchreierIntegralRoot P a ha))) =
      quadraticArtinSchreierIntegralUniformizer P a ha := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP P.valuationRing 2 :=
    P.valuationRing.subtype.charP P.valuationRing.subtype_injective 2
  have hderivative :
      derivative (minpoly P.valuationRing
        (quadraticArtinSchreierIntegralRoot P a ha)) =
      C (reciprocalUniformizer P a ha) := by
    rw [quadraticArtinSchreier_minpoly_integralRoot,
      quadraticArtinSchreierReciprocalPolynomial]
    simp only [derivative_add, derivative_X_pow,
      derivative_C_mul_X, derivative_C]
    reduce_mod_char!
    norm_num
  rw [hderivative]
  simp only [aeval_C, algebraMap_quadraticArtinSchreierUniformizer]

/-- The quadratic different is generated by the embedded lower uniformizer. -/
theorem quadraticArtinSchreierDifferentIdeal_eq_span
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    differentIdeal P.valuationRing
        (QuadraticArtinSchreierIntegralClosure P a ha) =
      Ideal.span
        ({quadraticArtinSchreierIntegralUniformizer P a ha} :
          Set (QuadraticArtinSchreierIntegralClosure P a ha)) := by
  let O := P.valuationRing
  let C := QuadraticArtinSchreierIntegralClosure P a ha
  let L := QuadraticArtinSchreierField P a ha
  let w : C := quadraticArtinSchreierIntegralRoot P a ha
  let hfieldAdjoin : Algebra.adjoin K
      ({algebraMap C L w} : Set L) = ⊤ := by
    have hport := (AdjoinRoot.powerBasis
      (quadraticArtinSchreierPolynomial_monic P a ha).ne_zero).adjoin_gen_eq_top
    simp only [C, L, w, coe_quadraticArtinSchreierIntegralRoot,
      quadraticArtinSchreierReciprocalRoot, AdjoinRoot.powerBasis_gen] at hport ⊢
    exact hport
  have hconductor : conductor O w = ⊤ :=
    conductor_eq_top_of_adjoin_eq_top (by
      simpa only [O, C, w] using
        quadraticArtinSchreierIntegralClosure_adjoin_root_eq_top P a ha)
  have hdifferent := conductor_mul_differentIdeal O K L w hfieldAdjoin
  rw [hconductor, Ideal.top_mul,
    quadraticArtinSchreier_aeval_derivative_minpoly] at hdifferent
  simpa only [O, C, w] using hdifferent

/-- The quadratic simple-pole step has exact weak different exponent two. -/
theorem quadraticArtinSchreierDifferentIdeal_multiplicity
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    multiplicity (quadraticArtinSchreierUpperIdeal P a ha)
        (differentIdeal P.valuationRing
          (QuadraticArtinSchreierIntegralClosure P a ha)) = 2 := by
  let O := P.valuationRing
  let C := QuadraticArtinSchreierIntegralClosure P a ha
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let Q : Ideal C := quadraticArtinSchreierUpperIdeal P a ha
  let t : C := quadraticArtinSchreierIntegralUniformizer P a ha
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  have hm_ne_bot : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap_ne_bot : Ideal.map (algebraMap O C) m ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm_ne_bot
  have hmap : Ideal.map (algebraMap O C) m =
      Ideal.span ({t} : Set C) := by
    simpa only [O, C, m, t] using
      map_maximalIdeal_eq_span_quadraticArtinSchreierIntegralUniformizer
        P a ha
  rw [quadraticArtinSchreierDifferentIdeal_eq_span]
  calc
    multiplicity Q (Ideal.span ({t} : Set C)) =
        multiplicity Q (Ideal.map (algebraMap O C) m) := by rw [hmap]
    _ = m.ramificationIdx' Q :=
      (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
        hmap_ne_bot
        (quadraticArtinSchreierUpperIdeal_isMaximal P a ha).isPrime).symm
    _ = 2 := quadraticArtinSchreier_ramificationIdx_eq_two P a ha

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
