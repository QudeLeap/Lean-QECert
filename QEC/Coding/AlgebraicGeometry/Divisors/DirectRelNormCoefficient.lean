import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import QEC.Coding.AlgebraicGeometry.Places.AffinePlaceDegree
import QEC.Coding.AlgebraicGeometry.Divisors.DirectNormCount
import QEC.Coding.AlgebraicGeometry.Divisors.SeparableNormalCover

namespace QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient

open scoped BigOperators Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid

section finite_collection

variable {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]

/-- Count a target after replacing every source occurrence by a finite block
of repeated target occurrences.  This is the reusable finite collection step
for any weighted pushforward of a normalized-factor multiset. -/
theorem count_bind_replicate_eq_sum (s : Multiset alpha) (f : alpha → beta)
    (w : alpha → Nat) (q : beta) :
    Multiset.count q (s.bind fun a => Multiset.replicate (w a) (f a)) =
      ∑ a ∈ s.toFinset, (if f a = q then w a else 0) * s.count a := by
  classical
  rw [Multiset.count_bind]
  simp only [Multiset.count_replicate]
  simpa [Nat.mul_comm] using
    Finset.sum_multiset_map_count s (fun a => if f a = q then w a else 0)

end finite_collection

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]

abbrev directRingOfIntegers : Type _ := _root_.FunctionField.ringOfIntegers k F

local notation3 "R" => k[X]
local notation3 "B" => directRingOfIntegers k F

local instance : Module.IsTorsionFree R B :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)

/-- A normalized factor of a nonzero direct-chart ideal is an actual maximal
ideal of the direct ring of integers.  Its contraction is maximal because the
actual extension is integral. -/
private theorem factor_isMaximal_and_under_isMaximal (I P : Ideal B)
    (hP : P ∈ normalizedFactors I) : P.IsMaximal ∧ (P.under R).IsMaximal := by
  have hprime : Prime P := prime_of_normalized_factor P hP
  have hP0 : P ≠ (⊥ : Ideal B) := by
    simpa only [Ideal.zero_eq_bot] using hprime.ne_zero
  have hPprime : P.IsPrime := Ideal.isPrime_of_prime hprime
  have hPmax : P.IsMaximal := hPprime.isMaximal hP0
  letI : P.IsMaximal := hPmax
  exact ⟨hPmax, Ideal.IsMaximal.under R P⟩

/-- The constructed normal-cover calculation specializes to every actual
normalized factor, after its contraction supplies the lower maximal ideal. -/
private theorem direct_relNorm_factor_eq_pow (I P : Ideal B)
    (hP : P ∈ normalizedFactors I) :
    Ideal.relNorm R P = (P.under R) ^ (P.under R).inertiaDeg' P := by
  obtain ⟨hPmax, hqmax⟩ := factor_isMaximal_and_under_isMaximal k F I P hP
  letI : P.IsMaximal := hPmax
  letI : (P.under R).IsMaximal := hqmax
  letI : P.LiesOver (P.under R) := ⟨rfl⟩
  exact
    SeparableNormalCover.direct_relNorm_eq_pow k F P (P.under R)

/-- The contraction of an actual normalized factor is nonzero in the direct
polynomial chart.  This unlocks the normalized-factor formula for its power. -/
private theorem under_factor_ne_bot (I P : Ideal B)
    (hP : P ∈ normalizedFactors I) : P.under R ≠ ⊥ := by
  obtain ⟨_, hqmax⟩ := factor_isMaximal_and_under_isMaximal k F I P hP
  exact Ring.ne_bot_of_isMaximal_of_not_isField hqmax (Ideal.polynomial_not_isField k)

/-- One direct factor contributes precisely its inertia-degree block at its
contracted lower prime. -/
private theorem normalizedFactors_relNorm_factor (I P : Ideal B)
    (hP : P ∈ normalizedFactors I) :
    normalizedFactors (Ideal.relNorm R P) =
      Multiset.replicate ((P.under R).inertiaDeg' P) (P.under R) := by
  rw [direct_relNorm_factor_eq_pow k F I P hP]
  have hq0 : P.under R ≠ ⊥ := under_factor_ne_bot k F I P hP
  obtain ⟨_, hqmax⟩ := factor_isMaximal_and_under_isMaximal k F I P hP
  have hqprime : Prime (P.under R) :=
    Ideal.prime_of_isPrime hq0 hqmax.isPrime
  rw [hqprime.irreducible.normalizedFactors_pow, normalize_eq]

/-- Relative ideal norm pushes the complete normalized-factor multiset
forward by contracting each factor and repeating it by the actual inertia
degree.  The proof uses only exact ideal factorization, norm multiplicativity,
and the constructed prime norm equation. -/
theorem normalizedFactors_relNorm_eq_bind (I : Ideal B) (hI : I ≠ ⊥) :
    normalizedFactors (Ideal.relNorm R I) =
      (normalizedFactors I).bind fun P =>
        Multiset.replicate ((P.under R).inertiaDeg' P) (P.under R) := by
  have hfactor : (normalizedFactors I).prod = I :=
    Ideal.prod_normalizedFactors_eq_self hI
  conv_lhs => rw [← hfactor]
  rw [map_multiset_prod]
  rw [normalizedFactors_multiset_prod]
  · apply congrArg Multiset.sum
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro P hP
    exact normalizedFactors_relNorm_factor k F I P hP
  · intro hzero
    obtain ⟨P, hP, hnormP⟩ := Multiset.mem_map.mp hzero
    have hnormPbot : Ideal.relNorm R P = ⊥ := by
      simpa only [Ideal.zero_eq_bot] using hnormP
    have hP0 : P ≠ (⊥ : Ideal B) := by
      simpa only [Ideal.zero_eq_bot] using (prime_of_normalized_factor P hP).ne_zero
    exact hP0 (Ideal.relNorm_eq_bot_iff.mp hnormPbot)

/-- The coefficient at a fixed lower prime after relative norm, expressed as
a finite weighted sum over the actual upper normalized factors. -/
private theorem direct_relNorm_coefficient_over_factors (I : Ideal B) (hI : I ≠ ⊥)
    (p : Ideal R) :
    Multiset.count p (normalizedFactors (Ideal.relNorm R I)) =
      ∑ P ∈ (normalizedFactors I).toFinset,
        (if P.under R = p then (P.under R).inertiaDeg' P else 0) *
          Multiset.count P (normalizedFactors I) := by
  rw [normalizedFactors_relNorm_eq_bind k F I hI]
  exact count_bind_replicate_eq_sum (normalizedFactors I) (fun P => P.under R)
    (fun P => (P.under R).inertiaDeg' P) p

/-- Collect the preceding finite factor sum along the actual finite fiber of
`p`.  Factors outside the fiber have zero conditional contribution, while
fiber primes absent from the factorization have zero multiset count. -/
private theorem direct_collect_factors_to_primesOverFinset (I : Ideal B)
    (p : Ideal R) [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ∑ P ∈ (normalizedFactors I).toFinset,
      (if P.under R = p then (P.under R).inertiaDeg' P else 0) *
        Multiset.count P (normalizedFactors I) =
      ∑ P ∈ IsDedekindDomain.primesOverFinset p B,
        p.inertiaDeg' P * Multiset.count P (normalizedFactors I) := by
  classical
  let s := (normalizedFactors I).toFinset.filter fun P => P.under R = p
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  change (∑ P ∈ s, (P.under R).inertiaDeg' P *
      Multiset.count P (normalizedFactors I)) = _
  have hs : s ⊆ IsDedekindDomain.primesOverFinset p B := by
    intro P hP
    rw [Finset.mem_filter] at hP
    obtain ⟨hPfactor, hPunder⟩ := hP
    have hprime : Prime P :=
      prime_of_normalized_factor P (by simpa only [Multiset.mem_toFinset] using hPfactor)
    have hPprime : P.IsPrime := Ideal.isPrime_of_prime hprime
    have hPover : P.LiesOver p := ⟨hPunder.symm⟩
    exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 B).mpr ⟨hPprime, hPover⟩
  calc
    ∑ P ∈ s, (P.under R).inertiaDeg' P *
        Multiset.count P (normalizedFactors I) =
      ∑ P ∈ IsDedekindDomain.primesOverFinset p B,
        (P.under R).inertiaDeg' P * Multiset.count P (normalizedFactors I) := by
      apply Finset.sum_subset hs
      intro P hPover hPnot
      have hPnotFactor : P ∉ normalizedFactors I := by
        intro hPfactor
        apply hPnot
        dsimp only [s]
        rw [Finset.mem_filter]
        refine ⟨Multiset.mem_toFinset.mpr hPfactor, ?_⟩
        obtain ⟨_, hPlies⟩ :=
          (IsDedekindDomain.mem_primesOverFinset_iff hp0 B).mp hPover
        letI : P.LiesOver p := hPlies
        exact (Ideal.over_def P p).symm
      simp only [Multiset.count_eq_zero_of_notMem hPnotFactor, mul_zero]
    _ = ∑ P ∈ IsDedekindDomain.primesOverFinset p B,
        p.inertiaDeg' P * Multiset.count P (normalizedFactors I) := by
      apply Finset.sum_congr rfl
      intro P hPfiber
      obtain ⟨_, hPover⟩ :=
        (IsDedekindDomain.mem_primesOverFinset_iff hp0 B).mp hPfiber
      letI : P.LiesOver p := hPover
      rw [← Ideal.over_def P p]

/-- Direct-chart coefficient identity for every nonzero actual ideal.  This
is the factorization form used by the principal specialization. -/
theorem direct_relNorm_coefficient_eq_sum_primesOver (I : Ideal B) (hI : I ≠ ⊥)
    (p : Ideal R) [p.IsMaximal] (hp0 : p ≠ ⊥) :
    Multiset.count p (normalizedFactors (Ideal.relNorm R I)) =
      ∑ P ∈ IsDedekindDomain.primesOverFinset p B,
        p.inertiaDeg' P * Multiset.count P (normalizedFactors I) := by
  rw [direct_relNorm_coefficient_over_factors k F I hI p]
  exact direct_collect_factors_to_primesOverFinset k F I p hp0

/-- Requested direct-chart principal-ideal coefficient identity. -/
theorem direct_relNorm_span_coefficient_eq_sum_primesOver (x : B) (hx : x ≠ 0)
    (p : Ideal R) [p.IsMaximal] (hp0 : p ≠ ⊥) :
    Multiset.count p
        (normalizedFactors (Ideal.relNorm R (Ideal.span ({x} : Set B)))) =
      ∑ P ∈ IsDedekindDomain.primesOverFinset p B,
        p.inertiaDeg' P *
          Multiset.count P (normalizedFactors (Ideal.span ({x} : Set B))) := by
  have hspan : Ideal.span ({x} : Set B) ≠ ⊥ := by
    exact mt Ideal.span_singleton_eq_bot.mp hx
  exact direct_relNorm_coefficient_eq_sum_primesOver k F
    (Ideal.span ({x} : Set B)) hspan p hp0

/-- The same coefficient identity after the existing direct relative-norm /
integral-norm bridge.  This is the form consumed by the field-norm and
divisor/order conversion already recorded for #721. -/
theorem direct_intNorm_span_coefficient_eq_sum_primesOver (x : B) (hx : x ≠ 0)
    (p : Ideal R) [p.IsMaximal] (hp0 : p ≠ ⊥) :
    Multiset.count p
        (normalizedFactors
          (Ideal.span ({Algebra.intNorm R B x} : Set R))) =
      ∑ P ∈ IsDedekindDomain.primesOverFinset p B,
        p.inertiaDeg' P *
          Multiset.count P (normalizedFactors (Ideal.span ({x} : Set B))) := by
  rw [← DirectNormCount.direct_relNorm_spanSingleton_eq_intNorm k F x]
  exact direct_relNorm_span_coefficient_eq_sum_primesOver k F x hx p hp0

end QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient
