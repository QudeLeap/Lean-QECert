import QEC.Coding.AlgebraicGeometry.Towers.Step

import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# The distinguished place in one Garcia--Stichtenoth step

This file forms the integral closure of the preceding normalized valuation
ring in the concrete degree-sixteen step and chooses an actual maximal ideal
above its maximal ideal.  The corresponding adic valuation is normalized and
therefore gives the next global place.  No recursive tower, place count,
genus, divisor, or asymptotic statement is packaged here.
-/

open Polynomial

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {K : Type*} [Field K] [Algebra F256 K]

instance stepFieldValuationRingScalarTower
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsScalarTower P.valuationRing K (StepField P x hx) :=
  IsScalarTower.of_algebraMap_eq' rfl

instance stepFieldConstantScalarTower
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsScalarTower F256 K (StepField P x hx) :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable instance stepFieldFiniteDimensional
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    FiniteDimensional K (StepField P x hx) :=
  (AdjoinRoot.powerBasis (stepPolynomial_monic P x hx).ne_zero).finite

/-- The actual integral closure of the preceding valuation ring in one step. -/
abbrev StepIntegralClosure (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :=
  integralClosure P.valuationRing (StepField P x hx)

noncomputable instance stepIntegralClosureIsTorsionFree
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Module.IsTorsionFree P.valuationRing (StepIntegralClosure P x hx) := by
  letI : Module.IsTorsionFree P.valuationRing (StepField P x hx) :=
    Module.IsTorsionFree.trans_faithfulSMul
      P.valuationRing K (StepField P x hx)
  exact IsIntegralClosure.isTorsionFree
    P.valuationRing (StepField P x hx)

noncomputable instance stepIntegralClosureFinite
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Module.Finite P.valuationRing (StepIntegralClosure P x hx) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite P.valuationRing K (StepField P x hx)
    (StepIntegralClosure P x hx)

noncomputable instance stepIntegralClosureIsFractionRing
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsFractionRing (StepIntegralClosure P x hx) (StepField P x hx) :=
  integralClosure.isFractionRing_of_finite_extension K (StepField P x hx)

noncomputable instance stepIntegralClosureIsDedekindDomain
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsDedekindDomain (StepIntegralClosure P x hx) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain P.valuationRing K (StepField P x hx)

/-- The reciprocal Artin--Schreier root, as an actual integral element. -/
noncomputable def stepIntegralRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    StepIntegralClosure P x hx := by
  refine ⟨stepReciprocalRoot P x hx, ?_⟩
  refine ⟨reciprocalPolynomial P x hx,
    reciprocalPolynomial_monic P x hx, ?_⟩
  change eval₂
      ((AdjoinRoot.of (stepPolynomial P x hx)).comp
        (algebraMap P.valuationRing K))
      (stepReciprocalRoot P x hx) (reciprocalPolynomial P x hx) = 0
  rw [← eval₂_map]
  exact AdjoinRoot.eval₂_root (stepPolynomial P x hx)

@[simp]
theorem coe_stepIntegralRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (stepIntegralRoot P x hx : StepField P x hx) =
      stepReciprocalRoot P x hx :=
  rfl

/-- The preceding reciprocal uniformizer, embedded in the integral closure. -/
noncomputable def stepIntegralUniformizer
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    StepIntegralClosure P x hx := by
  refine ⟨stepFieldEmbedding P x hx x⁻¹, ?_⟩
  change IsIntegral P.valuationRing
    (algebraMap P.valuationRing (StepField P x hx)
      (reciprocalUniformizer P x hx))
  exact isIntegral_algebraMap

@[simp]
theorem coe_stepIntegralUniformizer
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (stepIntegralUniformizer P x hx : StepField P x hx) =
      stepFieldEmbedding P x hx x⁻¹ :=
  rfl

private theorem exists_stepUpperIdeal
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    ∃ Q : Ideal (StepIntegralClosure P x hx),
      Q.IsMaximal ∧
        Q.LiesOver (IsLocalRing.maximalIdeal P.valuationRing) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := StepIntegralClosure P x hx)
    (IsLocalRing.maximalIdeal P.valuationRing)

/-- A concrete maximal ideal in the step integral closure above the preceding
maximal ideal. -/
noncomputable def stepUpperIdeal
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Ideal (StepIntegralClosure P x hx) :=
  Classical.choose (exists_stepUpperIdeal P x hx)

private theorem stepUpperIdeal_isMaximal
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (stepUpperIdeal P x hx).IsMaximal :=
  (Classical.choose_spec (exists_stepUpperIdeal P x hx)).1

theorem stepUpperIdeal_liesOver
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (stepUpperIdeal P x hx).LiesOver
      (IsLocalRing.maximalIdeal P.valuationRing) :=
  (Classical.choose_spec (exists_stepUpperIdeal P x hx)).2

@[simp]
theorem algebraMap_reciprocalUniformizer
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    algebraMap P.valuationRing (StepIntegralClosure P x hx)
        (reciprocalUniformizer P x hx) =
      stepIntegralUniformizer P x hx := by
  rfl

theorem stepIntegralUniformizer_mem_upperIdeal
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    stepIntegralUniformizer P x hx ∈ stepUpperIdeal P x hx := by
  have hover := (stepUpperIdeal_liesOver P x hx).over
  have hbase : reciprocalUniformizer P x hx ∈
      IsLocalRing.maximalIdeal P.valuationRing := by
    rw [maximalIdeal_eq_span_reciprocalUniformizer P x hx]
    exact Ideal.mem_span_singleton_self _
  have hmap : algebraMap P.valuationRing (StepIntegralClosure P x hx)
      (reciprocalUniformizer P x hx) ∈ stepUpperIdeal P x hx := by
    change reciprocalUniformizer P x hx ∈
      Ideal.under P.valuationRing (stepUpperIdeal P x hx)
    rw [← hover]
    exact hbase
  simpa only [algebraMap_reciprocalUniformizer] using hmap

theorem stepIntegralRoot_equation
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    stepIntegralRoot P x hx ^ 16 +
        stepIntegralUniformizer P x hx ^ 16 *
          stepIntegralRoot P x hx ^ 15 +
        stepIntegralUniformizer P x hx = 0 := by
  apply Subtype.ext
  have hport := stepReciprocalRoot_equation P x hx
  simp only [map_add, map_mul, map_pow, map_zero, coe_stepIntegralRoot, coe_stepIntegralUniformizer] at hport ⊢
  exact hport

theorem stepIntegralRoot_mem_upperIdeal
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    stepIntegralRoot P x hx ∈ stepUpperIdeal P x hx := by
  let Q := stepUpperIdeal P x hx
  let w := stepIntegralRoot P x hx
  let t := stepIntegralUniformizer P x hx
  have ht : t ∈ Q := stepIntegralUniformizer_mem_upperIdeal P x hx
  have ht16 : t ^ 16 ∈ Q := Q.pow_mem_of_mem ht 16 (by norm_num)
  have hterm : t ^ 16 * w ^ 15 ∈ Q := Q.mul_mem_right _ ht16
  have hrest : t ^ 16 * w ^ 15 + t ∈ Q := Q.add_mem hterm ht
  have heq : w ^ 16 + t ^ 16 * w ^ 15 + t = 0 :=
    stepIntegralRoot_equation P x hx
  have hw16eq : w ^ 16 = -(t ^ 16 * w ^ 15 + t) := by
    linear_combination heq
  have hw16 : w ^ 16 ∈ Q := hw16eq.symm ▸ Q.neg_mem hrest
  exact (stepUpperIdeal_isMaximal P x hx).isPrime.mem_of_pow_mem 16 hw16

theorem map_maximalIdeal_eq_span_stepIntegralUniformizer
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Ideal.map (algebraMap P.valuationRing (StepIntegralClosure P x hx))
        (IsLocalRing.maximalIdeal P.valuationRing) =
      Ideal.span ({stepIntegralUniformizer P x hx} :
        Set (StepIntegralClosure P x hx)) := by
  rw [maximalIdeal_eq_span_reciprocalUniformizer P x hx,
    Ideal.map_span, Set.image_singleton,
    algebraMap_reciprocalUniformizer]

theorem span_stepIntegralUniformizer_le_upperIdeal_pow_sixteen
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Ideal.span ({stepIntegralUniformizer P x hx} :
        Set (StepIntegralClosure P x hx)) ≤
      (stepUpperIdeal P x hx) ^ 16 := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  let Q := stepUpperIdeal P x hx
  let w := stepIntegralRoot P x hx
  let t := stepIntegralUniformizer P x hx
  have ht : t ∈ Q := stepIntegralUniformizer_mem_upperIdeal P x hx
  have hw : w ∈ Q := stepIntegralRoot_mem_upperIdeal P x hx
  have hw16 : w ^ 16 ∈ Q ^ 16 := Ideal.pow_mem_pow hw 16
  have ht16 : t ^ 16 ∈ Q ^ 16 := Ideal.pow_mem_pow ht 16
  have hterm : t ^ 16 * w ^ 15 ∈ Q ^ 16 :=
    (Q ^ 16).mul_mem_right _ ht16
  have hsum : w ^ 16 + t ^ 16 * w ^ 15 ∈ Q ^ 16 :=
    (Q ^ 16).add_mem hw16 hterm
  have heq : w ^ 16 + t ^ 16 * w ^ 15 + t = 0 :=
    stepIntegralRoot_equation P x hx
  have hteq : t = -(w ^ 16 + t ^ 16 * w ^ 15) := by
    linear_combination heq
  change t ∈ Q ^ 16
  rw [hteq]
  exact (Q ^ 16).neg_mem hsum

/-- The chosen upper ideal as a height-one prime of the integral closure. -/
noncomputable def stepUpperHeightOne
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsDedekindDomain.HeightOneSpectrum (StepIntegralClosure P x hx) :=
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  letI : (stepUpperIdeal P x hx).LiesOver
      (IsLocalRing.maximalIdeal P.valuationRing) :=
    stepUpperIdeal_liesOver P x hx
  { asIdeal := stepUpperIdeal P x hx
    isPrime := (stepUpperIdeal_isMaximal P x hx).isPrime
    ne_bot := Ideal.ne_bot_of_liesOver_of_ne_bot
      (IsDiscreteValuationRing.not_a_field P.valuationRing)
      (stepUpperIdeal P x hx) }

/-- The distinguished upper prime is totally ramified in the degree-sixteen
step. -/
theorem step_ramificationIdx_eq_sixteen
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx'
      (stepUpperIdeal P x hx) = 16 := by
  let O := P.valuationRing
  let C := StepIntegralClosure P x hx
  let L := StepField P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let Q : Ideal C := stepUpperIdeal P x hx
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  letI : Q.LiesOver m := stepUpperIdeal_liesOver P x hx
  letI : Q.IsPrime := (stepUpperIdeal_isMaximal P x hx).isPrime
  letI : NoZeroSMulDivisors O C :=
    ⟨fun {_ _} h => (smul_eq_zero.mp h)⟩
  have hm0 : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap0 : Ideal.map (algebraMap O C) m ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm0
  have hmap_le : Ideal.map (algebraMap O C) m ≤ Q ^ 16 := by
    simpa only [O, C, m, Q,
      map_maximalIdeal_eq_span_stepIntegralUniformizer] using
      span_stepIntegralUniformizer_le_upperIdeal_pow_sixteen P x hx
  have hmult : multiplicity Q (Q ^ 16) ≤
      multiplicity Q (Ideal.map (algebraMap O C) m) :=
    (stepUpperHeightOne P x hx).multiplicity_le_of_ideal_ge hmap_le hmap0
  have hQprime : Prime Q :=
    Ideal.prime_of_isPrime (stepUpperHeightOne P x hx).ne_bot inferInstance
  have hlower : 16 ≤ m.ramificationIdx' Q := by
    calc
      16 = multiplicity Q (Q ^ 16) := by
        symm
        exact multiplicity_pow_self_of_prime hQprime 16
      _ ≤ multiplicity Q (Ideal.map (algebraMap O C) m) := hmult
      _ = m.ramificationIdx' Q :=
        (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
          hmap0 (inferInstance : Q.IsPrime)).symm
  have hupper : m.ramificationIdx' Q ≤ Module.finrank K L := by
    exact Ideal.ramificationIdx_le_finrank C K L Q
  have hfinrank : Module.finrank K L = 16 :=
    stepField_finrank P x hx
  change m.ramificationIdx' Q = 16
  omega

theorem stepIntegralRoot_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    stepIntegralRoot P x hx ≠ 0 := by
  intro hzero
  have hcoe := congrArg
    (fun y : StepIntegralClosure P x hx => (y : StepField P x hx)) hzero
  simpa only [coe_stepIntegralRoot, map_zero] using
    (stepReciprocalRoot_ne_zero P x hx hcoe)

theorem stepIntegralRoot_not_mem_upperIdeal_sq
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    stepIntegralRoot P x hx ∉ (stepUpperIdeal P x hx) ^ 2 := by
  let O := P.valuationRing
  let C := StepIntegralClosure P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let Q : Ideal C := stepUpperIdeal P x hx
  let w : C := stepIntegralRoot P x hx
  let t : C := stepIntegralUniformizer P x hx
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  intro hw2
  change w ∈ Q ^ 2 at hw2
  have ht : t ∈ Q := stepIntegralUniformizer_mem_upperIdeal P x hx
  have hw : w ∈ Q := stepIntegralRoot_mem_upperIdeal P x hx
  have hw15 : w ^ 15 ∈ Q ^ 15 := Ideal.pow_mem_pow hw 15
  have hw16_17 : w ^ 16 ∈ Q ^ 17 := by
    have hmul : w * w ^ 15 ∈ Q ^ 2 * Q ^ 15 :=
      Ideal.mul_mem_mul hw2 hw15
    have hwpow : w * w ^ 15 = w ^ 16 := by
      ring
    have hQpow : Q ^ 2 * Q ^ 15 = Q ^ 17 := by
      rw [show 17 = 2 + 15 by norm_num, pow_add]
    rw [hwpow, hQpow] at hmul
    exact hmul
  have ht16 : t ^ 16 ∈ Q ^ 16 := Ideal.pow_mem_pow ht 16
  have hterm17 : t ^ 16 * w ^ 15 ∈ Q ^ 17 := by
    have hbase : t ^ 16 * w ∈ Q ^ 16 * Q :=
      Ideal.mul_mem_mul ht16 hw
    have hQpow : Q ^ 16 * Q = Q ^ 17 := by
      simpa only [show 17 = 16 + 1 by norm_num] using (pow_succ Q 16).symm
    rw [hQpow] at hbase
    have hmul := (Q ^ 17).mul_mem_right (w ^ 14) hbase
    convert hmul using 1 <;> ring
  have hsum : w ^ 16 + t ^ 16 * w ^ 15 ∈ Q ^ 17 :=
    (Q ^ 17).add_mem hw16_17 hterm17
  have heq : w ^ 16 + t ^ 16 * w ^ 15 + t = 0 :=
    stepIntegralRoot_equation P x hx
  have hteq : t = -(w ^ 16 + t ^ 16 * w ^ 15) := by
    linear_combination heq
  have ht17 : t ∈ Q ^ 17 := by
    rw [hteq]
    exact (Q ^ 17).neg_mem hsum
  have hspan17 : Ideal.span ({t} : Set C) ≤ Q ^ 17 := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact ht17
  have hmap17 : Ideal.map (algebraMap O C) m ≤ Q ^ 17 := by
    simpa only [O, C, m, Q,
      map_maximalIdeal_eq_span_stepIntegralUniformizer] using hspan17
  have hm0 : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap0 : Ideal.map (algebraMap O C) m ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm0
  have hmult17 : multiplicity Q (Q ^ 17) ≤
      multiplicity Q (Ideal.map (algebraMap O C) m) :=
    (stepUpperHeightOne P x hx).multiplicity_le_of_ideal_ge hmap17 hmap0
  have hQprime : Prime Q := Ideal.prime_of_isPrime
    (stepUpperHeightOne P x hx).ne_bot
    (stepUpperIdeal_isMaximal P x hx).isPrime
  have hleft : multiplicity Q (Q ^ 17) = 17 :=
    multiplicity_pow_self_of_prime hQprime 17
  have hright : multiplicity Q (Ideal.map (algebraMap O C) m) = 16 := by
    rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
      hmap0 (stepUpperIdeal_isMaximal P x hx).isPrime]
    exact step_ramificationIdx_eq_sixteen P x hx
  omega

theorem stepIntegralRoot_multiplicity
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    multiplicity (stepUpperIdeal P x hx)
      (Ideal.span ({stepIntegralRoot P x hx} :
        Set (StepIntegralClosure P x hx))) = 1 := by
  let C := StepIntegralClosure P x hx
  let Q : Ideal C := stepUpperIdeal P x hx
  let w : C := stepIntegralRoot P x hx
  let I : Ideal C := Ideal.span ({w} : Set C)
  have hI0 : I ≠ ⊥ := by
    change Ideal.span ({w} : Set C) ≠ ⊥
    rw [Ne, Ideal.span_singleton_eq_bot]
    simpa only [w] using stepIntegralRoot_ne_zero P x hx
  have hle : Ideal.map (algebraMap C C) I ≤ Q ^ 1 := by
    rw [Algebra.algebraMap_self, Ideal.map_id, pow_one]
    change Ideal.span ({w} : Set C) ≤ Q
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact stepIntegralRoot_mem_upperIdeal P x hx
  have hnle : ¬Ideal.map (algebraMap C C) I ≤ Q ^ (1 + 1) := by
    rw [Algebra.algebraMap_self, Ideal.map_id, one_add_one_eq_two]
    change ¬Ideal.span ({w} : Set C) ≤ Q ^ 2
    intro h
    exact stepIntegralRoot_not_mem_upperIdeal_sq P x hx
      (h (Ideal.mem_span_singleton_self w))
  have hram : I.ramificationIdx' Q = 1 :=
    Ideal.ramificationIdx_spec hle hnle
  have hmap0 : Ideal.map (algebraMap C C) I ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hI0
  calc
    multiplicity Q I = multiplicity Q (Ideal.map (algebraMap C C) I) := by
      rw [Algebra.algebraMap_self, Ideal.map_id]
    _ = I.ramificationIdx' Q :=
      (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hmap0
        (stepUpperIdeal_isMaximal P x hx).isPrime).symm
    _ = 1 := hram

/-- The normalized global place on one step induced by the chosen upper
height-one prime. -/
noncomputable def stepAbovePlace
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    GlobalPlace F256 (StepField P x hx) where
  valuation := (stepUpperHeightOne P x hx).valuation (StepField P x hx)
  normalized := (stepUpperHeightOne P x hx).valuation_surjective
    (StepField P x hx)

/-- At the distinguished upper place, the order of a nonzero integral
element is its multiplicity at the chosen upper prime. -/
theorem stepAbovePlace_order_integral_eq_multiplicity
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    {y : StepIntegralClosure P x hx} (hy : y ≠ 0) :
    (stepAbovePlace P x hx).order
        (algebraMap (StepIntegralClosure P x hx) (StepField P x hx) y) =
      (multiplicity (stepUpperIdeal P x hx) (Ideal.span {y}) : ℤ) := by
  unfold stepAbovePlace GlobalPlace.order
  rw [(stepUpperHeightOne P x hx).valuation_of_algebraMap,
    (stepUpperHeightOne P x hx).intValuation_eq_exp_neg_multiplicity hy,
    WithZero.log_exp]
  simp only [stepUpperHeightOne]
  ring

/-- The reciprocal Artin--Schreier root is a uniformizer at the chosen upper
place. -/
theorem stepAbovePlace_order_stepReciprocalRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (stepAbovePlace P x hx).order (stepReciprocalRoot P x hx) = 1 := by
  change (stepAbovePlace P x hx).order
    (algebraMap (StepIntegralClosure P x hx) (StepField P x hx)
      (stepIntegralRoot P x hx)) = 1
  rw [stepAbovePlace_order_integral_eq_multiplicity P x hx
      (stepIntegralRoot_ne_zero P x hx),
    stepIntegralRoot_multiplicity]
  norm_num

/-- The next distinguished coordinate again has a normalized simple pole at
the chosen upper place. -/
theorem stepAbovePlace_order_stepDistinguishedCoordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (stepAbovePlace P x hx).order (stepDistinguishedCoordinate P x hx) = -1 := by
  rw [stepDistinguishedCoordinate_eq_inv, GlobalPlace.order_inv,
    stepAbovePlace_order_stepReciprocalRoot]

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
