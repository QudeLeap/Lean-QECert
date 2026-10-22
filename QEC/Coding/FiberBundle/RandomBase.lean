import QEC.Coding.FiberBundle.Core
import QEC.Coding.CSS.ParityChecks
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The HHO20 random classical-code base

This module formalizes the probability space from
`hastings-haah-odonnell-2020-fiber-bundle/bundle.tex:719-810`.
For `n_B = 4 r` variables and `m_B = 3 r` checks, every possible Tanner
incidence is sampled independently with probability `Delta / n_B`.

The definitions below describe the random construction and its good events.
The quantitative probability bounds are proved in later proof-closure modules;
they are not accepted as fields or caller-supplied hypotheses here.
-/

namespace QEC.Coding.FiberBundle.RandomBase

open scoped BigOperators
open MeasureTheory

universe u

/--
The independent product of finitely many probability mass functions.

Its mass at `x` is the product of the coordinate masses, so independence is
built into the distribution rather than asserted separately.
-/
noncomputable def independentProduct
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type u} [∀ i, Fintype (κ i)]
    (p : ∀ i, PMF (κ i)) :
    PMF (∀ i, κ i) :=
  PMF.ofFintype
    (fun x => ∏ i, p i (x i))
    (by
      rw [← Fintype.prod_sum]
      apply Finset.prod_eq_one
      intro i _hi
      simpa only [tsum_fintype] using (PMF.tsum_coe (p i)))

@[simp]
theorem independentProduct_apply
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type u} [∀ i, Fintype (κ i)]
    (p : ∀ i, PMF (κ i)) (x : ∀ i, κ i) :
    independentProduct p x = ∏ i, p i (x i) := by
  rfl

/--
The measure induced by the finite independent-product PMF is Mathlib's product
measure of the coordinate PMFs.
-/
theorem independentProduct_toMeasure_eq_pi
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type u} [∀ i, Fintype (κ i)]
    [∀ i, MeasurableSpace (κ i)]
    [∀ i, MeasurableSingletonClass (κ i)]
    (p : ∀ i, PMF (κ i)) :
    (independentProduct p).toMeasure =
      Measure.pi (fun i => (p i).toMeasure) := by
  apply Measure.ext_of_singleton
  intro x
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  have hsingleton :
      ({x} : Set (∀ i, κ i)) =
        Set.univ.pi (fun i => ({x i} : Set (κ i))) := by
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_singleton_iff]
    exact funext_iff
  rw [hsingleton, Measure.pi_pi]
  simp only [independentProduct_apply,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]

/--
Coordinate projections are independent under the measure induced by
`independentProduct`.
-/
theorem independentProduct_iIndepFun
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type u} [∀ i, Fintype (κ i)]
    [∀ i, MeasurableSpace (κ i)]
    [∀ i, MeasurableSingletonClass (κ i)]
    (p : ∀ i, PMF (κ i)) :
    ProbabilityTheory.iIndepFun
      (fun i x => x i) (independentProduct p).toMeasure := by
  rw [independentProduct_toMeasure_eq_pi p]
  exact ProbabilityTheory.iIndepFun_pi fun _ => Measurable.aemeasurable measurable_id

/-- Each coordinate projection has exactly its specified coordinate law. -/
theorem independentProduct_coordinate_hasLaw
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type u} [∀ i, Fintype (κ i)]
    [∀ i, MeasurableSpace (κ i)]
    [∀ i, MeasurableSingletonClass (κ i)]
    (p : ∀ i, PMF (κ i)) (i : ι) :
    ProbabilityTheory.HasLaw
      (fun x => x i) (p i).toMeasure (independentProduct p).toMeasure := by
  rw [independentProduct_toMeasure_eq_pi p]
  exact (MeasureTheory.measurePreserving_eval
    (fun i => (p i).toMeasure) i).hasLaw

/-- The exact HHO20 incidence probability `Delta / n_B`. -/
noncomputable def incidenceProbability (nB Delta : Nat) : NNReal :=
  (Delta : NNReal) / (nB : NNReal)

theorem incidenceProbability_le_one
    {nB Delta : Nat} (hDelta : Delta ≤ nB) :
    incidenceProbability nB Delta ≤ 1 := by
  apply div_le_one_of_le₀
  · exact_mod_cast hDelta
  · exact bot_le

/--
A sampled Tanner graph with `m_B = 3 r` checks and `n_B = 4 r` variables.
-/
abbrev Sample (r : Nat) :=
  (Fin (3 * r) × Fin (4 * r)) → Bool

/--
The HHO20 random-base distribution.  Every check-variable incidence is an
independent Bernoulli variable of density `Delta / (4 r)`.
-/
noncomputable def distribution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    PMF (Sample r) :=
  independentProduct fun _ =>
    PMF.bernoulli
      (incidenceProbability (4 * r) Delta)
      (incidenceProbability_le_one hDelta)

@[simp]
theorem distribution_apply
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (sample : Sample r) :
    distribution r Delta hDelta sample =
      ∏ edge : Fin (3 * r) × Fin (4 * r),
        cond (sample edge)
          (incidenceProbability (4 * r) Delta)
          (1 - incidenceProbability (4 * r) Delta) := by
  simp only [distribution, independentProduct_apply, PMF.bernoulli_apply]
  exact (ENNReal.ofNNReal_finsetProd _ _).symm

/-- Every Tanner incidence coordinate is independent under the random-base measure. -/
theorem distribution_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun edge (sample : Sample r) => sample edge)
      (distribution r Delta hDelta).toMeasure := by
  exact independentProduct_iIndepFun _

/-- Each sampled incidence has the exact Bernoulli law `Delta / (4r)`. -/
theorem distribution_coordinate_hasLaw
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (edge : Fin (3 * r) × Fin (4 * r)) :
    ProbabilityTheory.HasLaw
      (fun sample : Sample r => sample edge)
      (PMF.bernoulli
        (incidenceProbability (4 * r) Delta)
        (incidenceProbability_le_one hDelta)).toMeasure
      (distribution r Delta hDelta).toMeasure := by
  simpa only [distribution] using
    (independentProduct_coordinate_hasLaw
      (fun _ : Fin (3 * r) × Fin (4 * r) =>
        PMF.bernoulli
          (incidenceProbability (4 * r) Delta)
          (incidenceProbability_le_one hDelta))
      edge)

/-- The real indicator of one sampled Tanner incidence. -/
def incidenceReal
    {r : Nat} (edge : Fin (3 * r) × Fin (4 * r))
    (sample : Sample r) : Real :=
  cond (sample edge) 1 0

/-- The real incidence indicators remain mutually independent. -/
theorem distribution_incidenceReal_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun edge => incidenceReal edge)
      (distribution r Delta hDelta).toMeasure := by
  exact (distribution_iIndepFun r Delta hDelta).comp
    (fun _ b => cond b (1 : Real) 0)
    (fun _ => by fun_prop)

/-- The expectation of every incidence indicator is exactly `Delta / (4r)`. -/
theorem integral_incidenceReal
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (edge : Fin (3 * r) × Fin (4 * r)) :
    ∫ sample, incidenceReal edge sample ∂(distribution r Delta hDelta).toMeasure =
      (incidenceProbability (4 * r) Delta).toReal := by
  calc
    _ = ∫ b, cond b (1 : Real) 0 ∂
        (PMF.bernoulli
          (incidenceProbability (4 * r) Delta)
          (incidenceProbability_le_one hDelta)).toMeasure := by
      exact (distribution_coordinate_hasLaw r Delta hDelta edge).integral_comp
        (f := fun b : Bool => cond b (1 : Real) 0)
        (by fun_prop)
    _ = _ := PMF.bernoulli_expectation
      (incidenceProbability_le_one hDelta)

/-- Exact moment-generating function of one sampled incidence. -/
theorem mgf_incidenceReal
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (edge : Fin (3 * r) × Fin (4 * r)) (t : Real) :
    ProbabilityTheory.mgf
        (incidenceReal edge)
        (distribution r Delta hDelta).toMeasure
        t =
      (1 - (incidenceProbability (4 * r) Delta).toReal) +
        (incidenceProbability (4 * r) Delta).toReal * Real.exp t := by
  rw [ProbabilityTheory.mgf]
  calc
    _ = ∫ b, Real.exp (t * cond b (1 : Real) 0) ∂
        (PMF.bernoulli
          (incidenceProbability (4 * r) Delta)
          (incidenceProbability_le_one hDelta)).toMeasure := by
      exact (distribution_coordinate_hasLaw r Delta hDelta edge).integral_comp
        (f := fun b : Bool => Real.exp (t * cond b (1 : Real) 0))
        (by fun_prop)
    _ = _ := by
      rw [PMF.integral_eq_sum]
      simp [PMF.bernoulli_apply]
      rw [NNReal.coe_sub (incidenceProbability_le_one hDelta)]
      norm_num
      ring

/-- Every real incidence indicator lies in the unit interval. -/
theorem incidenceReal_mem_Icc
    {r : Nat} (edge : Fin (3 * r) × Fin (4 * r)) :
    ∀ sample : Sample r, incidenceReal edge sample ∈ Set.Icc (0 : Real) 1 := by
  intro sample
  cases h : sample edge <;> simp [incidenceReal, h]

/--
One centered incidence indicator is sub-Gaussian with Hoeffding parameter
`1/4`.  The centering constant is computed from the sampled Bernoulli law,
not supplied by the caller.
-/
theorem incidenceReal_hasSubgaussianMGF
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (edge : Fin (3 * r) × Fin (4 * r)) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun sample =>
        incidenceReal edge sample -
          (incidenceProbability (4 * r) Delta).toReal)
      (1 / 4 : NNReal)
      (distribution r Delta hDelta).toMeasure := by
  have h :=
    ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
      (μ := (distribution r Delta hDelta).toMeasure)
      (X := incidenceReal edge)
      (a := (0 : Real))
      (b := (1 : Real))
      (by fun_prop)
      (Filter.Eventually.of_forall (incidenceReal_mem_Icc edge))
  convert h using 1
  · simp [integral_incidenceReal r Delta hDelta edge]
  · norm_num

/-- The centered Tanner-incidence indicators are mutually independent. -/
theorem distribution_centeredIncidence_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun edge sample =>
        incidenceReal edge sample -
          (incidenceProbability (4 * r) Delta).toReal)
      (distribution r Delta hDelta).toMeasure := by
  exact (distribution_incidenceReal_iIndepFun r Delta hDelta).comp
    (fun _ x => x - (incidenceProbability (4 * r) Delta).toReal)
    (fun _ => by fun_prop)

/-- Convert a sampled Tanner graph to its binary base-boundary matrix. -/
def boundary {r : Nat} (sample : Sample r) :
    Matrix (Fin (3 * r)) (Fin (4 * r)) (ZMod 2) :=
  fun a b => if sample (a, b) then 1 else 0

/-- The number of variables incident to a sampled check. -/
def checkDegree {r : Nat} (sample : Sample r) (a : Fin (3 * r)) : Nat :=
  (Finset.univ.filter fun b : Fin (4 * r) => sample (a, b)).card

/-- The number of checks incident to a sampled variable. -/
def variableDegree {r : Nat} (sample : Sample r) (b : Fin (4 * r)) : Nat :=
  (Finset.univ.filter fun a : Fin (3 * r) => sample (a, b)).card

/-- A check degree is the sum of its real incidence indicators. -/
theorem checkDegree_cast_eq_sum_incidenceReal
    {r : Nat} (sample : Sample r) (a : Fin (3 * r)) :
    (checkDegree sample a : Real) =
      ∑ b : Fin (4 * r), incidenceReal (a, b) sample := by
  simp [checkDegree, incidenceReal, Bool.cond_eq_ite]

/-- A variable degree is the sum of its real incidence indicators. -/
theorem variableDegree_cast_eq_sum_incidenceReal
    {r : Nat} (sample : Sample r) (b : Fin (4 * r)) :
    (variableDegree sample b : Real) =
      ∑ a : Fin (3 * r), incidenceReal (a, b) sample := by
  simp [variableDegree, incidenceReal, Bool.cond_eq_ite]

/-- The expected check degree is exactly `Delta`. -/
theorem check_expected_degree
    (r Delta : Nat) (hr : 0 < r) :
    ((4 * r : Nat) : Real) *
        (incidenceProbability (4 * r) Delta).toReal =
      Delta := by
  simp only [incidenceProbability, NNReal.coe_div, NNReal.coe_natCast]
  field_simp

/-- The expected variable degree is exactly `3 Delta / 4`. -/
theorem variable_expected_degree
    (r Delta : Nat) (hr : 0 < r) :
    ((3 * r : Nat) : Real) *
        (incidenceProbability (4 * r) Delta).toReal =
      3 * (Delta : Real) / 4 := by
  rw [← check_expected_degree r Delta hr]
  push_cast
  field_simp

/-- Rewrite a centered check-incidence sum as degree minus its exact mean. -/
theorem check_centered_sum_eq
    (r Delta : Nat) (hr : 0 < r)
    (sample : Sample r) (a : Fin (3 * r)) :
    (∑ b : Fin (4 * r),
        (incidenceReal (a, b) sample -
          (incidenceProbability (4 * r) Delta).toReal)) =
      (checkDegree sample a : Real) - Delta := by
  rw [Finset.sum_sub_distrib, ← checkDegree_cast_eq_sum_incidenceReal]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_fin]
  rw [check_expected_degree r Delta hr]

/-- Rewrite a centered variable-incidence sum as degree minus its exact mean. -/
theorem variable_centered_sum_eq
    (r Delta : Nat) (hr : 0 < r)
    (sample : Sample r) (b : Fin (4 * r)) :
    (∑ a : Fin (3 * r),
        (incidenceReal (a, b) sample -
          (incidenceProbability (4 * r) Delta).toReal)) =
      (variableDegree sample b : Real) - 3 * (Delta : Real) / 4 := by
  rw [Finset.sum_sub_distrib, ← variableDegree_cast_eq_sum_incidenceReal]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_fin]
  rw [variable_expected_degree r Delta hr]

/-- Exact MGF of a sampled check degree. -/
theorem mgf_checkDegree
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) (t : Real) :
    ProbabilityTheory.mgf
        (fun sample => (checkDegree sample a : Real))
        (distribution r Delta hDelta).toMeasure
        t =
      ((1 - (incidenceProbability (4 * r) Delta).toReal) +
          (incidenceProbability (4 * r) Delta).toReal * Real.exp t) ^
        (4 * r) := by
  rw [show (fun sample => (checkDegree sample a : Real)) =
      (fun sample => ∑ b : Fin (4 * r), incidenceReal (a, b) sample) by
    funext sample
    exact checkDegree_cast_eq_sum_incidenceReal sample a]
  have h_indep :=
    (distribution_incidenceReal_iIndepFun r Delta hDelta).precomp
      (g := fun b : Fin (4 * r) => (a, b))
      (by
        intro b₁ b₂ h
        exact congrArg Prod.snd h)
  rw [show (fun sample => ∑ b : Fin (4 * r), incidenceReal (a, b) sample) =
      (∑ b : Fin (4 * r), incidenceReal (a, b)) by
    funext sample
    simp]
  rw [h_indep.mgf_sum (fun _ => by fun_prop) Finset.univ]
  simp_rw [mgf_incidenceReal r Delta hDelta]
  simp

/-- Exact MGF of a sampled variable degree. -/
theorem mgf_variableDegree
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) (t : Real) :
    ProbabilityTheory.mgf
        (fun sample => (variableDegree sample b : Real))
        (distribution r Delta hDelta).toMeasure
        t =
      ((1 - (incidenceProbability (4 * r) Delta).toReal) +
          (incidenceProbability (4 * r) Delta).toReal * Real.exp t) ^
        (3 * r) := by
  rw [show (fun sample => (variableDegree sample b : Real)) =
      (fun sample => ∑ a : Fin (3 * r), incidenceReal (a, b) sample) by
    funext sample
    exact variableDegree_cast_eq_sum_incidenceReal sample b]
  have h_indep :=
    (distribution_incidenceReal_iIndepFun r Delta hDelta).precomp
      (g := fun a : Fin (3 * r) => (a, b))
      (by
        intro a₁ a₂ h
        exact congrArg Prod.fst h)
  rw [show (fun sample => ∑ a : Fin (3 * r), incidenceReal (a, b) sample) =
      (∑ a : Fin (3 * r), incidenceReal (a, b)) by
    funext sample
    simp]
  rw [h_indep.mgf_sum (fun _ => by fun_prop) Finset.univ]
  simp_rw [mgf_incidenceReal r Delta hDelta]
  simp

/-- The Bernoulli MGF is bounded by its Poisson envelope. -/
theorem bernoulli_mgf_le_poisson
    (r Delta : Nat) (t : Real) :
    (1 - (incidenceProbability (4 * r) Delta).toReal) +
        (incidenceProbability (4 * r) Delta).toReal * Real.exp t ≤
      Real.exp
        ((incidenceProbability (4 * r) Delta).toReal *
          (Real.exp t - 1)) := by
  calc
    _ = (incidenceProbability (4 * r) Delta).toReal *
          (Real.exp t - 1) + 1 := by ring
    _ ≤ _ := Real.add_one_le_exp _

/-- Poisson-envelope MGF bound for one check degree. -/
theorem mgf_checkDegree_le_poisson
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) (t : Real) :
    ProbabilityTheory.mgf
        (fun sample => (checkDegree sample a : Real))
        (distribution r Delta hDelta).toMeasure
        t ≤
      Real.exp ((Delta : Real) * (Real.exp t - 1)) := by
  rw [mgf_checkDegree r Delta hDelta a t]
  let p := (incidenceProbability (4 * r) Delta).toReal
  have hp_nonneg : 0 ≤ p := by positivity
  have hp_one : p ≤ 1 := by
    exact_mod_cast incidenceProbability_le_one hDelta
  have hbase :
      0 ≤ (1 - p) + p * Real.exp t := by
    positivity
  calc
    ((1 - p) + p * Real.exp t) ^ (4 * r) ≤
        (Real.exp (p * (Real.exp t - 1))) ^ (4 * r) :=
      pow_le_pow_left₀ hbase (bernoulli_mgf_le_poisson r Delta t) _
    _ = Real.exp
        (((4 * r : Nat) : Real) * (p * (Real.exp t - 1))) := by
      rw [Real.exp_nat_mul]
    _ = Real.exp ((Delta : Real) * (Real.exp t - 1)) := by
      congr 1
      dsimp [p]
      rw [← mul_assoc, check_expected_degree r Delta hr]

/-- Poisson-envelope MGF bound for one variable degree. -/
theorem mgf_variableDegree_le_poisson
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) (t : Real) :
    ProbabilityTheory.mgf
        (fun sample => (variableDegree sample b : Real))
        (distribution r Delta hDelta).toMeasure
        t ≤
      Real.exp ((3 * (Delta : Real) / 4) * (Real.exp t - 1)) := by
  rw [mgf_variableDegree r Delta hDelta b t]
  let p := (incidenceProbability (4 * r) Delta).toReal
  have hp_nonneg : 0 ≤ p := by positivity
  have hp_one : p ≤ 1 := by
    exact_mod_cast incidenceProbability_le_one hDelta
  have hbase :
      0 ≤ (1 - p) + p * Real.exp t := by
    positivity
  calc
    ((1 - p) + p * Real.exp t) ^ (3 * r) ≤
        (Real.exp (p * (Real.exp t - 1))) ^ (3 * r) :=
      pow_le_pow_left₀ hbase (bernoulli_mgf_le_poisson r Delta t) _
    _ = Real.exp
        (((3 * r : Nat) : Real) * (p * (Real.exp t - 1))) := by
      rw [Real.exp_nat_mul]
    _ = Real.exp ((3 * (Delta : Real) / 4) * (Real.exp t - 1)) := by
      congr 1
      dsimp [p]
      rw [← mul_assoc, variable_expected_degree r Delta hr]

/-- A convenient second-order upper bound for the exponential function. -/
theorem exp_sub_one_le_add_sq {t : Real} (ht : |t| ≤ 1) :
    Real.exp t - 1 ≤ t + t ^ 2 := by
  have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le ht)).2
  linarith

/-- Chernoff upper tail for one check degree, before optimizing `t`. -/
theorem check_degree_upper_chernoff
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) (ε t : Real) (ht : 0 ≤ t) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | ε ≤ (checkDegree sample a : Real)} ≤
      Real.exp (-t * ε + (Delta : Real) * (Real.exp t - 1)) := by
  calc
    _ ≤ Real.exp (-t * ε) *
        ProbabilityTheory.mgf
          (fun sample => (checkDegree sample a : Real))
          (distribution r Delta hDelta).toMeasure t := by
      exact ProbabilityTheory.measure_ge_le_exp_mul_mgf ε ht Integrable.of_finite
    _ ≤ Real.exp (-t * ε) *
        Real.exp ((Delta : Real) * (Real.exp t - 1)) := by
      gcongr
      exact mgf_checkDegree_le_poisson r Delta hr hDelta a t
    _ = _ := by rw [← Real.exp_add]

/-- Chernoff lower tail for one check degree, before optimizing `t`. -/
theorem check_degree_lower_chernoff
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) (ε t : Real) (ht : t ≤ 0) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | (checkDegree sample a : Real) ≤ ε} ≤
      Real.exp (-t * ε + (Delta : Real) * (Real.exp t - 1)) := by
  calc
    _ ≤ Real.exp (-t * ε) *
        ProbabilityTheory.mgf
          (fun sample => (checkDegree sample a : Real))
          (distribution r Delta hDelta).toMeasure t := by
      exact ProbabilityTheory.measure_le_le_exp_mul_mgf ε ht Integrable.of_finite
    _ ≤ Real.exp (-t * ε) *
        Real.exp ((Delta : Real) * (Real.exp t - 1)) := by
      gcongr
      exact mgf_checkDegree_le_poisson r Delta hr hDelta a t
    _ = _ := by rw [← Real.exp_add]

/-- Chernoff upper tail for one variable degree, before optimizing `t`. -/
theorem variable_degree_upper_chernoff
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) (ε t : Real) (ht : 0 ≤ t) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | ε ≤ (variableDegree sample b : Real)} ≤
      Real.exp
        (-t * ε + (3 * (Delta : Real) / 4) * (Real.exp t - 1)) := by
  calc
    _ ≤ Real.exp (-t * ε) *
        ProbabilityTheory.mgf
          (fun sample => (variableDegree sample b : Real))
          (distribution r Delta hDelta).toMeasure t := by
      exact ProbabilityTheory.measure_ge_le_exp_mul_mgf ε ht Integrable.of_finite
    _ ≤ Real.exp (-t * ε) *
        Real.exp ((3 * (Delta : Real) / 4) * (Real.exp t - 1)) := by
      gcongr
      exact mgf_variableDegree_le_poisson r Delta hr hDelta b t
    _ = _ := by rw [← Real.exp_add]

/-- Chernoff lower tail for one variable degree, before optimizing `t`. -/
theorem variable_degree_lower_chernoff
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) (ε t : Real) (ht : t ≤ 0) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | (variableDegree sample b : Real) ≤ ε} ≤
      Real.exp
        (-t * ε + (3 * (Delta : Real) / 4) * (Real.exp t - 1)) := by
  calc
    _ ≤ Real.exp (-t * ε) *
        ProbabilityTheory.mgf
          (fun sample => (variableDegree sample b : Real))
          (distribution r Delta hDelta).toMeasure t := by
      exact ProbabilityTheory.measure_le_le_exp_mul_mgf ε ht Integrable.of_finite
    _ ≤ Real.exp (-t * ε) *
        Real.exp ((3 * (Delta : Real) / 4) * (Real.exp t - 1)) := by
      gcongr
      exact mgf_variableDegree_le_poisson r Delta hr hDelta b t
    _ = _ := by rw [← Real.exp_add]

/-- The HHO20 upper check-degree window has exponentially small failure. -/
theorem check_degree_upper_window
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | (101 * (Delta : Real) / 100) ≤ checkDegree sample a} ≤
      Real.exp (-(Delta : Real) / 40000) := by
  calc
    _ ≤ Real.exp
        (-(1 / 200 : Real) * (101 * (Delta : Real) / 100) +
          (Delta : Real) * (Real.exp (1 / 200 : Real) - 1)) :=
      check_degree_upper_chernoff r Delta hr hDelta a _ _ (by norm_num)
    _ ≤ Real.exp (-(Delta : Real) / 40000) := by
      apply Real.exp_le_exp_of_le
      have he := exp_sub_one_le_add_sq (t := (1 / 200 : Real)) (by norm_num)
      calc
        _ ≤ -(1 / 200 : Real) * (101 * (Delta : Real) / 100) +
            (Delta : Real) * ((1 / 200 : Real) + (1 / 200 : Real) ^ 2) := by
          gcongr
        _ = _ := by ring

/-- The HHO20 lower check-degree window has exponentially small failure. -/
theorem check_degree_lower_window
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | (checkDegree sample a : Real) ≤ 99 * Delta / 100} ≤
      Real.exp (-(Delta : Real) / 40000) := by
  calc
    _ ≤ Real.exp
        (-(-1 / 200 : Real) * (99 * (Delta : Real) / 100) +
          (Delta : Real) * (Real.exp (-1 / 200 : Real) - 1)) :=
      check_degree_lower_chernoff r Delta hr hDelta a _ _ (by norm_num)
    _ ≤ Real.exp (-(Delta : Real) / 40000) := by
      apply Real.exp_le_exp_of_le
      have he := exp_sub_one_le_add_sq (t := (-1 / 200 : Real)) (by norm_num)
      calc
        _ ≤ -(-1 / 200 : Real) * (99 * (Delta : Real) / 100) +
            (Delta : Real) * ((-1 / 200 : Real) + (-1 / 200 : Real) ^ 2) := by
          gcongr
        _ = _ := by ring

/-- The HHO20 upper variable-degree window has exponentially small failure. -/
theorem variable_degree_upper_window
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | (76 * (Delta : Real) / 100) ≤ variableDegree sample b} ≤
      Real.exp (-(Delta : Real) / 32000) := by
  calc
    _ ≤ Real.exp
        (-(1 / 200 : Real) * (76 * (Delta : Real) / 100) +
          (3 * (Delta : Real) / 4) * (Real.exp (1 / 200 : Real) - 1)) :=
      variable_degree_upper_chernoff r Delta hr hDelta b _ _ (by norm_num)
    _ ≤ Real.exp (-(Delta : Real) / 32000) := by
      apply Real.exp_le_exp_of_le
      have he := exp_sub_one_le_add_sq (t := (1 / 200 : Real)) (by norm_num)
      calc
        _ ≤ -(1 / 200 : Real) * (76 * (Delta : Real) / 100) +
            (3 * (Delta : Real) / 4) *
              ((1 / 200 : Real) + (1 / 200 : Real) ^ 2) := by
          gcongr
        _ = _ := by ring

/-- The HHO20 lower variable-degree window has exponentially small failure. -/
theorem variable_degree_lower_window
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | (variableDegree sample b : Real) ≤ 74 * Delta / 100} ≤
      Real.exp (-(Delta : Real) / 32000) := by
  calc
    _ ≤ Real.exp
        (-(-1 / 200 : Real) * (74 * (Delta : Real) / 100) +
          (3 * (Delta : Real) / 4) * (Real.exp (-1 / 200 : Real) - 1)) :=
      variable_degree_lower_chernoff r Delta hr hDelta b _ _ (by norm_num)
    _ ≤ Real.exp (-(Delta : Real) / 32000) := by
      apply Real.exp_le_exp_of_le
      have he := exp_sub_one_le_add_sq (t := (-1 / 200 : Real)) (by norm_num)
      calc
        _ ≤ -(-1 / 200 : Real) * (74 * (Delta : Real) / 100) +
            (3 * (Delta : Real) / 4) *
              ((-1 / 200 : Real) + (-1 / 200 : Real) ^ 2) := by
          gcongr
        _ = _ := by ring

/--
Hoeffding upper tail for one check degree, expressed as the exact sum of
centered incidence indicators.
-/
theorem check_centered_upper_tail
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) (ε : Real) (hε : 0 ≤ ε) :
    (distribution r Delta hDelta).toMeasure.real
        {sample |
          ε ≤ ∑ b : Fin (4 * r),
            (incidenceReal (a, b) sample -
              (incidenceProbability (4 * r) Delta).toReal)} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ∑ _b : Fin (4 * r), ((1 / 4 : NNReal) : Real))) := by
  have h_indep :=
    (distribution_centeredIncidence_iIndepFun r Delta hDelta).precomp
      (g := fun b : Fin (4 * r) => (a, b))
      (by
        intro b₁ b₂ h
        exact congrArg Prod.snd h)
  simpa using
    (ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (μ := (distribution r Delta hDelta).toMeasure)
      (X := fun b sample =>
        incidenceReal (a, b) sample -
          (incidenceProbability (4 * r) Delta).toReal)
      (c := fun _ => (1 / 4 : NNReal))
      (s := Finset.univ)
      h_indep
      (fun b _hb => incidenceReal_hasSubgaussianMGF r Delta hDelta (a, b))
      hε)

/--
Hoeffding lower tail for one check degree.  Negation preserves both
independence and the sub-Gaussian parameter.
-/
theorem check_centered_lower_tail
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) (ε : Real) (hε : 0 ≤ ε) :
    (distribution r Delta hDelta).toMeasure.real
        {sample |
          ε ≤ ∑ b : Fin (4 * r),
            -(incidenceReal (a, b) sample -
              (incidenceProbability (4 * r) Delta).toReal)} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ∑ _b : Fin (4 * r), ((1 / 4 : NNReal) : Real))) := by
  have h_indep :=
    ((distribution_centeredIncidence_iIndepFun r Delta hDelta).precomp
      (g := fun b : Fin (4 * r) => (a, b))
      (by
        intro b₁ b₂ h
        exact congrArg Prod.snd h)).comp
      (fun _ x => -x)
      (fun _ => by fun_prop)
  simpa using
    (ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (μ := (distribution r Delta hDelta).toMeasure)
      (X := fun b sample =>
        -(incidenceReal (a, b) sample -
          (incidenceProbability (4 * r) Delta).toReal))
      (c := fun _ => (1 / 4 : NNReal))
      (s := Finset.univ)
      h_indep
      (fun b _hb =>
        (incidenceReal_hasSubgaussianMGF r Delta hDelta (a, b)).neg)
      hε)

/-- Hoeffding upper tail for one variable degree. -/
theorem variable_centered_upper_tail
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) (ε : Real) (hε : 0 ≤ ε) :
    (distribution r Delta hDelta).toMeasure.real
        {sample |
          ε ≤ ∑ a : Fin (3 * r),
            (incidenceReal (a, b) sample -
              (incidenceProbability (4 * r) Delta).toReal)} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ∑ _a : Fin (3 * r), ((1 / 4 : NNReal) : Real))) := by
  have h_indep :=
    (distribution_centeredIncidence_iIndepFun r Delta hDelta).precomp
      (g := fun a : Fin (3 * r) => (a, b))
      (by
        intro a₁ a₂ h
        exact congrArg Prod.fst h)
  simpa using
    (ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (μ := (distribution r Delta hDelta).toMeasure)
      (X := fun a sample =>
        incidenceReal (a, b) sample -
          (incidenceProbability (4 * r) Delta).toReal)
      (c := fun _ => (1 / 4 : NNReal))
      (s := Finset.univ)
      h_indep
      (fun a _ha => incidenceReal_hasSubgaussianMGF r Delta hDelta (a, b))
      hε)

/-- Hoeffding lower tail for one variable degree. -/
theorem variable_centered_lower_tail
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) (ε : Real) (hε : 0 ≤ ε) :
    (distribution r Delta hDelta).toMeasure.real
        {sample |
          ε ≤ ∑ a : Fin (3 * r),
            -(incidenceReal (a, b) sample -
              (incidenceProbability (4 * r) Delta).toReal)} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ∑ _a : Fin (3 * r), ((1 / 4 : NNReal) : Real))) := by
  have h_indep :=
    ((distribution_centeredIncidence_iIndepFun r Delta hDelta).precomp
      (g := fun a : Fin (3 * r) => (a, b))
      (by
        intro a₁ a₂ h
        exact congrArg Prod.fst h)).comp
      (fun _ x => -x)
      (fun _ => by fun_prop)
  simpa using
    (ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (μ := (distribution r Delta hDelta).toMeasure)
      (X := fun a sample =>
        -(incidenceReal (a, b) sample -
          (incidenceProbability (4 * r) Delta).toReal))
      (c := fun _ => (1 / 4 : NNReal))
      (s := Finset.univ)
      h_indep
      (fun a _ha =>
        (incidenceReal_hasSubgaussianMGF r Delta hDelta (a, b)).neg)
      hε)

/-- Upper-tail form stated directly for a check degree. -/
theorem check_degree_upper_tail
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) (ε : Real) (hε : 0 ≤ ε) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | ε ≤ (checkDegree sample a : Real) - Delta} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ∑ _b : Fin (4 * r), ((1 / 4 : NNReal) : Real))) := by
  simpa only [check_centered_sum_eq r Delta hr] using
    check_centered_upper_tail r Delta hDelta a ε hε

/-- Lower-tail form stated directly for a check degree. -/
theorem check_degree_lower_tail
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) (ε : Real) (hε : 0 ≤ ε) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | ε ≤ (Delta : Real) - checkDegree sample a} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ∑ _b : Fin (4 * r), ((1 / 4 : NNReal) : Real))) := by
  have hset :
      {sample : Sample r |
        ε ≤ ∑ b : Fin (4 * r),
          -(incidenceReal (a, b) sample -
            (incidenceProbability (4 * r) Delta).toReal)} =
      {sample : Sample r |
        ε ≤ (Delta : Real) - checkDegree sample a} := by
    ext sample
    change
      (ε ≤ ∑ b ∈ (Finset.univ : Finset (Fin (4 * r))),
        -(incidenceReal (a, b) sample -
          (incidenceProbability (4 * r) Delta).toReal)) ↔
      ε ≤ (Delta : Real) - checkDegree sample a
    rw [Finset.sum_neg_distrib, check_centered_sum_eq r Delta hr, neg_sub]
  rw [← hset]
  exact check_centered_lower_tail r Delta hDelta a ε hε

/-- Upper-tail form stated directly for a variable degree. -/
theorem variable_degree_upper_tail
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) (ε : Real) (hε : 0 ≤ ε) :
    (distribution r Delta hDelta).toMeasure.real
        {sample |
          ε ≤ (variableDegree sample b : Real) - 3 * (Delta : Real) / 4} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ∑ _a : Fin (3 * r), ((1 / 4 : NNReal) : Real))) := by
  simpa only [variable_centered_sum_eq r Delta hr] using
    variable_centered_upper_tail r Delta hDelta b ε hε

/-- Lower-tail form stated directly for a variable degree. -/
theorem variable_degree_lower_tail
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) (ε : Real) (hε : 0 ≤ ε) :
    (distribution r Delta hDelta).toMeasure.real
        {sample |
          ε ≤ 3 * (Delta : Real) / 4 - variableDegree sample b} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ∑ _a : Fin (3 * r), ((1 / 4 : NNReal) : Real))) := by
  have hset :
      {sample : Sample r |
        ε ≤ ∑ a : Fin (3 * r),
          -(incidenceReal (a, b) sample -
            (incidenceProbability (4 * r) Delta).toReal)} =
      {sample : Sample r |
        ε ≤ 3 * (Delta : Real) / 4 - variableDegree sample b} := by
    ext sample
    change
      (ε ≤ ∑ a ∈ (Finset.univ : Finset (Fin (3 * r))),
        -(incidenceReal (a, b) sample -
          (incidenceProbability (4 * r) Delta).toReal)) ↔
      ε ≤ 3 * (Delta : Real) / 4 - variableDegree sample b
    rw [Finset.sum_neg_distrib, variable_centered_sum_eq r Delta hr, neg_sub]
  rw [← hset]
  exact variable_centered_lower_tail r Delta hDelta b ε hε

/--
The exact integer-scaled degree windows from HHO20 Proposition
`prop:bounded-degree`.
-/
def HasDegreeWindows {r Delta : Nat} (sample : Sample r) : Prop :=
  (∀ a, 99 * Delta ≤ 100 * checkDegree sample a ∧
      100 * checkDegree sample a ≤ 101 * Delta) ∧
    ∀ b, 74 * Delta ≤ 100 * variableDegree sample b ∧
      100 * variableDegree sample b ≤ 76 * Delta

/--
The four kinds of pointwise degree-window failures: lower/upper failures for
checks and lower/upper failures for variables.
-/
abbrev DegreeFailureIndex (r : Nat) :=
  (Fin (3 * r) × Bool) ⊕ (Fin (4 * r) × Bool)

/-- The atomic bad event selected by a degree-failure index. -/
def degreeFailureEvent
    (r Delta : Nat) : DegreeFailureIndex r → Set (Sample r)
  | Sum.inl (a, false) =>
      {sample | ¬99 * Delta ≤ 100 * checkDegree sample a}
  | Sum.inl (a, true) =>
      {sample | ¬100 * checkDegree sample a ≤ 101 * Delta}
  | Sum.inr (b, false) =>
      {sample | ¬74 * Delta ≤ 100 * variableDegree sample b}
  | Sum.inr (b, true) =>
      {sample | ¬100 * variableDegree sample b ≤ 76 * Delta}

/--
Every atomic degree-window failure is controlled by the common (weaker)
check-tail exponent.  Variable tails are stronger and are monotonically
relaxed here so one finite-union bound can be used.
-/
theorem degreeFailureEvent_measure_le
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (i : DegreeFailureIndex r) :
    (distribution r Delta hDelta).toMeasure.real
        (degreeFailureEvent r Delta i) ≤
      Real.exp (-(Delta : Real) / 40000) := by
  rcases i with ⟨a, upper⟩ | ⟨b, upper⟩
  · cases upper
    · calc
        _ ≤ (distribution r Delta hDelta).toMeasure.real
            {sample |
              (checkDegree sample a : Real) ≤ 99 * Delta / 100} := by
          refine measureReal_mono ?_ (by finiteness)
          intro sample hs
          simp only [degreeFailureEvent, Set.mem_setOf_eq] at hs ⊢
          have hlt : 100 * checkDegree sample a < 99 * Delta :=
            Nat.lt_of_not_ge hs
          have hltR :
              (100 : Real) * checkDegree sample a < 99 * Delta := by
            exact_mod_cast hlt
          linarith
        _ ≤ _ := check_degree_lower_window r Delta hr hDelta a
    · calc
        _ ≤ (distribution r Delta hDelta).toMeasure.real
            {sample |
              (101 * (Delta : Real) / 100) ≤ checkDegree sample a} := by
          refine measureReal_mono ?_ (by finiteness)
          intro sample hs
          simp only [degreeFailureEvent, Set.mem_setOf_eq] at hs ⊢
          have hlt : 101 * Delta < 100 * checkDegree sample a :=
            Nat.lt_of_not_ge hs
          have hltR :
              (101 : Real) * Delta < 100 * checkDegree sample a := by
            exact_mod_cast hlt
          linarith
        _ ≤ _ := check_degree_upper_window r Delta hr hDelta a
  · cases upper
    · calc
        _ ≤ (distribution r Delta hDelta).toMeasure.real
            {sample |
              (variableDegree sample b : Real) ≤ 74 * Delta / 100} := by
          refine measureReal_mono ?_ (by finiteness)
          intro sample hs
          simp only [degreeFailureEvent, Set.mem_setOf_eq] at hs ⊢
          have hlt : 100 * variableDegree sample b < 74 * Delta :=
            Nat.lt_of_not_ge hs
          have hltR :
              (100 : Real) * variableDegree sample b < 74 * Delta := by
            exact_mod_cast hlt
          linarith
        _ ≤ Real.exp (-(Delta : Real) / 32000) :=
          variable_degree_lower_window r Delta hr hDelta b
        _ ≤ _ := by
          apply Real.exp_le_exp_of_le
          have hDelta_nonneg : (0 : Real) ≤ Delta := by positivity
          nlinarith
    · calc
        _ ≤ (distribution r Delta hDelta).toMeasure.real
            {sample |
              (76 * (Delta : Real) / 100) ≤ variableDegree sample b} := by
          refine measureReal_mono ?_ (by finiteness)
          intro sample hs
          simp only [degreeFailureEvent, Set.mem_setOf_eq] at hs ⊢
          have hlt : 76 * Delta < 100 * variableDegree sample b :=
            Nat.lt_of_not_ge hs
          have hltR :
              (76 : Real) * Delta < 100 * variableDegree sample b := by
            exact_mod_cast hlt
          linarith
        _ ≤ Real.exp (-(Delta : Real) / 32000) :=
          variable_degree_upper_window r Delta hr hDelta b
        _ ≤ _ := by
          apply Real.exp_le_exp_of_le
          have hDelta_nonneg : (0 : Real) ≤ Delta := by positivity
          nlinarith

/-- Failure of the global degree windows is covered by the atomic bad events. -/
theorem degreeWindows_failure_subset
    (r Delta : Nat) :
    {sample : Sample r | ¬HasDegreeWindows (Delta := Delta) sample} ⊆
      ⋃ i : DegreeFailureIndex r, degreeFailureEvent r Delta i := by
  intro sample hs
  simp only [Set.mem_setOf_eq, HasDegreeWindows] at hs
  rw [not_and_or] at hs
  rcases hs with hs | hs
  · simp only [not_forall] at hs
    rcases hs with ⟨a, ha⟩
    rw [not_and_or] at ha
    rcases ha with ha | ha
    · exact Set.mem_iUnion.2
        ⟨Sum.inl (a, false), by simpa [degreeFailureEvent] using ha⟩
    · exact Set.mem_iUnion.2
        ⟨Sum.inl (a, true), by simpa [degreeFailureEvent] using ha⟩
  · simp only [not_forall] at hs
    rcases hs with ⟨b, hb⟩
    rw [not_and_or] at hb
    rcases hb with hb | hb
    · exact Set.mem_iUnion.2
        ⟨Sum.inr (b, false), by simpa [degreeFailureEvent] using hb⟩
    · exact Set.mem_iUnion.2
        ⟨Sum.inr (b, true), by simpa [degreeFailureEvent] using hb⟩

/--
Union bound for the full HHO20 degree-window event.  There are exactly
`2(3r) + 2(4r) = 14r` atomic bad events.
-/
theorem degreeWindows_failure_measure_le
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | ¬HasDegreeWindows (Delta := Delta) sample} ≤
      (14 * r : Real) * Real.exp (-(Delta : Real) / 40000) := by
  calc
    _ ≤ (distribution r Delta hDelta).toMeasure.real
        (⋃ i : DegreeFailureIndex r, degreeFailureEvent r Delta i) :=
      measureReal_mono (degreeWindows_failure_subset r Delta)
    _ ≤ ∑ _i : DegreeFailureIndex r,
        Real.exp (-(Delta : Real) / 40000) := by
      refine (measureReal_iUnion_fintype_le
        (μ := (distribution r Delta hDelta).toMeasure)
        (fun i : DegreeFailureIndex r => degreeFailureEvent r Delta i)).trans ?_
      exact Finset.sum_le_sum fun i _hi =>
        degreeFailureEvent_measure_le r Delta hr hDelta i
    _ = _ := by
      simp [DegreeFailureIndex]
      ring

/-- The classical binary code checked by a sampled base boundary. -/
noncomputable def code {r : Nat} (sample : Sample r) :
    LinearCode (ZMod 2) (Fin (4 * r)) :=
  parityCheckKernelCode (Matrix.toLin' (boundary sample))

/-- Full row rank, equivalently surjectivity onto the base check space. -/
def HasFullRowRank {r : Nat} (sample : Sample r) : Prop :=
  Function.Surjective (Matrix.toLin' (boundary sample))

/-- A binary linear combination of the sampled parity-check rows. -/
def rowCombination {r : Nat}
    (sample : Sample r) (coeff : Fin (3 * r) → ZMod 2) :
    Fin (4 * r) → ZMod 2 :=
  Matrix.vecMul coeff (boundary sample)

/-- Independent sampled rows force surjectivity of the parity-check map. -/
theorem hasFullRowRank_of_rows_linearIndependent
    {r : Nat} {sample : Sample r}
    (hrows : LinearIndependent (ZMod 2) (boundary sample).row) :
    HasFullRowRank sample := by
  rw [HasFullRowRank, ← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [Matrix.range_toLin', ← Matrix.rank_eq_finrank_span_cols,
    hrows.rank_matrix]
  simp

/-- Injectivity of row combinations is equivalent to the needed row independence. -/
theorem hasFullRowRank_of_rowCombination_injective
    {r : Nat} {sample : Sample r}
    (hinj : Function.Injective fun coeff : Fin (3 * r) → ZMod 2 =>
      rowCombination sample coeff) :
    HasFullRowRank sample := by
  apply hasFullRowRank_of_rows_linearIndependent
  rw [← Matrix.vecMul_injective_iff]
  simpa only [rowCombination] using hinj

/--
Failure of full row rank produces a concrete nonzero binary row combination
whose sampled sum is zero.
-/
theorem exists_nonzero_rowCombination_eq_zero_of_not_fullRowRank
    {r : Nat} {sample : Sample r} (h : ¬HasFullRowRank sample) :
    ∃ coeff : Fin (3 * r) → ZMod 2,
      coeff ≠ 0 ∧ rowCombination sample coeff = 0 := by
  have hnotinj :
      ¬Function.Injective (fun coeff : Fin (3 * r) → ZMod 2 =>
        rowCombination sample coeff) := by
    intro hinj
    exact h (hasFullRowRank_of_rowCombination_injective hinj)
  rw [Function.not_injective_iff] at hnotinj
  rcases hnotinj with ⟨x, y, heq, hxy⟩
  refine ⟨x - y, sub_ne_zero.mpr hxy, ?_⟩
  change Matrix.vecMul (x - y) (boundary sample) = 0
  change (boundary sample).vecMulLinear (x - y) = 0
  rw [map_sub]
  change Matrix.vecMul x (boundary sample) -
    Matrix.vecMul y (boundary sample) = 0
  change rowCombination sample x - rowCombination sample y = 0
  rw [heq, sub_self]

/-- The source's `d_B ≥ 0.2 n_B` classical-distance event. -/
def HasLinearDistance {r : Nat} (sample : Sample r) : Prop :=
  ∀ x : Word (ZMod 2) (Fin (4 * r)),
    x ∈ (code sample).carrier →
    x ≠ 0 →
    5 * HammingWeight x ≥ 4 * r

/-- Probability mass of a decidable event in a finite sample space. -/
noncomputable def eventMass
    {Ω : Type u} [Fintype Ω]
    (p : PMF Ω) (event : Ω → Prop) [DecidablePred event] : ENNReal :=
  ∑ ω with event ω, p ω

/-- `eventMass` is the PMF measure of the represented finite event. -/
theorem eventMass_eq_toMeasure
    {Ω : Type u} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω]
    (p : PMF Ω) (event : Ω → Prop) [DecidablePred event] :
    eventMass p event = p.toMeasure {ω | event ω} := by
  classical
  let s : Finset Ω := Finset.univ.filter event
  have hset : {ω | event ω} = (s : Set Ω) := by
    ext ω
    simp [s]
  rw [eventMass, hset, PMF.toMeasure_apply_finset]

/-- Failure probability of a decidable event in a finite sample space. -/
noncomputable def failureMass
    {Ω : Type u} [Fintype Ω]
    (p : PMF Ω) (event : Ω → Prop) [DecidablePred event] : ENNReal :=
  eventMass p (fun ω => ¬ event ω)

/-- `failureMass` is the PMF measure of the complementary event. -/
theorem failureMass_eq_toMeasure
    {Ω : Type u} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω]
    (p : PMF Ω) (event : Ω → Prop) [DecidablePred event] :
    failureMass p event = p.toMeasure {ω | ¬event ω} := by
  classical
  let s : Finset Ω := Finset.univ.filter fun ω => ¬event ω
  have hset : {ω | ¬event ω} = (s : Set Ω) := by
    ext ω
    simp [s]
  rw [failureMass, eventMass, hset, PMF.toMeasure_apply_finset]

/-- ENNReal form of the global degree-window failure bound. -/
theorem degreeWindows_failureMass_le
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r) :
    @failureMass
        (Sample r)
        inferInstance
        (distribution r Delta hDelta)
        (fun sample => HasDegreeWindows (Delta := Delta) sample)
        (Classical.decPred _) ≤
      ENNReal.ofReal
        ((14 * r : Real) * Real.exp (-(Delta : Real) / 40000)) := by
  classical
  rw [failureMass_eq_toMeasure]
  rw [← ofReal_measureReal (μ := (distribution r Delta hDelta).toMeasure)
    (s := {sample | ¬HasDegreeWindows (Delta := Delta) sample})]
  exact ENNReal.ofReal_le_ofReal
    (degreeWindows_failure_measure_le r Delta hr hDelta)

/-- An event and its complement have total probability mass one. -/
theorem eventMass_add_failureMass
    {Ω : Type u} [Fintype Ω]
    (p : PMF Ω) (event : Ω → Prop) [DecidablePred event] :
    eventMass p event + failureMass p event = 1 := by
  classical
  simp only [eventMass, failureMass]
  rw [Finset.sum_filter_add_sum_filter_not]
  simpa only [tsum_fintype] using (PMF.tsum_coe p)

/--
A family of events has polynomially small failure probability when one finite
constant controls the tail by `r⁻ᵖᵒʷᵉʳ`.
-/
def HasPolynomialFailureBound
    {Ω : Nat → Type u} [∀ r, Fintype (Ω r)]
    (p : ∀ r, PMF (Ω r))
    (event : ∀ r, Ω r → Prop)
    [∀ r, DecidablePred (event r)]
    (power : Nat) : Prop :=
  ∃ C : ENNReal, C ≠ ⊤ ∧
    ∀ᶠ r in Filter.atTop,
      failureMass (p r) (event r) ≤ C / (r : ENNReal) ^ power

/-- The conjunction of the three random-base conclusions used by HHO20. -/
def IsGood {r Delta : Nat} (sample : Sample r) : Prop :=
  HasDegreeWindows (Delta := Delta) sample ∧
    HasFullRowRank sample ∧
    HasLinearDistance sample

/--
The exact `O(r⁻¹⁰⁰)` target for the construction-owned random-base family.
-/
noncomputable def HasHighProbabilityGoodBase
    (Delta : Nat → Nat)
    (hDelta : ∀ r, Delta r ≤ 4 * r) : Prop :=
  by
    classical
    exact HasPolynomialFailureBound
      (fun r => distribution r (Delta r) (hDelta r))
      (fun r sample => IsGood (Delta := Delta r) sample)
      100

end QEC.Coding.FiberBundle.RandomBase
