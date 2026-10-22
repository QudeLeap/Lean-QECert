import QEC.Coding.FiberBundle.RandomBase
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Full-row-rank closure for the HHO20 random base

This module regroups the construction-owned incidence sampler by variable
columns.  The regrouping is an equivalence, and its probability mass is proved
to be the corresponding iterated independent product.  It is the starting
point for the exact parity and union-bound proof of HHO20 Proposition
`prop:lin-indep`.
-/

namespace QEC.Coding.FiberBundle.RandomBase

open scoped BigOperators
open MeasureTheory

universe u

/-- All incidences in one variable column of the Tanner matrix. -/
abbrev ColumnSample (r : Nat) := Fin (3 * r) → Bool

/-- The incidence sample space regrouped as variable columns. -/
abbrev GroupedSample (r : Nat) := Fin (4 * r) → ColumnSample r

/-- Regroup `(check, variable)` incidences into `variable ↦ check ↦ bit`. -/
def sampleEquivGrouped (r : Nat) : Sample r ≃ GroupedSample r where
  toFun sample b a := sample (a, b)
  invFun grouped edge := grouped edge.2 edge.1
  left_inv sample := by
    funext edge
    rfl
  right_inv grouped := by
    funext b a
    rfl

/-- One independently sampled Tanner-matrix column. -/
noncomputable def columnDistribution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    PMF (ColumnSample r) :=
  independentProduct fun _ =>
    PMF.bernoulli
      (incidenceProbability (4 * r) Delta)
      (incidenceProbability_le_one hDelta)

/-- The same HHO20 sampler represented as an independent product of columns. -/
noncomputable def groupedDistribution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    PMF (GroupedSample r) :=
  independentProduct fun _ => columnDistribution r Delta hDelta

@[simp]
theorem columnDistribution_apply
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (column : ColumnSample r) :
    columnDistribution r Delta hDelta column =
      ∏ a : Fin (3 * r),
        cond (column a)
          (incidenceProbability (4 * r) Delta)
          (1 - incidenceProbability (4 * r) Delta) := by
  simp [columnDistribution, independentProduct_apply, PMF.bernoulli_apply]

@[simp]
theorem groupedDistribution_apply
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (grouped : GroupedSample r) :
    groupedDistribution r Delta hDelta grouped =
      ∏ b : Fin (4 * r), ∏ a : Fin (3 * r),
        cond (grouped b a)
          (incidenceProbability (4 * r) Delta)
          (1 - incidenceProbability (4 * r) Delta) := by
  simp [groupedDistribution, independentProduct_apply]

/-- Incidences within one sampled column are mutually independent. -/
theorem columnDistribution_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun a (column : ColumnSample r) => column a)
      (columnDistribution r Delta hDelta).toMeasure := by
  exact independentProduct_iIndepFun _

/-- Every coordinate of a sampled column has the construction's Bernoulli law. -/
theorem columnDistribution_coordinate_hasLaw
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) :
    ProbabilityTheory.HasLaw
      (fun column : ColumnSample r => column a)
      (PMF.bernoulli
        (incidenceProbability (4 * r) Delta)
        (incidenceProbability_le_one hDelta)).toMeasure
      (columnDistribution r Delta hDelta).toMeasure := by
  simpa only [columnDistribution] using
    (independentProduct_coordinate_hasLaw
      (fun _ : Fin (3 * r) =>
        PMF.bernoulli
          (incidenceProbability (4 * r) Delta)
          (incidenceProbability_le_one hDelta))
      a)

/--
Regrouping changes no probability mass.  This is an exact equality of PMFs,
not an independence assumption about the sampled matrix.
-/
theorem distribution_apply_eq_grouped
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (sample : Sample r) :
    distribution r Delta hDelta sample =
      groupedDistribution r Delta hDelta (sampleEquivGrouped r sample) := by
  rw [distribution_apply, groupedDistribution_apply]
  norm_cast
  rw [← Finset.prod_product' Finset.univ Finset.univ]
  exact Fintype.prod_equiv
    (Equiv.prodComm (Fin (3 * r)) (Fin (4 * r)))
    _ _ (fun _ => rfl)

/-- Rewrite a filtered finite sum as a total sum with an indicator. -/
theorem sum_filter_eq_sum_ite
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (event : α → Prop) [DecidablePred event]
    (f : α → M) :
    (∑ x ∈ s.filter event, f x) =
      ∑ x ∈ s, if event x then f x else 0 := by
  rw [Finset.sum_ite]
  simp

/--
An all-coordinate event under `independentProduct` factors into the product
of its coordinate event masses.
-/
theorem eventMass_independentProduct_forall
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type u} [∀ i, Fintype (κ i)]
    (p : ∀ i, PMF (κ i))
    (event : ∀ i, κ i → Prop)
    [∀ i, DecidablePred (event i)] :
    eventMass
        (independentProduct p)
        (fun x => ∀ i, event i (x i)) =
      ∏ i, eventMass (p i) (event i) := by
  classical
  simp only [eventMass, independentProduct_apply]
  rw [sum_filter_eq_sum_ite]
  simp_rw [sum_filter_eq_sum_ite]
  calc
    _ = ∑ x : (∀ i, κ i),
        ∏ i, if event i (x i) then p i (x i) else 0 := by
      apply Fintype.sum_congr
      intro x
      by_cases hx : ∀ i, event i (x i)
      · simp [hx]
      · simp only [not_forall] at hx
        rcases hx with ⟨i, hi⟩
        rw [if_neg (by
          intro hall
          exact hi (hall i))]
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hi]
    _ = _ :=
      (Fintype.prod_sum
        (f := fun i y => if event i y then p i y else 0)).symm

/-- Transport a finite event mass across an equivalence of sample spaces. -/
theorem eventMass_equiv
    {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (p : PMF Ω) (q : PMF Ω')
    (event : Ω → Prop) (event' : Ω' → Prop)
    [DecidablePred event] [DecidablePred event']
    (hmass : ∀ x, p x = q (e x))
    (hevent : ∀ x, event x ↔ event' (e x)) :
    eventMass p event = eventMass q event' := by
  classical
  simp only [eventMass]
  rw [sum_filter_eq_sum_ite, sum_filter_eq_sum_ite]
  calc
    _ = ∑ x, if event' (e x) then q (e x) else 0 := by
      apply Fintype.sum_congr
      intro x
      by_cases hx : event x
      · simp [hx, (hevent x).mp hx, hmass x]
      · have hx' : ¬event' (e x) := fun h' => hx ((hevent x).mpr h')
        simp [hx, hx']
    _ = _ := by
      simpa only [] using
        (e.sum_comp (fun y => if event' y then q y else 0))

/-- The finite event mass is independent of the chosen decision procedure. -/
theorem eventMass_decidable_irrel
    {Ω : Type*} [Fintype Ω]
    (p : PMF Ω) (event : Ω → Prop)
    (d₁ d₂ : DecidablePred event) :
    @eventMass Ω inferInstance p event d₁ =
      @eventMass Ω inferInstance p event d₂ := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  rw [hd]

/--
A finite cover of a failure event gives the corresponding union bound on
probability mass.
-/
theorem failureMass_le_sum_eventMass
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (event : Ω → Prop) [DecidablePred event]
    (bad : ι → Ω → Prop) [∀ i, DecidablePred (bad i)]
    (hcover : ∀ ω, ¬event ω → ∃ i, bad i ω) :
    failureMass p event ≤ ∑ i, eventMass p (bad i) := by
  rw [failureMass_eq_toMeasure]
  calc
    _ ≤ p.toMeasure (⋃ i, {ω | bad i ω}) := by
      apply measure_mono
      intro ω hω
      rcases hcover ω hω with ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    _ ≤ ∑' i, p.toMeasure {ω | bad i ω} := measure_iUnion_le _
    _ = ∑ i, eventMass p (bad i) := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro i _hi
      exact (eventMass_eq_toMeasure p (bad i)).symm

/-- The unique nonzero element of `ZMod 2` is `1`. -/
theorem zmod2_eq_one_of_ne_zero (x : ZMod 2) (hx : x ≠ 0) : x = 1 := by
  apply ZMod.val_injective 2
  rw [ZMod.val_one]
  have hxval : x.val ≠ 0 := (ZMod.val_eq_zero x).not.mpr hx
  have hxlt : x.val < 2 := x.val_lt
  omega

/-- The checks with nonzero coefficient in a binary row combination. -/
def rowSupport {r : Nat} (coeff : Fin (3 * r) → ZMod 2) :
    Finset (Fin (3 * r)) :=
  Finset.univ.filter fun a => coeff a ≠ 0

theorem rowSupport_nonempty_iff
    {r : Nat} (coeff : Fin (3 * r) → ZMod 2) :
    (rowSupport coeff).Nonempty ↔ coeff ≠ 0 := by
  rw [rowSupport, Finset.filter_nonempty_iff]
  simp only [Finset.mem_univ, true_and]
  exact Function.ne_iff.symm

/-- Sum the sampled rows selected by a check subset. -/
def subsetRowCombination {r : Nat}
    (sample : Sample r) (A : Finset (Fin (3 * r))) :
    Fin (4 * r) → ZMod 2 :=
  fun b => ∑ a ∈ A, boundary sample a b

/-- A binary coefficient vector is exactly the indicator of its support. -/
theorem rowCombination_eq_subsetRowCombination
    {r : Nat} (sample : Sample r)
    (coeff : Fin (3 * r) → ZMod 2) :
    rowCombination sample coeff =
      subsetRowCombination sample (rowSupport coeff) := by
  funext b
  rw [rowCombination, Matrix.vecMul, dotProduct]
  rw [subsetRowCombination, rowSupport, sum_filter_eq_sum_ite]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hcoeff : coeff a = 0
  · simp [hcoeff]
  · rw [zmod2_eq_one_of_ne_zero _ hcoeff]
    simp

/-- One grouped column has even parity on a selected row subset. -/
def ColumnParityZero {r : Nat}
    (A : Finset (Fin (3 * r))) (column : ColumnSample r) : Prop :=
  (∑ a ∈ A, cond (column a) (1 : ZMod 2) 0) = 0

instance instDecidablePredColumnParityZero
    {r : Nat} (A : Finset (Fin (3 * r))) :
    DecidablePred (ColumnParityZero A) := by
  intro column
  unfold ColumnParityZero
  infer_instance

/-- The real additive character of `ZMod 2`. -/
def paritySign (x : ZMod 2) : Real :=
  if x = 0 then 1 else -1

/-- A Bernoulli bit represented by the nontrivial real character of `ZMod 2`. -/
def signedBit (b : Bool) : Real :=
  cond b (-1) 1

theorem paritySign_add (x y : ZMod 2) :
    paritySign (x + y) = paritySign x * paritySign y := by
  by_cases hx : x = 0
  · simp [hx, paritySign]
  rw [zmod2_eq_one_of_ne_zero x hx]
  by_cases hy : y = 0
  · simp [hy, paritySign]
  rw [zmod2_eq_one_of_ne_zero y hy]
  have htwo : (1 + 1 : ZMod 2) = 0 := by decide
  simp [paritySign, htwo]

theorem paritySign_bit (b : Bool) :
    paritySign (cond b (1 : ZMod 2) 0) = signedBit b := by
  cases b <;> simp [paritySign, signedBit]

/-- The character of a parity sum factors into the product of bit characters. -/
theorem paritySign_sum
    {r : Nat} (A : Finset (Fin (3 * r))) (column : ColumnSample r) :
    paritySign (∑ a ∈ A, cond (column a) (1 : ZMod 2) 0) =
      ∏ a ∈ A, signedBit (column a) := by
  induction A using Finset.induction_on with
  | empty => simp [paritySign]
  | @insert a A ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, paritySign_add, ih,
        paritySign_bit]

/-- The expectation of one signed Bernoulli incidence is `1 - 2p`. -/
theorem integral_signedBit
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) :
    ∫ column, signedBit (column a) ∂
        (columnDistribution r Delta hDelta).toMeasure =
      1 - 2 * (incidenceProbability (4 * r) Delta).toReal := by
  calc
    _ = ∫ b, signedBit b ∂
        (PMF.bernoulli
          (incidenceProbability (4 * r) Delta)
          (incidenceProbability_le_one hDelta)).toMeasure := by
      exact (columnDistribution_coordinate_hasLaw r Delta hDelta a).integral_comp
        (f := signedBit)
        (by fun_prop)
    _ = _ := by
      rw [PMF.integral_eq_sum]
      simp [signedBit, PMF.bernoulli_apply]
      rw [NNReal.coe_sub (incidenceProbability_le_one hDelta)]
      norm_num
      ring

/-- The signed-character expectation over a selected row subset factors. -/
theorem integral_signedBit_product
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (A : Finset (Fin (3 * r))) :
    ∫ column, (∏ a ∈ A, signedBit (column a)) ∂
        (columnDistribution r Delta hDelta).toMeasure =
      (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^ A.card := by
  have h_indep : ProbabilityTheory.iIndepFun
      (fun a : A => fun column : ColumnSample r => signedBit (column a))
      (columnDistribution r Delta hDelta).toMeasure :=
    ((columnDistribution_iIndepFun r Delta hDelta).precomp
      (g := fun a : A => a.1)
      Subtype.val_injective).comp
      (fun _ b => signedBit b)
      (fun _ => by fun_prop)
  have hfactor :=
    h_indep.integral_fun_prod_eq_prod_integral
      (fun _ => (measurable_of_finite _).aestronglyMeasurable)
  rw [show (fun column : ColumnSample r =>
      ∏ a ∈ A, signedBit (column a)) =
      (fun column => ∏ a : A, signedBit (column a)) by
    funext column
    exact (Finset.prod_coe_sort A (fun a => signedBit (column a))).symm]
  simpa [integral_signedBit r Delta hDelta] using hfactor

/-- Real indicator of the even-parity event. -/
noncomputable def parityZeroIndicator {r : Nat}
    (A : Finset (Fin (3 * r))) (column : ColumnSample r) : Real :=
  by
    classical
    exact if ColumnParityZero A column then 1 else 0

/-- Fourier character identity for the even-parity indicator. -/
theorem parityZeroIndicator_eq
    {r : Nat} (A : Finset (Fin (3 * r))) (column : ColumnSample r) :
    parityZeroIndicator A column =
      (1 + ∏ a ∈ A, signedBit (column a)) / 2 := by
  classical
  rw [← paritySign_sum A column]
  simp only [parityZeroIndicator, ColumnParityZero]
  by_cases hzero :
      (∑ a ∈ A, cond (column a) (1 : ZMod 2) 0) = 0
  · erw [if_pos hzero]
    simp [paritySign, hzero]
  · erw [if_neg hzero]
    simp [paritySign, hzero]

/-- Exact probability that a selected row subset has even parity in one column. -/
theorem columnParityZero_measureReal
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (A : Finset (Fin (3 * r))) :
    (columnDistribution r Delta hDelta).toMeasure.real
        {column | ColumnParityZero A column} =
      (1 +
        (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^ A.card) / 2 := by
  classical
  let μ := (columnDistribution r Delta hDelta).toMeasure
  calc
    μ.real {column | ColumnParityZero A column} =
        ∫ column, parityZeroIndicator A column ∂μ := by
      rw [← integral_indicator_one (μ := μ) (Set.toFinite _).measurableSet]
      apply integral_congr_ae
      filter_upwards [] with column
      simp [parityZeroIndicator, Set.indicator]
    _ = ∫ column,
        (1 + ∏ a ∈ A, signedBit (column a)) / 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (parityZeroIndicator_eq A)
    _ = _ := by
      rw [integral_div, integral_add]
      · simp [μ, integral_signedBit_product r Delta hDelta A]
      · exact Integrable.of_finite
      · exact Integrable.of_finite

/-- ENNReal event-mass form of the exact one-column parity formula. -/
theorem columnParityZero_eventMass
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (A : Finset (Fin (3 * r))) :
    eventMass
        (columnDistribution r Delta hDelta)
        (ColumnParityZero A) =
      ENNReal.ofReal
        ((1 +
          (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^ A.card) / 2) := by
  classical
  calc
    _ = (columnDistribution r Delta hDelta).toMeasure
        {column | ColumnParityZero A column} :=
      eventMass_eq_toMeasure _ _
    _ = ENNReal.ofReal
        ((columnDistribution r Delta hDelta).toMeasure.real
          {column | ColumnParityZero A column}) := by
      rw [ofReal_measureReal]
    _ = _ := by rw [columnParityZero_measureReal r Delta hDelta A]

/-- Vanishing of a selected row sum is the all-column parity-zero event. -/
theorem subsetRowCombination_eq_zero_iff
    {r : Nat} (sample : Sample r)
    (A : Finset (Fin (3 * r))) :
    subsetRowCombination sample A = 0 ↔
      ∀ b : Fin (4 * r),
        ColumnParityZero A (sampleEquivGrouped r sample b) := by
  constructor
  · intro h b
    have hb := congrFun h b
    change
      (∑ a ∈ A, (if sample (a, b) then (1 : ZMod 2) else 0)) = 0 at hb
    simpa only [ColumnParityZero, sampleEquivGrouped, Equiv.coe_fn_mk,
      Bool.cond_eq_ite] using hb
  · intro h
    funext b
    change
      (∑ a ∈ A, (if sample (a, b) then (1 : ZMod 2) else 0)) = 0
    have hb := h b
    simpa only [ColumnParityZero, sampleEquivGrouped, Equiv.coe_fn_mk,
      Bool.cond_eq_ite] using hb

/--
Exact probability mass that a fixed row subset sums to zero in every column:
the paper's `q_w^(4r)` formula.
-/
theorem subsetRowCombination_zero_eventMass
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (A : Finset (Fin (3 * r))) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => subsetRowCombination sample A = 0) =
      (ENNReal.ofReal
        ((1 +
          (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^ A.card) / 2)) ^
        (4 * r) := by
  classical
  calc
    _ = eventMass
        (groupedDistribution r Delta hDelta)
        (fun grouped => ∀ b : Fin (4 * r), ColumnParityZero A (grouped b)) := by
      exact eventMass_equiv
        (sampleEquivGrouped r)
        (distribution r Delta hDelta)
        (groupedDistribution r Delta hDelta)
        (fun sample => subsetRowCombination sample A = 0)
        (fun grouped => ∀ b : Fin (4 * r), ColumnParityZero A (grouped b))
        (distribution_apply_eq_grouped r Delta hDelta)
        (subsetRowCombination_eq_zero_iff · A)
    _ = ∏ _b : Fin (4 * r),
        eventMass
          (columnDistribution r Delta hDelta)
          (ColumnParityZero A) := by
      have h :=
        eventMass_independentProduct_forall
          (fun _ : Fin (4 * r) => columnDistribution r Delta hDelta)
          (fun _ : Fin (4 * r) => ColumnParityZero A)
      rw [groupedDistribution]
      exact (eventMass_decidable_irrel
        (independentProduct fun _ : Fin (4 * r) =>
          columnDistribution r Delta hDelta)
        (fun grouped => ∀ b : Fin (4 * r), ColumnParityZero A (grouped b))
        _ _).trans h
    _ = _ := by
      simp [columnParityZero_eventMass r Delta hDelta A]

/-- Exponential envelope for the parity-zero base at a fixed subset weight. -/
theorem parityProbabilityBase_le_expEnvelope
    (p : Real) (w : Nat) (hpHalf : p ≤ 1 / 2) :
    (1 + (1 - 2 * p) ^ w) / 2 ≤
      (1 + Real.exp (-2 * (p * w))) / 2 := by
  have hbase_nonneg : 0 ≤ 1 - 2 * p := by linarith
  have hbase_exp : 1 - 2 * p ≤ Real.exp (-2 * p) := by
    linarith [Real.add_one_le_exp (-2 * p)]
  have hpow :
      (1 - 2 * p) ^ w ≤ Real.exp (-2 * (p * w)) := by
    calc
      _ ≤ (Real.exp (-2 * p)) ^ w :=
        pow_le_pow_left₀ hbase_nonneg hbase_exp w
      _ = Real.exp ((w : Real) * (-2 * p)) := by
        rw [Real.exp_nat_mul]
      _ = _ := by
        congr 1
        ring
  linarith

/--
For `p w ≤ 1`, the fixed-subset parity-zero base has the HHO20 small-weight
bound `exp(-p w / 2)`.
-/
theorem parityProbabilityBase_small_le
    (p : Real) (w : Nat) (hp0 : 0 ≤ p) (hpHalf : p ≤ 1 / 2)
    (hsmall : p * w ≤ 1) :
    (1 + (1 - 2 * p) ^ w) / 2 ≤
      Real.exp (-(p * w) / 2) := by
  let x : Real := p * w
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := hsmall
  calc
    _ ≤ (1 + Real.exp (-2 * x)) / 2 :=
      parityProbabilityBase_le_expEnvelope p w hpHalf
    _ = Real.exp (-x) * Real.cosh x := by
      rw [Real.cosh_eq]
      rw [show -2 * x = -(x + x) by ring, Real.exp_neg, Real.exp_add,
        Real.exp_neg]
      field_simp [Real.exp_ne_zero]
    _ ≤ Real.exp (-x) * Real.exp (x ^ 2 / 2) := by
      gcongr
      exact Real.cosh_le_exp_half_sq x
    _ = Real.exp (-x + x ^ 2 / 2) := by rw [← Real.exp_add]
    _ ≤ Real.exp (-x / 2) := by
      apply Real.exp_le_exp_of_le
      nlinarith [mul_nonneg hx0 (sub_nonneg.2 hx1)]

/-- A rational numerical bound used in the large-subset regime. -/
theorem exp_neg_two_le_one_seventh :
    Real.exp (-2) ≤ (1 : Real) / 7 := by
  have he : (7 : Real) < Real.exp 2 := by
    rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_d9]
  rw [Real.exp_neg]
  simpa [one_div] using
    (inv_le_inv₀ (Real.exp_pos 2) (by norm_num : (0 : Real) < 7)).2 he.le

/--
For `1 ≤ p w`, the fixed-subset parity-zero base is at most `4/7`.
-/
theorem parityProbabilityBase_large_le
    (p : Real) (w : Nat) (hpHalf : p ≤ 1 / 2)
    (hlarge : 1 ≤ p * w) :
    (1 + (1 - 2 * p) ^ w) / 2 ≤ (4 : Real) / 7 := by
  calc
    _ ≤ (1 + Real.exp (-2 * (p * w))) / 2 :=
      parityProbabilityBase_le_expEnvelope p w hpHalf
    _ ≤ (1 + Real.exp (-2)) / 2 := by
      gcongr
      nlinarith
    _ ≤ (1 + (1 : Real) / 7) / 2 := by
      gcongr
      exact exp_neg_two_le_one_seventh
    _ = _ := by norm_num

/-- Fixed-subset event-mass bound in the paper's small-weight regime. -/
theorem subsetRowCombination_zero_eventMass_small_le
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r)
    (A : Finset (Fin (3 * r))) (hsmall : A.card * Delta ≤ 4 * r) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => subsetRowCombination sample A = 0) ≤
      (ENNReal.ofReal
        (Real.exp
          (-((incidenceProbability (4 * r) Delta).toReal * A.card) / 2))) ^
        (4 * r) := by
  let p : Real := (incidenceProbability (4 * r) Delta).toReal
  have hp0 : 0 ≤ p := by positivity
  have hnpos : (0 : Real) < 4 * r := by positivity
  have hmean : ((4 * r : Nat) : Real) * p = Delta := by
    exact check_expected_degree r Delta hr
  have hp : p = (Delta : Real) / ((4 * r : Nat) : Real) := by
    apply (eq_div_iff (by positivity : (((4 * r : Nat) : Real) ≠ 0))).2
    simpa [mul_comm] using hmean
  have hpHalf : p ≤ 1 / 2 := by
    rw [hp, div_le_iff₀ (by positivity : (0 : Real) < (4 * r : Nat))]
    have hHalfR : ((2 * Delta : Nat) : Real) ≤ (4 * r : Nat) := by
      exact_mod_cast hHalf
    push_cast at hHalfR ⊢
    linarith
  have hsmallR : p * A.card ≤ 1 := by
    rw [hp]
    rw [div_mul_eq_mul_div, div_le_one (by positivity :
      (0 : Real) < (4 * r : Nat))]
    exact_mod_cast (show Delta * A.card ≤ 4 * r by
      simpa [Nat.mul_comm] using hsmall)
  rw [subsetRowCombination_zero_eventMass r Delta hDelta A]
  apply pow_le_pow_left'
  exact ENNReal.ofReal_le_ofReal
    (parityProbabilityBase_small_le p A.card hp0 hpHalf hsmallR)

/--
After substituting `p = Delta / (4r)`, the small-weight estimate is a
geometric weight in the row-subset cardinality.  Keeping this dependence is
essential: replacing it by a uniform estimate would lose against the
`2^(3r)` possible row subsets.
-/
theorem subsetRowCombination_zero_eventMass_small_geometric_le
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r)
    (A : Finset (Fin (3 * r))) (hsmall : A.card * Delta ≤ 4 * r) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => subsetRowCombination sample A = 0) ≤
      (ENNReal.ofReal (Real.exp (-(Delta : Real) / 2))) ^ A.card := by
  let p : Real := (incidenceProbability (4 * r) Delta).toReal
  have hmean : ((4 * r : Nat) : Real) * p = Delta := by
    exact check_expected_degree r Delta hr
  calc
    _ ≤
        (ENNReal.ofReal
          (Real.exp (-(p * A.card) / 2))) ^ (4 * r) :=
      subsetRowCombination_zero_eventMass_small_le
        r Delta hr hDelta hHalf A hsmall
    _ = ENNReal.ofReal
        ((Real.exp (-(p * A.card) / 2)) ^ (4 * r)) := by
      rw [ENNReal.ofReal_pow (Real.exp_pos _).le]
    _ = ENNReal.ofReal
        ((Real.exp (-(Delta : Real) / 2)) ^ A.card) := by
      congr 1
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      nlinarith
    _ = _ := ENNReal.ofReal_pow (Real.exp_pos _).le A.card

/-- Fixed-subset event-mass bound in the paper's large-weight regime. -/
theorem subsetRowCombination_zero_eventMass_large_le
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r)
    (A : Finset (Fin (3 * r))) (hlarge : 4 * r ≤ A.card * Delta) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => subsetRowCombination sample A = 0) ≤
      (ENNReal.ofReal ((4 : Real) / 7)) ^ (4 * r) := by
  let p : Real := (incidenceProbability (4 * r) Delta).toReal
  have hnpos : (0 : Real) < 4 * r := by positivity
  have hmean : ((4 * r : Nat) : Real) * p = Delta := by
    exact check_expected_degree r Delta hr
  have hp : p = (Delta : Real) / ((4 * r : Nat) : Real) := by
    apply (eq_div_iff (by positivity : (((4 * r : Nat) : Real) ≠ 0))).2
    simpa [mul_comm] using hmean
  have hpHalf : p ≤ 1 / 2 := by
    rw [hp, div_le_iff₀ (by positivity : (0 : Real) < (4 * r : Nat))]
    have hHalfR : ((2 * Delta : Nat) : Real) ≤ (4 * r : Nat) := by
      exact_mod_cast hHalf
    push_cast at hHalfR ⊢
    linarith
  have hlargeR : 1 ≤ p * A.card := by
    rw [hp]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity :
      (0 : Real) < (4 * r : Nat))]
    have hcast :
        (((4 * r : Nat) : Real) ≤ ((Delta * A.card : Nat) : Real)) := by
      exact_mod_cast (show 4 * r ≤ Delta * A.card by
        simpa [Nat.mul_comm] using hlarge)
    simpa using hcast
  rw [subsetRowCombination_zero_eventMass r Delta hDelta A]
  apply pow_le_pow_left'
  exact ENNReal.ofReal_le_ofReal
    (parityProbabilityBase_large_le p A.card hpHalf hlargeR)

/-- Binomial enumeration of subsets, with the subset weight left symbolic. -/
theorem sum_powerset_pow_card
    {α : Type*} [DecidableEq α]
    (s : Finset α) (t : ENNReal) :
    ∑ A ∈ s.powerset, t ^ A.card = (1 + t) ^ s.card := by
  rw [Finset.sum_powerset_apply_card]
  simpa [nsmul_eq_mul, mul_comm, add_comm] using
    (add_pow t 1 s.card).symm

/--
The nonempty subsets contribute the binomial sum with its empty-set term
removed.  This is the counting identity needed by the rank union bound.
-/
theorem sum_nonempty_finset_pow_card
    {α : Type*} [Fintype α] [DecidableEq α]
    (t : ENNReal) :
    (∑ A : {A : Finset α // A.Nonempty}, t ^ A.1.card) =
      (1 + t) ^ Fintype.card α - 1 := by
  let p : Finset α → Prop := fun A => A ≠ ∅
  let q : Finset α → Prop := fun A => A.Nonempty
  have hpq : p = q := by
    funext A
    apply propext
    exact Finset.nonempty_iff_ne_empty.symm
  have hfull :
      (∑ A : Finset α, t ^ A.card) =
        (1 + t) ^ Fintype.card α := by
    rw [← Finset.powerset_univ]
    simpa using sum_powerset_pow_card (Finset.univ : Finset α) t
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun A : Finset α => t ^ A.card) ∅] at hfull
  have hsub :
      (∑ A : {A : Finset α // A ≠ ∅}, t ^ A.1.card) =
        ∑ A : {A : Finset α // A.Nonempty}, t ^ A.1.card := by
    exact Fintype.sum_equiv
      (Equiv.subtypeEquivProp hpq)
      (fun A : {A : Finset α // A ≠ ∅} => t ^ A.1.card)
      (fun A : {A : Finset α // A.Nonempty} => t ^ A.1.card)
      (fun _ => rfl)
  simp only [Finset.card_empty, pow_zero] at hfull
  rw [hsub] at hfull
  apply (ENNReal.add_left_inj (by simp : (1 : ENNReal) ≠ ⊤)).mp
  rw [tsub_add_cancel_of_le]
  · simpa [add_comm] using hfull
  · rw [← hfull]
    exact le_add_right le_rfl

/-- Every nontrivial row dependency is a nonempty subset parity event. -/
theorem exists_nonempty_subsetRowCombination_eq_zero_of_not_fullRowRank
    {r : Nat} {sample : Sample r} (h : ¬HasFullRowRank sample) :
    ∃ A : Finset (Fin (3 * r)),
      A.Nonempty ∧ subsetRowCombination sample A = 0 := by
  rcases exists_nonzero_rowCombination_eq_zero_of_not_fullRowRank h with
    ⟨coeff, hcoeff, hzero⟩
  refine ⟨rowSupport coeff, (rowSupport_nonempty_iff coeff).2 hcoeff, ?_⟩
  rw [← rowCombination_eq_subsetRowCombination sample coeff]
  exact hzero

noncomputable instance instDecidablePredHasFullRowRank (r : Nat) :
    DecidablePred (@HasFullRowRank r) :=
  Classical.decPred _

/--
Union bound for full-row-rank failure, with the exact fixed-subset probability
still visible for the paper's subsequent small- and large-weight split.
-/
theorem fullRowRank_failureMass_le_exact_sum
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (@HasFullRowRank r) ≤
      ∑ A : {A : Finset (Fin (3 * r)) // A.Nonempty},
        (ENNReal.ofReal
          ((1 +
            (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^
              A.1.card) / 2)) ^ (4 * r) := by
  calc
    _ ≤ ∑ A : {A : Finset (Fin (3 * r)) // A.Nonempty},
        eventMass
          (distribution r Delta hDelta)
          (fun sample => subsetRowCombination sample A.1 = 0) := by
      apply failureMass_le_sum_eventMass
      intro sample hsample
      rcases
          exists_nonempty_subsetRowCombination_eq_zero_of_not_fullRowRank
            hsample with
        ⟨A, hA, hzero⟩
      exact ⟨⟨A, hA⟩, hzero⟩
    _ = _ := by
      apply Fintype.sum_congr
      intro A
      exact subsetRowCombination_zero_eventMass r Delta hDelta A.1

/--
The rank-failure union bound after the HHO20 small/large subset split.

The first summand is the exact binomial contribution of all nonempty
small-subset geometric weights.  The second summand bounds the number of
large subsets by all `2^(3r)` row subsets.  No independence between distinct
row-dependency events is assumed.
-/
theorem fullRowRank_failureMass_le_split
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (@HasFullRowRank r) ≤
      (1 + ENNReal.ofReal (Real.exp (-(Delta : Real) / 2))) ^ (3 * r) - 1 +
      (2 : ENNReal) ^ (3 * r) *
        (ENNReal.ofReal ((4 : Real) / 7)) ^ (4 * r) := by
  let t : ENNReal := ENNReal.ofReal (Real.exp (-(Delta : Real) / 2))
  let c : ENNReal := (ENNReal.ofReal ((4 : Real) / 7)) ^ (4 * r)
  calc
    _ ≤
        ∑ A : {A : Finset (Fin (3 * r)) // A.Nonempty},
          (ENNReal.ofReal
            ((1 +
              (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^
                A.1.card) / 2)) ^ (4 * r) :=
      fullRowRank_failureMass_le_exact_sum r Delta hDelta
    _ ≤ ∑ A : {A : Finset (Fin (3 * r)) // A.Nonempty},
          (t ^ A.1.card + c) := by
      apply Finset.sum_le_sum
      intro A _
      rw [← subsetRowCombination_zero_eventMass r Delta hDelta A.1]
      by_cases hsmall : A.1.card * Delta ≤ 4 * r
      · exact
          (subsetRowCombination_zero_eventMass_small_geometric_le
            r Delta hr hDelta hHalf A.1 hsmall).trans
            (le_add_right le_rfl)
      · have hlarge : 4 * r ≤ A.1.card * Delta :=
          (Nat.lt_of_not_ge hsmall).le
        exact
          (subsetRowCombination_zero_eventMass_large_le
            r Delta hr hDelta hHalf A.1 hlarge).trans
            (le_add_left le_rfl)
    _ =
        (∑ A : {A : Finset (Fin (3 * r)) // A.Nonempty},
          t ^ A.1.card) +
        ∑ _A : {A : Finset (Fin (3 * r)) // A.Nonempty}, c := by
      exact Finset.sum_add_distrib
    _ ≤
        ((1 + t) ^ (3 * r) - 1) +
          (2 : ENNReal) ^ (3 * r) * c := by
      gcongr
      · simpa only [Fintype.card_fin] using
          (sum_nonempty_finset_pow_card
            (α := Fin (3 * r)) t).le
      · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        gcongr
        norm_cast
        simpa [Fintype.card_finset] using
          (Fintype.card_subtype_le
            (fun A : Finset (Fin (3 * r)) => A.Nonempty))
    _ = _ := rfl

end QEC.Coding.FiberBundle.RandomBase
