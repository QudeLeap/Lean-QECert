import QEC.Coding.FiberBundle.RandomBase.Rank

/-!
# Linear-distance closure for the HHO20 random base

HHO20 Proposition `prop:min-dist` calls this a standard exercise.  This file
expands that exercise: rows are regrouped as an independent product, the
probability that a fixed binary support passes every parity check is computed
exactly, and the low-weight failure event is covered by those fixed-support
events.
-/

namespace QEC.Coding.FiberBundle.RandomBase

open scoped BigOperators
open MeasureTheory

/-- All incidences in one check row of the Tanner matrix. -/
abbrev RowSample (r : Nat) := Fin (4 * r) → Bool

/-- The incidence sample space regrouped as `check → variable → bit`. -/
abbrev RowGroupedSample (r : Nat) := Fin (3 * r) → RowSample r

/-- Regroup `(check, variable)` incidences into independent check rows. -/
def sampleEquivRows (r : Nat) : Sample r ≃ RowGroupedSample r where
  toFun sample a b := sample (a, b)
  invFun grouped edge := grouped edge.1 edge.2
  left_inv sample := by
    funext edge
    rfl
  right_inv grouped := by
    funext a b
    rfl

/-- One independently sampled Tanner-matrix row. -/
noncomputable def rowDistribution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    PMF (RowSample r) :=
  independentProduct fun _ =>
    PMF.bernoulli
      (incidenceProbability (4 * r) Delta)
      (incidenceProbability_le_one hDelta)

/-- The HHO20 sampler represented as an independent product of rows. -/
noncomputable def rowGroupedDistribution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    PMF (RowGroupedSample r) :=
  independentProduct fun _ => rowDistribution r Delta hDelta

@[simp]
theorem rowDistribution_apply
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (row : RowSample r) :
    rowDistribution r Delta hDelta row =
      ∏ b : Fin (4 * r),
        cond (row b)
          (incidenceProbability (4 * r) Delta)
          (1 - incidenceProbability (4 * r) Delta) := by
  simp [rowDistribution, independentProduct_apply, PMF.bernoulli_apply]

@[simp]
theorem rowGroupedDistribution_apply
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (grouped : RowGroupedSample r) :
    rowGroupedDistribution r Delta hDelta grouped =
      ∏ a : Fin (3 * r), ∏ b : Fin (4 * r),
        cond (grouped a b)
          (incidenceProbability (4 * r) Delta)
          (1 - incidenceProbability (4 * r) Delta) := by
  simp [rowGroupedDistribution, independentProduct_apply]

/-- Regrouping by rows preserves the original sampler pointwise. -/
theorem distribution_apply_eq_rows
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (sample : Sample r) :
    distribution r Delta hDelta sample =
      rowGroupedDistribution r Delta hDelta (sampleEquivRows r sample) := by
  rw [distribution_apply, rowGroupedDistribution_apply]
  norm_cast
  rw [← Finset.prod_product' Finset.univ Finset.univ]
  rfl

/-- Incidences within one sampled row are mutually independent. -/
theorem rowDistribution_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun b (row : RowSample r) => row b)
      (rowDistribution r Delta hDelta).toMeasure := by
  exact independentProduct_iIndepFun _

/-- Every coordinate of a sampled row has the construction's Bernoulli law. -/
theorem rowDistribution_coordinate_hasLaw
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) :
    ProbabilityTheory.HasLaw
      (fun row : RowSample r => row b)
      (PMF.bernoulli
        (incidenceProbability (4 * r) Delta)
        (incidenceProbability_le_one hDelta)).toMeasure
      (rowDistribution r Delta hDelta).toMeasure := by
  simpa only [rowDistribution] using
    (independentProduct_coordinate_hasLaw
      (fun _ : Fin (4 * r) =>
        PMF.bernoulli
          (incidenceProbability (4 * r) Delta)
          (incidenceProbability_le_one hDelta))
      b)

/-- A sampled row has even parity on a selected variable subset. -/
def RowParityZero {r : Nat}
    (A : Finset (Fin (4 * r))) (row : RowSample r) : Prop :=
  (∑ b ∈ A, cond (row b) (1 : ZMod 2) 0) = 0

instance instDecidablePredRowParityZero
    {r : Nat} (A : Finset (Fin (4 * r))) :
    DecidablePred (RowParityZero A) := by
  intro row
  unfold RowParityZero
  infer_instance

/-- The parity character factors over a selected variable subset. -/
theorem paritySign_row_sum
    {r : Nat} (A : Finset (Fin (4 * r))) (row : RowSample r) :
    paritySign (∑ b ∈ A, cond (row b) (1 : ZMod 2) 0) =
      ∏ b ∈ A, signedBit (row b) := by
  induction A using Finset.induction_on with
  | empty => simp [paritySign]
  | @insert b A hb ih =>
      rw [Finset.sum_insert hb, Finset.prod_insert hb, paritySign_add, ih,
        paritySign_bit]

/-- The expectation of one signed incidence in a sampled row. -/
theorem integral_row_signedBit
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) :
    ∫ row, signedBit (row b) ∂
        (rowDistribution r Delta hDelta).toMeasure =
      1 - 2 * (incidenceProbability (4 * r) Delta).toReal := by
  calc
    _ = ∫ bit, signedBit bit ∂
        (PMF.bernoulli
          (incidenceProbability (4 * r) Delta)
          (incidenceProbability_le_one hDelta)).toMeasure := by
      exact (rowDistribution_coordinate_hasLaw r Delta hDelta b).integral_comp
        (f := signedBit)
        (by fun_prop)
    _ = _ := by
      rw [PMF.integral_eq_sum]
      simp [signedBit, PMF.bernoulli_apply]
      rw [NNReal.coe_sub (incidenceProbability_le_one hDelta)]
      norm_num
      ring

/-- The signed expectation over a selected variable subset factors. -/
theorem integral_row_signedBit_product
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (A : Finset (Fin (4 * r))) :
    ∫ row, (∏ b ∈ A, signedBit (row b)) ∂
        (rowDistribution r Delta hDelta).toMeasure =
      (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^ A.card := by
  have hIndep : ProbabilityTheory.iIndepFun
      (fun b : A => fun row : RowSample r => signedBit (row b))
      (rowDistribution r Delta hDelta).toMeasure :=
    ((rowDistribution_iIndepFun r Delta hDelta).precomp
      (g := fun b : A => b.1)
      Subtype.val_injective).comp
      (fun _ bit => signedBit bit)
      (fun _ => by fun_prop)
  have hFactor :=
    hIndep.integral_fun_prod_eq_prod_integral
      (fun _ => (measurable_of_finite _).aestronglyMeasurable)
  rw [show (fun row : RowSample r =>
      ∏ b ∈ A, signedBit (row b)) =
      (fun row => ∏ b : A, signedBit (row b)) by
    funext row
    exact (Finset.prod_coe_sort A (fun b => signedBit (row b))).symm]
  simpa [integral_row_signedBit r Delta hDelta] using hFactor

/-- Real indicator of the selected-row even-parity event. -/
noncomputable def rowParityZeroIndicator {r : Nat}
    (A : Finset (Fin (4 * r))) (row : RowSample r) : Real :=
  if RowParityZero A row then 1 else 0

/-- Fourier character identity for the row parity indicator. -/
theorem rowParityZeroIndicator_eq
    {r : Nat} (A : Finset (Fin (4 * r))) (row : RowSample r) :
    rowParityZeroIndicator A row =
      (1 + ∏ b ∈ A, signedBit (row b)) / 2 := by
  classical
  rw [← paritySign_row_sum A row]
  simp only [rowParityZeroIndicator, RowParityZero]
  by_cases hzero :
      (∑ b ∈ A, cond (row b) (1 : ZMod 2) 0) = 0
  · erw [if_pos hzero]
    simp [paritySign, hzero]
  · erw [if_neg hzero]
    simp [paritySign, hzero]

/-- Exact probability that one row has even parity on a fixed support. -/
theorem rowParityZero_measureReal
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (A : Finset (Fin (4 * r))) :
    (rowDistribution r Delta hDelta).toMeasure.real
        {row | RowParityZero A row} =
      (1 +
        (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^ A.card) / 2 := by
  classical
  let μ := (rowDistribution r Delta hDelta).toMeasure
  calc
    μ.real {row | RowParityZero A row} =
        ∫ row, rowParityZeroIndicator A row ∂μ := by
      rw [← integral_indicator_one (μ := μ) (Set.toFinite _).measurableSet]
      apply integral_congr_ae
      filter_upwards [] with row
      simp [rowParityZeroIndicator, Set.indicator]
    _ = ∫ row,
        (1 + ∏ b ∈ A, signedBit (row b)) / 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (rowParityZeroIndicator_eq A)
    _ = _ := by
      rw [integral_div, integral_add]
      · simp [μ, integral_row_signedBit_product r Delta hDelta A]
      · exact Integrable.of_finite
      · exact Integrable.of_finite

/-- ENNReal form of the exact one-row parity probability. -/
theorem rowParityZero_eventMass
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (A : Finset (Fin (4 * r))) :
    eventMass
        (rowDistribution r Delta hDelta)
        (RowParityZero A) =
      ENNReal.ofReal
        ((1 +
          (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^ A.card) / 2) := by
  classical
  calc
    _ = (rowDistribution r Delta hDelta).toMeasure
        {row | RowParityZero A row} :=
      eventMass_eq_toMeasure _ _
    _ = ENNReal.ofReal
        ((rowDistribution r Delta hDelta).toMeasure.real
          {row | RowParityZero A row}) := by
      rw [ofReal_measureReal]
    _ = _ := by
      rw [rowParityZero_measureReal r Delta hDelta A]

/-- A support subset determines its binary indicator word. -/
def supportWord {r : Nat} (A : Finset (Fin (4 * r))) :
    Word (ZMod 2) (Fin (4 * r)) :=
  fun b => if b ∈ A then 1 else 0

@[simp]
theorem hammingSupport_supportWord
    {r : Nat} (A : Finset (Fin (4 * r))) :
    hammingSupport (supportWord A) = A := by
  ext b
  simp [hammingSupport, supportWord]

@[simp]
theorem HammingWeight_supportWord
    {r : Nat} (A : Finset (Fin (4 * r))) :
    HammingWeight (supportWord A) = A.card := by
  rw [HammingWeight_eq_card_hammingSupport, hammingSupport_supportWord]

/-- Every binary word is the indicator of its Hamming support. -/
theorem supportWord_hammingSupport
    {r : Nat} (x : Word (ZMod 2) (Fin (4 * r))) :
    supportWord (hammingSupport x) = x := by
  funext b
  by_cases hb : x b = 0
  · simp [supportWord, hammingSupport, hb]
  · rw [zmod2_eq_one_of_ne_zero (x b) hb]
    simp only [supportWord, hammingSupport, Finset.mem_filter,
      Finset.mem_univ, true_and, if_pos hb]

/-- Passing all parity checks is the all-row parity-zero event. -/
theorem supportWord_mem_code_iff
    {r : Nat} (sample : Sample r)
    (A : Finset (Fin (4 * r))) :
    supportWord A ∈ (code sample).carrier ↔
      ∀ a : Fin (3 * r),
        RowParityZero A (sampleEquivRows r sample a) := by
  rw [code, mem_parityCheckKernelCode]
  have hsum (sample : Sample r) (a : Fin (3 * r)) :
      (∑ b, if b ∈ A then
          (if sample (a, b) then (1 : ZMod 2) else 0) else 0) =
        ∑ b ∈ A, (if sample (a, b) then (1 : ZMod 2) else 0) := by
    rw [← sum_filter_eq_sum_ite]
    simp
  constructor
  · intro h a
    have ha := congrFun h a
    change
      (∑ b, (if sample (a, b) then (1 : ZMod 2) else 0) *
        (if b ∈ A then 1 else 0)) = 0 at ha
    simp only [mul_ite, mul_one, mul_zero] at ha
    rw [hsum sample a] at ha
    simpa only [RowParityZero, sampleEquivRows, Equiv.coe_fn_mk,
      Bool.cond_eq_ite] using ha
  · intro h
    funext a
    have ha := h a
    change
      (∑ b, (if sample (a, b) then (1 : ZMod 2) else 0) *
        (if b ∈ A then 1 else 0)) = 0
    simp only [mul_ite, mul_one, mul_zero]
    rw [hsum sample a]
    simpa only [RowParityZero, sampleEquivRows, Equiv.coe_fn_mk,
      Bool.cond_eq_ite] using ha

noncomputable instance instDecidablePredSupportWordMemCode
    (r : Nat) (A : Finset (Fin (4 * r))) :
    DecidablePred
      (fun sample : Sample r => supportWord A ∈ (code sample).carrier) :=
  Classical.decPred _

/--
Exact probability that the indicator word of a fixed support passes all
`3r` parity checks.
-/
theorem supportWord_mem_code_eventMass
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (A : Finset (Fin (4 * r))) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => supportWord A ∈ (code sample).carrier) =
      (ENNReal.ofReal
        ((1 +
          (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^
            A.card) / 2)) ^ (3 * r) := by
  classical
  calc
    _ = eventMass
        (rowGroupedDistribution r Delta hDelta)
        (fun grouped =>
          ∀ a : Fin (3 * r), RowParityZero A (grouped a)) := by
      exact eventMass_equiv
        (sampleEquivRows r)
        (distribution r Delta hDelta)
        (rowGroupedDistribution r Delta hDelta)
        (fun sample => supportWord A ∈ (code sample).carrier)
        (fun grouped =>
          ∀ a : Fin (3 * r), RowParityZero A (grouped a))
        (distribution_apply_eq_rows r Delta hDelta)
        (supportWord_mem_code_iff · A)
    _ = ∏ _a : Fin (3 * r),
        eventMass
          (rowDistribution r Delta hDelta)
          (RowParityZero A) := by
      have h :=
        eventMass_independentProduct_forall
          (fun _ : Fin (3 * r) => rowDistribution r Delta hDelta)
          (fun _ : Fin (3 * r) => RowParityZero A)
      rw [rowGroupedDistribution]
      exact (eventMass_decidable_irrel
        (independentProduct fun _ : Fin (3 * r) =>
          rowDistribution r Delta hDelta)
        (fun grouped =>
          ∀ a : Fin (3 * r), RowParityZero A (grouped a))
        _ _).trans h
    _ = _ := by
      simp [rowParityZero_eventMass r Delta hDelta A]

/--
For supports below the correlation length `4r / Delta`, substituting
`p = Delta/(4r)` turns the fixed-support probability into a geometric weight
`exp(-3 Delta / 8)^|A|`.
-/
theorem supportWord_mem_code_eventMass_small_geometric_le
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r)
    (A : Finset (Fin (4 * r))) (hsmall : A.card * Delta ≤ 4 * r) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => supportWord A ∈ (code sample).carrier) ≤
      (ENNReal.ofReal
        (Real.exp (-(3 : Real) * Delta / 8))) ^ A.card := by
  let p : Real := (incidenceProbability (4 * r) Delta).toReal
  have hmean : ((4 * r : Nat) : Real) * p = Delta := by
    exact check_expected_degree r Delta hr
  have hp : p = (Delta : Real) / ((4 * r : Nat) : Real) := by
    apply (eq_div_iff (by positivity : (((4 * r : Nat) : Real) ≠ 0))).2
    simpa [mul_comm] using hmean
  have hp0 : 0 ≤ p := by positivity
  have hpHalf : p ≤ 1 / 2 := by
    rw [hp, div_le_iff₀ (by positivity : (0 : Real) < (4 * r : Nat))]
    have hHalfR : ((2 * Delta : Nat) : Real) ≤ (4 * r : Nat) := by
      exact_mod_cast hHalf
    norm_num [Nat.cast_mul] at hHalfR ⊢
    linarith
  have hsmallR : p * A.card ≤ 1 := by
    rw [hp]
    rw [div_mul_eq_mul_div, div_le_one (by positivity :
      (0 : Real) < (4 * r : Nat))]
    exact_mod_cast (show Delta * A.card ≤ 4 * r by
      simpa [Nat.mul_comm] using hsmall)
  rw [supportWord_mem_code_eventMass r Delta hDelta A]
  calc
    _ ≤
        (ENNReal.ofReal
          (Real.exp (-(p * A.card) / 2))) ^ (3 * r) := by
      apply pow_le_pow_left'
      exact ENNReal.ofReal_le_ofReal
        (parityProbabilityBase_small_le
          p A.card hp0 hpHalf hsmallR)
    _ = ENNReal.ofReal
        ((Real.exp (-(p * A.card) / 2)) ^ (3 * r)) := by
      rw [ENNReal.ofReal_pow (Real.exp_pos _).le]
    _ = ENNReal.ofReal
        ((Real.exp (-(3 : Real) * Delta / 8)) ^ A.card) := by
      congr 1
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      calc
        ((3 * r : Nat) : Real) * (-(p * (A.card : Real)) / 2) =
            (-(3 : Real) * (A.card : Real) / 8) *
              (((4 * r : Nat) : Real) * p) := by
                norm_num [Nat.cast_mul]
                ring
        _ = (-(3 : Real) * (A.card : Real) / 8) * Delta := by
          rw [hmean]
        _ = (A.card : Real) * (-(3 : Real) * Delta / 8) := by ring
    _ = _ := ENNReal.ofReal_pow (Real.exp_pos _).le A.card

/--
For every fixed support, retain the exponential parity envelope before any
large-weight simplification.  This weight dependence is needed for the
Gilbert--Varshamov counting range.
-/
theorem supportWord_mem_code_eventMass_expEnvelope_le
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r)
    (A : Finset (Fin (4 * r))) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => supportWord A ∈ (code sample).carrier) ≤
      (ENNReal.ofReal
        ((1 + Real.exp
          (-2 * ((incidenceProbability (4 * r) Delta).toReal *
            A.card))) / 2)) ^ (3 * r) := by
  let p : Real := (incidenceProbability (4 * r) Delta).toReal
  have hmean : ((4 * r : Nat) : Real) * p = Delta := by
    exact check_expected_degree r Delta hr
  have hp : p = (Delta : Real) / ((4 * r : Nat) : Real) := by
    apply (eq_div_iff (by positivity : (((4 * r : Nat) : Real) ≠ 0))).2
    simpa [mul_comm] using hmean
  have hpHalf : p ≤ 1 / 2 := by
    rw [hp, div_le_iff₀ (by positivity : (0 : Real) < (4 * r : Nat))]
    have hHalfR : ((2 * Delta : Nat) : Real) ≤ (4 * r : Nat) := by
      exact_mod_cast hHalf
    norm_num [Nat.cast_mul] at hHalfR ⊢
    linarith
  rw [supportWord_mem_code_eventMass r Delta hDelta A]
  apply pow_le_pow_left'
  exact ENNReal.ofReal_le_ofReal
    (parityProbabilityBase_le_expEnvelope p A.card hpHalf)

/-- A reciprocal envelope for `exp (-2x)` on the nonnegative half-line. -/
theorem exp_neg_two_mul_le_inv_one_add_two_mul
    (x : Real) (hx : 0 ≤ x) :
    Real.exp (-2 * x) ≤ 1 / (1 + 2 * x) := by
  rw [show -2 * x = -(2 * x) by ring, Real.exp_neg]
  have hden : 0 < 1 + 2 * x := by positivity
  rw [one_div]
  apply (inv_le_inv₀ (Real.exp_pos (2 * x)) hden).2
  simpa [add_comm] using Real.add_one_le_exp (2 * x)

/--
On `0 ≤ p w ≤ 3`, the parity-zero base is at most `exp(-p w / 7)`.
The rational constant is deliberately conservative but remains strong enough
for the later low-weight union bound.
-/
theorem parityProbabilityBase_medium_le
    (p : Real) (w : Nat) (hp0 : 0 ≤ p) (hpHalf : p ≤ 1 / 2)
    (hmedium : p * w ≤ 3) :
    (1 + (1 - 2 * p) ^ w) / 2 ≤
      Real.exp (-(p * w) / 7) := by
  let x : Real := p * w
  have hx0 : 0 ≤ x := by positivity
  have hx3 : x ≤ 3 := hmedium
  have hden : 0 < 1 + 2 * x := by positivity
  calc
    _ ≤ (1 + Real.exp (-2 * x)) / 2 :=
      parityProbabilityBase_le_expEnvelope p w hpHalf
    _ ≤ (1 + 1 / (1 + 2 * x)) / 2 := by
      gcongr
      exact exp_neg_two_mul_le_inv_one_add_two_mul x hx0
    _ = (1 + x) / (1 + 2 * x) := by
      field_simp
      ring
    _ ≤ 1 - x / 7 := by
      rw [div_le_iff₀ hden]
      nlinarith [mul_nonneg hx0 (sub_nonneg.2 hx3)]
    _ ≤ Real.exp (-x / 7) := by
      linarith [Real.add_one_le_exp (-x / 7)]

/-- Numerical tail used once `p w ≥ 3`. -/
theorem exp_neg_six_le_one_over_343 :
    Real.exp (-6) ≤ (1 : Real) / 343 := by
  calc
    Real.exp (-6) = (Real.exp (-2)) ^ 3 := by
      rw [show (-6 : Real) = (3 : Nat) * (-2 : Real) by norm_num,
        Real.exp_nat_mul]
    _ ≤ ((1 : Real) / 7) ^ 3 := by
      exact pow_le_pow_left₀ (Real.exp_pos (-2)).le
        exp_neg_two_le_one_seventh 3
    _ = _ := by norm_num

/-- Once `p w ≥ 3`, the parity-zero base is at most `172/343`. -/
theorem parityProbabilityBase_veryLarge_le
    (p : Real) (w : Nat) (hpHalf : p ≤ 1 / 2)
    (hlarge : 3 ≤ p * w) :
    (1 + (1 - 2 * p) ^ w) / 2 ≤ (172 : Real) / 343 := by
  calc
    _ ≤ (1 + Real.exp (-2 * (p * w))) / 2 :=
      parityProbabilityBase_le_expEnvelope p w hpHalf
    _ ≤ (1 + Real.exp (-6)) / 2 := by
      gcongr
      nlinarith
    _ ≤ (1 + (1 : Real) / 343) / 2 := by
      gcongr
      exact exp_neg_six_le_one_over_343
    _ = _ := by norm_num

/--
Fixed-support geometric estimate throughout the enlarged regime
`Delta |A| ≤ 12r`.
-/
theorem supportWord_mem_code_eventMass_medium_geometric_le
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r)
    (A : Finset (Fin (4 * r))) (hmedium : A.card * Delta ≤ 12 * r) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => supportWord A ∈ (code sample).carrier) ≤
      (ENNReal.ofReal
        (Real.exp (-(3 : Real) * Delta / 28))) ^ A.card := by
  let p : Real := (incidenceProbability (4 * r) Delta).toReal
  have hmean : ((4 * r : Nat) : Real) * p = Delta := by
    exact check_expected_degree r Delta hr
  have hp : p = (Delta : Real) / ((4 * r : Nat) : Real) := by
    apply (eq_div_iff (by positivity : (((4 * r : Nat) : Real) ≠ 0))).2
    simpa [mul_comm] using hmean
  have hp0 : 0 ≤ p := by positivity
  have hpHalf : p ≤ 1 / 2 := by
    rw [hp, div_le_iff₀ (by positivity : (0 : Real) < (4 * r : Nat))]
    have hHalfR : ((2 * Delta : Nat) : Real) ≤ (4 * r : Nat) := by
      exact_mod_cast hHalf
    norm_num [Nat.cast_mul] at hHalfR ⊢
    linarith
  have hmediumR : p * A.card ≤ 3 := by
    rw [hp]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity :
      (0 : Real) < (4 * r : Nat))]
    have hcast :
        (((Delta * A.card : Nat) : Real) ≤ ((12 * r : Nat) : Real)) := by
      exact_mod_cast (show Delta * A.card ≤ 12 * r by
        simpa [Nat.mul_comm] using hmedium)
    norm_num [Nat.cast_mul] at hcast ⊢
    linarith
  rw [supportWord_mem_code_eventMass r Delta hDelta A]
  calc
    _ ≤
        (ENNReal.ofReal
          (Real.exp (-(p * A.card) / 7))) ^ (3 * r) := by
      apply pow_le_pow_left'
      exact ENNReal.ofReal_le_ofReal
        (parityProbabilityBase_medium_le
          p A.card hp0 hpHalf hmediumR)
    _ = ENNReal.ofReal
        ((Real.exp (-(p * A.card) / 7)) ^ (3 * r)) := by
      rw [ENNReal.ofReal_pow (Real.exp_pos _).le]
    _ = ENNReal.ofReal
        ((Real.exp (-(3 : Real) * Delta / 28)) ^ A.card) := by
      congr 1
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      calc
        ((3 * r : Nat) : Real) * (-(p * (A.card : Real)) / 7) =
            (-(3 : Real) * (A.card : Real) / 28) *
              (((4 * r : Nat) : Real) * p) := by
                norm_num [Nat.cast_mul]
                ring
        _ = (-(3 : Real) * (A.card : Real) / 28) * Delta := by
          rw [hmean]
        _ = (A.card : Real) * (-(3 : Real) * Delta / 28) := by ring
    _ = _ := ENNReal.ofReal_pow (Real.exp_pos _).le A.card

/-- Uniform fixed-support estimate in the regime `12r ≤ Delta |A|`. -/
theorem supportWord_mem_code_eventMass_veryLarge_le
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r)
    (A : Finset (Fin (4 * r))) (hlarge : 12 * r ≤ A.card * Delta) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => supportWord A ∈ (code sample).carrier) ≤
      (ENNReal.ofReal ((172 : Real) / 343)) ^ (3 * r) := by
  let p : Real := (incidenceProbability (4 * r) Delta).toReal
  have hmean : ((4 * r : Nat) : Real) * p = Delta := by
    exact check_expected_degree r Delta hr
  have hp : p = (Delta : Real) / ((4 * r : Nat) : Real) := by
    apply (eq_div_iff (by positivity : (((4 * r : Nat) : Real) ≠ 0))).2
    simpa [mul_comm] using hmean
  have hpHalf : p ≤ 1 / 2 := by
    rw [hp, div_le_iff₀ (by positivity : (0 : Real) < (4 * r : Nat))]
    have hHalfR : ((2 * Delta : Nat) : Real) ≤ (4 * r : Nat) := by
      exact_mod_cast hHalf
    norm_num [Nat.cast_mul] at hHalfR ⊢
    linarith
  have hlargeR : 3 ≤ p * A.card := by
    rw [hp]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity :
      (0 : Real) < (4 * r : Nat))]
    have hcast :
        (((12 * r : Nat) : Real) ≤ ((Delta * A.card : Nat) : Real)) := by
      exact_mod_cast (show 12 * r ≤ Delta * A.card by
        simpa [Nat.mul_comm] using hlarge)
    norm_num [Nat.cast_mul] at hcast ⊢
    linarith
  rw [supportWord_mem_code_eventMass r Delta hDelta A]
  apply pow_le_pow_left'
  exact ENNReal.ofReal_le_ofReal
    (parityProbabilityBase_veryLarge_le p A.card hpHalf hlargeR)

/-- Uniform fixed-support estimate once `p |A| ≥ 1`. -/
theorem supportWord_mem_code_eventMass_large_le
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r)
    (A : Finset (Fin (4 * r))) (hlarge : 4 * r ≤ A.card * Delta) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => supportWord A ∈ (code sample).carrier) ≤
      (ENNReal.ofReal ((4 : Real) / 7)) ^ (3 * r) := by
  let p : Real := (incidenceProbability (4 * r) Delta).toReal
  have hmean : ((4 * r : Nat) : Real) * p = Delta := by
    exact check_expected_degree r Delta hr
  have hp : p = (Delta : Real) / ((4 * r : Nat) : Real) := by
    apply (eq_div_iff (by positivity : (((4 * r : Nat) : Real) ≠ 0))).2
    simpa [mul_comm] using hmean
  have hpHalf : p ≤ 1 / 2 := by
    rw [hp, div_le_iff₀ (by positivity : (0 : Real) < (4 * r : Nat))]
    have hHalfR : ((2 * Delta : Nat) : Real) ≤ (4 * r : Nat) := by
      exact_mod_cast hHalf
    norm_num [Nat.cast_mul] at hHalfR ⊢
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
  rw [supportWord_mem_code_eventMass r Delta hDelta A]
  apply pow_le_pow_left'
  exact ENNReal.ofReal_le_ofReal
    (parityProbabilityBase_large_le p A.card hpHalf hlargeR)

/-- Supports of nonzero words violating the source's `0.2 n` distance bound. -/
def LowWeightSupport (r : Nat) :=
  {A : Finset (Fin (4 * r)) // A.Nonempty ∧ 5 * A.card < 4 * r}

noncomputable instance instFintypeLowWeightSupport (r : Nat) :
    Fintype (LowWeightSupport r) :=
  Fintype.subtype
    (Finset.univ.filter fun A : Finset (Fin (4 * r)) =>
      A.Nonempty ∧ 5 * A.card < 4 * r)
    (by simp)

/-- Every source-low-weight support has cardinality at most `⌊4r/5⌋`. -/
theorem lowWeightSupport_card_le
    {r : Nat} (A : LowWeightSupport r) :
    A.1.card ≤ (4 * r) / 5 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 5)).2
  have hle : 5 * A.1.card ≤ 4 * r := (Nat.le_of_lt A.2.2)
  simpa [Nat.mul_comm] using hle

/--
Weighted binomial count for all supports below the source's `0.2 n` cutoff.
This is an elementary entropy bound with the rational test weight `1/3`;
the floor is kept explicit, so no real-entropy approximation is assumed.
-/
theorem lowWeightSupport_card_cast_le
    (r : Nat) :
    (Fintype.card (LowWeightSupport r) : ENNReal) ≤
      (3 : ENNReal) ^ ((4 * r) / 5) *
        ((4 : ENNReal) / 3) ^ (4 * r) := by
  let k : Nat := (4 * r) / 5
  let x : ENNReal := (1 : ENNReal) / 3
  have hpoint (A : LowWeightSupport r) :
      (1 : ENNReal) ≤ (3 : ENNReal) ^ k * x ^ A.1.card := by
    have hcard : A.1.card ≤ k := lowWeightSupport_card_le A
    have hxle : x ≤ 1 := by
      dsimp [x]
      norm_num
    have hpow : x ^ k ≤ x ^ A.1.card :=
      pow_le_pow_right_of_le_one' hxle hcard
    calc
      (1 : ENNReal) =
          (3 : ENNReal) ^ k * x ^ k := by
            rw [← mul_pow]
            dsimp [x]
            rw [div_eq_mul_inv, one_mul,
              ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
      _ ≤ (3 : ENNReal) ^ k * x ^ A.1.card :=
        by gcongr
  have hsub :
      (∑ A : LowWeightSupport r, x ^ A.1.card) ≤
        ∑ A : Finset (Fin (4 * r)), x ^ A.card := by
    have hsplit :=
      Fintype.sum_subtype_add_sum_subtype
        (fun A : Finset (Fin (4 * r)) =>
          A.Nonempty ∧ 5 * A.card < 4 * r)
        (fun A => x ^ A.card)
    change
      (∑ A : {A : Finset (Fin (4 * r)) //
        A.Nonempty ∧ 5 * A.card < 4 * r}, x ^ A.1.card) ≤
        ∑ A : Finset (Fin (4 * r)), x ^ A.card
    rw [← hsplit]
    exact le_add_right le_rfl
  have hall :
      (∑ A : Finset (Fin (4 * r)), x ^ A.card) =
        (1 + x) ^ (4 * r) := by
    rw [← Finset.powerset_univ]
    simpa only [Fintype.card_fin, Finset.card_univ] using
      (sum_powerset_pow_card
        (Finset.univ : Finset (Fin (4 * r))) x)
  calc
    (Fintype.card (LowWeightSupport r) : ENNReal) =
        ∑ _A : LowWeightSupport r, (1 : ENNReal) := by simp
    _ ≤ ∑ A : LowWeightSupport r,
        (3 : ENNReal) ^ k * x ^ A.1.card := by
      exact Finset.sum_le_sum fun A _ => hpoint A
    _ = (3 : ENNReal) ^ k *
        ∑ A : LowWeightSupport r, x ^ A.1.card := by
      rw [Finset.mul_sum]
    _ ≤ (3 : ENNReal) ^ k *
        ∑ A : Finset (Fin (4 * r)), x ^ A.card :=
      by gcongr
    _ = (3 : ENNReal) ^ k * (1 + x) ^ (4 * r) := by
      rw [hall]
    _ = _ := by
      have hxsum : (1 + x : ENNReal) = 4 / 3 := by
        dsimp [x]
        calc
          (1 + (1 : ENNReal) / 3) =
              3 * 3⁻¹ + 1 * 3⁻¹ := by
                rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
                simp
          _ = (3 + 1) * 3⁻¹ := by rw [add_mul]
          _ = (4 : ENNReal) / 3 := by
            norm_num [div_eq_mul_inv]
      rw [hxsum]

/-- Nonempty variable supports, used to expose the missing empty-set term. -/
def NonemptyVariableSupport (r : Nat) :=
  {A : Finset (Fin (4 * r)) // A.Nonempty}

noncomputable instance instFintypeNonemptyVariableSupport (r : Nat) :
    Fintype (NonemptyVariableSupport r) :=
  Fintype.subtype
    (Finset.univ.filter fun A : Finset (Fin (4 * r)) => A.Nonempty)
    (by simp)

/-- Reassociate the two predicates defining a low-weight nonempty support. -/
def lowWeightSupportEquivSubtypeNonempty (r : Nat) :
    LowWeightSupport r ≃
      {A : NonemptyVariableSupport r // 5 * A.1.1.card < 4 * r} where
  toFun A := ⟨⟨A.1, A.2.1⟩, A.2.2⟩
  invFun A := ⟨A.1.1, A.1.2, A.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A low-weight-support sum is bounded by the sum over all nonempty supports. -/
theorem sum_lowWeightSupport_pow_card_le_nonempty
    (r : Nat) (t : ENNReal) :
    (∑ A : LowWeightSupport r, t ^ A.1.card) ≤
      ∑ A : NonemptyVariableSupport r, t ^ A.1.card := by
  let predicate : NonemptyVariableSupport r → Prop :=
    fun A => 5 * A.1.card < 4 * r
  let summand : NonemptyVariableSupport r → ENNReal :=
    fun A => t ^ A.1.card
  have heq :
      (∑ A : LowWeightSupport r, t ^ A.1.card) =
        ∑ A : {A : NonemptyVariableSupport r // predicate A},
          summand A.1 := by
    exact Fintype.sum_equiv
      (lowWeightSupportEquivSubtypeNonempty r)
      (fun A : LowWeightSupport r => t ^ A.1.card)
      (fun A : {A : NonemptyVariableSupport r // predicate A} =>
        summand A.1)
      (fun _ => rfl)
  rw [heq]
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype predicate summand
  rw [← hsplit]
  exact le_add_right le_rfl

/-- Exact binomial sum over all nonempty variable supports. -/
theorem sum_nonemptyVariableSupport_pow_card
    (r : Nat) (t : ENNReal) :
    (∑ A : NonemptyVariableSupport r, t ^ A.1.card) =
      (1 + t) ^ (4 * r) - 1 := by
  simpa only [NonemptyVariableSupport, Fintype.card_fin] using
    (sum_nonempty_finset_pow_card (α := Fin (4 * r)) t)

/-- A failed linear-distance event supplies a concrete low-weight support. -/
theorem exists_lowWeightSupport_mem_code_of_not_hasLinearDistance
    {r : Nat} {sample : Sample r}
    (h : ¬HasLinearDistance sample) :
    ∃ A : LowWeightSupport r,
      supportWord A.1 ∈ (code sample).carrier := by
  classical
  rw [HasLinearDistance] at h
  push Not at h
  rcases h with ⟨x, hxCode, hx0, hxWeight⟩
  let A := hammingSupport x
  have hAne : A.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have hWeightZero : HammingWeight x = 0 := by
      rw [HammingWeight_eq_card_hammingSupport, show hammingSupport x = A from rfl,
        hEmpty]
      simp
    exact hx0 ((HammingWeight_eq_zero_iff x).mp hWeightZero)
  have hAWeight : 5 * A.card < 4 * r := by
    simpa [A, HammingWeight_eq_card_hammingSupport] using hxWeight
  refine ⟨⟨A, hAne, hAWeight⟩, ?_⟩
  rw [supportWord_hammingSupport]
  exact hxCode

noncomputable instance instDecidablePredHasLinearDistance (r : Nat) :
    DecidablePred (@HasLinearDistance r) :=
  Classical.decPred _

/--
Exact low-support union bound for failure of the source's classical
linear-distance event.  The next analytic layer estimates this finite sum;
the reduction itself makes no counting assumption.
-/
theorem linearDistance_failureMass_le_exact_sum
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (@HasLinearDistance r) ≤
      ∑ A : LowWeightSupport r,
        (ENNReal.ofReal
          ((1 +
            (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^
              A.1.card) / 2)) ^ (3 * r) := by
  calc
    _ ≤ ∑ A : LowWeightSupport r,
        eventMass
          (distribution r Delta hDelta)
          (fun sample => supportWord A.1 ∈ (code sample).carrier) := by
      apply failureMass_le_sum_eventMass
      intro sample hsample
      exact exists_lowWeightSupport_mem_code_of_not_hasLinearDistance hsample
    _ = _ := by
      apply Fintype.sum_congr
      intro A
      exact supportWord_mem_code_eventMass r Delta hDelta A.1

/--
Fully counted small/very-large split for the HHO20 classical-distance event.

The first term sums the geometric estimate over every nonempty support.  The
second uses the rational `1/3` weighted count of all supports below `0.2n`
and the `172/343` parity base valid once `Delta |A| ≥ 12r`.
-/
theorem linearDistance_failureMass_le_split
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (@HasLinearDistance r) ≤
      (1 + ENNReal.ofReal
        (Real.exp (-(3 : Real) * Delta / 28))) ^ (4 * r) - 1 +
      ((3 : ENNReal) ^ ((4 * r) / 5) *
        ((4 : ENNReal) / 3) ^ (4 * r)) *
        (ENNReal.ofReal ((172 : Real) / 343)) ^ (3 * r) := by
  let t : ENNReal :=
    ENNReal.ofReal (Real.exp (-(3 : Real) * Delta / 28))
  let c : ENNReal :=
    (ENNReal.ofReal ((172 : Real) / 343)) ^ (3 * r)
  calc
    _ ≤
        ∑ A : LowWeightSupport r,
          (ENNReal.ofReal
            ((1 +
              (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^
                A.1.card) / 2)) ^ (3 * r) :=
      linearDistance_failureMass_le_exact_sum r Delta hDelta
    _ = ∑ A : LowWeightSupport r,
        eventMass
          (distribution r Delta hDelta)
          (fun sample => supportWord A.1 ∈ (code sample).carrier) := by
      apply Fintype.sum_congr
      intro A
      exact (supportWord_mem_code_eventMass r Delta hDelta A.1).symm
    _ ≤ ∑ A : LowWeightSupport r, (t ^ A.1.card + c) := by
      apply Finset.sum_le_sum
      intro A _
      by_cases hmedium : A.1.card * Delta ≤ 12 * r
      · exact
          (supportWord_mem_code_eventMass_medium_geometric_le
            r Delta hr hDelta hHalf A.1 hmedium).trans
            (le_add_right le_rfl)
      · have hlarge : 12 * r ≤ A.1.card * Delta :=
          (Nat.lt_of_not_ge hmedium).le
        exact
          (supportWord_mem_code_eventMass_veryLarge_le
            r Delta hr hDelta hHalf A.1 hlarge).trans
            (le_add_left le_rfl)
    _ =
        (∑ A : LowWeightSupport r, t ^ A.1.card) +
          ∑ _A : LowWeightSupport r, c := by
      exact Finset.sum_add_distrib
    _ ≤
        ((1 + t) ^ (4 * r) - 1) +
          ((3 : ENNReal) ^ ((4 * r) / 5) *
            ((4 : ENNReal) / 3) ^ (4 * r)) * c := by
      gcongr
      · exact (sum_lowWeightSupport_pow_card_le_nonempty r t).trans_eq
          (sum_nonemptyVariableSupport_pow_card r t)
      · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        gcongr
        exact lowWeightSupport_card_cast_le r
    _ = _ := rfl

/-- Failure of a conjunction is covered by failure of either component. -/
theorem failureMass_and_le
    {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (left right : Ω → Prop)
    [DecidablePred left] [DecidablePred right]
    [DecidablePred fun ω => left ω ∧ right ω] :
    failureMass p (fun ω => left ω ∧ right ω) ≤
      failureMass p left + failureMass p right := by
  rw [failureMass_eq_toMeasure, failureMass_eq_toMeasure,
    failureMass_eq_toMeasure]
  calc
    p.toMeasure {ω | ¬(left ω ∧ right ω)} ≤
        p.toMeasure ({ω | ¬left ω} ∪ {ω | ¬right ω}) := by
      apply measure_mono
      intro ω hω
      simp only [Set.mem_setOf_eq, Set.mem_union]
      tauto
    _ ≤ p.toMeasure {ω | ¬left ω} +
        p.toMeasure {ω | ¬right ω} :=
      measure_union_le _ _

/-- The finite failure mass is independent of the chosen decision procedure. -/
theorem failureMass_decidable_irrel
    {Ω : Type*} [Fintype Ω]
    (p : PMF Ω) (event : Ω → Prop)
    (d₁ d₂ : DecidablePred event) :
    @failureMass Ω inferInstance p event d₁ =
      @failureMass Ω inferInstance p event d₂ := by
  unfold failureMass
  exact eventMass_decidable_irrel p (fun ω => ¬event ω) _ _

noncomputable instance instDecidablePredHasDegreeWindows
    (r Delta : Nat) :
    DecidablePred
      (fun sample : Sample r => HasDegreeWindows (Delta := Delta) sample) :=
  Classical.decPred _

noncomputable instance instDecidablePredIsGood
    (r Delta : Nat) :
    DecidablePred
      (fun sample : Sample r => IsGood (Delta := Delta) sample) :=
  Classical.decPred _

/--
The three random-base conclusions fail only if the degree, full-rank, or
linear-distance component fails.  This is the probability-level conjunction
bridge used before instantiating the explicit tail bounds.
-/
theorem isGood_failureMass_le_components
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample => IsGood (Delta := Delta) sample) ≤
      failureMass
          (distribution r Delta hDelta)
          (fun sample => HasDegreeWindows (Delta := Delta) sample) +
        failureMass
          (distribution r Delta hDelta)
          (@HasFullRowRank r) +
        failureMass
          (distribution r Delta hDelta)
          (@HasLinearDistance r) := by
  let p := distribution r Delta hDelta
  calc
    _ ≤ failureMass p
          (fun sample => HasDegreeWindows (Delta := Delta) sample) +
        failureMass p
          (fun sample => HasFullRowRank sample ∧ HasLinearDistance sample) := by
      have h := failureMass_and_le p
        (fun sample => HasDegreeWindows (Delta := Delta) sample)
        (fun sample => HasFullRowRank sample ∧ HasLinearDistance sample)
      simpa only [IsGood, p] using
        (failureMass_decidable_irrel p
          (fun sample =>
            HasDegreeWindows (Delta := Delta) sample ∧
              HasFullRowRank sample ∧ HasLinearDistance sample)
          _ _).le.trans h
    _ ≤ failureMass p
          (fun sample => HasDegreeWindows (Delta := Delta) sample) +
        (failureMass p (@HasFullRowRank r) +
          failureMass p (@HasLinearDistance r)) := by
      gcongr
      exact failureMass_and_le p (@HasFullRowRank r) (@HasLinearDistance r)
    _ = _ := by
      simp only [p]
      ac_rfl

/--
Explicit combined failure bound for the construction-owned random base.
Every term on the right was derived from the Bernoulli sampler; none is a
caller-supplied rank, distance, or degree certificate.
-/
theorem isGood_failureMass_le_explicit
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample => IsGood (Delta := Delta) sample) ≤
      ENNReal.ofReal
          ((14 * r : Real) * Real.exp (-(Delta : Real) / 40000)) +
        ((1 + ENNReal.ofReal
          (Real.exp (-(Delta : Real) / 2))) ^ (3 * r) - 1 +
          (2 : ENNReal) ^ (3 * r) *
            (ENNReal.ofReal ((4 : Real) / 7)) ^ (4 * r)) +
        ((1 + ENNReal.ofReal
          (Real.exp (-(3 : Real) * Delta / 28))) ^ (4 * r) - 1 +
          ((3 : ENNReal) ^ ((4 * r) / 5) *
            ((4 : ENNReal) / 3) ^ (4 * r)) *
            (ENNReal.ofReal ((172 : Real) / 343)) ^ (3 * r)) := by
  calc
    _ ≤
        failureMass
            (distribution r Delta hDelta)
            (fun sample => HasDegreeWindows (Delta := Delta) sample) +
          failureMass
            (distribution r Delta hDelta)
            (@HasFullRowRank r) +
          failureMass
            (distribution r Delta hDelta)
            (@HasLinearDistance r) :=
      isGood_failureMass_le_components r Delta hDelta
    _ ≤ _ := by
      gcongr
      · exact degreeWindows_failureMass_le r Delta hr hDelta
      · exact fullRowRank_failureMass_le_split
          r Delta hr hDelta hHalf
      · exact linearDistance_failureMass_le_split
          r Delta hr hDelta hHalf

end QEC.Coding.FiberBundle.RandomBase
