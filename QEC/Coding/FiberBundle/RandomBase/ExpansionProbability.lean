import QEC.Coding.FiberBundle.RandomBase.Expansion

/-!
# Probability closure for HHO20 small-set expansion

Containment events alone overcount a small realized neighborhood by all of its
supersets.  This module instead factors the event that the neighborhood is
*exactly* a selected variable set.  Variables inside the set must be hit and
variables outside it must be avoided, exposing the occupancy factor required
for a convergent union bound.
-/

namespace QEC.Coding.FiberBundle.RandomBase

open scoped BigOperators
open MeasureTheory

/-- A sampled column has no incidence from the selected checks. -/
def ColumnAvoids {r : Nat}
    (S : Finset (Fin (3 * r))) (column : ColumnSample r) : Prop :=
  ∀ a : Fin (3 * r), if a ∈ S then column a = false else True

/-- A sampled column is hit by at least one selected check. -/
def ColumnHits {r : Nat}
    (S : Finset (Fin (3 * r))) (column : ColumnSample r) : Prop :=
  ∃ a ∈ S, column a = true

instance instDecidablePredColumnAvoids
    {r : Nat} (S : Finset (Fin (3 * r))) :
    DecidablePred (ColumnAvoids S) := by
  intro column
  unfold ColumnAvoids
  infer_instance

instance instDecidablePredColumnHits
    {r : Nat} (S : Finset (Fin (3 * r))) :
    DecidablePred (ColumnHits S) := by
  intro column
  unfold ColumnHits
  infer_instance

/-- Being hit is exactly the complement of avoiding all selected checks. -/
theorem columnHits_iff_not_columnAvoids
    {r : Nat} (S : Finset (Fin (3 * r)))
    (column : ColumnSample r) :
    ColumnHits S column ↔ ¬ColumnAvoids S column := by
  constructor
  · rintro ⟨a, haS, haTrue⟩ hAvoids
    have haFalse := hAvoids a
    rw [if_pos haS] at haFalse
    simp [haTrue] at haFalse
  · intro hAvoids
    rw [ColumnAvoids] at hAvoids
    push Not at hAvoids
    rcases hAvoids with ⟨a, ha⟩
    by_cases haS : a ∈ S
    · rw [if_pos haS] at ha
      have haTrue : column a = true := by
        cases hbit : column a
        · simp [hbit] at ha
        · rfl
      exact ⟨a, haS, haTrue⟩
    · rw [if_neg haS] at ha
      exact (ha trivial).elim

/-- Exact probability that a sampled column avoids all checks in `S`. -/
theorem columnAvoids_eventMass
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r))) :
    eventMass
        (columnDistribution r Delta hDelta)
        (ColumnAvoids S) =
      (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
        S.card) := by
  classical
  let coordinateEvent : Fin (3 * r) → Bool → Prop :=
    fun a bit => if a ∈ S then bit = false else True
  calc
    _ = eventMass
        (columnDistribution r Delta hDelta)
        (fun column => ∀ a : Fin (3 * r), coordinateEvent a (column a)) := by
      apply eventMass_congr
      intro column
      rfl
    _ = ∏ a : Fin (3 * r),
        eventMass
          (PMF.bernoulli
            (incidenceProbability (4 * r) Delta)
            (incidenceProbability_le_one hDelta))
          (coordinateEvent a) := by
      rw [columnDistribution]
      have hProduct := eventMass_independentProduct_forall
        (fun _ : Fin (3 * r) =>
          PMF.bernoulli
            (incidenceProbability (4 * r) Delta)
            (incidenceProbability_le_one hDelta))
        coordinateEvent
      exact (eventMass_decidable_irrel
        (independentProduct fun _ : Fin (3 * r) =>
          PMF.bernoulli
            (incidenceProbability (4 * r) Delta)
            (incidenceProbability_le_one hDelta))
        (fun column => ∀ a : Fin (3 * r), coordinateEvent a (column a))
        _ _).trans hProduct
    _ = ∏ a : Fin (3 * r),
        if a ∈ S then
          ((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal)
        else 1 := by
      apply Fintype.prod_congr
      intro a
      by_cases haS : a ∈ S
      · rw [if_pos haS]
        calc
          eventMass
              (PMF.bernoulli
                (incidenceProbability (4 * r) Delta)
                (incidenceProbability_le_one hDelta))
              (coordinateEvent a) =
            eventMass
              (PMF.bernoulli
                (incidenceProbability (4 * r) Delta)
                (incidenceProbability_le_one hDelta))
              (fun bit => bit = false) := by
            apply eventMass_congr
            intro bit
            dsimp [coordinateEvent]
            rw [if_pos haS]
          _ = _ := bernoulli_false_eventMass
            (incidenceProbability (4 * r) Delta)
            (incidenceProbability_le_one hDelta)
      · rw [if_neg haS]
        calc
          eventMass
              (PMF.bernoulli
                (incidenceProbability (4 * r) Delta)
                (incidenceProbability_le_one hDelta))
              (coordinateEvent a) =
            eventMass
              (PMF.bernoulli
                (incidenceProbability (4 * r) Delta)
                (incidenceProbability_le_one hDelta))
              (fun _bit => True) := by
            apply eventMass_congr
            intro bit
            dsimp [coordinateEvent]
            rw [if_neg haS]
          _ = _ := bernoulli_true_eventMass
            (incidenceProbability (4 * r) Delta)
            (incidenceProbability_le_one hDelta)
    _ = ∏ _a ∈ S,
        ((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) := by
      rw [Finset.prod_ite]
      simp
    _ = _ := by simp

/-- Exact probability that a sampled column is hit by `S`. -/
theorem columnHits_eventMass
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r))) :
    eventMass
        (columnDistribution r Delta hDelta)
        (ColumnHits S) =
      1 -
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          S.card) := by
  have hTotal :=
    eventMass_add_failureMass
      (columnDistribution r Delta hDelta)
      (ColumnAvoids S)
  have hComplement :
      failureMass
          (columnDistribution r Delta hDelta)
          (ColumnAvoids S) =
        eventMass
          (columnDistribution r Delta hDelta)
          (ColumnHits S) := by
    unfold failureMass
    exact eventMass_congr
      (columnDistribution r Delta hDelta)
      (fun column => ¬ColumnAvoids S column)
      (ColumnHits S)
      (fun column => (columnHits_iff_not_columnAvoids S column).symm)
  rw [hComplement, columnAvoids_eventMass] at hTotal
  let q : ENNReal :=
    (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
      S.card)
  change eventMass
      (columnDistribution r Delta hDelta)
      (ColumnHits S) = 1 - q
  have hTotalQ :
      q + eventMass
        (columnDistribution r Delta hDelta)
        (ColumnHits S) = 1 := by
    simpa [q] using hTotal
  have hqTop : q ≠ ⊤ := by
    exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  apply (ENNReal.add_left_inj hqTop).mp
  rw [tsub_add_cancel_of_le]
  · simpa [add_comm] using hTotalQ
  · rw [← hTotalQ]
    exact le_add_right le_rfl

/--
The probability that at least one of `n` Bernoulli coordinates is hit is at
most `n p`.  This is Bernoulli's inequality expressed in the `ENNReal` form
used by finite event masses.
-/
theorem one_sub_coe_one_sub_pow_le
    (p : NNReal) (hp : p ≤ 1) (n : Nat) :
    1 - (((1 - p : NNReal) : ENNReal) ^ n) ≤
      (n : ENNReal) * (p : ENNReal) := by
  have hq :
      (((1 - p : NNReal) : ENNReal) ^ n) ≤ 1 := by
    exact pow_le_one₀ (by positivity) (by simp)
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_sub_of_le hq (by simp)]
  simp only [ENNReal.toReal_one, ENNReal.toReal_pow, ENNReal.coe_toReal,
    ENNReal.toReal_mul, ENNReal.toReal_natCast]
  rw [NNReal.coe_sub hp]
  have hBernoulli :
      1 + (n : Real) * ((1 - (p : Real)) - 1) ≤
        (1 - (p : Real)) ^ n := by
    apply one_add_mul_sub_le_pow
    have hpNonneg : (0 : Real) ≤ p := by positivity
    linarith
  norm_num at hBernoulli ⊢
  linarith

/--
A second-order lower bound for a Bernoulli union.  Unlike an asymptotic
Taylor estimate, this holds for every finite `n` and every `p ≤ 1`.
-/
theorem nnreal_mul_one_sub_mul_le_one_sub_one_sub_pow
    (p : NNReal) (hp : p ≤ 1) (n : Nat) :
    (n : NNReal) * p * (1 - (n : NNReal) * p) ≤
      1 - (1 - p : NNReal) ^ n := by
  let q : NNReal := 1 - p
  have hq_le_one : q ≤ 1 := by
    dsimp [q]
    exact tsub_le_self
  have hqpow_lower :
      1 - (n : NNReal) * p ≤ q ^ n := by
    by_cases hnp : (n : NNReal) * p ≤ 1
    · change
        (((1 - (n : NNReal) * p : NNReal) : Real) ≤
          ((q ^ n : NNReal) : Real))
      rw [NNReal.coe_sub hnp]
      have hBernoulli :
          1 + (n : Real) * ((q : Real) - 1) ≤ (q : Real) ^ n := by
        apply one_add_mul_sub_le_pow
        have hqNonneg : (0 : Real) ≤ q := by positivity
        linarith
      have hqReal : (q : Real) = 1 - (p : Real) := by
        dsimp [q]
        rw [NNReal.coe_sub hp]
        norm_num
      norm_num only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow]
      rw [hqReal] at hBernoulli ⊢
      norm_num at hBernoulli ⊢
      linarith
    · have hnp' : 1 ≤ (n : NNReal) * p := le_of_not_ge hnp
      rw [tsub_eq_zero_of_le hnp']
      exact bot_le
  have hsum_lower :
      (n : NNReal) * q ^ n ≤
        ∑ i ∈ Finset.range n, q ^ i := by
    calc
      (n : NNReal) * q ^ n =
          ∑ _i ∈ Finset.range n, q ^ n := by
            simp [nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.range n, q ^ i := by
        exact Finset.sum_le_sum fun i hi =>
          pow_le_pow_right_of_le_one'
            hq_le_one
            (Nat.le_of_lt (Finset.mem_range.mp hi))
  have hgeom :
      (∑ i ∈ Finset.range n, q ^ i) * p =
        1 - q ^ n := by
    have hqComplement : 1 - q = p := by
      dsimp [q]
      exact tsub_tsub_cancel_of_le hp
    simpa only [hqComplement] using
      (geom_sum_mul_of_le_one hq_le_one n)
  calc
    (n : NNReal) * p * (1 - (n : NNReal) * p) ≤
        (n : NNReal) * p * q ^ n := by
      exact mul_le_mul_of_nonneg_left hqpow_lower (by positivity)
    _ = ((n : NNReal) * q ^ n) * p := by ring
    _ ≤ (∑ i ∈ Finset.range n, q ^ i) * p := by
      exact mul_le_mul_of_nonneg_right hsum_lower (by positivity)
    _ = 1 - q ^ n := hgeom
    _ = 1 - (1 - p : NNReal) ^ n := rfl

/-- The elementary finite-power exponential envelope `(1 - x)^n ≤ exp(-nx)`. -/
theorem coe_one_sub_pow_le_ofReal_exp_neg
    (x : NNReal) (hx : x ≤ 1) (n : Nat) :
    (((1 - x : NNReal) : ENNReal) ^ n) ≤
      ENNReal.ofReal (Real.exp (-(n : Real) * (x : Real))) := by
  have hxReal : (x : Real) ≤ 1 := by
    exact_mod_cast hx
  have hbaseNonneg : (0 : Real) ≤ 1 - (x : Real) := by
    linarith
  have hbase :
      1 - (x : Real) ≤ Real.exp (-(x : Real)) := by
    linarith [Real.add_one_le_exp (-(x : Real))]
  have hReal :
      (1 - (x : Real)) ^ n ≤
        Real.exp (-(n : Real) * (x : Real)) := by
    calc
      (1 - (x : Real)) ^ n ≤
          (Real.exp (-(x : Real))) ^ n := by
        exact pow_le_pow_left₀ hbaseNonneg hbase n
      _ = Real.exp (-(n : Real) * (x : Real)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  rw [← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  simpa only [NNReal.coe_pow, NNReal.coe_sub hx, NNReal.coe_one] using hReal

/-- The reciprocal test-weight cost is bounded by its elementary exponential envelope. -/
theorem twenty_nineteenths_pow_le_exp (n : Nat) :
    ((20 : ENNReal) / 19) ^ n ≤
      ENNReal.ofReal (Real.exp ((n : Real) / 19)) := by
  have hbaseReal :
      (20 : Real) / 19 ≤ Real.exp ((1 : Real) / 19) := by
    have hExp := Real.add_one_le_exp ((1 : Real) / 19)
    norm_num at hExp ⊢
    linarith
  have hbase :
      (20 : ENNReal) / 19 ≤
        ENNReal.ofReal (Real.exp ((1 : Real) / 19)) := by
    have hWeightEq :
        (((20 : NNReal) / 19 : NNReal) : ENNReal) =
          (20 : ENNReal) / 19 :=
      ENNReal.coe_div (by norm_num)
    rw [← hWeightEq, ← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    simpa only [NNReal.coe_div, NNReal.coe_ofNat] using hbaseReal
  calc
    ((20 : ENNReal) / 19) ^ n ≤
        (ENNReal.ofReal (Real.exp ((1 : Real) / 19))) ^ n := by
      exact pow_le_pow_left' hbase n
    _ = ENNReal.ofReal
        ((Real.exp ((1 : Real) / 19)) ^ n) := by
      rw [ENNReal.ofReal_pow (Real.exp_pos _).le]
    _ = ENNReal.ofReal (Real.exp ((n : Real) / 19)) := by
      congr 1
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/--
The HHO20 small-set cutoff forces the expected incidence load of a selected
check set below `3 / 400000`.
-/
theorem card_mul_incidenceProbability_le_of_small
    (r Delta : Nat) (hr : 0 < r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    (S.card : NNReal) * incidenceProbability (4 * r) Delta ≤
      (3 : NNReal) / 400000 := by
  have hExpected :=
    check_expected_degree r Delta hr
  have hSmallReal :
      (100000 : Real) * Delta * S.card ≤ 3 * r := by
    exact_mod_cast hSmall
  have hrReal : (0 : Real) < r := by
    exact_mod_cast hr
  change
    (S.card : Real) *
        (incidenceProbability (4 * r) Delta).toReal ≤
      (3 : Real) / 400000
  rw [mul_comm]
  rw [← hExpected] at hSmallReal
  norm_num [Nat.cast_mul] at hSmallReal
  nlinarith

/--
For an HHO20-small check set, the probability that a variable is hit is at
least `399997 / 400000` times its first-order incidence load.
-/
theorem hitProbability_lower_of_small
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    (399997 : NNReal) / 400000 *
        ((S.card : NNReal) * incidenceProbability (4 * r) Delta) ≤
      1 -
        (1 - incidenceProbability (4 * r) Delta : NNReal) ^ S.card := by
  let load : NNReal :=
    (S.card : NNReal) * incidenceProbability (4 * r) Delta
  have hload : load ≤ (3 : NNReal) / 400000 := by
    exact card_mul_incidenceProbability_le_of_small
      r Delta hr S hSmall
  have hthree : (3 : NNReal) / 400000 ≤ 1 := by
    apply div_le_one_of_le₀
    · norm_num
    · exact bot_le
  have hloadOne : load ≤ 1 := hload.trans hthree
  have hComplement :
      (399997 : NNReal) / 400000 ≤ 1 - load := by
    apply (le_tsub_iff_right hloadOne).2
    calc
      (399997 : NNReal) / 400000 + load ≤
          (399997 : NNReal) / 400000 + 3 / 400000 := by
        simpa only [add_comm] using
          add_le_add_left hload ((399997 : NNReal) / 400000)
      _ = 1 := by norm_num
  have hSecondOrder :=
    nnreal_mul_one_sub_mul_le_one_sub_one_sub_pow
      (incidenceProbability (4 * r) Delta)
      (incidenceProbability_le_one hDelta)
      S.card
  change
    (399997 : NNReal) / 400000 * load ≤
      1 -
        (1 - incidenceProbability (4 * r) Delta : NNReal) ^ S.card
  calc
    (399997 : NNReal) / 400000 * load ≤ load * (1 - load) := by
      rw [mul_comm ((399997 : NNReal) / 400000) load]
      exact mul_le_mul_of_nonneg_left hComplement (by positivity)
    _ ≤ _ := by
      simpa only [load] using hSecondOrder

/--
At the test weight `19 / 20`, the fixed-set generating-function base has a
strict first-order deficit controlled by the selected incidence load.
-/
theorem nineteen_twentieths_generatorBase_le_of_small
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    (19 : NNReal) / 20 *
          (1 -
            (1 - incidenceProbability (4 * r) Delta : NNReal) ^ S.card) +
        (1 - incidenceProbability (4 * r) Delta : NNReal) ^ S.card ≤
      1 -
        (1 : NNReal) / 20 *
          ((399997 : NNReal) / 400000 *
            ((S.card : NNReal) *
              incidenceProbability (4 * r) Delta)) := by
  let avoid : NNReal :=
    (1 - incidenceProbability (4 * r) Delta : NNReal) ^ S.card
  let hit : NNReal := 1 - avoid
  let load : NNReal :=
    (S.card : NNReal) * incidenceProbability (4 * r) Delta
  let penalty : NNReal :=
    (1 : NNReal) / 20 * ((399997 : NNReal) / 400000 * load)
  have hAvoid : avoid ≤ 1 := by
    dsimp [avoid]
    exact pow_le_one₀ (by positivity) (by simp)
  have hHit : (399997 : NNReal) / 400000 * load ≤ hit := by
    exact hitProbability_lower_of_small
      r Delta hr hDelta S hSmall
  have honeTwentieth : (1 : NNReal) / 20 ≤ 1 := by
    apply div_le_one_of_le₀
    · norm_num
    · exact bot_le
  have hPenaltyHit : penalty ≤ hit := by
    calc
      penalty ≤ 1 * ((399997 : NNReal) / 400000 * load) := by
        dsimp [penalty]
        gcongr
      _ = _ := by simp
      _ ≤ hit := hHit
  have hPenaltyOne : penalty ≤ 1 :=
    hPenaltyHit.trans tsub_le_self
  change (19 : NNReal) / 20 * hit + avoid ≤ 1 - penalty
  apply (le_tsub_iff_left hPenaltyOne).2
  calc
    penalty + ((19 : NNReal) / 20 * hit + avoid) ≤
        (1 : NNReal) / 20 * hit +
          ((19 : NNReal) / 20 * hit + avoid) := by
      have hScaled :
          (1 : NNReal) / 20 *
              ((399997 : NNReal) / 400000 * load) ≤
            (1 : NNReal) / 20 * hit :=
        mul_le_mul_of_nonneg_left hHit (by positivity)
      have hPenaltyScaled :
          penalty ≤ (1 : NNReal) / 20 * hit := by
        simpa only [penalty] using hScaled
      simpa only [add_comm] using
        add_le_add_right hPenaltyScaled
          ((19 : NNReal) / 20 * hit + avoid)
    _ = (((1 : NNReal) / 20) + 19 / 20) * hit + avoid := by
      ring
    _ = hit + avoid := by norm_num
    _ = 1 := by
      exact tsub_add_cancel_of_le hAvoid

/--
Exact two-weight binomial enumeration of subsets.  It is used to sum
neighborhood occupancy masses after applying an exponential test weight.
-/
theorem sum_powerset_pow_card_mul_pow_card_sub
    {α : Type*} [DecidableEq α]
    (carrier : Finset α) (hit avoid : ENNReal) :
    ∑ T ∈ carrier.powerset,
        hit ^ T.card * avoid ^ (carrier.card - T.card) =
      (hit + avoid) ^ carrier.card := by
  rw [Finset.sum_powerset_apply_card
    (fun cardinality =>
      hit ^ cardinality * avoid ^ (carrier.card - cardinality))]
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro cardinality _hCardinality
  simp only [nsmul_eq_mul]
  ac_rfl

/-- The regrouped sample has exactly the variable neighborhood `T`. -/
def GroupedExactNeighborhood {r : Nat}
    (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r)))
    (grouped : GroupedSample r) : Prop :=
  ∀ b : Fin (4 * r),
    if b ∈ T then ColumnHits S (grouped b)
    else ColumnAvoids S (grouped b)

instance instDecidablePredGroupedExactNeighborhood
    {r : Nat} (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    DecidablePred (GroupedExactNeighborhood S T) := by
  intro grouped
  unfold GroupedExactNeighborhood
  infer_instance

/-- Regrouping identifies exact-neighborhood and per-column hit/avoid events. -/
theorem checkSetNeighborhood_eq_iff_groupedExactNeighborhood
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    checkSetNeighborhood sample S = T ↔
      GroupedExactNeighborhood S T (sampleEquivGrouped r sample) := by
  constructor
  · intro h b
    by_cases hbT : b ∈ T
    · rw [if_pos hbT]
      rw [← h] at hbT
      have hbCount := (Finset.mem_filter.mp hbT).2
      have hNonempty :
          (S.filter fun a => sample (a, b)).Nonempty :=
        Finset.card_pos.mp hbCount
      rcases hNonempty with ⟨a, ha⟩
      exact ⟨a, (Finset.mem_filter.mp ha).1,
        (Finset.mem_filter.mp ha).2⟩
    · rw [if_neg hbT]
      intro a
      by_cases haS : a ∈ S
      · rw [if_pos haS]
        apply Bool.eq_false_iff.mpr
        intro haTrue
        have hbNeighborhood : b ∈ checkSetNeighborhood sample S := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          apply Finset.card_pos.mpr
          exact ⟨a, Finset.mem_filter.mpr ⟨haS, haTrue⟩⟩
        exact hbT (h ▸ hbNeighborhood)
      · rw [if_neg haS]
        trivial
  · intro h
    ext b
    constructor
    · intro hb
      by_contra hbT
      have hAvoids := h b
      rw [if_neg hbT] at hAvoids
      have hbCount := (Finset.mem_filter.mp hb).2
      have hNonempty :
          (S.filter fun a => sample (a, b)).Nonempty :=
        Finset.card_pos.mp hbCount
      rcases hNonempty with ⟨a, ha⟩
      have haFalse := hAvoids a
      rw [if_pos (Finset.mem_filter.mp ha).1] at haFalse
      have haTrue := (Finset.mem_filter.mp ha).2
      change sample (a, b) = false at haFalse
      rw [haTrue] at haFalse
      contradiction
    · intro hbT
      have hHits := h b
      rw [if_pos hbT] at hHits
      rcases hHits with ⟨a, haS, haTrue⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Finset.card_pos.mpr
      exact ⟨a, Finset.mem_filter.mpr ⟨haS, haTrue⟩⟩

instance instDecidablePredExactNeighborhood
    {r : Nat} (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    DecidablePred
      (fun sample : Sample r => checkSetNeighborhood sample S = T) := by
  intro sample
  infer_instance

/-- Exact probability that `S` has variable neighborhood exactly `T`. -/
theorem exactNeighborhood_eventMass
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => checkSetNeighborhood sample S = T) =
      (1 -
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          S.card)) ^ T.card *
      (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
        S.card) ^ (4 * r - T.card) := by
  classical
  let q : ENNReal :=
    (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
      S.card)
  let coordinateEvent : Fin (4 * r) → ColumnSample r → Prop :=
    fun b column =>
      if b ∈ T then ColumnHits S column else ColumnAvoids S column
  calc
    _ = eventMass
        (groupedDistribution r Delta hDelta)
        (GroupedExactNeighborhood S T) := by
      exact eventMass_equiv
        (sampleEquivGrouped r)
        (distribution r Delta hDelta)
        (groupedDistribution r Delta hDelta)
        (fun sample => checkSetNeighborhood sample S = T)
        (GroupedExactNeighborhood S T)
        (distribution_apply_eq_grouped r Delta hDelta)
        (checkSetNeighborhood_eq_iff_groupedExactNeighborhood · S T)
    _ = ∏ b : Fin (4 * r),
        eventMass
          (columnDistribution r Delta hDelta)
          (coordinateEvent b) := by
      rw [groupedDistribution]
      have hProduct := eventMass_independentProduct_forall
        (fun _ : Fin (4 * r) => columnDistribution r Delta hDelta)
        coordinateEvent
      exact (eventMass_decidable_irrel
        (independentProduct fun _ : Fin (4 * r) =>
          columnDistribution r Delta hDelta)
        (GroupedExactNeighborhood S T)
        _ _).trans hProduct
    _ = ∏ b : Fin (4 * r), if b ∈ T then 1 - q else q := by
      apply Fintype.prod_congr
      intro b
      by_cases hbT : b ∈ T
      · rw [if_pos hbT]
        calc
          eventMass
              (columnDistribution r Delta hDelta)
              (coordinateEvent b) =
            eventMass
              (columnDistribution r Delta hDelta)
              (ColumnHits S) := by
            apply eventMass_congr
            intro column
            dsimp [coordinateEvent]
            rw [if_pos hbT]
          _ = 1 - q := by
            simpa [q] using columnHits_eventMass r Delta hDelta S
      · rw [if_neg hbT]
        calc
          eventMass
              (columnDistribution r Delta hDelta)
              (coordinateEvent b) =
            eventMass
              (columnDistribution r Delta hDelta)
              (ColumnAvoids S) := by
            apply eventMass_congr
            intro column
            dsimp [coordinateEvent]
            rw [if_neg hbT]
          _ = q := by
            simpa [q] using columnAvoids_eventMass r Delta hDelta S
    _ = (1 - q) ^ T.card * q ^ (4 * r - T.card) := by
      have hIn :
          ((Finset.univ : Finset (Fin (4 * r))).filter
            (fun b => b ∈ T)).card = T.card := by
        simp
      have hOut :
          ((Finset.univ : Finset (Fin (4 * r))).filter
            (fun b => b ∉ T)).card = 4 * r - T.card := by
        rw [← Finset.sdiff_eq_filter, Finset.card_sdiff]
        simp
      rw [Finset.prod_ite]
      simp only [Finset.prod_const]
      rw [hIn, hOut]
    _ = _ := rfl

/--
Exact probability-generating function of the neighborhood size of a fixed
check set.  It is derived from the construction-owned sample distribution and
the exact-neighborhood partition, not postulated as a binomial law.
-/
theorem sum_weight_pow_mul_exactNeighborhood_eventMass
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r))) (weight : ENNReal) :
    (∑ T : Finset (Fin (4 * r)),
        weight ^ T.card *
          eventMass
            (distribution r Delta hDelta)
            (fun sample => checkSetNeighborhood sample S = T)) =
      (weight *
          (1 -
            (((1 - incidenceProbability (4 * r) Delta : NNReal) :
              ENNReal) ^ S.card)) +
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          S.card)) ^ (4 * r) := by
  classical
  rw [← Finset.powerset_univ]
  simp_rw [exactNeighborhood_eventMass r Delta hDelta S]
  calc
    (∑ T ∈ (Finset.univ : Finset (Fin (4 * r))).powerset,
        weight ^ T.card *
          ((1 -
            (((1 - incidenceProbability (4 * r) Delta : NNReal) :
              ENNReal) ^ S.card)) ^ T.card *
          (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
            S.card) ^ (4 * r - T.card))) =
      ∑ T ∈ (Finset.univ : Finset (Fin (4 * r))).powerset,
        (weight *
          (1 -
            (((1 - incidenceProbability (4 * r) Delta : NNReal) :
              ENNReal) ^ S.card))) ^ T.card *
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          S.card) ^ (4 * r - T.card) := by
      apply Finset.sum_congr rfl
      intro T _hT
      rw [← mul_assoc, ← mul_pow]
    _ = _ := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        sum_powerset_pow_card_mul_pow_card_sub
        (Finset.univ : Finset (Fin (4 * r)))
        (weight *
          (1 -
            (((1 - incidenceProbability (4 * r) Delta : NNReal) :
              ENNReal) ^ S.card)))
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          S.card)

/--
The exact-neighborhood events form a probability partition for every fixed
check set.
-/
theorem sum_exactNeighborhood_eventMass
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r))) :
    (∑ T : Finset (Fin (4 * r)),
        eventMass
          (distribution r Delta hDelta)
          (fun sample => checkSetNeighborhood sample S = T)) = 1 := by
  let q : ENNReal :=
    (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
      S.card)
  have hq : q ≤ 1 := by
    dsimp [q]
    exact pow_le_one₀ (by positivity) (by simp)
  calc
    _ = (1 * (1 - q) + q) ^ (4 * r) := by
      simpa only [one_pow, one_mul, q] using
        sum_weight_pow_mul_exactNeighborhood_eventMass
          r Delta hDelta S 1
    _ = 1 := by
      rw [one_mul, tsub_add_cancel_of_le hq, one_pow]

/--
A finite cover of an event gives a union bound on its probability mass.  This
is the event-side companion of `failureMass_le_sum_eventMass`.
-/
theorem eventMass_le_sum_eventMass
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (event : Ω → Prop) [DecidablePred event]
    (cover : ι → Ω → Prop) [∀ i, DecidablePred (cover i)]
    (hcover : ∀ ω, event ω → ∃ i, cover i ω) :
    eventMass p event ≤ ∑ i, eventMass p (cover i) := by
  rw [eventMass_eq_toMeasure]
  calc
    _ ≤ p.toMeasure (⋃ i, {ω | cover i ω}) := by
      apply measure_mono
      intro ω hω
      rcases hcover ω hω with ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    _ ≤ ∑' i, p.toMeasure {ω | cover i ω} := measure_iUnion_le _
    _ = ∑ i, eventMass p (cover i) := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro i _hi
      exact (eventMass_eq_toMeasure p (cover i)).symm

/-- Variable subsets whose cardinality is at most the proposed lower-tail cutoff. -/
def SmallNeighborhood (r cutoff : Nat) :=
  {T : Finset (Fin (4 * r)) // T.card ≤ cutoff}

noncomputable instance instFintypeSmallNeighborhood (r cutoff : Nat) :
    Fintype (SmallNeighborhood r cutoff) :=
  Fintype.subtype
    (Finset.univ.filter fun T : Finset (Fin (4 * r)) =>
      T.card ≤ cutoff)
    (by simp)

noncomputable instance instDecidablePredNeighborhoodCardLe
    (r cutoff : Nat) (S : Finset (Fin (3 * r))) :
    DecidablePred
      (fun sample : Sample r =>
        (checkSetNeighborhood sample S).card ≤ cutoff) :=
  Classical.decPred _

/--
Subunit exponential test weights control the lower tail without division:
`z^k P(|N(S)| ≤ k)` is at most the exact probability-generating function.
-/
theorem weight_pow_mul_smallNeighborhood_eventMass_le
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r))) (cutoff : Nat)
    (weight : ENNReal) (hweight : weight ≤ 1) :
    weight ^ cutoff *
        eventMass
          (distribution r Delta hDelta)
          (fun sample =>
            (checkSetNeighborhood sample S).card ≤ cutoff) ≤
      (weight *
          (1 -
            (((1 - incidenceProbability (4 * r) Delta : NNReal) :
              ENNReal) ^ S.card)) +
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          S.card)) ^ (4 * r) := by
  let exactMass : Finset (Fin (4 * r)) → ENNReal :=
    fun T =>
      eventMass
        (distribution r Delta hDelta)
        (fun sample => checkSetNeighborhood sample S = T)
  calc
    _ ≤ weight ^ cutoff *
        ∑ T : SmallNeighborhood r cutoff, exactMass T.1 := by
      gcongr
      apply eventMass_le_sum_eventMass
      intro sample hsample
      exact
        ⟨⟨checkSetNeighborhood sample S, hsample⟩, rfl⟩
    _ = ∑ T : SmallNeighborhood r cutoff,
        weight ^ cutoff * exactMass T.1 := by
      rw [Finset.mul_sum]
    _ ≤ ∑ T : SmallNeighborhood r cutoff,
        weight ^ T.1.card * exactMass T.1 := by
      exact Finset.sum_le_sum fun T _ => by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right_of_le_one' hweight T.2)
          (by positivity)
    _ ≤ ∑ T : Finset (Fin (4 * r)),
        weight ^ T.card * exactMass T := by
      have hsplit :=
        Fintype.sum_subtype_add_sum_subtype
          (fun T : Finset (Fin (4 * r)) => T.card ≤ cutoff)
          (fun T => weight ^ T.card * exactMass T)
      rw [← hsplit]
      exact le_add_right le_rfl
    _ = _ := by
      dsimp only [exactMass]
      exact sum_weight_pow_mul_exactNeighborhood_eventMass
        r Delta hDelta S weight

/--
The concrete `19 / 20` lower-tail test for an HHO20-small check set, with a
fully explicit finite-power deficit.
-/
theorem nineteen_twentieths_pow_mul_smallNeighborhood_eventMass_le
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r)
    (cutoff : Nat) :
    ((19 : ENNReal) / 20) ^ cutoff *
        eventMass
          (distribution r Delta hDelta)
          (fun sample =>
            (checkSetNeighborhood sample S).card ≤ cutoff) ≤
      (((1 -
          (1 : NNReal) / 20 *
            ((399997 : NNReal) / 400000 *
              ((S.card : NNReal) *
                incidenceProbability (4 * r) Delta)) : NNReal) :
        ENNReal) ^ (4 * r)) := by
  calc
    _ ≤ (((19 : ENNReal) / 20) *
          (1 -
            (((1 - incidenceProbability (4 * r) Delta : NNReal) :
              ENNReal) ^ S.card)) +
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          S.card)) ^ (4 * r) := by
      have hWeightNN : (19 : NNReal) / 20 ≤ 1 := by
        apply div_le_one_of_le₀
        · norm_num
        · exact bot_le
      have hWeightEq :
          (((19 : NNReal) / 20 : NNReal) : ENNReal) =
            (19 : ENNReal) / 20 :=
        ENNReal.coe_div (by norm_num)
      have hWeight : (19 : ENNReal) / 20 ≤ 1 := by
        rw [← hWeightEq]
        exact_mod_cast hWeightNN
      exact weight_pow_mul_smallNeighborhood_eventMass_le
        r Delta hDelta S cutoff ((19 : ENNReal) / 20) hWeight
    _ ≤ _ := by
      apply pow_le_pow_left'
      have hWeightEq :
          (((19 : NNReal) / 20 : NNReal) : ENNReal) =
            (19 : ENNReal) / 20 :=
        ENNReal.coe_div (by norm_num)
      rw [← hWeightEq]
      rw [← ENNReal.coe_pow]
      rw [← ENNReal.coe_one]
      rw [← ENNReal.coe_sub]
      exact_mod_cast nineteen_twentieths_generatorBase_le_of_small
        r Delta hr hDelta S hSmall

/--
Exponential form of the concrete fixed-set lower-tail bound.
-/
theorem nineteen_twentieths_pow_mul_smallNeighborhood_eventMass_le_exp
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r)
    (cutoff : Nat) :
    ((19 : ENNReal) / 20) ^ cutoff *
        eventMass
          (distribution r Delta hDelta)
          (fun sample =>
            (checkSetNeighborhood sample S).card ≤ cutoff) ≤
      ENNReal.ofReal
        (Real.exp
          (-((399997 : Real) * Delta * S.card / 8000000))) := by
  let load : NNReal :=
    (S.card : NNReal) * incidenceProbability (4 * r) Delta
  let penalty : NNReal :=
    (1 : NNReal) / 20 * ((399997 : NNReal) / 400000 * load)
  have hload :=
    card_mul_incidenceProbability_le_of_small r Delta hr S hSmall
  have honeTwentieth : (1 : NNReal) / 20 ≤ 1 := by
    apply div_le_one_of_le₀
    · norm_num
    · exact bot_le
  have hcoefficient : (399997 : NNReal) / 400000 ≤ 1 := by
    apply div_le_one_of_le₀
    · norm_num
    · exact bot_le
  have hthree : (3 : NNReal) / 400000 ≤ 1 := by
    apply div_le_one_of_le₀
    · norm_num
    · exact bot_le
  have hpenalty : penalty ≤ 1 := by
    calc
      penalty ≤ 1 * (1 * load) := by
        dsimp [penalty]
        gcongr
      _ = load := by simp
      _ ≤ (3 : NNReal) / 400000 := hload
      _ ≤ 1 := hthree
  calc
    _ ≤ (((1 - penalty : NNReal) : ENNReal) ^ (4 * r)) := by
      simpa only [penalty, load] using
        nineteen_twentieths_pow_mul_smallNeighborhood_eventMass_le
          r Delta hr hDelta S hSmall cutoff
    _ ≤ ENNReal.ofReal
        (Real.exp (-((4 * r : Nat) : Real) * (penalty : Real))) :=
      coe_one_sub_pow_le_ofReal_exp_neg penalty hpenalty (4 * r)
    _ = ENNReal.ofReal
        (Real.exp
          (-((399997 : Real) * Delta * S.card / 8000000))) := by
      congr 2
      have hExpected :=
        check_expected_degree r Delta hr
      dsimp [penalty, load]
      norm_num [Nat.cast_mul] at hExpected ⊢
      nlinarith

/--
Unweighted fixed-set lower-tail bound after paying the reciprocal
`19 / 20` test-weight cost.
-/
theorem smallNeighborhood_eventMass_le_exp
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r)
    (cutoff : Nat) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample =>
          (checkSetNeighborhood sample S).card ≤ cutoff) ≤
      ENNReal.ofReal
        (Real.exp
          ((cutoff : Real) / 19 -
            (399997 : Real) * Delta * S.card / 8000000)) := by
  let tailMass : ENNReal :=
    eventMass
      (distribution r Delta hDelta)
      (fun sample =>
        (checkSetNeighborhood sample S).card ≤ cutoff)
  have hWeighted :
      ((19 : ENNReal) / 20) ^ cutoff * tailMass ≤
        ENNReal.ofReal
          (Real.exp
            (-((399997 : Real) * Delta * S.card / 8000000))) := by
    exact nineteen_twentieths_pow_mul_smallNeighborhood_eventMass_le_exp
      r Delta hr hDelta S hSmall cutoff
  have hReciprocalEq :
      (((20 : NNReal) / 19 : NNReal) : ENNReal) =
        (20 : ENNReal) / 19 :=
    ENNReal.coe_div (by norm_num)
  have hWeightEq :
      (((19 : NNReal) / 20 : NNReal) : ENNReal) =
        (19 : ENNReal) / 20 :=
    ENNReal.coe_div (by norm_num)
  have hCancel :
      (20 : ENNReal) / 19 * ((19 : ENNReal) / 20) = 1 := by
    rw [← hReciprocalEq, ← hWeightEq, ← ENNReal.coe_mul, ← ENNReal.coe_one]
    norm_num
  have hIdentity :
      ((20 : ENNReal) / 19) ^ cutoff *
          (((19 : ENNReal) / 20) ^ cutoff * tailMass) =
        tailMass := by
    rw [← mul_assoc, ← mul_pow, hCancel, one_pow, one_mul]
  calc
    eventMass
        (distribution r Delta hDelta)
        (fun sample =>
          (checkSetNeighborhood sample S).card ≤ cutoff) =
        tailMass := rfl
    _ = ((20 : ENNReal) / 19) ^ cutoff *
          (((19 : ENNReal) / 20) ^ cutoff * tailMass) := hIdentity.symm
    _ ≤ ((20 : ENNReal) / 19) ^ cutoff *
          ENNReal.ofReal
            (Real.exp
              (-((399997 : Real) * Delta * S.card / 8000000))) := by
      exact mul_le_mul_of_nonneg_left hWeighted (by positivity)
    _ ≤ ENNReal.ofReal (Real.exp ((cutoff : Real) / 19)) *
          ENNReal.ofReal
            (Real.exp
              (-((399997 : Real) * Delta * S.card / 8000000))) := by
      exact mul_le_mul_of_nonneg_right
        (twenty_nineteenths_pow_le_exp cutoff)
        (by positivity)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      rw [← Real.exp_add]
      congr 1

/-- The integral cutoff corresponding to the strengthened `0.92 Δ |S|` target. -/
def expansionCutoff (Delta : Nat) {r : Nat}
    (S : Finset (Fin (3 * r))) : Nat :=
  (92 * Delta * S.card) / 100

/-- The strict expansion failure inequality implies the integral cutoff event. -/
theorem card_le_expansionCutoff_of_strict
    {r Delta : Nat} {S : Finset (Fin (3 * r))}
    {cardinality : Nat}
    (hStrict : 100 * cardinality < 92 * Delta * S.card) :
    cardinality ≤ expansionCutoff Delta S := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 100)).2
  simpa only [Nat.mul_comm] using Nat.le_of_lt hStrict

/-- Finite event mass is monotone under pointwise event inclusion. -/
theorem eventMass_mono
    {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (left right : Ω → Prop)
    [DecidablePred left] [DecidablePred right]
    (h : ∀ ω, left ω → right ω) :
    eventMass p left ≤ eventMass p right := by
  rw [eventMass_eq_toMeasure, eventMass_eq_toMeasure]
  exact measure_mono h

/--
Uniform exponential lower-tail bound at the strengthened HHO20 expansion
cutoff.
-/
theorem expansionCutoff_eventMass_le_exp
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample =>
          (checkSetNeighborhood sample S).card ≤
            expansionCutoff Delta S) ≤
      ENNReal.ofReal
        (Real.exp (-((Delta : Real) * S.card / 1000))) := by
  have hCutoffNat :
      expansionCutoff Delta S * 100 ≤ 92 * Delta * S.card := by
    exact Nat.div_mul_le_self (92 * Delta * S.card) 100
  have hCutoffReal :
      (expansionCutoff Delta S : Real) * 100 ≤
        92 * (Delta : Real) * S.card := by
    exact_mod_cast hCutoffNat
  calc
    _ ≤ ENNReal.ofReal
        (Real.exp
          ((expansionCutoff Delta S : Real) / 19 -
            (399997 : Real) * Delta * S.card / 8000000)) :=
      smallNeighborhood_eventMass_le_exp
        r Delta hr hDelta S hSmall (expansionCutoff Delta S)
    _ ≤ ENNReal.ofReal
        (Real.exp (-((Delta : Real) * S.card / 1000))) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp_of_le
      have hDeltaNonneg : (0 : Real) ≤ Delta := by positivity
      have hCardNonneg : (0 : Real) ≤ S.card := by positivity
      nlinarith

/--
For every fixed HHO20-small check set, failure of `0.92 Δ` neighborhood
expansion has mass at most `exp(-Δ |S| / 1000)`.
-/
theorem fixedSet_expansionFailure_eventMass_le_exp
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample =>
          100 * (checkSetNeighborhood sample S).card <
            92 * Delta * S.card) ≤
      ENNReal.ofReal
        (Real.exp (-((Delta : Real) * S.card / 1000))) := by
  calc
    _ ≤ eventMass
        (distribution r Delta hDelta)
        (fun sample =>
          (checkSetNeighborhood sample S).card ≤
            expansionCutoff Delta S) := by
      apply eventMass_mono
      intro sample hStrict
      exact card_le_expansionCutoff_of_strict hStrict
    _ ≤ _ := expansionCutoff_eventMass_le_exp
      r Delta hr hDelta S hSmall

/-- A nonempty selected check set. -/
def NonemptyCheckSet (r : Nat) :=
  {S : Finset (Fin (3 * r)) // S.Nonempty}

noncomputable instance instFintypeNonemptyCheckSet (r : Nat) :
    Fintype (NonemptyCheckSet r) :=
  Fintype.subtype
    (Finset.univ.filter fun S : Finset (Fin (3 * r)) => S.Nonempty)
    (by simp)

/-- A nonempty check set inside the HHO20 small-set range. -/
def SmallNonemptyCheckSet (r Delta : Nat) :=
  {S : NonemptyCheckSet r //
    100000 * Delta * S.1.card ≤ 3 * r}

noncomputable instance instFintypeSmallNonemptyCheckSet
    (r Delta : Nat) :
    Fintype (SmallNonemptyCheckSet r Delta) :=
  Fintype.subtype
    (Finset.univ.filter fun S : NonemptyCheckSet r =>
      100000 * Delta * S.1.card ≤ 3 * r)
    (by simp)

/-- Every failed strong-expansion sample supplies a nonempty small check set. -/
theorem exists_smallNonemptyCheckSet_of_not_hasStrongSmallSetExpansion
    {r Delta : Nat} {sample : Sample r}
    (h : ¬HasStrongSmallSetExpansion (Delta := Delta) sample) :
    ∃ S : SmallNonemptyCheckSet r Delta,
      100 * (checkSetNeighborhood sample S.1.1).card <
        92 * Delta * S.1.1.card := by
  rw [HasStrongSmallSetExpansion] at h
  push Not at h
  rcases h with ⟨S, hSmall, hStrict⟩
  have hNonempty : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    subst S
    simp at hStrict
  exact ⟨⟨⟨S, hNonempty⟩, hSmall⟩, hStrict⟩

/--
Global strong-expansion failure is bounded by the sum of the fixed-set
exponential tails.
-/
theorem strongSmallSetExpansion_failureMass_le_smallSet_sum
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample =>
          HasStrongSmallSetExpansion (Delta := Delta) sample) ≤
      ∑ S : SmallNonemptyCheckSet r Delta,
        ENNReal.ofReal
          (Real.exp (-((Delta : Real) * S.1.1.card / 1000))) := by
  calc
    _ ≤ ∑ S : SmallNonemptyCheckSet r Delta,
        eventMass
          (distribution r Delta hDelta)
          (fun sample =>
            100 * (checkSetNeighborhood sample S.1.1).card <
              92 * Delta * S.1.1.card) := by
      apply failureMass_le_sum_eventMass
      intro sample hsample
      exact
        exists_smallNonemptyCheckSet_of_not_hasStrongSmallSetExpansion
          hsample
    _ ≤ _ := by
      exact Finset.sum_le_sum fun S _ =>
        fixedSet_expansionFailure_eventMass_le_exp
          r Delta hr hDelta S.1.1 S.2

/-- The fixed-set exponential tail is geometric in the set cardinality. -/
theorem ofReal_exp_card_eq_pow (Delta cardinality : Nat) :
    ENNReal.ofReal
        (Real.exp (-((Delta : Real) * cardinality / 1000))) =
      (ENNReal.ofReal
        (Real.exp (-(Delta : Real) / 1000))) ^ cardinality := by
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/--
Explicit binomial bound for random-base strong-expansion failure.
-/
theorem strongSmallSetExpansion_failureMass_le_binomial
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample =>
          HasStrongSmallSetExpansion (Delta := Delta) sample) ≤
      (1 +
        ENNReal.ofReal
          (Real.exp (-(Delta : Real) / 1000))) ^ (3 * r) - 1 := by
  let tailWeight : ENNReal :=
    ENNReal.ofReal (Real.exp (-(Delta : Real) / 1000))
  calc
    _ ≤ ∑ S : SmallNonemptyCheckSet r Delta,
        ENNReal.ofReal
          (Real.exp (-((Delta : Real) * S.1.1.card / 1000))) :=
      strongSmallSetExpansion_failureMass_le_smallSet_sum
        r Delta hr hDelta
    _ = ∑ S : SmallNonemptyCheckSet r Delta,
        tailWeight ^ S.1.1.card := by
      apply Fintype.sum_congr
      intro S
      exact ofReal_exp_card_eq_pow Delta S.1.1.card
    _ ≤ ∑ S : NonemptyCheckSet r,
        tailWeight ^ S.1.card := by
      let predicate : NonemptyCheckSet r → Prop :=
        fun S => 100000 * Delta * S.1.card ≤ 3 * r
      let summand : NonemptyCheckSet r → ENNReal :=
        fun S => tailWeight ^ S.1.card
      have hsplit :=
        Fintype.sum_subtype_add_sum_subtype predicate summand
      change
        (∑ S : {S : NonemptyCheckSet r // predicate S},
          summand S.1) ≤
        ∑ S : NonemptyCheckSet r, summand S
      rw [← hsplit]
      exact le_add_right le_rfl
    _ = (1 + tailWeight) ^ (3 * r) - 1 := by
      simpa only [NonemptyCheckSet, Fintype.card_fin] using
        (sum_nonempty_finset_pow_card
          (α := Fin (3 * r)) tailWeight)
    _ = _ := rfl

/--
All four random-base conclusions used by the fiber-bundle construction:
degree windows, full row rank, classical distance, and strengthened
small-set expansion.
-/
def IsFullyGood {r Delta : Nat} (sample : Sample r) : Prop :=
  IsGood (Delta := Delta) sample ∧
    HasStrongSmallSetExpansion (Delta := Delta) sample

noncomputable instance instDecidablePredIsFullyGood
    (r Delta : Nat) :
    DecidablePred
      (fun sample : Sample r => IsFullyGood (Delta := Delta) sample) :=
  Classical.decPred _

/-- Failure of `IsFullyGood` is covered by its old and expansion components. -/
theorem isFullyGood_failureMass_le_components
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample => IsFullyGood (Delta := Delta) sample) ≤
      failureMass
          (distribution r Delta hDelta)
          (fun sample => IsGood (Delta := Delta) sample) +
        failureMass
          (distribution r Delta hDelta)
          (fun sample =>
            HasStrongSmallSetExpansion (Delta := Delta) sample) := by
  let p := distribution r Delta hDelta
  have h := failureMass_and_le p
    (fun sample => IsGood (Delta := Delta) sample)
    (fun sample =>
      HasStrongSmallSetExpansion (Delta := Delta) sample)
  simpa only [IsFullyGood, p] using
    (failureMass_decidable_irrel p
      (fun sample =>
        IsGood (Delta := Delta) sample ∧
          HasStrongSmallSetExpansion (Delta := Delta) sample)
      _ _).le.trans h

/--
Explicit combined failure bound including random-base small-set expansion.
-/
theorem isFullyGood_failureMass_le_explicit
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample => IsFullyGood (Delta := Delta) sample) ≤
      (ENNReal.ofReal
          ((14 * r : Real) * Real.exp (-(Delta : Real) / 40000)) +
        ((1 + ENNReal.ofReal
          (Real.exp (-(Delta : Real) / 2))) ^ (3 * r) - 1 +
          (2 : ENNReal) ^ (3 * r) *
            (ENNReal.ofReal ((4 : Real) / 7)) ^ (4 * r)) +
        ((1 + ENNReal.ofReal
          (Real.exp (-(3 : Real) * Delta / 28))) ^ (4 * r) - 1 +
          ((3 : ENNReal) ^ ((4 * r) / 5) *
            ((4 : ENNReal) / 3) ^ (4 * r)) *
            (ENNReal.ofReal ((172 : Real) / 343)) ^ (3 * r))) +
      ((1 + ENNReal.ofReal
        (Real.exp (-(Delta : Real) / 1000))) ^ (3 * r) - 1) := by
  calc
    _ ≤ failureMass
          (distribution r Delta hDelta)
          (fun sample => IsGood (Delta := Delta) sample) +
        failureMass
          (distribution r Delta hDelta)
          (fun sample =>
            HasStrongSmallSetExpansion (Delta := Delta) sample) :=
      isFullyGood_failureMass_le_components r Delta hDelta
    _ ≤ _ := by
      gcongr
      · exact isGood_failureMass_le_explicit
          r Delta hr hDelta hHalf
      · exact strongSmallSetExpansion_failureMass_le_binomial
          r Delta hr hDelta

/--
The exact-neighborhood mass exposes the occupancy penalty `(s p)^t` for the
`t` variables that must actually be hit.  This is the factor absent from a
mere containment-event union bound.
-/
theorem exactNeighborhood_eventMass_le_hitBound
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => checkSetNeighborhood sample S = T) ≤
      ((S.card : ENNReal) *
        (incidenceProbability (4 * r) Delta : ENNReal)) ^ T.card *
      (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
        S.card) ^ (4 * r - T.card) := by
  rw [exactNeighborhood_eventMass r Delta hDelta S T]
  gcongr
  exact one_sub_coe_one_sub_pow_le
    (incidenceProbability (4 * r) Delta)
    (incidenceProbability_le_one hDelta)
    S.card

/--
Every failed expansion instance has a witness whose second component is the
*actual* variable neighborhood.  Keeping equality here, rather than weakening
it to containment, prevents the same sample from being charged to every
superset of its neighborhood.
-/
theorem exists_exact_expansionWitness_of_not_hasStrongSmallSetExpansion
    {r Delta : Nat} {sample : Sample r}
    (h : ¬HasStrongSmallSetExpansion (Delta := Delta) sample) :
    ∃ witness : ExpansionWitness r Delta,
      checkSetNeighborhood sample witness.1.1 = witness.1.2 := by
  rw [HasStrongSmallSetExpansion] at h
  push Not at h
  rcases h with ⟨S, hSmall, hExpansion⟩
  exact
    ⟨⟨(S, checkSetNeighborhood sample S), hSmall, hExpansion⟩, rfl⟩

/--
Expansion failure is bounded by the exact-neighborhood occupancy sum.  This is
the finite probabilistic reduction used by the subsequent analytic estimate;
it has no externally supplied matrix or expansion certificate.
-/
theorem strongSmallSetExpansion_failureMass_le_exactNeighborhood_sum
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample =>
          HasStrongSmallSetExpansion (Delta := Delta) sample) ≤
      ∑ witness : ExpansionWitness r Delta,
        (1 -
          (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
            witness.1.1.card)) ^ witness.1.2.card *
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          witness.1.1.card) ^ (4 * r - witness.1.2.card) := by
  calc
    _ ≤ ∑ witness : ExpansionWitness r Delta,
        eventMass
          (distribution r Delta hDelta)
          (fun sample =>
            checkSetNeighborhood sample witness.1.1 = witness.1.2) := by
      apply failureMass_le_sum_eventMass
      intro sample hsample
      exact
        exists_exact_expansionWitness_of_not_hasStrongSmallSetExpansion
          hsample
    _ = _ := by
      apply Fintype.sum_congr
      intro witness
      exact exactNeighborhood_eventMass
        r Delta hDelta witness.1.1 witness.1.2

/--
Expansion failure is bounded by the occupancy-weighted witness sum.  The
factor involving `witness.1.2.card` records that every member of the proposed
neighborhood must be hit, while every variable outside it must be avoided.
-/
theorem strongSmallSetExpansion_failureMass_le_occupancy_sum
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample =>
          HasStrongSmallSetExpansion (Delta := Delta) sample) ≤
      ∑ witness : ExpansionWitness r Delta,
        ((witness.1.1.card : ENNReal) *
          (incidenceProbability (4 * r) Delta : ENNReal)) ^
            witness.1.2.card *
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          witness.1.1.card) ^ (4 * r - witness.1.2.card) := by
  calc
    _ ≤ ∑ witness : ExpansionWitness r Delta,
        eventMass
          (distribution r Delta hDelta)
          (fun sample =>
            checkSetNeighborhood sample witness.1.1 = witness.1.2) := by
      apply failureMass_le_sum_eventMass
      intro sample hsample
      exact
        exists_exact_expansionWitness_of_not_hasStrongSmallSetExpansion
          hsample
    _ ≤ _ := by
      exact Finset.sum_le_sum fun witness _ =>
        exactNeighborhood_eventMass_le_hitBound
          r Delta hDelta witness.1.1 witness.1.2

end QEC.Coding.FiberBundle.RandomBase
