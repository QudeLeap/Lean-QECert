import QEC.Coding.FiberBundle.TwistGraphSpectrumProbability
import QEC.Coding.FiberBundle.RandomBase.Rank
import QEC.Coding.FiberBundle.RandomBase.Distance
import QEC.Coding.FiberBundle.RandomBase.ExpansionProbability
import Mathlib.Probability.Independence.Integration

/-!
# Random partitioned-check events for the HHO20 base

This file uses a row-grouped sampler for the two independent bits attached to
each possible Tanner incidence:

* whether the incidence is present in the random base matrix;
* whether a present incidence is assigned to the tail rather than the head.

Grouping those bits by check row makes the check outcomes independent across
rows.  The decoded base and head/tail samples are definitionally compatible
with the deterministic `HasHHO20LightChecks` and `HasHHO20HeavyChecks`
interfaces.
-/

namespace QEC.Coding.FiberBundle.RandomPartition

open scoped BigOperators
open MeasureTheory

/-- One possible incidence carries an incidence bit (`false`) and an
independent head/tail bit (`true`). -/
abbrev LocalSample := Bool → Bool

/-- One row contains one local two-bit sample for each possible variable. -/
abbrev RowSample (r : Nat) :=
  Fin (4 * r) → LocalSample

/-- The full partitioned-base sample, grouped by check row. -/
abbrev Sample (r : Nat) :=
  Fin (3 * r) → RowSample r

/-- The two coordinate laws within one row. -/
noncomputable def localCoordinatePMF
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (side : Bool) : PMF Bool :=
  if side then
    PMF.bernoulli (1 / 2 : NNReal) (by norm_num)
  else
    PMF.bernoulli
      (RandomBase.incidenceProbability (4 * r) Delta)
      (RandomBase.incidenceProbability_le_one hDelta)

/-- The independent incidence/head-tail law at one possible incidence. -/
noncomputable def localDistribution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    PMF LocalSample :=
  RandomBase.independentProduct
    (localCoordinatePMF r Delta hDelta)

/-- One independently sampled partitioned check row. -/
noncomputable def rowDistribution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    PMF (RowSample r) :=
  RandomBase.independentProduct fun _ =>
    localDistribution r Delta hDelta

/-- All check rows sampled independently. -/
noncomputable def distribution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    PMF (Sample r) :=
  RandomBase.independentProduct fun _ =>
    rowDistribution r Delta hDelta

/-- Decode the incidence coordinates as the existing random-base sample. -/
def baseSample
    {r : Nat} (sample : Sample r) :
    RandomBase.Sample r :=
  fun edge => sample edge.1 edge.2 false

/-- Decode one head/tail coordinate. -/
def isTail
    {r : Nat} (sample : Sample r)
    (a : Fin (3 * r)) (b : Fin (4 * r)) : Bool :=
  sample a b true

/-- Assemble decoded head/tail bits and an arbitrary chosen type-shift vector
into the existing dependent twist-sample interface. -/
def twistSample
    {r typeCount ell : Nat}
    (sample : Sample r)
    (typeShifts : Fin typeCount → Fin (ell - 1)) :
    RandomTwist.Sample r typeCount ell
  | Sum.inl edge => isTail sample edge.1 edge.2
  | Sum.inr τ => typeShifts τ

@[simp]
theorem baseSample_apply
    {r : Nat} (sample : Sample r)
    (a : Fin (3 * r)) (b : Fin (4 * r)) :
    baseSample sample (a, b) = sample a b false := by
  rfl

@[simp]
theorem isTail_twistSample
    {r typeCount ell : Nat}
    (sample : Sample r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (a : Fin (3 * r)) (b : Fin (4 * r)) :
    RandomTwist.isTail (twistSample sample typeShifts) a b =
      isTail sample a b := by
  rfl

@[simp]
theorem typeTwist_twistSample
    {r typeCount ell : Nat}
    (sample : Sample r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (τ : Fin typeCount) :
    RandomTwist.typeTwist (twistSample sample typeShifts) τ =
      typeShifts τ := by
  rfl

/-- The rows of the partitioned-base sampler are mutually independent. -/
theorem distribution_row_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun a (sample : Sample r) => sample a)
      (distribution r Delta hDelta).toMeasure := by
  exact RandomBase.independentProduct_iIndepFun _

/-- Every sampled row has the explicit within-row product law. -/
theorem distribution_row_hasLaw
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) :
    ProbabilityTheory.HasLaw
      (fun sample : Sample r => sample a)
      (rowDistribution r Delta hDelta).toMeasure
      (distribution r Delta hDelta).toMeasure := by
  simpa only [distribution] using
    (RandomBase.independentProduct_coordinate_hasLaw
      (fun _ : Fin (3 * r) => rowDistribution r Delta hDelta) a)

/-- Variable-local samples within one check row are mutually independent. -/
theorem rowDistribution_variable_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun b (row : RowSample r) => row b)
      (rowDistribution r Delta hDelta).toMeasure := by
  exact RandomBase.independentProduct_iIndepFun _

/-- Every variable-local sample has the two-bit product law. -/
theorem rowDistribution_variable_hasLaw
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) :
    ProbabilityTheory.HasLaw
      (fun row : RowSample r => row b)
      (localDistribution r Delta hDelta).toMeasure
      (rowDistribution r Delta hDelta).toMeasure := by
  simpa only [rowDistribution] using
    (RandomBase.independentProduct_coordinate_hasLaw
      (fun _ : Fin (4 * r) =>
        localDistribution r Delta hDelta) b)

/-- Incidence and head/tail bits at one possible incidence are independent. -/
theorem localDistribution_coordinate_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun side (localSample : LocalSample) => localSample side)
      (localDistribution r Delta hDelta).toMeasure := by
  exact RandomBase.independentProduct_iIndepFun _

/-- Each local bit has its declared Bernoulli law. -/
theorem localDistribution_coordinate_hasLaw
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (side : Bool) :
    ProbabilityTheory.HasLaw
      (fun localSample : LocalSample => localSample side)
      (localCoordinatePMF r Delta hDelta side).toMeasure
      (localDistribution r Delta hDelta).toMeasure := by
  simpa only [localDistribution] using
    (RandomBase.independentProduct_coordinate_hasLaw
      (localCoordinatePMF r Delta hDelta) side)

/-- Incidence projections within one partitioned row remain mutually
independent. -/
theorem rowDistribution_incidence_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun b (row : RowSample r) => row b false)
      (rowDistribution r Delta hDelta).toMeasure := by
  exact
    (rowDistribution_variable_iIndepFun r Delta hDelta).comp
      (fun _b localSample => localSample false)
      (fun _b => Measurable.of_discrete)

/-- Every incidence projection within one row has exactly the Bernoulli base
law. -/
theorem rowDistribution_incidence_hasLaw
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) :
    ProbabilityTheory.HasLaw
      (fun row : RowSample r => row b false)
      (PMF.bernoulli
        (RandomBase.incidenceProbability (4 * r) Delta)
        (RandomBase.incidenceProbability_le_one hDelta)).toMeasure
      (rowDistribution r Delta hDelta).toMeasure := by
  have hLocal :=
    localDistribution_coordinate_hasLaw r Delta hDelta false
  have hVariable :=
    rowDistribution_variable_hasLaw r Delta hDelta b
  exact hLocal.comp hVariable

/-- For a fixed check row, all decoded incidence bits remain independent
under the full partition sampler. -/
theorem distribution_fixedRow_incidence_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) :
    ProbabilityTheory.iIndepFun
      (fun b (sample : Sample r) => sample a b false)
      (distribution r Delta hDelta).toMeasure := by
  let μb : Fin (4 * r) → Measure Bool :=
    fun _ =>
      (PMF.bernoulli
        (RandomBase.incidenceProbability (4 * r) Delta)
        (RandomBase.incidenceProbability_le_one hDelta)).toMeasure
  have hCoordinateRow :
      ∀ b,
        ProbabilityTheory.HasLaw
          (fun row : RowSample r => row b false)
          (μb b) (rowDistribution r Delta hDelta).toMeasure := by
    intro b
    exact rowDistribution_incidence_hasLaw r Delta hDelta b
  have hVectorRow :
      ProbabilityTheory.HasLaw
        (fun row : RowSample r => fun b => row b false)
        (Measure.pi μb)
        (rowDistribution r Delta hDelta).toMeasure :=
    (rowDistribution_incidence_iIndepFun
      r Delta hDelta).hasLaw_pi hCoordinateRow
  have hRow :=
    distribution_row_hasLaw r Delta hDelta a
  have hVectorFull :
      ProbabilityTheory.HasLaw
        (fun sample : Sample r => fun b => sample a b false)
        (Measure.pi μb)
        (distribution r Delta hDelta).toMeasure := by
    simpa [Function.comp_def] using hVectorRow.comp hRow
  have hCoordinateFull :
      ∀ b,
        ProbabilityTheory.HasLaw
          (fun sample : Sample r => sample a b false)
          (μb b) (distribution r Delta hDelta).toMeasure := by
    intro b
    have hCoordinate := hCoordinateRow b
    simpa [Function.comp_def] using hCoordinate.comp hRow
  exact
    (ProbabilityTheory.iIndepFun_iff_hasLaw_pi_pi
      hCoordinateFull).2 hVectorFull

/-- All decoded Tanner incidences are mutually independent under the grouped
partition sampler. -/
theorem distribution_incidence_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun edge : Fin (3 * r) × Fin (4 * r) =>
        fun sample : Sample r => sample edge.1 edge.2 false)
      (distribution r Delta hDelta).toMeasure := by
  have hOuter :
      ProbabilityTheory.iIndepFun
        (fun a (sample : Sample r) => fun b => sample a b false)
        (distribution r Delta hDelta).toMeasure :=
    (distribution_row_iIndepFun r Delta hDelta).comp
      (fun _a row => fun b => row b false)
      (fun _a => Measurable.of_discrete)
  exact ProbabilityTheory.iIndepFun_uncurry'
    (fun _a _b => Measurable.of_discrete)
    hOuter
    (distribution_fixedRow_incidence_iIndepFun r Delta hDelta)

/-- Every decoded Tanner incidence has exactly the Bernoulli base law under
the full partition sampler. -/
theorem distribution_incidence_hasLaw
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (edge : Fin (3 * r) × Fin (4 * r)) :
    ProbabilityTheory.HasLaw
      (fun sample : Sample r => sample edge.1 edge.2 false)
      (PMF.bernoulli
        (RandomBase.incidenceProbability (4 * r) Delta)
        (RandomBase.incidenceProbability_le_one hDelta)).toMeasure
      (distribution r Delta hDelta).toMeasure := by
  have hLocal :=
    localDistribution_coordinate_hasLaw r Delta hDelta false
  have hVariable :=
    rowDistribution_variable_hasLaw r Delta hDelta edge.2
  have hRow :=
    distribution_row_hasLaw r Delta hDelta edge.1
  simpa [localCoordinatePMF, Function.comp_def] using
    (hLocal.comp hVariable).comp hRow

/-- Decoding the incidence coordinates pushes the grouped sampler exactly to
the original HHO20 random-base distribution. -/
theorem distribution_baseSample_hasLaw
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.HasLaw
      (baseSample : Sample r → RandomBase.Sample r)
      (RandomBase.distribution r Delta hDelta).toMeasure
      (distribution r Delta hDelta).toMeasure := by
  let μedge :
      (Fin (3 * r) × Fin (4 * r)) → Measure Bool :=
    fun _ =>
      (PMF.bernoulli
        (RandomBase.incidenceProbability (4 * r) Delta)
        (RandomBase.incidenceProbability_le_one hDelta)).toMeasure
  have hCoordinate :
      ∀ edge,
        ProbabilityTheory.HasLaw
          (fun sample : Sample r => sample edge.1 edge.2 false)
          (μedge edge)
          (distribution r Delta hDelta).toMeasure := by
    intro edge
    exact distribution_incidence_hasLaw r Delta hDelta edge
  have hLawPi :
      ProbabilityTheory.HasLaw
        (fun sample : Sample r =>
          fun edge => sample edge.1 edge.2 false)
        (Measure.pi μedge)
        (distribution r Delta hDelta).toMeasure :=
    (distribution_incidence_iIndepFun
      r Delta hDelta).hasLaw_pi hCoordinate
  rw [RandomBase.distribution,
    RandomBase.independentProduct_toMeasure_eq_pi]
  exact hLawPi

/-- Exact transfer of every event measure through the decoded incidence
projection. -/
theorem distribution_baseSample_measureReal_eq
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (event : RandomBase.Sample r → Prop) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | event (baseSample sample)} =
      (RandomBase.distribution r Delta hDelta).toMeasure.real
        {base | event base} := by
  exact
    (distribution_baseSample_hasLaw
      r Delta hDelta).measureReal_eq MeasurableSet.of_discrete

/-- The explicit ENNReal union bound already proved for all four random-base
good events. -/
noncomputable def fullyGoodBaseFailureBound
    (r Delta : Nat) : ENNReal :=
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
    (Real.exp (-(Delta : Real) / 1000))) ^ (3 * r) - 1)

/- The random-base failure estimate transferred to the grouped partition
sampler. -/
set_option maxHeartbeats 800000 in
theorem measure_not_isFullyGood_baseSample_le
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r) :
    (distribution r Delta hDelta).toMeasure.real
        {sample |
          ¬RandomBase.IsFullyGood
            (Delta := Delta) (baseSample sample)} ≤
      (fullyGoodBaseFailureBound r Delta).toReal := by
  rw [distribution_baseSample_measureReal_eq
    r Delta hDelta
    (fun base =>
      ¬RandomBase.IsFullyGood (Delta := Delta) base)]
  rw [measureReal_def]
  have hFailure :=
    RandomBase.isFullyGood_failureMass_le_explicit
      r Delta hr hDelta hHalf
  rw [RandomBase.failureMass_eq_toMeasure] at hFailure
  exact ENNReal.toReal_mono
    (by
      dsimp [fullyGoodBaseFailureBound]
      finiteness)
    hFailure

/-- Contribution of one possible incidence to the partitioned check on
`(y,z)`. -/
noncomputable def localPairContribution
    {r : Nat}
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (b : Fin (4 * r))
    (localSample : LocalSample) : ZMod 2 :=
  if localSample false then
    if localSample true then y b else z b
  else
    0

/-- The parity syndrome of one sampled partitioned check row. -/
noncomputable def rowPairSyndrome
    {r : Nat}
    (row : RowSample r)
    (y z : Word (ZMod 2) (Fin (4 * r))) : ZMod 2 :=
  ∑ b : Fin (4 * r), localPairContribution y z b (row b)

/-- Decoding a grouped sample gives exactly the deterministic pair-check
syndrome already used by the twist-graph proof. -/
theorem pairCheckSyndrome_baseSample_twistSample
    {r typeCount ell : Nat}
    (sample : Sample r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r)) :
    TwistGraph.pairCheckSyndrome
        (baseSample sample) (twistSample sample typeShifts)
        y z a =
      rowPairSyndrome (sample a) y z := by
  simp only [TwistGraph.pairCheckSyndrome, RandomBase.boundary,
    rowPairSyndrome, localPairContribution, baseSample_apply,
    isTail_twistSample]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hIncidence : sample a b false <;>
    simp [hIncidence, isTail] <;> rfl

/-- The real nontrivial character of one local contribution. -/
noncomputable def localPairSign
    {r : Nat}
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (b : Fin (4 * r))
    (localSample : LocalSample) : Real :=
  RandomBase.paritySign
    (localPairContribution y z b localSample)

/-- The parity character of a whole row factors over variables. -/
theorem paritySign_rowPairSyndrome
    {r : Nat}
    (row : RowSample r)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    RandomBase.paritySign (rowPairSyndrome row y z) =
      ∏ b : Fin (4 * r), localPairSign y z b (row b) := by
  classical
  change
    RandomBase.paritySign
        (∑ b ∈ (Finset.univ : Finset (Fin (4 * r))),
          localPairContribution y z b (row b)) =
      ∏ b ∈ (Finset.univ : Finset (Fin (4 * r))),
        localPairSign y z b (row b)
  generalize (Finset.univ : Finset (Fin (4 * r))) = s
  induction s using Finset.induction_on with
  | empty =>
      simp [RandomBase.paritySign]
  | @insert b s hb ih =>
      rw [Finset.sum_insert hb, Finset.prod_insert hb,
        RandomBase.paritySign_add, ih]
      rfl

/-- Real incidence indicator inside one local two-bit sample. -/
def localIncidenceReal (localSample : LocalSample) : Real :=
  cond (localSample false) 1 0

/-- Character selected by the independent head/tail bit once an incidence is
present. -/
noncomputable def localSelectedPairSign
    {r : Nat}
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (b : Fin (4 * r))
    (localSample : LocalSample) : Real :=
  if localSample true then
    RandomBase.paritySign (y b)
  else
    RandomBase.paritySign (z b)

/-- Algebraic decomposition of a local parity character into its incidence
and head/tail factors. -/
theorem localPairSign_eq
    {r : Nat}
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (b : Fin (4 * r))
    (localSample : LocalSample) :
    localPairSign y z b localSample =
      1 - localIncidenceReal localSample +
        localIncidenceReal localSample *
          localSelectedPairSign y z b localSample := by
  by_cases hIncidence : localSample false <;>
    by_cases hTail : localSample true <;>
    simp [localPairSign, localPairContribution, localIncidenceReal,
      localSelectedPairSign, RandomBase.paritySign, hIncidence, hTail]

/-- Exact expectation of the local incidence indicator. -/
theorem integral_localIncidenceReal
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ∫ localSample, localIncidenceReal localSample
      ∂(localDistribution r Delta hDelta).toMeasure =
      (RandomBase.incidenceProbability (4 * r) Delta).toReal := by
  calc
    _ =
        ∫ incidence, cond incidence (1 : Real) 0
          ∂(PMF.bernoulli
            (RandomBase.incidenceProbability (4 * r) Delta)
            (RandomBase.incidenceProbability_le_one hDelta)).toMeasure := by
      exact
        (localDistribution_coordinate_hasLaw
          r Delta hDelta false).integral_comp
          (f := fun incidence => cond incidence (1 : Real) 0)
          (by fun_prop)
    _ = _ := by
      exact PMF.bernoulli_expectation
        (RandomBase.incidenceProbability_le_one hDelta)

/-- Exact expectation of the fair head/tail-selected character. -/
theorem integral_localSelectedPairSign
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (b : Fin (4 * r)) :
    ∫ localSample, localSelectedPairSign y z b localSample
      ∂(localDistribution r Delta hDelta).toMeasure =
      (RandomBase.paritySign (y b) +
        RandomBase.paritySign (z b)) / 2 := by
  calc
    _ =
        ∫ tail,
          if tail then
            RandomBase.paritySign (y b)
          else
            RandomBase.paritySign (z b)
          ∂(PMF.bernoulli (1 / 2 : NNReal) (by norm_num)).toMeasure := by
      exact
        (localDistribution_coordinate_hasLaw
          r Delta hDelta true).integral_comp
          (f := fun tail =>
            if tail then
              RandomBase.paritySign (y b)
            else
              RandomBase.paritySign (z b))
          (by fun_prop)
    _ = _ := by
      rw [PMF.integral_eq_sum]
      simp [PMF.bernoulli_apply]
      ring

/-- The incidence indicator and selected head/tail character are independent
because they read the two distinct local coordinates. -/
theorem localIncidenceReal_indep_localSelectedPairSign
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (b : Fin (4 * r)) :
    ProbabilityTheory.IndepFun
      localIncidenceReal
      (localSelectedPairSign y z b)
      (localDistribution r Delta hDelta).toMeasure := by
  exact
    (((localDistribution_coordinate_iIndepFun
      r Delta hDelta).indepFun
      (by decide : false ≠ true)).comp
      (Measurable.of_discrete :
        Measurable (fun incidence : Bool =>
          cond incidence (1 : Real) 0))
      (Measurable.of_discrete :
        Measurable (fun tail : Bool =>
          if tail then
            RandomBase.paritySign (y b)
          else
            RandomBase.paritySign (z b))))

/-- Exact expectation of the product of the independent local factors. -/
theorem integral_localIncidenceReal_mul_selectedPairSign
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (b : Fin (4 * r)) :
    ∫ localSample,
        localIncidenceReal localSample *
          localSelectedPairSign y z b localSample
      ∂(localDistribution r Delta hDelta).toMeasure =
      (RandomBase.incidenceProbability (4 * r) Delta).toReal *
        ((RandomBase.paritySign (y b) +
          RandomBase.paritySign (z b)) / 2) := by
  calc
    _ =
        (∫ localSample, localIncidenceReal localSample
          ∂(localDistribution r Delta hDelta).toMeasure) *
        (∫ localSample, localSelectedPairSign y z b localSample
          ∂(localDistribution r Delta hDelta).toMeasure) := by
      exact
        (localIncidenceReal_indep_localSelectedPairSign
          r Delta hDelta y z b).integral_fun_mul_eq_mul_integral
          Measurable.of_discrete.aestronglyMeasurable
          Measurable.of_discrete.aestronglyMeasurable
    _ = _ := by
      rw [integral_localIncidenceReal,
        integral_localSelectedPairSign]

/-- Exact HHO20 local character expectation. -/
theorem integral_localPairSign
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (b : Fin (4 * r)) :
    ∫ localSample, localPairSign y z b localSample
      ∂(localDistribution r Delta hDelta).toMeasure =
      1 -
        (RandomBase.incidenceProbability (4 * r) Delta).toReal +
        (RandomBase.incidenceProbability (4 * r) Delta).toReal *
          ((RandomBase.paritySign (y b) +
            RandomBase.paritySign (z b)) / 2) := by
  let μ := (localDistribution r Delta hDelta).toMeasure
  calc
    ∫ localSample, localPairSign y z b localSample ∂μ =
        ∫ localSample,
          (1 - localIncidenceReal localSample) +
            localIncidenceReal localSample *
              localSelectedPairSign y z b localSample ∂μ := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun localSample =>
        localPairSign_eq y z b localSample
    _ =
        (∫ localSample, (1 - localIncidenceReal localSample) ∂μ) +
          ∫ localSample,
            localIncidenceReal localSample *
              localSelectedPairSign y z b localSample ∂μ := by
      rw [MeasureTheory.integral_add]
      · exact Integrable.of_finite
      · exact Integrable.of_finite
    _ =
        1 -
          (∫ localSample, localIncidenceReal localSample ∂μ) +
          ∫ localSample,
            localIncidenceReal localSample *
              localSelectedPairSign y z b localSample ∂μ := by
      rw [MeasureTheory.integral_sub]
      · simp [μ]
      · exact MeasureTheory.integrable_const 1
      · exact Integrable.of_finite
    _ = _ := by
      rw [integral_localIncidenceReal,
        integral_localIncidenceReal_mul_selectedPairSign]

/-- Exact whole-row parity-character expectation, factored over variables. -/
theorem integral_paritySign_rowPairSyndrome
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    ∫ row, RandomBase.paritySign (rowPairSyndrome row y z)
      ∂(rowDistribution r Delta hDelta).toMeasure =
      ∏ b : Fin (4 * r),
        (1 -
          (RandomBase.incidenceProbability (4 * r) Delta).toReal +
          (RandomBase.incidenceProbability (4 * r) Delta).toReal *
            ((RandomBase.paritySign (y b) +
              RandomBase.paritySign (z b)) / 2)) := by
  have hIndep :
      ProbabilityTheory.iIndepFun
        (fun b (row : RowSample r) =>
          localPairSign y z b (row b))
        (rowDistribution r Delta hDelta).toMeasure :=
    (rowDistribution_variable_iIndepFun r Delta hDelta).comp
      (fun b localSample => localPairSign y z b localSample)
      (fun _b => Measurable.of_discrete)
  calc
    _ =
        ∫ row,
          ∏ b : Fin (4 * r), localPairSign y z b (row b)
          ∂(rowDistribution r Delta hDelta).toMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun row =>
        paritySign_rowPairSyndrome row y z
    _ =
        ∏ b : Fin (4 * r),
          ∫ row, localPairSign y z b (row b)
            ∂(rowDistribution r Delta hDelta).toMeasure := by
      exact hIndep.integral_fun_prod_eq_prod_integral
        (fun _b => Measurable.of_discrete.aestronglyMeasurable)
    _ =
        ∏ b : Fin (4 * r),
          ∫ localSample, localPairSign y z b localSample
            ∂(localDistribution r Delta hDelta).toMeasure := by
      apply Finset.prod_congr rfl
      intro b _hb
      exact (rowDistribution_variable_hasLaw
        r Delta hDelta b).integral_comp
        (f := localPairSign y z b)
        Measurable.of_discrete.aestronglyMeasurable
    _ = _ := by
      apply Finset.prod_congr rfl
      intro b _hb
      rw [integral_localPairSign]

/-- Real indicator that one partitioned check is violated. -/
noncomputable def rowViolationIndicator
    {r : Nat}
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (row : RowSample r) : Real :=
  if rowPairSyndrome row y z ≠ 0 then 1 else 0

/-- Fourier-character identity for the row-violation indicator. -/
theorem rowViolationIndicator_eq
    {r : Nat}
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (row : RowSample r) :
    rowViolationIndicator y z row =
      (1 - RandomBase.paritySign (rowPairSyndrome row y z)) / 2 := by
  by_cases hzero : rowPairSyndrome row y z = 0
  · simp [rowViolationIndicator, hzero, RandomBase.paritySign]
  · simp [rowViolationIndicator, hzero, RandomBase.paritySign]

/-- Exact HHO20 `prop:chi` probability in product form. -/
theorem rowViolation_measureReal
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    (rowDistribution r Delta hDelta).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0} =
      (1 -
        ∏ b : Fin (4 * r),
          (1 -
            (RandomBase.incidenceProbability (4 * r) Delta).toReal +
            (RandomBase.incidenceProbability (4 * r) Delta).toReal *
              ((RandomBase.paritySign (y b) +
                RandomBase.paritySign (z b)) / 2))) / 2 := by
  let μ := (rowDistribution r Delta hDelta).toMeasure
  calc
    μ.real {row | rowPairSyndrome row y z ≠ 0} =
        ∫ row, rowViolationIndicator y z row ∂μ := by
      rw [← integral_indicator_one
        (μ := μ) (Set.toFinite _).measurableSet]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun row => by
        by_cases hviol : rowPairSyndrome row y z ≠ 0 <;>
          simp [rowViolationIndicator, Set.indicator, hviol]
    _ =
        ∫ row,
          (1 - RandomBase.paritySign (rowPairSyndrome row y z)) / 2
          ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun row =>
        rowViolationIndicator_eq y z row
    _ = _ := by
      rw [integral_div, integral_sub]
      · simp [μ, integral_paritySign_rowPairSyndrome
          r Delta hDelta y z]
      · exact Integrable.of_finite
      · exact Integrable.of_finite

/-- Number of coordinates where both input words are nonzero. -/
noncomputable def pairOverlapCount
    {r : Nat}
    (y z : Word (ZMod 2) (Fin (4 * r))) : Nat :=
  (Finset.univ.filter fun b => y b ≠ 0 ∧ z b ≠ 0).card

/-- Each local character mean has one factor for the XOR support and one for
the overlap support. -/
theorem localPairMean_eq_indicatorFactors
    (r Delta : Nat)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (b : Fin (4 * r)) :
    1 -
        (RandomBase.incidenceProbability (4 * r) Delta).toReal +
        (RandomBase.incidenceProbability (4 * r) Delta).toReal *
          ((RandomBase.paritySign (y b) +
            RandomBase.paritySign (z b)) / 2) =
      (if y b + z b ≠ 0 then
        1 - (RandomBase.incidenceProbability (4 * r) Delta).toReal
      else 1) *
      (if y b ≠ 0 ∧ z b ≠ 0 then
        1 -
          2 *
            (RandomBase.incidenceProbability (4 * r) Delta).toReal
      else 1) := by
  by_cases hy : y b = 0
  · rw [hy]
    by_cases hz : z b = 0
    · simp [hz, RandomBase.paritySign]
    · rw [RandomBase.zmod2_eq_one_of_ne_zero (z b) hz]
      norm_num [RandomBase.paritySign]
  · rw [RandomBase.zmod2_eq_one_of_ne_zero (y b) hy]
    by_cases hz : z b = 0
    · simp [hz, RandomBase.paritySign]
    · rw [RandomBase.zmod2_eq_one_of_ne_zero (z b) hz]
      have htwo : (1 + 1 : ZMod 2) = 0 := by decide
      simp [RandomBase.paritySign, htwo]
      ring

/-- Closed-form HHO20 `prop:chi` character product. -/
theorem product_localPairMean_eq
    (r Delta : Nat)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    (∏ b : Fin (4 * r),
        (1 -
          (RandomBase.incidenceProbability (4 * r) Delta).toReal +
          (RandomBase.incidenceProbability (4 * r) Delta).toReal *
            ((RandomBase.paritySign (y b) +
              RandomBase.paritySign (z b)) / 2))) =
      (1 -
        (RandomBase.incidenceProbability (4 * r) Delta).toReal) ^
          HammingWeight (y + z) *
      (1 -
        2 * (RandomBase.incidenceProbability (4 * r) Delta).toReal) ^
          pairOverlapCount y z := by
  classical
  simp_rw [localPairMean_eq_indicatorFactors r Delta y z]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite, Finset.prod_const]
  congr 2
  · simp [HammingWeight, hammingSupport]
  · simp [pairOverlapCount]

/-- Exact closed form of HHO20 `prop:chi`: one row violates the paired
checks with probability one half minus one half of the XOR/overlap
character product. -/
theorem rowViolation_measureReal_closed
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    (rowDistribution r Delta hDelta).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0} =
      (1 -
        (1 -
          (RandomBase.incidenceProbability (4 * r) Delta).toReal) ^
            HammingWeight (y + z) *
        (1 -
          2 * (RandomBase.incidenceProbability (4 * r) Delta).toReal) ^
            pairOverlapCount y z) / 2 := by
  rw [rowViolation_measureReal r Delta hDelta y z,
    product_localPairMean_eq r Delta y z]

/-- Binary support arithmetic: the two input supports decompose into their
XOR support plus two copies of their overlap. -/
theorem hammingWeight_add_eq_add_two_pairOverlapCount
    {r : Nat}
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    HammingWeight y + HammingWeight z =
      HammingWeight (y + z) + 2 * pairOverlapCount y z := by
  classical
  have hpoint :
      ∀ b : Fin (4 * r),
        (if y b ≠ 0 then 1 else 0) +
            (if z b ≠ 0 then 1 else 0) =
          (if y b + z b ≠ 0 then 1 else 0) +
            2 * (if y b ≠ 0 ∧ z b ≠ 0 then 1 else 0) := by
    intro b
    by_cases hy : y b = 0
    · simp [hy]
    · rw [RandomBase.zmod2_eq_one_of_ne_zero (y b) hy]
      by_cases hz : z b = 0
      · simp [hz]
      · rw [RandomBase.zmod2_eq_one_of_ne_zero (z b) hz]
        have htwo : (1 + 1 : ZMod 2) = 0 := by decide
        simp [htwo]
  have hsum := Finset.sum_congr rfl
    (fun b (_hb : b ∈ (Finset.univ : Finset (Fin (4 * r)))) => hpoint b)
  have hyCard :
      HammingWeight y =
        ∑ b : Fin (4 * r), if y b ≠ 0 then 1 else 0 := by
    rw [HammingWeight, hammingSupport, Finset.card_filter]
  have hzCard :
      HammingWeight z =
        ∑ b : Fin (4 * r), if z b ≠ 0 then 1 else 0 := by
    rw [HammingWeight, hammingSupport, Finset.card_filter]
  have hxorCard :
      HammingWeight (y + z) =
        ∑ b : Fin (4 * r), if y b + z b ≠ 0 then 1 else 0 := by
    rw [HammingWeight, hammingSupport, Finset.card_filter]
    simp
  have hoverlapCard :
      pairOverlapCount y z =
        ∑ b : Fin (4 * r), if y b ≠ 0 ∧ z b ≠ 0 then 1 else 0 := by
    rw [pairOverlapCount, Finset.card_filter]
  rw [hyCard, hzCard, hxorCard, hoverlapCard,
    ← Finset.sum_add_distrib, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact hsum

/-- The exact XOR/overlap character product is bounded by the exponential
envelope used in HHO20.  This analytic lemma is stated for an abstract
incidence density so that every numerical side condition is explicit. -/
theorem xorOverlapCharacterProduct_le_exp
    (p : Real) (xorWeight overlap : Nat)
    (hpHalf : p ≤ 1 / 2) :
    (1 - p) ^ xorWeight * (1 - 2 * p) ^ overlap ≤
      Real.exp
        (-p * ((xorWeight : Real) + 2 * (overlap : Real))) := by
  have hbaseOne0 : 0 ≤ 1 - p := by linarith
  have hbaseTwo0 : 0 ≤ 1 - 2 * p := by linarith
  have hbaseOneExp : 1 - p ≤ Real.exp (-p) := by
    linarith [Real.add_one_le_exp (-p)]
  have hbaseTwoExp : 1 - 2 * p ≤ Real.exp (-(2 * p)) := by
    linarith [Real.add_one_le_exp (-(2 * p))]
  have hpowOne :
      (1 - p) ^ xorWeight ≤ (Real.exp (-p)) ^ xorWeight :=
    pow_le_pow_left₀ hbaseOne0 hbaseOneExp xorWeight
  have hpowTwo :
      (1 - 2 * p) ^ overlap ≤
        (Real.exp (-(2 * p))) ^ overlap :=
    pow_le_pow_left₀ hbaseTwo0 hbaseTwoExp overlap
  calc
    (1 - p) ^ xorWeight * (1 - 2 * p) ^ overlap ≤
        (Real.exp (-p)) ^ xorWeight *
          (Real.exp (-(2 * p))) ^ overlap := by
      exact mul_le_mul hpowOne hpowTwo
        (pow_nonneg hbaseTwo0 overlap)
        (pow_nonneg (Real.exp_pos (-p)).le xorWeight)
    _ = Real.exp ((xorWeight : Real) * (-p)) *
          Real.exp ((overlap : Real) * (-(2 * p))) := by
      rw [Real.exp_nat_mul, Real.exp_nat_mul]
    _ = Real.exp
          (-p * ((xorWeight : Real) + 2 * (overlap : Real))) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The HHO20 parameter condition `Delta ≤ 2r` puts the sampled incidence
density below one half, including the degenerate `r = 0` case. -/
theorem incidenceProbability_toReal_le_half
    (r Delta : Nat) (hDeltaHalf : Delta ≤ 2 * r) :
    (RandomBase.incidenceProbability (4 * r) Delta).toReal ≤
      (1 : Real) / 2 := by
  cases r with
  | zero =>
      have hDeltaZero : Delta = 0 := by omega
      simp [hDeltaZero, RandomBase.incidenceProbability]
  | succ r =>
      simp only [RandomBase.incidenceProbability, NNReal.coe_div,
        NNReal.coe_natCast]
      rw [div_le_iff₀ (by positivity : (0 : Real) < (4 * (r + 1) : Nat))]
      have hDeltaHalfReal :
          (Delta : Real) ≤ 2 * (r + 1 : Nat) := by
        exact_mod_cast hDeltaHalf
      norm_num at hDeltaHalfReal ⊢
      linarith

/-- On the full HHO20 light-word range `0 ≤ x ≤ 8`, the one-row violation
probability has the uniform linear lower bound `x / 25 = .04 x`. -/
theorem div_twentyFive_le_one_sub_exp_neg_div_two
    (x : Real) (hx0 : 0 ≤ x) (hx8 : x ≤ 8) :
    x / 25 ≤ (1 - Real.exp (-x)) / 2 := by
  have hden : 0 < 1 + x := by linarith
  have hExpRecip : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg]
    simpa [one_div] using
      (inv_le_inv₀ (Real.exp_pos x) hden).2
        (by simpa [add_comm] using Real.add_one_le_exp x)
  have hlinearRecip :
      x / 25 ≤ (1 - 1 / (1 + x)) / 2 := by
    rw [show 1 - 1 / (1 + x) = x / (1 + x) by
      field_simp
      ring]
    rw [div_div]
    rw [div_le_div_iff₀ (by norm_num : (0 : Real) < 25)
      (by positivity : (0 : Real) < (1 + x) * 2)]
    nlinarith
  linarith

/-- HHO20 `prop:chi` exponential lower bound for one partition row. -/
theorem rowViolation_measureReal_ge_exp
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (hpHalf :
      (RandomBase.incidenceProbability (4 * r) Delta).toReal ≤
        1 / 2) :
    (1 -
      Real.exp
        (-(RandomBase.incidenceProbability (4 * r) Delta).toReal *
          ((HammingWeight y : Real) + HammingWeight z))) / 2 ≤
      (rowDistribution r Delta hDelta).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0} := by
  let p : Real :=
    (RandomBase.incidenceProbability (4 * r) Delta).toReal
  have hweight :
      (HammingWeight y : Real) + HammingWeight z =
        (HammingWeight (y + z) : Real) +
          2 * (pairOverlapCount y z : Real) := by
    exact_mod_cast hammingWeight_add_eq_add_two_pairOverlapCount y z
  have hcharacter :
      (1 - p) ^ HammingWeight (y + z) *
          (1 - 2 * p) ^ pairOverlapCount y z ≤
        Real.exp
          (-p * ((HammingWeight y : Real) + HammingWeight z)) := by
    rw [hweight]
    exact xorOverlapCharacterProduct_le_exp p
      (HammingWeight (y + z)) (pairOverlapCount y z) hpHalf
  rw [rowViolation_measureReal_closed r Delta hDelta y z]
  change
    (1 -
      Real.exp
        (-p * ((HammingWeight y : Real) + HammingWeight z))) / 2 ≤
      (1 -
        (1 - p) ^ HammingWeight (y + z) *
          (1 - 2 * p) ^ pairOverlapCount y z) / 2
  linarith

/-- Assumption-free-in-use form of `prop:chi`: the natural HHO20 scale
condition discharges the analytic density side condition. -/
theorem rowViolation_measureReal_ge_exp_of_Delta_le
    (r Delta : Nat) (hDeltaHalf : Delta ≤ 2 * r)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    (1 -
      Real.exp
        (-(RandomBase.incidenceProbability (4 * r) Delta).toReal *
          ((HammingWeight y : Real) + HammingWeight z))) / 2 ≤
      (rowDistribution r Delta (by omega)).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0} := by
  exact rowViolation_measureReal_ge_exp r Delta (by omega) y z
    (incidenceProbability_toReal_le_half r Delta hDeltaHalf)

/-- Linear `prop:chi` bound on the entire light-word range.  The integer
hypothesis is exactly `p (|y|+|z|) ≤ 8` after substituting
`p = Delta/(4r)`. -/
theorem rowViolation_measureReal_ge_linear
    (r Delta : Nat) (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (hTotal :
      Delta * (HammingWeight y + HammingWeight z) ≤ 32 * r) :
    (RandomBase.incidenceProbability (4 * r) Delta).toReal *
          ((HammingWeight y : Real) + HammingWeight z) / 25 ≤
      (rowDistribution r Delta (by omega)).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0} := by
  let p : Real :=
    (RandomBase.incidenceProbability (4 * r) Delta).toReal
  let total : Real :=
    (HammingWeight y : Real) + HammingWeight z
  have hp0 : 0 ≤ p := NNReal.zero_le_coe
  have htotal0 : 0 ≤ total := by positivity
  have hscale :
      ((4 * r : Nat) : Real) * p = Delta :=
    RandomBase.check_expected_degree r Delta hr
  have hTotalReal :
      (Delta : Real) * total ≤ 32 * r := by
    dsimp [total]
    exact_mod_cast hTotal
  have hFourRPos : (0 : Real) < (4 * r : Nat) := by positivity
  have hpTotal :
      p * total =
        ((Delta : Real) * total) / (4 * r : Nat) := by
    apply (eq_div_iff hFourRPos.ne').2
    nlinarith
  have hpTotal8 : p * total ≤ 8 := by
    rw [hpTotal]
    apply (div_le_iff₀ hFourRPos).2
    calc
      (Delta : Real) * total ≤ 32 * r := hTotalReal
      _ = 8 * (4 * r : Nat) := by push_cast; ring
  calc
    p * total / 25 ≤ (1 - Real.exp (-(p * total))) / 2 :=
      div_twentyFive_le_one_sub_exp_neg_div_two
        (p * total) (mul_nonneg hp0 htotal0) hpTotal8
    _ ≤
        (rowDistribution r Delta (by omega)).toMeasure.real
          {row | rowPairSyndrome row y z ≠ 0} := by
      simpa [p, total] using
        rowViolation_measureReal_ge_exp_of_Delta_le
          r Delta hDeltaHalf y z

/-- The two individual HHO20 light-word cutoffs imply the linear one-row
violation bound with no additional probabilistic assumption. -/
theorem rowViolation_measureReal_ge_linear_of_light
    (r Delta : Nat) (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (hy : Delta * HammingWeight y ≤ 4 * (4 * r))
    (hz : Delta * HammingWeight z ≤ 4 * (4 * r)) :
    (RandomBase.incidenceProbability (4 * r) Delta).toReal *
          ((HammingWeight y : Real) + HammingWeight z) / 25 ≤
      (rowDistribution r Delta (by omega)).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0} := by
  apply rowViolation_measureReal_ge_linear r Delta hr hDeltaHalf y z
  calc
    Delta * (HammingWeight y + HammingWeight z) =
        Delta * HammingWeight y + Delta * HammingWeight z := by
      exact Nat.mul_add _ _ _
    _ ≤ 4 * (4 * r) + 4 * (4 * r) := Nat.add_le_add hy hz
    _ = 32 * r := by omega

/-- The violation indicator for one named row of the full grouped sample. -/
noncomputable def sampleRowViolationIndicator
    {r : Nat}
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r))
    (sample : Sample r) : Real :=
  rowViolationIndicator y z (sample a)

/-- Each full-sample row indicator lies in `[0,1]`. -/
theorem sampleRowViolationIndicator_mem_Icc
    {r : Nat}
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r))
    (sample : Sample r) :
    sampleRowViolationIndicator y z a sample ∈ Set.Icc (0 : Real) 1 := by
  by_cases hviol : rowPairSyndrome (sample a) y z ≠ 0 <;>
    simp [sampleRowViolationIndicator, rowViolationIndicator, hviol]

/-- The expectation of a row indicator under the row law is its violation
probability. -/
theorem integral_rowViolationIndicator
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    ∫ row, rowViolationIndicator y z row ∂
        (rowDistribution r Delta hDelta).toMeasure =
      (rowDistribution r Delta hDelta).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0} := by
  rw [← integral_indicator_one
    (μ := (rowDistribution r Delta hDelta).toMeasure)
    (Set.toFinite _).measurableSet]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun row => by
    by_cases hviol : rowPairSyndrome row y z ≠ 0 <;>
      simp [rowViolationIndicator, Set.indicator, hviol]

/-- Every named row indicator has the same exact expectation under the full
independent-row law. -/
theorem integral_sampleRowViolationIndicator
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r)) :
    ∫ sample, sampleRowViolationIndicator y z a sample ∂
        (distribution r Delta hDelta).toMeasure =
      (rowDistribution r Delta hDelta).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0} := by
  calc
    _ =
        ∫ row, rowViolationIndicator y z row ∂
          (rowDistribution r Delta hDelta).toMeasure := by
      exact
        (distribution_row_hasLaw r Delta hDelta a).integral_comp
          ((Measurable.of_discrete :
            Measurable (rowViolationIndicator y z)).aestronglyMeasurable)
    _ = _ := integral_rowViolationIndicator r Delta hDelta y z

/-- Row-violation indicators are mutually independent. -/
theorem distribution_sampleRowViolationIndicator_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    ProbabilityTheory.iIndepFun
      (fun a => sampleRowViolationIndicator y z a)
      (distribution r Delta hDelta).toMeasure := by
  exact (distribution_row_iIndepFun r Delta hDelta).comp
    (fun _a row => rowViolationIndicator y z row)
    (fun _a => Measurable.of_discrete)

/-- Exact moment-generating function of one Bernoulli row-violation
indicator. -/
theorem mgf_sampleRowViolationIndicator
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r)) (t : Real) :
    ProbabilityTheory.mgf
        (sampleRowViolationIndicator y z a)
        (distribution r Delta hDelta).toMeasure t =
      1 -
        (rowDistribution r Delta hDelta).toMeasure.real
          {row | rowPairSyndrome row y z ≠ 0} +
        (rowDistribution r Delta hDelta).toMeasure.real
          {row | rowPairSyndrome row y z ≠ 0} * Real.exp t := by
  let μ : Real :=
    (rowDistribution r Delta hDelta).toMeasure.real
      {row | rowPairSyndrome row y z ≠ 0}
  rw [ProbabilityTheory.mgf]
  calc
    (∫ sample,
        Real.exp (t * sampleRowViolationIndicator y z a sample) ∂
          (distribution r Delta hDelta).toMeasure) =
        ∫ sample,
          (1 +
            sampleRowViolationIndicator y z a sample *
              (Real.exp t - 1)) ∂
            (distribution r Delta hDelta).toMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun sample => by
        by_cases hviol : rowPairSyndrome (sample a) y z ≠ 0 <;>
          simp [sampleRowViolationIndicator, rowViolationIndicator, hviol]
    _ = 1 + μ * (Real.exp t - 1) := by
      rw [integral_add, integral_mul_const,
        integral_sampleRowViolationIndicator r Delta hDelta y z a]
      · simp [μ]
      · exact Integrable.of_finite
      · exact Integrable.of_finite
    _ = _ := by
      dsimp [μ]
      ring

/-- Exact MGF of the violation count on any fixed row set. -/
theorem mgf_sum_sampleRowViolationIndicator
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (rows : Finset (Fin (3 * r))) (t : Real) :
    ProbabilityTheory.mgf
        (fun sample =>
          ∑ a ∈ rows, sampleRowViolationIndicator y z a sample)
        (distribution r Delta hDelta).toMeasure t =
      (1 -
        (rowDistribution r Delta hDelta).toMeasure.real
          {row | rowPairSyndrome row y z ≠ 0} +
        (rowDistribution r Delta hDelta).toMeasure.real
          {row | rowPairSyndrome row y z ≠ 0} * Real.exp t) ^
        rows.card := by
  have hSum :
      (fun sample =>
        ∑ a ∈ rows, sampleRowViolationIndicator y z a sample) =
        ∑ a ∈ rows, sampleRowViolationIndicator y z a := by
    funext sample
    simp
  rw [hSum]
  rw [(distribution_sampleRowViolationIndicator_iIndepFun
    r Delta hDelta y z).mgf_sum
      (fun _a => Measurable.of_discrete) rows]
  simp_rw [mgf_sampleRowViolationIndicator r Delta hDelta y z]
  rw [Finset.prod_const]

/-- Multiplicative Chernoff lower tail: fewer than one third of the exact
mean has probability at most `exp(-mean/6)`. -/
theorem measure_rowViolationSum_le_oneThirdMean_le
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (rows : Finset (Fin (3 * r))) :
    let μ :=
      (rowDistribution r Delta hDelta).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0}
    (distribution r Delta hDelta).toMeasure.real
        {sample |
          (∑ a ∈ rows,
            sampleRowViolationIndicator y z a sample) ≤
              μ * rows.card / 3} ≤
      Real.exp (-(μ * rows.card) / 6) := by
  dsimp only
  let μ : Real :=
    (rowDistribution r Delta hDelta).toMeasure.real
      {row | rowPairSyndrome row y z ≠ 0}
  let count : Sample r → Real :=
    fun sample =>
      ∑ a ∈ rows, sampleRowViolationIndicator y z a sample
  have hμ0 : 0 ≤ μ := measureReal_nonneg
  have hμ1 : μ ≤ 1 := measureReal_le_one
  have hExpHalf : Real.exp (-1) ≤ (1 : Real) / 2 := by
    rw [Real.exp_neg]
    have hTwoExp : (2 : Real) ≤ Real.exp 1 := by
      nlinarith [Real.add_one_le_exp (1 : Real)]
    simpa [one_div] using
      (inv_le_inv₀ (Real.exp_pos 1)
        (by norm_num : (0 : Real) < 2)).2 hTwoExp
  have hBase0 : 0 ≤ 1 - μ + μ * Real.exp (-1) := by
    nlinarith [Real.exp_pos (-1)]
  have hBaseExp :
      1 - μ + μ * Real.exp (-1) ≤
        Real.exp (μ * (Real.exp (-1) - 1)) := by
    convert Real.add_one_le_exp
      (μ * (Real.exp (-1) - 1)) using 1
    ring
  have hPow :
      (1 - μ + μ * Real.exp (-1)) ^ rows.card ≤
        Real.exp
          ((rows.card : Real) *
            (μ * (Real.exp (-1) - 1))) := by
    calc
      _ ≤ (Real.exp (μ * (Real.exp (-1) - 1))) ^ rows.card :=
        pow_le_pow_left₀ hBase0 hBaseExp rows.card
      _ = _ := by rw [Real.exp_nat_mul]
  have hChernoff :
      (distribution r Delta hDelta).toMeasure.real
          {sample | count sample ≤ μ * rows.card / 3} ≤
        Real.exp (-(-1 : Real) * (μ * rows.card / 3)) *
          ProbabilityTheory.mgf count
            (distribution r Delta hDelta).toMeasure (-1) := by
    exact ProbabilityTheory.measure_le_le_exp_mul_mgf
      (X := count) (μ * rows.card / 3)
      (show (-1 : Real) ≤ 0 by norm_num)
      Integrable.of_finite
  calc
    (distribution r Delta hDelta).toMeasure.real
        {sample |
          (∑ a ∈ rows,
            sampleRowViolationIndicator y z a sample) ≤
              μ * rows.card / 3} =
        (distribution r Delta hDelta).toMeasure.real
          {sample | count sample ≤ μ * rows.card / 3} := rfl
    _ ≤ Real.exp (-(-1 : Real) * (μ * rows.card / 3)) *
          ProbabilityTheory.mgf count
            (distribution r Delta hDelta).toMeasure (-1) :=
      hChernoff
    _ =
        Real.exp (μ * rows.card / 3) *
          (1 - μ + μ * Real.exp (-1)) ^ rows.card := by
      rw [show ProbabilityTheory.mgf count
          (distribution r Delta hDelta).toMeasure (-1) =
        (1 - μ + μ * Real.exp (-1)) ^ rows.card by
          simpa [count, μ] using
            mgf_sum_sampleRowViolationIndicator
              r Delta hDelta y z rows (-1)]
      congr 2
      ring
    _ ≤
        Real.exp (μ * rows.card / 3) *
          Real.exp
            ((rows.card : Real) *
              (μ * (Real.exp (-1) - 1))) := by
      exact mul_le_mul_of_nonneg_left hPow (Real.exp_pos _).le
    _ =
        Real.exp
          (μ * rows.card / 3 +
            (rows.card : Real) *
              (μ * (Real.exp (-1) - 1))) := by
      rw [Real.exp_add]
    _ ≤ Real.exp (-(μ * rows.card) / 6) := by
      apply Real.exp_le_exp_of_le
      have hRows0 : (0 : Real) ≤ rows.card := by positivity
      have hmul :
          μ * (rows.card : Real) * Real.exp (-1) ≤
            μ * (rows.card : Real) / 2 := by
        calc
          _ ≤ μ * (rows.card : Real) * ((1 : Real) / 2) :=
            mul_le_mul_of_nonneg_left hExpHalf
              (mul_nonneg hμ0 hRows0)
          _ = _ := by ring
      nlinarith

/-- Centered row-violation indicator. -/
noncomputable def centeredSampleRowViolationIndicator
    {r : Nat}
    (Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r))
    (sample : Sample r) : Real :=
  sampleRowViolationIndicator y z a sample -
    (rowDistribution r Delta hDelta).toMeasure.real
      {row | rowPairSyndrome row y z ≠ 0}

/-- Centered row indicators are sub-Gaussian with the sharp Hoeffding
parameter `1/4` for variables in `[0,1]`. -/
theorem centeredSampleRowViolationIndicator_hasSubgaussianMGF
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r)) :
    ProbabilityTheory.HasSubgaussianMGF
      (centeredSampleRowViolationIndicator Delta hDelta y z a)
      (1 / 4 : NNReal)
      (distribution r Delta hDelta).toMeasure := by
  have h :=
    ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
      (μ := (distribution r Delta hDelta).toMeasure)
      (X := sampleRowViolationIndicator y z a)
      (a := (0 : Real)) (b := (1 : Real))
      (Measurable.of_discrete.aemeasurable)
      (Filter.Eventually.of_forall fun sample =>
        sampleRowViolationIndicator_mem_Icc y z a sample)
  convert h using 1
  · funext sample
    simp only [centeredSampleRowViolationIndicator]
    rw [integral_sampleRowViolationIndicator r Delta hDelta y z a]
  · norm_num

/-- Centering by the common deterministic row mean preserves mutual
independence. -/
theorem distribution_centeredSampleRowViolationIndicator_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    ProbabilityTheory.iIndepFun
      (fun a =>
        centeredSampleRowViolationIndicator Delta hDelta y z a)
      (distribution r Delta hDelta).toMeasure := by
  exact
    (distribution_sampleRowViolationIndicator_iIndepFun
      r Delta hDelta y z).comp
      (fun _a x =>
        x -
          (rowDistribution r Delta hDelta).toMeasure.real
            {row | rowPairSyndrome row y z ≠ 0})
      (fun _a => by fun_prop)

/-- Hoeffding lower tail for the violation count on any fixed set of rows. -/
theorem measure_centeredRowViolationSum_le_neg_le
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (rows : Finset (Fin (3 * r)))
    (ε : Real) (hε : 0 ≤ ε) :
    (distribution r Delta hDelta).toMeasure.real
        {sample |
          (∑ a ∈ rows,
            centeredSampleRowViolationIndicator
              Delta hDelta y z a sample) ≤ -ε} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ↑(∑ _a ∈ rows, (1 / 4 : NNReal)))) := by
  have hIndep :
      ProbabilityTheory.iIndepFun
        (fun a sample =>
          -centeredSampleRowViolationIndicator
            Delta hDelta y z a sample)
        (distribution r Delta hDelta).toMeasure :=
    (distribution_centeredSampleRowViolationIndicator_iIndepFun
      r Delta hDelta y z).comp
      (fun _a x => -x) (fun _a => by fun_prop)
  have hRaw :=
    ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (s := rows)
      (c := fun _a : Fin (3 * r) => (1 / 4 : NNReal))
      hIndep
      (fun a _ha =>
        (centeredSampleRowViolationIndicator_hasSubgaussianMGF
          r Delta hDelta y z a).neg)
      hε
  calc
    _ =
        (distribution r Delta hDelta).toMeasure.real
          {sample |
            ε ≤
              ∑ a ∈ rows,
                -centeredSampleRowViolationIndicator
                  Delta hDelta y z a sample} := by
      congr 1
      ext sample
      simp only [Set.mem_setOf_eq, Finset.sum_neg_distrib]
      constructor <;> intro h <;> linarith
    _ ≤ _ := hRaw

/-- The deterministic cyclic fiber of rows assigned to one check type. -/
noncomputable def typeRows
    (r typeCount : Nat) [NeZero typeCount]
    (τ : Fin typeCount) : Finset (Fin (3 * r)) :=
  Finset.univ.filter fun a => RandomTwist.checkType typeCount a = τ

/-- Number of violated rows in one cyclic type fiber, expressed directly on
the grouped sampler. -/
noncomputable def groupedTypeViolationCount
    {r typeCount : Nat} [NeZero typeCount]
    (sample : Sample r)
    (τ : Fin typeCount)
    (y z : Word (ZMod 2) (Fin (4 * r))) : Nat :=
  ((typeRows r typeCount τ).filter fun a =>
    rowPairSyndrome (sample a) y z ≠ 0).card

/-- The real sum of row indicators is the cast of the grouped natural
violation count. -/
theorem sum_sampleRowViolationIndicator_typeRows_eq_groupedCount
    {r typeCount : Nat} [NeZero typeCount]
    (sample : Sample r)
    (τ : Fin typeCount)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    (∑ a ∈ typeRows r typeCount τ,
        sampleRowViolationIndicator y z a sample) =
      (groupedTypeViolationCount sample τ y z : Real) := by
  classical
  simp only [groupedTypeViolationCount, Finset.card_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hviol : rowPairSyndrome (sample a) y z ≠ 0 <;>
    simp [sampleRowViolationIndicator, rowViolationIndicator, hviol]

/-- Summing grouped row indicators over a type fiber is definitionally the
existing deterministic `typeViolationCount`, for every choice of type
shifts.  Thus partitioned-check events do not depend on the spectrum
randomness. -/
theorem sum_sampleRowViolationIndicator_typeRows_eq
    {r typeCount ell : Nat} [NeZero typeCount]
    (sample : Sample r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (τ : Fin typeCount)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    (∑ a ∈ typeRows r typeCount τ,
        sampleRowViolationIndicator y z a sample) =
      (TwistGraph.typeViolationCount
        (baseSample sample) (twistSample sample typeShifts)
        τ y z : Real) := by
  classical
  simp only [TwistGraph.typeViolationCount, TwistGraph.typeViolationSet,
    typeRows, sampleRowViolationIndicator, rowViolationIndicator,
    Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [pairCheckSyndrome_baseSample_twistSample sample typeShifts y z a]
  by_cases htype : RandomTwist.checkType typeCount a = τ
  · simp [htype]
  · simp [htype]

/-- Natural-number version of the bridge to deterministic
`typeViolationCount`. -/
theorem groupedTypeViolationCount_eq_typeViolationCount
    {r typeCount ell : Nat} [NeZero typeCount]
    (sample : Sample r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (τ : Fin typeCount)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    groupedTypeViolationCount sample τ y z =
      TwistGraph.typeViolationCount
        (baseSample sample) (twistSample sample typeShifts)
        τ y z := by
  exact_mod_cast
    (sum_sampleRowViolationIndicator_typeRows_eq_groupedCount
      sample τ y z).symm.trans
      (sum_sampleRowViolationIndicator_typeRows_eq
        sample typeShifts τ y z)

/-- When the cyclic type partition divides the number of base checks, every
type receives exactly `3r/typeCount` rows. -/
theorem card_typeRows_of_dvd
    (r typeCount : Nat) [NeZero typeCount]
    (hDvd : typeCount ∣ 3 * r)
    (τ : Fin typeCount) :
    (typeRows r typeCount τ).card = (3 * r) / typeCount := by
  classical
  let q := (3 * r) / typeCount
  have hEq : q * typeCount = 3 * r := Nat.div_mul_cancel hDvd
  let castEquiv : Fin (q * typeCount) ≃ Fin (3 * r) :=
    (Fin.castOrderIso hEq).toEquiv
  let fullEquiv : Fin q × Fin typeCount ≃ Fin (3 * r) :=
    finProdFinEquiv.trans castEquiv
  let rowEmbedding : Fin q ↪ Fin (3 * r) :=
    ⟨fun j => fullEquiv (j, τ), fun j k hjk => by
      have hpair : (j, τ) = (k, τ) := fullEquiv.injective hjk
      exact congrArg Prod.fst hpair⟩
  have hRows :
      typeRows r typeCount τ =
        (Finset.univ : Finset (Fin q)).map rowEmbedding := by
    ext a
    simp only [typeRows, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_map]
    constructor
    · intro ha
      let pair := fullEquiv.symm a
      have hsecond : pair.2 = τ := by
        apply Fin.ext
        simp only [pair, fullEquiv, Equiv.symm_trans_apply,
          finProdFinEquiv_symm_apply]
        change ((castEquiv.symm a).val % typeCount) = τ.val
        rw [show (castEquiv.symm a).val = a.val by
          simp [castEquiv, Fin.val_cast]]
        exact congrArg Fin.val ha
      refine ⟨pair.1, ?_⟩
      change fullEquiv (pair.1, τ) = a
      rw [show (pair.1, τ) = pair by
        ext <;> simp [hsecond]]
      exact fullEquiv.apply_symm_apply a
    · rintro ⟨j, rfl⟩
      apply Fin.ext
      change (τ.val + typeCount * j.val) % typeCount = τ.val
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt τ.isLt]
  rw [hRows, Finset.card_map]
  simp [q]

/-- The exact type-fiber size and the `.04 p t` row bound give expected
type violations at least `.03 Delta t / typeCount`, in integer-cleared
form. -/
theorem three_delta_total_le_expected_type_violations
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (τ : Fin typeCount)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (hy : Delta * HammingWeight y ≤ 4 * (4 * r))
    (hz : Delta * HammingWeight z ≤ 4 * (4 * r)) :
    3 * (Delta : Real) *
          ((HammingWeight y : Real) + HammingWeight z) ≤
      100 * typeCount *
        ((rowDistribution r Delta (by omega)).toMeasure.real
            {row | rowPairSyndrome row y z ≠ 0} *
          (typeRows r typeCount τ).card) := by
  let p : Real :=
    (RandomBase.incidenceProbability (4 * r) Delta).toReal
  let total : Real :=
    (HammingWeight y : Real) + HammingWeight z
  let μ : Real :=
    (rowDistribution r Delta (by omega)).toMeasure.real
      {row | rowPairSyndrome row y z ≠ 0}
  have hμ :
      p * total / 25 ≤ μ := by
    simpa [p, total, μ] using
      rowViolation_measureReal_ge_linear_of_light
        r Delta hr hDeltaHalf y z hy hz
  have hCard :
      ((typeRows r typeCount τ).card : Real) =
        ((3 * r) / typeCount : Nat) := by
    exact_mod_cast card_typeRows_of_dvd r typeCount hTypeDvd τ
  have hTypeScaleNat :
      ((3 * r) / typeCount) * typeCount = 3 * r :=
    Nat.div_mul_cancel hTypeDvd
  have hTypeScale :
      (((3 * r) / typeCount : Nat) : Real) *
          typeCount = 3 * r := by
    exact_mod_cast hTypeScaleNat
  have hIncidenceScale :
      ((4 * r : Nat) : Real) * p = Delta := by
    exact RandomBase.check_expected_degree r Delta hr
  have hExact :
      100 * (typeCount : Real) *
          ((p * total / 25) *
            ((3 * r) / typeCount : Nat)) =
        3 * (Delta : Real) * total := by
    calc
      _ = 4 *
          ((((3 * r) / typeCount : Nat) : Real) * typeCount) *
          p * total := by ring
      _ = 4 * (3 * (r : Real)) * p * total := by rw [hTypeScale]
      _ = 3 * (((4 * r : Nat) : Real) * p) * total := by
        push_cast
        ring
      _ = 3 * (Delta : Real) * total := by rw [hIncidenceScale]
  change
    3 * (Delta : Real) * total ≤
      100 * typeCount * (μ * (typeRows r typeCount τ).card)
  rw [← hExact, hCard]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hμ (by positivity))
    (by positivity)

/-- Fixed-type, fixed-word light-check failure probability. -/
theorem measure_groupedLightFailure_le
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (τ : Fin typeCount)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (hy : Delta * HammingWeight y ≤ 4 * (4 * r))
    (hz : Delta * HammingWeight z ≤ 4 * (4 * r)) :
    (distribution r Delta (by omega)).toMeasure.real
        {sample |
          100 * typeCount *
              groupedTypeViolationCount sample τ y z <
            Delta * (HammingWeight y + HammingWeight z)} ≤
      Real.exp
        (-((Delta : Real) *
            ((HammingWeight y : Real) + HammingWeight z)) /
          (200 * typeCount)) := by
  let hDelta : Delta ≤ 4 * r := by omega
  let rows := typeRows r typeCount τ
  let μ : Real :=
    (rowDistribution r Delta hDelta).toMeasure.real
      {row | rowPairSyndrome row y z ≠ 0}
  let total : Real :=
    (HammingWeight y : Real) + HammingWeight z
  have hTypePos : (0 : Real) < typeCount := by
    exact_mod_cast NeZero.pos typeCount
  have hExpected :
      3 * (Delta : Real) * total ≤
        100 * typeCount * (μ * rows.card) := by
    simpa [hDelta, rows, μ, total] using
      three_delta_total_le_expected_type_violations
        r Delta typeCount hr hDeltaHalf hTypeDvd τ y z hy hz
  have hSubset :
      {sample |
        100 * typeCount *
            groupedTypeViolationCount sample τ y z <
          Delta * (HammingWeight y + HammingWeight z)} ⊆
        {sample |
          (∑ a ∈ rows,
            sampleRowViolationIndicator y z a sample) ≤
              μ * rows.card / 3} := by
    intro sample hbad
    have hbadReal :
        100 * (typeCount : Real) *
            (groupedTypeViolationCount sample τ y z : Real) ≤
          (Delta : Real) * total := by
      dsimp [total]
      exact_mod_cast (Nat.le_of_lt hbad)
    change
      (∑ a ∈ rows,
        sampleRowViolationIndicator y z a sample) ≤
          μ * rows.card / 3
    rw [show rows = typeRows r typeCount τ by rfl,
      sum_sampleRowViolationIndicator_typeRows_eq_groupedCount]
    have hden : (0 : Real) < 100 * typeCount := by positivity
    apply (le_div_iff₀ (by norm_num : (0 : Real) < 3)).2
    apply (le_of_mul_le_mul_left
      (a := (100 : Real) * typeCount) _ hden)
    nlinarith
  calc
    _ ≤
        (distribution r Delta hDelta).toMeasure.real
          {sample |
            (∑ a ∈ rows,
              sampleRowViolationIndicator y z a sample) ≤
                μ * rows.card / 3} :=
      measureReal_mono hSubset
    _ ≤ Real.exp (-(μ * rows.card) / 6) := by
      simpa [rows, μ] using
        measure_rowViolationSum_le_oneThirdMean_le
          r Delta hDelta y z rows
    _ ≤
        Real.exp
          (-((Delta : Real) * total) /
            (200 * typeCount)) := by
      apply Real.exp_le_exp_of_le
      have hden : (0 : Real) < 200 * typeCount := by positivity
      rw [show -(μ * rows.card) / 6 =
          -(μ * rows.card / 6) by ring,
        show -((Delta : Real) * total) / (200 * typeCount) =
          -((Delta : Real) * total / (200 * typeCount)) by ring]
      apply neg_le_neg
      rw [div_le_div_iff₀ hden (by norm_num : (0 : Real) < 6)]
      nlinarith

/-- Binary words are equivalent to their finite supports. -/
noncomputable def binaryWordFinsetEquiv (r : Nat) :
    Word (ZMod 2) (Fin (4 * r)) ≃ Finset (Fin (4 * r)) where
  toFun := hammingSupport
  invFun := RandomBase.supportWord
  left_inv := RandomBase.supportWord_hammingSupport
  right_inv := RandomBase.hammingSupport_supportWord

/-- Binary Hamming-weight generating function. -/
theorem sum_binaryWord_pow_hammingWeight
    (r : Nat) (t : Real) :
    (∑ y : Word (ZMod 2) (Fin (4 * r)),
        t ^ HammingWeight y) =
      (1 + t) ^ (4 * r) := by
  classical
  calc
    _ =
        ∑ A : Finset (Fin (4 * r)), t ^ A.card := by
      exact Fintype.sum_equiv
        (binaryWordFinsetEquiv r)
        (fun y : Word (ZMod 2) (Fin (4 * r)) =>
          t ^ HammingWeight y)
        (fun A : Finset (Fin (4 * r)) => t ^ A.card)
        (fun y => by
          simp [binaryWordFinsetEquiv,
            HammingWeight_eq_card_hammingSupport])
    _ =
        ∑ A ∈ (Finset.univ : Finset (Fin (4 * r))).powerset,
          t ^ A.card := by
      rw [Finset.powerset_univ]
    _ = (1 + t) ^ (4 * r) := by
      rw [Finset.sum_powerset_apply_card]
      simpa [nsmul_eq_mul, mul_comm, add_comm] using
        (add_pow t 1 (4 * r)).symm

/-- Weight generating function for ordered pairs of binary words. -/
theorem sum_binaryWordPair_pow_totalWeight
    (r : Nat) (t : Real) :
    (∑ y : Word (ZMod 2) (Fin (4 * r)),
      ∑ z : Word (ZMod 2) (Fin (4 * r)),
        t ^ (HammingWeight y + HammingWeight z)) =
      (1 + t) ^ (8 * r) := by
  calc
    _ =
        (∑ y : Word (ZMod 2) (Fin (4 * r)),
          t ^ HammingWeight y) *
        (∑ z : Word (ZMod 2) (Fin (4 * r)),
          t ^ HammingWeight z) := by
      simp_rw [pow_add]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.mul_sum]
    _ = (1 + t) ^ (4 * r) * (1 + t) ^ (4 * r) := by
      simp only [sum_binaryWord_pow_hammingWeight]
    _ = (1 + t) ^ (8 * r) := by
      rw [← pow_add]
      congr 1
      omega

/-- Ordered nonzero pairs of binary words. -/
abbrev NonzeroWordPair (r : Nat) :=
  {pair :
      Word (ZMod 2) (Fin (4 * r)) ×
        Word (ZMod 2) (Fin (4 * r)) //
    pair ≠ (0, 0)}

noncomputable instance instFintypeNonzeroWordPair (r : Nat) :
    Fintype (NonzeroWordPair r) := by
  classical
  exact Subtype.fintype _

/-- Removing the all-zero word pair removes exactly the constant term from
the pair weight enumerator. -/
theorem sum_nonzeroBinaryWordPair_pow_totalWeight
    (r : Nat) (t : Real) :
    (∑ pair : NonzeroWordPair r,
        t ^
          (HammingWeight pair.1.1 +
            HammingWeight pair.1.2)) =
      (1 + t) ^ (8 * r) - 1 := by
  classical
  let weight :
      Word (ZMod 2) (Fin (4 * r)) ×
          Word (ZMod 2) (Fin (4 * r)) → Real :=
    fun pair =>
      t ^ (HammingWeight pair.1 + HammingWeight pair.2)
  have hFull :
      (∑ pair :
          Word (ZMod 2) (Fin (4 * r)) ×
            Word (ZMod 2) (Fin (4 * r)),
          weight pair) =
        (1 + t) ^ (8 * r) := by
    simpa [weight, Fintype.sum_prod_type] using
      sum_binaryWordPair_pow_totalWeight r t
  rw [Fintype.sum_eq_add_sum_subtype_ne weight (0, 0)] at hFull
  have hZero : weight (0, 0) = 1 := by
    simp [weight]
  rw [hZero] at hFull
  have hFull' :
      1 + (∑ pair : NonzeroWordPair r, weight pair.1) =
        (1 + t) ^ (8 * r) := by
    simpa only using hFull
  change
    (∑ pair : {pair :
        Word (ZMod 2) (Fin (4 * r)) ×
          Word (ZMod 2) (Fin (4 * r)) //
        pair ≠ (0, 0)}, weight pair.1) =
      (1 + t) ^ (8 * r) - 1
  linarith [hFull']

/-- A fixed check type together with a nonzero pair of candidate words. -/
abbrev LightFailureIndex (r typeCount : Nat) :=
  Fin typeCount × NonzeroWordPair r

/-- The bad event for one nonzero type/word triple; pairs outside the HHO20
light range contribute the empty event. -/
noncomputable def groupedLightBadAt
    (r Delta typeCount : Nat) [NeZero typeCount]
    (index : LightFailureIndex r typeCount) :
    Set (Sample r) :=
  if
      Delta * HammingWeight index.2.1.1 ≤ 4 * (4 * r) ∧
      Delta * HammingWeight index.2.1.2 ≤ 4 * (4 * r)
    then
      {sample |
        100 * typeCount *
            groupedTypeViolationCount sample index.1
              index.2.1.1 index.2.1.2 <
          Delta *
            (HammingWeight index.2.1.1 +
              HammingWeight index.2.1.2)}
    else ∅

/-- The grouped sampler satisfies all HHO20 light-check inequalities. -/
def HasGroupedHHO20LightChecks
    {r typeCount : Nat} [NeZero typeCount]
    (Delta : Nat) (sample : Sample r) : Prop :=
  ∀ (τ : Fin typeCount)
      (y z : Word (ZMod 2) (Fin (4 * r))),
    Delta * HammingWeight y ≤ 4 * (4 * r) →
    Delta * HammingWeight z ≤ 4 * (4 * r) →
      Delta * (HammingWeight y + HammingWeight z) ≤
        100 * typeCount * groupedTypeViolationCount sample τ y z

/-- Failure of the simultaneous grouped light event is covered by the
finite union of nonzero fixed-triple bad events. -/
theorem groupedLightFailure_subset_iUnion_badAt
    (r Delta typeCount : Nat) [NeZero typeCount] :
    {sample | ¬ HasGroupedHHO20LightChecks
      (r := r) (typeCount := typeCount) Delta sample} ⊆
      ⋃ index : LightFailureIndex r typeCount,
        groupedLightBadAt r Delta typeCount index := by
  intro sample hFailure
  simp only [HasGroupedHHO20LightChecks] at hFailure
  push Not at hFailure
  obtain ⟨τ, y, z, hy, hz, hbad⟩ := hFailure
  have hpair : (y, z) ≠ (0, 0) := by
    intro hzero
    have hy0 : y = 0 := congrArg Prod.fst hzero
    have hz0 : z = 0 := congrArg Prod.snd hzero
    rw [hy0, hz0] at hbad
    simp at hbad
  refine Set.mem_iUnion.2
    ⟨(τ, ⟨(y, z), hpair⟩), ?_⟩
  simp only [groupedLightBadAt, hy, hz, and_self, if_true,
    Set.mem_setOf_eq]
  exact hbad

/-- Fixed-index bound in geometric-weight form. -/
theorem measure_groupedLightBadAt_le_pow
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (index : LightFailureIndex r typeCount) :
    (distribution r Delta (by omega)).toMeasure.real
        (groupedLightBadAt r Delta typeCount index) ≤
      (Real.exp
        (-(Delta : Real) / (200 * typeCount))) ^
          (HammingWeight index.2.1.1 +
            HammingWeight index.2.1.2) := by
  by_cases hLight :
      Delta * HammingWeight index.2.1.1 ≤ 4 * (4 * r) ∧
      Delta * HammingWeight index.2.1.2 ≤ 4 * (4 * r)
  · rw [groupedLightBadAt, if_pos hLight]
    refine (measure_groupedLightFailure_le
      r Delta typeCount hr hDeltaHalf hTypeDvd
      index.1 index.2.1.1 index.2.1.2 hLight.1 hLight.2).trans_eq ?_
    calc
      Real.exp
          (-((Delta : Real) *
            ((HammingWeight index.2.1.1 : Real) +
              HammingWeight index.2.1.2)) /
            (200 * typeCount)) =
          Real.exp
            (((HammingWeight index.2.1.1 +
                HammingWeight index.2.1.2 : Nat) : Real) *
              (-(Delta : Real) / (200 * typeCount))) := by
        congr 1
        push_cast
        ring
      _ =
          (Real.exp
            (-(Delta : Real) / (200 * typeCount))) ^
              (HammingWeight index.2.1.1 +
                HammingWeight index.2.1.2) := by
        rw [Real.exp_nat_mul]
  · rw [groupedLightBadAt, if_neg hLight]
    simp only [measureReal_empty]
    positivity

/-- Summing geometric weights over all type/nonzero-word indices. -/
theorem sum_lightFailureIndex_pow_totalWeight
    (r typeCount : Nat)
    (t : Real) :
    (∑ index : LightFailureIndex r typeCount,
        t ^
          (HammingWeight index.2.1.1 +
            HammingWeight index.2.1.2)) =
      typeCount * ((1 + t) ^ (8 * r) - 1) := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [sum_nonzeroBinaryWordPair_pow_totalWeight]

/-- Simultaneous light-check failure mass, before discharging the final
numeric geometric-series inequality. -/
theorem measure_groupedHHO20LightFailure_le
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r) :
    (distribution r Delta (by omega)).toMeasure.real
        {sample | ¬ HasGroupedHHO20LightChecks
          (r := r) (typeCount := typeCount) Delta sample} ≤
      typeCount *
        ((1 +
          Real.exp
            (-(Delta : Real) / (200 * typeCount))) ^
              (8 * r) - 1) := by
  let badAt : LightFailureIndex r typeCount → Set (Sample r) :=
    groupedLightBadAt r Delta typeCount
  calc
    _ ≤
        (distribution r Delta (by omega)).toMeasure.real
          (⋃ index : LightFailureIndex r typeCount, badAt index) :=
      measureReal_mono
        (groupedLightFailure_subset_iUnion_badAt
          r Delta typeCount)
    _ ≤
        ∑ index : LightFailureIndex r typeCount,
          (distribution r Delta (by omega)).toMeasure.real
            (badAt index) :=
      measureReal_iUnion_fintype_le badAt
    _ ≤
        ∑ index : LightFailureIndex r typeCount,
          (Real.exp
            (-(Delta : Real) / (200 * typeCount))) ^
              (HammingWeight index.2.1.1 +
                HammingWeight index.2.1.2) := by
      apply Finset.sum_le_sum
      intro index _hindex
      exact measure_groupedLightBadAt_le_pow
        r Delta typeCount hr hDeltaHalf hTypeDvd index
    _ = _ :=
      sum_lightFailureIndex_pow_totalWeight r typeCount
        (Real.exp
          (-(Delta : Real) / (200 * typeCount)))

/-- A grouped light-good sample exists whenever the explicit geometric union
bound is below one. -/
theorem exists_sample_hasGroupedHHO20LightChecks
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hNumeric :
      (typeCount : Real) *
        ((1 +
          Real.exp
            (-(Delta : Real) / (200 * typeCount))) ^
              (8 * r) - 1) < 1) :
    ∃ sample : Sample r,
      HasGroupedHHO20LightChecks
        (r := r) (typeCount := typeCount) Delta sample := by
  let μ := (distribution r Delta (by omega)).toMeasure
  have hBadLt :
      μ.real
          {sample | ¬ HasGroupedHHO20LightChecks
            (r := r) (typeCount := typeCount) Delta sample} < 1 :=
    lt_of_le_of_lt
      (measure_groupedHHO20LightFailure_le
        r Delta typeCount hr hDeltaHalf hTypeDvd)
      hNumeric
  by_contra hNoGood
  push Not at hNoGood
  have hBadUniv :
      {sample : Sample r |
        ¬ HasGroupedHHO20LightChecks
          (r := r) (typeCount := typeCount) Delta sample} =
        Set.univ :=
    Set.eq_univ_of_forall hNoGood
  have hMeasureOne :
      μ.real
          {sample | ¬ HasGroupedHHO20LightChecks
            (r := r) (typeCount := typeCount) Delta sample} = 1 := by
    rw [hBadUniv]
    simp [μ]
  linarith

/-- A simple scale condition on the one-coordinate geometric factor
discharges the simultaneous light-event union bound. -/
theorem light_geometric_union_lt_one_of_exp_lt
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r)
    (hExpSmall :
      Real.exp
          (-(Delta : Real) / (200 * typeCount)) <
        1 / (16 * r * typeCount : Nat)) :
    (typeCount : Real) *
        ((1 +
          Real.exp
            (-(Delta : Real) / (200 * typeCount))) ^
              (8 * r) - 1) < 1 := by
  let t : Real :=
    Real.exp (-(Delta : Real) / (200 * typeCount))
  let x : Real := (8 * r : Nat) * t
  have ht0 : 0 ≤ t := (Real.exp_pos _).le
  have hTypeOne : (1 : Real) ≤ typeCount := by
    exact_mod_cast NeZero.pos typeCount
  have hDenPos : (0 : Real) < (16 * r * typeCount : Nat) := by
    exact_mod_cast
      Nat.mul_pos (Nat.mul_pos (by omega) hr) (NeZero.pos typeCount)
  have hSmallMul :
      t * (16 * r * typeCount : Nat) < 1 := by
    exact (lt_div_iff₀ hDenPos).1 (by simpa [t] using hExpSmall)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    have hrReal : (0 : Real) < r := by exact_mod_cast hr
    push_cast at hSmallMul ⊢
    have hfactor :
        8 * (r : Real) * t ≤
          8 * (r : Real) * t * typeCount := by
      exact le_mul_of_one_le_right
        (mul_nonneg (by positivity) ht0) hTypeOne
    nlinarith
  have hPowExp :
      (1 + t) ^ (8 * r) ≤ Real.exp x := by
    calc
      _ ≤ (Real.exp t) ^ (8 * r) :=
        pow_le_pow_left₀ (by positivity)
          (by simpa [add_comm] using Real.add_one_le_exp t)
          (8 * r)
      _ = Real.exp ((8 * r : Nat) * t) := by
        rw [Real.exp_nat_mul]
      _ = Real.exp x := rfl
  have hExpLinear : Real.exp x - 1 ≤ 2 * x := by
    have hAbs :=
      Real.abs_exp_sub_one_le
        (show |x| ≤ 1 by simpa [abs_of_nonneg hx0] using hx1)
    calc
      Real.exp x - 1 ≤ |Real.exp x - 1| := le_abs_self _
      _ ≤ 2 * |x| := hAbs
      _ = 2 * x := by rw [abs_of_nonneg hx0]
  calc
    (typeCount : Real) * ((1 + t) ^ (8 * r) - 1) ≤
        typeCount * (Real.exp x - 1) := by
      gcongr
    _ ≤ typeCount * (2 * x) := by
      gcongr
    _ < 1 := by
      dsimp [x] at *
      push_cast at hSmallMul ⊢
      nlinarith

/-- A logarithmic HHO20 scale inequality implies the exponential smallness
condition used by the light-event union bound. -/
theorem exp_neg_delta_div_lt_of_log_scale
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r)
    (hLogScale :
      200 * (typeCount : Real) *
          Real.log (16 * r * typeCount : Nat) <
        Delta) :
    Real.exp
        (-(Delta : Real) / (200 * typeCount)) <
      1 / (16 * r * typeCount : Nat) := by
  have hTypePos : (0 : Real) < typeCount := by
    exact_mod_cast NeZero.pos typeCount
  have hDenPos : (0 : Real) < (16 * r * typeCount : Nat) := by
    exact_mod_cast
      Nat.mul_pos (Nat.mul_pos (by omega) hr) (NeZero.pos typeCount)
  have hScalePos : (0 : Real) < 200 * typeCount := by positivity
  have hLogDiv :
      Real.log (16 * r * typeCount : Nat) <
        (Delta : Real) / (200 * typeCount) := by
    apply (lt_div_iff₀ hScalePos).2
    nlinarith
  have hExp :
      Real.exp (-(Delta : Real) / (200 * typeCount)) <
        Real.exp (-Real.log (16 * r * typeCount : Nat)) := by
    apply Real.exp_lt_exp.mpr
    simpa only [neg_div] using neg_lt_neg hLogDiv
  calc
    _ < Real.exp (-Real.log (16 * r * typeCount : Nat)) := hExp
    _ = 1 / (16 * r * typeCount : Nat) := by
      rw [Real.exp_neg, Real.exp_log hDenPos]
      rw [one_div]

/-- Light-check existence under the simpler explicit exponential scale
condition. -/
theorem exists_sample_hasGroupedHHO20LightChecks_of_exp_lt
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hExpSmall :
      Real.exp
          (-(Delta : Real) / (200 * typeCount)) <
        1 / (16 * r * typeCount : Nat)) :
    ∃ sample : Sample r,
      HasGroupedHHO20LightChecks
        (r := r) (typeCount := typeCount) Delta sample :=
  exists_sample_hasGroupedHHO20LightChecks
    r Delta typeCount hr hDeltaHalf hTypeDvd
      (light_geometric_union_lt_one_of_exp_lt
        r Delta typeCount hr hExpSmall)

/-- Light-check existence under the paper-natural logarithmic scale
condition. -/
theorem exists_sample_hasGroupedHHO20LightChecks_of_log_scale
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hLogScale :
      200 * (typeCount : Real) *
          Real.log (16 * r * typeCount : Nat) <
        Delta) :
    ∃ sample : Sample r,
      HasGroupedHHO20LightChecks
        (r := r) (typeCount := typeCount) Delta sample :=
  exists_sample_hasGroupedHHO20LightChecks_of_exp_lt
    r Delta typeCount hr hDeltaHalf hTypeDvd
      (exp_neg_delta_div_lt_of_log_scale
        r Delta typeCount hr hLogScale)

/-- The grouped light event is exactly strong enough for the deterministic
HHO20 light-check interface, independently of the chosen type shifts. -/
theorem hasHHO20LightChecks_of_hasGrouped
    {r Delta typeCount ell : Nat} [NeZero typeCount]
    (sample : Sample r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (hGrouped :
      HasGroupedHHO20LightChecks
        (r := r) (typeCount := typeCount) Delta sample) :
    TwistGraph.HasHHO20LightChecks Delta
      (baseSample sample) (twistSample sample typeShifts) := by
  intro τ y z hy hz
  rw [← groupedTypeViolationCount_eq_typeViolationCount
    sample typeShifts τ y z]
  exact hGrouped τ y z hy hz

/-- Public light-check existence statement: one partition sample works for
every independently selected spectrum-shift vector. -/
theorem exists_sample_forall_typeShifts_hasHHO20LightChecks
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hNumeric :
      (typeCount : Real) *
        ((1 +
          Real.exp
            (-(Delta : Real) / (200 * typeCount))) ^
              (8 * r) - 1) < 1) :
    ∃ sample : Sample r,
      ∀ typeShifts : Fin typeCount → Fin (ell - 1),
        TwistGraph.HasHHO20LightChecks Delta
          (baseSample sample) (twistSample sample typeShifts) := by
  obtain ⟨sample, hGrouped⟩ :=
    exists_sample_hasGroupedHHO20LightChecks
      r Delta typeCount hr hDeltaHalf hTypeDvd hNumeric
  exact ⟨sample, fun typeShifts =>
    hasHHO20LightChecks_of_hasGrouped
      sample typeShifts hGrouped⟩

/-- Logarithmic-scale form of the public simultaneous light-check
existence theorem. -/
theorem exists_sample_forall_typeShifts_hasHHO20LightChecks_of_log_scale
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hLogScale :
      200 * (typeCount : Real) *
          Real.log (16 * r * typeCount : Nat) <
        Delta) :
    ∃ sample : Sample r,
      ∀ typeShifts : Fin typeCount → Fin (ell - 1),
        TwistGraph.HasHHO20LightChecks Delta
          (baseSample sample) (twistSample sample typeShifts) :=
  exists_sample_forall_typeShifts_hasHHO20LightChecks
    r Delta typeCount ell hr hDeltaHalf hTypeDvd
      (light_geometric_union_lt_one_of_exp_lt
        r Delta typeCount hr
          (exp_neg_delta_div_lt_of_log_scale
            r Delta typeCount hr hLogScale))

/-- The sum of the outgoing and incoming paired syndromes is itself the
paired syndrome on the two XOR words used in HHO20's heavy argument. -/
theorem rowPairSyndrome_add
    {r : Nat}
    (row : RowSample r)
    (x outWord inWord : Word (ZMod 2) (Fin (4 * r))) :
    rowPairSyndrome row x outWord +
        rowPairSyndrome row inWord x =
      rowPairSyndrome row (x + inWord) (outWord + x) := by
  classical
  simp only [rowPairSyndrome, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hIncidence : row b false
  · by_cases hTail : row b true <;>
      simp [localPairContribution, hIncidence, hTail]
  · simp [localPairContribution, hIncidence]

/-- Exponential upper envelope for one row parity character. -/
theorem integral_paritySign_rowPairSyndrome_le_exp
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (hpHalf :
      (RandomBase.incidenceProbability (4 * r) Delta).toReal ≤
        1 / 2) :
    (∫ row,
        RandomBase.paritySign (rowPairSyndrome row y z) ∂
          (rowDistribution r Delta hDelta).toMeasure) ≤
      Real.exp
        (-(RandomBase.incidenceProbability (4 * r) Delta).toReal *
          ((HammingWeight y : Real) + HammingWeight z)) := by
  let p : Real :=
    (RandomBase.incidenceProbability (4 * r) Delta).toReal
  rw [integral_paritySign_rowPairSyndrome r Delta hDelta y z,
    product_localPairMean_eq r Delta y z]
  have hweight :
      (HammingWeight y : Real) + HammingWeight z =
        (HammingWeight (y + z) : Real) +
          2 * (pairOverlapCount y z : Real) := by
    exact_mod_cast hammingWeight_add_eq_add_two_pairOverlapCount y z
  rw [hweight]
  exact xorOverlapCharacterProduct_le_exp p
    (HammingWeight (y + z)) (pairOverlapCount y z) hpHalf

/-- Indicator that at least one of the outgoing/incoming paired checks in a
row is violated. -/
noncomputable def rowEitherViolationIndicator
    {r : Nat}
    (x outWord inWord : Word (ZMod 2) (Fin (4 * r)))
    (row : RowSample r) : Real :=
  if
      rowPairSyndrome row x outWord ≠ 0 ∨
      rowPairSyndrome row inWord x ≠ 0
    then 1
    else 0

/-- Joint two-check Fourier identity. -/
theorem rowEitherViolationIndicator_eq
    {r : Nat}
    (x outWord inWord : Word (ZMod 2) (Fin (4 * r)))
    (row : RowSample r) :
    rowEitherViolationIndicator x outWord inWord row =
      (3 -
        RandomBase.paritySign
          (rowPairSyndrome row x outWord) -
        RandomBase.paritySign
          (rowPairSyndrome row inWord x) -
        RandomBase.paritySign
          (rowPairSyndrome row (x + inWord) (outWord + x))) / 4 := by
  let first := rowPairSyndrome row x outWord
  let second := rowPairSyndrome row inWord x
  have hsum :
      first + second =
        rowPairSyndrome row (x + inWord) (outWord + x) :=
    rowPairSyndrome_add row x outWord inWord
  change
    (if first ≠ 0 ∨ second ≠ 0 then 1 else 0) =
      (3 - RandomBase.paritySign first -
        RandomBase.paritySign second -
        RandomBase.paritySign
          (rowPairSyndrome row (x + inWord) (outWord + x))) / 4
  rw [← hsum]
  by_cases hFirst : first = 0
  · by_cases hSecond : second = 0
    · norm_num [hFirst, hSecond, RandomBase.paritySign]
    · rw [RandomBase.zmod2_eq_one_of_ne_zero second hSecond]
      norm_num [hFirst, RandomBase.paritySign]
  · rw [RandomBase.zmod2_eq_one_of_ne_zero first hFirst]
    by_cases hSecond : second = 0
    · norm_num [hSecond, RandomBase.paritySign]
    · rw [RandomBase.zmod2_eq_one_of_ne_zero second hSecond]
      have htwo : (1 + 1 : ZMod 2) = 0 := by decide
      rw [htwo]
      norm_num [RandomBase.paritySign]

/-- Exact probability of at least one violation among the two paired checks
in one row. -/
theorem rowEitherViolation_measureReal
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (x outWord inWord : Word (ZMod 2) (Fin (4 * r))) :
    (rowDistribution r Delta hDelta).toMeasure.real
        {row |
          rowPairSyndrome row x outWord ≠ 0 ∨
          rowPairSyndrome row inWord x ≠ 0} =
      (3 -
        (∫ row,
          RandomBase.paritySign
            (rowPairSyndrome row x outWord) ∂
              (rowDistribution r Delta hDelta).toMeasure) -
        (∫ row,
          RandomBase.paritySign
            (rowPairSyndrome row inWord x) ∂
              (rowDistribution r Delta hDelta).toMeasure) -
        (∫ row,
          RandomBase.paritySign
            (rowPairSyndrome row
              (x + inWord) (outWord + x)) ∂
              (rowDistribution r Delta hDelta).toMeasure)) / 4 := by
  let μ := (rowDistribution r Delta hDelta).toMeasure
  calc
    μ.real
        {row |
          rowPairSyndrome row x outWord ≠ 0 ∨
          rowPairSyndrome row inWord x ≠ 0} =
        ∫ row,
          rowEitherViolationIndicator x outWord inWord row ∂μ := by
      rw [← integral_indicator_one
        (μ := μ) (Set.toFinite _).measurableSet]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun row => by
        by_cases hviol :
            rowPairSyndrome row x outWord ≠ 0 ∨
            rowPairSyndrome row inWord x ≠ 0 <;>
          simp [rowEitherViolationIndicator, Set.indicator, hviol]
    _ =
        ∫ row,
          (3 -
            RandomBase.paritySign
              (rowPairSyndrome row x outWord) -
            RandomBase.paritySign
              (rowPairSyndrome row inWord x) -
            RandomBase.paritySign
              (rowPairSyndrome row
                (x + inWord) (outWord + x))) / 4 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun row =>
        rowEitherViolationIndicator_eq x outWord inWord row
    _ = _ := by
      rw [integral_div, integral_sub, integral_sub, integral_sub]
      · simp [μ]
      all_goals exact Integrable.of_finite

/-- Heavy/light word arithmetic forces all three Fourier characters in the
joint two-check identity to have HHO20 scale at least four. -/
theorem delta_mul_four_r_le_xorPairWeight
    (r Delta : Nat)
    (x outWord inWord : Word (ZMod 2) (Fin (4 * r)))
    (hx : 4 * (4 * r) ≤ Delta * HammingWeight x)
    (hOut : Delta * HammingWeight outWord ≤ 2 * (4 * r))
    (hIn : Delta * HammingWeight inWord ≤ 2 * (4 * r)) :
    4 * (4 * r) ≤
      Delta *
        (HammingWeight (x + inWord) +
          HammingWeight (outWord + x)) := by
  have hbitAddSelf (a : ZMod 2) : a + a = 0 := by
    by_cases ha : a = 0
    · simp [ha]
    · rw [RandomBase.zmod2_eq_one_of_ne_zero a ha]
      decide
  have hCancelIn : (x + inWord) + inWord = x := by
    funext b
    simp only [Pi.add_apply]
    rw [add_assoc, hbitAddSelf, add_zero]
  have hCancelOut : (outWord + x) + outWord = x := by
    funext b
    simp only [Pi.add_apply]
    rw [add_assoc, add_comm (x b) (outWord b),
      ← add_assoc, hbitAddSelf, zero_add]
  have hxIn :
      HammingWeight x ≤
        HammingWeight (x + inWord) + HammingWeight inWord := by
    have h :=
      HammingWeight_add_le (x + inWord) inWord
    rw [hCancelIn] at h
    exact h
  have hxOut :
      HammingWeight x ≤
        HammingWeight (outWord + x) + HammingWeight outWord := by
    have h :=
      HammingWeight_add_le (outWord + x) outWord
    rw [hCancelOut] at h
    exact h
  have hBoth := Nat.add_le_add hxIn hxOut
  have hBothDelta := Nat.mul_le_mul_left Delta hBoth
  simp only [Nat.mul_add] at hBothDelta
  rw [Nat.mul_add]
  omega

/-- Convert an integer-cleared weight threshold into `p * weight ≥ 4`. -/
theorem four_le_incidenceProbability_mul_weight
    (r Delta weight : Nat) (hr : 0 < r)
    (hWeight : 4 * (4 * r) ≤ Delta * weight) :
    (4 : Real) ≤
      (RandomBase.incidenceProbability (4 * r) Delta).toReal *
        weight := by
  let p : Real :=
    (RandomBase.incidenceProbability (4 * r) Delta).toReal
  have hScale :
      ((4 * r : Nat) : Real) * p = Delta :=
    RandomBase.check_expected_degree r Delta hr
  have hWeightReal :
      (4 : Real) * (4 * r : Nat) ≤ (Delta : Real) * weight := by
    exact_mod_cast hWeight
  have hFourRPos : (0 : Real) < (4 * r : Nat) := by positivity
  have hpWeight :
      p * weight =
        ((Delta : Real) * weight) / (4 * r : Nat) := by
    apply (eq_div_iff hFourRPos.ne').2
    nlinarith
  rw [hpWeight]
  exact (le_div_iff₀ hFourRPos).2 hWeightReal

/-- Numerical bound used for the paper's `.73` joint-row probability. -/
theorem exp_neg_four_lt_one_fiftieth :
    Real.exp (-4) < (1 : Real) / 50 := by
  have hExpTwo : (71 : Real) / 10 < Real.exp 2 := by
    rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_d9]
  have hExpFour : (50 : Real) < Real.exp 4 := by
    rw [show (4 : Real) = 2 + 2 by norm_num, Real.exp_add]
    nlinarith
  rw [Real.exp_neg]
  simpa [one_div] using
    (inv_lt_inv₀ (Real.exp_pos 4)
      (by norm_num : (0 : Real) < 50)).2 hExpFour

/-- HHO20 heavy-row estimate: with one heavy central word and two light
neighbor words, at least one paired check is violated with probability
strictly greater than `.73`. -/
theorem rowEitherViolation_measureReal_gt_seventyThreeHundredths
    (r Delta : Nat) (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (x outWord inWord : Word (ZMod 2) (Fin (4 * r)))
    (hx : 4 * (4 * r) ≤ Delta * HammingWeight x)
    (hOut : Delta * HammingWeight outWord ≤ 2 * (4 * r))
    (hIn : Delta * HammingWeight inWord ≤ 2 * (4 * r)) :
    (73 : Real) / 100 <
      (rowDistribution r Delta (by omega)).toMeasure.real
        {row |
          rowPairSyndrome row x outWord ≠ 0 ∨
          rowPairSyndrome row inWord x ≠ 0} := by
  let p : Real :=
    (RandomBase.incidenceProbability (4 * r) Delta).toReal
  have hpHalf : p ≤ 1 / 2 :=
    incidenceProbability_toReal_le_half r Delta hDeltaHalf
  have hFirstScale :
      (4 : Real) ≤ p *
        ((HammingWeight x : Real) + HammingWeight outWord) := by
    have h :=
      four_le_incidenceProbability_mul_weight
        r Delta (HammingWeight x + HammingWeight outWord) hr
        (le_trans hx
          (Nat.mul_le_mul_left Delta (Nat.le_add_right _ _)))
    simpa [p, Nat.cast_add] using h
  have hSecondScale :
      (4 : Real) ≤ p *
        ((HammingWeight inWord : Real) + HammingWeight x) := by
    have h :
        4 * (4 * r) ≤
          Delta * (HammingWeight inWord + HammingWeight x) := by
      calc
        _ ≤ Delta * HammingWeight x := hx
        _ ≤ _ :=
          Nat.mul_le_mul_left Delta (Nat.le_add_left _ _)
    simpa [p, Nat.cast_add] using
      four_le_incidenceProbability_mul_weight
        r Delta (HammingWeight inWord + HammingWeight x) hr h
  have hThirdNat :
      4 * (4 * r) ≤
        Delta *
          (HammingWeight (x + inWord) +
            HammingWeight (outWord + x)) :=
    delta_mul_four_r_le_xorPairWeight
      r Delta x outWord inWord hx hOut hIn
  have hThirdScale :
      (4 : Real) ≤ p *
        ((HammingWeight (x + inWord) : Real) +
          HammingWeight (outWord + x)) := by
    simpa [p, Nat.cast_add] using
      four_le_incidenceProbability_mul_weight
        r Delta
          (HammingWeight (x + inWord) +
            HammingWeight (outWord + x))
          hr hThirdNat
  have hFirstChar :
      (∫ row,
          RandomBase.paritySign
            (rowPairSyndrome row x outWord) ∂
            (rowDistribution r Delta (by omega)).toMeasure) ≤
        Real.exp (-4) := by
    calc
      _ ≤ Real.exp
          (-p * ((HammingWeight x : Real) +
            HammingWeight outWord)) :=
        integral_paritySign_rowPairSyndrome_le_exp
          r Delta (by omega) x outWord hpHalf
      _ ≤ Real.exp (-4) := by
        apply Real.exp_le_exp.mpr
        linarith
  have hSecondChar :
      (∫ row,
          RandomBase.paritySign
            (rowPairSyndrome row inWord x) ∂
            (rowDistribution r Delta (by omega)).toMeasure) ≤
        Real.exp (-4) := by
    calc
      _ ≤ Real.exp
          (-p * ((HammingWeight inWord : Real) +
            HammingWeight x)) :=
        integral_paritySign_rowPairSyndrome_le_exp
          r Delta (by omega) inWord x hpHalf
      _ ≤ Real.exp (-4) := by
        apply Real.exp_le_exp.mpr
        linarith
  have hThirdChar :
      (∫ row,
          RandomBase.paritySign
            (rowPairSyndrome row
              (x + inWord) (outWord + x)) ∂
            (rowDistribution r Delta (by omega)).toMeasure) ≤
        Real.exp (-4) := by
    calc
      _ ≤ Real.exp
          (-p * ((HammingWeight (x + inWord) : Real) +
            HammingWeight (outWord + x))) :=
        integral_paritySign_rowPairSyndrome_le_exp
          r Delta (by omega) (x + inWord) (outWord + x) hpHalf
      _ ≤ Real.exp (-4) := by
        apply Real.exp_le_exp.mpr
        linarith
  rw [rowEitherViolation_measureReal
    r Delta (by omega) x outWord inWord]
  nlinarith [exp_neg_four_lt_one_fiftieth]

/-- Rows whose cyclic check type belongs to a chosen type set. -/
noncomputable def selectedTypeRows
    (r typeCount : Nat) [NeZero typeCount]
    (types : Finset (Fin typeCount)) :
    Finset (Fin (3 * r)) :=
  Finset.univ.filter fun a =>
    RandomTwist.checkType typeCount a ∈ types

/-- Exact size of a union of cyclic type fibers under the divisibility
condition. -/
theorem card_selectedTypeRows_of_dvd
    (r typeCount : Nat) [NeZero typeCount]
    (hTypeDvd : typeCount ∣ 3 * r)
    (types : Finset (Fin typeCount)) :
    (selectedTypeRows r typeCount types).card =
      types.card * ((3 * r) / typeCount) := by
  classical
  have hPartition :
      (∑ τ : Fin typeCount,
        (Finset.univ.filter fun a : Fin (3 * r) =>
          RandomTwist.checkType typeCount a = τ ∧
            RandomTwist.checkType typeCount a ∈ types).card) =
        (selectedTypeRows r typeCount types).card := by
    simp only [selectedTypeRows, Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _ha
    by_cases hmem :
        RandomTwist.checkType typeCount a ∈ types <;>
      simp [hmem]
  rw [← hPartition]
  calc
    (∑ τ : Fin typeCount,
        (Finset.univ.filter fun a : Fin (3 * r) =>
          RandomTwist.checkType typeCount a = τ ∧
            RandomTwist.checkType typeCount a ∈ types).card) =
        ∑ τ ∈ types, (typeRows r typeCount τ).card := by
      rw [show types =
          (Finset.univ.filter fun τ : Fin typeCount => τ ∈ types) by
        ext τ
        simp]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro τ _hτ
      by_cases hmem : τ ∈ types
      · simp only [hmem, if_true, typeRows]
        congr 1
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨htype, _⟩
          exact htype
        · intro htype
          exact ⟨htype, htype ▸ hmem⟩
      · simp only [hmem, if_false, Finset.card_eq_zero]
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false]
        rintro ⟨htype, ha⟩
        exact hmem (htype ▸ ha)
    _ = ∑ _τ ∈ types, ((3 * r) / typeCount) := by
      apply Finset.sum_congr rfl
      intro τ _hτ
      exact card_typeRows_of_dvd r typeCount hTypeDvd τ
    _ = _ := by
      simp

/-- Full-sample indicator that at least one paired check is violated in a
named row, with neighbor words chosen by the row's type. -/
noncomputable def sampleRowEitherViolationIndicator
    {r typeCount : Nat} [NeZero typeCount]
    (x : Word (ZMod 2) (Fin (4 * r)))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r))
    (sample : Sample r) : Real :=
  rowEitherViolationIndicator x
    (outWord (RandomTwist.checkType typeCount a))
    (inWord (RandomTwist.checkType typeCount a))
    (sample a)

/-- Heavy-row indicators lie in `[0,1]`. -/
theorem sampleRowEitherViolationIndicator_mem_Icc
    {r typeCount : Nat} [NeZero typeCount]
    (x : Word (ZMod 2) (Fin (4 * r)))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r))
    (sample : Sample r) :
    sampleRowEitherViolationIndicator
        x outWord inWord a sample ∈ Set.Icc (0 : Real) 1 := by
  by_cases hviol :
      rowPairSyndrome (sample a) x
          (outWord (RandomTwist.checkType typeCount a)) ≠ 0 ∨
      rowPairSyndrome (sample a)
          (inWord (RandomTwist.checkType typeCount a)) x ≠ 0 <;>
    simp [sampleRowEitherViolationIndicator,
      rowEitherViolationIndicator, hviol]

/-- Heavy-row indicators are mutually independent. -/
theorem distribution_sampleRowEitherViolationIndicator_iIndepFun
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hDelta : Delta ≤ 4 * r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r))) :
    ProbabilityTheory.iIndepFun
      (fun a =>
        sampleRowEitherViolationIndicator x outWord inWord a)
      (distribution r Delta hDelta).toMeasure := by
  exact (distribution_row_iIndepFun r Delta hDelta).comp
    (fun a row =>
      rowEitherViolationIndicator x
        (outWord (RandomTwist.checkType typeCount a))
        (inWord (RandomTwist.checkType typeCount a)) row)
    (fun _a => Measurable.of_discrete)

/-- Exact expectation of a named heavy-row indicator. -/
theorem integral_sampleRowEitherViolationIndicator
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hDelta : Delta ≤ 4 * r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r)) :
    (∫ sample,
        sampleRowEitherViolationIndicator
          x outWord inWord a sample ∂
          (distribution r Delta hDelta).toMeasure) =
      (rowDistribution r Delta hDelta).toMeasure.real
        {row |
          rowPairSyndrome row x
              (outWord (RandomTwist.checkType typeCount a)) ≠ 0 ∨
          rowPairSyndrome row
              (inWord (RandomTwist.checkType typeCount a)) x ≠ 0} := by
  calc
    _ =
        ∫ row,
          rowEitherViolationIndicator x
            (outWord (RandomTwist.checkType typeCount a))
            (inWord (RandomTwist.checkType typeCount a)) row ∂
              (rowDistribution r Delta hDelta).toMeasure := by
      exact
        (distribution_row_hasLaw r Delta hDelta a).integral_comp
          ((Measurable.of_discrete :
            Measurable
              (rowEitherViolationIndicator x
                (outWord (RandomTwist.checkType typeCount a))
                (inWord (RandomTwist.checkType typeCount a))
              )).aestronglyMeasurable)
    _ = _ := by
      rw [← integral_indicator_one
        (μ := (rowDistribution r Delta hDelta).toMeasure)
        (Set.toFinite _).measurableSet]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun row => by
        by_cases hviol :
            rowPairSyndrome row x
                (outWord (RandomTwist.checkType typeCount a)) ≠ 0 ∨
            rowPairSyndrome row
                (inWord (RandomTwist.checkType typeCount a)) x ≠ 0 <;>
          simp [rowEitherViolationIndicator, Set.indicator, hviol]

/-- Centered heavy-row indicator, with its row-dependent exact mean. -/
noncomputable def centeredSampleRowEitherViolationIndicator
    {r typeCount : Nat} [NeZero typeCount]
    (Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r))
    (sample : Sample r) : Real :=
  sampleRowEitherViolationIndicator x outWord inWord a sample -
    ∫ sample',
      sampleRowEitherViolationIndicator
        x outWord inWord a sample' ∂
        (distribution r Delta hDelta).toMeasure

/-- Centered heavy-row indicators have Hoeffding parameter `1/4`. -/
theorem centeredSampleRowEitherViolationIndicator_hasSubgaussianMGF
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hDelta : Delta ≤ 4 * r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r)) :
    ProbabilityTheory.HasSubgaussianMGF
      (centeredSampleRowEitherViolationIndicator
        Delta hDelta x outWord inWord a)
      (1 / 4 : NNReal)
      (distribution r Delta hDelta).toMeasure := by
  have h :=
    ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
      (μ := (distribution r Delta hDelta).toMeasure)
      (X := sampleRowEitherViolationIndicator x outWord inWord a)
      (a := (0 : Real)) (b := (1 : Real))
      Measurable.of_discrete.aemeasurable
      (Filter.Eventually.of_forall fun sample =>
        sampleRowEitherViolationIndicator_mem_Icc
          x outWord inWord a sample)
  convert h using 1
  all_goals
    norm_num [centeredSampleRowEitherViolationIndicator] <;> rfl

/-- Centered heavy-row indicators remain mutually independent. -/
theorem distribution_centeredSampleRowEitherViolationIndicator_iIndepFun
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hDelta : Delta ≤ 4 * r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r))) :
    ProbabilityTheory.iIndepFun
      (fun a =>
        centeredSampleRowEitherViolationIndicator
          Delta hDelta x outWord inWord a)
      (distribution r Delta hDelta).toMeasure := by
  exact
    (distribution_sampleRowEitherViolationIndicator_iIndepFun
      r Delta typeCount hDelta x outWord inWord).comp
      (fun a value =>
        value -
          ∫ sample,
            sampleRowEitherViolationIndicator
              x outWord inWord a sample ∂
              (distribution r Delta hDelta).toMeasure)
      (fun _a => by fun_prop)

/-- Hoeffding lower tail for any fixed collection of heavy rows. -/
theorem measure_centeredRowEitherViolationSum_le_neg_le
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hDelta : Delta ≤ 4 * r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (rows : Finset (Fin (3 * r)))
    (ε : Real) (hε : 0 ≤ ε) :
    (distribution r Delta hDelta).toMeasure.real
        {sample |
          (∑ a ∈ rows,
            centeredSampleRowEitherViolationIndicator
              Delta hDelta x outWord inWord a sample) ≤ -ε} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ↑(∑ _a ∈ rows, (1 / 4 : NNReal)))) := by
  have hIndep :
      ProbabilityTheory.iIndepFun
        (fun a sample =>
          -centeredSampleRowEitherViolationIndicator
            Delta hDelta x outWord inWord a sample)
        (distribution r Delta hDelta).toMeasure :=
    (distribution_centeredSampleRowEitherViolationIndicator_iIndepFun
      r Delta typeCount hDelta x outWord inWord).comp
      (fun _a value => -value) (fun _a => by fun_prop)
  have hRaw :=
    ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (s := rows)
      (c := fun _a : Fin (3 * r) => (1 / 4 : NNReal))
      hIndep
      (fun a _ha =>
        (centeredSampleRowEitherViolationIndicator_hasSubgaussianMGF
          r Delta typeCount hDelta x outWord inWord a).neg)
      hε
  calc
    _ =
        (distribution r Delta hDelta).toMeasure.real
          {sample |
            ε ≤
              ∑ a ∈ rows,
                -centeredSampleRowEitherViolationIndicator
                  Delta hDelta x outWord inWord a sample} := by
      congr 1
      ext sample
      simp only [Set.mem_setOf_eq, Finset.sum_neg_distrib]
      constructor <;> intro h <;> linarith
    _ ≤ _ := hRaw

/-- Fiberwise decomposition of a sum over selected cyclic types. -/
theorem sum_selectedTypeRows_eq_sum_typeRows
    {r typeCount : Nat} [NeZero typeCount]
    (types : Finset (Fin typeCount))
    (f : Fin (3 * r) → Real) :
    (∑ a ∈ selectedTypeRows r typeCount types, f a) =
      ∑ τ ∈ types, ∑ a ∈ typeRows r typeCount τ, f a := by
  unfold selectedTypeRows typeRows
  exact
    (Finset.sum_fiberwise_eq_sum_filter
      (Finset.univ : Finset (Fin (3 * r))) types
      (RandomTwist.checkType typeCount) f).symm

/-- Every selected heavy row has mean at least `.73`. -/
theorem seventyThreeHundredths_mul_card_le_sum_heavyRowMeans
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (types : Finset (Fin typeCount))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (hx : 4 * (4 * r) ≤ Delta * HammingWeight x)
    (hNeighbors :
      ∀ τ ∈ types,
        Delta * HammingWeight (outWord τ) ≤ 2 * (4 * r) ∧
        Delta * HammingWeight (inWord τ) ≤ 2 * (4 * r)) :
    (73 : Real) / 100 *
        (selectedTypeRows r typeCount types).card ≤
      ∑ a ∈ selectedTypeRows r typeCount types,
        ∫ sample,
          sampleRowEitherViolationIndicator
            x outWord inWord a sample ∂
            (distribution r Delta (by omega)).toMeasure := by
  calc
    (73 : Real) / 100 *
        (selectedTypeRows r typeCount types).card =
        ∑ _a ∈ selectedTypeRows r typeCount types,
          (73 : Real) / 100 := by
      simp [mul_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a ha
      have hTypeMem :
          RandomTwist.checkType typeCount a ∈ types := by
        simpa [selectedTypeRows] using ha
      rw [integral_sampleRowEitherViolationIndicator
        r Delta typeCount (by omega) x outWord inWord a]
      exact le_of_lt
        (rowEitherViolation_measureReal_gt_seventyThreeHundredths
          r Delta hr hDeltaHalf x
          (outWord (RandomTwist.checkType typeCount a))
          (inWord (RandomTwist.checkType typeCount a))
          hx
          (hNeighbors _ hTypeMem).1
          (hNeighbors _ hTypeMem).2)

/-- Sum of centered heavy-row indicators equals raw count minus the sum of
their exact means. -/
theorem sum_centeredSampleRowEitherViolationIndicator_eq
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hDelta : Delta ≤ 4 * r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (rows : Finset (Fin (3 * r)))
    (sample : Sample r) :
    (∑ a ∈ rows,
      centeredSampleRowEitherViolationIndicator
        Delta hDelta x outWord inWord a sample) =
      (∑ a ∈ rows,
        sampleRowEitherViolationIndicator
          x outWord inWord a sample) -
      ∑ a ∈ rows,
        ∫ sample',
          sampleRowEitherViolationIndicator
            x outWord inWord a sample' ∂
            (distribution r Delta hDelta).toMeasure := by
  simp only [centeredSampleRowEitherViolationIndicator,
    Finset.sum_sub_distrib]

/-- Fixed heavy configuration: fewer than one fifth of selected rows with
an outgoing-or-incoming violation has probability at most
`exp(-selectedRows/2)`. -/
theorem measure_heavyEitherViolationSum_le_oneFifth_le
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (types : Finset (Fin typeCount))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (hx : 4 * (4 * r) ≤ Delta * HammingWeight x)
    (hTypes : 98 * typeCount ≤ 100 * types.card)
    (hNeighbors :
      ∀ τ ∈ types,
        Delta * HammingWeight (outWord τ) ≤ 2 * (4 * r) ∧
        Delta * HammingWeight (inWord τ) ≤ 2 * (4 * r)) :
    let rows := selectedTypeRows r typeCount types
    (distribution r Delta (by omega)).toMeasure.real
        {sample |
          (∑ a ∈ rows,
            sampleRowEitherViolationIndicator
              x outWord inWord a sample) ≤
            (rows.card : Real) / 5} ≤
      Real.exp (-(rows.card : Real) / 2) := by
  dsimp only
  let hDelta : Delta ≤ 4 * r := by omega
  let rows := selectedTypeRows r typeCount types
  have hTypesPos : 0 < types.card := by
    have hTypePos : 0 < typeCount := NeZero.pos typeCount
    omega
  have hQuotPos : 0 < (3 * r) / typeCount := by
    have hEq :=
      Nat.div_mul_cancel hTypeDvd
    have hRPos : 0 < 3 * r := by omega
    by_contra hzero
    have : (3 * r) / typeCount = 0 := Nat.eq_zero_of_not_pos hzero
    rw [this] at hEq
    simp at hEq
    omega
  have hRowsPos : 0 < rows.card := by
    change 0 < (selectedTypeRows r typeCount types).card
    rw [card_selectedTypeRows_of_dvd
      r typeCount hTypeDvd types]
    exact Nat.mul_pos hTypesPos hQuotPos
  have hMean :
      (73 : Real) / 100 * rows.card ≤
        ∑ a ∈ rows,
          ∫ sample,
            sampleRowEitherViolationIndicator
              x outWord inWord a sample ∂
              (distribution r Delta hDelta).toMeasure := by
    simpa [rows, hDelta] using
      seventyThreeHundredths_mul_card_le_sum_heavyRowMeans
        r Delta typeCount hr hDeltaHalf x types
        outWord inWord hx hNeighbors
  have hSubset :
      {sample |
        (∑ a ∈ rows,
          sampleRowEitherViolationIndicator
            x outWord inWord a sample) ≤
          (rows.card : Real) / 5} ⊆
        {sample |
          (∑ a ∈ rows,
            centeredSampleRowEitherViolationIndicator
              Delta hDelta x outWord inWord a sample) ≤
            -((rows.card : Real) / 2)} := by
    intro sample hLow
    change
      (∑ a ∈ rows,
        sampleRowEitherViolationIndicator
          x outWord inWord a sample) ≤
        (rows.card : Real) / 5 at hLow
    change
      (∑ a ∈ rows,
        centeredSampleRowEitherViolationIndicator
          Delta hDelta x outWord inWord a sample) ≤
        -((rows.card : Real) / 2)
    rw [sum_centeredSampleRowEitherViolationIndicator_eq
      r Delta typeCount hDelta x outWord inWord rows sample]
    have hRowsNonneg : (0 : Real) ≤ rows.card := by positivity
    linarith
  calc
    _ ≤
        (distribution r Delta hDelta).toMeasure.real
          {sample |
            (∑ a ∈ rows,
              centeredSampleRowEitherViolationIndicator
                Delta hDelta x outWord inWord a sample) ≤
              -((rows.card : Real) / 2)} :=
      measureReal_mono hSubset
    _ ≤
        Real.exp
          (-((rows.card : Real) / 2) ^ 2 /
            (2 * ↑(∑ _a ∈ rows, (1 / 4 : NNReal)))) :=
      measure_centeredRowEitherViolationSum_le_neg_le
        r Delta typeCount hDelta x outWord inWord rows
        ((rows.card : Real) / 2) (by positivity)
    _ = Real.exp (-(rows.card : Real) / 2) := by
      congr 1
      have hSum :
          (↑(∑ _a ∈ rows, (1 / 4 : NNReal)) : Real) =
            (rows.card : Real) / 4 := by
        simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
      rw [hSum]
      have hRowsReal : (0 : Real) < rows.card := by
        exact_mod_cast hRowsPos
      field_simp
      norm_num

/-- An OR-violation indicator is bounded by the sum of its two constituent
check indicators. -/
theorem rowEitherViolationIndicator_le_add
    {r : Nat}
    (x outWord inWord : Word (ZMod 2) (Fin (4 * r)))
    (row : RowSample r) :
    rowEitherViolationIndicator x outWord inWord row ≤
      rowViolationIndicator x outWord row +
        rowViolationIndicator inWord x row := by
  by_cases hOut : rowPairSyndrome row x outWord ≠ 0
  · by_cases hIn : rowPairSyndrome row inWord x ≠ 0
    · simp [rowEitherViolationIndicator, rowViolationIndicator, hOut, hIn]
    · simp [rowEitherViolationIndicator, rowViolationIndicator, hOut, hIn]
  · by_cases hIn : rowPairSyndrome row inWord x ≠ 0
    · simp [rowEitherViolationIndicator, rowViolationIndicator, hOut, hIn]
    · simp [rowEitherViolationIndicator, rowViolationIndicator, hOut, hIn]

/-- The selected-row OR count is bounded pointwise by the deterministic
incident-violation count.  This bridge is independent of all type shifts. -/
theorem sum_sampleRowEitherViolationIndicator_selected_le_heavyIncidentViolationCount
    {r typeCount ell : Nat} [NeZero typeCount]
    (sample : Sample r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (x : Word (ZMod 2) (Fin (4 * r)))
    (types : Finset (Fin typeCount))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r))) :
    (∑ a ∈ selectedTypeRows r typeCount types,
        sampleRowEitherViolationIndicator
          x outWord inWord a sample) ≤
      (TwistGraph.heavyIncidentViolationCount
        (baseSample sample) (twistSample sample typeShifts)
        x types outWord inWord : Real) := by
  classical
  rw [sum_selectedTypeRows_eq_sum_typeRows]
  simp only [TwistGraph.heavyIncidentViolationCount, Nat.cast_sum,
    Nat.cast_add]
  apply Finset.sum_le_sum
  intro τ hτ
  calc
    (∑ a ∈ typeRows r typeCount τ,
        sampleRowEitherViolationIndicator
          x outWord inWord a sample) ≤
        (∑ a ∈ typeRows r typeCount τ,
          (sampleRowViolationIndicator x (outWord τ) a sample +
            sampleRowViolationIndicator (inWord τ) x a sample)) := by
      apply Finset.sum_le_sum
      intro a ha
      have htype :
          RandomTwist.checkType typeCount a = τ := by
        simpa [typeRows] using ha
      simp only [sampleRowEitherViolationIndicator, htype]
      exact rowEitherViolationIndicator_le_add
        x (outWord τ) (inWord τ) (sample a)
    _ =
        (TwistGraph.typeViolationCount
            (baseSample sample) (twistSample sample typeShifts)
            τ x (outWord τ) : Real) +
          (TwistGraph.typeViolationCount
            (baseSample sample) (twistSample sample typeShifts)
            τ (inWord τ) x : Real) := by
      rw [Finset.sum_add_distrib,
        sum_sampleRowViolationIndicator_typeRows_eq
          sample typeShifts τ x (outWord τ),
        sum_sampleRowViolationIndicator_typeRows_eq
          sample typeShifts τ (inWord τ) x]

/-- Selecting at least 98 percent of the types selects at least `2r` rows
when the equal cyclic partition exists. -/
theorem two_mul_r_le_card_selectedTypeRows
    (r typeCount : Nat) [NeZero typeCount]
    (hTypeDvd : typeCount ∣ 3 * r)
    (types : Finset (Fin typeCount))
    (hTypes : 98 * typeCount ≤ 100 * types.card) :
    2 * r ≤ (selectedTypeRows r typeCount types).card := by
  rw [card_selectedTypeRows_of_dvd r typeCount hTypeDvd types]
  let q := (3 * r) / typeCount
  have hEq : q * typeCount = 3 * r :=
    Nat.div_mul_cancel hTypeDvd
  have hScaled := Nat.mul_le_mul_right q hTypes
  dsimp [q] at hEq hScaled ⊢
  nlinarith

/-- Exact integer-scaled bounds recording that at least 98 percent of the
three-quarters-rate check rows are selected. -/
theorem selectedTypeRows_card_bounds
    (r typeCount : Nat) [NeZero typeCount]
    (hTypeDvd : typeCount ∣ 3 * r)
    (types : Finset (Fin typeCount))
    (hTypes : 98 * typeCount ≤ 100 * types.card) :
    294 * r ≤
        100 * (selectedTypeRows r typeCount types).card ∧
      (selectedTypeRows r typeCount types).card ≤ 3 * r := by
  rw [card_selectedTypeRows_of_dvd r typeCount hTypeDvd types]
  let q := (3 * r) / typeCount
  have hEq : q * typeCount = 3 * r :=
    Nat.div_mul_cancel hTypeDvd
  have hLower := Nat.mul_le_mul_right q hTypes
  have hTypesLe : types.card ≤ typeCount := by
    simpa using types.card_le_univ
  have hUpper := Nat.mul_le_mul_right q hTypesLe
  dsimp [q] at hEq hLower hUpper ⊢
  constructor <;> nlinarith

/-- Fixed heavy configuration at the actual HHO20 `.01n = .04r`
threshold.  Keeping the exact 98-percent row count sharpens the Hoeffding
exponent to at least `3r`, which is strong enough to beat the `2^(4r)`
choices of the central word. -/
theorem measure_heavyEitherViolationSum_le_r_div_twentyFive_le
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (types : Finset (Fin typeCount))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (hx : 4 * (4 * r) ≤ Delta * HammingWeight x)
    (hTypes : 98 * typeCount ≤ 100 * types.card)
    (hNeighbors :
      ∀ τ ∈ types,
        Delta * HammingWeight (outWord τ) ≤ 2 * (4 * r) ∧
        Delta * HammingWeight (inWord τ) ≤ 2 * (4 * r)) :
    let rows := selectedTypeRows r typeCount types
    (distribution r Delta (by omega)).toMeasure.real
        {sample |
          (∑ a ∈ rows,
            sampleRowEitherViolationIndicator
              x outWord inWord a sample) ≤
            (r : Real) / 25} ≤
      Real.exp (-3 * (r : Real)) := by
  dsimp only
  let hDelta : Delta ≤ 4 * r := by omega
  let rows := selectedTypeRows r typeCount types
  have hBounds :
      294 * r ≤ 100 * rows.card ∧ rows.card ≤ 3 * r := by
    exact selectedTypeRows_card_bounds
      r typeCount hTypeDvd types hTypes
  have hRowsPos : 0 < rows.card := by omega
  have hMean :
      (73 : Real) / 100 * rows.card ≤
        ∑ a ∈ rows,
          ∫ sample,
            sampleRowEitherViolationIndicator
              x outWord inWord a sample ∂
              (distribution r Delta hDelta).toMeasure := by
    simpa [rows, hDelta] using
      seventyThreeHundredths_mul_card_le_sum_heavyRowMeans
        r Delta typeCount hr hDeltaHalf x types
        outWord inWord hx hNeighbors
  let ε : Real := (73 : Real) / 100 * rows.card - r / 25
  have hBoundsReal :
      (294 : Real) * r ≤ 100 * rows.card ∧
        (rows.card : Real) ≤ 3 * r := by
    constructor
    · exact_mod_cast hBounds.1
    · exact_mod_cast hBounds.2
  have hrReal : (0 : Real) < r := by exact_mod_cast hr
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hSubset :
      {sample |
        (∑ a ∈ rows,
          sampleRowEitherViolationIndicator
            x outWord inWord a sample) ≤
          (r : Real) / 25} ⊆
        {sample |
          (∑ a ∈ rows,
            centeredSampleRowEitherViolationIndicator
              Delta hDelta x outWord inWord a sample) ≤ -ε} := by
    intro sample hLow
    change
      (∑ a ∈ rows,
        sampleRowEitherViolationIndicator
          x outWord inWord a sample) ≤
        (r : Real) / 25 at hLow
    change
      (∑ a ∈ rows,
        centeredSampleRowEitherViolationIndicator
          Delta hDelta x outWord inWord a sample) ≤ -ε
    rw [sum_centeredSampleRowEitherViolationIndicator_eq
      r Delta typeCount hDelta x outWord inWord rows sample]
    dsimp [ε]
    linarith
  calc
    _ ≤
        (distribution r Delta hDelta).toMeasure.real
          {sample |
            (∑ a ∈ rows,
              centeredSampleRowEitherViolationIndicator
                Delta hDelta x outWord inWord a sample) ≤ -ε} :=
      measureReal_mono hSubset
    _ ≤
        Real.exp
          (-(ε ^ 2) /
            (2 * ↑(∑ _a ∈ rows, (1 / 4 : NNReal)))) :=
      measure_centeredRowEitherViolationSum_le_neg_le
        r Delta typeCount hDelta x outWord inWord rows ε (le_of_lt hε)
    _ ≤ Real.exp (-3 * (r : Real)) := by
      apply Real.exp_le_exp.mpr
      have hSum :
          (↑(∑ _a ∈ rows, (1 / 4 : NNReal)) : Real) =
            (rows.card : Real) / 4 := by
        simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
      rw [hSum]
      have hRowsReal : (0 : Real) < rows.card := by
        exact_mod_cast hRowsPos
      dsimp [ε]
      rw [div_le_iff₀ (by positivity : (0 : Real) <
        2 * ((rows.card : Real) / 4))]
      nlinarith [sq_nonneg
        ((73 : Real) / 100 * rows.card - r / 25)]

/-- For a fixed admissible heavy configuration, failure of the deterministic
HHO20 heavy-check conclusion has probability at most `exp(-3r)`. -/
theorem measure_not_heavyConfigurationConclusion_le
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (x : Word (ZMod 2) (Fin (4 * r)))
    (types : Finset (Fin typeCount))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (hx : 4 * (4 * r) ≤ Delta * HammingWeight x)
    (hTypes : 98 * typeCount ≤ 100 * types.card)
    (hNeighbors :
      ∀ τ ∈ types,
        Delta * HammingWeight (outWord τ) ≤ 2 * (4 * r) ∧
        Delta * HammingWeight (inWord τ) ≤ 2 * (4 * r)) :
    (distribution r Delta (by omega)).toMeasure.real
        {sample |
          ¬4 * r ≤
            100 *
              TwistGraph.heavyIncidentViolationCount
                (baseSample sample) (twistSample sample typeShifts)
                x types outWord inWord} ≤
      Real.exp (-3 * (r : Real)) := by
  let hDelta : Delta ≤ 4 * r := by omega
  let rows := selectedTypeRows r typeCount types
  have hSubset :
      {sample |
        ¬4 * r ≤
          100 *
            TwistGraph.heavyIncidentViolationCount
              (baseSample sample) (twistSample sample typeShifts)
              x types outWord inWord} ⊆
        {sample |
          (∑ a ∈ rows,
            sampleRowEitherViolationIndicator
              x outWord inWord a sample) ≤
            (r : Real) / 25} := by
    intro sample hFail
    change
      (∑ a ∈ rows,
        sampleRowEitherViolationIndicator
          x outWord inWord a sample) ≤
        (r : Real) / 25
    have hBridge :=
      sum_sampleRowEitherViolationIndicator_selected_le_heavyIncidentViolationCount
        sample typeShifts x types outWord inWord
    have hFail' :
        100 *
            TwistGraph.heavyIncidentViolationCount
              (baseSample sample) (twistSample sample typeShifts)
              x types outWord inWord <
          4 * r := Nat.lt_of_not_ge hFail
    have hFailReal :
        (100 : Real) *
            TwistGraph.heavyIncidentViolationCount
              (baseSample sample) (twistSample sample typeShifts)
              x types outWord inWord <
          4 * r := by
      exact_mod_cast hFail'
    linarith
  calc
    _ ≤
        (distribution r Delta hDelta).toMeasure.real
          {sample |
            (∑ a ∈ rows,
              sampleRowEitherViolationIndicator
                x outWord inWord a sample) ≤
              (r : Real) / 25} :=
      measureReal_mono hSubset
    _ ≤ Real.exp (-3 * (r : Real)) := by
      simpa [rows, hDelta] using
        measure_heavyEitherViolationSum_le_r_div_twentyFive_le
          r Delta typeCount hr hDeltaHalf hTypeDvd
          x types outWord inWord hx hTypes hNeighbors

/-- A binary neighbor word in the light range used by the heavy argument. -/
abbrev HHO20LightNeighborWord (r Delta : Nat) :=
  {w : Word (ZMod 2) (Fin (4 * r)) //
    Delta * HammingWeight w ≤ 2 * (4 * r)}

/-- Finite index type for the heavy union bound.  Neighbor functions are
globally light; values outside the selected type set are harmless and allow
an exact finite product index. -/
abbrev HeavyFailureIndex (r Delta typeCount : Nat) :=
  Word (ZMod 2) (Fin (4 * r)) ×
    Finset (Fin typeCount) ×
      (Fin typeCount → HHO20LightNeighborWord r Delta) ×
        (Fin typeCount → HHO20LightNeighborWord r Delta)

/-- The bad event attached to one finite heavy-configuration index.  Indices
whose central word or selected-type set is inadmissible contribute the empty
event. -/
def groupedHeavyBadAt
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (index : HeavyFailureIndex r Delta typeCount) :
    Set (Sample r) :=
  if
      4 * (4 * r) ≤ Delta * HammingWeight index.1 ∧
      98 * typeCount ≤ 100 * index.2.1.card
    then
      {sample |
        ¬4 * r ≤
          100 *
            TwistGraph.heavyIncidentViolationCount
              (baseSample sample) (twistSample sample typeShifts)
              index.1 index.2.1
              (fun τ => (index.2.2.1 τ).1)
              (fun τ => (index.2.2.2 τ).1)}
    else ∅

/-- Every indexed heavy bad event has the sharp fixed-configuration mass
bound. -/
theorem measure_groupedHeavyBadAt_le
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (index : HeavyFailureIndex r Delta typeCount) :
    (distribution r Delta (by omega)).toMeasure.real
        (groupedHeavyBadAt
          r Delta typeCount ell typeShifts index) ≤
      Real.exp (-3 * (r : Real)) := by
  by_cases hAdmissible :
      4 * (4 * r) ≤ Delta * HammingWeight index.1 ∧
      98 * typeCount ≤ 100 * index.2.1.card
  · rw [groupedHeavyBadAt, if_pos hAdmissible]
    apply measure_not_heavyConfigurationConclusion_le
      r Delta typeCount ell hr hDeltaHalf hTypeDvd typeShifts
      index.1 index.2.1
      (fun τ => (index.2.2.1 τ).1)
      (fun τ => (index.2.2.2 τ).1)
      hAdmissible.1 hAdmissible.2
    intro τ _hτ
    exact ⟨(index.2.2.1 τ).2, (index.2.2.2 τ).2⟩
  · rw [groupedHeavyBadAt, if_neg hAdmissible]
    simp only [measureReal_empty]
    positivity

/-- Failure of the full deterministic heavy-check interface is covered by
the finite union of normalized globally-light configurations. -/
theorem groupedHeavyFailure_subset_iUnion_badAt
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (typeShifts : Fin typeCount → Fin (ell - 1)) :
    {sample |
      ¬TwistGraph.HasHHO20HeavyChecks Delta
        (baseSample sample) (twistSample sample typeShifts)} ⊆
      ⋃ index : HeavyFailureIndex r Delta typeCount,
        groupedHeavyBadAt
          r Delta typeCount ell typeShifts index := by
  classical
  intro sample hFailure
  change
    ¬TwistGraph.HasHHO20HeavyChecks Delta
      (baseSample sample) (twistSample sample typeShifts) at hFailure
  simp only [TwistGraph.HasHHO20HeavyChecks] at hFailure
  push Not at hFailure
  rcases hFailure with
    ⟨x, types, outWord, inWord, hx, hTypes, hNeighbors, hConclusion⟩
  let outConfig :
      Fin typeCount → HHO20LightNeighborWord r Delta :=
    fun τ =>
      if hτ : τ ∈ types then
        ⟨outWord τ, (hNeighbors τ hτ).1⟩
      else
        ⟨0, by simp⟩
  let inConfig :
      Fin typeCount → HHO20LightNeighborWord r Delta :=
    fun τ =>
      if hτ : τ ∈ types then
        ⟨inWord τ, (hNeighbors τ hτ).2⟩
      else
        ⟨0, by simp⟩
  let index : HeavyFailureIndex r Delta typeCount :=
    (x, types, outConfig, inConfig)
  apply Set.mem_iUnion.mpr
  refine ⟨index, ?_⟩
  rw [groupedHeavyBadAt, if_pos (show
    4 * (4 * r) ≤ Delta * HammingWeight index.1 ∧
      98 * typeCount ≤ 100 * index.2.1.card by
        simpa [index] using And.intro hx hTypes)]
  change
    ¬4 * r ≤
      100 *
        TwistGraph.heavyIncidentViolationCount
          (baseSample sample) (twistSample sample typeShifts)
          index.1 index.2.1
          (fun τ => (index.2.2.1 τ).1)
          (fun τ => (index.2.2.2 τ).1)
  intro hNormalized
  have hCountEq :
      TwistGraph.heavyIncidentViolationCount
          (baseSample sample) (twistSample sample typeShifts)
          index.1 index.2.1
          (fun τ => (index.2.2.1 τ).1)
          (fun τ => (index.2.2.2 τ).1) =
        TwistGraph.heavyIncidentViolationCount
          (baseSample sample) (twistSample sample typeShifts)
          x types outWord inWord := by
    simp only [TwistGraph.heavyIncidentViolationCount]
    apply Finset.sum_congr
    · simp [index]
    · intro τ hτ
      simp [index, outConfig, inConfig, hτ]
  have hNormalized' :
      4 * r ≤
        100 *
          TwistGraph.heavyIncidentViolationCount
            (baseSample sample) (twistSample sample typeShifts)
            x types outWord inWord := by
    rwa [hCountEq] at hNormalized
  omega

/-- Simultaneous heavy-check failure mass, expressed using the exact finite
configuration count. -/
theorem measure_groupedHHO20HeavyFailure_le
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (typeShifts : Fin typeCount → Fin (ell - 1)) :
    (distribution r Delta (by omega)).toMeasure.real
        {sample |
          ¬TwistGraph.HasHHO20HeavyChecks Delta
            (baseSample sample) (twistSample sample typeShifts)} ≤
      Fintype.card (HeavyFailureIndex r Delta typeCount) *
        Real.exp (-3 * (r : Real)) := by
  let badAt : HeavyFailureIndex r Delta typeCount → Set (Sample r) :=
    groupedHeavyBadAt r Delta typeCount ell typeShifts
  calc
    _ ≤
        (distribution r Delta (by omega)).toMeasure.real
          (⋃ index : HeavyFailureIndex r Delta typeCount,
            badAt index) :=
      measureReal_mono
        (groupedHeavyFailure_subset_iUnion_badAt
          r Delta typeCount ell typeShifts)
    _ ≤
        ∑ index : HeavyFailureIndex r Delta typeCount,
          (distribution r Delta (by omega)).toMeasure.real
            (badAt index) :=
      measureReal_iUnion_fintype_le badAt
    _ ≤
        ∑ _index : HeavyFailureIndex r Delta typeCount,
          Real.exp (-3 * (r : Real)) := by
      apply Finset.sum_le_sum
      intro index _hindex
      exact measure_groupedHeavyBadAt_le
        r Delta typeCount ell hr hDeltaHalf hTypeDvd
        typeShifts index
    _ = _ := by simp

/-- Exact product count for the finite heavy-configuration index. -/
theorem card_heavyFailureIndex
    (r Delta typeCount : Nat) :
    Fintype.card (HeavyFailureIndex r Delta typeCount) =
      2 ^ (4 * r) *
        (2 ^ typeCount *
          (Fintype.card (HHO20LightNeighborWord r Delta) ^ typeCount *
            Fintype.card (HHO20LightNeighborWord r Delta) ^ typeCount)) := by
  simp [HeavyFailureIndex, Word, Fintype.card_finset]

/-- Weighted counting bound for all light neighbor words.  It is an exact
finite analogue of the paper's binary-entropy estimate. -/
theorem card_lightNeighborWord_mul_invDelta_pow_le
    (r Delta : Nat) (hDelta : 0 < Delta) :
    (Fintype.card (HHO20LightNeighborWord r Delta) : Real) *
        (1 / (Delta : Real)) ^ ((8 * r) / Delta) ≤
      (1 + 1 / (Delta : Real)) ^ (4 * r) := by
  let t : Real := 1 / (Delta : Real)
  have hDeltaReal : (0 : Real) < Delta := by exact_mod_cast hDelta
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact (div_le_one₀ hDeltaReal).2 (by exact_mod_cast hDelta)
  calc
    (Fintype.card (HHO20LightNeighborWord r Delta) : Real) *
          t ^ ((8 * r) / Delta) =
        ∑ _w : HHO20LightNeighborWord r Delta,
          t ^ ((8 * r) / Delta) := by simp
    _ ≤
        ∑ w : HHO20LightNeighborWord r Delta,
          t ^ HammingWeight w.1 := by
      apply Finset.sum_le_sum
      intro w _hw
      apply pow_le_pow_of_le_one ht0 ht1
      apply (Nat.le_div_iff_mul_le hDelta).2
      calc
        HammingWeight w.1 * Delta =
            Delta * HammingWeight w.1 := Nat.mul_comm _ _
        _ ≤ 2 * (4 * r) := w.2
        _ = 8 * r := by omega
    _ ≤
        ∑ w : Word (ZMod 2) (Fin (4 * r)),
          t ^ HammingWeight w := by
      let predicate :
          Word (ZMod 2) (Fin (4 * r)) → Prop :=
        fun w => Delta * HammingWeight w ≤ 2 * (4 * r)
      let summand :
          Word (ZMod 2) (Fin (4 * r)) → Real :=
        fun w => t ^ HammingWeight w
      have hsplit :=
        Fintype.sum_subtype_add_sum_subtype predicate summand
      change
        (∑ w : {w : Word (ZMod 2) (Fin (4 * r)) // predicate w},
            summand w.1) ≤
          ∑ w : Word (ZMod 2) (Fin (4 * r)), summand w
      rw [← hsplit]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)
    _ = (1 + t) ^ (4 * r) :=
      sum_binaryWord_pow_hammingWeight r t

/-- Unweighted cardinal bound obtained by clearing the positive geometric
test weight. -/
theorem card_lightNeighborWord_le
    (r Delta : Nat) (hDelta : 0 < Delta) :
    (Fintype.card (HHO20LightNeighborWord r Delta) : Real) ≤
      (1 + 1 / (Delta : Real)) ^ (4 * r) *
        (Delta : Real) ^ ((8 * r) / Delta) := by
  have hWeighted :=
    card_lightNeighborWord_mul_invDelta_pow_le r Delta hDelta
  have hDeltaReal : (0 : Real) < Delta := by exact_mod_cast hDelta
  have hCancel :
      (1 / (Delta : Real)) ^ ((8 * r) / Delta) *
          (Delta : Real) ^ ((8 * r) / Delta) =
        1 := by
    rw [← mul_pow]
    field_simp
    simp
  calc
    (Fintype.card (HHO20LightNeighborWord r Delta) : Real) =
        ((Fintype.card
            (HHO20LightNeighborWord r Delta) : Real) *
          (1 / (Delta : Real)) ^ ((8 * r) / Delta)) *
            (Delta : Real) ^ ((8 * r) / Delta) := by
      rw [mul_assoc, hCancel, mul_one]
    _ ≤
        (1 + 1 / (Delta : Real)) ^ (4 * r) *
          (Delta : Real) ^ ((8 * r) / Delta) :=
      mul_le_mul_of_nonneg_right hWeighted (by positivity)

/-- Explicit real-valued product bound for the full heavy union index. -/
theorem card_heavyFailureIndex_real_le
    (r Delta typeCount : Nat) (hDelta : 0 < Delta) :
    (Fintype.card (HeavyFailureIndex r Delta typeCount) : Real) ≤
      (2 : Real) ^ (4 * r) *
        ((2 : Real) ^ typeCount *
          (((1 + 1 / (Delta : Real)) ^ (4 * r) *
              (Delta : Real) ^ ((8 * r) / Delta)) ^ typeCount *
            ((1 + 1 / (Delta : Real)) ^ (4 * r) *
              (Delta : Real) ^ ((8 * r) / Delta)) ^ typeCount)) := by
  rw [card_heavyFailureIndex]
  push_cast
  gcongr <;> exact card_lightNeighborWord_le r Delta hDelta

/-- A positive real power written as an exponential with a natural
multiplier. -/
theorem real_pow_eq_exp_nat_mul_log
    (x : Real) (n : Nat) (hx : 0 < x) :
    x ^ n = Real.exp ((n : Real) * Real.log x) := by
  calc
    x ^ n = (Real.exp (Real.log x)) ^ n := by
      rw [Real.exp_log hx]
    _ = Real.exp ((n : Real) * Real.log x) := by
      rw [Real.exp_nat_mul]

/-- The elementary exponential envelope for the weighted light-neighbor
count. -/
theorem lightNeighborCardEnvelope_le_exp
    (r Delta : Nat) (hDelta : 0 < Delta) :
    (1 + 1 / (Delta : Real)) ^ (4 * r) *
        (Delta : Real) ^ ((8 * r) / Delta) ≤
      Real.exp
        (((4 * r : Nat) : Real) / Delta +
          (((8 * r) / Delta : Nat) : Real) * Real.log Delta) := by
  have hDeltaReal : (0 : Real) < Delta := by exact_mod_cast hDelta
  have hInvNonneg : (0 : Real) ≤ 1 / Delta := by positivity
  have hFirst :
      (1 + 1 / (Delta : Real)) ^ (4 * r) ≤
        Real.exp (((4 * r : Nat) : Real) / Delta) := by
    calc
      _ ≤ (Real.exp (1 / (Delta : Real))) ^ (4 * r) := by
        apply pow_le_pow_left₀ (by positivity)
        simpa [add_comm] using Real.add_one_le_exp (1 / (Delta : Real))
      _ = Real.exp (((4 * r : Nat) : Real) / Delta) := by
        rw [← Real.exp_nat_mul]
        ring_nf
  calc
    _ ≤
        Real.exp (((4 * r : Nat) : Real) / Delta) *
          (Delta : Real) ^ ((8 * r) / Delta) :=
      mul_le_mul_of_nonneg_right hFirst (by positivity)
    _ =
        Real.exp (((4 * r : Nat) : Real) / Delta) *
          Real.exp
            ((((8 * r) / Delta : Nat) : Real) *
              Real.log Delta) := by
      rw [real_pow_eq_exp_nat_mul_log
        (Delta : Real) ((8 * r) / Delta) hDeltaReal]
    _ = _ := by rw [← Real.exp_add]

/-- The heavy union term is bounded by one explicit exponential exponent. -/
theorem heavyFailureUnionTerm_le_exp
    (r Delta typeCount : Nat) (hDelta : 0 < Delta) :
    (Fintype.card (HeavyFailureIndex r Delta typeCount) : Real) *
        Real.exp (-3 * (r : Real)) ≤
      Real.exp
        ((((4 * r + typeCount : Nat) : Real) * Real.log 2) +
          ((2 * typeCount : Nat) : Real) *
            ((((4 * r : Nat) : Real) / Delta) +
              (((8 * r) / Delta : Nat) : Real) * Real.log Delta) -
          3 * (r : Real)) := by
  let B : Real :=
    (1 + 1 / (Delta : Real)) ^ (4 * r) *
      (Delta : Real) ^ ((8 * r) / Delta)
  let A : Real :=
    (((4 * r : Nat) : Real) / Delta) +
      (((8 * r) / Delta : Nat) : Real) * Real.log Delta
  have hCard :
      (Fintype.card (HeavyFailureIndex r Delta typeCount) : Real) ≤
        (2 : Real) ^ (4 * r) *
          ((2 : Real) ^ typeCount *
            (B ^ typeCount * B ^ typeCount)) := by
    simpa [B] using
      card_heavyFailureIndex_real_le r Delta typeCount hDelta
  have hB : B ≤ Real.exp A := by
    simpa [B, A] using lightNeighborCardEnvelope_le_exp r Delta hDelta
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  calc
    _ ≤
        ((2 : Real) ^ (4 * r) *
          ((2 : Real) ^ typeCount *
            (B ^ typeCount * B ^ typeCount))) *
          Real.exp (-3 * (r : Real)) :=
      mul_le_mul_of_nonneg_right hCard (Real.exp_pos _).le
    _ =
        (2 : Real) ^ (4 * r + typeCount) *
          B ^ (2 * typeCount) *
          Real.exp (-3 * (r : Real)) := by
      simp only [pow_add]
      ring
    _ =
        Real.exp
            (((4 * r + typeCount : Nat) : Real) * Real.log 2) *
          B ^ (2 * typeCount) *
          Real.exp (-3 * (r : Real)) := by
      rw [real_pow_eq_exp_nat_mul_log
        (2 : Real) (4 * r + typeCount) (by norm_num)]
    _ ≤
        Real.exp
            (((4 * r + typeCount : Nat) : Real) * Real.log 2) *
          (Real.exp A) ^ (2 * typeCount) *
          Real.exp (-3 * (r : Real)) := by
      gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [A]
      push_cast
      ring

/-- Paper-natural scale conditions make the full heavy union exponentially
small, with a concrete remaining exponent `r/10`. -/
theorem heavyFailureUnionTerm_le_exp_neg_tenth
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hDelta : 0 < Delta) (hDeltaOne : 1 ≤ Delta)
    (hTypeSmall :
      (100 : Real) * typeCount ≤ r)
    (hScale :
      (100 : Real) * typeCount *
          (1 + 2 * Real.log Delta) ≤
        Delta) :
    (Fintype.card (HeavyFailureIndex r Delta typeCount) : Real) *
        Real.exp (-3 * (r : Real)) ≤
      Real.exp (-(r : Real) / 10) := by
  have hEnvelope :=
    heavyFailureUnionTerm_le_exp r Delta typeCount hDelta
  apply hEnvelope.trans
  apply Real.exp_le_exp.mpr
  have hDeltaReal : (0 : Real) < Delta := by exact_mod_cast hDelta
  have hLogDelta : 0 ≤ Real.log (Delta : Real) :=
    Real.log_nonneg (by exact_mod_cast hDeltaOne)
  have hLogTwo : Real.log 2 ≤ (7 : Real) / 10 := by
    exact le_trans (le_of_lt Real.log_two_lt_d9) (by norm_num)
  have hK :
      ((((8 * r) / Delta : Nat) : Real)) ≤
        ((8 * r : Nat) : Real) / Delta :=
    Nat.cast_div_le
  have hKLog :
      ((((8 * r) / Delta : Nat) : Real) * Real.log Delta) ≤
        (((8 * r : Nat) : Real) / Delta) * Real.log Delta :=
    mul_le_mul_of_nonneg_right hK hLogDelta
  have hBinary :
      (((4 * r + typeCount : Nat) : Real) * Real.log 2) ≤
        (((4 * r + typeCount : Nat) : Real) * ((7 : Real) / 10)) :=
    mul_le_mul_of_nonneg_left hLogTwo (by positivity)
  have hBinary' :
      (((4 * r + typeCount : Nat) : Real) * Real.log 2) ≤
        (14 : Real) / 5 * r + (7 : Real) / 10 * typeCount := by
    calc
      _ ≤
          (((4 * r + typeCount : Nat) : Real) *
            ((7 : Real) / 10)) := hBinary
      _ = _ := by push_cast; ring
  have hNeighborRaw :
      ((2 * typeCount : Nat) : Real) *
          ((((4 * r : Nat) : Real) / Delta) +
            (((8 * r) / Delta : Nat) : Real) * Real.log Delta) ≤
        ((2 * typeCount : Nat) : Real) *
          ((((4 * r : Nat) : Real) / Delta) +
            (((8 * r : Nat) : Real) / Delta) * Real.log Delta) := by
    gcongr
  have hQ :
      (typeCount : Real) * (1 + 2 * Real.log Delta) / Delta ≤
        (1 : Real) / 100 := by
    apply (div_le_iff₀ hDeltaReal).2
    nlinarith
  have hNeighborEq :
      ((2 * typeCount : Nat) : Real) *
          ((((4 * r : Nat) : Real) / Delta) +
            (((8 * r : Nat) : Real) / Delta) * Real.log Delta) =
        8 * (r : Real) *
          ((typeCount : Real) * (1 + 2 * Real.log Delta) / Delta) := by
    push_cast
    field_simp
    ring
  have hNeighbor :
      ((2 * typeCount : Nat) : Real) *
          ((((4 * r : Nat) : Real) / Delta) +
            (((8 * r) / Delta : Nat) : Real) * Real.log Delta) ≤
        (2 : Real) / 25 * r := by
    calc
      _ ≤
          ((2 * typeCount : Nat) : Real) *
            ((((4 * r : Nat) : Real) / Delta) +
              (((8 * r : Nat) : Real) / Delta) *
                Real.log Delta) := hNeighborRaw
      _ =
          8 * (r : Real) *
            ((typeCount : Real) *
              (1 + 2 * Real.log Delta) / Delta) := hNeighborEq
      _ ≤ 8 * (r : Real) * ((1 : Real) / 100) := by
        gcongr
      _ = (2 : Real) / 25 * r := by ring
  calc
    (((4 * r + typeCount : Nat) : Real) * Real.log 2) +
          ((2 * typeCount : Nat) : Real) *
            ((((4 * r : Nat) : Real) / Delta) +
              (((8 * r) / Delta : Nat) : Real) * Real.log Delta) -
        3 * (r : Real) ≤
      ((14 : Real) / 5 * r + (7 : Real) / 10 * typeCount) +
        (2 : Real) / 25 * r - 3 * r := by
      gcongr
    _ ≤ -(r : Real) / 10 := by
      nlinarith

/-- Simultaneous HHO20 heavy-check failure has the concrete exponential
bound under the paper-natural scale regime. -/
theorem measure_groupedHHO20HeavyFailure_le_exp_neg_tenth
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hDelta : 0 < Delta) (hDeltaOne : 1 ≤ Delta)
    (hTypeSmall : (100 : Real) * typeCount ≤ r)
    (hScale :
      (100 : Real) * typeCount *
          (1 + 2 * Real.log Delta) ≤
        Delta)
    (typeShifts : Fin typeCount → Fin (ell - 1)) :
    (distribution r Delta (by omega)).toMeasure.real
        {sample |
          ¬TwistGraph.HasHHO20HeavyChecks Delta
            (baseSample sample) (twistSample sample typeShifts)} ≤
      Real.exp (-(r : Real) / 10) := by
  exact
    (measure_groupedHHO20HeavyFailure_le
      r Delta typeCount ell hr hDeltaHalf hTypeDvd typeShifts).trans
      (heavyFailureUnionTerm_le_exp_neg_tenth
        r Delta typeCount hDelta hDeltaOne hTypeSmall hScale)

/-- Once `r ≥ 7`, the remaining heavy failure exponential is below one
half. -/
theorem exp_neg_r_div_ten_lt_half
    (r : Nat) (hr : 7 ≤ r) :
    Real.exp (-(r : Real) / 10) < (1 : Real) / 2 := by
  have hLog :
      Real.log 2 < (r : Real) / 10 := by
    have hSeven : (7 : Real) ≤ r := by exact_mod_cast hr
    have hApprox := Real.log_two_lt_d9
    nlinarith
  calc
    Real.exp (-(r : Real) / 10) <
        Real.exp (-Real.log 2) := by
      apply Real.exp_lt_exp.mpr
      linarith
    _ = (1 : Real) / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : Real) < 2)]
      rw [one_div]

/-- A factor-two strengthening of the light geometric union estimate, used
to reserve the other half of the probability budget for heavy checks. -/
theorem light_geometric_union_lt_half_of_exp_lt
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r)
    (hExpSmall :
      Real.exp
          (-(Delta : Real) / (200 * typeCount)) <
        1 / (32 * r * typeCount : Nat)) :
    (typeCount : Real) *
        ((1 +
          Real.exp
            (-(Delta : Real) / (200 * typeCount))) ^
              (8 * r) - 1) < (1 : Real) / 2 := by
  let t : Real :=
    Real.exp (-(Delta : Real) / (200 * typeCount))
  let x : Real := (8 * r : Nat) * t
  have ht0 : 0 ≤ t := (Real.exp_pos _).le
  have hTypeOne : (1 : Real) ≤ typeCount := by
    exact_mod_cast NeZero.pos typeCount
  have hDenPos : (0 : Real) < (32 * r * typeCount : Nat) := by
    exact_mod_cast
      Nat.mul_pos (Nat.mul_pos (by omega) hr) (NeZero.pos typeCount)
  have hSmallMul :
      t * (32 * r * typeCount : Nat) < 1 := by
    exact (lt_div_iff₀ hDenPos).1 (by simpa [t] using hExpSmall)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    have hrReal : (0 : Real) < r := by exact_mod_cast hr
    push_cast at hSmallMul ⊢
    have hfactor :
        8 * (r : Real) * t ≤
          8 * (r : Real) * t * typeCount := by
      exact le_mul_of_one_le_right
        (mul_nonneg (by positivity) ht0) hTypeOne
    nlinarith
  have hPowExp :
      (1 + t) ^ (8 * r) ≤ Real.exp x := by
    calc
      _ ≤ (Real.exp t) ^ (8 * r) :=
        pow_le_pow_left₀ (by positivity)
          (by simpa [add_comm] using Real.add_one_le_exp t)
          (8 * r)
      _ = Real.exp ((8 * r : Nat) * t) := by
        rw [← Real.exp_nat_mul]
      _ = Real.exp x := rfl
  have hExpLinear : Real.exp x - 1 ≤ 2 * x := by
    have hAbs :=
      Real.abs_exp_sub_one_le
        (show |x| ≤ 1 by simpa [abs_of_nonneg hx0] using hx1)
    calc
      Real.exp x - 1 ≤ |Real.exp x - 1| := le_abs_self _
      _ ≤ 2 * |x| := hAbs
      _ = 2 * x := by rw [abs_of_nonneg hx0]
  calc
    (typeCount : Real) * ((1 + t) ^ (8 * r) - 1) ≤
        typeCount * (Real.exp x - 1) := by
      gcongr
    _ ≤ typeCount * (2 * x) := by
      gcongr
    _ < (1 : Real) / 2 := by
      dsimp [x] at *
      push_cast at hSmallMul ⊢
      nlinarith

/-- Logarithmic scale condition for the half-budget light estimate. -/
theorem exp_neg_delta_div_lt_inv_thirtyTwo_of_log_scale
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r)
    (hLogScale :
      200 * (typeCount : Real) *
          Real.log (32 * r * typeCount : Nat) <
        Delta) :
    Real.exp
        (-(Delta : Real) / (200 * typeCount)) <
      1 / (32 * r * typeCount : Nat) := by
  have hTypePos : (0 : Real) < typeCount := by
    exact_mod_cast NeZero.pos typeCount
  have hDenPos : (0 : Real) < (32 * r * typeCount : Nat) := by
    exact_mod_cast
      Nat.mul_pos (Nat.mul_pos (by omega) hr) (NeZero.pos typeCount)
  have hScalePos : (0 : Real) < 200 * typeCount := by positivity
  have hLogDiv :
      Real.log (32 * r * typeCount : Nat) <
        (Delta : Real) / (200 * typeCount) := by
    apply (lt_div_iff₀ hScalePos).2
    nlinarith
  have hExp :
      Real.exp (-(Delta : Real) / (200 * typeCount)) <
        Real.exp (-Real.log (32 * r * typeCount : Nat)) := by
    apply Real.exp_lt_exp.mpr
    simpa only [neg_div] using neg_lt_neg hLogDiv
  calc
    _ < Real.exp (-Real.log (32 * r * typeCount : Nat)) := hExp
    _ = 1 / (32 * r * typeCount : Nat) := by
      rw [Real.exp_neg, Real.exp_log hDenPos]
      rw [one_div]

/-- Grouped sampler formulation of the two partitioned-check events. -/
def HasGroupedHHO20PartitionedChecks
    {r typeCount ell : Nat} [NeZero typeCount]
    (Delta : Nat) (typeShifts : Fin typeCount → Fin (ell - 1))
    (sample : Sample r) : Prop :=
  HasGroupedHHO20LightChecks
      (r := r) (typeCount := typeCount) Delta sample ∧
    TwistGraph.HasHHO20HeavyChecks Delta
      (baseSample sample) (twistSample sample typeShifts)

/-- The combined light/heavy failure mass under the quantitative scale
conditions. -/
theorem measure_groupedHHO20PartitionedChecksFailure_le
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hDelta : 0 < Delta) (hDeltaOne : 1 ≤ Delta)
    (hTypeSmall : (100 : Real) * typeCount ≤ r)
    (hHeavyScale :
      (100 : Real) * typeCount *
          (1 + 2 * Real.log Delta) ≤
        Delta)
    (typeShifts : Fin typeCount → Fin (ell - 1)) :
    (distribution r Delta (by omega)).toMeasure.real
        {sample |
          ¬HasGroupedHHO20PartitionedChecks
            Delta typeShifts sample} ≤
      (typeCount : Real) *
          ((1 +
            Real.exp
              (-(Delta : Real) / (200 * typeCount))) ^
                (8 * r) - 1) +
        Real.exp (-(r : Real) / 10) := by
  let μ := (distribution r Delta (by omega)).toMeasure
  let lightBad : Set (Sample r) :=
    {sample |
      ¬HasGroupedHHO20LightChecks
        (r := r) (typeCount := typeCount) Delta sample}
  let heavyBad : Set (Sample r) :=
    {sample |
      ¬TwistGraph.HasHHO20HeavyChecks Delta
        (baseSample sample) (twistSample sample typeShifts)}
  have hFailure :
      {sample |
        ¬HasGroupedHHO20PartitionedChecks
          Delta typeShifts sample} =
        lightBad ∪ heavyBad := by
    ext sample
    simp only [HasGroupedHHO20PartitionedChecks, lightBad, heavyBad,
      Set.mem_setOf_eq, Set.mem_union]
    tauto
  rw [hFailure]
  calc
    μ.real (lightBad ∪ heavyBad) ≤
        μ.real lightBad + μ.real heavyBad :=
      MeasureTheory.measureReal_union_le lightBad heavyBad
    _ ≤
        (typeCount : Real) *
            ((1 +
              Real.exp
                (-(Delta : Real) / (200 * typeCount))) ^
                  (8 * r) - 1) +
          Real.exp (-(r : Real) / 10) := by
      apply add_le_add
      · exact measure_groupedHHO20LightFailure_le
          r Delta typeCount hr hDeltaHalf hTypeDvd
      · exact
          measure_groupedHHO20HeavyFailure_le_exp_neg_tenth
            r Delta typeCount ell hr hDeltaHalf hTypeDvd
            hDelta hDeltaOne hTypeSmall hHeavyScale typeShifts

/-- A grouped sample satisfying light and heavy partitioned checks exists
once each union bound is assigned half of the probability budget. -/
theorem exists_sample_hasGroupedHHO20PartitionedChecks
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (hr : 7 ≤ r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hDelta : 0 < Delta) (hDeltaOne : 1 ≤ Delta)
    (hTypeSmall : (100 : Real) * typeCount ≤ r)
    (hHeavyScale :
      (100 : Real) * typeCount *
          (1 + 2 * Real.log Delta) ≤
        Delta)
    (hLightLogScale :
      200 * (typeCount : Real) *
          Real.log (32 * r * typeCount : Nat) <
        Delta)
    (typeShifts : Fin typeCount → Fin (ell - 1)) :
    ∃ sample : Sample r,
      HasGroupedHHO20PartitionedChecks
        Delta typeShifts sample := by
  let μ := (distribution r Delta (by omega)).toMeasure
  have hrPos : 0 < r := by omega
  have hLightHalf :
      (typeCount : Real) *
          ((1 +
            Real.exp
              (-(Delta : Real) / (200 * typeCount))) ^
                (8 * r) - 1) < (1 : Real) / 2 :=
    light_geometric_union_lt_half_of_exp_lt
      r Delta typeCount hrPos
      (exp_neg_delta_div_lt_inv_thirtyTwo_of_log_scale
        r Delta typeCount hrPos hLightLogScale)
  have hHeavyHalf :
      Real.exp (-(r : Real) / 10) < (1 : Real) / 2 :=
    exp_neg_r_div_ten_lt_half r hr
  have hBadLt :
      μ.real
          {sample |
            ¬HasGroupedHHO20PartitionedChecks
              Delta typeShifts sample} < 1 := by
    exact lt_of_le_of_lt
      (measure_groupedHHO20PartitionedChecksFailure_le
        r Delta typeCount ell hrPos hDeltaHalf hTypeDvd
        hDelta hDeltaOne hTypeSmall hHeavyScale typeShifts)
      (by linarith)
  by_contra hNoGood
  push Not at hNoGood
  have hBadUniv :
      {sample : Sample r |
        ¬HasGroupedHHO20PartitionedChecks
          Delta typeShifts sample} = Set.univ :=
    Set.eq_univ_of_forall hNoGood
  have hMeasureOne :
      μ.real
          {sample |
            ¬HasGroupedHHO20PartitionedChecks
              Delta typeShifts sample} = 1 := by
    rw [hBadUniv]
    simp [μ]
  linarith

/-- Grouped light checks plus deterministic heavy checks are exactly the
partitioned-check interface consumed by `TwistGraph.thm_ltc`. -/
theorem hasHHO20PartitionedChecks_of_hasGrouped
    {r Delta typeCount ell : Nat} [NeZero typeCount]
    (sample : Sample r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (h :
      HasGroupedHHO20PartitionedChecks
        Delta typeShifts sample) :
    TwistGraph.HasHHO20PartitionedChecks Delta
      (baseSample sample) (twistSample sample typeShifts) := by
  exact
    ⟨hasHHO20LightChecks_of_hasGrouped
        sample typeShifts h.1,
      h.2⟩

/-- Public positive-probability selection theorem for all partitioned HHO20
checks, with no caller-supplied matrix or check-quality assumption. -/
theorem exists_sample_hasHHO20PartitionedChecks
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (hr : 7 ≤ r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hDelta : 0 < Delta) (hDeltaOne : 1 ≤ Delta)
    (hTypeSmall : (100 : Real) * typeCount ≤ r)
    (hHeavyScale :
      (100 : Real) * typeCount *
          (1 + 2 * Real.log Delta) ≤
        Delta)
    (hLightLogScale :
      200 * (typeCount : Real) *
          Real.log (32 * r * typeCount : Nat) <
        Delta)
    (typeShifts : Fin typeCount → Fin (ell - 1)) :
    ∃ sample : Sample r,
      TwistGraph.HasHHO20PartitionedChecks Delta
        (baseSample sample) (twistSample sample typeShifts) := by
  obtain ⟨sample, hsample⟩ :=
    exists_sample_hasGroupedHHO20PartitionedChecks
      r Delta typeCount ell hr hDeltaHalf hTypeDvd
      hDelta hDeltaOne hTypeSmall hHeavyScale
      hLightLogScale typeShifts
  exact
    ⟨sample,
      hasHHO20PartitionedChecks_of_hasGrouped
        sample typeShifts hsample⟩

/-- The construction-owned base event combines all four random-base
properties with the two partitioned-check properties. -/
def HasGroupedHHO20ConstructionBase
    {r typeCount ell : Nat} [NeZero typeCount]
    (Delta : Nat) (typeShifts : Fin typeCount → Fin (ell - 1))
    (sample : Sample r) : Prop :=
  RandomBase.IsFullyGood
      (Delta := Delta) (baseSample sample) ∧
    HasGroupedHHO20PartitionedChecks
      Delta typeShifts sample

/-- Failure mass for the entire random base layer: rank, classical distance,
degree windows, strong small-set expansion, and both partitioned-check
events. -/
theorem measure_groupedHHO20ConstructionBaseFailure_le
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hDelta : 0 < Delta) (hDeltaOne : 1 ≤ Delta)
    (hTypeSmall : (100 : Real) * typeCount ≤ r)
    (hHeavyScale :
      (100 : Real) * typeCount *
          (1 + 2 * Real.log Delta) ≤
        Delta)
    (typeShifts : Fin typeCount → Fin (ell - 1)) :
    (distribution r Delta (by omega)).toMeasure.real
        {sample |
          ¬HasGroupedHHO20ConstructionBase
            Delta typeShifts sample} ≤
      (fullyGoodBaseFailureBound r Delta).toReal +
        ((typeCount : Real) *
            ((1 +
              Real.exp
                (-(Delta : Real) / (200 * typeCount))) ^
                  (8 * r) - 1) +
          Real.exp (-(r : Real) / 10)) := by
  let hDeltaFour : Delta ≤ 4 * r := by omega
  let μ := (distribution r Delta hDeltaFour).toMeasure
  let baseBad : Set (Sample r) :=
    {sample |
      ¬RandomBase.IsFullyGood
        (Delta := Delta) (baseSample sample)}
  let partitionBad : Set (Sample r) :=
    {sample |
      ¬HasGroupedHHO20PartitionedChecks
        Delta typeShifts sample}
  have hFailure :
      {sample |
        ¬HasGroupedHHO20ConstructionBase
          Delta typeShifts sample} =
        baseBad ∪ partitionBad := by
    ext sample
    simp only [HasGroupedHHO20ConstructionBase, baseBad, partitionBad,
      Set.mem_setOf_eq, Set.mem_union]
    tauto
  rw [hFailure]
  calc
    μ.real (baseBad ∪ partitionBad) ≤
        μ.real baseBad + μ.real partitionBad :=
      MeasureTheory.measureReal_union_le baseBad partitionBad
    _ ≤
        (fullyGoodBaseFailureBound r Delta).toReal +
          ((typeCount : Real) *
              ((1 +
                Real.exp
                  (-(Delta : Real) / (200 * typeCount))) ^
                    (8 * r) - 1) +
            Real.exp (-(r : Real) / 10)) := by
      apply add_le_add
      · exact measure_not_isFullyGood_baseSample_le
          r Delta hr hDeltaFour (by omega)
      · exact
          measure_groupedHHO20PartitionedChecksFailure_le
            r Delta typeCount ell hr hDeltaHalf hTypeDvd
            hDelta hDeltaOne hTypeSmall hHeavyScale typeShifts

/-- Exact finite numeric selection theorem for the complete random base
layer.  Later parameter lemmas discharge `hNumeric`; it is not exposed by the
final code-family theorem. -/
theorem exists_sample_isFullyGood_and_hasHHO20PartitionedChecks
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hDelta : 0 < Delta) (hDeltaOne : 1 ≤ Delta)
    (hTypeSmall : (100 : Real) * typeCount ≤ r)
    (hHeavyScale :
      (100 : Real) * typeCount *
          (1 + 2 * Real.log Delta) ≤
        Delta)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (hNumeric :
      (fullyGoodBaseFailureBound r Delta).toReal +
          ((typeCount : Real) *
              ((1 +
                Real.exp
                  (-(Delta : Real) / (200 * typeCount))) ^
                    (8 * r) - 1) +
            Real.exp (-(r : Real) / 10)) <
        1) :
    ∃ sample : Sample r,
      RandomBase.IsFullyGood
          (Delta := Delta) (baseSample sample) ∧
        TwistGraph.HasHHO20PartitionedChecks Delta
          (baseSample sample) (twistSample sample typeShifts) := by
  let μ := (distribution r Delta (by omega)).toMeasure
  have hBadLt :
      μ.real
          {sample |
            ¬HasGroupedHHO20ConstructionBase
              Delta typeShifts sample} < 1 :=
    lt_of_le_of_lt
      (measure_groupedHHO20ConstructionBaseFailure_le
        r Delta typeCount ell hr hDeltaHalf hTypeDvd
        hDelta hDeltaOne hTypeSmall hHeavyScale typeShifts)
      hNumeric
  have hExists :
      ∃ sample : Sample r,
        HasGroupedHHO20ConstructionBase
          Delta typeShifts sample := by
    by_contra hNoGood
    push Not at hNoGood
    have hBadUniv :
        {sample : Sample r |
          ¬HasGroupedHHO20ConstructionBase
            Delta typeShifts sample} = Set.univ :=
      Set.eq_univ_of_forall hNoGood
    have hMeasureOne :
        μ.real
            {sample |
              ¬HasGroupedHHO20ConstructionBase
                Delta typeShifts sample} = 1 := by
      rw [hBadUniv]
      simp [μ]
    linarith
  obtain ⟨sample, hBase, hPartition⟩ := hExists
  exact
    ⟨sample, hBase,
      hasHHO20PartitionedChecks_of_hasGrouped
        sample typeShifts hPartition⟩

/-- Replacing the head/tail bits while retaining every sampled type twist
leaves the Cayley multiplier unchanged. -/
theorem cayleyMultiplier_twistSample_typeTwist
    {r typeCount ell : Nat} [NeZero ell]
    (partitionSample : Sample r)
    (spectrumSample : RandomTwist.Sample r typeCount ell)
    (frequency : ZMod ell) :
    TwistGraph.cayleyMultiplier
        (twistSample partitionSample
          (fun τ => RandomTwist.typeTwist spectrumSample τ))
        frequency =
      TwistGraph.cayleyMultiplier spectrumSample frequency := by
  simp [TwistGraph.cayleyMultiplier, TwistGraph.step]

/-- The spectrum event depends only on type twists, so it survives assembly
with independently selected partition bits. -/
theorem hasHHO20CayleySpectrum_twistSample_typeTwist
    {r typeCount ell : Nat} [NeZero ell]
    (partitionSample : Sample r)
    (spectrumSample : RandomTwist.Sample r typeCount ell)
    (hSpectrum : TwistGraph.HasHHO20CayleySpectrum spectrumSample) :
    TwistGraph.HasHHO20CayleySpectrum
      (twistSample partitionSample
        (fun τ => RandomTwist.typeTwist spectrumSample τ)) := by
  intro frequency hfrequency
  rw [cayleyMultiplier_twistSample_typeTwist]
  exact hSpectrum frequency hfrequency

/-- Complete finite random-selection closure before asymptotic parameter
specialization: one construction-owned base/twist pair has all random-base
properties, partitioned checks, Cayley spectrum, and local testability. -/
theorem exists_fullyGood_hho20_base_and_twist
    (r Delta typeCount ell : Nat)
    [NeZero r] [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hDeltaForty : 40 ≤ Delta)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hDelta : 0 < Delta) (hDeltaOne : 1 ≤ Delta)
    (hTypeSmall : (100 : Real) * typeCount ≤ r)
    (hHeavyScale :
      (100 : Real) * typeCount *
          (1 + 2 * Real.log Delta) ≤
        Delta)
    (hEll : 100001 ≤ ell)
    (hTypeCountSpectrum :
      (40000000000 : Real) * Real.log (ell : Real) ≤
        (typeCount : Real))
    (hNumeric :
      (fullyGoodBaseFailureBound r Delta).toReal +
          ((typeCount : Real) *
              ((1 +
                Real.exp
                  (-(Delta : Real) / (200 * typeCount))) ^
                    (8 * r) - 1) +
            Real.exp (-(r : Real) / 10)) <
        1) :
    ∃ (baseSample : RandomBase.Sample r)
        (twistSample : RandomTwist.Sample r typeCount ell),
      RandomBase.IsFullyGood
          (Delta := Delta) baseSample ∧
        TwistGraph.HasHHO20PartitionedChecks
          Delta baseSample twistSample ∧
        TwistGraph.HasHHO20CayleySpectrum twistSample ∧
        TwistGraph.HasHHO20LocalTestability
          Delta baseSample twistSample := by
  obtain ⟨spectrumSample, hSpectrumSample⟩ :=
    TwistGraph.exists_twistSample_hasHHO20CayleySpectrum
      r typeCount ell hEll hTypeCountSpectrum
  let typeShifts : Fin typeCount → Fin (ell - 1) :=
    fun τ => RandomTwist.typeTwist spectrumSample τ
  obtain ⟨partitionSample, hBase, hChecks⟩ :=
    exists_sample_isFullyGood_and_hasHHO20PartitionedChecks
      r Delta typeCount ell hr hDeltaHalf hTypeDvd
      hDelta hDeltaOne hTypeSmall hHeavyScale
      typeShifts hNumeric
  let assembledTwist :=
    twistSample partitionSample typeShifts
  have hSpectrum :
      TwistGraph.HasHHO20CayleySpectrum assembledTwist := by
    exact hasHHO20CayleySpectrum_twistSample_typeTwist
      partitionSample spectrumSample hSpectrumSample
  have hOperator :
      TwistGraph.HasHHO20OperatorMixing assembledTwist :=
    TwistGraph.hasHHO20OperatorMixing_of_cayleySpectrum
      assembledTwist hSpectrum
  have hSquared :
      TwistGraph.HasHHO20SquaredExpanderMixing assembledTwist :=
    TwistGraph.hasHHO20SquaredExpanderMixing_of_operatorMixing
      assembledTwist hOperator
  have hEdge :
      TwistGraph.HasHHO20EdgeMixing Delta assembledTwist :=
    TwistGraph.hasHHO20EdgeMixing_of_squaredExpanderMixing
      Delta assembledTwist hSquared
  have hLayer :
      TwistGraph.HasHHO20LayerMixing Delta assembledTwist :=
    TwistGraph.hasHHO20LayerMixing_of_edgeMixing
      Delta assembledTwist hEdge
  have hLocal :
      TwistGraph.HasHHO20LocalTestability
        Delta (baseSample partitionSample) assembledTwist :=
    TwistGraph.hasHHO20LocalTestability_of_partitionedChecks_and_layerMixing
      Delta (baseSample partitionSample) assembledTwist
      hDeltaForty hChecks hLayer
  exact
    ⟨baseSample partitionSample, assembledTwist,
      hBase, hChecks, hSpectrum, hLocal⟩

end QEC.Coding.FiberBundle.RandomPartition
