import QEC.Coding.FiberBundle.TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian

/-!
# Random character bounds for the HHO20 cyclic twist graph

Each type shift is uniform on the nonzero elements of `ZMod ell`.  For a
nonzero frequency, its undirected character contribution has exact mean
`-2 / (ell - 1)` and lies in `[-2, 2]`.  This file develops the independent
sub-Gaussian variables needed for the Alon--Roichman union bound.
-/

namespace QEC.Coding.FiberBundle.TwistGraph

open scoped BigOperators ZMod ENNReal NNReal

local instance instMeasurableSpaceChoiceValue
    (ell : Nat) {r typeCount : Nat}
    (i : RandomTwist.ChoiceIndex r typeCount) :
    MeasurableSpace (RandomTwist.ChoiceValue ell i) := by
  cases i with
  | inl _ =>
      change MeasurableSpace Bool
      infer_instance
  | inr _ =>
      change MeasurableSpace (Fin (ell - 1))
      infer_instance

local instance instMeasurableSingletonClassChoiceValue
    (ell : Nat) {r typeCount : Nat}
    (i : RandomTwist.ChoiceIndex r typeCount) :
    MeasurableSingletonClass (RandomTwist.ChoiceValue ell i) := by
  cases i with
  | inl _ =>
      change MeasurableSingletonClass Bool
      infer_instance
  | inr _ =>
      change MeasurableSingletonClass (Fin (ell - 1))
      infer_instance

/-- Undirected character contribution of one nonzero shift value. -/
noncomputable def typeCharacterValue
    {ell : Nat}
    [NeZero ell]
    (frequency : ZMod ell)
    (shiftIndex : Fin (ell - 1)) : Real :=
  2 *
    (ZMod.stdAddChar
      (((shiftIndex.val + 1 : Nat) : ZMod ell) * frequency)).re

/-- The corresponding contribution read from one sampled check type. -/
noncomputable def sampledTypeCharacter
    {r typeCount ell : Nat}
    [NeZero ell]
    (frequency : ZMod ell)
    (τ : Fin typeCount)
    (sample : RandomTwist.Sample r typeCount ell) : Real :=
  typeCharacterValue frequency (RandomTwist.typeTwist sample τ)

/-- One character contribution centered at its exact nonzero-shift mean. -/
noncomputable def centeredSampledTypeCharacter
    {r typeCount ell : Nat}
    [NeZero ell]
    (frequency : ZMod ell)
    (τ : Fin typeCount)
    (sample : RandomTwist.Sample r typeCount ell) : Real :=
  sampledTypeCharacter frequency τ sample -
    (-2 / (ell - 1 : Real))

/-- Sum of all centered type-character contributions at one frequency. -/
noncomputable def centeredCharacterSum
    {r typeCount ell : Nat}
    [NeZero ell]
    (frequency : ZMod ell)
    (sample : RandomTwist.Sample r typeCount ell) : Real :=
  ∑ τ : Fin typeCount,
    centeredSampledTypeCharacter frequency τ sample

/-- Failure of the centered character bound at one frequency. -/
def CenteredFrequencyBad
    {r typeCount ell : Nat}
    [NeZero ell]
    (frequency : ZMod ell)
    (sample : RandomTwist.Sample r typeCount ell) : Prop :=
  (typeCount : Real) / 50000 <
    |centeredCharacterSum frequency sample|

/-- Some nonzero frequency violates the centered character bound. -/
def CenteredSpectrumBad
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell) : Prop :=
  ∃ frequency : ZMod ell,
    frequency ≠ 0 ∧ CenteredFrequencyBad frequency sample

theorem finEquiv_apply_eq_natCast
    {ell : Nat} [NeZero ell] (i : Fin ell) :
    (ZMod.finEquiv ell) i = (i.val : ZMod ell) := by
  cases ell with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      simp only [ZMod.finEquiv]
      apply Fin.ext
      change i.val = i.val % (n + 1)
      exact (Nat.mod_eq_of_lt i.isLt).symm

/--
The nonzero representatives `1, ..., ell - 1` have character sum `-1` at
every nonzero frequency.
-/
theorem sum_nonzero_stdAddChar
    {ell : Nat}
    [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell)
    (hfrequency : frequency ≠ 0) :
    (∑ shiftIndex : Fin (ell - 1),
        ZMod.stdAddChar
          (((shiftIndex.val + 1 : Nat) : ZMod ell) * frequency)) =
      -1 := by
  have hFull :
      (∑ shiftIndex : Fin ell,
          ZMod.stdAddChar
            ((shiftIndex.val : ZMod ell) * frequency)) = 0 := by
    calc
      _ = ∑ u : ZMod ell,
          ZMod.stdAddChar (u * frequency) := by
        exact Fintype.sum_equiv
          (ZMod.finEquiv ell)
          _ _ (fun i => by
            exact congrArg
              (fun u : ZMod ell =>
                ZMod.stdAddChar (u * frequency))
              (finEquiv_apply_eq_natCast i).symm)
      _ = ∑ u : ZMod ell,
          ZMod.stdAddChar (frequency * u) := by
        apply Finset.sum_congr rfl
        intro u _hu
        rw [mul_comm]
      _ = 0 :=
        AddChar.sum_eq_zero_of_ne_one
          (ZMod.isPrimitive_stdAddChar ell hfrequency)
  have hSplit :
      1 +
          (∑ shiftIndex : Fin (ell - 1),
            ZMod.stdAddChar
              (((shiftIndex.val + 1 : Nat) : ZMod ell) * frequency)) =
        0 := by
    calc
      _ =
          ZMod.stdAddChar (((0 : Nat) : ZMod ell) * frequency) +
            (∑ shiftIndex : Fin (ell - 1),
              ZMod.stdAddChar
                (((shiftIndex.val + 1 : Nat) : ZMod ell) * frequency)) := by
        simp
      _ =
          ∑ shiftIndex : Fin ((ell - 1) + 1),
            ZMod.stdAddChar
              ((shiftIndex.val : ZMod ell) * frequency) := by
        rw [Fin.sum_univ_succ]
        rfl
      _ = 0 := by
        have hPositive : 0 < ell - 1 := NeZero.pos (ell - 1)
        have hSize : (ell - 1) + 1 = ell := by omega
        calc
          _ =
              ∑ shiftIndex : Fin ell,
                ZMod.stdAddChar
                  ((shiftIndex.val : ZMod ell) * frequency) := by
            exact Fintype.sum_equiv
              (finCongr hSize) _ _ (fun i => by
                simp only [finCongr_apply_coe])
          _ = 0 := hFull
  exact eq_neg_of_add_eq_zero_right hSplit

/-- Exact sum of the real undirected contributions over all nonzero shifts. -/
theorem sum_typeCharacterValue
    {ell : Nat}
    [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell)
    (hfrequency : frequency ≠ 0) :
    (∑ shiftIndex : Fin (ell - 1),
        typeCharacterValue frequency shiftIndex) = -2 := by
  have h :
      (∑ shiftIndex : Fin (ell - 1),
          (ZMod.stdAddChar
            (((shiftIndex.val + 1 : Nat) : ZMod ell) * frequency)).re) =
        -1 := by
    calc
      _ = Complex.reCLM
          (∑ shiftIndex : Fin (ell - 1),
            ZMod.stdAddChar
              (((shiftIndex.val + 1 : Nat) : ZMod ell) * frequency)) := by
        rw [map_sum]
        rfl
      _ = Complex.reCLM (-1) := by
        rw [sum_nonzero_stdAddChar frequency hfrequency]
      _ = -1 := by norm_num
  calc
    (∑ shiftIndex : Fin (ell - 1),
        typeCharacterValue frequency shiftIndex) =
        2 * ∑ shiftIndex : Fin (ell - 1),
          (ZMod.stdAddChar
            (((shiftIndex.val + 1 : Nat) : ZMod ell) * frequency)).re := by
      simp only [typeCharacterValue, Finset.mul_sum]
    _ = 2 * (-1) := by rw [h]
    _ = -2 := by norm_num

/-- The exact mean of one uniform nonzero-shift contribution. -/
theorem integral_typeCharacterValue_uniform
    {ell : Nat}
    [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell)
    (hfrequency : frequency ≠ 0) :
    ∫ shiftIndex,
        typeCharacterValue frequency shiftIndex
      ∂(PMF.uniformOfFintype (Fin (ell - 1))).toMeasure =
      -2 / (ell - 1 : Real) := by
  rw [PMF.integral_eq_sum]
  simp_rw [PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← Finset.smul_sum, sum_typeCharacterValue frequency hfrequency]
  have hPositive : 0 < ell - 1 := NeZero.pos (ell - 1)
  have hOneLe : 1 ≤ ell := by omega
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp only [smul_eq_mul]
  rw [Nat.cast_sub hOneLe]
  ring

/-- Every undirected character contribution lies in the sharp interval
`[-2, 2]`. -/
theorem typeCharacterValue_mem_Icc
    {ell : Nat} [NeZero ell]
    (frequency : ZMod ell)
    (shiftIndex : Fin (ell - 1)) :
    typeCharacterValue frequency shiftIndex ∈ Set.Icc (-2 : Real) 2 := by
  let z :=
    ZMod.stdAddChar
      (((shiftIndex.val + 1 : Nat) : ZMod ell) * frequency)
  have hzNorm : ‖z‖ = (1 : Real) := by
    simp [z]
  have hzAbs : |z.re| ≤ (1 : Real) := by
    simpa [hzNorm] using (Complex.abs_re_le_norm z)
  rw [abs_le] at hzAbs
  constructor <;> simp only [typeCharacterValue] <;> linarith

/-- The sampled type-shift coordinates are mutually independent. -/
theorem distribution_typeTwist_iIndepFun
    (r typeCount ell : Nat)
    [NeZero (ell - 1)] :
    ProbabilityTheory.iIndepFun
      (fun τ (sample : RandomTwist.Sample r typeCount ell) =>
        RandomTwist.typeTwist sample τ)
      (RandomTwist.distribution r typeCount ell).toMeasure := by
  exact
    (RandomBase.independentProduct_iIndepFun
      (RandomTwist.coordinatePMF ell)).precomp
      (g := fun τ : Fin typeCount =>
        (Sum.inr τ :
          RandomTwist.ChoiceIndex r typeCount))
      (by
        intro τ₁ τ₂ h
        simpa using h)

/-- Every sampled type shift has the uniform nonzero-shift law. -/
theorem distribution_typeTwist_hasLaw
    (r typeCount ell : Nat)
    [NeZero (ell - 1)]
    (τ : Fin typeCount) :
    ProbabilityTheory.HasLaw
      (fun sample : RandomTwist.Sample r typeCount ell =>
        RandomTwist.typeTwist sample τ)
      (PMF.uniformOfFintype (Fin (ell - 1))).toMeasure
      (RandomTwist.distribution r typeCount ell).toMeasure := by
  exact
    (RandomBase.independentProduct_coordinate_hasLaw
      (RandomTwist.coordinatePMF ell)
      (Sum.inr τ :
        RandomTwist.ChoiceIndex r typeCount))

/-- The real character contributions remain mutually independent. -/
theorem distribution_sampledTypeCharacter_iIndepFun
    (r typeCount ell : Nat)
    [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell) :
    ProbabilityTheory.iIndepFun
      (fun τ => sampledTypeCharacter frequency τ)
      (RandomTwist.distribution r typeCount ell).toMeasure := by
  exact
    (distribution_typeTwist_iIndepFun r typeCount ell).comp
      (fun _τ shiftIndex =>
        typeCharacterValue frequency shiftIndex)
      (fun _τ => Measurable.of_discrete)

/-- Exact expectation of each sampled character coordinate. -/
theorem integral_sampledTypeCharacter
    (r typeCount ell : Nat)
    [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell)
    (hfrequency : frequency ≠ 0)
    (τ : Fin typeCount) :
    ∫ sample,
        sampledTypeCharacter frequency τ sample
      ∂(RandomTwist.distribution r typeCount ell).toMeasure =
      -2 / (ell - 1 : Real) := by
  calc
    _ =
        ∫ shiftIndex,
          typeCharacterValue frequency shiftIndex
        ∂(PMF.uniformOfFintype (Fin (ell - 1))).toMeasure := by
      exact
        (distribution_typeTwist_hasLaw r typeCount ell τ).integral_comp
          ((Measurable.of_discrete :
            Measurable (typeCharacterValue frequency)).aestronglyMeasurable)
    _ = -2 / (ell - 1 : Real) :=
      integral_typeCharacterValue_uniform frequency hfrequency

/-- Each centered sampled character coordinate is sub-Gaussian with
Hoeffding parameter `4`. -/
theorem centeredSampledTypeCharacter_hasSubgaussianMGF
    (r typeCount ell : Nat)
    [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell)
    (hfrequency : frequency ≠ 0)
    (τ : Fin typeCount) :
    ProbabilityTheory.HasSubgaussianMGF
      (centeredSampledTypeCharacter frequency τ)
      (4 : NNReal)
      (RandomTwist.distribution r typeCount ell).toMeasure := by
  have h :=
    ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
      (μ := (RandomTwist.distribution r typeCount ell).toMeasure)
      (X := sampledTypeCharacter frequency τ)
      (a := (-2 : Real))
      (b := (2 : Real))
      ((Measurable.of_discrete :
        Measurable (sampledTypeCharacter frequency τ)).aemeasurable)
      (Filter.Eventually.of_forall fun sample =>
        typeCharacterValue_mem_Icc frequency
          (RandomTwist.typeTwist sample τ))
  convert h using 1
  · funext sample
    simp only [centeredSampledTypeCharacter]
    rw [integral_sampledTypeCharacter
      r typeCount ell frequency hfrequency τ]
  · norm_num

/-- Centering by the exact deterministic mean preserves mutual
independence. -/
theorem distribution_centeredSampledTypeCharacter_iIndepFun
    (r typeCount ell : Nat)
    [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell) :
    ProbabilityTheory.iIndepFun
      (fun τ => centeredSampledTypeCharacter frequency τ)
      (RandomTwist.distribution r typeCount ell).toMeasure := by
  exact
    (distribution_sampledTypeCharacter_iIndepFun
      r typeCount ell frequency).comp
      (fun _τ x => x - (-2 / (ell - 1 : Real)))
      (fun _τ => by fun_prop)

/-- One-sided Hoeffding bound for the centered multiplier at a fixed
nonzero frequency. -/
theorem measure_centeredCharacterSum_ge_le
    (r typeCount ell : Nat)
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell)
    (hfrequency : frequency ≠ 0) :
    (RandomTwist.distribution r typeCount ell).toMeasure.real
        {sample |
          (typeCount : Real) / 50000 ≤
            centeredCharacterSum frequency sample} ≤
      Real.exp (-(typeCount : Real) / 20000000000) := by
  have hRaw :=
    ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (s := Finset.univ)
      (c := fun _τ : Fin typeCount => (4 : NNReal))
      (distribution_centeredSampledTypeCharacter_iIndepFun
        r typeCount ell frequency)
      (fun τ _hτ =>
        centeredSampledTypeCharacter_hasSubgaussianMGF
          r typeCount ell frequency hfrequency τ)
      (show (0 : Real) ≤ (typeCount : Real) / 50000 by positivity)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hRaw
  convert hRaw using 1
  congr 1
  have hTypeCount : (typeCount : Real) ≠ 0 := by
    exact_mod_cast (NeZero.ne typeCount)
  field_simp
  norm_num
  field_simp [hTypeCount] <;> ring

/-- Matching lower-tail Hoeffding bound for the centered multiplier at a
fixed nonzero frequency. -/
theorem measure_centeredCharacterSum_le_neg_le
    (r typeCount ell : Nat)
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell)
    (hfrequency : frequency ≠ 0) :
    (RandomTwist.distribution r typeCount ell).toMeasure.real
        {sample |
          centeredCharacterSum frequency sample ≤
            -((typeCount : Real) / 50000)} ≤
      Real.exp (-(typeCount : Real) / 20000000000) := by
  have hIndep :
      ProbabilityTheory.iIndepFun
        (fun τ sample =>
          -centeredSampledTypeCharacter frequency τ sample)
        (RandomTwist.distribution r typeCount ell).toMeasure :=
    (distribution_centeredSampledTypeCharacter_iIndepFun
      r typeCount ell frequency).comp
      (fun _τ x => -x) (fun _τ => by fun_prop)
  have hRaw :=
    ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (s := Finset.univ)
      (c := fun _τ : Fin typeCount => (4 : NNReal))
      hIndep
      (fun τ _hτ =>
        (centeredSampledTypeCharacter_hasSubgaussianMGF
          r typeCount ell frequency hfrequency τ).neg)
      (show (0 : Real) ≤ (typeCount : Real) / 50000 by positivity)
  calc
    _ =
        (RandomTwist.distribution r typeCount ell).toMeasure.real
          {sample |
            (typeCount : Real) / 50000 ≤
              ∑ τ : Fin typeCount,
                -centeredSampledTypeCharacter frequency τ sample} := by
      congr 1
      ext sample
      simp only [Set.mem_setOf_eq, centeredCharacterSum,
        Finset.sum_neg_distrib]
      constructor <;> intro h <;> linarith
    _ ≤
        Real.exp
          (-((typeCount : Real) / 50000) ^ 2 /
            (2 * ↑(∑ _τ : Fin typeCount, (4 : NNReal)))) := hRaw
    _ = Real.exp (-(typeCount : Real) / 20000000000) := by
      congr 1
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hTypeCount : (typeCount : Real) ≠ 0 := by
        exact_mod_cast (NeZero.ne typeCount)
      field_simp
      norm_num
      ring

/-- Two-sided fixed-frequency failure probability. -/
theorem measure_centeredFrequencyBad_le
    (r typeCount ell : Nat)
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell)
    (hfrequency : frequency ≠ 0) :
    (RandomTwist.distribution r typeCount ell).toMeasure.real
        {sample | CenteredFrequencyBad frequency sample} ≤
      2 * Real.exp (-(typeCount : Real) / 20000000000) := by
  let μ :=
    (RandomTwist.distribution r typeCount ell).toMeasure
  let upper : Set (RandomTwist.Sample r typeCount ell) :=
    {sample |
      (typeCount : Real) / 50000 ≤
        centeredCharacterSum frequency sample}
  let lower : Set (RandomTwist.Sample r typeCount ell) :=
    {sample |
      centeredCharacterSum frequency sample ≤
        -((typeCount : Real) / 50000)}
  have hSubset :
      {sample | CenteredFrequencyBad frequency sample} ⊆
        upper ∪ lower := by
    intro sample hBad
    change (typeCount : Real) / 50000 <
      |centeredCharacterSum frequency sample| at hBad
    by_cases hNonneg :
        0 ≤ centeredCharacterSum frequency sample
    · left
      change (typeCount : Real) / 50000 ≤
        centeredCharacterSum frequency sample
      rw [abs_of_nonneg hNonneg] at hBad
      exact hBad.le
    · right
      change centeredCharacterSum frequency sample ≤
        -((typeCount : Real) / 50000)
      rw [abs_of_neg (lt_of_not_ge hNonneg)] at hBad
      linarith
  calc
    μ.real {sample | CenteredFrequencyBad frequency sample} ≤
        μ.real (upper ∪ lower) :=
      MeasureTheory.measureReal_mono hSubset
    _ ≤ μ.real upper + μ.real lower :=
      MeasureTheory.measureReal_union_le upper lower
    _ ≤
        Real.exp (-(typeCount : Real) / 20000000000) +
          Real.exp (-(typeCount : Real) / 20000000000) := by
      apply add_le_add
      · exact measure_centeredCharacterSum_ge_le
          r typeCount ell frequency hfrequency
      · exact measure_centeredCharacterSum_le_neg_le
          r typeCount ell frequency hfrequency
    _ = 2 * Real.exp (-(typeCount : Real) / 20000000000) := by
      ring

/-- Union bound over all nonzero Fourier frequencies. -/
theorem measure_centeredSpectrumBad_le
    (r typeCount ell : Nat)
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)] :
    (RandomTwist.distribution r typeCount ell).toMeasure.real
        {sample | CenteredSpectrumBad sample} ≤
      2 * ell *
        Real.exp (-(typeCount : Real) / 20000000000) := by
  let μ :=
    (RandomTwist.distribution r typeCount ell).toMeasure
  let badAt :
      ZMod ell → Set (RandomTwist.Sample r typeCount ell) :=
    fun frequency =>
      if hfrequency : frequency = 0 then ∅
      else {sample | CenteredFrequencyBad frequency sample}
  have hUnion :
      μ.real (⋃ frequency : ZMod ell, badAt frequency) ≤
        ∑ frequency : ZMod ell, μ.real (badAt frequency) :=
    MeasureTheory.measureReal_iUnion_fintype_le badAt
  calc
    μ.real {sample | CenteredSpectrumBad sample} =
        μ.real (⋃ frequency : ZMod ell, badAt frequency) := by
      congr 1
      ext sample
      simp only [CenteredSpectrumBad, Set.mem_setOf_eq, Set.mem_iUnion,
        badAt]
      constructor
      · rintro ⟨frequency, hfrequency, hBad⟩
        refine ⟨frequency, ?_⟩
        simp [hfrequency, hBad]
      · rintro ⟨frequency, hBad⟩
        by_cases hfrequency : frequency = 0
        · simp [hfrequency] at hBad
        · exact ⟨frequency, hfrequency, by simpa [hfrequency] using hBad⟩
    _ ≤ ∑ frequency : ZMod ell, μ.real (badAt frequency) :=
      hUnion
    _ ≤
        ∑ _frequency : ZMod ell,
          2 * Real.exp (-(typeCount : Real) / 20000000000) := by
      apply Finset.sum_le_sum
      intro frequency _hfrequency
      by_cases hzero : frequency = 0
      · simp [badAt, hzero]
        positivity
      · simpa [badAt, hzero, μ] using
          measure_centeredFrequencyBad_le
            r typeCount ell frequency hzero
    _ = 2 * ell *
        Real.exp (-(typeCount : Real) / 20000000000) := by
      simp only [Finset.sum_const, Finset.card_univ,
        ZMod.card, nsmul_eq_mul]
      ring

/-- The HHO20 logarithmic number of sampled types makes the simultaneous
Fourier failure probability strictly smaller than one. -/
theorem two_mul_ell_mul_exp_neg_typeCount_lt_one
    (typeCount ell : Nat)
    (hEll : 100001 ≤ ell)
    (hTypeCount :
      (40000000000 : Real) * Real.log (ell : Real) ≤
        (typeCount : Real)) :
    2 * ell *
        Real.exp (-(typeCount : Real) / 20000000000) <
      1 := by
  have hEllPos : (0 : Real) < ell := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 100001) hEll)
  have hExponent :
      -(typeCount : Real) / 20000000000 ≤
        -2 * Real.log (ell : Real) := by
    linarith
  calc
    2 * ell *
        Real.exp (-(typeCount : Real) / 20000000000) ≤
        2 * ell * Real.exp (-2 * Real.log (ell : Real)) := by
      gcongr
    _ = 2 / (ell : Real) := by
      rw [show -2 * Real.log (ell : Real) =
          -(Real.log (ell : Real) + Real.log (ell : Real)) by ring,
        Real.exp_neg, Real.exp_add, Real.exp_log hEllPos]
      field_simp [hEllPos.ne']
    _ < 1 := by
      rw [div_lt_one hEllPos]
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 2 < 100001) hEll)

/-- The complex Cayley multiplier is the real sum of the sampled
undirected character contributions. -/
theorem cayleyMultiplier_eq_ofReal_sum_sampledTypeCharacter
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (frequency : ZMod ell) :
    cayleyMultiplier sample frequency =
      ((∑ τ : Fin typeCount,
        sampledTypeCharacter frequency τ sample : Real) : Complex) := by
  calc
    cayleyMultiplier sample frequency =
        ∑ τ : Fin typeCount,
          ((sampledTypeCharacter frequency τ sample : Real) :
            Complex) := by
      rw [cayleyMultiplier]
      apply Finset.sum_congr rfl
      intro τ _hτ
      rw [AddChar.map_neg_eq_conj, Complex.add_conj]
      simp only [sampledTypeCharacter, typeCharacterValue, step]
    _ =
        ((∑ τ : Fin typeCount,
          sampledTypeCharacter frequency τ sample : Real) :
          Complex) := by
      rw [Complex.ofReal_sum]

/-- Removing the exact mean expresses the raw character sum as the
centered sum minus its deterministic bias. -/
theorem sum_sampledTypeCharacter_eq_centeredCharacterSum_sub
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (frequency : ZMod ell) :
    (∑ τ : Fin typeCount,
        sampledTypeCharacter frequency τ sample) =
      centeredCharacterSum frequency sample -
        2 * typeCount / (ell - 1 : Real) := by
  simp only [centeredCharacterSum, centeredSampledTypeCharacter,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- A simultaneous centered bound at every nonzero frequency implies the
exact Fourier-spectrum event required by the deterministic mixing proof. -/
theorem hasHHO20CayleySpectrum_of_forall_not_centeredFrequencyBad
    {r typeCount ell : Nat}
    [NeZero ell] [NeZero (ell - 1)]
    (sample : RandomTwist.Sample r typeCount ell)
    (hEll : 100001 ≤ ell)
    (hGood :
      ∀ frequency : ZMod ell, frequency ≠ 0 →
        ¬ CenteredFrequencyBad frequency sample) :
    HasHHO20CayleySpectrum sample := by
  intro frequency hfrequency
  have hCentered :
      |centeredCharacterSum frequency sample| ≤
        (typeCount : Real) / 50000 := by
    exact le_of_not_gt (hGood frequency hfrequency)
  have hEllReal : (100001 : Real) ≤ ell := by
    exact_mod_cast hEll
  have hDen : (100000 : Real) ≤ (ell : Real) - 1 := by
    linarith
  have hDenPos : (0 : Real) < (ell : Real) - 1 :=
    lt_of_lt_of_le (by norm_num) hDen
  have hBiasNonneg :
      (0 : Real) ≤ 2 * typeCount / (ell - 1 : Real) := by
    exact div_nonneg (by positivity) hDenPos.le
  have hBias :
      (2 : Real) * typeCount / (ell - 1 : Real) ≤
        (typeCount : Real) / 50000 := by
    calc
      (2 : Real) * typeCount / (ell - 1 : Real) ≤
          (2 : Real) * typeCount / 100000 := by
        gcongr
      _ = (typeCount : Real) / 50000 := by ring
  have hRaw :
      |∑ τ : Fin typeCount,
          sampledTypeCharacter frequency τ sample| ≤
        2 * typeCount / 50000 := by
    calc
      |∑ τ : Fin typeCount,
          sampledTypeCharacter frequency τ sample| =
          |centeredCharacterSum frequency sample -
            2 * typeCount / (ell - 1 : Real)| := by
        rw [sum_sampledTypeCharacter_eq_centeredCharacterSum_sub]
      _ ≤
          |centeredCharacterSum frequency sample| +
            |2 * typeCount / (ell - 1 : Real)| :=
        abs_sub _ _
      _ =
          |centeredCharacterSum frequency sample| +
            2 * typeCount / (ell - 1 : Real) := by
        rw [abs_of_nonneg hBiasNonneg]
      _ ≤
          (typeCount : Real) / 50000 +
            (typeCount : Real) / 50000 :=
        add_le_add hCentered hBias
      _ = 2 * typeCount / 50000 := by ring
  rw [cayleyMultiplier_eq_ofReal_sum_sampledTypeCharacter,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    (50000 : Real) *
        |∑ τ : Fin typeCount,
          sampledTypeCharacter frequency τ sample| ≤
        50000 * (2 * typeCount / 50000) :=
      mul_le_mul_of_nonneg_left hRaw (by norm_num)
    _ = 2 * typeCount := by ring

/-- The random nonzero shifts contain a deterministic sample satisfying the
complete HHO20 Cayley-spectrum event.  No spectral certificate is supplied
by the caller. -/
theorem exists_twistSample_hasHHO20CayleySpectrum
    (r typeCount ell : Nat)
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (hEll : 100001 ≤ ell)
    (hTypeCount :
      (40000000000 : Real) * Real.log (ell : Real) ≤
        (typeCount : Real)) :
    ∃ sample : RandomTwist.Sample r typeCount ell,
      HasHHO20CayleySpectrum sample := by
  let μ :=
    (RandomTwist.distribution r typeCount ell).toMeasure
  have hBadLt :
      μ.real {sample | CenteredSpectrumBad sample} < 1 :=
    lt_of_le_of_lt
      (measure_centeredSpectrumBad_le r typeCount ell)
      (two_mul_ell_mul_exp_neg_typeCount_lt_one
        typeCount ell hEll hTypeCount)
  have hExistsGood :
      ∃ sample : RandomTwist.Sample r typeCount ell,
        ¬ CenteredSpectrumBad sample := by
    by_contra hNoGood
    push Not at hNoGood
    have hBadUniv :
        {sample : RandomTwist.Sample r typeCount ell |
          CenteredSpectrumBad sample} = Set.univ :=
      Set.eq_univ_of_forall hNoGood
    have hMeasureOne :
        μ.real {sample | CenteredSpectrumBad sample} = 1 := by
      rw [hBadUniv]
      simp [μ]
    linarith
  obtain ⟨sample, hGood⟩ := hExistsGood
  refine ⟨sample,
    hasHHO20CayleySpectrum_of_forall_not_centeredFrequencyBad
      sample hEll ?_⟩
  intro frequency hfrequency hBad
  exact hGood ⟨frequency, hfrequency, hBad⟩

end QEC.Coding.FiberBundle.TwistGraph
