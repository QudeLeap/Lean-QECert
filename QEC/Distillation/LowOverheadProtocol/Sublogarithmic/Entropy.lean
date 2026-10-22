import QEC.Distillation.LowOverheadProtocol.Sublogarithmic.BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open scoped BigOperators

/-!
# HH18 sublogarithmic entropy

This module contains the canonical real Gamma infimum and the exact rational
p0 certificate.  It has no physical protocol, selector, or terminal theorem.
-/

namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy

open Filter Topology

noncomputable section

/-- The real source interval for the HH18 asymptotic parameter. -/
def hh18ParameterInterval : Set ℝ := Set.Ioo (1 / 6 : ℝ) (1 / 3 : ℝ)

/-- Binary entropy measured in bits. -/
noncomputable def hh18BinaryEntropy (p : ℝ) : ℝ :=
  Real.binEntropy p / Real.log 2

/-- The source limiting exponent at a real parameter. -/
noncomputable def hh18Gamma (p : ℝ) : ℝ :=
  3 * (1 - hh18BinaryEntropy p) / hh18BinaryEntropy (3 * p)

/-- The real image whose infimum is the HH18 source exponent. -/
noncomputable def hh18GammaSet : Set ℝ := hh18Gamma '' hh18ParameterInterval

/-- The source infimum over all real interval parameters. -/
noncomputable def hh18GammaInf : ℝ := sInf hh18GammaSet

theorem hh18GammaInf_eq_sInf : hh18GammaInf = sInf hh18GammaSet := rfl

private theorem hh18BinaryEntropy_pos_of_mem_parameterInterval {p : ℝ}
    (hp : p ∈ hh18ParameterInterval) : 0 < hh18BinaryEntropy p := by
  rw [hh18BinaryEntropy]
  apply div_pos
  · apply Real.binEntropy_pos <;> simp only [hh18ParameterInterval] at hp
    · linarith [hp.1]
    · linarith [hp.2]
  · exact Real.log_pos one_lt_two

private theorem hh18BinaryEntropy_three_mul_pos_of_mem_parameterInterval
    {p : ℝ} (hp : p ∈ hh18ParameterInterval) :
    0 < hh18BinaryEntropy (3 * p) := by
  rw [hh18BinaryEntropy]
  apply div_pos
  · apply Real.binEntropy_pos
    · simp only [hh18ParameterInterval] at hp
      linarith [hp.1]
    · simp only [hh18ParameterInterval] at hp
      linarith [hp.2]
  · exact Real.log_pos one_lt_two

private theorem hh18BinaryEntropy_lt_one_of_mem_parameterInterval {p : ℝ}
    (hp : p ∈ hh18ParameterInterval) : hh18BinaryEntropy p < 1 := by
  rw [hh18BinaryEntropy]
  apply (div_lt_iff₀ (Real.log_pos one_lt_two)).mpr
  rw [one_mul]
  apply Real.binEntropy_lt_log_two.mpr
  intro hp_half
  simp only [hh18ParameterInterval] at hp
  rw [hp_half] at hp
  norm_num at hp

private theorem hh18Gamma_pos_of_mem_parameterInterval {p : ℝ}
    (hp : p ∈ hh18ParameterInterval) : 0 < hh18Gamma p := by
  unfold hh18Gamma
  apply div_pos
  · apply mul_pos
    · norm_num
    · exact sub_pos.mpr (hh18BinaryEntropy_lt_one_of_mem_parameterInterval hp)
  · exact hh18BinaryEntropy_three_mul_pos_of_mem_parameterInterval hp

theorem continuousAt_hh18Gamma_of_mem_parameterInterval {p : ℝ}
    (hp : p ∈ hh18ParameterInterval) : ContinuousAt hh18Gamma p := by
  have hlog_ne : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hentropy : ContinuousAt hh18BinaryEntropy p := by
    unfold hh18BinaryEntropy
    exact Real.binEntropy_continuous.continuousAt.div continuousAt_const hlog_ne
  have hentropy_at_three : ContinuousAt hh18BinaryEntropy (3 * p) := by
    unfold hh18BinaryEntropy
    exact Real.binEntropy_continuous.continuousAt.div continuousAt_const hlog_ne
  have hentropy_three : ContinuousAt (fun x : ℝ => hh18BinaryEntropy (3 * x)) p :=
    hentropy_at_three.comp' (continuousAt_const.mul continuousAt_id)
  unfold hh18Gamma
  exact (continuousAt_const.mul (continuousAt_const.sub hentropy)).div
    hentropy_three
    (hh18BinaryEntropy_three_mul_pos_of_mem_parameterInterval hp).ne'

theorem hh18GammaSet_nonempty : hh18GammaSet.Nonempty := by
  refine ⟨hh18Gamma (1 / 4 : ℝ), ?_⟩
  refine ⟨(1 / 4 : ℝ), ?_, rfl⟩
  norm_num [hh18GammaSet, hh18ParameterInterval]

theorem hh18GammaSet_bddBelow : BddBelow hh18GammaSet := by
  refine ⟨0, ?_⟩
  intro y hy
  rcases (show y ∈ hh18Gamma '' hh18ParameterInterval by
    simpa only [hh18GammaSet] using hy) with ⟨p, hp, rfl⟩
  exact (hh18Gamma_pos_of_mem_parameterInterval hp).le

theorem exists_rat_mem_parameterInterval_hh18Gamma_lt (delta : ℝ)
    (hdelta : 0 < delta) :
    ∃ q : ℚ, ((q : ℝ) ∈ hh18ParameterInterval) ∧
      hh18Gamma (q : ℝ) < hh18GammaInf + delta := by
  have hlt : hh18GammaInf < hh18GammaInf + delta := by linarith
  have hlt' : sInf hh18GammaSet < hh18GammaInf + delta := by
    simpa only [hh18GammaInf] using hlt
  rcases (csInf_lt_iff hh18GammaSet_bddBelow hh18GammaSet_nonempty).mp hlt' with
    ⟨y, hy, hylt⟩
  rcases (show y ∈ hh18Gamma '' hh18ParameterInterval by
    simpa only [hh18GammaSet] using hy) with ⟨x, hx, rfl⟩
  have htarget : hh18Gamma ⁻¹' Set.Iio (hh18GammaInf + delta) ∈ 𝓝 x :=
    (continuousAt_hh18Gamma_of_mem_parameterInterval hx).tendsto
      (IsOpen.mem_nhds isOpen_Iio hylt)
  have hinter :
      (hh18Gamma ⁻¹' Set.Iio (hh18GammaInf + delta) ∩ hh18ParameterInterval) ∈
        𝓝 x := Filter.inter_mem htarget (Ioo_mem_nhds hx.1 hx.2)
  rcases Metric.mem_nhds_iff.mp hinter with ⟨radius, hradius, hball⟩
  rcases exists_rat_btwn
      (show x - radius / 2 < x + radius / 2 by linarith) with
    ⟨q, hleft, hright⟩
  have hqball : (q : ℝ) ∈ Metric.ball x radius := by
    rw [Metric.mem_ball, Real.dist_eq]
    have hqhalf : |(q : ℝ) - x| < radius / 2 := by
      refine abs_lt.mpr ?_
      constructor <;> linarith
    linarith
  exact ⟨q, (hball hqball).2, (hball hqball).1⟩

/-! ## Exact p0 certificate

The remaining declarations materialize the positive log-one-add certificate
at the fixed rational source point.  They are placed in this namespace, not a
draft namespace, so the final strict inequality below is a direct witness for
the canonical infimum.
-/

def p0Q : ℚ := HH18ParameterSequence.p0
def p0R : ℝ := (p0Q : ℝ)
def p0q : ℝ := 1 - p0R
def p0u : ℝ := 3 * p0R
def p0v : ℝ := 1 - p0u

theorem p0_interval : (1 / 6 : ℝ) < p0R ∧ p0R < 1 / 3 := by
  norm_num [p0R, p0Q, HH18ParameterSequence.p0]

theorem p0_mem_parameterInterval : p0R ∈ hh18ParameterInterval := by
  exact p0_interval

theorem p0_complements :
    p0q = 729371 / 1000000 ∧
      p0u = 811887 / 1000000 ∧
      p0v = 188113 / 1000000 ∧
      0 < p0u ∧ p0u < 1 ∧ 0 < p0v ∧ p0v < 1 := by
  norm_num [p0R, p0Q, p0q, p0u, p0v, HH18ParameterSequence.p0]

def logOneAddTerm (a : ℝ) (k : Nat) : ℝ :=
  (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * (a / (a + 2)) ^ (2 * k + 1)
def logOneAddPartial (a : ℝ) (N : Nat) : ℝ :=
  ∑ k ∈ Finset.range N, logOneAddTerm a k
def logOneAddRemainder (y : ℝ) (N : Nat) : ℝ :=
  2 * y ^ (2 * N + 1) / ((2 * N + 1) * (1 - y ^ 2))

theorem logOneAdd_partial_le {a : ℝ} (ha : 0 ≤ a) (N : Nat) :
    logOneAddPartial a N ≤ Real.log (1 + a) := by
  have hs : HasSum (logOneAddTerm a) (Real.log (1 + a)) := by
    exact Real.hasSum_log_one_add ha
  simpa only [logOneAddPartial] using sum_le_hasSum (Finset.range N) (by
    intro k hk
    dsimp [logOneAddTerm]
    positivity) hs

theorem logOneAdd_le_partial_add_remainder {a : ℝ} (ha : 0 ≤ a) (N : Nat) :
    Real.log (1 + a) ≤ logOneAddPartial a N +
      logOneAddRemainder (a / (a + 2)) N := by
  let y : ℝ := a / (a + 2)
  let f : Nat → ℝ := logOneAddTerm a
  have ha2 : 0 < a + 2 := by linarith
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact div_nonneg ha ha2.le
  have hy1 : y < 1 := by
    dsimp [y]
    exact (div_lt_one₀ ha2).mpr (by linarith)
  have hy2 : y ^ 2 < 1 := by
    have hsq : y ^ 2 ≤ y := by
      rw [pow_two]
      nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1.le)]
    exact hsq.trans_lt hy1
  have hs : HasSum f (Real.log (1 + a)) := by
    exact Real.hasSum_log_one_add ha
  have hshift : Summable (fun k : Nat => f (k + N)) := by
    exact hs.summable.comp_injective (add_left_injective N)
  let C : ℝ := 2 * y ^ (2 * N + 1) / (2 * N + 1)
  have htail : ∀ k : Nat, f (k + N) ≤ C * (y ^ 2) ^ k := by
    intro k
    have hindex : 2 * (k + N) + 1 = (2 * N + 1) + 2 * k := by omega
    have hden : (0 : ℝ) < (2 * N + 1 : Nat) := by
      exact_mod_cast (Nat.succ_pos (2 * N))
    have hle : ((2 * N + 1 : Nat) : ℝ) ≤ ((2 * (k + N) + 1 : Nat) : ℝ) := by
      exact_mod_cast (show 2 * N + 1 ≤ 2 * (k + N) + 1 by omega)
    have hnum : 0 ≤ 2 * y ^ (2 * N + 1) * (y ^ 2) ^ k := by positivity
    calc
      f (k + N) = (2 * y ^ (2 * N + 1) * (y ^ 2) ^ k) /
          ((2 * (k + N) + 1 : Nat) : ℝ) := by
        dsimp [f, logOneAddTerm, y]
        have hcast :
            2 * ((k + N : Nat) : ℝ) + 1 = ((2 * (k + N) + 1 : Nat) : ℝ) := by
          norm_num [Nat.cast_add, Nat.cast_mul]
        rw [hcast, hindex, pow_add, pow_mul]
        ring
      _ ≤ (2 * y ^ (2 * N + 1) * (y ^ 2) ^ k) /
          ((2 * N + 1 : Nat) : ℝ) :=
        div_le_div_of_nonneg_left hnum hden hle
      _ = C * (y ^ 2) ^ k := by
        dsimp [C]
        field_simp
        push_cast
        ring
  have hgeom : Summable (fun k : Nat => C * (y ^ 2) ^ k) :=
    (summable_geometric_of_lt_one (sq_nonneg y) hy2).mul_left C
  have htailSum := hshift.tsum_le_tsum htail hgeom
  have hgeomEval : ∑' k : Nat, C * (y ^ 2) ^ k = logOneAddRemainder y N := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg y) hy2]
    dsimp [C, logOneAddRemainder]
    field_simp
  calc
    Real.log (1 + a) = ∑' k : Nat, f k := hs.tsum_eq.symm
    _ = logOneAddPartial a N + ∑' k : Nat, f (k + N) := by
      simpa [logOneAddPartial, f] using (hs.summable.sum_add_tsum_nat_add N).symm
    _ ≤ logOneAddPartial a N + ∑' k : Nat, C * (y ^ 2) ^ k :=
      add_le_add_right htailSum _
    _ = _ := by rw [hgeomEval]

/-! ## The fourteen finite rational terms -/

def s1 (y : ℝ) : ℝ := 2 * y
def s3 (y : ℝ) : ℝ := 2 * y + 2 * y ^ 3 / 3 + 2 * y ^ 5 / 5
def s4 (y : ℝ) : ℝ := s3 y + 2 * y ^ 7 / 7

/-- The one-term truncation, with the `Finset.range 1` index made explicit. -/
theorem logOneAddPartial_one_eq_s1 (a : ℝ) :
    logOneAddPartial a 1 = s1 (a / (a + 2)) := by
  norm_num [logOneAddPartial, logOneAddTerm, Finset.sum_range_succ, s1]

/-- The three-term truncation uses exactly the odd indices `0, 1, 2`. -/
theorem logOneAddPartial_three_eq_s3 (a : ℝ) :
    logOneAddPartial a 3 = s3 (a / (a + 2)) := by
  norm_num [logOneAddPartial, logOneAddTerm, Finset.sum_range_succ, s3]
  ring

/-- The four-term truncation uses exactly the odd indices `0, 1, 2, 3`. -/
theorem logOneAddPartial_four_eq_s4 (a : ℝ) :
    logOneAddPartial a 4 = s4 (a / (a + 2)) := by
  norm_num [logOneAddPartial, logOneAddTerm, Finset.sum_range_succ, s3, s4]
  ring

def y2 : ℝ := 1 / 3
def yA : ℝ := 20629 / 520629
def yB : ℝ := 270629 / 1729371
def yC : ℝ := 188113 / 1811887
def yD : ℝ := 61887 / 438113

def aA : ℝ := 82516 / 1000000
def aB : ℝ := p0R / p0q
def aC : ℝ := p0v / p0u
def aD : ℝ := (1 - 4 * p0v) / (4 * p0v)

def log2Upper : ℝ := s4 y2 + 1 / 78732
def logAUpper : ℝ := s1 yA + 1 / 23400
def logBLower : ℝ := s3 yB
def logCLower : ℝ := s3 yC
def logDLower : ℝ := s3 yD

theorem p0_series_parameters :
    (1 : ℝ) / (1 + 2) = y2 ∧
      aA / (aA + 2) = yA ∧
      aB / (aB + 2) = yB ∧
      aC / (aC + 2) = yC ∧
      aD / (aD + 2) = yD := by
  norm_num [p0R, p0Q, p0q, p0u, p0v, aA, aB, aC, aD,
    y2, yA, yB, yC, yD, HH18ParameterSequence.p0]

theorem p0_series_range_facts :
    0 ≤ yA ∧ yA ≤ 1 / 25 ∧
      0 ≤ yB ∧ yB < 1 ∧
      0 ≤ yC ∧ yC < 1 ∧
      0 ≤ yD ∧ yD < 1 := by
  norm_num [yA, yB, yC, yD]

/-- Exact geometric remainder for the four log-two terms (`N = 4`). -/
theorem p0_log2_remainder_exact :
    logOneAddRemainder (1 / 3 : ℝ) 4 = 1 / 78732 := by
  norm_num [logOneAddRemainder]

/-- Rational majorant used for the one A-term remainder. -/
theorem p0_logA_remainder_majorant_exact :
    logOneAddRemainder (1 / 25 : ℝ) 1 = 1 / 23400 := by
  norm_num [logOneAddRemainder]

/-- The exact A-series parameter is below the rational majorant at `N = 1`. -/
theorem p0_logA_remainder_bound :
    logOneAddRemainder (aA / (aA + 2)) 1 ≤ 1 / 23400 := by
  norm_num [aA, yA, logOneAddRemainder]

/-! The four logarithms are written both in their entropy form and in the
positive `log (1+a)` form consumed by the series helper. -/

def p0A : ℝ := Real.log (4 * p0R)
def p0B : ℝ := Real.log (1 / p0q)
def p0C : ℝ := Real.log (1 / p0u)
def p0D : ℝ := Real.log (1 / (4 * p0v))

theorem p0_range_reductions :
    p0A = Real.log (1 + aA) ∧
      p0B = Real.log (1 + aB) ∧
      p0C = Real.log (1 + aC) ∧
      p0D = Real.log (1 + aD) := by
  constructor
  · norm_num [p0A, p0R, p0Q, aA, HH18ParameterSequence.p0]
  constructor
  · norm_num [p0B, p0R, p0Q, p0q, aB, HH18ParameterSequence.p0]
  constructor
  · norm_num [p0C, p0R, p0Q, p0u, p0v, aC, HH18ParameterSequence.p0]
  · norm_num [p0D, p0R, p0Q, p0u, p0v, aD, HH18ParameterSequence.p0]

theorem p0_log2_upper : Real.log 2 ≤ log2Upper := by
  have h := logOneAdd_le_partial_add_remainder (a := (1 : ℝ)) (N := 4)
    (by norm_num)
  have hratio : (1 : ℝ) / (1 + 2) = y2 := by norm_num [y2]
  calc
    Real.log 2 = Real.log (1 + (1 : ℝ)) := by norm_num
    _ ≤ logOneAddPartial (1 : ℝ) 4 +
        logOneAddRemainder ((1 : ℝ) / (1 + 2)) 4 := h
    _ = s4 y2 + 1 / 78732 := by
      rw [logOneAddPartial_four_eq_s4, hratio]
      simpa [y2] using congrArg (fun t : ℝ => s4 y2 + t)
        p0_log2_remainder_exact
    _ = log2Upper := rfl

theorem p0_logA_upper : p0A ≤ logAUpper := by
  have h := logOneAdd_le_partial_add_remainder (a := aA) (N := 1)
    (by norm_num [aA])
  rcases p0_range_reductions with ⟨hA, _, _, _⟩
  rcases p0_series_parameters with ⟨_, hAparam, _, _, _⟩
  have hrem := p0_logA_remainder_bound
  have hrem' : logOneAddRemainder yA 1 ≤ 1 / 23400 := by
    rw [← hAparam]
    exact hrem
  calc
    p0A = Real.log (1 + aA) := hA
    _ ≤ logOneAddPartial aA 1 + logOneAddRemainder (aA / (aA + 2)) 1 := h
    _ = s1 yA + logOneAddRemainder yA 1 := by
      rw [logOneAddPartial_one_eq_s1, hAparam]
    _ ≤ s1 yA + 1 / 23400 := add_le_add_right hrem' _
    _ = logAUpper := rfl

theorem p0_logB_lower : logBLower ≤ p0B := by
  have h := logOneAdd_partial_le (a := aB) (N := 3) (by norm_num [aB, p0R, p0Q,
    p0q, HH18ParameterSequence.p0])
  rcases p0_range_reductions with ⟨_, hB, _, _⟩
  rcases p0_series_parameters with ⟨_, _, hBparam, _, _⟩
  calc
    logBLower = s3 yB := rfl
    _ = s3 (aB / (aB + 2)) := by rw [hBparam]
    _ = logOneAddPartial aB 3 := (logOneAddPartial_three_eq_s3 aB).symm
    _ ≤ Real.log (1 + aB) := h
    _ = p0B := hB.symm

theorem p0_logC_lower : logCLower ≤ p0C := by
  have h := logOneAdd_partial_le (a := aC) (N := 3) (by norm_num [aC, p0R, p0Q,
    p0u, p0v, HH18ParameterSequence.p0])
  rcases p0_range_reductions with ⟨_, _, hC, _⟩
  rcases p0_series_parameters with ⟨_, _, _, hCparam, _⟩
  calc
    logCLower = s3 yC := rfl
    _ = s3 (aC / (aC + 2)) := by rw [hCparam]
    _ = logOneAddPartial aC 3 := (logOneAddPartial_three_eq_s3 aC).symm
    _ ≤ Real.log (1 + aC) := h
    _ = p0C := hC.symm

theorem p0_logD_lower : logDLower ≤ p0D := by
  have h := logOneAdd_partial_le (a := aD) (N := 3) (by norm_num [aD, p0R, p0Q,
    p0u, p0v, HH18ParameterSequence.p0])
  rcases p0_range_reductions with ⟨_, _, _, hD⟩
  rcases p0_series_parameters with ⟨_, _, _, _, hDparam⟩
  calc
    logDLower = s3 yD := rfl
    _ = s3 (aD / (aD + 2)) := by rw [hDparam]
    _ = logOneAddPartial aD 3 := (logOneAddPartial_three_eq_s3 aD).symm
    _ ≤ Real.log (1 + aD) := h
    _ = p0D := hD.symm

/-! ## Exact rational gap: all fourteen terms, no numerical oracle -/

def s1Q (y : ℚ) : ℚ := 2 * y
def s3Q (y : ℚ) : ℚ := 2 * y + 2 * y ^ 3 / 3 + 2 * y ^ 5 / 5
def s4Q (y : ℚ) : ℚ := s3Q y + 2 * y ^ 7 / 7

def y2Q : ℚ := 1 / 3
def yAQ : ℚ := 20629 / 520629
def yBQ : ℚ := 270629 / 1729371
def yCQ : ℚ := 188113 / 1811887
def yDQ : ℚ := 61887 / 438113

/-- Exactly fourteen finite series terms: `1 + 3 + 3 + 3 + 4`. -/
def p0CertifiedGapQ : ℚ :=
    (2188113 / 2000) * s3Q yBQ
  + (275229693 / 1000000) * s3Q yCQ
  + (63770307 / 1000000) * s3Q yDQ
  - (811887 / 2000) * (s1Q yAQ + 1 / 23400)
  - (280286193 / 500000) * (s4Q y2Q + 1 / 78732)

theorem p0CertifiedGapQ_between :
    10869 / 10000000 < p0CertifiedGapQ ∧
      p0CertifiedGapQ < 1087 / 1000000 := by
  norm_num [p0CertifiedGapQ, s1Q, s3Q, s4Q, y2Q, yAQ, yBQ, yCQ, yDQ]

theorem p0CertifiedGapQ_gt_thousandth : (1 / 1000 : ℚ) < p0CertifiedGapQ := by
  norm_num [p0CertifiedGapQ, s1Q, s3Q, s4Q, y2Q, yAQ, yBQ, yCQ, yDQ]

def p0LinearLower : ℝ :=
    (2188113 / 2000) * logBLower
  + (275229693 / 1000000) * logCLower
  + (63770307 / 1000000) * logDLower
  - (811887 / 2000) * logAUpper
  - (280286193 / 500000) * log2Upper

theorem p0LinearLower_eq_gap : p0LinearLower = (p0CertifiedGapQ : ℝ) := by
  norm_num [p0LinearLower, logBLower, logCLower, logDLower, logAUpper,
    log2Upper, s1, s3, s4, y2, yA, yB, yC, yD, p0CertifiedGapQ,
    s1Q, s3Q, s4Q, y2Q, yAQ, yBQ, yCQ, yDQ]

/-! ## Entropy normal form and strict Gamma inequality -/

def p0EntropyGap : ℝ :=
  339 * Real.binEntropy p0u - 1500 * (Real.log 2 - Real.binEntropy p0R)

theorem binEntropy_eq_log_inv_form (x : ℝ) :
    Real.binEntropy x =
      x * Real.log (1 / x) + (1 - x) * Real.log (1 / (1 - x)) := by
  unfold Real.binEntropy
  simp only [one_div, Real.log_inv]

theorem p0_log_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
  calc
    Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
    _ = 2 * Real.log 2 := by
      rw [Real.log_pow]
      norm_num

theorem p0_inverse_log_reductions :
    Real.log (1 / p0R) = 2 * Real.log 2 - p0A ∧
      Real.log (1 / p0q) = p0B ∧
      Real.log (1 / p0u) = p0C ∧
      Real.log (1 / p0v) = 2 * Real.log 2 + p0D := by
  have hp0R_pos : 0 < p0R := (by norm_num : (0 : ℝ) < 1 / 6).trans p0_interval.1
  rcases p0_complements with ⟨_, _, _, _, _, hp0v_pos, _⟩
  constructor
  · calc
      Real.log (1 / p0R) = Real.log (4 / (4 * p0R)) := by
        congr 1
        field_simp [p0R, p0Q, HH18ParameterSequence.p0]
      _ = Real.log 4 - Real.log (4 * p0R) := by
        rw [Real.log_div (by norm_num) (by positivity)]
      _ = 2 * Real.log 2 - p0A := by
        rw [p0_log_four]
        rfl
  constructor
  · rfl
  constructor
  · rfl
  · calc
      Real.log (1 / p0v) = Real.log (4 * (1 / (4 * p0v))) := by
        congr 1
        field_simp [p0R, p0Q, p0u, p0v, HH18ParameterSequence.p0]
      _ = Real.log 4 + Real.log (1 / (4 * p0v)) := by
        rw [Real.log_mul (by norm_num) (by positivity)]
      _ = 2 * Real.log 2 + p0D := by
        rw [p0_log_four]
        rfl

theorem p0_entropy_expansions :
    Real.binEntropy p0R = p0R * (2 * Real.log 2 - p0A) + p0q * p0B ∧
      Real.binEntropy p0u = p0u * p0C + p0v * (2 * Real.log 2 + p0D) := by
  rcases p0_inverse_log_reductions with ⟨hp, hq, hu, hv⟩
  constructor
  · rw [binEntropy_eq_log_inv_form, hp]
    change p0R * (2 * Real.log 2 - p0A) + p0q * Real.log (1 / p0q) =
      p0R * (2 * Real.log 2 - p0A) + p0q * p0B
    rw [hq]
  · rw [binEntropy_eq_log_inv_form, hu]
    change p0u * p0C + p0v * Real.log (1 / p0v) =
      p0u * p0C + p0v * (2 * Real.log 2 + p0D)
    rw [hv]

theorem p0_entropyGap_linear_form :
    p0EntropyGap =
      - (280286193 / 500000 : ℝ) * Real.log 2
      - (811887 / 2000 : ℝ) * p0A
      + (2188113 / 2000 : ℝ) * p0B
      + (275229693 / 1000000 : ℝ) * p0C
      + (63770307 / 1000000 : ℝ) * p0D := by
  rcases p0_entropy_expansions with ⟨hp, hu⟩
  unfold p0EntropyGap
  rw [hp, hu]
  norm_num [p0R, p0Q, p0q, p0u, p0v, HH18ParameterSequence.p0]
  ring

theorem p0_binEntropy_u_pos : 0 < Real.binEntropy p0u := by
  rcases p0_complements with ⟨_, _, _, hu0, hu1, hv0, hv1⟩
  exact Real.binEntropy_pos hu0 hu1

/-- The analytic part has been reduced to the exact fourteen-term rational
certificate, whose gap is strictly larger than `1 / 1000`. -/
theorem p0EntropyGap_gt_thousandth : (1 / 1000 : ℝ) < p0EntropyGap := by
  have hlinear : p0LinearLower ≤ p0EntropyGap := by
    rw [p0_entropyGap_linear_form]
    unfold p0LinearLower
    nlinarith [p0_log2_upper, p0_logA_upper, p0_logB_lower,
      p0_logC_lower, p0_logD_lower]
  calc
    (1 / 1000 : ℝ) < (p0CertifiedGapQ : ℝ) := by
      calc
        (1 / 1000 : ℝ) = ((1 / 1000 : ℚ) : ℝ) := by norm_num [Rat.cast_div]
        _ < (p0CertifiedGapQ : ℝ) := by
          exact_mod_cast p0CertifiedGapQ_gt_thousandth
    _ = p0LinearLower := p0LinearLower_eq_gap.symm
    _ ≤ p0EntropyGap := hlinear

theorem p0EntropyGap_gt_zero : 0 < p0EntropyGap := by
  exact (by norm_num : (0 : ℝ) < 1 / 1000).trans p0EntropyGap_gt_thousandth

/-! ## Canonical p0 upper witness -/

theorem p0Gamma_denominator_pos :
    0 < hh18BinaryEntropy (3 * p0R) := by
  change 0 < Real.binEntropy p0u / Real.log 2
  exact div_pos p0_binEntropy_u_pos (Real.log_pos one_lt_two)

theorem hh18Gamma_p0_lt_339_div_500 :
    hh18Gamma p0R < (339 / 500 : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hHu : 0 < Real.binEntropy p0u := p0_binEntropy_u_pos
  have hden : 0 < Real.binEntropy p0u / Real.log 2 := div_pos hHu hlog2
  change 3 * (1 - Real.binEntropy p0R / Real.log 2) /
      (Real.binEntropy p0u / Real.log 2) < (339 / 500 : ℝ)
  apply (div_lt_iff₀ hden).mpr
  field_simp [hlog2.ne', hHu.ne']
  have hgap := p0EntropyGap_gt_thousandth
  unfold p0EntropyGap at hgap
  nlinarith [hgap]

/-- The exact p0 certificate is a strict upper witness for the real infimum.
It makes no attainment or minimizer claim. -/
theorem hh18GammaInf_lt_339_div_500 :
    hh18GammaInf < (339 / 500 : ℝ) := by
  refine lt_of_le_of_lt ?_ hh18Gamma_p0_lt_339_div_500
  rw [hh18GammaInf]
  exact csInf_le hh18GammaSet_bddBelow ⟨p0R, p0_mem_parameterInterval, rfl⟩

end
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
