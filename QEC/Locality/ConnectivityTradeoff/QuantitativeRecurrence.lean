import QEC.Locality.ConnectivityTradeoff.SumPreservingRecurrence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Quantitative solution of the sum-preserving BK recurrence

This module proves the finite real-power estimate for the admissible-pair
recurrence in `BKSumPreservingRecurrence`.  All constants are explicit; the
results do not use asymptotic notation or store a desired bound in input data.
-/

noncomputable section

namespace QEC.Locality

open Set

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The worst balanced complementary-child `rpow` gap for the `2/3` convention. -/
def bkRpowGap (c : ℝ) : ℝ :=
  (2 / 3 : ℝ) ^ c + (1 / 3 : ℝ) ^ c - 1

/-- The positive entropy slope used to make the near-linear gap quantitative. -/
def bkEntropyGap : ℝ :=
  -((2 / 3 : ℝ) * Real.log (2 / 3 : ℝ) +
      (1 / 3 : ℝ) * Real.log (1 / 3 : ℝ))

/-- The exact coefficient in the BK finite recurrence solution. -/
def bkRpowCoefficient (beta c : ℝ) : ℝ :=
  beta / (bkRpowGap c * (1 / 3 : ℝ) ^ (1 - c))

/-- The sharper induction potential underlying the closed-form estimate. -/
def bkRpowPotential (beta c : ℝ) (d parent : Nat) : ℝ :=
  (beta / bkRpowGap c) * (d : ℝ) ^ c *
    (((parent : ℝ) / d) / (1 / 3 : ℝ) ^ (1 - c) -
      ((parent : ℝ) / d) ^ c)

/--
Every admissible pair can be enlarged, componentwise, to complementary
balanced children.  This is the finite rounding bridge to the source's
`alpha_r` and `1-alpha_r` notation.
-/
theorem exists_saturated_bkAdmissibleChildPair
    {parent : Nat} {children : Nat × Nat} (hparent : 2 ≤ parent)
    (hchildren : children ∈ bkAdmissibleChildPairs parent) :
    ∃ saturated : Nat × Nat,
      children.1 ≤ saturated.1 ∧ children.2 ≤ saturated.2 ∧
      saturated.1 + saturated.2 = parent ∧
      parent ≤ 3 * saturated.1 ∧ parent ≤ 3 * saturated.2 ∧
      3 * saturated.1 ≤ 2 * parent ∧ 3 * saturated.2 ≤ 2 * parent ∧
      saturated.1 < parent ∧ saturated.2 < parent := by
  have h := (mem_bkAdmissibleChildPairs_iff).1 hchildren
  rcases children with ⟨left, right⟩
  simp only at h ⊢
  unfold BKAdmissibleChildPair at h
  by_cases hleft : left ≤ (parent + 2) / 3
  · refine ⟨((parent + 2) / 3, parent - (parent + 2) / 3), ?_⟩
    simp only
    omega
  · refine ⟨(left, parent - left), ?_⟩
    simp only
    omega

/-- Endpoint lower bound for complementary powers on the balanced interval. -/
theorem bkRpowGap_le_complementary_sum_sub_one
    {c t : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (ht : t ∈ Set.Icc (1 / 3 : ℝ) (2 / 3 : ℝ)) :
    bkRpowGap c ≤ t ^ c + (1 - t) ^ c - 1 := by
  let a : ℝ := 2 - 3 * t
  let b : ℝ := 3 * t - 1
  have ha : 0 ≤ a := by dsimp [a]; linarith [ht.2]
  have hb : 0 ≤ b := by dsimp [b]; linarith [ht.1]
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have hba : b + a = 1 := by linarith
  have htCombo : a * (1 / 3 : ℝ) + b * (2 / 3 : ℝ) = t := by
    dsimp [a, b]
    ring
  have hOneSubCombo : b * (1 / 3 : ℝ) + a * (2 / 3 : ℝ) = 1 - t := by
    dsimp [a, b]
    ring
  have hconcave := Real.concaveOn_rpow hc0 hc1
  have htPower := hconcave.2
    (show (1 / 3 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (2 / 3 : ℝ) ∈ Set.Ici 0 by norm_num)
    ha hb hab
  have hOneSubPower := hconcave.2
    (show (1 / 3 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (2 / 3 : ℝ) ∈ Set.Ici 0 by norm_num)
    hb ha hba
  simp only [smul_eq_mul, htCombo] at htPower
  simp only [smul_eq_mul, hOneSubCombo] at hOneSubPower
  unfold bkRpowGap
  nlinarith [htPower, hOneSubPower]

/-- The balanced `rpow` gap is strictly positive for every exponent below one. -/
theorem bkRpowGap_pos {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    0 < bkRpowGap c := by
  rcases hc0.eq_or_lt with rfl | hc0
  · norm_num [bkRpowGap]
  · have hthird : (1 / 3 : ℝ) < (1 / 3 : ℝ) ^ c :=
      Real.self_lt_rpow_of_lt_one (by norm_num) (by norm_num) hc1
    have htwoThirds : (2 / 3 : ℝ) < (2 / 3 : ℝ) ^ c :=
      Real.self_lt_rpow_of_lt_one (by norm_num) (by norm_num) hc1
    unfold bkRpowGap
    linarith

/-- Scaling the complementary-child gap from unit mass to an arbitrary positive parent. -/
theorem bkRpowGap_mul_parent_le_children_gap
    {c parent left right : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hparent : 0 < parent) (hsum : left + right = parent)
    (hleftLower : parent / 3 ≤ left) (hleftUpper : left ≤ 2 * parent / 3) :
    bkRpowGap c * parent ^ c ≤ left ^ c + right ^ c - parent ^ c := by
  let t := left / parent
  have ht : t ∈ Set.Icc (1 / 3 : ℝ) (2 / 3 : ℝ) := by
    constructor
    · dsimp [t]
      apply (le_div_iff₀ hparent).2
      nlinarith [hleftLower]
    · dsimp [t]
      apply (div_le_iff₀ hparent).2
      nlinarith [hleftUpper]
  have hunit := bkRpowGap_le_complementary_sum_sub_one hc0 hc1 ht
  have htNonneg : 0 ≤ t := (show (0 : ℝ) ≤ 1 / 3 by norm_num).trans ht.1
  have htLeOne : t ≤ 1 := ht.2.trans (by norm_num)
  have hOneSubNonneg : 0 ≤ 1 - t := sub_nonneg.mpr htLeOne
  have hleft : left = parent * t := by
    dsimp [t]
    field_simp [hparent.ne']
  have hright : right = parent * (1 - t) := by
    calc
      right = parent - left := by linarith [hsum]
      _ = parent * (1 - t) := by rw [hleft]; ring
  have hparentNonneg : 0 ≤ parent := hparent.le
  have hscaled := mul_le_mul_of_nonneg_right hunit (Real.rpow_nonneg hparentNonneg c)
  rw [hleft, hright, Real.mul_rpow hparentNonneg htNonneg,
    Real.mul_rpow hparentNonneg hOneSubNonneg]
  nlinarith [hscaled]

/-- The entropy slope is positive for the `1/3`--`2/3` split. -/
theorem bkEntropyGap_pos : 0 < bkEntropyGap := by
  have hlogThird : Real.log (1 / 3 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hlogTwoThirds : Real.log (2 / 3 : ℝ) < 0 :=
    Real.log_neg (by norm_num) (by norm_num)
  unfold bkEntropyGap
  nlinarith

/-- Tangent-line lower bound for a fixed-base real power. -/
theorem neg_mul_log_mul_one_sub_le_rpow_sub
    {base c : ℝ} (hbase : 0 < base) :
    -base * Real.log base * (1 - c) ≤ base ^ c - base := by
  have hexp := mul_le_mul_of_nonneg_left
    (Real.add_one_le_exp ((c - 1) * Real.log base)) hbase.le
  have hrpow : base ^ c = base * Real.exp ((c - 1) * Real.log base) := by
    calc
      base ^ c = base ^ (1 + (c - 1)) := by ring_nf
      _ = base ^ (1 : ℝ) * base ^ (c - 1) := Real.rpow_add hbase 1 (c - 1)
      _ = base * Real.exp (Real.log base * (c - 1)) := by
        rw [Real.rpow_one, Real.rpow_def_of_pos hbase]
      _ = base * Real.exp ((c - 1) * Real.log base) := by ring_nf
  rw [← hrpow] at hexp
  nlinarith

/-- The exact gap dominates its first-order entropy lower bound. -/
theorem bkEntropyGap_mul_one_sub_le_bkRpowGap (c : ℝ) :
    bkEntropyGap * (1 - c) ≤ bkRpowGap c := by
  have htwo := neg_mul_log_mul_one_sub_le_rpow_sub
    (c := c) (show (0 : ℝ) < 2 / 3 by norm_num)
  have hone := neg_mul_log_mul_one_sub_le_rpow_sub
    (c := c) (show (0 : ℝ) < 1 / 3 by norm_num)
  unfold bkEntropyGap bkRpowGap
  nlinarith

/-- On `[a,1]`, a sublinear power is bounded by its endpoint-scaled chord. -/
theorem rpow_le_div_endpoint_rpow
    {a q c : ℝ} (ha : 0 < a) (haq : a ≤ q)
    (hc1 : c < 1) :
    q ^ c ≤ q / a ^ (1 - c) := by
  have hq : 0 < q := ha.trans_le haq
  have hp : 0 < 1 - c := sub_pos.mpr hc1
  have hpow : a ^ (1 - c) ≤ q ^ (1 - c) :=
    Real.rpow_le_rpow ha.le haq hp.le
  have haPowPos : 0 < a ^ (1 - c) := Real.rpow_pos_of_pos ha _
  apply (le_div_iff₀ haPowPos).2
  calc
    q ^ c * a ^ (1 - c) ≤ q ^ c * q ^ (1 - c) := by
      exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hq.le c)
    _ = q := by
      rw [← Real.rpow_add hq]
      ring_nf
      exact Real.rpow_one q

theorem beta_div_bkRpowGap_nonneg
    {beta c : ℝ} (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    0 ≤ beta / bkRpowGap c :=
  div_nonneg hbeta (bkRpowGap_pos hc0 hc1).le

theorem bkRpowCoefficient_nonneg
    {beta c : ℝ} (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    0 ≤ bkRpowCoefficient beta c := by
  unfold bkRpowCoefficient
  exact div_nonneg hbeta (mul_nonneg (bkRpowGap_pos hc0 hc1).le
    (Real.rpow_nonneg (by norm_num) _))

/-- A terminal balanced child has nonnegative source potential. -/
theorem bkRpowPotential_nonneg_of_lower_scale
    {beta c : ℝ} {d child : Nat}
    (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hd : 0 < d) (hlower : d ≤ 3 * child) :
    0 ≤ bkRpowPotential beta c d child := by
  have hdReal : (0 : ℝ) < d := by exact_mod_cast hd
  have hratio : (1 / 3 : ℝ) ≤ (child : ℝ) / d := by
    apply (le_div_iff₀ hdReal).2
    have hlowerReal : (d : ℝ) ≤ 3 * child := by exact_mod_cast hlower
    nlinarith
  have hpower := rpow_le_div_endpoint_rpow
    (a := (1 / 3 : ℝ)) (q := (child : ℝ) / d) (c := c)
    (by norm_num) hratio hc1
  unfold bkRpowPotential
  exact mul_nonneg
    (mul_nonneg (beta_div_bkRpowGap_nonneg hbeta hc0 hc1)
      (Real.rpow_nonneg hdReal.le c))
    (sub_nonneg.mpr hpower)

/-- The normalized potential is exactly the source's linear-minus-power expression. -/
theorem bkRpowPotential_eq_source_form
    {beta c : ℝ} {d parent : Nat} (hd : 0 < d) :
    bkRpowPotential beta c d parent =
      bkRpowCoefficient beta c * parent / (d : ℝ) ^ (1 - c) -
        (beta / bkRpowGap c) * (parent : ℝ) ^ c := by
  have hdReal : (0 : ℝ) < d := by exact_mod_cast hd
  have hdPowC : 0 < (d : ℝ) ^ c := Real.rpow_pos_of_pos hdReal _
  have hdPowOneSub : 0 < (d : ℝ) ^ (1 - c) := Real.rpow_pos_of_pos hdReal _
  have hdFactor : (d : ℝ) ^ c * (d : ℝ) ^ (1 - c) = d := by
    rw [← Real.rpow_add hdReal]
    ring_nf
    exact Real.rpow_one d
  have hparentRpow : (d : ℝ) ^ c * ((parent : ℝ) / d) ^ c =
      (parent : ℝ) ^ c := by
    rw [Real.div_rpow (Nat.cast_nonneg parent) hdReal.le]
    field_simp
  have hparentLinear : (d : ℝ) ^ c * ((parent : ℝ) / d) =
      (parent : ℝ) / (d : ℝ) ^ (1 - c) := by
    apply (eq_div_iff hdPowOneSub.ne').2
    calc
      ((d : ℝ) ^ c * ((parent : ℝ) / d)) * (d : ℝ) ^ (1 - c) =
          (parent : ℝ) / d * ((d : ℝ) ^ c * (d : ℝ) ^ (1 - c)) := by ring
      _ = (parent : ℝ) := by rw [hdFactor]; field_simp
  unfold bkRpowPotential bkRpowCoefficient
  rw [mul_sub]
  rw [mul_assoc (beta / bkRpowGap c) ((d : ℝ) ^ c)
    (((parent : ℝ) / d) ^ c), hparentRpow]
  rw [show (beta / bkRpowGap c) * (d : ℝ) ^ c *
      ((parent : ℝ) / d / (1 / 3 : ℝ) ^ (1 - c)) =
      (beta / bkRpowGap c) *
        ((d : ℝ) ^ c * ((parent : ℝ) / d)) /
          (1 / 3 : ℝ) ^ (1 - c) by ring]
  rw [hparentLinear]
  have haPow : (1 / 3 : ℝ) ^ (1 - c) ≠ 0 :=
    (Real.rpow_pos_of_pos (by norm_num) _).ne'
  field_simp [haPow]

/-- One complementary balanced split closes the source potential induction step. -/
theorem add_bkRpowPotential_children_le_parent
    (G : ConnectivityGraph ι)
    {beta c : ℝ} {d parent left right : Nat}
    (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1) (hd : 0 < d)
    (hparent : 0 < parent) (hsum : left + right = parent)
    (hleftLower : parent ≤ 3 * left) (hleftUpper : 3 * left ≤ 2 * parent)
    (hcharge : (twoThirdsSeparationProfile G parent : ℝ) ≤
      beta * (parent : ℝ) ^ c) :
    (twoThirdsSeparationProfile G parent : ℝ) +
        bkRpowPotential beta c d left + bkRpowPotential beta c d right ≤
      bkRpowPotential beta c d parent := by
  have hparentReal : (0 : ℝ) < parent := by exact_mod_cast hparent
  have hsumReal : (left : ℝ) + right = parent := by exact_mod_cast hsum
  have hleftLowerReal : (parent : ℝ) / 3 ≤ left := by
    have h : (parent : ℝ) ≤ 3 * left := by exact_mod_cast hleftLower
    linarith
  have hleftUpperReal : (left : ℝ) ≤ 2 * parent / 3 := by
    have h : 3 * (left : ℝ) ≤ 2 * parent := by exact_mod_cast hleftUpper
    linarith
  have hgap := bkRpowGap_mul_parent_le_children_gap hc0 hc1.le
    hparentReal hsumReal hleftLowerReal hleftUpperReal
  have hfactor : 0 ≤ beta / bkRpowGap c :=
    beta_div_bkRpowGap_nonneg hbeta hc0 hc1
  have hscaled := mul_le_mul_of_nonneg_left hgap hfactor
  have hgapNe : bkRpowGap c ≠ 0 := (bkRpowGap_pos hc0 hc1).ne'
  have hchargeScaled :
      beta * (parent : ℝ) ^ c ≤
        (beta / bkRpowGap c) *
          ((left : ℝ) ^ c + (right : ℝ) ^ c - (parent : ℝ) ^ c) := by
    calc
      beta * (parent : ℝ) ^ c =
          (beta / bkRpowGap c) *
            (bkRpowGap c * (parent : ℝ) ^ c) := by
        field_simp [hgapNe]
      _ ≤ (beta / bkRpowGap c) *
          ((left : ℝ) ^ c + (right : ℝ) ^ c - (parent : ℝ) ^ c) := hscaled
  rw [bkRpowPotential_eq_source_form hd,
    bkRpowPotential_eq_source_form hd,
    bkRpowPotential_eq_source_form hd]
  have hdPowNe : (d : ℝ) ^ (1 - c) ≠ 0 :=
    (Real.rpow_pos_of_pos (by exact_mod_cast hd) _).ne'
  have hlinear :
      bkRpowCoefficient beta c * (left : ℝ) / (d : ℝ) ^ (1 - c) +
          bkRpowCoefficient beta c * (right : ℝ) / (d : ℝ) ^ (1 - c) =
        bkRpowCoefficient beta c * (parent : ℝ) / (d : ℝ) ^ (1 - c) := by
    rw [← add_div, ← mul_add, hsumReal]
  linarith [hchargeScaled]

/--
The source potential bounds the exact finite admissible-pair recurrence.
The profile hypothesis is required only on scales between the terminal
threshold and the chosen root.
-/
theorem bkSumPreservingRecurrence_cast_le_bkRpowPotential
    (G : ConnectivityGraph ι) (d root parent : Nat) (beta c : ℝ)
    (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1) (hd : 2 ≤ d)
    (hparent : d ≤ parent) (hroot : parent ≤ root)
    (hprofile : ∀ scale : Nat, d ≤ scale → scale ≤ root →
      (twoThirdsSeparationProfile G scale : ℝ) ≤ beta * (scale : ℝ) ^ c) :
    (bkSumPreservingRecurrence G d parent : ℝ) ≤
      bkRpowPotential beta c d parent := by
  induction parent using Nat.strong_induction_on with
  | h parent ih =>
      have hdPos : 0 < d := by omega
      have hparentPos : 0 < parent := by omega
      have hnonterminal : ¬bkScaleTerminal d parent := by
        unfold bkScaleTerminal
        omega
      have hpairs : (bkAdmissibleChildPairs parent).Nonempty :=
        ⟨(0, 0), zero_zero_mem_bkAdmissibleChildPairs hparentPos⟩
      let childCost : Nat × Nat → Nat := fun children ↦
        if hchildren : children ∈ bkAdmissibleChildPairs parent then
          bkSumPreservingRecurrence G d children.1 +
            bkSumPreservingRecurrence G d children.2
        else 0
      obtain ⟨children, hchildren, hsup⟩ :=
        Finset.exists_mem_eq_sup (bkAdmissibleChildPairs parent) hpairs childCost
      obtain ⟨saturated, hleftMono, hrightMono, hsum,
          hsatLeftLower, hsatRightLower, hsatLeftUpper, hsatRightUpper,
          hsatLeftLt, hsatRightLt⟩ :=
        exists_saturated_bkAdmissibleChildPair
          (hparent.trans' hd) hchildren
      have hsaturatedLeftBound :
          (bkSumPreservingRecurrence G d saturated.1 : ℝ) ≤
            bkRpowPotential beta c d saturated.1 := by
        by_cases hterminal : bkScaleTerminal d saturated.1
        · rw [bkSumPreservingRecurrence_eq_zero_of_terminal G d saturated.1 hterminal]
          simpa only [Nat.cast_zero] using
            bkRpowPotential_nonneg_of_lower_scale hbeta hc0 hc1 hdPos
              (hparent.trans hsatLeftLower)
        · have hdsaturated : d ≤ saturated.1 := by
            unfold bkScaleTerminal at hterminal
            omega
          exact ih saturated.1 hsatLeftLt hdsaturated
            ((Nat.le_of_lt hsatLeftLt).trans hroot)
      have hsaturatedRightBound :
          (bkSumPreservingRecurrence G d saturated.2 : ℝ) ≤
            bkRpowPotential beta c d saturated.2 := by
        by_cases hterminal : bkScaleTerminal d saturated.2
        · rw [bkSumPreservingRecurrence_eq_zero_of_terminal G d saturated.2 hterminal]
          simpa only [Nat.cast_zero] using
            bkRpowPotential_nonneg_of_lower_scale hbeta hc0 hc1 hdPos
              (hparent.trans hsatRightLower)
        · have hdsaturated : d ≤ saturated.2 := by
            unfold bkScaleTerminal at hterminal
            omega
          exact ih saturated.2 hsatRightLt hdsaturated
            ((Nat.le_of_lt hsatRightLt).trans hroot)
      have hleftRecurrenceMono :
          (bkSumPreservingRecurrence G d children.1 : ℝ) ≤
            bkSumPreservingRecurrence G d saturated.1 := by
        exact_mod_cast bkSumPreservingRecurrence_mono G d hleftMono
      have hrightRecurrenceMono :
          (bkSumPreservingRecurrence G d children.2 : ℝ) ≤
            bkSumPreservingRecurrence G d saturated.2 := by
        exact_mod_cast bkSumPreservingRecurrence_mono G d hrightMono
      have hcharge := hprofile parent hparent hroot
      have hclose := add_bkRpowPotential_children_le_parent G
        hbeta hc0 hc1 hdPos hparentPos hsum hsatLeftLower hsatLeftUpper hcharge
      rw [bkSumPreservingRecurrence_eq_profile_add G d parent hnonterminal]
      change ((twoThirdsSeparationProfile G parent +
        (bkAdmissibleChildPairs parent).sup childCost : Nat) : ℝ) ≤ _
      rw [hsup]
      simp only [childCost, dif_pos hchildren, Nat.cast_add]
      linarith

/-- The potential estimate implies the explicit source linear-over-gap bound. -/
theorem bkSumPreservingRecurrence_cast_le_bkRpowCoefficient
    (G : ConnectivityGraph ι) (d root parent : Nat) (beta c : ℝ)
    (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1) (hd : 2 ≤ d)
    (hparent : d ≤ parent) (hroot : parent ≤ root)
    (hprofile : ∀ scale : Nat, d ≤ scale → scale ≤ root →
      (twoThirdsSeparationProfile G scale : ℝ) ≤ beta * (scale : ℝ) ^ c) :
    (bkSumPreservingRecurrence G d parent : ℝ) ≤
      bkRpowCoefficient beta c * parent / (d : ℝ) ^ (1 - c) := by
  have hpotential := bkSumPreservingRecurrence_cast_le_bkRpowPotential
    G d root parent beta c hbeta hc0 hc1 hd hparent hroot hprofile
  rw [bkRpowPotential_eq_source_form (by omega)] at hpotential
  have hsubtracted : 0 ≤
      (beta / bkRpowGap c) * (parent : ℝ) ^ c :=
    mul_nonneg (beta_div_bkRpowGap_nonneg hbeta hc0 hc1)
      (Real.rpow_nonneg (Nat.cast_nonneg parent) c)
  linarith

/-- The exact coefficient is controlled explicitly by the entropy tangent gap. -/
theorem bkRpowCoefficient_le_entropy_bound
    {beta c : ℝ} (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    bkRpowCoefficient beta c ≤
      3 * beta / (bkEntropyGap * (1 - c)) := by
  have hOneSubPos : 0 < 1 - c := sub_pos.mpr hc1
  have hEntropyDenomPos : 0 < bkEntropyGap * (1 - c) :=
    mul_pos bkEntropyGap_pos hOneSubPos
  have hthirdPower : (1 / 3 : ℝ) ≤ (1 / 3 : ℝ) ^ (1 - c) :=
    Real.self_le_rpow_of_le_one (by norm_num) (by norm_num) (by linarith)
  have hgapLower := bkEntropyGap_mul_one_sub_le_bkRpowGap c
  have hgapNonneg : 0 ≤ bkRpowGap c := (bkRpowGap_pos hc0 hc1).le
  have hdenomLower :
      bkEntropyGap * (1 - c) / 3 ≤
        bkRpowGap c * (1 / 3 : ℝ) ^ (1 - c) := by
    calc
      bkEntropyGap * (1 - c) / 3 =
          bkEntropyGap * (1 - c) * (1 / 3 : ℝ) := by ring
      _ ≤ bkRpowGap c * (1 / 3 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hgapLower (by norm_num)
      _ ≤ bkRpowGap c * (1 / 3 : ℝ) ^ (1 - c) :=
        mul_le_mul_of_nonneg_left hthirdPower hgapNonneg
  have hsmallPos : 0 < bkEntropyGap * (1 - c) / 3 := div_pos hEntropyDenomPos (by norm_num)
  have hdiv := div_le_div_of_nonneg_left hbeta hsmallPos hdenomLower
  unfold bkRpowCoefficient
  calc
    beta / (bkRpowGap c * (1 / 3 : ℝ) ^ (1 - c)) ≤
        beta / (bkEntropyGap * (1 - c) / 3) := hdiv
    _ = 3 * beta / (bkEntropyGap * (1 - c)) := by
      field_simp [hEntropyDenomPos.ne']

/-- The source exponent threshold converts the near-linear gap into `log n`. -/
theorem bkRpowCoefficient_le_log_bound
    {beta c n : ℝ} (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hn : 1 < n) (hthreshold : c ≤ 1 + Real.logb n (1 / 3 : ℝ)) :
    bkRpowCoefficient beta c ≤
      3 * beta * Real.log n / (bkEntropyGap * Real.log 3) := by
  have hlogN : 0 < Real.log n := Real.log_pos hn
  have hlogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogThird : Real.log (1 / 3 : ℝ) = -Real.log 3 := by
    rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hgapLog : Real.log 3 ≤ (1 - c) * Real.log n := by
    rw [Real.logb, hlogThird] at hthreshold
    have hthreshold' : c ≤ 1 - Real.log 3 / Real.log n := by
      convert hthreshold using 1
      ring
    have hdiv : Real.log 3 / Real.log n ≤ 1 - c := by linarith
    exact (div_le_iff₀ hlogN).mp hdiv
  have hreciprocal : 1 / (1 - c) ≤ Real.log n / Real.log 3 := by
    apply (div_le_div_iff₀ (sub_pos.mpr hc1) hlogThree).2
    simpa [mul_comm] using hgapLog
  have hscale : 0 ≤ 3 * beta / bkEntropyGap :=
    div_nonneg (mul_nonneg (by norm_num) hbeta) bkEntropyGap_pos.le
  calc
    bkRpowCoefficient beta c ≤
        3 * beta / (bkEntropyGap * (1 - c)) :=
      bkRpowCoefficient_le_entropy_bound hbeta hc0 hc1
    _ = (3 * beta / bkEntropyGap) * (1 / (1 - c)) := by
      field_simp [bkEntropyGap_pos.ne', (sub_pos.mpr hc1).ne']
    _ ≤ (3 * beta / bkEntropyGap) * (Real.log n / Real.log 3) :=
      mul_le_mul_of_nonneg_left hreciprocal hscale
    _ = 3 * beta * Real.log n / (bkEntropyGap * Real.log 3) := by ring

/--
An explicit logarithmic gap controls the near-linear recurrence coefficient.

This is the Lean-QEC repair used by the public BK terminal: the positive
`gamma` hypothesis is visible and is not derived from the pointwise fact
`c < 1`.  The fixed source threshold is recovered by taking
`gamma = log 3`.
-/
theorem bkRpowCoefficient_le_logarithmic_gap_bound
    {beta c n gamma : ℝ} (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hgamma : 0 < gamma)
    (hgap : gamma ≤ (1 - c) * Real.log n) :
    bkRpowCoefficient beta c ≤
      3 * beta * Real.log n / (bkEntropyGap * gamma) := by
  have hOneSubPos : 0 < 1 - c := sub_pos.mpr hc1
  have hreciprocal : 1 / (1 - c) ≤ Real.log n / gamma := by
    apply (div_le_div_iff₀ hOneSubPos hgamma).2
    simpa [mul_comm] using hgap
  have hscale : 0 ≤ 3 * beta / bkEntropyGap :=
    div_nonneg (mul_nonneg (by norm_num) hbeta) bkEntropyGap_pos.le
  calc
    bkRpowCoefficient beta c ≤
        3 * beta / (bkEntropyGap * (1 - c)) :=
      bkRpowCoefficient_le_entropy_bound hbeta hc0 hc1
    _ = (3 * beta / bkEntropyGap) * (1 / (1 - c)) := by
      field_simp [bkEntropyGap_pos.ne', hOneSubPos.ne']
    _ ≤ (3 * beta / bkEntropyGap) * (Real.log n / gamma) :=
      mul_le_mul_of_nonneg_left hreciprocal hscale
    _ = 3 * beta * Real.log n / (bkEntropyGap * gamma) := by ring

/--
Applying the concrete #380 partition a second time costs at most the square of
the one-pass coefficient.  The second recurrence is evaluated at the actual
first remainder cardinality, not at an independently maximized child scale.
-/
theorem BKRecursivePartition.remainder_recurrence_cast_le_bkRpowCoefficient_sq
    {G : ConnectivityGraph ι} {d : Nat} {vertices : Finset ι}
    (partition : BKRecursivePartition G d vertices) (beta c : ℝ)
    (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1) (hd : 2 ≤ d)
    (hvertices : d ≤ vertices.card)
    (hprofile : ∀ scale : Nat, d ≤ scale → scale ≤ vertices.card →
      (twoThirdsSeparationProfile G scale : ℝ) ≤ beta * (scale : ℝ) ^ c) :
    (bkSeparatorRecurrence G d partition.remainder : ℝ) ≤
      (bkRpowCoefficient beta c * bkRpowCoefficient beta c) * vertices.card /
        (((d : ℝ) ^ (1 - c)) * ((d : ℝ) ^ (1 - c))) := by
  let coefficient := bkRpowCoefficient beta c
  let denominator := (d : ℝ) ^ (1 - c)
  have hdPos : 0 < d := by omega
  have hdenominatorPos : 0 < denominator := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast hdPos) _
  have hcoefficientNonneg : 0 ≤ coefficient :=
    bkRpowCoefficient_nonneg hbeta hc0 hc1
  have hrootBound := bkSumPreservingRecurrence_cast_le_bkRpowCoefficient
    G d vertices.card vertices.card beta c hbeta hc0 hc1 hd hvertices le_rfl hprofile
  have hremainderRecurrence :
      (partition.remainder.card : ℝ) ≤
        (bkSumPreservingRecurrence G d vertices.card : ℝ) := by
    exact_mod_cast partition.remainder_card_le_bkSumPreservingRecurrence
  have hremainderBound :
      (partition.remainder.card : ℝ) ≤
        coefficient * vertices.card / denominator := by
    exact hremainderRecurrence.trans hrootBound
  have hremainderLeRoot : partition.remainder.card ≤ vertices.card :=
    Finset.card_le_card partition.remainder_subset
  have hseparatorRecurrence :
      (bkSeparatorRecurrence G d partition.remainder : ℝ) ≤
        (bkSumPreservingRecurrence G d partition.remainder.card : ℝ) := by
    exact_mod_cast bkSeparatorRecurrence_le_bkSumPreservingRecurrence_card
      G d partition.remainder
  by_cases hterminal : bkScaleTerminal d partition.remainder.card
  · have hrecurrenceZero := bkSumPreservingRecurrence_eq_zero_of_terminal
      G d partition.remainder.card hterminal
    rw [hrecurrenceZero] at hseparatorRecurrence
    have hseparatorZero :
        (bkSeparatorRecurrence G d partition.remainder : ℝ) ≤ 0 := by
      simpa only [Nat.cast_zero] using hseparatorRecurrence
    have hrightNonneg : 0 ≤
        (bkRpowCoefficient beta c * bkRpowCoefficient beta c) * vertices.card /
          (((d : ℝ) ^ (1 - c)) * ((d : ℝ) ^ (1 - c))) := by positivity
    exact hseparatorZero.trans hrightNonneg
  · have hdremainder : d ≤ partition.remainder.card := by
      unfold bkScaleTerminal at hterminal
      omega
    have hsecondBound := bkSumPreservingRecurrence_cast_le_bkRpowCoefficient
      G d vertices.card partition.remainder.card beta c hbeta hc0 hc1 hd
        hdremainder hremainderLeRoot hprofile
    have hscaledRemainder :
        coefficient * (partition.remainder.card : ℝ) / denominator ≤
          coefficient * (coefficient * vertices.card / denominator) / denominator := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hremainderBound hcoefficientNonneg)
        hdenominatorPos.le
    calc
      (bkSeparatorRecurrence G d partition.remainder : ℝ) ≤
          (bkSumPreservingRecurrence G d partition.remainder.card : ℝ) :=
        hseparatorRecurrence
      _ ≤ coefficient * partition.remainder.card / denominator := hsecondBound
      _ ≤ coefficient * (coefficient * vertices.card / denominator) / denominator :=
        hscaledRemainder
      _ = (bkRpowCoefficient beta c * bkRpowCoefficient beta c) * vertices.card /
          (((d : ℝ) ^ (1 - c)) * ((d : ℝ) ^ (1 - c))) := by
        simp only [coefficient, denominator]
        ring

namespace BKQLDPCFamily

variable {iota : Nat → Type u} {kappa : Nat → Type v}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable [∀ n, Fintype (kappa n)]

/-- The attained measured exponent gives the exact finite one-pass BK estimate. -/
theorem recurrence_le_cMax_coefficient
    (family : BKQLDPCFamily iota kappa) (i : family.Index) :
    (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
        (family.distance i.1) i.1 : ℝ) ≤
      bkRpowCoefficient 1 (family.cMax i) * i.1 /
        (family.distance i.1 : ℝ) ^ (1 - family.cMax i) := by
  apply bkSumPreservingRecurrence_cast_le_bkRpowCoefficient
    (root := i.1) (beta := 1) (c := family.cMax i)
  · norm_num
  · exact family.cMax_nonneg i
  · exact family.cMax_lt_one i
  · simpa [distance] using family.distance_two_le i.1 i.2
  · exact family.distance_le_index i.1 i.2
  · exact le_rfl
  · intro scale hdistance hscale
    simpa [measuredSeparationProfile] using
      family.measuredSeparationProfile_le_rpow_cMax i
        ((family.mem_validScales_iff i scale).2 ⟨hdistance, hscale⟩)

/-- The pointwise source threshold gives the explicit finite logarithmic coefficient. -/
theorem recurrence_le_cMax_log_bound
    (family : BKQLDPCFamily iota kappa) (i : family.Index)
    (hthreshold : family.cMax i ≤
      1 + Real.logb (i.1 : ℝ) (1 / 3 : ℝ)) :
    (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
        (family.distance i.1) i.1 : ℝ) ≤
      (3 * Real.log i.1 / (bkEntropyGap * Real.log 3)) * i.1 /
        (family.distance i.1 : ℝ) ^ (1 - family.cMax i) := by
  have hbase := family.recurrence_le_cMax_coefficient i
  have hn : (1 : ℝ) < i.1 := by
    have hnNat : 1 < i.1 :=
      lt_of_lt_of_le (by
        have := family.distance_two_le i.1 i.2
        omega) (family.distance_le_index i.1 i.2)
    exact_mod_cast hnNat
  have hcoeff := bkRpowCoefficient_le_log_bound
    (beta := 1) (c := family.cMax i) (n := (i.1 : ℝ))
    (by norm_num) (family.cMax_nonneg i) (family.cMax_lt_one i) hn hthreshold
  have hparentNonneg : (0 : ℝ) ≤ i.1 := Nat.cast_nonneg i.1
  have hdenomPos : 0 < (family.distance i.1 : ℝ) ^ (1 - family.cMax i) :=
    Real.rpow_pos_of_pos (by
      have hdNat : 0 < family.distance i.1 :=
        lt_of_lt_of_le (by omega) (family.distance_two_le i.1 i.2)
      exact_mod_cast hdNat) _
  calc
    (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
        (family.distance i.1) i.1 : ℝ) ≤
        bkRpowCoefficient 1 (family.cMax i) * i.1 /
          (family.distance i.1 : ℝ) ^ (1 - family.cMax i) := hbase
    _ ≤ (3 * Real.log i.1 / (bkEntropyGap * Real.log 3)) * i.1 /
          (family.distance i.1 : ℝ) ^ (1 - family.cMax i) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by simpa using hcoeff) hparentNonneg) hdenomPos.le

/--
The actual measured `cMax` coefficient is logarithmic on an explicitly given
Lean-QEC `gamma`-gap.  The gap is an input condition on measured family data,
not a consequence of `cMax < 1`.
-/
theorem recurrence_le_cMax_logarithmic_gap_bound
    (family : BKQLDPCFamily iota kappa) (i : family.Index)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : gamma ≤ (1 - family.cMax i) * Real.log i.1) :
    (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
        (family.distance i.1) i.1 : ℝ) ≤
      (3 * Real.log i.1 / (bkEntropyGap * gamma)) * i.1 /
        (family.distance i.1 : ℝ) ^ (1 - family.cMax i) := by
  have hbase := family.recurrence_le_cMax_coefficient i
  have hcoeff := bkRpowCoefficient_le_logarithmic_gap_bound
    (beta := 1) (c := family.cMax i) (n := (i.1 : ℝ)) (gamma := gamma)
    (by norm_num) (family.cMax_nonneg i) (family.cMax_lt_one i) hgamma hgap
  have hparentNonneg : (0 : ℝ) ≤ i.1 := Nat.cast_nonneg i.1
  have hdenomPos : 0 < (family.distance i.1 : ℝ) ^ (1 - family.cMax i) :=
    Real.rpow_pos_of_pos (by
      have hdNat : 0 < family.distance i.1 :=
        lt_of_lt_of_le (by omega) (family.distance_two_le i.1 i.2)
      exact_mod_cast hdNat) _
  calc
    (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
        (family.distance i.1) i.1 : ℝ) ≤
        bkRpowCoefficient 1 (family.cMax i) * i.1 /
          (family.distance i.1 : ℝ) ^ (1 - family.cMax i) := hbase
    _ ≤ (3 * Real.log i.1 / (bkEntropyGap * gamma)) * i.1 /
          (family.distance i.1 : ℝ) ^ (1 - family.cMax i) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by simpa using hcoeff) hparentNonneg) hdenomPos.le

/-- The exact eventual source condition for the logarithmic specialization. -/
def EventuallyCMaxAtMostBKLogThreshold
    (family : BKQLDPCFamily iota kappa) : Prop :=
  family.EventuallyOnValidIndices (fun i ↦
    family.cMax i ≤ 1 + Real.logb (i.1 : ℝ) (1 / 3 : ℝ))

/-- The source threshold is uniform over one explicit valid-index tail. -/
theorem eventually_recurrence_le_cMax_log_bound
    (family : BKQLDPCFamily iota kappa)
    (hfamily : family.EventuallyCMaxAtMostBKLogThreshold) :
    family.EventuallyOnValidIndices (fun i ↦
      (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
          (family.distance i.1) i.1 : ℝ) ≤
        (3 * Real.log i.1 / (bkEntropyGap * Real.log 3)) * i.1 /
          (family.distance i.1 : ℝ) ^ (1 - family.cMax i)) := by
  rcases hfamily with ⟨start, hstart⟩
  exact ⟨start, fun n hn hvalid ↦
    family.recurrence_le_cMax_log_bound ⟨n, hvalid⟩ (hstart n hn hvalid)⟩

/-- The logarithmic-gap recurrence estimate holds on the exact valid-index tail. -/
theorem eventually_recurrence_le_cMax_logarithmic_gap_bound
    (family : BKQLDPCFamily iota kappa) {gamma : ℝ} (hgamma : 0 < gamma)
    (hfamily : family.EventuallyOnValidIndices (fun i ↦
      gamma ≤ (1 - family.cMax i) * Real.log i.1)) :
    family.EventuallyOnValidIndices (fun i ↦
      (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
          (family.distance i.1) i.1 : ℝ) ≤
        (3 * Real.log i.1 / (bkEntropyGap * gamma)) * i.1 /
          (family.distance i.1 : ℝ) ^ (1 - family.cMax i)) := by
  rcases hfamily with ⟨start, hstart⟩
  exact ⟨start, fun n hn hvalid ↦
    family.recurrence_le_cMax_logarithmic_gap_bound ⟨n, hvalid⟩ hgamma
      (hstart n hn hvalid)⟩

/--
A fixed exponent ceiling below one uniformly controls the coefficient while
preserving the sharper pointwise `cMax` exponent in the distance denominator.
-/
theorem recurrence_le_uniform_ceiling
    (family : BKQLDPCFamily iota kappa) (i : family.Index)
    {ceiling : ℝ} (_hceiling0 : 0 ≤ ceiling) (hceiling1 : ceiling < 1)
    (hcMax : family.cMax i ≤ ceiling) :
    (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
        (family.distance i.1) i.1 : ℝ) ≤
      (3 / (bkEntropyGap * (1 - ceiling))) * i.1 /
        (family.distance i.1 : ℝ) ^ (1 - family.cMax i) := by
  have hbase := family.recurrence_le_cMax_coefficient i
  have hpointwiseCoeff := bkRpowCoefficient_le_entropy_bound
    (beta := (1 : ℝ)) (c := family.cMax i) (by norm_num)
      (family.cMax_nonneg i) (family.cMax_lt_one i)
  have hceilingDenomPos : 0 < bkEntropyGap * (1 - ceiling) :=
    mul_pos bkEntropyGap_pos (sub_pos.mpr hceiling1)
  have hdenomOrder :
      bkEntropyGap * (1 - ceiling) ≤
        bkEntropyGap * (1 - family.cMax i) := by
    exact mul_le_mul_of_nonneg_left (by linarith) bkEntropyGap_pos.le
  have huniformCoeff :
      bkRpowCoefficient 1 (family.cMax i) ≤
        3 / (bkEntropyGap * (1 - ceiling)) := by
    have hdiv :
        (3 : ℝ) / (bkEntropyGap * (1 - family.cMax i)) ≤
          3 / (bkEntropyGap * (1 - ceiling)) :=
      div_le_div_of_nonneg_left (by norm_num) hceilingDenomPos hdenomOrder
    have hpointwiseCoeff' :
        bkRpowCoefficient 1 (family.cMax i) ≤
          3 / (bkEntropyGap * (1 - family.cMax i)) := by
      simpa using hpointwiseCoeff
    exact hpointwiseCoeff'.trans hdiv
  have hparentNonneg : (0 : ℝ) ≤ i.1 := Nat.cast_nonneg i.1
  have hdistancePos : (0 : ℝ) < family.distance i.1 := by
    have hdNat : 0 < family.distance i.1 := by
      have hdTwo : 2 ≤ family.distance i.1 := by
        simpa [distance] using family.distance_two_le i.1 i.2
      omega
    exact_mod_cast hdNat
  have hdenomPos : 0 <
      (family.distance i.1 : ℝ) ^ (1 - family.cMax i) :=
    Real.rpow_pos_of_pos hdistancePos _
  calc
    (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
        (family.distance i.1) i.1 : ℝ) ≤
        bkRpowCoefficient 1 (family.cMax i) * i.1 /
          (family.distance i.1 : ℝ) ^ (1 - family.cMax i) := hbase
    _ ≤ (3 / (bkEntropyGap * (1 - ceiling))) * i.1 /
          (family.distance i.1 : ℝ) ^ (1 - family.cMax i) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right huniformCoeff hparentNonneg) hdenomPos.le

/-- `UniformCMaxBelowOne` supplies one constant and one valid-index tail. -/
theorem eventually_recurrence_le_uniform_ceiling
    (family : BKQLDPCFamily iota kappa)
    (hfamily : family.UniformCMaxBelowOne) :
    ∃ ceiling : ℝ, 0 < ceiling ∧ ceiling < 1 ∧
      family.EventuallyOnValidIndices (fun i ↦
        (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
            (family.distance i.1) i.1 : ℝ) ≤
          (3 / (bkEntropyGap * (1 - ceiling))) * i.1 /
            (family.distance i.1 : ℝ) ^ (1 - family.cMax i)) := by
  rcases hfamily with ⟨ceiling, hceiling0, hceiling1, start, hstart⟩
  refine ⟨ceiling, hceiling0, hceiling1, start, ?_⟩
  intro n hn hvalid
  exact family.recurrence_le_uniform_ceiling ⟨n, hvalid⟩ hceiling0.le hceiling1
    (hstart n hn hvalid)

end BKQLDPCFamily

end QEC.Locality
