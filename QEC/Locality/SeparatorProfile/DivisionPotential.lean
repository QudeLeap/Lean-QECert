import QEC.Locality.ConnectivityTradeoff.QuantitativeRecurrence
import QEC.Locality.SeparatorProfile.Quantitative
/-!
# Retained-separator potential for finite profile divisions

Size recursion retains its separator in both child carriers.  If the separator
is at most one twelfth of the parent, the two retained carriers still occupy
between one quarter and three quarters of their combined mass.  The potential
below records the resulting concavity gap and pays for three copies of every
separator in the inherited-boundary ledger.
-/

noncomputable section

namespace QEC.Locality

/-- Concavity gap for the retained-child interval `[1/4, 3/4]`. -/
private def profileDivisionRpowGap (exponent : ℝ) : ℝ :=
  (3 / 4 : ℝ) ^ exponent + (1 / 4 : ℝ) ^ exponent - 1

/-- Four separator copies: three boundary copies and one retained-mass copy. -/
def profileDivisionPotentialCoefficient (beta exponent : ℝ) : ℝ :=
  4 * beta / profileDivisionRpowGap exponent

/-- Linear-minus-power potential at terminal scale `r`. -/
def profileDivisionPotential
    (beta exponent : ℝ) (r parent : Nat) : ℝ :=
  profileDivisionPotentialCoefficient beta exponent * (r : ℝ) ^ exponent *
    (((parent : ℝ) / r) / (1 / 4 : ℝ) ^ (1 - exponent) -
      ((parent : ℝ) / r) ^ exponent)

/-- Uniform scale at which both strict recursion and retained-mass amortization apply. -/
noncomputable def profileDivisionThreshold (beta exponent : ℝ) : Nat :=
  max (profileSeparatorThreshold beta exponent)
    (Nat.ceil
      ((profileDivisionPotentialCoefficient beta exponent /
          (1 / 4 : ℝ) ^ (1 - exponent)) ^ ((1 - exponent)⁻¹)))

private theorem profileDivisionRpowGap_pos
    {exponent : ℝ} (hexponent : 0 < exponent ∧ exponent < 1) :
    0 < profileDivisionRpowGap exponent := by
  have hquarter : (1 / 4 : ℝ) < (1 / 4 : ℝ) ^ exponent :=
    Real.self_lt_rpow_of_lt_one (by norm_num) (by norm_num) hexponent.2
  have hthreeQuarter : (3 / 4 : ℝ) < (3 / 4 : ℝ) ^ exponent :=
    Real.self_lt_rpow_of_lt_one (by norm_num) (by norm_num) hexponent.2
  unfold profileDivisionRpowGap
  linarith

/-- Endpoint lower bound for complementary powers on the retained-child interval. -/
private theorem profileDivisionRpowGap_le_complementary_sum_sub_one
    {exponent t : ℝ} (hexponent : 0 ≤ exponent ∧ exponent ≤ 1)
    (ht : t ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ)) :
    profileDivisionRpowGap exponent ≤ t ^ exponent + (1 - t) ^ exponent - 1 := by
  let a : ℝ := 3 / 2 - 2 * t
  let b : ℝ := 2 * t - 1 / 2
  have ha : 0 ≤ a := by dsimp [a]; linarith [ht.2]
  have hb : 0 ≤ b := by dsimp [b]; linarith [ht.1]
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have hba : b + a = 1 := by linarith
  have htCombo : a * (1 / 4 : ℝ) + b * (3 / 4 : ℝ) = t := by
    dsimp [a, b]
    ring
  have hOneSubCombo : b * (1 / 4 : ℝ) + a * (3 / 4 : ℝ) = 1 - t := by
    dsimp [a, b]
    ring
  have hconcave := Real.concaveOn_rpow hexponent.1 hexponent.2
  have htPower := hconcave.2
    (show (1 / 4 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (3 / 4 : ℝ) ∈ Set.Ici 0 by norm_num) ha hb hab
  have hOneSubPower := hconcave.2
    (show (1 / 4 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (3 / 4 : ℝ) ∈ Set.Ici 0 by norm_num) hb ha hba
  simp only [smul_eq_mul, htCombo] at htPower
  simp only [smul_eq_mul, hOneSubCombo] at hOneSubPower
  have hsum :
      (3 / 4 : ℝ) ^ exponent + (1 / 4 : ℝ) ^ exponent ≤
        t ^ exponent + (1 - t) ^ exponent := by
    calc
      (3 / 4 : ℝ) ^ exponent + (1 / 4 : ℝ) ^ exponent =
          (a * (1 / 4 : ℝ) ^ exponent + b * (3 / 4 : ℝ) ^ exponent) +
            (b * (1 / 4 : ℝ) ^ exponent + a * (3 / 4 : ℝ) ^ exponent) := by
        calc
          _ = 1 * (1 / 4 : ℝ) ^ exponent + 1 * (3 / 4 : ℝ) ^ exponent := by ring
          _ = (a + b) * (1 / 4 : ℝ) ^ exponent +
              (a + b) * (3 / 4 : ℝ) ^ exponent := by rw [hab]
          _ = _ := by ring
      _ ≤ t ^ exponent + (1 - t) ^ exponent := add_le_add htPower hOneSubPower
  unfold profileDivisionRpowGap
  linarith [hsum]

/-- Scaling the retained-child gap from unit mass to an arbitrary positive total. -/
private theorem profileDivisionRpowGap_mul_total_le_children_gap
    {exponent total left right : ℝ} (hexponent : 0 ≤ exponent ∧ exponent ≤ 1)
    (htotal : 0 < total) (hsum : left + right = total)
    (hleftLower : total / 4 ≤ left) (hleftUpper : left ≤ 3 * total / 4) :
    profileDivisionRpowGap exponent * total ^ exponent ≤
      left ^ exponent + right ^ exponent - total ^ exponent := by
  let t := left / total
  have ht : t ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) := by
    constructor
    · dsimp [t]
      apply (le_div_iff₀ htotal).2
      nlinarith [hleftLower]
    · dsimp [t]
      apply (div_le_iff₀ htotal).2
      nlinarith [hleftUpper]
  have hunit := profileDivisionRpowGap_le_complementary_sum_sub_one hexponent ht
  have htNonneg : 0 ≤ t := (show (0 : ℝ) ≤ 1 / 4 by norm_num).trans ht.1
  have htLeOne : t ≤ 1 := ht.2.trans (by norm_num)
  have hOneSubNonneg : 0 ≤ 1 - t := sub_nonneg.mpr htLeOne
  have hleft : left = total * t := by
    dsimp [t]
    field_simp [htotal.ne']
  have hright : right = total * (1 - t) := by
    calc
      right = total - left := by linarith [hsum]
      _ = total * (1 - t) := by rw [hleft]; ring
  have hscaled := mul_le_mul_of_nonneg_right hunit
    (Real.rpow_nonneg htotal.le exponent)
  rw [hleft, hright, Real.mul_rpow htotal.le htNonneg,
    Real.mul_rpow htotal.le hOneSubNonneg]
  nlinarith [hscaled]

theorem profileDivisionPotentialCoefficient_nonneg
    {beta exponent : ℝ} (hbeta : 0 ≤ beta)
    (hexponent : 0 < exponent ∧ exponent < 1) :
    0 ≤ profileDivisionPotentialCoefficient beta exponent := by
  exact div_nonneg (mul_nonneg (by norm_num) hbeta)
    (profileDivisionRpowGap_pos hexponent).le

theorem profileDivisionPotentialCoefficient_pos
    {beta exponent : ℝ} (hbeta : 1 ≤ beta)
    (hexponent : 0 < exponent ∧ exponent < 1) :
    0 < profileDivisionPotentialCoefficient beta exponent := by
  exact div_pos (mul_pos (by norm_num) (zero_lt_one.trans_le hbeta))
    (profileDivisionRpowGap_pos hexponent)

/-- The uniform division threshold makes the retained linear penalty at most one. -/
theorem profileDivisionPotential_linearScale_le_one_of_threshold
    {beta exponent : ℝ} (hbeta : 1 ≤ beta)
    (hexponent : 0 < exponent ∧ exponent < 1)
    {r : Nat} (hthreshold : profileDivisionThreshold beta exponent ≤ r) :
    profileDivisionPotentialCoefficient beta exponent *
        (r : ℝ) ^ (exponent - 1) /
          (1 / 4 : ℝ) ^ (1 - exponent) ≤ 1 := by
  let gap : ℝ := 1 - exponent
  let base : ℝ := profileDivisionPotentialCoefficient beta exponent /
    (1 / 4 : ℝ) ^ gap
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hquarterPow : 0 < (1 / 4 : ℝ) ^ gap := Real.rpow_pos_of_pos (by norm_num) gap
  have hbase : 0 < base := by
    exact div_pos (profileDivisionPotentialCoefficient_pos hbeta hexponent) hquarterPow
  have hbaseRoot : base ^ gap⁻¹ ≤ (r : ℝ) := by
    calc
      base ^ gap⁻¹ ≤
          (Nat.ceil
            ((profileDivisionPotentialCoefficient beta exponent /
              (1 / 4 : ℝ) ^ (1 - exponent)) ^ ((1 - exponent)⁻¹)) : Nat) := by
        exact_mod_cast (Nat.le_ceil (base ^ gap⁻¹))
      _ ≤ profileDivisionThreshold beta exponent := by
        exact_mod_cast (Nat.le_max_right
          (profileSeparatorThreshold beta exponent)
          (Nat.ceil
            ((profileDivisionPotentialCoefficient beta exponent /
              (1 / 4 : ℝ) ^ (1 - exponent)) ^ ((1 - exponent)⁻¹))))
      _ ≤ r := by exact_mod_cast hthreshold
  have hrPos : (0 : ℝ) < r := (Real.rpow_pos_of_pos hbase _).trans_le hbaseRoot
  have hgapPow : base ≤ (r : ℝ) ^ gap := by
    calc
      base = (base ^ gap⁻¹) ^ gap := by
        rw [← Real.rpow_mul hbase.le]
        field_simp [hgap.ne']
        simp
      _ ≤ (r : ℝ) ^ gap :=
        Real.rpow_le_rpow (Real.rpow_nonneg hbase.le _) hbaseRoot hgap.le
  have hdivide : base / (r : ℝ) ^ gap ≤ 1 :=
    (div_le_one (Real.rpow_pos_of_pos hrPos gap)).2 hgapPow
  have hrpowNeg : (r : ℝ) ^ (exponent - 1) = 1 / (r : ℝ) ^ gap := by
    rw [show exponent - 1 = -gap by dsimp [gap]; ring, Real.rpow_neg hrPos.le]
    simp [one_div]
  rw [hrpowNeg]
  change profileDivisionPotentialCoefficient beta exponent *
      (1 / (r : ℝ) ^ gap) / (1 / 4 : ℝ) ^ gap ≤ 1
  dsimp [base] at hdivide
  calc
    profileDivisionPotentialCoefficient beta exponent *
          (1 / (r : ℝ) ^ gap) / (1 / 4 : ℝ) ^ gap =
        (profileDivisionPotentialCoefficient beta exponent /
          (1 / 4 : ℝ) ^ gap) / (r : ℝ) ^ gap := by ring
    _ ≤ 1 := hdivide

/-- The retained potential is nonnegative once the parent is at least one quarter of `r`. -/
theorem profileDivisionPotential_nonneg
    {beta exponent : ℝ} {r parent : Nat}
    (hbeta : 0 ≤ beta) (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 0 < r) (hlower : r ≤ 4 * parent) :
    0 ≤ profileDivisionPotential beta exponent r parent := by
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have hratio : (1 / 4 : ℝ) ≤ (parent : ℝ) / r := by
    apply (le_div_iff₀ hrReal).2
    have hlowerReal : (r : ℝ) ≤ 4 * parent := by exact_mod_cast hlower
    nlinarith
  have hpower := rpow_le_div_endpoint_rpow
    (a := (1 / 4 : ℝ)) (q := (parent : ℝ) / r) (c := exponent)
    (by norm_num) hratio hexponent.2
  unfold profileDivisionPotential
  exact mul_nonneg
    (mul_nonneg
      (profileDivisionPotentialCoefficient_nonneg hbeta hexponent)
      (Real.rpow_nonneg hrReal.le exponent))
    (sub_nonneg.mpr hpower)

/-- Expanded form separating the retained linear mass from the concave power term. -/
private theorem profileDivisionPotential_eq_expanded
    {beta exponent : ℝ} {r parent : Nat} (hr : 0 < r) :
    profileDivisionPotential beta exponent r parent =
      profileDivisionPotentialCoefficient beta exponent *
        ((parent : ℝ) * (r : ℝ) ^ (exponent - 1) /
            (1 / 4 : ℝ) ^ (1 - exponent) -
          (parent : ℝ) ^ exponent) := by
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have hrPowPos : 0 < (r : ℝ) ^ exponent := Real.rpow_pos_of_pos hrReal exponent
  rw [profileDivisionPotential, Real.div_rpow (Nat.cast_nonneg parent) hrReal.le,
    Real.rpow_sub_one hrReal.ne']
  field_simp [hrReal.ne', hrPowPos.ne']

/-- Dropping the nonnegative concave term gives the useful linear potential bound. -/
theorem profileDivisionPotential_le_linear
    {beta exponent : ℝ} {r parent : Nat}
    (hbeta : 0 ≤ beta) (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 0 < r) :
    profileDivisionPotential beta exponent r parent ≤
      profileDivisionPotentialCoefficient beta exponent *
        ((parent : ℝ) * (r : ℝ) ^ (exponent - 1) /
          (1 / 4 : ℝ) ^ (1 - exponent)) := by
  rw [profileDivisionPotential_eq_expanded hr]
  have hcoefficient := profileDivisionPotentialCoefficient_nonneg hbeta hexponent
  have hparentPower : 0 ≤ (parent : ℝ) ^ exponent :=
    Real.rpow_nonneg (Nat.cast_nonneg parent) exponent
  nlinarith

/-- At scale at least one, the retained potential is at most a fixed multiple of root mass. -/
theorem profileDivisionPotential_le_root
    {beta exponent : ℝ} {r parent : Nat}
    (hbeta : 0 ≤ beta) (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 1 ≤ r) :
    profileDivisionPotential beta exponent r parent ≤
      (profileDivisionPotentialCoefficient beta exponent /
        (1 / 4 : ℝ) ^ (1 - exponent)) * parent := by
  have hrPos : 0 < r := Nat.zero_lt_of_lt hr
  have hrReal : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrpow : (r : ℝ) ^ (exponent - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hrReal (by linarith)
  have hcoefficient : 0 ≤ profileDivisionPotentialCoefficient beta exponent :=
    profileDivisionPotentialCoefficient_nonneg hbeta hexponent
  have hquarterPow : 0 < (1 / 4 : ℝ) ^ (1 - exponent) :=
    Real.rpow_pos_of_pos (by norm_num) _
  calc
    profileDivisionPotential beta exponent r parent ≤
        profileDivisionPotentialCoefficient beta exponent *
          ((parent : ℝ) * (r : ℝ) ^ (exponent - 1) /
            (1 / 4 : ℝ) ^ (1 - exponent)) :=
      profileDivisionPotential_le_linear hbeta hexponent hrPos
    _ ≤ profileDivisionPotentialCoefficient beta exponent *
          ((parent : ℝ) * 1 / (1 / 4 : ℝ) ^ (1 - exponent)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrpow (Nat.cast_nonneg parent)) hquarterPow.le)
        hcoefficient
    _ = (profileDivisionPotentialCoefficient beta exponent /
          (1 / 4 : ℝ) ^ (1 - exponent)) * parent := by ring

/-- One retained separator split is paid for by the drop in the graph-uniform potential. -/
theorem profileDivisionPotential_split
    {beta exponent : ℝ} {r parent left right separator : Nat}
    (hbeta : 0 ≤ beta) (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 0 < r) (hparent : 0 < parent)
    (hsum : left + right = parent + separator)
    (hleftLower : parent + separator ≤ 4 * left)
    (hleftUpper : 4 * left ≤ 3 * (parent + separator))
    (hseparator : (separator : ℝ) ≤ beta * (parent : ℝ) ^ exponent)
    (hscale :
      profileDivisionPotentialCoefficient beta exponent *
          (r : ℝ) ^ (exponent - 1) /
            (1 / 4 : ℝ) ^ (1 - exponent) ≤ 1) :
    3 * separator + profileDivisionPotential beta exponent r left +
        profileDivisionPotential beta exponent r right ≤
      profileDivisionPotential beta exponent r parent := by
  let coefficient := profileDivisionPotentialCoefficient beta exponent
  let linearScale :=
    (r : ℝ) ^ (exponent - 1) / (1 / 4 : ℝ) ^ (1 - exponent)
  have hsumReal : (left : ℝ) + right = parent + separator := by exact_mod_cast hsum
  have htotalPos : 0 < (parent : ℝ) + separator := by positivity
  have hleftLowerReal : ((parent : ℝ) + separator) / 4 ≤ left := by
    have : (parent : ℝ) + separator ≤ 4 * left := by exact_mod_cast hleftLower
    linarith
  have hleftUpperReal : (left : ℝ) ≤ 3 * ((parent : ℝ) + separator) / 4 := by
    have : (4 : ℝ) * left ≤ 3 * ((parent : ℝ) + separator) := by
      exact_mod_cast hleftUpper
    linarith
  have hconcavity := profileDivisionRpowGap_mul_total_le_children_gap
    (exponent := exponent) (total := (parent : ℝ) + separator)
    (left := left) (right := right) ⟨hexponent.1.le, hexponent.2.le⟩
    htotalPos hsumReal hleftLowerReal hleftUpperReal
  have hparentPower : (parent : ℝ) ^ exponent ≤
      ((parent : ℝ) + separator) ^ exponent := by
    exact Real.rpow_le_rpow (Nat.cast_nonneg parent)
      (le_add_of_nonneg_right (Nat.cast_nonneg separator)) hexponent.1.le
  have hgapNonneg : 0 ≤ profileDivisionRpowGap exponent :=
    (profileDivisionRpowGap_pos hexponent).le
  have hpowerGap :
      profileDivisionRpowGap exponent * (parent : ℝ) ^ exponent ≤
        (left : ℝ) ^ exponent + (right : ℝ) ^ exponent -
          (parent : ℝ) ^ exponent := by
    have hscaledParent := mul_le_mul_of_nonneg_left hparentPower hgapNonneg
    linarith
  have hcoefficientGap :
      coefficient * profileDivisionRpowGap exponent = 4 * beta := by
    dsimp [coefficient, profileDivisionPotentialCoefficient]
    field_simp [(profileDivisionRpowGap_pos hexponent).ne']
  have hseparatorNonneg : (0 : ℝ) ≤ separator := Nat.cast_nonneg separator
  have hscale' : coefficient * linearScale ≤ 1 := by
    calc
      coefficient * linearScale =
          profileDivisionPotentialCoefficient beta exponent *
              (r : ℝ) ^ (exponent - 1) /
                (1 / 4 : ℝ) ^ (1 - exponent) := by
            dsimp [coefficient, linearScale]
            ring
      _ ≤ 1 := hscale
  have hlinearPenalty : coefficient * ((separator : ℝ) * linearScale) ≤ separator := by
    calc
      coefficient * ((separator : ℝ) * linearScale) =
          (separator : ℝ) * (coefficient * linearScale) := by ring
      _ ≤ (separator : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hscale' hseparatorNonneg
      _ = separator := by ring
  have hseparatorPayment : (4 : ℝ) * separator ≤
      coefficient * ((left : ℝ) ^ exponent + (right : ℝ) ^ exponent -
        (parent : ℝ) ^ exponent) := by
    calc
      (4 : ℝ) * separator ≤ 4 * (beta * (parent : ℝ) ^ exponent) := by
        nlinarith [hseparator]
      _ = coefficient *
          (profileDivisionRpowGap exponent * (parent : ℝ) ^ exponent) := by
        calc
          4 * (beta * (parent : ℝ) ^ exponent) =
              (coefficient * profileDivisionRpowGap exponent) *
                (parent : ℝ) ^ exponent := by rw [hcoefficientGap]; ring
          _ = _ := by ring
      _ ≤ coefficient * ((left : ℝ) ^ exponent + (right : ℝ) ^ exponent -
          (parent : ℝ) ^ exponent) := by
        exact mul_le_mul_of_nonneg_left hpowerGap
          (profileDivisionPotentialCoefficient_nonneg hbeta hexponent)
  rw [profileDivisionPotential_eq_expanded hr,
    profileDivisionPotential_eq_expanded hr,
    profileDivisionPotential_eq_expanded hr]
  have hlinearForm (x : ℝ) :
      x * (r : ℝ) ^ (exponent - 1) / (1 / 4 : ℝ) ^ (1 - exponent) =
        x * linearScale := by
    dsimp [linearScale]
    ring
  rw [hlinearForm, hlinearForm, hlinearForm]
  change (3 : ℝ) * separator +
      coefficient * ((left : ℝ) * linearScale - (left : ℝ) ^ exponent) +
      coefficient * ((right : ℝ) * linearScale - (right : ℝ) ^ exponent) ≤
    coefficient * ((parent : ℝ) * linearScale - (parent : ℝ) ^ exponent)
  calc
    (3 : ℝ) * separator +
          coefficient * ((left : ℝ) * linearScale - (left : ℝ) ^ exponent) +
          coefficient * ((right : ℝ) * linearScale - (right : ℝ) ^ exponent) =
        coefficient * ((parent : ℝ) * linearScale - (parent : ℝ) ^ exponent) +
          ((3 : ℝ) * separator + coefficient * ((separator : ℝ) * linearScale) -
            coefficient * ((left : ℝ) ^ exponent + (right : ℝ) ^ exponent -
              (parent : ℝ) ^ exponent)) := by
      have hlinearSum := congrArg
        (fun x : ℝ => coefficient * (x * linearScale)) hsumReal
      linear_combination hlinearSum
    _ ≤ coefficient * ((parent : ℝ) * linearScale - (parent : ℝ) ^ exponent) := by
      nlinarith [hlinearPenalty, hseparatorPayment]

end QEC.Locality
