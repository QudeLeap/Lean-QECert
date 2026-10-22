import QEC.Locality.SeparatorProfile.Recursion
/-!
# Uniform quantitative constants for profile-separator recursion

The threshold in this module is fixed before a graph or a scale is chosen. It
turns the sublinear profile exponent into a strict fixed-fraction separator
bound, which is the termination input for the edge-restricted recursion.
-/

namespace QEC.Locality

universe u

/-- The left child edge set at a separator node, relative to the node's own edge set. -/
noncomputable def separatorLeftEdges {ι : Type u} [DecidableEq ι]
    (edges : Finset (ι × ι)) (left : Finset ι) : Finset (ι × ι) :=
  edges.filter fun edge => edge.1 ∈ left ∨ edge.2 ∈ left

/-- The complementary right child edge set at a separator node. -/
noncomputable def separatorRightEdges {ι : Type u} [DecidableEq ι]
    (edges : Finset (ι × ι)) (left : Finset ι) : Finset (ι × ι) :=
  edges.filter fun edge => ¬ (edge.1 ∈ left ∨ edge.2 ∈ left)

/-- A reverse-symmetric node edge set stays reverse-symmetric after separator allocation. -/
theorem separatorLeftEdges_reverse {ι : Type u} [DecidableEq ι]
    (edges : Finset (ι × ι)) (left : Finset ι)
    (hsymmetric : ∀ x y, (x, y) ∈ edges ↔ (y, x) ∈ edges) (x y : ι) :
    (x, y) ∈ separatorLeftEdges edges left ↔ (y, x) ∈ separatorLeftEdges edges left := by
  simp only [separatorLeftEdges, Finset.mem_filter]
  constructor
  · rintro ⟨hxy, hleft⟩
    exact ⟨(hsymmetric x y).1 hxy, hleft.symm⟩
  · rintro ⟨hyx, hleft⟩
    exact ⟨(hsymmetric y x).1 hyx, hleft.symm⟩

theorem separatorRightEdges_reverse {ι : Type u} [DecidableEq ι]
    (edges : Finset (ι × ι)) (left : Finset ι)
    (hsymmetric : ∀ x y, (x, y) ∈ edges ↔ (y, x) ∈ edges) (x y : ι) :
    (x, y) ∈ separatorRightEdges edges left ↔ (y, x) ∈ separatorRightEdges edges left := by
  simp only [separatorRightEdges, Finset.mem_filter]
  constructor
  · rintro ⟨hxy, hleft⟩
    exact ⟨(hsymmetric x y).1 hxy, by simpa [or_comm] using hleft⟩
  · rintro ⟨hyx, hleft⟩
    exact ⟨(hsymmetric y x).1 hyx, by simpa [or_comm] using hleft⟩

/-- A graph-uniform threshold at which a `beta * n^exponent` separator is at most `n / 12`. -/
noncomputable def profileSeparatorThreshold (beta exponent : ℝ) : Nat :=
  Nat.ceil ((12 * beta) ^ ((1 - exponent)⁻¹))

/-- The graph-uniform profile hypothesis is inherited by every finite edge subproblem. -/
theorem AssumedBGKLMeasuredProfilePowerUpperBound.edgeRestricted
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (edges : Finset (ι × ι)) :
    AssumedBGKLMeasuredProfilePowerUpperBound
      (edgeRestrictedGraph G edges) beta exponent := by
  refine ⟨hProfile.1, hProfile.2.1, hProfile.2.2.1, ?_⟩
  intro scale hscale hcard
  exact (Nat.cast_le.2 (twoThirdsSeparationProfile_edgeRestricted_le G edges scale)).trans
    (hProfile.2.2.2 scale hscale hcard)

/-- Above the explicit threshold, the profile term is at most one twelfth of the scale. -/
private theorem profilePower_le_twelfth_of_threshold
    {beta exponent : ℝ} (hbeta : 1 ≤ beta) (hexponent : exponent < 1)
    {scale : Nat} (hscale : profileSeparatorThreshold beta exponent ≤ scale) :
    12 * beta * Real.rpow scale exponent ≤ (scale : ℝ) := by
  let gap : ℝ := 1 - exponent
  let base : ℝ := 12 * beta
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith
  have hbase : 0 < base := by
    dsimp [base]
    nlinarith
  have hscaleNonneg : 0 ≤ (scale : ℝ) := Nat.cast_nonneg scale
  have hthreshold : base ^ gap⁻¹ ≤ (scale : ℝ) := by
    calc
      base ^ gap⁻¹ ≤ (profileSeparatorThreshold beta exponent : ℝ) := by
        simpa [profileSeparatorThreshold, base, gap] using
          (Nat.le_ceil ((12 * beta) ^ ((1 - exponent)⁻¹)))
      _ ≤ (scale : ℝ) := by exact_mod_cast hscale
  have hgapPow : base ≤ (scale : ℝ) ^ gap := by
    calc
      base = (base ^ gap⁻¹) ^ gap := by
        rw [← Real.rpow_mul hbase.le]
        field_simp [hgap.ne']
        simp
      _ ≤ (scale : ℝ) ^ gap :=
        Real.rpow_le_rpow (Real.rpow_nonneg hbase.le _) hthreshold hgap.le
  have hscalePos : 0 < (scale : ℝ) :=
    (Real.rpow_pos_of_pos hbase _).trans_le hthreshold
  have hfactor : (scale : ℝ) ^ exponent * (scale : ℝ) ^ gap = scale := by
    rw [← Real.rpow_add hscalePos]
    dsimp [gap]
    ring_nf
    exact Real.rpow_one _
  calc
    12 * beta * Real.rpow scale exponent = base * (scale : ℝ) ^ exponent := by
      simp [base]
    _ ≤ (scale : ℝ) ^ gap * (scale : ℝ) ^ exponent := by
      exact mul_le_mul_of_nonneg_right hgapPow (Real.rpow_nonneg hscaleNonneg _)
    _ = (scale : ℝ) := by
      rw [mul_comm]
      exact hfactor

/-- A balanced side plus a twelfth-scale separator is strictly smaller than its parent. -/
private theorem separatorChild_card_lt_of_balanced_and_twelfth
    {parent child separator : Nat} (hparent : 0 < parent)
    (hbalanced : 3 * child ≤ 2 * parent) (hseparator : 12 * separator ≤ parent) :
    child + separator < parent := by
  omega

/-- At the uniform threshold, a minimum profile separator is at most one twelfth of its node. -/
private theorem profileSeparator_separator_card_twelfth
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : exponent < 1)
    {vertices separator : Finset ι}
    (hvertices : 1 ≤ vertices.card)
    (hscale : profileSeparatorThreshold beta exponent ≤ vertices.card)
    (hminimum :
      separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices) :
    12 * separator.card ≤ vertices.card := by
  have hprofileReal := minimumSeparator_card_real_le_profilePower
    G beta exponent hProfile vertices separator hvertices hminimum
  have hpower := profilePower_le_twelfth_of_threshold hProfile.1 hexponent hscale
  have hseparatorReal : (12 * separator.card : ℝ) ≤ vertices.card := by
    nlinarith
  exact_mod_cast hseparatorReal

/-- The profile threshold turns a minimum balanced separator into strict edge-region descent. -/
theorem profileSeparator_child_card_lt
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : exponent < 1)
    {vertices left separator : Finset ι}
    (hvertices : 1 ≤ vertices.card)
    (hscale : profileSeparatorThreshold beta exponent ≤ vertices.card)
    (hminimum :
      separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices)
    (hbalanced : 3 * left.card ≤ 2 * vertices.card) :
    left.card + separator.card < vertices.card := by
  have hseparator := profileSeparator_separator_card_twelfth
    G beta exponent hProfile hexponent hvertices hscale hminimum
  exact separatorChild_card_lt_of_balanced_and_twelfth
    (by omega) hbalanced hseparator

end QEC.Locality
