import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Exponential moment criteria for the LPS spectral bound

The proof of the LPS Ramanujan theorem bounds spectral moments at every
exponential rate strictly above the tree spectral radius.  This file records
the elementary analytic endgame: such bounds force every individual real
spectral value into the closed limiting interval.  The statements are kept
independent of the graph construction so that the later theta-series count
only has to supply the moment estimate.
-/

open Filter Asymptotics

namespace QEC.Coding.TannerLiftedProduct

/-- A real exponential sequence can be big-O of another positive
exponential sequence only when its base is no larger. -/
theorem abs_le_of_pow_isBigO
    {x r : ℝ} (hr : 0 < r)
    (h : (fun n : ℕ => |x| ^ n) =O[atTop]
      fun n : ℕ => r ^ n) :
    |x| ≤ r := by
  by_contra hxr
  have hrx : r < |x| := lt_of_not_ge hxr
  have hlittle : (fun n : ℕ => r ^ n) =o[atTop]
      fun n : ℕ => |x| ^ n :=
    isLittleO_pow_pow_of_lt_left hr.le hrx
  have hfrequent : ∃ᶠ n : ℕ in atTop, r ^ n ≠ 0 :=
    ((eventually_gt_atTop 0).mono fun n _hn =>
      pow_ne_zero n hr.ne').frequently
  exact hlittle.not_isBigO hfrequent h

/-- If `|x|^n` has every exponential upper rate strictly above `r`, then
`|x| ≤ r`.  This is the closed-boundary passage used in the LPS moment
argument. -/
theorem abs_le_of_forall_gt_pow_isBigO
    {x r : ℝ} (hr : 0 ≤ r)
    (h : ∀ s : ℝ, r < s →
      (fun n : ℕ => |x| ^ n) =O[atTop]
        fun n : ℕ => s ^ n) :
    |x| ≤ r := by
  by_contra hxr
  have hrx : r < |x| := lt_of_not_ge hxr
  let s := (r + |x|) / 2
  have hrs : r < s := by
    dsimp [s]
    linarith
  have hsx : s < |x| := by
    dsimp [s]
    linarith
  have hs : 0 < s := hr.trans_lt hrs
  exact (not_le_of_gt hsx) (abs_le_of_pow_isBigO hs (h s hrs))

/-- An even-power version of the preceding criterion.  This is convenient
for self-adjoint adjacency spectra because all summands in an even spectral
moment are nonnegative. -/
theorem abs_le_of_forall_gt_evenPow_isBigO
    {x r : ℝ} (hr : 0 ≤ r)
    (h : ∀ s : ℝ, r < s →
      (fun n : ℕ => |x| ^ (2 * n)) =O[atTop]
        fun n : ℕ => s ^ (2 * n)) :
    |x| ≤ r := by
  by_contra hxr
  have hrx : r < |x| := lt_of_not_ge hxr
  let s := (r + |x|) / 2
  have hrs : r < s := by
    dsimp [s]
    linarith
  have hsx : s < |x| := by
    dsimp [s]
    linarith
  have hs : 0 < s := hr.trans_lt hrs
  have hsq : 0 < s ^ 2 := sq_pos_of_pos hs
  have hO : (fun n : ℕ => (|x| ^ 2) ^ n) =O[atTop]
      fun n : ℕ => (s ^ 2) ^ n := by
    simpa [pow_mul] using h s hrs
  have hO' : (fun n : ℕ => |(|x| ^ 2)| ^ n) =O[atTop]
      fun n : ℕ => (s ^ 2) ^ n := by
    simpa [abs_of_nonneg (sq_nonneg |x|)] using hO
  have hle := abs_le_of_pow_isBigO (x := |x| ^ 2) hsq hO'
  rw [abs_of_nonneg (sq_nonneg |x|)] at hle
  nlinarith [sq_nonneg (|x| - s)]

/-- A big-O bound for a finite nonnegative even spectral moment controls
each individual spectral value. -/
theorem abs_le_of_evenMoment_isBigO
    {I : Type*} [Fintype I] (eigenvalue : I → ℝ)
    {r : ℝ} (hr : 0 ≤ r)
    (hMoment : ∀ s : ℝ, r < s →
      (fun n : ℕ => ∑ i, |eigenvalue i| ^ (2 * n)) =O[atTop]
        fun n : ℕ => s ^ (2 * n)) :
    ∀ i, |eigenvalue i| ≤ r := by
  classical
  intro i
  apply abs_le_of_forall_gt_evenPow_isBigO hr
  intro s hrs
  have hTerm : (fun n : ℕ => |eigenvalue i| ^ (2 * n)) =O[atTop]
      fun n : ℕ => ∑ j, |eigenvalue j| ^ (2 * n) := by
    apply isBigO_of_le atTop
    intro n
    rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _),
      Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ =>
        pow_nonneg (abs_nonneg _) _)]
    exact Finset.single_le_sum
      (fun j _hj => pow_nonneg (abs_nonneg (eigenvalue j)) _)
      (Finset.mem_univ i)
  exact hTerm.trans (hMoment s hrs)

end QEC.Coding.TannerLiftedProduct
