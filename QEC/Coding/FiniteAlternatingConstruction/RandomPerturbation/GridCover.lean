import QEC.Coding.ProbabilisticConstruction.SphericalCap.Measure
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Int.Interval

/-! # Explicit finite unit-ball covers of integer-radius Euclidean balls -/

namespace QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap

abbrev GridCoordinate (K : ℕ) := ↥(Finset.Icc (-(K : ℤ)) (K : ℤ))
abbrev Grid (K : ℕ) := Fin 3 → GridCoordinate K

noncomputable def gridPoint (K : ℕ) (g : Grid K) : Space :=
  WithLp.toLp 2 (fun i => ((g i).val : ℝ))

theorem gridCoordinate_card (K : ℕ) : Fintype.card (GridCoordinate K) = 2*K+1 := by
  simp [GridCoordinate,Int.card_Icc]
  omega

theorem grid_card (K : ℕ) : Fintype.card (Grid K) = (2*K+1)^3 := by
  simp only [Grid,Fintype.card_fun,gridCoordinate_card,Fintype.card_fin]

/-- Nearest integer coordinates of a point in an integer-radius ball stay in the cube. -/
theorem round_mem_grid (K : ℕ) (x : ℝ) (hx : |x| ≤ K) :
    round x ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
  have he := abs_sub_round x
  obtain ⟨hxlo,hxhi⟩ := abs_le.mp hx
  obtain ⟨helo,hehi⟩ := abs_le.mp he
  have hu : (round x : ℝ) < (K : ℝ)+1 := by linarith
  have hl : -(K : ℝ)-1 < (round x : ℝ) := by linarith
  have hu' : round x < (K : ℤ)+1 := by exact_mod_cast hu
  have hl' : -(K : ℤ)-1 < round x := by exact_mod_cast hl
  simp only [Finset.mem_Icc]
  omega

noncomputable def nearestGrid (K : ℕ) (p : Space) (hp : ‖p‖ ≤ K) : Grid K :=
  fun i => ⟨round (p i), round_mem_grid K (p i)
    (by simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le p i).trans hp)⟩

theorem nearestGrid_dist (K : ℕ) (p : Space) (hp : ‖p‖ ≤ K) :
    dist p (gridPoint K (nearestGrid K p hp)) ≤ 1 := by
  have hcoord (i : Fin 3) : (p i - (round (p i) : ℝ))^2 ≤ (1/2 : ℝ)^2 := by
    have h := mul_self_le_mul_self (abs_nonneg (p i - (round (p i) : ℝ)))
      (abs_sub_round (p i))
    simpa only [← pow_two, sq_abs] using h
  have hsq : ‖p-gridPoint K (nearestGrid K p hp)‖^2 ≤ (3 : ℝ)/4 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i : Fin 3, (p i - (round (p i) : ℝ))^2) ≤ 3/4
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    have h0 := hcoord 0
    have h1 := hcoord 1
    have h2 := hcoord 2
    norm_num at h0 h1 h2 ⊢
    linarith
  rw [dist_eq_norm]
  have hn := norm_nonneg (p-gridPoint K (nearestGrid K p hp))
  nlinarith

/-- A ball of integer radius K is covered by the explicit (2K+1)^3 unit balls. -/
theorem exists_grid_cover (K : ℕ) (center p : Space) (hp : p ∈ Metric.closedBall center K) :
    ∃ g : Grid K, p ∈ Metric.closedBall (center+gridPoint K g) 1 := by
  have hn : ‖p-center‖ ≤ K := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hp
  refine ⟨nearestGrid K (p-center) hn, ?_⟩
  have h := nearestGrid_dist K (p-center) hn
  have he : p-(center+gridPoint K (nearestGrid K (p-center) hn)) =
      (p-center)-gridPoint K (nearestGrid K (p-center) hn) := by abel
  simpa only [Metric.mem_closedBall,dist_eq_norm,he] using h

/-- The approved half-scale and radius-two repair uses all 125 indexed balls. -/
theorem radius_two_grid_card : Fintype.card (Grid 2) = 125 := by
  rw [grid_card]
  norm_num

/-- Nearest-grid enlargement sends every radius-one ball into a radius-two net ball. -/
theorem unitBall_subset_radiusTwo (center net : Space) (h : dist center net ≤ 1) :
    Metric.closedBall center 1 ⊆ Metric.closedBall net 2 := by
  intro p hp
  have hp' : dist p center ≤ 1 := hp
  have ht := dist_triangle p center net
  change dist p net ≤ 2
  linarith

end QEC.Coding.BDL26RandomPerturbation
