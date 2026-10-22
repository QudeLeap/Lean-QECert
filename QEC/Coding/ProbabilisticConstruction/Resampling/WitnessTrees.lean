import QEC.Coding.ProbabilisticConstruction.LocalLemma
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Proper witness trees and their finite partition sum

A root labeled i has at most one child of each label in its closed dependency
neighborhood. Height-bounded trees form a finite type. Their probability-weight
sum is bounded directly from the asymmetric local-lemma criterion.
-/

namespace QEC.Coding.ProbabilisticConstruction.Resampling

open scoped BigOperators

universe u

variable {I : Type u} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

/-- A resampling of the same event is also a dependency. -/
def closedNeighbors (i : I) : Finset I := insert i (G.neighborFinset i)

@[simp] theorem mem_closedNeighbors (i j : I) :
    j ∈ closedNeighbors G i ↔ j = i ∨ G.Adj i j := by
  simp [closedNeighbors]

/-- Trees of height strictly below h, with the root label in the type.
Each optional child slot is indexed by its own label, so siblings are distinct. -/
def WitnessTree : ℕ → I → Type u
  | 0, _ => PEmpty
  | h + 1, i => ∀ j : closedNeighbors G i, Option (WitnessTree h j)

instance witnessTreeFintype (h : ℕ) (i : I) : Fintype (WitnessTree G h i) := by
  induction h generalizing i with
  | zero => exact inferInstanceAs (Fintype PEmpty)
  | succ h ih =>
    letI (j : I) : Fintype (WitnessTree G h j) := ih j
    exact inferInstanceAs (Fintype (∀ j : closedNeighbors G i, Option (WitnessTree G h j)))

/-- Product of the event probabilities at all nodes of a proper witness tree. -/
noncomputable def witnessWeight (p : I → ℝ) : (h : ℕ) → (i : I) → WitnessTree G h i → ℝ
  | 0, _, t => PEmpty.elim t
  | h + 1, i, t => p i * ∏ j : closedNeighbors G i,
      (t j).elim 1 (witnessWeight p h j)

/-- Sum over all proper trees of the given bounded height and root label. -/
noncomputable def witnessPartition (p : I → ℝ) (h : ℕ) (i : I) : ℝ :=
  ∑ t : WitnessTree G h i, witnessWeight G p h i t

@[simp] theorem witnessPartition_zero (p : I → ℝ) (i : I) :
    witnessPartition G p 0 i = 0 := by
  unfold witnessPartition
  apply Finset.sum_eq_zero
  intro t ht
  exact PEmpty.elim t

theorem witnessPartition_succ (p : I → ℝ) (h : ℕ) (i : I) :
    witnessPartition G p (h + 1) i =
      p i * ∏ j ∈ closedNeighbors G i, (1 + witnessPartition G p h j) := by
  classical
  change (∑ t : (∀ j : closedNeighbors G i, Option (WitnessTree G h j)),
    p i * ∏ j : closedNeighbors G i, (t j).elim 1 (witnessWeight G p h j)) = _
  rw [← Finset.mul_sum]
  rw [← Fintype.prod_sum (fun (j : closedNeighbors G i)
    (child : Option (WitnessTree G h j)) => child.elim 1 (witnessWeight G p h j))]
  congr 1
  simpa only [Fintype.sum_option, Option.elim_none, Option.elim_some,
    witnessPartition] using
    (Finset.prod_coe_sort (closedNeighbors G i) (fun j => 1 +
      ∑ t : WitnessTree G h j, witnessWeight G p h j t))

theorem witnessWeight_nonneg (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (h : ℕ) (i : I) (t : WitnessTree G h i) : 0 ≤ witnessWeight G p h i t := by
  induction h generalizing i with
  | zero => exact PEmpty.elim t
  | succ h ih =>
    apply mul_nonneg (hp i)
    apply Finset.prod_nonneg
    intro j hj
    cases hc : t j with
    | none => simp [hc]
    | some child => exact ih j child

theorem witnessPartition_nonneg (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (h : ℕ) (i : I) : 0 ≤ witnessPartition G p h i :=
  Finset.sum_nonneg (fun t _ => witnessWeight_nonneg G p hp h i t)

/-- The resampling expectation budget associated with an asymmetric LLL weight. -/
noncomputable def resamplingBudget (x : I → ℝ) (i : I) : ℝ := x i / (1 - x i)

theorem resamplingBudget_nonneg (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i < 1) (i : I) : 0 ≤ resamplingBudget x i :=
  div_nonneg (hx0 i) (sub_pos.mpr (hx1 i)).le

theorem one_add_budget_mul (x : I → ℝ) (hx1 : ∀ i, x i < 1) (i : I) :
    (1 + resamplingBudget x i) * (1 - x i) = 1 := by
  unfold resamplingBudget
  field_simp [(sub_pos.mpr (hx1 i)).ne']
  ring

/-- The finite branching recurrence is bounded by the explicit asymmetric budget. -/
theorem branching_budget_bound (p x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i < 1)
    (hcrit : ∀ i, p i ≤ x i * ∏ j ∈ G.neighborFinset i, (1 - x j)) (i : I) :
    p i * ∏ j ∈ closedNeighbors G i, (1 + resamplingBudget x j) ≤
      resamplingBudget x i := by
  have hnn : ∀ j, 0 ≤ 1 + resamplingBudget x j := fun j =>
    add_nonneg (by norm_num) (resamplingBudget_nonneg x hx0 hx1 j)
  have hcancel : (∏ j ∈ G.neighborFinset i, (1 - x j)) *
      (∏ j ∈ G.neighborFinset i, (1 + resamplingBudget x j)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro j hj
    simpa [mul_comm] using one_add_budget_mul x hx1 j
  have hi : i ∉ G.neighborFinset i := by simp
  have heq : (x i * ∏ j ∈ G.neighborFinset i, (1 - x j)) *
      (∏ j ∈ closedNeighbors G i, (1 + resamplingBudget x j)) =
      resamplingBudget x i := by
    rw [closedNeighbors, Finset.prod_insert hi]
    calc
      (x i * ∏ j ∈ G.neighborFinset i, (1 - x j)) *
          ((1 + resamplingBudget x i) *
            ∏ j ∈ G.neighborFinset i, (1 + resamplingBudget x j)) =
          (x i * (1 + resamplingBudget x i)) *
            ((∏ j ∈ G.neighborFinset i, (1 - x j)) *
              ∏ j ∈ G.neighborFinset i, (1 + resamplingBudget x j)) := by ring
      _ = resamplingBudget x i := by
        rw [hcancel, mul_one]
        unfold resamplingBudget
        field_simp [(sub_pos.mpr (hx1 i)).ne']
        ring
  exact heq ▸ mul_le_mul_of_nonneg_right (hcrit i)
    (Finset.prod_nonneg (fun j _ => hnn j))

/-- Proper witness trees have a uniformly bounded total probability weight. -/
theorem witnessPartition_le_budget (p x : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hcrit : ∀ i, p i ≤ x i * ∏ j ∈ G.neighborFinset i, (1 - x j))
    (h : ℕ) (i : I) : witnessPartition G p h i ≤ resamplingBudget x i := by
  induction h generalizing i with
  | zero => simpa using resamplingBudget_nonneg x hx0 hx1 i
  | succ h ih =>
    rw [witnessPartition_succ]
    apply le_trans _ (branching_budget_bound G p x hx0 hx1 hcrit i)
    apply mul_le_mul_of_nonneg_left _ (hp i)
    apply Finset.prod_le_prod
    · intro j hj; exact add_nonneg (by norm_num) (witnessPartition_nonneg G p hp h j)
    · intro j hj; exact add_le_add le_rfl (ih j)

end QEC.Coding.ProbabilisticConstruction.Resampling
