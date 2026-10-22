import QEC.Coding.ProbabilisticConstruction.Resampling.ExecutionWitness
import Mathlib.Data.ENNReal.BigOperators

/-! # Probability weights of the finite proper-tree family -/

namespace QEC.Coding.ProbabilisticConstruction.Resampling

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

/-- Recursive tree weight is the product over its distinct path-addressed nodes. -/
theorem witnessWeight_eq_prod_paths (p : I → ℝ) (h : ℕ) (i : I)
    (t : WitnessTree G h i) :
    witnessWeight G p h i t = ∏ q ∈ witnessPaths G h i t, p (pathLabel i q) := by
  classical
  induction h generalizing i with
  | zero => exact PEmpty.elim t
  | succ h ih =>
    let children : closedNeighbors G i → Finset (List I) := fun j =>
      match t j with
      | none => ∅
      | some child => (witnessPaths G h j child).image (List.cons j.val)
    have hn : [] ∉ Finset.univ.biUnion children := by
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists]
      intro j
      cases hc : t j <;> simp [children, hc]
    have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset (closedNeighbors G i))) children := by
      intro j hj k hk hjk
      apply Finset.disjoint_left.mpr
      intro q hqj hqk
      cases hcj : t j with
      | none => simp [children, hcj] at hqj
      | some tj =>
        cases hck : t k with
        | none => simp [children, hck] at hqk
        | some tk =>
          obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp (by simpa [children, hcj] using hqj)
          obtain ⟨b, hb, heb⟩ := Finset.mem_image.mp (by simpa [children, hck] using hqk)
          exact hjk (Subtype.ext (List.cons.inj (hea.trans heb.symm)).1)
    change p i * (∏ j, (t j).elim 1 (witnessWeight G p h j)) =
      ∏ q ∈ insert [] (Finset.univ.biUnion children), p (pathLabel i q)
    rw [Finset.prod_insert hn, Finset.prod_biUnion hd]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    cases hc : t j with
    | none => simp [children, hc]
    | some child =>
      simp only [hc, Option.elim_some, children]
      rw [Finset.prod_image]
      · exact ih j child
      · intro a ha b hb he
        exact (List.cons.inj he).2

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (bad : ∀ i, Set (∀ v : vars i, X v))

/-- Actual real event probabilities under the finite coordinate product law. -/
noncomputable def eventProbability (i : I) : ℝ :=
  ((Measure.pi ν) (localEvent vars bad i)).toReal

theorem eventProbability_nonneg (i : I) : 0 ≤ eventProbability vars ν bad i :=
  ENNReal.toReal_nonneg

theorem ofReal_eventProbability (i : I) :
    ENNReal.ofReal (eventProbability vars ν bad i) =
      (Measure.pi ν) (localEvent vars bad i) :=
  ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- Every tree's compatibility probability is bounded by its derived product weight. -/
theorem tree_compatibility_probability_le (hbad : ∀ i, MeasurableSet (bad i))
    (h : ℕ) (i : I) (t : WitnessTree (supportGraph vars) h i) :
    tableLaw ν (compatible vars bad i (witnessPaths (supportGraph vars) h i t)) ≤
      ENNReal.ofReal (witnessWeight (supportGraph vars) (eventProbability vars ν bad) h i t) := by
  have hb := compatibility_probability_le vars ν bad hbad i
    (witnessPaths (supportGraph vars) h i t)
  rw [witnessWeight_eq_prod_paths, ENNReal.ofReal_prod_of_nonneg
    (fun q _ => eventProbability_nonneg vars ν bad _)]
  simp only [ofReal_eventProbability]
  exact hb.trans_eq (Finset.prod_coe_sort
    (witnessPaths (supportGraph vars) h i t)
    (fun p => (Measure.pi ν) (localEvent vars bad (pathLabel i p))))

end QEC.Coding.ProbabilisticConstruction.Resampling
