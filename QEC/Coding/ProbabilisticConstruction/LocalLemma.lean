import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

/-!
# Finite measurable asymmetric local lemma

The generic theorem uses joint independence from the sigma algebra of all
nonneighbors. Its product-variable specialization derives that independence
from disjoint coordinate supports, without restricting the coordinate laws to
finite or discrete sample spaces.
-/

namespace QEC.Coding.ProbabilisticConstruction

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]

/-- Avoid every bad event in a finite family of indices. -/
def avoid (B : I → Set Ω) (S : Finset I) : Set Ω :=
  {ω | ∀ i ∈ S, ω ∉ B i}

@[simp] theorem avoid_empty (B : I → Set Ω) : avoid B ∅ = Set.univ := by
  ext ω
  simp [avoid]

@[simp] theorem avoid_insert (B : I → Set Ω) (i : I) (S : Finset I) :
    avoid B (insert i S) = avoid B S \ B i := by
  ext ω
  simp only [avoid, Set.mem_setOf_eq, Finset.mem_insert, forall_eq_or_imp,
    Set.mem_diff]
  tauto

theorem avoid_union (B : I → Set Ω) (S T : Finset I) :
    avoid B (S ∪ T) = avoid B S ∩ avoid B T := by
  ext ω
  simp [avoid, or_imp, forall_and]

theorem avoid_antitone (B : I → Set Ω) {S T : Finset I} (h : S ⊆ T) :
    avoid B T ⊆ avoid B S := by
  intro ω hω i hi
  exact hω i (h hi)

theorem measurableSet_avoid (B : I → Set Ω) (hB : ∀ i, MeasurableSet (B i))
    (S : Finset I) : MeasurableSet (avoid B S) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => rw [avoid_insert]; exact ih.diff (hB i)

/-- Full joint nonneighbor independence, not just pairwise event independence. -/
def HasDependencyGraph (μ : Measure Ω) (B : I → Set Ω) (G : SimpleGraph I) : Prop :=
  ∀ i, Indep (MeasurableSpace.generateFrom {B i})
    (MeasurableSpace.generateFrom
      {E | ∃ j, j ≠ i ∧ ¬ G.Adj i j ∧ E = B j}) μ

theorem HasDependencyGraph.factor_avoid {μ : Measure Ω} {B : I → Set Ω}
    {G : SimpleGraph I} (h : HasDependencyGraph μ B G) (i : I) (S : Finset I)
    (hS : ∀ j ∈ S, j ≠ i ∧ ¬ G.Adj i j) :
    μ.real (B i ∩ avoid B S) = μ.real (B i) * μ.real (avoid B S) := by
  have hleft : MeasurableSet[MeasurableSpace.generateFrom {B i}] (B i) :=
    MeasurableSpace.measurableSet_generateFrom (by simp)
  have hright : MeasurableSet[MeasurableSpace.generateFrom
      {E | ∃ j, j ≠ i ∧ ¬ G.Adj i j ∧ E = B j}] (avoid B S) := by
    revert hS
    induction S using Finset.induction_on with
    | empty => intro hS; simp
    | @insert j S hj ih =>
      intro hS
      rw [avoid_insert]
      exact (ih (fun k hk => hS k (Finset.mem_insert_of_mem hk))).diff
        (MeasurableSpace.measurableSet_generateFrom
          ⟨j, (hS j (Finset.mem_insert_self _ _)).1,
            (hS j (Finset.mem_insert_self _ _)).2, rfl⟩)
  have hf := ((h i).indepSet_of_measurableSet hleft hright).measure_inter_eq_mul
  simpa only [Measure.real, ENNReal.toReal_mul] using congrArg ENNReal.toReal hf

section MeasureBounds

variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (B : I → Set Ω) (hB : ∀ i, MeasurableSet (B i))
variable (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)

include hB

/-- Insert one avoided event using a cross-multiplied conditional bound. -/
theorem avoid_insert_lower (i : I) (S : Finset I)
    (hc : μ.real (B i ∩ avoid B S) ≤ x i * μ.real (avoid B S)) :
    (1 - x i) * μ.real (avoid B S) ≤ μ.real (avoid B (insert i S)) := by
  have he := measureReal_inter_add_diff (μ := μ) (s := avoid B S) (hB i)
  rw [Set.inter_comm, ← avoid_insert] at he
  nlinarith

include hx1 in
/-- Multiply the one-event bounds along a finite extension of a conditioning set. -/
theorem avoid_union_lower (T U : Finset I)
    (hc : ∀ A ⊆ U, ∀ i ∈ U, i ∉ A →
      μ.real (B i ∩ avoid B (T ∪ A)) ≤ x i * μ.real (avoid B (T ∪ A))) :
    (∏ i ∈ U, (1 - x i)) * μ.real (avoid B T) ≤ μ.real (avoid B (T ∪ U)) := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert i U hi ih =>
    have ih' := ih (fun A hA j hj hjA =>
      hc A (hA.trans (Finset.subset_insert _ _)) j (Finset.mem_insert_of_mem hj) hjA)
    have hs := avoid_insert_lower μ B hB x i (T ∪ U)
      (hc U (Finset.subset_insert _ _) i (Finset.mem_insert_self _ _) hi)
    rw [Finset.prod_insert hi]
    have hm := mul_le_mul_of_nonneg_left ih' (sub_nonneg.mpr (hx1 i).le)
    calc
      ((1 - x i) * ∏ j ∈ U, (1 - x j)) * μ.real (avoid B T)
          ≤ (1 - x i) * μ.real (avoid B (T ∪ U)) := by simpa [mul_assoc] using hm
      _ ≤ μ.real (avoid B (T ∪ insert i U)) := by
        simpa [Finset.union_insert] using hs

variable (G : SimpleGraph I) [DecidableRel G.Adj]
variable (hdep : HasDependencyGraph μ B G)
variable (hcrit : ∀ i, μ.real (B i) ≤ x i * ∏ j ∈ G.neighborFinset i, (1 - x j))

include hx0 hx1 hdep hcrit

/-- The asymmetric local lemma's conditional estimate, without division. -/
theorem localLemma_conditional (S : Finset I) (i : I) (hi : i ∉ S) :
    μ.real (B i ∩ avoid B S) ≤ x i * μ.real (avoid B S) := by
  induction S using Finset.strongInductionOn generalizing i with
  | _ S ih =>
    let T := S.filter (fun j => ¬ G.Adj i j)
    let U := S.filter (fun j => G.Adj i j)
    have hTU : T ∪ U = S := by ext j; simp [T, U]; tauto
    have hT : T ⊆ S := Finset.filter_subset _ _
    have hU : U ⊆ S := Finset.filter_subset _ _
    have hfactor := hdep.factor_avoid i T (by
      intro j hj
      have hj' := Finset.mem_filter.mp hj
      exact ⟨fun he => hi (he ▸ hj'.1), hj'.2⟩)
    have hext := avoid_union_lower μ B hB x hx1 T U (by
      intro A hA j hj hjA
      have hjU := Finset.mem_filter.mp hj
      have hsubset : T ∪ A ⊆ S := Finset.union_subset hT (hA.trans hU)
      have hjnot : j ∉ T ∪ A := by
        simp only [Finset.mem_union, not_or]
        exact ⟨fun hjT => (Finset.mem_filter.mp hjT).2 hjU.2, hjA⟩
      have hstrict : T ∪ A ⊂ S :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, fun he => hjnot (he.symm ▸ hjU.1)⟩
      exact ih (T ∪ A) hstrict j hjnot)
    rw [hTU] at hext
    have hprod : (∏ j ∈ G.neighborFinset i, (1 - x j)) ≤ ∏ j ∈ U, (1 - x j) := by
      apply Finset.prod_le_prod_of_subset_of_le_one
      · intro j hj
        simpa using (Finset.mem_filter.mp hj).2
      · intro j hj; exact sub_nonneg.mpr (hx1 j).le
      · intro j hj hjU; linarith [hx0 j]
    have hbound : μ.real (B i) ≤ x i * ∏ j ∈ U, (1 - x j) :=
      (hcrit i).trans (mul_le_mul_of_nonneg_left hprod (hx0 i))
    calc
      μ.real (B i ∩ avoid B S) ≤ μ.real (B i ∩ avoid B T) :=
        measureReal_mono (fun _ hω => ⟨hω.1, avoid_antitone B hT hω.2⟩)
      _ = μ.real (B i) * μ.real (avoid B T) := hfactor
      _ ≤ (x i * ∏ j ∈ U, (1 - x j)) * μ.real (avoid B T) :=
        mul_le_mul_of_nonneg_right hbound measureReal_nonneg
      _ ≤ x i * μ.real (avoid B S) := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hext (hx0 i)

/-- Avoidance has the asymmetric product lower bound. -/
theorem localLemma_product_lower (S : Finset I) :
    (∏ i ∈ S, (1 - x i)) ≤ μ.real (avoid B S) := by
  have h := avoid_union_lower μ B hB x hx1 ∅ S (by
    intro A hA i hi hiA
    simpa using localLemma_conditional μ B hB x hx0 hx1 G hdep hcrit A i hiA)
  simpa using h

/-- The good event has strictly positive probability, also for an empty index type. -/
theorem localLemma_positive (S : Finset I) : 0 < μ.real (avoid B S) :=
  lt_of_lt_of_le (Finset.prod_pos (fun i _ => sub_pos.mpr (hx1 i)))
    (localLemma_product_lower μ B hB x hx0 hx1 G hdep hcrit S)

/-- There is a point avoiding every bad event. -/
theorem localLemma_exists : ∃ ω, ∀ i, ω ∉ B i := by
  obtain ⟨ω, hω⟩ := nonempty_of_measureReal_ne_zero
    (localLemma_positive μ B hB x hx0 hx1 G hdep hcrit Finset.univ).ne'
  exact ⟨ω, fun i => hω i (Finset.mem_univ _)⟩

end MeasureBounds

section ProductVariables

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]

/-- The actual overlap graph of finite coordinate supports. -/
def supportGraph (vars : I → Finset V) : SimpleGraph I where
  Adj i j := i ≠ j ∧ ¬ Disjoint (vars i) (vars j)
  symm := by constructor; intro i j h; exact ⟨h.1.symm, fun hd => h.2 hd.symm⟩
  loopless := by constructor; intro i h; exact h.1 rfl

instance (vars : I → Finset V) : DecidableRel (supportGraph vars).Adj := by
  unfold supportGraph
  infer_instance

/-- A local measurable predicate pulled back along its actual coordinates. -/
def localEvent (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
    (i : I) : Set (∀ v, X v) :=
  (vars i).restrict ⁻¹' bad i

theorem measurableSet_localEvent (vars : I → Finset V)
    (bad : ∀ i, Set (∀ v : vars i, X v)) (hbad : ∀ i, MeasurableSet (bad i))
    (i : I) : MeasurableSet (localEvent vars bad i) :=
  (hbad i).preimage (vars i).measurable_restrict

/-- Independent coordinate laws derive joint nonneighbor independence of all local events.
The complement tuple contains every nonneighbor's coordinates simultaneously. -/
theorem product_hasDependencyGraph (ν : ∀ v, Measure (X v))
    [∀ v, IsProbabilityMeasure (ν v)] (vars : I → Finset V)
    (bad : ∀ i, Set (∀ v : vars i, X v)) (hbad : ∀ i, MeasurableSet (bad i)) :
    HasDependencyGraph (Measure.pi ν) (localEvent vars bad) (supportGraph vars) := by
  intro i
  let C : Finset V := (vars i)ᶜ
  have hcoords : iIndepFun (fun v (ω : ∀ v, X v) => ω v) (Measure.pi ν) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hind := hcoords.indepFun_finset (vars i) C (by
    apply Finset.disjoint_left.mpr
    intro v hv hvC
    exact Finset.mem_compl.mp hvC hv)
    (fun v => measurable_pi_apply v)
  apply indep_of_indep_of_le hind
  · apply MeasurableSpace.generateFrom_le
    intro E hE
    have he : E = localEvent vars bad i := Set.mem_singleton_iff.mp hE
    subst E
    exact MeasurableSpace.measurableSet_comap.mpr ⟨bad i, hbad i, rfl⟩
  · apply MeasurableSpace.generateFrom_le
    intro E hE
    obtain ⟨j, hji, hnon, rfl⟩ := hE
    have hdisj : Disjoint (vars i) (vars j) := by
      by_contra h
      exact hnon ⟨Ne.symm hji, h⟩
    have hsub : vars j ⊆ C := by
      intro v hv
      apply Finset.mem_compl.mpr
      intro hvi
      exact Finset.disjoint_left.mp hdisj hvi hv
    refine MeasurableSpace.measurableSet_comap.mpr
      ⟨(Finset.restrict₂ hsub) ⁻¹' bad j,
        (hbad j).preimage (Finset.measurable_restrict₂ hsub), ?_⟩
    rfl

/-- Product-variable asymmetric LLL: independence is proved from the local supports. -/
theorem product_localLemma (ν : ∀ v, Measure (X v))
    [∀ v, IsProbabilityMeasure (ν v)] (vars : I → Finset V)
    (bad : ∀ i, Set (∀ v : vars i, X v)) (hbad : ∀ i, MeasurableSet (bad i))
    (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hcrit : ∀ i, (Measure.pi ν).real (localEvent vars bad i) ≤
      x i * ∏ j ∈ (supportGraph vars).neighborFinset i, (1 - x j)) :
    (∀ S, (∏ i ∈ S, (1 - x i)) ≤ (Measure.pi ν).real (avoid (localEvent vars bad) S)) ∧
    (∀ S, 0 < (Measure.pi ν).real (avoid (localEvent vars bad) S)) ∧
    (∀ S i, i ∉ S → (Measure.pi ν).real (localEvent vars bad i ∩
      avoid (localEvent vars bad) S) ≤ x i * (Measure.pi ν).real
        (avoid (localEvent vars bad) S)) ∧
    (∃ ω, ∀ i, ω ∉ localEvent vars bad i) := by
  have hd := product_hasDependencyGraph ν vars bad hbad
  have hm := measurableSet_localEvent vars bad hbad
  exact ⟨localLemma_product_lower _ _ hm x hx0 hx1 _ hd hcrit,
    localLemma_positive _ _ hm x hx0 hx1 _ hd hcrit,
    localLemma_conditional _ _ hm x hx0 hx1 _ hd hcrit,
    localLemma_exists _ _ hm x hx0 hx1 _ hd hcrit⟩

end ProductVariables

end QEC.Coding.ProbabilisticConstruction
