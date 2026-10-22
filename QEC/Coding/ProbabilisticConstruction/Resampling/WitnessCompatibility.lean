import QEC.Coding.ProbabilisticConstruction.Resampling.HistoryTimes
import QEC.Coding.ProbabilisticConstruction.Resampling.TableProbability

/-!
# Witness compatibility with the independent random table

Nodes that share a variable must have distinct depths. This property is proved
for actual history witnesses. Trees without the property have empty compatibility
events, so bounding by the sum of all proper-tree weights remains valid.
-/

namespace QEC.Coding.ProbabilisticConstruction.Resampling

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)

/-- Depth separates all nodes whose local events read a common variable. -/
def DistinctVariableDepth (root : I) (P : Finset (List I)) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, ∀ v ∈ vars (pathLabel root p),
    v ∈ vars (pathLabel root q) → p.length = q.length → p = q

theorem historyWitness_distinctVariableDepth (root : I) (L : List I) :
    DistinctVariableDepth vars root (historyWitness (supportGraph vars) root L) := by
  intro p hp q hq v hpv hqv hd
  exact historyWitness_shared_depth_injective vars root L p q hp hq v hpv hqv hd

/-- Number of earlier (deeper) uses of a variable in a finite witness. -/
def variableRank (root : I) (P : Finset (List I)) (p : List I) (v : V) : ℕ :=
  (P.filter (fun q => v ∈ vars (pathLabel root q) ∧ p.length < q.length)).card

theorem variableRank_strict (root : I) (P : Finset (List I))
    (p q : List I) (hq : q ∈ P) (v : V) (hqv : v ∈ vars (pathLabel root q))
    (hdepth : p.length < q.length) :
    variableRank vars root P q v < variableRank vars root P p v := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro r hr
    obtain ⟨hrP, hrv, hqr⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hrP, hrv, lt_trans hdepth hqr⟩
  · intro he
    have hm : q ∈ P.filter (fun r => v ∈ vars (pathLabel root r) ∧ p.length < r.length) :=
      Finset.mem_filter.mpr ⟨hq, hqv, hdepth⟩
    rw [← he] at hm
    exact (Finset.mem_filter.mp hm).2.2.false

theorem variableRank_injective (root : I) (P : Finset (List I))
    (hd : DistinctVariableDepth vars root P) (p q : List I) (hp : p ∈ P) (hq : q ∈ P)
    (v : V) (hpv : v ∈ vars (pathLabel root p)) (hqv : v ∈ vars (pathLabel root q))
    (he : variableRank vars root P p v = variableRank vars root P q v) : p = q := by
  apply hd p hp q hq v hpv hqv
  have hle : p.length ≤ q.length := by
    by_contra h
    have hh := variableRank_strict vars root P q p hp v hpv (Nat.lt_of_not_ge h)
    omega
  have hge : q.length ≤ p.length := by
    by_contra h
    have hh := variableRank_strict vars root P p q hq v hqv (Nat.lt_of_not_ge h)
    omega
  exact Nat.le_antisymm hle hge

/-- Variable ranks assign genuinely distinct table addresses to all node-variable slots. -/
theorem witness_address_injective (root : I) (P : Finset (List I))
    (hd : DistinctVariableDepth vars root P) :
    Function.Injective (fun s : (p : P) × vars (pathLabel root p.val) =>
      (s.2.val, variableRank vars root P s.1.val s.2.val)) := by
  intro a b he
  have hv : a.2.val = b.2.val := congrArg Prod.fst he
  have hr := congrArg Prod.snd he
  have hpb : a.2.val ∈ vars (pathLabel root b.1.val) := hv.symm ▸ b.2.property
  have hp : a.1 = b.1 := Subtype.ext (variableRank_injective vars root P hd
    a.1.val b.1.val a.1.property b.1.property a.2.val a.2.property hpb (by simpa [hv] using hr))
  cases a with
  | mk p v =>
    cases b with
    | mk q w =>
      dsimp only at hp
      subst q
      have hw : v = w := Subtype.ext hv
      subst w
      rfl

variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (bad : ∀ i, Set (∀ v : vars i, X v))

/-- Each node tests its event on the table entries determined by its variable ranks. -/
def compatible (root : I) (P : Finset (List I)) : Set (Table (X := X)) :=
  {R | DistinctVariableDepth vars root P ∧
    ∀ p : P, familyRead (fun q : P => vars (pathLabel root q.val))
      (fun q v => variableRank vars root P q.val v.val) R p ∈ bad (pathLabel root p.val)}

theorem measurableSet_compatible (hbad : ∀ i, MeasurableSet (bad i))
    (root : I) (P : Finset (List I)) : MeasurableSet (compatible vars bad root P) := by
  classical
  by_cases hd : DistinctVariableDepth vars root P
  · have hm := measurable_familyRead (X := X) (fun q : P => vars (pathLabel root q.val))
      (fun q v => variableRank vars root P q.val v.val)
    have he : compatible vars bad root P =
        familyRead (fun q : P => vars (pathLabel root q.val))
          (fun q v => variableRank vars root P q.val v.val) ⁻¹'
            Set.univ.pi (fun q : P => bad (pathLabel root q.val)) := by
      ext R; simp [compatible, hd]
    rw [he]
    exact (MeasurableSet.univ_pi (fun q => hbad _)).preimage hm
  · have he : compatible vars bad root P = ∅ := by ext R; simp [compatible, hd]
    rw [he]; exact MeasurableSet.empty

/-- A compatible witness has at most the product probability of its labeled events. -/
theorem compatibility_probability_le (hbad : ∀ i, MeasurableSet (bad i))
    (root : I) (P : Finset (List I)) :
    tableLaw ν (compatible vars bad root P) ≤
      ∏ p : P, (Measure.pi ν) (localEvent vars bad (pathLabel root p.val)) := by
  classical
  by_cases hd : DistinctVariableDepth vars root P
  · have he : compatible vars bad root P =
        {R | ∀ p : P, familyRead (fun q : P => vars (pathLabel root q.val))
          (fun q v => variableRank vars root P q.val v.val) R p ∈ bad (pathLabel root p.val)} := by
      ext R; simp [compatible, hd]
    rw [he, table_tests_probability ν _ _ (witness_address_injective vars root P hd)
      _ (fun p => hbad _)]
    apply le_of_eq
    apply Finset.prod_congr rfl
    intro p hp
    exact (local_probability_eq ν _ _ (hbad _)).symm
  · have he : compatible vars bad root P = ∅ := by ext R; simp [compatible, hd]
    simp [he]

end QEC.Coding.ProbabilisticConstruction.Resampling
