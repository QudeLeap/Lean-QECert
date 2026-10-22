import QEC.Coding.ProbabilisticConstruction.Resampling.Termination

/-!
# Joint measurability of parameterized original resampling

The parameter changes the bad predicates, while variable supports and priority
are fixed. Every function below is the original execution, including its
specified least-clean-scan default on nonterminating tables.
-/

namespace QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory

section ParameterizedScan
variable {A W I : Type*} [MeasurableSpace A] [MeasurableSpace W]
variable [Fintype I] [LinearOrder I] [MeasurableSpace I]
variable (B : A → I → Set W) [∀ a i, DecidablePred (· ∈ B a i)]

/-- Carrying the parameter in the sample does not change the selected label. -/
theorem firstBadFrom_parameter (L : List I) (a : A) (w : W) :
    firstBadFrom (B a) L w =
      firstBadFrom (fun i => {z : A × W | z.2 ∈ B z.1 i}) L (a,w) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
      by_cases h : w ∈ B a i
      · simp only [firstBadFrom, h, Set.mem_setOf_eq, if_true]
      · simp only [firstBadFrom, h, Set.mem_setOf_eq, if_false, ih]

theorem measurable_parameterized_select
    (hB : ∀ i, MeasurableSet {z : A × W | z.2 ∈ B z.1 i}) :
    Measurable (fun z : A × W => select (B z.1) z.2) := by
  have h := measurable_firstBadFrom
    (fun i => {z : A × W | z.2 ∈ B z.1 i}) hB (Finset.univ.sort (· ≤ ·))
  convert h using 1
  funext z
  exact firstBadFrom_parameter B _ z.1 z.2

end ParameterizedScan

section OrderConjugacy
variable {W I K : Type*} [Fintype I] [LinearOrder I] [Fintype K] [LinearOrder K]
variable (B : I → Set W) (C : K → Set W)
variable [∀ i, DecidablePred (· ∈ B i)] [∀ k, DecidablePred (· ∈ C k)]

/-- Inserting disabled labels preserves the original priority selection exactly. -/
theorem select_map_of_enabled (f : I → K)
    (hle : ∀ i j, f i ≤ f j ↔ i ≤ j)
    (hbad : ∀ i w, w ∈ C (f i) ↔ w ∈ B i)
    (henabled : ∀ k w, w ∈ C k → ∃ i, f i = k) (w : W) :
    (select B w).map f = select C w := by
  cases hb : select B w with
  | none =>
      have hc : select C w = none := (select_none_iff C w).mpr (by
        intro k hk
        obtain ⟨i, rfl⟩ := henabled k w hk
        exact (select_none_iff B w).mp hb i ((hbad i w).mp hk))
      simp only [Option.map_none, hc]
  | some i =>
      have hi : w ∈ C (f i) := (hbad i w).mpr (select_some_bad B hb)
      cases hc : select C w with
      | none => exact False.elim ((select_none_iff C w).mp hc (f i) hi)
      | some k =>
          obtain ⟨j, hj⟩ := henabled k w (select_some_bad C hc)
          have hij : i ≤ j := select_le B hb ((hbad j w).mp (hj.symm ▸ select_some_bad C hc))
          have hji : j ≤ i := (hle j i).mp (hj.symm ▸ select_le C hc hi)
          have he : i = j := le_antisymm hij hji
          simp only [Option.map_some, he, hj]
end OrderConjugacy

section ParameterizedExecution
variable {A V I : Type*} [MeasurableSpace A]
variable [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : A → ∀ i, Set (∀ v : vars i, X v))
variable [∀ a i, DecidablePred (· ∈ bad a i)]
variable (hbad : ∀ i, MeasurableSet
  {z : A × (∀ v : vars i, X v) | z.2 ∈ bad z.1 i})

include hbad in
/-- Coordinate restriction preserves the parameter and the actual variable addresses. -/
theorem measurableSet_parameterized_localEvent (i : I) :
    MeasurableSet {z : A × (∀ v, X v) | z.2 ∈ localEvent vars (bad z.1) i} := by
  have hm : Measurable (fun z : A × (∀ v, X v) =>
      (z.1, fun v : vars i => z.2 v.val)) :=
    measurable_fst.prodMk (measurable_pi_lambda _ fun v : vars i =>
      (measurable_pi_apply v.val).comp measurable_snd)
  exact (hbad i).preimage hm

/-- The lookup index is the countable SECOND factor; no separate-section shortcut is used. -/
theorem measurable_parameterized_assignment
    {c : A × Table (X := X) → Counters V} (hc : Measurable c) :
    Measurable (fun z : A × Table (X := X) => assignment z.2 (c z)) := by
  apply measurable_pi_lambda
  intro v
  have lookup : Measurable (fun z : Table (X := X) × ℕ => tableRead z.1 v z.2) :=
    measurable_from_prod_countable_left (fun n => measurable_pi_apply (v,n))
  exact lookup.comp (measurable_snd.prodMk ((measurable_pi_apply v).comp hc))

include hbad in
theorem measurable_parameterized_step
    {c : A × Table (X := X) → Counters V} (hc : Measurable c) :
    Measurable (fun z : A × Table (X := X) => step vars (bad z.1) z.2 (c z)) := by
  have hselect : Measurable (fun z : A × Table (X := X) =>
      select (localEvent vars (bad z.1)) (assignment z.2 (c z))) :=
    (measurable_parameterized_select (fun a => localEvent vars (bad a))
      (measurableSet_parameterized_localEvent vars bad hbad)).comp
        (measurable_fst.prodMk (measurable_parameterized_assignment hc))
  have update : Measurable (fun z : Counters V × Option I =>
      match z.2 with | none => z.1 | some i => advance vars i z.1) := by
    apply measurable_from_prod_countable_left
    intro choice
    cases choice with
    | none => exact measurable_id
    | some i =>
        apply measurable_pi_lambda
        intro v
        exact (measurable_pi_apply v).add_const _
  exact update.comp (hc.prodMk hselect)

include hbad in
theorem measurable_parameterized_counters (n : ℕ) :
    Measurable (fun z : A × Table (X := X) => counters vars (bad z.1) z.2 n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_parameterized_step vars bad hbad ih

include hbad in
theorem measurable_parameterized_selected (n : ℕ) :
    Measurable (fun z : A × Table (X := X) => selected vars (bad z.1) z.2 n) :=
  (measurable_parameterized_select (fun a => localEvent vars (bad a))
    (measurableSet_parameterized_localEvent vars bad hbad)).comp
      (measurable_fst.prodMk (measurable_parameterized_assignment
        (measurable_parameterized_counters vars bad hbad n)))

include hbad in
theorem measurableSet_parameterized_halts :
    MeasurableSet {z : A × Table (X := X) | Halts vars (bad z.1) z.2} := by
  have he : {z : A × Table (X := X) | Halts vars (bad z.1) z.2} =
      ⋃ n : ℕ, {z | selected vars (bad z.1) z.2 n = none} := by
    ext z
    simp only [Halts, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [he]
  exact MeasurableSet.iUnion fun n =>
    (measurable_parameterized_selected vars bad hbad n) (measurableSet_singleton none)

include hbad in
/-- Nat.find is applied to an everywhere-witnessed total predicate, exactly as in haltTime. -/
theorem measurable_parameterized_haltTime :
    Measurable (fun z : A × Table (X := X) => haltTime vars (bad z.1) z.2) := by
  classical
  let p : (A × Table (X := X)) → ℕ → Prop := fun z n =>
    selected vars (bad z.1) z.2 n = none ∨ ¬ Halts vars (bad z.1) z.2
  have hp : ∀ z, ∃ n, p z n := by
    intro z
    by_cases hz : Halts vars (bad z.1) z.2
    · obtain ⟨n,hn⟩ := hz
      exact ⟨n,Or.inl hn⟩
    · exact ⟨0,Or.inr hz⟩
  have hm : Measurable (fun z => Nat.find (hp z)) :=
    measurable_find hp fun n =>
      ((measurable_parameterized_selected vars bad hbad n) (measurableSet_singleton none)).union
        (measurableSet_parameterized_halts vars bad hbad).compl
  convert hm using 1
  funext z
  by_cases hz : Halts vars (bad z.1) z.2
  · simp only [haltTime, dif_pos hz]
    symm
    exact Nat.find_congr' (by intro n; simp [p,hz])
  · simp only [haltTime, dif_neg hz]
    symm
    exact Nat.find_eq_zero (hp z) |>.mpr (Or.inr hz)

include hbad in
theorem measurable_parameterized_output :
    Measurable (fun z : A × Table (X := X) => output vars (bad z.1) z.2) := by
  have hm : Measurable (fun z : (A × Table (X := X)) × ℕ =>
      counters vars (bad z.1.1) z.1.2 z.2) :=
    measurable_from_prod_countable_left fun n => measurable_parameterized_counters vars bad hbad n
  exact measurable_parameterized_assignment
    (hm.comp (measurable_id.prodMk (measurable_parameterized_haltTime vars bad hbad)))

end ParameterizedExecution
end QEC.Coding.ProbabilisticConstruction.Resampling
