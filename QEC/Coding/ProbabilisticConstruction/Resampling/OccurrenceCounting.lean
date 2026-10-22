import QEC.Coding.ProbabilisticConstruction.Resampling.TreeProbability
import Mathlib.Data.Fintype.Fin

/-! # Injecting actual resampling occurrences into compatible proper trees -/

namespace QEC.Coding.ProbabilisticConstruction.Resampling

open scoped BigOperators

variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

/-- Actual occurrences of one event in the first T transitions. -/
def occurrences (R : Table (X := X)) (T : ℕ) (i : I) : Finset ℕ :=
  (Finset.range T).filter (fun n => selected vars bad R n = some i)

def prefixCount (R : Table (X := X)) (T : ℕ) (i : I) : ℕ :=
  (occurrences vars bad R T i).card

theorem prefixCount_monotone (R : Table (X := X)) (i : I) :
    Monotone (fun T => prefixCount vars bad R T i) := by
  intro a b hab
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hab))

theorem prefixCount_strict (R : Table (X := X)) (i : I) (a b : ℕ)
    (hab : a < b) (ha : selected vars bad R a = some i) :
    prefixCount vars bad R a i < prefixCount vars bad R b i := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset_filter _ (Finset.range_mono hab.le), ?_⟩
  intro he
  have hm : a ∈ occurrences vars bad R b i := by simp [occurrences, hab, ha]
  rw [← he] at hm
  simpa [occurrences] using hm

theorem list_count_eq_history_count (root i : I) (L : List I) :
    L.count i = ((Finset.range L.length).filter (fun k => historyLabel root L k = i)).card := by
  let v : List.Vector I L.length := ⟨L, rfl⟩
  have hc := Fin.card_filter_univ_eq_vector_get_eq_count i v
  change _ = L.count i at hc
  rw [← hc]
  apply Finset.card_bij (fun k _ => k.val)
  · intro k hk
    obtain ⟨_, he⟩ := Finset.mem_filter.mp hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr k.isLt, ?_⟩
    change L[k.val] = i at he
    simpa only [historyLabel, List.getElem?_eq_getElem k.isLt, Option.getD_some] using he
  · intro a ha b hb he; exact Fin.ext he
  · intro k hk
    obtain ⟨hk, he⟩ := Finset.mem_filter.mp hk
    refine ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    have hkl : k < L.length := Finset.mem_range.mp hk
    change L[k] = i
    simpa only [historyLabel, List.getElem?_eq_getElem (Finset.mem_range.mp hk),
      Option.getD_some] using he

theorem occurrenceHistory_count (R : Table (X := X)) (n : ℕ) (i : I)
    (hi : selected vars bad R n = some i) :
    (occurrenceHistory vars bad R n i hi).count i = prefixCount vars bad R n i := by
  rw [list_count_eq_history_count i i, occurrenceHistory_length]
  unfold prefixCount occurrences
  congr 1
  apply Finset.filter_congr
  intro k hk
  have he := occurrenceHistory_matches vars bad R n i hi k (Finset.mem_range.mp hk).le
  rw [he, Option.some.injEq]

/-- Embed each actual occurrence in a single common finite tree family. -/
noncomputable def occurrenceTree (R : Table (X := X)) (T : ℕ) (i : I)
    (n : occurrences vars bad R T i) : WitnessTree (supportGraph vars) (T + 1) i :=
  let hn := (Finset.mem_filter.mp n.property).2
  let L := occurrenceHistory vars bad R n.val i hn
  pathsToTree (supportGraph vars) (T + 1) i (historyWitness (supportGraph vars) i L)
    (historyWitness_proper (supportGraph vars) i L) (by
      intro p hp
      have hd := historyWitness_depth (supportGraph vars) i L p hp
      have hl : L.length = n.val := occurrenceHistory_length vars bad R n.val i hn
      have ht := Finset.mem_range.mp (Finset.mem_filter.mp n.property).1
      omega)

theorem occurrenceTree_paths (R : Table (X := X)) (T : ℕ) (i : I)
    (n : occurrences vars bad R T i) :
    witnessPaths (supportGraph vars) (T + 1) i (occurrenceTree vars bad R T i n) =
      historyWitness (supportGraph vars) i (occurrenceHistory vars bad R n.val i
        (Finset.mem_filter.mp n.property).2) := by
  unfold occurrenceTree
  apply witnessPaths_pathsToTree

theorem occurrenceTree_compatible (R : Table (X := X)) (T : ℕ) (i : I)
    (n : occurrences vars bad R T i) :
    R ∈ compatible vars bad i
      (witnessPaths (supportGraph vars) (T + 1) i (occurrenceTree vars bad R T i n)) := by
  rw [occurrenceTree_paths]
  exact occurrenceHistory_compatible vars bad R n.val i _

/-- Different occurrences of an event produce different proper witnesses. -/
theorem occurrenceTree_injective (R : Table (X := X)) (T : ℕ) (i : I) :
    Function.Injective (occurrenceTree vars bad R T i) := by
  intro a b he
  have hp := congrArg (witnessPaths (supportGraph vars) (T + 1) i) he
  rw [occurrenceTree_paths, occurrenceTree_paths] at hp
  have hc := congrArg (labelCount i i) hp
  rw [historyWitness_root_count, historyWitness_root_count,
    occurrenceHistory_count, occurrenceHistory_count] at hc
  apply Subtype.ext
  rcases lt_trichotomy a.val b.val with hab | he | hba
  · have hh := prefixCount_strict vars bad R i a.val b.val hab
      (Finset.mem_filter.mp a.property).2
    omega
  · exact he
  · have hh := prefixCount_strict vars bad R i b.val a.val hba
      (Finset.mem_filter.mp b.property).2
    omega

open scoped Classical in
/-- A finite execution count is bounded pointwise by the compatible-tree count. -/
theorem prefixCount_le_compatible (R : Table (X := X)) (T : ℕ) (i : I) :
    prefixCount vars bad R T i ≤
      (Finset.univ.filter (fun t : WitnessTree (supportGraph vars) (T + 1) i =>
        R ∈ compatible vars bad i (witnessPaths (supportGraph vars) (T + 1) i t))).card := by
  classical
  apply Finset.card_le_card_of_injective (f := fun n =>
    ⟨occurrenceTree vars bad R T i n,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, occurrenceTree_compatible vars bad R T i n⟩⟩)
  intro a b he
  exact occurrenceTree_injective vars bad R T i (congrArg Subtype.val he)

end QEC.Coding.ProbabilisticConstruction.Resampling
