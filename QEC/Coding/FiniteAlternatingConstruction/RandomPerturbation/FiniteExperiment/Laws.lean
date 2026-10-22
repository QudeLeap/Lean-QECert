import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.FiniteExperiment.Core
import Mathlib.Probability.Independence.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Exact product and output laws of the literal finite experiment

The independent random objects are the original stage tables. The output
embeddings retain their recursive dependence. Prefix and table laws are exact
pushforwards, not conditional laws on successful executions.
-/

noncomputable section
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal ProbabilityTheory

def experimentLaw {L : ℝ} (p : GeometricParameters L) :
    (n : ℕ) → Measure (Experiment p n)
  | 0 => Measure.dirac ()
  | n+1 => (experimentLaw p n).prod (physicalTableLaw p n)

instance experimentLaw_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    IsProbabilityMeasure (experimentLaw p n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | succ n ih =>
      letI := ih
      change IsProbabilityMeasure ((experimentLaw p n).prod (physicalTableLaw p n))
      infer_instance

theorem measurePreserving_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) :
    MeasurePreserving (experimentPrefix p m n h) (experimentLaw p n) (experimentLaw p m) := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      exact MeasurePreserving.id _
  | succ n ih =>
      by_cases hm : m = n+1
      · subst m
        simpa only [show experimentPrefix p (n+1) (n+1) h = id from funext (prefix_self p _ h)]
          using MeasurePreserving.id (experimentLaw p (n+1))
      · have hmn : m ≤ n := by omega
        have heq : experimentPrefix p m (n+1) h = (experimentPrefix p m n hmn) ∘ Prod.fst :=
          funext (prefix_succ p hmn)
        rw [heq]
        exact (ih hmn).comp measurePreserving_fst

theorem measurePreserving_tableAt {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) :
    MeasurePreserving (tableAt p n i) (experimentLaw p n) (physicalTableLaw p i.val) :=
  measurePreserving_snd.comp (measurePreserving_prefix p i.isLt)

theorem tableAt_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    (experimentLaw p n).map (tableAt p n i) = physicalTableLaw p i.val :=
  (measurePreserving_tableAt p n i).map_eq

theorem tableAt_preimage {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (B : Set (StageTables p i.val)) (hB : MeasurableSet B) :
    experimentLaw p n (tableAt p n i ⁻¹' B) = physicalTableLaw p i.val B := by
  rw [← Measure.map_apply (measurable_tableAt p n i) hB, tableAt_law]

/-- The full dependent rectangle splits into the preceding rectangle and final table set. -/
theorem full_rectangle_succ {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (B : (i : Fin (n+1)) → Set (StageTables p i.val)) :
    {z : Experiment p (n+1) | ∀ i, tableAt p (n+1) i z ∈ B i} =
      {z : Experiment p n | ∀ i : Fin n, tableAt p n i z ∈ B i.castSucc} ×ˢ
        B (Fin.last n) := by
  ext z
  constructor
  · intro hz
    exact ⟨fun i => by simpa only [tableAt_castSucc] using hz i.castSucc,
      by simpa only [tableAt_last] using hz (Fin.last n)⟩
  · rintro ⟨hfirst, hlast⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [tableAt_last] using hlast
    · simpa only [tableAt_castSucc] using hfirst j

/-- Arbitrary table rectangles have the actual product probability, including zero stages. -/
theorem full_rectangle_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (B : (i : Fin n) → Set (StageTables p i.val)) :
    experimentLaw p n {z | ∀ i, tableAt p n i z ∈ B i} =
      ∏ i : Fin n, physicalTableLaw p i.val (B i) := by
  induction n with
  | zero =>
      have heq : {z : Experiment p 0 | ∀ i : Fin 0, tableAt p 0 i z ∈ B i} = Set.univ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro i
        exact Fin.elim0 i
      rw [heq]
      simp only [Fin.prod_univ_zero]
      exact measure_univ
  | succ n ih =>
      rw [full_rectangle_succ]
      change (experimentLaw p n).prod (physicalTableLaw p n) _ = _
      rw [Measure.prod_prod, ih, Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]

/-- Every selected finite rectangle factors; unused factors remain the original whole laws. -/
theorem finite_rectangle_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (A : Finset (Fin n)) (B : (i : Fin n) → Set (StageTables p i.val)) :
    experimentLaw p n (⋂ i ∈ A, tableAt p n i ⁻¹' B i) =
      ∏ i ∈ A, physicalTableLaw p i.val (B i) := by
  let full : (i : Fin n) → Set (StageTables p i.val) :=
    fun i => if i ∈ A then B i else Set.univ
  have hset : {z : Experiment p n | ∀ i, tableAt p n i z ∈ full i} =
      ⋂ i ∈ A, tableAt p n i ⁻¹' B i := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h i hi
      simpa only [full, if_pos hi] using h i
    · intro h i
      by_cases hi : i ∈ A
      · simpa only [full, if_pos hi] using h i hi
      · simp only [full, if_neg hi, Set.mem_univ]
  rw [← hset, full_rectangle_probability]
  calc
    (∏ i : Fin n, physicalTableLaw p i.val (full i)) =
        ∏ i ∈ A, physicalTableLaw p i.val (full i) := by
      symm
      apply Finset.prod_subset (Finset.subset_univ A)
      intro i _ hi
      simp only [full, if_neg hi, measure_univ]
    _ = ∏ i ∈ A, physicalTableLaw p i.val (B i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [full, if_pos hi]

theorem tableAt_iIndepFun {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    iIndepFun (tableAt p n) (experimentLaw p n) := by
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro A B hB
  rw [finite_rectangle_probability]
  apply Finset.prod_congr rfl
  intro i hi
  exact (tableAt_preimage p n i (B i) (hB i hi)).symm

def outputLaw {L : ℝ} (p : GeometricParameters L) (n : ℕ) : Measure (StageMaps p n) :=
  (experimentLaw p n).map (evaluate p n)

instance outputLaw_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    IsProbabilityMeasure (outputLaw p n) :=
  Measure.isProbabilityMeasure_map (measurable_evaluate p n).aemeasurable

@[simp] theorem outputLaw_zero {L : ℝ} (p : GeometricParameters L) :
    outputLaw p 0 = Measure.dirac (BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p)) := by
  change (Measure.dirac (() : Experiment p 0)).map (evaluate p 0) = _
  exact Measure.map_dirac' (measurable_evaluate p 0) ()

def freshPair {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Experiment p (n+1) → StageMaps p n × StageTables p n :=
  fun z => (evaluate p n z.1, z.2)

theorem measurable_freshPair {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (freshPair p n) :=
  ((measurable_evaluate p n).comp measurable_fst).prodMk measurable_snd

theorem freshPair_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (experimentLaw p (n+1)).map (freshPair p n) =
      (outputLaw p n).prod (physicalTableLaw p n) := by
  have hid : Measurable (id : StageTables p n → StageTables p n) := measurable_id
  have h : (outputLaw p n).prod ((physicalTableLaw p n).map (id : StageTables p n → StageTables p n)) =
      ((experimentLaw p n).prod (physicalTableLaw p n)).map
        (Prod.map (evaluate p n) (id : StageTables p n → StageTables p n)) :=
    Measure.map_prod_map (experimentLaw p n) (physicalTableLaw p n) (measurable_evaluate p n) hid
  rw [Measure.map_id] at h
  have hfun : Prod.map (evaluate p n) (id : StageTables p n → StageTables p n) = freshPair p n := by
    funext z
    rcases z with ⟨x,T⟩
    rfl
  rw [hfun] at h
  exact h.symm

theorem stagePair_eq_freshPair_prefix {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) :
    stagePair p n i = (freshPair p i.val) ∘ experimentPrefix p (i.val+1) n i.isLt := by
  funext z
  apply Prod.ext
  · change evaluate p i.val (experimentPrefix p i.val n (by omega) z) =
      evaluate p i.val (experimentPrefix p (i.val+1) n i.isLt z).1
    congr 1
    rw [← prefix_last p i.val, prefix_comp]
  · rfl

theorem stagePair_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    (experimentLaw p n).map (stagePair p n i) =
      (outputLaw p i.val).prod (physicalTableLaw p i.val) := by
  rw [stagePair_eq_freshPair_prefix, ← Measure.map_map
    (measurable_freshPair p i.val) (measurable_prefix p i.isLt),
    (measurePreserving_prefix p i.isLt).map_eq, freshPair_law]

theorem prefix_output_law {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) :
    (experimentLaw p n).map ((evaluate p m) ∘ experimentPrefix p m n h) = outputLaw p m := by
  rw [← Measure.map_map (measurable_evaluate p m) (measurable_prefix p h),
    (measurePreserving_prefix p h).map_eq]
  rfl

/-- The incoming law is first in `bind`; the same total successor kernel is used. -/
theorem outputLaw_succ {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    outputLaw p (n+1) = (successorKernel p n) ∘ₘ (outputLaw p n) := by
  rw [← physicalSuccessorOutput_law p n (outputLaw p n), ← freshPair_law,
    Measure.map_map (measurable_joint_physicalSuccessorOutput p n) (measurable_freshPair p n)]
  rfl

theorem outputLaw_succ_bind {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    outputLaw p (n+1) = (outputLaw p n).bind (successorKernel p n) :=
  outputLaw_succ p n

end QEC.Coding.BDL26FiniteEmbeddingExperiment
