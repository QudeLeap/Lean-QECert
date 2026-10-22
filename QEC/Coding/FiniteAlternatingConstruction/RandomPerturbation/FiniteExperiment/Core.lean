import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.EmbeddingKernel
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.SeedEmbedding

/-!
# Literal finite experiments with the original fresh tables

The parameters precede the level. A stage factor is the whole original
countable-address table, not a finite table approximation. All maps below are
total, so their identities also cover nonhalting tables and default outputs.
This finite probability-space representation asserts no operational sampling
or rank-dictionary cost.
-/

noncomputable section
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

abbrev StageMaps {L : ℝ} (p : GeometricParameters L) (n : ℕ) :=
  Vertex (state (perturbationOddScale p) n).presentation → Space

abbrev StageTables {L : ℝ} (p : GeometricParameters L) (n : ℕ) :=
  Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space)

/-- Exactly one independent whole table factor is appended at each stage. -/
def Experiment {L : ℝ} (p : GeometricParameters L) : ℕ → Type
  | 0 => Unit
  | n+1 => Experiment p n × StageTables p n

instance experimentMeasurableSpace {L : ℝ} (p : GeometricParameters L) :
    (n : ℕ) → MeasurableSpace (Experiment p n)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n+1 => (experimentMeasurableSpace p n).prod inferInstance

/-- Retain the first `m` actual stage factors, by deleting later factors. -/
def experimentPrefix {L : ℝ} (p : GeometricParameters L) (m : ℕ) :
    (n : ℕ) → m ≤ n → Experiment p n → Experiment p m
  | 0, h, z => by
      have hm : m = 0 := by omega
      subst m
      exact z
  | n+1, h, z =>
      if he : m = n+1 then he.symm ▸ z
      else experimentPrefix p m n (by omega) z.1

@[simp] theorem prefix_self {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (h : n ≤ n) (z : Experiment p n) : experimentPrefix p n n h z = z := by
  cases n with
  | zero => rfl
  | succ n => simp [experimentPrefix]

theorem prefix_proof_irrel {L : ℝ} (p : GeometricParameters L) (m n : ℕ)
    (h h' : m ≤ n) : experimentPrefix p m n h = experimentPrefix p m n h' := rfl

@[simp] theorem prefix_zero {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (h : 0 ≤ n) (z : Experiment p n) : experimentPrefix p 0 n h z = () := by
  change (experimentPrefix p 0 n h z : Unit) = ()
  exact @Subsingleton.elim Unit inferInstance (experimentPrefix p 0 n h z) ()

/-- Deleting a final stage does not inspect its table. -/
theorem prefix_succ {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (z : Experiment p (n+1)) :
    experimentPrefix p m (n+1) (by omega) z = experimentPrefix p m n h z.1 := by
  have he : ¬m = n+1 := by omega
  simp only [experimentPrefix, dif_neg he]

@[simp] theorem prefix_last {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : Experiment p (n+1)) : experimentPrefix p n (n+1) (by omega) z = z.1 := by
  rw [prefix_succ p (le_refl n), prefix_self]

/-- Prefix composition is a pointwise identity, without an almost-everywhere restriction. -/
theorem prefix_comp {L : ℝ} (p : GeometricParameters L) {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) (z : Experiment p n) :
    experimentPrefix p l m hlm (experimentPrefix p m n hmn z) = experimentPrefix p l n (hlm.trans hmn) z := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := by omega
      have hl : l = 0 := by omega
      subst m
      subst l
      rfl
  | succ n ih =>
      by_cases hm : m = n+1
      · subst m
        rw [prefix_self]
      · have hmn' : m ≤ n := by omega
        have hln : l ≤ n := hlm.trans hmn'
        rw [prefix_succ p hmn', prefix_succ p hln]
        exact ih hlm hmn' z.1

/-- The actual factor at stage `i`, read from the prefix ending at `i+1`. -/
def tableAt {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Experiment p n → StageTables p i.val :=
  fun z => (experimentPrefix p (i.val+1) n i.isLt z).2

@[simp] theorem tableAt_last {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : Experiment p (n+1)) : tableAt p (n+1) (Fin.last n) z = z.2 := by
  simp only [tableAt, Fin.val_last, prefix_self]

theorem tableAt_castSucc {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) (z : Experiment p (n+1)) :
    tableAt p (n+1) i.castSucc z = tableAt p n i z.1 := by
  simp only [tableAt, Fin.coe_castSucc]
  rw [prefix_succ p i.isLt]

theorem tableAt_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (i : Fin m) (z : Experiment p n) :
    tableAt p m i (experimentPrefix p m n h z) = tableAt p n (i.castLE h) z := by
  simp only [tableAt, Fin.val_castLE]
  rw [prefix_comp]

/-- Evaluate the literal selected successor, including its original total default. -/
def evaluate {L : ℝ} (p : GeometricParameters L) : (n : ℕ) → Experiment p n → StageMaps p n
  | 0, _ => BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p)
  | n+1, z => physicalSuccessorOutput p n (evaluate p n z.1) z.2

@[simp] theorem evaluate_zero {L : ℝ} (p : GeometricParameters L) (z : Experiment p 0) :
    evaluate p 0 z = BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p) := rfl

@[simp] theorem evaluate_succ {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : Experiment p (n+1)) :
    evaluate p (n+1) z = physicalSuccessorOutput p n (evaluate p n z.1) z.2 := rfl

def history {L : ℝ} (p : GeometricParameters L) (n : ℕ) (z : Experiment p n)
    (i : Fin (n+1)) : StageMaps p i.val :=
  evaluate p i.val (experimentPrefix p i.val n (by omega) z)

def stageInput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Experiment p n → StageMaps p i.val :=
  fun z => evaluate p i.val (experimentPrefix p i.val n (by omega) z)

def stagePair {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Experiment p n → StageMaps p i.val × StageTables p i.val :=
  fun z => (stageInput p n i z, tableAt p n i z)

theorem evaluate_prefix_succ {L : ℝ} (p : GeometricParameters L) {i n : ℕ}
    (hi : i < n) (z : Experiment p n) :
    evaluate p (i+1) (experimentPrefix p (i+1) n hi z) =
      physicalSuccessorOutput p i (stageInput p n ⟨i,hi⟩ z) (tableAt p n ⟨i,hi⟩ z) := by
  rw [evaluate_succ]
  congr 1
  unfold stageInput
  congr 1
  rw [← prefix_last p i, prefix_comp]

theorem history_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (z : Experiment p n) (i : Fin (m+1)) :
    history p m (experimentPrefix p m n h z) i =
      history p n z (i.castLE (by omega)) := by
  simp only [history, Fin.val_castLE]
  rw [prefix_comp]

theorem stagePair_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (i : Fin m) (z : Experiment p n) :
    stagePair p m i (experimentPrefix p m n h z) = stagePair p n (i.castLE h) z := by
  apply Prod.ext
  · simp only [stagePair, stageInput, Fin.val_castLE]
    rw [prefix_comp]
  · exact tableAt_prefix p h i z

theorem measurable_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) : Measurable (experimentPrefix p m n h) := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      exact measurable_id
  | succ n ih =>
      by_cases hm : m = n+1
      · subst m
        simpa only [show experimentPrefix p (n+1) (n+1) h = id from funext (prefix_self p _ h)]
          using measurable_id
      · have hmn : m ≤ n := by omega
        have heq : experimentPrefix p m (n+1) h = (experimentPrefix p m n hmn) ∘ Prod.fst :=
          funext (prefix_succ p hmn)
        rw [heq]
        exact (ih hmn).comp measurable_fst

theorem measurable_tableAt {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Measurable (tableAt p n i) :=
  measurable_snd.comp (measurable_prefix p i.isLt)

theorem measurable_evaluate {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (evaluate p n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      change Measurable (fun z : Experiment p n × StageTables p n =>
        physicalSuccessorOutput p n (evaluate p n z.1) z.2)
      have hleft : Measurable (fun z : Experiment p n × StageTables p n =>
          evaluate p n z.1) := ih.comp measurable_fst
      have hright : Measurable (fun z : Experiment p n × StageTables p n => z.2) :=
        measurable_snd
      have hpair : Measurable (fun z : Experiment p n × StageTables p n =>
          (evaluate p n z.1, z.2)) := hleft.prodMk hright
      have hsuccessor : Measurable (fun w : StageMaps p n × StageTables p n =>
          physicalSuccessorOutput p n w.1 w.2) := measurable_joint_physicalSuccessorOutput p n
      exact @Measurable.comp
        (Experiment p n × StageTables p n) (StageMaps p n × StageTables p n) (StageMaps p (n+1))
        inferInstance inferInstance inferInstance
        (fun w : StageMaps p n × StageTables p n => physicalSuccessorOutput p n w.1 w.2)
        (fun z : Experiment p n × StageTables p n => (evaluate p n z.1, z.2))
        hsuccessor hpair

theorem measurable_history {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (history p n) := by
  apply measurable_pi_lambda _
  intro i
  exact (measurable_evaluate p i.val).comp (measurable_prefix p (by omega))

theorem measurable_stageInput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Measurable (stageInput p n i) :=
  (measurable_evaluate p i.val).comp (measurable_prefix p (by omega))

theorem measurable_stagePair {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Measurable (stagePair p n i) :=
  (measurable_stageInput p n i).prodMk (measurable_tableAt p n i)

end QEC.Coding.BDL26FiniteEmbeddingExperiment
