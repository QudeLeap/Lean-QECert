import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.FiniteExperiment

/-!
# Whole-stage streams and literal finite truncations

All coordinates are the original countable-address stage tables. Packing a
finite dependent vector uses exactly the Unit/nested-product experiment;
unpacking reads its original tableAt. These are total pointwise identities,
including the original nonhalting/default tables.
-/

noncomputable section
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

abbrev Omega {L : ℝ} (p : GeometricParameters L) := (n : ℕ) → StageTables p n
abbrev TableVector {L : ℝ} (p : GeometricParameters L) (n : ℕ) :=
  (i : Fin n) → StageTables p i.val

/-- No restriction or successful-output choice is used in truncation. -/
def truncate {L : ℝ} (p : GeometricParameters L) :
    (n : ℕ) → Omega p → Experiment p n
  | 0, _ => ()
  | n+1, omega => (truncate p n omega, omega n)

@[simp] theorem truncate_zero {L : ℝ} (p : GeometricParameters L) (omega : Omega p) :
    truncate p 0 omega = () := rfl

@[simp] theorem truncate_succ {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (omega : Omega p) : truncate p (n+1) omega = (truncate p n omega, omega n) := rfl

def restrictTables {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Omega p → TableVector p n := fun omega i => omega i.val

/-- Last-coordinate recursion packs precisely the actual experiment carrier. -/
def packTables {L : ℝ} (p : GeometricParameters L) :
    (n : ℕ) → TableVector p n → Experiment p n
  | 0, _ => ()
  | n+1, v => (packTables p n (fun i => v i.castSucc), v (Fin.last n))

def unpackTables {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Experiment p n → TableVector p n := fun z i => tableAt p n i z

@[simp] theorem packTables_zero {L : ℝ} (p : GeometricParameters L) (v : TableVector p 0) :
    packTables p 0 v = () := rfl

@[simp] theorem packTables_succ {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (v : TableVector p (n+1)) :
    packTables p (n+1) v = (packTables p n (fun i => v i.castSucc), v (Fin.last n)) := rfl

/-- Every retained table is its original vector coordinate, not only its law. -/
theorem tableAt_packTables {L : ℝ} (p : GeometricParameters L) :
    ∀ (n : ℕ) (v : TableVector p n) (i : Fin n),
      tableAt p n i (packTables p n v) = v i := by
  intro n
  induction n with
  | zero => intro v i; exact Fin.elim0 i
  | succ n ih =>
      intro v i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [tableAt_last]
        rfl
      · rw [tableAt_castSucc]
        exact ih (fun j => v j.castSucc) j

theorem unpack_packTables {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (v : TableVector p n) : unpackTables p n (packTables p n v) = v := by
  funext i
  exact tableAt_packTables p n v i

theorem pack_unpackTables {L : ℝ} (p : GeometricParameters L) :
    ∀ (n : ℕ) (z : Experiment p n), packTables p n (unpackTables p n z) = z := by
  intro n
  induction n with
  | zero =>
      intro z
      exact @Subsingleton.elim Unit inferInstance _ _
  | succ n ih =>
      intro z
      apply Prod.ext
      · change packTables p n (fun i : Fin n => tableAt p (n+1) i.castSucc z) = z.1
        have hv : (fun i : Fin n => tableAt p (n+1) i.castSucc z) = unpackTables p n z.1 := by
          funext i
          exact tableAt_castSucc p n i z
        rw [hv]
        exact ih z.1
      · exact tableAt_last p n z

theorem measurable_packTables {L : ℝ} (p : GeometricParameters L) :
    ∀ n : ℕ, Measurable (packTables p n) := by
  intro n
  induction n with
  | zero =>
      change Measurable (fun _ : TableVector p 0 => (() : Unit))
      exact measurable_const
  | succ n ih =>
      let r : TableVector p (n+1) → TableVector p n := fun v i => v i.castSucc
      have hr : Measurable r := measurable_pi_lambda _ (fun i => measurable_pi_apply i.castSucc)
      have hfirst : Measurable (fun v : TableVector p (n+1) => packTables p n (r v)) :=
        @Measurable.comp (TableVector p (n+1)) (TableVector p n) (Experiment p n)
          inferInstance inferInstance inferInstance (packTables p n) r ih hr
      change Measurable (fun v : TableVector p (n+1) =>
        (packTables p n (r v), v (Fin.last n)))
      exact hfirst.prodMk (measurable_pi_apply (Fin.last n))

theorem measurable_unpackTables {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (unpackTables p n) :=
  measurable_pi_lambda _ (fun i => measurable_tableAt p n i)

/-- The equivalence keeps every actual table coordinate and both inverse identities. -/
def finiteVectorEquiv {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    TableVector p n ≃ᵐ Experiment p n where
  toEquiv := {
    toFun := packTables p n
    invFun := unpackTables p n
    left_inv := unpack_packTables p n
    right_inv := pack_unpackTables p n }
  measurable_toFun := measurable_packTables p n
  measurable_invFun := measurable_unpackTables p n

theorem truncate_eq_packTables {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (omega : Omega p) : truncate p n omega = packTables p n (restrictTables p n omega) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (truncate p n omega, omega n) =
        (packTables p n (restrictTables p n omega), omega n)
      rw [ih]

theorem measurable_restrictTables {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (restrictTables p n) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)

theorem measurable_truncate {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (truncate p n) := by
  have heq : truncate p n = (packTables p n) ∘ restrictTables p n :=
    funext (truncate_eq_packTables p n)
  rw [heq]
  exact @Measurable.comp (Omega p) (TableVector p n) (Experiment p n)
    inferInstance inferInstance inferInstance (packTables p n) (restrictTables p n)
    (measurable_packTables p n) (measurable_restrictTables p n)

/-- All finite prefix equations hold at every stream, even on exceptional tables. -/
theorem truncate_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (omega : Omega p) :
    experimentPrefix p m n h (truncate p n omega) = truncate p m omega := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      rw [prefix_self]
  | succ n ih =>
      by_cases hm : m = n+1
      · subst m
        rw [prefix_self]
      · have hmn : m ≤ n := by omega
        rw [prefix_succ p hmn]
        exact ih hmn

theorem truncate_prefix_proof_irrel {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h h' : m ≤ n) (omega : Omega p) :
    experimentPrefix p m n h (truncate p n omega) =
      experimentPrefix p m n h' (truncate p n omega) := rfl

theorem tableAt_truncate {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (omega : Omega p) : tableAt p n i (truncate p n omega) = omega i.val := by
  change (experimentPrefix p (i.val+1) n i.isLt (truncate p n omega)).2 = omega i.val
  rw [truncate_prefix]
  rfl

end QEC.Coding.BDL26CountableEmbeddingExperiment
