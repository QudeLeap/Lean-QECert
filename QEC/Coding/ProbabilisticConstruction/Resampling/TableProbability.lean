import QEC.Coding.ProbabilisticConstruction.Resampling.Execution
import Mathlib.Probability.Independence.InfinitePi

/-!
# Probability of finite disjoint table tests

A finite family of local tests reads pairwise distinct table coordinates. The
actual infinite product law then gives the product of their local probabilities.
Injectivity concerns coordinate addresses, not outcomes or probability claims.
-/

namespace QEC.Coding.ProbabilisticConstruction.Resampling

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]

/-- Each node reads its local variables from prescribed table columns. -/
def familyRead (coords : A → Finset V) (column : ∀ a, coords a → ℕ)
    (R : Table (X := X)) (a : A) (v : coords a) : X v := R (v, column a v)

theorem measurable_familyRead (coords : A → Finset V) (column : ∀ a, coords a → ℕ) :
    Measurable (familyRead (X := X) coords column) := by
  apply measurable_pi_lambda
  intro a
  exact measurable_pi_lambda _ (fun v => measurable_pi_apply (v.val, column a v))

/-- Distinct addresses transfer the independent table law to a finite product of local laws. -/
theorem familyRead_law (coords : A → Finset V) (column : ∀ a, coords a → ℕ)
    (haddress : Function.Injective
      (fun s : (a : A) × coords a => (s.2.val, column s.1 s.2))) :
    (tableLaw ν).map (familyRead (X := X) coords column) =
      Measure.pi (fun a => Measure.pi (fun v : coords a => ν v)) := by
  let key : ((a : A) × coords a) → V × ℕ := fun s => (s.2.val, column s.1 s.2)
  have hflat := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun p : V × ℕ => ν p.1) (f := key) haddress
  have hcur := congrArg
    (fun m => m.map (MeasurableEquiv.piCurry (fun (a : A) (v : coords a) => X v))) hflat
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hcur
  change _ = (Measure.infinitePi (fun s : (a : A) × coords a => ν s.2.val)).map
    (MeasurableEquiv.piCurry (fun (a : A) (v : coords a) => X v)) at hcur
  rw [Measure.infinitePi_map_piCurry (fun (a : A) (v : coords a) => ν v)] at hcur
  simp only [key, Function.comp_def, MeasurableEquiv.coe_piCurry,
    Measure.infinitePi_eq_pi] at hcur
  change (Measure.infinitePi (fun p : V × ℕ => ν p.1)).map
    (fun R a v => R (v.val, column a v)) = _
  exact hcur

/-- The finite compatibility probability is derived from the table law. -/
theorem table_tests_probability (coords : A → Finset V) (column : ∀ a, coords a → ℕ)
    (haddress : Function.Injective
      (fun s : (a : A) × coords a => (s.2.val, column s.1 s.2)))
    (test : ∀ a, Set (∀ v : coords a, X v)) (htest : ∀ a, MeasurableSet (test a)) :
    tableLaw ν {R | ∀ a, familyRead coords column R a ∈ test a} =
      ∏ a, (Measure.pi (fun v : coords a => ν v)) (test a) := by
  have hm := measurable_familyRead (X := X) coords column
  have hset : {R | ∀ a, familyRead coords column R a ∈ test a} =
      familyRead coords column ⁻¹' Set.univ.pi test := by ext R; simp
  rw [hset, ← Measure.map_apply hm (MeasurableSet.univ_pi htest),
    familyRead_law ν coords column haddress, Measure.pi_pi]

/-- Restricting the full finite variable law gives its actual coordinate product law. -/
theorem finiteRestriction_law (S : Finset V) :
    (Measure.pi ν).map S.restrict = Measure.pi (fun v : S => ν v) := by
  have h := Measure.map_infinitePi_infinitePi_of_inj
    (P := ν) (f := fun v : S => v.val) Subtype.val_injective
  simp only [Measure.infinitePi_eq_pi] at h
  change (Measure.pi ν).map (fun ω (i : S) => ω i.val) = _
  exact h

theorem local_probability_eq (S : Finset V) (bad : Set (∀ v : S, X v))
    (hbad : MeasurableSet bad) :
    (Measure.pi ν) (S.restrict ⁻¹' bad) = (Measure.pi (fun v : S => ν v)) bad := by
  rw [← Measure.map_apply S.measurable_restrict hbad, finiteRestriction_law ν S]

end QEC.Coding.ProbabilisticConstruction.Resampling
