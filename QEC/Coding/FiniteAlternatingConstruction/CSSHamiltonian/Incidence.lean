import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.Rows
import QEC.Coding.FiniteAlternatingConstruction.BoundedValenceSuccessors

/-! # Measured check incidence and a uniform combinatorial region bound -/
noncomputable section
namespace QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26BoundedValence PauliSymplectic
open scoped BigOperators
variable (S : OddScale) (n : Nat)

def checkSupport (j : Sum (ZLabel S n) (XLabel S n)) : Finset (Physical S n) := support (check S n j)

@[simp] theorem mem_z_checkSupport (z : ZLabel S n) (q : Physical S n) :
    q ∈ checkSupport S n (.inl z) ↔ (presentation S n).qz q z = true := by
  simp [checkSupport, check, binaryCSSParityCheckGenerators, support_cssZCheck, hammingSupport]

@[simp] theorem mem_x_checkSupport (x : XLabel S n) (q : Physical S n) :
    q ∈ checkSupport S n (.inr x) ↔ (presentation S n).xq x q = true := by
  simp [checkSupport, check, binaryCSSParityCheckGenerators, support_cssXCheck, hammingSupport]

theorem z_check_card (z : ZLabel S n) : (checkSupport S n (.inl z)).card = zDegree (presentation S n) z := by
  have h : checkSupport S n (.inl z) = Finset.univ.filter (fun q => (presentation S n).qz q z = true) := by
    ext q; simp
  rw [h, zDegree, Fintype.card_subtype]

theorem x_check_card (x : XLabel S n) : (checkSupport S n (.inr x)).card = xDegree (presentation S n) x := by
  have h : checkSupport S n (.inr x) = Finset.univ.filter (fun q => (presentation S n).xq x q = true) := by
    ext q; simp
  rw [h, xDegree, Fintype.card_subtype]

theorem check_card_le_seven (j : Sum (ZLabel S n) (XLabel S n)) : (checkSupport S n j).card ≤ 7 := by
  cases j with
  | inl z => rw [z_check_card]; exact (state_boundedValence S n).2.1 z
  | inr x => rw [x_check_card]; exact (state_boundedValence S n).1 x

/-- Labelled incident rows; equal operators are never deduplicated. -/
def incident (q : Physical S n) : Finset (Sum (ZLabel S n) (XLabel S n)) :=
  Finset.univ.filter (fun j => q ∈ checkSupport S n j)

theorem incident_card (q : Physical S n) : (incident S n q).card =
    qZDegree (presentation S n) q + qXDegree (presentation S n) q := by
  have h : incident S n q =
      (Finset.univ.filter (fun z => (presentation S n).qz q z = true)).disjSum
        (Finset.univ.filter (fun x => (presentation S n).xq x q = true)) := by
    ext j
    cases j <;> simp [incident]
  rw [h, Finset.card_disjSum, qZDegree, qXDegree, Fintype.card_subtype, Fintype.card_subtype]

theorem incident_card_le_seven (q : Physical S n) : (incident S n q).card ≤ 7 := by
  rw [incident_card, Nat.add_comm]
  exact ((state_boundedValence S n).2.2 q).2.2

/-- Combinatorial candidate region, prior to any operator or metric interpretation. -/
def region (q : Physical S n) : Finset (Physical S n) :=
  {q} ∪ (incident S n q).biUnion (checkSupport S n)

theorem region_card_le_fifty (q : Physical S n) : (region S n q).card ≤ 50 := by
  calc
    (region S n q).card ≤ 1 + ((incident S n q).biUnion (checkSupport S n)).card := by
      simpa [region] using Finset.card_union_le ({q} : Finset (Physical S n)) ((incident S n q).biUnion (checkSupport S n))
    _ ≤ 1 + ∑ j ∈ incident S n q, (checkSupport S n j).card :=
      Nat.add_le_add_left Finset.card_biUnion_le 1
    _ ≤ 1 + ∑ _j ∈ incident S n q, 7 := by
      exact Nat.add_le_add_left (Finset.sum_le_sum (fun j _ => check_card_le_seven S n j)) 1
    _ = 1 + (incident S n q).card * 7 := by simp
    _ ≤ 50 := by have h := incident_card_le_seven S n q; omega

end QEC.Coding.BDL26CSSHamiltonian
