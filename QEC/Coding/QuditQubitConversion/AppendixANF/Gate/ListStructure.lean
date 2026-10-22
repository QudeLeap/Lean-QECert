import QEC.Coding.QuditQubitConversion.AppendixANF.Target

/-!
# Structural certificates for the WHY24 Appendix-A gate lists

These certificates traverse only the twenty printed pairs and seventy printed
triples.  In particular, the ordering proofs use `List.all`; they do not
enumerate the ambient coordinate products or any Boolean input word.
-/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

open scoped BigOperators

/-- The printed quadratic gate list has no repeated pair. -/
theorem quadraticGatePairs_nodup : quadraticGatePairs.Nodup := by
  set_option maxRecDepth 2048 in decide

/-- Every printed quadratic pair is in increasing order. -/
theorem quadraticGatePairs_ordered (pair : Fin 10 × Fin 10)
    (hpair : pair ∈ quadraticGatePairs) : pair.1 < pair.2 := by
  have hall :
      quadraticGatePairs.all (fun pair => decide (pair.1 < pair.2)) = true := by
    set_option maxRecDepth 2048 in decide
  exact of_decide_eq_true ((List.all_eq_true.mp hall) pair hpair)

/-- The quadratic coefficient is the membership indicator of the printed
pair list. -/
theorem quadraticGateCoefficient_eq_indicator (pair : Fin 10 × Fin 10) :
    quadraticGateCoefficient pair.1 pair.2 =
      if pair ∈ quadraticGatePairs then 1 else 0 := rfl

/-- The printed cubic gate list has no repeated triple. -/
theorem cubicGateTriples_nodup : cubicGateTriples.Nodup := by
  set_option maxRecDepth 2048 in decide

/-- Every printed cubic triple is strictly increasing. -/
theorem cubicGateTriples_ordered (triple : Fin 10 × Fin 10 × Fin 10)
    (htriple : triple ∈ cubicGateTriples) :
    triple.1 < triple.2.1 ∧ triple.2.1 < triple.2.2 := by
  have hall : cubicGateTriples.all (fun triple =>
      decide (triple.1 < triple.2.1 ∧ triple.2.1 < triple.2.2)) = true := by
    set_option maxRecDepth 2048 in decide
  exact of_decide_eq_true ((List.all_eq_true.mp hall) triple htriple)

/-- The cubic coefficient is the membership indicator of the printed triple
list. -/
theorem cubicGateCoefficient_eq_indicator
    (triple : Fin 10 × Fin 10 × Fin 10) :
    cubicGateCoefficient triple.1 triple.2.1 triple.2.2 =
      if triple ∈ cubicGateTriples then 1 else 0 := rfl

/-- Reassociate a sum over a right-associated triple product without exposing
the summand during rewriting. -/
theorem fintype_sum_triple
    {A B C Value : Type*} [Fintype A] [Fintype B] [Fintype C]
    [AddCommMonoid Value] (value : A → B → C → Value) :
    (∑ entry : A × B × C, value entry.1 entry.2.1 entry.2.2) =
      ∑ first : A, ∑ second : B, ∑ third : C, value first second third := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro first _
  rw [Fintype.sum_prod_type]

end QEC.Coding.Why24AppendixANF
