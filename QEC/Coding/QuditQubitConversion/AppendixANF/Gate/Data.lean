import QEC.Coding.QuditQubitConversion.AppendixANF.Evaluation
import QEC.Coding.QuditQubitConversion.AppendixANF.Gate.Certificate

/-!
# Literal WHY24 Appendix-A gate data and sparse-ANF semantics

The source gate program is assembled from its literal ten linear sites,
twenty listed pairs, and seventy listed triples.  Its phase fold is identified
symbolically with the sparse target ANF and hence with the concrete
seventh-power trace.  No Boolean input word is enumerated.
-/

noncomputable section

namespace QEC.Coding

open scoped BigOperators
open Why24BooleanANF
open Why24AppendixANF

/-- The three diagonal gate kinds listed in WHY24 Appendix A for the selected
ten-qubit gate. -/
inductive Why24AppendixGate where
  | z (site : Fin 10)
  | cz (left right : Fin 10)
  | ccz (first second third : Fin 10)
  deriving DecidableEq

private def why24AppendixZGateList : List Why24AppendixGate :=
  List.ofFn fun site : Fin 10 => .z site

/-- The literal ordered Appendix-A decomposition of `theta(U_1^(7))`.  The
pair and triple data are the source lists certified by the sparse ANF layer. -/
def why24AppendixGateList : List Why24AppendixGate :=
  why24AppendixZGateList ++
    quadraticGatePairs.map (fun pair => .cz pair.1 pair.2) ++
    cubicGateTriples.map
      (fun triple => .ccz triple.1 triple.2.1 triple.2.2)

private def why24AppendixGateIsZ : Why24AppendixGate → Bool
  | .z _ => true
  | .cz _ _ => false
  | .ccz _ _ _ => false

private def why24AppendixGateIsCZ : Why24AppendixGate → Bool
  | .z _ => false
  | .cz _ _ => true
  | .ccz _ _ _ => false

private def why24AppendixGateIsCCZ : Why24AppendixGate → Bool
  | .z _ => false
  | .cz _ _ => false
  | .ccz _ _ _ => true

/-- The `(Z, CZ, CCZ)` count derived from the literal Appendix-A gate list. -/
def why24AppendixGateCounts : Nat × Nat × Nat :=
  (why24AppendixGateList.countP why24AppendixGateIsZ,
    why24AppendixGateList.countP why24AppendixGateIsCZ,
    why24AppendixGateList.countP why24AppendixGateIsCCZ)

/-- The literal source list contains ten `Z`, twenty `CZ`, and seventy `CCZ`
gates. -/
theorem why24AppendixGateCounts_eq_source :
    why24AppendixGateCounts = (10, 20, 70) := by decide

/-- The squarefree ANF monomial contributed by one Appendix-A gate. -/
def why24AppendixGateANF : Why24AppendixGate → ANF
  | .z site => generator site
  | .cz left right => generator left * generator right
  | .ccz first second third =>
      generator first * generator second * generator third

/-- The sparse polynomial obtained by adding the monomials in a gate list. -/
def why24AppendixGateListANF (gates : List Why24AppendixGate) : ANF :=
  gates.foldr (fun gate polynomial => why24AppendixGateANF gate + polynomial) 0

/-- Boolean phase contributed by one literal Appendix-A gate. -/
def why24AppendixWordGatePhase (gate : Why24AppendixGate)
    (word : Why24AppendixANF.Word) : ZMod 2 :=
  match gate with
  | .z site => word site
  | .cz left right => word left * word right
  | .ccz first second third => word first * word second * word third

/-- Boolean phase obtained by folding a literal Appendix-A gate list. -/
def why24AppendixWordPhaseList (gates : List Why24AppendixGate)
    (word : Why24AppendixANF.Word) : ZMod 2 :=
  gates.foldr (fun gate phase => why24AppendixWordGatePhase gate word + phase) 0

private theorem gateListANF_append (left right : List Why24AppendixGate) :
    why24AppendixGateListANF (left ++ right) =
      why24AppendixGateListANF left + why24AppendixGateListANF right := by
  induction left with
  | nil => simp [why24AppendixGateListANF]
  | cons gate gates ih =>
      change why24AppendixGateANF gate +
          why24AppendixGateListANF (gates ++ right) =
        (why24AppendixGateANF gate + why24AppendixGateListANF gates) +
          why24AppendixGateListANF right
      rw [ih, add_assoc]

private theorem gateListANF_eq_sum_map (gates : List Why24AppendixGate) :
    why24AppendixGateListANF gates =
      (gates.map why24AppendixGateANF).sum := by
  induction gates with
  | nil => rfl
  | cons gate gates ih =>
      change why24AppendixGateANF gate + why24AppendixGateListANF gates =
        why24AppendixGateANF gate +
          (gates.map why24AppendixGateANF).sum
      rw [ih]

private theorem zGateListANF_eq :
    why24AppendixGateListANF why24AppendixZGateList =
      ∑ site : Fin 10, generator site := by
  rw [gateListANF_eq_sum_map]
  simp only [why24AppendixZGateList, List.map_ofFn, why24AppendixGateANF,
    Function.comp_apply, Fin.sum_ofFn]

private theorem quadraticGateListANF_eq :
    why24AppendixGateListANF
        (quadraticGatePairs.map (fun pair => .cz pair.1 pair.2)) =
      ∑ left : Fin 10, ∑ right : Fin 10,
        if left < right then
          quadraticGateCoefficient left right •
            (generator left * generator right)
        else 0 := by
  rw [gateListANF_eq_sum_map]
  simp only [List.map_map]
  calc
    (quadraticGatePairs.map
        (fun pair => generator pair.1 * generator pair.2)).sum =
        ∑ pair : Fin 10 × Fin 10,
          if pair.1 < pair.2 then
            quadraticGateCoefficient pair.1 pair.2 •
              (generator pair.1 * generator pair.2)
          else 0 := quadraticGatePairs_ANF_sum
    _ = ∑ left : Fin 10, ∑ right : Fin 10,
        if left < right then
          quadraticGateCoefficient left right •
            (generator left * generator right)
        else 0 := by
      rw [Fintype.sum_prod_type]

private theorem cubicGateListANF_eq :
    why24AppendixGateListANF
        (cubicGateTriples.map
          (fun triple => .ccz triple.1 triple.2.1 triple.2.2)) =
      ∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
        if first < second ∧ second < third then
          cubicGateCoefficient first second third •
            (generator first * generator second * generator third)
        else 0 := by
  rw [gateListANF_eq_sum_map]
  simp only [List.map_map]
  calc
    (cubicGateTriples.map
        (fun triple => generator triple.1 * generator triple.2.1 *
          generator triple.2.2)).sum =
        ∑ triple : Fin 10 × Fin 10 × Fin 10,
          if triple.1 < triple.2.1 ∧ triple.2.1 < triple.2.2 then
            cubicGateCoefficient triple.1 triple.2.1 triple.2.2 •
              (generator triple.1 * generator triple.2.1 *
                generator triple.2.2)
          else 0 := cubicGateTriples_ANF_sum
    _ = ∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
        if first < second ∧ second < third then
          cubicGateCoefficient first second third •
            (generator first * generator second * generator third)
        else 0 := by
      exact fintype_sum_triple (fun first second third =>
        if first < second ∧ second < third then
          cubicGateCoefficient first second third •
            (generator first * generator second * generator third)
        else 0)

/-- The literal Appendix-A gate list denotes exactly the sparse target ANF. -/
theorem why24AppendixGateListANF_eq_gatePhasePolynomial :
    why24AppendixGateListANF why24AppendixGateList = gatePhasePolynomial := by
  rw [why24AppendixGateList, gateListANF_append, gateListANF_append,
    zGateListANF_eq, quadraticGateListANF_eq, cubicGateListANF_eq,
    gatePhasePolynomial]

theorem why24AppendixWordPhaseList_eq_evaluate_gateListANF
    (gates : List Why24AppendixGate) (word : Why24AppendixANF.Word) :
    why24AppendixWordPhaseList gates word =
      evaluate word (why24AppendixGateListANF gates) := by
  induction gates with
  | nil => simp [why24AppendixWordPhaseList, why24AppendixGateListANF]
  | cons gate gates ih =>
      simp only [why24AppendixWordPhaseList, why24AppendixGateListANF,
        List.foldr_cons, map_add] at ih ⊢
      rw [ih]
      cases gate with
      | z site =>
          simp [why24AppendixWordGatePhase, why24AppendixGateANF,
            evaluate_generator]
      | cz left right =>
          simp [why24AppendixWordGatePhase, why24AppendixGateANF,
            evaluate_generator]
      | ccz first second third =>
          simp [why24AppendixWordGatePhase, why24AppendixGateANF,
            evaluate_generator]

/-- The literal Appendix-A phase fold is evaluation of the certified target
sparse polynomial. -/
theorem why24AppendixWordPhaseList_eq_evaluate_gatePhasePolynomial
    (word : Why24AppendixANF.Word) :
    why24AppendixWordPhaseList why24AppendixGateList word =
      evaluate word gatePhasePolynomial := by
  rw [why24AppendixWordPhaseList_eq_evaluate_gateListANF,
    why24AppendixGateListANF_eq_gatePhasePolynomial]

/-- The literal Appendix-A phase fold equals the concrete selected-basis
seventh-power trace for every Boolean word. -/
theorem why24AppendixWordPhaseList_eq_trace
    (word : Why24AppendixANF.Word) :
    why24AppendixWordPhaseList why24AppendixGateList word =
      Algebra.trace (ZMod 2) F1024
        ((f1024SelectedCoordinates.symm word) ^ 7) := by
  rw [why24AppendixWordPhaseList_eq_evaluate_gatePhasePolynomial,
    ← sourcePhasePolynomial_eq_gatePhasePolynomial,
    evaluate_sourcePhasePolynomial]

end QEC.Coding
