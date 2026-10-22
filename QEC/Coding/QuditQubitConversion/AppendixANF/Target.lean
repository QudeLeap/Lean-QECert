import QEC.Coding.QuditQubitConversion.AppendixANF.Symbolic

/-!
# Canonical sparse target polynomial for the WHY24 Appendix-A list

The target is expressed by its linear, increasing-pair, and increasing-triple
terms.  Its coefficient interface uses the sorted coordinates of a support;
no Boolean word is enumerated.
-/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

open scoped BigOperators
open Why24BooleanANF

/-- Literal gate-list coefficient indexed by a squarefree monomial support. -/
def gateCoefficient (support : Finset (Fin 10)) : ZMod 2 :=
  if hsingle : support.card = 1 then 1
  else if hpair : support.card = 2 then
    quadraticGateCoefficient
      (support.orderEmbOfFin hpair (0 : Fin 2))
      (support.orderEmbOfFin hpair (1 : Fin 2))
  else if htriple : support.card = 3 then
    cubicGateCoefficient
      (support.orderEmbOfFin htriple (0 : Fin 3))
      (support.orderEmbOfFin htriple (1 : Fin 3))
      (support.orderEmbOfFin htriple (2 : Fin 3))
  else 0

/-- Coefficient formula obtained directly from the three target term sums. -/
def expandedGateCoefficient (support : Finset (Fin 10)) : ZMod 2 :=
  (∑ coordinate : Fin 10, if {coordinate} = support then 1 else 0) +
  (∑ left : Fin 10, ∑ right : Fin 10,
    if left < right ∧ {left, right} = support then
      quadraticGateCoefficient left right
    else 0) +
  (∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
    if first < second ∧ second < third ∧
        {first, second, third} = support then
      cubicGateCoefficient first second third
    else 0)

/-- Sparse polynomial represented by the ten linear, twenty quadratic, and
seventy cubic terms of the literal target list. -/
def gatePhasePolynomial : ANF :=
  (∑ coordinate : Fin 10, generator coordinate) +
  (∑ left : Fin 10, ∑ right : Fin 10,
    if left < right then
      quadraticGateCoefficient left right • (generator left * generator right)
    else 0) +
  (∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
    if first < second ∧ second < third then
      cubicGateCoefficient first second third •
        (generator first * generator second * generator third)
    else 0)

private theorem singleSupport_smul_apply (support : Finset (Fin 10))
    (coefficient : ZMod 2) (monomial : Monomial 10) :
    (coefficient • MonoidAlgebra.single ⟨support⟩ 1 : ANF).coeff monomial =
      if support = monomial.support then coefficient else 0 := by
  have heq : (⟨support⟩ : Monomial 10) = monomial ↔
      support = monomial.support := by
    constructor
    · intro h
      exact congrArg Monomial.support h
    · intro h
      exact Monomial.ext h
  simp only [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply, heq, smul_eq_mul]
  split_ifs <;> simp

private theorem generator_apply (coordinate : Fin 10) (monomial : Monomial 10) :
    (generator coordinate).coeff monomial =
      if {coordinate} = monomial.support then 1 else 0 := by
  rw [generator]
  simpa only [one_smul] using
    (singleSupport_smul_apply {coordinate} 1 monomial)

private theorem pairSummand_apply (left right : Fin 10)
    (monomial : Monomial 10) :
    (quadraticGateCoefficient left right •
        (generator left * generator right)).coeff monomial =
      if {left, right} = monomial.support then
        quadraticGateCoefficient left right
      else 0 := by
  rw [generator_mul_generator]
  exact singleSupport_smul_apply {left, right}
    (quadraticGateCoefficient left right) monomial

private theorem tripleSummand_apply (first second third : Fin 10)
    (monomial : Monomial 10) :
    (cubicGateCoefficient first second third •
        (generator first * generator second * generator third)).coeff monomial =
      if {first, second, third} = monomial.support then
        cubicGateCoefficient first second third
      else 0 := by
  rw [generator_mul_generator_mul_generator]
  exact singleSupport_smul_apply {first, second, third}
    (cubicGateCoefficient first second third) monomial

/-- Coefficient of the target polynomial before support-cardinality
normalization. -/
theorem gatePhasePolynomial_apply_expanded (monomial : Monomial 10) :
    gatePhasePolynomial.coeff monomial = expandedGateCoefficient monomial.support := by
  classical
  let coefficient : ANF →ₗ[ZMod 2] ZMod 2 :=
    (Finsupp.lapply monomial).comp (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).toLinearMap
  change coefficient gatePhasePolynomial = expandedGateCoefficient monomial.support
  have hlinear :
      coefficient (∑ coordinate : Fin 10, generator coordinate) =
        ∑ coordinate : Fin 10,
          if {coordinate} = monomial.support then 1 else 0 := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro coordinate _
    exact generator_apply coordinate monomial
  have hpair :
      coefficient
          (∑ left : Fin 10, ∑ right : Fin 10,
            if left < right then
              quadraticGateCoefficient left right •
                (generator left * generator right)
            else 0) =
        ∑ left : Fin 10, ∑ right : Fin 10,
          if left < right ∧ {left, right} = monomial.support then
            quadraticGateCoefficient left right
          else 0 := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro left _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro right _
    by_cases hlt : left < right
    · rw [if_pos hlt]
      change
        (quadraticGateCoefficient left right •
          (generator left * generator right)).coeff monomial = _
      rw [pairSummand_apply]
      simp only [hlt, true_and]
    · rw [if_neg hlt]
      simp [hlt]
  have htriple :
      coefficient
          (∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
            if first < second ∧ second < third then
              cubicGateCoefficient first second third •
                (generator first * generator second * generator third)
            else 0) =
        ∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
          if first < second ∧ second < third ∧
              {first, second, third} = monomial.support then
            cubicGateCoefficient first second third
          else 0 := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro first _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro second _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro third _
    by_cases hlt : first < second ∧ second < third
    · rw [if_pos hlt]
      change
        (cubicGateCoefficient first second third •
          (generator first * generator second * generator third)).coeff monomial = _
      rw [tripleSummand_apply]
      simp only [hlt.1, hlt.2, true_and]
    · rw [if_neg hlt]
      split_ifs with h
      · exact (hlt ⟨h.1, h.2.1⟩).elim
      · exact map_zero coefficient
  rw [gatePhasePolynomial, expandedGateCoefficient, map_add, map_add,
    hlinear, hpair, htriple]

end QEC.Coding.Why24AppendixANF
