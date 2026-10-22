import QEC.Coding.QuditQubitConversion.AppendixANF.Quadratic.Certificate
import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Certificate

/-!
# Symbolic composition of the WHY24 Appendix-A ANF certificate

This module turns the separately compiled coefficient certificates into one
sparse polynomial identity.  It reasons about monomial supports and never
enumerates Boolean input words.
-/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

open scoped BigOperators
open Why24BooleanANF

theorem generator_mul_generator (left right : Fin 10) :
    generator left * generator right =
      MonoidAlgebra.single ⟨{left, right}⟩ 1 := by
  have hmonomial :
      (⟨{left}⟩ : Monomial 10) * ⟨{right}⟩ = ⟨{left, right}⟩ := by
    apply Monomial.ext
    simp only [mul_support]
    simp
  simp only [generator]
  rw [MonoidAlgebra.single_mul_single, hmonomial, one_mul]

theorem generator_mul_generator_mul_generator
    (first second third : Fin 10) :
    generator first * generator second * generator third =
      MonoidAlgebra.single ⟨{first, second, third}⟩ 1 := by
  rw [generator_mul_generator]
  simp only [generator]
  rw [MonoidAlgebra.single_mul_single, one_mul]
  congr 1
  apply Monomial.ext
  simp only [mul_support]
  simp

private theorem sourcePhaseSummand_apply
    (first second third : Fin 10) (monomial : Monomial 10) :
    (traceTensor first second third •
        (generator first * generator second * generator third)).coeff monomial =
      if tripleSupport first second third = monomial.support then
        traceTensor first second third
      else 0 := by
  have heq :
      (⟨{first, second, third}⟩ : Monomial 10) = monomial ↔
        tripleSupport first second third = monomial.support := by
    constructor
    · intro h
      simpa only [tripleSupport] using congrArg Monomial.support h
    · intro h
      apply Monomial.ext
      simpa only [tripleSupport] using h
  rw [generator_mul_generator_mul_generator]
  simp only [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply, heq, smul_eq_mul]
  split_ifs <;> simp

/-- Coefficients of the sparse source polynomial are exactly the normalized
ordered-tensor coefficients certified in the preceding modules. -/
theorem sourcePhasePolynomial_apply (monomial : Monomial 10) :
    sourcePhasePolynomial.coeff monomial = sourceCoefficient monomial.support := by
  classical
  let coefficient : ANF →ₗ[ZMod 2] ZMod 2 :=
    (Finsupp.lapply monomial).comp (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).toLinearMap
  change coefficient sourcePhasePolynomial = sourceCoefficient monomial.support
  rw [sourcePhasePolynomial, sourceCoefficient, map_sum]
  apply Finset.sum_congr rfl
  intro first _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro second _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro third _
  change
    (traceTensor first second third •
      (generator first * generator second * generator third)).coeff monomial = _
  exact sourcePhaseSummand_apply first second third monomial

end QEC.Coding.Why24AppendixANF
