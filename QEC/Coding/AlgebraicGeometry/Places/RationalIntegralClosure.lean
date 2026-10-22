import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.IsIntegral

open scoped Polynomial RatFunc

namespace QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure

abbrev K : Type := ZMod 2

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev F : Type := RatFunc K
abbrev B : Type := FunctionField.ringOfIntegers K F

local instance : IsIntegralClosure K[X] K[X] F :=
  IsIntegralClosure.of_isIntegrallyClosed K[X] K[X] F

noncomputable def ringOfIntegersToPolynomial : B ≃ₐ[K[X]] K[X] :=
  IsIntegralClosure.equiv K[X] B F K[X]

noncomputable def directIntegralClosureEquiv : K[X] ≃ₐ[K[X]] B :=
  ringOfIntegersToPolynomial.symm

theorem algebraMap_ringOfIntegersToPolynomial (b : B) :
    algebraMap K[X] F (ringOfIntegersToPolynomial b) = algebraMap B F b :=
  IsIntegralClosure.algebraMap_equiv K[X] B F K[X] b

theorem algebraMap_directIntegralClosureEquiv (p : K[X]) :
    algebraMap B F (directIntegralClosureEquiv p) = algebraMap K[X] F p := by
  have h := algebraMap_ringOfIntegersToPolynomial (directIntegralClosureEquiv p)
  simpa only [directIntegralClosureEquiv, AlgEquiv.apply_symm_apply] using h.symm

end QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure
