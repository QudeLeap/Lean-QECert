import QEC.Coding.AlgebraicGeometry.Codes.CodeDuality
import QEC.Coding.AlgebraicGeometry.Codes.ResiduePairing
import QEC.Coding.AlgebraicGeometry.Codes.EvaluationInterpolation

/-!
# AG-code parameters under an equal constant-field algebra

The Riemann--Roch construction uses the constant algebra induced by the
polynomial chart. A concrete function field can carry an equal algebra with
a different instance expression. These lemmas transport the actual code and
place types along a proved equality, without identifying unequal structures
by an elaborator convention or assuming any parameter conclusion.
-/

namespace QEC.Coding.AlgebraicGeometry

noncomputable section

variable (k F : Type*) [Field k] [Fintype k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
variable [κ : Algebra k F]
variable [@IsFullConstantField k F _ _ (@AffinePlace.constantAlgebra k F _ _ π)]
variable {ι : Type*} [Fintype ι]

/-- Exact evaluation dimension, transported along an actual algebra equality. -/
theorem agEvaluation_dimension_eq_of_constantAlgebra_eq
    (hκ : κ = @AffinePlace.constantAlgebra k F _ _ π)
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0)
    (hlarge : 2 * (GlobalPlace.functionFieldGenus
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 1 ≤
        Divisor.degree GlobalPlace.residueDegree G)
    (hsmall : Divisor.degree GlobalPlace.residueDegree G < Fintype.card ι) :
    (Dimension (agEvaluationCode G Q hG) : ℤ) =
      Divisor.degree GlobalPlace.residueDegree G + 1 -
        (GlobalPlace.functionFieldGenus
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) := by
  subst κ
  exact agEvaluation_dimension_eq_of_large_degree k F G Q hQ hG hlarge hsmall

/-- Designed dual distance is preserved under the same constant-algebra equality. -/
theorem agEvaluation_dual_distance_of_constantAlgebra_eq
    [Nonempty ι] [DecidableEq k] [DecidableEq ι]
    (hκ : κ = @AffinePlace.constantAlgebra k F _ _ π)
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0)
    (hlarge : 2 * (GlobalPlace.functionFieldGenus
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 1 ≤
        Divisor.degree GlobalPlace.residueDegree G)
    (hsmall : Divisor.degree GlobalPlace.residueDegree G < Fintype.card ι) :
    (Int.toNat (Divisor.degree GlobalPlace.residueDegree G + 2 -
      2 * (GlobalPlace.functionFieldGenus
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ)) : WithTop ℕ) ≤
      HypergraphProduct.extendedMinimumDistance (agEvaluationCode G Q hG).dual := by
  subst κ
  exact agEvaluation_dual_distance_lower_bound k F G Q hQ hG hlarge hsmall

omit [@IsFullConstantField k F _ _ (@AffinePlace.constantAlgebra k F _ _ π)] in
/-- Orthogonality for a specified differential, under an equal constant algebra. -/
theorem agEvaluation_le_dual_of_residue_of_constantAlgebra_eq
    [IsScalarTower k (RatFunc k) F]
    (hκ : κ = @AffinePlace.constantAlgebra k F _ _ π)
    (G H : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0) (hH : ∀ j, H (Q j).place = 0)
    (eta : Differential k F) (heta : eta ≠ 0)
    (etaAt : ∀ j, Differential.simplePoleDifferentialLattice (Q j).place)
    (hAt : ∀ j, (etaAt j : Differential k F) = eta)
    (hres : ∀ j, Differential.simplePoleResidue (Q j).place (etaAt j) = 1)
    (hGH : G + H ≤ FunctionFieldDifferential.differentialDivisor eta heta + evaluationDivisor Q) :
    (agEvaluationCode H Q hH).carrier ≤ (agEvaluationCode G Q hG).dual.carrier := by
  subst κ
  exact agEvaluation_le_dual_of_residue k F G H Q hQ hG hH eta heta etaAt hAt hres hGH

/-- Interpolation is preserved under a proved equality of constant-field algebras. -/
theorem agEvaluation_surjective_of_constantAlgebra_eq
    (hκ : κ = @AffinePlace.constantAlgebra k F _ _ π)
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0)
    (hlarge : 2 * (GlobalPlace.functionFieldGenus
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 1 ≤
        Divisor.degree GlobalPlace.residueDegree G - Fintype.card ι) :
    Function.Surjective (agEvaluationLinearMap G Q hG) := by
  subst κ
  exact agEvaluation_surjective_of_sub_degree k F G Q hQ hG hlarge

end

end QEC.Coding.AlgebraicGeometry
