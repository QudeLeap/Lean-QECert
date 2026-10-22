import QEC.Coding.AlgebraicGeometry.Codes.EvaluationKernel
import QEC.Coding.AlgebraicGeometry.RiemannRoch.Theorem

/-!
# Interpolation at rational places from Riemann--Roch

If subtracting all evaluation places leaves a divisor of degree at least
`2g - 1`, evaluation is onto. The exact kernel and two Riemann--Roch
dimension formulas prove this; no independent interpolation assumption is used.
-/

namespace QEC.Coding.AlgebraicGeometry

noncomputable section

variable (k F : Type*) [Field k] [Fintype k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]

local instance interpolationConstantAlgebra : Algebra k F := AffinePlace.constantAlgebra k F
local instance interpolationConstantTower : IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
local instance interpolationFiniteDimensional (G : Divisor (GlobalPlace k F)) :
    FiniteDimensional k (GlobalPlace.riemannRochSubmodule G) :=
  GlobalPlace.finiteDimensional_riemannRochSubmodule
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G

variable [IsFullConstantField k F] {ι : Type*} [Fintype ι]

/-- Riemann--Roch proves that arbitrary values can be prescribed on the selected places. -/
theorem agEvaluation_surjective_of_sub_degree
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0)
    (hlarge : 2 * (GlobalPlace.functionFieldGenus
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 1 ≤
        Divisor.degree GlobalPlace.residueDegree G - Fintype.card ι) :
    Function.Surjective (agEvaluationLinearMap G Q hG) := by
  let T := agEvaluationLinearMap G Q hG
  have hdegree : Divisor.degree GlobalPlace.residueDegree (G - evaluationDivisor Q) =
      Divisor.degree GlobalPlace.residueDegree G - Fintype.card ι := by
    rw [Divisor.degree_sub, evaluationDivisor_degree_eq_card]
  have hbase := GlobalPlace.riemannRoch_eq_of_large_degree
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
    (G - evaluationDivisor Q) (by rw [hdegree]; exact hlarge)
  have htotal := GlobalPlace.riemannRoch_eq_of_large_degree
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G (by omega)
  change (Module.finrank k (GlobalPlace.riemannRochSubmodule
    (G - evaluationDivisor Q)) : ℤ) = _ at hbase
  change (Module.finrank k (GlobalPlace.riemannRochSubmodule G) : ℤ) = _ at htotal
  rw [hdegree] at hbase
  have hker := (agEvaluationKernelEquiv G Q hQ hG).finrank_eq
  change Module.finrank k T.ker = _ at hker
  have hrank := T.finrank_range_add_finrank_ker
  have hrankInt := congrArg (fun n : ℕ => (n : ℤ)) hrank
  simp only [Nat.cast_add] at hrankInt
  rw [hker] at hrankInt
  have hrange : Module.finrank k T.range = Fintype.card ι := by omega
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simpa using hrange

end

end QEC.Coding.AlgebraicGeometry
