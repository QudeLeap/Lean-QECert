import QEC.Coding.AlgebraicGeometry.Codes.NormalClosureShortening

/-!
# Local interpolation in the shortened normal-closure codes

Riemann--Roch on the actual shortened divisor permits arbitrary values on
every retained region smaller than the proved shortened dual-distance bound.
This is the classical input to local-error detection for the coset encoder.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

/-- Small retained regions leave the shortened divisor in the large-degree range. -/
theorem f256ShortenedMultiplicationDivisor_sub_region_large (i : ℕ)
    (S : Finset (F256MultiplicationRetained i))
    (hS : S.card < (f256GarciaStichtenothLength i + 4) / 5 -
      f256MultiplicationLogicalCount i) :
    2 * (f256GarciaStichtenothGenus i : ℤ) - 1 ≤
      Divisor.degree GlobalPlace.residueDegree (f256ShortenedMultiplicationDivisor i) -
        Fintype.card S := by
  rw [f256ShortenedMultiplicationDivisor_degree, Fintype.card_coe]
  have h := f256MultiplicationDivisor_dual_distance_numerator i
  have hn := f256GarciaStichtenothLength_two_hundred_forty_le i
  unfold f256MultiplicationLogicalCount at *
  omega

/-- Arbitrary field values on a sufficiently small retained region are attained
by actual shortened-code words, via Riemann--Roch interpolation. -/
theorem f256ShortenedMultiplicationCode_restrict_surjective (i : ℕ)
    (S : Finset (F256MultiplicationRetained i))
    (hS : S.card < (f256GarciaStichtenothLength i + 4) / 5 -
      f256MultiplicationLogicalCount i) :
    Function.Surjective (fun x : (f256ShortenedMultiplicationCode i).carrier =>
      fun j : S => x.val j.val) := by
  classical
  have honto := agEvaluation_surjective_of_constantAlgebra_eq F256
    (f256GarciaStichtenothField i)
    (π := f256GarciaStichtenothPolynomialAlgebra i)
    (ρ := f256GarciaStichtenothRatFuncAlgebra i)
    (τ := f256GarciaStichtenothPolynomialTower i)
    (φ := f256GarciaStichtenothFunctionField i)
    (s := f256GarciaStichtenothSeparable i)
    (sourceClosureDirectConstant_eq (i + 2)).symm
    (f256ShortenedMultiplicationDivisor i)
    (fun j : S => f256GarciaStichtenothSelectedRationalPlace i j.val.val)
    ((f256GarciaStichtenothSelectedPlace_injective i).comp
      (Subtype.val_injective.comp Subtype.val_injective))
    (fun j => f256ShortenedMultiplicationDivisor_retained_eq_zero i j.val)
    (f256ShortenedMultiplicationDivisor_sub_region_large i S hS)
  intro values
  obtain ⟨a, ha⟩ := honto values
  refine ⟨⟨agEvaluationLinearMap (f256ShortenedMultiplicationDivisor i)
    (fun j : F256MultiplicationRetained i => f256GarciaStichtenothSelectedRationalPlace i j.val)
    (f256ShortenedMultiplicationDivisor_retained_eq_zero i) a, ⟨a, rfl⟩⟩, ?_⟩
  exact ha

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
