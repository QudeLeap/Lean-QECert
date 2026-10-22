import QEC.Coding.AlgebraicGeometry.Codes.NormalClosureDivisor
import QEC.Coding.AlgebraicGeometry.Codes.ConstantFieldTransport

/-!
# Evaluation codes of the explicit normal-closure family

The code is the actual evaluation range for the divisor chosen in
[Ngu24, Theorem: AG multiplication family]. The all-ones word and parameter
bounds are derived from that range and the proved function-field data.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

/-- The source's actual code, with the selected places as its finite coordinates. -/
def f256MultiplicationCode (i : ℕ) : LinearCode F256 (Fin (f256GarciaStichtenothLength i)) :=
  agEvaluationCode (f256MultiplicationDivisor i) (f256GarciaStichtenothSelectedRationalPlace i)
    (f256MultiplicationDivisor_selected_eq_zero i)

theorem f256GarciaStichtenothDivisorD_eq_evaluationDivisor (i : ℕ) :
    f256GarciaStichtenothDivisorD i =
      evaluationDivisor (f256GarciaStichtenothSelectedRationalPlace i) := rfl

/-- The actual unit-residue differential gives the paper's multiplication property. -/
theorem f256MultiplicationCode_starSquare_le_dual (i : ℕ) :
    agStarProduct (f256MultiplicationCode i) (f256MultiplicationCode i) ≤
      (f256MultiplicationCode i).dual.carrier := by
  let G := f256MultiplicationDivisor i
  let Q := f256GarciaStichtenothSelectedRationalPlace i
  have hG := f256MultiplicationDivisor_selected_eq_zero i
  apply le_trans (starProduct_le_agEvaluationCode_add G G Q hG hG)
  apply agEvaluation_le_dual_of_residue_of_constantAlgebra_eq F256
    (f256GarciaStichtenothField i)
    (π := f256GarciaStichtenothPolynomialAlgebra i)
    (ρ := f256GarciaStichtenothRatFuncAlgebra i)
    (τ := f256GarciaStichtenothPolynomialTower i)
    (φ := f256GarciaStichtenothFunctionField i)
    (s := f256GarciaStichtenothSeparable i)
    (sourceClosureDirectConstant_eq (i + 2)).symm G (G + G) Q
    (f256GarciaStichtenothSelectedPlace_injective i) hG
    (evaluationSupport_add G G Q hG hG)
    (f256GarciaStichtenothCanonicalDifferential i)
    (f256GarciaStichtenothCanonicalDifferential_ne_zero i)
    (fun j => f256GarciaStichtenothCanonicalDifferentialAtPlace i
      (f256GarciaStichtenothSelectedPlace i j))
    (fun j => f256GarciaStichtenothCanonicalDifferentialAtPlace_coe i
      (f256GarciaStichtenothSelectedPlace i j))
    (f256GarciaStichtenothCanonicalDifferential_selected_residue i)
  have hthree : G + (G + G) = (3 : ℤ) • G := by
    ext P
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    ring
  rw [hthree]
  exact three_mul_f256MultiplicationDivisor_le i

theorem f256MultiplicationCode_one_mem (i : ℕ) :
    (1 : Word F256 (Fin (f256GarciaStichtenothLength i))) ∈
      (f256MultiplicationCode i).carrier :=
  agEvaluation_one_mem (f256MultiplicationDivisor i)
    (f256GarciaStichtenothSelectedRationalPlace i)
    (f256MultiplicationDivisor_selected_eq_zero i) (f256MultiplicationDivisor_nonnegative i)

theorem f256MultiplicationCode_dimension_eq (i : ℕ) :
    (Dimension (f256MultiplicationCode i) : ℤ) =
      Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) + 1 -
        f256GarciaStichtenothGenus i := by
  exact agEvaluation_dimension_eq_of_constantAlgebra_eq F256 (f256GarciaStichtenothField i)
      (π := f256GarciaStichtenothPolynomialAlgebra i)
      (ρ := f256GarciaStichtenothRatFuncAlgebra i)
      (τ := f256GarciaStichtenothPolynomialTower i)
      (φ := f256GarciaStichtenothFunctionField i)
      (s := f256GarciaStichtenothSeparable i)
      (sourceClosureDirectConstant_eq (i + 2)).symm
      (f256MultiplicationDivisor i) (f256GarciaStichtenothSelectedRationalPlace i)
      (f256GarciaStichtenothSelectedPlace_injective i)
      (f256MultiplicationDivisor_selected_eq_zero i)
      (f256MultiplicationDivisor_large_degree i)
      (by simpa only [Fintype.card_fin] using f256MultiplicationDivisor_degree_lt_length i)

theorem f256MultiplicationCode_dimension_lower (i : ℕ) :
    f256GarciaStichtenothLength i ≤ 4 * Dimension (f256MultiplicationCode i) := by
  have h := f256MultiplicationDivisor_dimension_numerator i
  rw [← f256MultiplicationCode_dimension_eq] at h
  exact_mod_cast h

theorem f256MultiplicationCode_distance_lower (i : ℕ) :
    (((f256GarciaStichtenothLength i + 3) / 4 : ℕ) : WithTop ℕ) ≤
      HypergraphProduct.extendedMinimumDistance (f256MultiplicationCode i) := by
  classical
  have h := agEvaluation_distance_lower_bound (f256MultiplicationDivisor i)
    (f256GarciaStichtenothSelectedRationalPlace i)
    (f256GarciaStichtenothSelectedPlace_injective i)
    (f256MultiplicationDivisor_selected_eq_zero i)
  have hu := f256MultiplicationDivisor_degree_upper i
  have hb : (f256GarciaStichtenothLength i + 3) / 4 ≤
      Int.toNat ((Fintype.card (Fin (f256GarciaStichtenothLength i)) : ℤ) -
        Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i)) := by
    simp only [Fintype.card_fin]
    omega
  exact le_trans (WithTop.coe_le_coe.mpr hb) h

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
