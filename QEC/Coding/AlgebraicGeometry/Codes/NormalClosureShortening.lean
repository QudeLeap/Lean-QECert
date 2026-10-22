import QEC.Coding.AlgebraicGeometry.Codes.NormalClosureEvaluation
import QEC.Coding.AlgebraicGeometry.Codes.EvaluationShortening

/-!
# The concrete shortened multiplication-code family

Take the first `K = floor (n / 10)` selected places. Riemann--Roch proves
surjectivity onto these coordinates. Subtracting their actual divisor gives
the shortened AG code and the dual-distance estimate from
[Ngu24, Theorem: AG multiplication family].
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

def f256MultiplicationLogicalCount (i : ℕ) : ℕ := f256GarciaStichtenothLength i / 10

theorem f256MultiplicationLogicalCount_pos (i : ℕ) : 0 < f256MultiplicationLogicalCount i := by
  have h := f256GarciaStichtenothLength_two_hundred_forty_le i
  unfold f256MultiplicationLogicalCount
  omega

theorem f256MultiplicationLogicalCount_lt_fifth (i : ℕ) :
    5 * f256MultiplicationLogicalCount i < f256GarciaStichtenothLength i := by
  have h := f256GarciaStichtenothLength_two_hundred_forty_le i
  unfold f256MultiplicationLogicalCount
  omega

def f256MultiplicationPivot (i : ℕ) :
    Fin (f256MultiplicationLogicalCount i) ↪ Fin (f256GarciaStichtenothLength i) where
  toFun a := ⟨a.val, lt_of_lt_of_le a.isLt (Nat.div_le_self _ _)⟩
  inj' _ _ h := Fin.ext (congrArg (fun j : Fin (f256GarciaStichtenothLength i) => j.val) h)

def F256MultiplicationRetained (i : ℕ) : Type :=
  {j : Fin (f256GarciaStichtenothLength i) // j ∉ Set.range (f256MultiplicationPivot i)}

instance f256MultiplicationRetainedDecidableEq (i : ℕ) : DecidableEq (F256MultiplicationRetained i) :=
  Classical.decEq _

instance f256MultiplicationRetainedFintype (i : ℕ) : Fintype (F256MultiplicationRetained i) := by
  unfold F256MultiplicationRetained
  exact Fintype.ofFinite _

theorem f256MultiplicationRetained_card (i : ℕ) :
    Fintype.card (F256MultiplicationRetained i) =
      f256GarciaStichtenothLength i - f256MultiplicationLogicalCount i := by
  classical
  letI : Fintype (Set.range (f256MultiplicationPivot i)) := Fintype.ofFinite _
  rw [Fintype.card_congr (show F256MultiplicationRetained i ≃
    {j : Fin (f256GarciaStichtenothLength i) // j ∉ Set.range (f256MultiplicationPivot i)} from
      Equiv.refl _)]
  rw [Fintype.card_subtype_compl, Fintype.card_fin]
  congr 1
  simpa only [Fintype.card_fin] using
    (Fintype.card_congr (Equiv.ofInjective (f256MultiplicationPivot i)
      (f256MultiplicationPivot i).injective)).symm

instance f256MultiplicationRetainedNonempty (i : ℕ) : Nonempty (F256MultiplicationRetained i) := by
  apply Fintype.card_pos_iff.mp
  rw [f256MultiplicationRetained_card]
  have h := f256MultiplicationLogicalCount_lt_fifth i
  omega

def f256ShortenedMultiplicationDivisor (i : ℕ) :
    Divisor (GlobalPlace F256 (f256GarciaStichtenothField i)) :=
  f256MultiplicationDivisor i - evaluationDivisor
    (fun a => f256GarciaStichtenothSelectedRationalPlace i (f256MultiplicationPivot i a))

theorem f256ShortenedMultiplicationDivisor_degree (i : ℕ) :
    Divisor.degree GlobalPlace.residueDegree (f256ShortenedMultiplicationDivisor i) =
      Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) -
        f256MultiplicationLogicalCount i := by
  rw [f256ShortenedMultiplicationDivisor, Divisor.degree_sub,
    evaluationDivisor_degree_eq_card, Fintype.card_fin]

theorem f256ShortenedMultiplicationDivisor_large_degree (i : ℕ) :
    2 * (f256GarciaStichtenothGenus i : ℤ) - 1 ≤
      Divisor.degree GlobalPlace.residueDegree (f256ShortenedMultiplicationDivisor i) := by
  rw [f256ShortenedMultiplicationDivisor_degree]
  have h := f256MultiplicationDivisor_dual_distance_numerator i
  have hn := f256GarciaStichtenothLength_two_hundred_forty_le i
  unfold f256MultiplicationLogicalCount
  omega

theorem f256ShortenedMultiplicationDivisor_small_degree (i : ℕ) :
    Divisor.degree GlobalPlace.residueDegree (f256ShortenedMultiplicationDivisor i) <
      Fintype.card (F256MultiplicationRetained i) := by
  rw [f256ShortenedMultiplicationDivisor_degree, f256MultiplicationRetained_card]
  have h := f256MultiplicationDivisor_degree_lt_length i
  have hK := f256MultiplicationLogicalCount_lt_fifth i
  omega

theorem f256MultiplicationPivot_evaluation_surjective (i : ℕ) :
    Function.Surjective (agEvaluationLinearMap (f256MultiplicationDivisor i)
      (fun a => f256GarciaStichtenothSelectedRationalPlace i (f256MultiplicationPivot i a))
      (fun a => f256MultiplicationDivisor_selected_eq_zero i (f256MultiplicationPivot i a))) := by
  apply agEvaluation_surjective_of_constantAlgebra_eq F256 (f256GarciaStichtenothField i)
    (π := f256GarciaStichtenothPolynomialAlgebra i)
    (ρ := f256GarciaStichtenothRatFuncAlgebra i)
    (τ := f256GarciaStichtenothPolynomialTower i)
    (φ := f256GarciaStichtenothFunctionField i)
    (s := f256GarciaStichtenothSeparable i)
    (sourceClosureDirectConstant_eq (i + 2)).symm
    (f256MultiplicationDivisor i) _
    ((f256GarciaStichtenothSelectedPlace_injective i).comp
      (f256MultiplicationPivot i).injective)
  have h := f256ShortenedMultiplicationDivisor_large_degree i
  rw [f256ShortenedMultiplicationDivisor_degree] at h
  simp only [Fintype.card_fin]
  exact h

theorem f256ShortenedMultiplicationDivisor_retained_eq_zero (i : ℕ)
    (j : F256MultiplicationRetained i) :
    f256ShortenedMultiplicationDivisor i (f256GarciaStichtenothSelectedPlace i j.val) = 0 :=
  evaluationSupport_sub_of_not_range (f256MultiplicationDivisor i)
    (f256GarciaStichtenothSelectedRationalPlace i)
    (f256GarciaStichtenothSelectedPlace_injective i)
    (f256MultiplicationDivisor_selected_eq_zero i) (f256MultiplicationPivot i) j

def f256ShortenedMultiplicationCode (i : ℕ) : LinearCode F256 (F256MultiplicationRetained i) :=
  agEvaluationCode (f256ShortenedMultiplicationDivisor i)
    (fun j : F256MultiplicationRetained i => f256GarciaStichtenothSelectedRationalPlace i j.val)
    (f256ShortenedMultiplicationDivisor_retained_eq_zero i)

/-- The concrete shortened AG code equals the source's zero-then-puncture construction. -/
theorem f256ShortenedMultiplicationCode_mem_iff (i : ℕ)
    (w : Word F256 (F256MultiplicationRetained i)) :
    w ∈ (f256ShortenedMultiplicationCode i).carrier ↔
      ∃ x ∈ (f256MultiplicationCode i).carrier,
        (∀ a, x (f256MultiplicationPivot i a) = 0) ∧
        (fun j : F256MultiplicationRetained i => x j.val) = w :=
  mem_agEvaluation_sub_divisor_iff_shortened (f256MultiplicationDivisor i)
    (f256GarciaStichtenothSelectedRationalPlace i)
    (f256GarciaStichtenothSelectedPlace_injective i)
    (f256MultiplicationDivisor_selected_eq_zero i) (f256MultiplicationPivot i) w

theorem f256ShortenedMultiplicationCode_dimension_eq (i : ℕ) :
    Dimension (f256ShortenedMultiplicationCode i) + f256MultiplicationLogicalCount i =
      Dimension (f256MultiplicationCode i) := by
  have h := agEvaluation_dimension_eq_of_constantAlgebra_eq F256 (f256GarciaStichtenothField i)
    (π := f256GarciaStichtenothPolynomialAlgebra i)
    (ρ := f256GarciaStichtenothRatFuncAlgebra i)
    (τ := f256GarciaStichtenothPolynomialTower i)
    (φ := f256GarciaStichtenothFunctionField i)
    (s := f256GarciaStichtenothSeparable i)
    (sourceClosureDirectConstant_eq (i + 2)).symm (f256ShortenedMultiplicationDivisor i)
    (fun j : F256MultiplicationRetained i => f256GarciaStichtenothSelectedRationalPlace i j.val)
    ((f256GarciaStichtenothSelectedPlace_injective i).comp Subtype.val_injective)
    (f256ShortenedMultiplicationDivisor_retained_eq_zero i)
    (f256ShortenedMultiplicationDivisor_large_degree i)
    (f256ShortenedMultiplicationDivisor_small_degree i)
  change (Dimension (f256ShortenedMultiplicationCode i) : ℤ) = _ at h
  rw [f256ShortenedMultiplicationDivisor_degree,
    f256GarciaStichtenothFunctionFieldGenus_eq] at h
  have hfull := f256MultiplicationCode_dimension_eq i
  omega

theorem f256ShortenedMultiplicationCode_dual_distance_lower (i : ℕ) :
    (((f256GarciaStichtenothLength i + 4) / 5 - f256MultiplicationLogicalCount i : ℕ) : WithTop ℕ) ≤
      HypergraphProduct.extendedMinimumDistance (f256ShortenedMultiplicationCode i).dual := by
  classical
  have h := agEvaluation_dual_distance_of_constantAlgebra_eq F256 (f256GarciaStichtenothField i)
    (π := f256GarciaStichtenothPolynomialAlgebra i)
    (ρ := f256GarciaStichtenothRatFuncAlgebra i)
    (τ := f256GarciaStichtenothPolynomialTower i)
    (φ := f256GarciaStichtenothFunctionField i)
    (s := f256GarciaStichtenothSeparable i)
    (sourceClosureDirectConstant_eq (i + 2)).symm (f256ShortenedMultiplicationDivisor i)
    (fun j : F256MultiplicationRetained i => f256GarciaStichtenothSelectedRationalPlace i j.val)
    ((f256GarciaStichtenothSelectedPlace_injective i).comp Subtype.val_injective)
    (f256ShortenedMultiplicationDivisor_retained_eq_zero i)
    (f256ShortenedMultiplicationDivisor_large_degree i)
    (f256ShortenedMultiplicationDivisor_small_degree i)
  rw [f256ShortenedMultiplicationDivisor_degree,
    f256GarciaStichtenothFunctionFieldGenus_eq] at h
  have hb := f256MultiplicationDivisor_dual_distance_numerator i
  have hb' : (f256GarciaStichtenothLength i + 4) / 5 - f256MultiplicationLogicalCount i ≤
      Int.toNat (Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) -
        f256MultiplicationLogicalCount i + 2 - 2 * (f256GarciaStichtenothGenus i : ℤ)) := by
    omega
  exact le_trans (WithTop.coe_le_coe.mpr hb') h

/-- Puncturing all codewords retains the same functions but fewer evaluation places. -/
def f256PuncturedMultiplicationCode (i : ℕ) : LinearCode F256 (F256MultiplicationRetained i) :=
  agEvaluationCode (f256MultiplicationDivisor i)
    (fun j : F256MultiplicationRetained i => f256GarciaStichtenothSelectedRationalPlace i j.val)
    (fun j => f256MultiplicationDivisor_selected_eq_zero i j.val)

theorem f256PuncturedMultiplicationCode_mem_iff (i : ℕ)
    (w : Word F256 (F256MultiplicationRetained i)) :
    w ∈ (f256PuncturedMultiplicationCode i).carrier ↔
      ∃ x ∈ (f256MultiplicationCode i).carrier,
        (fun j : F256MultiplicationRetained i => x j.val) = w := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨agEvaluationLinearMap (f256MultiplicationDivisor i)
      (f256GarciaStichtenothSelectedRationalPlace i)
      (f256MultiplicationDivisor_selected_eq_zero i) f, ⟨f, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨f, rfl⟩, h⟩
    exact ⟨f, h⟩

theorem f256MultiplicationDivisor_degree_lt_retained (i : ℕ) :
    Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) <
      Fintype.card (F256MultiplicationRetained i) := by
  rw [f256MultiplicationRetained_card]
  have h := f256MultiplicationDivisor_degree_upper i
  have hn := f256GarciaStichtenothLength_two_hundred_forty_le i
  unfold f256MultiplicationLogicalCount
  omega

theorem f256PuncturedMultiplicationCode_dimension_eq (i : ℕ) :
    Dimension (f256PuncturedMultiplicationCode i) = Dimension (f256MultiplicationCode i) := by
  have h := agEvaluation_dimension_eq_of_constantAlgebra_eq F256 (f256GarciaStichtenothField i)
    (π := f256GarciaStichtenothPolynomialAlgebra i)
    (ρ := f256GarciaStichtenothRatFuncAlgebra i)
    (τ := f256GarciaStichtenothPolynomialTower i)
    (φ := f256GarciaStichtenothFunctionField i)
    (s := f256GarciaStichtenothSeparable i)
    (sourceClosureDirectConstant_eq (i + 2)).symm (f256MultiplicationDivisor i)
    (fun j : F256MultiplicationRetained i => f256GarciaStichtenothSelectedRationalPlace i j.val)
    ((f256GarciaStichtenothSelectedPlace_injective i).comp Subtype.val_injective)
    (fun j => f256MultiplicationDivisor_selected_eq_zero i j.val)
    (f256MultiplicationDivisor_large_degree i)
    (f256MultiplicationDivisor_degree_lt_retained i)
  change (Dimension (f256PuncturedMultiplicationCode i) : ℤ) = _ at h
  rw [f256GarciaStichtenothFunctionFieldGenus_eq, ← f256MultiplicationCode_dimension_eq] at h
  exact_mod_cast h

theorem f256PuncturedMultiplicationCode_distance_lower (i : ℕ) :
    (((f256GarciaStichtenothLength i + 3) / 4 - f256MultiplicationLogicalCount i : ℕ) : WithTop ℕ) ≤
      HypergraphProduct.extendedMinimumDistance (f256PuncturedMultiplicationCode i) := by
  classical
  have h := agEvaluation_distance_lower_bound (f256MultiplicationDivisor i)
    (fun j : F256MultiplicationRetained i => f256GarciaStichtenothSelectedRationalPlace i j.val)
    ((f256GarciaStichtenothSelectedPlace_injective i).comp Subtype.val_injective)
    (fun j => f256MultiplicationDivisor_selected_eq_zero i j.val)
  rw [f256MultiplicationRetained_card] at h
  have hu := f256MultiplicationDivisor_degree_upper i
  have hK := f256MultiplicationLogicalCount_lt_fifth i
  have hb : (f256GarciaStichtenothLength i + 3) / 4 - f256MultiplicationLogicalCount i ≤
      Int.toNat ((f256GarciaStichtenothLength i - f256MultiplicationLogicalCount i : ℕ) -
        Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i)) := by
    omega
  exact le_trans (WithTop.coe_le_coe.mpr hb) h

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
