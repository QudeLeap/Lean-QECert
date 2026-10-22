import QEC.Coding.AlgebraicGeometry.Towers.SourceSelectedPlaces
import QEC.Coding.AlgebraicGeometry.Towers.SourceSplitOrder

/-!
# The fixed-base uniformizer along selected source places

The polynomial `(X^16+X)^15-1` has a simple root at each of the 240 selected
initial values.  Unramified order transport through every selected source
step therefore proves that the fixed-base function `z-1` has normalized order
one at every constructed source place.

No normal-closure splitting, divisor, genus, or asymptotic conclusion is made.
-/

open Polynomial

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

private noncomputable def sourceSelectedSplitPolynomial : Polynomial F256 :=
  (Polynomial.X ^ 16 + Polynomial.X) ^ 15 - 1

private theorem sourceSelectedSplitPolynomial_derivative :
    sourceSelectedSplitPolynomial.derivative =
      (Polynomial.X ^ 16 + Polynomial.X) ^ 14 := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) F256).injective 2
  rw [sourceSelectedSplitPolynomial, Polynomial.derivative_sub,
    Polynomial.derivative_pow, Polynomial.derivative_add,
    Polynomial.derivative_X_pow, Polynomial.derivative_X,
    Polynomial.derivative_one]
  reduce_mod_char!
  simp

private theorem sourceSelectedSplitPolynomial_ne_zero :
    sourceSelectedSplitPolynomial ≠ 0 := by
  intro hzero
  have hderivative := congrArg Polynomial.derivative hzero
  rw [sourceSelectedSplitPolynomial_derivative, map_zero] at hderivative
  exact (pow_ne_zero 14
    (Polynomial.monic_X_pow_add (by norm_num)).ne_zero) hderivative

private theorem sourceSelectedSplitPolynomial_isRoot
    (a : GaloisBaseSplitPoint) :
    sourceSelectedSplitPolynomial.IsRoot (a : F256) := by
  rw [Polynomial.IsRoot, sourceSelectedSplitPolynomial]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  have hz := (galoisBaseZValue_eq_one_iff (a : F256)).2 a.property
  simpa only [galoisBaseZValue_eq, sub_eq_zero] using hz

private theorem sourceSelectedSplitPolynomial_derivative_eval_ne_zero
    (a : GaloisBaseSplitPoint) :
    sourceSelectedSplitPolynomial.derivative.eval (a : F256) ≠ 0 := by
  rw [sourceSelectedSplitPolynomial_derivative]
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X]
  apply pow_ne_zero
  simpa only [galoisBaseWValue_eq] using a.property

private theorem sourceSelectedSplitPolynomial_rootMultiplicity
    (a : GaloisBaseSplitPoint) :
    sourceSelectedSplitPolynomial.rootMultiplicity (a : F256) = 1 := by
  have hpositive : 0 <
      sourceSelectedSplitPolynomial.rootMultiplicity (a : F256) :=
    (Polynomial.rootMultiplicity_pos
      sourceSelectedSplitPolynomial_ne_zero).2
      (sourceSelectedSplitPolynomial_isRoot a)
  have hnotGreater : ¬ 1 <
      sourceSelectedSplitPolynomial.rootMultiplicity (a : F256) := by
    intro hgreater
    have hroot := (Polynomial.one_lt_rootMultiplicity_iff_isRoot
      sourceSelectedSplitPolynomial_ne_zero).1 hgreater
    exact sourceSelectedSplitPolynomial_derivative_eval_ne_zero a hroot.2
  omega

private theorem sourceGaloisBaseParameter_sub_one_eq_polynomial (m : ℕ) :
    sourceGaloisBaseParameter m - 1 =
      algebraMap (RatFunc F256) (SourceField m)
        (algebraMap (Polynomial F256) (RatFunc F256)
          sourceSelectedSplitPolynomial) := by
  rw [sourceGaloisBaseParameter]
  calc
    algebraMap (RatFunc F256) (SourceField m) galoisBaseZ - 1 =
        algebraMap (RatFunc F256) (SourceField m) (galoisBaseZ - 1) := by
      rw [map_sub, map_one]
    _ = algebraMap (RatFunc F256) (SourceField m)
        (algebraMap (Polynomial F256) (RatFunc F256)
          sourceSelectedSplitPolynomial) := by
      congr 1
      simp [sourceSelectedSplitPolynomial, galoisBaseZ, galoisBaseW,
        RatFunc.algebraMap_X]

/-- The fixed-base function `z-1` remains nonzero in every source level. -/
theorem sourceGaloisBaseParameter_sub_one_ne_zero (m : ℕ) :
    sourceGaloisBaseParameter m - 1 ≠ 0 := by
  rw [sourceGaloisBaseParameter_sub_one_eq_polynomial]
  simpa only [map_zero] using
    (algebraMap (RatFunc F256) (SourceField m)).injective.ne
      (RatFunc.algebraMap_ne_zero sourceSelectedSplitPolynomial_ne_zero)

private theorem sourceGaloisBaseParameter_succ (m : ℕ) :
    sourceGaloisBaseParameter (m + 1) =
      sourceRecursionEmbedding m (sourceGaloisBaseParameter m) := by
  rfl

/-- At every explicitly selected source place, `z-1` is a local uniformizer:
its normalized order is exactly one. -/
theorem sourceSelectedRationalPlace_order_galoisBaseParameter_sub_one :
    ∀ (m : ℕ) (index : SourceSelectedPlaceIndex m),
      (sourceSelectedRationalPlace m index).place.order
          (sourceGaloisBaseParameter m - 1) = 1
  | 0, a => by
      let b : BasePoint := Units.mk0 (a : F256) (by
        intro ha
        apply a.property
        simp [galoisBaseWValue_eq, ha])
      have horder := baseRationalPlace_order_algebraMap_polynomial b
        sourceSelectedSplitPolynomial sourceSelectedSplitPolynomial_ne_zero
      have hb : (b : F256) = (a : F256) := rfl
      rw [hb, sourceSelectedSplitPolynomial_rootMultiplicity] at horder
      rw [sourceSelectedRationalPlace_zero,
        sourceGaloisBaseParameter_sub_one_eq_polynomial]
      simp only [b] at horder ⊢
      exact horder
  | m + 1, index => by
      rcases index with ⟨index, c⟩
      have htransport := sourceSplitAbovePlace_order_sourceStepEmbedding
        (sourceSelectedRationalPlace m index)
        (sourceDistinguishedPlace m) (sourceDistinguishedCoordinate m)
        (sourceDistinguishedCoordinate_order m)
        (sourceSelectedRationalPlace_coordinate_regular m index)
        (sourceSelectedRationalPlace_coordinate_split m index) c
        (sourceGaloisBaseParameter m - 1)
        (sourceGaloisBaseParameter_sub_one_ne_zero m)
      have hlower :=
        sourceSelectedRationalPlace_order_galoisBaseParameter_sub_one m index
      rw [← hlower]
      simp only [sourceSelectedRationalPlace_succ,
        sourceGaloisBaseParameter_succ, map_sub, map_one,
        RationalPlace.place] at htransport ⊢
      exact htransport

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
