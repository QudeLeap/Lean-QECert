import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Norm.IntrinsicNorm

/-!
# Exact split coordinates of the Cartwright--Steger arithmetic order

Every element of the actual cyclic-algebra order has coordinates over the
localized constant coefficient ring, and the resulting full inner-form map
covers every actual order unit.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

/-- A chosen arithmetic coefficient of an actual order element in the
construction's cyclic basis. -/
noncomputable def cartwrightStegerOrderArithmeticCoordinate
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) : ArithmeticRing P :=
  Classical.choose
    (exists_arithmetic_coordinate_of_cartwrightStegerOrder P r x p)

theorem arithmeticCoordinate_to_functionField
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    arithmeticRingToFunctionField P
        (cartwrightStegerOrderArithmeticCoordinate P r x p) =
      (functionFieldCyclicBasis P r).repr
        (cartwrightStegerOrderToCyclicAlgebra P r x) p :=
  Classical.choose_spec
    (exists_arithmetic_coordinate_of_cartwrightStegerOrder P r x p)

/-- Every actual arithmetic-order element has a matrix over the localized
constant coefficient ring whose scalar extension is exactly that element. -/
noncomputable def cartwrightStegerOrderSplitCoordinate
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  ∑ p : Fin r.matrixRank × Fin r.matrixRank,
    arithmeticToConstantArithmetic P r
        (cartwrightStegerOrderArithmeticCoordinate P r x p) •
      orderIndexCyclicBasisVector P r p

set_option maxHeartbeats 800000 in
theorem cartwrightStegerOrderSplitCoordinate_to_global
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r) :
    (cartwrightStegerOrderSplitCoordinate P r x).map
        (constantArithmeticToSplittingFunctionField P r) = x := by
  rw [cartwrightStegerOrderSplitCoordinate]
  have hmapSum :
      ((∑ p : Fin r.matrixRank × Fin r.matrixRank,
          arithmeticToConstantArithmetic P r
              (cartwrightStegerOrderArithmeticCoordinate P r x p) •
            orderIndexCyclicBasisVector P r p).map
        (constantArithmeticToSplittingFunctionField P r)) =
      ∑ p : Fin r.matrixRank × Fin r.matrixRank,
        (arithmeticToConstantArithmetic P r
              (cartwrightStegerOrderArithmeticCoordinate P r x p) •
            orderIndexCyclicBasisVector P r p).map
          (constantArithmeticToSplittingFunctionField P r) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sum_apply, map_sum]
  rw [hmapSum]
  calc
    _ = ∑ p : Fin r.matrixRank × Fin r.matrixRank,
        arithmeticRingToSplittingFunctionField P r
            (cartwrightStegerOrderArithmeticCoordinate P r x p) •
          splittingCyclicBasisVector P r p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Matrix.map_smul' _ _ _ (map_mul _),
        orderIndexCyclicBasisVector_to_global,
        constantArithmeticToSplittingFunctionField_arithmeticBaseChange]
    _ = x := by
      have hx := functionFieldCyclicBasis_sum_repr_coe P r
        (cartwrightStegerOrderToCyclicAlgebra P r x)
      have hcoeff (p : Fin r.matrixRank × Fin r.matrixRank) :
          arithmeticRingToSplittingFunctionField P r
              (cartwrightStegerOrderArithmeticCoordinate P r x p) =
            functionFieldEmbedding P r
              ((functionFieldCyclicBasis P r).repr
                (cartwrightStegerOrderToCyclicAlgebra P r x) p) := by
        rw [arithmeticRingToSplittingFunctionField, RingHom.comp_apply,
          arithmeticCoordinate_to_functionField]
      calc
        _ = ∑ p : Fin r.matrixRank × Fin r.matrixRank,
            functionFieldEmbedding P r
                ((functionFieldCyclicBasis P r).repr
                  (cartwrightStegerOrderToCyclicAlgebra P r x) p) •
              splittingCyclicBasisVector P r p := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [hcoeff]
        _ = (cartwrightStegerOrderToCyclicAlgebra P r x :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (SplittingFunctionField P r)) := by
          simp only [Algebra.smul_def,
            functionFieldCyclicBasisVector_coe] at hx ⊢
          exact hx
        _ = x := rfl

/-- The split-coordinate full inner form is not merely a selected subgroup:
it covers every unit of the actual Cartwright--Steger arithmetic order. -/
theorem orderInnerFormToOrderUnits_surjective
    (P : BasePrime) (r : Rank) :
    Function.Surjective (orderInnerFormToOrderUnits P r) := by
  intro u
  let A := cartwrightStegerOrderSplitCoordinate P r
    (u : CartwrightStegerOrder P r)
  let B := cartwrightStegerOrderSplitCoordinate P r
    ((u⁻¹ : (CartwrightStegerOrder P r)ˣ) : CartwrightStegerOrder P r)
  have hA : A.map (constantArithmeticToSplittingFunctionField P r) = u :=
    cartwrightStegerOrderSplitCoordinate_to_global P r
      (u : CartwrightStegerOrder P r)
  have hB : B.map (constantArithmeticToSplittingFunctionField P r) = u⁻¹ :=
    cartwrightStegerOrderSplitCoordinate_to_global P r
      ((u⁻¹ : (CartwrightStegerOrder P r)ˣ) : CartwrightStegerOrder P r)
  have hA' :
      (constantArithmeticToSplittingFunctionField P r).mapMatrix A =
        ((u : CartwrightStegerOrder P r) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) := hA
  have hB' :
      (constantArithmeticToSplittingFunctionField P r).mapMatrix B =
        (((u⁻¹ : (CartwrightStegerOrder P r)ˣ) :
          CartwrightStegerOrder P r) :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (SplittingFunctionField P r)) := hB
  have mapMatrix_injective : Function.Injective
      ((constantArithmeticToSplittingFunctionField P r).mapMatrix :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ConstantArithmeticRing P r) →
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) := by
    intro M N hMN
    ext i j
    apply constantArithmeticToSplittingFunctionField_injective P r
    exact congrArg (fun X => X i j) hMN
  have hAB : A * B = 1 := by
    apply mapMatrix_injective
    rw [map_mul, map_one, hA', hB']
    exact congrArg Subtype.val u.val_inv
  have hBA : B * A = 1 := by
    apply mapMatrix_injective
    rw [map_mul, map_one, hB', hA']
    exact congrArg Subtype.val u.inv_val
  let gGL : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
    { val := A
      inv := B
      val_inv := hAB
      inv_val := hBA }
  have hg : gGL ∈ OrderInnerFormUnits P r := by
    constructor
    · change A.map (constantArithmeticToSplittingFunctionField P r) ∈
          CartwrightStegerOrder P r
      rw [hA]
      exact (u : CartwrightStegerOrder P r).property
    · change B.map (constantArithmeticToSplittingFunctionField P r) ∈
          CartwrightStegerOrder P r
      rw [hB]
      exact ((u⁻¹ : (CartwrightStegerOrder P r)ˣ) :
        CartwrightStegerOrder P r).property
  let g : OrderInnerFormUnits P r := ⟨gGL, hg⟩
  refine ⟨g, ?_⟩
  apply Units.ext
  apply Subtype.ext
  exact hA

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
