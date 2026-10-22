import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Integral.SkewReconstruction

/-!
# The integral cyclic reconstruction theorem
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

noncomputable def integralCyclicSkewReconstruction
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hcoords : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      ∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a =
          (functionFieldCyclicBasis P r).repr x p) :
    CartwrightStegerSkewLaurentRing P r :=
  ∑ p, integralCyclicCoordinateSkew P r x hcoords p *
    skewLaurentCyclicBasisMonomial P r p

theorem skewLaurentToGlobalMatrix_integralCyclicSkewReconstruction
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hcoords : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      ∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a =
          (functionFieldCyclicBasis P r).repr x p) :
    skewLaurentToGlobalMatrix P r
        (integralCyclicSkewReconstruction P r x hcoords) =
      ∑ p, (functionFieldCyclicBasis P r).repr x p •
        (functionFieldCyclicBasisVector P r p :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) := by
  rw [integralCyclicSkewReconstruction, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [skewLaurentToGlobalMatrix_integralScalar_mul_cyclicBasisMonomial
    P r _ _ (integralCyclicCoordinateSkew_spec P r x hcoords p) p]
  rw [integralCyclicCoordinate_spec P r x hcoords p]

theorem functionFieldCyclicBasis_sum_repr_coe
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    (∑ p, (functionFieldCyclicBasis P r).repr x p •
        (functionFieldCyclicBasisVector P r p :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r))) = x.1 := by
  calc
    _ = (CyclicAlgebra P r).val
        (∑ p, (functionFieldCyclicBasis P r).repr x p •
          functionFieldCyclicBasis P r p) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [map_smul, functionFieldCyclicBasis_apply]
      ext i j
      simp [Algebra.smul_def]
    _ = x.1 := congrArg Subtype.val
      ((functionFieldCyclicBasis P r).sum_repr x)

theorem exists_skewLaurent_of_integralCyclicCoordinates
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hcoords : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      ∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a =
          (functionFieldCyclicBasis P r).repr x p) :
    ∃ f : CartwrightStegerSkewLaurentRing P r,
      skewLaurentToGlobalMatrix P r f = x.1 := by
  refine ⟨integralCyclicSkewReconstruction P r x hcoords, ?_⟩
  rw [skewLaurentToGlobalMatrix_integralCyclicSkewReconstruction,
    functionFieldCyclicBasis_sum_repr_coe]

theorem exists_skewLaurent_of_order_and_buildingIntegral
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r)
    (hlocal : ∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r
          (cartwrightStegerOrderToCyclicAlgebra P r x)) :
    ∃ f : CartwrightStegerSkewLaurentRing P r,
      skewLaurentToGlobalMatrix P r f =
        (cartwrightStegerOrderToCyclicAlgebra P r x).1 := by
  have hcoords : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      ∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a =
          (functionFieldCyclicBasis P r).repr
            (cartwrightStegerOrderToCyclicAlgebra P r x) p := by
    intro p
    exact exists_integralArithmetic_coordinate_of_order_and_buildingIntegral
      P r x hlocal p
  exact exists_skewLaurent_of_integralCyclicCoordinates P r
    (cartwrightStegerOrderToCyclicAlgebra P r x) hcoords

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
