import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Integral.SkewCoordinates

/-!
# Reconstruction from integral cyclic coordinates

Finite families of `R_T` cyclic coordinates are assembled into an actual
element of the Cartwright--Steger skew Laurent ring.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

noncomputable def integralCyclicCoordinate
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hcoords : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      ∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a =
          (functionFieldCyclicBasis P r).repr x p)
    (p : Fin r.matrixRank × Fin r.matrixRank) : IntegralArithmeticRing P :=
  Classical.choose (hcoords p)

theorem integralCyclicCoordinate_spec
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hcoords : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      ∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a =
          (functionFieldCyclicBasis P r).repr x p)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    integralArithmeticToFunctionField P
        (integralCyclicCoordinate P r x hcoords p) =
      (functionFieldCyclicBasis P r).repr x p :=
  Classical.choose_spec (hcoords p)

noncomputable def integralCyclicCoordinateSkew
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hcoords : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      ∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a =
          (functionFieldCyclicBasis P r).repr x p)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    CartwrightStegerSkewLaurentRing P r :=
  Classical.choose (exists_skewLaurent_of_integralArithmetic P r
    (integralCyclicCoordinate P r x hcoords p))

theorem integralCyclicCoordinateSkew_spec
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hcoords : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      ∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a =
          (functionFieldCyclicBasis P r).repr x p)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    skewLaurentToGlobalMatrix P r
        (integralCyclicCoordinateSkew P r x hcoords p) =
      functionFieldScalarMatrix P r
        (integralArithmeticToFunctionField P
          (integralCyclicCoordinate P r x hcoords p)) :=
  Classical.choose_spec (exists_skewLaurent_of_integralArithmetic P r
    (integralCyclicCoordinate P r x hcoords p))

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
