import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Building.SimpleTransitivity
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Arithmetic.StrongApproximation

/-!
# Cartwright--Steger chamber relations

The colored generator sets of an LSV Cayley complex are prefixes of
rank-length color-one relations.  This file constructs the required relation
from the explicit apartment loop: multiplying the one-coordinate
uniformizers once in every coordinate gives a scalar, hence returns to the
standard projective building vertex.  Unique color-one generator labels and
simple transitivity then turn that loop into a relation in the actual
Cartwright--Steger lattice.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped MatrixGroups

private noncomputable def rankThreeCoordinateCoweight
    (P : BasePrime) (i : Fin 3) :
    Matrix.ProjGenLinGroup (Fin 3) (BuildingLocalField P) :=
  SphericalHecke.coordinateUniformizerCoweight (BaseField P) 3 i

private theorem rankThreeCoordinateCoweight_cycle
    (P : BasePrime) :
    rankThreeCoordinateCoweight P 0 *
        rankThreeCoordinateCoweight P 1 *
          rankThreeCoordinateCoweight P 2 = 1 := by
  change Matrix.ProjGenLinGroup.mk
      (SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 3 0) *
    Matrix.ProjGenLinGroup.mk
      (SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 3 1) *
    Matrix.ProjGenLinGroup.mk
      (SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 3 2) = 1
  rw [← map_mul, ← map_mul]
  have hscalar :
      SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 3 0 *
          SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 3 1 *
            SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 3 2 =
        Matrix.GeneralLinearGroup.scalar (Fin 3)
          (SphericalHecke.uniformizerUnit (BaseField P)) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SphericalHecke.coordinateUniformizerGeneralLinear,
    SphericalHecke.coordinateUniformizerUnits,
    SphericalHecke.diagonalGeneralLinear_apply,
    Matrix.mul_apply]
  rw [hscalar, Matrix.ProjGenLinGroup.mk_scalar]

private theorem rankThreeCoordinateCoweight_mem_colorOne
    (P : BasePrime) (i : Fin 3) :
    rankThreeCoordinateCoweight P i ∈
      SphericalHecke.fundamentalDoubleCoset (BaseField P) 3 1 := by
  exact SphericalHecke.coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
    (BaseField P) (by omega) i

private noncomputable def rankThreeVertex0 (P : BasePrime) :
    CartwrightStegerBuildingVertex P .three := QuotientGroup.mk 1

private noncomputable def rankThreeVertex1 (P : BasePrime) :
    CartwrightStegerBuildingVertex P .three :=
  QuotientGroup.mk (rankThreeCoordinateCoweight P 0)

private noncomputable def rankThreeVertex2 (P : BasePrime) :
    CartwrightStegerBuildingVertex P .three :=
  QuotientGroup.mk
    (rankThreeCoordinateCoweight P 0 * rankThreeCoordinateCoweight P 1)

private theorem rankThreeAdjacent01 (P : BasePrime) :
    SphericalHecke.ColoredBuildingAdjacent (BaseField P) 3 1
      (rankThreeVertex0 P) (rankThreeVertex1 P) := by
  rw [rankThreeVertex0, rankThreeVertex1]
  change SphericalHecke.ColoredBuildingAdjacent (BaseField P) 3 1
    (QuotientGroup.mk 1) (QuotientGroup.mk (rankThreeCoordinateCoweight P 0))
  rw [SphericalHecke.coloredBuildingAdjacent_mk_iff]
  simpa using rankThreeCoordinateCoweight_mem_colorOne P 0

private theorem rankThreeAdjacent12 (P : BasePrime) :
    SphericalHecke.ColoredBuildingAdjacent (BaseField P) 3 1
      (rankThreeVertex1 P) (rankThreeVertex2 P) := by
  rw [rankThreeVertex1, rankThreeVertex2]
  change SphericalHecke.ColoredBuildingAdjacent (BaseField P) 3 1
    (QuotientGroup.mk (rankThreeCoordinateCoweight P 0))
    (QuotientGroup.mk
      (rankThreeCoordinateCoweight P 0 * rankThreeCoordinateCoweight P 1))
  rw [SphericalHecke.coloredBuildingAdjacent_mk_iff]
  simpa [mul_assoc] using rankThreeCoordinateCoweight_mem_colorOne P 1

private theorem rankThreeAdjacent20 (P : BasePrime) :
    SphericalHecke.ColoredBuildingAdjacent (BaseField P) 3 1
      (rankThreeVertex2 P) (rankThreeVertex0 P) := by
  rw [rankThreeVertex0, rankThreeVertex2]
  change SphericalHecke.ColoredBuildingAdjacent (BaseField P) 3 1
    (QuotientGroup.mk
      (rankThreeCoordinateCoweight P 0 * rankThreeCoordinateCoweight P 1))
    (QuotientGroup.mk 1)
  have hcycle :
      (QuotientGroup.mk
        (rankThreeCoordinateCoweight P 0 * rankThreeCoordinateCoweight P 1 *
          rankThreeCoordinateCoweight P 2) : CartwrightStegerBuildingVertex P .three) =
        QuotientGroup.mk 1 := by
    rw [rankThreeCoordinateCoweight_cycle]
    rfl
  have h20' : SphericalHecke.ColoredBuildingAdjacent (BaseField P) 3 1
      (QuotientGroup.mk
        (rankThreeCoordinateCoweight P 0 * rankThreeCoordinateCoweight P 1))
      (QuotientGroup.mk
        (rankThreeCoordinateCoweight P 0 * rankThreeCoordinateCoweight P 1 *
          rankThreeCoordinateCoweight P 2)) := by
    rw [SphericalHecke.coloredBuildingAdjacent_mk_iff]
    simpa [mul_assoc] using rankThreeCoordinateCoweight_mem_colorOne P 2
  exact hcycle ▸ h20'

private noncomputable def rankThreeGenerator0 (P : BasePrime) :
    ConstantProjectiveClass P .three :=
  Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor
    P .three 1 (rankThreeVertex1 P) (by
      rw [buildingLatticeVertexMap_one]
      exact rankThreeAdjacent01 P))

private theorem rankThreeGenerator0_maps (P : BasePrime) :
    buildingLatticeVertexMap P .three
        (1 * buildingLatticeGenerator P .three (rankThreeGenerator0 P)) =
      rankThreeVertex1 P := by
  exact (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor
    P .three 1 (rankThreeVertex1 P) (by
      rw [buildingLatticeVertexMap_one]
      exact rankThreeAdjacent01 P))).1

private noncomputable def rankThreeGenerator1 (P : BasePrime) :
    ConstantProjectiveClass P .three :=
  Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor P .three
    (1 * buildingLatticeGenerator P .three (rankThreeGenerator0 P))
    (rankThreeVertex2 P) (by
      rw [rankThreeGenerator0_maps]
      exact rankThreeAdjacent12 P))

private theorem rankThreeGenerator01_maps (P : BasePrime) :
    buildingLatticeVertexMap P .three
        ((1 * buildingLatticeGenerator P .three (rankThreeGenerator0 P)) *
          buildingLatticeGenerator P .three (rankThreeGenerator1 P)) =
      rankThreeVertex2 P := by
  exact (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor P .three
    (1 * buildingLatticeGenerator P .three (rankThreeGenerator0 P))
    (rankThreeVertex2 P) (by
      rw [rankThreeGenerator0_maps]
      exact rankThreeAdjacent12 P))).1

private noncomputable def rankThreeGenerator2 (P : BasePrime) :
    ConstantProjectiveClass P .three :=
  Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor P .three
    ((1 * buildingLatticeGenerator P .three (rankThreeGenerator0 P)) *
      buildingLatticeGenerator P .three (rankThreeGenerator1 P))
    (rankThreeVertex0 P) (by
      rw [rankThreeGenerator01_maps]
      exact rankThreeAdjacent20 P))

private theorem rankThreeGenerator012_maps (P : BasePrime) :
    buildingLatticeVertexMap P .three
        (((1 * buildingLatticeGenerator P .three (rankThreeGenerator0 P)) *
          buildingLatticeGenerator P .three (rankThreeGenerator1 P)) *
            buildingLatticeGenerator P .three (rankThreeGenerator2 P)) =
      rankThreeVertex0 P := by
  exact (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor P .three
    ((1 * buildingLatticeGenerator P .three (rankThreeGenerator0 P)) *
      buildingLatticeGenerator P .three (rankThreeGenerator1 P))
    (rankThreeVertex0 P) (by
      rw [rankThreeGenerator01_maps]
      exact rankThreeAdjacent20 P))).1

/-- Three actual Cartwright--Steger generators trace the explicit
rank-three apartment loop and multiply to one in the building lattice. -/
theorem exists_rankThree_buildingGenerator_relation
    (P : BasePrime) :
    ∃ u0 u1 u2 : ConstantProjectiveClass P .three,
      buildingLatticeGenerator P .three u0 *
          buildingLatticeGenerator P .three u1 *
            buildingLatticeGenerator P .three u2 = 1 := by
  refine ⟨rankThreeGenerator0 P, rankThreeGenerator1 P,
    rankThreeGenerator2 P, ?_⟩
  apply buildingLatticeVertexMap_injective P .three
  rw [buildingLatticeVertexMap_one]
  simpa only [one_mul, rankThreeVertex0] using rankThreeGenerator012_maps P

private noncomputable def rankFourCoordinateCoweight
    (P : BasePrime) (i : Fin 4) :
    Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P) :=
  SphericalHecke.coordinateUniformizerCoweight (BaseField P) 4 i

private theorem rankFourCoordinateCoweight_cycle
    (P : BasePrime) :
    ((rankFourCoordinateCoweight P 0 * rankFourCoordinateCoweight P 1) *
        rankFourCoordinateCoweight P 2) * rankFourCoordinateCoweight P 3 = 1 := by
  change Matrix.ProjGenLinGroup.mk
      (((SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 4 0 *
        SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 4 1) *
          SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 4 2) *
            SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 4 3) = 1
  have hscalar :
      ((SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 4 0 *
        SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 4 1) *
          SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 4 2) *
            SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 4 3 =
        Matrix.GeneralLinearGroup.scalar (Fin 4)
          (SphericalHecke.uniformizerUnit (BaseField P)) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SphericalHecke.coordinateUniformizerGeneralLinear,
        SphericalHecke.coordinateUniformizerUnits,
        SphericalHecke.diagonalGeneralLinear_apply,
        Matrix.mul_apply]
  rw [hscalar, Matrix.ProjGenLinGroup.mk_scalar]

private theorem rankFourCoordinateCoweight_mem_colorOne
    (P : BasePrime) (i : Fin 4) :
    rankFourCoordinateCoweight P i ∈
      SphericalHecke.fundamentalDoubleCoset (BaseField P) 4 1 := by
  exact SphericalHecke.coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
    (BaseField P) (by omega) i

private noncomputable def rankFourVertex0 (P : BasePrime) :
    CartwrightStegerBuildingVertex P .four := QuotientGroup.mk 1

private noncomputable def rankFourVertex1 (P : BasePrime) :
    CartwrightStegerBuildingVertex P .four :=
  QuotientGroup.mk (rankFourCoordinateCoweight P 0)

private noncomputable def rankFourVertex2 (P : BasePrime) :
    CartwrightStegerBuildingVertex P .four :=
  QuotientGroup.mk
    (rankFourCoordinateCoweight P 0 * rankFourCoordinateCoweight P 1)

private noncomputable def rankFourVertex3 (P : BasePrime) :
    CartwrightStegerBuildingVertex P .four :=
  QuotientGroup.mk
    ((rankFourCoordinateCoweight P 0 * rankFourCoordinateCoweight P 1) *
      rankFourCoordinateCoweight P 2)

private theorem rankFourAdjacent01 (P : BasePrime) :
    SphericalHecke.ColoredBuildingAdjacent (BaseField P) 4 1
      (rankFourVertex0 P) (rankFourVertex1 P) := by
  rw [rankFourVertex0, rankFourVertex1]
  change SphericalHecke.ColoredBuildingAdjacent (BaseField P) 4 1
    (QuotientGroup.mk 1) (QuotientGroup.mk (rankFourCoordinateCoweight P 0))
  rw [SphericalHecke.coloredBuildingAdjacent_mk_iff]
  simpa using rankFourCoordinateCoweight_mem_colorOne P 0

private theorem rankFourAdjacent12 (P : BasePrime) :
    SphericalHecke.ColoredBuildingAdjacent (BaseField P) 4 1
      (rankFourVertex1 P) (rankFourVertex2 P) := by
  rw [rankFourVertex1, rankFourVertex2]
  change SphericalHecke.ColoredBuildingAdjacent (BaseField P) 4 1
    (QuotientGroup.mk (rankFourCoordinateCoweight P 0))
    (QuotientGroup.mk
      (rankFourCoordinateCoweight P 0 * rankFourCoordinateCoweight P 1))
  rw [SphericalHecke.coloredBuildingAdjacent_mk_iff]
  simpa [mul_assoc] using rankFourCoordinateCoweight_mem_colorOne P 1

private theorem rankFourAdjacent23 (P : BasePrime) :
    SphericalHecke.ColoredBuildingAdjacent (BaseField P) 4 1
      (rankFourVertex2 P) (rankFourVertex3 P) := by
  rw [rankFourVertex2, rankFourVertex3]
  change SphericalHecke.ColoredBuildingAdjacent (BaseField P) 4 1
    (QuotientGroup.mk
      (rankFourCoordinateCoweight P 0 * rankFourCoordinateCoweight P 1))
    (QuotientGroup.mk
      ((rankFourCoordinateCoweight P 0 * rankFourCoordinateCoweight P 1) *
        rankFourCoordinateCoweight P 2))
  rw [SphericalHecke.coloredBuildingAdjacent_mk_iff]
  simpa [mul_assoc] using rankFourCoordinateCoweight_mem_colorOne P 2

private theorem rankFourAdjacent30 (P : BasePrime) :
    SphericalHecke.ColoredBuildingAdjacent (BaseField P) 4 1
      (rankFourVertex3 P) (rankFourVertex0 P) := by
  rw [rankFourVertex0, rankFourVertex3]
  change SphericalHecke.ColoredBuildingAdjacent (BaseField P) 4 1
    (QuotientGroup.mk
      ((rankFourCoordinateCoweight P 0 * rankFourCoordinateCoweight P 1) *
        rankFourCoordinateCoweight P 2))
    (QuotientGroup.mk 1)
  have hcycle :
      (QuotientGroup.mk
        (((rankFourCoordinateCoweight P 0 * rankFourCoordinateCoweight P 1) *
          rankFourCoordinateCoweight P 2) * rankFourCoordinateCoweight P 3) :
            CartwrightStegerBuildingVertex P .four) = QuotientGroup.mk 1 := by
    rw [rankFourCoordinateCoweight_cycle]
    rfl
  have h30' : SphericalHecke.ColoredBuildingAdjacent (BaseField P) 4 1
      (QuotientGroup.mk
        ((rankFourCoordinateCoweight P 0 * rankFourCoordinateCoweight P 1) *
          rankFourCoordinateCoweight P 2))
      (QuotientGroup.mk
        (((rankFourCoordinateCoweight P 0 * rankFourCoordinateCoweight P 1) *
          rankFourCoordinateCoweight P 2) * rankFourCoordinateCoweight P 3)) := by
    rw [SphericalHecke.coloredBuildingAdjacent_mk_iff]
    simpa [mul_assoc] using rankFourCoordinateCoweight_mem_colorOne P 3
  exact hcycle ▸ h30'

private noncomputable def rankFourGenerator0 (P : BasePrime) :
    ConstantProjectiveClass P .four :=
  Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor
    P .four 1 (rankFourVertex1 P) (by
      rw [buildingLatticeVertexMap_one]
      exact rankFourAdjacent01 P))

private theorem rankFourGenerator0_maps (P : BasePrime) :
    buildingLatticeVertexMap P .four
        (1 * buildingLatticeGenerator P .four (rankFourGenerator0 P)) =
      rankFourVertex1 P := by
  exact (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor
    P .four 1 (rankFourVertex1 P) (by
      rw [buildingLatticeVertexMap_one]
      exact rankFourAdjacent01 P))).1

private noncomputable def rankFourGenerator1 (P : BasePrime) :
    ConstantProjectiveClass P .four :=
  Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor P .four
    (1 * buildingLatticeGenerator P .four (rankFourGenerator0 P))
    (rankFourVertex2 P) (by
      rw [rankFourGenerator0_maps]
      exact rankFourAdjacent12 P))

private theorem rankFourGenerator01_maps (P : BasePrime) :
    buildingLatticeVertexMap P .four
        ((1 * buildingLatticeGenerator P .four (rankFourGenerator0 P)) *
          buildingLatticeGenerator P .four (rankFourGenerator1 P)) =
      rankFourVertex2 P := by
  exact (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor P .four
    (1 * buildingLatticeGenerator P .four (rankFourGenerator0 P))
    (rankFourVertex2 P) (by
      rw [rankFourGenerator0_maps]
      exact rankFourAdjacent12 P))).1

private noncomputable def rankFourGenerator2 (P : BasePrime) :
    ConstantProjectiveClass P .four :=
  Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor P .four
    ((1 * buildingLatticeGenerator P .four (rankFourGenerator0 P)) *
      buildingLatticeGenerator P .four (rankFourGenerator1 P))
    (rankFourVertex3 P) (by
      rw [rankFourGenerator01_maps]
      exact rankFourAdjacent23 P))

private theorem rankFourGenerator012_maps (P : BasePrime) :
    buildingLatticeVertexMap P .four
        (((1 * buildingLatticeGenerator P .four (rankFourGenerator0 P)) *
          buildingLatticeGenerator P .four (rankFourGenerator1 P)) *
            buildingLatticeGenerator P .four (rankFourGenerator2 P)) =
      rankFourVertex3 P := by
  exact (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor P .four
    ((1 * buildingLatticeGenerator P .four (rankFourGenerator0 P)) *
      buildingLatticeGenerator P .four (rankFourGenerator1 P))
    (rankFourVertex3 P) (by
      rw [rankFourGenerator01_maps]
      exact rankFourAdjacent23 P))).1

private noncomputable def rankFourGenerator3 (P : BasePrime) :
    ConstantProjectiveClass P .four :=
  Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor P .four
    (((1 * buildingLatticeGenerator P .four (rankFourGenerator0 P)) *
      buildingLatticeGenerator P .four (rankFourGenerator1 P)) *
        buildingLatticeGenerator P .four (rankFourGenerator2 P))
    (rankFourVertex0 P) (by
      rw [rankFourGenerator012_maps]
      exact rankFourAdjacent30 P))

private theorem rankFourGenerator0123_maps (P : BasePrime) :
    buildingLatticeVertexMap P .four
        ((((1 * buildingLatticeGenerator P .four (rankFourGenerator0 P)) *
          buildingLatticeGenerator P .four (rankFourGenerator1 P)) *
            buildingLatticeGenerator P .four (rankFourGenerator2 P)) *
              buildingLatticeGenerator P .four (rankFourGenerator3 P)) =
      rankFourVertex0 P := by
  exact (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor P .four
    (((1 * buildingLatticeGenerator P .four (rankFourGenerator0 P)) *
      buildingLatticeGenerator P .four (rankFourGenerator1 P)) *
        buildingLatticeGenerator P .four (rankFourGenerator2 P))
    (rankFourVertex0 P) (by
      rw [rankFourGenerator012_maps]
      exact rankFourAdjacent30 P))).1

/-- Four actual Cartwright--Steger generators trace the explicit
rank-four apartment loop and multiply to one in the building lattice. -/
theorem exists_rankFour_buildingGenerator_relation
    (P : BasePrime) :
    ∃ u0 u1 u2 u3 : ConstantProjectiveClass P .four,
      ((buildingLatticeGenerator P .four u0 *
          buildingLatticeGenerator P .four u1) *
            buildingLatticeGenerator P .four u2) *
              buildingLatticeGenerator P .four u3 = 1 := by
  refine ⟨rankFourGenerator0 P, rankFourGenerator1 P,
    rankFourGenerator2 P, rankFourGenerator3 P, ?_⟩
  apply buildingLatticeVertexMap_injective P .four
  rw [buildingLatticeVertexMap_one]
  simpa only [one_mul, rankFourVertex0] using rankFourGenerator0123_maps P

/-! ## Transport of building relations to every finite congruence image -/

private noncomputable def orderGeneratorWordProduct
    (P : BasePrime) (r : Rank)
    (word : List (ConstantProjectiveClass P r)) :
    (CartwrightStegerOrder P r)ˣ :=
  (word.map (cartwrightStegerOrderUnitGenerator P r)).prod

private noncomputable def orderSplitGeneratorWordProduct
    (P : BasePrime) (r : Rank)
    (word : List (ConstantProjectiveClass P r)) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  (word.map fun u => orderSplitCartwrightStegerGeneratorGL P r
    (constantClassRepresentative P r u)).prod

private theorem orderUnitToGlobalPGL_generator
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    orderUnitToGlobalPGL P r (cartwrightStegerOrderUnitGenerator P r u) =
      Matrix.ProjGenLinGroup.mk (cartwrightStegerGenerator P r u) := by
  change Matrix.ProjGenLinGroup.mk
      (orderUnitToGlobalGL P r (cartwrightStegerOrderUnitGenerator P r u)) = _
  rw [orderUnitToGlobalGL_generator]

private theorem orderGeneratorWordProduct_to_building
    (P : BasePrime) (r : Rank)
    (word : List (ConstantProjectiveClass P r)) :
    orderUnitToBuildingPGL P r (orderGeneratorWordProduct P r word) =
      (word.map (buildingCartwrightStegerGenerator P r)).prod := by
  induction word with
  | nil => simp [orderGeneratorWordProduct]
  | cons u word ih =>
      simp only [orderGeneratorWordProduct, List.map_cons, List.prod_cons,
        map_mul, orderUnitToBuildingPGL_generator]
      simpa [orderGeneratorWordProduct] using congrArg
        (fun g => buildingCartwrightStegerGenerator P r u * g) ih

private theorem orderGeneratorWordProduct_to_global
    (P : BasePrime) (r : Rank)
    (word : List (ConstantProjectiveClass P r)) :
    orderUnitToGlobalPGL P r (orderGeneratorWordProduct P r word) =
      Matrix.ProjGenLinGroup.mk
        (orderSplitBaseChangeGLHom P r
          (orderSplitGeneratorWordProduct P r word)) := by
  induction word with
  | nil => simp [orderGeneratorWordProduct, orderSplitGeneratorWordProduct]
  | cons u word ih =>
      simp only [orderGeneratorWordProduct, orderSplitGeneratorWordProduct,
        List.map_cons, List.prod_cons, map_mul,
        orderUnitToGlobalPGL_generator,
        map_orderSplitCartwrightStegerClassGeneratorGL_to_global]
      simpa [orderGeneratorWordProduct, orderSplitGeneratorWordProduct] using
        congrArg (fun g => Matrix.ProjGenLinGroup.mk
          (cartwrightStegerGenerator P r u) * g) ih

private theorem orderSplitGeneratorWordProduct_to_finite
    (P : BasePrime) (r : Rank) (level : Nat)
    (word : List (ConstantProjectiveClass P r)) :
    orderSplitReductionPGLHom P r level
        (orderSplitGeneratorWordProduct P r word) =
      (word.map (indexCartwrightStegerClassGenerator P r level)).prod := by
  induction word with
  | nil => simp [orderSplitGeneratorWordProduct]
  | cons u word ih =>
      simp only [orderSplitGeneratorWordProduct, List.map_cons, List.prod_cons,
        map_mul, orderSplitReductionPGLHom_classGenerator]
      simpa [orderSplitGeneratorWordProduct] using congrArg
        (fun g => indexCartwrightStegerClassGenerator P r level u * g) ih

/-- A relation among the actual building-lattice generators remains a
relation after every selected finite congruence reduction.  The proof passes
through genuine arithmetic-order units, descends projective scalar equality
globally, and only then reduces coefficients. -/
theorem indexClassGenerator_wordProduct_eq_one_of_building_relation
    (P : BasePrime) (r : Rank) (level : Nat)
    (word : List (ConstantProjectiveClass P r))
    (hbuilding :
      (word.map (buildingLatticeGenerator P r)).prod = 1) :
    (word.map (indexCartwrightStegerClassGenerator P r level)).prod = 1 := by
  have hbuildingPGL :
      (word.map (buildingCartwrightStegerGenerator P r)).prod = 1 := by
    calc
      (word.map (buildingCartwrightStegerGenerator P r)).prod =
          (BuildingCartwrightStegerLattice P r).subtype
            ((word.map (buildingLatticeGenerator P r)).prod) := by
        exact
          List.prod_map_hom word (buildingLatticeGenerator P r)
            (BuildingCartwrightStegerLattice P r).subtype
      _ = (BuildingCartwrightStegerLattice P r).subtype 1 := by rw [hbuilding]
      _ = 1 := map_one _
  let ug := orderGeneratorWordProduct P r word
  have hugBuilding : orderUnitToBuildingPGL P r ug = 1 := by
    rw [orderGeneratorWordProduct_to_building]
    exact hbuildingPGL
  have hugCompact : orderUnitToBuildingPGL P r ug ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank := by
    rw [hugBuilding]
    exact Subgroup.one_mem _
  have hugNormalForm : orderUnitToGlobalPGL P r ug =
      Matrix.ProjGenLinGroup.mk (globalCompactNormalForm P r 1 0) :=
    orderUnitToGlobalPGL_eq_compactNormalForm_of_building_eq
      P r ug hugCompact 1 0 (by simpa using hugBuilding)
  have hugGlobal : orderUnitToGlobalPGL P r ug = 1 := by
    simpa [globalCompactNormalForm, constantUnitMatrix] using hugNormalForm
  let A := orderSplitGeneratorWordProduct P r word
  have hbase : Matrix.ProjGenLinGroup.mk
        (orderSplitBaseChangeGLHom P r A) =
      Matrix.ProjGenLinGroup.mk (orderSplitBaseChangeGLHom P r 1) := by
    rw [← orderGeneratorWordProduct_to_global]
    simpa [ug] using hugGlobal
  have hfinite := orderSplitReductionPGLHom_eq_of_baseChange_projective_eq
    P r level A 1 hbase
  dsimp [A] at hfinite
  rw [orderSplitGeneratorWordProduct_to_finite] at hfinite
  simpa only [map_one] using hfinite

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
