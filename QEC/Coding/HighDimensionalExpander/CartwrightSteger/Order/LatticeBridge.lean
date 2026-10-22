import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Integral.SkewCompatibility
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Building.InfinityLattice

/-!
# The arithmetic-order lift of the Cartwright--Steger lattice

The same explicit order units generate both the global split-matrix lattice
and its building-place projective image.  This provides genuine order-unit
lifts for every element of the building lattice.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

noncomputable def orderUnitToCyclicUnit
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrder P r)ˣ →* (CyclicAlgebra P r)ˣ :=
  Units.map (cartwrightStegerOrderToCyclicAlgebra P r).toMonoidHom

noncomputable def orderUnitToGlobalGL
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrder P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  (Units.map (CyclicAlgebra P r).val.toRingHom).comp
    (orderUnitToCyclicUnit P r)

noncomputable def orderUnitToBuildingPGL
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrder P r)ˣ →*
      Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  (cyclicUnitToBuildingPGL P r).comp (orderUnitToCyclicUnit P r)

noncomputable def cartwrightStegerOrderUnitGenerator
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    (CartwrightStegerOrder P r)ˣ :=
  cartwrightStegerOrderGenerator P r (constantClassRepresentative P r x)

theorem orderUnitToCyclicUnit_generator
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    orderUnitToCyclicUnit P r (cartwrightStegerOrderUnitGenerator P r x) =
      cartwrightStegerGeneratorCyclicUnit P r x := by
  apply Units.ext
  rfl

@[simp] theorem orderUnitToGlobalGL_generator
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    orderUnitToGlobalGL P r (cartwrightStegerOrderUnitGenerator P r x) =
      cartwrightStegerGenerator P r x := by
  rw [orderUnitToGlobalGL, MonoidHom.comp_apply,
    orderUnitToCyclicUnit_generator]
  apply Units.ext
  rfl

@[simp] theorem orderUnitToBuildingPGL_generator
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    orderUnitToBuildingPGL P r (cartwrightStegerOrderUnitGenerator P r x) =
      buildingCartwrightStegerGenerator P r x := by
  rw [orderUnitToBuildingPGL, MonoidHom.comp_apply,
    orderUnitToCyclicUnit_generator,
    cartwrightStegerGeneratorCyclicUnit_to_buildingPGL]

/-- The lift of the Cartwright--Steger lattice inside actual arithmetic-order
units, before quotienting by central units. -/
noncomputable def CartwrightStegerOrderUnitLattice
    (P : BasePrime) (r : Rank) :
    Subgroup ((CartwrightStegerOrder P r)ˣ) :=
  Subgroup.closure (Set.range (cartwrightStegerOrderUnitGenerator P r))

theorem map_orderUnitLattice_to_global
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrderUnitLattice P r).map (orderUnitToGlobalGL P r) =
      CartwrightStegerMatrixGroup P r := by
  rw [CartwrightStegerOrderUnitLattice, MonoidHom.map_closure,
    CartwrightStegerMatrixGroup]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (orderUnitToGlobalGL_generator P r x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨cartwrightStegerOrderUnitGenerator P r x,
      ⟨x, rfl⟩, orderUnitToGlobalGL_generator P r x⟩

theorem map_orderUnitLattice_to_building
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrderUnitLattice P r).map
        (orderUnitToBuildingPGL P r) =
      BuildingCartwrightStegerLattice P r := by
  rw [CartwrightStegerOrderUnitLattice, MonoidHom.map_closure,
    BuildingCartwrightStegerLattice]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (orderUnitToBuildingPGL_generator P r x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨cartwrightStegerOrderUnitGenerator P r x,
      ⟨x, rfl⟩, orderUnitToBuildingPGL_generator P r x⟩

theorem exists_orderUnitLattice_lift_of_buildingLattice
    (P : BasePrime) (r : Rank)
    (g : BuildingCartwrightStegerLattice P r) :
    ∃ u : (CartwrightStegerOrder P r)ˣ,
      u ∈ CartwrightStegerOrderUnitLattice P r ∧
      orderUnitToBuildingPGL P r u = g := by
  have hg : (g : Matrix.ProjGenLinGroup (Fin r.matrixRank)
      (BuildingLocalField P)) ∈
      (CartwrightStegerOrderUnitLattice P r).map
        (orderUnitToBuildingPGL P r) := by
    rw [map_orderUnitLattice_to_building]
    exact g.property
  obtain ⟨u, hu, hmap⟩ := hg
  exact ⟨u, hu, hmap⟩

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
