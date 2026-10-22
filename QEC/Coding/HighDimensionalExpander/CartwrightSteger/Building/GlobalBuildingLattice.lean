import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Building.BuildingCyclicAlgebra

/-!
# The common global and building Cartwright--Steger lattice

The arithmetic order is included in the construction-owned cyclic algebra,
whose explicit building-place representation sends each genuine global
Cartwright--Steger unit to the corresponding local general-linear generator.
This supplies the representation bridge needed for the global arithmetic
intersection in LSV05b Proposition 4.8.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem cartwrightStegerOrder_le_cyclicAlgebra
    (P : BasePrime) (r : Rank) :
    ∀ M, M ∈ CartwrightStegerOrder P r → M ∈ CyclicAlgebra P r := by
  intro M hM
  apply Algebra.adjoin_induction
    (R := ArithmeticRing P)
    (s := Set.range (constantMatrix P r) ∪
      {cyclicGeneratorMatrix P r, cyclicGeneratorInverseMatrix P r})
    (p := fun M _ => M ∈ CyclicAlgebra P r)
  · intro N hN
    rcases hN with hN | hN
    · obtain ⟨c, rfl⟩ := hN
      exact constantMatrix_mem_cyclicAlgebra P r c
    · rcases hN with (rfl | hN)
      · exact cyclicGeneratorMatrix_mem_cyclicAlgebra P r
      · rw [Set.mem_singleton_iff] at hN
        subst N
        exact cyclicGeneratorInverseMatrix_mem_cyclicAlgebra P r
  · intro a
    have ha := (CyclicAlgebra P r).algebraMap_mem
      (arithmeticRingToFunctionField P a)
    change arithmeticRingToSplitMatrix P r a ∈ CyclicAlgebra P r
    change Matrix.scalar (Fin r.matrixRank)
        (functionFieldEmbedding P r (arithmeticRingToFunctionField P a)) ∈
      CyclicAlgebra P r
    exact ha
  · intro A B _ _ hA hB
    exact (CyclicAlgebra P r).add_mem hA hB
  · intro A B _ _ hA hB
    exact (CyclicAlgebra P r).mul_mem hA hB
  · exact hM

noncomputable def cartwrightStegerOrderToCyclicAlgebra
    (P : BasePrime) (r : Rank) :
    CartwrightStegerOrder P r →+* CyclicAlgebra P r where
  toFun x := ⟨x.1, cartwrightStegerOrder_le_cyclicAlgebra P r x.1 x.2⟩
  map_zero' := Subtype.ext rfl
  map_one' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

set_option maxHeartbeats 800000 in
@[simp] theorem cartwrightStegerOrderToCyclicAlgebra_coe
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r) :
    (cartwrightStegerOrderToCyclicAlgebra P r x :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) = x.1 :=
  rfl

theorem cartwrightStegerOrderToCyclicAlgebra_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (cartwrightStegerOrderToCyclicAlgebra P r) := by
  intro x y hxy
  apply Subtype.ext
  calc
    x.1 = (cartwrightStegerOrderToCyclicAlgebra P r x :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) :=
      (cartwrightStegerOrderToCyclicAlgebra_coe P r x).symm
    _ = (cartwrightStegerOrderToCyclicAlgebra P r y :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) :=
      congrArg (fun z : CyclicAlgebra P r => z.1) hxy
    _ = y.1 := cartwrightStegerOrderToCyclicAlgebra_coe P r y

noncomputable def cartwrightStegerOrderToBuilding
    (P : BasePrime) (r : Rank) :
    CartwrightStegerOrder P r →+*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingLocalField P) :=
  (cyclicAlgebraToBuilding P r).toRingHom.comp
    (cartwrightStegerOrderToCyclicAlgebra P r)

noncomputable def cartwrightStegerOrderUnitToBuildingGL
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrder P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Units.map (cartwrightStegerOrderToBuilding P r)

noncomputable def constantCyclicEmbedding
    (P : BasePrime) (r : Rank) :
    ConstantExtension P r →+* CyclicAlgebra P r where
  toFun := constantCyclicElement P r
  map_zero' := Subtype.ext (map_zero (constantMatrixEmbedding P r))
  map_one' := Subtype.ext (map_one (constantMatrixEmbedding P r))
  map_add' c d := Subtype.ext (map_add (constantMatrixEmbedding P r) c d)
  map_mul' c d := Subtype.ext (map_mul (constantMatrixEmbedding P r) c d)

noncomputable def constantCyclicUnitHom
    (P : BasePrime) (r : Rank) :
    (ConstantExtension P r)ˣ →* (CyclicAlgebra P r)ˣ :=
  Units.map (constantCyclicEmbedding P r)

noncomputable def cartwrightStegerBCyclicUnit
    (P : BasePrime) (r : Rank) : (CyclicAlgebra P r)ˣ where
  val := cartwrightStegerBCyclicElement P r
  inv := ⟨cartwrightStegerBInverseMatrix P r,
    cartwrightStegerOrder_le_cyclicAlgebra P r _
      (cartwrightStegerBInverseMatrix_mem_order P r)⟩
  val_inv := Subtype.ext (cartwrightStegerB_mul_inverse P r)
  inv_val := Subtype.ext (cartwrightStegerB_inverse_mul P r)

noncomputable def cartwrightStegerGeneratorCyclicUnit
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    (CyclicAlgebra P r)ˣ :=
  constantCyclicUnitHom P r (constantClassRepresentative P r u) *
    cartwrightStegerBCyclicUnit P r *
      (constantCyclicUnitHom P r (constantClassRepresentative P r u))⁻¹

@[simp] theorem cartwrightStegerGeneratorCyclicUnit_coe
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    (cartwrightStegerGeneratorCyclicUnit P r u : CyclicAlgebra P r) =
      cartwrightStegerGeneratorCyclicElement P r u := by
  apply Subtype.ext
  simp [cartwrightStegerGeneratorCyclicUnit, constantCyclicUnitHom,
    constantCyclicEmbedding, cartwrightStegerBCyclicUnit,
    cartwrightStegerGeneratorCyclicElement]

noncomputable def cyclicUnitToBuildingGL
    (P : BasePrime) (r : Rank) :
    (CyclicAlgebra P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Units.map (cyclicAlgebraToBuilding P r).toRingHom

@[simp] theorem cartwrightStegerGeneratorCyclicUnit_to_buildingGL
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    cyclicUnitToBuildingGL P r (cartwrightStegerGeneratorCyclicUnit P r u) =
      buildingCartwrightStegerGeneratorGL P r
        (constantClassRepresentative P r u) := by
  apply Units.ext
  change cyclicAlgebraToBuilding P r
      (cartwrightStegerGeneratorCyclicUnit P r u : CyclicAlgebra P r) = _
  rw [cartwrightStegerGeneratorCyclicUnit_coe,
    cyclicAlgebraToBuilding_cartwrightStegerGeneratorCyclicElement]

noncomputable def cyclicUnitToBuildingPGL
    (P : BasePrime) (r : Rank) :
    (CyclicAlgebra P r)ˣ →*
      Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Matrix.ProjGenLinGroup.mk.comp (cyclicUnitToBuildingGL P r)

noncomputable def CyclicCartwrightStegerLattice
    (P : BasePrime) (r : Rank) : Subgroup ((CyclicAlgebra P r)ˣ) :=
  Subgroup.closure (Set.range (cartwrightStegerGeneratorCyclicUnit P r))

@[simp] theorem cartwrightStegerGeneratorCyclicUnit_to_buildingPGL
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    cyclicUnitToBuildingPGL P r
        (cartwrightStegerGeneratorCyclicUnit P r u) =
      buildingCartwrightStegerGenerator P r u := by
  change Matrix.ProjGenLinGroup.mk
      (cyclicUnitToBuildingGL P r
        (cartwrightStegerGeneratorCyclicUnit P r u)) = _
  rw [cartwrightStegerGeneratorCyclicUnit_to_buildingGL]
  rfl

theorem map_CyclicCartwrightStegerLattice_to_building
    (P : BasePrime) (r : Rank) :
    (CyclicCartwrightStegerLattice P r).map
        (cyclicUnitToBuildingPGL P r) =
      BuildingCartwrightStegerLattice P r := by
  rw [CyclicCartwrightStegerLattice, MonoidHom.map_closure,
    BuildingCartwrightStegerLattice]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, (cartwrightStegerGeneratorCyclicUnit_to_buildingPGL
      P r u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨cartwrightStegerGeneratorCyclicUnit P r u,
      ⟨u, rfl⟩,
      cartwrightStegerGeneratorCyclicUnit_to_buildingPGL P r u⟩

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
