import QEC.Coding.HighDimensionalExpander.CartwrightSteger.CyclicAlgebra.Relations

/-!
# The finite Cartwright--Steger image as a quotient of the building lattice

The global arithmetic-order lattice and the building-place lattice are two
images of the same explicit order-unit generators.  This file proves that
finite congruence reduction descends through the building image.  Thus the
finite vertex group is a genuine quotient of the simply transitive building
lattice, rather than merely a group equipped with similarly named generators.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

/-- Base change from the integral split lattice to the global split-matrix
lattice, with codomain restricted to the actual Cartwright--Steger group. -/
noncomputable def orderSplitLatticeToGlobalMatrixGroup
    (P : BasePrime) (r : Rank) :
    OrderSplitCartwrightStegerLattice P r →*
      CartwrightStegerMatrixGroup P r where
  toFun x := ⟨orderSplitBaseChangeGLHom P r
      (x : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r)), by
    have hx : orderSplitBaseChangeGLHom P r
        (x : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) ∈
        (OrderSplitCartwrightStegerLattice P r).map
          (orderSplitBaseChangeGLHom P r) :=
      ⟨x, x.property, rfl⟩
    rw [map_OrderSplitCartwrightStegerLattice_to_global] at hx
    exact hx⟩
  map_one' := Subtype.ext (map_one (orderSplitBaseChangeGLHom P r))
  map_mul' x y := Subtype.ext
    (map_mul (orderSplitBaseChangeGLHom P r)
      (x : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r))
      (y : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r)))

theorem orderSplitLatticeToGlobalMatrixGroup_surjective
    (P : BasePrime) (r : Rank) :
    Function.Surjective (orderSplitLatticeToGlobalMatrixGroup P r) := by
  intro y
  have hy : (y : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)) ∈
      (OrderSplitCartwrightStegerLattice P r).map
        (orderSplitBaseChangeGLHom P r) := by
    rw [map_OrderSplitCartwrightStegerLattice_to_global]
    exact y.property
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem orderSplitLatticeToGlobalMatrixGroup_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (orderSplitLatticeToGlobalMatrixGroup P r) := by
  intro x y hxy
  apply Subtype.ext
  apply orderSplitBaseChangeGLHom_injective P r
  exact congrArg Subtype.val hxy

/-- Finite congruence reduction transported to the global matrix lattice.
The descent is canonical because integral base change is injective. -/
noncomputable def globalMatrixLatticeReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    CartwrightStegerMatrixGroup P r →* IndexCartwrightStegerImage P r level :=
  (orderSplitLatticeToGlobalMatrixGroup P r).liftOfSurjective
    (orderSplitLatticeToGlobalMatrixGroup_surjective P r)
    ⟨orderSplitLatticeReduction P r level, by
      intro x hx
      have hxOne : x = 1 :=
        orderSplitLatticeToGlobalMatrixGroup_injective P r
          ((MonoidHom.mem_ker.mp hx).trans (map_one _).symm)
      subst x
      exact Subgroup.one_mem _⟩

@[simp] theorem globalMatrixLatticeReduction_orderSplit
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : OrderSplitCartwrightStegerLattice P r) :
    globalMatrixLatticeReduction P r level
        (orderSplitLatticeToGlobalMatrixGroup P r x) =
      orderSplitLatticeReduction P r level x := by
  simp [globalMatrixLatticeReduction]

/-- The order-unit lattice mapped to its global split-matrix image. -/
noncomputable def orderUnitLatticeToGlobalMatrixGroup
    (P : BasePrime) (r : Rank) :
    CartwrightStegerOrderUnitLattice P r →*
      CartwrightStegerMatrixGroup P r where
  toFun u := ⟨orderUnitToGlobalGL P r
      (u : (CartwrightStegerOrder P r)ˣ), by
    have hu : orderUnitToGlobalGL P r
        (u : (CartwrightStegerOrder P r)ˣ) ∈
        (CartwrightStegerOrderUnitLattice P r).map
          (orderUnitToGlobalGL P r) := ⟨u, u.property, rfl⟩
    rw [map_orderUnitLattice_to_global] at hu
    exact hu⟩
  map_one' := Subtype.ext (map_one (orderUnitToGlobalGL P r))
  map_mul' u v := Subtype.ext (map_mul (orderUnitToGlobalGL P r)
    (u : (CartwrightStegerOrder P r)ˣ)
    (v : (CartwrightStegerOrder P r)ˣ))

theorem orderUnitLatticeToGlobalMatrixGroup_surjective
    (P : BasePrime) (r : Rank) :
    Function.Surjective (orderUnitLatticeToGlobalMatrixGroup P r) := by
  intro y
  have hy : (y : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)) ∈
      (CartwrightStegerOrderUnitLattice P r).map
        (orderUnitToGlobalGL P r) := by
    rw [map_orderUnitLattice_to_global]
    exact y.property
  obtain ⟨u, hu, huy⟩ := hy
  exact ⟨⟨u, hu⟩, Subtype.ext huy⟩

/-- The order-unit lattice mapped onto the genuine building lattice. -/
noncomputable def orderUnitLatticeToBuildingLattice
    (P : BasePrime) (r : Rank) :
    CartwrightStegerOrderUnitLattice P r →*
      BuildingCartwrightStegerLattice P r where
  toFun u := ⟨orderUnitToBuildingPGL P r
      (u : (CartwrightStegerOrder P r)ˣ), by
    have hu : orderUnitToBuildingPGL P r
        (u : (CartwrightStegerOrder P r)ˣ) ∈
        (CartwrightStegerOrderUnitLattice P r).map
          (orderUnitToBuildingPGL P r) := ⟨u, u.property, rfl⟩
    rw [map_orderUnitLattice_to_building] at hu
    exact hu⟩
  map_one' := Subtype.ext (map_one (orderUnitToBuildingPGL P r))
  map_mul' u v := Subtype.ext (map_mul (orderUnitToBuildingPGL P r)
    (u : (CartwrightStegerOrder P r)ˣ)
    (v : (CartwrightStegerOrder P r)ˣ))

theorem orderUnitLatticeToBuildingLattice_surjective
    (P : BasePrime) (r : Rank) :
    Function.Surjective (orderUnitLatticeToBuildingLattice P r) := by
  intro g
  obtain ⟨u, hu, hug⟩ :=
    exists_orderUnitLattice_lift_of_buildingLattice P r g
  exact ⟨⟨u, hu⟩, Subtype.ext hug⟩

/-- Reduction of the common order-unit lattice, routed through its global
split-matrix image. -/
noncomputable def orderUnitLatticeReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    CartwrightStegerOrderUnitLattice P r →*
      IndexCartwrightStegerImage P r level :=
  (globalMatrixLatticeReduction P r level).comp
    (orderUnitLatticeToGlobalMatrixGroup P r)

theorem orderUnitLatticeReduction_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (orderUnitLatticeReduction P r level) := by
  intro y
  obtain ⟨x, hx⟩ := orderSplitLatticeReduction_surjective P r level y
  obtain ⟨u, hu⟩ := orderUnitLatticeToGlobalMatrixGroup_surjective P r
    (orderSplitLatticeToGlobalMatrixGroup P r x)
  refine ⟨u, ?_⟩
  change globalMatrixLatticeReduction P r level
      (orderUnitLatticeToGlobalMatrixGroup P r u) = y
  rw [hu, globalMatrixLatticeReduction_orderSplit, hx]

/-- If an arithmetic lattice unit is projectively trivial at the building
place, then every selected finite projective reduction is trivial.  This is
the kernel inclusion needed for quotient descent. -/
theorem ker_orderUnitLatticeToBuildingLattice_le_reduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    (orderUnitLatticeToBuildingLattice P r).ker ≤
      (orderUnitLatticeReduction P r level).ker := by
  intro u hu
  have huBuilding : orderUnitToBuildingPGL P r u = 1 := by
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hu)
  have huCompact : orderUnitToBuildingPGL P r u ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank := by
    rw [huBuilding]
    exact Subgroup.one_mem _
  have huGlobal : orderUnitToGlobalPGL P r u = 1 := by
    have hnormal :=
      orderUnitToGlobalPGL_eq_compactNormalForm_of_building_eq
        P r u huCompact 1 0 (by simpa using huBuilding)
    simpa [globalCompactNormalForm, constantUnitMatrix] using hnormal
  obtain ⟨x, hx⟩ := orderSplitLatticeToGlobalMatrixGroup_surjective P r
    (orderUnitLatticeToGlobalMatrixGroup P r u)
  have hxGlobal : Matrix.ProjGenLinGroup.mk
        (orderSplitBaseChangeGLHom P r x) =
      Matrix.ProjGenLinGroup.mk (orderSplitBaseChangeGLHom P r 1) := by
    rw [show orderSplitBaseChangeGLHom P r x =
        orderUnitToGlobalGL P r u from congrArg Subtype.val hx]
    simpa [orderUnitToGlobalPGL] using huGlobal
  have hxReduction :=
    orderSplitReductionPGLHom_eq_of_baseChange_projective_eq
      P r level x 1 hxGlobal
  rw [MonoidHom.mem_ker]
  change globalMatrixLatticeReduction P r level
      (orderUnitLatticeToGlobalMatrixGroup P r u) = 1
  rw [← hx, globalMatrixLatticeReduction_orderSplit]
  apply Subtype.ext
  change orderSplitReductionPGLHom P r level x = 1
  simpa using hxReduction

/-- Genuine congruence reduction of the simply transitive building lattice.
It is obtained by quotient descent, not by choosing a word for each element. -/
noncomputable def buildingLatticeReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    BuildingCartwrightStegerLattice P r →*
      IndexCartwrightStegerImage P r level :=
  (orderUnitLatticeToBuildingLattice P r).liftOfSurjective
    (orderUnitLatticeToBuildingLattice_surjective P r)
    ⟨orderUnitLatticeReduction P r level,
      ker_orderUnitLatticeToBuildingLattice_le_reduction P r level⟩

@[simp] theorem buildingLatticeReduction_orderUnit
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : CartwrightStegerOrderUnitLattice P r) :
    buildingLatticeReduction P r level
        (orderUnitLatticeToBuildingLattice P r u) =
      orderUnitLatticeReduction P r level u := by
  simp [buildingLatticeReduction]

theorem buildingLatticeReduction_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (buildingLatticeReduction P r level) := by
  intro y
  obtain ⟨u, hu⟩ := orderUnitLatticeReduction_surjective P r level y
  exact ⟨orderUnitLatticeToBuildingLattice P r u, by
    rw [buildingLatticeReduction_orderUnit, hu]⟩

/-- A class-indexed generator bundled in the common arithmetic order-unit
lattice. -/
noncomputable def orderUnitLatticeGenerator
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    CartwrightStegerOrderUnitLattice P r :=
  ⟨cartwrightStegerOrderUnitGenerator P r u,
    Subgroup.subset_closure ⟨u, rfl⟩⟩

/-- The corresponding class-indexed generator in the integral split
lattice. -/
noncomputable def orderSplitLatticeGenerator
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    OrderSplitCartwrightStegerLattice P r :=
  ⟨orderSplitCartwrightStegerGeneratorGL P r
      (constantClassRepresentative P r u),
    Subgroup.subset_closure ⟨u, rfl⟩⟩

@[simp] theorem orderUnitLatticeGenerator_to_building
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    orderUnitLatticeToBuildingLattice P r
        (orderUnitLatticeGenerator P r u) =
      buildingLatticeGenerator P r u := by
  apply Subtype.ext
  exact orderUnitToBuildingPGL_generator P r u

theorem orderUnitLatticeGenerator_to_global_eq_orderSplit
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    orderUnitLatticeToGlobalMatrixGroup P r
        (orderUnitLatticeGenerator P r u) =
      orderSplitLatticeToGlobalMatrixGroup P r
        (orderSplitLatticeGenerator P r u) := by
  apply Subtype.ext
  change orderUnitToGlobalGL P r
      (cartwrightStegerOrderUnitGenerator P r u) =
    orderSplitBaseChangeGLHom P r
      (orderSplitCartwrightStegerGeneratorGL P r
        (constantClassRepresentative P r u))
  rw [orderUnitToGlobalGL_generator,
    map_orderSplitCartwrightStegerClassGeneratorGL_to_global]

@[simp] theorem orderUnitLatticeReduction_generator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) :
    orderUnitLatticeReduction P r level
        (orderUnitLatticeGenerator P r u) =
      ⟨indexCartwrightStegerClassGenerator P r level u,
        indexCartwrightStegerGenerator_mem_image P r level u⟩ := by
  change globalMatrixLatticeReduction P r level
      (orderUnitLatticeToGlobalMatrixGroup P r
        (orderUnitLatticeGenerator P r u)) = _
  rw [orderUnitLatticeGenerator_to_global_eq_orderSplit,
    globalMatrixLatticeReduction_orderSplit]
  apply Subtype.ext
  exact orderSplitReductionPGLHom_classGenerator P r level u

/-- Building-lattice reduction sends each genuine building generator to the
corresponding finite Cartwright--Steger generator. -/
@[simp] theorem buildingLatticeReduction_generator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) :
    buildingLatticeReduction P r level
        (buildingLatticeGenerator P r u) =
      ⟨indexCartwrightStegerClassGenerator P r level u,
        indexCartwrightStegerGenerator_mem_image P r level u⟩ := by
  rw [← orderUnitLatticeGenerator_to_building,
    buildingLatticeReduction_orderUnit,
    orderUnitLatticeReduction_generator]

/-- The principal congruence subgroup directly inside the simply transitive
building lattice. -/
noncomputable def BuildingCartwrightStegerCongruenceSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (BuildingCartwrightStegerLattice P r) :=
  (buildingLatticeReduction P r level).ker

noncomputable instance buildingCartwrightStegerCongruenceSubgroupNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (BuildingCartwrightStegerCongruenceSubgroup P r level).Normal := by
  dsimp [BuildingCartwrightStegerCongruenceSubgroup]
  infer_instance

/-- Exact quotient identification between the simply transitive building
lattice and the finite Cartwright--Steger vertex group. -/
noncomputable def buildingLatticeQuotientEquiv
    (P : BasePrime) (r : Rank) (level : Nat) :
    BuildingCartwrightStegerLattice P r ⧸
        BuildingCartwrightStegerCongruenceSubgroup P r level ≃*
      IndexCartwrightStegerImage P r level :=
  QuotientGroup.quotientKerEquivOfSurjective
    (buildingLatticeReduction P r level)
    (buildingLatticeReduction_surjective P r level)

theorem natCard_buildingLatticeQuotient
    (P : BasePrime) (r : Rank) (level : Nat) :
    Nat.card
        (BuildingCartwrightStegerLattice P r ⧸
          BuildingCartwrightStegerCongruenceSubgroup P r level) =
      Nat.card (IndexCartwrightStegerImage P r level) :=
  Nat.card_congr (buildingLatticeQuotientEquiv P r level).toEquiv

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
