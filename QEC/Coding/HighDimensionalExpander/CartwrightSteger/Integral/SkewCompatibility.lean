import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Integral.OrderUnitReconstruction
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Building.BuildingSkewRepresentation

/-!
# Compatibility of the global and building skew representations

The global skew representation lands in the constructed cyclic algebra, and
the building representation is obtained by applying the explicit
building-place algebra map to that cyclic-algebra element.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

/-- The cyclic generator as a unit of the constructed cyclic algebra. -/
noncomputable def cyclicGeneratorCyclicUnit
    (P : BasePrime) (r : Rank) : (CyclicAlgebra P r)ˣ where
  val := cyclicGeneratorCyclicElement P r
  inv := cyclicGeneratorInverseCyclicElement P r
  val_inv := Subtype.ext (cyclicGenerator_mul_inverse P r)
  inv_val := Subtype.ext (cyclicGenerator_inverse_mul P r)

theorem cyclicGeneratorCyclicUnit_zpow_coe
    (P : BasePrime) (r : Rank) (n : ℤ) :
    ((cyclicGeneratorCyclicUnit P r ^ n : (CyclicAlgebra P r)ˣ) :
        CyclicAlgebra P r).1 =
      globalCyclicZMatrixHom P r (Multiplicative.ofAdd n) := by
  let F : (CyclicAlgebra P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
    Units.map (CyclicAlgebra P r).val.toRingHom
  have hgen : F (cyclicGeneratorCyclicUnit P r) = cyclicGenerator P r := by
    apply Units.ext
    rfl
  have hp := map_zpow F (cyclicGeneratorCyclicUnit P r) n
  rw [hgen] at hp
  exact congrArg Units.val hp

theorem globalCyclicZMatrixHom_mem_cyclicAlgebra
    (P : BasePrime) (r : Rank) (n : Multiplicative ℤ) :
    globalCyclicZMatrixHom P r n ∈ CyclicAlgebra P r := by
  have hn : n = Multiplicative.ofAdd n.toAdd := rfl
  rw [hn, ← cyclicGeneratorCyclicUnit_zpow_coe P r n.toAdd]
  exact (cyclicGeneratorCyclicUnit P r ^ n.toAdd).1.property

theorem skewLaurentToGlobalMatrix_mem_cyclicAlgebra
    (P : BasePrime) (r : Rank)
    (f : CartwrightStegerSkewLaurentRing P r) :
    skewLaurentToGlobalMatrix P r f ∈ CyclicAlgebra P r := by
  induction f using SkewMonoidAlgebra.induction_on with
  | zero => exact (CyclicAlgebra P r).zero_mem
  | add f g hf hg =>
      rw [map_add]
      exact (CyclicAlgebra P r).add_mem hf hg
  | single n c =>
      rw [skewLaurentToGlobalMatrix_single]
      exact (CyclicAlgebra P r).mul_mem
        (constantMatrix_mem_cyclicAlgebra P r c)
        (globalCyclicZMatrixHom_mem_cyclicAlgebra P r n)

/-- The global skew representation with its proved cyclic-algebra codomain. -/
noncomputable def skewLaurentToCyclicAlgebra
    (P : BasePrime) (r : Rank) :
    CartwrightStegerSkewLaurentRing P r →+* CyclicAlgebra P r :=
  (skewLaurentToGlobalMatrix P r).codRestrict
    (CyclicAlgebra P r)
    (skewLaurentToGlobalMatrix_mem_cyclicAlgebra P r)

@[simp] theorem skewLaurentToCyclicAlgebra_coe
    (P : BasePrime) (r : Rank)
    (f : CartwrightStegerSkewLaurentRing P r) :
    (skewLaurentToCyclicAlgebra P r f).1 =
      skewLaurentToGlobalMatrix P r f := rfl

theorem cyclicAlgebraToBuilding_globalCyclicZ
    (P : BasePrime) (r : Rank) (n : Multiplicative ℤ) :
    cyclicAlgebraToBuilding P r
        ⟨globalCyclicZMatrixHom P r n,
          globalCyclicZMatrixHom_mem_cyclicAlgebra P r n⟩ =
      buildingCyclicZMatrixHom P r n := by
  let F : (CyclicAlgebra P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (BuildingLocalField P) :=
    Units.map (cyclicAlgebraToBuilding P r).toRingHom
  have hgen : F (cyclicGeneratorCyclicUnit P r) =
      buildingCyclicGeneratorGL P r := by
    apply Units.ext
    dsimp [F]
    simpa only [cyclicGeneratorCyclicUnit,
      cyclicAlgebraToBuilding_apply, buildingCyclicGeneratorGL_coe] using
      cyclicAlgebraToBuilding_cyclicGeneratorCyclicElement P r
  have hp := map_zpow F (cyclicGeneratorCyclicUnit P r) n.toAdd
  rw [hgen] at hp
  have hpval := congrArg Units.val hp
  change cyclicAlgebraToBuilding P r
      ((cyclicGeneratorCyclicUnit P r ^ n.toAdd :
        (CyclicAlgebra P r)ˣ) : CyclicAlgebra P r) =
    ((buildingCyclicGeneratorGL P r ^ n.toAdd :
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (BuildingLocalField P)) : Matrix _ _ _) at hpval
  have hsource :
      ((cyclicGeneratorCyclicUnit P r ^ n.toAdd :
        (CyclicAlgebra P r)ˣ) : CyclicAlgebra P r) =
      ⟨globalCyclicZMatrixHom P r n,
        globalCyclicZMatrixHom_mem_cyclicAlgebra P r n⟩ := by
    apply Subtype.ext
    exact cyclicGeneratorCyclicUnit_zpow_coe P r n.toAdd
  rw [← hsource]
  exact hpval

/-- Applying the building-place algebra map to the global skew image gives
the independently constructed building skew representation. -/
theorem cyclicAlgebraToBuilding_skewLaurentToCyclicAlgebra
    (P : BasePrime) (r : Rank)
    (f : CartwrightStegerSkewLaurentRing P r) :
    cyclicAlgebraToBuilding P r (skewLaurentToCyclicAlgebra P r f) =
      skewLaurentToBuildingMatrix P r f := by
  induction f using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | add f g hf hg =>
      calc
        _ = cyclicAlgebraToBuilding P r
              (skewLaurentToCyclicAlgebra P r f +
                skewLaurentToCyclicAlgebra P r g) :=
          congrArg (cyclicAlgebraToBuilding P r)
            (map_add (skewLaurentToCyclicAlgebra P r) f g)
        _ = cyclicAlgebraToBuilding P r
              (skewLaurentToCyclicAlgebra P r f) +
            cyclicAlgebraToBuilding P r
              (skewLaurentToCyclicAlgebra P r g) :=
          map_add (cyclicAlgebraToBuilding P r) _ _
        _ = skewLaurentToBuildingMatrix P r f +
            skewLaurentToBuildingMatrix P r g := by rw [hf, hg]
        _ = _ := (map_add (skewLaurentToBuildingMatrix P r) f g).symm
  | single n c =>
      rw [skewLaurentToBuildingMatrix_single]
      have hs : skewLaurentToCyclicAlgebra P r
          (SkewMonoidAlgebra.single n c) =
          constantCyclicElement P r c *
            ⟨globalCyclicZMatrixHom P r n,
              globalCyclicZMatrixHom_mem_cyclicAlgebra P r n⟩ := by
        apply Subtype.ext
        rw [skewLaurentToCyclicAlgebra_coe,
          skewLaurentToGlobalMatrix_single]
        rfl
      rw [hs]
      rw [map_mul, cyclicAlgebraToBuilding_constantCyclicElement,
        cyclicAlgebraToBuilding_globalCyclicZ]

/-- A global order unit which is integral at the building place together
with its inverse has building projective image in the explicit compact cyclic
subgroup. -/
theorem cyclicOrderUnitToBuildingPGL_mem_compactCyclicSubgroup
    (P : BasePrime) (r : Rank) (u : (CartwrightStegerOrder P r)ˣ)
    (hlocal : ∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r
          (cartwrightStegerOrderToCyclicAlgebra P r
            (u : CartwrightStegerOrder P r)))
    (hlocalInv : ∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r
          (cartwrightStegerOrderToCyclicAlgebra P r
            ((u⁻¹ : (CartwrightStegerOrder P r)ˣ) :
              CartwrightStegerOrder P r))) :
    cyclicUnitToBuildingPGL P r
        (Units.map (cartwrightStegerOrderToCyclicAlgebra P r).toMonoidHom u) ∈
      BuildingCompactCyclicSubgroup P r := by
  obtain ⟨v, hv⟩ :=
    exists_skewLaurentUnit_of_orderUnit_and_buildingIntegral
      P r u hlocal hlocalInv
  have hcyclic : skewLaurentToCyclicAlgebra P r
      (v : CartwrightStegerSkewLaurentRing P r) =
      cartwrightStegerOrderToCyclicAlgebra P r
        (u : CartwrightStegerOrder P r) := by
    apply Subtype.ext
    exact hv
  have himage : buildingIntegralUnitPGLHom P r v =
      cyclicUnitToBuildingPGL P r
        (Units.map (cartwrightStegerOrderToCyclicAlgebra P r).toMonoidHom u) := by
    apply congrArg (Matrix.ProjGenLinGroup.mk :
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) →*
        Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))
    apply Units.ext
    change skewLaurentToBuildingMatrix P r v =
      cyclicAlgebraToBuilding P r
        (cartwrightStegerOrderToCyclicAlgebra P r
          (u : CartwrightStegerOrder P r))
    rw [← cyclicAlgebraToBuilding_skewLaurentToCyclicAlgebra, hcyclic]
  rw [← himage, ← range_buildingIntegralUnitPGLHom]
  exact ⟨v, rfl⟩

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
