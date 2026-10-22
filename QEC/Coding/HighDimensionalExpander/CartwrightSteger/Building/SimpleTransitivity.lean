import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Projective.Stabilizer

/-!
# Simple transitivity of the Cartwright--Steger lattice

This file closes the arithmetic-to-building argument.  It first records that
the upper-unipotent infinity-residue condition depends only on the projective
matrix, then uses arithmetic-order lifts to prove that the building lattice
has trivial vertex stabilizers.  Together with the previously proved
surjectivity, this gives simple transitivity on vertices.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

/-- Inner conjugation, and hence the upper-unipotent infinity-residue
condition, is unchanged when a global matrix is multiplied by a scalar. -/
theorem hasUpperUnipotentInfinityResidue_of_projective_mk_eq
    (P : BasePrime) (r : Rank)
    {A B : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)}
    (hA : HasUpperUnipotentInfinityResidue P r A)
    (hprojective : Matrix.ProjGenLinGroup.mk A =
      Matrix.ProjGenLinGroup.mk B) :
    HasUpperUnipotentInfinityResidue P r B := by
  obtain ⟨c, hc⟩ :=
    SphericalHecke.exists_scalar_mul_eq_of_projective_mk_eq hprojective
  let S := Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank) c
  have hScomm (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) :
      (S : Matrix _ _ _) * M = M * (S : Matrix _ _ _) := by
    dsimp [S]
    exact Matrix.scalar_comm _ (fun b => Commute.all _ b) M
  have hScancel (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) :
      (S : Matrix _ _ _) * M *
        ((S⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) : Matrix _ _ _) = M := by
    rw [hScomm]
    simp only [mul_assoc]
    rw [← Units.val_mul]
    simp
  have hconj : ∀ X,
      infinityConjugationLinearMap P r A X =
        infinityConjugationLinearMap P r B X := by
    intro X
    change (A : Matrix _ _ _) * X *
        ((A⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) : Matrix _ _ _) =
      (B : Matrix _ _ _) * X *
        ((B⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) : Matrix _ _ _)
    change A = S * B at hc
    rw [hc]
    calc
      (((S * B : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) : Matrix _ _ _) * X *
        (((S * B)⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) : Matrix _ _ _)) =
          (S : Matrix _ _ _) *
            ((B : Matrix _ _ _) * X *
              ((B⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
                (SplittingFunctionField P r)) : Matrix _ _ _)) *
            ((S⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) : Matrix _ _ _) := by
              simp only [mul_inv_rev, Units.val_mul]
              group
      _ = _ := hScancel _
  refine ⟨?_, ?_⟩
  · intro X hX
    rw [← hconj X]
    exact hA.1 X hX
  · intro k ζ
    rw [← hconj]
    exact hA.2 k ζ

/-- The global projective representation of arithmetic-order units. -/
noncomputable def orderUnitToGlobalPGL
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrder P r)ˣ →*
      Matrix.ProjGenLinGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  Matrix.ProjGenLinGroup.mk.comp (orderUnitToGlobalGL P r)

theorem orderUnitToGlobalGL_orderYUnit
    (P : BasePrime) (r : Rank) :
    orderUnitToGlobalGL P r (cartwrightStegerOrderYUnit P r) =
      Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
        (Units.mk0 (splittingY P r) (splittingY_ne_zero P r)) := by
  apply Units.ext
  rfl

/-- The central normalization used to choose an integral building
representative is invisible in the global projective representation too. -/
theorem orderUnitToGlobalPGL_normalizedOrderUnit
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ) (q : ℤ) :
    orderUnitToGlobalPGL P r (normalizedOrderUnit P r u q) =
      orderUnitToGlobalPGL P r u := by
  rw [normalizedOrderUnit, map_mul, map_zpow]
  have hy : orderUnitToGlobalPGL P r
      (cartwrightStegerOrderYUnit P r) = 1 := by
    change Matrix.ProjGenLinGroup.mk
        (orderUnitToGlobalGL P r (cartwrightStegerOrderYUnit P r)) = 1
    rw [orderUnitToGlobalGL_orderYUnit]
    exact Matrix.ProjGenLinGroup.mk_scalar _
  rw [hy]
  simp

/-- A projectively compact order unit and any compact normal form for its
building image determine the same global projective element.  The bridge is
an actual unit of the integral skew Laurent order, reconstructed together
with its inverse; no local-to-global injectivity is assumed. -/
theorem orderUnitToGlobalPGL_eq_compactNormalForm_of_building_eq
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ)
    (hcompact : orderUnitToBuildingPGL P r u ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank)
    (c : (ConstantExtension P r)ˣ) (j : ℕ)
    (hbuilding : orderUnitToBuildingPGL P r u =
      buildingConstantPGLHom P r c *
        buildingCyclicGeneratorPGL P r ^ j) :
    orderUnitToGlobalPGL P r u =
      Matrix.ProjGenLinGroup.mk (globalCompactNormalForm P r c j) := by
  obtain ⟨q, hq⟩ :=
    exists_localDetOrder_quotient_of_orderUnit_mem_maximalCompact
      P r u hcompact
  obtain ⟨hlocal, hlocalInv⟩ :=
    normalizedOrderUnit_buildingIntegral_witnesses
      P r u q hcompact hq
  obtain ⟨v, hv⟩ :=
    exists_skewLaurentUnit_of_orderUnit_and_buildingIntegral
      P r (normalizedOrderUnit P r u q) hlocal hlocalInv
  let w : (CartwrightStegerSkewLaurentRing P r)ˣ :=
    skewLaurentMonomialUnit P r c (j : ℤ)
  have hcyclic : skewLaurentToCyclicAlgebra P r
      (v : CartwrightStegerSkewLaurentRing P r) =
      cartwrightStegerOrderToCyclicAlgebra P r
        (normalizedOrderUnit P r u q : CartwrightStegerOrder P r) := by
    apply Subtype.ext
    exact hv
  have hvBuilding : buildingIntegralUnitPGLHom P r v =
      orderUnitToBuildingPGL P r (normalizedOrderUnit P r u q) := by
    apply congrArg (Matrix.ProjGenLinGroup.mk :
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) →*
        Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))
    apply Units.ext
    change skewLaurentToBuildingMatrix P r v =
      cyclicAlgebraToBuilding P r
        (cartwrightStegerOrderToCyclicAlgebra P r
          (normalizedOrderUnit P r u q : CartwrightStegerOrder P r))
    rw [← cyclicAlgebraToBuilding_skewLaurentToCyclicAlgebra, hcyclic]
  have hvwBuilding : buildingIntegralUnitPGLHom P r v =
      buildingIntegralUnitPGLHom P r w := by
    calc
      _ = orderUnitToBuildingPGL P r
          (normalizedOrderUnit P r u q) := hvBuilding
      _ = orderUnitToBuildingPGL P r u :=
        orderUnitToBuildingPGL_normalizedOrderUnit P r u q
      _ = buildingConstantPGLHom P r c *
          buildingCyclicGeneratorPGL P r ^ j := hbuilding
      _ = buildingIntegralUnitPGLHom P r w := by
        dsimp [w]
        rw [buildingIntegralUnitPGLHom_monomial, zpow_natCast]
  have hvwGlobal : globalIntegralUnitPGLHom P r v =
      globalIntegralUnitPGLHom P r w :=
    globalIntegralUnitPGLHom_eq_of_buildingIntegralUnitPGLHom_eq
      P r hvwBuilding
  have hvGlobal : globalIntegralUnitPGLHom P r v =
      orderUnitToGlobalPGL P r (normalizedOrderUnit P r u q) := by
    apply congrArg (Matrix.ProjGenLinGroup.mk :
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r) →*
        Matrix.ProjGenLinGroup (Fin r.matrixRank)
          (SplittingFunctionField P r))
    apply Units.ext
    exact hv
  calc
    orderUnitToGlobalPGL P r u =
        orderUnitToGlobalPGL P r (normalizedOrderUnit P r u q) :=
      (orderUnitToGlobalPGL_normalizedOrderUnit P r u q).symm
    _ = globalIntegralUnitPGLHom P r v := hvGlobal.symm
    _ = globalIntegralUnitPGLHom P r w := hvwGlobal
    _ = Matrix.ProjGenLinGroup.mk (globalCompactNormalForm P r c j) := by
      dsimp [w, globalCompactNormalForm]
      rw [globalIntegralUnitPGLHom_monomial, zpow_natCast]
      rfl

/-- A compact building image of an arithmetic lattice unit satisfies the
identity-diagonal condition at infinity. -/
theorem orderUnitLattice_hasIdentityConjugationDiagonal
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ)
    (hu : u ∈ CartwrightStegerOrderUnitLattice P r)
    (hcompact : orderUnitToBuildingPGL P r u ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank) :
    BuildingElementHasIdentityConjugationDiagonal P r
      (orderUnitToBuildingPGL P r u) := by
  intro c j hj hbuilding
  have hglobal :=
    orderUnitToGlobalPGL_eq_compactNormalForm_of_building_eq
      P r u hcompact c j hbuilding
  have hglobalMem : orderUnitToGlobalGL P r u ∈
      CartwrightStegerMatrixGroup P r := by
    have hmap : orderUnitToGlobalGL P r u ∈
        (CartwrightStegerOrderUnitLattice P r).map
          (orderUnitToGlobalGL P r) := ⟨u, hu, rfl⟩
    rw [map_orderUnitLattice_to_global] at hmap
    exact hmap
  have hupperUnit : HasUpperUnipotentInfinityResidue P r
      (orderUnitToGlobalGL P r u) :=
    cartwrightStegerMatrixGroup_le_upperUnipotentInfinityResidueSubgroup
      P r hglobalMem
  have hupperNormal : HasUpperUnipotentInfinityResidue P r
      (globalCompactNormalForm P r c j) := by
    apply hasUpperUnipotentInfinityResidue_of_projective_mk_eq
      P r hupperUnit
    exact hglobal
  exact compactNormalForm_hasIdentityDiagonal_of_upperResidue
    P r c j hupperNormal

/-- The constructed Cartwright--Steger lattice has trivial stabilizer of
the standard building vertex. -/
theorem buildingCartwrightStegerLattice_stabilizer_trivial
    (P : BasePrime) (r : Rank)
    (g : BuildingCartwrightStegerLattice P r)
    (hg : (g : Matrix.ProjGenLinGroup (Fin r.matrixRank)
        (BuildingLocalField P)) ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank) :
    g = 1 := by
  obtain ⟨u, hu, hmap⟩ :=
    exists_orderUnitLattice_lift_of_buildingLattice P r g
  have huCompact : orderUnitToBuildingPGL P r u ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank := by
    rw [hmap]
    exact hg
  have huCyclic : orderUnitToBuildingPGL P r u ∈
      BuildingCompactCyclicSubgroup P r :=
    orderUnitToBuildingPGL_mem_compactCyclicSubgroup_of_mem_maximalCompact
      P r u huCompact
  have huDiag : BuildingElementHasIdentityConjugationDiagonal P r
      (orderUnitToBuildingPGL P r u) :=
    orderUnitLattice_hasIdentityConjugationDiagonal
      P r u hu huCompact
  have huOne : orderUnitToBuildingPGL P r u = 1 :=
    eq_one_of_mem_compactCyclicSubgroup_of_identityConjugationDiagonal
      P r (orderUnitToBuildingPGL P r u) huCyclic huDiag
  apply Subtype.ext
  rw [← hmap]
  exact huOne

/-- The lattice orbit map on building vertices is injective. -/
theorem buildingLatticeVertexMap_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (buildingLatticeVertexMap P r) := by
  rw [buildingLatticeVertexMap_injective_iff]
  exact buildingCartwrightStegerLattice_stabilizer_trivial P r

/-- The Cartwright--Steger lattice acts simply transitively on the vertices
of the rank-three or rank-four affine building. -/
theorem buildingLatticeVertexMap_bijective
    (P : BasePrime) (r : Rank) :
    Function.Bijective (buildingLatticeVertexMap P r) :=
  ⟨buildingLatticeVertexMap_injective P r,
    buildingLatticeVertexMap_surjective P r⟩

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
