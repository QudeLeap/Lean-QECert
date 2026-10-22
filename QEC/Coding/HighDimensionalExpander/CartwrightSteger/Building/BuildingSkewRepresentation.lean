import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Building.BuildingCompactNormalForm
import Mathlib.Algebra.SkewMonoidAlgebra.Lift

/-!
# Building-place representation of the integral Cartwright--Steger order

The integral skew Laurent ring is represented at the building place by
regular constant matrices and integer powers of the local cyclic generator.
The Frobenius-twisted multiplication law is proved for every integer exponent.
The resulting projective unit image is exactly the previously constructed
compact cyclic subgroup.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem constantFrobeniusUnitEquiv_zpow_coe
    (P : BasePrime) (r : Rank) (n : ℤ)
    (u : (ConstantExtension P r)ˣ) :
    (((constantFrobeniusUnitEquiv P r ^ n) u :
        (ConstantExtension P r)ˣ) : ConstantExtension P r) =
      Multiplicative.ofAdd n • (u : ConstantExtension P r) := by
  change _ = constantFrobeniusZRingAction P r (Multiplicative.ofAdd n) u
  rw [constantFrobeniusZRingAction, zpowersHom_apply]
  induction n using Int.induction_on generalizing u with
  | zero => simp
  | succ n ih =>
      change _ = ((constantFrobenius P r).toRingEquiv ^ ((n : ℤ) + 1)) u
      rw [zpow_add_one, MulAut.mul_apply, zpow_add_one, RingAut.mul_apply]
      rw [ih, constantFrobeniusUnitEquiv_coe]
      simp
  | pred n ih =>
      change _ = ((constantFrobenius P r).toRingEquiv ^ (-(n : ℤ) - 1)) u
      rw [zpow_sub_one, MulAut.mul_apply, zpow_sub_one, RingAut.mul_apply]
      rw [ih]
      rfl

theorem buildingCyclicGeneratorGL_zpow_conj_constant
    (P : BasePrime) (r : Rank) (n : ℤ)
    (u : (ConstantExtension P r)ˣ) :
    buildingCyclicGeneratorGL P r ^ n * buildingConstantGL P r u *
        (buildingCyclicGeneratorGL P r ^ n)⁻¹ =
      buildingConstantGL P r
        ((constantFrobeniusUnitEquiv P r ^ n) u) := by
  induction n using Int.induction_on generalizing u with
  | zero => simp
  | succ n ih =>
      calc
        buildingCyclicGeneratorGL P r ^ ((n : ℤ) + 1) *
              buildingConstantGL P r u *
              (buildingCyclicGeneratorGL P r ^ ((n : ℤ) + 1))⁻¹ =
            buildingCyclicGeneratorGL P r ^ (n : ℤ) *
              (buildingCyclicGeneratorGL P r *
                buildingConstantGL P r u *
                (buildingCyclicGeneratorGL P r)⁻¹) *
              (buildingCyclicGeneratorGL P r ^ (n : ℤ))⁻¹ := by
                rw [zpow_add_one]
                group
        _ = buildingCyclicGeneratorGL P r ^ (n : ℤ) *
              buildingConstantGL P r
                (constantFrobeniusUnitEquiv P r u) *
              (buildingCyclicGeneratorGL P r ^ (n : ℤ))⁻¹ := by
                rw [buildingCyclicGeneratorGL_conj_constant]
        _ = buildingConstantGL P r
              ((constantFrobeniusUnitEquiv P r ^ (n : ℤ))
                (constantFrobeniusUnitEquiv P r u)) :=
              ih (constantFrobeniusUnitEquiv P r u)
        _ = buildingConstantGL P r
              ((constantFrobeniusUnitEquiv P r ^ ((n : ℤ) + 1)) u) := by
                rw [zpow_add_one, MulAut.mul_apply]
  | pred n ih =>
      have hinverse (v : (ConstantExtension P r)ˣ) :
          (buildingCyclicGeneratorGL P r)⁻¹ *
              buildingConstantGL P r v *
              buildingCyclicGeneratorGL P r =
            buildingConstantGL P r
              ((constantFrobeniusUnitEquiv P r)⁻¹ v) := by
        have hforward := buildingCyclicGeneratorGL_conj_constant P r
          ((constantFrobeniusUnitEquiv P r)⁻¹ v)
        have hforward' :
            buildingCyclicGeneratorGL P r *
                buildingConstantGL P r
                  ((constantFrobeniusUnitEquiv P r)⁻¹ v) *
                (buildingCyclicGeneratorGL P r)⁻¹ =
              buildingConstantGL P r v := by
          simpa using hforward
        calc
          (buildingCyclicGeneratorGL P r)⁻¹ *
                buildingConstantGL P r v *
                buildingCyclicGeneratorGL P r =
              (buildingCyclicGeneratorGL P r)⁻¹ *
                (buildingCyclicGeneratorGL P r *
                  buildingConstantGL P r
                    ((constantFrobeniusUnitEquiv P r)⁻¹ v) *
                  (buildingCyclicGeneratorGL P r)⁻¹) *
                buildingCyclicGeneratorGL P r := by rw [hforward']
          _ = buildingConstantGL P r
                ((constantFrobeniusUnitEquiv P r)⁻¹ v) := by group
      change buildingCyclicGeneratorGL P r ^ (-(n : ℤ) - 1) *
            buildingConstantGL P r u *
            (buildingCyclicGeneratorGL P r ^ (-(n : ℤ) - 1))⁻¹ =
        buildingConstantGL P r
          ((constantFrobeniusUnitEquiv P r ^ (-(n : ℤ) - 1)) u)
      calc
        buildingCyclicGeneratorGL P r ^ (-(n : ℤ) - 1) *
              buildingConstantGL P r u *
              (buildingCyclicGeneratorGL P r ^ (-(n : ℤ) - 1))⁻¹ =
            buildingCyclicGeneratorGL P r ^ (-(n : ℤ)) *
              ((buildingCyclicGeneratorGL P r)⁻¹ *
                buildingConstantGL P r u *
                buildingCyclicGeneratorGL P r) *
              (buildingCyclicGeneratorGL P r ^ (-(n : ℤ)))⁻¹ := by
                rw [zpow_sub_one]
                group
        _ = buildingCyclicGeneratorGL P r ^ (-(n : ℤ)) *
              buildingConstantGL P r
                ((constantFrobeniusUnitEquiv P r)⁻¹ u) *
              (buildingCyclicGeneratorGL P r ^ (-(n : ℤ)))⁻¹ := by
                rw [hinverse]
        _ = buildingConstantGL P r
              ((constantFrobeniusUnitEquiv P r ^ (-(n : ℤ)))
                ((constantFrobeniusUnitEquiv P r)⁻¹ u)) :=
              ih ((constantFrobeniusUnitEquiv P r)⁻¹ u)
        _ = buildingConstantGL P r
              ((constantFrobeniusUnitEquiv P r ^ (-(n : ℤ) - 1)) u) := by
                rw [zpow_sub_one, MulAut.mul_apply]

noncomputable def buildingConstantMatrixEmbedding
    (P : BasePrime) (r : Rank) :
    ConstantExtension P r →+*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) where
  toFun := buildingConstantMatrix P r
  map_zero' := by simp [buildingConstantMatrix]
  map_one' := by simp [buildingConstantMatrix]
  map_add' c d := by
    ext i j
    simp [buildingConstantMatrix]
  map_mul' c d := by
    rw [buildingConstantMatrix, buildingConstantMatrix, buildingConstantMatrix,
      ← Matrix.map_mul, map_mul]

@[simp] theorem buildingConstantMatrixEmbedding_apply
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    buildingConstantMatrixEmbedding P r c =
      buildingConstantMatrix P r c := rfl

noncomputable def buildingCyclicZGLHom
    (P : BasePrime) (r : Rank) :
    Multiplicative ℤ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  zpowersHom _ (buildingCyclicGeneratorGL P r)

noncomputable def buildingCyclicZMatrixHom
    (P : BasePrime) (r : Rank) :
    Multiplicative ℤ →*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) :=
  (Units.coeHom _).comp (buildingCyclicZGLHom P r)

@[simp] theorem buildingCyclicZMatrixHom_apply
    (P : BasePrime) (r : Rank) (n : Multiplicative ℤ) :
    buildingCyclicZMatrixHom P r n =
      ((buildingCyclicGeneratorGL P r) ^ n.toAdd :
        Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :=
  rfl

theorem buildingCyclic_zpow_conj_constant
    (P : BasePrime) (r : Rank) (n : ℤ)
    (c : ConstantExtension P r) :
    ((buildingCyclicGeneratorGL P r ^ n :
        Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)) *
        buildingConstantMatrix P r c *
        (((buildingCyclicGeneratorGL P r ^ n)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)) =
      buildingConstantMatrix P r (Multiplicative.ofAdd n • c) := by
  by_cases hc : c = 0
  · simp [hc, buildingConstantMatrix]
  · let u : (ConstantExtension P r)ˣ := Units.mk0 c hc
    have h := buildingCyclicGeneratorGL_zpow_conj_constant P r n u
    have hval := congrArg Units.val h
    rw [Units.val_mul, Units.val_mul, buildingConstantGL_coe,
      buildingConstantGL_coe] at hval
    have hcoe : (((constantFrobeniusUnitEquiv P r ^ n) u :
          (ConstantExtension P r)ˣ) : ConstantExtension P r) =
        Multiplicative.ofAdd n • (u : ConstantExtension P r) :=
      constantFrobeniusUnitEquiv_zpow_coe P r n u
    calc
      _ = buildingConstantMatrix P r
          (((constantFrobeniusUnitEquiv P r ^ n) u :
            (ConstantExtension P r)ˣ) : ConstantExtension P r) := by
              simpa [u] using hval
      _ = _ := congrArg (buildingConstantMatrix P r) hcoe

theorem buildingSkewLaurent_compatibility
    (P : BasePrime) (r : Rank)
    {c : ConstantExtension P r} {n : Multiplicative ℤ} :
    buildingConstantMatrixEmbedding P r (n • c) *
        buildingCyclicZMatrixHom P r n =
      buildingCyclicZMatrixHom P r n *
        buildingConstantMatrixEmbedding P r c := by
  have hconj := buildingCyclic_zpow_conj_constant P r n.toAdd c
  rw [buildingCyclicZMatrixHom_apply,
    buildingConstantMatrixEmbedding_apply,
    buildingConstantMatrixEmbedding_apply]
  have haction : n • c = Multiplicative.ofAdd n.toAdd • c := by
    congr 1
  rw [haction]
  calc
    buildingConstantMatrix P r (Multiplicative.ofAdd n.toAdd • c) *
        ((buildingCyclicGeneratorGL P r ^ n.toAdd :
          Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
          Matrix _ _ _) =
      (((buildingCyclicGeneratorGL P r ^ n.toAdd :
          Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
          Matrix _ _ _) * buildingConstantMatrix P r c *
        (((buildingCyclicGeneratorGL P r ^ n.toAdd)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
          Matrix _ _ _)) *
        ((buildingCyclicGeneratorGL P r ^ n.toAdd :
          Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
          Matrix _ _ _) := by rw [hconj]
    _ = ((buildingCyclicGeneratorGL P r ^ n.toAdd :
          Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
          Matrix _ _ _) * buildingConstantMatrix P r c := by
      simp only [mul_assoc]
      rw [← Units.val_mul]
      simp

noncomputable def skewLaurentToBuildingMatrix
    (P : BasePrime) (r : Rank) :
    CartwrightStegerSkewLaurentRing P r →+*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) :=
  SkewMonoidAlgebra.liftNCRingHom
    (buildingConstantMatrixEmbedding P r)
    (buildingCyclicZMatrixHom P r)
    (fun {_ _} => buildingSkewLaurent_compatibility P r)

@[simp] theorem skewLaurentToBuildingMatrix_single
    (P : BasePrime) (r : Rank) (n : Multiplicative ℤ)
    (c : ConstantExtension P r) :
    skewLaurentToBuildingMatrix P r
        (SkewMonoidAlgebra.single n c) =
      buildingConstantMatrix P r c * buildingCyclicZMatrixHom P r n := by
  simp [skewLaurentToBuildingMatrix,
    SkewMonoidAlgebra.liftNCRingHom,
    SkewMonoidAlgebra.liftNC_single]

noncomputable def buildingIntegralUnitGLHom
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerSkewLaurentRing P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Units.map (skewLaurentToBuildingMatrix P r).toMonoidHom

noncomputable def buildingIntegralUnitPGLHom
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerSkewLaurentRing P r)ˣ →*
      Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Matrix.ProjGenLinGroup.mk.comp (buildingIntegralUnitGLHom P r)

@[simp] theorem buildingIntegralUnitPGLHom_monomial
    (P : BasePrime) (r : Rank)
    (c : (ConstantExtension P r)ˣ) (n : ℤ) :
    buildingIntegralUnitPGLHom P r
        (skewLaurentMonomialUnit P r c n) =
      buildingConstantPGLHom P r c *
        buildingCyclicGeneratorPGL P r ^ n := by
  apply congrArg (Matrix.ProjGenLinGroup.mk :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) →
      Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))
  apply Units.ext
  change skewLaurentToBuildingMatrix P r
      (SkewMonoidAlgebra.single (Multiplicative.ofAdd n)
        (c : ConstantExtension P r)) = _
  rw [skewLaurentToBuildingMatrix_single]
  rfl

theorem range_buildingIntegralUnitPGLHom
    (P : BasePrime) (r : Rank) :
    (buildingIntegralUnitPGLHom P r).range =
      BuildingCompactCyclicSubgroup P r := by
  apply le_antisymm
  · rintro g ⟨u, rfl⟩
    obtain ⟨c, n, hu⟩ := exists_constant_zpow_of_skewLaurent_unit P r u
    have hmatrix := congrArg (skewLaurentToBuildingMatrix P r) hu
    rw [skewLaurentToBuildingMatrix_single] at hmatrix
    have hGL : buildingIntegralUnitGLHom P r u =
        buildingConstantGLHom P r c *
          buildingCyclicGeneratorGL P r ^ n := by
      apply Units.ext
      exact hmatrix
    change Matrix.ProjGenLinGroup.mk (buildingIntegralUnitGLHom P r u) ∈ _
    rw [hGL, map_mul]
    exact (BuildingCompactCyclicSubgroup P r).mul_mem
      (buildingConstantPGL_mem_compactCyclicSubgroup P r c)
      ((BuildingCompactCyclicSubgroup P r).zpow_mem
        (buildingCyclicGeneratorPGL_mem_compactCyclicSubgroup P r) n)
  · rw [BuildingCompactCyclicSubgroup]
    apply (Subgroup.closure_le _).mpr
    rintro g (hg | hg)
    · obtain ⟨c, rfl⟩ := hg
      refine ⟨skewLaurentMonomialUnit P r c 0, ?_⟩
      simp
    · rw [Set.mem_singleton_iff] at hg
      subst g
      refine ⟨skewLaurentMonomialUnit P r 1 1, ?_⟩
      rw [buildingIntegralUnitPGLHom_monomial, map_one, one_mul,
        zpow_one]

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
