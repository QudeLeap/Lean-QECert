import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Order.LatticeBridge
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Integral.RepresentationKernel
import QEC.Coding.HighDimensionalExpander.Combinatorics.LocalLinkReduction

/-!
# The projective stabilizer normalization step

Projective maximal compactness forces the determinant order of an arithmetic
order unit to be divisible by the matrix rank.  This is the scalar exponent
needed to choose an honest integral representative.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped MatrixGroups

/-- The central scalar `y` as an actual unit of the arithmetic order. -/
noncomputable def cartwrightStegerOrderYUnit
    (P : BasePrime) (r : Rank) : (CartwrightStegerOrder P r)ˣ where
  val := ⟨Matrix.scalar (Fin r.matrixRank) (splittingY P r), by
    have hy : algebraMap (ArithmeticRing P)
        (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r))
        (algebraMap (PolynomialRing P) (ArithmeticRing P) Polynomial.X) =
        Matrix.scalar (Fin r.matrixRank) (splittingY P r) := by
      change arithmeticRingToSplitMatrix P r
          (algebraMap (PolynomialRing P) (ArithmeticRing P) Polynomial.X) = _
      simp [arithmeticRingToSplitMatrix,
        arithmeticRingToSplittingFunctionField,
        arithmeticRingToFunctionField_algebraMap,
        functionFieldEmbedding_X, RatFunc.algebraMap_X, splittingY]
    rw [← hy]
    exact (CartwrightStegerOrder P r).algebraMap_mem _⟩
  inv := ⟨Matrix.scalar (Fin r.matrixRank) (splittingY P r)⁻¹, by
    rw [← algebraMap_arithmeticYInv P r]
    exact (CartwrightStegerOrder P r).algebraMap_mem _⟩
  val_inv := by
    apply Subtype.ext
    ext i j
    simp [Matrix.scalar_apply, splittingY_ne_zero P r]
  inv_val := by
    apply Subtype.ext
    ext i j
    simp [Matrix.scalar_apply, splittingY_ne_zero P r]

noncomputable def buildingLocalYUnit
    (P : BasePrime) : (BuildingLocalField P)ˣ :=
  Units.mk0 (buildingLocalY P) (buildingLocalY_ne_zero P)

theorem cyclicUnitToBuildingGL_orderYUnit
    (P : BasePrime) (r : Rank) :
    cyclicUnitToBuildingGL P r
        (orderUnitToCyclicUnit P r (cartwrightStegerOrderYUnit P r)) =
      Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
        (buildingLocalYUnit P) := by
  apply Units.ext
  change cyclicAlgebraToBuilding P r
      ((orderUnitToCyclicUnit P r (cartwrightStegerOrderYUnit P r) :
        (CyclicAlgebra P r)ˣ) : CyclicAlgebra P r) =
    Matrix.scalar (Fin r.matrixRank) (buildingLocalY P)
  have hsource : ((orderUnitToCyclicUnit P r
        (cartwrightStegerOrderYUnit P r) : (CyclicAlgebra P r)ˣ) :
      CyclicAlgebra P r) =
      algebraMap (FunctionField P) (CyclicAlgebra P r) RatFunc.X := by
    apply Subtype.ext
    change Matrix.scalar (Fin r.matrixRank) (splittingY P r) =
      Matrix.scalar (Fin r.matrixRank)
        (functionFieldEmbedding P r RatFunc.X)
    rw [functionFieldEmbedding_X, splittingY]
  rw [hsource]
  calc
    _ = algebraMap (FunctionField P)
        (Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P))
        RatFunc.X := (cyclicAlgebraToBuilding P r).commutes RatFunc.X
    _ = Matrix.scalar (Fin r.matrixRank)
        (functionFieldToBuildingLocalField P RatFunc.X) := rfl
    _ = _ := congrArg (Matrix.scalar (Fin r.matrixRank))
      (functionFieldToBuildingLocalField_X P)

theorem localUnitOrder_buildingLocalYUnit
    (P : BasePrime) :
    SphericalHecke.localUnitOrder (buildingLocalYUnit P) = 1 := by
  have hunit : buildingLocalYUnit P =
      SphericalHecke.uniformizerUnit (BaseField P) := by
    apply Units.ext
    simp [buildingLocalYUnit, buildingLocalY,
      SphericalHecke.coe_uniformizerUnit]
  rw [hunit]
  simpa using
    (SphericalHecke.localUnitOrder_uniformizerUnit_pow
      (k := BaseField P) 1)

/-- Multiply an order unit by the construction-owned central power which
removes a prescribed determinant-order quotient. -/
noncomputable def normalizedOrderUnit
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ) (q : ℤ) :
    (CartwrightStegerOrder P r)ˣ :=
  cartwrightStegerOrderYUnit P r ^ (-q) * u

theorem cyclicUnitToBuildingGL_normalizedOrderUnit
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ) (q : ℤ) :
    cyclicUnitToBuildingGL P r
        (orderUnitToCyclicUnit P r (normalizedOrderUnit P r u q)) =
      (Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
          (buildingLocalYUnit P)) ^ (-q) *
        cyclicUnitToBuildingGL P r (orderUnitToCyclicUnit P r u) := by
  rw [normalizedOrderUnit, map_mul, map_zpow,
    map_mul, map_zpow, cyclicUnitToBuildingGL_orderYUnit]

theorem orderUnitToBuildingPGL_normalizedOrderUnit
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ) (q : ℤ) :
    orderUnitToBuildingPGL P r (normalizedOrderUnit P r u q) =
      orderUnitToBuildingPGL P r u := by
  rw [normalizedOrderUnit, map_mul, map_zpow]
  have hy : orderUnitToBuildingPGL P r (cartwrightStegerOrderYUnit P r) = 1 := by
    change Matrix.ProjGenLinGroup.mk
        (cyclicUnitToBuildingGL P r
          (orderUnitToCyclicUnit P r (cartwrightStegerOrderYUnit P r))) = 1
    rw [cyclicUnitToBuildingGL_orderYUnit]
    exact Matrix.ProjGenLinGroup.mk_scalar _
  rw [hy]
  simp

theorem localUnitOrder_zpow
    (P : BasePrime) (a : (BuildingLocalField P)ˣ) (n : ℤ) :
    SphericalHecke.localUnitOrder (a ^ n) =
      n * SphericalHecke.localUnitOrder a := by
  induction n using Int.induction_on with
  | zero => simp [SphericalHecke.localUnitOrder]
  | succ n ih =>
      rw [zpow_add_one, SphericalHecke.localUnitOrder_mul, ih]
      ring
  | pred n ih =>
      rw [zpow_sub_one, SphericalHecke.localUnitOrder_mul, ih,
        SphericalHecke.localUnitOrder_inv]
      ring

theorem localDetOrder_normalizedOrderUnit_eq_zero
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ) (q : ℤ)
    (hq : SphericalHecke.localUnitOrder
        (Matrix.GeneralLinearGroup.det
          (cyclicUnitToBuildingGL P r (orderUnitToCyclicUnit P r u))) =
      (r.matrixRank : ℤ) * q) :
    SphericalHecke.localUnitOrder
        (Matrix.GeneralLinearGroup.det
          (cyclicUnitToBuildingGL P r
            (orderUnitToCyclicUnit P r
              (normalizedOrderUnit P r u q)))) = 0 := by
  rw [cyclicUnitToBuildingGL_normalizedOrderUnit]
  rw [map_mul, map_zpow, SphericalHecke.localUnitOrder_mul,
    localUnitOrder_zpow, hq]
  have hdetY : SphericalHecke.localUnitOrder
      (Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
          (buildingLocalYUnit P))) = (r.matrixRank : ℤ) := by
    simp [Matrix.GeneralLinearGroup.det_scalar,
      SphericalHecke.localUnitOrder_pow,
      localUnitOrder_buildingLocalYUnit]
  rw [hdetY]
  ring

theorem normalizedOrderUnit_mem_integralGeneralLinearSet
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ) (q : ℤ)
    (hcompact : orderUnitToBuildingPGL P r u ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank)
    (hq : SphericalHecke.localUnitOrder
        (Matrix.GeneralLinearGroup.det
          (cyclicUnitToBuildingGL P r (orderUnitToCyclicUnit P r u))) =
      (r.matrixRank : ℤ) * q) :
    cyclicUnitToBuildingGL P r
        (orderUnitToCyclicUnit P r (normalizedOrderUnit P r u q)) ∈
      SphericalHecke.integralGeneralLinearSet
        (BaseField P) r.matrixRank := by
  let A := cyclicUnitToBuildingGL P r
    (orderUnitToCyclicUnit P r (normalizedOrderUnit P r u q))
  have hdet : SphericalHecke.localUnitOrder
      (Matrix.GeneralLinearGroup.det A) = 0 :=
    localDetOrder_normalizedOrderUnit_eq_zero P r u q hq
  apply (SphericalHecke.projective_mk_mem_maximalCompact_iff_integral
    (BaseField P) r.matrixRank
    (lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)) A hdet).mp
  change orderUnitToBuildingPGL P r
      (normalizedOrderUnit P r u q) ∈
    SphericalHecke.maximalCompact (BaseField P) r.matrixRank
  rw [orderUnitToBuildingPGL_normalizedOrderUnit]
  exact hcompact

/-- The normalized unit and its inverse have honest matrices over the
building integer ring, in the exact form required by coordinate
reconstruction. -/
theorem normalizedOrderUnit_buildingIntegral_witnesses
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ) (q : ℤ)
    (hcompact : orderUnitToBuildingPGL P r u ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank)
    (hq : SphericalHecke.localUnitOrder
        (Matrix.GeneralLinearGroup.det
          (cyclicUnitToBuildingGL P r (orderUnitToCyclicUnit P r u))) =
      (r.matrixRank : ℤ) * q) :
    (∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r
          (cartwrightStegerOrderToCyclicAlgebra P r
            (normalizedOrderUnit P r u q : CartwrightStegerOrder P r))) ∧
    (∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r
          (cartwrightStegerOrderToCyclicAlgebra P r
            (((normalizedOrderUnit P r u q)⁻¹ :
              (CartwrightStegerOrder P r)ˣ) :
                CartwrightStegerOrder P r))) := by
  let A := cyclicUnitToBuildingGL P r
    (orderUnitToCyclicUnit P r (normalizedOrderUnit P r u q))
  have hA : A ∈ SphericalHecke.integralGeneralLinearSet
      (BaseField P) r.matrixRank :=
    normalizedOrderUnit_mem_integralGeneralLinearSet
      P r u q hcompact hq
  rw [← SphericalHecke.range_integralGeneralLinearToLocal] at hA
  obtain ⟨D, hD⟩ := hA
  let C := SphericalHecke.integerGeneralLinearToPowerSeries
    (BaseField P) r.matrixRank D
  have hC : SphericalHecke.powerSeriesGeneralLinearToLocal
      (BaseField P) r.matrixRank C = A := by
    rw [← SphericalHecke.powerSeries_integer_local_triangle]
    rw [SphericalHecke.powerSeriesGeneralLinearToInteger_inverse]
    exact hD
  have hCval := congrArg Units.val hC
  have hCinv : SphericalHecke.powerSeriesGeneralLinearToLocal
      (BaseField P) r.matrixRank C⁻¹ = A⁻¹ := by
    rw [map_inv, hC]
  have hCinvVal := congrArg Units.val hCinv
  constructor
  · refine ⟨(C : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P)), ?_⟩
    calc
      _ = (SphericalHecke.powerSeriesGeneralLinearToLocal
          (BaseField P) r.matrixRank C :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (BuildingLocalField P)) :=
        (SphericalHecke.coe_powerSeriesGeneralLinearToLocal C).symm
      _ = (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) := hCval
      _ = _ := rfl
  · refine ⟨((C⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (BuildingIntegerRing P)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingIntegerRing P)), ?_⟩
    calc
      _ = (SphericalHecke.powerSeriesGeneralLinearToLocal
          (BaseField P) r.matrixRank C⁻¹ :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (BuildingLocalField P)) :=
        (SphericalHecke.coe_powerSeriesGeneralLinearToLocal C⁻¹).symm
      _ = ((A⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (BuildingLocalField P)) :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (BuildingLocalField P)) := hCinvVal
      _ = _ := by
        have hinv : cyclicUnitToBuildingGL P r
            (orderUnitToCyclicUnit P r
              ((normalizedOrderUnit P r u q)⁻¹)) = A⁻¹ := by
          rw [map_inv, map_inv]
        exact (congrArg Units.val hinv).symm
/-- A projectively integral order unit has determinant order divisible by the
matrix rank.  The divisor is extracted from the actual projective scalar
relating it to an integral general-linear representative. -/
theorem exists_localDetOrder_quotient_of_orderUnit_mem_maximalCompact
    (P : BasePrime) (r : Rank) (u : (CartwrightStegerOrder P r)ˣ)
    (hcompact : orderUnitToBuildingPGL P r u ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank) :
    ∃ q : ℤ,
      SphericalHecke.localUnitOrder
          (Matrix.GeneralLinearGroup.det
            (cyclicUnitToBuildingGL P r (orderUnitToCyclicUnit P r u))) =
        (r.matrixRank : ℤ) * q := by
  let A := cyclicUnitToBuildingGL P r (orderUnitToCyclicUnit P r u)
  change Matrix.ProjGenLinGroup.mk A ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank at hcompact
  obtain ⟨B, hB⟩ :=
    (SphericalHecke.mem_maximalCompact_iff
      (BaseField P) r.matrixRank _).mp hcompact
  change Matrix.ProjGenLinGroup.mk
      (SphericalHecke.integralGeneralLinearToLocal
        (BaseField P) r.matrixRank B) =
    Matrix.ProjGenLinGroup.mk A at hB
  obtain ⟨c, hc⟩ :=
    SphericalHecke.exists_scalar_mul_eq_of_projective_mk_eq hB.symm
  refine ⟨SphericalHecke.localUnitOrder c, ?_⟩
  change SphericalHecke.localUnitOrder
      (Matrix.GeneralLinearGroup.det A) = _
  rw [hc]
  simp [Matrix.GeneralLinearGroup.det_scalar,
    SphericalHecke.localUnitOrder_mul,
    SphericalHecke.localUnitOrder_pow,
    SphericalHecke.integralGeneralLinear_det_localUnitOrder_eq_zero]

/-- Every projectively compact arithmetic-order unit has image in the
explicit compact cyclic subgroup.  The proof constructs its normalized unit,
both integral matrices, and the corresponding skew Laurent unit. -/
theorem orderUnitToBuildingPGL_mem_compactCyclicSubgroup_of_mem_maximalCompact
    (P : BasePrime) (r : Rank) (u : (CartwrightStegerOrder P r)ˣ)
    (hcompact : orderUnitToBuildingPGL P r u ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank) :
    orderUnitToBuildingPGL P r u ∈
      BuildingCompactCyclicSubgroup P r := by
  obtain ⟨q, hq⟩ :=
    exists_localDetOrder_quotient_of_orderUnit_mem_maximalCompact
      P r u hcompact
  obtain ⟨hlocal, hlocalInv⟩ :=
    normalizedOrderUnit_buildingIntegral_witnesses
      P r u q hcompact hq
  have hmem := cyclicOrderUnitToBuildingPGL_mem_compactCyclicSubgroup
    P r (normalizedOrderUnit P r u q) hlocal hlocalInv
  change orderUnitToBuildingPGL P r (normalizedOrderUnit P r u q) ∈
    BuildingCompactCyclicSubgroup P r at hmem
  rw [orderUnitToBuildingPGL_normalizedOrderUnit] at hmem
  exact hmem

/-- Equality in the building projective representation transfers to equality
in the global projective representation because the two explicitly
constructed representations have the same proved kernel. -/
theorem globalIntegralUnitPGLHom_eq_of_buildingIntegralUnitPGLHom_eq
    (P : BasePrime) (r : Rank)
    {v w : (CartwrightStegerSkewLaurentRing P r)ˣ}
    (h : buildingIntegralUnitPGLHom P r v =
      buildingIntegralUnitPGLHom P r w) :
    globalIntegralUnitPGLHom P r v =
      globalIntegralUnitPGLHom P r w := by
  have hk : v * w⁻¹ ∈ (buildingIntegralUnitPGLHom P r).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h]
    simp
  have hkGlobal : v * w⁻¹ ∈ (globalIntegralUnitPGLHom P r).ker := by
    rw [integralProjectiveRepresentation_ker_eq P r]
    exact hk
  rw [MonoidHom.mem_ker, map_mul, map_inv] at hkGlobal
  exact mul_inv_eq_one.mp hkGlobal

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
