import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Building.BuildingCyclicCoordinates

/-!
# Arithmetic cyclic coordinates of the Cartwright--Steger order

The order generated over `F_q[y,1/y,1/(1+y)]` by the constant field and
`z^{±1}` is contained in the span of the explicit cyclic basis over that
same arithmetic ring.  Multiplicative closure is checked using the actual
Frobenius twist and the carry `z^d = 1+y`.  Consequently every cyclic
coordinate of an order element comes from the arithmetic ring.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

noncomputable instance arithmeticRingFunctionFieldAlgebra
    (P : BasePrime) : Algebra (ArithmeticRing P) (FunctionField P) :=
  (arithmeticRingToFunctionField P).toAlgebra

noncomputable instance arithmeticRingCyclicAlgebra
    (P : BasePrime) (r : Rank) :
    Algebra (ArithmeticRing P) (CyclicAlgebra P r) where
  smul a x := (arithmeticRingToFunctionField P a) • x
  algebraMap := (algebraMap (FunctionField P) (CyclicAlgebra P r)).comp
    (arithmeticRingToFunctionField P)
  commutes' a x := Algebra.commutes
    (arithmeticRingToFunctionField P a) x
  smul_def' a x := by
    change (arithmeticRingToFunctionField P a) • x =
      algebraMap (FunctionField P) (CyclicAlgebra P r)
        (arithmeticRingToFunctionField P a) * x
    rw [Algebra.smul_def]

noncomputable instance arithmeticFunctionFieldCyclicTower
    (P : BasePrime) (r : Rank) :
    IsScalarTower (ArithmeticRing P) (FunctionField P) (CyclicAlgebra P r) :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable def arithmeticCyclicSpan
    (P : BasePrime) (r : Rank) :
    Submodule (ArithmeticRing P) (CyclicAlgebra P r) :=
  Submodule.span (ArithmeticRing P)
    (Set.range (functionFieldCyclicBasisVector P r))

theorem constantCyclicMonomial_mem_arithmeticCyclicSpan
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r)
    (k : ℕ) (hk : k < r.matrixRank) :
    (⟨constantMatrix P r c * cyclicGeneratorMatrix P r ^ k,
      (CyclicAlgebra P r).mul_mem
        (constantMatrix_mem_cyclicAlgebra P r c)
        ((CyclicAlgebra P r).pow_mem
          (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) k)⟩ :
      CyclicAlgebra P r) ∈ arithmeticCyclicSpan P r := by
  let kf : Fin r.matrixRank := ⟨k, hk⟩
  have hc : (⟨constantMatrix P r c * cyclicGeneratorMatrix P r ^ k,
      (CyclicAlgebra P r).mul_mem
        (constantMatrix_mem_cyclicAlgebra P r c)
        ((CyclicAlgebra P r).pow_mem
          (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) k)⟩ :
      CyclicAlgebra P r) =
      ∑ j, algebraMap (BaseField P) (ArithmeticRing P)
          ((constantBasis P r).repr c j) •
            functionFieldCyclicBasisVector P r (j, kf) := by
    calc
      _ = ∑ j, algebraMap (BaseField P) (FunctionField P)
          ((constantBasis P r).repr c j) •
            functionFieldCyclicBasisVector P r (j, kf) :=
        constantCyclicMonomial_eq_sum_basis P r c k hk
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        have hcoeff : arithmeticRingToFunctionField P
            (algebraMap (BaseField P) (ArithmeticRing P)
              ((constantBasis P r).repr c j)) =
          algebraMap (BaseField P) (FunctionField P)
            ((constantBasis P r).repr c j) := by
          change arithmeticRingToFunctionField P
              (algebraMap (PolynomialRing P) (ArithmeticRing P)
                (Polynomial.C ((constantBasis P r).repr c j))) =
            RatFunc.C ((constantBasis P r).repr c j)
          rw [arithmeticRingToFunctionField_algebraMap]
          simp
        change (algebraMap (BaseField P) (FunctionField P)
            ((constantBasis P r).repr c j)) •
              (functionFieldCyclicBasisVector P r (j, kf) :
                CyclicAlgebra P r) =
          (arithmeticRingToFunctionField P
            (algebraMap (BaseField P) (ArithmeticRing P)
              ((constantBasis P r).repr c j))) •
                (functionFieldCyclicBasisVector P r (j, kf) :
                  CyclicAlgebra P r)
        rw [hcoeff]
  rw [hc]
  apply Submodule.sum_mem
  intro j _
  exact (arithmeticCyclicSpan P r).smul_mem _
    (Submodule.subset_span ⟨(j, kf), rfl⟩)

/-- The element `(1+y)` of the arithmetic coefficient ring. -/
noncomputable def arithmeticOnePlusY (P : BasePrime) : ArithmeticRing P :=
  algebraMap (PolynomialRing P) (ArithmeticRing P) (1 + Polynomial.X)

@[simp] theorem arithmeticRingToFunctionField_arithmeticOnePlusY
    (P : BasePrime) :
    arithmeticRingToFunctionField P (arithmeticOnePlusY P) =
      1 + RatFunc.X := by
  simp [arithmeticOnePlusY, arithmeticRingToFunctionField_algebraMap]

theorem basis_mul_mem_arithmeticCyclicSpan
    (P : BasePrime) (r : Rank)
    (p q : Fin r.matrixRank × Fin r.matrixRank) :
    functionFieldCyclicBasisVector P r p *
        functionFieldCyclicBasisVector P r q ∈
      arithmeticCyclicSpan P r := by
  let e : ConstantExtension P r :=
    constantBasis P r p.1 *
      (constantFrobenius P r ^ (p.2 : ℕ)) (constantBasis P r q.1)
  have hproduct :
      (functionFieldCyclicBasisVector P r p) *
          functionFieldCyclicBasisVector P r q =
        ⟨constantMatrix P r e *
            cyclicGeneratorMatrix P r ^ ((p.2 : ℕ) + (q.2 : ℕ)),
          (CyclicAlgebra P r).mul_mem
            (constantMatrix_mem_cyclicAlgebra P r e)
            ((CyclicAlgebra P r).pow_mem
              (cyclicGeneratorMatrix_mem_cyclicAlgebra P r)
              ((p.2 : ℕ) + (q.2 : ℕ)))⟩ := by
    apply Subtype.ext
    exact constantCyclicMonomial_mul_eq P r
      (constantBasis P r p.1) (constantBasis P r q.1)
      (p.2 : ℕ) (q.2 : ℕ)
  by_cases hsum : (p.2 : ℕ) + (q.2 : ℕ) < r.matrixRank
  · rw [hproduct]
    exact constantCyclicMonomial_mem_arithmeticCyclicSpan P r e _ hsum
  · let j := (p.2 : ℕ) + (q.2 : ℕ) - r.matrixRank
    have hj : j < r.matrixRank := by
      have hp := p.2.isLt
      have hq := q.2.isLt
      omega
    have hsumEq : (p.2 : ℕ) + (q.2 : ℕ) = r.matrixRank + j := by omega
    have hbase := constantCyclicMonomial_mem_arithmeticCyclicSpan P r e j hj
    have hcarry := (arithmeticCyclicSpan P r).smul_mem
      (arithmeticOnePlusY P) hbase
    have hscalarAction (z : CyclicAlgebra P r) :
        (arithmeticOnePlusY P) • z =
          (1 + RatFunc.X : FunctionField P) • z := by
      change (arithmeticRingToFunctionField P (arithmeticOnePlusY P)) • z = _
      rw [arithmeticRingToFunctionField_arithmeticOnePlusY]
    rw [hscalarAction] at hcarry
    rw [hproduct]
    let a : FunctionField P := 1 + RatFunc.X
    have hmatrix : constantMatrix P r e *
          cyclicGeneratorMatrix P r ^ ((p.2 : ℕ) + (q.2 : ℕ)) =
        a • (constantMatrix P r e * cyclicGeneratorMatrix P r ^ j) := by
      rw [hsumEq, cyclicGeneratorMatrix_pow_rank_add, Matrix.mul_smul]
      rw [onePlusY_eq_functionField_smul_one]
      simp only [a, Algebra.smul_def, map_add, map_one]
      congr 1
      rw [IsScalarTower.algebraMap_apply
        (FunctionField P) (SplittingFunctionField P r)
        (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r))]
      simp
    have heq :
        (⟨constantMatrix P r e *
            cyclicGeneratorMatrix P r ^ ((p.2 : ℕ) + (q.2 : ℕ)),
          (CyclicAlgebra P r).mul_mem
            (constantMatrix_mem_cyclicAlgebra P r e)
            ((CyclicAlgebra P r).pow_mem
              (cyclicGeneratorMatrix_mem_cyclicAlgebra P r)
              ((p.2 : ℕ) + (q.2 : ℕ)))⟩ : CyclicAlgebra P r) =
          a • ⟨constantMatrix P r e * cyclicGeneratorMatrix P r ^ j,
            (CyclicAlgebra P r).mul_mem
              (constantMatrix_mem_cyclicAlgebra P r e)
              ((CyclicAlgebra P r).pow_mem
                (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) j)⟩ := by
      apply Subtype.ext
      exact hmatrix
    rw [heq]
    exact hcarry

theorem arithmeticCyclicSpan_mul_mem
    (P : BasePrime) (r : Rank) (x y : CyclicAlgebra P r)
    (hx : x ∈ arithmeticCyclicSpan P r)
    (hy : y ∈ arithmeticCyclicSpan P r) :
    x * y ∈ arithmeticCyclicSpan P r := by
  let S := arithmeticCyclicSpan P r
  refine Submodule.span_induction
    (p := fun x _ => ∀ y, y ∈ S → x * y ∈ S)
    ?basisX ?zeroX ?addX ?smulX hx y hy
  · intro x hxRange
    obtain ⟨p, rfl⟩ := hxRange
    intro y hy
    refine Submodule.span_induction
      (p := fun y _ => functionFieldCyclicBasisVector P r p * y ∈ S)
      ?basisY ?zeroY ?addY ?smulY hy
    · intro z hzRange
      obtain ⟨q, rfl⟩ := hzRange
      exact basis_mul_mem_arithmeticCyclicSpan P r p q
    · simp [S]
    · intro a b _ _ ha hb
      simpa only [mul_add] using S.add_mem ha hb
    · intro a z _ hz
      simpa only [mul_smul_comm] using S.smul_mem a hz
  · intro y _
    simp [S]
  · intro a b _ _ ha hb y hy
    simpa only [add_mul] using S.add_mem (ha y hy) (hb y hy)
  · intro a z _ hz y hy
    simpa only [smul_mul_assoc] using S.smul_mem a (hz y hy)

theorem one_mem_arithmeticCyclicSpan (P : BasePrime) (r : Rank) :
    (1 : CyclicAlgebra P r) ∈ arithmeticCyclicSpan P r := by
  have h := constantCyclicMonomial_mem_arithmeticCyclicSpan P r 1 0
    (lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r))
  have heq : (1 : CyclicAlgebra P r) =
      ⟨constantMatrix P r 1 * cyclicGeneratorMatrix P r ^ 0,
        (CyclicAlgebra P r).mul_mem
          (constantMatrix_mem_cyclicAlgebra P r 1)
          ((CyclicAlgebra P r).pow_mem
            (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) 0)⟩ := by
    apply Subtype.ext
    simp only [pow_zero, mul_one]
    exact (map_one (constantMatrixEmbedding P r)).symm
  rw [heq]
  exact h

/-- The inverse of `(1+y)` constructed in the localization away from
`y(1+y)`. -/
noncomputable def arithmeticOnePlusYInv (P : BasePrime) : ArithmeticRing P :=
  algebraMap (PolynomialRing P) (ArithmeticRing P) Polynomial.X *
    IsLocalization.Away.invSelf
      (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P)

theorem arithmeticRingToFunctionField_invSelfProduct
    (P : BasePrime) :
    arithmeticRingToFunctionField P
        (IsLocalization.Away.invSelf
          (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P)) =
      (RatFunc.X * (1 + RatFunc.X))⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  have h := congrArg (arithmeticRingToFunctionField P)
    (IsLocalization.Away.mul_invSelf
      (S := ArithmeticRing P)
      (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P))
  simpa [map_mul, arithmeticRingToFunctionField_algebraMap] using h

@[simp] theorem arithmeticRingToFunctionField_arithmeticOnePlusYInv
    (P : BasePrime) :
    arithmeticRingToFunctionField P (arithmeticOnePlusYInv P) =
      (1 + RatFunc.X : FunctionField P)⁻¹ := by
  rw [arithmeticOnePlusYInv, map_mul,
    arithmeticRingToFunctionField_algebraMap,
    arithmeticRingToFunctionField_invSelfProduct]
  have hX : (RatFunc.X : FunctionField P) ≠ 0 := RatFunc.X_ne_zero
  have hOnePlus : (1 + RatFunc.X : FunctionField P) ≠ 0 := by
    have hpoly : (1 + Polynomial.X : PolynomialRing P) ≠ 0 := by
      intro h
      have := congrArg (Polynomial.eval (0 : BaseField P)) h
      simp at this
    simpa only [map_add, map_one, RatFunc.algebraMap_X] using
      (RatFunc.algebraMap_ne_zero hpoly)
  field_simp
  simp

theorem cyclicGenerator_mem_arithmeticCyclicSpan
    (P : BasePrime) (r : Rank) :
    (⟨cyclicGeneratorMatrix P r,
      cyclicGeneratorMatrix_mem_cyclicAlgebra P r⟩ : CyclicAlgebra P r) ∈
      arithmeticCyclicSpan P r := by
  have h := constantCyclicMonomial_mem_arithmeticCyclicSpan P r 1 1
    (lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r))
  have heq : (⟨cyclicGeneratorMatrix P r,
      cyclicGeneratorMatrix_mem_cyclicAlgebra P r⟩ : CyclicAlgebra P r) =
      ⟨constantMatrix P r 1 * cyclicGeneratorMatrix P r ^ 1,
        (CyclicAlgebra P r).mul_mem
          (constantMatrix_mem_cyclicAlgebra P r 1)
          ((CyclicAlgebra P r).pow_mem
            (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) 1)⟩ := by
    apply Subtype.ext
    simp only [pow_one]
    rw [show constantMatrix P r 1 = 1 by
      exact map_one (constantMatrixEmbedding P r)]
    simp
  rw [heq]
  exact h

theorem cyclicGeneratorInverse_mem_arithmeticCyclicSpan
    (P : BasePrime) (r : Rank) :
    (⟨cyclicGeneratorInverseMatrix P r,
      cyclicGeneratorInverseMatrix_mem_cyclicAlgebra P r⟩ : CyclicAlgebra P r) ∈
      arithmeticCyclicSpan P r := by
  have hrank : 0 < r.matrixRank :=
    lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)
  have hpred : r.matrixRank - 1 < r.matrixRank := by omega
  have hbase := constantCyclicMonomial_mem_arithmeticCyclicSpan P r 1
    (r.matrixRank - 1) hpred
  have hmem := (arithmeticCyclicSpan P r).smul_mem
    (arithmeticOnePlusYInv P) hbase
  have hscalarAction (z : CyclicAlgebra P r) :
      (arithmeticOnePlusYInv P) • z =
        ((1 + RatFunc.X : FunctionField P)⁻¹) • z := by
    change arithmeticRingToFunctionField P (arithmeticOnePlusYInv P) • z = _
    rw [arithmeticRingToFunctionField_arithmeticOnePlusYInv]
  rw [hscalarAction] at hmem
  convert hmem using 1
  apply Subtype.ext
  change cyclicGeneratorInverseMatrix P r =
    ((1 + RatFunc.X : FunctionField P)⁻¹) •
      (constantMatrix P r 1 *
        cyclicGeneratorMatrix P r ^ (r.matrixRank - 1))
  calc
    cyclicGeneratorInverseMatrix P r =
        (onePlusY P r)⁻¹ •
          cyclicGeneratorMatrix P r ^ (r.matrixRank - 1) :=
      cyclicGeneratorInverseMatrix_eq_inv_smul_pow_pred P r
    _ = ((1 + RatFunc.X : FunctionField P)⁻¹) •
          cyclicGeneratorMatrix P r ^ (r.matrixRank - 1) := by
      simpa only using onePlusYInv_smul_eq_functionField_smul P r
        (cyclicGeneratorMatrix P r ^ (r.matrixRank - 1))
    _ = _ := by simp [← constantMatrixEmbedding_apply]

/-- Every element of the arithmetic Cartwright--Steger order has arithmetic
coordinates in the explicit cyclic basis. -/
theorem cartwrightStegerOrderToCyclic_mem_arithmeticCyclicSpan
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r) :
    cartwrightStegerOrderToCyclicAlgebra P r x ∈
      arithmeticCyclicSpan P r := by
  apply Algebra.adjoin_induction
    (R := ArithmeticRing P)
    (s := Set.range (constantMatrix P r) ∪
      {cyclicGeneratorMatrix P r, cyclicGeneratorInverseMatrix P r})
    (p := fun M hM =>
      (⟨M, cartwrightStegerOrder_le_cyclicAlgebra P r M hM⟩ :
        CyclicAlgebra P r) ∈ arithmeticCyclicSpan P r)
  · intro M hM
    rcases hM with hM | hM
    · obtain ⟨c, rfl⟩ := hM
      have h := constantCyclicMonomial_mem_arithmeticCyclicSpan P r c 0
        (lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r))
      simpa only [pow_zero, mul_one] using h
    · rcases hM with (rfl | hM)
      · exact cyclicGenerator_mem_arithmeticCyclicSpan P r
      · rw [Set.mem_singleton_iff] at hM
        subst M
        exact cyclicGeneratorInverse_mem_arithmeticCyclicSpan P r
  · intro a
    have h := (arithmeticCyclicSpan P r).smul_mem a
      (one_mem_arithmeticCyclicSpan P r)
    convert h using 1
    apply Subtype.ext
    change arithmeticRingToSplitMatrix P r a =
      ((arithmeticRingToFunctionField P a) •
        (1 : CyclicAlgebra P r) : CyclicAlgebra P r).1
    rw [Algebra.smul_def, mul_one]
    rfl
  · intro M N hM hN hMi hNi
    exact (arithmeticCyclicSpan P r).add_mem hMi hNi
  · intro M N hM hN hMi hNi
    exact arithmeticCyclicSpan_mul_mem P r _ _ hMi hNi
  · exact x.property

/-- Each function-field cyclic coordinate of an order element is the image
of an arithmetic-ring coefficient. -/
theorem exists_arithmetic_coordinate_of_cartwrightStegerOrder
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    ∃ a : ArithmeticRing P,
      arithmeticRingToFunctionField P a =
        (functionFieldCyclicBasis P r).repr
          (cartwrightStegerOrderToCyclicAlgebra P r x) p := by
  have hx := cartwrightStegerOrderToCyclic_mem_arithmeticCyclicSpan P r x
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (ArithmeticRing P)).mp hx
  have hc' : (∑ q, arithmeticRingToFunctionField P (c q) •
      functionFieldCyclicBasis P r q) =
      cartwrightStegerOrderToCyclicAlgebra P r x := by
    simp only [functionFieldCyclicBasis_apply]
    exact hc
  refine ⟨c p, ?_⟩
  have hp := congrArg ((functionFieldCyclicBasis P r).coord p) hc'
  have hrepr (q : Fin r.matrixRank × Fin r.matrixRank) :
      (functionFieldCyclicBasis P r).coord p
          (functionFieldCyclicBasis P r q) =
        if q = p then 1 else 0 := by
    have hq := congrArg
      (fun f : (Fin r.matrixRank × Fin r.matrixRank) →₀ FunctionField P => f p)
      ((functionFieldCyclicBasis P r).repr_self q)
    simp only [Finsupp.single_apply] at hq
    exact hq
  simp only [map_sum, map_smul, smul_eq_mul] at hp
  simp_rw [hrepr] at hp
  simpa using hp

/-- Coordinatewise form of the arithmetic/building intersection for an
actual order element. -/
theorem exists_integralArithmetic_coordinate_of_order_and_buildingIntegral
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r)
    (hlocal : ∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r
          (cartwrightStegerOrderToCyclicAlgebra P r x))
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    ∃ a : IntegralArithmeticRing P,
      integralArithmeticToFunctionField P a =
        (functionFieldCyclicBasis P r).repr
          (cartwrightStegerOrderToCyclicAlgebra P r x) p := by
  let z := (functionFieldCyclicBasis P r).repr
    (cartwrightStegerOrderToCyclicAlgebra P r x) p
  have harithmetic : ∃ a : ArithmeticRing P,
      arithmeticRingToFunctionField P a = z :=
    exists_arithmetic_coordinate_of_cartwrightStegerOrder P r x p
  have hbuilding : ∃ f : BuildingIntegerRing P,
      SphericalHecke.integerEmbedding (BaseField P) f =
        functionFieldToBuildingLocalField P z :=
    exists_buildingInteger_coordinate_of_cyclicAlgebra_integral
      P r (cartwrightStegerOrderToCyclicAlgebra P r x) hlocal p
  exact arithmetic_building_integer_intersection P z harithmetic hbuilding

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
