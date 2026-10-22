import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Integral.SkewCompatibility
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Integral.SkewReconstructionTheorem
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Integral.SkewUnits

/-!
# The Cartwright--Steger cyclic division algebra

This module proves that the construction-owned cyclic algebra has no zero
divisors, rather than assuming the division-algebra assertion from the source
paper.  The proof clears the finitely many function-field coordinates of an
arbitrary cyclic-algebra element by one nonzero central polynomial.  The
cleared element belongs to the faithful skew Laurent order, whose extremal
support coefficient cannot vanish under multiplication.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

/-- Two nonzero skew Laurent polynomials have nonzero product. -/
theorem skewLaurent_mul_ne_zero
    (P : BasePrime) (r : Rank)
    {f g : CartwrightStegerSkewLaurentRing P r}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    f * g ≠ 0 := by
  obtain ⟨a, ha, hmaxa⟩ := exists_skewLaurent_support_max P r hf
  obtain ⟨b, hb, hmaxb⟩ := exists_skewLaurent_support_max P r hg
  intro hzero
  have hcoeff := skewLaurent_coeff_mul_at_support_max_ne_zero P r
    ha hmaxa hb hmaxb
  rw [hzero] at hcoeff
  exact hcoeff rfl

/-- A common polynomial denominator for all coordinates in the fixed cyclic
basis. -/
noncomputable def cyclicCoordinateCommonDenominator
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    PolynomialRing P :=
  ∏ p : Fin r.matrixRank × Fin r.matrixRank,
    ((functionFieldCyclicBasis P r).repr x p).denom

theorem cyclicCoordinateCommonDenominator_ne_zero
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    cyclicCoordinateCommonDenominator P r x ≠ 0 := by
  rw [cyclicCoordinateCommonDenominator, Finset.prod_ne_zero_iff]
  intro p _
  exact RatFunc.denom_ne_zero _

theorem cyclicCoordinate_denom_dvd_commonDenominator
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    ((functionFieldCyclicBasis P r).repr x p).denom ∣
      cyclicCoordinateCommonDenominator P r x := by
  unfold cyclicCoordinateCommonDenominator
  exact Finset.dvd_prod_of_mem
    (fun q : Fin r.matrixRank × Fin r.matrixRank =>
      ((functionFieldCyclicBasis P r).repr x q).denom)
    (Finset.mem_univ p)

/-- After multiplication by the common central denominator, every cyclic
coordinate comes from the integral arithmetic coefficient ring. -/
theorem exists_integralArithmetic_coordinate_commonDenominator_smul
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    ∃ a : IntegralArithmeticRing P,
      integralArithmeticToFunctionField P a =
        (functionFieldCyclicBasis P r).repr
          ((algebraMap (PolynomialRing P) (FunctionField P)
              (cyclicCoordinateCommonDenominator P r x)) • x) p := by
  let D := cyclicCoordinateCommonDenominator P r x
  let c := (functionFieldCyclicBasis P r).repr x p
  have hD : D ≠ 0 := cyclicCoordinateCommonDenominator_ne_zero P r x
  have hdvd : c.denom ∣ D :=
    cyclicCoordinate_denom_dvd_commonDenominator P r x p
  obtain ⟨q, hq⟩ := (RatFunc.denom_dvd hD).mp hdvd
  refine ⟨algebraMap (PolynomialRing P) (IntegralArithmeticRing P) q, ?_⟩
  rw [integralArithmeticToFunctionField_algebraMap]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  change algebraMap (PolynomialRing P) (FunctionField P) q =
    algebraMap (PolynomialRing P) (FunctionField P) D * c
  rw [hq]
  rw [div_eq_mul_inv, mul_left_comm,
    mul_inv_cancel₀ (RatFunc.algebraMap_ne_zero hD), mul_one]

/-- Every cyclic-algebra element becomes an element of the faithful skew
Laurent order after multiplication by one nonzero central polynomial. -/
theorem exists_skewLaurent_clearing_cyclic_denominators
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    ∃ D : PolynomialRing P, D ≠ 0 ∧
      ∃ f : CartwrightStegerSkewLaurentRing P r,
        skewLaurentToCyclicAlgebra P r f =
          (algebraMap (PolynomialRing P) (FunctionField P) D) • x := by
  let D := cyclicCoordinateCommonDenominator P r x
  have hD : D ≠ 0 := cyclicCoordinateCommonDenominator_ne_zero P r x
  have hcoords : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      ∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a =
          (functionFieldCyclicBasis P r).repr
            ((algebraMap (PolynomialRing P) (FunctionField P) D) • x) p := by
    intro p
    exact exists_integralArithmetic_coordinate_commonDenominator_smul P r x p
  obtain ⟨f, hf⟩ := exists_skewLaurent_of_integralCyclicCoordinates P r
    ((algebraMap (PolynomialRing P) (FunctionField P) D) • x) hcoords
  refine ⟨D, hD, f, ?_⟩
  apply Subtype.ext
  exact hf

/-- The concrete cyclic algebra has no zero divisors. -/
theorem cyclicAlgebra_mul_ne_zero
    (P : BasePrime) (r : Rank)
    {x y : CyclicAlgebra P r} (hx : x ≠ 0) (hy : y ≠ 0) :
    x * y ≠ 0 := by
  obtain ⟨D, hD, f, hf⟩ :=
    exists_skewLaurent_clearing_cyclic_denominators P r x
  obtain ⟨E, hE, g, hg⟩ :=
    exists_skewLaurent_clearing_cyclic_denominators P r y
  have hDf : f ≠ 0 := by
    intro hf0
    rw [hf0, map_zero] at hf
    have hscalar :
        algebraMap (PolynomialRing P) (FunctionField P) D ≠ 0 :=
      RatFunc.algebraMap_ne_zero hD
    exact hx ((smul_eq_zero.mp hf.symm).resolve_left hscalar)
  have hEg : g ≠ 0 := by
    intro hg0
    rw [hg0, map_zero] at hg
    have hscalar :
        algebraMap (PolynomialRing P) (FunctionField P) E ≠ 0 :=
      RatFunc.algebraMap_ne_zero hE
    exact hy ((smul_eq_zero.mp hg.symm).resolve_left hscalar)
  intro hxy
  have hmap : skewLaurentToCyclicAlgebra P r (f * g) = 0 := by
    rw [map_mul, hf, hg]
    rw [smul_mul_smul_comm, hxy, smul_zero]
  have hfg : f * g = 0 := by
    apply skewLaurentToGlobalMatrix_injective P r
    simpa only [skewLaurentToCyclicAlgebra_coe, map_zero, ZeroMemClass.coe_zero]
      using congrArg Subtype.val hmap
  exact (skewLaurent_mul_ne_zero P r hDf hEg) hfg

/-- The construction-owned cyclic algebra is a domain. -/
@[implicit_reducible] noncomputable def cyclicAlgebraIsDomain
    (P : BasePrime) (r : Rank) : IsDomain (CyclicAlgebra P r) := by
  letI : NoZeroDivisors (CyclicAlgebra P r) :=
    ⟨fun h => Classical.byContradiction fun hn =>
      cyclicAlgebra_mul_ne_zero P r
        (fun hx => hn (Or.inl hx)) (fun hy => hn (Or.inr hy)) h⟩
  exact NoZeroDivisors.to_isDomain (CyclicAlgebra P r)

/-- The explicit cyclic algebra is a division ring because it is a
finite-dimensional domain over its function-field center. -/
@[implicit_reducible] noncomputable def cyclicAlgebraDivisionRing
    (P : BasePrime) (r : Rank) : DivisionRing (CyclicAlgebra P r) := by
  letI : IsDomain (CyclicAlgebra P r) := cyclicAlgebraIsDomain P r
  letI : FiniteDimensional (FunctionField P) (CyclicAlgebra P r) :=
    (functionFieldCyclicBasis P r).finiteDimensional_of_finite
  exact divisionRingOfFiniteDimensional (FunctionField P) (CyclicAlgebra P r)

/-- The construction-owned cyclic division algebra is simple as a ring.
Together with `cyclicAlgebraIsCentral` and the explicit cyclic basis, this
supplies the finite-dimensional central-simple-algebra premises used by the
specialized strong-approximation argument. -/
theorem cyclicAlgebraIsSimpleRing
    (P : BasePrime) (r : Rank) : IsSimpleRing (CyclicAlgebra P r) := by
  letI : DivisionRing (CyclicAlgebra P r) := cyclicAlgebraDivisionRing P r
  infer_instance

/-- The central division algebra has degree exactly the selected matrix rank:
its dimension over the global function field is `d²`. -/
theorem finrank_cyclicAlgebra
    (P : BasePrime) (r : Rank) :
    Module.finrank (FunctionField P) (CyclicAlgebra P r) =
      r.matrixRank * r.matrixRank := by
  rw [Module.finrank_eq_card_basis (functionFieldCyclicBasis P r),
    Fintype.card_prod, Fintype.card_fin]

/-- The explicit representation at the building place is faithful.  This is
now a consequence of the proved division-ring structure, not an assumption
about the displayed matrices. -/
theorem cyclicAlgebraToBuilding_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (cyclicAlgebraToBuilding P r) := by
  letI : DivisionRing (CyclicAlgebra P r) := cyclicAlgebraDivisionRing P r
  exact RingHom.injective (cyclicAlgebraToBuilding P r).toRingHom

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
