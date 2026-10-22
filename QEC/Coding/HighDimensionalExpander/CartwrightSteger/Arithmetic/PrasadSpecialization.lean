import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Arithmetic.IntrinsicStrongApproximation
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# The Prasad specialization for the Cartwright--Steger inner form

This module fixes the concrete global and local groups used by the
strong-approximation step in the Cartwright--Steger construction.  The
building-place factor is used to verify the noncompactness hypothesis at the
place removed from the adeles.  The approximation endpoint is the genuine
completed norm-one cyclic order at the selected congruence place.

No density, connectedness, simply-connectedness, or surjectivity hypothesis
is packaged into these definitions.  They identify the construction's actual
global points, the adelic integral open, and the selected local projection.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped TensorProduct
open scoped commutatorElement
open Topology

/-! ## The concrete S-arithmetic base -/

/-- The polynomial, localized arithmetic, and rational-function rings form
the scalar tower used by the construction. -/
noncomputable instance polynomialArithmeticFunctionFieldTower
    (P : BasePrime) :
    IsScalarTower (PolynomialRing P) (ArithmeticRing P)
      (FunctionField P) :=
  IsScalarTower.of_algebraMap_eq fun f =>
    (arithmeticRingToFunctionField_algebraMap P f).symm

private theorem arithmeticLocalizationElement_ne_zero
    (P : BasePrime) :
    (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P) ≠ 0 := by
  apply mul_ne_zero Polynomial.X_ne_zero
  intro h
  have := congrArg (Polynomial.eval (0 : BaseField P)) h
  simp at this

/-- Localizing the polynomial coefficient ring at the construction's two
distinguished units does not introduce zero divisors. -/
noncomputable instance arithmeticRingIsDomain
    (P : BasePrime) : IsDomain (ArithmeticRing P) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (ArithmeticRing P)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (arithmeticLocalizationElement_ne_zero P))

/-- The construction's function field is the fraction field of the actual
S-arithmetic coefficient ring `F_q[y,1/y,1/(1+y)]`. -/
noncomputable instance arithmeticRingFunctionFieldIsFractionRing
    (P : BasePrime) :
    IsFractionRing (ArithmeticRing P) (FunctionField P) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers
      (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P))
    (ArithmeticRing P) (FunctionField P)

/-- The actual S-arithmetic coefficient ring is Dedekind. -/
noncomputable instance arithmeticRingIsDedekindDomain
    (P : BasePrime) : IsDedekindDomain (ArithmeticRing P) := by
  exact IsLocalization.isDedekindDomain (PolynomialRing P)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (arithmeticLocalizationElement_ne_zero P))
    (ArithmeticRing P)

/-! ## Finite adeles away from the two inverted places -/

/-- The finite adele ring over the actual `S`-arithmetic base.  Because
`y` and `1+y` are units of `ArithmeticRing`, its height-one spectrum is
precisely the collection of finite places outside the two distinguished
places used by the Cartwright--Steger construction. -/
noncomputable abbrev ArithmeticFiniteAdeleRing (P : BasePrime) :=
  IsDedekindDomain.FiniteAdeleRing (ArithmeticRing P) (FunctionField P)

/-- The diagonal embedding of the global function field into its finite
adeles away from the construction's two inverted places. -/
noncomputable def functionFieldToArithmeticFiniteAdeles
    (P : BasePrime) :
    FunctionField P →+* ArithmeticFiniteAdeleRing P :=
  IsDedekindDomain.FiniteAdeleRing.algebraMap
    (ArithmeticRing P) (FunctionField P)

/-- The compact-open integral part of the finite adeles away from the two
inverted Cartwright--Steger places.  This is the scalar coefficient ring of
the open subgroup used in the specialized Prasad argument. -/
noncomputable def ArithmeticIntegralFiniteAdeles
    (P : BasePrime) : Subring (ArithmeticFiniteAdeleRing P) where
  carrier a := ∀ v, a v ∈ v.adicCompletionIntegers (FunctionField P)
  zero_mem' v := (v.adicCompletionIntegers (FunctionField P)).zero_mem
  one_mem' v := (v.adicCompletionIntegers (FunctionField P)).one_mem
  add_mem' {a b} ha hb v := by
    exact
      (v.adicCompletionIntegers (FunctionField P)).add_mem
        (a v) (b v) (ha v) (hb v)
  mul_mem' {a b} ha hb v := by
    exact
      (v.adicCompletionIntegers (FunctionField P)).mul_mem
        (a v) (b v) (ha v) (hb v)
  neg_mem' {a} ha v := by
    exact
      (v.adicCompletionIntegers (FunctionField P)).neg_mem (a v) (ha v)

/-- Every scalar from the actual `S`-arithmetic ring is integral at every
finite-adele coordinate (the two allowed pole places have already been
removed by the choice of the Dedekind base). -/
theorem functionFieldToArithmeticFiniteAdeles_algebraMap_mem_integral
    (P : BasePrime) (a : ArithmeticRing P) :
    functionFieldToArithmeticFiniteAdeles P
        (algebraMap (ArithmeticRing P) (FunctionField P) a) ∈
      ArithmeticIntegralFiniteAdeles P := by
  show ∀ v, _
  intro v
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem
    (ArithmeticRing P) (FunctionField P) v a

/-- A global scalar is integral at every finite place outside the two
inverted Cartwright--Steger places exactly when it comes from the concrete
`S`-arithmetic coefficient ring. -/
theorem functionFieldToArithmeticFiniteAdeles_mem_integral_iff
    (P : BasePrime) (x : FunctionField P) :
    functionFieldToArithmeticFiniteAdeles P x ∈
        ArithmeticIntegralFiniteAdeles P ↔
      x ∈ (algebraMap (ArithmeticRing P) (FunctionField P)).range := by
  constructor
  · intro hx
    apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have hv := hx v
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hv
    change Valued.v
        (x : v.adicCompletion (FunctionField P)) ≤ 1 at hv
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe] at hv
    exact hv
  · rintro ⟨a, rfl⟩
    exact functionFieldToArithmeticFiniteAdeles_algebraMap_mem_integral P a

/-! ## Finite-adelic scalar extension of the cyclic division algebra -/

/-- The actual cyclic division algebra after scalar extension from the
global function field to the finite adeles away from the two inverted
places.  This is the ambient algebra underlying the finite-adelic
`SL₁(D)` in the specialized Prasad theorem. -/
noncomputable abbrev ArithmeticFiniteAdeleCyclicAlgebra
    (P : BasePrime) (r : Rank) :=
  TensorProduct (FunctionField P) (ArithmeticFiniteAdeleRing P)
    (CyclicAlgebra P r)

/-- Diagonal scalar extension of a global cyclic-algebra point to the
finite-adelic cyclic algebra. -/
noncomputable def cyclicAlgebraToArithmeticFiniteAdeles
    (P : BasePrime) (r : Rank) :
    CyclicAlgebra P r →ₐ[FunctionField P]
      ArithmeticFiniteAdeleCyclicAlgebra P r :=
  Algebra.TensorProduct.includeRight

@[simp] theorem cyclicAlgebraToArithmeticFiniteAdeles_apply
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    cyclicAlgebraToArithmeticFiniteAdeles P r x =
      TensorProduct.tmul (FunctionField P) 1 x :=
  rfl

/-- The construction-owned cyclic basis remains a basis after finite-adelic
scalar extension.  Hence all topology and integral conditions below can be
stated in explicit, finite coordinates. -/
noncomputable def arithmeticFiniteAdeleCyclicBasis
    (P : BasePrime) (r : Rank) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (ArithmeticFiniteAdeleRing P)
      (ArithmeticFiniteAdeleCyclicAlgebra P r) :=
  (functionFieldCyclicBasis P r).baseChange
    (ArithmeticFiniteAdeleRing P)

/-- The finite-adelic cyclic algebra carries the finite-coordinate topology
transported by the construction-owned cyclic basis.  This is the canonical
finite-dimensional adelic topology, stated without choosing an external
matrix representation. -/
noncomputable instance arithmeticFiniteAdeleCyclicAlgebraTopologicalSpace
    (P : BasePrime) (r : Rank) :
    TopologicalSpace (ArithmeticFiniteAdeleCyclicAlgebra P r) :=
  TopologicalSpace.induced
    (arithmeticFiniteAdeleCyclicBasis P r).equivFun inferInstance

/-- The all-integral finite-adelic cyclic lattice: every coordinate in the
actual cyclic basis is integral at every finite place away from the two
inverted Cartwright--Steger places. -/
noncomputable def ArithmeticFiniteAdeleCyclicIntegralLattice
    (P : BasePrime) (r : Rank) :
    Set (ArithmeticFiniteAdeleCyclicAlgebra P r) :=
  {x | ∀ p, (arithmeticFiniteAdeleCyclicBasis P r).equivFun x p ∈
    ArithmeticIntegralFiniteAdeles P}

/-- The finite set of arithmetic places at which at least one cyclic
coordinate of a finite-adelic cyclic element is nonintegral. -/
noncomputable def arithmeticFiniteAdeleCyclicNonintegralPlaces
    (P : BasePrime) (r : Rank)
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r) :
    Set (IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :=
  {v | ∃ p,
    (arithmeticFiniteAdeleCyclicBasis P r).equivFun x p v ∉
      v.adicCompletionIntegers (FunctionField P)}

theorem arithmeticFiniteAdeleCyclicNonintegralPlaces_finite
    (P : BasePrime) (r : Rank)
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r) :
    (arithmeticFiniteAdeleCyclicNonintegralPlaces P r x).Finite := by
  classical
  rw [show arithmeticFiniteAdeleCyclicNonintegralPlaces P r x =
      ⋃ p, {v |
        (arithmeticFiniteAdeleCyclicBasis P r).equivFun x p v ∉
          v.adicCompletionIntegers (FunctionField P)} by
    ext v
    simp [arithmeticFiniteAdeleCyclicNonintegralPlaces]]
  apply Set.finite_iUnion
  intro p
  have hp :=
    ((arithmeticFiniteAdeleCyclicBasis P r).equivFun x p).property
  exact Filter.mem_cofinite.mp hp

/-- The finite denominator support of an adelic cyclic-algebra unit records
the nonintegral places of both the unit and its inverse. -/
noncomputable def arithmeticFiniteAdeleCyclicUnitDenominatorPlaces
    (P : BasePrime) (r : Rank)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    Set (IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :=
  arithmeticFiniteAdeleCyclicNonintegralPlaces P r u ∪
    arithmeticFiniteAdeleCyclicNonintegralPlaces P r (↑u⁻¹)

theorem arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_finite
    (P : BasePrime) (r : Rank)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    (arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r u).Finite :=
  (arithmeticFiniteAdeleCyclicNonintegralPlaces_finite P r u).union
    (arithmeticFiniteAdeleCyclicNonintegralPlaces_finite P r (↑u⁻¹))

theorem arithmeticFiniteAdeleCyclic_mem_integralLattice_iff_denominatorPlaces_empty
    (P : BasePrime) (r : Rank)
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r) :
    x ∈ ArithmeticFiniteAdeleCyclicIntegralLattice P r ↔
      arithmeticFiniteAdeleCyclicNonintegralPlaces P r x = ∅ := by
  constructor
  · intro hx
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨p, hp⟩ := hv
    exact hp (hx p v)
  · intro h p v
    by_contra hp
    have hv : v ∈ arithmeticFiniteAdeleCyclicNonintegralPlaces P r x :=
      ⟨p, hp⟩
    rw [h] at hv
    exact hv

/-- Elements of the all-integral finite-adelic cyclic lattice, bundled so
their integral coordinates can be reduced at a selected place. -/
noncomputable abbrev ArithmeticFiniteAdeleCyclicIntegralElement
    (P : BasePrime) (r : Rank) :=
  ↥(ArithmeticFiniteAdeleCyclicIntegralLattice P r)

/-- Cyclic coordinates commute with the diagonal finite-adele scalar
extension. -/
theorem arithmeticFiniteAdeleCyclicBasis_equivFun_diagonal
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (arithmeticFiniteAdeleCyclicBasis P r).equivFun
        (cyclicAlgebraToArithmeticFiniteAdeles P r x) p =
      functionFieldToArithmeticFiniteAdeles P
        ((functionFieldCyclicBasis P r).equivFun x p) := by
  rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
    cyclicAlgebraToArithmeticFiniteAdeles_apply,
    arithmeticFiniteAdeleCyclicBasis,
    Module.Basis.baseChange_repr_tmul]
  rw [Algebra.smul_def, mul_one]
  rfl

/-- Every cyclic coordinate of an element of the arithmetic cyclic order
comes from the actual `S`-arithmetic coefficient ring. -/
theorem exists_arithmetic_coordinate_of_mem_arithmeticCyclicSpan
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hx : x ∈ arithmeticCyclicSpan P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    ∃ a : ArithmeticRing P,
      arithmeticRingToFunctionField P a =
        (functionFieldCyclicBasis P r).equivFun x p := by
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (ArithmeticRing P)).mp hx
  have hc' : (∑ q, arithmeticRingToFunctionField P (c q) •
      functionFieldCyclicBasis P r q) = x := by
    simp only [functionFieldCyclicBasis_apply, Algebra.smul_def] at hc ⊢
    exact hc
  refine ⟨c p, ?_⟩
  have hp := congrArg ((functionFieldCyclicBasis P r).coord p) hc'
  have hrepr (q : Fin r.matrixRank × Fin r.matrixRank) :
      (functionFieldCyclicBasis P r).coord p
          (functionFieldCyclicBasis P r q) =
        if q = p then 1 else 0 := by
    have hq := congrArg
      (fun f : (Fin r.matrixRank × Fin r.matrixRank) →₀ FunctionField P =>
        f p)
      ((functionFieldCyclicBasis P r).repr_self q)
    simp only [Finsupp.single_apply, eq_comm] at hq ⊢
    exact hq
  simp only [map_sum, map_smul, smul_eq_mul] at hp
  simp_rw [hrepr] at hp
  simpa [Module.Basis.equivFun_apply] using hp

/-- A canonical arithmetic lift of each cyclic coordinate of an element of
the arithmetic cyclic order. -/
noncomputable def arithmeticCyclicCoordinate
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hx : x ∈ arithmeticCyclicSpan P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) : ArithmeticRing P :=
  Classical.choose
    (exists_arithmetic_coordinate_of_mem_arithmeticCyclicSpan P r x hx p)

@[simp] theorem arithmeticRingToFunctionField_arithmeticCyclicCoordinate
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hx : x ∈ arithmeticCyclicSpan P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    arithmeticRingToFunctionField P
        (arithmeticCyclicCoordinate P r x hx p) =
      (functionFieldCyclicBasis P r).equivFun x p :=
  Classical.choose_spec
    (exists_arithmetic_coordinate_of_mem_arithmeticCyclicSpan P r x hx p)

/-- The chosen arithmetic coordinates reconstruct the original global
cyclic-algebra element in its construction-owned basis. -/
theorem sum_arithmeticCyclicCoordinate_smul_basis
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hx : x ∈ arithmeticCyclicSpan P r) :
    (∑ p, arithmeticRingToFunctionField P
        (arithmeticCyclicCoordinate P r x hx p) •
          functionFieldCyclicBasis P r p) = x := by
  simp_rw [arithmeticRingToFunctionField_arithmeticCyclicCoordinate]
  exact (functionFieldCyclicBasis P r).sum_equivFun x

/-- The same arithmetic cyclic coordinates assembled in the integral split
matrix chart used by the construction. -/
noncomputable def arithmeticCyclicCoordinateMatrix
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hx : x ∈ arithmeticCyclicSpan P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  ∑ p, arithmeticToConstantArithmetic P r
      (arithmeticCyclicCoordinate P r x hx p) •
        orderIndexCyclicBasisVector P r p

/-- The integral split matrix assembled from the arithmetic coordinates
maps back to the original global cyclic-algebra matrix. -/
theorem arithmeticCyclicCoordinateMatrix_to_global
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hx : x ∈ arithmeticCyclicSpan P r) :
    (arithmeticCyclicCoordinateMatrix P r x hx).map
        (constantArithmeticToSplittingFunctionField P r) = x.1 := by
  rw [arithmeticCyclicCoordinateMatrix]
  have hmapSum :
      ((∑ p, arithmeticToConstantArithmetic P r
          (arithmeticCyclicCoordinate P r x hx p) •
            orderIndexCyclicBasisVector P r p).map
          (constantArithmeticToSplittingFunctionField P r)) =
        ∑ p, (arithmeticToConstantArithmetic P r
          (arithmeticCyclicCoordinate P r x hx p) •
            orderIndexCyclicBasisVector P r p).map
          (constantArithmeticToSplittingFunctionField P r) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sum_apply, map_sum]
  rw [hmapSum]
  simp_rw [Matrix.map_smul' _ _ _ (map_mul _),
    constantArithmeticToSplittingFunctionField_arithmeticBaseChange,
    orderIndexCyclicBasisVector_to_global]
  have hsum := congrArg Subtype.val
    (sum_arithmeticCyclicCoordinate_smul_basis P r x hx)
  simp [functionFieldCyclicBasis_apply,
    arithmeticRingToSplittingFunctionField, Algebra.smul_def] at hsum ⊢
  exact hsum

/-- An arithmetic cyclic-order element enters the all-integral adelic
lattice under the genuine diagonal scalar extension. -/
theorem cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hx : x ∈ arithmeticCyclicSpan P r) :
    cyclicAlgebraToArithmeticFiniteAdeles P r x ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r := by
  intro p
  obtain ⟨a, ha⟩ :=
    exists_arithmetic_coordinate_of_mem_arithmeticCyclicSpan P r x hx p
  rw [arithmeticFiniteAdeleCyclicBasis_equivFun_diagonal, ← ha]
  exact functionFieldToArithmeticFiniteAdeles_algebraMap_mem_integral P a

/-- The concrete all-place finite-adelic integrality condition on a global
cyclic-algebra point is exactly membership in the construction's arithmetic
cyclic span.  This is the coordinate form of the source equality
`D(k) ∩ D(𝔸_f)^integral = D(R)`. -/
theorem cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice_iff
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    cyclicAlgebraToArithmeticFiniteAdeles P r x ∈
        ArithmeticFiniteAdeleCyclicIntegralLattice P r ↔
      x ∈ arithmeticCyclicSpan P r := by
  constructor
  · intro hx
    have hcoord : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
        ∃ a : ArithmeticRing P,
          arithmeticRingToFunctionField P a =
            (functionFieldCyclicBasis P r).equivFun x p := by
      intro p
      have hp := hx p
      rw [arithmeticFiniteAdeleCyclicBasis_equivFun_diagonal,
        functionFieldToArithmeticFiniteAdeles_mem_integral_iff] at hp
      exact hp
    choose c hc using hcoord
    apply (Submodule.mem_span_range_iff_exists_fun
      (ArithmeticRing P)).mpr
    refine ⟨c, ?_⟩
    have hsum := (functionFieldCyclicBasis P r).sum_equivFun x
    calc
      (∑ p, c p • functionFieldCyclicBasisVector P r p) =
          ∑ p, (functionFieldCyclicBasis P r).equivFun x p •
            functionFieldCyclicBasisVector P r p := by
        apply Finset.sum_congr rfl
        intro p _
        change arithmeticRingToFunctionField P (c p) •
            functionFieldCyclicBasisVector P r p = _
        rw [hc]
      _ = x := by
        simpa [functionFieldCyclicBasis_apply] using hsum
  · exact cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice P r x

/-- Every point of the arithmetic cyclic span is represented by an element
of the actual Cartwright--Steger order generated by constants and
`z^{±1}`.  No larger auxiliary order is introduced. -/
theorem exists_cartwrightStegerOrder_of_mem_arithmeticCyclicSpan
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hx : x ∈ arithmeticCyclicSpan P r) :
    ∃ y : CartwrightStegerOrder P r,
      cartwrightStegerOrderToCyclicAlgebra P r y = x := by
  refine Submodule.span_induction
    (p := fun x _ => ∃ y : CartwrightStegerOrder P r,
      cartwrightStegerOrderToCyclicAlgebra P r y = x)
    ?basis ?zero ?add ?smul hx
  · intro x hxRange
    obtain ⟨p, rfl⟩ := hxRange
    let y : CartwrightStegerOrder P r :=
      ⟨(functionFieldCyclicBasisVector P r p :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)),
        (CartwrightStegerOrder P r).mul_mem
          (constantMatrix_mem_cartwrightStegerOrder P r
            (constantBasis P r p.1))
          ((CartwrightStegerOrder P r).pow_mem
            (cyclicGeneratorMatrix_mem_cartwrightStegerOrder P r)
            (p.2 : Nat))⟩
    exact ⟨y, Subtype.ext rfl⟩
  · exact ⟨0, map_zero (cartwrightStegerOrderToCyclicAlgebra P r)⟩
  · intro x y _ _ hx hy
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add (cartwrightStegerOrderToCyclicAlgebra P r) x' y'⟩
  · intro a x _ hx
    obtain ⟨x', rfl⟩ := hx
    refine ⟨a • x', ?_⟩
    apply Subtype.ext
    change ((a • x' : CartwrightStegerOrder P r) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) =
      ((a • cartwrightStegerOrderToCyclicAlgebra P r x' :
          CyclicAlgebra P r) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r))
    rw [Subalgebra.coe_smul]
    change a • (x'.1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) =
      (((arithmeticRingToFunctionField P a) •
          cartwrightStegerOrderToCyclicAlgebra P r x' :
        CyclicAlgebra P r) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r))
    rw [Subalgebra.coe_smul]
    change a • (x'.1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) =
      arithmeticRingToFunctionField P a • x'.1
    simp only [Algebra.smul_def]
    congr 1

/-- The explicit arithmetic cyclic span is exactly the image of the
construction-owned Cartwright--Steger order in the global cyclic algebra. -/
theorem mem_arithmeticCyclicSpan_iff_exists_cartwrightStegerOrder
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    x ∈ arithmeticCyclicSpan P r ↔
      ∃ y : CartwrightStegerOrder P r,
        cartwrightStegerOrderToCyclicAlgebra P r y = x := by
  constructor
  · exact exists_cartwrightStegerOrder_of_mem_arithmeticCyclicSpan P r x
  · rintro ⟨y, rfl⟩
    exact cartwrightStegerOrderToCyclic_mem_arithmeticCyclicSpan P r y

/-- Diagonal scalar extension on units of the genuine global cyclic
algebra. -/
noncomputable def cyclicAlgebraUnitToArithmeticFiniteAdeles
    (P : BasePrime) (r : Rank) :
    (CyclicAlgebra P r)ˣ →*
      (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ :=
  Units.map (cyclicAlgebraToArithmeticFiniteAdeles P r).toRingHom

@[simp] theorem cyclicAlgebraUnitToArithmeticFiniteAdeles_coe
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    (cyclicAlgebraUnitToArithmeticFiniteAdeles P r u :
        ArithmeticFiniteAdeleCyclicAlgebra P r) =
      cyclicAlgebraToArithmeticFiniteAdeles P r (u : CyclicAlgebra P r) :=
  rfl

/-! ## The concrete finite-adelic reduced-norm-one group -/

/-- A common splitting ring for the finite-adelic scalar extension of the
cyclic algebra.  It is obtained by extending the construction-owned global
splitting field along the finite adele ring, rather than by choosing local
matrix splittings place by place. -/
noncomputable abbrev ArithmeticFiniteAdeleSplittingRing
    (P : BasePrime) (r : Rank) :=
  TensorProduct (FunctionField P) (ArithmeticFiniteAdeleRing P)
    (SplittingFunctionField P r)

/-- The global splitting field embeds diagonally in the common finite-adelic
splitting ring. -/
noncomputable def splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing
    (P : BasePrime) (r : Rank) :
    SplittingFunctionField P r →ₐ[FunctionField P]
      ArithmeticFiniteAdeleSplittingRing P r :=
  Algebra.TensorProduct.includeRight

/-- The construction-owned splitting representation of the global cyclic
algebra, with coefficients extended to the common finite-adelic splitting
ring. -/
noncomputable def cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix
    (P : BasePrime) (r : Rank) :
    CyclicAlgebra P r →ₐ[FunctionField P]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ArithmeticFiniteAdeleSplittingRing P r) :=
  (splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r).mapMatrix.comp
    (CyclicAlgebra P r).val

/-- Splitting representation of the actual finite-adelic cyclic algebra.
On the finite-adele factor it acts by scalar matrices, and on the cyclic
algebra factor it is the verified global splitting representation. -/
noncomputable def arithmeticFiniteAdeleCyclicSplittingMap
    (P : BasePrime) (r : Rank) :
    ArithmeticFiniteAdeleCyclicAlgebra P r →ₐ[ArithmeticFiniteAdeleRing P]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ArithmeticFiniteAdeleSplittingRing P r) :=
  Algebra.TensorProduct.lift
    (Algebra.ofId (ArithmeticFiniteAdeleRing P)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ArithmeticFiniteAdeleSplittingRing P r)))
    (cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix P r)
    (fun a M => by
      change Commute
        (algebraMap (ArithmeticFiniteAdeleRing P)
          (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ArithmeticFiniteAdeleSplittingRing P r)) a)
        (cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix P r M)
      exact Algebra.commutes a _)

/-- Arithmetic Frobenius on the common finite-adelic splitting ring.  It
fixes the finite-adele factor and acts by the construction's constant-field
Frobenius on the global splitting factor. -/
noncomputable def arithmeticFiniteAdeleSplittingFrobenius
    (P : BasePrime) (r : Rank) :
    ArithmeticFiniteAdeleSplittingRing P r
      →ₐ[ArithmeticFiniteAdeleRing P]
        ArithmeticFiniteAdeleSplittingRing P r where
  toRingHom := (Algebra.TensorProduct.map
    (AlgHom.id (FunctionField P) (ArithmeticFiniteAdeleRing P))
    (splittingFunctionFieldFrobenius P r).toAlgHom).toRingHom
  commutes' a := by
    change Algebra.TensorProduct.map
      (AlgHom.id (FunctionField P) (ArithmeticFiniteAdeleRing P))
      (splittingFunctionFieldFrobenius P r).toAlgHom
        (TensorProduct.tmul (FunctionField P) a 1) = _
    simp

@[simp] theorem arithmeticFiniteAdeleSplittingFrobenius_tmul
    (P : BasePrime) (r : Rank)
    (a : ArithmeticFiniteAdeleRing P) (x : SplittingFunctionField P r) :
    arithmeticFiniteAdeleSplittingFrobenius P r
        (TensorProduct.tmul (FunctionField P) a x) =
      TensorProduct.tmul (FunctionField P) a
        (splittingFunctionFieldFrobenius P r x) := by
  simp [arithmeticFiniteAdeleSplittingFrobenius]

/-- The cyclic conjugating matrix in the common finite-adelic splitting
ring. -/
noncomputable def arithmeticFiniteAdeleCyclicGeneratorMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ArithmeticFiniteAdeleSplittingRing P r) :=
  (cyclicGeneratorMatrix P r).map
    (splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r)

/-- The inverse cyclic conjugating matrix in the common finite-adelic
splitting ring. -/
noncomputable def arithmeticFiniteAdeleCyclicGeneratorInverseMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ArithmeticFiniteAdeleSplittingRing P r) :=
  (cyclicGeneratorInverseMatrix P r).map
    (splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r)

/-- Frobenius acts on the splitting matrix of every finite-adelic cyclic
element by conjugation with the construction's cyclic generator.  The proof
is over the actual tensor product and therefore also covers non-diagonal
adelic points. -/
theorem arithmeticFiniteAdeleCyclicSplittingMap_frobenius
    (P : BasePrime) (r : Rank)
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r) :
    (arithmeticFiniteAdeleSplittingFrobenius P r).toRingHom.mapMatrix
        (arithmeticFiniteAdeleCyclicSplittingMap P r x) =
      arithmeticFiniteAdeleCyclicGeneratorMatrix P r *
        arithmeticFiniteAdeleCyclicSplittingMap P r x *
          arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy, Matrix.mul_add, Matrix.add_mul]
  | tmul a x =>
      rw [arithmeticFiniteAdeleCyclicSplittingMap,
        Algebra.TensorProduct.lift_tmul]
      have hglobal := congrArg
        (fun M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r) =>
          M.map
            (splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r))
        (splittingFunctionFieldFrobenius_mapMatrix_eq_cyclicGenerator_conj
          P r x)
      simp only [RingHom.mapMatrix_apply, Matrix.map_mul] at hglobal
      have hscalar :
          (arithmeticFiniteAdeleSplittingFrobenius P r).toRingHom.mapMatrix
            ((Algebra.ofId (ArithmeticFiniteAdeleRing P)
              (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                (ArithmeticFiniteAdeleSplittingRing P r))) a) =
          (Algebra.ofId (ArithmeticFiniteAdeleRing P)
              (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                (ArithmeticFiniteAdeleSplittingRing P r))) a := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [arithmeticFiniteAdeleSplittingFrobenius,
            Matrix.algebraMap_matrix_apply]
        · simp [arithmeticFiniteAdeleSplittingFrobenius,
            Matrix.algebraMap_matrix_apply, hij]
      rw [show
          (arithmeticFiniteAdeleSplittingFrobenius P r).toRingHom.mapMatrix
            ((Algebra.ofId (ArithmeticFiniteAdeleRing P)
              (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                (ArithmeticFiniteAdeleSplittingRing P r))) a *
              cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix P r x) =
          (Algebra.ofId (ArithmeticFiniteAdeleRing P)
              (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                (ArithmeticFiniteAdeleSplittingRing P r))) a *
            (arithmeticFiniteAdeleSplittingFrobenius P r).toRingHom.mapMatrix
              (cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix P r x) by
          change (((Algebra.ofId (ArithmeticFiniteAdeleRing P)
            (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (ArithmeticFiniteAdeleSplittingRing P r))) a *
            cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix P r x).map
              (arithmeticFiniteAdeleSplittingFrobenius P r).toRingHom) = _
          rw [Matrix.map_mul]
          change
            (arithmeticFiniteAdeleSplittingFrobenius P r).toRingHom.mapMatrix
                ((Algebra.ofId (ArithmeticFiniteAdeleRing P)
                  (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                    (ArithmeticFiniteAdeleSplittingRing P r))) a) * _ = _
          rw [hscalar]
          rfl]
      rw [show
          (arithmeticFiniteAdeleSplittingFrobenius P r).toRingHom.mapMatrix
              (cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix P r x) =
            arithmeticFiniteAdeleCyclicGeneratorMatrix P r *
              cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix P r x *
                arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r by
          calc
            _ = ((splittingFunctionFieldFrobenius P r).toRingHom.mapMatrix
                (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                  (SplittingFunctionField P r))).map
                (splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r) := by
              ext i j
              exact arithmeticFiniteAdeleSplittingFrobenius_tmul P r 1 (x.1 i j)
            _ = _ := hglobal]
      let A := (Algebra.ofId (ArithmeticFiniteAdeleRing P)
        (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ArithmeticFiniteAdeleSplittingRing P r))) a
      let M := cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix P r x
      change A * (arithmeticFiniteAdeleCyclicGeneratorMatrix P r * M *
          arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r) =
        arithmeticFiniteAdeleCyclicGeneratorMatrix P r * (A * M) *
          arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r
      calc
        A * (arithmeticFiniteAdeleCyclicGeneratorMatrix P r * M *
            arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r) =
          (A * arithmeticFiniteAdeleCyclicGeneratorMatrix P r) * M *
            arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r := by
              simp only [mul_assoc]
        _ = (arithmeticFiniteAdeleCyclicGeneratorMatrix P r * A) * M *
            arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r := by
          rw [show A * arithmeticFiniteAdeleCyclicGeneratorMatrix P r =
              arithmeticFiniteAdeleCyclicGeneratorMatrix P r * A from
            Algebra.commutes a _]
        _ = arithmeticFiniteAdeleCyclicGeneratorMatrix P r * (A * M) *
            arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r := by
          simp only [mul_assoc]

/-- The determinant of every finite-adelic splitting matrix is Frobenius
fixed.  This is the precise descent invariant required before identifying
the determinant with a base finite adele. -/
theorem arithmeticFiniteAdeleCyclicSplitting_det_frobenius
    (P : BasePrime) (r : Rank)
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r) :
    arithmeticFiniteAdeleSplittingFrobenius P r
        (Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r x)) =
      Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r x) := by
  rw [(arithmeticFiniteAdeleSplittingFrobenius P r).map_det]
  change Matrix.det
      ((arithmeticFiniteAdeleCyclicSplittingMap P r x).map
        (arithmeticFiniteAdeleSplittingFrobenius P r).toRingHom) = _
  rw [show (arithmeticFiniteAdeleCyclicSplittingMap P r x).map
        (arithmeticFiniteAdeleSplittingFrobenius P r).toRingHom =
      arithmeticFiniteAdeleCyclicGeneratorMatrix P r *
        arithmeticFiniteAdeleCyclicSplittingMap P r x *
          arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r by
      exact arithmeticFiniteAdeleCyclicSplittingMap_frobenius P r x]
  rw [Matrix.det_mul, Matrix.det_mul]
  have hz : arithmeticFiniteAdeleCyclicGeneratorMatrix P r *
        arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r = 1 := by
    have h := congrArg
      (fun M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r) =>
        M.map
          (splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r))
      (cyclicGenerator_mul_inverse P r)
    simpa [arithmeticFiniteAdeleCyclicGeneratorMatrix,
      arithmeticFiniteAdeleCyclicGeneratorInverseMatrix,
      Matrix.map_mul] using h
  calc
    Matrix.det (arithmeticFiniteAdeleCyclicGeneratorMatrix P r) *
          Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r x) *
        Matrix.det (arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r) =
      Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r x) *
        (Matrix.det (arithmeticFiniteAdeleCyclicGeneratorMatrix P r) *
          Matrix.det
            (arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r)) := by
      ac_rfl
    _ = _ := by rw [← Matrix.det_mul, hz, Matrix.det_one, mul_one]

/-- The Frobenius-fixed subspace of the global splitting function field. -/
noncomputable def SplittingFunctionFieldFrobeniusFixedSubspace
    (P : BasePrime) (r : Rank) :=
  LinearMap.eqLocus (splittingFunctionFieldFrobenius P r).toLinearMap
    (LinearMap.id : SplittingFunctionField P r →ₗ[FunctionField P]
      SplittingFunctionField P r)

/-- The base function field maps into the Frobenius-fixed subspace of the
splitting field. -/
noncomputable def functionFieldToSplittingFrobeniusFixed
    (P : BasePrime) (r : Rank) :
    FunctionField P →ₗ[FunctionField P]
      SplittingFunctionFieldFrobeniusFixedSubspace P r where
  toFun a := ⟨functionFieldEmbedding P r a,
    splittingFunctionFieldFrobeniusRingEquiv_functionFieldEmbedding P r a⟩
  map_add' a b := by
    apply Subtype.ext
    simp
  map_smul' a b := by
    apply Subtype.ext
    change functionFieldEmbedding P r (a * b) =
      algebraMap (FunctionField P) (SplittingFunctionField P r) a *
        functionFieldEmbedding P r b
    rw [map_mul]
    rfl

theorem functionFieldToSplittingFrobeniusFixed_bijective
    (P : BasePrime) (r : Rank) :
    Function.Bijective (functionFieldToSplittingFrobeniusFixed P r) := by
  constructor
  · intro a b h
    apply (functionFieldEmbedding P r).injective
    exact congrArg Subtype.val h
  · intro x
    obtain ⟨a, ha⟩ := exists_eq_functionFieldEmbedding_of_frobenius_eq
      P r x x.property
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact ha

/-- The explicit fixed-field theorem, bundled as a linear equivalence for
flat equalizer base change. -/
noncomputable def functionFieldEquivSplittingFrobeniusFixed
    (P : BasePrime) (r : Rank) :
    FunctionField P ≃ₗ[FunctionField P]
      SplittingFunctionFieldFrobeniusFixedSubspace P r :=
  LinearEquiv.ofBijective
    (functionFieldToSplittingFrobeniusFixed P r)
    (functionFieldToSplittingFrobeniusFixed_bijective P r)

private noncomputable def arithmeticFiniteAdeleSplittingFrobeniusLinear
    (P : BasePrime) (r : Rank) :
    ArithmeticFiniteAdeleSplittingRing P r
      →ₗ[ArithmeticFiniteAdeleRing P]
        ArithmeticFiniteAdeleSplittingRing P r :=
  TensorProduct.AlgebraTensorModule.lTensor (ArithmeticFiniteAdeleRing P)
    (ArithmeticFiniteAdeleRing P)
    (splittingFunctionFieldFrobenius P r).toLinearMap

private noncomputable def arithmeticFiniteAdeleSplittingIdentityLinear
    (P : BasePrime) (r : Rank) :
    ArithmeticFiniteAdeleSplittingRing P r
      →ₗ[ArithmeticFiniteAdeleRing P]
        ArithmeticFiniteAdeleSplittingRing P r :=
  TensorProduct.AlgebraTensorModule.lTensor (ArithmeticFiniteAdeleRing P)
    (ArithmeticFiniteAdeleRing P)
    (LinearMap.id : SplittingFunctionField P r →ₗ[FunctionField P]
      SplittingFunctionField P r)

private theorem arithmeticFiniteAdeleSplittingFrobeniusLinear_eq
    (P : BasePrime) (r : Rank) :
    arithmeticFiniteAdeleSplittingFrobeniusLinear P r =
      (arithmeticFiniteAdeleSplittingFrobenius P r).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  simp [arithmeticFiniteAdeleSplittingFrobeniusLinear,
    arithmeticFiniteAdeleSplittingFrobenius]

private theorem arithmeticFiniteAdeleSplittingIdentityLinear_eq
    (P : BasePrime) (r : Rank) :
    arithmeticFiniteAdeleSplittingIdentityLinear P r = LinearMap.id := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  simp [arithmeticFiniteAdeleSplittingIdentityLinear]

/-- Collapse a finite adele tensored with a Frobenius-fixed splitting scalar
back to the finite adele ring via the explicit fixed-field equivalence. -/
private noncomputable def arithmeticFiniteAdeleFixedTensorCollapse
    (P : BasePrime) (r : Rank) :
    (ArithmeticFiniteAdeleRing P ⊗[FunctionField P]
        (SplittingFunctionFieldFrobeniusFixedSubspace P r))
      →ₗ[ArithmeticFiniteAdeleRing P] ArithmeticFiniteAdeleRing P :=
  (TensorProduct.AlgebraTensorModule.rid (FunctionField P)
      (ArithmeticFiniteAdeleRing P) (ArithmeticFiniteAdeleRing P)) ∘ₗ
    (LinearEquiv.baseChange (FunctionField P) (ArithmeticFiniteAdeleRing P)
      (SplittingFunctionFieldFrobeniusFixedSubspace P r) (FunctionField P)
      (functionFieldEquivSplittingFrobeniusFixed P r).symm).toLinearMap

@[simp] private theorem arithmeticFiniteAdeleFixedTensorCollapse_tmul
    (P : BasePrime) (r : Rank)
    (a : ArithmeticFiniteAdeleRing P)
    (x : SplittingFunctionFieldFrobeniusFixedSubspace P r) :
    arithmeticFiniteAdeleFixedTensorCollapse P r
        (a ⊗ₜ[FunctionField P] x) =
      (functionFieldEquivSplittingFrobeniusFixed P r).symm x • a := by
  simp [arithmeticFiniteAdeleFixedTensorCollapse]

private theorem arithmeticFiniteAdeleTensorFixed_val_eq
    (P : BasePrime) (r : Rank)
    (y : ArithmeticFiniteAdeleRing P ⊗[FunctionField P]
      (SplittingFunctionFieldFrobeniusFixedSubspace P r)) :
    ((LinearMap.tensorEqLocus
        (ArithmeticFiniteAdeleRing P) (ArithmeticFiniteAdeleRing P)
        (splittingFunctionFieldFrobenius P r).toLinearMap
        (LinearMap.id : SplittingFunctionField P r →ₗ[FunctionField P]
          SplittingFunctionField P r) y :
      LinearMap.eqLocus
        (arithmeticFiniteAdeleSplittingFrobeniusLinear P r)
        (arithmeticFiniteAdeleSplittingIdentityLinear P r)) :
        ArithmeticFiniteAdeleSplittingRing P r) =
      algebraMap (ArithmeticFiniteAdeleRing P)
        (ArithmeticFiniteAdeleSplittingRing P r)
          (arithmeticFiniteAdeleFixedTensorCollapse P r y) := by
  let lhs := (LinearMap.eqLocus
    (arithmeticFiniteAdeleSplittingFrobeniusLinear P r)
    (arithmeticFiniteAdeleSplittingIdentityLinear P r)).subtype.comp
      (LinearMap.tensorEqLocus
        (ArithmeticFiniteAdeleRing P) (ArithmeticFiniteAdeleRing P)
        (splittingFunctionFieldFrobenius P r).toLinearMap
        (LinearMap.id : SplittingFunctionField P r →ₗ[FunctionField P]
          SplittingFunctionField P r))
  let rhs := (Algebra.linearMap (ArithmeticFiniteAdeleRing P)
    (ArithmeticFiniteAdeleSplittingRing P r)).comp
      (arithmeticFiniteAdeleFixedTensorCollapse P r)
  have hmaps : lhs = rhs := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    change TensorProduct.tmul (FunctionField P) a x.1 =
      algebraMap (ArithmeticFiniteAdeleRing P)
        (ArithmeticFiniteAdeleSplittingRing P r)
          ((functionFieldEquivSplittingFrobeniusFixed P r).symm x • a)
    have hxdesc :=
      (functionFieldEquivSplittingFrobeniusFixed P r).apply_symm_apply x
    have hxval := congrArg Subtype.val hxdesc
    change TensorProduct.tmul (FunctionField P) a x.1 =
      TensorProduct.tmul (FunctionField P)
        ((functionFieldEquivSplittingFrobeniusFixed P r).symm x • a) 1
    change functionFieldEmbedding P r
        ((functionFieldEquivSplittingFrobeniusFixed P r).symm x) = x.1
      at hxval
    rw [← hxval]
    rw [show functionFieldEmbedding P r
          ((functionFieldEquivSplittingFrobeniusFixed P r).symm x) =
        (functionFieldEquivSplittingFrobeniusFixed P r).symm x •
          (1 : SplittingFunctionField P r) by
      change functionFieldEmbedding P r
          ((functionFieldEquivSplittingFrobeniusFixed P r).symm x) =
        functionFieldEmbedding P r
          ((functionFieldEquivSplittingFrobeniusFixed P r).symm x) * 1
      rw [mul_one]]
    rw [TensorProduct.tmul_smul]
    rfl
  exact DFunLike.congr_fun hmaps y

/-- Fixed-ring descent in the common finite-adelic splitting ring: every
Frobenius-fixed element comes from the finite-adele factor.  Flatness is
automatic because the finite adeles form a vector space over the global
function field. -/
theorem exists_eq_arithmeticFiniteAdele_algebraMap_of_frobenius_eq
    (P : BasePrime) (r : Rank)
    (x : ArithmeticFiniteAdeleSplittingRing P r)
    (hx : arithmeticFiniteAdeleSplittingFrobenius P r x = x) :
    ∃ a : ArithmeticFiniteAdeleRing P,
      algebraMap (ArithmeticFiniteAdeleRing P)
        (ArithmeticFiniteAdeleSplittingRing P r) a = x := by
  let xfixed : LinearMap.eqLocus
      (arithmeticFiniteAdeleSplittingFrobeniusLinear P r)
      (arithmeticFiniteAdeleSplittingIdentityLinear P r) := ⟨x, by
    rw [arithmeticFiniteAdeleSplittingFrobeniusLinear_eq,
      arithmeticFiniteAdeleSplittingIdentityLinear_eq]
    exact hx⟩
  let eqv := LinearMap.tensorEqLocusEquiv
    (ArithmeticFiniteAdeleRing P) (ArithmeticFiniteAdeleRing P)
    (splittingFunctionFieldFrobenius P r).toLinearMap
    (LinearMap.id : SplittingFunctionField P r →ₗ[FunctionField P]
      SplittingFunctionField P r)
  let y := eqv.symm xfixed
  refine ⟨arithmeticFiniteAdeleFixedTensorCollapse P r y, ?_⟩
  have hback := congrArg Subtype.val (eqv.apply_symm_apply xfixed)
  calc
    algebraMap (ArithmeticFiniteAdeleRing P)
        (ArithmeticFiniteAdeleSplittingRing P r)
          (arithmeticFiniteAdeleFixedTensorCollapse P r y) =
      ((LinearMap.tensorEqLocus
        (ArithmeticFiniteAdeleRing P) (ArithmeticFiniteAdeleRing P)
        (splittingFunctionFieldFrobenius P r).toLinearMap
        (LinearMap.id : SplittingFunctionField P r →ₗ[FunctionField P]
          SplittingFunctionField P r) y :
        LinearMap.eqLocus
          (arithmeticFiniteAdeleSplittingFrobeniusLinear P r)
          (arithmeticFiniteAdeleSplittingIdentityLinear P r)) :
          ArithmeticFiniteAdeleSplittingRing P r) :=
      (arithmeticFiniteAdeleTensorFixed_val_eq P r y).symm
    _ = x := hback

/-- The induced homomorphism from units of the finite-adelic cyclic algebra
to the corresponding general linear group over the common splitting ring. -/
noncomputable def arithmeticFiniteAdeleCyclicUnitToGL
    (P : BasePrime) (r : Rank) :
    (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ArithmeticFiniteAdeleSplittingRing P r) :=
  Units.map (arithmeticFiniteAdeleCyclicSplittingMap P r).toRingHom

/-- The concrete finite-adelic reduced norm, computed by the determinant of
the extended construction-owned splitting representation. -/
noncomputable def arithmeticFiniteAdeleCyclicReducedNorm
    (P : BasePrime) (r : Rank) :
    (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ →*
      (ArithmeticFiniteAdeleSplittingRing P r)ˣ :=
  Matrix.GeneralLinearGroup.det.comp
    (arithmeticFiniteAdeleCyclicUnitToGL P r)

private theorem arithmeticFiniteAdeleToSplittingRing_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective
      (algebraMap (ArithmeticFiniteAdeleRing P)
        (ArithmeticFiniteAdeleSplittingRing P r)) :=
  Algebra.TensorProduct.includeLeft_injective
    (R := FunctionField P)
    (S := ArithmeticFiniteAdeleRing P)
    (A := ArithmeticFiniteAdeleRing P)
    (B := SplittingFunctionField P r)
    (algebraMap (FunctionField P) (SplittingFunctionField P r)).injective

/-- The finite-adele-valued reduced norm of an arbitrary element, obtained
by the proved Frobenius fixed-ring descent of its splitting determinant. -/
noncomputable def arithmeticFiniteAdeleCyclicBaseReducedNormValue
    (P : BasePrime) (r : Rank)
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r) :
    ArithmeticFiniteAdeleRing P :=
  Classical.choose
    (exists_eq_arithmeticFiniteAdele_algebraMap_of_frobenius_eq P r
      (Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r x))
      (arithmeticFiniteAdeleCyclicSplitting_det_frobenius P r x))

theorem algebraMap_arithmeticFiniteAdeleCyclicBaseReducedNormValue
    (P : BasePrime) (r : Rank)
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r) :
    algebraMap (ArithmeticFiniteAdeleRing P)
        (ArithmeticFiniteAdeleSplittingRing P r)
        (arithmeticFiniteAdeleCyclicBaseReducedNormValue P r x) =
      Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r x) :=
  Classical.choose_spec
    (exists_eq_arithmeticFiniteAdele_algebraMap_of_frobenius_eq P r
      (Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r x))
      (arithmeticFiniteAdeleCyclicSplitting_det_frobenius P r x))

@[simp] theorem arithmeticFiniteAdeleCyclicBaseReducedNormValue_one
    (P : BasePrime) (r : Rank) :
    arithmeticFiniteAdeleCyclicBaseReducedNormValue P r 1 = 1 := by
  apply arithmeticFiniteAdeleToSplittingRing_injective P r
  rw [algebraMap_arithmeticFiniteAdeleCyclicBaseReducedNormValue]
  change Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r
      (1 : ArithmeticFiniteAdeleCyclicAlgebra P r)) =
    (1 : ArithmeticFiniteAdeleSplittingRing P r)
  rw [map_one, Matrix.det_one]

theorem arithmeticFiniteAdeleCyclicBaseReducedNormValue_mul
    (P : BasePrime) (r : Rank)
    (x y : ArithmeticFiniteAdeleCyclicAlgebra P r) :
    arithmeticFiniteAdeleCyclicBaseReducedNormValue P r (x * y) =
      arithmeticFiniteAdeleCyclicBaseReducedNormValue P r x *
        arithmeticFiniteAdeleCyclicBaseReducedNormValue P r y := by
  apply arithmeticFiniteAdeleToSplittingRing_injective P r
  calc
    algebraMap (ArithmeticFiniteAdeleRing P)
        (ArithmeticFiniteAdeleSplittingRing P r)
        (arithmeticFiniteAdeleCyclicBaseReducedNormValue P r (x * y)) =
      Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r (x * y)) :=
        algebraMap_arithmeticFiniteAdeleCyclicBaseReducedNormValue P r (x * y)
    _ = Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r x) *
        Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r y) := by
      rw [map_mul, Matrix.det_mul]
    _ = algebraMap (ArithmeticFiniteAdeleRing P)
        (ArithmeticFiniteAdeleSplittingRing P r)
          (arithmeticFiniteAdeleCyclicBaseReducedNormValue P r x *
            arithmeticFiniteAdeleCyclicBaseReducedNormValue P r y) := by
      rw [map_mul,
        algebraMap_arithmeticFiniteAdeleCyclicBaseReducedNormValue,
        algebraMap_arithmeticFiniteAdeleCyclicBaseReducedNormValue]

/-- The genuine base-finite-adele-valued reduced norm on units. -/
noncomputable def arithmeticFiniteAdeleCyclicBaseReducedNorm
    (P : BasePrime) (r : Rank) :
    (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ →*
      (ArithmeticFiniteAdeleRing P)ˣ where
  toFun u :=
    ⟨arithmeticFiniteAdeleCyclicBaseReducedNormValue P r u,
      arithmeticFiniteAdeleCyclicBaseReducedNormValue P r
        ((u⁻¹ : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
          ArithmeticFiniteAdeleCyclicAlgebra P r), by
        rw [← arithmeticFiniteAdeleCyclicBaseReducedNormValue_mul]
        have hu : (u : ArithmeticFiniteAdeleCyclicAlgebra P r) *
            ((u⁻¹ : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
              ArithmeticFiniteAdeleCyclicAlgebra P r) = 1 :=
          congrArg Units.val (mul_inv_cancel u)
        rw [hu, arithmeticFiniteAdeleCyclicBaseReducedNormValue_one], by
        rw [← arithmeticFiniteAdeleCyclicBaseReducedNormValue_mul]
        have hu :
            ((u⁻¹ : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
              ArithmeticFiniteAdeleCyclicAlgebra P r) *
              (u : ArithmeticFiniteAdeleCyclicAlgebra P r) = 1 :=
          congrArg Units.val (inv_mul_cancel u)
        rw [hu, arithmeticFiniteAdeleCyclicBaseReducedNormValue_one]⟩
  map_one' := by
    apply Units.ext
    exact arithmeticFiniteAdeleCyclicBaseReducedNormValue_one P r
  map_mul' u v := by
    apply Units.ext
    exact arithmeticFiniteAdeleCyclicBaseReducedNormValue_mul P r u v

/-- The splitting-ring determinant is exactly scalar extension of the
base-finite-adele-valued reduced norm. -/
theorem arithmeticFiniteAdeleCyclicReducedNorm_eq_baseChange
    (P : BasePrime) (r : Rank)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    arithmeticFiniteAdeleCyclicReducedNorm P r u =
      Units.map
        (algebraMap (ArithmeticFiniteAdeleRing P)
          (ArithmeticFiniteAdeleSplittingRing P r))
        (arithmeticFiniteAdeleCyclicBaseReducedNorm P r u) := by
  apply Units.ext
  exact
    (algebraMap_arithmeticFiniteAdeleCyclicBaseReducedNormValue P r u).symm

theorem arithmeticFiniteAdeleCyclicReducedNorm_eq_one_iff_base
    (P : BasePrime) (r : Rank)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    arithmeticFiniteAdeleCyclicReducedNorm P r u = 1 ↔
      arithmeticFiniteAdeleCyclicBaseReducedNorm P r u = 1 := by
  rw [arithmeticFiniteAdeleCyclicReducedNorm_eq_baseChange]
  constructor
  · intro h
    apply Units.ext
    apply arithmeticFiniteAdeleToSplittingRing_injective P r
    exact congrArg Units.val h
  · intro h
    rw [h, map_one]

/-- The actual finite-adelic `SL₁(D)`: the kernel of the concrete reduced
norm on units of the finite-adelic scalar extension of the cyclic algebra. -/
noncomputable def ArithmeticFiniteAdeleCyclicNormOne
    (P : BasePrime) (r : Rank) :
    Subgroup (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ :=
  (arithmeticFiniteAdeleCyclicReducedNorm P r).ker

@[simp] theorem arithmeticFiniteAdeleCyclicSplittingMap_diagonal
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    arithmeticFiniteAdeleCyclicSplittingMap P r
        (cyclicAlgebraToArithmeticFiniteAdeles P r x) =
      (splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r).mapMatrix
        x.1 := by
  rw [cyclicAlgebraToArithmeticFiniteAdeles_apply,
    arithmeticFiniteAdeleCyclicSplittingMap,
    Algebra.TensorProduct.lift_tmul]
  simp [cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix]

/-- Compatibility of finite-adelic and global reduced norms on diagonal
global units. -/
theorem arithmeticFiniteAdeleCyclicReducedNorm_diagonal
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    arithmeticFiniteAdeleCyclicReducedNorm P r
        (cyclicAlgebraUnitToArithmeticFiniteAdeles P r u) =
      Units.map
        (splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r).toRingHom.toMonoidHom
        (cyclicAlgebraSplitReducedNorm P r u) := by
  apply Units.ext
  change Matrix.det
      (arithmeticFiniteAdeleCyclicSplittingMap P r
        (cyclicAlgebraToArithmeticFiniteAdeles P r
          (u : CyclicAlgebra P r))) =
    splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r
      (Matrix.det (u : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)))
  rw [arithmeticFiniteAdeleCyclicSplittingMap_diagonal]
  exact
    ((splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r).map_det
      (u : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r))).symm

/-- Diagonal localization sends every intrinsic global reduced-norm-one
point to the concrete finite-adelic reduced-norm-one group. -/
noncomputable def cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne
    (P : BasePrime) (r : Rank) :
    CyclicAlgebraNormOne P r →* ArithmeticFiniteAdeleCyclicNormOne P r where
  toFun u := ⟨cyclicAlgebraUnitToArithmeticFiniteAdeles P r u, by
    change arithmeticFiniteAdeleCyclicReducedNorm P r
      (cyclicAlgebraUnitToArithmeticFiniteAdeles P r u) = 1
    rw [arithmeticFiniteAdeleCyclicReducedNorm_diagonal]
    change Units.map
      (splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r).toRingHom.toMonoidHom
        (cyclicAlgebraSplitReducedNorm P r u) = 1
    have hu : (u : (CyclicAlgebra P r)ˣ) ∈
        CyclicAlgebraSplitNormOne P r := by
      rw [cyclicAlgebraSplitNormOne_eq_normOne]
      exact u.property
    rw [hu, map_one]⟩
  map_one' := Subtype.ext
    (map_one (cyclicAlgebraUnitToArithmeticFiniteAdeles P r))
  map_mul' u v := Subtype.ext
    (map_mul (cyclicAlgebraUnitToArithmeticFiniteAdeles P r)
      (u : (CyclicAlgebra P r)ˣ) (v : (CyclicAlgebra P r)ˣ))

/-- The integral chart inside the concrete finite-adelic `SL₁(D)`.  Both a
unit and its inverse are required to have integral cyclic coordinates, so
this is exactly the integral-unit condition used by the arithmetic order. -/
noncomputable def ArithmeticFiniteAdeleCyclicIntegralNormOneSet
    (P : BasePrime) (r : Rank) :
    Set (ArithmeticFiniteAdeleCyclicNormOne P r) :=
  {u |
    ((u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
        ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r ∧
    (((u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ)⁻¹ :
        (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
        ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r}

/-- Membership in the all-integral norm-one chart is exactly the absence of
denominator places for the adelic unit and its inverse. -/
theorem mem_arithmeticFiniteAdeleCyclicIntegralNormOneSet_iff_denominatorPlaces_empty
    (P : BasePrime) (r : Rank)
    (u : ArithmeticFiniteAdeleCyclicNormOne P r) :
    u ∈ ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r ↔
      arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r u = ∅ := by
  change
    ((u.1 : ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
        ArithmeticFiniteAdeleCyclicIntegralLattice P r ∧
      (↑(u.1⁻¹) : ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
        ArithmeticFiniteAdeleCyclicIntegralLattice P r) ↔ _
  rw [arithmeticFiniteAdeleCyclic_mem_integralLattice_iff_denominatorPlaces_empty,
    arithmeticFiniteAdeleCyclic_mem_integralLattice_iff_denominatorPlaces_empty]
  simp [arithmeticFiniteAdeleCyclicUnitDenominatorPlaces]

/-- Denominator support of an intrinsic global norm-one point after its
diagonal embedding in the arithmetic finite adeles. -/
noncomputable def cyclicAlgebraNormOneDenominatorPlaces
    (P : BasePrime) (r : Rank) (u : CyclicAlgebraNormOne P r) :
    Set (IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :=
  arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r
    (cyclicAlgebraUnitToArithmeticFiniteAdeles P r u)

theorem cyclicAlgebraNormOneDenominatorPlaces_finite
    (P : BasePrime) (r : Rank) (u : CyclicAlgebraNormOne P r) :
    (cyclicAlgebraNormOneDenominatorPlaces P r u).Finite :=
  arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_finite P r
    (cyclicAlgebraUnitToArithmeticFiniteAdeles P r u)

theorem cyclicAlgebraNormOneDenominatorPlaces_eq_empty_iff
    (P : BasePrime) (r : Rank) (u : CyclicAlgebraNormOne P r) :
    cyclicAlgebraNormOneDenominatorPlaces P r u = ∅ ↔
      cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r u ∈
        ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r := by
  rw [mem_arithmeticFiniteAdeleCyclicIntegralNormOneSet_iff_denominatorPlaces_empty]
  rfl

/-- Assemble a unit of the actual order from independently verified order
lifts of a cyclic-algebra unit and its inverse. -/
private noncomputable def cartwrightStegerOrderUnitOfLifts
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ)
    (v vInv : CartwrightStegerOrder P r)
    (hv : cartwrightStegerOrderToCyclicAlgebra P r v =
      (u : CyclicAlgebra P r))
    (hvInv : cartwrightStegerOrderToCyclicAlgebra P r vInv =
      (↑(u⁻¹) : CyclicAlgebra P r)) :
    (CartwrightStegerOrder P r)ˣ where
  val := v
  inv := vInv
  val_inv := by
    apply cartwrightStegerOrderToCyclicAlgebra_injective P r
    calc
      cartwrightStegerOrderToCyclicAlgebra P r (v * vInv) =
          cartwrightStegerOrderToCyclicAlgebra P r v *
            cartwrightStegerOrderToCyclicAlgebra P r vInv :=
        map_mul (cartwrightStegerOrderToCyclicAlgebra P r) v vInv
      _ = (u : CyclicAlgebra P r) *
          (↑(u⁻¹) : CyclicAlgebra P r) :=
        congrArg₂ (· * ·) hv hvInv
      _ = 1 := u.val_inv
      _ = cartwrightStegerOrderToCyclicAlgebra P r 1 :=
        (map_one (cartwrightStegerOrderToCyclicAlgebra P r)).symm
  inv_val := by
    apply cartwrightStegerOrderToCyclicAlgebra_injective P r
    calc
      cartwrightStegerOrderToCyclicAlgebra P r (vInv * v) =
          cartwrightStegerOrderToCyclicAlgebra P r vInv *
            cartwrightStegerOrderToCyclicAlgebra P r v :=
        map_mul (cartwrightStegerOrderToCyclicAlgebra P r) vInv v
      _ = (↑(u⁻¹) : CyclicAlgebra P r) *
          (u : CyclicAlgebra P r) :=
        congrArg₂ (· * ·) hvInv hv
      _ = 1 := u.inv_val
      _ = cartwrightStegerOrderToCyclicAlgebra P r 1 :=
        (map_one (cartwrightStegerOrderToCyclicAlgebra P r)).symm

private theorem orderUnitToCyclicUnit_orderUnitOfLifts
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ)
    (v vInv : CartwrightStegerOrder P r)
    (hv : cartwrightStegerOrderToCyclicAlgebra P r v =
      (u : CyclicAlgebra P r))
    (hvInv : cartwrightStegerOrderToCyclicAlgebra P r vInv =
      (↑(u⁻¹) : CyclicAlgebra P r)) :
    orderUnitToCyclicUnit P r
        (cartwrightStegerOrderUnitOfLifts P r u v vInv hv hvInv) = u := by
  apply Units.ext
  exact hv

/-- A global cyclic-algebra unit whose value and inverse are both integral
at every finite place away from the two inverted places comes from a
genuine unit of the construction-owned Cartwright--Steger order. -/
theorem exists_cartwrightStegerOrderUnit_of_finiteAdele_integral
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ)
    (hu : (cyclicAlgebraUnitToArithmeticFiniteAdeles P r u :
        ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r)
    (huInv : (cyclicAlgebraUnitToArithmeticFiniteAdeles P r u⁻¹ :
        ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r) :
    ∃ v : (CartwrightStegerOrder P r)ˣ,
      orderUnitToCyclicUnit P r v = u := by
  have huSpan : (u : CyclicAlgebra P r) ∈ arithmeticCyclicSpan P r :=
    (cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice_iff
      P r (u : CyclicAlgebra P r)).mp hu
  have huInvSpan : (↑(u⁻¹) : CyclicAlgebra P r) ∈
      arithmeticCyclicSpan P r :=
    (cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice_iff
      P r (↑(u⁻¹) : CyclicAlgebra P r)).mp huInv
  obtain ⟨v, hv⟩ :=
    exists_cartwrightStegerOrder_of_mem_arithmeticCyclicSpan
      P r (u : CyclicAlgebra P r) huSpan
  obtain ⟨vInv, hvInv⟩ :=
    exists_cartwrightStegerOrder_of_mem_arithmeticCyclicSpan
      P r (↑(u⁻¹) : CyclicAlgebra P r) huInvSpan
  exact ⟨cartwrightStegerOrderUnitOfLifts P r u v vInv hv hvInv,
    orderUnitToCyclicUnit_orderUnitOfLifts P r u v vInv hv hvInv⟩

/-- Every genuine unit of the construction-owned arithmetic order lies in
the all-integral finite-adelic lattice after diagonal scalar extension. -/
theorem orderUnitToArithmeticFiniteAdeles_mem_integralLattice
    (P : BasePrime) (r : Rank) (u : (CartwrightStegerOrder P r)ˣ) :
    (cyclicAlgebraUnitToArithmeticFiniteAdeles P r
        (orderUnitToCyclicUnit P r u) :
      ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
        ArithmeticFiniteAdeleCyclicIntegralLattice P r := by
  rw [cyclicAlgebraUnitToArithmeticFiniteAdeles_coe]
  apply cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice
  exact cartwrightStegerOrderToCyclic_mem_arithmeticCyclicSpan P r u.1

/-- Diagonal finite-adelic localization of intrinsic global reduced-norm-one
points.  The domain is the actual norm-one kernel of the cyclic division
algebra, not an ordinary split special-linear replacement. -/
noncomputable def cyclicAlgebraNormOneToArithmeticFiniteAdeles
    (P : BasePrime) (r : Rank) :
    CyclicAlgebraNormOne P r →*
      (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ :=
  (cyclicAlgebraUnitToArithmeticFiniteAdeles P r).comp
    (CyclicAlgebraNormOne P r).subtype

/-- Every construction-owned integral norm-one point satisfies the
all-place integral adelic condition. -/
theorem orderNormOneInnerFormToArithmeticFiniteAdeles_mem_integralLattice
    (P : BasePrime) (r : Rank) (s : OrderNormOneInnerForm P r) :
    (cyclicAlgebraNormOneToArithmeticFiniteAdeles P r
        (orderNormOneInnerFormToCyclicAlgebraNormOne P r s) :
      ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
        ArithmeticFiniteAdeleCyclicIntegralLattice P r := by
  change (cyclicAlgebraUnitToArithmeticFiniteAdeles P r
      (orderUnitToCyclicUnit P r
        (orderNormOneInnerFormToOrderUnits P r s)) :
    ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r
  exact orderUnitToArithmeticFiniteAdeles_mem_integralLattice P r
    (orderNormOneInnerFormToOrderUnits P r s)

/-- Concrete adelic intersection for the source group `SL₁(D)`: a global
reduced-norm-one point whose value and inverse are integral at every finite
place away from the two inverted Cartwright--Steger places comes from the
actual integral norm-one inner form. -/
theorem exists_orderNormOneInnerForm_of_finiteAdele_integral
    (P : BasePrime) (r : Rank) (u : CyclicAlgebraNormOne P r)
    (hu : (cyclicAlgebraNormOneToArithmeticFiniteAdeles P r u :
        ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r)
    (huInv : (cyclicAlgebraUnitToArithmeticFiniteAdeles P r
        ((u : (CyclicAlgebra P r)ˣ)⁻¹) :
        ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r) :
    ∃ s : OrderNormOneInnerForm P r,
      orderNormOneInnerFormToCyclicAlgebraNormOne P r s = u := by
  obtain ⟨v, hv⟩ :=
    exists_cartwrightStegerOrderUnit_of_finiteAdele_integral
      P r (u : (CyclicAlgebra P r)ˣ) hu huInv
  have hvNorm : v ∈ CartwrightStegerBaseNormOneOrderUnits P r := by
    change cyclicAlgebraReducedNorm P r
      (orderUnitToCyclicUnit P r v) = 1
    rw [hv]
    exact u.property
  let vn : CartwrightStegerBaseNormOneOrderUnits P r := ⟨v, hvNorm⟩
  let s : OrderNormOneInnerForm P r :=
    (orderNormOneInnerFormEquivBaseNormOneOrderUnits P r).symm vn
  refine ⟨s, ?_⟩
  have hs : orderNormOneInnerFormToBaseNormOneOrderUnits P r s = vn :=
    (orderNormOneInnerFormEquivBaseNormOneOrderUnits P r).apply_symm_apply vn
  have hsVal : orderNormOneInnerFormToOrderUnits P r s = v :=
    congrArg (fun w : CartwrightStegerBaseNormOneOrderUnits P r =>
      (w : (CartwrightStegerOrder P r)ˣ)) hs
  apply Subtype.ext
  change orderUnitToCyclicUnit P r
      (orderNormOneInnerFormToOrderUnits P r s) =
    (u : (CyclicAlgebra P r)ˣ)
  rw [hsVal, hv]

/-- Exact group-point form of the adelic intersection used in the source:
a global point of the concrete `SL₁(D)` lies in the integral finite-adelic
subgroup away from the two inverted Cartwright--Steger places (together
with its inverse) if and only if it is the image of an actual point of the
construction-owned integral norm-one inner form. -/
theorem cyclicAlgebraNormOne_finiteAdele_integral_iff_mem_range
    (P : BasePrime) (r : Rank) (u : CyclicAlgebraNormOne P r) :
    ((cyclicAlgebraNormOneToArithmeticFiniteAdeles P r u :
          ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
        ArithmeticFiniteAdeleCyclicIntegralLattice P r ∧
      (cyclicAlgebraUnitToArithmeticFiniteAdeles P r
          ((u : (CyclicAlgebra P r)ˣ)⁻¹) :
          ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
        ArithmeticFiniteAdeleCyclicIntegralLattice P r) ↔
      u ∈ (orderNormOneInnerFormToCyclicAlgebraNormOne P r).range := by
  constructor
  · rintro ⟨hu, huInv⟩
    exact exists_orderNormOneInnerForm_of_finiteAdele_integral
      P r u hu huInv
  · rintro ⟨s, rfl⟩
    constructor
    · exact
        orderNormOneInnerFormToArithmeticFiniteAdeles_mem_integralLattice
          P r s
    · have hsInv :=
        orderNormOneInnerFormToArithmeticFiniteAdeles_mem_integralLattice
          P r s⁻¹
      simp only [map_inv] at hsInv ⊢
      exact hsInv

/-- Exact preimage form of `G(k) ∩ U = G(R)` for the finite-adelic integral
chart: a global rational point lands in the chart precisely when it comes
from the construction-owned integral norm-one inner form. -/
theorem cyclicAlgebraNormOne_preimage_integralNormOneSet
    (P : BasePrime) (r : Rank) (u : CyclicAlgebraNormOne P r) :
    cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r u ∈
        ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r ↔
      u ∈ (orderNormOneInnerFormToCyclicAlgebraNormOne P r).range := by
  exact cyclicAlgebraNormOne_finiteAdele_integral_iff_mem_range P r u

/-- Diagonal finite-adelic localization of the actual integral norm-one
inner form. -/
noncomputable def orderNormOneInnerFormToArithmeticFiniteAdeleNormOne
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r →*
      ArithmeticFiniteAdeleCyclicNormOne P r :=
  (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r).comp
    (orderNormOneInnerFormToCyclicAlgebraNormOne P r)

/-- Exact image form of the arithmetic intersection: restricting the global
rational norm-one points to the adelic integral chart gives precisely the
finite-adelic image of the construction-owned integral norm-one inner form. -/
theorem image_preimage_arithmeticFiniteAdeleCyclicIntegralNormOneSet
    (P : BasePrime) (r : Rank) :
    cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r ''
        (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r) ⁻¹'
          ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r =
      Set.range (orderNormOneInnerFormToArithmeticFiniteAdeleNormOne P r) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    change cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r u ∈
      ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r at hu
    rw [cyclicAlgebraNormOne_preimage_integralNormOneSet] at hu
    obtain ⟨s, rfl⟩ := hu
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    refine ⟨orderNormOneInnerFormToCyclicAlgebraNormOne P r s, ?_, rfl⟩
    change cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r
        (orderNormOneInnerFormToCyclicAlgebraNormOne P r s) ∈
      ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r
    rw [cyclicAlgebraNormOne_preimage_integralNormOneSet]
    exact ⟨s, rfl⟩

/-- The integral norm-one inner form embeds faithfully in the global
cyclic-algebra norm-one group.  Combined with the preceding range theorem,
this makes the source equality `G(k) ∩ U = G(R)` an identification rather
than merely an existence statement. -/
theorem orderNormOneInnerFormToCyclicAlgebraNormOne_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective
      (orderNormOneInnerFormToCyclicAlgebraNormOne P r) := by
  intro s t hst
  apply orderNormOneInnerFormToOrderUnits_injective P r
  apply Units.ext
  apply cartwrightStegerOrderToCyclicAlgebra_injective P r
  exact congrArg
    (fun u : CyclicAlgebraNormOne P r =>
      (((u : (CyclicAlgebra P r)ˣ) : CyclicAlgebra P r))) hst

/-- Group-level identification of the actual integral norm-one inner form
with its subgroup of global cyclic-algebra norm-one points.  The carrier of
the codomain is characterized by finite-adelic integrality in
`cyclicAlgebraNormOne_finiteAdele_integral_iff_mem_range`. -/
noncomputable def orderNormOneInnerFormEquivGlobalIntegralRange
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r ≃*
      (orderNormOneInnerFormToCyclicAlgebraNormOne P r).range :=
  MulEquiv.ofBijective
    (orderNormOneInnerFormToCyclicAlgebraNormOne P r).rangeRestrict
    ⟨fun _ _ h =>
        orderNormOneInnerFormToCyclicAlgebraNormOne_injective P r
          (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩

/-- The underlying global cyclic-algebra point of a genuine integral
norm-one inner-form element. -/
noncomputable def orderNormOneInnerFormCyclicAlgebraPoint
    (P : BasePrime) (r : Rank) (s : OrderNormOneInnerForm P r) :
    CyclicAlgebra P r :=
  (((orderNormOneInnerFormToCyclicAlgebraNormOne P r s :
      CyclicAlgebraNormOne P r) : (CyclicAlgebra P r)ˣ) :
    CyclicAlgebra P r)

/-- Its global splitting-field matrix is exactly the construction's
constant-arithmetic matrix after scalar extension. -/
theorem orderNormOneInnerFormCyclicAlgebraPoint_coe
    (P : BasePrime) (r : Rank) (s : OrderNormOneInnerForm P r) :
    (orderNormOneInnerFormCyclicAlgebraPoint P r s :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) =
      ((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ConstantArithmeticRing P r)).map
        (constantArithmeticToSplittingFunctionField P r) := by
  rfl

/-- Integral norm-one inner-form points belong to the arithmetic cyclic
span through their actual order-unit descent. -/
theorem orderNormOneInnerFormCyclicAlgebraPoint_mem_arithmeticCyclicSpan
    (P : BasePrime) (r : Rank) (s : OrderNormOneInnerForm P r) :
    orderNormOneInnerFormCyclicAlgebraPoint P r s ∈
      arithmeticCyclicSpan P r := by
  change cartwrightStegerOrderToCyclicAlgebra P r
      (orderNormOneInnerFormToOrderUnits P r s).1 ∈
        arithmeticCyclicSpan P r
  exact cartwrightStegerOrderToCyclic_mem_arithmeticCyclicSpan P r
    (orderNormOneInnerFormToOrderUnits P r s).1

/-- For a genuine integral norm-one inner-form point, reconstruction from
its arithmetic cyclic coordinates recovers its original construction-owned
constant-arithmetic matrix. -/
theorem arithmeticCyclicCoordinateMatrix_orderNormOneInnerForm
    (P : BasePrime) (r : Rank) (s : OrderNormOneInnerForm P r) :
    arithmeticCyclicCoordinateMatrix P r
        (orderNormOneInnerFormCyclicAlgebraPoint P r s)
        (orderNormOneInnerFormCyclicAlgebraPoint_mem_arithmeticCyclicSpan
          P r s) =
      ((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) := by
  apply Matrix.map_injective
    (constantArithmeticToSplittingFunctionField_injective P r)
  change (arithmeticCyclicCoordinateMatrix P r
      (orderNormOneInnerFormCyclicAlgebraPoint P r s)
      (orderNormOneInnerFormCyclicAlgebraPoint_mem_arithmeticCyclicSpan
        P r s)).map (constantArithmeticToSplittingFunctionField P r) =
    (((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ConstantArithmeticRing P r)).map
          (constantArithmeticToSplittingFunctionField P r))
  rw [arithmeticCyclicCoordinateMatrix_to_global]
  exact orderNormOneInnerFormCyclicAlgebraPoint_coe P r s

/-- Evaluation of an arithmetic finite adele at one genuine height-one
place. -/
noncomputable def arithmeticFiniteAdeleAt
    (P : BasePrime)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    ArithmeticFiniteAdeleRing P →+*
      v.adicCompletion (FunctionField P) where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem arithmeticFiniteAdeleAt_diagonal
    (P : BasePrime)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : FunctionField P) :
    arithmeticFiniteAdeleAt P v
        (functionFieldToArithmeticFiniteAdeles P x) =
      algebraMap (FunctionField P)
        (v.adicCompletion (FunctionField P)) x :=
  rfl

/-- Evaluation at an arbitrary arithmetic finite place as a global-function-
field algebra map. -/
noncomputable def arithmeticFiniteAdeleAtAlgHom
    (P : BasePrime)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    ArithmeticFiniteAdeleRing P →ₐ[FunctionField P]
      v.adicCompletion (FunctionField P) where
  __ := arithmeticFiniteAdeleAt P v
  commutes' := arithmeticFiniteAdeleAt_diagonal P v

/-- The splitting ring after evaluation at one arbitrary arithmetic finite
place. -/
noncomputable abbrev ArithmeticAdicSplittingRing
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :=
  TensorProduct (FunctionField P)
    (v.adicCompletion (FunctionField P)) (SplittingFunctionField P r)

/-- Evaluate the finite-adele factor of the common splitting ring at one
arithmetic finite place while retaining the global splitting factor. -/
noncomputable def arithmeticFiniteAdeleSplittingRingAt
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    ArithmeticFiniteAdeleSplittingRing P r →ₐ[FunctionField P]
      ArithmeticAdicSplittingRing P r v :=
  Algebra.TensorProduct.map (arithmeticFiniteAdeleAtAlgHom P v)
    (AlgHom.id (FunctionField P) (SplittingFunctionField P r))

@[simp] theorem arithmeticFiniteAdeleSplittingRingAt_left
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (a : ArithmeticFiniteAdeleRing P) :
    arithmeticFiniteAdeleSplittingRingAt P r v
        (algebraMap (ArithmeticFiniteAdeleRing P)
          (ArithmeticFiniteAdeleSplittingRing P r) a) =
      algebraMap (v.adicCompletion (FunctionField P))
        (ArithmeticAdicSplittingRing P r v)
          (arithmeticFiniteAdeleAt P v a) := by
  change arithmeticFiniteAdeleSplittingRingAt P r v
      (TensorProduct.tmul (FunctionField P) a 1) = _
  simp [arithmeticFiniteAdeleSplittingRingAt,
    arithmeticFiniteAdeleAtAlgHom]
  rfl

/-- At every arithmetic finite place, scalar extension of the corresponding
coordinate of the descended reduced norm equals the determinant of the
placewise splitting matrix. -/
theorem arithmeticFiniteAdeleCyclicBaseReducedNorm_atPlace
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    algebraMap (v.adicCompletion (FunctionField P))
        (ArithmeticAdicSplittingRing P r v)
        (arithmeticFiniteAdeleAt P v
          (arithmeticFiniteAdeleCyclicBaseReducedNorm P r u)) =
      Matrix.det
        ((arithmeticFiniteAdeleCyclicSplittingMap P r
          (u : ArithmeticFiniteAdeleCyclicAlgebra P r)).map
            (arithmeticFiniteAdeleSplittingRingAt P r v)) := by
  calc
    algebraMap (v.adicCompletion (FunctionField P))
        (ArithmeticAdicSplittingRing P r v)
        (arithmeticFiniteAdeleAt P v
          (arithmeticFiniteAdeleCyclicBaseReducedNorm P r u)) =
      arithmeticFiniteAdeleSplittingRingAt P r v
        (algebraMap (ArithmeticFiniteAdeleRing P)
          (ArithmeticFiniteAdeleSplittingRing P r)
          (arithmeticFiniteAdeleCyclicBaseReducedNorm P r u)) := by
        symm
        exact arithmeticFiniteAdeleSplittingRingAt_left P r v _
    _ = arithmeticFiniteAdeleSplittingRingAt P r v
        (Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r
          (u : ArithmeticFiniteAdeleCyclicAlgebra P r))) := by
      change arithmeticFiniteAdeleSplittingRingAt P r v
        (algebraMap (ArithmeticFiniteAdeleRing P)
          (ArithmeticFiniteAdeleSplittingRing P r)
            (arithmeticFiniteAdeleCyclicBaseReducedNormValue P r
              (u : ArithmeticFiniteAdeleCyclicAlgebra P r))) = _
      rw [algebraMap_arithmeticFiniteAdeleCyclicBaseReducedNormValue]
    _ = _ :=
      (arithmeticFiniteAdeleSplittingRingAt P r v).map_det
        (arithmeticFiniteAdeleCyclicSplittingMap P r
          (u : ArithmeticFiniteAdeleCyclicAlgebra P r))

/-! ## The selected congruence place -/

/-- The selected congruence kernel is maximal because its construction-owned
residue map is onto a field. -/
noncomputable instance indexCongruenceIdealIsMaximal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexCongruenceIdeal P r level).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective
    (indexArithmeticEval P r level)
    (indexArithmeticEval_surjective P r level)

/-- The closed-point polynomial remains nonzero after passing to the actual
S-arithmetic coefficient ring. -/
theorem indexPlacePolynomial_arithmetic_ne_zero
    (P : BasePrime) (r : Rank) (level : Nat) :
    algebraMap (PolynomialRing P) (ArithmeticRing P)
        (indexPlacePolynomial P r level) ≠ 0 := by
  rw [map_ne_zero_iff _ (IsLocalization.injective (ArithmeticRing P)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (arithmeticLocalizationElement_ne_zero P)))]
  exact (indexPlacePolynomial_irreducible P r level).ne_zero

/-- The chosen irreducible polynomial lies in the construction's congruence
kernel. -/
theorem indexPlacePolynomial_mem_indexCongruenceIdeal
    (P : BasePrime) (r : Rank) (level : Nat) :
    algebraMap (PolynomialRing P) (ArithmeticRing P)
        (indexPlacePolynomial P r level) ∈
      IndexCongruenceIdeal P r level := by
  change indexArithmeticEval P r level
      (algebraMap (PolynomialRing P) (ArithmeticRing P)
        (indexPlacePolynomial P r level)) = 0
  rw [indexArithmeticEval_algebraMap]
  exact minpoly.aeval (BaseField P) (indexPlaceY P r level)

theorem indexCongruenceIdeal_ne_bot
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceIdeal P r level ≠ ⊥ := by
  intro hbot
  have hp := indexPlacePolynomial_mem_indexCongruenceIdeal P r level
  rw [hbot, Ideal.mem_bot] at hp
  exact indexPlacePolynomial_arithmetic_ne_zero P r level hp

/-- The actual selected closed point of
`F_q[y,1/y,1/(1+y)]`; its ideal is definitionally the kernel of the genuine
congruence map. -/
noncomputable def indexCongruencePlace
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P) where
  asIdeal := IndexCongruenceIdeal P r level
  isPrime := RingHom.ker_isPrime (indexArithmeticEval P r level)
  ne_bot := indexCongruenceIdeal_ne_bot P r level

@[simp] theorem indexCongruencePlace_asIdeal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (indexCongruencePlace P r level).asIdeal =
      IndexCongruenceIdeal P r level :=
  rfl

/-- The abstract adic completion appearing as the selected coordinate of
the construction's finite adele ring. -/
noncomputable abbrev IndexCongruenceAdicCompletion
    (P : BasePrime) (r : Rank) (level : Nat) :=
  (indexCongruencePlace P r level).adicCompletion (FunctionField P)

/-- The canonical integer ring inside the selected abstract adic
completion. -/
noncomputable abbrev IndexCongruenceAdicIntegers
    (P : BasePrime) (r : Rank) (level : Nat) :=
  (indexCongruencePlace P r level).adicCompletionIntegers (FunctionField P)

/-- Projection of an arithmetic finite adele to the selected congruence
place. -/
noncomputable def arithmeticFiniteAdeleAtIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdeleRing P →+*
      IndexCongruenceAdicCompletion P r level :=
  arithmeticFiniteAdeleAt P (indexCongruencePlace P r level)

/-- A genuine finite adele supported only at the selected congruence place.
This is the concrete one-place section needed to insert a local lifting into
the finite restricted product; all other coordinates are zero, hence are
automatically integral. -/
noncomputable def arithmeticFiniteAdeleSupportedAtIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexCongruenceAdicCompletion P r level) :
    ArithmeticFiniteAdeleRing P := by
  classical
  refine ⟨Pi.single (indexCongruencePlace P r level) x, ?_⟩
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset
    (Set.finite_singleton (indexCongruencePlace P r level))
  intro v hv
  simp only [Set.mem_singleton_iff]
  by_contra hne
  apply hv
  rw [Pi.single_eq_of_ne hne]
  exact (v.adicCompletionIntegers (FunctionField P)).zero_mem

@[simp] theorem arithmeticFiniteAdeleAtIndexPlace_supported
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexCongruenceAdicCompletion P r level) :
    arithmeticFiniteAdeleAtIndexPlace P r level
        (arithmeticFiniteAdeleSupportedAtIndexPlace P r level x) = x := by
  classical
  simp [arithmeticFiniteAdeleAtIndexPlace, arithmeticFiniteAdeleAt,
    arithmeticFiniteAdeleSupportedAtIndexPlace]
  exact Pi.single_eq_same (indexCongruencePlace P r level) x

/-- A scalar supported at the selected congruence place evaluates to zero
at every other arithmetic finite place. -/
theorem arithmeticFiniteAdeleAt_supportedAtIndexPlace_of_ne
    (P : BasePrime) (r : Rank) (level : Nat)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hv : v ≠ indexCongruencePlace P r level)
    (x : IndexCongruenceAdicCompletion P r level) :
    arithmeticFiniteAdeleAt P v
        (arithmeticFiniteAdeleSupportedAtIndexPlace P r level x) = 0 := by
  classical
  change Pi.single (indexCongruencePlace P r level) x v = 0
  rw [Pi.single_eq_of_ne hv]

/-- A one-place supported scalar is integral at every arithmetic finite
place exactly when its selected adic coordinate is integral. -/
theorem arithmeticFiniteAdeleSupportedAtIndexPlace_mem_integral_iff
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexCongruenceAdicCompletion P r level) :
    arithmeticFiniteAdeleSupportedAtIndexPlace P r level x ∈
        ArithmeticIntegralFiniteAdeles P ↔
      x ∈ IndexCongruenceAdicIntegers P r level := by
  classical
  constructor
  · intro hx
    have hselected := hx (indexCongruencePlace P r level)
    change Pi.single (indexCongruencePlace P r level) x
        (indexCongruencePlace P r level) ∈
      IndexCongruenceAdicIntegers P r level at hselected
    rw [Pi.single_eq_same] at hselected
    exact hselected
  · intro hx v
    by_cases hv : v = indexCongruencePlace P r level
    · subst v
      change Pi.single (indexCongruencePlace P r level) x
          (indexCongruencePlace P r level) ∈
        IndexCongruenceAdicIntegers P r level
      rw [Pi.single_eq_same]
      exact hx
    · change Pi.single (indexCongruencePlace P r level) x v ∈
        v.adicCompletionIntegers (FunctionField P)
      rw [Pi.single_eq_of_ne hv]
      exact (v.adicCompletionIntegers (FunctionField P)).zero_mem

/-- One-place support is a nonunital ring homomorphism.  It preserves
multiplication but sends the local unit to the idempotent supported at the
selected coordinate, not to the unit of the full restricted product. -/
noncomputable def arithmeticFiniteAdeleSupportedAtIndexPlaceNonUnitalRingHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicCompletion P r level →ₙ+*
      ArithmeticFiniteAdeleRing P where
  toFun := arithmeticFiniteAdeleSupportedAtIndexPlace P r level
  map_zero' := by
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro v
    classical
    change Pi.single (indexCongruencePlace P r level) 0 v = 0
    by_cases hv : v = indexCongruencePlace P r level
    · subst v
      rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hv]
  map_add' x y := by
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro v
    classical
    change Pi.single (indexCongruencePlace P r level) (x + y) v =
      Pi.single (indexCongruencePlace P r level) x v +
        Pi.single (indexCongruencePlace P r level) y v
    by_cases hv : v = indexCongruencePlace P r level
    · subst v
      simp only [Pi.single_eq_same]
    · simp only [Pi.single_eq_of_ne hv, add_zero]
  map_mul' x y := by
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro v
    classical
    change Pi.single (indexCongruencePlace P r level) (x * y) v =
      Pi.single (indexCongruencePlace P r level) x v *
        Pi.single (indexCongruencePlace P r level) y v
    by_cases hv : v = indexCongruencePlace P r level
    · subst v
      simp only [Pi.single_eq_same]
    · simp only [Pi.single_eq_of_ne hv, mul_zero]

/-- The same supported insertion is linear over the diagonal global
function field. -/
noncomputable def arithmeticFiniteAdeleSupportedAtIndexPlaceLinearMap
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicCompletion P r level →ₗ[FunctionField P]
      ArithmeticFiniteAdeleRing P where
  toFun := arithmeticFiniteAdeleSupportedAtIndexPlace P r level
  map_add' := map_add
    (arithmeticFiniteAdeleSupportedAtIndexPlaceNonUnitalRingHom P r level)
  map_smul' c x := by
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro v
    classical
    change Pi.single (indexCongruencePlace P r level) (c • x) v =
      algebraMap (FunctionField P)
        (v.adicCompletion (FunctionField P)) c *
          Pi.single (indexCongruencePlace P r level) x v
    by_cases hv : v = indexCongruencePlace P r level
    · subst v
      simp only [Pi.single_eq_same, Algebra.smul_def]
    · simp only [Pi.single_eq_of_ne hv, mul_zero]

/-- Evaluation of the arithmetic finite adeles at the selected abstract
adic place is onto, by the explicit one-place supported section. -/
theorem arithmeticFiniteAdeleAtIndexPlace_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (arithmeticFiniteAdeleAtIndexPlace P r level) := by
  intro x
  exact ⟨arithmeticFiniteAdeleSupportedAtIndexPlace P r level x,
    arithmeticFiniteAdeleAtIndexPlace_supported P r level x⟩

@[simp] theorem arithmeticFiniteAdeleAtIndexPlace_diagonal
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : FunctionField P) :
    arithmeticFiniteAdeleAtIndexPlace P r level
        (functionFieldToArithmeticFiniteAdeles P x) =
      algebraMap (FunctionField P)
        (IndexCongruenceAdicCompletion P r level) x :=
  rfl

/-- Evaluation at the selected congruence place, with its compatibility
with the global function-field scalars recorded in the type. -/
noncomputable def arithmeticFiniteAdeleAtIndexPlaceAlgHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdeleRing P →ₐ[FunctionField P]
      IndexCongruenceAdicCompletion P r level where
  __ := arithmeticFiniteAdeleAtIndexPlace P r level
  commutes' x := arithmeticFiniteAdeleAtIndexPlace_diagonal P r level x

/-- The cyclic division algebra after scalar extension to the selected
abstract adic completion. -/
noncomputable abbrev IndexAdicCyclicAlgebra
    (P : BasePrime) (r : Rank) (level : Nat) :=
  TensorProduct (FunctionField P)
    (IndexCongruenceAdicCompletion P r level) (CyclicAlgebra P r)

/-- Projection of the finite-adelic cyclic algebra to its selected adic
coordinate.  Both scalar and cyclic-algebra factors are kept explicit, so
this is the actual base-change map rather than an unrelated matrix lift. -/
noncomputable def arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdeleCyclicAlgebra P r →ₐ[FunctionField P]
      IndexAdicCyclicAlgebra P r level :=
  Algebra.TensorProduct.map
    (arithmeticFiniteAdeleAtIndexPlaceAlgHom P r level)
    (AlgHom.id (FunctionField P) (CyclicAlgebra P r))

/-- Insert an element of the selected adic cyclic algebra coefficientwise
as a finite-adelic cyclic element supported at that one place.  This is an
additive one-place section; the later unit construction uses its supported
idempotent explicitly rather than incorrectly treating it as unital. -/
noncomputable def arithmeticFiniteAdeleCyclicSupportedAtIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexAdicCyclicAlgebra P r level →ₗ[FunctionField P]
      ArithmeticFiniteAdeleCyclicAlgebra P r :=
  TensorProduct.map
    (arithmeticFiniteAdeleSupportedAtIndexPlaceLinearMap P r level)
    LinearMap.id

@[simp] theorem arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace_tmul
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : ArithmeticFiniteAdeleRing P) (x : CyclicAlgebra P r) :
    arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level
        (TensorProduct.tmul (FunctionField P) a x) =
      TensorProduct.tmul (FunctionField P)
        (arithmeticFiniteAdeleAtIndexPlace P r level a) x := by
  simp [arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace,
    arithmeticFiniteAdeleAtIndexPlaceAlgHom]
  rfl

/-- The supported cyclic insertion on a pure tensor. -/
@[simp] theorem arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_tmul
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : IndexCongruenceAdicCompletion P r level)
    (x : CyclicAlgebra P r) :
    arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level
        (TensorProduct.tmul (FunctionField P) a x) =
      TensorProduct.tmul (FunctionField P)
        (arithmeticFiniteAdeleSupportedAtIndexPlace P r level a) x := by
  simp [arithmeticFiniteAdeleCyclicSupportedAtIndexPlace,
    arithmeticFiniteAdeleSupportedAtIndexPlaceLinearMap]
  rfl

/-- At every non-selected finite place, the splitting matrix of a supported
cyclic element is zero. -/
theorem arithmeticFiniteAdeleCyclicSplitting_supportedAtIndexPlace_of_ne
    (P : BasePrime) (r : Rank) (level : Nat)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hv : v ≠ indexCongruencePlace P r level)
    (x : IndexAdicCyclicAlgebra P r level) :
    (arithmeticFiniteAdeleCyclicSplittingMap P r
        (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x)).map
          (arithmeticFiniteAdeleSplittingRingAt P r v) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      rw [show arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level
            (x + y) =
          arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x +
            arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level y from
        map_add (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level) x y]
      rw [show arithmeticFiniteAdeleCyclicSplittingMap P r
            (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x +
              arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level y) =
          arithmeticFiniteAdeleCyclicSplittingMap P r
              (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x) +
            arithmeticFiniteAdeleCyclicSplittingMap P r
              (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level y) from
        map_add (arithmeticFiniteAdeleCyclicSplittingMap P r) _ _]
      rw [Matrix.map_add _ (fun a b =>
        map_add (arithmeticFiniteAdeleSplittingRingAt P r v) a b),
        hx, hy, add_zero]
  | tmul a x =>
      rw [arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_tmul,
        arithmeticFiniteAdeleCyclicSplittingMap,
        Algebra.TensorProduct.lift_tmul, Matrix.map_mul]
      have ha := arithmeticFiniteAdeleAt_supportedAtIndexPlace_of_ne
        P r level v hv a
      have hscalar :
          ((Algebra.ofId (ArithmeticFiniteAdeleRing P)
            (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (ArithmeticFiniteAdeleSplittingRing P r)))
                (arithmeticFiniteAdeleSupportedAtIndexPlace P r level a)).map
              (arithmeticFiniteAdeleSplittingRingAt P r v) = 0 := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [arithmeticFiniteAdeleSplittingRingAt,
            arithmeticFiniteAdeleAtAlgHom,
            Matrix.algebraMap_matrix_apply, ha]
          change arithmeticFiniteAdeleAt P v
            (arithmeticFiniteAdeleSupportedAtIndexPlace P r level a) ⊗ₜ[FunctionField P] 1 = 0
          rw [ha, TensorProduct.zero_tmul]
        · simp [arithmeticFiniteAdeleSplittingRingAt,
            arithmeticFiniteAdeleAtAlgHom,
            Matrix.algebraMap_matrix_apply, hij]
      rw [hscalar, zero_mul]

/-- The coefficientwise one-place insertion is a right inverse to the
selected adic projection. -/
@[simp] theorem arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace_supported
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicAlgebra P r level) :
    arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level
        (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp [arithmeticFiniteAdeleCyclicSupportedAtIndexPlace]
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul a x =>
      rw [arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_tmul,
        arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace_tmul,
        arithmeticFiniteAdeleAtIndexPlace_supported]

/-- The construction-owned cyclic basis after scalar extension to the
selected adic completion.  This is the local chart used for the integral
patching argument; no external matrix coordinates are chosen. -/
noncomputable def indexAdicCyclicBasis
    (P : BasePrime) (r : Rank) (level : Nat) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (IndexCongruenceAdicCompletion P r level)
      (IndexAdicCyclicAlgebra P r level) :=
  (functionFieldCyclicBasis P r).baseChange
    (IndexCongruenceAdicCompletion P r level)

/-- The integral lattice in the selected adic cyclic algebra, expressed in
the same construction-owned cyclic basis as the global adelic lattice. -/
noncomputable def IndexAdicCyclicIntegralLattice
    (P : BasePrime) (r : Rank) (level : Nat) :
    Set (IndexAdicCyclicAlgebra P r level) :=
  {x | ∀ p, (indexAdicCyclicBasis P r level).equivFun x p ∈
    IndexCongruenceAdicIntegers P r level}

/-- Cyclic coordinates commute with scalar extension from the global
cyclic algebra to the selected abstract adic completion. -/
theorem indexAdicCyclicBasis_equivFun_diagonal
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : CyclicAlgebra P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (indexAdicCyclicBasis P r level).equivFun
        (TensorProduct.tmul (FunctionField P) 1 x) p =
      algebraMap (FunctionField P)
        (IndexCongruenceAdicCompletion P r level)
          ((functionFieldCyclicBasis P r).equivFun x p) := by
  rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
    indexAdicCyclicBasis, Module.Basis.baseChange_repr_tmul]
  rw [Algebra.smul_def, mul_one]

/-- Every global arithmetic cyclic-order element is integral after scalar
extension to the selected adic completion. -/
theorem indexAdicCyclic_diagonal_mem_integralLattice
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : CyclicAlgebra P r) (hx : x ∈ arithmeticCyclicSpan P r) :
    TensorProduct.tmul (FunctionField P) 1 x ∈
      IndexAdicCyclicIntegralLattice P r level := by
  intro p
  obtain ⟨a, ha⟩ :=
    exists_arithmetic_coordinate_of_mem_arithmeticCyclicSpan P r x hx p
  rw [indexAdicCyclicBasis_equivFun_diagonal, ← ha]
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem
    (ArithmeticRing P) (FunctionField P)
    (indexCongruencePlace P r level) a

/-- The unit of the selected adic cyclic algebra belongs to its
construction-owned integral cyclic lattice. -/
theorem one_mem_indexAdicCyclicIntegralLattice
    (P : BasePrime) (r : Rank) (level : Nat) :
    (1 : IndexAdicCyclicAlgebra P r level) ∈
      IndexAdicCyclicIntegralLattice P r level := by
  exact indexAdicCyclic_diagonal_mem_integralLattice P r level 1
    (one_mem_arithmeticCyclicSpan P r)

/-- The selected adic integral cyclic lattice is closed under
subtraction, coefficient by coefficient. -/
theorem IndexAdicCyclicIntegralLattice.sub_mem
    (P : BasePrime) (r : Rank) (level : Nat)
    {x y : IndexAdicCyclicAlgebra P r level}
    (hx : x ∈ IndexAdicCyclicIntegralLattice P r level)
    (hy : y ∈ IndexAdicCyclicIntegralLattice P r level) :
    x - y ∈ IndexAdicCyclicIntegralLattice P r level := by
  intro p
  have hcoord := congrArg
    (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
      IndexCongruenceAdicCompletion P r level => f p)
    ((indexAdicCyclicBasis P r level).equivFun.map_sub x y)
  change (indexAdicCyclicBasis P r level).equivFun (x - y) p =
      (indexAdicCyclicBasis P r level).equivFun x p -
        (indexAdicCyclicBasis P r level).equivFun y p at hcoord
  rw [hcoord]
  exact (indexCongruencePlace P r level).adicCompletionIntegers
    (FunctionField P) |>.sub_mem (hx p) (hy p)

/-- The global finite-adelic integral cyclic lattice is closed under
addition, coefficient by coefficient. -/
theorem ArithmeticFiniteAdeleCyclicIntegralLattice.add_mem
    (P : BasePrime) (r : Rank)
    {x y : ArithmeticFiniteAdeleCyclicAlgebra P r}
    (hx : x ∈ ArithmeticFiniteAdeleCyclicIntegralLattice P r)
    (hy : y ∈ ArithmeticFiniteAdeleCyclicIntegralLattice P r) :
    x + y ∈ ArithmeticFiniteAdeleCyclicIntegralLattice P r := by
  intro p
  rw [(arithmeticFiniteAdeleCyclicBasis P r).equivFun.map_add]
  exact (ArithmeticIntegralFiniteAdeles P).add_mem (hx p) (hy p)

/-- The global finite-adelic integral cyclic lattice is closed under
subtraction, coefficient by coefficient. -/
theorem ArithmeticFiniteAdeleCyclicIntegralLattice.sub_mem
    (P : BasePrime) (r : Rank)
    {x y : ArithmeticFiniteAdeleCyclicAlgebra P r}
    (hx : x ∈ ArithmeticFiniteAdeleCyclicIntegralLattice P r)
    (hy : y ∈ ArithmeticFiniteAdeleCyclicIntegralLattice P r) :
    x - y ∈ ArithmeticFiniteAdeleCyclicIntegralLattice P r := by
  intro p
  have hcoord := congrArg
    (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
      ArithmeticFiniteAdeleRing P => f p)
    ((arithmeticFiniteAdeleCyclicBasis P r).equivFun.map_sub x y)
  change (arithmeticFiniteAdeleCyclicBasis P r).equivFun (x - y) p =
      (arithmeticFiniteAdeleCyclicBasis P r).equivFun x p -
        (arithmeticFiniteAdeleCyclicBasis P r).equivFun y p at hcoord
  rw [hcoord]
  exact (ArithmeticIntegralFiniteAdeles P).sub_mem (hx p) (hy p)

/-- The supported cyclic insertion is the coefficientwise supported scalar
insertion in the common cyclic basis. -/
theorem arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_eq_sum
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicAlgebra P r level) :
    arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x =
      ∑ p, TensorProduct.tmul (FunctionField P)
        (arithmeticFiniteAdeleSupportedAtIndexPlace P r level
          ((indexAdicCyclicBasis P r level).equivFun x p))
        (functionFieldCyclicBasis P r p) := by
  conv_lhs => rw [← (indexAdicCyclicBasis P r level).sum_equivFun x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hterm : (indexAdicCyclicBasis P r level).equivFun x p •
      indexAdicCyclicBasis P r level p =
      TensorProduct.tmul (FunctionField P)
        ((indexAdicCyclicBasis P r level).equivFun x p)
        (functionFieldCyclicBasis P r p) := by
    simp [indexAdicCyclicBasis, Module.Basis.baseChange_apply,
      TensorProduct.smul_tmul']
  rw [hterm, arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_tmul]

private theorem arithmeticFiniteAdeleCyclicBasis_repr_tmul_basis
    (P : BasePrime) (r : Rank)
    (a : ArithmeticFiniteAdeleRing P)
    (q p : Fin r.matrixRank × Fin r.matrixRank) :
    (arithmeticFiniteAdeleCyclicBasis P r).repr
        (TensorProduct.tmul (FunctionField P) a
          (functionFieldCyclicBasis P r q)) p =
      if q = p then a else 0 := by
  rw [arithmeticFiniteAdeleCyclicBasis,
    Module.Basis.baseChange_repr_tmul]
  rw [(functionFieldCyclicBasis P r).repr_self]
  by_cases h : q = p <;> simp [h]

/-- Cyclic coordinates commute with the one-place supported insertion. -/
theorem arithmeticFiniteAdeleCyclicBasis_equivFun_supportedAtIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicAlgebra P r level)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (arithmeticFiniteAdeleCyclicBasis P r).equivFun
        (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x) p =
      arithmeticFiniteAdeleSupportedAtIndexPlace P r level
        ((indexAdicCyclicBasis P r level).equivFun x p) := by
  rw [Module.Basis.equivFun_apply,
    arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_eq_sum]
  have hsum := map_sum
    (arithmeticFiniteAdeleCyclicBasis P r).repr
    (fun q => TensorProduct.tmul (FunctionField P)
      (arithmeticFiniteAdeleSupportedAtIndexPlace P r level
        ((indexAdicCyclicBasis P r level).equivFun x q))
      (functionFieldCyclicBasis P r q)) Finset.univ
  rw [hsum]
  change Finsupp.applyAddHom p
      (∑ q, (arithmeticFiniteAdeleCyclicBasis P r).repr
        (TensorProduct.tmul (FunctionField P)
          (arithmeticFiniteAdeleSupportedAtIndexPlace P r level
            ((indexAdicCyclicBasis P r level).equivFun x q))
          (functionFieldCyclicBasis P r q))) = _
  rw [map_sum, Finset.sum_eq_single p]
  · exact arithmeticFiniteAdeleCyclicBasis_repr_tmul_basis P r _ p p
      |>.trans (by simp)
  · intro q _ hqp
    change ((arithmeticFiniteAdeleCyclicBasis P r).repr
      (TensorProduct.tmul (FunctionField P)
        (arithmeticFiniteAdeleSupportedAtIndexPlace P r level
          ((indexAdicCyclicBasis P r level).equivFun x q))
        (functionFieldCyclicBasis P r q))) p = 0
    rw [arithmeticFiniteAdeleCyclicBasis_repr_tmul_basis]
    simp [hqp]
  · simp

/-- One-place cyclic support is globally integral exactly when all selected
local cyclic coordinates are adic integral. -/
theorem arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_mem_integral_iff
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicAlgebra P r level) :
    arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x ∈
        ArithmeticFiniteAdeleCyclicIntegralLattice P r ↔
      x ∈ IndexAdicCyclicIntegralLattice P r level := by
  simp only [ArithmeticFiniteAdeleCyclicIntegralLattice,
    IndexAdicCyclicIntegralLattice, Set.mem_setOf_eq]
  simp_rw [arithmeticFiniteAdeleCyclicBasis_equivFun_supportedAtIndexPlace,
    arithmeticFiniteAdeleSupportedAtIndexPlace_mem_integral_iff]

/-- The unit of the finite-adelic cyclic algebra is in the all-place
integral cyclic lattice. -/
theorem one_mem_arithmeticFiniteAdeleCyclicIntegralLattice
    (P : BasePrime) (r : Rank) :
    (1 : ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r := by
  exact cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice
    P r 1 (one_mem_arithmeticCyclicSpan P r)

/-- One-place insertion preserves multiplication.  It remains deliberately
nonunital: its image unit is the selected-coordinate idempotent. -/
theorem arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_mul
    (P : BasePrime) (r : Rank) (level : Nat)
    (x y : IndexAdicCyclicAlgebra P r level) :
    arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level (x * y) =
      arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x *
        arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level y := by
  induction x using TensorProduct.induction_on with
  | zero => simp [arithmeticFiniteAdeleCyclicSupportedAtIndexPlace]
  | add x z hx hz => simp [add_mul, map_add, hx, hz]
  | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp [arithmeticFiniteAdeleCyclicSupportedAtIndexPlace]
      | add y z hy hz => simp [mul_add, map_add, hy, hz]
      | tmul b y =>
          simp [Algebra.TensorProduct.tmul_mul_tmul,
            show arithmeticFiniteAdeleSupportedAtIndexPlace P r level
                (a * b) =
              arithmeticFiniteAdeleSupportedAtIndexPlace P r level a *
                arithmeticFiniteAdeleSupportedAtIndexPlace P r level b from
              map_mul
                (arithmeticFiniteAdeleSupportedAtIndexPlaceNonUnitalRingHom
                  P r level) a b]

/-- The idempotent which is one at the selected cyclic-algebra coordinate
and zero at every other finite-adelic coordinate. -/
noncomputable def arithmeticFiniteAdeleCyclicIndexIdempotent
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdeleCyclicAlgebra P r :=
  arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level 1

theorem arithmeticFiniteAdeleCyclicIndexIdempotent_mul_self
    (P : BasePrime) (r : Rank) (level : Nat) :
    arithmeticFiniteAdeleCyclicIndexIdempotent P r level *
        arithmeticFiniteAdeleCyclicIndexIdempotent P r level =
      arithmeticFiniteAdeleCyclicIndexIdempotent P r level := by
  rw [arithmeticFiniteAdeleCyclicIndexIdempotent,
    ← arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_mul]
  simp

theorem arithmeticFiniteAdeleCyclicIndexIdempotent_mul_supported
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicAlgebra P r level) :
    arithmeticFiniteAdeleCyclicIndexIdempotent P r level *
        arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x =
      arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x := by
  rw [arithmeticFiniteAdeleCyclicIndexIdempotent,
    ← arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_mul]
  simp

theorem arithmeticFiniteAdeleCyclicSupported_mul_indexIdempotent
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicAlgebra P r level) :
    arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x *
        arithmeticFiniteAdeleCyclicIndexIdempotent P r level =
      arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x := by
  rw [arithmeticFiniteAdeleCyclicIndexIdempotent,
    ← arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_mul]
  simp

/-- Replace the selected coordinate of the adelic unit by `x` while
leaving the unit at every other place. -/
noncomputable def arithmeticFiniteAdeleCyclicPatchAtIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicAlgebra P r level) :
    ArithmeticFiniteAdeleCyclicAlgebra P r :=
  1 - arithmeticFiniteAdeleCyclicIndexIdempotent P r level +
    arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x

/-- Patching an integral selected adic cyclic element by the identity at
all other places preserves the all-place finite-adelic integral lattice. -/
theorem arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mem_integral
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicAlgebra P r level)
    (hx : x ∈ IndexAdicCyclicIntegralLattice P r level) :
    arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r := by
  apply ArithmeticFiniteAdeleCyclicIntegralLattice.add_mem P r
  · apply ArithmeticFiniteAdeleCyclicIntegralLattice.sub_mem P r
    · exact one_mem_arithmeticFiniteAdeleCyclicIntegralLattice P r
    · exact
        (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_mem_integral_iff
          P r level 1).mpr
            (one_mem_indexAdicCyclicIntegralLattice P r level)
  · exact
      (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_mem_integral_iff
        P r level x).mpr hx

theorem arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mul
    (P : BasePrime) (r : Rank) (level : Nat)
    (x y : IndexAdicCyclicAlgebra P r level) :
    arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x *
        arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level y =
      arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level (x * y) := by
  change
    (1 - arithmeticFiniteAdeleCyclicIndexIdempotent P r level +
        arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x) *
      (1 - arithmeticFiniteAdeleCyclicIndexIdempotent P r level +
        arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level y) =
    1 - arithmeticFiniteAdeleCyclicIndexIdempotent P r level +
      arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level (x * y)
  noncomm_ring
    [arithmeticFiniteAdeleCyclicIndexIdempotent_mul_self P r level,
      arithmeticFiniteAdeleCyclicIndexIdempotent_mul_supported P r level x,
      arithmeticFiniteAdeleCyclicIndexIdempotent_mul_supported P r level y,
      arithmeticFiniteAdeleCyclicSupported_mul_indexIdempotent P r level x,
      arithmeticFiniteAdeleCyclicSupported_mul_indexIdempotent P r level y,
      arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_mul P r level x y]

/-- At every non-selected finite place, the splitting matrix of the patched
cyclic element is the identity matrix. -/
theorem arithmeticFiniteAdeleCyclicSplitting_patchAtIndexPlace_of_ne
    (P : BasePrime) (r : Rank) (level : Nat)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hv : v ≠ indexCongruencePlace P r level)
    (x : IndexAdicCyclicAlgebra P r level) :
    (arithmeticFiniteAdeleCyclicSplittingMap P r
        (arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x)).map
          (arithmeticFiniteAdeleSplittingRingAt P r v) = 1 := by
  let h : ArithmeticFiniteAdeleCyclicAlgebra P r →+*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ArithmeticAdicSplittingRing P r v) :=
    (arithmeticFiniteAdeleSplittingRingAt P r v).toRingHom.mapMatrix.comp
      (arithmeticFiniteAdeleCyclicSplittingMap P r).toRingHom
  change h (arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x) = 1
  have he : h (arithmeticFiniteAdeleCyclicIndexIdempotent P r level) = 0 := by
    exact arithmeticFiniteAdeleCyclicSplitting_supportedAtIndexPlace_of_ne
      P r level v hv 1
  have hx : h
      (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x) = 0 := by
    exact arithmeticFiniteAdeleCyclicSplitting_supportedAtIndexPlace_of_ne
      P r level v hv x
  change h (1 - arithmeticFiniteAdeleCyclicIndexIdempotent P r level +
    arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x) = 1
  calc
    h (1 - arithmeticFiniteAdeleCyclicIndexIdempotent P r level +
        arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x) =
      h (1 - arithmeticFiniteAdeleCyclicIndexIdempotent P r level) +
        h (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x) :=
      h.map_add _ _
    _ = (h 1 - h (arithmeticFiniteAdeleCyclicIndexIdempotent P r level)) +
        h (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x) := by
      rw [h.map_sub]
    _ = 1 := by rw [h.map_one, he, hx]; simp

/-- A local adic cyclic-algebra unit patched into the selected coordinate
of a genuine finite-adelic cyclic-algebra unit. -/
noncomputable def arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (IndexAdicCyclicAlgebra P r level)ˣ) :
    (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ where
  val := arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level
    (u : IndexAdicCyclicAlgebra P r level)
  inv := arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level
    ((u⁻¹ : (IndexAdicCyclicAlgebra P r level)ˣ) :
      IndexAdicCyclicAlgebra P r level)
  val_inv := by
    rw [arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mul]
    have hu : (u : IndexAdicCyclicAlgebra P r level) *
        ((u⁻¹ : (IndexAdicCyclicAlgebra P r level)ˣ) :
          IndexAdicCyclicAlgebra P r level) = 1 := by
      exact congrArg Units.val (mul_inv_cancel u)
    rw [hu]
    simp [arithmeticFiniteAdeleCyclicPatchAtIndexPlace,
      arithmeticFiniteAdeleCyclicIndexIdempotent]
  inv_val := by
    rw [arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mul]
    have hu :
        ((u⁻¹ : (IndexAdicCyclicAlgebra P r level)ˣ) :
          IndexAdicCyclicAlgebra P r level) *
          (u : IndexAdicCyclicAlgebra P r level) = 1 := by
      exact congrArg Units.val (inv_mul_cancel u)
    rw [hu]
    simp [arithmeticFiniteAdeleCyclicPatchAtIndexPlace,
      arithmeticFiniteAdeleCyclicIndexIdempotent]

/-- Every non-selected coordinate of the base-finite-adele reduced norm of
a one-place patched unit is one. -/
theorem arithmeticFiniteAdeleCyclicBaseReducedNorm_supportedAtIndexPlace_of_ne
    (P : BasePrime) (r : Rank) (level : Nat)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hv : v ≠ indexCongruencePlace P r level)
    (u : (IndexAdicCyclicAlgebra P r level)ˣ) :
    arithmeticFiniteAdeleAt P v
        (arithmeticFiniteAdeleCyclicBaseReducedNorm P r
          (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace P r level u)) =
      1 := by
  apply Algebra.TensorProduct.includeLeft_injective
    (R := FunctionField P)
    (S := v.adicCompletion (FunctionField P))
    (A := v.adicCompletion (FunctionField P))
    (B := SplittingFunctionField P r)
    (algebraMap (FunctionField P) (SplittingFunctionField P r)).injective
  change algebraMap (v.adicCompletion (FunctionField P))
      (ArithmeticAdicSplittingRing P r v)
        (arithmeticFiniteAdeleAt P v
          (arithmeticFiniteAdeleCyclicBaseReducedNorm P r
            (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace
              P r level u))) =
    algebraMap (v.adicCompletion (FunctionField P))
      (ArithmeticAdicSplittingRing P r v) 1
  rw [arithmeticFiniteAdeleCyclicBaseReducedNorm_atPlace]
  change Matrix.det
      ((arithmeticFiniteAdeleCyclicSplittingMap P r
        (arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level
          (u : IndexAdicCyclicAlgebra P r level))).map
            (arithmeticFiniteAdeleSplittingRingAt P r v)) =
    algebraMap (v.adicCompletion (FunctionField P))
      (ArithmeticAdicSplittingRing P r v) 1
  rw [arithmeticFiniteAdeleCyclicSplitting_patchAtIndexPlace_of_ne
    P r level v hv, Matrix.det_one, map_one]

/-- Projection on units from the finite-adelic cyclic algebra to the
selected abstract adic cyclic algebra. -/
noncomputable def arithmeticFiniteAdeleCyclicUnitToIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat) :
    (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ →*
      (IndexAdicCyclicAlgebra P r level)ˣ :=
  Units.map
    (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace
      P r level).toRingHom.toMonoidHom

@[simp] theorem arithmeticFiniteAdeleCyclicUnitToIndexPlace_supported
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (IndexAdicCyclicAlgebra P r level)ˣ) :
    arithmeticFiniteAdeleCyclicUnitToIndexPlace P r level
        (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace P r level u) =
      u := by
  apply Units.ext
  simp [arithmeticFiniteAdeleCyclicUnitToIndexPlace,
    arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace,
    arithmeticFiniteAdeleCyclicPatchAtIndexPlace,
    arithmeticFiniteAdeleCyclicIndexIdempotent]

/-- Every selected adic cyclic-algebra unit has a genuine finite-adelic
unit representative which is the identity away from that place. -/
theorem arithmeticFiniteAdeleCyclicUnitToIndexPlace_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
      (arithmeticFiniteAdeleCyclicUnitToIndexPlace P r level) := by
  intro u
  exact ⟨arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace P r level u,
    arithmeticFiniteAdeleCyclicUnitToIndexPlace_supported P r level u⟩

@[simp] theorem arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace_patch
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicAlgebra P r level) :
    arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level
        (arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x) = x := by
  simp [arithmeticFiniteAdeleCyclicPatchAtIndexPlace,
    arithmeticFiniteAdeleCyclicIndexIdempotent]

/-- Construction-owned cyclic coordinates commute with projection from
the finite adeles to the selected intrinsic adic completion. -/
theorem indexAdicCyclicBasis_equivFun_atIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (indexAdicCyclicBasis P r level).equivFun
        (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level x) p =
      arithmeticFiniteAdeleAtIndexPlace P r level
        ((arithmeticFiniteAdeleCyclicBasis P r).equivFun x p) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      rw [map_zero]
      have hleft := congrArg
        (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
          IndexCongruenceAdicCompletion P r level => f p)
        ((indexAdicCyclicBasis P r level).equivFun.map_zero)
      have hright := congrArg
        (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
          ArithmeticFiniteAdeleRing P => f p)
        ((arithmeticFiniteAdeleCyclicBasis P r).equivFun.map_zero)
      change (indexAdicCyclicBasis P r level).equivFun 0 p = 0 at hleft
      change (arithmeticFiniteAdeleCyclicBasis P r).equivFun 0 p = 0 at hright
      rw [hleft, hright, map_zero]
  | add x y hx hy =>
      rw [map_add]
      have hleft := congrArg
        (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
          IndexCongruenceAdicCompletion P r level => f p)
        ((indexAdicCyclicBasis P r level).equivFun.map_add
          (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level x)
          (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level y))
      have hright := congrArg
        (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
          ArithmeticFiniteAdeleRing P => f p)
        ((arithmeticFiniteAdeleCyclicBasis P r).equivFun.map_add x y)
      change (indexAdicCyclicBasis P r level).equivFun
          (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level x +
            arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level y) p =
        (indexAdicCyclicBasis P r level).equivFun
            (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level x) p +
          (indexAdicCyclicBasis P r level).equivFun
            (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level y) p
        at hleft
      change (arithmeticFiniteAdeleCyclicBasis P r).equivFun (x + y) p =
        (arithmeticFiniteAdeleCyclicBasis P r).equivFun x p +
          (arithmeticFiniteAdeleCyclicBasis P r).equivFun y p at hright
      rw [hleft, hright, map_add, hx, hy]
  | tmul a x =>
      rw [arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace_tmul]
      simp [Module.Basis.equivFun_apply, indexAdicCyclicBasis,
        arithmeticFiniteAdeleCyclicBasis,
        Module.Basis.baseChange_repr_tmul]
      exact ((arithmeticFiniteAdeleAtIndexPlaceAlgHom
        P r level).toLinearMap.map_smul _ _).symm

/-- Projection of the finite-adelic cyclic algebra to its selected adic
factor is onto, witnessed by the explicit supported section. -/
theorem arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
      (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level) := by
  intro x
  exact ⟨arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x,
    arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace_supported P r level x⟩

@[simp] theorem arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace_diagonal
    (P : BasePrime) (r : Rank) (level : Nat) (x : CyclicAlgebra P r) :
    arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level
        (cyclicAlgebraToArithmeticFiniteAdeles P r x) =
      TensorProduct.tmul (FunctionField P) 1 x := by
  simp [cyclicAlgebraToArithmeticFiniteAdeles_apply]

/-- The local ring at the construction-owned congruence place. -/
noncomputable abbrev IndexCongruenceLocalRing
    (P : BasePrime) (r : Rank) (level : Nat) :=
  Localization.AtPrime (IndexCongruenceIdeal P r level)

/-- The existing power-series chart reduces to the genuine residue map on
the base arithmetic ring. -/
@[simp] theorem indexCompletedBaseArithmeticEval_constantCoeff
    (P : BasePrime) (r : Rank) (level : Nat) (a : ArithmeticRing P) :
    PowerSeries.constantCoeff
        (indexCompletedBaseArithmeticEval P r level a) =
      indexArithmeticEval P r level a := by
  rw [indexCompletedBaseArithmeticEval, RingHom.comp_apply,
    indexCompletedArithmeticEval_constantCoeff,
    indexConstantArithmeticEval_arithmeticBaseChange]

/-- The closed point cut out by the completed chart is exactly the selected
congruence place, not merely an abstract residue map with the same target. -/
theorem ker_constantCoeff_comp_indexCompletedBaseArithmeticEval
    (P : BasePrime) (r : Rank) (level : Nat) :
    RingHom.ker
        (PowerSeries.constantCoeff.comp
          (indexCompletedBaseArithmeticEval P r level)) =
      IndexCongruenceIdeal P r level := by
  ext a
  change PowerSeries.constantCoeff
      (indexCompletedBaseArithmeticEval P r level a) = 0 ↔
    indexArithmeticEval P r level a = 0
  rw [indexCompletedBaseArithmeticEval_constantCoeff]

private noncomputable def indexCompletedBasePolynomialTaylorHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    PolynomialRing P →+* PowerSeries (ResidueField P r level) :=
  Polynomial.coeToPowerSeries.ringHom.comp
    ((Polynomial.taylorAlgHom (indexPlaceY P r level)).toRingHom.comp
      (Polynomial.mapRingHom
        (algebraMap (BaseField P) (ResidueField P r level))))

private theorem indexCompletedBasePolynomialEval_eq_taylor
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexCompletedBasePolynomialEval P r level =
      indexCompletedBasePolynomialTaylorHom P r level := by
  ext a
  · simp [indexCompletedBasePolynomialEval,
      indexCompletedBasePolynomialTaylorHom,
      indexCompletedPolynomialEval, add_comm]
  · simp [indexCompletedBasePolynomialEval,
      indexCompletedBasePolynomialTaylorHom,
      indexCompletedPolynomialEval, add_comm]

/-- The selected Taylor chart is faithful on the polynomial coefficient
ring: translating by the closed-point value and then adjoining the formal
parameter loses no global polynomial. -/
theorem indexCompletedBasePolynomialEval_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective (indexCompletedBasePolynomialEval P r level) := by
  rw [indexCompletedBasePolynomialEval_eq_taylor]
  exact (Polynomial.coe_injective (ResidueField P r level)).comp
    ((Polynomial.taylor_injective (indexPlaceY P r level)).comp
      (Polynomial.map_injective
        (algebraMap (BaseField P) (ResidueField P r level))
        (algebraMap (BaseField P) (ResidueField P r level)).injective))

/-- Faithfulness survives localization at `y(1+y)`, so the completed chart
really embeds the construction's S-arithmetic ring. -/
theorem indexCompletedBaseArithmeticEval_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective (indexCompletedBaseArithmeticEval P r level) := by
  apply IsLocalization.injective_of_map_algebraMap_zero (ArithmeticRing P)
    (M := Submonoid.powers
      (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P))
    (indexCompletedBaseArithmeticEval P r level)
  intro f hf
  rw [indexCompletedBaseArithmeticEval_algebraMap] at hf
  have hf0 : f = 0 := by
    apply indexCompletedBasePolynomialEval_injective P r level
    simpa using hf
  rw [hf0, map_zero]

/-- The actual local field at the selected congruence place. -/
abbrev IndexCongruenceLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :=
  LaurentSeries (ResidueField P r level)

/-- The S-arithmetic Taylor chart, now regarded in its Laurent-series
fraction field. -/
noncomputable def indexArithmeticToCongruenceLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticRing P →+* IndexCongruenceLocalField P r level :=
  (HahnSeries.ofPowerSeries ℤ (ResidueField P r level)).comp
    (indexCompletedBaseArithmeticEval P r level)

theorem indexArithmeticToCongruenceLocalField_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective
      (indexArithmeticToCongruenceLocalField P r level) :=
  (HahnSeries.ofPowerSeries_injective (Γ := ℤ)
      (R := ResidueField P r level)).comp
    (indexCompletedBaseArithmeticEval_injective P r level)

/-- The global rational-function field embedded into the genuine selected
Laurent-series local field. -/
noncomputable def functionFieldToIndexCongruenceLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    FunctionField P →+* IndexCongruenceLocalField P r level :=
  IsFractionRing.lift
    (indexArithmeticToCongruenceLocalField_injective P r level)

@[simp] theorem functionFieldToIndexCongruenceLocalField_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat) (a : ArithmeticRing P) :
    functionFieldToIndexCongruenceLocalField P r level
        (algebraMap (ArithmeticRing P) (FunctionField P) a) =
      indexArithmeticToCongruenceLocalField P r level a :=
  IsFractionRing.lift_algebraMap
    (indexArithmeticToCongruenceLocalField_injective P r level) a

/-- The selected Laurent field carries the construction-owned global
function-field algebra structure, not an implicitly chosen embedding. -/
noncomputable instance indexCongruenceLocalFieldFunctionFieldAlgebra
    (P : BasePrime) (r : Rank) (level : Nat) :
    Algebra (FunctionField P) (IndexCongruenceLocalField P r level) :=
  (functionFieldToIndexCongruenceLocalField P r level).toAlgebra

private noncomputable def indexCompletedPolynomialTaylorHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    ConstantPolynomialRing P r →+*
      PowerSeries (ResidueField P r level) :=
  Polynomial.coeToPowerSeries.ringHom.comp
    ((Polynomial.taylorAlgHom (indexPlaceY P r level)).toRingHom.comp
      (Polynomial.mapRingHom
        (indexConstantEmbedding P r level).toRingHom))

private theorem indexCompletedPolynomialEval_eq_taylor
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexCompletedPolynomialEval P r level =
      indexCompletedPolynomialTaylorHom P r level := by
  ext a <;>
    simp [indexCompletedPolynomialEval,
      indexCompletedPolynomialTaylorHom, add_comm]

/-- Taylor expansion is faithful after the construction-owned embedding of
the cyclic constant field into the selected residue field. -/
theorem indexCompletedPolynomialEval_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective (indexCompletedPolynomialEval P r level) := by
  rw [indexCompletedPolynomialEval_eq_taylor]
  exact (Polynomial.coe_injective (ResidueField P r level)).comp
    ((Polynomial.taylor_injective (indexPlaceY P r level)).comp
      (Polynomial.map_injective
        (indexConstantEmbedding P r level).toRingHom
        (indexConstantEmbedding P r level).injective))

/-- The selected completion map is faithful on the constant-extended
S-arithmetic coefficient ring as well. -/
theorem indexCompletedArithmeticEval_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective (indexCompletedArithmeticEval P r level) := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (ConstantArithmeticRing P r)
    (M := Submonoid.powers
      (Polynomial.X * (1 + Polynomial.X) : ConstantPolynomialRing P r))
    (indexCompletedArithmeticEval P r level)
  intro f hf
  rw [indexCompletedArithmeticEval_algebraMap] at hf
  have hf0 : f = 0 := by
    apply indexCompletedPolynomialEval_injective P r level
    simpa using hf
  rw [hf0, map_zero]

/-- The construction-owned embedding of the cyclic constant polynomial ring
into the selected Laurent local field. -/
noncomputable def indexConstantPolynomialToCongruenceLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    ConstantPolynomialRing P r →+*
      IndexCongruenceLocalField P r level :=
  (HahnSeries.ofPowerSeries ℤ (ResidueField P r level)).comp
    (indexCompletedPolynomialEval P r level)

theorem indexConstantPolynomialToCongruenceLocalField_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective
      (indexConstantPolynomialToCongruenceLocalField P r level) :=
  (HahnSeries.ofPowerSeries_injective (Γ := ℤ)
      (R := ResidueField P r level)).comp
    (indexCompletedPolynomialEval_injective P r level)

/-- Laurent-series embedding of the cyclic constant-field splitting
function field at the selected congruence place. -/
noncomputable def splittingFunctionFieldToIndexCongruenceLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    SplittingFunctionField P r →+*
      IndexCongruenceLocalField P r level :=
  IsFractionRing.lift
    (indexConstantPolynomialToCongruenceLocalField_injective P r level)

@[simp] theorem splittingFunctionFieldToIndexCongruenceLocalField_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat)
    (f : ConstantPolynomialRing P r) :
    splittingFunctionFieldToIndexCongruenceLocalField P r level
        (algebraMap (ConstantPolynomialRing P r)
          (SplittingFunctionField P r) f) =
      indexConstantPolynomialToCongruenceLocalField P r level f :=
  IsFractionRing.lift_algebraMap
    (indexConstantPolynomialToCongruenceLocalField_injective P r level) f

@[simp] private theorem splittingFunctionFieldToIndexCongruenceLocalField_C
    (P : BasePrime) (r : Rank) (level : Nat) (a : ConstantExtension P r) :
    splittingFunctionFieldToIndexCongruenceLocalField P r level
        (RatFunc.C a) =
      HahnSeries.single 0 (indexConstantEmbedding P r level a) := by
  rw [show (RatFunc.C a : SplittingFunctionField P r) =
      algebraMap (ConstantPolynomialRing P r)
          (SplittingFunctionField P r) (Polynomial.C a) by simp,
    splittingFunctionFieldToIndexCongruenceLocalField_algebraMap]
  simp [indexConstantPolynomialToCongruenceLocalField,
    indexCompletedPolynomialEval]

@[simp] private theorem splittingFunctionFieldToIndexCongruenceLocalField_X
    (P : BasePrime) (r : Rank) (level : Nat) :
    splittingFunctionFieldToIndexCongruenceLocalField P r level
        (RatFunc.X : SplittingFunctionField P r) =
      HahnSeries.single 0 (indexPlaceY P r level) +
        HahnSeries.single 1 1 := by
  rw [show (RatFunc.X : SplittingFunctionField P r) =
      algebraMap (ConstantPolynomialRing P r)
          (SplittingFunctionField P r) Polynomial.X by simp,
    splittingFunctionFieldToIndexCongruenceLocalField_algebraMap]
  simp [indexConstantPolynomialToCongruenceLocalField,
    indexCompletedPolynomialEval]

private theorem splittingFunctionFieldToIndexCongruenceLocalField_arithmetic
    (P : BasePrime) (r : Rank) (level : Nat) :
    (splittingFunctionFieldToIndexCongruenceLocalField P r level).comp
        (arithmeticRingToSplittingFunctionField P r) =
      indexArithmeticToCongruenceLocalField P r level := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers
      (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P))
  apply Polynomial.ringHom_ext
  · intro a
    simp [arithmeticRingToSplittingFunctionField,
      arithmeticRingToFunctionField, functionFieldEmbedding_C,
      indexArithmeticToCongruenceLocalField,
      indexCompletedBaseArithmeticEval,
      indexCompletedArithmeticEval,
      arithmeticToConstantArithmetic,
      indexCompletedPolynomialEval]
  · simp [arithmeticRingToSplittingFunctionField,
      arithmeticRingToFunctionField, functionFieldEmbedding_X,
      indexArithmeticToCongruenceLocalField,
      indexCompletedBaseArithmeticEval,
      indexCompletedArithmeticEval,
      arithmeticToConstantArithmetic,
      indexCompletedPolynomialEval]

/-- The selected Laurent embedding of the splitting field extends the
selected embedding of the original rational-function field. -/
theorem splittingFunctionFieldToIndexCongruenceLocalField_functionFieldEmbedding
    (P : BasePrime) (r : Rank) (level : Nat) (x : FunctionField P) :
    splittingFunctionFieldToIndexCongruenceLocalField P r level
        (functionFieldEmbedding P r x) =
      functionFieldToIndexCongruenceLocalField P r level x := by
  have h :
      (splittingFunctionFieldToIndexCongruenceLocalField P r level).comp
          (functionFieldEmbedding P r) =
        functionFieldToIndexCongruenceLocalField P r level := by
    apply IsFractionRing.ringHom_ext (A := ArithmeticRing P)
    intro a
    rw [functionFieldToIndexCongruenceLocalField_algebraMap]
    change splittingFunctionFieldToIndexCongruenceLocalField P r level
        (arithmeticRingToSplittingFunctionField P r a) =
      indexArithmeticToCongruenceLocalField P r level a
    exact DFunLike.congr_fun
      (splittingFunctionFieldToIndexCongruenceLocalField_arithmetic
        P r level) a
  exact DFunLike.congr_fun h x

private theorem splittingFunctionFieldToIndexCongruenceLocalField_constantArithmetic
    (P : BasePrime) (r : Rank) (level : Nat) :
    (splittingFunctionFieldToIndexCongruenceLocalField P r level).comp
        (constantArithmeticToSplittingFunctionField P r) =
      (HahnSeries.ofPowerSeries ℤ
        (ResidueField P r level)).comp
          (indexCompletedArithmeticEval P r level) := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers
      (Polynomial.X * (1 + Polynomial.X) :
        ConstantPolynomialRing P r))
  apply RingHom.ext
  intro f
  rw [RingHom.comp_apply, RingHom.comp_apply,
    constantArithmeticToSplittingFunctionField_algebraMap,
    splittingFunctionFieldToIndexCongruenceLocalField_algebraMap]
  change indexConstantPolynomialToCongruenceLocalField P r level f =
    HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
      (indexCompletedArithmeticEval P r level
        (algebraMap (ConstantPolynomialRing P r)
          (ConstantArithmeticRing P r) f))
  rw [indexCompletedArithmeticEval_algebraMap]
  rfl

private theorem indexCompletedBaseArithmeticEval_isUnit_of_not_mem
    (P : BasePrime) (r : Rank) (level : Nat) (a : ArithmeticRing P)
    (ha : a ∉ IndexCongruenceIdeal P r level) :
    IsUnit (indexCompletedBaseArithmeticEval P r level a) := by
  rw [PowerSeries.isUnit_iff_constantCoeff,
    indexCompletedBaseArithmeticEval_constantCoeff, isUnit_iff_ne_zero]
  exact ha

/-- The selected-place arithmetic embedding extends canonically from the
Dedekind domain to its local ring and lands in the already constructed
power-series local chart. -/
noncomputable def indexCongruenceLocalRingToCompletion
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceLocalRing P r level →+*
      PowerSeries (ResidueField P r level) :=
  IsLocalization.lift
    (fun a : (IndexCongruenceIdeal P r level).primeCompl =>
      indexCompletedBaseArithmeticEval_isUnit_of_not_mem
        P r level a.1 a.2)

@[simp] theorem indexCongruenceLocalRingToCompletion_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat) (a : ArithmeticRing P) :
    indexCongruenceLocalRingToCompletion P r level
        (algebraMap (ArithmeticRing P)
          (IndexCongruenceLocalRing P r level) a) =
      indexCompletedBaseArithmeticEval P r level a := by
  exact IsLocalization.lift_eq _ _

/-- The concrete power-series chart is faithful on the genuine local ring;
it is therefore a completion chart rather than a quotient presentation. -/
theorem indexCongruenceLocalRingToCompletion_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective
      (indexCongruenceLocalRingToCompletion P r level) := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (IndexCongruenceLocalRing P r level)
    (M := (IndexCongruenceIdeal P r level).primeCompl)
  intro a ha
  rw [indexCongruenceLocalRingToCompletion_algebraMap] at ha
  have ha0 : a = 0 := indexCompletedBaseArithmeticEval_injective P r level
    (by simpa using ha)
  rw [ha0, map_zero]

/-- In the selected local chart, the construction's irreducible closed-point
polynomial becomes the explicit simple-zero uniformizer already used by the
finite-jet proofs. -/
theorem indexCongruenceLocalRingToCompletion_indexPlacePolynomial
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexCongruenceLocalRingToCompletion P r level
        (algebraMap (ArithmeticRing P)
          (IndexCongruenceLocalRing P r level)
          (algebraMap (PolynomialRing P) (ArithmeticRing P)
            (indexPlacePolynomial P r level))) =
      indexCompletedUniformizer P r level := by
  rw [indexCongruenceLocalRingToCompletion_algebraMap,
    indexCompletedBaseArithmeticEval_algebraMap,
    indexCompletedBasePolynomialEval_indexPlacePolynomial]

/-- The local image of the selected prime polynomial is associated to the
power-series parameter `X`; hence the existing chart has the correct
valuation-one parameter, including its proved nonzero derivative. -/
theorem indexCongruenceLocalRing_uniformizer_associated_X
    (P : BasePrime) (r : Rank) (level : Nat) :
    Associated
      (indexCongruenceLocalRingToCompletion P r level
        (algebraMap (ArithmeticRing P)
          (IndexCongruenceLocalRing P r level)
          (algebraMap (PolynomialRing P) (ArithmeticRing P)
            (indexPlacePolynomial P r level))))
      (PowerSeries.X : PowerSeries (ResidueField P r level)) := by
  rw [indexCongruenceLocalRingToCompletion_indexPlacePolynomial,
    indexCompletedUniformizer_eq_X_mul_unitFactor]
  exact associated_mul_unit_left _ _
    (indexCompletedUniformizerUnitFactor_isUnit P r level)

/-! ## Identification of the selected height-one valuation ring -/

/-- The intrinsic valuation ring at the selected height-one place maps to
the same concrete power-series chart as the explicit localization. -/
noncomputable def indexValuationSubringToCompletion
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime (FunctionField P)
        (indexCongruencePlace P r level) →+*
      PowerSeries (ResidueField P r level) :=
  IsLocalization.lift
    (fun a : (indexCongruencePlace P r level).asIdeal.primeCompl ↦
      indexCompletedBaseArithmeticEval_isUnit_of_not_mem
        P r level a.1 a.2)

@[simp] theorem indexValuationSubringToCompletion_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat) (a : ArithmeticRing P) :
    indexValuationSubringToCompletion P r level
        (algebraMap (ArithmeticRing P)
          (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime (FunctionField P)
            (indexCongruencePlace P r level)) a) =
      indexCompletedBaseArithmeticEval P r level a := by
  exact IsLocalization.lift_eq _ _

/-- Restricting the global Laurent embedding to the intrinsic selected
valuation ring gives precisely the power-series localization chart. -/
theorem functionFieldToIndexCongruenceLocalField_on_valuationSubring
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime (FunctionField P)
      (indexCongruencePlace P r level)) :
    functionFieldToIndexCongruenceLocalField P r level x.1 =
      HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
        (indexValuationSubringToCompletion P r level x) := by
  have h :
      (functionFieldToIndexCongruenceLocalField P r level).comp
          (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
            (FunctionField P)
            (indexCongruencePlace P r level)).subtype =
        (HahnSeries.ofPowerSeries ℤ
            (ResidueField P r level)).comp
          (indexValuationSubringToCompletion P r level) := by
    apply IsLocalization.ringHom_ext
      (indexCongruencePlace P r level).asIdeal.primeCompl
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply]
    rw [show
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
          (FunctionField P) (indexCongruencePlace P r level)).subtype
          (algebraMap (ArithmeticRing P)
            (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
              (FunctionField P) (indexCongruencePlace P r level)) a) =
          algebraMap (ArithmeticRing P) (FunctionField P) a by
        exact (IsScalarTower.algebraMap_apply (ArithmeticRing P)
          (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
            (FunctionField P) (indexCongruencePlace P r level))
          (FunctionField P) a).symm]
    rw [functionFieldToIndexCongruenceLocalField_algebraMap,
      indexValuationSubringToCompletion_algebraMap]
    rfl
  exact DFunLike.congr_fun h x

/-- Pull back the Laurent-series valuation along the construction's actual
global-field embedding. -/
noncomputable def indexLaurentPullbackValuation
    (P : BasePrime) (r : Rank) (level : Nat) :
    Valuation (FunctionField P) (WithZero (Multiplicative ℤ)) :=
  Valuation.comap (functionFieldToIndexCongruenceLocalField P r level)
    (Valued.v : Valuation (IndexCongruenceLocalField P r level) _)

/-- The valuation ring of the pulled-back concrete Laurent valuation. -/
noncomputable def indexLaurentPullbackValuationSubring
    (P : BasePrime) (r : Rank) (level : Nat) :
    ValuationSubring (FunctionField P) :=
  (indexLaurentPullbackValuation P r level).valuationSubring

/-- Every element integral at the selected height-one place is integral in
the concrete Laurent chart. -/
theorem valuationSubringAtIndexPlace_le_indexLaurentPullback
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime (FunctionField P)
        (indexCongruencePlace P r level) ≤
      indexLaurentPullbackValuationSubring P r level := by
  intro x hx
  change functionFieldToIndexCongruenceLocalField P r level x ∈
    (Valued.v : Valuation (IndexCongruenceLocalField P r level) _).valuationSubring
  rw [Valuation.mem_valuationSubring_iff,
    LaurentSeries.val_le_one_iff_eq_coe]
  exact ⟨indexValuationSubringToCompletion P r level ⟨x, hx⟩,
    (functionFieldToIndexCongruenceLocalField_on_valuationSubring
      P r level ⟨x, hx⟩).symm⟩

/-- The selected prime polynomial as an element of the construction's
global rational-function field. -/
noncomputable def indexGlobalUniformizer
    (P : BasePrime) (r : Rank) (level : Nat) : FunctionField P :=
  algebraMap (ArithmeticRing P) (FunctionField P)
    (algebraMap (PolynomialRing P) (ArithmeticRing P)
      (indexPlacePolynomial P r level))

theorem indexGlobalUniformizer_ne_zero
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexGlobalUniformizer P r level ≠ 0 := by
  rw [indexGlobalUniformizer,
    map_ne_zero_iff _
      (IsFractionRing.injective (ArithmeticRing P) (FunctionField P))]
  exact indexPlacePolynomial_arithmetic_ne_zero P r level

/-- The global selected uniformizer maps to the explicit completed
uniformizer of the Taylor chart. -/
theorem functionFieldToIndexCongruenceLocalField_indexGlobalUniformizer
    (P : BasePrime) (r : Rank) (level : Nat) :
    functionFieldToIndexCongruenceLocalField P r level
        (indexGlobalUniformizer P r level) =
      HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
        (indexCompletedUniformizer P r level) := by
  rw [indexGlobalUniformizer,
    functionFieldToIndexCongruenceLocalField_algebraMap]
  change HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
      (indexCompletedBaseArithmeticEval P r level
        (algebraMap (PolynomialRing P) (ArithmeticRing P)
          (indexPlacePolynomial P r level))) = _
  rw [indexCompletedBaseArithmeticEval_algebraMap,
    indexCompletedBasePolynomialEval_indexPlacePolynomial]

/-- The inverse selected uniformizer is not integral in the concrete
Laurent chart.  This is proved from the construction-owned identity
`uniformizer = X * unit`, without assuming nontriviality of the valuation. -/
theorem inv_indexGlobalUniformizer_not_mem_indexLaurentPullback
    (P : BasePrime) (r : Rank) (level : Nat) :
    (indexGlobalUniformizer P r level)⁻¹ ∉
      indexLaurentPullbackValuationSubring P r level := by
  intro hmem
  change Valued.v
      (functionFieldToIndexCongruenceLocalField P r level
        (indexGlobalUniformizer P r level)⁻¹) ≤ 1 at hmem
  obtain ⟨F, hF⟩ :=
    (LaurentSeries.val_le_one_iff_eq_coe _ _).mp hmem
  have hprod :
      HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
          (indexCompletedUniformizer P r level) *
        HahnSeries.ofPowerSeries ℤ (ResidueField P r level) F = 1 := by
    rw [hF,
      ← functionFieldToIndexCongruenceLocalField_indexGlobalUniformizer]
    rw [← map_mul, mul_inv_cancel₀
      (indexGlobalUniformizer_ne_zero P r level), map_one]
  have hmul : indexCompletedUniformizer P r level * F = 1 := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa only [map_mul, map_one] using hprod
  have hu : IsUnit (indexCompletedUniformizer P r level) :=
    isUnit_iff_exists_inv.mpr ⟨F, hmul⟩
  rw [PowerSeries.isUnit_iff_constantCoeff,
    indexCompletedUniformizer_eq_X_mul_unitFactor] at hu
  simpa using hu

/-- The pulled-back Laurent valuation ring is proper. -/
theorem indexLaurentPullbackValuationSubring_ne_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexLaurentPullbackValuationSubring P r level ≠ ⊤ := by
  intro htop
  apply inv_indexGlobalUniformizer_not_mem_indexLaurentPullback P r level
  rw [htop]
  trivial

/-- The construction's concrete Laurent valuation ring is exactly the
intrinsic height-one valuation ring of the selected congruence place. -/
theorem valuationSubringAtIndexPlace_eq_indexLaurentPullback
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
        (FunctionField P) (indexCongruencePlace P r level) =
      indexLaurentPullbackValuationSubring P r level :=
  ValuationSubring.eq_of_le_of_ne_top _
    (valuationSubringAtIndexPlace_le_indexLaurentPullback P r level)
    (indexLaurentPullbackValuationSubring_ne_top P r level)

/-- Therefore the intrinsic height-one valuation and the valuation pulled
back from the explicit Laurent chart are equivalent. -/
theorem indexCongruenceValuation_isEquiv_indexLaurentPullback
    (P : BasePrime) (r : Rank) (level : Nat) :
    ((indexCongruencePlace P r level).valuation (FunctionField P)).IsEquiv
      (indexLaurentPullbackValuation P r level) := by
  rw [Valuation.isEquiv_iff_valuationSubring,
    ← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    valuationSubringAtIndexPlace_eq_indexLaurentPullback]
  rfl

/-- Completion of the global function field for the valuation pulled back
from the explicit selected Laurent chart. -/
noncomputable abbrev IndexLaurentPullbackCompletion
    (P : BasePrime) (r : Rank) (level : Nat) :=
  (indexLaurentPullbackValuation P r level).Completion

/-- Equivalent valuations give canonically uniformly equivalent
completions.  Thus the abstract selected finite-adele coordinate already
carries exactly the topology induced by the concrete Laurent chart. -/
noncomputable def indexAdicCompletionEquivLaurentPullbackCompletion
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicCompletion P r level ≃ᵤ
      IndexLaurentPullbackCompletion P r level :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv
    (FunctionField P) (indexCongruencePlace P r level)).trans
    (UniformSpace.Completion.mapEquiv
      (indexCongruenceValuation_isEquiv_indexLaurentPullback
        P r level).uniformEquiv)

/-- The same completion comparison as a ring equivalence. -/
noncomputable def indexAdicCompletionRingEquivLaurentPullbackCompletion
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicCompletion P r level ≃+*
      IndexLaurentPullbackCompletion P r level :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv
    (FunctionField P) (indexCongruencePlace P r level)).trans
    (UniformSpace.Completion.mapRingEquiv
    (WithVal.congr
      ((indexCongruencePlace P r level).valuation (FunctionField P))
      (indexLaurentPullbackValuation P r level)
      (RingEquiv.refl (FunctionField P)))
    (indexCongruenceValuation_isEquiv_indexLaurentPullback
      P r level).uniformContinuous_congr.continuous
    (indexCongruenceValuation_isEquiv_indexLaurentPullback
      P r level).symm.uniformContinuous_congr.continuous)

theorem indexAdicCompletionRingEquiv_eq_uniformEquiv
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexCongruenceAdicCompletion P r level) :
    indexAdicCompletionRingEquivLaurentPullbackCompletion P r level x =
      indexAdicCompletionEquivLaurentPullbackCompletion P r level x :=
  rfl

/-- The comparison of completions sends the intrinsic diagonal copy of a
global field element to the corresponding diagonal copy for the pulled-back
Laurent valuation. -/
@[simp] theorem indexAdicCompletionEquivLaurentPullbackCompletion_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat) (x : FunctionField P) :
    indexAdicCompletionEquivLaurentPullbackCompletion P r level
        (algebraMap (FunctionField P)
          (IndexCongruenceAdicCompletion P r level) x) =
      ((WithVal.toVal (indexLaurentPullbackValuation P r level) x :
        WithVal (indexLaurentPullbackValuation P r level)) :
          IndexLaurentPullbackCompletion P r level) := by
  exact UniformSpace.Completion.mapEquiv_coe
    (indexCongruenceValuation_isEquiv_indexLaurentPullback
      P r level).uniformEquiv
    (WithVal.toVal
      ((indexCongruencePlace P r level).valuation (FunctionField P)) x)

/-- The comparison preserves the closed unit ball, so the abstract adic
integer condition and the concrete pulled-back Laurent integer condition
are literally equivalent. -/
theorem indexAdicCompletionEquivLaurentPullbackCompletion_le_one_iff
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexCongruenceAdicCompletion P r level) :
    Valued.v x ≤ 1 ↔
      Valued.v
        (indexAdicCompletionEquivLaurentPullbackCompletion P r level x) ≤ 1 :=
  (indexCongruenceValuation_isEquiv_indexLaurentPullback
    P r level).valuedCompletion_le_one_iff (x := x.toCompletion)

/-- Closed unit ball in the completion for the pulled-back Laurent
valuation. -/
noncomputable abbrev IndexLaurentPullbackCompletionIntegers
    (P : BasePrime) (r : Rank) (level : Nat) :=
  (Valued.v : Valuation
    (IndexLaurentPullbackCompletion P r level) _).valuationSubring

/-- The completion comparison restricts to a ring equivalence of the two
integer rings. -/
noncomputable def indexAdicIntegersRingEquivLaurentPullbackIntegers
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicIntegers P r level ≃+*
      IndexLaurentPullbackCompletionIntegers P r level where
  toFun x :=
    ⟨indexAdicCompletionRingEquivLaurentPullbackCompletion P r level x,
      (indexAdicCompletionEquivLaurentPullbackCompletion_le_one_iff
        P r level x).mp x.property⟩
  invFun y := by
    let x :=
      (indexAdicCompletionRingEquivLaurentPullbackCompletion
        P r level).symm y.1
    refine ⟨x, ?_⟩
    apply (indexAdicCompletionEquivLaurentPullbackCompletion_le_one_iff
      P r level x).mpr
    rw [← indexAdicCompletionRingEquiv_eq_uniformEquiv]
    change Valued.v
      (indexAdicCompletionRingEquivLaurentPullbackCompletion P r level
        ((indexAdicCompletionRingEquivLaurentPullbackCompletion
          P r level).symm y.1)) ≤ 1
    rw [(indexAdicCompletionRingEquivLaurentPullbackCompletion
      P r level).apply_symm_apply]
    exact y.property
  left_inv x := by
    apply Subtype.ext
    exact (indexAdicCompletionRingEquivLaurentPullbackCompletion
      P r level).symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact (indexAdicCompletionRingEquivLaurentPullbackCompletion
      P r level).apply_symm_apply y
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul
      (indexAdicCompletionRingEquivLaurentPullbackCompletion P r level) x.1 y.1
  map_add' x y := by
    apply Subtype.ext
    exact map_add
      (indexAdicCompletionRingEquivLaurentPullbackCompletion P r level) x.1 y.1

section SelectedPlaceTopology

open scoped PowerSeries.WithPiTopology Topology WithZeroTopology Multiplicative
open MonoidWithZeroHom.ValueGroup₀
open Filter

/-- The product of all local integer rings is an open subring of the
restricted product.  This is the precise finite-adelic open set whose
intersection with rational points gives the `S`-arithmetic group. -/
theorem isOpen_arithmeticIntegralFiniteAdeles
    (P : BasePrime) :
    IsOpen (ArithmeticIntegralFiniteAdeles P :
      Set (ArithmeticFiniteAdeleRing P)) := by
  exact RestrictedProduct.isOpen_forall_mem fun v =>
    Valued.isOpen_valuationSubring
      (v.adicCompletion (FunctionField P))

/-- The all-integral cyclic lattice is open in the genuine finite-adelic
scalar extension.  Finiteness here is the construction's exact `d²` cyclic
basis, so this is a finite intersection of open scalar conditions. -/
theorem isOpen_arithmeticFiniteAdeleCyclicIntegralLattice
    (P : BasePrime) (r : Rank) :
    IsOpen (ArithmeticFiniteAdeleCyclicIntegralLattice P r) := by
  rw [show ArithmeticFiniteAdeleCyclicIntegralLattice P r =
      ⋂ p, (fun x =>
        (arithmeticFiniteAdeleCyclicBasis P r).equivFun x p) ⁻¹'
          (ArithmeticIntegralFiniteAdeles P :
            Set (ArithmeticFiniteAdeleRing P)) by
    ext x
    simp [ArithmeticFiniteAdeleCyclicIntegralLattice]]
  exact isOpen_iInter_of_finite fun p =>
    (isOpen_arithmeticIntegralFiniteAdeles P).preimage
      ((continuous_apply p).comp continuous_induced_dom)

/-- The integral chart in the concrete finite-adelic `SL₁(D)` is open.
The topology on units records both the value and its inverse, exactly
matching the two integral conditions in the chart. -/
theorem isOpen_arithmeticFiniteAdeleCyclicIntegralNormOneSet
    (P : BasePrime) (r : Rank) :
    IsOpen (ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r) := by
  change IsOpen
    ({u : ArithmeticFiniteAdeleCyclicNormOne P r |
        ((u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
          ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
        ArithmeticFiniteAdeleCyclicIntegralLattice P r} ∩
      {u : ArithmeticFiniteAdeleCyclicNormOne P r |
        (((u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ)⁻¹ :
          (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
          ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
        ArithmeticFiniteAdeleCyclicIntegralLattice P r})
  exact
    ((isOpen_arithmeticFiniteAdeleCyclicIntegralLattice P r).preimage
      (Units.continuous_val.comp continuous_subtype_val)).inter
    ((isOpen_arithmeticFiniteAdeleCyclicIntegralLattice P r).preimage
      (Units.continuous_coe_inv.comp continuous_subtype_val))

/-- Internal open-chart consequence of adelic strong approximation.  Once
global rational norm-one points are dense in the concrete finite-adelic
norm-one group, the actual integral inner-form points are dense throughout
the integral chart. -/
private theorem arithmeticFiniteAdeleCyclicIntegralNormOneSet_subset_closure_range
    (P : BasePrime) (r : Rank)
    (hdense : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r)) :
    ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r ⊆
      closure (Set.range
        (orderNormOneInnerFormToArithmeticFiniteAdeleNormOne P r)) := by
  rw [← image_preimage_arithmeticFiniteAdeleCyclicIntegralNormOneSet]
  exact hdense.subset_closure_image_preimage_of_isOpen
    (isOpen_arithmeticFiniteAdeleCyclicIntegralNormOneSet P r)

local instance selectedPlaceResidueFieldTopologicalSpace
    (P : BasePrime) (r : Rank) (level : Nat) :
    TopologicalSpace (ResidueField P r level) := ⊥

local instance selectedPlaceResidueFieldDiscreteTopology
    (P : BasePrime) (r : Rank) (level : Nat) :
    DiscreteTopology (ResidueField P r level) := ⟨rfl⟩

/-- Coefficientwise finite-jet approximation in the concrete power-series
chart also converges after embedding into the valued Laurent local field. -/
theorem tendsto_indexCompletedBaseArithmeticEval_in_localField
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : PowerSeries (ResidueField P r level))
    (a : Nat → ArithmeticRing P)
    (ha : ∀ n k, k < n →
      PowerSeries.coeff k
          (indexCompletedBaseArithmeticEval P r level (a n)) =
        PowerSeries.coeff k s) :
    Filter.Tendsto
      (fun n ↦ HahnSeries.ofPowerSeries ℤ
        (ResidueField P r level)
        (indexCompletedBaseArithmeticEval P r level (a n)))
      Filter.atTop
      (𝓝 (HahnSeries.ofPowerSeries ℤ
        (ResidueField P r level) s)) := by
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hU
  obtain ⟨N, hN⟩ := WithZero.exists_exp_neg_natCast_lt
    (show embedding γ.1 ≠ 0 by simp)
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  apply hγ
  change Valued.v.restrict
      (HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
          (indexCompletedBaseArithmeticEval P r level (a n)) -
        HahnSeries.ofPowerSeries ℤ (ResidueField P r level) s) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  rw [← map_sub]
  apply lt_of_le_of_lt
    ((LaurentSeries.valuation_le_iff_coeff_lt_eq_zero
      (ResidueField P r level)).mpr ?_) hN
  intro z hz
  cases z with
  | ofNat k =>
      have hkN : k < N := Int.ofNat_lt.mp hz
      calc
        _ = PowerSeries.coeff k
            (indexCompletedBaseArithmeticEval P r level (a n) - s) :=
          HahnSeries.ofPowerSeries_apply_coeff _ k
        _ = 0 := by
          rw [map_sub,
            ha n k (hkN.trans_le hn), sub_self]
  | negSucc k =>
      simp [HahnSeries.ofPowerSeries_apply,
        HahnSeries.embDomain_notin_image_support]

/-- Every integral element of the selected Laurent local field lies in the
closure of the construction's actual global function-field image. -/
theorem ofPowerSeries_mem_closure_range_functionFieldToIndexCongruenceLocalField
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : PowerSeries (ResidueField P r level)) :
    HahnSeries.ofPowerSeries ℤ (ResidueField P r level) s ∈
      closure (Set.range
        (functionFieldToIndexCongruenceLocalField P r level)) := by
  choose a ha using fun n =>
    exists_indexCompletedBaseArithmeticEval_finite_coeff_lift
      P r level s n
  apply mem_closure_of_tendsto
    (f := fun n : Nat =>
      functionFieldToIndexCongruenceLocalField P r level
        (algebraMap (ArithmeticRing P) (FunctionField P) (a n)))
    (b := (Filter.atTop : Filter Nat))
  · simpa [functionFieldToIndexCongruenceLocalField_algebraMap,
      indexArithmeticToCongruenceLocalField] using
      tendsto_indexCompletedBaseArithmeticEval_in_localField
        P r level s a ha
  · exact Filter.Eventually.of_forall fun n => Set.mem_range_self _

/-- The construction's global rational-function field is dense in its
selected Laurent-series completion.  The passage from the integral chart
to the whole local field uses the genuine fraction-field presentation of
Laurent series, so no matrix or split-group approximation is inserted. -/
theorem denseRange_functionFieldToIndexCongruenceLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    DenseRange
      (functionFieldToIndexCongruenceLocalField P r level) := by
  intro z
  let K : Subfield (IndexCongruenceLocalField P r level) :=
    (functionFieldToIndexCongruenceLocalField P r level).fieldRange.topologicalClosure
  change z ∈ K
  obtain ⟨x, y, _, rfl⟩ :=
    IsFractionRing.div_surjective
      (PowerSeries (ResidueField P r level)) z
  apply K.div_mem
  · exact ofPowerSeries_mem_closure_range_functionFieldToIndexCongruenceLocalField
      P r level x
  · exact ofPowerSeries_mem_closure_range_functionFieldToIndexCongruenceLocalField
      P r level y

/-- The same global-field embedding with the source carrying precisely the
pulled-back selected-place valuation topology. -/
noncomputable def indexLaurentPullbackValuedEmbedding
    (P : BasePrime) (r : Rank) (level : Nat) :
    WithVal (indexLaurentPullbackValuation P r level) →+*
      IndexCongruenceLocalField P r level :=
  (functionFieldToIndexCongruenceLocalField P r level).comp
    (WithVal.equiv (indexLaurentPullbackValuation P r level)).toRingHom

@[simp] theorem indexLaurentPullbackValuedEmbedding_apply
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : WithVal (indexLaurentPullbackValuation P r level)) :
    indexLaurentPullbackValuedEmbedding P r level x =
      functionFieldToIndexCongruenceLocalField P r level x.ofVal :=
  rfl

@[simp] theorem indexLaurentPullbackValuedEmbedding_valuation
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : WithVal (indexLaurentPullbackValuation P r level)) :
    Valued.v (indexLaurentPullbackValuedEmbedding P r level x) =
      Valued.v x :=
  rfl

/-- Density of the concrete global embedding forces its pulled-back
valuation to attain the entire Laurent value group: away from zero the
valuation is locally constant, so every Laurent value is already attained
on a global element. -/
theorem indexLaurentPullbackValuation_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (indexLaurentPullbackValuation P r level) := by
  intro γ
  by_cases hγ : γ = 0
  · use 0
    simp [hγ]
  · obtain ⟨z, hz⟩ :=
      LaurentSeries.valuation_surjective
        (ResidueField P r level) γ
    obtain ⟨x, hx⟩ :=
      (denseRange_functionFieldToIndexCongruenceLocalField P r level).mem_nhds
        (Valued.locally_const (hz.symm ▸ hγ))
    use x
    exact hx.trans hz

/-- The valued version of the global embedding still has dense range. -/
theorem denseRange_indexLaurentPullbackValuedEmbedding
    (P : BasePrime) (r : Rank) (level : Nat) :
    DenseRange (indexLaurentPullbackValuedEmbedding P r level) := by
  apply (denseRange_functionFieldToIndexCongruenceLocalField P r level).mono
  rintro _ ⟨x, rfl⟩
  exact ⟨WithVal.toVal (indexLaurentPullbackValuation P r level) x, rfl⟩

theorem indexLaurentPullbackWithVal_valuation_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
      (Valued.v :
        WithVal (indexLaurentPullbackValuation P r level) →
          WithZero (Multiplicative ℤ)) := by
  intro γ
  obtain ⟨x, hx⟩ := indexLaurentPullbackValuation_surjective P r level γ
  exact ⟨WithVal.toVal (indexLaurentPullbackValuation P r level) x,
    by simpa using hx⟩

/-- The concrete embedding induces exactly the pulled-back valuation
uniformity.  Surjectivity onto both copies of the common value group lets us
match every basic entourage on either side by an entourage with the same
valuation threshold. -/
theorem isUniformInducing_indexLaurentPullbackValuedEmbedding
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsUniformInducing (indexLaurentPullbackValuedEmbedding P r level) := by
  let v := indexLaurentPullbackValuation P r level
  let e := indexLaurentPullbackValuedEmbedding P r level
  have hsource : Function.Surjective
      (Valued.v : WithVal v → WithZero (Multiplicative ℤ)) := by
    simpa [v] using
      indexLaurentPullbackWithVal_valuation_surjective P r level
  apply ((Valued.hasBasis_uniformity (WithVal v)
      (WithZero (Multiplicative ℤ))).isUniformInducing_iff
    (Valued.hasBasis_uniformity (IndexCongruenceLocalField P r level)
      (WithZero (Multiplicative ℤ)))).mpr
  constructor
  · intro γ _
    obtain ⟨x, hx⟩ := hsource (embedding γ.1)
    let δ := Units.mk0 (Valued.v.restrict x) (by
      intro hx0
      have hxzero : x = 0 := by
        exact (Valuation.zero_iff Valued.v).mp
          ((Valuation.restrict_eq_zero_iff (v := Valued.v)).mp hx0)
      subst x
      have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
      exact hγ0 (hx.symm.trans (map_zero Valued.v)))
    refine ⟨δ, trivial, ?_⟩
    intro a b hab
    simp only [Set.mem_setOf_eq] at hab ⊢
    rw [Valuation.restrict_lt_iff_lt_embedding] at hab ⊢
    rw [← map_sub, indexLaurentPullbackValuedEmbedding_valuation]
    change Valued.v (b - a) <
      MonoidWithZeroHom.ValueGroup₀.embedding (Valued.v.restrict x) at hab
    rw [Valuation.embedding_restrict, hx] at hab
    exact hab
  · intro δ _
    obtain ⟨z, hz⟩ := LaurentSeries.valuation_surjective
      (ResidueField P r level) (embedding δ.1)
    let γ := Units.mk0 (Valued.v.restrict z) (by
      intro hz0
      have hzzero : z = 0 := by
        exact (Valuation.zero_iff Valued.v).mp
          ((Valuation.restrict_eq_zero_iff (v := Valued.v)).mp hz0)
      subst z
      have hδ0 : MonoidWithZeroHom.ValueGroup₀.embedding δ.1 ≠ 0 := by simp
      exact hδ0 (hz.symm.trans (map_zero Valued.v)))
    refine ⟨γ, trivial, ?_⟩
    intro a b hab
    simp only [Set.mem_setOf_eq] at hab ⊢
    rw [Valuation.restrict_lt_iff_lt_embedding] at hab ⊢
    rw [← map_sub, indexLaurentPullbackValuedEmbedding_valuation] at hab
    change Valued.v (b - a) <
      MonoidWithZeroHom.ValueGroup₀.embedding (Valued.v.restrict z) at hab
    rw [Valuation.embedding_restrict, hz] at hab
    exact hab

/-- The concrete Laurent local field, packaged as an abstract completion of
the global field with the pulled-back selected-place valuation. -/
noncomputable def indexLaurentLocalFieldCompletionPkg
    (P : BasePrime) (r : Rank) (level : Nat) :
    AbstractCompletion
      (WithVal (indexLaurentPullbackValuation P r level)) where
  space := IndexCongruenceLocalField P r level
  coe := indexLaurentPullbackValuedEmbedding P r level
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing :=
    isUniformInducing_indexLaurentPullbackValuedEmbedding P r level
  dense := denseRange_indexLaurentPullbackValuedEmbedding P r level

/-- Canonical uniform equivalence from the abstract completion for the
pulled-back Laurent valuation to the concrete Laurent local field. -/
noncomputable def indexLaurentPullbackCompletionEquivLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexLaurentPullbackCompletion P r level ≃ᵤ
      IndexCongruenceLocalField P r level :=
  AbstractCompletion.compareEquiv UniformSpace.Completion.cPkg
    (indexLaurentLocalFieldCompletionPkg P r level)

@[simp] theorem indexLaurentPullbackCompletionEquivLocalField_coe
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : WithVal (indexLaurentPullbackValuation P r level)) :
    indexLaurentPullbackCompletionEquivLocalField P r level x =
      indexLaurentPullbackValuedEmbedding P r level x :=
  AbstractCompletion.compare_coe UniformSpace.Completion.cPkg
    (indexLaurentLocalFieldCompletionPkg P r level) x

/-- The canonical completion comparison is also a ring equivalence. -/
noncomputable def indexLaurentPullbackCompletionRingEquivLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexLaurentPullbackCompletion P r level ≃+*
      IndexCongruenceLocalField P r level := by
  let f := indexLaurentPullbackValuedEmbedding P r level
  let hf : Continuous f :=
    (isUniformInducing_indexLaurentPullbackValuedEmbedding
      P r level).uniformContinuous.continuous
  let F := UniformSpace.Completion.extensionHom f hf
  apply RingEquiv.ofBijective F
  have hF : (F : IndexLaurentPullbackCompletion P r level →
      IndexCongruenceLocalField P r level) =
      indexLaurentPullbackCompletionEquivLocalField P r level := rfl
  rw [hF]
  exact (indexLaurentPullbackCompletionEquivLocalField P r level).bijective

theorem indexLaurentPullbackCompletionRingEquiv_eq_uniformEquiv
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexLaurentPullbackCompletion P r level) :
    indexLaurentPullbackCompletionRingEquivLocalField P r level x =
      indexLaurentPullbackCompletionEquivLocalField P r level x :=
  rfl

/-- The completion comparison preserves the full selected-place valuation,
not merely its topology. -/
theorem indexLaurentPullbackCompletionEquivLocalField_valuation
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexLaurentPullbackCompletion P r level) :
    Valued.v
        (indexLaurentPullbackCompletionEquivLocalField P r level x) =
      Valued.v x := by
  let v := indexLaurentPullbackValuation P r level
  have htarget : Continuous
      (Valued.v : IndexCongruenceLocalField P r level →
        WithZero (Multiplicative ℤ)) :=
    Valued.continuous_valuation_of_surjective
      (LaurentSeries.valuation_surjective (ResidueField P r level))
  have hsourceSurj : Function.Surjective
      (Valued.v : IndexLaurentPullbackCompletion P r level →
        WithZero (Multiplicative ℤ)) :=
    (Valued.valuedCompletion_surjective_iff
      (K := WithVal v) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      (by simpa [v] using
        indexLaurentPullbackWithVal_valuation_surjective P r level)
  have hsource : Continuous
      (Valued.v : IndexLaurentPullbackCompletion P r level →
        WithZero (Multiplicative ℤ)) :=
    Valued.continuous_valuation_of_surjective hsourceSurj
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        (htarget.comp
          (indexLaurentPullbackCompletionEquivLocalField
            P r level).continuous)
        hsource
  | ih a =>
      rw [indexLaurentPullbackCompletionEquivLocalField_coe,
        indexLaurentPullbackValuedEmbedding_valuation,
        Valued.valuedCompletion_apply]

theorem indexLaurentPullbackCompletionEquivLocalField_le_one_iff
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexLaurentPullbackCompletion P r level) :
    Valued.v x ≤ 1 ↔
      Valued.v
        (indexLaurentPullbackCompletionEquivLocalField P r level x) ≤ 1 := by
  rw [indexLaurentPullbackCompletionEquivLocalField_valuation]

/-- The intrinsic height-one adic completion is the concrete selected
Laurent-series local field as a ring. -/
noncomputable def indexAdicCompletionRingEquivLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicCompletion P r level ≃+*
      IndexCongruenceLocalField P r level :=
  (indexAdicCompletionRingEquivLaurentPullbackCompletion P r level).trans
    (indexLaurentPullbackCompletionRingEquivLocalField P r level)

/-- The intrinsic selected-place completion and the explicit Laurent local
field are uniformly equivalent.  This is the topological form of
`indexAdicCompletionRingEquivLocalField`, used by the finite-adele
projection below. -/
noncomputable def indexAdicCompletionEquivLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicCompletion P r level ≃ᵤ
      IndexCongruenceLocalField P r level :=
  (indexAdicCompletionEquivLaurentPullbackCompletion P r level).trans
    (indexLaurentPullbackCompletionEquivLocalField P r level)

theorem indexAdicCompletionRingEquivLocalField_eq_uniformEquiv
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexCongruenceAdicCompletion P r level) :
    indexAdicCompletionRingEquivLocalField P r level x =
      indexAdicCompletionEquivLocalField P r level x :=
  rfl

@[simp] theorem indexAdicCompletionRingEquivLocalField_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat) (x : FunctionField P) :
    indexAdicCompletionRingEquivLocalField P r level
        (algebraMap (FunctionField P)
          (IndexCongruenceAdicCompletion P r level) x) =
      functionFieldToIndexCongruenceLocalField P r level x := by
  rw [indexAdicCompletionRingEquivLocalField,
    RingEquiv.trans_apply,
    indexAdicCompletionRingEquiv_eq_uniformEquiv,
    indexAdicCompletionEquivLaurentPullbackCompletion_algebraMap,
    indexLaurentPullbackCompletionRingEquiv_eq_uniformEquiv,
    indexLaurentPullbackCompletionEquivLocalField_coe]
  rfl

/-- The comparison between the abstract selected completion and the
concrete Laurent field respects the actual global function-field
embedding. -/
noncomputable def indexAdicCompletionAlgEquivLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicCompletion P r level ≃ₐ[FunctionField P]
      IndexCongruenceLocalField P r level where
  __ := indexAdicCompletionRingEquivLocalField P r level
  commutes' x :=
    indexAdicCompletionRingEquivLocalField_algebraMap P r level x

/-- The construction's global cyclic algebra represented over the selected
Laurent field.  This maps the entries of its original splitting-field
matrix representation along the explicitly constructed local embedding. -/
noncomputable def cyclicAlgebraToIndexLocalMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    CyclicAlgebra P r →ₐ[FunctionField P]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level) where
  toFun x := x.1.map
    (splittingFunctionFieldToIndexCongruenceLocalField P r level)
  map_one' := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.one_apply, hij]
  map_mul' x y := Matrix.map_mul
  map_zero' := by
    apply Matrix.ext
    intro i j
    simp
  map_add' x y := by
    apply Matrix.ext
    intro i j
    simp
  commutes' x := by
    change
      (algebraMap (FunctionField P)
        (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) x).map
          (splittingFunctionFieldToIndexCongruenceLocalField P r level) =
        algebraMap (FunctionField P)
          (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (IndexCongruenceLocalField P r level)) x
    apply Matrix.map_algebraMap
    · exact map_zero
        (splittingFunctionFieldToIndexCongruenceLocalField P r level)
    · exact
        splittingFunctionFieldToIndexCongruenceLocalField_functionFieldEmbedding
          P r level x

/-- Scalar matrices from the selected abstract completion, expressed over
the concrete Laurent field. -/
noncomputable def indexAdicCompletionToIndexLocalMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicCompletion P r level →ₐ[FunctionField P]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level) :=
  ((Algebra.ofId (IndexCongruenceLocalField P r level)
    (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (IndexCongruenceLocalField P r level))).restrictScalars
        (FunctionField P)).comp
    (indexAdicCompletionAlgEquivLocalField P r level).toAlgHom

/-- The actual selected local splitting map of the cyclic algebra. -/
noncomputable def indexAdicCyclicAlgebraToIndexLocalMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexAdicCyclicAlgebra P r level →ₐ[FunctionField P]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level) :=
  Algebra.TensorProduct.lift
    (indexAdicCompletionToIndexLocalMatrix P r level)
    (cyclicAlgebraToIndexLocalMatrix P r level)
    (fun a x => by
      change Commute
        (algebraMap (IndexCongruenceLocalField P r level)
          (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (IndexCongruenceLocalField P r level))
          (indexAdicCompletionAlgEquivLocalField P r level a))
        ((x.1.map
          (splittingFunctionFieldToIndexCongruenceLocalField
            P r level)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (IndexCongruenceLocalField P r level))
      exact Algebra.commutes _ _)

@[simp] theorem indexAdicCyclicAlgebraToIndexLocalMatrix_tmul
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : IndexCongruenceAdicCompletion P r level)
    (x : CyclicAlgebra P r) :
    indexAdicCyclicAlgebraToIndexLocalMatrix P r level
        (TensorProduct.tmul (FunctionField P) a x) =
      (indexAdicCompletionAlgEquivLocalField P r level a) •
        cyclicAlgebraToIndexLocalMatrix P r level x := by
  rw [indexAdicCyclicAlgebraToIndexLocalMatrix,
    Algebra.TensorProduct.lift_tmul]
  rw [Algebra.smul_def]
  rfl

/-- The completed construction-owned cyclic family, embedded from power
series into the selected Laurent field. -/
noncomputable def indexLocalCyclicBasisVector
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (IndexCongruenceLocalField P r level) :=
  (completedIndexCyclicBasisVector P r level p).map
    (HahnSeries.ofPowerSeries ℤ (ResidueField P r level))

/-- The local cyclic family remains a basis after passing from the completed
integer ring to its Laurent fraction field. -/
theorem indexLocalCyclicBasisVector_det_isUnit
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsUnit ((Matrix.stdBasis (IndexCongruenceLocalField P r level)
      (Fin r.matrixRank) (Fin r.matrixRank)).det
        (indexLocalCyclicBasisVector P r level)) := by
  let f := HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
  have hunit :=
    (completedIndexCyclicBasisVector_det_isUnit P r level).map f
  have hmap :
      f ((Matrix.stdBasis (PowerSeries (ResidueField P r level))
        (Fin r.matrixRank) (Fin r.matrixRank)).det
          (completedIndexCyclicBasisVector P r level)) =
        (Matrix.stdBasis (IndexCongruenceLocalField P r level)
          (Fin r.matrixRank) (Fin r.matrixRank)).det
            (indexLocalCyclicBasisVector P r level) := by
    simp only [Module.Basis.det_apply]
    rw [RingHom.map_det]
    apply congrArg Matrix.det
    apply Matrix.ext
    intro p q
    rw [RingHom.mapMatrix_apply, Matrix.map_apply,
      Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply]
    rw [show (Matrix.stdBasis (PowerSeries (ResidueField P r level))
        (Fin r.matrixRank) (Fin r.matrixRank)).repr
          (completedIndexCyclicBasisVector P r level q) p =
        completedIndexCyclicBasisVector P r level q p.1 p.2 by
          simp [Matrix.stdBasis]]
    rw [show (Matrix.stdBasis (IndexCongruenceLocalField P r level)
        (Fin r.matrixRank) (Fin r.matrixRank)).repr
          (indexLocalCyclicBasisVector P r level q) p =
        indexLocalCyclicBasisVector P r level q p.1 p.2 by
          simp [Matrix.stdBasis]]
    rfl
  rwa [hmap] at hunit

/-- The actual cyclic basis of the selected Laurent matrix algebra. -/
noncomputable def indexLocalCyclicBasis
    (P : BasePrime) (r : Rank) (level : Nat) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (IndexCongruenceLocalField P r level)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level)) := by
  let hbasis := (Module.Basis.is_basis_iff_det
    (Matrix.stdBasis (IndexCongruenceLocalField P r level)
      (Fin r.matrixRank) (Fin r.matrixRank))).mpr
        (indexLocalCyclicBasisVector_det_isUnit P r level)
  exact Module.Basis.mk hbasis.1 hbasis.2.ge

@[simp] theorem indexLocalCyclicBasis_apply
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    indexLocalCyclicBasis P r level p =
      indexLocalCyclicBasisVector P r level p := by
  simp [indexLocalCyclicBasis]

/-- The cyclic algebra after scalar extension directly to the concrete
selected Laurent field. -/
noncomputable abbrev IndexLocalCyclicAlgebra
    (P : BasePrime) (r : Rank) (level : Nat) :=
  TensorProduct (FunctionField P)
    (IndexCongruenceLocalField P r level) (CyclicAlgebra P r)

/-- Base change from the abstract adic realization to the concrete Laurent
realization of the selected local cyclic algebra. -/
noncomputable def indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexAdicCyclicAlgebra P r level →ₐ[FunctionField P]
      IndexLocalCyclicAlgebra P r level :=
  Algebra.TensorProduct.map
    (indexAdicCompletionAlgEquivLocalField P r level).toAlgHom
    (AlgHom.id (FunctionField P) (CyclicAlgebra P r))

theorem indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra_bijective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Bijective
      (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra P r level) :=
  Algebra.TensorProduct.map_bijective
    (indexAdicCompletionAlgEquivLocalField P r level).bijective
    Function.bijective_id

/-- The abstract adic and concrete Laurent realizations of the selected
local cyclic algebra are canonically equivalent. -/
noncomputable def indexAdicCyclicAlgebraEquivIndexLocalCyclicAlgebra
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexAdicCyclicAlgebra P r level ≃ₐ[FunctionField P]
      IndexLocalCyclicAlgebra P r level :=
  AlgEquiv.ofBijective
    (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra P r level)
    (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra_bijective P r level)

/-- The Laurent scalar extension represented in the full selected local
matrix algebra. -/
noncomputable def indexLocalCyclicAlgebraToMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexLocalCyclicAlgebra P r level
      →ₐ[IndexCongruenceLocalField P r level]
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level) :=
  Algebra.TensorProduct.lift
    (Algebra.ofId (IndexCongruenceLocalField P r level)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level)))
    (cyclicAlgebraToIndexLocalMatrix P r level)
    (fun a x => by
      change Commute
        (algebraMap (IndexCongruenceLocalField P r level)
          (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (IndexCongruenceLocalField P r level)) a)
        (cyclicAlgebraToIndexLocalMatrix P r level x)
      exact Algebra.commutes _ _)

@[simp] theorem indexLocalCyclicAlgebraToMatrix_tmul
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : IndexCongruenceLocalField P r level)
    (x : CyclicAlgebra P r) :
    indexLocalCyclicAlgebraToMatrix P r level
        (TensorProduct.tmul (FunctionField P) a x) =
      a • cyclicAlgebraToIndexLocalMatrix P r level x := by
  rw [indexLocalCyclicAlgebraToMatrix, Algebra.TensorProduct.lift_tmul,
    Algebra.smul_def]
  rfl

@[simp] theorem indexLocalCyclicAlgebraToMatrix_includeRight
    (P : BasePrime) (r : Rank) (level : Nat) (x : CyclicAlgebra P r) :
    indexLocalCyclicAlgebraToMatrix P r level
        (Algebra.TensorProduct.includeRight x) =
      cyclicAlgebraToIndexLocalMatrix P r level x := by
  rw [Algebra.TensorProduct.includeRight_apply,
    indexLocalCyclicAlgebraToMatrix_tmul, one_smul]

/-- The global cyclic basis becomes the completed cyclic basis at the
selected Laurent place. -/
theorem cyclicAlgebraToIndexLocalMatrix_basis
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    cyclicAlgebraToIndexLocalMatrix P r level
        (functionFieldCyclicBasis P r p) =
      indexLocalCyclicBasisVector P r level p := by
  change ((functionFieldCyclicBasis P r p : CyclicAlgebra P r).1).map
      (splittingFunctionFieldToIndexCongruenceLocalField P r level) = _
  rw [functionFieldCyclicBasis_apply]
  change (splittingCyclicBasisVector P r p).map
      (splittingFunctionFieldToIndexCongruenceLocalField P r level) = _
  rw [← orderIndexCyclicBasisVector_to_global P r p,
    Matrix.map_map]
  change (orderIndexCyclicBasisVector P r p).map
      (fun x => splittingFunctionFieldToIndexCongruenceLocalField P r level
        (constantArithmeticToSplittingFunctionField P r x)) =
    ((orderIndexCyclicBasisVector P r p).map
      (indexCompletedArithmeticEval P r level)).map
        (HahnSeries.ofPowerSeries ℤ (ResidueField P r level))
  rw [Matrix.map_map]
  congr 1
  funext x
  exact DFunLike.congr_fun
    (splittingFunctionFieldToIndexCongruenceLocalField_constantArithmetic
      P r level) x

/-- The selected local splitting map sends the construction-owned adic
cyclic basis to the construction-owned Laurent matrix basis. -/
@[simp] theorem indexAdicCyclicAlgebraToIndexLocalMatrix_basis
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    indexAdicCyclicAlgebraToIndexLocalMatrix P r level
        (indexAdicCyclicBasis P r level p) =
      indexLocalCyclicBasis P r level p := by
  rw [indexAdicCyclicBasis, Module.Basis.baseChange_apply,
    indexAdicCyclicAlgebraToIndexLocalMatrix_tmul, map_one, one_smul,
    cyclicAlgebraToIndexLocalMatrix_basis,
    indexLocalCyclicBasis_apply]

/-- Extending a completed matrix coefficientwise to Laurent series is the
same as extending its completed cyclic-basis expansion coefficientwise. -/
theorem indexLocalCyclicBasis_sum_completed_equivFun
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))) :
    (∑ p, HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
        ((completedIndexCyclicBasis P r level).equivFun M p) •
          indexLocalCyclicBasis P r level p) =
      M.map (HahnSeries.ofPowerSeries ℤ (ResidueField P r level)) := by
  have hsum := (completedIndexCyclicBasis P r level).sum_equivFun M
  apply Matrix.ext
  intro i j
  have hij := congrArg
    (fun N : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)) =>
        HahnSeries.ofPowerSeries ℤ (ResidueField P r level) (N i j)) hsum
  simpa [indexLocalCyclicBasis_apply, indexLocalCyclicBasisVector,
    completedIndexCyclicBasis_apply, Matrix.sum_apply] using hij

/-- Reducing a completed matrix coefficientwise is the same as reducing
its completed cyclic-basis expansion coefficientwise. -/
theorem indexCyclicBasis_sum_completed_equivFun_constantCoeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))) :
    (∑ p, PowerSeries.constantCoeff
        ((completedIndexCyclicBasis P r level).equivFun M p) •
          indexCyclicBasis P r level p) =
      M.map PowerSeries.constantCoeff := by
  have hsum := (completedIndexCyclicBasis P r level).sum_equivFun M
  apply Matrix.ext
  intro i j
  have hij := congrArg
    (fun N : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)) =>
        PowerSeries.constantCoeff (N i j)) hsum
  have hred (p : Fin r.matrixRank × Fin r.matrixRank) :
      PowerSeries.constantCoeff
          (completedIndexCyclicBasisVector P r level p i j) =
        indexCyclicBasisVector P r level p i j :=
    congrFun (congrFun
      (completedIndexCyclicBasisVector_reduction P r level p) i) j
  simpa [indexCyclicBasis_apply, completedIndexCyclicBasis_apply,
    Matrix.sum_apply, hred] using hij

/-- The base-changed global cyclic basis of the Laurent scalar extension. -/
noncomputable def indexLocalCyclicScalarExtensionBasis
    (P : BasePrime) (r : Rank) (level : Nat) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (IndexCongruenceLocalField P r level)
      (IndexLocalCyclicAlgebra P r level) :=
  (functionFieldCyclicBasis P r).baseChange
    (IndexCongruenceLocalField P r level)

@[simp] theorem indexLocalCyclicAlgebraToMatrix_basis
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    indexLocalCyclicAlgebraToMatrix P r level
        (indexLocalCyclicScalarExtensionBasis P r level p) =
      indexLocalCyclicBasis P r level p := by
  rw [indexLocalCyclicScalarExtensionBasis, Module.Basis.baseChange_apply,
    indexLocalCyclicAlgebraToMatrix_tmul,
    cyclicAlgebraToIndexLocalMatrix_basis,
    indexLocalCyclicBasis_apply, one_smul]

theorem indexLocalCyclicAlgebraToMatrix_bijective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Bijective (indexLocalCyclicAlgebraToMatrix P r level) := by
  let e := (indexLocalCyclicScalarExtensionBasis P r level).equiv
    (indexLocalCyclicBasis P r level) (Equiv.refl _)
  have heq : (indexLocalCyclicAlgebraToMatrix P r level).toLinearMap =
      e.toLinearMap := by
    apply (indexLocalCyclicScalarExtensionBasis P r level).ext
    intro p
    change indexLocalCyclicAlgebraToMatrix P r level
        (indexLocalCyclicScalarExtensionBasis P r level p) =
      e (indexLocalCyclicScalarExtensionBasis P r level p)
    rw [indexLocalCyclicAlgebraToMatrix_basis]
    exact (Module.Basis.equiv_apply
      (indexLocalCyclicScalarExtensionBasis P r level) p
      (indexLocalCyclicBasis P r level) (Equiv.refl _)).symm
  rw [show (indexLocalCyclicAlgebraToMatrix P r level : _ → _) = e by
    funext x
    exact DFunLike.congr_fun heq x]
  exact e.bijective

/-- The selected Laurent scalar extension is the full matrix algebra. -/
noncomputable def indexLocalCyclicAlgebraEquivMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexLocalCyclicAlgebra P r level
      ≃ₐ[IndexCongruenceLocalField P r level]
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level) :=
  AlgEquiv.ofBijective (indexLocalCyclicAlgebraToMatrix P r level)
    (indexLocalCyclicAlgebraToMatrix_bijective P r level)

/-- Reassembly from the selected local cyclic coordinates is continuous in
the coefficientwise matrix topology. -/
theorem continuous_indexLocalCyclicBasis_equivFun_symm
    (P : BasePrime) (r : Rank) (level : Nat) :
    Continuous
      (indexLocalCyclicBasis P r level).equivFun.symm := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [Module.Basis.equivFun_symm_apply]
  fun_prop

/-- Coordinates of a global cyclic-algebra point after embedding each
global coefficient in the selected Laurent completion. -/
noncomputable def cyclicAlgebraToIndexLocalCoordinates
    (P : BasePrime) (r : Rank) (level : Nat) :
    CyclicAlgebra P r →
      ((Fin r.matrixRank × Fin r.matrixRank) →
        IndexCongruenceLocalField P r level) :=
  fun x p => functionFieldToIndexCongruenceLocalField P r level
    ((functionFieldCyclicBasis P r).equivFun x p)

/-- The global cyclic coordinates are dense in the full tuple of selected
local coordinates. -/
theorem denseRange_cyclicAlgebraToIndexLocalCoordinates
    (P : BasePrime) (r : Rank) (level : Nat) :
    DenseRange (cyclicAlgebraToIndexLocalCoordinates P r level) := by
  let f : ((Fin r.matrixRank × Fin r.matrixRank) → FunctionField P) →
      ((Fin r.matrixRank × Fin r.matrixRank) →
        IndexCongruenceLocalField P r level) :=
    Pi.map fun _ => functionFieldToIndexCongruenceLocalField P r level
  have hf : DenseRange f :=
    DenseRange.piMap fun _ =>
      denseRange_functionFieldToIndexCongruenceLocalField P r level
  have hsurj : Function.Surjective
      (functionFieldCyclicBasis P r).equivFun :=
    (functionFieldCyclicBasis P r).equivFun.surjective
  rw [show cyclicAlgebraToIndexLocalCoordinates P r level =
      f ∘ (functionFieldCyclicBasis P r).equivFun by rfl,
    DenseRange, Set.range_comp, hsurj.range_eq, Set.image_univ]
  exact hf

/-- The construction's global cyclic division algebra is additively dense
in its full split matrix algebra at the selected congruence completion. -/
theorem denseRange_cyclicAlgebraToIndexLocalMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    DenseRange (cyclicAlgebraToIndexLocalMatrix P r level) := by
  let assemble := (indexLocalCyclicBasis P r level).equivFun.symm
  have hassemble : DenseRange assemble :=
    assemble.surjective.denseRange
  have hcomp : DenseRange
      (assemble ∘ cyclicAlgebraToIndexLocalCoordinates P r level) :=
    hassemble.comp
      (denseRange_cyclicAlgebraToIndexLocalCoordinates P r level)
      (continuous_indexLocalCyclicBasis_equivFun_symm P r level)
  have heq : assemble ∘ cyclicAlgebraToIndexLocalCoordinates P r level =
      cyclicAlgebraToIndexLocalMatrix P r level := by
    funext x
    change assemble (cyclicAlgebraToIndexLocalCoordinates P r level x) = _
    rw [show assemble (cyclicAlgebraToIndexLocalCoordinates P r level x) =
        ∑ p, functionFieldToIndexCongruenceLocalField P r level
            ((functionFieldCyclicBasis P r).equivFun x p) •
          indexLocalCyclicBasis P r level p by
      exact Module.Basis.equivFun_symm_apply
        (indexLocalCyclicBasis P r level)
        (cyclicAlgebraToIndexLocalCoordinates P r level x)]
    conv_rhs =>
      rw [← (functionFieldCyclicBasis P r).sum_equivFun x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [map_smul, cyclicAlgebraToIndexLocalMatrix_basis,
      indexLocalCyclicBasis_apply]
    change functionFieldToIndexCongruenceLocalField P r level
        ((functionFieldCyclicBasis P r).equivFun x p) •
          indexLocalCyclicBasisVector P r level p =
      functionFieldToIndexCongruenceLocalField P r level
        ((functionFieldCyclicBasis P r).equivFun x p) •
          indexLocalCyclicBasisVector P r level p
    rfl
  rw [← heq]
  exact hcomp

/-- Over the selected Laurent field, the value map from `GL` to the ambient
matrix algebra is an open embedding.  Openness is the nonvanishing of the
continuous determinant; the inverse map is continuous on that locus by the
adjugate formula. -/
theorem isOpenEmbedding_indexLocalMatrix_unitsVal
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsOpenEmbedding
      (Units.val :
        (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level))ˣ →
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level)) := by
  have hinv : ContinuousOn Inv.inv
      {A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level) | IsUnit A} := by
    intro A hA
    apply (continuousAt_matrix_inv A ?_).continuousWithinAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀
      (((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero)
  have hembed : IsEmbedding
      (Units.val :
        (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level))ˣ →
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level)) :=
    Units.isEmbedding_val_mk' hinv fun u :
        (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level))ˣ => by
      apply Matrix.inv_eq_right_inv
      exact Units.mul_inv u
  refine ⟨hembed, ?_⟩
  have hrange : Set.range
      (Units.val :
        (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level))ˣ →
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level)) =
      {A | IsUnit A} := by
    ext A
    constructor
    · rintro ⟨u, rfl⟩
      exact u.isUnit
    · intro hA
      exact ⟨hA.unit, hA.unit_spec⟩
  rw [hrange]
  simpa [Matrix.isUnit_iff_isUnit_det] using
    ((isOpen_ne : IsOpen {z : IndexCongruenceLocalField P r level |
        z ≠ 0}).preimage continuous_id.matrix_det)

/-- The direct adic splitting map factors through the canonical
adic-to-Laurent base change. -/
theorem indexAdicCyclicAlgebraToIndexLocalMatrix_factorization
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexAdicCyclicAlgebraToIndexLocalMatrix P r level =
      ((indexLocalCyclicAlgebraToMatrix P r level).restrictScalars
        (FunctionField P)).comp
          (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra P r level) := by
  apply Algebra.TensorProduct.ext
  · ext a
    simp [indexAdicCyclicAlgebraToIndexLocalMatrix,
      indexAdicCompletionToIndexLocalMatrix,
      indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra,
      indexLocalCyclicAlgebraToMatrix]
  · ext x
    simp [indexAdicCyclicAlgebraToIndexLocalMatrix,
      indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra,
      indexLocalCyclicAlgebraToMatrix]

theorem indexAdicCyclicAlgebraToIndexLocalMatrix_bijective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Bijective
      (indexAdicCyclicAlgebraToIndexLocalMatrix P r level) := by
  rw [indexAdicCyclicAlgebraToIndexLocalMatrix_factorization]
  exact (indexLocalCyclicAlgebraToMatrix_bijective P r level).comp
    (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra_bijective P r level)

/-- The construction-owned cyclic division algebra really becomes the full
matrix algebra at the selected congruence completion. -/
noncomputable def indexAdicCyclicAlgebraEquivIndexLocalMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexAdicCyclicAlgebra P r level ≃ₐ[FunctionField P]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level) :=
  AlgEquiv.ofBijective
    (indexAdicCyclicAlgebraToIndexLocalMatrix P r level)
    (indexAdicCyclicAlgebraToIndexLocalMatrix_bijective P r level)

/-- Units of the actual selected Laurent scalar extension, identified with
the corresponding general-linear group. -/
noncomputable def indexLocalCyclicAlgebraUnitEquivGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexLocalCyclicAlgebra P r level)ˣ ≃*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level) :=
  Units.mapEquiv
    (indexLocalCyclicAlgebraEquivMatrix P r level).toMulEquiv

/-- Reduced norm on the actual selected Laurent scalar extension. -/
noncomputable def indexLocalCyclicAlgebraReducedNorm
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexLocalCyclicAlgebra P r level)ˣ →*
      (IndexCongruenceLocalField P r level)ˣ :=
  Matrix.GeneralLinearGroup.det.comp
    (indexLocalCyclicAlgebraUnitEquivGL P r level).toMonoidHom

/-- The genuine local reduced-norm-one group of the scalar-extended cyclic
division algebra. -/
noncomputable def IndexLocalCyclicAlgebraNormOne
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (IndexLocalCyclicAlgebra P r level)ˣ :=
  (indexLocalCyclicAlgebraReducedNorm P r level).ker

/-- At the selected congruence place, the genuine reduced-norm-one inner
form is exactly the standard special-linear group. -/
noncomputable def indexLocalCyclicAlgebraNormOneEquivSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexLocalCyclicAlgebraNormOne P r level ≃*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level) where
  toFun u :=
    ⟨((indexLocalCyclicAlgebraUnitEquivGL P r level u :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level)),
      congrArg Units.val u.property⟩
  invFun s :=
    ⟨(indexLocalCyclicAlgebraUnitEquivGL P r level).symm
        (Matrix.SpecialLinearGroup.toGL s), by
      change indexLocalCyclicAlgebraReducedNorm P r level
        ((indexLocalCyclicAlgebraUnitEquivGL P r level).symm
          (Matrix.SpecialLinearGroup.toGL s)) = 1
      rw [indexLocalCyclicAlgebraReducedNorm]
      simp⟩
  left_inv u := by
    apply Subtype.ext
    apply (indexLocalCyclicAlgebraUnitEquivGL P r level).injective
    apply Units.ext
    simp
    rfl
  right_inv s := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    apply Units.ext
    simp
    rfl
  map_mul' u v := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    apply Units.ext
    simp
    rfl

theorem indexAdicCompletionRingEquivLocalField_le_one_iff
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexCongruenceAdicCompletion P r level) :
    Valued.v x ≤ 1 ↔
      Valued.v (indexAdicCompletionRingEquivLocalField P r level x) ≤ 1 := by
  simpa [indexAdicCompletionRingEquivLocalField, RingEquiv.trans_apply,
    indexAdicCompletionRingEquiv_eq_uniformEquiv,
    indexLaurentPullbackCompletionRingEquiv_eq_uniformEquiv] using
    (indexAdicCompletionEquivLaurentPullbackCompletion_le_one_iff
      P r level x).trans
      (indexLaurentPullbackCompletionEquivLocalField_le_one_iff
        P r level
        (indexAdicCompletionEquivLaurentPullbackCompletion P r level x))

/-- The concrete valuation ring inside the selected Laurent local field. -/
noncomputable abbrev IndexCongruenceLocalIntegers
    (P : BasePrime) (r : Rank) (level : Nat) :=
  (Valued.v : Valuation (IndexCongruenceLocalField P r level) _).valuationSubring

/-- The intrinsic height-one adic integers are the concrete closed unit ball
inside the selected Laurent local field. -/
noncomputable def indexAdicIntegersRingEquivLocalIntegers
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicIntegers P r level ≃+*
      IndexCongruenceLocalIntegers P r level where
  toFun x :=
    ⟨indexAdicCompletionRingEquivLocalField P r level x,
      (indexAdicCompletionRingEquivLocalField_le_one_iff
        P r level x).mp x.property⟩
  invFun y := by
    let x := (indexAdicCompletionRingEquivLocalField P r level).symm y.1
    refine ⟨x, ?_⟩
    apply (indexAdicCompletionRingEquivLocalField_le_one_iff
      P r level x).mpr
    change Valued.v
      (indexAdicCompletionRingEquivLocalField P r level
        ((indexAdicCompletionRingEquivLocalField P r level).symm y.1)) ≤ 1
    rw [(indexAdicCompletionRingEquivLocalField P r level).apply_symm_apply]
    exact y.property
  left_inv x := by
    apply Subtype.ext
    exact (indexAdicCompletionRingEquivLocalField P r level).symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact (indexAdicCompletionRingEquivLocalField P r level).apply_symm_apply y
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (indexAdicCompletionRingEquivLocalField P r level) x.1 y.1
  map_add' x y := by
    apply Subtype.ext
    exact map_add (indexAdicCompletionRingEquivLocalField P r level) x.1 y.1

/-- The concrete Laurent closed unit ball is exactly the power-series ring,
as a ring equivalence rather than a set-level existence statement. -/
noncomputable def indexCongruenceLocalIntegersRingEquivPowerSeries
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceLocalIntegers P r level ≃+*
      PowerSeries (ResidueField P r level) := by
  let f : PowerSeries (ResidueField P r level) →+*
      IndexCongruenceLocalIntegers P r level :=
    (HahnSeries.ofPowerSeries ℤ (ResidueField P r level)).codRestrict
      (IndexCongruenceLocalIntegers P r level) (fun s => by
        rw [Valuation.mem_valuationSubring_iff,
          LaurentSeries.val_le_one_iff_eq_coe]
        exact ⟨s, rfl⟩)
  exact (RingEquiv.ofBijective f ⟨
    fun x y hxy =>
      HahnSeries.ofPowerSeries_injective
        (congr_arg Subtype.val hxy),
    fun z => by
      have hz := z.property
      rw [Valuation.mem_valuationSubring_iff,
        LaurentSeries.val_le_one_iff_eq_coe] at hz
      obtain ⟨s, hs⟩ := hz
      exact ⟨s, Subtype.ext hs⟩⟩).symm

/-- Final identification of the intrinsic selected-place adic integers with
the explicit power-series chart used by the finite-jet construction. -/
noncomputable def indexAdicIntegersRingEquivPowerSeries
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicIntegers P r level ≃+*
      PowerSeries (ResidueField P r level) :=
  (indexAdicIntegersRingEquivLocalIntegers P r level).trans
    (indexCongruenceLocalIntegersRingEquivPowerSeries P r level)

/-- A completed split matrix lifted coefficientwise to the intrinsic adic
cyclic algebra in the construction-owned completed cyclic basis. -/
noncomputable def indexCompletedMatrixToIndexAdicCyclicAlgebra
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))) :
    IndexAdicCyclicAlgebra P r level :=
  (indexAdicCyclicBasis P r level).equivFun.symm
    (fun p =>
      (((indexAdicIntegersRingEquivPowerSeries P r level).symm
        ((completedIndexCyclicBasis P r level).equivFun M p) :
          IndexCongruenceAdicIntegers P r level) :
            IndexCongruenceAdicCompletion P r level))

@[simp] theorem indexAdicCyclicBasis_equivFun_completedMatrixLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (indexAdicCyclicBasis P r level).equivFun
        (indexCompletedMatrixToIndexAdicCyclicAlgebra P r level M) p =
      (((indexAdicIntegersRingEquivPowerSeries P r level).symm
        ((completedIndexCyclicBasis P r level).equivFun M p) :
          IndexCongruenceAdicIntegers P r level) :
            IndexCongruenceAdicCompletion P r level) := by
  rw [indexCompletedMatrixToIndexAdicCyclicAlgebra]
  exact congrArg
    (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
      IndexCongruenceAdicCompletion P r level => f p)
    ((indexAdicCyclicBasis P r level).equivFun.apply_symm_apply
      (fun q =>
        (((indexAdicIntegersRingEquivPowerSeries P r level).symm
          ((completedIndexCyclicBasis P r level).equivFun M q) :
            IndexCongruenceAdicIntegers P r level) :
              IndexCongruenceAdicCompletion P r level)))

/-- The coefficientwise completed-matrix lift has integral adic cyclic
coordinates by construction. -/
theorem indexCompletedMatrixToIndexAdicCyclicAlgebra_mem_integral
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))) :
    indexCompletedMatrixToIndexAdicCyclicAlgebra P r level M ∈
      IndexAdicCyclicIntegralLattice P r level := by
  intro p
  rw [indexAdicCyclicBasis_equivFun_completedMatrixLift]
  exact ((indexAdicIntegersRingEquivPowerSeries P r level).symm
    ((completedIndexCyclicBasis P r level).equivFun M p)).property

/-- Integral elements of the selected intrinsic adic cyclic algebra,
bundled for residue reduction. -/
noncomputable abbrev IndexAdicCyclicIntegralElement
    (P : BasePrime) (r : Rank) (level : Nat) :=
  ↥(IndexAdicCyclicIntegralLattice P r level)

/-- Residue coordinates of an integral intrinsic adic cyclic element in
the construction-owned cyclic basis. -/
noncomputable def indexAdicCyclicIntegralReductionCoordinates
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicIntegralElement P r level) :
    Fin r.matrixRank × Fin r.matrixRank → ResidueField P r level :=
  fun p => PowerSeries.constantCoeff
    (indexAdicIntegersRingEquivPowerSeries P r level
      ⟨(indexAdicCyclicBasis P r level).equivFun x.1 p,
        x.property p⟩)

/-- Matrix residue reduction of an integral intrinsic adic cyclic element,
reconstructed in the actual selected finite cyclic basis. -/
noncomputable def indexAdicCyclicIntegralReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexAdicCyclicIntegralElement P r level →
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level) :=
  fun x => (indexCyclicBasis P r level).equivFun.symm
    (indexAdicCyclicIntegralReductionCoordinates P r level x)

/-- The explicit adic lift of a completed matrix reduces to the
coefficientwise constant-term reduction of that matrix. -/
theorem indexAdicCyclicIntegralReduction_completedMatrixLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))) :
    indexAdicCyclicIntegralReduction P r level
        ⟨indexCompletedMatrixToIndexAdicCyclicAlgebra P r level M,
          indexCompletedMatrixToIndexAdicCyclicAlgebra_mem_integral
            P r level M⟩ =
      M.map PowerSeries.constantCoeff := by
  rw [indexAdicCyclicIntegralReduction,
    Module.Basis.equivFun_symm_apply,
    ← indexCyclicBasis_sum_completed_equivFun_constantCoeff P r level M]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  let z : IndexCongruenceAdicIntegers P r level :=
    ⟨(indexAdicCyclicBasis P r level).equivFun
      (indexCompletedMatrixToIndexAdicCyclicAlgebra P r level M) p,
      (indexCompletedMatrixToIndexAdicCyclicAlgebra_mem_integral
        P r level M) p⟩
  have hz : z =
      (indexAdicIntegersRingEquivPowerSeries P r level).symm
        ((completedIndexCyclicBasis P r level).equivFun M p) := by
    apply Subtype.ext
    exact indexAdicCyclicBasis_equivFun_completedMatrixLift P r level M p
  change PowerSeries.constantCoeff
      (indexAdicIntegersRingEquivPowerSeries P r level z) = _
  rw [hz, (indexAdicIntegersRingEquivPowerSeries
    P r level).apply_symm_apply]

theorem indexCongruenceLocalIntegersRingEquivPowerSeries_ofPowerSeries
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : PowerSeries (ResidueField P r level)) :
    indexCongruenceLocalIntegersRingEquivPowerSeries P r level
        ⟨HahnSeries.ofPowerSeries ℤ (ResidueField P r level) s, by
          rw [Valuation.mem_valuationSubring_iff,
            LaurentSeries.val_le_one_iff_eq_coe]
          exact ⟨s, rfl⟩⟩ = s := by
  apply (indexCongruenceLocalIntegersRingEquivPowerSeries
    P r level).symm.injective
  rw [(indexCongruenceLocalIntegersRingEquivPowerSeries
    P r level).symm_apply_apply]
  rfl

/-- Pulling a power series back to the intrinsic adic integers and then
embedding it in the Laurent field gives the standard power-series
inclusion. -/
theorem indexAdicCompletionRingEquivLocalField_powerSeries_symm
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : PowerSeries (ResidueField P r level)) :
    indexAdicCompletionRingEquivLocalField P r level
        (((indexAdicIntegersRingEquivPowerSeries P r level).symm s :
          IndexCongruenceAdicIntegers P r level) :
            IndexCongruenceAdicCompletion P r level) =
      HahnSeries.ofPowerSeries ℤ (ResidueField P r level) s := by
  let z : IndexCongruenceAdicIntegers P r level :=
    (indexAdicIntegersRingEquivPowerSeries P r level).symm s
  let w : IndexCongruenceLocalIntegers P r level :=
    ⟨HahnSeries.ofPowerSeries ℤ (ResidueField P r level) s, by
      rw [Valuation.mem_valuationSubring_iff,
        LaurentSeries.val_le_one_iff_eq_coe]
      exact ⟨s, rfl⟩⟩
  have hz : indexCongruenceLocalIntegersRingEquivPowerSeries P r level
      (indexAdicIntegersRingEquivLocalIntegers P r level z) = s := by
    change indexAdicIntegersRingEquivPowerSeries P r level z = s
    exact (indexAdicIntegersRingEquivPowerSeries
      P r level).apply_symm_apply s
  have hw : indexCongruenceLocalIntegersRingEquivPowerSeries P r level w =
      s := by
    exact indexCongruenceLocalIntegersRingEquivPowerSeries_ofPowerSeries
      P r level s
  have hzw : indexAdicIntegersRingEquivLocalIntegers P r level z = w :=
    (indexCongruenceLocalIntegersRingEquivPowerSeries
      P r level).injective (hz.trans hw.symm)
  exact congrArg Subtype.val hzw

/-- The coefficientwise adic lift of a completed matrix has exactly the
original matrix, embedded coefficientwise in Laurent series, as its local
splitting matrix. -/
theorem indexAdicCyclicAlgebraToIndexLocalMatrix_completedMatrixLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))) :
    indexAdicCyclicAlgebraToIndexLocalMatrix P r level
        (indexCompletedMatrixToIndexAdicCyclicAlgebra P r level M) =
      M.map (HahnSeries.ofPowerSeries ℤ (ResidueField P r level)) := by
  rw [← indexLocalCyclicBasis_sum_completed_equivFun P r level M]
  conv_lhs =>
    rw [← (indexAdicCyclicBasis P r level).sum_equivFun
      (indexCompletedMatrixToIndexAdicCyclicAlgebra P r level M)]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hterm :
      (indexAdicCyclicBasis P r level).equivFun
          (indexCompletedMatrixToIndexAdicCyclicAlgebra P r level M) p •
        indexAdicCyclicBasis P r level p =
      TensorProduct.tmul (FunctionField P)
        ((indexAdicCyclicBasis P r level).equivFun
          (indexCompletedMatrixToIndexAdicCyclicAlgebra P r level M) p)
        (functionFieldCyclicBasis P r p) := by
    simp [indexAdicCyclicBasis, Module.Basis.baseChange_apply,
      TensorProduct.smul_tmul']
  rw [hterm, indexAdicCyclicAlgebraToIndexLocalMatrix_tmul,
    indexAdicCyclicBasis_equivFun_completedMatrixLift]
  change indexAdicCompletionRingEquivLocalField P r level
      (((indexAdicIntegersRingEquivPowerSeries P r level).symm
        ((completedIndexCyclicBasis P r level).equivFun M p) :
          IndexCongruenceAdicIntegers P r level) :
            IndexCongruenceAdicCompletion P r level) •
        cyclicAlgebraToIndexLocalMatrix P r level
          (functionFieldCyclicBasis P r p) = _
  rw [indexAdicCompletionRingEquivLocalField_powerSeries_symm,
    cyclicAlgebraToIndexLocalMatrix_basis,
    indexLocalCyclicBasis_apply]

/-- Vanishing of the selected residue coefficient is exactly strict
positive valuation in the concrete local integer ring. -/
theorem indexCongruenceLocalIntegers_constantCoeff_eq_zero_iff
    (P : BasePrime) (r : Rank) (level : Nat)
    (z : IndexCongruenceLocalIntegers P r level) :
    PowerSeries.constantCoeff
        (indexCongruenceLocalIntegersRingEquivPowerSeries P r level z) = 0 ↔
      Valued.v z.1 < 1 := by
  calc
    PowerSeries.constantCoeff
          (indexCongruenceLocalIntegersRingEquivPowerSeries P r level z) = 0 ↔
        ¬ IsUnit (PowerSeries.constantCoeff
          (indexCongruenceLocalIntegersRingEquivPowerSeries P r level z)) := by
      simp
    _ ↔ ¬ IsUnit
        (indexCongruenceLocalIntegersRingEquivPowerSeries P r level z) :=
      not_congr PowerSeries.isUnit_iff_constantCoeff.symm
    _ ↔ ¬ IsUnit z :=
      not_congr (isUnit_map_iff
        (indexCongruenceLocalIntegersRingEquivPowerSeries P r level) z)
    _ ↔ Valued.v z.1 < 1 :=
      Valuation.Integer.not_isUnit_iff_valuation_lt_one

/-! ## The selected coordinate of the arithmetic finite adeles -/

/-- Projection of the genuine arithmetic finite adele ring to the concrete
selected Laurent local field. -/
noncomputable def arithmeticFiniteAdeleAtIndexLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdeleRing P →+*
      IndexCongruenceLocalField P r level :=
  (indexAdicCompletionRingEquivLocalField P r level).toRingHom.comp
    (arithmeticFiniteAdeleAtIndexPlace P r level)

/-- A finite adele whose selected Laurent coordinate is prescribed and
whose remaining coordinates vanish. -/
noncomputable def arithmeticFiniteAdeleSupportedAtIndexLocalField
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexCongruenceLocalField P r level) :
    ArithmeticFiniteAdeleRing P :=
  arithmeticFiniteAdeleSupportedAtIndexPlace P r level
    ((indexAdicCompletionRingEquivLocalField P r level).symm x)

@[simp] theorem arithmeticFiniteAdeleAtIndexLocalField_supported
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexCongruenceLocalField P r level) :
    arithmeticFiniteAdeleAtIndexLocalField P r level
        (arithmeticFiniteAdeleSupportedAtIndexLocalField P r level x) = x := by
  simp [arithmeticFiniteAdeleAtIndexLocalField,
    arithmeticFiniteAdeleSupportedAtIndexLocalField]

/-- Projection from the genuine finite restricted product to the selected
concrete Laurent completion is onto. -/
theorem arithmeticFiniteAdeleAtIndexLocalField_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
      (arithmeticFiniteAdeleAtIndexLocalField P r level) := by
  intro x
  exact ⟨arithmeticFiniteAdeleSupportedAtIndexLocalField P r level x,
    arithmeticFiniteAdeleAtIndexLocalField_supported P r level x⟩

/-- Projection from the restricted product of arithmetic finite adeles to
the selected concrete local field is continuous. -/
theorem continuous_arithmeticFiniteAdeleAtIndexLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    Continuous (arithmeticFiniteAdeleAtIndexLocalField P r level) := by
  rw [show (arithmeticFiniteAdeleAtIndexLocalField P r level :
      ArithmeticFiniteAdeleRing P → IndexCongruenceLocalField P r level) =
      (indexAdicCompletionEquivLocalField P r level) ∘
        (fun a : ArithmeticFiniteAdeleRing P =>
          a (indexCongruencePlace P r level)) by
    funext a
    rw [Function.comp_apply, ←
      indexAdicCompletionRingEquivLocalField_eq_uniformEquiv]
    rfl]
  exact (indexAdicCompletionEquivLocalField P r level).continuous.comp
    (RestrictedProduct.continuous_eval (indexCongruencePlace P r level))

@[simp] theorem arithmeticFiniteAdeleAtIndexLocalField_diagonal
    (P : BasePrime) (r : Rank) (level : Nat) (x : FunctionField P) :
    arithmeticFiniteAdeleAtIndexLocalField P r level
        (functionFieldToArithmeticFiniteAdeles P x) =
      functionFieldToIndexCongruenceLocalField P r level x := by
  rw [arithmeticFiniteAdeleAtIndexLocalField, RingHom.comp_apply,
    arithmeticFiniteAdeleAtIndexPlace_diagonal]
  change indexAdicCompletionRingEquivLocalField P r level
      (algebraMap (FunctionField P)
        (IndexCongruenceAdicCompletion P r level) x) = _
  exact indexAdicCompletionRingEquivLocalField_algebraMap P r level x

/-- Arithmetic finite adeles integral at the selected congruence place. -/
noncomputable def ArithmeticFiniteAdelesIntegralAtIndex
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subring (ArithmeticFiniteAdeleRing P) :=
  (IndexCongruenceLocalIntegers P r level).toSubring.comap
    (arithmeticFiniteAdeleAtIndexLocalField P r level)

/-- Integrality at the selected congruence coordinate is an open condition
in the genuine arithmetic finite-adele ring. -/
theorem isOpen_arithmeticFiniteAdelesIntegralAtIndex
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsOpen (ArithmeticFiniteAdelesIntegralAtIndex P r level :
      Set (ArithmeticFiniteAdeleRing P)) := by
  exact (Valued.isOpen_valuationSubring
    (IndexCongruenceLocalField P r level)).preimage
      (continuous_arithmeticFiniteAdeleAtIndexLocalField P r level)

/-- An adele integral at every finite place is, in particular, integral at
the selected congruence place. -/
noncomputable def arithmeticIntegralFiniteAdelesToIntegralAtIndex
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticIntegralFiniteAdeles P →+*
      ArithmeticFiniteAdelesIntegralAtIndex P r level where
  toFun a := ⟨a.1, by
    change Valued.v
        (indexAdicCompletionRingEquivLocalField P r level
          (a.1 (indexCongruencePlace P r level))) ≤ 1
    apply (indexAdicCompletionRingEquivLocalField_le_one_iff
      P r level (a.1 (indexCongruencePlace P r level))).mp
    exact a.property (indexCongruencePlace P r level)⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- Every element of the actual S-arithmetic coefficient ring is integral
at the selected coordinate of its finite-adele diagonal. -/
theorem functionFieldToArithmeticFiniteAdeles_algebraMap_mem_integralAtIndex
    (P : BasePrime) (r : Rank) (level : Nat) (a : ArithmeticRing P) :
    functionFieldToArithmeticFiniteAdeles P
        (algebraMap (ArithmeticRing P) (FunctionField P) a) ∈
      ArithmeticFiniteAdelesIntegralAtIndex P r level := by
  change arithmeticFiniteAdeleAtIndexLocalField P r level
      (functionFieldToArithmeticFiniteAdeles P
        (algebraMap (ArithmeticRing P) (FunctionField P) a)) ∈
    IndexCongruenceLocalIntegers P r level
  rw [arithmeticFiniteAdeleAtIndexLocalField_diagonal,
    functionFieldToIndexCongruenceLocalField_algebraMap]
  rw [Valuation.mem_valuationSubring_iff,
    LaurentSeries.val_le_one_iff_eq_coe]
  exact ⟨indexCompletedBaseArithmeticEval P r level a, rfl⟩

/-- Selected integral coordinate, bundled in the concrete Laurent
valuation ring. -/
noncomputable def arithmeticFiniteAdeleIntegralAtIndexToLocalIntegers
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdelesIntegralAtIndex P r level →+*
      IndexCongruenceLocalIntegers P r level where
  toFun a := ⟨arithmeticFiniteAdeleAtIndexLocalField P r level a.1,
    a.property⟩
  map_one' := Subtype.ext (map_one
    (arithmeticFiniteAdeleAtIndexLocalField P r level))
  map_mul' a b := Subtype.ext (map_mul
    (arithmeticFiniteAdeleAtIndexLocalField P r level) a.1 b.1)
  map_zero' := Subtype.ext (map_zero
    (arithmeticFiniteAdeleAtIndexLocalField P r level))
  map_add' a b := Subtype.ext (map_add
    (arithmeticFiniteAdeleAtIndexLocalField P r level) a.1 b.1)

@[simp] theorem arithmeticFiniteAdeleIntegralAtIndexToLocalIntegers_diagonal
    (P : BasePrime) (r : Rank) (level : Nat) (a : ArithmeticRing P) :
    arithmeticFiniteAdeleIntegralAtIndexToLocalIntegers P r level
        ⟨functionFieldToArithmeticFiniteAdeles P
            (algebraMap (ArithmeticRing P) (FunctionField P) a),
          functionFieldToArithmeticFiniteAdeles_algebraMap_mem_integralAtIndex
            P r level a⟩ =
      ⟨HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
          (indexCompletedBaseArithmeticEval P r level a), by
        rw [Valuation.mem_valuationSubring_iff,
          LaurentSeries.val_le_one_iff_eq_coe]
        exact ⟨indexCompletedBaseArithmeticEval P r level a, rfl⟩⟩ := by
  apply Subtype.ext
  change arithmeticFiniteAdeleAtIndexLocalField P r level
      (functionFieldToArithmeticFiniteAdeles P
        (algebraMap (ArithmeticRing P) (FunctionField P) a)) = _
  rw [arithmeticFiniteAdeleAtIndexLocalField_diagonal,
    functionFieldToIndexCongruenceLocalField_algebraMap]
  rfl

/-- Residue reduction at the selected coordinate, defined on the exact
integral open subring of the arithmetic finite adeles. -/
noncomputable def arithmeticFiniteAdeleIntegralAtIndexReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdelesIntegralAtIndex P r level →+*
      ResidueField P r level :=
  PowerSeries.constantCoeff.comp
    ((indexCongruenceLocalIntegersRingEquivPowerSeries P r level).toRingHom.comp
      (arithmeticFiniteAdeleIntegralAtIndexToLocalIntegers P r level))

/-- The kernel of selected-place residue reduction is open in the selected
integral finite-adele subring.  This is the exact congruence neighbourhood
used to turn adelic density into finite reduction surjectivity. -/
theorem isOpen_ker_arithmeticFiniteAdeleIntegralAtIndexReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsOpen (RingHom.ker
      (arithmeticFiniteAdeleIntegralAtIndexReduction P r level) :
        Set (ArithmeticFiniteAdelesIntegralAtIndex P r level)) := by
  let f : ArithmeticFiniteAdelesIntegralAtIndex P r level →
      IndexCongruenceLocalField P r level := fun a =>
    arithmeticFiniteAdeleAtIndexLocalField P r level a.1
  have hf : Continuous f :=
    (continuous_arithmeticFiniteAdeleAtIndexLocalField P r level).comp
      continuous_subtype_val
  have hopen : IsOpen {x : IndexCongruenceLocalField P r level |
      Valued.v.restrict x < 1} :=
    Valued.isOpen_ball (IndexCongruenceLocalField P r level) 1
  rw [show (RingHom.ker
      (arithmeticFiniteAdeleIntegralAtIndexReduction P r level) :
        Set (ArithmeticFiniteAdelesIntegralAtIndex P r level)) =
      f ⁻¹' {x : IndexCongruenceLocalField P r level |
        Valued.v.restrict x < 1} by
    ext a
    change arithmeticFiniteAdeleIntegralAtIndexReduction P r level a = 0 ↔
      Valued.v.restrict (f a) < 1
    rw [Valuation.restrict_lt_one_iff]
    change PowerSeries.constantCoeff
        (indexCongruenceLocalIntegersRingEquivPowerSeries P r level
          (arithmeticFiniteAdeleIntegralAtIndexToLocalIntegers P r level a)) =
        0 ↔ _
    exact indexCongruenceLocalIntegers_constantCoeff_eq_zero_iff
      P r level
      (arithmeticFiniteAdeleIntegralAtIndexToLocalIntegers P r level a)]
  exact hopen.preimage hf

@[simp] theorem arithmeticFiniteAdeleIntegralAtIndexReduction_diagonal
    (P : BasePrime) (r : Rank) (level : Nat) (a : ArithmeticRing P) :
    arithmeticFiniteAdeleIntegralAtIndexReduction P r level
        ⟨functionFieldToArithmeticFiniteAdeles P
            (algebraMap (ArithmeticRing P) (FunctionField P) a),
          functionFieldToArithmeticFiniteAdeles_algebraMap_mem_integralAtIndex
            P r level a⟩ =
      indexArithmeticEval P r level a := by
  rw [arithmeticFiniteAdeleIntegralAtIndexReduction, RingHom.comp_apply,
    RingHom.comp_apply]
  change PowerSeries.constantCoeff
      (indexCongruenceLocalIntegersRingEquivPowerSeries P r level
        (arithmeticFiniteAdeleIntegralAtIndexToLocalIntegers P r level _)) = _
  rw [arithmeticFiniteAdeleIntegralAtIndexToLocalIntegers_diagonal,
    indexCongruenceLocalIntegersRingEquivPowerSeries_ofPowerSeries,
    indexCompletedBaseArithmeticEval_constantCoeff]

/-- Selected residue reduction restricted to the actual compact-open
integral finite-adeles subring. -/
noncomputable def arithmeticIntegralFiniteAdeleReductionAtIndex
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticIntegralFiniteAdeles P →+* ResidueField P r level :=
  (arithmeticFiniteAdeleIntegralAtIndexReduction P r level).comp
    (arithmeticIntegralFiniteAdelesToIntegralAtIndex P r level)

/-- Selected residue reduction of an all-integral scalar adele depends
only on its selected intrinsic adic coordinate. -/
theorem arithmeticIntegralFiniteAdeleReductionAtIndex_eq_adic
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : ArithmeticIntegralFiniteAdeles P) :
    arithmeticIntegralFiniteAdeleReductionAtIndex P r level a =
      PowerSeries.constantCoeff
        (indexAdicIntegersRingEquivPowerSeries P r level
          ⟨arithmeticFiniteAdeleAtIndexPlace P r level a.1,
            a.property (indexCongruencePlace P r level)⟩) := by
  rfl

@[simp] theorem arithmeticIntegralFiniteAdeleReductionAtIndex_diagonal
    (P : BasePrime) (r : Rank) (level : Nat) (a : ArithmeticRing P) :
    arithmeticIntegralFiniteAdeleReductionAtIndex P r level
        ⟨functionFieldToArithmeticFiniteAdeles P
            (algebraMap (ArithmeticRing P) (FunctionField P) a),
          functionFieldToArithmeticFiniteAdeles_algebraMap_mem_integral
            P a⟩ =
      indexArithmeticEval P r level a := by
  exact arithmeticFiniteAdeleIntegralAtIndexReduction_diagonal
    P r level a

/-- The inclusion from all-place integral adeles to adeles integral at the
selected place is continuous. -/
theorem continuous_arithmeticIntegralFiniteAdelesToIntegralAtIndex
    (P : BasePrime) (r : Rank) (level : Nat) :
    Continuous
      (arithmeticIntegralFiniteAdelesToIntegralAtIndex P r level) := by
  exact Continuous.subtype_mk continuous_subtype_val _

/-- The selected residue kernel remains open after restriction to the
all-place integral finite adeles. -/
theorem isOpen_ker_arithmeticIntegralFiniteAdeleReductionAtIndex
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsOpen (RingHom.ker
      (arithmeticIntegralFiniteAdeleReductionAtIndex P r level) :
        Set (ArithmeticIntegralFiniteAdeles P)) := by
  rw [show (RingHom.ker
      (arithmeticIntegralFiniteAdeleReductionAtIndex P r level) :
        Set (ArithmeticIntegralFiniteAdeles P)) =
      (arithmeticIntegralFiniteAdelesToIntegralAtIndex P r level) ⁻¹'
        (RingHom.ker
          (arithmeticFiniteAdeleIntegralAtIndexReduction P r level) :
            Set (ArithmeticFiniteAdelesIntegralAtIndex P r level)) by
    ext a
    rfl]
  exact (isOpen_ker_arithmeticFiniteAdeleIntegralAtIndexReduction
    P r level).preimage
      (continuous_arithmeticIntegralFiniteAdelesToIntegralAtIndex
        P r level)

private theorem continuous_ringHom_to_discrete_of_isOpen_ker
    {A B : Type*} [Ring A] [Ring B] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [TopologicalSpace B] [DiscreteTopology B]
    (f : A →+* B) (hker : IsOpen (RingHom.ker f : Set A)) :
    Continuous f := by
  rw [continuous_discrete_rng]
  intro y
  by_cases hy : ∃ x, f x = y
  · obtain ⟨x, hx⟩ := hy
    rw [show f ⁻¹' {y} =
        (fun k : A => x + k) '' (RingHom.ker f : Set A) by
      ext z
      constructor
      · intro hz
        change f z = y at hz
        refine ⟨z - x, ?_, by abel⟩
        change f (z - x) = 0
        rw [map_sub, hz, hx, sub_self]
      · rintro ⟨k, hk, rfl⟩
        change f (x + k) = y
        change f k = 0 at hk
        rw [map_add, hx, hk, add_zero]]
    exact isOpenMap_add_left x _ hker
  · rw [show f ⁻¹' {y} = ∅ by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false]
      exact fun hx => hy ⟨x, hx⟩]
    exact isOpen_empty

/-- Selected residue reduction is continuous on the compact-open
all-integral scalar adeles. -/
theorem continuous_arithmeticIntegralFiniteAdeleReductionAtIndex
    (P : BasePrime) (r : Rank) (level : Nat) :
    Continuous (arithmeticIntegralFiniteAdeleReductionAtIndex P r level) :=
  continuous_ringHom_to_discrete_of_isOpen_ker
    (arithmeticIntegralFiniteAdeleReductionAtIndex P r level)
    (isOpen_ker_arithmeticIntegralFiniteAdeleReductionAtIndex P r level)

/-- Residue coordinates of an all-integral finite-adelic cyclic element at
the construction-owned selected congruence place. -/
noncomputable def arithmeticFiniteAdeleCyclicIntegralReductionCoordinates
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : ArithmeticFiniteAdeleCyclicIntegralElement P r) :
    Fin r.matrixRank × Fin r.matrixRank → ResidueField P r level :=
  fun p => arithmeticIntegralFiniteAdeleReductionAtIndex P r level
    ⟨(arithmeticFiniteAdeleCyclicBasis P r).equivFun x.1 p,
      x.property p⟩

/-- Matrix reduction of an all-integral finite-adelic cyclic element,
reconstructed in the actual reduced cyclic basis at the selected place. -/
noncomputable def arithmeticFiniteAdeleCyclicIntegralReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdeleCyclicIntegralElement P r →
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level) :=
  fun x => (indexCyclicBasis P r level).equivFun.symm
    (arithmeticFiniteAdeleCyclicIntegralReductionCoordinates
      P r level x)

@[simp] theorem indexCyclicBasis_equivFun_arithmeticFiniteAdeleCyclicReduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : ArithmeticFiniteAdeleCyclicIntegralElement P r) :
    (indexCyclicBasis P r level).equivFun
        (arithmeticFiniteAdeleCyclicIntegralReduction P r level x) =
      arithmeticFiniteAdeleCyclicIntegralReductionCoordinates
        P r level x :=
  (indexCyclicBasis P r level).equivFun.apply_symm_apply _

/-- Integral one-place cyclic patching commutes with selected finite
residue reduction. -/
theorem arithmeticFiniteAdeleCyclicIntegralReduction_patchAtIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicAlgebra P r level)
    (hx : x ∈ IndexAdicCyclicIntegralLattice P r level) :
    arithmeticFiniteAdeleCyclicIntegralReduction P r level
        ⟨arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x,
          arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mem_integral
            P r level x hx⟩ =
      indexAdicCyclicIntegralReduction P r level ⟨x, hx⟩ := by
  apply (indexCyclicBasis P r level).equivFun.injective
  funext p
  have hleft := congrArg
    (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
      ResidueField P r level => f p)
    (indexCyclicBasis_equivFun_arithmeticFiniteAdeleCyclicReduction
      P r level
      ⟨arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x,
        arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mem_integral
          P r level x hx⟩)
  have hright := congrArg
    (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
      ResidueField P r level => f p)
    ((indexCyclicBasis P r level).equivFun.apply_symm_apply
      (indexAdicCyclicIntegralReductionCoordinates P r level ⟨x, hx⟩))
  change (indexCyclicBasis P r level).equivFun
      (arithmeticFiniteAdeleCyclicIntegralReduction P r level
        ⟨arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x,
          arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mem_integral
            P r level x hx⟩) p =
    arithmeticFiniteAdeleCyclicIntegralReductionCoordinates P r level
      ⟨arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x,
        arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mem_integral
          P r level x hx⟩ p at hleft
  change (indexCyclicBasis P r level).equivFun
      (indexAdicCyclicIntegralReduction P r level ⟨x, hx⟩) p =
    indexAdicCyclicIntegralReductionCoordinates P r level ⟨x, hx⟩ p
      at hright
  rw [hleft, hright]
  change arithmeticIntegralFiniteAdeleReductionAtIndex P r level
      ⟨(arithmeticFiniteAdeleCyclicBasis P r).equivFun
          (arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x) p,
        _⟩ =
    PowerSeries.constantCoeff
      (indexAdicIntegersRingEquivPowerSeries P r level
        ⟨(indexAdicCyclicBasis P r level).equivFun x p, hx p⟩)
  rw [arithmeticIntegralFiniteAdeleReductionAtIndex_eq_adic]
  have hcoord := indexAdicCyclicBasis_equivFun_atIndexPlace
    P r level
      (arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x) p
  rw [arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace_patch] at hcoord
  have hpatch :=
    arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mem_integral
      P r level x hx
  have hz :
      (⟨arithmeticFiniteAdeleAtIndexPlace P r level
          ((arithmeticFiniteAdeleCyclicBasis P r).equivFun
            (arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x) p),
        (hpatch p) (indexCongruencePlace P r level)⟩ :
          IndexCongruenceAdicIntegers P r level) =
      ⟨(indexAdicCyclicBasis P r level).equivFun x p,
        hx p⟩ := by
    apply Subtype.ext
    exact hcoord.symm
  rw [hz]

/-- The full tuple of selected residue coordinates varies continuously on
the all-integral finite-adelic cyclic lattice. -/
theorem continuous_arithmeticFiniteAdeleCyclicIntegralReductionCoordinates
    (P : BasePrime) (r : Rank) (level : Nat) :
    Continuous
      (arithmeticFiniteAdeleCyclicIntegralReductionCoordinates
        P r level) := by
  apply continuous_pi
  intro p
  apply (continuous_arithmeticIntegralFiniteAdeleReductionAtIndex
    P r level).comp
  apply Continuous.subtype_mk
  exact ((continuous_apply p).comp continuous_induced_dom).comp
    continuous_subtype_val

/-- Matrix reduction at the selected congruence place is continuous on the
all-integral finite-adelic cyclic lattice. -/
theorem continuous_arithmeticFiniteAdeleCyclicIntegralReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    Continuous
      (arithmeticFiniteAdeleCyclicIntegralReduction P r level) := by
  exact (continuous_of_discreteTopology (f :=
      (indexCyclicBasis P r level).equivFun.symm)).comp
    (continuous_arithmeticFiniteAdeleCyclicIntegralReductionCoordinates
      P r level)

/-- Every selected finite matrix fiber is an open congruence neighborhood
inside the actual all-integral finite-adelic cyclic lattice. -/
theorem isOpen_arithmeticFiniteAdeleCyclicIntegralReduction_fiber
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    IsOpen ((arithmeticFiniteAdeleCyclicIntegralReduction P r level) ⁻¹'
      {M}) := by
  exact (isOpen_discrete {M}).preimage
    (continuous_arithmeticFiniteAdeleCyclicIntegralReduction P r level)

/-- The genuine finite-adelic congruence neighborhood determined by a
selected residue matrix.  Its points satisfy all-place integrality in the
construction-owned cyclic basis and have the prescribed selected-place
reduction. -/
noncomputable def arithmeticFiniteAdeleCyclicCongruenceNeighborhood
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    Set (ArithmeticFiniteAdeleCyclicAlgebra P r) :=
  Subtype.val ''
    ((arithmeticFiniteAdeleCyclicIntegralReduction P r level) ⁻¹' {M})

/-- A congruence fiber is open in the ambient finite-adelic cyclic algebra,
not merely in the bundled integral lattice. -/
theorem isOpen_arithmeticFiniteAdeleCyclicCongruenceNeighborhood
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    IsOpen (arithmeticFiniteAdeleCyclicCongruenceNeighborhood
      P r level M) := by
  exact (isOpen_arithmeticFiniteAdeleCyclicIntegralLattice P r
    ).isOpenMap_subtype_val _
    (isOpen_arithmeticFiniteAdeleCyclicIntegralReduction_fiber
      P r level M)

/-- Membership in the ambient congruence neighborhood is exactly
all-place integrality together with the prescribed cyclic reduction. -/
theorem mem_arithmeticFiniteAdeleCyclicCongruenceNeighborhood_iff
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level))
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r) :
    x ∈ arithmeticFiniteAdeleCyclicCongruenceNeighborhood P r level M ↔
      ∃ hx : x ∈ ArithmeticFiniteAdeleCyclicIntegralLattice P r,
        arithmeticFiniteAdeleCyclicIntegralReduction P r level ⟨x, hx⟩ = M := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hy
  · rintro ⟨hx, hred⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hred

/-- On a diagonal arithmetic cyclic-order point, finite-adelic residue
coordinates are exactly the construction's genuine arithmetic coefficient
reduction. -/
theorem arithmeticFiniteAdeleCyclicIntegralReductionCoordinates_diagonal
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : CyclicAlgebra P r) (hx : x ∈ arithmeticCyclicSpan P r)
    (p : Fin r.matrixRank × Fin r.matrixRank)
    (a : ArithmeticRing P)
    (ha : arithmeticRingToFunctionField P a =
      (functionFieldCyclicBasis P r).equivFun x p) :
    arithmeticFiniteAdeleCyclicIntegralReductionCoordinates P r level
        ⟨cyclicAlgebraToArithmeticFiniteAdeles P r x,
          cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice
            P r x hx⟩ p =
      indexArithmeticEval P r level a := by
  let c : ArithmeticIntegralFiniteAdeles P :=
    ⟨(arithmeticFiniteAdeleCyclicBasis P r).equivFun
        (cyclicAlgebraToArithmeticFiniteAdeles P r x) p,
      (cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice
        P r x hx) p⟩
  let d : ArithmeticIntegralFiniteAdeles P :=
    ⟨functionFieldToArithmeticFiniteAdeles P
        (algebraMap (ArithmeticRing P) (FunctionField P) a),
      functionFieldToArithmeticFiniteAdeles_algebraMap_mem_integral P a⟩
  have hcd : c = d := by
    apply Subtype.ext
    change (arithmeticFiniteAdeleCyclicBasis P r).equivFun
        (cyclicAlgebraToArithmeticFiniteAdeles P r x) p =
      functionFieldToArithmeticFiniteAdeles P
        (algebraMap (ArithmeticRing P) (FunctionField P) a)
    rw [arithmeticFiniteAdeleCyclicBasis_equivFun_diagonal, ← ha]
    have hbase : arithmeticRingToFunctionField P =
        algebraMap (ArithmeticRing P) (FunctionField P) := by
      apply IsLocalization.ringHom_ext
        (Submonoid.powers
          (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P))
      apply RingHom.ext
      intro f
      simp only [RingHom.comp_apply]
      rw [arithmeticRingToFunctionField_algebraMap]
      exact IsScalarTower.algebraMap_apply
        (PolynomialRing P) (ArithmeticRing P) (FunctionField P) f
    rw [hbase]
  change arithmeticIntegralFiniteAdeleReductionAtIndex P r level c = _
  rw [hcd]
  exact arithmeticIntegralFiniteAdeleReductionAtIndex_diagonal
    P r level a

/-- The selected residue of the integral split matrix assembled from global
arithmetic cyclic coordinates is exactly the finite-adelic cyclic
reduction. -/
theorem arithmeticCyclicCoordinateMatrix_reduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : CyclicAlgebra P r) (hx : x ∈ arithmeticCyclicSpan P r) :
    (arithmeticCyclicCoordinateMatrix P r x hx).map
        (indexConstantArithmeticEval P r level) =
      arithmeticFiniteAdeleCyclicIntegralReduction P r level
        ⟨cyclicAlgebraToArithmeticFiniteAdeles P r x,
          cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice
            P r x hx⟩ := by
  rw [arithmeticCyclicCoordinateMatrix]
  have hmapSum :
      ((∑ p, arithmeticToConstantArithmetic P r
          (arithmeticCyclicCoordinate P r x hx p) •
            orderIndexCyclicBasisVector P r p).map
          (indexConstantArithmeticEval P r level)) =
        ∑ p, (arithmeticToConstantArithmetic P r
          (arithmeticCyclicCoordinate P r x hx p) •
            orderIndexCyclicBasisVector P r p).map
          (indexConstantArithmeticEval P r level) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sum_apply, map_sum]
  rw [hmapSum, arithmeticFiniteAdeleCyclicIntegralReduction,
    Module.Basis.equivFun_symm_apply]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Matrix.map_smul' _ _ _ (map_mul _),
    indexConstantArithmeticEval_arithmeticBaseChange,
    orderIndexCyclicBasisVector_reduction,
    ← indexCyclicBasis_apply]
  congr 1
  exact (arithmeticFiniteAdeleCyclicIntegralReductionCoordinates_diagonal
    P r level x hx p (arithmeticCyclicCoordinate P r x hx p)
      (arithmeticRingToFunctionField_arithmeticCyclicCoordinate
        P r x hx p)).symm

/-- On a genuine integral norm-one inner-form point, finite-adelic cyclic
reduction is exactly the existing construction-owned entrywise reduction.
This is the matrix-level commutative square needed by the Prasad argument. -/
theorem arithmeticFiniteAdeleCyclicIntegralReduction_orderNormOneInnerForm
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : OrderNormOneInnerForm P r) :
    arithmeticFiniteAdeleCyclicIntegralReduction P r level
        ⟨cyclicAlgebraToArithmeticFiniteAdeles P r
            (orderNormOneInnerFormCyclicAlgebraPoint P r s),
          cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice P r
            (orderNormOneInnerFormCyclicAlgebraPoint P r s)
            (orderNormOneInnerFormCyclicAlgebraPoint_mem_arithmeticCyclicSpan
              P r s)⟩ =
      (((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ConstantArithmeticRing P r)).map
            (indexConstantArithmeticEval P r level)) := by
  calc
    _ = (arithmeticCyclicCoordinateMatrix P r
          (orderNormOneInnerFormCyclicAlgebraPoint P r s)
          (orderNormOneInnerFormCyclicAlgebraPoint_mem_arithmeticCyclicSpan
            P r s)).map
          (indexConstantArithmeticEval P r level) :=
      (arithmeticCyclicCoordinateMatrix_reduction P r level
        (orderNormOneInnerFormCyclicAlgebraPoint P r s)
        (orderNormOneInnerFormCyclicAlgebraPoint_mem_arithmeticCyclicSpan
          P r s)).symm
    _ = _ := congrArg
      (fun M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ConstantArithmeticRing P r) =>
          M.map (indexConstantArithmeticEval P r level))
      (arithmeticCyclicCoordinateMatrix_orderNormOneInnerForm P r s)

/-- For a genuine integral norm-one inner-form point, membership in the
finite-adelic congruence neighborhood is equivalent to the construction's
existing entrywise matrix congruence. -/
theorem orderNormOneInnerForm_mem_arithmeticFiniteAdeleCyclicCongruenceNeighborhood_iff
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : OrderNormOneInnerForm P r)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    cyclicAlgebraToArithmeticFiniteAdeles P r
        (orderNormOneInnerFormCyclicAlgebraPoint P r s) ∈
      arithmeticFiniteAdeleCyclicCongruenceNeighborhood P r level M ↔
        (((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ConstantArithmeticRing P r)).map
              (indexConstantArithmeticEval P r level)) = M := by
  rw [mem_arithmeticFiniteAdeleCyclicCongruenceNeighborhood_iff]
  constructor
  · rintro ⟨hx, hred⟩
    have hpoint :
        (⟨cyclicAlgebraToArithmeticFiniteAdeles P r
            (orderNormOneInnerFormCyclicAlgebraPoint P r s), hx⟩ :
          ArithmeticFiniteAdeleCyclicIntegralElement P r) =
        ⟨cyclicAlgebraToArithmeticFiniteAdeles P r
            (orderNormOneInnerFormCyclicAlgebraPoint P r s),
          cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice P r
            (orderNormOneInnerFormCyclicAlgebraPoint P r s)
            (orderNormOneInnerFormCyclicAlgebraPoint_mem_arithmeticCyclicSpan
              P r s)⟩ := by
      exact Subtype.ext rfl
    rw [hpoint,
      arithmeticFiniteAdeleCyclicIntegralReduction_orderNormOneInnerForm]
      at hred
    exact hred
  · intro hred
    refine ⟨cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice P r
      (orderNormOneInnerFormCyclicAlgebraPoint P r s)
      (orderNormOneInnerFormCyclicAlgebraPoint_mem_arithmeticCyclicSpan
        P r s), ?_⟩
    rw [arithmeticFiniteAdeleCyclicIntegralReduction_orderNormOneInnerForm]
    exact hred

/-- The actual base S-arithmetic ring is dense in the selected power-series
chart.  This uses the proved coefficient-by-coefficient lifts, so it does not
import a density certificate. -/
theorem denseRange_indexCompletedBaseArithmeticEval
    (P : BasePrime) (r : Rank) (level : Nat) :
    DenseRange (indexCompletedBaseArithmeticEval P r level) := by
  intro s
  choose a ha using fun n =>
    exists_indexCompletedBaseArithmeticEval_finite_coeff_lift
      P r level s n
  apply mem_closure_of_tendsto
    (f := fun n : Nat => indexCompletedBaseArithmeticEval P r level (a n))
    (b := (Filter.atTop : Filter Nat))
  · rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro k
    exact tendsto_atTop_of_eventually_const fun n (hkn : k < n) =>
      ha n k hkn
  · exact Filter.Eventually.of_forall fun n => Set.mem_range_self (a n)

/-- Consequently the genuine selected local ring also has dense image in
the same completion chart. -/
theorem denseRange_indexCongruenceLocalRingToCompletion
    (P : BasePrime) (r : Rank) (level : Nat) :
    DenseRange (indexCongruenceLocalRingToCompletion P r level) := by
  apply (denseRange_indexCompletedBaseArithmeticEval P r level).mono
  rintro _ ⟨a, rfl⟩
  exact ⟨algebraMap (ArithmeticRing P)
      (IndexCongruenceLocalRing P r level) a,
    indexCongruenceLocalRingToCompletion_algebraMap P r level a⟩

end SelectedPlaceTopology

/-! ## The split norm-one group at the selected congruence place -/

/-- Because the completed cyclic order is the full matrix algebra, its
norm-one unit group is literally the full special-linear group. -/
theorem IndexCompletedNormOneInnerForm_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCompletedNormOneInnerForm P r level = ⊤ := by
  apply top_unique
  intro s _
  constructor <;> rw [IndexCompletedCyclicOrder_eq_top] <;>
    exact Set.mem_univ _

/-- Explicit identification of the actual completed norm-one inner form with
split `SL_d` at the selected congruence place. -/
noncomputable def indexCompletedNormOneInnerFormEquivSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCompletedNormOneInnerForm P r level ≃*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level)) where
  toFun s := s
  invFun s := ⟨s, by
    rw [IndexCompletedNormOneInnerForm_eq_top]
    exact Subgroup.mem_top s⟩
  left_inv s := Subtype.ext rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-! ## The split form of the construction-owned norm-one group -/

/-- Units of the cyclic algebra after scalar extension to its explicit
global splitting field, identified with the corresponding general-linear
group. -/
noncomputable def splittingCyclicScalarExtensionUnitEquivGL
    (P : BasePrime) (r : Rank) :
    (SplittingCyclicScalarExtension P r)ˣ ≃*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  Units.mapEquiv
    (splittingCyclicScalarExtensionEquivMatrix P r).toMulEquiv

/-- Reduced norm on the explicit global split form. -/
noncomputable def splittingCyclicScalarExtensionReducedNorm
    (P : BasePrime) (r : Rank) :
    (SplittingCyclicScalarExtension P r)ˣ →*
      (SplittingFunctionField P r)ˣ :=
  Matrix.GeneralLinearGroup.det.comp
    (splittingCyclicScalarExtensionUnitEquivGL P r).toMonoidHom

/-- The norm-one group after extension to the explicit splitting field. -/
noncomputable def SplittingCyclicScalarExtensionNormOne
    (P : BasePrime) (r : Rank) :
    Subgroup (SplittingCyclicScalarExtension P r)ˣ :=
  (splittingCyclicScalarExtensionReducedNorm P r).ker

/-- The scalar-extended Cartwright--Steger norm-one inner form is exactly
`SL₃` or `SL₄` over the construction's explicit splitting field. -/
noncomputable def splittingCyclicScalarExtensionNormOneEquivSL
    (P : BasePrime) (r : Rank) :
    SplittingCyclicScalarExtensionNormOne P r ≃*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) where
  toFun u :=
    ⟨((splittingCyclicScalarExtensionUnitEquivGL P r u :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)),
      congrArg Units.val u.property⟩
  invFun s :=
    ⟨(splittingCyclicScalarExtensionUnitEquivGL P r).symm
        (Matrix.SpecialLinearGroup.toGL s), by
      change splittingCyclicScalarExtensionReducedNorm P r
        ((splittingCyclicScalarExtensionUnitEquivGL P r).symm
          (Matrix.SpecialLinearGroup.toGL s)) = 1
      rw [splittingCyclicScalarExtensionReducedNorm]
      simp⟩
  left_inv u := by
    apply Subtype.ext
    apply (splittingCyclicScalarExtensionUnitEquivGL P r).injective
    apply Units.ext
    simp
    rfl
  right_inv s := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    apply Units.ext
    simp
    rfl
  map_mul' u v := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    apply Units.ext
    simp
    rfl

/-- Scalar extension of a global cyclic-algebra unit to the explicit
splitting field. -/
noncomputable def cyclicAlgebraUnitToSplittingScalarExtension
    (P : BasePrime) (r : Rank) :
    (CyclicAlgebra P r)ˣ →*
      (SplittingCyclicScalarExtension P r)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight
    (R := FunctionField P) (A := SplittingFunctionField P r)
      (B := CyclicAlgebra P r)).toRingHom

/-- The genuine scalar-extension splitting agrees with the construction's
original global matrix representation on every cyclic-algebra unit. -/
theorem splittingScalarExtensionUnitEquivGL_global_compatibility
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    splittingCyclicScalarExtensionUnitEquivGL P r
        (cyclicAlgebraUnitToSplittingScalarExtension P r u) =
      cyclicAlgebraUnitToGlobalGL P r u := by
  apply Units.ext
  exact splittingCyclicScalarExtensionMap_includeRight P r u

/-- Intrinsic global norm-one points base-change to norm-one points of the
explicit split form. -/
noncomputable def cyclicAlgebraNormOneToSplittingNormOne
    (P : BasePrime) (r : Rank) :
    CyclicAlgebraNormOne P r →*
      SplittingCyclicScalarExtensionNormOne P r where
  toFun u :=
    ⟨cyclicAlgebraUnitToSplittingScalarExtension P r u, by
      change splittingCyclicScalarExtensionReducedNorm P r
        (cyclicAlgebraUnitToSplittingScalarExtension P r u) = 1
      change Matrix.GeneralLinearGroup.det
        (splittingCyclicScalarExtensionUnitEquivGL P r
          (cyclicAlgebraUnitToSplittingScalarExtension P r u)) = 1
      rw [splittingScalarExtensionUnitEquivGL_global_compatibility]
      have hu : (u : (CyclicAlgebra P r)ˣ) ∈
          CyclicAlgebraSplitNormOne P r := by
        rw [cyclicAlgebraSplitNormOne_eq_normOne]
        exact u.property
      exact hu⟩
  map_one' := Subtype.ext
    (map_one (cyclicAlgebraUnitToSplittingScalarExtension P r))
  map_mul' u v := Subtype.ext
    (map_mul (cyclicAlgebraUnitToSplittingScalarExtension P r)
      (u : (CyclicAlgebra P r)ˣ) (v : (CyclicAlgebra P r)ˣ))

/-- The global inner form in split coordinates, valued directly in the
standard special-linear group. -/
noncomputable def cyclicAlgebraNormOneToSplittingSL
    (P : BasePrime) (r : Rank) :
    CyclicAlgebraNormOne P r →*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  (splittingCyclicScalarExtensionNormOneEquivSL P r).toMonoidHom.comp
    (cyclicAlgebraNormOneToSplittingNormOne P r)

theorem cyclicAlgebraNormOneToSplittingSL_toGL
    (P : BasePrime) (r : Rank) (u : CyclicAlgebraNormOne P r) :
    Matrix.SpecialLinearGroup.toGL
        (cyclicAlgebraNormOneToSplittingSL P r u) =
      cyclicAlgebraUnitToGlobalGL P r u := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  change ((splittingCyclicScalarExtensionUnitEquivGL P r
      (cyclicAlgebraUnitToSplittingScalarExtension P r u) :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) i j = _
  exact congrArg (fun M : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r) =>
    ((M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) i j))
    (splittingScalarExtensionUnitEquivGL_global_compatibility P r u)

theorem cyclicAlgebraUnitToGlobalGL_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (cyclicAlgebraUnitToGlobalGL P r) :=
  Units.map_injective (fun _ _ h => Subtype.ext h)

theorem cyclicAlgebraNormOneToSplittingSL_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (cyclicAlgebraNormOneToSplittingSL P r) := by
  intro u v huv
  apply Subtype.ext
  apply cyclicAlgebraUnitToGlobalGL_injective P r
  rw [← cyclicAlgebraNormOneToSplittingSL_toGL P r u,
    ← cyclicAlgebraNormOneToSplittingSL_toGL P r v, huv]

theorem cyclicAlgebraNormOneToSplittingSL_order_compatibility
    (P : BasePrime) (r : Rank) (s : OrderNormOneInnerForm P r) :
    cyclicAlgebraNormOneToSplittingSL P r
        (orderNormOneInnerFormToCyclicAlgebraNormOne P r s) =
      Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
        (constantArithmeticToSplittingFunctionField P r)
        (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [cyclicAlgebraNormOneToSplittingSL_toGL]
  change orderUnitToGlobalGL P r
      (orderNormOneInnerFormToOrderUnits P r s) = _
  rw [orderUnitToGlobalGL_orderNormOneInnerFormToOrderUnits]
  apply Units.ext
  rfl

/-! ## The rational norm-one group at the selected congruence place -/

/-- The actual split norm-one local group over the selected Laurent field. -/
abbrev IndexLocalNormOneInnerForm
    (P : BasePrime) (r : Rank) (level : Nat) :=
  Matrix.SpecialLinearGroup (Fin r.matrixRank)
    (IndexCongruenceLocalField P r level)

/-- Global rational norm-one points in the selected Laurent local group.
This is the congruence-place factor to which Prasad strong approximation
applies, as distinct from its integral `PowerSeries` subgroup. -/
noncomputable def cyclicAlgebraNormOneToIndexLocal
    (P : BasePrime) (r : Rank) (level : Nat) :
    CyclicAlgebraNormOne P r →*
      IndexLocalNormOneInnerForm P r level :=
  (Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
    (splittingFunctionFieldToIndexCongruenceLocalField P r level)).comp
      (cyclicAlgebraNormOneToSplittingSL P r)

theorem cyclicAlgebraNormOneToIndexLocal_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective
      (cyclicAlgebraNormOneToIndexLocal P r level) := by
  intro u v huv
  apply cyclicAlgebraNormOneToSplittingSL_injective P r
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  apply RingHom.injective
    (splittingFunctionFieldToIndexCongruenceLocalField P r level)
  exact congrArg (fun M : IndexLocalNormOneInnerForm P r level =>
    ((M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (IndexCongruenceLocalField P r level)) i j)) huv

/-- Scalar extension of a global cyclic-algebra unit to the actual selected
Laurent local algebra. -/
noncomputable def cyclicAlgebraUnitToIndexLocalCyclicAlgebra
    (P : BasePrime) (r : Rank) (level : Nat) :
    (CyclicAlgebra P r)ˣ →*
      (IndexLocalCyclicAlgebra P r level)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight
    (R := FunctionField P)
    (A := IndexCongruenceLocalField P r level)
    (B := CyclicAlgebra P r)).toRingHom

/-- The unit-group scalar extension agrees with the selected local matrix
representation on every global cyclic-algebra unit. -/
theorem indexLocalCyclicAlgebraUnitEquivGL_global_compatibility
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (CyclicAlgebra P r)ˣ) :
    indexLocalCyclicAlgebraUnitEquivGL P r level
        (cyclicAlgebraUnitToIndexLocalCyclicAlgebra P r level u) =
      Units.map (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom u := by
  apply Units.ext
  exact indexLocalCyclicAlgebraToMatrix_includeRight P r level u

/-- Global units of the cyclic division algebra are dense in the selected
local general-linear group.  Additive density supplies a global algebra
point in every open matrix neighborhood of a local unit; openness of `GL`
and the division-algebra property turn that point into a genuine global
unit. -/
theorem denseRange_cyclicAlgebraUnitToIndexLocalGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    DenseRange
      (Units.map
        (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom.toMonoidHom) := by
  letI : DivisionRing (CyclicAlgebra P r) := cyclicAlgebraDivisionRing P r
  rw [DenseRange]
  apply dense_iff_inter_open.mpr
  intro U hUopen hUne
  let V : Set (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (IndexCongruenceLocalField P r level)) := Units.val '' U
  have hVopen : IsOpen V :=
    (isOpenEmbedding_indexLocalMatrix_unitsVal P r level).isOpenMap U hUopen
  have hVne : V.Nonempty := hUne.image Units.val
  obtain ⟨M, hMV, hMrange⟩ := dense_iff_inter_open.mp
    (denseRange_cyclicAlgebraToIndexLocalMatrix P r level) V hVopen hVne
  obtain ⟨x, rfl⟩ := hMrange
  obtain ⟨g, hgU, hg⟩ := hMV
  have hx : x ≠ 0 := by
    intro hx0
    subst x
    have hg0 : (g : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level)) = 0 := by
      exact hg.trans (map_zero (cyclicAlgebraToIndexLocalMatrix P r level))
    exact g.isUnit.ne_zero hg0
  let xUnit : (CyclicAlgebra P r)ˣ := Units.mk0 x hx
  refine ⟨Units.map
      (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom.toMonoidHom xUnit,
    ?_, Set.mem_range_self xUnit⟩
  have hunitEq : Units.map
      (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom.toMonoidHom xUnit = g := by
    apply Units.ext
    exact hg.symm
  rwa [hunitEq]

/-- Intrinsic global norm-one points base-change to genuine norm-one points
of the selected local scalar extension. -/
noncomputable def cyclicAlgebraNormOneToIndexLocalNormOne
    (P : BasePrime) (r : Rank) (level : Nat) :
    CyclicAlgebraNormOne P r →*
      IndexLocalCyclicAlgebraNormOne P r level where
  toFun u :=
    ⟨cyclicAlgebraUnitToIndexLocalCyclicAlgebra P r level u, by
      change indexLocalCyclicAlgebraReducedNorm P r level
        (cyclicAlgebraUnitToIndexLocalCyclicAlgebra P r level u) = 1
      change Matrix.GeneralLinearGroup.det
        (indexLocalCyclicAlgebraUnitEquivGL P r level
          (cyclicAlgebraUnitToIndexLocalCyclicAlgebra P r level u)) = 1
      rw [indexLocalCyclicAlgebraUnitEquivGL_global_compatibility]
      apply Units.ext
      change Matrix.det
        ((splittingFunctionFieldToIndexCongruenceLocalField P r level).mapMatrix
          ((u : (CyclicAlgebra P r)ˣ).1.1)) = 1
      rw [← RingHom.map_det]
      have hu : (u : (CyclicAlgebra P r)ˣ) ∈
          CyclicAlgebraSplitNormOne P r := by
        rw [cyclicAlgebraSplitNormOne_eq_normOne]
        exact u.property
      have hdet : Matrix.det ((u : (CyclicAlgebra P r)ˣ).1.1) = 1 := by
        simpa [CyclicAlgebraSplitNormOne,
          cyclicAlgebraSplitReducedNorm,
          cyclicAlgebraUnitToGlobalGL] using congrArg Units.val hu
      rw [hdet, map_one]⟩
  map_one' := Subtype.ext
    (map_one (cyclicAlgebraUnitToIndexLocalCyclicAlgebra P r level))
  map_mul' u v := Subtype.ext
    (map_mul (cyclicAlgebraUnitToIndexLocalCyclicAlgebra P r level)
      (u : (CyclicAlgebra P r)ˣ) (v : (CyclicAlgebra P r)ˣ))

/-- The genuine local norm-one base change agrees exactly with the earlier
selected-place `SL` localization of global norm-one points. -/
theorem cyclicAlgebraNormOneToIndexLocalNormOne_compatibility
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : CyclicAlgebraNormOne P r) :
    indexLocalCyclicAlgebraNormOneEquivSL P r level
        (cyclicAlgebraNormOneToIndexLocalNormOne P r level u) =
      cyclicAlgebraNormOneToIndexLocal P r level u := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  have hleft : Matrix.SpecialLinearGroup.toGL
      (indexLocalCyclicAlgebraNormOneEquivSL P r level
        (cyclicAlgebraNormOneToIndexLocalNormOne P r level u)) =
      indexLocalCyclicAlgebraUnitEquivGL P r level
        (cyclicAlgebraUnitToIndexLocalCyclicAlgebra P r level u) := by
    apply Units.ext
    rfl
  have hright : Matrix.SpecialLinearGroup.toGL
      (cyclicAlgebraNormOneToIndexLocal P r level u) =
      Matrix.GeneralLinearGroup.map
        (splittingFunctionFieldToIndexCongruenceLocalField P r level)
          (Matrix.SpecialLinearGroup.toGL
            (cyclicAlgebraNormOneToSplittingSL P r u)) := by
    apply Units.ext
    rfl
  rw [hleft, hright]
  rw [indexLocalCyclicAlgebraUnitEquivGL_global_compatibility,
    cyclicAlgebraNormOneToSplittingSL_toGL]
  apply Units.ext
  apply Matrix.ext
  intro i j
  rfl

/-- The commutator of two global cyclic-algebra units has reduced norm one.
This is the intrinsic source of rational norm-one approximants: no choice of
matrix splitting enters the definition. -/
noncomputable def cyclicAlgebraUnitCommutatorNormOne
    (P : BasePrime) (r : Rank)
    (u v : (CyclicAlgebra P r)ˣ) : CyclicAlgebraNormOne P r :=
  ⟨⁅u, v⁆, by
    change cyclicAlgebraReducedNorm P r ⁅u, v⁆ = 1
    rw [map_commutatorElement]
    exact (Commute.all _ _).commutator_eq⟩

/-- The commutator of two matrices in the selected local `GL` is a matrix in
the selected local `SL`. -/
noncomputable def indexLocalGLCommutatorToSL
    (P : BasePrime) (r : Rank) (level : Nat)
    (a b : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (IndexCongruenceLocalField P r level)) :
    IndexLocalNormOneInnerForm P r level :=
  ⟨(⁅a, b⁆ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (IndexCongruenceLocalField P r level)), by
    have hdet : Matrix.GeneralLinearGroup.det ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement]
      exact (Commute.all _ _).commutator_eq
    exact congrArg Units.val hdet⟩

theorem continuous_indexLocalGLCommutatorToSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    Continuous (fun p :
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level) ×
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level) =>
      indexLocalGLCommutatorToSL P r level p.1 p.2) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level) ×
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level) =>
    (((⁅p.1, p.2⁆ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (IndexCongruenceLocalField P r level))) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level)))
  simp only [commutatorElement_def]
  fun_prop

/-- Localizing a global unit commutator gives exactly the corresponding
commutator in the selected local special-linear group. -/
theorem cyclicAlgebraUnitCommutatorNormOne_compatibility
    (P : BasePrime) (r : Rank) (level : Nat)
    (u v : (CyclicAlgebra P r)ˣ) :
    cyclicAlgebraNormOneToIndexLocal P r level
        (cyclicAlgebraUnitCommutatorNormOne P r u v) =
      indexLocalGLCommutatorToSL P r level
        (Units.map
          (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom.toMonoidHom u)
        (Units.map
          (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom.toMonoidHom v) := by
  rw [← cyclicAlgebraNormOneToIndexLocalNormOne_compatibility]
  apply Matrix.SpecialLinearGroup.toGL_injective
  have hleft : Matrix.SpecialLinearGroup.toGL
      (indexLocalCyclicAlgebraNormOneEquivSL P r level
        (cyclicAlgebraNormOneToIndexLocalNormOne P r level
          (cyclicAlgebraUnitCommutatorNormOne P r u v))) =
      indexLocalCyclicAlgebraUnitEquivGL P r level
        (cyclicAlgebraUnitToIndexLocalCyclicAlgebra P r level ⁅u, v⁆) := by
    apply Units.ext
    rfl
  rw [hleft,
    indexLocalCyclicAlgebraUnitEquivGL_global_compatibility]
  apply Units.ext
  change cyclicAlgebraToIndexLocalMatrix P r level (↑⁅u, v⁆) =
    ↑⁅Units.map
        (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom.toMonoidHom u,
      Units.map
        (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom.toMonoidHom v⁆
  exact congrArg Units.val
    (map_commutatorElement
      (Units.map
        (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom.toMonoidHom)
      u v)

/-- Global rational norm-one points are dense in the selected local
special-linear group.  The proof first uses additive approximation to obtain
density of global cyclic-algebra units in local `GL`; continuity of the
commutator then puts every local commutator in the closure of the global
norm-one image.  Finally, the explicitly proved perfectness of `SL` in ranks
three and four identifies those commutators with the whole local group. -/
theorem denseRange_cyclicAlgebraNormOneToIndexLocal
    (P : BasePrime) (r : Rank) (level : Nat) :
    DenseRange (cyclicAlgebraNormOneToIndexLocal P r level) := by
  let f : (CyclicAlgebra P r)ˣ →
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level) :=
    Units.map
      (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom.toMonoidHom
  let c :
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level) ×
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level) →
      IndexLocalNormOneInnerForm P r level :=
    fun p => indexLocalGLCommutatorToSL P r level p.1 p.2
  let H : Subgroup (IndexLocalNormOneInnerForm P r level) :=
    (cyclicAlgebraNormOneToIndexLocal P r level).range.topologicalClosure
  have hf : DenseRange f :=
    denseRange_cyclicAlgebraUnitToIndexLocalGL P r level
  have hpair : DenseRange (Prod.map f f) := hf.prodMap hf
  have hc : Continuous c :=
    continuous_indexLocalGLCommutatorToSL P r level
  have himage : c '' Set.range (Prod.map f f) ⊆
      Set.range (cyclicAlgebraNormOneToIndexLocal P r level) := by
    rintro z ⟨p, ⟨q, rfl⟩, rfl⟩
    rcases q with ⟨u, v⟩
    refine ⟨cyclicAlgebraUnitCommutatorNormOne P r u v, ?_⟩
    exact cyclicAlgebraUnitCommutatorNormOne_compatibility P r level u v
  have hcomm : ∀ a b :
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level),
      indexLocalGLCommutatorToSL P r level a b ∈ H := by
    intro a b
    change c (a, b) ∈ H
    change c (a, b) ∈ closure
      (Set.range (cyclicAlgebraNormOneToIndexLocal P r level))
    exact closure_mono himage
      (hc.range_subset_closure_image_dense hpair (Set.mem_range_self (a, b)))
  have hcommutator :
      commutator (IndexLocalNormOneInnerForm P r level) ≤ H := by
    rw [commutator_def]
    apply Subgroup.commutator_le.mpr
    intro a _ b _
    exact hcomm (Matrix.SpecialLinearGroup.toGL a)
      (Matrix.SpecialLinearGroup.toGL b)
  rw [specialLinearGroup_commutator_eq_top r] at hcommutator
  have hHtop : H = ⊤ := top_unique hcommutator
  rw [DenseRange, dense_iff_closure_eq]
  change (H : Set (IndexLocalNormOneInnerForm P r level)) = Set.univ
  rw [hHtop]
  rfl

/-- The canonical completed lift of a finite special-linear target, viewed
in the selected Laurent local group. -/
noncomputable def finiteSpecialLinearToIndexLocalNormOne
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    IndexLocalNormOneInnerForm P r level :=
  Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
    (HahnSeries.ofPowerSeries ℤ (ResidueField P r level))
      ((orderIndexNormOneCompletedInnerFormLift P r level g :
        IndexCompletedNormOneInnerForm P r level) :
          Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level)))

/-- The open first-order selected-place congruence neighborhood of a finite
`SL` target, stated directly in the Laurent local group. -/
noncomputable def indexLocalNormOneFiniteTargetNeighborhood
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    Set (IndexLocalNormOneInnerForm P r level) :=
  {s | ∀ i j,
    Valued.v.restrict
      (((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level)) i j) -
        ((finiteSpecialLinearToIndexLocalNormOne P r level g :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (IndexCongruenceLocalField P r level)) i j)) < 1}

theorem isOpen_indexLocalNormOneFiniteTargetNeighborhood
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    IsOpen (indexLocalNormOneFiniteTargetNeighborhood P r level g) := by
  rw [show indexLocalNormOneFiniteTargetNeighborhood P r level g =
      ⋂ i, ⋂ j, (fun s : IndexLocalNormOneInnerForm P r level =>
        ((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level)) i j) -
        ((finiteSpecialLinearToIndexLocalNormOne P r level g :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (IndexCongruenceLocalField P r level)) i j)) ⁻¹'
          {x | Valued.v.restrict x < 1} by
    ext s
    simp [indexLocalNormOneFiniteTargetNeighborhood]]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  exact (Valued.isOpen_ball
    (IndexCongruenceLocalField P r level) 1).preimage (by fun_prop)

theorem finiteSpecialLinearToIndexLocalNormOne_mem_neighborhood
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    finiteSpecialLinearToIndexLocalNormOne P r level g ∈
      indexLocalNormOneFiniteTargetNeighborhood P r level g := by
  intro i j
  simp

/-- Every matrix entry of a point in a selected local finite-target
neighborhood is integral. -/
theorem indexLocalNormOneFiniteTargetNeighborhood_entry_integral
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level))
    (s : IndexLocalNormOneInnerForm P r level)
    (hs : s ∈ indexLocalNormOneFiniteTargetNeighborhood P r level g)
    (i j : Fin r.matrixRank) :
    ((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (IndexCongruenceLocalField P r level)) i j) ∈
        IndexCongruenceLocalIntegers P r level := by
  let z := ((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
    (IndexCongruenceLocalField P r level)) i j)
  let c := ((finiteSpecialLinearToIndexLocalNormOne P r level g :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (IndexCongruenceLocalField P r level)) i j)
  have hdiff : Valued.v (z - c) < 1 := by
    have h := hs i j
    rw [Valuation.restrict_lt_one_iff] at h
    exact h
  have hdiffInt : z - c ∈ IndexCongruenceLocalIntegers P r level :=
    le_of_lt hdiff
  have hcInt : c ∈ IndexCongruenceLocalIntegers P r level := by
    change Valued.v
      (HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
        ((((orderIndexNormOneCompletedInnerFormLift P r level g :
          IndexCompletedNormOneInnerForm P r level) :
            Matrix.SpecialLinearGroup (Fin r.matrixRank)
              (PowerSeries (ResidueField P r level))) :
                Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                  (PowerSeries (ResidueField P r level))) i j)) ≤ 1
    rw [LaurentSeries.val_le_one_iff_eq_coe]
    exact ⟨_, rfl⟩
  have hadd := (IndexCongruenceLocalIntegers P r level).add_mem
    (z - c) c hdiffInt hcInt
  simpa [z, c] using hadd

/-- Every finite special-linear target has a global *rational* norm-one
point in its selected local congruence neighborhood.  This theorem makes no
integrality claim at the other arithmetic finite places; clearing precisely
those possible denominators is the remaining specialized strong-
approximation step. -/
theorem exists_cyclicAlgebraNormOne_mem_indexLocalFiniteTargetNeighborhood
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    ∃ u : CyclicAlgebraNormOne P r,
      cyclicAlgebraNormOneToIndexLocal P r level u ∈
        indexLocalNormOneFiniteTargetNeighborhood P r level g := by
  let U := indexLocalNormOneFiniteTargetNeighborhood P r level g
  obtain ⟨_, hu, ⟨u, rfl⟩⟩ := dense_iff_inter_open.mp
    (denseRange_cyclicAlgebraNormOneToIndexLocal P r level) U
    (isOpen_indexLocalNormOneFiniteTargetNeighborhood P r level g)
    ⟨finiteSpecialLinearToIndexLocalNormOne P r level g,
      finiteSpecialLinearToIndexLocalNormOne_mem_neighborhood P r level g⟩
  exact ⟨u, hu⟩

/-! ## Projection of the finite-adelic norm-one group to the selected place -/

/-- Evaluation of the arithmetic finite adele ring in the concrete Laurent
model of the selected congruence completion, as a global-field algebra map. -/
noncomputable def arithmeticFiniteAdeleAtIndexLocalFieldAlgHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdeleRing P →ₐ[FunctionField P]
      IndexCongruenceLocalField P r level where
  __ := arithmeticFiniteAdeleAtIndexLocalField P r level
  commutes' x := arithmeticFiniteAdeleAtIndexLocalField_diagonal P r level x

/-- Evaluation of the common finite-adelic splitting ring at the selected
congruence place.  It combines finite-adele evaluation with the verified
embedding of the construction-owned global splitting field. -/
noncomputable def arithmeticFiniteAdeleSplittingRingToIndexLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdeleSplittingRing P r →ₐ[FunctionField P]
      IndexCongruenceLocalField P r level :=
  Algebra.TensorProduct.lift
    (arithmeticFiniteAdeleAtIndexLocalFieldAlgHom P r level)
    ({ __ := splittingFunctionFieldToIndexCongruenceLocalField P r level
       commutes' := fun x =>
        splittingFunctionFieldToIndexCongruenceLocalField_functionFieldEmbedding
          P r level x } :
      SplittingFunctionField P r →ₐ[FunctionField P]
        IndexCongruenceLocalField P r level)
    (fun _ _ => Commute.all _ _)

@[simp] theorem arithmeticFiniteAdeleSplittingRingToIndexLocalField_left
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : ArithmeticFiniteAdeleRing P) :
    arithmeticFiniteAdeleSplittingRingToIndexLocalField P r level
        (algebraMap (ArithmeticFiniteAdeleRing P)
          (ArithmeticFiniteAdeleSplittingRing P r) a) =
      arithmeticFiniteAdeleAtIndexLocalField P r level a := by
  change arithmeticFiniteAdeleSplittingRingToIndexLocalField P r level
      (TensorProduct.tmul (FunctionField P) a 1) = _
  rw [arithmeticFiniteAdeleSplittingRingToIndexLocalField,
    Algebra.TensorProduct.lift_tmul]
  simp [arithmeticFiniteAdeleAtIndexLocalFieldAlgHom]
  rfl

@[simp] theorem arithmeticFiniteAdeleSplittingRingToIndexLocalField_right
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : SplittingFunctionField P r) :
    arithmeticFiniteAdeleSplittingRingToIndexLocalField P r level
        (splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r x) =
      splittingFunctionFieldToIndexCongruenceLocalField P r level x := by
  change arithmeticFiniteAdeleSplittingRingToIndexLocalField P r level
      (TensorProduct.tmul (FunctionField P) 1 x) = _
  rw [arithmeticFiniteAdeleSplittingRingToIndexLocalField,
    Algebra.TensorProduct.lift_tmul]
  simp

/-- Selected-place projection of the actual finite-adelic cyclic algebra to
the concrete Laurent scalar extension. -/
noncomputable def arithmeticFiniteAdeleCyclicAlgebraToIndexLocal
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdeleCyclicAlgebra P r →ₐ[FunctionField P]
      IndexLocalCyclicAlgebra P r level :=
  (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra P r level).comp
    (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level)

/-- The finite-adelic splitting representation commutes with evaluation at
the selected congruence place. -/
theorem arithmeticFiniteAdeleCyclicSplitting_atIndex_compatibility
    (P : BasePrime) (r : Rank) (level : Nat) :
    ((indexLocalCyclicAlgebraToMatrix P r level).restrictScalars
      (FunctionField P)).comp
        (arithmeticFiniteAdeleCyclicAlgebraToIndexLocal P r level) =
      (arithmeticFiniteAdeleSplittingRingToIndexLocalField
        P r level).mapMatrix.comp
        ((arithmeticFiniteAdeleCyclicSplittingMap P r).restrictScalars
          (FunctionField P)) := by
  apply Algebra.TensorProduct.ext
  · apply DFunLike.ext _ _
    intro a
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp [arithmeticFiniteAdeleCyclicAlgebraToIndexLocal,
        arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace,
        indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra,
        indexLocalCyclicAlgebraToMatrix,
        arithmeticFiniteAdeleCyclicSplittingMap,
        Matrix.algebraMap_matrix_apply]
      rw [show TensorProduct.tmul (FunctionField P) a
          (1 : SplittingFunctionField P r) =
        algebraMap (ArithmeticFiniteAdeleRing P)
          (ArithmeticFiniteAdeleSplittingRing P r) a by rfl,
        arithmeticFiniteAdeleSplittingRingToIndexLocalField_left]
      rfl
    · simp [arithmeticFiniteAdeleCyclicAlgebraToIndexLocal,
      arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace,
      indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra,
      indexLocalCyclicAlgebraToMatrix,
      arithmeticFiniteAdeleCyclicSplittingMap,
      Matrix.algebraMap_matrix_apply, hij]
  · apply DFunLike.ext _ _
    intro x
    apply Matrix.ext
    intro i j
    simp [arithmeticFiniteAdeleCyclicAlgebraToIndexLocal,
      arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace,
      indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra,
      indexLocalCyclicAlgebraToMatrix,
      arithmeticFiniteAdeleCyclicSplittingMap,
      cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix,
      cyclicAlgebraToIndexLocalMatrix]

/-- Selected-place localization on units of the finite-adelic cyclic
algebra. -/
noncomputable def arithmeticFiniteAdeleCyclicUnitToIndexLocal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ →*
      (IndexLocalCyclicAlgebra P r level)ˣ :=
  Units.map
    (arithmeticFiniteAdeleCyclicAlgebraToIndexLocal
      P r level).toRingHom.toMonoidHom

/-- Reduced norm commutes with selected-place evaluation on every
finite-adelic cyclic-algebra unit. -/
theorem arithmeticFiniteAdeleCyclicReducedNorm_atIndex
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    indexLocalCyclicAlgebraReducedNorm P r level
        (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level u) =
      Units.map
        (arithmeticFiniteAdeleSplittingRingToIndexLocalField
          P r level).toRingHom.toMonoidHom
        (arithmeticFiniteAdeleCyclicReducedNorm P r u) := by
  apply Units.ext
  change Matrix.det
      ((indexLocalCyclicAlgebraUnitEquivGL P r level
        (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level u) :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (IndexCongruenceLocalField P r level)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level)) =
    arithmeticFiniteAdeleSplittingRingToIndexLocalField P r level
      (Matrix.det
        ((arithmeticFiniteAdeleCyclicUnitToGL P r u :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ArithmeticFiniteAdeleSplittingRing P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ArithmeticFiniteAdeleSplittingRing P r)))
  change Matrix.det
      (indexLocalCyclicAlgebraToMatrix P r level
        (arithmeticFiniteAdeleCyclicAlgebraToIndexLocal P r level
          (u : ArithmeticFiniteAdeleCyclicAlgebra P r))) =
    arithmeticFiniteAdeleSplittingRingToIndexLocalField P r level
      (Matrix.det
        (arithmeticFiniteAdeleCyclicSplittingMap P r
          (u : ArithmeticFiniteAdeleCyclicAlgebra P r)))
  have hcompat := DFunLike.congr_fun
    (arithmeticFiniteAdeleCyclicSplitting_atIndex_compatibility P r level)
    (u : ArithmeticFiniteAdeleCyclicAlgebra P r)
  have hcompat' :
      indexLocalCyclicAlgebraToMatrix P r level
          (arithmeticFiniteAdeleCyclicAlgebraToIndexLocal P r level
            (u : ArithmeticFiniteAdeleCyclicAlgebra P r)) =
        (arithmeticFiniteAdeleCyclicSplittingMap P r
          (u : ArithmeticFiniteAdeleCyclicAlgebra P r)).map
            (arithmeticFiniteAdeleSplittingRingToIndexLocalField
              P r level) := by
    simpa using hcompat
  rw [hcompat']
  exact
    ((arithmeticFiniteAdeleSplittingRingToIndexLocalField
      P r level).map_det
        (arithmeticFiniteAdeleCyclicSplittingMap P r
          (u : ArithmeticFiniteAdeleCyclicAlgebra P r))).symm

/-- The selected local reduced norm is the selected coordinate of the
base-finite-adele-valued reduced norm. -/
theorem arithmeticFiniteAdeleCyclicBaseReducedNorm_atIndex
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    indexLocalCyclicAlgebraReducedNorm P r level
        (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level u) =
      Units.map (arithmeticFiniteAdeleAtIndexLocalField P r level)
        (arithmeticFiniteAdeleCyclicBaseReducedNorm P r u) := by
  rw [arithmeticFiniteAdeleCyclicReducedNorm_atIndex,
    arithmeticFiniteAdeleCyclicReducedNorm_eq_baseChange]
  apply Units.ext
  exact arithmeticFiniteAdeleSplittingRingToIndexLocalField_left P r level
    (arithmeticFiniteAdeleCyclicBaseReducedNorm P r u)

@[simp] theorem arithmeticFiniteAdeleCyclicUnitToIndexLocal_supported
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (IndexAdicCyclicAlgebra P r level)ˣ) :
    arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level
        (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace P r level u) =
      Units.map
        (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra
          P r level).toRingHom.toMonoidHom u := by
  apply Units.ext
  change indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra P r level
      (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level
        (arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level
          (u : IndexAdicCyclicAlgebra P r level))) =
    indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra P r level
      (u : IndexAdicCyclicAlgebra P r level)
  rw [arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace_patch]

/-- If the selected local image of a patched unit has reduced norm one,
then the selected abstract adic coordinate of its descended base norm is
one. -/
theorem arithmeticFiniteAdeleCyclicBaseReducedNorm_supportedAtIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (IndexAdicCyclicAlgebra P r level)ˣ)
    (hu : indexLocalCyclicAlgebraReducedNorm P r level
      (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level
        (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace
          P r level u)) = 1) :
    arithmeticFiniteAdeleAtIndexPlace P r level
        (arithmeticFiniteAdeleCyclicBaseReducedNorm P r
          (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace P r level u)) =
      1 := by
  have hcompat := arithmeticFiniteAdeleCyclicBaseReducedNorm_atIndex
    P r level
      (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace P r level u)
  rw [hu] at hcompat
  have hval := congrArg Units.val hcompat
  apply (indexAdicCompletionRingEquivLocalField P r level).injective
  simpa [arithmeticFiniteAdeleAtIndexLocalField] using hval.symm

/-- A one-place patched local norm-one unit has global finite-adelic reduced
norm one: the selected coordinate follows from local compatibility and all
other coordinates are one because the patch is the identity there. -/
theorem arithmeticFiniteAdeleCyclicBaseReducedNorm_supported_eq_one
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (IndexAdicCyclicAlgebra P r level)ˣ)
    (hu : indexLocalCyclicAlgebraReducedNorm P r level
      (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level
        (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace
          P r level u)) = 1) :
    arithmeticFiniteAdeleCyclicBaseReducedNorm P r
        (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace P r level u) =
      1 := by
  apply Units.ext
  apply IsDedekindDomain.FiniteAdeleRing.ext
  intro v
  by_cases hv : v = indexCongruencePlace P r level
  · subst v
    exact arithmeticFiniteAdeleCyclicBaseReducedNorm_supportedAtIndexPlace
      P r level u hu
  · exact
      arithmeticFiniteAdeleCyclicBaseReducedNorm_supportedAtIndexPlace_of_ne
        P r level v hv u

/-- Patch a selected local norm-one unit into a genuine point of the actual
finite-adelic `SL₁(D)`. -/
noncomputable def arithmeticFiniteAdeleNormOneSupportedAtIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (IndexAdicCyclicAlgebra P r level)ˣ)
    (hu : indexLocalCyclicAlgebraReducedNorm P r level
      (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level
        (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace
          P r level u)) = 1) :
    ArithmeticFiniteAdeleCyclicNormOne P r :=
  ⟨arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace P r level u,
    (arithmeticFiniteAdeleCyclicReducedNorm_eq_one_iff_base P r _).mpr
      (arithmeticFiniteAdeleCyclicBaseReducedNorm_supported_eq_one
        P r level u hu)⟩

/-- If both a selected adic norm-one unit and its inverse have integral
cyclic coordinates, its one-place adelic patch lies in the genuine open
integral chart of finite-adelic `SL₁(D)`. -/
theorem arithmeticFiniteAdeleNormOneSupportedAtIndexPlace_mem_integral
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (IndexAdicCyclicAlgebra P r level)ˣ)
    (huNorm : indexLocalCyclicAlgebraReducedNorm P r level
      (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level
        (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace
          P r level u)) = 1)
    (hu : (u : IndexAdicCyclicAlgebra P r level) ∈
      IndexAdicCyclicIntegralLattice P r level)
    (huInv : ((u⁻¹ : (IndexAdicCyclicAlgebra P r level)ˣ) :
        IndexAdicCyclicAlgebra P r level) ∈
      IndexAdicCyclicIntegralLattice P r level) :
    arithmeticFiniteAdeleNormOneSupportedAtIndexPlace P r level u huNorm ∈
      ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r := by
  constructor
  · change arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level
        (u : IndexAdicCyclicAlgebra P r level) ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r
    exact arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mem_integral
      P r level (u : IndexAdicCyclicAlgebra P r level) hu
  · change arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level
        ((u⁻¹ : (IndexAdicCyclicAlgebra P r level)ˣ) :
          IndexAdicCyclicAlgebra P r level) ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r
    exact arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mem_integral
      P r level
        ((u⁻¹ : (IndexAdicCyclicAlgebra P r level)ˣ) :
          IndexAdicCyclicAlgebra P r level) huInv

/-- Selected-place localization restricts to a homomorphism from the actual
finite-adelic reduced-norm-one group to the actual local norm-one group. -/
noncomputable def arithmeticFiniteAdeleNormOneToIndexLocalNormOne
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdeleCyclicNormOne P r →*
      IndexLocalCyclicAlgebraNormOne P r level where
  toFun u := ⟨arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level u, by
    change indexLocalCyclicAlgebraReducedNorm P r level
      (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level u) = 1
    rw [arithmeticFiniteAdeleCyclicReducedNorm_atIndex]
    rw [u.property, map_one]⟩
  map_one' := Subtype.ext
    (map_one (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level))
  map_mul' u v := Subtype.ext
    (map_mul (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level)
      (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ)
      (v : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ))

/-- The adic-to-Laurent equivalence on the corresponding unit groups. -/
noncomputable def indexAdicCyclicAlgebraUnitEquivIndexLocal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexAdicCyclicAlgebra P r level)ˣ ≃*
      (IndexLocalCyclicAlgebra P r level)ˣ :=
  Units.mapEquiv
    (indexAdicCyclicAlgebraEquivIndexLocalCyclicAlgebra
      P r level).toMulEquiv

/-- A concrete one-place section from the selected local `SL₁` into the
finite-adelic `SL₁`: pull the local unit back to the adic realization and
patch it by the identity at every other finite place. -/
noncomputable def indexLocalCyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : IndexLocalCyclicAlgebraNormOne P r level) :
    ArithmeticFiniteAdeleCyclicNormOne P r :=
  arithmeticFiniteAdeleNormOneSupportedAtIndexPlace P r level
    ((indexAdicCyclicAlgebraUnitEquivIndexLocal P r level).symm u.1)
    (by
      rw [arithmeticFiniteAdeleCyclicUnitToIndexLocal_supported]
      rw [show Units.map
          (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra
            P r level).toRingHom.toMonoidHom
          ((indexAdicCyclicAlgebraUnitEquivIndexLocal
            P r level).symm u.1) = u.1 by
        exact (indexAdicCyclicAlgebraUnitEquivIndexLocal
          P r level).apply_symm_apply u.1]
      exact u.property)

/-- The one-place adelic patch is a right inverse to selected-place
localization on the genuine local norm-one group. -/
@[simp] theorem arithmeticFiniteAdeleNormOneToIndexLocalNormOne_section
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : IndexLocalCyclicAlgebraNormOne P r level) :
    arithmeticFiniteAdeleNormOneToIndexLocalNormOne P r level
        (indexLocalCyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne
          P r level u) = u := by
  apply Subtype.ext
  change arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level
      (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace P r level
        ((indexAdicCyclicAlgebraUnitEquivIndexLocal P r level).symm u.1)) =
    u.1
  rw [arithmeticFiniteAdeleCyclicUnitToIndexLocal_supported]
  exact (indexAdicCyclicAlgebraUnitEquivIndexLocal
    P r level).apply_symm_apply u.1

/-- Selected-place localization of the actual finite-adelic `SL₁(D)` is
surjective, with the preceding one-place patch as an explicit section. -/
theorem arithmeticFiniteAdeleNormOneToIndexLocalNormOne_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
      (arithmeticFiniteAdeleNormOneToIndexLocalNormOne P r level) := by
  intro u
  exact ⟨indexLocalCyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne
    P r level u,
      arithmeticFiniteAdeleNormOneToIndexLocalNormOne_section P r level u⟩

@[simp] theorem arithmeticFiniteAdeleCyclicAlgebraToIndexLocal_diagonal
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : CyclicAlgebra P r) :
    arithmeticFiniteAdeleCyclicAlgebraToIndexLocal P r level
        (cyclicAlgebraToArithmeticFiniteAdeles P r x) =
      Algebra.TensorProduct.includeRight x := by
  simp [arithmeticFiniteAdeleCyclicAlgebraToIndexLocal,
    cyclicAlgebraToArithmeticFiniteAdeles_apply,
    arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace,
    indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra]

/-- The adelic selected-place map agrees with the existing direct global
localization on every global reduced-norm-one point. -/
theorem arithmeticFiniteAdeleNormOneToIndexLocalNormOne_diagonal
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : CyclicAlgebraNormOne P r) :
    arithmeticFiniteAdeleNormOneToIndexLocalNormOne P r level
        (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r u) =
      cyclicAlgebraNormOneToIndexLocalNormOne P r level u := by
  apply Subtype.ext
  apply Units.ext
  exact arithmeticFiniteAdeleCyclicAlgebraToIndexLocal_diagonal P r level
    ((u : (CyclicAlgebra P r)ˣ) : CyclicAlgebra P r)

/-- Equality of selected local projections transports selected-place
integrality of both an adelic cyclic-algebra unit and its inverse. -/
theorem indexCongruencePlace_not_mem_denominatorPlaces_of_projection_eq
    (P : BasePrime) (r : Rank) (level : Nat)
    (u v : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ)
    (hproj : arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level u =
      arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level v)
    (hv : (v : ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
          ArithmeticFiniteAdeleCyclicIntegralLattice P r ∧
        (↑v⁻¹ : ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
          ArithmeticFiniteAdeleCyclicIntegralLattice P r) :
    indexCongruencePlace P r level ∉
      arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r u := by
  have hadic_of_projection_eq
      (a b : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ)
      (hab : arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level a =
        arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level b) :
      arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level
          (a : ArithmeticFiniteAdeleCyclicAlgebra P r) =
        arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level
          (b : ArithmeticFiniteAdeleCyclicAlgebra P r) := by
    apply (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra_bijective
      P r level).1
    exact congrArg Units.val hab
  have hcoord_of_projection_eq
      (a b : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ)
      (hab : arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level a =
        arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level b)
      (p : Fin r.matrixRank × Fin r.matrixRank) :
      arithmeticFiniteAdeleAtIndexPlace P r level
          ((arithmeticFiniteAdeleCyclicBasis P r).equivFun a p) =
        arithmeticFiniteAdeleAtIndexPlace P r level
          ((arithmeticFiniteAdeleCyclicBasis P r).equivFun b p) := by
    calc
      _ = (indexAdicCyclicBasis P r level).equivFun
          (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace
            P r level (a : ArithmeticFiniteAdeleCyclicAlgebra P r)) p :=
        (indexAdicCyclicBasis_equivFun_atIndexPlace
          P r level (a : ArithmeticFiniteAdeleCyclicAlgebra P r) p).symm
      _ = (indexAdicCyclicBasis P r level).equivFun
          (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace
            P r level (b : ArithmeticFiniteAdeleCyclicAlgebra P r)) p :=
        congrArg (fun x =>
          (indexAdicCyclicBasis P r level).equivFun x p)
          (hadic_of_projection_eq a b hab)
      _ = _ := indexAdicCyclicBasis_equivFun_atIndexPlace
        P r level (b : ArithmeticFiniteAdeleCyclicAlgebra P r) p
  rw [arithmeticFiniteAdeleCyclicUnitDenominatorPlaces, Set.mem_union]
  push Not
  constructor
  · intro hu
    obtain ⟨p, hp⟩ := hu
    apply hp
    change arithmeticFiniteAdeleAtIndexPlace P r level
      ((arithmeticFiniteAdeleCyclicBasis P r).equivFun u p) ∈
        (indexCongruencePlace P r level).adicCompletionIntegers
          (FunctionField P)
    rw [hcoord_of_projection_eq u v hproj p]
    exact hv.1 p (indexCongruencePlace P r level)
  · intro huInv
    obtain ⟨p, hp⟩ := huInv
    apply hp
    have hprojInv :
        arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level u⁻¹ =
          arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level v⁻¹ := by
      rw [map_inv, map_inv, hproj]
    change arithmeticFiniteAdeleAtIndexPlace P r level
      ((arithmeticFiniteAdeleCyclicBasis P r).equivFun (↑u⁻¹) p) ∈
        (indexCongruencePlace P r level).adicCompletionIntegers
          (FunctionField P)
    rw [hcoord_of_projection_eq u⁻¹ v⁻¹ hprojInv p]
    exact hv.2 p (indexCongruencePlace P r level)

/-- The construction's actual `S`-integral norm-one group: intrinsic
norm-one units of the construction-owned arithmetic order. -/
noncomputable abbrev CartwrightStegerSIntegralNormOne
    (P : BasePrime) (r : Rank) :=
  CartwrightStegerBaseNormOneOrderUnits P r

/-- Split order coordinates and intrinsic `S`-integral norm-one points are
canonically equivalent. -/
noncomputable def orderNormOneInnerFormEquivSIntegralNormOne
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r ≃*
      CartwrightStegerSIntegralNormOne P r :=
  orderNormOneInnerFormEquivBaseNormOneOrderUnits P r

/-- Intrinsic `S`-integral norm-one points map to the global rational
norm-one group of the cyclic division algebra. -/
noncomputable def sIntegralNormOneToCyclicAlgebraNormOne
    (P : BasePrime) (r : Rank) :
    CartwrightStegerSIntegralNormOne P r →*
      CyclicAlgebraNormOne P r :=
  (orderNormOneInnerFormToCyclicAlgebraNormOne P r).comp
    (orderNormOneInnerFormEquivSIntegralNormOne P r).symm.toMonoidHom

/-- The completed integral norm-one group embeds in its Laurent rational
local group by the canonical power-series inclusion. -/
noncomputable def indexCompletedNormOneInnerFormToIndexLocal
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCompletedNormOneInnerForm P r level →*
      IndexLocalNormOneInnerForm P r level :=
  (Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
    (HahnSeries.ofPowerSeries ℤ (ResidueField P r level))).comp
      (IndexCompletedNormOneInnerForm P r level).subtype

/-- Reconstruct a power-series matrix from a Laurent special-linear matrix
whose entries are all integral. -/
noncomputable def indexLocalIntegralEntriesToPowerSeriesMatrix
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexLocalNormOneInnerForm P r level)
    (hs : ∀ i j,
      ((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level)) i j) ∈
          IndexCongruenceLocalIntegers P r level) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)) :=
  fun i j => indexCongruenceLocalIntegersRingEquivPowerSeries P r level
    ⟨((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (IndexCongruenceLocalField P r level)) i j), hs i j⟩

theorem indexLocalIntegralEntriesToPowerSeriesMatrix_map
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexLocalNormOneInnerForm P r level)
    (hs : ∀ i j,
      ((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level)) i j) ∈
          IndexCongruenceLocalIntegers P r level) :
    (indexLocalIntegralEntriesToPowerSeriesMatrix P r level s hs).map
        (HahnSeries.ofPowerSeries ℤ (ResidueField P r level)) =
      (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level)) := by
  apply Matrix.ext
  intro i j
  let z : IndexCongruenceLocalIntegers P r level :=
    ⟨((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (IndexCongruenceLocalField P r level)) i j), hs i j⟩
  have hz := congrArg Subtype.val
    ((indexCongruenceLocalIntegersRingEquivPowerSeries
      P r level).symm_apply_apply z)
  exact hz

/-- An integral-entry Laurent `SL` matrix has a canonical preimage in the
actual completed norm-one cyclic order. -/
noncomputable def indexLocalNormOneToCompletedOfIntegralEntries
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexLocalNormOneInnerForm P r level)
    (hs : ∀ i j,
      ((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level)) i j) ∈
          IndexCongruenceLocalIntegers P r level) :
    IndexCompletedNormOneInnerForm P r level := by
  let M := indexLocalIntegralEntriesToPowerSeriesMatrix P r level s hs
  have hdet : Matrix.det M = 1 := by
    apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ))
    rw [RingHom.map_det]
    change Matrix.det
      (M.map (HahnSeries.ofPowerSeries ℤ (ResidueField P r level))) =
        HahnSeries.ofPowerSeries ℤ (ResidueField P r level) 1
    rw [show M =
          indexLocalIntegralEntriesToPowerSeriesMatrix P r level s hs from rfl,
      indexLocalIntegralEntriesToPowerSeriesMatrix_map P r level s hs,
      s.property, map_one]
  exact (indexCompletedNormOneInnerFormEquivSL P r level).symm ⟨M, hdet⟩

theorem indexCompletedNormOneInnerFormToIndexLocal_ofIntegralEntries
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexLocalNormOneInnerForm P r level)
    (hs : ∀ i j,
      ((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level)) i j) ∈
          IndexCongruenceLocalIntegers P r level) :
    indexCompletedNormOneInnerFormToIndexLocal P r level
        (indexLocalNormOneToCompletedOfIntegralEntries P r level s hs) = s := by
  apply Subtype.ext
  exact indexLocalIntegralEntriesToPowerSeriesMatrix_map P r level s hs

/-- A point in a selected local finite-target neighborhood comes from an
actual completed integral norm-one point, and that point reduces to the
prescribed finite `SL` target. -/
theorem exists_indexCompletedNormOne_of_mem_finiteTargetNeighborhood
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level))
    (s : IndexLocalNormOneInnerForm P r level)
    (hs : s ∈ indexLocalNormOneFiniteTargetNeighborhood P r level g) :
    ∃ t : IndexCompletedNormOneInnerForm P r level,
      indexCompletedNormOneInnerFormToIndexLocal P r level t = s ∧
        indexCompletedNormOneReduction P r level t = g := by
  have hint : ∀ i j,
      ((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level)) i j) ∈
          IndexCongruenceLocalIntegers P r level :=
    fun i j => indexLocalNormOneFiniteTargetNeighborhood_entry_integral
      P r level g s hs i j
  let t := indexLocalNormOneToCompletedOfIntegralEntries P r level s hint
  have htlocal : indexCompletedNormOneInnerFormToIndexLocal P r level t = s :=
    indexCompletedNormOneInnerFormToIndexLocal_ofIntegralEntries
      P r level s hint
  refine ⟨t, htlocal, ?_⟩
  have hred : indexCompletedNormOneReduction P r level t =
      indexCompletedNormOneReduction P r level
        (orderIndexNormOneCompletedInnerFormLift P r level g) := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    let tSL : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level)) := t
    let lift : IndexCompletedNormOneInnerForm P r level :=
      orderIndexNormOneCompletedInnerFormLift P r level g
    let liftSL : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level)) := lift
    let a : PowerSeries (ResidueField P r level) :=
      ((tSL : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level))) i j)
    let b : PowerSeries (ResidueField P r level) :=
      ((liftSL : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level))) i j)
    change PowerSeries.constantCoeff a = PowerSeries.constantCoeff b
    have hclose := hs i j
    rw [← htlocal] at hclose
    change Valued.v.restrict
      (HahnSeries.ofPowerSeries ℤ (ResidueField P r level) a -
        HahnSeries.ofPowerSeries ℤ (ResidueField P r level) b) < 1 at hclose
    rw [← map_sub, Valuation.restrict_lt_one_iff] at hclose
    let z : IndexCongruenceLocalIntegers P r level :=
      ⟨HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
        (a - b),
        le_of_lt hclose⟩
    have hz0 :=
      (indexCongruenceLocalIntegers_constantCoeff_eq_zero_iff
        P r level z).mpr hclose
    have hz : indexCongruenceLocalIntegersRingEquivPowerSeries P r level z =
        a - b :=
      indexCongruenceLocalIntegersRingEquivPowerSeries_ofPowerSeries
        P r level (a - b)
    rw [hz] at hz0
    simpa only [map_sub, sub_eq_zero] using hz0
  exact hred.trans (indexCompletedNormOneReduction_lift P r level g)

/-- Units of the intrinsic adic cyclic algebra identified with general
linear matrices over the concrete selected Laurent field. -/
noncomputable def indexAdicCyclicAlgebraUnitEquivIndexLocalGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexAdicCyclicAlgebra P r level)ˣ ≃*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level) :=
  Units.mapEquiv
    (indexAdicCyclicAlgebraEquivIndexLocalMatrix P r level).toMulEquiv

/-- Pull a completed integral special-linear point back through the actual
adic cyclic splitting equivalence. -/
noncomputable def indexCompletedNormOneInnerFormToIndexAdicCyclicUnit
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level) :
    (IndexAdicCyclicAlgebra P r level)ˣ :=
  (indexAdicCyclicAlgebraUnitEquivIndexLocalGL P r level).symm
    (Matrix.SpecialLinearGroup.toGL
      (indexCompletedNormOneInnerFormToIndexLocal P r level s))

@[simp] theorem indexAdicCyclicAlgebraUnitEquivIndexLocalGL_completed
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level) :
    indexAdicCyclicAlgebraUnitEquivIndexLocalGL P r level
        (indexCompletedNormOneInnerFormToIndexAdicCyclicUnit
          P r level s) =
      Matrix.SpecialLinearGroup.toGL
        (indexCompletedNormOneInnerFormToIndexLocal P r level s) := by
  exact (indexAdicCyclicAlgebraUnitEquivIndexLocalGL
    P r level).apply_symm_apply _

/-- The value of the pulled-back adic unit is exactly the explicit
coefficientwise completed-matrix lift. -/
theorem indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_val
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level) :
    (indexCompletedNormOneInnerFormToIndexAdicCyclicUnit P r level s :
        IndexAdicCyclicAlgebra P r level) =
      indexCompletedMatrixToIndexAdicCyclicAlgebra P r level
        ((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (PowerSeries (ResidueField P r level))) :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (PowerSeries (ResidueField P r level))) := by
  apply (indexAdicCyclicAlgebraToIndexLocalMatrix_bijective
    P r level).1
  rw [indexAdicCyclicAlgebraToIndexLocalMatrix_completedMatrixLift]
  have h := congrArg Units.val
    (indexAdicCyclicAlgebraUnitEquivIndexLocalGL_completed
      P r level s)
  simpa [indexAdicCyclicAlgebraUnitEquivIndexLocalGL,
    indexAdicCyclicAlgebraEquivIndexLocalMatrix,
    indexCompletedNormOneInnerFormToIndexLocal] using h

/-- The inverse of the pulled-back adic unit is the explicit lift of the
inverse completed special-linear matrix. -/
theorem indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_inv_val
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level) :
    ((indexCompletedNormOneInnerFormToIndexAdicCyclicUnit
        P r level s)⁻¹ : (IndexAdicCyclicAlgebra P r level)ˣ) =
      indexCompletedNormOneInnerFormToIndexAdicCyclicUnit
        P r level s⁻¹ := by
  apply (indexAdicCyclicAlgebraUnitEquivIndexLocalGL P r level).injective
  simp [indexCompletedNormOneInnerFormToIndexAdicCyclicUnit,
    indexCompletedNormOneInnerFormToIndexLocal]

/-- The general-linear realization commutes with passing from the abstract
adic cyclic algebra to the concrete Laurent cyclic algebra. -/
theorem indexLocalCyclicAlgebraUnitEquivGL_adic_compatibility
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (IndexAdicCyclicAlgebra P r level)ˣ) :
    indexLocalCyclicAlgebraUnitEquivGL P r level
        (Units.map
          (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra
            P r level).toRingHom.toMonoidHom u) =
      indexAdicCyclicAlgebraUnitEquivIndexLocalGL P r level u := by
  apply Units.ext
  exact (DFunLike.congr_fun
    (indexAdicCyclicAlgebraToIndexLocalMatrix_factorization P r level)
      (u : IndexAdicCyclicAlgebra P r level)).symm

/-- The pulled-back adic unit of every completed integral special-linear
point has genuine local reduced norm one. -/
theorem indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_normOne
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level) :
    indexLocalCyclicAlgebraReducedNorm P r level
        (Units.map
          (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra
            P r level).toRingHom.toMonoidHom
          (indexCompletedNormOneInnerFormToIndexAdicCyclicUnit
            P r level s)) = 1 := by
  rw [indexLocalCyclicAlgebraReducedNorm,
    MonoidHom.comp_apply]
  change Matrix.GeneralLinearGroup.det
      (indexLocalCyclicAlgebraUnitEquivGL P r level
        (Units.map
          (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra
            P r level).toRingHom.toMonoidHom
          (indexCompletedNormOneInnerFormToIndexAdicCyclicUnit
            P r level s))) = 1
  rw [indexLocalCyclicAlgebraUnitEquivGL_adic_compatibility,
    indexAdicCyclicAlgebraUnitEquivIndexLocalGL_completed]
  apply Units.ext
  exact (indexCompletedNormOneInnerFormToIndexLocal P r level s).property

/-- The pulled-back adic unit and its inverse both lie in the intrinsic
adic integral cyclic lattice. -/
theorem indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_integral
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level) :
    (indexCompletedNormOneInnerFormToIndexAdicCyclicUnit P r level s :
        IndexAdicCyclicAlgebra P r level) ∈
        IndexAdicCyclicIntegralLattice P r level ∧
      (((indexCompletedNormOneInnerFormToIndexAdicCyclicUnit
          P r level s)⁻¹ : (IndexAdicCyclicAlgebra P r level)ˣ) :
        IndexAdicCyclicAlgebra P r level) ∈
          IndexAdicCyclicIntegralLattice P r level := by
  constructor
  · rw [indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_val]
    exact indexCompletedMatrixToIndexAdicCyclicAlgebra_mem_integral
      P r level _
  · rw [indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_inv_val,
      indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_val]
    exact indexCompletedMatrixToIndexAdicCyclicAlgebra_mem_integral
      P r level _

/-- The explicit one-place finite-adelic `SL₁(D)` lift of a completed
integral special-linear point. -/
noncomputable def indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level) :
    ArithmeticFiniteAdeleCyclicNormOne P r :=
  arithmeticFiniteAdeleNormOneSupportedAtIndexPlace P r level
    (indexCompletedNormOneInnerFormToIndexAdicCyclicUnit P r level s)
    (by
      rw [arithmeticFiniteAdeleCyclicUnitToIndexLocal_supported]
      exact indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_normOne
        P r level s)

/-- Every completed integral special-linear point has a finite-adelic
norm-one lift in the genuine all-place integral chart. -/
theorem indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne_integral
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level) :
    indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne
        P r level s ∈
      ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r := by
  have hint := indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_integral
    P r level s
  apply arithmeticFiniteAdeleNormOneSupportedAtIndexPlace_mem_integral
  · exact hint.1
  · exact hint.2

/-- Selected-place localization of the integral adelic lift recovers the
original completed special-linear point after the canonical Laurent
embedding. -/
theorem indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne_projection
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level) :
    indexLocalCyclicAlgebraNormOneEquivSL P r level
        (arithmeticFiniteAdeleNormOneToIndexLocalNormOne P r level
          (indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne
            P r level s)) =
      indexCompletedNormOneInnerFormToIndexLocal P r level s := by
  have hGL : indexLocalCyclicAlgebraUnitEquivGL P r level
      (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level
        (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace P r level
          (indexCompletedNormOneInnerFormToIndexAdicCyclicUnit
            P r level s))) =
    Matrix.SpecialLinearGroup.toGL
      (indexCompletedNormOneInnerFormToIndexLocal P r level s) := by
    rw [arithmeticFiniteAdeleCyclicUnitToIndexLocal_supported,
      indexLocalCyclicAlgebraUnitEquivGL_adic_compatibility,
      indexAdicCyclicAlgebraUnitEquivIndexLocalGL_completed]
  apply Matrix.SpecialLinearGroup.toGL_injective
  apply Units.ext
  have hmatrix := congrArg Units.val hGL
  simp [indexLocalCyclicAlgebraNormOneEquivSL,
    arithmeticFiniteAdeleNormOneToIndexLocalNormOne,
    indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne,
    arithmeticFiniteAdeleNormOneSupportedAtIndexPlace] at hmatrix ⊢
  exact hmatrix

/-- A global rational norm-one point lying in a selected finite-target
neighborhood has no denominator at the selected congruence place.  Its
remaining denominator support is therefore a finite set of other arithmetic
places. -/
theorem indexCongruencePlace_not_mem_cyclicAlgebraNormOneDenominatorPlaces
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level))
    (u : CyclicAlgebraNormOne P r)
    (hu : cyclicAlgebraNormOneToIndexLocal P r level u ∈
      indexLocalNormOneFiniteTargetNeighborhood P r level g) :
    indexCongruencePlace P r level ∉
      cyclicAlgebraNormOneDenominatorPlaces P r u := by
  obtain ⟨t, htlocal, _⟩ :=
    exists_indexCompletedNormOne_of_mem_finiteTargetNeighborhood
      P r level g (cyclicAlgebraNormOneToIndexLocal P r level u) hu
  let a : ArithmeticFiniteAdeleCyclicNormOne P r :=
    cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r u
  let b : ArithmeticFiniteAdeleCyclicNormOne P r :=
    indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne
      P r level t
  have hprojNorm :
      arithmeticFiniteAdeleNormOneToIndexLocalNormOne P r level a =
        arithmeticFiniteAdeleNormOneToIndexLocalNormOne P r level b := by
    apply (indexLocalCyclicAlgebraNormOneEquivSL P r level).injective
    calc
      indexLocalCyclicAlgebraNormOneEquivSL P r level
          (arithmeticFiniteAdeleNormOneToIndexLocalNormOne P r level a) =
        cyclicAlgebraNormOneToIndexLocal P r level u := by
          rw [show a = cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne
              P r u from rfl,
            arithmeticFiniteAdeleNormOneToIndexLocalNormOne_diagonal,
            cyclicAlgebraNormOneToIndexLocalNormOne_compatibility]
      _ = indexCompletedNormOneInnerFormToIndexLocal P r level t :=
        htlocal.symm
      _ = indexLocalCyclicAlgebraNormOneEquivSL P r level
          (arithmeticFiniteAdeleNormOneToIndexLocalNormOne P r level b) := by
        rw [show b =
            indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne
              P r level t from rfl]
        exact
          (indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne_projection
            P r level t).symm
  change indexCongruencePlace P r level ∉
    arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r a.1
  apply indexCongruencePlace_not_mem_denominatorPlaces_of_projection_eq
    P r level a.1 b.1
  · exact congrArg Subtype.val hprojNorm
  · exact indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne_integral
      P r level t

/-- For every finite special-linear target there is a global rational
norm-one approximant with finite denominator support disjoint from the
selected congruence place. -/
theorem exists_cyclicAlgebraNormOne_with_finite_offTarget_denominators
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    ∃ u : CyclicAlgebraNormOne P r,
      cyclicAlgebraNormOneToIndexLocal P r level u ∈
          indexLocalNormOneFiniteTargetNeighborhood P r level g ∧
        (cyclicAlgebraNormOneDenominatorPlaces P r u).Finite ∧
        indexCongruencePlace P r level ∉
          cyclicAlgebraNormOneDenominatorPlaces P r u := by
  obtain ⟨u, hu⟩ :=
    exists_cyclicAlgebraNormOne_mem_indexLocalFiniteTargetNeighborhood
      P r level g
  exact ⟨u, hu,
    cyclicAlgebraNormOneDenominatorPlaces_finite P r u,
    indexCongruencePlace_not_mem_cyclicAlgebraNormOneDenominatorPlaces
      P r level g u hu⟩

/-- Cyclic reduction of the integral adelic lift agrees exactly with the
existing completed special-linear reduction. -/
theorem indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne_reduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level) :
    arithmeticFiniteAdeleCyclicIntegralReduction P r level
        ⟨(indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne
            P r level s).1.1,
          (indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne_integral
            P r level s).1⟩ =
      ((indexCompletedNormOneReduction P r level s :
          Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ResidueField P r level)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) := by
  have hint := indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_integral
    P r level s
  change arithmeticFiniteAdeleCyclicIntegralReduction P r level
      ⟨arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level
        (indexCompletedNormOneInnerFormToIndexAdicCyclicUnit
          P r level s), _⟩ = _
  rw [arithmeticFiniteAdeleCyclicIntegralReduction_patchAtIndexPlace
    P r level _ hint.1]
  let x : IndexAdicCyclicIntegralElement P r level :=
    ⟨indexCompletedNormOneInnerFormToIndexAdicCyclicUnit P r level s,
      hint.1⟩
  let y : IndexAdicCyclicIntegralElement P r level :=
    ⟨indexCompletedMatrixToIndexAdicCyclicAlgebra P r level
      ((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level))) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))),
      indexCompletedMatrixToIndexAdicCyclicAlgebra_mem_integral
        P r level _⟩
  have hxy : x = y := by
    apply Subtype.ext
    exact indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_val
      P r level s
  change indexAdicCyclicIntegralReduction P r level x = _
  rw [hxy]
  rw [indexAdicCyclicIntegralReduction_completedMatrixLift]
  rfl

/-- An explicit integral finite-adelic norm-one lift of every selected
finite special-linear target. -/
noncomputable def finiteSpecialLinearToArithmeticFiniteAdeleNormOne
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    ArithmeticFiniteAdeleCyclicNormOne P r :=
  indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne P r level
    (orderIndexNormOneCompletedInnerFormLift P r level g)

/-- The explicit finite-special-linear adelic lift belongs to the genuine
all-place integral norm-one chart. -/
theorem finiteSpecialLinearToArithmeticFiniteAdeleNormOne_integral
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    finiteSpecialLinearToArithmeticFiniteAdeleNormOne P r level g ∈
      ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r :=
  indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne_integral
    P r level (orderIndexNormOneCompletedInnerFormLift P r level g)

/-- The explicit integral adelic lift has precisely the prescribed finite
special-linear residue matrix. -/
theorem finiteSpecialLinearToArithmeticFiniteAdeleNormOne_reduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    arithmeticFiniteAdeleCyclicIntegralReduction P r level
        ⟨(finiteSpecialLinearToArithmeticFiniteAdeleNormOne
            P r level g).1.1,
          (finiteSpecialLinearToArithmeticFiniteAdeleNormOne_integral
            P r level g).1⟩ =
      (g : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level)) := by
  have hred :=
    indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne_reduction
      P r level (orderIndexNormOneCompletedInnerFormLift P r level g)
  have hlift := congrArg Subtype.val
    (indexCompletedNormOneReduction_lift P r level g)
  simpa [finiteSpecialLinearToArithmeticFiniteAdeleNormOne] using
    hred.trans hlift

/-- The open norm-one congruence chart above a prescribed selected-place
finite special-linear matrix.  Besides fixing the residue, the definition
retains integrality of the inverse, so an approximating global point
descends to an actual unit of the Cartwright--Steger order. -/
noncomputable def arithmeticFiniteAdeleCyclicNormOneCongruenceNeighborhood
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    Set (ArithmeticFiniteAdeleCyclicNormOne P r) :=
  ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r ∩
    {u | u.1.1 ∈ arithmeticFiniteAdeleCyclicCongruenceNeighborhood
      P r level (g : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level))}

/-- The genuine norm-one congruence chart is open in finite-adelic
`SL₁(D)`. -/
theorem isOpen_arithmeticFiniteAdeleCyclicNormOneCongruenceNeighborhood
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    IsOpen (arithmeticFiniteAdeleCyclicNormOneCongruenceNeighborhood
      P r level g) := by
  exact (isOpen_arithmeticFiniteAdeleCyclicIntegralNormOneSet P r).inter
    ((isOpen_arithmeticFiniteAdeleCyclicCongruenceNeighborhood P r level
      (g : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level))).preimage
      (Units.continuous_val.comp continuous_subtype_val))

/-- Every finite special-linear target has a point in its genuine
finite-adelic norm-one congruence chart. -/
theorem arithmeticFiniteAdeleCyclicNormOneCongruenceNeighborhood_nonempty
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    (arithmeticFiniteAdeleCyclicNormOneCongruenceNeighborhood
      P r level g).Nonempty := by
  refine ⟨finiteSpecialLinearToArithmeticFiniteAdeleNormOne P r level g,
    finiteSpecialLinearToArithmeticFiniteAdeleNormOne_integral
      P r level g, ?_⟩
  change
    (finiteSpecialLinearToArithmeticFiniteAdeleNormOne P r level g).1.1 ∈
      arithmeticFiniteAdeleCyclicCongruenceNeighborhood P r level
        (g : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level))
  rw [mem_arithmeticFiniteAdeleCyclicCongruenceNeighborhood_iff]
  exact ⟨(finiteSpecialLinearToArithmeticFiniteAdeleNormOne_integral
      P r level g).1,
    finiteSpecialLinearToArithmeticFiniteAdeleNormOne_reduction
      P r level g⟩

theorem indexCompletedNormOneInnerFormToIndexLocal_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective
      (indexCompletedNormOneInnerFormToIndexLocal P r level) := by
  intro s t h
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  have hij := congrArg (fun M => M i j) (congrArg Subtype.val h)
  exact HahnSeries.ofPowerSeries_injective hij

/-- The integral points inside the selected Laurent local norm-one group. -/
noncomputable abbrev IndexLocalIntegralNormOneInnerForm
    (P : BasePrime) (r : Rank) (level : Nat) :=
  (indexCompletedNormOneInnerFormToIndexLocal P r level).range

/-- The power-series model and the actual integral subgroup of the Laurent
local group are canonically the same group. -/
noncomputable def indexCompletedNormOneInnerFormEquivIndexLocalIntegral
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCompletedNormOneInnerForm P r level ≃*
      IndexLocalIntegralNormOneInnerForm P r level :=
  MulEquiv.ofBijective
    (indexCompletedNormOneInnerFormToIndexLocal P r level).rangeRestrict
    ⟨(MonoidHom.rangeRestrict_injective_iff.mpr
      (indexCompletedNormOneInnerFormToIndexLocal_injective P r level)),
      MonoidHom.rangeRestrict_surjective _⟩

/-- Reduction from the genuine integral subgroup of the Laurent local
norm-one group to finite `SL`. -/
noncomputable def indexLocalIntegralNormOneReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexLocalIntegralNormOneInnerForm P r level →*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
  (indexCompletedNormOneReduction P r level).comp
    (indexCompletedNormOneInnerFormEquivIndexLocalIntegral
      P r level).symm.toMonoidHom

/-- The local-lifting half of the LSV argument, now stated on the actual
integral subgroup of the selected Laurent local group. -/
theorem indexLocalIntegralNormOneReduction_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
      (indexLocalIntegralNormOneReduction P r level) := by
  intro s
  obtain ⟨t, ht⟩ := indexCompletedNormOneReduction_surjective P r level s
  refine ⟨indexCompletedNormOneInnerFormEquivIndexLocalIntegral
    P r level t, ?_⟩
  simpa [indexLocalIntegralNormOneReduction]

/-- The selected-place localization of every intrinsic global `S`-integral
norm-one point, with codomain the genuine integral subgroup of the Laurent
local norm-one group. -/
noncomputable def sIntegralNormOneToIndexLocalIntegral
    (P : BasePrime) (r : Rank) (level : Nat) :
    CartwrightStegerSIntegralNormOne P r →*
      IndexLocalIntegralNormOneInnerForm P r level :=
  (indexCompletedNormOneInnerFormEquivIndexLocalIntegral
    P r level).toMonoidHom.comp
      (baseNormOneOrderUnitsToCompleted P r level)

/-- Finite special-linear reduction of the actual global `S`-integral
norm-one group.  Its surjectivity is the remaining finite endpoint of the
construction-specialized Prasad argument. -/
noncomputable def sIntegralNormOneReductionToSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    CartwrightStegerSIntegralNormOne P r →*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
  (indexLocalIntegralNormOneReduction P r level).comp
    (sIntegralNormOneToIndexLocalIntegral P r level)

theorem sIntegralNormOneReductionToSL_factor_completed
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : CartwrightStegerSIntegralNormOne P r) :
    sIntegralNormOneReductionToSL P r level u =
      indexCompletedNormOneReduction P r level
        (baseNormOneOrderUnitsToCompleted P r level u) := by
  simp [sIntegralNormOneReductionToSL,
    sIntegralNormOneToIndexLocalIntegral,
    indexLocalIntegralNormOneReduction]

/-- The construction-specialized Prasad assumption implies surjectivity of
the actual finite `SL` reduction.  The sole external input is the precise
finite-adelic density statement used in [Pra77, pp. 553--572] and in the
proof of [LSV05b, Theorem `isonto`].  Everything after that input is proved
here: the dense range meets the explicit nonempty open congruence chart,
and inverse-integrality descends the resulting global rational point to a
genuine Cartwright--Steger order unit. -/
theorem sIntegralNormOneReductionToSL_surjective_of_prasadStrongApproximation
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r)) :
    Function.Surjective (sIntegralNormOneReductionToSL P r level) := by
  intro g
  let U : Set (ArithmeticFiniteAdeleCyclicNormOne P r) :=
    arithmeticFiniteAdeleCyclicNormOneCongruenceNeighborhood
      P r level g
  have hUopen : IsOpen U :=
    isOpen_arithmeticFiniteAdeleCyclicNormOneCongruenceNeighborhood
      P r level g
  have hUne : U.Nonempty :=
    arithmeticFiniteAdeleCyclicNormOneCongruenceNeighborhood_nonempty
      P r level g
  obtain ⟨z, hzU, hzrange⟩ :=
    dense_iff_inter_open.mp hPrasad U hUopen hUne
  obtain ⟨u, rfl⟩ := hzrange
  have hint :
      cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r u ∈
        ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r := hzU.1
  rw [cyclicAlgebraNormOne_preimage_integralNormOneSet] at hint
  obtain ⟨s, hs⟩ := hint
  have hcong := hzU.2
  rw [← hs] at hcong
  change cyclicAlgebraToArithmeticFiniteAdeles P r
      (orderNormOneInnerFormCyclicAlgebraPoint P r s) ∈
    arithmeticFiniteAdeleCyclicCongruenceNeighborhood P r level
      (g : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level)) at hcong
  have hred :=
    (orderNormOneInnerForm_mem_arithmeticFiniteAdeleCyclicCongruenceNeighborhood_iff
      P r level s
        (g : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level))).mp hcong
  refine ⟨orderNormOneInnerFormEquivBaseNormOneOrderUnits P r s, ?_⟩
  rw [sIntegralNormOneReductionToSL_factor_completed]
  change indexCompletedNormOneReduction P r level
      (orderNormOneInnerFormToCompleted P r level
        ((orderNormOneInnerFormEquivBaseNormOneOrderUnits P r).symm
          (orderNormOneInnerFormEquivBaseNormOneOrderUnits P r s))) = g
  rw [(orderNormOneInnerFormEquivBaseNormOneOrderUnits P r).symm_apply_apply]
  rw [indexCompletedNormOneReduction_global_compatibility]
  apply Subtype.ext
  exact hred

/-- The source theorem's projective finite reduction
`G'_1(R) → G'_1(R/𝔭) = PSL_d(k_𝔭)`, now on the actual construction-owned
`S`-integral norm-one group. -/
noncomputable def sIntegralNormOneReductionToPSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    CartwrightStegerSIntegralNormOne P r →* PSL P r level :=
  (specialLinearToPSL P r level).comp
    (sIntegralNormOneReductionToSL P r level)

theorem sIntegralNormOneReductionToPSL_eq_baseReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    sIntegralNormOneReductionToPSL P r level =
      baseNormOneOrderUnitsReduction P r level := by
  ext u
  rw [sIntegralNormOneReductionToPSL, MonoidHom.comp_apply,
    sIntegralNormOneReductionToSL_factor_completed,
    baseNormOneOrderUnitsReduction_factor_completed]

/-- Exact finite endpoint of the remaining Prasad step: surjectivity of the
intrinsic `S`-integral reduction is equivalent to containment of the full
finite `PSL` in the genuine Cartwright--Steger image. -/
theorem sIntegralNormOneReductionToPSL_surjective_iff_PSL_le_image
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (sIntegralNormOneReductionToPSL P r level) ↔
      PSL P r level ≤ IndexCartwrightStegerImage P r level := by
  rw [sIntegralNormOneReductionToPSL_eq_baseReduction,
    baseNormOneOrderUnitsReduction_surjective_iff_PSL_le_image]

/-- Projectivizing the construction-specialized Prasad consequence gives
surjectivity of the genuine `S`-integral reduction to finite `PSL`.  No
finite reduction or image-containment statement is assumed. -/
theorem sIntegralNormOneReductionToPSL_surjective_of_prasadStrongApproximation
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r)) :
    Function.Surjective (sIntegralNormOneReductionToPSL P r level) := by
  intro y
  obtain ⟨g, rfl⟩ := specialLinearToPSL_surjective P r level y
  obtain ⟨u, hu⟩ :=
    sIntegralNormOneReductionToSL_surjective_of_prasadStrongApproximation
      P r level hPrasad g
  refine ⟨u, ?_⟩
  change specialLinearToPSL P r level
      (sIntegralNormOneReductionToSL P r level u) =
    specialLinearToPSL P r level g
  rw [hu]

/-- The intrinsic norm-one order-unit reduction is surjective under exactly
the construction-specialized Prasad density assumption. -/
theorem baseNormOneOrderUnitsReduction_surjective_of_prasadStrongApproximation
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r)) :
    Function.Surjective (baseNormOneOrderUnitsReduction P r level) := by
  rw [← sIntegralNormOneReductionToPSL_eq_baseReduction P r level]
  exact
    sIntegralNormOneReductionToPSL_surjective_of_prasadStrongApproximation
      P r level hPrasad

/-- The exact LSV finite-image consequence of the external Prasad input:
the full selected finite `PSL` lies in the genuine Cartwright--Steger image.
Normality, nontriviality, local lifting, and finite `PSL` simplicity are all
proved in the construction chain rather than included in the assumption. -/
theorem PSL_le_IndexCartwrightStegerImage_of_prasadStrongApproximation
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r)) :
    PSL P r level ≤ IndexCartwrightStegerImage P r level :=
  (sIntegralNormOneReductionToPSL_surjective_iff_PSL_le_image
    P r level).mp
      (sIntegralNormOneReductionToPSL_surjective_of_prasadStrongApproximation
        P r level hPrasad)

/-- For an integral global norm-one point, the rational localization route
and the completed-integral route give the same selected local point. -/
theorem cyclicAlgebraNormOneToIndexLocal_order_compatibility
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : OrderNormOneInnerForm P r) :
    cyclicAlgebraNormOneToIndexLocal P r level
        (orderNormOneInnerFormToCyclicAlgebraNormOne P r s) =
      indexCompletedNormOneInnerFormToIndexLocal P r level
        (orderNormOneInnerFormToCompleted P r level s) := by
  rw [cyclicAlgebraNormOneToIndexLocal, MonoidHom.comp_apply,
    cyclicAlgebraNormOneToSplittingSL_order_compatibility]
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  change splittingFunctionFieldToIndexCongruenceLocalField P r level
      (constantArithmeticToSplittingFunctionField P r
        ((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) i j)) =
    HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
      (indexCompletedArithmeticEval P r level
        ((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) i j))
  exact DFunLike.congr_fun
    (splittingFunctionFieldToIndexCongruenceLocalField_constantArithmetic
      P r level)
    ((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) i j)

/-- The intrinsic global, completed-integral, and Laurent-local routes form
the same localization map on every actual `S`-integral norm-one point. -/
theorem sIntegralNormOneToIndexLocalIntegral_compatibility
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : CartwrightStegerSIntegralNormOne P r) :
    (sIntegralNormOneToIndexLocalIntegral P r level u :
        IndexLocalNormOneInnerForm P r level) =
      cyclicAlgebraNormOneToIndexLocal P r level
        (sIntegralNormOneToCyclicAlgebraNormOne P r u) := by
  symm
  exact cyclicAlgebraNormOneToIndexLocal_order_compatibility P r level
    ((orderNormOneInnerFormEquivSIntegralNormOne P r).symm u)

/-- Intrinsic global reduced-norm-one points embedded into the genuine
building-place local norm-one group. -/
noncomputable def cyclicAlgebraNormOneToBuildingLocal
    (P : BasePrime) (r : Rank) :
    CyclicAlgebraNormOne P r →*
      BuildingCyclicScalarExtensionNormOne P r :=
  (cyclicAlgebraBuildingNormOneToLocal P r).comp
    (MulEquiv.subgroupCongr
      (cyclicAlgebraBuildingNormOne_eq_normOne P r).symm).toMonoidHom

theorem cyclicAlgebraNormOneToBuildingLocal_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (cyclicAlgebraNormOneToBuildingLocal P r) :=
  (cyclicAlgebraBuildingNormOneToLocal_injective P r).comp
    (MulEquiv.subgroupCongr
      (cyclicAlgebraBuildingNormOne_eq_normOne P r).symm).injective

/-- The construction-owned integral norm-one inner form embedded at the
distinguished building place. -/
noncomputable def orderNormOneInnerFormToBuildingLocal
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r →*
      BuildingCyclicScalarExtensionNormOne P r :=
  (cyclicAlgebraNormOneToBuildingLocal P r).comp
    (orderNormOneInnerFormToCyclicAlgebraNormOne P r)

/-- Intrinsic norm-one order units embedded at the building place. -/
noncomputable def baseNormOneOrderUnitsToBuildingLocal
    (P : BasePrime) (r : Rank) :
    CartwrightStegerBaseNormOneOrderUnits P r →*
      BuildingCyclicScalarExtensionNormOne P r :=
  (orderNormOneInnerFormToBuildingLocal P r).comp
    (orderNormOneInnerFormEquivBaseNormOneOrderUnits P r).symm.toMonoidHom

/-! ## Consequences of finite `PSL` containment -/

/-- If the genuine finite image contains `PSL`, its color-zero subgroup is
not merely analogous to `PSL`: it is canonically isomorphic to the full
finite projective special-linear group. -/
noncomputable def indexCartwrightStegerColorZeroEquivPSLOfLe
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexCartwrightStegerImage P r level) :
    IndexCartwrightStegerColorZero P r level ≃* PSL P r level where
  toFun g :=
    ⟨(g : IndexCartwrightStegerImage P r level),
      (mem_IndexCartwrightStegerColorZero_iff_mem_PSL
        P r level (g : IndexCartwrightStegerImage P r level)).mp
          g.property⟩
  invFun s := by
    let g : IndexCartwrightStegerImage P r level :=
      ⟨s, hPSL s.property⟩
    exact ⟨g,
      (mem_IndexCartwrightStegerColorZero_iff_mem_PSL
        P r level g).mpr s.property⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv s := by
    apply Subtype.ext
    rfl
  map_mul' g h := by
    apply Subtype.ext
    rfl

/-- Containment of finite `PSL` gives the exact cardinal lower bound needed
for the Cartwright--Steger quotient hierarchy. -/
theorem natCard_PSL_le_indexCartwrightStegerImage_of_le
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexCartwrightStegerImage P r level) :
    Nat.card (PSL P r level) ≤
      Nat.card (IndexCartwrightStegerImage P r level) := by
  letI : Finite (PGL P r level) :=
    Finite.of_surjective
      (Matrix.ProjGenLinGroup.mk :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (ResidueField P r level) → PGL P r level)
      Matrix.ProjGenLinGroup.mk_surjective
  letI : Finite (IndexCartwrightStegerImage P r level) :=
    Finite.of_injective
      (fun g : IndexCartwrightStegerImage P r level =>
        (g : PGL P r level))
      Subtype.val_injective
  exact Nat.card_le_card_of_injective
    (fun s : PSL P r level =>
      (⟨s, hPSL s.property⟩ : IndexCartwrightStegerImage P r level))
    (fun _ _ h => Subtype.ext <| congrArg
      (fun g : IndexCartwrightStegerImage P r level =>
        (g : PGL P r level)) h)

/-- Once specialized strong approximation supplies `PSL` containment at
every selected congruence place, the actual finite Cartwright--Steger image
sizes are unbounded. -/
theorem indexCartwrightStegerImage_unbounded_of_PSL_le
    (P : BasePrime) (r : Rank)
    (hPSL : ∀ level,
      PSL P r level ≤ IndexCartwrightStegerImage P r level)
    (bound : Nat) :
    ∃ level, bound <
      Nat.card (IndexCartwrightStegerImage P r level) := by
  obtain ⟨level, hlevel⟩ := CongruenceLifting.PSL_unbounded P r bound
  exact ⟨level, hlevel.trans_le
    (natCard_PSL_le_indexCartwrightStegerImage_of_le
      P r level (hPSL level))⟩

/-- Under the sole construction-specialized Prasad density premise, the
color-zero subgroup of the actual Cartwright--Steger finite image is the full
selected finite `PSL`. -/
noncomputable def
    indexCartwrightStegerColorZeroEquivPSLOfPrasadStrongApproximation
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r)) :
    IndexCartwrightStegerColorZero P r level ≃* PSL P r level :=
  indexCartwrightStegerColorZeroEquivPSLOfLe P r level
    (PSL_le_IndexCartwrightStegerImage_of_prasadStrongApproximation
      P r level hPrasad)

/-- The actual finite Cartwright--Steger images form an unbounded hierarchy
under exactly the construction-specialized Prasad density premise.  No
finite-image containment or cardinal-growth statement is assumed. -/
theorem indexCartwrightStegerImage_unbounded_of_prasadStrongApproximation
    (P : BasePrime) (r : Rank)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r))
    (bound : Nat) :
    ∃ level, bound <
      Nat.card (IndexCartwrightStegerImage P r level) :=
  indexCartwrightStegerImage_unbounded_of_PSL_le P r
    (fun level =>
      PSL_le_IndexCartwrightStegerImage_of_prasadStrongApproximation
        P r level hPrasad)
    bound

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
