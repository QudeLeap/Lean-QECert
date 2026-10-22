import QEC.Coding.AlgebraicGeometry.Towers.QuadraticStepDifferent

import Mathlib.NumberTheory.RamificationInertia.Unramified

/-!
# A regular quadratic Artin--Schreier step

This file constructs the literal quadratic extension `y² + y = b` when
`b` belongs to the lower valuation ring and the corresponding polynomial is
irreducible over the lower field.  Its derivative is one.  Evaluating that
derivative at the actual integral root puts one in the different ideal, so
the different is the unit ideal at every upper prime.

The irreducibility input is field-construction data that the later compositum
argument must derive.  No linear-disjointness, compositum, normal-closure,
divisor, genus, or tower conclusion is stored here.
-/

open Polynomial

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {K : Type*} [Field K] [Algebra F256 K]

/-- The integral polynomial `Y² + Y + b` for a regular Artin--Schreier
parameter. -/
noncomputable def regularQuadraticArtinSchreierIntegralPolynomial
    (P : GlobalPlace F256 K) (b : P.valuationRing) : P.valuationRing[X] :=
  X ^ 2 + X + C b

theorem regularQuadraticArtinSchreierIntegralPolynomial_monic
    (P : GlobalPlace F256 K) (b : P.valuationRing) :
    (regularQuadraticArtinSchreierIntegralPolynomial P b).Monic := by
  rw [regularQuadraticArtinSchreierIntegralPolynomial, add_assoc]
  exact Monic.add_of_left (monic_X_pow 2) (by
    calc
      ((X : P.valuationRing[X]) + C b).degree ≤ (1 : WithBot ℕ) := by
        apply degree_add_le_of_degree_le
        · exact degree_X_le
        · exact degree_C_le.trans (by norm_num)
      _ < ((X : P.valuationRing[X]) ^ 2).degree := by
        rw [degree_X_pow]
        norm_num)

@[simp]
theorem regularQuadraticArtinSchreierIntegralPolynomial_natDegree
    (P : GlobalPlace F256 K) (b : P.valuationRing) :
    (regularQuadraticArtinSchreierIntegralPolynomial P b).natDegree = 2 := by
  apply natDegree_eq_of_degree_eq_some
  rw [regularQuadraticArtinSchreierIntegralPolynomial, add_assoc,
    degree_add_eq_left_of_degree_lt]
  · exact degree_X_pow (R := P.valuationRing) 2
  · calc
      ((X : P.valuationRing[X]) + C b).degree ≤ (1 : WithBot ℕ) := by
        apply degree_add_le_of_degree_le
        · exact degree_X_le
        · exact degree_C_le.trans (by norm_num)
      _ < ((X : P.valuationRing[X]) ^ 2).degree := by
        rw [degree_X_pow]
        norm_num

/-- The regular integral polynomial transported to the lower field. -/
noncomputable def regularQuadraticArtinSchreierPolynomial
    (P : GlobalPlace F256 K) (b : P.valuationRing) : K[X] :=
  (regularQuadraticArtinSchreierIntegralPolynomial P b).map
    (algebraMap P.valuationRing K)

private theorem regularQuadraticArtinSchreierPolynomial_eq_explicit
    (P : GlobalPlace F256 K) (b : P.valuationRing) :
    regularQuadraticArtinSchreierPolynomial P b =
      X ^ 2 + X + C (b : K) := by
  simp [regularQuadraticArtinSchreierPolynomial,
    regularQuadraticArtinSchreierIntegralPolynomial]

theorem regularQuadraticArtinSchreierPolynomial_monic
    (P : GlobalPlace F256 K) (b : P.valuationRing) :
    (regularQuadraticArtinSchreierPolynomial P b).Monic :=
  (regularQuadraticArtinSchreierIntegralPolynomial_monic P b).map _

@[simp]
theorem regularQuadraticArtinSchreierPolynomial_natDegree
    (P : GlobalPlace F256 K) (b : P.valuationRing) :
    (regularQuadraticArtinSchreierPolynomial P b).natDegree = 2 := by
  rw [regularQuadraticArtinSchreierPolynomial,
    (regularQuadraticArtinSchreierIntegralPolynomial_monic P b).natDegree_map,
    regularQuadraticArtinSchreierIntegralPolynomial_natDegree]

theorem regularQuadraticArtinSchreierPolynomial_separable
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    (regularQuadraticArtinSchreierPolynomial P b).Separable := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  rw [Polynomial.separable_iff_derivative_ne_zero hirr]
  rw [regularQuadraticArtinSchreierPolynomial_eq_explicit]
  simp only [derivative_add, derivative_X_pow, derivative_X, derivative_C]
  reduce_mod_char!
  norm_num

private noncomputable def regularQuadraticArtinSchreierDefiningPolynomial
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (_hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) : K[X] :=
  regularQuadraticArtinSchreierPolynomial P b

theorem regularQuadraticArtinSchreierDefiningPolynomial_monic
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    (regularQuadraticArtinSchreierDefiningPolynomial P b hirr).Monic := by
  simpa only [regularQuadraticArtinSchreierDefiningPolynomial] using
    regularQuadraticArtinSchreierPolynomial_monic P b

/-- The actual quadratic field defined by a regular irreducible
Artin--Schreier polynomial. -/
abbrev RegularQuadraticArtinSchreierField
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :=
  AdjoinRoot (regularQuadraticArtinSchreierDefiningPolynomial P b hirr)

noncomputable instance regularQuadraticArtinSchreierPolynomialIrreducibleFact
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    Fact (Irreducible
      (regularQuadraticArtinSchreierDefiningPolynomial P b hirr)) :=
  ⟨by
    simpa only [regularQuadraticArtinSchreierDefiningPolynomial] using hirr⟩

noncomputable instance regularQuadraticArtinSchreierConstantScalarTower
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    IsScalarTower F256 K (RegularQuadraticArtinSchreierField P b hirr) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The literal embedding into the regular quadratic field. -/
noncomputable def regularQuadraticArtinSchreierEmbedding
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    K →ₐ[F256] RegularQuadraticArtinSchreierField P b hirr :=
  (Algebra.ofId K (RegularQuadraticArtinSchreierField P b hirr)).restrictScalars F256

/-- The integral Artin--Schreier root. -/
noncomputable def regularQuadraticArtinSchreierRoot
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    RegularQuadraticArtinSchreierField P b hirr :=
  AdjoinRoot.root (regularQuadraticArtinSchreierDefiningPolynomial P b hirr)

/-- The constructed root satisfies the literal regular Artin--Schreier
equation. -/
theorem regularQuadraticArtinSchreierRoot_equation
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    regularQuadraticArtinSchreierRoot P b hirr ^ 2 +
        regularQuadraticArtinSchreierRoot P b hirr =
      regularQuadraticArtinSchreierEmbedding P b hirr (b : K) := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP (RegularQuadraticArtinSchreierField P b hirr) 2 :=
    charP_of_injective_algebraMap
      (algebraMap K (RegularQuadraticArtinSchreierField P b hirr)).injective 2
  have hroot := AdjoinRoot.eval₂_root
    (regularQuadraticArtinSchreierDefiningPolynomial P b hirr)
  have hpoly : regularQuadraticArtinSchreierDefiningPolynomial P b hirr =
      X ^ 2 + X + C (b : K) := by
    rw [regularQuadraticArtinSchreierDefiningPolynomial,
      regularQuadraticArtinSchreierPolynomial_eq_explicit]
  have hpolyEval := congrArg
    (eval₂
      (AdjoinRoot.of
        (regularQuadraticArtinSchreierDefiningPolynomial P b hirr))
      (AdjoinRoot.root
        (regularQuadraticArtinSchreierDefiningPolynomial P b hirr))) hpoly
  have hexplicit :
      eval₂
          (AdjoinRoot.of
            (regularQuadraticArtinSchreierDefiningPolynomial P b hirr))
          (AdjoinRoot.root
            (regularQuadraticArtinSchreierDefiningPolynomial P b hirr))
          (X ^ 2 + X + C (b : K)) = 0 :=
    hpolyEval.symm.trans hroot
  rw [eval₂_add, eval₂_add, eval₂_X_pow, eval₂_X, eval₂_C] at hexplicit
  change AdjoinRoot.root
        (regularQuadraticArtinSchreierDefiningPolynomial P b hirr) ^ 2 +
      AdjoinRoot.root
        (regularQuadraticArtinSchreierDefiningPolynomial P b hirr) =
    AdjoinRoot.of
      (regularQuadraticArtinSchreierDefiningPolynomial P b hirr) (b : K)
  have htwo : (2 : RegularQuadraticArtinSchreierField P b hirr) = 0 :=
    CharP.cast_eq_zero (RegularQuadraticArtinSchreierField P b hirr) 2
  linear_combination hexplicit -
    AdjoinRoot.of
      (regularQuadraticArtinSchreierDefiningPolynomial P b hirr) (b : K) * htwo

/-- The regular Artin--Schreier step has degree two. -/
theorem regularQuadraticArtinSchreier_finrank
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    Module.finrank K (RegularQuadraticArtinSchreierField P b hirr) = 2 := by
  calc
    Module.finrank K (RegularQuadraticArtinSchreierField P b hirr) =
        (AdjoinRoot.powerBasis
          (regularQuadraticArtinSchreierDefiningPolynomial_monic
            P b hirr).ne_zero).dim :=
      PowerBasis.finrank _
    _ = (regularQuadraticArtinSchreierDefiningPolynomial P b hirr).natDegree := rfl
    _ = 2 := by
      simpa only [regularQuadraticArtinSchreierDefiningPolynomial] using
        regularQuadraticArtinSchreierPolynomial_natDegree P b

noncomputable instance regularQuadraticArtinSchreierFiniteDimensional
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    FiniteDimensional K (RegularQuadraticArtinSchreierField P b hirr) :=
  (AdjoinRoot.powerBasis
    (regularQuadraticArtinSchreierDefiningPolynomial_monic
      P b hirr).ne_zero).finite

noncomputable instance regularQuadraticArtinSchreier_isSeparable
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    Algebra.IsSeparable K (RegularQuadraticArtinSchreierField P b hirr) := by
  let y := regularQuadraticArtinSchreierRoot P b hirr
  have hysep : IsSeparable K y := by
    dsimp [y, regularQuadraticArtinSchreierRoot]
    rw [IsSeparable, AdjoinRoot.minpoly_root
      (regularQuadraticArtinSchreierDefiningPolynomial_monic P b hirr).ne_zero,
      (regularQuadraticArtinSchreierDefiningPolynomial_monic P b hirr).leadingCoeff,
      inv_one, C.map_one, mul_one]
    simpa only [regularQuadraticArtinSchreierDefiningPolynomial] using
      regularQuadraticArtinSchreierPolynomial_separable P b hirr
  letI : Algebra.IsSeparable K
      (IntermediateField.adjoin K
        ({y} : Set (RegularQuadraticArtinSchreierField P b hirr))) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
      (F := K) (E := RegularQuadraticArtinSchreierField P b hirr)
      (x := y)).mpr hysep
  have hAlgebraAdjoin : Algebra.adjoin K
      ({y} : Set (RegularQuadraticArtinSchreierField P b hirr)) = ⊤ := by
    have hport := (AdjoinRoot.powerBasis
      (regularQuadraticArtinSchreierDefiningPolynomial_monic
        P b hirr).ne_zero).adjoin_gen_eq_top
    simp only [y, regularQuadraticArtinSchreierRoot,
      AdjoinRoot.powerBasis_gen] at hport ⊢
    exact hport
  have hadjoin : IntermediateField.adjoin K
      ({y} : Set (RegularQuadraticArtinSchreierField P b hirr)) = ⊤ := by
    apply top_unique
    intro z _
    exact (IntermediateField.algebra_adjoin_le_adjoin K
      ({y} : Set (RegularQuadraticArtinSchreierField P b hirr))) (by
        rw [hAlgebraAdjoin]
        exact Set.mem_univ z)
  refine ⟨fun z => IntermediateField.isSeparable_of_mem_isSeparable
    (F := K) (E := RegularQuadraticArtinSchreierField P b hirr)
    (L := IntermediateField.adjoin K
      ({y} : Set (RegularQuadraticArtinSchreierField P b hirr))) ?_⟩
  rw [hadjoin]
  exact Set.mem_univ z

instance regularQuadraticArtinSchreierValuationRingScalarTower
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    IsScalarTower P.valuationRing K
      (RegularQuadraticArtinSchreierField P b hirr) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The integral closure of the lower valuation ring in the regular
quadratic field. -/
abbrev RegularQuadraticArtinSchreierIntegralClosure
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :=
  integralClosure P.valuationRing
    (RegularQuadraticArtinSchreierField P b hirr)

noncomputable instance regularQuadraticArtinSchreierIntegralClosureIsTorsionFree
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    Module.IsTorsionFree P.valuationRing
      (RegularQuadraticArtinSchreierIntegralClosure P b hirr) := by
  letI : Module.IsTorsionFree P.valuationRing
      (RegularQuadraticArtinSchreierField P b hirr) :=
    Module.IsTorsionFree.trans_faithfulSMul P.valuationRing K
      (RegularQuadraticArtinSchreierField P b hirr)
  exact IsIntegralClosure.isTorsionFree P.valuationRing
    (RegularQuadraticArtinSchreierField P b hirr)

noncomputable instance regularQuadraticArtinSchreierIntegralClosureFinite
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    Module.Finite P.valuationRing
      (RegularQuadraticArtinSchreierIntegralClosure P b hirr) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite P.valuationRing K
    (RegularQuadraticArtinSchreierField P b hirr)
    (RegularQuadraticArtinSchreierIntegralClosure P b hirr)

noncomputable instance regularQuadraticArtinSchreierIntegralClosureIsFractionRing
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    IsFractionRing (RegularQuadraticArtinSchreierIntegralClosure P b hirr)
      (RegularQuadraticArtinSchreierField P b hirr) :=
  integralClosure.isFractionRing_of_finite_extension K
    (RegularQuadraticArtinSchreierField P b hirr)

noncomputable instance regularQuadraticArtinSchreierIntegralClosureIsDedekindDomain
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    IsDedekindDomain (RegularQuadraticArtinSchreierIntegralClosure P b hirr) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain P.valuationRing K
    (RegularQuadraticArtinSchreierField P b hirr)

/-- The polynomial root as an element of the actual integral closure. -/
noncomputable def regularQuadraticArtinSchreierIntegralRoot
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    RegularQuadraticArtinSchreierIntegralClosure P b hirr := by
  refine ⟨regularQuadraticArtinSchreierRoot P b hirr, ?_⟩
  refine ⟨regularQuadraticArtinSchreierIntegralPolynomial P b,
    regularQuadraticArtinSchreierIntegralPolynomial_monic P b, ?_⟩
  change eval₂
      ((AdjoinRoot.of
        (regularQuadraticArtinSchreierDefiningPolynomial P b hirr)).comp
        (algebraMap P.valuationRing K))
      (regularQuadraticArtinSchreierRoot P b hirr)
      (regularQuadraticArtinSchreierIntegralPolynomial P b) = 0
  rw [← eval₂_map]
  exact AdjoinRoot.eval₂_root
    (regularQuadraticArtinSchreierDefiningPolynomial P b hirr)

@[simp]
theorem coe_regularQuadraticArtinSchreierIntegralRoot
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    (regularQuadraticArtinSchreierIntegralRoot P b hirr :
        RegularQuadraticArtinSchreierField P b hirr) =
      regularQuadraticArtinSchreierRoot P b hirr :=
  rfl

private theorem regularQuadraticArtinSchreierIntegralPolynomial_aeval_root
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    Polynomial.aeval (regularQuadraticArtinSchreierRoot P b hirr)
        (regularQuadraticArtinSchreierIntegralPolynomial P b) = 0 := by
  rw [Polynomial.aeval_def]
  change eval₂
      ((AdjoinRoot.of
        (regularQuadraticArtinSchreierDefiningPolynomial P b hirr)).comp
        (algebraMap P.valuationRing K))
      (regularQuadraticArtinSchreierRoot P b hirr)
      (regularQuadraticArtinSchreierIntegralPolynomial P b) = 0
  rw [← eval₂_map]
  exact AdjoinRoot.eval₂_root
    (regularQuadraticArtinSchreierDefiningPolynomial P b hirr)

private theorem regularQuadraticArtinSchreier_minpoly_root
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    minpoly P.valuationRing (regularQuadraticArtinSchreierRoot P b hirr) =
      regularQuadraticArtinSchreierIntegralPolynomial P b := by
  symm
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  letI : Module.IsTorsionFree P.valuationRing
      (RegularQuadraticArtinSchreierField P b hirr) :=
    Module.IsTorsionFree.trans_faithfulSMul P.valuationRing K
      (RegularQuadraticArtinSchreierField P b hirr)
  have hy_integral : IsIntegral P.valuationRing
      (regularQuadraticArtinSchreierRoot P b hirr) := by
    exact (regularQuadraticArtinSchreierIntegralRoot P b hirr).property
  have hmin_K : minpoly K (regularQuadraticArtinSchreierRoot P b hirr) =
      regularQuadraticArtinSchreierPolynomial P b := by
    have hport := AdjoinRoot.minpoly_powerBasis_gen_of_monic
      (regularQuadraticArtinSchreierDefiningPolynomial_monic P b hirr)
    simp only [regularQuadraticArtinSchreierRoot,
      regularQuadraticArtinSchreierDefiningPolynomial,
      AdjoinRoot.powerBasis_gen] at hport ⊢
    exact hport
  have hmin_natDegree :
      (minpoly P.valuationRing
        (regularQuadraticArtinSchreierRoot P b hirr)).natDegree = 2 := by
    calc
      (minpoly P.valuationRing
          (regularQuadraticArtinSchreierRoot P b hirr)).natDegree =
          ((minpoly P.valuationRing
            (regularQuadraticArtinSchreierRoot P b hirr)).map
              (algebraMap P.valuationRing K)).natDegree :=
        ((minpoly.monic hy_integral).natDegree_map _).symm
      _ = (minpoly K
          (regularQuadraticArtinSchreierRoot P b hirr)).natDegree := by
        rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hy_integral]
      _ = (regularQuadraticArtinSchreierPolynomial P b).natDegree := by
        rw [hmin_K]
      _ = 2 := regularQuadraticArtinSchreierPolynomial_natDegree P b
  apply minpoly.IsIntegrallyClosed.unique_of_degree_le_degree_minpoly
  · exact regularQuadraticArtinSchreierIntegralPolynomial_monic P b
  · exact regularQuadraticArtinSchreierIntegralPolynomial_aeval_root
      P b hirr
  · rw [degree_eq_natDegree
        (regularQuadraticArtinSchreierIntegralPolynomial_monic P b).ne_zero,
      degree_eq_natDegree (minpoly.ne_zero hy_integral),
      regularQuadraticArtinSchreierIntegralPolynomial_natDegree,
      hmin_natDegree]

private theorem regularQuadraticArtinSchreier_minpoly_integralRoot
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    minpoly P.valuationRing
        (regularQuadraticArtinSchreierIntegralRoot P b hirr) =
      regularQuadraticArtinSchreierIntegralPolynomial P b := by
  calc
    minpoly P.valuationRing
        (regularQuadraticArtinSchreierIntegralRoot P b hirr) =
        minpoly P.valuationRing
          (algebraMap
            (RegularQuadraticArtinSchreierIntegralClosure P b hirr)
            (RegularQuadraticArtinSchreierField P b hirr)
            (regularQuadraticArtinSchreierIntegralRoot P b hirr)) :=
      (minpoly.algebraMap_eq
        (IsFractionRing.injective
          (RegularQuadraticArtinSchreierIntegralClosure P b hirr)
          (RegularQuadraticArtinSchreierField P b hirr))
        (regularQuadraticArtinSchreierIntegralRoot P b hirr)).symm
    _ = minpoly P.valuationRing
        (regularQuadraticArtinSchreierRoot P b hirr) := by
      congr 1
    _ = regularQuadraticArtinSchreierIntegralPolynomial P b :=
      regularQuadraticArtinSchreier_minpoly_root P b hirr

theorem regularQuadraticArtinSchreier_aeval_derivative_minpoly
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    Polynomial.aeval (regularQuadraticArtinSchreierIntegralRoot P b hirr)
        (derivative (minpoly P.valuationRing
          (regularQuadraticArtinSchreierIntegralRoot P b hirr))) = 1 := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP P.valuationRing 2 :=
    P.valuationRing.subtype.charP P.valuationRing.subtype_injective 2
  have hderivative :
      derivative (minpoly P.valuationRing
        (regularQuadraticArtinSchreierIntegralRoot P b hirr)) = 1 := by
    rw [regularQuadraticArtinSchreier_minpoly_integralRoot,
      regularQuadraticArtinSchreierIntegralPolynomial]
    simp only [derivative_add, derivative_X_pow, derivative_X, derivative_C]
    reduce_mod_char!
    norm_num
  rw [hderivative]
  simp

/-- The different of a regular irreducible quadratic Artin--Schreier step is
the unit ideal. -/
theorem regularQuadraticArtinSchreierDifferentIdeal_eq_top
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    differentIdeal P.valuationRing
        (RegularQuadraticArtinSchreierIntegralClosure P b hirr) = ⊤ := by
  let O := P.valuationRing
  let C := RegularQuadraticArtinSchreierIntegralClosure P b hirr
  let L := RegularQuadraticArtinSchreierField P b hirr
  let y : C := regularQuadraticArtinSchreierIntegralRoot P b hirr
  have hfieldAdjoin : Algebra.adjoin K
      ({algebraMap C L y} : Set L) = ⊤ := by
    have hport := (AdjoinRoot.powerBasis
      (regularQuadraticArtinSchreierDefiningPolynomial_monic
        P b hirr).ne_zero).adjoin_gen_eq_top
    simp only [C, L, y, coe_regularQuadraticArtinSchreierIntegralRoot,
      regularQuadraticArtinSchreierRoot, AdjoinRoot.powerBasis_gen] at hport ⊢
    exact hport
  have hmem := aeval_derivative_mem_differentIdeal O K L y hfieldAdjoin
  rw [regularQuadraticArtinSchreier_aeval_derivative_minpoly] at hmem
  exact (differentIdeal O C).eq_top_iff_one.mpr hmem

private theorem exists_regularQuadraticArtinSchreierUpperIdeal
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    ∃ Q : Ideal (RegularQuadraticArtinSchreierIntegralClosure P b hirr),
      Q.IsMaximal ∧
        Q.LiesOver (IsLocalRing.maximalIdeal P.valuationRing) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := RegularQuadraticArtinSchreierIntegralClosure P b hirr)
    (IsLocalRing.maximalIdeal P.valuationRing)

/-- A concrete upper prime of the regular quadratic step. -/
noncomputable def regularQuadraticArtinSchreierUpperIdeal
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    Ideal (RegularQuadraticArtinSchreierIntegralClosure P b hirr) :=
  Classical.choose (exists_regularQuadraticArtinSchreierUpperIdeal P b hirr)

private theorem regularQuadraticArtinSchreierUpperIdeal_isMaximal
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    (regularQuadraticArtinSchreierUpperIdeal P b hirr).IsMaximal :=
  (Classical.choose_spec
    (exists_regularQuadraticArtinSchreierUpperIdeal P b hirr)).1

theorem regularQuadraticArtinSchreierUpperIdeal_liesOver
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    (regularQuadraticArtinSchreierUpperIdeal P b hirr).LiesOver
      (IsLocalRing.maximalIdeal P.valuationRing) :=
  (Classical.choose_spec
    (exists_regularQuadraticArtinSchreierUpperIdeal P b hirr)).2

/-- The chosen upper prime as a height-one prime. -/
noncomputable def regularQuadraticArtinSchreierUpperHeightOne
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    IsDedekindDomain.HeightOneSpectrum
      (RegularQuadraticArtinSchreierIntegralClosure P b hirr) :=
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  letI : (regularQuadraticArtinSchreierUpperIdeal P b hirr).LiesOver
      (IsLocalRing.maximalIdeal P.valuationRing) :=
    regularQuadraticArtinSchreierUpperIdeal_liesOver P b hirr
  { asIdeal := regularQuadraticArtinSchreierUpperIdeal P b hirr
    isPrime :=
      (regularQuadraticArtinSchreierUpperIdeal_isMaximal P b hirr).isPrime
    ne_bot := Ideal.ne_bot_of_liesOver_of_ne_bot
      (IsDiscreteValuationRing.not_a_field P.valuationRing)
      (regularQuadraticArtinSchreierUpperIdeal P b hirr) }

/-- The normalized upper place of the regular quadratic step. -/
noncomputable def regularQuadraticArtinSchreierAbovePlace
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    GlobalPlace F256 (RegularQuadraticArtinSchreierField P b hirr) where
  valuation := (regularQuadraticArtinSchreierUpperHeightOne P b hirr).valuation
    (RegularQuadraticArtinSchreierField P b hirr)
  normalized :=
    (regularQuadraticArtinSchreierUpperHeightOne P b hirr).valuation_surjective
      (RegularQuadraticArtinSchreierField P b hirr)

/-- Every chosen upper prime has relative different exponent zero. -/
theorem regularQuadraticArtinSchreierDifferentIdeal_multiplicity_eq_zero
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    multiplicity (regularQuadraticArtinSchreierUpperIdeal P b hirr)
        (differentIdeal P.valuationRing
          (RegularQuadraticArtinSchreierIntegralClosure P b hirr)) = 0 := by
  rw [regularQuadraticArtinSchreierDifferentIdeal_eq_top]
  apply multiplicity_eq_zero.mpr
  rw [Ideal.dvd_iff_le]
  intro htop
  exact (regularQuadraticArtinSchreierUpperIdeal_isMaximal P b hirr).ne_top
    (top_unique htop)

/-- Every chosen upper prime has ramification index one. -/
theorem regularQuadraticArtinSchreier_ramificationIdx_eq_one
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    (IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx'
      (regularQuadraticArtinSchreierUpperIdeal P b hirr) = 1 := by
  let O := P.valuationRing
  let C := RegularQuadraticArtinSchreierIntegralClosure P b hirr
  let L := RegularQuadraticArtinSchreierField P b hirr
  let Q : Ideal C := regularQuadraticArtinSchreierUpperIdeal P b hirr
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  letI : Algebra (FractionRing O) (FractionRing C) :=
    FractionRing.liftAlgebra _ _
  letI : Algebra.IsSeparable (FractionRing O) (FractionRing C) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv O K).symm.toRingEquiv
      (FractionRing.algEquiv C L).symm.toRingEquiv ?_
    ext x
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv O K).symm
      (FractionRing.algEquiv C L).symm x
  letI : Q.IsPrime :=
    (regularQuadraticArtinSchreierUpperIdeal_isMaximal P b hirr).isPrime
  have hQ_ne_bot : Q ≠ ⊥ :=
    (regularQuadraticArtinSchreierUpperHeightOne P b hirr).ne_bot
  have hQ_ne_top : Q ≠ ⊤ :=
    (regularQuadraticArtinSchreierUpperIdeal_isMaximal P b hirr).ne_top
  have hnotdvd : ¬ Q ∣ differentIdeal O C := by
    rw [regularQuadraticArtinSchreierDifferentIdeal_eq_top]
    intro hdvd
    apply hQ_ne_top
    exact top_unique (Ideal.dvd_iff_le.mp hdvd)
  have hunramified : Algebra.IsUnramifiedAt O Q :=
    (not_dvd_differentIdeal_iff (A := O) (B := C)).mp hnotdvd
  letI : Algebra.IsUnramifiedAt O Q := hunramified
  letI : Q.LiesOver (IsLocalRing.maximalIdeal O) :=
    regularQuadraticArtinSchreierUpperIdeal_liesOver P b hirr
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (IsLocalRing.maximalIdeal O)
    Q (IsDiscreteValuationRing.not_a_field O)]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := O) (p := Q)

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
