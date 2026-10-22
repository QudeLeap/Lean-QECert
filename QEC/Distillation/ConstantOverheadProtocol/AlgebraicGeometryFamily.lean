/-
Copyright (c) 2026 The Lean-QEC authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EnjiXiong
-/

import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Data.Fin.Rev
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Unramified.Dedekind
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.LocalSubring
import QEC.Coding.AlgebraicGeometry.Towers.ArtinSchreier
import QEC.Coding.AlgebraicGeometry.Codes.Evaluation
import QEC.Coding.AlgebraicGeometry.Codes.CodeDuality
import QEC.Coding.AlgebraicGeometry.Places.AffinePlaceDegree
import QEC.Coding.AlgebraicGeometry.Differentials.Differential
import QEC.Coding.AlgebraicGeometry.Differentials.DifferentialLocal
import QEC.Coding.AlgebraicGeometry.Places.FullConstantField
import QEC.Coding.AlgebraicGeometry.Towers.GarciaStichtenothParameters
import QEC.Coding.AlgebraicGeometry.Residues.Inverse.FibreDirectFactor
import QEC.Coding.AlgebraicGeometry.Places.InverseInfinityFibre
import QEC.Coding.AlgebraicGeometry.Residues.Local.ResidueProduct
import QEC.Coding.AlgebraicGeometry.Places.RationalPlace
import QEC.Coding.AlgebraicGeometry.Differentials.RatFuncDifferentialOrder
import QEC.Coding.AlgebraicGeometry.RiemannRoch.PolarDegree
import QEC.Coding.AlgebraicGeometry.RiemannRoch.Theorem
import QEC.Coding.QuditQubitConversion.FiniteField
import QEC.Distillation.ConstantOverheadProtocol.WeightedTriorthogonalCSS

/-!
# Concrete field facts for the WHY24 algebraic-geometry family

WHY24 `main.tex:1976-2002` fixes the Garcia--Stichtenoth recursion at
`l = 32`, beginning with `F₁ = F1024(x₁)` and
`z₂^32 + z₂ = x₁^33`.  The first non-rational field is constructed below as
an actual `AdjoinRoot`, not as a tower witness: its irreducibility follows by
viewing the relation bivariately, swapping the variables, and applying
Eisenstein at the prime `(x₁)` to
`x₁^33 - (z₂^32 + z₂)`.

WHY24 `main.tex:1695-1707` also scales the selected AG evaluation code by
seventh roots of nonzero residue weights.  For the source-selected field
`F1024`, this is a theorem about its actual multiplicative group: the group
has order `1023`, which is coprime to `7`, so the seventh-power map is
bijective.

The remaining fixed tower levels, places, divisors, different, and code
construction must be derived from these concrete objects; none is supplied
as a record field or an assumed conclusion here.
-/

namespace QEC.Distillation.Why24AGFamily

open QEC.Coding
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
open scoped Polynomial.Bivariate WithZero
open Polynomial

noncomputable section

local instance f1024CharTwo : CharP F1024 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F1024).injective 2

/-- The source's base function field `F₁ = F1024(x₁)`. -/
noncomputable abbrev F1024TowerF1 : Type := RatFunc F1024

/-- The first Garcia--Stichtenoth relation as a polynomial in `z₂` over the
actual rational function field `F₁`. -/
noncomputable def f1024FirstStepPolynomial : F1024TowerF1[X] :=
  X ^ 32 + X - C (RatFunc.X ^ 33)

/-- The source-orientation bivariate relation
`z₂^32 + z₂ - x₁^33`.  Mapping its inner coefficients to the rational
function field is exactly `f1024FirstStepPolynomial`. -/
private noncomputable def f1024FirstStepBivariate : F1024[X][Y] :=
  Y ^ 32 + Y - C ((X : F1024[X]) ^ 33)

/-- After swapping `x₁` and `z₂`, the same affine curve has the Eisenstein
orientation `x₁^33 - (z₂^32 + z₂)` at the principal prime `(z₂)`. -/
private noncomputable def f1024FirstStepEisensteinPolynomial : F1024[X][Y] :=
  Y ^ 33 - C ((X : F1024[X]) ^ 32 + X)

private theorem f1024FirstStepEisenstein_monic :
    f1024FirstStepEisensteinPolynomial.Monic := by
  rw [f1024FirstStepEisensteinPolynomial]
  exact monic_X_pow_sub_C _ (by norm_num)

private theorem f1024FirstStepEisenstein_irreducible :
    Irreducible f1024FirstStepEisensteinPolynomial := by
  let P : Ideal F1024[X] := Ideal.span ({X} : Set F1024[X])
  have hPprime : P.IsPrime := by
    dsimp [P]
    exact (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X
  have hcoeff : ∀ {n : ℕ}, n < f1024FirstStepEisensteinPolynomial.natDegree →
      f1024FirstStepEisensteinPolynomial.coeff n ∈ P := by
    intro n hn
    have hnlt : n < 33 := by
      change n < (Y ^ 33 - C ((X : F1024[X]) ^ 32 + X)).natDegree at hn
      simpa only [natDegree_X_pow_sub_C] using hn
    by_cases hn0 : n = 0
    · subst n
      have hzero : f1024FirstStepEisensteinPolynomial.coeff 0 =
          -((X : F1024[X]) ^ 32 + X) := by
        rw [f1024FirstStepEisensteinPolynomial, coeff_sub, coeff_X_pow,
          if_neg (by norm_num), coeff_C_zero, zero_sub]
      rw [hzero]
      rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
      simp [coeff_neg, coeff_add, coeff_X_pow]
    · have hn33 : n ≠ 33 := Nat.ne_of_lt hnlt
      have hzero : f1024FirstStepEisensteinPolynomial.coeff n = 0 := by
        rw [f1024FirstStepEisensteinPolynomial, coeff_sub, coeff_X_pow,
          if_neg hn33, coeff_C, if_neg hn0, sub_zero]
      rw [hzero]
      exact P.zero_mem
  have hconstant : f1024FirstStepEisensteinPolynomial.coeff 0 ∉ P ^ 2 := by
    dsimp [P]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdiv
    have hcoeff := (Polynomial.X_pow_dvd_iff.mp hdiv) 1 (by norm_num)
    have hzero : f1024FirstStepEisensteinPolynomial.coeff 0 =
        -((X : F1024[X]) ^ 32 + X) := by
      rw [f1024FirstStepEisensteinPolynomial, coeff_sub, coeff_X_pow,
        if_neg (by norm_num), coeff_C_zero, zero_sub]
    rw [hzero] at hcoeff
    norm_num [coeff_neg, coeff_add, coeff_X_pow, coeff_X] at hcoeff
  have hEisenstein : f1024FirstStepEisensteinPolynomial.IsEisensteinAt P :=
    f1024FirstStepEisenstein_monic.isEisensteinAt_of_mem_of_notMem hPprime.ne_top hcoeff hconstant
  exact hEisenstein.irreducible hPprime f1024FirstStepEisenstein_monic.isPrimitive
    (by
      change 0 < (Y ^ 33 - C ((X : F1024[X]) ^ 32 + X)).natDegree
      rw [natDegree_X_pow_sub_C]
      norm_num)

private theorem f1024FirstStepBivariate_swap :
    Polynomial.Bivariate.swap f1024FirstStepBivariate =
      -f1024FirstStepEisensteinPolynomial := by
  simp [f1024FirstStepBivariate, f1024FirstStepEisensteinPolynomial,
    Polynomial.Bivariate.swap_C, Polynomial.Bivariate.swap_Y]

private theorem f1024FirstStepBivariate_irreducible :
    Irreducible f1024FirstStepBivariate := by
  have hneg : Irreducible (-f1024FirstStepEisensteinPolynomial) := by
    rw [show -f1024FirstStepEisensteinPolynomial =
      (-1) * f1024FirstStepEisensteinPolynomial by ring]
    exact (irreducible_isUnit_mul (y := f1024FirstStepEisensteinPolynomial)
      (by exact isUnit_neg_one (α := F1024[X][Y]))).mpr
      f1024FirstStepEisenstein_irreducible
  have hswap : Irreducible (Polynomial.Bivariate.swap f1024FirstStepBivariate) := by
    simpa only [f1024FirstStepBivariate_swap] using hneg
  exact (MulEquiv.irreducible_iff (Polynomial.Bivariate.swap (R := F1024))
    (x := f1024FirstStepBivariate)).mp hswap

private theorem f1024FirstStepBivariate_monic : f1024FirstStepBivariate.Monic := by
  rw [f1024FirstStepBivariate]
  rw [show (Y ^ 32 + Y - C ((X : F1024[X]) ^ 33) : F1024[X][Y]) =
    Y ^ 32 - (C ((X : F1024[X]) ^ 33) - Y) by ring]
  exact monic_X_pow_sub (p := C ((X : F1024[X]) ^ 33) - Y) (show
      degree (C ((X : F1024[X]) ^ 33) - Y) < (32 : ℕ) by
        calc
          degree (C ((X : F1024[X]) ^ 33) - Y) ≤
              max (degree (C ((X : F1024[X]) ^ 33))) (degree Y) := degree_sub_le _ _
          _ ≤ 1 := by
            exact max_le (degree_C_le.trans (by norm_num)) (by simp)
          _ < (32 : ℕ) := by norm_num)

private theorem f1024FirstStepBivariate_map :
    f1024FirstStepBivariate.map (algebraMap F1024[X] F1024TowerF1) =
      f1024FirstStepPolynomial := by
  simp [f1024FirstStepBivariate, f1024FirstStepPolynomial, RatFunc.algebraMap_X]

private theorem f1024FirstStepPolynomial_monic : f1024FirstStepPolynomial.Monic := by
  rw [← f1024FirstStepBivariate_map]
  exact f1024FirstStepBivariate_monic.map _

private theorem f1024FirstStepPolynomial_natDegree :
    f1024FirstStepPolynomial.natDegree = 32 := by
  change (X ^ 32 + X - C (RatFunc.X ^ 33) : F1024TowerF1[X]).natDegree = 32
  calc
    (X ^ 32 + X - C (RatFunc.X ^ 33) : F1024TowerF1[X]).natDegree =
        (X ^ 32 + X : F1024TowerF1[X]).natDegree := natDegree_sub_C
    _ = (X ^ 32 : F1024TowerF1[X]).natDegree :=
      natDegree_add_eq_left_of_natDegree_lt (by norm_num)
    _ = 32 := natDegree_X_pow 32

/-- The actual first Garcia--Stichtenoth polynomial over `F1024(x₁)` is
irreducible.  The proof is source-specific: it is the bivariate Eisenstein
argument for the displayed `z₂^32 + z₂ = x₁^33` relation, followed by
Gauss's lemma for `F1024[x₁] ⊂ F1024(x₁)`. -/
theorem f1024_firstStep_irreducible : Irreducible f1024FirstStepPolynomial := by
  have hmapped : Irreducible
      (f1024FirstStepBivariate.map (algebraMap F1024[X] F1024TowerF1)) :=
    (f1024FirstStepBivariate_monic.irreducible_iff_irreducible_map_fraction_map).mp
      f1024FirstStepBivariate_irreducible
  simpa only [f1024FirstStepBivariate_map] using hmapped

/-- The first non-rational field in the fixed tower. -/
noncomputable abbrev F1024TowerF2 : Type := AdjoinRoot f1024FirstStepPolynomial

noncomputable instance f1024FirstStepIrreducibleFact :
    Fact (Irreducible f1024FirstStepPolynomial) :=
  ⟨f1024_firstStep_irreducible⟩

local instance f1024TowerF2CharTwo : CharP F1024TowerF2 2 :=
  charP_of_injective_algebraMap
    (algebraMap F1024TowerF1 F1024TowerF2).injective 2

noncomputable instance f1024TowerF2FiniteDimensional :
    FiniteDimensional F1024TowerF1 F1024TowerF2 :=
  (AdjoinRoot.powerBasis' f1024FirstStepPolynomial_monic).basis.finiteDimensional_of_finite

/-- The concrete first extension has the source-required degree `32`. -/
theorem f1024TowerF2_finrank : Module.finrank F1024TowerF1 F1024TowerF2 = 32 := by
  simpa [F1024TowerF2, f1024FirstStepPolynomial_natDegree] using
    (AdjoinRoot.powerBasis' f1024FirstStepPolynomial_monic).finrank

noncomputable instance f1024TowerF2Separable :
    Algebra.IsSeparable F1024TowerF1 F1024TowerF2 := by
  rw [← AlgEquiv.Algebra.isSeparable_iff <|
    (IntermediateField.equivOfEq
      (IntermediateField.adjoin_root_eq_top f1024FirstStepPolynomial)).trans
        IntermediateField.topEquiv,
    IntermediateField.isSeparable_adjoin_simple_iff_isSeparable,
    IsSeparable, AdjoinRoot.minpoly_root f1024FirstStepPolynomial_monic.ne_zero,
    f1024FirstStepPolynomial_monic.leadingCoeff, inv_one, C.map_one, mul_one]
  simpa only [f1024FirstStepPolynomial,
    QEC.Coding.AlgebraicGeometry.ArtinSchreier.artinSchreierPolynomial] using
    (QEC.Coding.AlgebraicGeometry.ArtinSchreier.artinSchreierPolynomial_separable
      (F := F1024TowerF1) (RatFunc.X ^ 33))

noncomputable instance f1024TowerF2FunctionField : _root_.FunctionField F1024 F1024TowerF2 :=
  f1024TowerF2FiniteDimensional

/-- The quotient's canonical affine-coordinate action and the root-extension
action form the concrete direct tower `F1024[x₁] ⊂ F1024(x₁) ⊂ F₂`.  This is
the source's direct chart, not the transported inverse chart used to study
places at infinity. -/
noncomputable instance f1024TowerF2PolynomialRatFuncTower :
    IsScalarTower F1024[X] F1024TowerF1 F1024TowerF2 :=
  by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl

/-- Lying-over constructs an actual nonempty inverse-chart fibre above `(X)`
for the first fixed tower field.  The fibre is deliberately left unchosen:
this theorem neither identifies a unique source infinity place nor assigns a
residue degree or valuation to one. -/
theorem f1024TowerF2_inverseInfinityFibre_nonempty : Nonempty
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF2)) := by
  exact QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre_nonempty
    (k := F1024) (F := F1024TowerF2)

/-- The concrete generator `z₂` of the first non-rational tower field. -/
noncomputable def f1024TowerZ2 : F1024TowerF2 :=
  AdjoinRoot.root f1024FirstStepPolynomial

/-- The generator satisfies the first source recurrence exactly. -/
theorem f1024TowerZ2_equation : f1024TowerZ2 ^ 32 + f1024TowerZ2 =
    algebraMap F1024TowerF1 F1024TowerF2 (RatFunc.X ^ 33) := by
  rw [AdjoinRoot.algebraMap_eq]
  apply sub_eq_zero.mp
  have hroot := AdjoinRoot.eval₂_root f1024FirstStepPolynomial
  change (X ^ 32 + X - C (RatFunc.X ^ 33) : F1024TowerF1[X]).eval₂
      (AdjoinRoot.of f1024FirstStepPolynomial)
      (AdjoinRoot.root f1024FirstStepPolynomial) = 0 at hroot
  simpa only [f1024TowerZ2, eval₂_sub, eval₂_add,
    eval₂_pow, eval₂_X, eval₂_C] using
    hroot

/-- The source's first rational-function coordinate, embedded in `F₂`. -/
noncomputable def f1024TowerX1 : F1024TowerF2 :=
  algebraMap F1024TowerF1 F1024TowerF2 RatFunc.X

/-- The embedded first coordinate is nonzero, so the source quotient defining
`x₂` is an actual field element. -/
theorem f1024TowerX1_ne_zero : f1024TowerX1 ≠ 0 := by
  rw [f1024TowerX1]
  exact (map_ne_zero_iff (algebraMap F1024TowerF1 F1024TowerF2)
    (algebraMap F1024TowerF1 F1024TowerF2).injective).mpr RatFunc.X_ne_zero

/-- The source's next tower coordinate `x₂ = z₂ / x₁`. -/
noncomputable def f1024TowerX2 : F1024TowerF2 :=
  f1024TowerZ2 / f1024TowerX1

/-- The defining quotient is equivalent to `z₂ = x₁ x₂`. -/
theorem f1024TowerX1_mul_X2 : f1024TowerX1 * f1024TowerX2 = f1024TowerZ2 := by
  calc
    f1024TowerX1 * f1024TowerX2 =
        f1024TowerZ2 / f1024TowerX1 * f1024TowerX1 := by
      rw [f1024TowerX2, mul_comm]
    _ = f1024TowerZ2 := div_mul_cancel₀ _ f1024TowerX1_ne_zero

/-- Clearing the nonzero `x₁` denominator rewrites the first source relation
in the coordinate `x₂`; this is the concrete recurrence needed before a
second extension can be considered. -/
theorem f1024TowerX2_equation : f1024TowerX1 ^ 31 * f1024TowerX2 ^ 32 +
    f1024TowerX2 = f1024TowerX1 ^ 32 := by
  have hz : f1024TowerZ2 ^ 32 + f1024TowerZ2 = f1024TowerX1 ^ 33 := by
    simpa only [f1024TowerX1, map_pow] using f1024TowerZ2_equation
  rw [f1024TowerX2, div_pow]
  field_simp [f1024TowerX1_ne_zero]
  linear_combination hz

/-- The first Artin--Schreier generator is nonzero because its defining
relation has the nonzero right-hand side `x₁^33`. -/
theorem f1024TowerZ2_ne_zero : f1024TowerZ2 ≠ 0 := by
  intro hz
  have hzero : algebraMap F1024TowerF1 F1024TowerF2 (RatFunc.X ^ 33) = 0 := by
    rw [← f1024TowerZ2_equation, hz]
    norm_num
  exact (map_ne_zero_iff (algebraMap F1024TowerF1 F1024TowerF2)
    (algebraMap F1024TowerF1 F1024TowerF2).injective).mpr
      (pow_ne_zero _ RatFunc.X_ne_zero) hzero

/-- The second coordinate is nonzero, so its reciprocal supplies the local
inverse-chart coordinate at the source infinity point. -/
theorem f1024TowerX2_ne_zero : f1024TowerX2 ≠ 0 := by
  rw [f1024TowerX2]
  exact div_ne_zero f1024TowerZ2_ne_zero f1024TowerX1_ne_zero

/-- The inverse-chart base coordinate `t = x₁⁻¹`. -/
noncomputable def f1024TowerT1 : F1024TowerF2 :=
  f1024TowerX1⁻¹

theorem f1024TowerT1_def : f1024TowerT1 = f1024TowerX1⁻¹ := rfl

/-- The inverse-chart first-step coordinate `w = x₂⁻¹`. -/
noncomputable def f1024TowerW2 : F1024TowerF2 :=
  f1024TowerX2⁻¹

theorem f1024TowerW2_def : f1024TowerW2 = f1024TowerX2⁻¹ := rfl

/-- The inverse-chart coordinate is nonzero because it is the reciprocal of
the nonzero source coordinate `x₂`. -/
theorem f1024TowerW2_ne_zero : f1024TowerW2 ≠ 0 := by
  rw [f1024TowerW2_def]
  exact inv_ne_zero f1024TowerX2_ne_zero

/-- In the inverse chart the first tower relation is
`w^32 + t^32 w^31 = t`.  Its monic left-hand side is the source-specific
Eisenstein orientation at the inverse base prime `(t)`. -/
theorem f1024TowerW2_inverse_equation : f1024TowerW2 ^ 32 +
    f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31 = f1024TowerT1 := by
  have htwo : (2 : F1024TowerF2) = 0 :=
    CharP.ofNat_eq_zero' (R := F1024TowerF2) 2 2 (by norm_num)
  have hx2_add_self : f1024TowerX2 + f1024TowerX2 = 0 := by
    rw [← two_mul, htwo, zero_mul]
  have hcleared : f1024TowerX1 ^ 32 + f1024TowerX2 =
      f1024TowerX1 ^ 31 * f1024TowerX2 ^ 32 := by
    calc
      f1024TowerX1 ^ 32 + f1024TowerX2 =
          (f1024TowerX1 ^ 31 * f1024TowerX2 ^ 32 + f1024TowerX2) +
            f1024TowerX2 := by rw [f1024TowerX2_equation]
      _ = f1024TowerX1 ^ 31 * f1024TowerX2 ^ 32 +
          (f1024TowerX2 + f1024TowerX2) := by ring
      _ = f1024TowerX1 ^ 31 * f1024TowerX2 ^ 32 := by
        rw [hx2_add_self, add_zero]
  rw [f1024TowerT1_def, f1024TowerW2_def, inv_pow, inv_pow]
  field_simp [f1024TowerX1_ne_zero, f1024TowerX2_ne_zero]
  simpa [mul_comm] using hcleared

private theorem f1024Tower_exp_lt_exp {a b : ℤ} :
    WithZero.exp a < WithZero.exp b ↔ a < b := by
  simp [WithZero.exp]

/-- The inverse Eisenstein recurrence forces the ramification exponent of
`t = x₁⁻¹` to be divisible by `32`.  This is a valuation calculation over an
actual normalized place: no upper ideal is selected and no total-ramification
claim is stored in the construction. -/
private theorem f1024TowerW2_inverse_valuation_dvd_32
    (ν : Valuation F1024TowerF2 ℤᵐ⁰) (E : ℕ) (hEpos : 0 < E)
    (hνt : ν f1024TowerT1 = WithZero.exp (-(E : ℤ))) : 32 ∣ E := by
  have hw0 : ν f1024TowerW2 ≠ 0 :=
    (Valuation.ne_zero_iff ν).mpr (inv_ne_zero f1024TowerX2_ne_zero)
  let r : ℤ := WithZero.log (ν f1024TowerW2)
  have hνw : ν f1024TowerW2 = WithZero.exp r := by
    dsimp only [r]
    exact (WithZero.exp_log hw0).symm
  have hνw32 : ν (f1024TowerW2 ^ 32) = WithZero.exp ((32 : ℕ) • r) := by
    rw [map_pow, hνw, ← WithZero.exp_nsmul]
  have hνtw : ν (f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) =
      WithZero.exp ((32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r) := by
    rw [map_mul, map_pow, map_pow, hνt, hνw,
      ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add]
  have hνsum : ν (f1024TowerW2 ^ 32 + f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) =
      WithZero.exp (-(E : ℤ)) := by
    rw [f1024TowerW2_inverse_equation, hνt]
  rcases lt_trichotomy (ν (f1024TowerW2 ^ 32))
      (ν (f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31)) with hlt | heq | hgt
  · have hsum : ν (f1024TowerW2 ^ 32 + f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) =
        ν (f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) := by
      rw [Valuation.map_add_eq_of_lt_right ν hlt]
    rw [hsum, hνtw] at hνsum
    have hEq : (32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r = -(E : ℤ) :=
      WithZero.exp_inj.mp hνsum
    have hltExp : (32 : ℕ) • r <
        (32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r := by
      rw [← f1024Tower_exp_lt_exp, ← hνw32, ← hνtw]
      exact hlt
    simp only [nsmul_eq_mul] at hEq hltExp
    omega
  · have hsame : WithZero.exp ((32 : ℕ) • r) =
        WithZero.exp ((32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r) := by
      rw [← hνw32, ← hνtw]
      exact heq
    have hEq : (32 : ℕ) • r = (32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r :=
      WithZero.exp_inj.mp hsame
    have hsumle : ν (f1024TowerW2 ^ 32 + f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) ≤
        ν (f1024TowerW2 ^ 32) :=
      (map_add_le_max ν _ _).trans_eq (by rw [← heq, max_self])
    rw [hνsum, hνw32] at hsumle
    have hsmall : (32 : ℕ) • r < -(E : ℤ) := by
      have hEq' : (32 : ℤ) * r =
          (32 : ℤ) * (-(E : ℤ)) + (31 : ℤ) * r := by
        have hport := hEq
        simp only [nsmul_eq_mul] at hport ⊢
        exact hport
      have hsmall' : (32 : ℤ) * r < -(E : ℤ) := by
        omega
      have hport := hsmall'
      simp only [nsmul_eq_mul] at hport ⊢
      exact hport
    exfalso
    exact (not_lt_of_ge hsumle) (f1024Tower_exp_lt_exp.mpr hsmall)
  · have hsum : ν (f1024TowerW2 ^ 32 + f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) =
        ν (f1024TowerW2 ^ 32) := by
      rw [Valuation.map_add_eq_of_lt_left ν hgt]
    rw [hsum, hνw32] at hνsum
    have hEq : (32 : ℕ) • r = -(E : ℤ) := WithZero.exp_inj.mp hνsum
    have hrneg : r < 0 := by
      rw [nsmul_eq_mul] at hEq
      omega
    refine ⟨(-r).toNat, ?_⟩
    have hnonneg : 0 ≤ -r := by omega
    rw [nsmul_eq_mul] at hEq
    have hEq' : (E : ℤ) = 32 * (-r) := by omega
    have hcast : ((-r).toNat : ℤ) = -r := Int.toNat_of_nonneg hnonneg
    have hEq'' : (E : ℤ) = (32 : ℤ) * ((-r).toNat : ℤ) := by
      rw [hcast]
      exact hEq'
    exact_mod_cast hEq''

/-- Once the inverse base coordinate has order `32`, the fixed recurrence
forces its reciprocal coordinate `w₂` to have order `1`.  This is the local
Newton-polygon calculation for the source's first tower step, expressed only
through its normalized valuation. -/
private theorem f1024TowerW2_inverse_valuation_eq_exp_neg_one
    (ν : Valuation F1024TowerF2 ℤᵐ⁰)
    (hνt : ν f1024TowerT1 = WithZero.exp (-(32 : ℤ))) :
    ν f1024TowerW2 = WithZero.exp (-(1 : ℤ)) := by
  have hw0 : ν f1024TowerW2 ≠ 0 :=
    (Valuation.ne_zero_iff ν).mpr (inv_ne_zero f1024TowerX2_ne_zero)
  let r : ℤ := WithZero.log (ν f1024TowerW2)
  have hνw : ν f1024TowerW2 = WithZero.exp r := by
    dsimp only [r]
    exact (WithZero.exp_log hw0).symm
  have hνw32 : ν (f1024TowerW2 ^ 32) = WithZero.exp ((32 : ℕ) • r) := by
    rw [map_pow, hνw, ← WithZero.exp_nsmul]
  have hνtw : ν (f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) =
      WithZero.exp ((32 : ℕ) • (-(32 : ℤ)) + (31 : ℕ) • r) := by
    rw [map_mul, map_pow, map_pow, hνt, hνw,
      ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add]
  have hνsum : ν (f1024TowerW2 ^ 32 + f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) =
      WithZero.exp (-(32 : ℤ)) := by
    rw [f1024TowerW2_inverse_equation, hνt]
  rcases lt_trichotomy (ν (f1024TowerW2 ^ 32))
      (ν (f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31)) with hlt | heq | hgt
  · have hsum : ν (f1024TowerW2 ^ 32 + f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) =
        ν (f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) := by
      rw [Valuation.map_add_eq_of_lt_right ν hlt]
    rw [hsum, hνtw] at hνsum
    have hEq : (32 : ℕ) • (-(32 : ℤ)) + (31 : ℕ) • r = -(32 : ℤ) :=
      WithZero.exp_inj.mp hνsum
    have hltExp : (32 : ℕ) • r <
        (32 : ℕ) • (-(32 : ℤ)) + (31 : ℕ) • r := by
      rw [← f1024Tower_exp_lt_exp, ← hνw32, ← hνtw]
      exact hlt
    simp only [nsmul_eq_mul] at hEq hltExp
    omega
  · have hsame : WithZero.exp ((32 : ℕ) • r) =
        WithZero.exp ((32 : ℕ) • (-(32 : ℤ)) + (31 : ℕ) • r) := by
      rw [← hνw32, ← hνtw]
      exact heq
    have hEq : (32 : ℕ) • r = (32 : ℕ) • (-(32 : ℤ)) + (31 : ℕ) • r :=
      WithZero.exp_inj.mp hsame
    have hsumle : ν (f1024TowerW2 ^ 32 + f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) ≤
        ν (f1024TowerW2 ^ 32) :=
      (map_add_le_max ν _ _).trans_eq (by rw [← heq, max_self])
    rw [hνsum, hνw32] at hsumle
    have hsmall : (32 : ℕ) • r < -(32 : ℤ) := by
      have hEq' : (32 : ℤ) * r =
          (32 : ℤ) * (-(32 : ℤ)) + (31 : ℤ) * r := by
        have hport := hEq
        simp only [nsmul_eq_mul] at hport ⊢
        exact hport
      have hsmall' : (32 : ℤ) * r < -(32 : ℤ) := by
        omega
      have hport := hsmall'
      simp only [nsmul_eq_mul] at hport ⊢
      exact hport
    exfalso
    exact (not_lt_of_ge hsumle) (f1024Tower_exp_lt_exp.mpr hsmall)
  · have hsum : ν (f1024TowerW2 ^ 32 + f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) =
        ν (f1024TowerW2 ^ 32) := by
      rw [Valuation.map_add_eq_of_lt_left ν hgt]
    rw [hsum, hνw32] at hνsum
    have hEq : (32 : ℕ) • r = -(32 : ℤ) := WithZero.exp_inj.mp hνsum
    have hr : r = -(1 : ℤ) := by
      have hEq' : (32 : ℤ) * r = -(32 : ℤ) := by
        have hport := hEq
        simp only [nsmul_eq_mul] at hport ⊢
        exact hport
      omega
    rw [hνw, hr]

/-- Repackage a normalized valuation under the direct-chart constant algebra.
The inverse chart carries a deliberately separate scalar-map instance, while
the value group and its normalization are the same concrete data. -/
private noncomputable def f1024TowerRepackageRawGlobalPlace
    (A : Algebra F1024 F1024TowerF2) {A₀ : Algebra F1024 F1024TowerF2}
    (P : @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F1024TowerF2 _ _ _ A₀) :
    @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F1024TowerF2 _ _ _ A := by
  exact @QEC.Coding.AlgebraicGeometry.GlobalPlace.mk F1024 F1024TowerF2 _ _ _ A
    (@QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024 F1024TowerF2 _ _ _ A₀ P)
    (@QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized F1024 F1024TowerF2 _ _ _ A₀ P)

/-- The direct-chart constant algebra used by the first tower's packaged
inverse places.  Naming it keeps the direct and transported chart maps
distinct in dependent `GlobalPlace` types. -/
@[reducible] noncomputable def f1024TowerF2DirectConstantAlgebra : Algebra F1024 F1024TowerF2 :=
  QEC.Coding.AlgebraicGeometry.AffinePlace.constantAlgebra F1024 F1024TowerF2

/-- An actual prime over the inverse-chart base prime `(X)`, packaged as its
normalized global place.  No fibre point is chosen: the place remains indexed
by the genuine upper ideal supplied by lying-over. -/
noncomputable def f1024TowerF2InverseInfinityPlace
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF2)) :
    @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F1024TowerF2 _ _ _
      f1024TowerF2DirectConstantAlgebra :=
  f1024TowerRepackageRawGlobalPlace
    f1024TowerF2DirectConstantAlgebra
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.globalPlace
      (k := F1024) (F := F1024TowerF2) P)

/-- The normalized order at a packaged first-tower inverse place.  This
wrapper fixes the direct-chart constant algebra explicitly, so consumers do
not rely on instance inference across the transported inverse chart. -/
noncomputable def f1024TowerF2InverseInfinityOrder
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF2)) (u : F1024TowerF2) : ℤ :=
  @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
    f1024TowerF2DirectConstantAlgebra
    (f1024TowerF2InverseInfinityPlace P) u

/-- At each actual inverse-chart upper ideal, the original coordinate has
order equal to the negative ramification index over `(X)`.  This is the
normalization bridge for the source-specific inverse Eisenstein calculation:
the next step must prove that this concrete index is `32`. -/
theorem f1024TowerF2InverseInfinityPlace_order_x1
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF2)) :
    f1024TowerF2InverseInfinityOrder P f1024TowerX1 =
      -((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal : ℤ) := by
  change @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
      f1024TowerF2DirectConstantAlgebra
      (f1024TowerF2InverseInfinityPlace P) f1024TowerX1 = _
  let oldRationalAlgebra : Algebra F1024TowerF1 F1024TowerF2 := inferInstance
  let oldFunctionField : _root_.FunctionField F1024 F1024TowerF2 := inferInstance
  let oldSeparable : Algebra.IsSeparable F1024TowerF1 F1024TowerF2 := inferInstance
  have htransportX :
      QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialMap
          (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2
          Polynomial.X = f1024TowerT1 := by
    change QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalMap
        (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2 RatFunc.X =
      f1024TowerT1
    rw [show f1024TowerT1 = f1024TowerX1⁻¹ from f1024TowerT1_def]
    change algebraMap F1024TowerF1 F1024TowerF2
        (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024
          RatFunc.X) =
      (algebraMap F1024TowerF1 F1024TowerF2 RatFunc.X)⁻¹
    rw [QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution_X, map_inv₀]
  letI : Algebra F1024TowerF1 F1024TowerF2 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2
  letI : Algebra F1024[X] F1024TowerF2 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2
  letI : @IsScalarTower F1024[X] F1024TowerF1 F1024TowerF2
      RatFunc.instSMulOfFractionRingPolynomial
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2).toSMul
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2).toSMul :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2
  letI : _root_.FunctionField F1024 F1024TowerF2 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField)
      F1024 F1024TowerF2
  letI : Algebra.IsSeparable F1024TowerF1 F1024TowerF2 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
      F1024 F1024TowerF2
  let inverseConstantAlgebra : Algebra F1024 F1024TowerF2 :=
    QEC.Coding.AlgebraicGeometry.AffinePlace.constantAlgebra F1024 F1024TowerF2
  let B : Type _ := _root_.FunctionField.ringOfIntegers F1024 F1024TowerF2
  letI : Module.IsTorsionFree F1024[X] B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective F1024 F1024TowerF2)
  let e := QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2
  let Q := e P
  let x : B := algebraMap F1024[X] B Polynomial.X
  have hx : x ≠ 0 := by
    simpa only [x, map_zero] using
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective F1024 F1024TowerF2).ne
        (Polynomial.X_ne_zero : (Polynomial.X : F1024[X]) ≠ 0)
  have hmap : Ideal.map (algebraMap F1024[X] B)
      (Polynomial.idealX F1024).asIdeal ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot (Polynomial.idealX F1024).ne_bot
  have hspan : Ideal.span ({x} : Set B) =
      Ideal.map (algebraMap F1024[X] B) (Polynomial.idealX F1024).asIdeal := by
    dsimp only [x]
    calc
      Ideal.span ({algebraMap F1024[X] B Polynomial.X} : Set B) =
          Ideal.map (algebraMap F1024[X] B)
            (Ideal.span ({Polynomial.X} : Set F1024[X])) := by
        rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.map (algebraMap F1024[X] B)
          (Polynomial.idealX F1024).asIdeal := by
        rw [Polynomial.idealX_span]
  have horder :
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
        inverseConstantAlgebra
        (QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace F1024 F1024TowerF2
          (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
            F1024 F1024TowerF2 (Polynomial.idealX F1024) Q))
        (algebraMap F1024[X] F1024TowerF2 Polynomial.X) =
        ((Polynomial.idealX F1024).asIdeal.ramificationIdx' (Q : Ideal B) : ℤ) := by
    rw [IsScalarTower.algebraMap_apply F1024[X] B F1024TowerF2]
    change @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
        inverseConstantAlgebra
        (QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace F1024 F1024TowerF2
          (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
            F1024 F1024TowerF2 (Polynomial.idealX F1024) Q))
        (algebraMap B F1024TowerF2 x) = _
    rw [QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace_order_of_integral_eq_multiplicity
      F1024 F1024TowerF2
      (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
        F1024 F1024TowerF2 (Polynomial.idealX F1024) Q) hx,
      QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace_asIdeal,
      hspan]
    exact_mod_cast
      (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hmap
        (Ideal.Factors.isPrime (Polynomial.idealX F1024).asIdeal Q)).symm
  have hQ : (Q : Ideal B) = P.1.asIdeal := by
    dsimp only [Q, e]
    exact QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors_apply_asIdeal
        (oldRationalAlgebra := oldRationalAlgebra)
        (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable)
        F1024 F1024TowerF2 P
  have hplace :
      QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace F1024 F1024TowerF2
          (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
            F1024 F1024TowerF2 (Polynomial.idealX F1024) Q) =
        QEC.Coding.AlgebraicGeometry.InverseAffinePlace.globalPlace
          (oldRationalAlgebra := oldRationalAlgebra)
          (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable)
          F1024 F1024TowerF2 P :=
    QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.directFactorGlobalPlace_infinityFibreEquiv
          (oldRationalAlgebra := oldRationalAlgebra)
          (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable)
          F1024 F1024TowerF2 P
  have hplace_order (u : F1024TowerF2) :
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
          f1024TowerF2DirectConstantAlgebra
          (f1024TowerF2InverseInfinityPlace P) u =
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
          inverseConstantAlgebra
          (QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace F1024 F1024TowerF2
            (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
              F1024 F1024TowerF2 (Polynomial.idealX F1024) Q)) u := by
    change -WithZero.log
        ((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.globalPlace
          (oldRationalAlgebra := oldRationalAlgebra)
          (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable)
          F1024 F1024TowerF2 P).valuation u) =
      -WithZero.log
        ((QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace F1024 F1024TowerF2
          (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
            F1024 F1024TowerF2 (Polynomial.idealX F1024) Q)).valuation u)
    rw [← congrArg (fun V => V.valuation) hplace]
  calc
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
        f1024TowerF2DirectConstantAlgebra
        (f1024TowerF2InverseInfinityPlace P) f1024TowerX1 =
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
          f1024TowerF2DirectConstantAlgebra
          (f1024TowerF2InverseInfinityPlace P)
          (algebraMap F1024[X] F1024TowerF2 Polynomial.X)⁻¹ := by
      change @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
          f1024TowerF2DirectConstantAlgebra
          (f1024TowerF2InverseInfinityPlace P) f1024TowerX1 =
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
          f1024TowerF2DirectConstantAlgebra
          (f1024TowerF2InverseInfinityPlace P)
          (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialMap
            (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2 Polynomial.X)⁻¹
      rw [htransportX, f1024TowerT1_def, inv_inv]
    _ = -@QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
        f1024TowerF2DirectConstantAlgebra
        (f1024TowerF2InverseInfinityPlace P)
        (algebraMap F1024[X] F1024TowerF2 Polynomial.X) :=
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order_inv F1024 F1024TowerF2 _ _ _
        f1024TowerF2DirectConstantAlgebra
        (f1024TowerF2InverseInfinityPlace P) _
    _ = -@QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
        inverseConstantAlgebra
        (QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace F1024 F1024TowerF2
          (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
            F1024 F1024TowerF2 (Polynomial.idealX F1024) Q))
        (algebraMap F1024[X] F1024TowerF2 Polynomial.X) := by
      rw [hplace_order]
    _ = -((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal : ℤ) := by
      rw [horder, hQ]

/-- The inverse Eisenstein recurrence is totally ramified at every actual
first-tower inverse-fibre prime.  The proof obtains the upper bound from the
actual degree of the constructed extension and the divisibility from the
normalized valuation of the source recurrence; no infinity place is selected
or stored. -/
theorem f1024TowerF2InverseInfinityPlace_ramificationIdx_eq_32
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF2)) :
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
      P.1.asIdeal = 32 := by
  let oldRationalAlgebra : Algebra F1024TowerF1 F1024TowerF2 := inferInstance
  let oldFunctionField : _root_.FunctionField F1024 F1024TowerF2 := inferInstance
  let oldSeparable : Algebra.IsSeparable F1024TowerF1 F1024TowerF2 := inferInstance
  letI : Algebra F1024TowerF1 F1024TowerF2 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2
  letI : Algebra F1024[X] F1024TowerF2 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2
  letI : @IsScalarTower F1024[X] F1024TowerF1 F1024TowerF2
      RatFunc.instSMulOfFractionRingPolynomial
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2).toSMul
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2).toSMul :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2
  letI : _root_.FunctionField F1024 F1024TowerF2 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField)
      F1024 F1024TowerF2
  letI : Algebra.IsSeparable F1024TowerF1 F1024TowerF2 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
      F1024 F1024TowerF2
  let B : Type _ := _root_.FunctionField.ringOfIntegers F1024 F1024TowerF2
  letI : Module.IsTorsionFree F1024[X] B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective F1024 F1024TowerF2)
  letI : Module.Finite F1024[X] B :=
    QEC.Coding.AlgebraicGeometry.AffinePlace.finite_ringOfIntegers F1024 F1024TowerF2
  letI : NoZeroSMulDivisors F1024[X] B :=
    ⟨fun {c x} hzero =>
      (Module.isTorsionFree_iff_smul_eq_zero.mp
        (inferInstance : Module.IsTorsionFree F1024[X] B)) c x hzero⟩
  letI : ((Polynomial.idealX F1024).asIdeal).IsMaximal := by
    simpa using (Polynomial.idealX F1024).isMaximal
  let e := QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors
    (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2
  let Q := e P
  have hQ : (Q : Ideal B) = P.1.asIdeal := by
    dsimp only [Q, e]
    exact QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors_apply_asIdeal
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable)
      F1024 F1024TowerF2 P
  let E : ℕ :=
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
      P.1.asIdeal
  have hEeq : E = (Polynomial.idealX F1024).asIdeal.ramificationIdx' (Q : Ideal B) := by
    dsimp only [E, QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime]
    rw [← hQ]
  have hEpos : 0 < E := by
    rw [hEeq]
    exact Nat.pos_of_ne_zero
      (Ideal.Factors.ramificationIdx_ne_zero (Polynomial.idealX F1024).asIdeal Q)
  have hfinrank : Module.finrank F1024TowerF1 F1024TowerF2 = 32 := by
    calc
      Module.finrank F1024TowerF1 F1024TowerF2 =
          (letI : Algebra F1024TowerF1 F1024TowerF2 := oldRationalAlgebra
           Module.finrank F1024TowerF1 F1024TowerF2) := by
        symm
        exact @Algebra.finrank_eq_of_equiv_equiv
          F1024TowerF1 F1024TowerF2 _ _ oldRationalAlgebra
          F1024TowerF1 F1024TowerF2 _ _
          (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
            (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2)
          (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024).symm.toRingEquiv
          (RingEquiv.refl F1024TowerF2) (by
            ext x
            change QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalMap
                (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2
                ((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024).symm x) =
              (@algebraMap F1024TowerF1 F1024TowerF2 _ _ oldRationalAlgebra) x
            change (@algebraMap F1024TowerF1 F1024TowerF2 _ _ oldRationalAlgebra)
                (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024
                  ((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024).symm x)) =
              (@algebraMap F1024TowerF1 F1024TowerF2 _ _ oldRationalAlgebra) x
            simp)
      _ = 32 := f1024TowerF2_finrank
  have hEbound : E ≤ 32 := by
    rw [hEeq]
    calc
      (Polynomial.idealX F1024).asIdeal.ramificationIdx' (Q : Ideal B) ≤
          Module.finrank F1024TowerF1 F1024TowerF2 :=
        Ideal.ramificationIdx_le_finrank B F1024TowerF1 F1024TowerF2 (Q : Ideal B)
      _ = 32 := hfinrank
  have horderT : f1024TowerF2InverseInfinityOrder P f1024TowerT1 = (E : ℤ) := by
    change @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
        f1024TowerF2DirectConstantAlgebra
        (f1024TowerF2InverseInfinityPlace P) f1024TowerT1 = _
    rw [f1024TowerT1_def,
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order_inv F1024 F1024TowerF2 _ _ _
        f1024TowerF2DirectConstantAlgebra
        (f1024TowerF2InverseInfinityPlace P) _]
    change -f1024TowerF2InverseInfinityOrder P f1024TowerX1 = (E : ℤ)
    rw [f1024TowerF2InverseInfinityPlace_order_x1]
    dsimp [E]
    ring
  let ν : Valuation F1024TowerF2 ℤᵐ⁰ :=
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024 F1024TowerF2 _ _ _
      f1024TowerF2DirectConstantAlgebra
      (f1024TowerF2InverseInfinityPlace P)
  have hlog : WithZero.log (ν f1024TowerT1) = -(E : ℤ) := by
    change -WithZero.log (ν f1024TowerT1) = (E : ℤ) at horderT
    omega
  have hνt : ν f1024TowerT1 = WithZero.exp (-(E : ℤ)) := by
    have ht0 : ν f1024TowerT1 ≠ 0 :=
      (Valuation.ne_zero_iff ν).mpr (inv_ne_zero f1024TowerX1_ne_zero)
    calc
      ν f1024TowerT1 = WithZero.exp (WithZero.log (ν f1024TowerT1)) :=
        (WithZero.exp_log ht0).symm
      _ = WithZero.exp (-(E : ℤ)) := by rw [hlog]
  have hdiv : 32 ∣ E :=
    f1024TowerW2_inverse_valuation_dvd_32 ν E hEpos hνt
  change E = 32
  rcases hdiv with ⟨m, hm⟩
  omega

/-- At every actual inverse-fibre place of the first fixed tower, the next
Garcia--Stichtenoth coordinate `x₂` has a simple pole.  This realizes the
first local pole calculation needed for the next source recursion. -/
theorem f1024TowerF2InverseInfinityPlace_order_x2
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF2)) :
    f1024TowerF2InverseInfinityOrder P f1024TowerX2 = -1 := by
  let ν : Valuation F1024TowerF2 ℤᵐ⁰ :=
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024 F1024TowerF2 _ _ _
      f1024TowerF2DirectConstantAlgebra
      (f1024TowerF2InverseInfinityPlace P)
  have horderT : f1024TowerF2InverseInfinityOrder P f1024TowerT1 = (32 : ℤ) := by
    change @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
        f1024TowerF2DirectConstantAlgebra
        (f1024TowerF2InverseInfinityPlace P) f1024TowerT1 = _
    rw [f1024TowerT1_def,
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order_inv F1024 F1024TowerF2 _ _ _
        f1024TowerF2DirectConstantAlgebra
        (f1024TowerF2InverseInfinityPlace P) _]
    change -f1024TowerF2InverseInfinityOrder P f1024TowerX1 = (32 : ℤ)
    rw [f1024TowerF2InverseInfinityPlace_order_x1,
      f1024TowerF2InverseInfinityPlace_ramificationIdx_eq_32]
    norm_num
  have hlog : WithZero.log (ν f1024TowerT1) = -(32 : ℤ) := by
    change -WithZero.log (ν f1024TowerT1) = (32 : ℤ) at horderT
    omega
  have hνt : ν f1024TowerT1 = WithZero.exp (-(32 : ℤ)) := by
    have ht0 : ν f1024TowerT1 ≠ 0 :=
      (Valuation.ne_zero_iff ν).mpr (inv_ne_zero f1024TowerX1_ne_zero)
    calc
      ν f1024TowerT1 = WithZero.exp (WithZero.log (ν f1024TowerT1)) :=
        (WithZero.exp_log ht0).symm
      _ = WithZero.exp (-(32 : ℤ)) := by rw [hlog]
  have hνw : ν f1024TowerW2 = WithZero.exp (-(1 : ℤ)) :=
    f1024TowerW2_inverse_valuation_eq_exp_neg_one ν hνt
  have horderW : f1024TowerF2InverseInfinityOrder P f1024TowerW2 = 1 := by
    change -WithZero.log (ν f1024TowerW2) = 1
    rw [hνw]
    norm_num
  calc
    f1024TowerF2InverseInfinityOrder P f1024TowerX2 =
        f1024TowerF2InverseInfinityOrder P f1024TowerW2⁻¹ := by
      rw [f1024TowerW2_def, inv_inv]
    _ = -f1024TowerF2InverseInfinityOrder P f1024TowerW2 :=
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order_inv F1024 F1024TowerF2 _ _ _
        f1024TowerF2DirectConstantAlgebra
        (f1024TowerF2InverseInfinityPlace P) _
    _ = -1 := by rw [horderW]

/-- The second Garcia--Stichtenoth relation, written in the inverse coordinate
`V = x₂ / z₃`, is irreducible over the actual first tower field.  At a genuine
inverse-infinity place, `w₂ = x₂⁻¹` is a uniformizer, so
`V^32 + w₂^32 V^31 - w₂` is Eisenstein in its valuation ring.  The place is
chosen only inside this proof and is not made a tower datum. -/
theorem f1024_secondStepInverse_irreducible : Irreducible
    (X ^ 32 + C (f1024TowerW2 ^ 32) * X ^ 31 - C f1024TowerW2 : F1024TowerF2[X]) := by
  rcases f1024TowerF2_inverseInfinityFibre_nonempty with ⟨P⟩
  let ν : Valuation F1024TowerF2 ℤᵐ⁰ :=
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024 F1024TowerF2 _ _ _
      f1024TowerF2DirectConstantAlgebra
      (f1024TowerF2InverseInfinityPlace P)
  have hνsurj : Function.Surjective ν := by
    exact @QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized F1024 F1024TowerF2 _ _ _
      f1024TowerF2DirectConstantAlgebra
      (f1024TowerF2InverseInfinityPlace P)
  have hw2_ne : f1024TowerW2 ≠ 0 := by
    rw [f1024TowerW2_def]
    exact inv_ne_zero f1024TowerX2_ne_zero
  have horderW : f1024TowerF2InverseInfinityOrder P f1024TowerW2 = 1 := by
    calc
      f1024TowerF2InverseInfinityOrder P f1024TowerW2 =
          f1024TowerF2InverseInfinityOrder P f1024TowerX2⁻¹ := by
        rw [f1024TowerW2_def]
      _ = -f1024TowerF2InverseInfinityOrder P f1024TowerX2 :=
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.order_inv F1024 F1024TowerF2 _ _ _
          f1024TowerF2DirectConstantAlgebra
          (f1024TowerF2InverseInfinityPlace P) _
      _ = 1 := by
        rw [f1024TowerF2InverseInfinityPlace_order_x2]
        norm_num
  have hlog : WithZero.log (ν f1024TowerW2) = -(1 : ℤ) := by
    change -WithZero.log (ν f1024TowerW2) = 1 at horderW
    omega
  have hνw : ν f1024TowerW2 = WithZero.exp (-(1 : ℤ)) := by
    have hw0 : ν f1024TowerW2 ≠ 0 :=
      (Valuation.ne_zero_iff ν).mpr hw2_ne
    calc
      ν f1024TowerW2 = WithZero.exp (WithZero.log (ν f1024TowerW2)) :=
        (WithZero.exp_log hw0).symm
      _ = WithZero.exp (-(1 : ℤ)) := by rw [hlog]
  letI : ν.IsNontrivial := by
    rw [Valuation.isNontrivial_iff_exists_lt_one]
    refine ⟨f1024TowerW2, ?_, ?_⟩
    · exact hw2_ne
    · rw [hνw, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
  letI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass ν)) := inferInstance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass ν)) := inferInstance
  letI : ν.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' ν
  let w : ν.valuationSubring :=
    ⟨f1024TowerW2, (ν.mem_valuationSubring_iff _).mpr (by
      rw [hνw, ← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega))⟩
  have hw_ne : w ≠ 0 := by
    intro hw
    apply hw2_ne
    simpa [w] using
      congrArg (fun a : ν.valuationSubring => (a : F1024TowerF2)) hw
  have hwUniform : ν.IsUniformizer (w : F1024TowerF2) := by
    change ν f1024TowerW2 =
      (Valuation.IsRankOneDiscrete.generator ν : ℤᵐ⁰)
    calc
      ν f1024TowerW2 = WithZero.exp (-(1 : ℤ)) := hνw
      _ = (Valuation.IsRankOneDiscrete.generator ν : ℤᵐ⁰) := by
        simpa using congrArg (fun u : ℤᵐ⁰ˣ => (u : ℤᵐ⁰))
          (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
            (v := ν) hνsurj).symm
  let m : Ideal ν.valuationSubring := IsLocalRing.maximalIdeal ν.valuationSubring
  have hmprime : m.IsPrime := by
    dsimp [m]
    exact (IsLocalRing.maximalIdeal.isMaximal ν.valuationSubring).isPrime
  have hwM : w ∈ m := by
    dsimp [m]
    rw [Valuation.mem_maximalIdeal_iff]
    change ν f1024TowerW2 < 1
    rw [hνw, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hmgen : m = Ideal.span ({w} : Set ν.valuationSubring) := by
    dsimp [m]
    exact Valuation.IsUniformizer.is_generator (π := w) hwUniform
  let g : ν.valuationSubring[X] := X ^ 32 + C (w ^ 32) * X ^ 31 - C w
  have hwPow : w ^ 32 ≠ 0 := pow_ne_zero _ hw_ne
  have hgNatDegree : g.natDegree = 32 := by
    calc
      g.natDegree = (X ^ 32 + C (w ^ 32) * X ^ 31).natDegree := by
        dsimp only [g]
        rw [natDegree_sub_C]
      _ = (X ^ 32 : ν.valuationSubring[X]).natDegree :=
        natDegree_add_eq_left_of_natDegree_lt (by
          rw [natDegree_C_mul_X_pow 31 (w ^ 32) hwPow, natDegree_X_pow]
          norm_num)
      _ = 32 := natDegree_X_pow 32
  have hgMonic : g.Monic := by
    dsimp only [g]
    rw [add_sub_assoc]
    apply monic_X_pow_add
    calc
      degree (C (w ^ 32) * X ^ 31 - C w) ≤
          max (degree (C (w ^ 32) * X ^ 31)) (degree (C w)) := degree_sub_le _ _
      _ ≤ (31 : WithBot ℕ) := by
        apply max_le
        · exact degree_C_mul_X_pow_le 31 (w ^ 32)
        · exact degree_C_le.trans (by norm_num)
      _ < (32 : ℕ) := by norm_num
  have hcoeff : ∀ {n : ℕ}, n < g.natDegree → g.coeff n ∈ m := by
    intro n hn
    rw [hgNatDegree] at hn
    by_cases hn0 : n = 0
    · subst n
      have hcoeff0 : g.coeff 0 = -w := by
        simp only [g, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C,
          if_neg (by norm_num : (0 : ℕ) ≠ 32),
          if_neg (by norm_num : (0 : ℕ) ≠ 31), ite_true, zero_add, zero_sub]
      rw [hcoeff0]
      exact m.neg_mem hwM
    · by_cases hn31 : n = 31
      · subst n
        have hcoeff31 : g.coeff 31 = w ^ 32 := by
          simp only [g, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C,
            if_neg (by norm_num : (31 : ℕ) ≠ 32), ite_true,
            if_neg (by norm_num : (31 : ℕ) ≠ 0), zero_add, sub_zero]
        rw [hcoeff31]
        exact m.pow_mem_of_mem hwM 32 (by norm_num)
      · have hn32 : n ≠ 32 := Nat.ne_of_lt hn
        have hzero : g.coeff n = 0 := by
          simp only [g, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C,
            if_neg hn32, if_neg hn31, if_neg hn0, zero_add, sub_zero]
        rw [hzero]
        exact m.zero_mem
  have hconstant : g.coeff 0 ∉ m ^ 2 := by
    have hcoeff0 : g.coeff 0 = -w := by
      simp only [g, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C,
        if_neg (by norm_num : (0 : ℕ) ≠ 32),
        if_neg (by norm_num : (0 : ℕ) ≠ 31), ite_true, zero_add, zero_sub]
    rw [hcoeff0]
    intro hneg
    have hwSq : w ∈ m ^ 2 := by
      simpa using (m ^ 2).neg_mem hneg
    rw [hmgen, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hwSq
    obtain ⟨a, ha⟩ := hwSq
    have hwUnit : IsUnit w := by
      rw [isUnit_iff_exists_inv]
      refine ⟨a, ?_⟩
      exact mul_left_cancel₀ hw_ne (by
        calc
          w * (w * a) = w ^ 2 * a := by ring
          _ = w := ha.symm
          _ = w * 1 := (mul_one w).symm)
    exact hmprime.ne_top (Ideal.eq_top_of_isUnit_mem m hwM hwUnit)
  have hEisenstein : g.IsEisensteinAt m :=
    hgMonic.isEisensteinAt_of_mem_of_notMem hmprime.ne_top hcoeff hconstant
  have hIrreducible : Irreducible g :=
    hEisenstein.irreducible hmprime hgMonic.isPrimitive (by
      rw [hgNatDegree]
      norm_num)
  have hMapped : Irreducible (g.map (algebraMap ν.valuationSubring F1024TowerF2)) :=
    (hgMonic.irreducible_iff_irreducible_map_fraction_map
      (K := F1024TowerF2)).mp hIrreducible
  simpa [g, w] using hMapped

/-- The source-specific inverse polynomial for the second fixed
Garcia--Stichtenoth extension.  Its root is the inverse coordinate
`V = x₂ / z₃`, whose reciprocal change of variables recovers the displayed
source recurrence for `z₃`. -/
noncomputable def f1024SecondStepInversePolynomial : F1024TowerF2[X] :=
  X ^ 32 + C (f1024TowerW2 ^ 32) * X ^ 31 - C f1024TowerW2

private theorem f1024SecondStepInversePolynomial_monic :
    f1024SecondStepInversePolynomial.Monic := by
  rw [f1024SecondStepInversePolynomial, add_sub_assoc]
  apply monic_X_pow_add
  calc
    degree (C (f1024TowerW2 ^ 32) * X ^ 31 - C f1024TowerW2) ≤
        max (degree (C (f1024TowerW2 ^ 32) * X ^ 31)) (degree (C f1024TowerW2)) :=
      degree_sub_le _ _
    _ ≤ (31 : WithBot ℕ) := by
      apply max_le
      · exact degree_C_mul_X_pow_le 31 (f1024TowerW2 ^ 32)
      · exact degree_C_le.trans (by norm_num)
    _ < (32 : ℕ) := by norm_num

private theorem f1024SecondStepInversePolynomial_natDegree :
    f1024SecondStepInversePolynomial.natDegree = 32 := by
  have hwPow : f1024TowerW2 ^ 32 ≠ 0 :=
    pow_ne_zero _ f1024TowerW2_ne_zero
  calc
    f1024SecondStepInversePolynomial.natDegree =
        (X ^ 32 + C (f1024TowerW2 ^ 32) * X ^ 31 : F1024TowerF2[X]).natDegree := by
      rw [f1024SecondStepInversePolynomial, natDegree_sub_C]
    _ = (X ^ 32 : F1024TowerF2[X]).natDegree :=
      natDegree_add_eq_left_of_natDegree_lt (by
        rw [natDegree_C_mul_X_pow 31 (f1024TowerW2 ^ 32) hwPow, natDegree_X_pow]
        norm_num)
    _ = 32 := natDegree_X_pow 32

private theorem f1024SecondStepInversePolynomial_derivative :
    derivative f1024SecondStepInversePolynomial =
      C (f1024TowerW2 ^ 32 * ((31 : ℕ) : F1024TowerF2)) * X ^ 30 := by
  have h32 : ((32 : ℕ) : F1024TowerF2) = 0 := by
    rw [CharP.cast_eq_zero_iff F1024TowerF2 2]
    norm_num
  simp only [f1024SecondStepInversePolynomial, derivative_sub, derivative_add,
    derivative_X_pow, derivative_C_mul_X_pow, derivative_C, h32, C_0, zero_mul,
    zero_add, Nat.reduceSub, sub_zero]

private theorem f1024SecondStepInversePolynomial_separable :
    f1024SecondStepInversePolynomial.Separable := by
  rw [separable_iff_derivative_ne_zero
    (by simpa only [f1024SecondStepInversePolynomial] using
      f1024_secondStepInverse_irreducible)]
  rw [f1024SecondStepInversePolynomial_derivative]
  apply mul_ne_zero
  · apply C_ne_zero.mpr
    apply mul_ne_zero
    · exact pow_ne_zero _ f1024TowerW2_ne_zero
    · intro h31
      have hdiv : 2 ∣ 31 :=
        (CharP.cast_eq_zero_iff F1024TowerF2 2 31).mp h31
      norm_num at hdiv
  · exact pow_ne_zero _ Polynomial.X_ne_zero

/-- The actual second non-rational field in the fixed `F1024` tower. -/
noncomputable abbrev F1024TowerF3 : Type :=
  AdjoinRoot f1024SecondStepInversePolynomial

noncomputable instance f1024SecondStepInverseIrreducibleFact :
    Fact (Irreducible f1024SecondStepInversePolynomial) :=
  ⟨by
    simpa only [f1024SecondStepInversePolynomial] using
      f1024_secondStepInverse_irreducible⟩

local instance f1024TowerF3CharTwo : CharP F1024TowerF3 2 :=
  charP_of_injective_algebraMap
    (algebraMap F1024TowerF2 F1024TowerF3).injective 2

noncomputable instance f1024TowerF3FiniteDimensional :
    FiniteDimensional F1024TowerF2 F1024TowerF3 :=
  (AdjoinRoot.powerBasis' f1024SecondStepInversePolynomial_monic).basis.finiteDimensional_of_finite

/-- The concrete second extension has the source-required degree `32`. -/
theorem f1024TowerF3_finrank : Module.finrank F1024TowerF2 F1024TowerF3 = 32 := by
  simpa [F1024TowerF3, f1024SecondStepInversePolynomial_natDegree] using
    (AdjoinRoot.powerBasis' f1024SecondStepInversePolynomial_monic).finrank

/-- The concrete second tower field has total degree `32² = 1024` over the
source rational function field. -/
theorem f1024TowerF3_finrank_over_F1 :
    Module.finrank F1024TowerF1 F1024TowerF3 = 1024 := by
  calc
    Module.finrank F1024TowerF1 F1024TowerF3 =
        Module.finrank F1024TowerF1 F1024TowerF2 *
          Module.finrank F1024TowerF2 F1024TowerF3 := by
      symm
      exact Module.finrank_mul_finrank F1024TowerF1 F1024TowerF2 F1024TowerF3
    _ = 1024 := by norm_num [f1024TowerF2_finrank, f1024TowerF3_finrank]

noncomputable instance f1024TowerF3Separable :
    Algebra.IsSeparable F1024TowerF2 F1024TowerF3 := by
  rw [← AlgEquiv.Algebra.isSeparable_iff <|
    (IntermediateField.equivOfEq
      (IntermediateField.adjoin_root_eq_top f1024SecondStepInversePolynomial)).trans
        IntermediateField.topEquiv,
    IntermediateField.isSeparable_adjoin_simple_iff_isSeparable,
    IsSeparable, AdjoinRoot.minpoly_root f1024SecondStepInversePolynomial_monic.ne_zero,
    f1024SecondStepInversePolynomial_monic.leadingCoeff, inv_one, C.map_one, mul_one]
  exact f1024SecondStepInversePolynomial_separable

noncomputable instance f1024TowerF3FunctionField : _root_.FunctionField F1024 F1024TowerF3 :=
  FiniteDimensional.trans F1024TowerF1 F1024TowerF2 F1024TowerF3

/-- The second fixed tower field is separable over the original rational
function field.  This is the direct scalar interface needed to transport the
inverse chart for its actual height-one primes. -/
noncomputable instance f1024TowerF3SeparableOverF1 :
    Algebra.IsSeparable F1024TowerF1 F1024TowerF3 :=
  Algebra.IsSeparable.trans F1024TowerF1 F1024TowerF2 F1024TowerF3

/-- The direct coordinate tower reaches the concrete second tower field.
Keeping this scalar tower explicit prevents the inverse-chart construction
from choosing an unrelated polynomial action. -/
noncomputable instance f1024TowerF3PolynomialRatFuncTower :
    IsScalarTower F1024[X] F1024TowerF1 F1024TowerF3 := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rfl

/-- The inverse root used to construct the second fixed tower field. -/
noncomputable def f1024TowerV3 : F1024TowerF3 :=
  AdjoinRoot.root f1024SecondStepInversePolynomial

/-- The inverse root satisfies the source-specific Eisenstein orientation of
the second Garcia--Stichtenoth relation. -/
theorem f1024TowerV3_inverse_equation : f1024TowerV3 ^ 32 +
    algebraMap F1024TowerF2 F1024TowerF3 (f1024TowerW2 ^ 32) *
      f1024TowerV3 ^ 31 =
    algebraMap F1024TowerF2 F1024TowerF3 f1024TowerW2 := by
  rw [AdjoinRoot.algebraMap_eq]
  apply sub_eq_zero.mp
  have hroot := AdjoinRoot.eval₂_root f1024SecondStepInversePolynomial
  change (X ^ 32 + C (f1024TowerW2 ^ 32) * X ^ 31 - C f1024TowerW2 : F1024TowerF2[X]).eval₂
      (AdjoinRoot.of f1024SecondStepInversePolynomial)
      (AdjoinRoot.root f1024SecondStepInversePolynomial) = 0 at hroot
  simpa only [f1024TowerV3, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C] using
    hroot

/-- The inverse root is nonzero because its defining relation has the
nonzero constant coefficient `-w₂`. -/
theorem f1024TowerV3_ne_zero : f1024TowerV3 ≠ 0 := by
  intro hV
  have hzero : algebraMap F1024TowerF2 F1024TowerF3 f1024TowerW2 = 0 := by
    rw [← f1024TowerV3_inverse_equation, hV]
    norm_num
  exact (map_ne_zero_iff (algebraMap F1024TowerF2 F1024TowerF3)
    (algebraMap F1024TowerF2 F1024TowerF3).injective).mpr f1024TowerW2_ne_zero hzero

/-- The source's second Artin--Schreier generator, recovered from the inverse
root by `z₃ = x₂ / V`. -/
noncomputable def f1024TowerZ3 : F1024TowerF3 :=
  algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2 / f1024TowerV3

/-- The recovered generator satisfies the displayed second
Garcia--Stichtenoth recurrence exactly. -/
theorem f1024TowerZ3_equation : f1024TowerZ3 ^ 32 + f1024TowerZ3 =
    algebraMap F1024TowerF2 F1024TowerF3 (f1024TowerX2 ^ 33) := by
  let u : F1024TowerF3 := algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2
  have hu : u ≠ 0 := by
    dsimp [u]
    exact (map_ne_zero_iff (algebraMap F1024TowerF2 F1024TowerF3)
      (algebraMap F1024TowerF2 F1024TowerF3).injective).mpr f1024TowerX2_ne_zero
  have hroot : f1024TowerV3 ^ 32 + u⁻¹ ^ 32 * f1024TowerV3 ^ 31 = u⁻¹ := by
    dsimp [u]
    have hport := f1024TowerV3_inverse_equation
    simp only [f1024TowerW2_def, map_inv₀, map_pow] at hport ⊢
    exact hport
  have hcleared : u ^ 33 * f1024TowerV3 ^ 32 + u * f1024TowerV3 ^ 31 = u ^ 32 := by
    calc
      u ^ 33 * f1024TowerV3 ^ 32 + u * f1024TowerV3 ^ 31 =
      u ^ 33 * (f1024TowerV3 ^ 32 + u⁻¹ ^ 32 * f1024TowerV3 ^ 31) := by
        field_simp [hu]
      _ = u ^ 33 * u⁻¹ := by rw [hroot]
      _ = u ^ 32 := by
        field_simp [hu]
  have htwo : (2 : F1024TowerF3) = 0 :=
    CharP.ofNat_eq_zero' (R := F1024TowerF3) 2 2 (by norm_num)
  have hadd_self (a : F1024TowerF3) : a + a = 0 := by
    rw [← two_mul, htwo, zero_mul]
  have htarget : u ^ 32 + u * f1024TowerV3 ^ 31 =
      u ^ 33 * f1024TowerV3 ^ 32 := by
    calc
      u ^ 32 + u * f1024TowerV3 ^ 31 =
          (u ^ 33 * f1024TowerV3 ^ 32 + u * f1024TowerV3 ^ 31) +
            u * f1024TowerV3 ^ 31 := by rw [hcleared]
      _ = u ^ 33 * f1024TowerV3 ^ 32 +
          (u * f1024TowerV3 ^ 31 + u * f1024TowerV3 ^ 31) := by ring
      _ = u ^ 33 * f1024TowerV3 ^ 32 := by rw [hadd_self, add_zero]
  rw [map_pow]
  change (u / f1024TowerV3) ^ 32 + u / f1024TowerV3 = u ^ 33
  calc
    (u / f1024TowerV3) ^ 32 + u / f1024TowerV3 =
        (u ^ 32 + u * f1024TowerV3 ^ 31) / f1024TowerV3 ^ 32 := by
      rw [div_pow]
      field_simp [f1024TowerV3_ne_zero]
    _ = u ^ 33 := by
      rw [htarget]
      field_simp [f1024TowerV3_ne_zero]

private theorem f1024TowerF3_x2_ne_zero :
    algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2 ≠ 0 :=
  (map_ne_zero_iff (algebraMap F1024TowerF2 F1024TowerF3)
    (algebraMap F1024TowerF2 F1024TowerF3).injective).mpr f1024TowerX2_ne_zero

/-- The source's third tower coordinate `x₃ = z₃ / x₂`, in the actual
second non-rational field. -/
noncomputable def f1024TowerX3 : F1024TowerF3 :=
  f1024TowerZ3 / algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2

/-- The defining quotient is exactly `z₃ = x₂ x₃` in the constructed
second tower field. -/
theorem f1024TowerX2_mul_X3 :
    algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2 * f1024TowerX3 =
      f1024TowerZ3 := by
  calc
    algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2 * f1024TowerX3 =
        f1024TowerZ3 / algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2 *
          algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2 := by
      rw [f1024TowerX3, mul_comm]
    _ = f1024TowerZ3 := div_mul_cancel₀ _ f1024TowerF3_x2_ne_zero

/-- Clearing the nonzero `x₂` denominator rewrites the second source
relation in the concrete coordinate `x₃`. -/
theorem f1024TowerX3_equation :
    (algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2) ^ 31 *
      f1024TowerX3 ^ 32 + f1024TowerX3 =
    (algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2) ^ 32 := by
  let u : F1024TowerF3 := algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2
  have hu : u ≠ 0 := by
    dsimp [u]
    exact f1024TowerF3_x2_ne_zero
  have hz : f1024TowerZ3 ^ 32 + f1024TowerZ3 = u ^ 33 := by
    dsimp [u]
    have hport := f1024TowerZ3_equation
    simp only [map_pow] at hport ⊢
    exact hport
  change u ^ 31 * (f1024TowerZ3 / u) ^ 32 + f1024TowerZ3 / u = u ^ 32
  calc
    u ^ 31 * (f1024TowerZ3 / u) ^ 32 + f1024TowerZ3 / u =
        (f1024TowerZ3 ^ 32 + f1024TowerZ3) / u := by
      rw [div_pow]
      field_simp [hu]
    _ = u ^ 32 := by
      rw [hz]
      field_simp [hu]

/-- Repackage the concrete second-tower inverse-chart valuation under its
direct-chart constant algebra.  The underlying normalized valuation is the
same actual place data; only the scalar-map record is changed. -/
private noncomputable def f1024TowerF3RepackageRawGlobalPlace
    (A : Algebra F1024 F1024TowerF3) {A₀ : Algebra F1024 F1024TowerF3}
    (P : @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F1024TowerF3 _ _ _ A₀) :
    @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F1024TowerF3 _ _ _ A := by
  exact @QEC.Coding.AlgebraicGeometry.GlobalPlace.mk F1024 F1024TowerF3 _ _ _ A
    (@QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024 F1024TowerF3 _ _ _ A₀ P)
    (@QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized F1024 F1024TowerF3 _ _ _ A₀ P)

/-- The direct-chart constant algebra used to express normalized orders in
the concrete second tower field. -/
@[reducible] noncomputable def f1024TowerF3DirectConstantAlgebra : Algebra F1024 F1024TowerF3 :=
  QEC.Coding.AlgebraicGeometry.AffinePlace.constantAlgebra F1024 F1024TowerF3

/-- An actual inverse-chart upper prime of the concrete second tower field,
repackaged as its normalized direct-chart global place.  The upper ideal stays
an argument, so this construction neither selects nor stores an infinity
place. -/
private noncomputable def f1024TowerF3InverseInfinityPlace
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF3)) :
    @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F1024TowerF3 _ _ _
      f1024TowerF3DirectConstantAlgebra :=
  f1024TowerF3RepackageRawGlobalPlace
    f1024TowerF3DirectConstantAlgebra
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.globalPlace
      (k := F1024) (F := F1024TowerF3) P)

/-- The normalized order at a concrete second-tower inverse-chart upper
prime.  Its argument is an actual fibre point rather than a synthetic place
witness. -/
noncomputable def f1024TowerF3InverseInfinityOrder
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF3)) (u : F1024TowerF3) : ℤ :=
  @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF3 _ _ _
    f1024TowerF3DirectConstantAlgebra
    (f1024TowerF3InverseInfinityPlace P) u

/-- At every actual second-tower inverse-chart upper prime, the embedded
source coordinate `x₁` has order the negative ramification index above `(X)`.
This is the concrete normalization bridge required before the second
inverse-Eisenstein valuation calculation; it asserts neither a chosen prime
nor total ramification. -/
theorem f1024TowerF3InverseInfinityPlace_order_x1
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF3)) :
    f1024TowerF3InverseInfinityOrder P
        (algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX1) =
      -((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal : ℤ) := by
  change @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF3 _ _ _
      f1024TowerF3DirectConstantAlgebra
      (f1024TowerF3InverseInfinityPlace P)
      (algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX1) = _
  let oldRationalAlgebra : Algebra F1024TowerF1 F1024TowerF3 := inferInstance
  let oldFunctionField : _root_.FunctionField F1024 F1024TowerF3 := inferInstance
  let oldSeparable : Algebra.IsSeparable F1024TowerF1 F1024TowerF3 := inferInstance
  have htransportX :
      QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialMap
          (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3
          Polynomial.X = (algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX1)⁻¹ := by
    change QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalMap
        (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3 RatFunc.X =
      (algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX1)⁻¹
    change algebraMap F1024TowerF1 F1024TowerF3
        (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024
          RatFunc.X) =
      (algebraMap F1024TowerF2 F1024TowerF3
        (algebraMap F1024TowerF1 F1024TowerF2 RatFunc.X))⁻¹
    rw [QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution_X,
      ← IsScalarTower.algebraMap_apply F1024TowerF1 F1024TowerF2 F1024TowerF3, map_inv₀]
  letI : Algebra F1024TowerF1 F1024TowerF3 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3
  letI : Algebra F1024[X] F1024TowerF3 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3
  letI : @IsScalarTower F1024[X] F1024TowerF1 F1024TowerF3
      RatFunc.instSMulOfFractionRingPolynomial
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3).toSMul
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3).toSMul :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3
  letI : _root_.FunctionField F1024 F1024TowerF3 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField)
      F1024 F1024TowerF3
  letI : Algebra.IsSeparable F1024TowerF1 F1024TowerF3 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
      F1024 F1024TowerF3
  let inverseConstantAlgebra : Algebra F1024 F1024TowerF3 :=
    QEC.Coding.AlgebraicGeometry.AffinePlace.constantAlgebra F1024 F1024TowerF3
  let B : Type _ := _root_.FunctionField.ringOfIntegers F1024 F1024TowerF3
  letI : Module.IsTorsionFree F1024[X] B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective F1024 F1024TowerF3)
  let e := QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3
  let Q := e P
  let x : B := algebraMap F1024[X] B Polynomial.X
  have hx : x ≠ 0 := by
    simpa only [x, map_zero] using
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective F1024 F1024TowerF3).ne
        (Polynomial.X_ne_zero : (Polynomial.X : F1024[X]) ≠ 0)
  have hmap : Ideal.map (algebraMap F1024[X] B)
      (Polynomial.idealX F1024).asIdeal ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot (Polynomial.idealX F1024).ne_bot
  have hspan : Ideal.span ({x} : Set B) =
      Ideal.map (algebraMap F1024[X] B) (Polynomial.idealX F1024).asIdeal := by
    dsimp only [x]
    calc
      Ideal.span ({algebraMap F1024[X] B Polynomial.X} : Set B) =
          Ideal.map (algebraMap F1024[X] B)
            (Ideal.span ({Polynomial.X} : Set F1024[X])) := by
        rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.map (algebraMap F1024[X] B)
          (Polynomial.idealX F1024).asIdeal := by
        rw [Polynomial.idealX_span]
  have horder :
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF3 _ _ _
        inverseConstantAlgebra
        (QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace F1024 F1024TowerF3
          (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
            F1024 F1024TowerF3 (Polynomial.idealX F1024) Q))
        (algebraMap F1024[X] F1024TowerF3 Polynomial.X) =
        ((Polynomial.idealX F1024).asIdeal.ramificationIdx' (Q : Ideal B) : ℤ) := by
    rw [IsScalarTower.algebraMap_apply F1024[X] B F1024TowerF3]
    change @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF3 _ _ _
        inverseConstantAlgebra
        (QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace F1024 F1024TowerF3
          (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
            F1024 F1024TowerF3 (Polynomial.idealX F1024) Q))
        (algebraMap B F1024TowerF3 x) = _
    rw [QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace_order_of_integral_eq_multiplicity
      F1024 F1024TowerF3
      (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
        F1024 F1024TowerF3 (Polynomial.idealX F1024) Q) hx,
      QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace_asIdeal,
      hspan]
    exact_mod_cast
      (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hmap
        (Ideal.Factors.isPrime (Polynomial.idealX F1024).asIdeal Q)).symm
  have hQ : (Q : Ideal B) = P.1.asIdeal := by
    dsimp only [Q, e]
    exact QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors_apply_asIdeal
        (oldRationalAlgebra := oldRationalAlgebra)
        (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable)
        F1024 F1024TowerF3 P
  have hplace :
      QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace F1024 F1024TowerF3
          (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
            F1024 F1024TowerF3 (Polynomial.idealX F1024) Q) =
        QEC.Coding.AlgebraicGeometry.InverseAffinePlace.globalPlace
          (oldRationalAlgebra := oldRationalAlgebra)
          (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable)
          F1024 F1024TowerF3 P :=
    QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.directFactorGlobalPlace_infinityFibreEquiv
          (oldRationalAlgebra := oldRationalAlgebra)
          (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable)
          F1024 F1024TowerF3 P
  have hplace_order (u : F1024TowerF3) :
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF3 _ _ _
          f1024TowerF3DirectConstantAlgebra
          (f1024TowerF3InverseInfinityPlace P) u =
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF3 _ _ _
          inverseConstantAlgebra
          (QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace F1024 F1024TowerF3
            (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
              F1024 F1024TowerF3 (Polynomial.idealX F1024) Q)) u := by
    change -WithZero.log
        ((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.globalPlace
          (oldRationalAlgebra := oldRationalAlgebra)
          (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable)
          F1024 F1024TowerF3 P).valuation u) =
      -WithZero.log
        ((QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace F1024 F1024TowerF3
          (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
            F1024 F1024TowerF3 (Polynomial.idealX F1024) Q)).valuation u)
    rw [← congrArg (fun V => V.valuation) hplace]
  calc
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF3 _ _ _
        f1024TowerF3DirectConstantAlgebra
        (f1024TowerF3InverseInfinityPlace P)
        (algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX1) =
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF3 _ _ _
          f1024TowerF3DirectConstantAlgebra
          (f1024TowerF3InverseInfinityPlace P)
          (algebraMap F1024[X] F1024TowerF3 Polynomial.X)⁻¹ := by
      change @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF3 _ _ _
          f1024TowerF3DirectConstantAlgebra
          (f1024TowerF3InverseInfinityPlace P)
          (algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX1) =
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF3 _ _ _
          f1024TowerF3DirectConstantAlgebra
          (f1024TowerF3InverseInfinityPlace P)
          (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialMap
            (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3 Polynomial.X)⁻¹
      rw [htransportX, inv_inv]
    _ = -@QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF3 _ _ _
        f1024TowerF3DirectConstantAlgebra
        (f1024TowerF3InverseInfinityPlace P)
        (algebraMap F1024[X] F1024TowerF3 Polynomial.X) :=
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order_inv F1024 F1024TowerF3 _ _ _
        f1024TowerF3DirectConstantAlgebra
        (f1024TowerF3InverseInfinityPlace P) _
    _ = -@QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF3 _ _ _
        inverseConstantAlgebra
        (QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace F1024 F1024TowerF3
          (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
            F1024 F1024TowerF3 (Polynomial.idealX F1024) Q))
        (algebraMap F1024[X] F1024TowerF3 Polynomial.X) := by
      rw [hplace_order]
    _ = -((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal : ℤ) := by
      rw [horder, hQ]

/-- The first inverse coordinate, embedded into the concrete second tower
field. -/
private noncomputable def f1024TowerF3T1 : F1024TowerF3 :=
  algebraMap F1024TowerF2 F1024TowerF3 f1024TowerT1

/-- The reciprocal of `x₂`, embedded into the concrete second tower field. -/
private noncomputable def f1024TowerF3W2 : F1024TowerF3 :=
  algebraMap F1024TowerF2 F1024TowerF3 f1024TowerW2

private theorem f1024TowerF3T1_ne_zero : f1024TowerF3T1 ≠ 0 := by
  rw [f1024TowerF3T1]
  exact (map_ne_zero_iff (algebraMap F1024TowerF2 F1024TowerF3)
    (algebraMap F1024TowerF2 F1024TowerF3).injective).mpr
      (inv_ne_zero f1024TowerX1_ne_zero)

private theorem f1024TowerF3W2_ne_zero : f1024TowerF3W2 ≠ 0 := by
  rw [f1024TowerF3W2]
  exact (map_ne_zero_iff (algebraMap F1024TowerF2 F1024TowerF3)
    (algebraMap F1024TowerF2 F1024TowerF3).injective).mpr f1024TowerW2_ne_zero

/-- The first inverse Garcia--Stichtenoth recurrence transported to the
actual second tower field. -/
private theorem f1024TowerF3W2_inverse_equation : f1024TowerF3W2 ^ 32 +
    f1024TowerF3T1 ^ 32 * f1024TowerF3W2 ^ 31 = f1024TowerF3T1 := by
  simpa only [f1024TowerF3W2, f1024TowerF3T1, map_add, map_mul, map_pow] using
    congrArg (algebraMap F1024TowerF2 F1024TowerF3)
      f1024TowerW2_inverse_equation

/-- The second inverse Garcia--Stichtenoth recurrence in the two local
coordinates of the actual second tower field. -/
private theorem f1024TowerV3_inverse_equation_local : f1024TowerV3 ^ 32 +
    f1024TowerF3W2 ^ 32 * f1024TowerV3 ^ 31 = f1024TowerF3W2 := by
  simpa only [f1024TowerF3W2, map_pow] using f1024TowerV3_inverse_equation

/-- The first inverse recurrence, evaluated at a normalized second-tower
place, identifies the valuation of `w₂` as one thirty-second of the base
ramification exponent. -/
private theorem f1024TowerF3W2_inverse_valuation_data
    (ν : Valuation F1024TowerF3 ℤᵐ⁰) (E : ℕ) (hEpos : 0 < E)
    (hνt : ν f1024TowerF3T1 = WithZero.exp (-(E : ℤ))) :
    ∃ m : ℕ, E = 32 * m ∧
      ν f1024TowerF3W2 = WithZero.exp (-(m : ℤ)) := by
  have hw0 : ν f1024TowerF3W2 ≠ 0 :=
    (Valuation.ne_zero_iff ν).mpr f1024TowerF3W2_ne_zero
  let r : ℤ := WithZero.log (ν f1024TowerF3W2)
  have hνw : ν f1024TowerF3W2 = WithZero.exp r := by
    dsimp only [r]
    exact (WithZero.exp_log hw0).symm
  have hνw32 : ν (f1024TowerF3W2 ^ 32) = WithZero.exp ((32 : ℕ) • r) := by
    rw [map_pow, hνw, ← WithZero.exp_nsmul]
  have hνtw : ν (f1024TowerF3T1 ^ 32 * f1024TowerF3W2 ^ 31) =
      WithZero.exp ((32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r) := by
    rw [map_mul, map_pow, map_pow, hνt, hνw,
      ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add]
  have hνsum : ν (f1024TowerF3W2 ^ 32 +
      f1024TowerF3T1 ^ 32 * f1024TowerF3W2 ^ 31) =
      WithZero.exp (-(E : ℤ)) := by
    rw [f1024TowerF3W2_inverse_equation, hνt]
  rcases lt_trichotomy (ν (f1024TowerF3W2 ^ 32))
      (ν (f1024TowerF3T1 ^ 32 * f1024TowerF3W2 ^ 31)) with hlt | heq | hgt
  · have hsum : ν (f1024TowerF3W2 ^ 32 +
        f1024TowerF3T1 ^ 32 * f1024TowerF3W2 ^ 31) =
        ν (f1024TowerF3T1 ^ 32 * f1024TowerF3W2 ^ 31) := by
      rw [Valuation.map_add_eq_of_lt_right ν hlt]
    rw [hsum, hνtw] at hνsum
    have hEq : (32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r = -(E : ℤ) :=
      WithZero.exp_inj.mp hνsum
    have hltExp : (32 : ℕ) • r <
        (32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r := by
      rw [← f1024Tower_exp_lt_exp, ← hνw32, ← hνtw]
      exact hlt
    simp only [nsmul_eq_mul] at hEq hltExp
    omega
  · have hsame : WithZero.exp ((32 : ℕ) • r) =
        WithZero.exp ((32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r) := by
      rw [← hνw32, ← hνtw]
      exact heq
    have hEq : (32 : ℕ) • r =
        (32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r :=
      WithZero.exp_inj.mp hsame
    have hsumle : ν (f1024TowerF3W2 ^ 32 +
        f1024TowerF3T1 ^ 32 * f1024TowerF3W2 ^ 31) ≤
        ν (f1024TowerF3W2 ^ 32) :=
      (map_add_le_max ν _ _).trans_eq (by rw [← heq, max_self])
    rw [hνsum, hνw32] at hsumle
    have hsmall : (32 : ℕ) • r < -(E : ℤ) := by
      have hEq' : (32 : ℤ) * r =
          (32 : ℤ) * (-(E : ℤ)) + (31 : ℤ) * r := by
        have hport := hEq
        simp only [nsmul_eq_mul] at hport ⊢
        exact hport
      have hsmall' : (32 : ℤ) * r < -(E : ℤ) := by
        omega
      have hport := hsmall'
      simp only [nsmul_eq_mul] at hport ⊢
      exact hport
    exfalso
    exact (not_lt_of_ge hsumle) (f1024Tower_exp_lt_exp.mpr hsmall)
  · have hsum : ν (f1024TowerF3W2 ^ 32 +
        f1024TowerF3T1 ^ 32 * f1024TowerF3W2 ^ 31) =
        ν (f1024TowerF3W2 ^ 32) := by
      rw [Valuation.map_add_eq_of_lt_left ν hgt]
    rw [hsum, hνw32] at hνsum
    have hEq : (32 : ℕ) • r = -(E : ℤ) := WithZero.exp_inj.mp hνsum
    have hrneg : r < 0 := by
      rw [nsmul_eq_mul] at hEq
      omega
    have hnonneg : 0 ≤ -r := by omega
    rw [nsmul_eq_mul] at hEq
    have hEq' : (E : ℤ) = 32 * (-r) := by omega
    have hcast : (((-r).toNat : ℕ) : ℤ) = -r :=
      Int.toNat_of_nonneg hnonneg
    have hEq'' : (E : ℤ) = (32 : ℤ) * (((-r).toNat : ℕ) : ℤ) := by
      rw [hcast]
      exact hEq'
    refine ⟨(-r).toNat, ?_, ?_⟩
    · exact_mod_cast hEq''
    · calc
        ν f1024TowerF3W2 = WithZero.exp r := hνw
        _ = WithZero.exp (-(((-r).toNat : ℕ) : ℤ)) := by
          congr 1
          rw [hcast]
          ring

/-- The second inverse recurrence then identifies the inverse root valuation
as one thirty-second of the `w₂` exponent. -/
private theorem f1024TowerV3_inverse_valuation_data
    (ν : Valuation F1024TowerF3 ℤᵐ⁰) (m : ℕ) (hmpos : 0 < m)
    (hνw : ν f1024TowerF3W2 = WithZero.exp (-(m : ℤ))) :
    ∃ n : ℕ, m = 32 * n ∧
      ν f1024TowerV3 = WithZero.exp (-(n : ℤ)) := by
  have hV0 : ν f1024TowerV3 ≠ 0 :=
    (Valuation.ne_zero_iff ν).mpr f1024TowerV3_ne_zero
  let s : ℤ := WithZero.log (ν f1024TowerV3)
  have hνV : ν f1024TowerV3 = WithZero.exp s := by
    dsimp only [s]
    exact (WithZero.exp_log hV0).symm
  have hνV32 : ν (f1024TowerV3 ^ 32) = WithZero.exp ((32 : ℕ) • s) := by
    rw [map_pow, hνV, ← WithZero.exp_nsmul]
  have hνwV : ν (f1024TowerF3W2 ^ 32 * f1024TowerV3 ^ 31) =
      WithZero.exp ((32 : ℕ) • (-(m : ℤ)) + (31 : ℕ) • s) := by
    rw [map_mul, map_pow, map_pow, hνw, hνV,
      ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add]
  have hνsum : ν (f1024TowerV3 ^ 32 +
      f1024TowerF3W2 ^ 32 * f1024TowerV3 ^ 31) =
      WithZero.exp (-(m : ℤ)) := by
    rw [f1024TowerV3_inverse_equation_local, hνw]
  rcases lt_trichotomy (ν (f1024TowerV3 ^ 32))
      (ν (f1024TowerF3W2 ^ 32 * f1024TowerV3 ^ 31)) with hlt | heq | hgt
  · have hsum : ν (f1024TowerV3 ^ 32 +
        f1024TowerF3W2 ^ 32 * f1024TowerV3 ^ 31) =
        ν (f1024TowerF3W2 ^ 32 * f1024TowerV3 ^ 31) := by
      rw [Valuation.map_add_eq_of_lt_right ν hlt]
    rw [hsum, hνwV] at hνsum
    have hEq : (32 : ℕ) • (-(m : ℤ)) + (31 : ℕ) • s = -(m : ℤ) :=
      WithZero.exp_inj.mp hνsum
    have hltExp : (32 : ℕ) • s <
        (32 : ℕ) • (-(m : ℤ)) + (31 : ℕ) • s := by
      rw [← f1024Tower_exp_lt_exp, ← hνV32, ← hνwV]
      exact hlt
    simp only [nsmul_eq_mul] at hEq hltExp
    omega
  · have hsame : WithZero.exp ((32 : ℕ) • s) =
        WithZero.exp ((32 : ℕ) • (-(m : ℤ)) + (31 : ℕ) • s) := by
      rw [← hνV32, ← hνwV]
      exact heq
    have hEq : (32 : ℕ) • s =
        (32 : ℕ) • (-(m : ℤ)) + (31 : ℕ) • s :=
      WithZero.exp_inj.mp hsame
    have hsumle : ν (f1024TowerV3 ^ 32 +
        f1024TowerF3W2 ^ 32 * f1024TowerV3 ^ 31) ≤
        ν (f1024TowerV3 ^ 32) :=
      (map_add_le_max ν _ _).trans_eq (by rw [← heq, max_self])
    rw [hνsum, hνV32] at hsumle
    have hsmall : (32 : ℕ) • s < -(m : ℤ) := by
      have hEq' : (32 : ℤ) * s =
          (32 : ℤ) * (-(m : ℤ)) + (31 : ℤ) * s := by
        have hport := hEq
        simp only [nsmul_eq_mul] at hport ⊢
        exact hport
      have hsmall' : (32 : ℤ) * s < -(m : ℤ) := by
        omega
      have hport := hsmall'
      simp only [nsmul_eq_mul] at hport ⊢
      exact hport
    exfalso
    exact (not_lt_of_ge hsumle) (f1024Tower_exp_lt_exp.mpr hsmall)
  · have hsum : ν (f1024TowerV3 ^ 32 +
        f1024TowerF3W2 ^ 32 * f1024TowerV3 ^ 31) =
        ν (f1024TowerV3 ^ 32) := by
      rw [Valuation.map_add_eq_of_lt_left ν hgt]
    rw [hsum, hνV32] at hνsum
    have hEq : (32 : ℕ) • s = -(m : ℤ) := WithZero.exp_inj.mp hνsum
    have hsneg : s < 0 := by
      rw [nsmul_eq_mul] at hEq
      omega
    have hnonneg : 0 ≤ -s := by omega
    rw [nsmul_eq_mul] at hEq
    have hEq' : (m : ℤ) = 32 * (-s) := by omega
    have hcast : (((-s).toNat : ℕ) : ℤ) = -s :=
      Int.toNat_of_nonneg hnonneg
    have hEq'' : (m : ℤ) = (32 : ℤ) * (((-s).toNat : ℕ) : ℤ) := by
      rw [hcast]
      exact hEq'
    refine ⟨(-s).toNat, ?_, ?_⟩
    · exact_mod_cast hEq''
    · calc
        ν f1024TowerV3 = WithZero.exp s := hνV
        _ = WithZero.exp (-(((-s).toNat : ℕ) : ℤ)) := by
          congr 1
          rw [hcast]
          ring

/-- The actual direct-factor prime above `(X)` has positive ramification
index, bounded by the constructed total degree `1024` of the second tower
field. -/
private theorem f1024TowerF3InverseInfinityPlace_ramification_bounds
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF3)) :
    0 < (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal ∧
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal ≤ 1024 := by
  let oldRationalAlgebra : Algebra F1024TowerF1 F1024TowerF3 := inferInstance
  let oldFunctionField : _root_.FunctionField F1024 F1024TowerF3 := inferInstance
  let oldSeparable : Algebra.IsSeparable F1024TowerF1 F1024TowerF3 := inferInstance
  letI : Algebra F1024TowerF1 F1024TowerF3 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3
  letI : Algebra F1024[X] F1024TowerF3 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3
  letI : @IsScalarTower F1024[X] F1024TowerF1 F1024TowerF3
      RatFunc.instSMulOfFractionRingPolynomial
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3).toSMul
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3).toSMul :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3
  letI : _root_.FunctionField F1024 F1024TowerF3 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField)
      F1024 F1024TowerF3
  letI : Algebra.IsSeparable F1024TowerF1 F1024TowerF3 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
      F1024 F1024TowerF3
  let B : Type _ := _root_.FunctionField.ringOfIntegers F1024 F1024TowerF3
  letI : Module.IsTorsionFree F1024[X] B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective F1024 F1024TowerF3)
  letI : Module.Finite F1024[X] B :=
    QEC.Coding.AlgebraicGeometry.AffinePlace.finite_ringOfIntegers F1024 F1024TowerF3
  letI : NoZeroSMulDivisors F1024[X] B :=
    ⟨fun {c x} hzero =>
      (Module.isTorsionFree_iff_smul_eq_zero.mp
        (inferInstance : Module.IsTorsionFree F1024[X] B)) c x hzero⟩
  letI : ((Polynomial.idealX F1024).asIdeal).IsMaximal := by
    simpa using (Polynomial.idealX F1024).isMaximal
  let e := QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors
    (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3
  let Q := e P
  have hQ : (Q : Ideal B) = P.1.asIdeal := by
    dsimp only [Q, e]
    exact QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors_apply_asIdeal
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable)
      F1024 F1024TowerF3 P
  let E : ℕ :=
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
      P.1.asIdeal
  have hEeq : E = (Polynomial.idealX F1024).asIdeal.ramificationIdx' (Q : Ideal B) := by
    dsimp only [E, QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime]
    rw [← hQ]
  have hEpos : 0 < E := by
    rw [hEeq]
    exact Nat.pos_of_ne_zero
      (Ideal.Factors.ramificationIdx_ne_zero (Polynomial.idealX F1024).asIdeal Q)
  have hfinrank : Module.finrank F1024TowerF1 F1024TowerF3 = 1024 := by
    calc
      Module.finrank F1024TowerF1 F1024TowerF3 =
          (letI : Algebra F1024TowerF1 F1024TowerF3 := oldRationalAlgebra
           Module.finrank F1024TowerF1 F1024TowerF3) := by
        symm
        exact @Algebra.finrank_eq_of_equiv_equiv
          F1024TowerF1 F1024TowerF3 _ _ oldRationalAlgebra
          F1024TowerF1 F1024TowerF3 _ _
          (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
            (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3)
          (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024).symm.toRingEquiv
          (RingEquiv.refl F1024TowerF3) (by
            ext x
            change QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalMap
                (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3
                ((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024).symm x) =
              (@algebraMap F1024TowerF1 F1024TowerF3 _ _ oldRationalAlgebra) x
            change (@algebraMap F1024TowerF1 F1024TowerF3 _ _ oldRationalAlgebra)
                (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024
                  ((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024).symm x)) =
              (@algebraMap F1024TowerF1 F1024TowerF3 _ _ oldRationalAlgebra) x
            simp)
      _ = 1024 := f1024TowerF3_finrank_over_F1
  have hEbound : E ≤ 1024 := by
    rw [hEeq]
    calc
      (Polynomial.idealX F1024).asIdeal.ramificationIdx' (Q : Ideal B) ≤
          Module.finrank F1024TowerF1 F1024TowerF3 :=
        Ideal.ramificationIdx_le_finrank B F1024TowerF1 F1024TowerF3 (Q : Ideal B)
      _ = 1024 := hfinrank
  exact ⟨hEpos, hEbound⟩

/-- The two source inverse recurrences determine the local data at every
actual second-tower inverse-chart upper prime: total index `1024`, the
`x₂` pole order, and the inverse-root order. -/
private theorem f1024TowerF3InverseInfinityPlace_local_data
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF3)) :
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal = 1024 ∧
      f1024TowerF3InverseInfinityOrder P
        (algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2) = -32 ∧
      f1024TowerF3InverseInfinityOrder P f1024TowerV3 = 1 := by
  let E : ℕ :=
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
      P.1.asIdeal
  obtain ⟨hEpos, hEbound⟩ :=
    f1024TowerF3InverseInfinityPlace_ramification_bounds P
  have horderT : f1024TowerF3InverseInfinityOrder P f1024TowerF3T1 = (E : ℤ) := by
    change @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF3 _ _ _
        f1024TowerF3DirectConstantAlgebra
        (f1024TowerF3InverseInfinityPlace P) f1024TowerF3T1 = _
    rw [f1024TowerF3T1, f1024TowerT1_def, map_inv₀,
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order_inv F1024 F1024TowerF3 _ _ _
        f1024TowerF3DirectConstantAlgebra
        (f1024TowerF3InverseInfinityPlace P) _]
    change -f1024TowerF3InverseInfinityOrder P
      (algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX1) = (E : ℤ)
    rw [f1024TowerF3InverseInfinityPlace_order_x1]
    dsimp [E]
    ring
  let ν : Valuation F1024TowerF3 ℤᵐ⁰ :=
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024 F1024TowerF3 _ _ _
      f1024TowerF3DirectConstantAlgebra
      (f1024TowerF3InverseInfinityPlace P)
  have hlog : WithZero.log (ν f1024TowerF3T1) = -(E : ℤ) := by
    change -WithZero.log (ν f1024TowerF3T1) = (E : ℤ) at horderT
    omega
  have hνt : ν f1024TowerF3T1 = WithZero.exp (-(E : ℤ)) := by
    have ht0 : ν f1024TowerF3T1 ≠ 0 :=
      (Valuation.ne_zero_iff ν).mpr f1024TowerF3T1_ne_zero
    calc
      ν f1024TowerF3T1 = WithZero.exp (WithZero.log (ν f1024TowerF3T1)) :=
        (WithZero.exp_log ht0).symm
      _ = WithZero.exp (-(E : ℤ)) := by rw [hlog]
  obtain ⟨m, hEm, hνw⟩ :=
    f1024TowerF3W2_inverse_valuation_data ν E hEpos hνt
  have hmpos : 0 < m := by omega
  obtain ⟨n, hmn, hνV⟩ :=
    f1024TowerV3_inverse_valuation_data ν m hmpos hνw
  have hn : n = 1 := by omega
  have hm : m = 32 := by omega
  have hE : E = 1024 := by omega
  have hνw32 : ν f1024TowerF3W2 = WithZero.exp (-(32 : ℤ)) := by
    simpa [hm] using hνw
  have hνV1 : ν f1024TowerV3 = WithZero.exp (-(1 : ℤ)) := by
    simpa [hn] using hνV
  have horderW : f1024TowerF3InverseInfinityOrder P f1024TowerF3W2 = 32 := by
    change -WithZero.log (ν f1024TowerF3W2) = 32
    rw [hνw32]
    norm_num
  have horderX2 : f1024TowerF3InverseInfinityOrder P
      (algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2) = -32 := by
    calc
      f1024TowerF3InverseInfinityOrder P
          (algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2) =
          f1024TowerF3InverseInfinityOrder P f1024TowerF3W2⁻¹ := by
        rw [f1024TowerF3W2, f1024TowerW2_def, map_inv₀, inv_inv]
      _ = -f1024TowerF3InverseInfinityOrder P f1024TowerF3W2 :=
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.order_inv F1024 F1024TowerF3 _ _ _
          f1024TowerF3DirectConstantAlgebra
          (f1024TowerF3InverseInfinityPlace P) _
      _ = -32 := by rw [horderW]
  have horderV : f1024TowerF3InverseInfinityOrder P f1024TowerV3 = 1 := by
    change -WithZero.log (ν f1024TowerV3) = 1
    rw [hνV1]
    norm_num
  dsimp [E] at hE
  exact ⟨hE, horderX2, horderV⟩

/-- The second inverse recursion is totally ramified at every actual
inverse-chart upper prime of the constructed second tower field. -/
theorem f1024TowerF3InverseInfinityPlace_ramificationIdx_eq_1024
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF3)) :
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
      P.1.asIdeal = 1024 :=
  (f1024TowerF3InverseInfinityPlace_local_data P).1

/-- At every actual second-tower inverse-chart upper prime, the embedded
coordinate `x₂` has order `-32`. -/
theorem f1024TowerF3InverseInfinityPlace_order_x2
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF3)) :
    f1024TowerF3InverseInfinityOrder P
      (algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2) = -32 :=
  (f1024TowerF3InverseInfinityPlace_local_data P).2.1

private theorem f1024TowerX3_eq_V3_inv : f1024TowerX3 = f1024TowerV3⁻¹ := by
  let u : F1024TowerF3 := algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2
  have hu : u ≠ 0 := by
    dsimp [u]
    exact f1024TowerF3_x2_ne_zero
  change (u / f1024TowerV3) / u = f1024TowerV3⁻¹
  calc
    (u / f1024TowerV3) / u = u / (f1024TowerV3 * u) := by rw [div_div]
    _ = u / (u * f1024TowerV3) := by rw [mul_comm]
    _ = (u / u) / f1024TowerV3 := by rw [div_div]
    _ = f1024TowerV3⁻¹ := by rw [div_self hu, one_div]

/-- At every actual second-tower inverse-chart upper prime, the next source
coordinate `x₃` has a simple pole. -/
theorem f1024TowerF3InverseInfinityPlace_order_x3
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF3)) :
    f1024TowerF3InverseInfinityOrder P f1024TowerX3 = -1 := by
  rw [f1024TowerX3_eq_V3_inv]
  change @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF3 _ _ _
      f1024TowerF3DirectConstantAlgebra
      (f1024TowerF3InverseInfinityPlace P) f1024TowerV3⁻¹ = -1
  rw [
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.order_inv F1024 F1024TowerF3 _ _ _
      f1024TowerF3DirectConstantAlgebra
      (f1024TowerF3InverseInfinityPlace P) _]
  change -f1024TowerF3InverseInfinityOrder P f1024TowerV3 = -1
  have horderV : f1024TowerF3InverseInfinityOrder P f1024TowerV3 = 1 :=
    (f1024TowerF3InverseInfinityPlace_local_data P).2.2
  rw [horderV]

/-! ## The actual indexed Garcia--Stichtenoth tower -/

/-- The private recursion carrier for the actual indexed tower.  Its fields
are only constructed algebraic data: the field, its direct coordinate maps,
the finite inverse-coordinate chain, and the degree calculation.  In
particular it stores no place, genus, rational-place count, or asymptotic
conclusion. -/
private structure F1024TowerStageData (height : ℕ) where
  carrier : Type
  [fieldInst : Field carrier]
  [rationalAlgebraInst : Algebra F1024TowerF1 carrier]
  [finiteDimensionalInst : FiniteDimensional F1024TowerF1 carrier]
  [separableInst : Algebra.IsSeparable F1024TowerF1 carrier]
  [constantAlgebraInst : Algebra F1024 carrier]
  [constantRationalTowerInst : IsScalarTower F1024 F1024TowerF1 carrier]
  [polynomialAlgebraInst : Algebra F1024[X] carrier]
  [polynomialRationalTowerInst : IsScalarTower F1024[X] F1024TowerF1 carrier]
  [charTwoInst : CharP carrier 2]
  x : carrier
  x_ne_zero : x ≠ 0
  inverseCoordinate : ℕ → carrier
  inverseCoordinate_zero :
    inverseCoordinate 0 = (algebraMap F1024TowerF1 carrier RatFunc.X)⁻¹
  inverseCoordinate_current : inverseCoordinate height = x⁻¹
  inverseCoordinate_ne_zero : ∀ i, inverseCoordinate i ≠ 0
  inverseCoordinate_recurrence : ∀ i, i < height →
    inverseCoordinate (i + 1) ^ 32 +
      inverseCoordinate i ^ 32 * inverseCoordinate (i + 1) ^ 31 =
        inverseCoordinate i
  finrank_eq : Module.finrank F1024TowerF1 carrier = 32 ^ height

attribute [instance] F1024TowerStageData.fieldInst
  F1024TowerStageData.rationalAlgebraInst
  F1024TowerStageData.finiteDimensionalInst
  F1024TowerStageData.separableInst
  F1024TowerStageData.constantAlgebraInst
  F1024TowerStageData.constantRationalTowerInst
  F1024TowerStageData.polynomialAlgebraInst
  F1024TowerStageData.polynomialRationalTowerInst
  F1024TowerStageData.charTwoInst

/-- Height zero is the actual rational function field with coordinate `x₁`.
The inverse-coordinate chain has only its required zeroth value. -/
private noncomputable def f1024TowerStageBase : F1024TowerStageData 0 where
  carrier := F1024TowerF1
  fieldInst := inferInstance
  rationalAlgebraInst := inferInstance
  finiteDimensionalInst := inferInstance
  separableInst := inferInstance
  constantAlgebraInst := inferInstance
  constantRationalTowerInst := inferInstance
  polynomialAlgebraInst := inferInstance
  polynomialRationalTowerInst := inferInstance
  charTwoInst := charP_of_injective_algebraMap
    (algebraMap F1024 F1024TowerF1).injective 2
  x := RatFunc.X
  x_ne_zero := RatFunc.X_ne_zero
  inverseCoordinate := fun _ => (RatFunc.X : F1024TowerF1)⁻¹
  inverseCoordinate_zero := rfl
  inverseCoordinate_current := rfl
  inverseCoordinate_ne_zero := fun _ => inv_ne_zero RatFunc.X_ne_zero
  inverseCoordinate_recurrence := by omega
  finrank_eq := by simp

/-- The actual normalized valuation attached to a genuine raw inverse-chart
upper prime of a constructed stage. -/
private noncomputable def f1024TowerStageInverseValuation
    {height : ℕ} (stage : F1024TowerStageData height)
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := stage.carrier)) :
    Valuation stage.carrier ℤᵐ⁰ := by
  let oldRationalAlgebra : Algebra F1024TowerF1 stage.carrier := inferInstance
  let oldFunctionField : _root_.FunctionField F1024 stage.carrier := inferInstance
  let oldSeparable : Algebra.IsSeparable F1024TowerF1 stage.carrier := inferInstance
  letI : Algebra F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : Algebra F1024[X] stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : IsScalarTower F1024[X] F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : _root_.FunctionField F1024 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField) F1024 stage.carrier
  letI : Algebra.IsSeparable F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
      F1024 stage.carrier
  exact QEC.Coding.AlgebraicGeometry.AffinePlace.valuation
    F1024 stage.carrier P.1

/-- The normalized valuation of a raw inverse-chart upper prime is
surjective.  This is inherited from the actual height-one-prime adic
valuation. -/
private theorem f1024TowerStageInverseValuation_surjective
    {height : ℕ} (stage : F1024TowerStageData height)
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := stage.carrier)) :
    Function.Surjective (f1024TowerStageInverseValuation stage P) := by
  let oldRationalAlgebra : Algebra F1024TowerF1 stage.carrier := inferInstance
  let oldFunctionField : _root_.FunctionField F1024 stage.carrier := inferInstance
  let oldSeparable : Algebra.IsSeparable F1024TowerF1 stage.carrier := inferInstance
  letI : Algebra F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : Algebra F1024[X] stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : IsScalarTower F1024[X] F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : _root_.FunctionField F1024 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField) F1024 stage.carrier
  letI : Algebra.IsSeparable F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
      F1024 stage.carrier
  change Function.Surjective
    (QEC.Coding.AlgebraicGeometry.AffinePlace.valuation
      F1024 stage.carrier P.1)
  exact P.1.valuation_surjective stage.carrier

/-- Order at an actual inverse-chart upper prime, expressed directly through
its normalized adic valuation. -/
private noncomputable def f1024TowerStageInverseOrder
    {height : ℕ} (stage : F1024TowerStageData height)
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := stage.carrier)) (u : stage.carrier) : ℤ :=
  -WithZero.log (f1024TowerStageInverseValuation stage P u)

/-- Lying-over supplies a genuine inverse-chart upper prime for every
constructed stage. -/
private theorem f1024TowerStage_inverseInfinityFibre_nonempty
    {height : ℕ} (stage : F1024TowerStageData height) :
    Nonempty (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := stage.carrier)) := by
  exact QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre_nonempty
    (k := F1024) (F := stage.carrier)

/-- The zeroth inverse coordinate has order equal to the actual
ramification index above the inverse base prime. -/
private theorem f1024TowerStageInversePlace_order_inverseCoordinate_zero
    {height : ℕ} (stage : F1024TowerStageData height)
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := stage.carrier)) :
    f1024TowerStageInverseOrder stage P (stage.inverseCoordinate 0) =
      ((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal : ℤ) := by
  let oldRationalAlgebra : Algebra F1024TowerF1 stage.carrier := inferInstance
  let oldFunctionField : _root_.FunctionField F1024 stage.carrier := inferInstance
  let oldSeparable : Algebra.IsSeparable F1024TowerF1 stage.carrier := inferInstance
  letI : Algebra F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : Algebra F1024[X] stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : IsScalarTower F1024[X] F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : _root_.FunctionField F1024 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField) F1024 stage.carrier
  letI : Algebra.IsSeparable F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
      F1024 stage.carrier
  let B : Type _ := _root_.FunctionField.ringOfIntegers F1024 stage.carrier
  letI : Module.IsTorsionFree F1024[X] B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective F1024 stage.carrier)
  let x : B := algebraMap F1024[X] B Polynomial.X
  have hx : x ≠ 0 := by
    simpa only [x, map_zero] using
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective F1024 stage.carrier).ne
        (Polynomial.X_ne_zero : (Polynomial.X : F1024[X]) ≠ 0)
  have htransportX : algebraMap F1024[X] stage.carrier Polynomial.X =
      stage.inverseCoordinate 0 := by
    rw [stage.inverseCoordinate_zero]
    change (@algebraMap F1024TowerF1 stage.carrier _ _ oldRationalAlgebra)
        (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024
          RatFunc.X) =
      ((@algebraMap F1024TowerF1 stage.carrier _ _ oldRationalAlgebra) RatFunc.X)⁻¹
    rw [QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution_X, map_inv₀]
  have hspan : Ideal.span ({x} : Set B) =
      Ideal.map (algebraMap F1024[X] B)
        (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024) := by
    dsimp only [x]
    calc
      Ideal.span ({algebraMap F1024[X] B Polynomial.X} : Set B) =
          Ideal.map (algebraMap F1024[X] B)
            (Ideal.span ({Polynomial.X} : Set F1024[X])) := by
        rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.map (algebraMap F1024[X] B)
          (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024) := by
        rw [QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime,
          Polynomial.idealX_span]
  have hmap : Ideal.map (algebraMap F1024[X] B)
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime_ne_zero F1024)
  have horder :=
    QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace_order_of_integral_eq_multiplicity
      F1024 stage.carrier P.1 hx
  change -WithZero.log
      (QEC.Coding.AlgebraicGeometry.AffinePlace.valuation F1024 stage.carrier P.1
        (algebraMap B stage.carrier x)) =
      (multiplicity P.1.asIdeal (Ideal.span {x}) : ℤ) at horder
  rw [← IsScalarTower.algebraMap_apply F1024[X] B stage.carrier, htransportX] at horder
  calc
    f1024TowerStageInverseOrder stage P (stage.inverseCoordinate 0) =
        (multiplicity P.1.asIdeal (Ideal.span {x}) : ℤ) := horder
    _ = ((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal : ℤ) := by
      rw [hspan]
      exact_mod_cast
        (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hmap P.1.isPrime).symm

/-- The actual inverse-base ramification index is positive and bounded by
the constructed total extension degree. -/
private theorem f1024TowerStageInversePlace_ramification_bounds
    {height : ℕ} (stage : F1024TowerStageData height)
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := stage.carrier)) :
    0 < (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal ∧
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal ≤ 32 ^ height := by
  let oldRationalAlgebra : Algebra F1024TowerF1 stage.carrier := inferInstance
  let oldFunctionField : _root_.FunctionField F1024 stage.carrier := inferInstance
  let oldSeparable : Algebra.IsSeparable F1024TowerF1 stage.carrier := inferInstance
  letI : Algebra F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : Algebra F1024[X] stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : IsScalarTower F1024[X] F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : _root_.FunctionField F1024 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField) F1024 stage.carrier
  letI : Algebra.IsSeparable F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
      F1024 stage.carrier
  let B : Type _ := _root_.FunctionField.ringOfIntegers F1024 stage.carrier
  letI : Module.IsTorsionFree F1024[X] B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective F1024 stage.carrier)
  letI : Module.Finite F1024[X] B :=
    QEC.Coding.AlgebraicGeometry.AffinePlace.finite_ringOfIntegers
      F1024 stage.carrier
  letI : NoZeroSMulDivisors F1024[X] B :=
    ⟨fun {c x} hzero =>
      (Module.isTorsionFree_iff_smul_eq_zero.mp
        (inferInstance : Module.IsTorsionFree F1024[X] B)) c x hzero⟩
  letI : ((Polynomial.idealX F1024).asIdeal).IsMaximal := by
    simpa using (Polynomial.idealX F1024).isMaximal
  have hmap : Ideal.map (algebraMap F1024[X] B)
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime_ne_zero F1024)
  have hle : Ideal.map (algebraMap F1024[X] B)
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024) ≤
        P.1.asIdeal := Ideal.dvd_iff_le.mp P.2
  letI : P.1.asIdeal.LiesOver
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024) :=
    (Ideal.liesOver_iff_dvd_map P.1.isPrime.ne_top).mpr P.2
  have hpos : 0 <
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal := Nat.pos_of_ne_zero
    (Ideal.IsDedekindDomain.ramificationIdx_ne_zero hmap P.1.isPrime hle)
  have hfinrank : Module.finrank F1024TowerF1 stage.carrier = 32 ^ height := by
    calc
      Module.finrank F1024TowerF1 stage.carrier =
          (letI : Algebra F1024TowerF1 stage.carrier := oldRationalAlgebra
           Module.finrank F1024TowerF1 stage.carrier) := by
        symm
        exact @Algebra.finrank_eq_of_equiv_equiv
          F1024TowerF1 stage.carrier _ _ oldRationalAlgebra
          F1024TowerF1 stage.carrier _ _
          (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
            (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier)
          (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024).symm.toRingEquiv
          (RingEquiv.refl stage.carrier) (by
            ext u
            change QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalMap
                (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
                ((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024).symm u) =
              (@algebraMap F1024TowerF1 stage.carrier _ _ oldRationalAlgebra) u
            change (@algebraMap F1024TowerF1 stage.carrier _ _ oldRationalAlgebra)
                (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024
                  ((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024).symm u)) =
              (@algebraMap F1024TowerF1 stage.carrier _ _ oldRationalAlgebra) u
            simp)
      _ = 32 ^ height := stage.finrank_eq
  refine ⟨hpos, ?_⟩
  calc
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal ≤ Module.finrank F1024TowerF1 stage.carrier :=
      Ideal.ramificationIdx_le_finrank B F1024TowerF1 stage.carrier P.1.asIdeal
    _ = 32 ^ height := hfinrank

/-- One inverse Garcia--Stichtenoth recurrence divides a positive valuation
exponent by exactly `32`.  This is the reusable local calculation used along
the finite coordinate chain of a constructed stage. -/
private theorem f1024Tower_inverseRecurrence_valuation_data
    {F : Type*} [Field F] (ν : Valuation F ℤᵐ⁰)
    {u v : F} (hv : v ≠ 0)
    (hrec : v ^ 32 + u ^ 32 * v ^ 31 = u)
    (E : ℕ) (hEpos : 0 < E)
    (hνu : ν u = WithZero.exp (-(E : ℤ))) :
    ∃ m : ℕ, E = 32 * m ∧ ν v = WithZero.exp (-(m : ℤ)) := by
  have hv0 : ν v ≠ 0 := (Valuation.ne_zero_iff ν).mpr hv
  let r : ℤ := WithZero.log (ν v)
  have hνv : ν v = WithZero.exp r := by
    dsimp only [r]
    exact (WithZero.exp_log hv0).symm
  have hνv32 : ν (v ^ 32) = WithZero.exp ((32 : ℕ) • r) := by
    rw [map_pow, hνv, ← WithZero.exp_nsmul]
  have hνuv : ν (u ^ 32 * v ^ 31) =
      WithZero.exp ((32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r) := by
    rw [map_mul, map_pow, map_pow, hνu, hνv,
      ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add]
  have hνsum : ν (v ^ 32 + u ^ 32 * v ^ 31) =
      WithZero.exp (-(E : ℤ)) := by
    rw [hrec, hνu]
  rcases lt_trichotomy (ν (v ^ 32)) (ν (u ^ 32 * v ^ 31)) with hlt | heq | hgt
  · have hsum : ν (v ^ 32 + u ^ 32 * v ^ 31) = ν (u ^ 32 * v ^ 31) := by
      rw [Valuation.map_add_eq_of_lt_right ν hlt]
    rw [hsum, hνuv] at hνsum
    have hEq : (32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r = -(E : ℤ) :=
      WithZero.exp_inj.mp hνsum
    have hltExp : (32 : ℕ) • r <
        (32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r := by
      rw [← f1024Tower_exp_lt_exp, ← hνv32, ← hνuv]
      exact hlt
    simp only [nsmul_eq_mul] at hEq hltExp
    omega
  · have hsame : WithZero.exp ((32 : ℕ) • r) =
        WithZero.exp ((32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r) := by
      rw [← hνv32, ← hνuv]
      exact heq
    have hEq : (32 : ℕ) • r =
        (32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r :=
      WithZero.exp_inj.mp hsame
    have hsumle : ν (v ^ 32 + u ^ 32 * v ^ 31) ≤ ν (v ^ 32) :=
      (map_add_le_max ν _ _).trans_eq (by rw [← heq, max_self])
    rw [hνsum, hνv32] at hsumle
    have hsmall : (32 : ℕ) • r < -(E : ℤ) := by
      have hEq' : (32 : ℤ) * r =
          (32 : ℤ) * (-(E : ℤ)) + (31 : ℤ) * r := by
        have hport := hEq
        simp only [nsmul_eq_mul] at hport ⊢
        exact hport
      have hsmall' : (32 : ℤ) * r < -(E : ℤ) := by omega
      have hport := hsmall'
      simp only [nsmul_eq_mul] at hport ⊢
      exact hport
    exfalso
    exact (not_lt_of_ge hsumle) (f1024Tower_exp_lt_exp.mpr hsmall)
  · have hsum : ν (v ^ 32 + u ^ 32 * v ^ 31) = ν (v ^ 32) := by
      rw [Valuation.map_add_eq_of_lt_left ν hgt]
    rw [hsum, hνv32] at hνsum
    have hEq : (32 : ℕ) • r = -(E : ℤ) := WithZero.exp_inj.mp hνsum
    have hrneg : r < 0 := by
      rw [nsmul_eq_mul] at hEq
      omega
    have hnonneg : 0 ≤ -r := by omega
    rw [nsmul_eq_mul] at hEq
    have hEq' : (E : ℤ) = 32 * (-r) := by omega
    have hcast : (((-r).toNat : ℕ) : ℤ) = -r :=
      Int.toNat_of_nonneg hnonneg
    have hEq'' : (E : ℤ) = (32 : ℤ) * (((-r).toNat : ℕ) : ℤ) := by
      rw [hcast]
      exact hEq'
    refine ⟨(-r).toNat, ?_, ?_⟩
    · exact_mod_cast hEq''
    · calc
        ν v = WithZero.exp r := hνv
        _ = WithZero.exp (-(((-r).toNat : ℕ) : ℤ)) := by
          congr 1
          rw [hcast]
          ring

/-- Iterating the actual inverse-coordinate recurrences divides the base
ramification exponent by `32` once per constructed level. -/
private theorem f1024TowerStage_inverseCoordinate_valuation_data
    {height : ℕ} (stage : F1024TowerStageData height)
    (ν : Valuation stage.carrier ℤᵐ⁰) (E : ℕ) (hEpos : 0 < E)
    (hνzero : ν (stage.inverseCoordinate 0) = WithZero.exp (-(E : ℤ))) :
    ∃ m : ℕ, E = 32 ^ height * m ∧
      ν (stage.inverseCoordinate height) = WithZero.exp (-(m : ℤ)) := by
  have hprefix : ∀ j : ℕ, j ≤ height →
      ∃ m : ℕ, E = 32 ^ j * m ∧
        ν (stage.inverseCoordinate j) = WithZero.exp (-(m : ℤ)) := by
    intro j hj
    induction j with
    | zero =>
        exact ⟨E, by simp, hνzero⟩
    | succ j ih =>
        have hjle : j ≤ height := Nat.le_trans (Nat.le_succ j) hj
        obtain ⟨m, hEm, hνm⟩ := ih hjle
        have hmpos : 0 < m := by
          by_contra hm
          have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm
          subst m
          simp at hEm
          omega
        obtain ⟨n, hmn, hνn⟩ :=
          f1024Tower_inverseRecurrence_valuation_data ν
            (stage.inverseCoordinate_ne_zero (j + 1))
            (stage.inverseCoordinate_recurrence j (Nat.lt_of_succ_le hj))
            m hmpos hνm
        refine ⟨n, ?_, hνn⟩
        calc
          E = 32 ^ j * m := hEm
          _ = 32 ^ (j + 1) * n := by rw [hmn, pow_succ]; ring
  exact hprefix height (le_refl height)

/-- Every actual inverse-chart upper prime of a constructed stage sees the
current source coordinate with a simple pole.  Total ramification is derived
from the recurrence chain and the finite degree bound; it is not stored in
the recursive carrier. -/
private theorem f1024TowerStageInversePlace_order_x
    {height : ℕ} (stage : F1024TowerStageData height)
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := stage.carrier)) :
    f1024TowerStageInverseOrder stage P stage.x = -1 := by
  let E : ℕ :=
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
      P.1.asIdeal
  obtain ⟨hEpos, hEbound⟩ :=
    f1024TowerStageInversePlace_ramification_bounds stage P
  let ν : Valuation stage.carrier ℤᵐ⁰ :=
    f1024TowerStageInverseValuation stage P
  have horderZero :
      f1024TowerStageInverseOrder stage P (stage.inverseCoordinate 0) = (E : ℤ) := by
    exact f1024TowerStageInversePlace_order_inverseCoordinate_zero stage P
  have hlogZero : WithZero.log (ν (stage.inverseCoordinate 0)) = -(E : ℤ) := by
    change -WithZero.log (ν (stage.inverseCoordinate 0)) = (E : ℤ) at horderZero
    omega
  have hνzero : ν (stage.inverseCoordinate 0) = WithZero.exp (-(E : ℤ)) := by
    have hzero : ν (stage.inverseCoordinate 0) ≠ 0 :=
      (Valuation.ne_zero_iff ν).mpr (stage.inverseCoordinate_ne_zero 0)
    calc
      ν (stage.inverseCoordinate 0) =
          WithZero.exp (WithZero.log (ν (stage.inverseCoordinate 0))) :=
        (WithZero.exp_log hzero).symm
      _ = WithZero.exp (-(E : ℤ)) := by rw [hlogZero]
  obtain ⟨m, hEm, hνcurrent⟩ :=
    f1024TowerStage_inverseCoordinate_valuation_data stage ν E hEpos hνzero
  have hpowpos : 0 < 32 ^ height := pow_pos (by norm_num) height
  have hmpos : 0 < m := by
    by_contra hm
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    simp at hEm
    omega
  have hmle : m ≤ 1 := by
    have hmul : 32 ^ height * m ≤ 32 ^ height * 1 := by
      calc
        32 ^ height * m = E := hEm.symm
        _ ≤ 32 ^ height := by simpa only [E] using hEbound
        _ = 32 ^ height * 1 := (mul_one _).symm
    apply Nat.le_of_mul_le_mul_left
    · exact hmul
    · exact hpowpos
  have hm : m = 1 := by omega
  have horderInv :
      -WithZero.log (ν stage.x⁻¹) = 1 := by
    rw [← stage.inverseCoordinate_current, hνcurrent, hm]
    norm_num
  change -WithZero.log (ν stage.x) = -1
  rw [map_inv₀, WithZero.log_inv] at horderInv
  omega

/-- The inverse-coordinate polynomial defining the successor of an arbitrary
constructed stage. -/
private noncomputable def f1024TowerStageStepPolynomial
    {height : ℕ} (stage : F1024TowerStageData height) : stage.carrier[X] :=
  X ^ 32 + C (stage.x⁻¹ ^ 32) * X ^ 31 - C stage.x⁻¹

private theorem f1024TowerStageStepPolynomial_monic
    {height : ℕ} (stage : F1024TowerStageData height) :
    (f1024TowerStageStepPolynomial stage).Monic := by
  rw [f1024TowerStageStepPolynomial, add_sub_assoc]
  apply monic_X_pow_add
  calc
    degree (C (stage.x⁻¹ ^ 32) * X ^ 31 - C stage.x⁻¹) ≤
        max (degree (C (stage.x⁻¹ ^ 32) * X ^ 31)) (degree (C stage.x⁻¹)) :=
      degree_sub_le _ _
    _ ≤ (31 : WithBot ℕ) := by
      apply max_le
      · exact degree_C_mul_X_pow_le 31 (stage.x⁻¹ ^ 32)
      · exact degree_C_le.trans (by norm_num)
    _ < (32 : ℕ) := by norm_num

private theorem f1024TowerStageStepPolynomial_natDegree
    {height : ℕ} (stage : F1024TowerStageData height) :
    (f1024TowerStageStepPolynomial stage).natDegree = 32 := by
  have hwPow : stage.x⁻¹ ^ 32 ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero stage.x_ne_zero)
  calc
    (f1024TowerStageStepPolynomial stage).natDegree =
        (X ^ 32 + C (stage.x⁻¹ ^ 32) * X ^ 31 : stage.carrier[X]).natDegree := by
      rw [f1024TowerStageStepPolynomial, natDegree_sub_C]
    _ = (X ^ 32 : stage.carrier[X]).natDegree :=
      natDegree_add_eq_left_of_natDegree_lt (by
        rw [natDegree_C_mul_X_pow 31 (stage.x⁻¹ ^ 32) hwPow, natDegree_X_pow]
        norm_num)
    _ = 32 := natDegree_X_pow 32

/-- The successor inverse polynomial is Eisenstein at any actual inverse
infinity prime of the current stage.  The required uniformizer is derived
from the simple-pole theorem above. -/
private theorem f1024TowerStageStepPolynomial_irreducible
    {height : ℕ} (stage : F1024TowerStageData height) :
    Irreducible (f1024TowerStageStepPolynomial stage) := by
  rcases f1024TowerStage_inverseInfinityFibre_nonempty stage with ⟨P⟩
  let ν : Valuation stage.carrier ℤᵐ⁰ :=
    f1024TowerStageInverseValuation stage P
  have hνsurj : Function.Surjective ν :=
    f1024TowerStageInverseValuation_surjective stage P
  let w : stage.carrier := stage.x⁻¹
  have hw_ne : w ≠ 0 := inv_ne_zero stage.x_ne_zero
  have horderX : f1024TowerStageInverseOrder stage P stage.x = -1 :=
    f1024TowerStageInversePlace_order_x stage P
  have horderW : -WithZero.log (ν w) = 1 := by
    change -WithZero.log (ν stage.x⁻¹) = 1
    rw [map_inv₀, WithZero.log_inv]
    change -WithZero.log (ν stage.x) = -1 at horderX
    omega
  have hlog : WithZero.log (ν w) = -(1 : ℤ) := by omega
  have hνw : ν w = WithZero.exp (-(1 : ℤ)) := by
    have hw0 : ν w ≠ 0 := (Valuation.ne_zero_iff ν).mpr hw_ne
    calc
      ν w = WithZero.exp (WithZero.log (ν w)) := (WithZero.exp_log hw0).symm
      _ = WithZero.exp (-(1 : ℤ)) := by rw [hlog]
  letI : ν.IsNontrivial := by
    rw [Valuation.isNontrivial_iff_exists_lt_one]
    refine ⟨w, hw_ne, ?_⟩
    rw [hνw, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  letI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass ν)) := inferInstance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass ν)) := inferInstance
  letI : ν.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' ν
  let wIntegral : ν.valuationSubring :=
    ⟨w, (ν.mem_valuationSubring_iff _).mpr (by
      rw [hνw, ← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega))⟩
  have hwIntegral_ne : wIntegral ≠ 0 := by
    intro hw
    apply hw_ne
    simpa [wIntegral] using
      congrArg (fun a : ν.valuationSubring => (a : stage.carrier)) hw
  have hwUniform : ν.IsUniformizer (wIntegral : stage.carrier) := by
    change ν w = (Valuation.IsRankOneDiscrete.generator ν : ℤᵐ⁰)
    calc
      ν w = WithZero.exp (-(1 : ℤ)) := hνw
      _ = (Valuation.IsRankOneDiscrete.generator ν : ℤᵐ⁰) := by
        simpa using congrArg (fun u : ℤᵐ⁰ˣ => (u : ℤᵐ⁰))
          (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
            (v := ν) hνsurj).symm
  let m : Ideal ν.valuationSubring := IsLocalRing.maximalIdeal ν.valuationSubring
  have hmprime : m.IsPrime := by
    dsimp [m]
    exact (IsLocalRing.maximalIdeal.isMaximal ν.valuationSubring).isPrime
  have hwM : wIntegral ∈ m := by
    dsimp [m]
    rw [Valuation.mem_maximalIdeal_iff]
    change ν w < 1
    rw [hνw, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hmgen : m = Ideal.span ({wIntegral} : Set ν.valuationSubring) := by
    dsimp [m]
    exact Valuation.IsUniformizer.is_generator (π := wIntegral) hwUniform
  let g : ν.valuationSubring[X] :=
    X ^ 32 + C (wIntegral ^ 32) * X ^ 31 - C wIntegral
  have hwPow : wIntegral ^ 32 ≠ 0 := pow_ne_zero _ hwIntegral_ne
  have hgNatDegree : g.natDegree = 32 := by
    calc
      g.natDegree =
          (X ^ 32 + C (wIntegral ^ 32) * X ^ 31 : ν.valuationSubring[X]).natDegree := by
        dsimp only [g]
        rw [natDegree_sub_C]
      _ = (X ^ 32 : ν.valuationSubring[X]).natDegree :=
        natDegree_add_eq_left_of_natDegree_lt (by
          rw [natDegree_C_mul_X_pow 31 (wIntegral ^ 32) hwPow, natDegree_X_pow]
          norm_num)
      _ = 32 := natDegree_X_pow 32
  have hgMonic : g.Monic := by
    dsimp only [g]
    rw [add_sub_assoc]
    apply monic_X_pow_add
    calc
      degree (C (wIntegral ^ 32) * X ^ 31 - C wIntegral) ≤
          max (degree (C (wIntegral ^ 32) * X ^ 31)) (degree (C wIntegral)) :=
        degree_sub_le _ _
      _ ≤ (31 : WithBot ℕ) := by
        apply max_le
        · exact degree_C_mul_X_pow_le 31 (wIntegral ^ 32)
        · exact degree_C_le.trans (by norm_num)
      _ < (32 : ℕ) := by norm_num
  have hcoeff : ∀ {n : ℕ}, n < g.natDegree → g.coeff n ∈ m := by
    intro n hn
    rw [hgNatDegree] at hn
    by_cases hn0 : n = 0
    · subst n
      have hcoeff0 : g.coeff 0 = -wIntegral := by
        simp only [g, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C,
          if_neg (by norm_num : (0 : ℕ) ≠ 32),
          if_neg (by norm_num : (0 : ℕ) ≠ 31), ite_true, zero_add, zero_sub]
      rw [hcoeff0]
      exact m.neg_mem hwM
    · by_cases hn31 : n = 31
      · subst n
        have hcoeff31 : g.coeff 31 = wIntegral ^ 32 := by
          simp only [g, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C,
            if_neg (by norm_num : (31 : ℕ) ≠ 32), ite_true,
            if_neg (by norm_num : (31 : ℕ) ≠ 0), zero_add, sub_zero]
        rw [hcoeff31]
        exact m.pow_mem_of_mem hwM 32 (by norm_num)
      · have hn32 : n ≠ 32 := Nat.ne_of_lt hn
        have hzero : g.coeff n = 0 := by
          simp only [g, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C,
            if_neg hn32, if_neg hn31, if_neg hn0, zero_add, sub_zero]
        rw [hzero]
        exact m.zero_mem
  have hconstant : g.coeff 0 ∉ m ^ 2 := by
    have hcoeff0 : g.coeff 0 = -wIntegral := by
      simp only [g, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C,
        if_neg (by norm_num : (0 : ℕ) ≠ 32),
        if_neg (by norm_num : (0 : ℕ) ≠ 31), ite_true, zero_add, zero_sub]
    rw [hcoeff0]
    intro hneg
    have hwSq : wIntegral ∈ m ^ 2 := by
      simpa using (m ^ 2).neg_mem hneg
    rw [hmgen, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hwSq
    obtain ⟨a, ha⟩ := hwSq
    have hwUnit : IsUnit wIntegral := by
      rw [isUnit_iff_exists_inv]
      refine ⟨a, ?_⟩
      exact mul_left_cancel₀ hwIntegral_ne (by
        calc
          wIntegral * (wIntegral * a) = wIntegral ^ 2 * a := by ring
          _ = wIntegral := ha.symm
          _ = wIntegral * 1 := (mul_one wIntegral).symm)
    exact hmprime.ne_top (Ideal.eq_top_of_isUnit_mem m hwM hwUnit)
  have hEisenstein : g.IsEisensteinAt m :=
    hgMonic.isEisensteinAt_of_mem_of_notMem hmprime.ne_top hcoeff hconstant
  have hIrreducible : Irreducible g :=
    hEisenstein.irreducible hmprime hgMonic.isPrimitive (by
      rw [hgNatDegree]
      norm_num)
  have hMapped : Irreducible (g.map (algebraMap ν.valuationSubring stage.carrier)) :=
    (hgMonic.irreducible_iff_irreducible_map_fraction_map
      (K := stage.carrier)).mp hIrreducible
  simpa [g, wIntegral, w, f1024TowerStageStepPolynomial] using hMapped

private noncomputable instance f1024TowerStageStepIrreducibleFact
    {height : ℕ} (stage : F1024TowerStageData height) :
    Fact (Irreducible (f1024TowerStageStepPolynomial stage)) :=
  ⟨f1024TowerStageStepPolynomial_irreducible stage⟩

/-- The actual successor field of a constructed stage. -/
private noncomputable abbrev F1024TowerStageStep
    {height : ℕ} (stage : F1024TowerStageData height) : Type :=
  AdjoinRoot (f1024TowerStageStepPolynomial stage)

private noncomputable instance f1024TowerStageStepFiniteDimensional
    {height : ℕ} (stage : F1024TowerStageData height) :
    FiniteDimensional stage.carrier (F1024TowerStageStep stage) :=
  (AdjoinRoot.powerBasis'
    (f1024TowerStageStepPolynomial_monic stage)).basis.finiteDimensional_of_finite

private theorem f1024TowerStageStep_finrank
    {height : ℕ} (stage : F1024TowerStageData height) :
    Module.finrank stage.carrier (F1024TowerStageStep stage) = 32 := by
  simpa [F1024TowerStageStep, f1024TowerStageStepPolynomial_natDegree stage] using
    (AdjoinRoot.powerBasis' (f1024TowerStageStepPolynomial_monic stage)).finrank

private theorem f1024TowerStageStepPolynomial_derivative
    {height : ℕ} (stage : F1024TowerStageData height) :
    derivative (f1024TowerStageStepPolynomial stage) =
      C (stage.x⁻¹ ^ 32 * ((31 : ℕ) : stage.carrier)) * X ^ 30 := by
  have h32 : ((32 : ℕ) : stage.carrier) = 0 := by
    rw [CharP.cast_eq_zero_iff stage.carrier 2]
    norm_num
  simp only [f1024TowerStageStepPolynomial, derivative_sub, derivative_add,
    derivative_X_pow, derivative_C_mul_X_pow, derivative_C, h32, C_0, zero_mul,
    zero_add, Nat.reduceSub, sub_zero]

private theorem f1024TowerStageStepPolynomial_separable
    {height : ℕ} (stage : F1024TowerStageData height) :
    (f1024TowerStageStepPolynomial stage).Separable := by
  rw [separable_iff_derivative_ne_zero
    (f1024TowerStageStepPolynomial_irreducible stage)]
  rw [f1024TowerStageStepPolynomial_derivative]
  apply mul_ne_zero
  · apply C_ne_zero.mpr
    apply mul_ne_zero
    · exact pow_ne_zero _ (inv_ne_zero stage.x_ne_zero)
    · intro h31
      have hdiv : 2 ∣ 31 :=
        (CharP.cast_eq_zero_iff stage.carrier 2 31).mp h31
      norm_num at hdiv
  · exact pow_ne_zero _ Polynomial.X_ne_zero

private noncomputable instance f1024TowerStageStepSeparable
    {height : ℕ} (stage : F1024TowerStageData height) :
    Algebra.IsSeparable stage.carrier (F1024TowerStageStep stage) := by
  rw [← AlgEquiv.Algebra.isSeparable_iff <|
    (IntermediateField.equivOfEq
      (IntermediateField.adjoin_root_eq_top
        (f1024TowerStageStepPolynomial stage))).trans IntermediateField.topEquiv,
    IntermediateField.isSeparable_adjoin_simple_iff_isSeparable,
    IsSeparable,
    AdjoinRoot.minpoly_root (f1024TowerStageStepPolynomial_monic stage).ne_zero,
    (f1024TowerStageStepPolynomial_monic stage).leadingCoeff,
    inv_one, C.map_one, mul_one]
  exact f1024TowerStageStepPolynomial_separable stage

private noncomputable instance f1024TowerStageStepFiniteDimensionalOverF1
    {height : ℕ} (stage : F1024TowerStageData height) :
    FiniteDimensional F1024TowerF1 (F1024TowerStageStep stage) :=
  FiniteDimensional.trans F1024TowerF1 stage.carrier (F1024TowerStageStep stage)

private noncomputable instance f1024TowerStageStepSeparableOverF1
    {height : ℕ} (stage : F1024TowerStageData height) :
    Algebra.IsSeparable F1024TowerF1 (F1024TowerStageStep stage) :=
  Algebra.IsSeparable.trans F1024TowerF1 stage.carrier (F1024TowerStageStep stage)

private noncomputable instance f1024TowerStageStepCharTwo
    {height : ℕ} (stage : F1024TowerStageData height) :
    CharP (F1024TowerStageStep stage) 2 :=
  charP_of_injective_algebraMap
    (algebraMap stage.carrier (F1024TowerStageStep stage)).injective 2

/-- The inverse root defining the successor. -/
private noncomputable def f1024TowerStageStepRoot
    {height : ℕ} (stage : F1024TowerStageData height) :
    F1024TowerStageStep stage :=
  AdjoinRoot.root (f1024TowerStageStepPolynomial stage)

private theorem f1024TowerStageStepRoot_equation
    {height : ℕ} (stage : F1024TowerStageData height) :
    f1024TowerStageStepRoot stage ^ 32 +
      algebraMap stage.carrier (F1024TowerStageStep stage) (stage.x⁻¹ ^ 32) *
        f1024TowerStageStepRoot stage ^ 31 =
      algebraMap stage.carrier (F1024TowerStageStep stage) stage.x⁻¹ := by
  rw [AdjoinRoot.algebraMap_eq]
  apply sub_eq_zero.mp
  have hroot := AdjoinRoot.eval₂_root (f1024TowerStageStepPolynomial stage)
  change (X ^ 32 + C (stage.x⁻¹ ^ 32) * X ^ 31 - C stage.x⁻¹ :
      stage.carrier[X]).eval₂
        (AdjoinRoot.of (f1024TowerStageStepPolynomial stage))
        (AdjoinRoot.root (f1024TowerStageStepPolynomial stage)) = 0 at hroot
  simpa only [f1024TowerStageStepRoot, eval₂_sub, eval₂_add, eval₂_mul,
    eval₂_pow, eval₂_X, eval₂_C] using hroot

private theorem f1024TowerStageStepRoot_ne_zero
    {height : ℕ} (stage : F1024TowerStageData height) :
    f1024TowerStageStepRoot stage ≠ 0 := by
  intro hroot
  have hzero : algebraMap stage.carrier (F1024TowerStageStep stage) stage.x⁻¹ = 0 := by
    rw [← f1024TowerStageStepRoot_equation stage, hroot]
    norm_num
  exact (map_ne_zero_iff (algebraMap stage.carrier (F1024TowerStageStep stage))
    (algebraMap stage.carrier (F1024TowerStageStep stage)).injective).mpr
      (inv_ne_zero stage.x_ne_zero) hzero

/-- The successor source coordinate is the reciprocal of the inverse root. -/
private noncomputable def f1024TowerStageStepX
    {height : ℕ} (stage : F1024TowerStageData height) :
    F1024TowerStageStep stage :=
  (f1024TowerStageStepRoot stage)⁻¹

private theorem f1024TowerStageStepX_ne_zero
    {height : ℕ} (stage : F1024TowerStageData height) :
    f1024TowerStageStepX stage ≠ 0 :=
  inv_ne_zero (f1024TowerStageStepRoot_ne_zero stage)

/-- The successor Artin--Schreier generator recovered from the inverse root. -/
private noncomputable def f1024TowerStageStepZ
    {height : ℕ} (stage : F1024TowerStageData height) :
    F1024TowerStageStep stage :=
  algebraMap stage.carrier (F1024TowerStageStep stage) stage.x /
    f1024TowerStageStepRoot stage

private theorem f1024TowerStageStepZ_ne_zero
    {height : ℕ} (stage : F1024TowerStageData height) :
    f1024TowerStageStepZ stage ≠ 0 := by
  unfold f1024TowerStageStepZ
  exact div_ne_zero
    ((map_ne_zero_iff
      (algebraMap stage.carrier (F1024TowerStageStep stage))
      (algebraMap stage.carrier (F1024TowerStageStep stage)).injective).mpr
        stage.x_ne_zero)
    (f1024TowerStageStepRoot_ne_zero stage)

private theorem f1024TowerStageStepZ_adjoin_eq_top
    {height : ℕ} (stage : F1024TowerStageData height) :
    IntermediateField.adjoin stage.carrier
        {f1024TowerStageStepZ stage} = ⊤ := by
  apply top_unique
  rw [← IntermediateField.adjoin_root_eq_top
    (f1024TowerStageStepPolynomial stage)]
  apply IntermediateField.adjoin_le_iff.mpr
  intro root hroot
  rw [Set.mem_singleton_iff.mp hroot]
  let generated : IntermediateField stage.carrier
      (F1024TowerStageStep stage) :=
    IntermediateField.adjoin stage.carrier
      {f1024TowerStageStepZ stage}
  have hzmem : f1024TowerStageStepZ stage ∈ generated :=
    IntermediateField.subset_adjoin stage.carrier
      ({f1024TowerStageStepZ stage} :
        Set (F1024TowerStageStep stage)) (Set.mem_singleton _)
  have hxmem : algebraMap stage.carrier (F1024TowerStageStep stage) stage.x ∈
      generated := generated.algebraMap_mem stage.x
  have hxne : algebraMap stage.carrier (F1024TowerStageStep stage) stage.x ≠ 0 :=
    (map_ne_zero_iff
      (algebraMap stage.carrier (F1024TowerStageStep stage))
      (algebraMap stage.carrier (F1024TowerStageStep stage)).injective).mpr
        stage.x_ne_zero
  have hrootEq : f1024TowerStageStepRoot stage =
      algebraMap stage.carrier (F1024TowerStageStep stage) stage.x /
        f1024TowerStageStepZ stage := by
    unfold f1024TowerStageStepZ
    field_simp [hxne, f1024TowerStageStepRoot_ne_zero stage]
  change f1024TowerStageStepRoot stage ∈ generated
  rw [hrootEq]
  exact generated.div_mem hxmem hzmem

private theorem f1024TowerStageStepZ_equation
    {height : ℕ} (stage : F1024TowerStageData height) :
    f1024TowerStageStepZ stage ^ 32 + f1024TowerStageStepZ stage =
      algebraMap stage.carrier (F1024TowerStageStep stage) (stage.x ^ 33) := by
  let u : F1024TowerStageStep stage :=
    algebraMap stage.carrier (F1024TowerStageStep stage) stage.x
  have hu : u ≠ 0 := by
    dsimp [u]
    exact (map_ne_zero_iff (algebraMap stage.carrier (F1024TowerStageStep stage))
      (algebraMap stage.carrier (F1024TowerStageStep stage)).injective).mpr stage.x_ne_zero
  have hroot : f1024TowerStageStepRoot stage ^ 32 +
      u⁻¹ ^ 32 * f1024TowerStageStepRoot stage ^ 31 = u⁻¹ := by
    dsimp [u]
    have hport := f1024TowerStageStepRoot_equation stage
    simp only [map_inv₀, map_pow] at hport ⊢
    exact hport
  have hcleared : u ^ 33 * f1024TowerStageStepRoot stage ^ 32 +
      u * f1024TowerStageStepRoot stage ^ 31 = u ^ 32 := by
    calc
      u ^ 33 * f1024TowerStageStepRoot stage ^ 32 +
          u * f1024TowerStageStepRoot stage ^ 31 =
        u ^ 33 * (f1024TowerStageStepRoot stage ^ 32 +
          u⁻¹ ^ 32 * f1024TowerStageStepRoot stage ^ 31) := by
            field_simp [hu]
      _ = u ^ 33 * u⁻¹ := by rw [hroot]
      _ = u ^ 32 := by field_simp [hu]
  have htwo : (2 : F1024TowerStageStep stage) = 0 :=
    CharP.ofNat_eq_zero' (R := F1024TowerStageStep stage) 2 2 (by norm_num)
  have hadd_self (a : F1024TowerStageStep stage) : a + a = 0 := by
    rw [← two_mul, htwo, zero_mul]
  have htarget : u ^ 32 + u * f1024TowerStageStepRoot stage ^ 31 =
      u ^ 33 * f1024TowerStageStepRoot stage ^ 32 := by
    calc
      u ^ 32 + u * f1024TowerStageStepRoot stage ^ 31 =
          (u ^ 33 * f1024TowerStageStepRoot stage ^ 32 +
            u * f1024TowerStageStepRoot stage ^ 31) +
              u * f1024TowerStageStepRoot stage ^ 31 := by rw [hcleared]
      _ = u ^ 33 * f1024TowerStageStepRoot stage ^ 32 +
          (u * f1024TowerStageStepRoot stage ^ 31 +
            u * f1024TowerStageStepRoot stage ^ 31) := by ring
      _ = u ^ 33 * f1024TowerStageStepRoot stage ^ 32 := by
        rw [hadd_self, add_zero]
  rw [map_pow]
  change (u / f1024TowerStageStepRoot stage) ^ 32 +
      u / f1024TowerStageStepRoot stage = u ^ 33
  calc
    (u / f1024TowerStageStepRoot stage) ^ 32 +
        u / f1024TowerStageStepRoot stage =
      (u ^ 32 + u * f1024TowerStageStepRoot stage ^ 31) /
        f1024TowerStageStepRoot stage ^ 32 := by
          rw [div_pow]
          field_simp [f1024TowerStageStepRoot_ne_zero stage]
    _ = u ^ 33 := by
      rw [htarget]
      field_simp [f1024TowerStageStepRoot_ne_zero stage]

private theorem f1024TowerStageStep_X_mul_nextX
    {height : ℕ} (stage : F1024TowerStageData height) :
    algebraMap stage.carrier (F1024TowerStageStep stage) stage.x *
      f1024TowerStageStepX stage = f1024TowerStageStepZ stage := by
  rw [f1024TowerStageStepX, f1024TowerStageStepZ, div_eq_mul_inv]

/-- Recursively construct the actual indexed tower.  At a successor, all old
inverse coordinates are mapped forward and the new inverse root is appended.
The only induction data retained are the displayed algebraic recurrences and
the finite degree. -/
private noncomputable def f1024TowerStage :
    ∀ height : ℕ, F1024TowerStageData height
  | 0 => f1024TowerStageBase
  | height + 1 => by
      let previous := f1024TowerStage height
      let nextCoordinate : ℕ → F1024TowerStageStep previous := fun i =>
        if i ≤ height then
          algebraMap previous.carrier (F1024TowerStageStep previous)
            (previous.inverseCoordinate i)
        else
          f1024TowerStageStepRoot previous
      have hzero : nextCoordinate 0 =
          (algebraMap F1024TowerF1 (F1024TowerStageStep previous) RatFunc.X)⁻¹ := by
        dsimp only [nextCoordinate]
        rw [if_pos (Nat.zero_le height), previous.inverseCoordinate_zero,
          map_inv₀, ← IsScalarTower.algebraMap_apply F1024TowerF1 previous.carrier
            (F1024TowerStageStep previous)]
      have hcurrent : nextCoordinate (height + 1) =
          (f1024TowerStageStepX previous)⁻¹ := by
        dsimp only [nextCoordinate]
        rw [if_neg (by omega)]
        simp only [f1024TowerStageStepX, inv_inv]
      have hne : ∀ i, nextCoordinate i ≠ 0 := by
        intro i
        by_cases hi : i ≤ height
        · dsimp only [nextCoordinate]
          rw [if_pos hi]
          exact (map_ne_zero_iff
            (algebraMap previous.carrier (F1024TowerStageStep previous))
            (algebraMap previous.carrier
              (F1024TowerStageStep previous)).injective).mpr
                (previous.inverseCoordinate_ne_zero i)
        · dsimp only [nextCoordinate]
          rw [if_neg hi]
          exact f1024TowerStageStepRoot_ne_zero previous
      have hrec : ∀ i, i < height + 1 →
          nextCoordinate (i + 1) ^ 32 +
            nextCoordinate i ^ 32 * nextCoordinate (i + 1) ^ 31 =
              nextCoordinate i := by
        intro i hi
        by_cases hilast : i = height
        · subst i
          dsimp only [nextCoordinate]
          rw [if_pos (le_refl height), if_neg (by omega),
            previous.inverseCoordinate_current]
          simpa only [map_inv₀, map_pow] using
            f1024TowerStageStepRoot_equation previous
        · have hiold : i < height := by omega
          have hile : i ≤ height := Nat.le_of_lt hiold
          have hisuccle : i + 1 ≤ height := by omega
          dsimp only [nextCoordinate]
          rw [if_pos hile, if_pos hisuccle]
          simpa only [map_add, map_mul, map_pow] using
            congrArg (algebraMap previous.carrier (F1024TowerStageStep previous))
              (previous.inverseCoordinate_recurrence i hiold)
      have hfinrank : Module.finrank F1024TowerF1
          (F1024TowerStageStep previous) = 32 ^ (height + 1) := by
        calc
          Module.finrank F1024TowerF1 (F1024TowerStageStep previous) =
              Module.finrank F1024TowerF1 previous.carrier *
                Module.finrank previous.carrier (F1024TowerStageStep previous) := by
            symm
            exact Module.finrank_mul_finrank F1024TowerF1 previous.carrier
              (F1024TowerStageStep previous)
          _ = 32 ^ height * 32 := by
            rw [previous.finrank_eq, f1024TowerStageStep_finrank previous]
          _ = 32 ^ (height + 1) := by rw [pow_succ]
      exact
        { carrier := F1024TowerStageStep previous
          fieldInst := inferInstance
          rationalAlgebraInst := inferInstance
          finiteDimensionalInst := inferInstance
          separableInst := inferInstance
          constantAlgebraInst := inferInstance
          constantRationalTowerInst := inferInstance
          polynomialAlgebraInst := inferInstance
          polynomialRationalTowerInst := inferInstance
          charTwoInst := inferInstance
          x := f1024TowerStageStepX previous
          x_ne_zero := f1024TowerStageStepX_ne_zero previous
          inverseCoordinate := nextCoordinate
          inverseCoordinate_zero := hzero
          inverseCoordinate_current := hcurrent
          inverseCoordinate_ne_zero := hne
          inverseCoordinate_recurrence := hrec
          finrank_eq := hfinrank }

private theorem f1024TowerStage_succ_x (height : ℕ) :
    (f1024TowerStage (height + 1)).x =
      f1024TowerStageStepX (f1024TowerStage height) :=
  rfl

/-- The actual field at extension height `height` in the fixed `F1024`
Garcia--Stichtenoth tower. -/
noncomputable abbrev F1024TowerLevel (height : ℕ) : Type :=
  (f1024TowerStage height).carrier

/-- The source coordinate `x_(height+1)` in the actual indexed tower. -/
noncomputable def f1024TowerLevelX (height : ℕ) : F1024TowerLevel height :=
  (f1024TowerStage height).x

/-- Every coordinate in the actual indexed tower is nonzero. -/
theorem f1024TowerLevelX_ne_zero (height : ℕ) :
    f1024TowerLevelX height ≠ 0 :=
  (f1024TowerStage height).x_ne_zero

/-- The canonical inclusion of a constructed level into its actual
`AdjoinRoot` successor. -/
noncomputable instance f1024TowerLevelStepAlgebra (height : ℕ) :
    Algebra (F1024TowerLevel height) (F1024TowerLevel (height + 1)) := by
  change Algebra (f1024TowerStage height).carrier
    (F1024TowerStageStep (f1024TowerStage height))
  infer_instance

private noncomputable instance f1024TowerLevelStepFiniteDimensional
    (height : ℕ) :
    FiniteDimensional (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) := by
  change FiniteDimensional (f1024TowerStage height).carrier
    (F1024TowerStageStep (f1024TowerStage height))
  infer_instance

/-- The constant-field algebra maps through one literal successor embedding. -/
noncomputable instance f1024TowerLevelStepConstantScalarTower (height : ℕ) :
    IsScalarTower F1024 (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The rational-function algebra maps through one literal successor
embedding. -/
noncomputable instance f1024TowerLevelStepRationalScalarTower (height : ℕ) :
    IsScalarTower F1024TowerF1 (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The Artin--Schreier generator used for the successor of `height`. -/
noncomputable def f1024TowerLevelZ (height : ℕ) :
    F1024TowerLevel (height + 1) :=
  f1024TowerStageStepZ (f1024TowerStage height)

/-- The actual indexed successor satisfies the source recursion
`z_(i+1)^32 + z_(i+1) = x_i^33`. -/
theorem f1024TowerLevel_step_equation (height : ℕ) :
    f1024TowerLevelZ height ^ 32 + f1024TowerLevelZ height =
      algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
        (f1024TowerLevelX height ^ 33) := by
  exact f1024TowerStageStepZ_equation (f1024TowerStage height)

/-- The source change of coordinates is exact at every successor:
`x_i * x_(i+1) = z_(i+1)`. -/
theorem f1024TowerLevel_X_mul_nextX (height : ℕ) :
    algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
        (f1024TowerLevelX height) * f1024TowerLevelX (height + 1) =
      f1024TowerLevelZ height := by
  have hport := f1024TowerStageStep_X_mul_nextX (f1024TowerStage height)
  simp only [f1024TowerLevelX, f1024TowerLevelZ, f1024TowerStage_succ_x] at hport ⊢
  exact hport

/-- The direct source coordinates satisfy the cleared Garcia--Stichtenoth
recurrence at every adjacent pair of actual levels. -/
private theorem f1024TowerLevel_step_X_recurrence (height : ℕ) :
    algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
          (f1024TowerLevelX height) ^ 31 *
        f1024TowerLevelX (height + 1) ^ 32 +
      f1024TowerLevelX (height + 1) =
        algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
          (f1024TowerLevelX height) ^ 32 := by
  let u : F1024TowerLevel (height + 1) :=
    algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
      (f1024TowerLevelX height)
  let v : F1024TowerLevel (height + 1) := f1024TowerLevelX (height + 1)
  have hu : u ≠ 0 :=
    (map_ne_zero_iff
      (algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1)))
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1))).injective).mpr
          (f1024TowerLevelX_ne_zero height)
  have hz : (u * v) ^ 32 + u * v = u ^ 33 := by
    rw [f1024TowerLevel_X_mul_nextX]
    simpa only [u, v, map_pow] using f1024TowerLevel_step_equation height
  apply mul_left_cancel₀ hu
  calc
    u * (u ^ 31 * v ^ 32 + v) = (u * v) ^ 32 + u * v := by ring
    _ = u ^ 33 := hz
    _ = u * u ^ 32 := by ring

/-- The canonical function-field derivations commute with the actual
embedding of one constructed tower level into its successor. -/
theorem f1024TowerLevel_functionFieldDerivation_stepEmbedding
    (height : ℕ) (u : F1024TowerLevel height) :
    functionFieldDerivation (k := F1024)
        (F := F1024TowerLevel (height + 1))
        (algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1)) u) =
      algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1))
        (functionFieldDerivation (k := F1024)
          (F := F1024TowerLevel height) u) := by
  let Dupper : Derivation F1024 (F1024TowerLevel (height + 1))
      (F1024TowerLevel (height + 1)) :=
    functionFieldDerivation (k := F1024)
      (F := F1024TowerLevel (height + 1))
  let Dlower : Derivation F1024 (F1024TowerLevel height)
      (F1024TowerLevel height) :=
    functionFieldDerivation (k := F1024)
      (F := F1024TowerLevel height)
  let Drestricted : Derivation F1024 (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) :=
    Dupper.compAlgebraMap (F1024TowerLevel height)
  let Dtransported : Derivation F1024 (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) :=
    (Algebra.ofId (F1024TowerLevel height)
      (F1024TowerLevel (height + 1))).toLinearMap.compDer Dlower
  have hderivation : Drestricted = Dtransported := by
    apply QEC.Coding.AlgebraicGeometry.SeparableDerivationExtension.extension_unique
    apply (QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv
      (k := F1024) (M := F1024TowerLevel (height + 1))).injective
    change
      Dupper (algebraMap (RatFunc F1024)
          (F1024TowerLevel (height + 1)) RatFunc.X) =
        algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1))
          (Dlower (algebraMap (RatFunc F1024)
            (F1024TowerLevel height) RatFunc.X))
    rw [functionFieldDerivation_apply_X,
      functionFieldDerivation_apply_X, map_one]
  have hu := Derivation.congr_fun hderivation u
  change
    Dupper (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1)) u) =
      algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1)) (Dlower u) at hu
  simpa only [Dupper, Dlower] using hu

/-- Implicit differentiation of the actual indexed relation
`z_(i+1)^32 + z_(i+1) = x_i^33`. -/
theorem f1024TowerLevel_functionFieldDerivation_z (height : ℕ) :
    functionFieldDerivation (k := F1024)
        (F := F1024TowerLevel (height + 1))
        (f1024TowerLevelZ height) =
      algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1))
          (f1024TowerLevelX height) ^ 32 *
        algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1))
          (functionFieldDerivation (k := F1024)
            (F := F1024TowerLevel height)
            (f1024TowerLevelX height)) := by
  let D : Derivation F1024 (F1024TowerLevel (height + 1))
      (F1024TowerLevel (height + 1)) :=
    functionFieldDerivation (k := F1024)
      (F := F1024TowerLevel (height + 1))
  let x : F1024TowerLevel (height + 1) :=
    algebraMap (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) (f1024TowerLevelX height)
  have hequation : f1024TowerLevelZ height ^ 32 +
      f1024TowerLevelZ height = x ^ 33 := by
    simpa only [x, map_pow] using f1024TowerLevel_step_equation height
  have hderivative := congrArg D hequation
  rw [map_add, Derivation.leibniz_pow, Derivation.leibniz_pow] at hderivative
  simp only [nsmul_eq_mul] at hderivative
  have h32 : ((32 : ℕ) : F1024TowerLevel (height + 1)) = 0 := by
    rw [CharP.cast_eq_zero_iff (F1024TowerLevel (height + 1)) 2]
    norm_num
  have h33 : ((33 : ℕ) : F1024TowerLevel (height + 1)) = 1 := by
    rw [show (33 : ℕ) = 32 + 1 by norm_num, Nat.cast_add, h32]
    simp
  simp only [h32, h33, Nat.reduceSub, zero_mul, zero_add, one_mul] at hderivative
  rw [f1024TowerLevel_functionFieldDerivation_stepEmbedding] at hderivative
  have hport := hderivative
  simp only [D, x, zero_mul, zero_add, one_mul, smul_eq_mul] at hport ⊢
  exact hport

/-- The derivative of the next source coordinate follows the exact
Garcia--Stichtenoth recurrence. -/
theorem f1024TowerLevel_functionFieldDerivation_x_succ (height : ℕ) :
    functionFieldDerivation (k := F1024)
        (F := F1024TowerLevel (height + 1))
        (f1024TowerLevelX (height + 1)) =
      algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1))
          (functionFieldDerivation (k := F1024)
            (F := F1024TowerLevel height)
            (f1024TowerLevelX height)) *
        algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1))
          (f1024TowerLevelX height) ^ 30 *
        f1024TowerLevelX (height + 1) ^ 32 := by
  let D : Derivation F1024 (F1024TowerLevel (height + 1))
      (F1024TowerLevel (height + 1)) :=
    functionFieldDerivation (k := F1024)
      (F := F1024TowerLevel (height + 1))
  let x : F1024TowerLevel (height + 1) :=
    algebraMap (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) (f1024TowerLevelX height)
  let z : F1024TowerLevel (height + 1) := f1024TowerLevelZ height
  let dx : F1024TowerLevel (height + 1) :=
    algebraMap (F1024TowerLevel height)
      (F1024TowerLevel (height + 1))
      (functionFieldDerivation (k := F1024)
        (F := F1024TowerLevel height) (f1024TowerLevelX height))
  have hx_ne : x ≠ 0 := by
    exact (map_ne_zero_iff
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1)))
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1))).injective).mpr
          (f1024TowerLevelX_ne_zero height)
  have hnext : f1024TowerLevelX (height + 1) = z / x := by
    apply (eq_div_iff hx_ne).mpr
    simpa only [x, z, mul_comm] using
      f1024TowerLevel_X_mul_nextX height
  have hzDerivative : D z = x ^ 32 * dx := by
    simpa only [D, x, z, dx] using
      f1024TowerLevel_functionFieldDerivation_z height
  have hxDerivative : D x = dx := by
    simpa only [D, x, dx] using
      f1024TowerLevel_functionFieldDerivation_stepEmbedding height
        (f1024TowerLevelX height)
  have hequation : z ^ 32 + z = x ^ 33 := by
    simpa only [x, z, map_pow] using f1024TowerLevel_step_equation height
  rw [hnext]
  change D (z / x) = dx * x ^ 30 * (z / x) ^ 32
  rw [Derivation.leibniz_div, hzDerivative, hxDerivative]
  simp only [smul_eq_mul]
  field_simp [hx_ne]
  linear_combination -dx * hequation

/-- The `height`th constructed field has exact degree `32^height` over the
source rational function field. -/
theorem f1024TowerLevel_finrank_over_F1 (height : ℕ) :
    Module.finrank F1024TowerF1 (F1024TowerLevel height) = 32 ^ height :=
  (f1024TowerStage height).finrank_eq

/-- Every actual indexed level has a genuine inverse-chart upper prime by
lying-over.  No prime is selected or retained by the family. -/
theorem f1024TowerLevel_inverseInfinityFibre_nonempty (height : ℕ) :
    Nonempty (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerLevel height)) :=
  f1024TowerStage_inverseInfinityFibre_nonempty (f1024TowerStage height)

/-- The normalized order at a genuine inverse-chart upper prime of an actual
indexed level. -/
noncomputable def f1024TowerLevelInverseInfinityOrder (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerLevel height))
    (u : F1024TowerLevel height) : ℤ :=
  f1024TowerStageInverseOrder (f1024TowerStage height) P u

/-- At every genuine inverse-chart upper prime of every constructed level,
the current source coordinate has a simple pole. -/
theorem f1024TowerLevelInverseInfinityPlace_order_x (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerLevel height)) :
    f1024TowerLevelInverseInfinityOrder height P
      (f1024TowerLevelX height) = -1 :=
  f1024TowerStageInversePlace_order_x (f1024TowerStage height) P

/-! ## Finite source coordinates -/

private noncomputable instance f1024TowerStepLabelFintype :
    Fintype (GaloisField 2 5) :=
  Fintype.ofFinite (GaloisField 2 5)

/-- The finite coordinate set used to enumerate the split affine fibres at
extension height `height`.  The first component is the nonzero value of
`x₁`; every later component records one of the `32` Artin--Schreier
choices. -/
noncomputable abbrev F1024TowerFiniteCoordinate (height : ℕ) : Type :=
  F1024ˣ × (Fin height → GaloisField 2 5)

private theorem f1024TowerStepLabel_card :
    Fintype.card (GaloisField 2 5) = 32 := by
  have h := GaloisField.card 2 (n := 5) (by norm_num)
  norm_num at h
  simpa only [Nat.card_eq_fintype_card] using h

/-- The concrete finite coordinate set has exactly
`1023 * 32^height` elements. -/
theorem f1024TowerFiniteCoordinate_card (height : ℕ) :
    Fintype.card (F1024TowerFiniteCoordinate height) = 1023 * 32 ^ height := by
  rw [Fintype.card_prod, Fintype.card_units, f1024_card,
    Fintype.card_pi_const, f1024TowerStepLabel_card]

/-- The degree-five binary label field embeds into the actual degree-ten
constant field because `5 ∣ 10`. -/
private noncomputable def f1024TowerStepLabelEmbedding :
    GaloisField 2 5 →ₐ[ZMod 2] F1024 := by
  exact Classical.choice (FiniteField.nonempty_algHom_of_finrank_dvd (by
    rw [GaloisField.finrank 2 (by norm_num), f1024_finrank]
    norm_num))

private theorem f1024TowerStepLabel_frobenius (label : GaloisField 2 5) :
    label ^ 32 = label := by
  have h := FiniteField.pow_card label
  rw [f1024TowerStepLabel_card] at h
  exact h

private theorem f1024TowerStepLabelEmbedding_kernel
    (label : GaloisField 2 5) :
    f1024TowerStepLabelEmbedding label ^ 32 +
        f1024TowerStepLabelEmbedding label = 0 := by
  rw [← map_pow, f1024TowerStepLabel_frobenius,
    ← map_add, CharTwo.add_self_eq_zero, map_zero]

private theorem exists_f1024ArtinSchreierAnchor :
    ∃ anchor : F1024, anchor ^ 32 + anchor ≠ 0 := by
  let p : F1024[X] := X ^ 32 + X
  have hp : p ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun q : F1024[X] => q.coeff 32) hzero
    norm_num [p, coeff_add, coeff_X_pow, coeff_X] at hcoeff
  by_contra h
  push Not at h
  have hsubset : (Finset.univ : Finset F1024).val ⊆ p.roots := by
    intro a ha
    rw [Polynomial.mem_roots hp, Polynomial.IsRoot]
    simpa only [p, eval_add, eval_pow, eval_X] using h a
  have hcard := Polynomial.card_le_degree_of_subset_roots hsubset
  have hdegree : p.natDegree = 32 := by
    dsimp only [p]
    rw [natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · rw [natDegree_X_pow, natDegree_X]
      norm_num
  rw [Finset.card_univ, f1024_card, hdegree] at hcard
  omega

private noncomputable def f1024ArtinSchreierAnchor : F1024 :=
  Classical.choose exists_f1024ArtinSchreierAnchor

private theorem f1024ArtinSchreierAnchor_delta_ne_zero :
    f1024ArtinSchreierAnchor ^ 32 + f1024ArtinSchreierAnchor ≠ 0 :=
  Classical.choose_spec exists_f1024ArtinSchreierAnchor

private theorem f1024_pow_thirtyTwo_fixed_delta :
    (f1024ArtinSchreierAnchor ^ 32 + f1024ArtinSchreierAnchor) ^ 32 =
      f1024ArtinSchreierAnchor ^ 32 + f1024ArtinSchreierAnchor := by
  have hpow : f1024ArtinSchreierAnchor ^ 1024 = f1024ArtinSchreierAnchor := by
    simpa only [f1024_card] using
      (FiniteField.pow_card f1024ArtinSchreierAnchor)
  calc
    (f1024ArtinSchreierAnchor ^ 32 + f1024ArtinSchreierAnchor) ^ 32 =
        (f1024ArtinSchreierAnchor ^ 32) ^ 32 +
          f1024ArtinSchreierAnchor ^ 32 := by
      rw [show 32 = 2 ^ 5 by norm_num, add_pow_char_pow]
    _ = f1024ArtinSchreierAnchor ^ 1024 +
          f1024ArtinSchreierAnchor ^ 32 := by rw [← pow_mul]
    _ = f1024ArtinSchreierAnchor ^ 32 + f1024ArtinSchreierAnchor := by
      rw [hpow, add_comm]

private theorem f1024_pow_thirtyThree_frobenius
    {a : F1024} (ha : a ≠ 0) : (a ^ 33) ^ 32 = a ^ 33 := by
  have hpow : a ^ 1023 = 1 := by
    simpa only [f1024_card] using
      (FiniteField.pow_card_sub_one_eq_one a ha)
  rw [← pow_mul]
  calc
    a ^ (33 * 32) = a ^ (1023 + 33) := by norm_num
    _ = a ^ 1023 * a ^ 33 := by rw [pow_add]
    _ = a ^ 33 := by rw [hpow, one_mul]

/-- A deterministic base solution of `z^32 + z = a^33` for nonzero `a`.
The fixed anchor converts the Frobenius-fixed right-hand side into an
Artin--Schreier preimage. -/
private noncomputable def f1024ArtinSchreierBaseSolution (a : F1024) : F1024 :=
  f1024ArtinSchreierAnchor *
    (a ^ 33 /
      (f1024ArtinSchreierAnchor ^ 32 + f1024ArtinSchreierAnchor))

private theorem f1024ArtinSchreierBaseSolution_equation
    {a : F1024} (ha : a ≠ 0) :
    f1024ArtinSchreierBaseSolution a ^ 32 +
        f1024ArtinSchreierBaseSolution a = a ^ 33 := by
  have hb := f1024_pow_thirtyThree_frobenius ha
  have hdelta := f1024_pow_thirtyTwo_fixed_delta
  rw [f1024ArtinSchreierBaseSolution, mul_pow, div_pow, hb, hdelta]
  calc
    f1024ArtinSchreierAnchor ^ 32 *
          (a ^ 33 /
            (f1024ArtinSchreierAnchor ^ 32 + f1024ArtinSchreierAnchor)) +
        f1024ArtinSchreierAnchor *
          (a ^ 33 /
            (f1024ArtinSchreierAnchor ^ 32 + f1024ArtinSchreierAnchor)) =
      (f1024ArtinSchreierAnchor ^ 32 + f1024ArtinSchreierAnchor) *
        (a ^ 33 /
          (f1024ArtinSchreierAnchor ^ 32 + f1024ArtinSchreierAnchor)) := by
            ring
    _ = a ^ 33 := by
      rw [mul_div_cancel₀ _ f1024ArtinSchreierAnchor_delta_ne_zero]

/-- The label selects one of the `32` distinct Artin--Schreier solutions
over a nonzero predecessor coordinate. -/
private noncomputable def f1024ArtinSchreierSolution
    (a : F1024) (label : GaloisField 2 5) : F1024 :=
  f1024ArtinSchreierBaseSolution a + f1024TowerStepLabelEmbedding label

private theorem f1024ArtinSchreierSolution_equation
    {a : F1024} (ha : a ≠ 0) (label : GaloisField 2 5) :
    f1024ArtinSchreierSolution a label ^ 32 +
        f1024ArtinSchreierSolution a label = a ^ 33 := by
  rw [f1024ArtinSchreierSolution,
    show 32 = 2 ^ 5 by norm_num, add_pow_char_pow]
  change f1024ArtinSchreierBaseSolution a ^ 32 +
      f1024TowerStepLabelEmbedding label ^ 32 +
        (f1024ArtinSchreierBaseSolution a +
          f1024TowerStepLabelEmbedding label) = a ^ 33
  calc
    f1024ArtinSchreierBaseSolution a ^ 32 +
        f1024TowerStepLabelEmbedding label ^ 32 +
          (f1024ArtinSchreierBaseSolution a +
            f1024TowerStepLabelEmbedding label) =
      (f1024ArtinSchreierBaseSolution a ^ 32 +
          f1024ArtinSchreierBaseSolution a) +
        (f1024TowerStepLabelEmbedding label ^ 32 +
          f1024TowerStepLabelEmbedding label) := by ring
    _ = a ^ 33 := by
      rw [f1024ArtinSchreierBaseSolution_equation ha,
        f1024TowerStepLabelEmbedding_kernel, add_zero]

private theorem f1024ArtinSchreierSolution_ne_zero
    {a : F1024} (ha : a ≠ 0) (label : GaloisField 2 5) :
    f1024ArtinSchreierSolution a label ≠ 0 := by
  intro hzero
  have heq := f1024ArtinSchreierSolution_equation ha label
  rw [hzero] at heq
  simp only [zero_pow (by norm_num : 32 ≠ 0), zero_add] at heq
  exact (pow_ne_zero 33 ha) heq.symm

/-- Forget the final Artin--Schreier choice of a finite coordinate. -/
noncomputable def f1024TowerFiniteCoordinatePrefix {height : ℕ}
    (coordinate : F1024TowerFiniteCoordinate (height + 1)) :
    F1024TowerFiniteCoordinate height :=
  ⟨coordinate.1, fun i => coordinate.2 i.castSucc⟩

/-- Evaluate the current source coordinate in `F1024` along a finite choice
sequence. -/
noncomputable def f1024TowerFiniteCoordinateValue :
    {height : ℕ} → F1024TowerFiniteCoordinate height → F1024
  | 0, coordinate => coordinate.1
  | height + 1, coordinate =>
      let previous := f1024TowerFiniteCoordinatePrefix coordinate
      let z := f1024ArtinSchreierSolution
        (f1024TowerFiniteCoordinateValue previous)
        (coordinate.2 (Fin.last height))
      z / f1024TowerFiniteCoordinateValue previous

/-- Every recursively evaluated finite coordinate is nonzero. -/
theorem f1024TowerFiniteCoordinateValue_ne_zero :
    ∀ {height : ℕ} (coordinate : F1024TowerFiniteCoordinate height),
      f1024TowerFiniteCoordinateValue coordinate ≠ 0
  | 0, coordinate => Units.ne_zero coordinate.1
  | height + 1, coordinate => by
      have hprevious := f1024TowerFiniteCoordinateValue_ne_zero
        (f1024TowerFiniteCoordinatePrefix coordinate)
      exact div_ne_zero
        (f1024ArtinSchreierSolution_ne_zero hprevious
          (coordinate.2 (Fin.last height)))
        hprevious

/-- The Artin--Schreier root chosen at the final step of a finite
coordinate. -/
noncomputable def f1024TowerFiniteCoordinateStepZ {height : ℕ}
    (coordinate : F1024TowerFiniteCoordinate (height + 1)) : F1024 :=
  f1024ArtinSchreierSolution
    (f1024TowerFiniteCoordinateValue
      (f1024TowerFiniteCoordinatePrefix coordinate))
    (coordinate.2 (Fin.last height))

/-- The finite coordinate values satisfy the exact source recursion at
every successor. -/
theorem f1024TowerFiniteCoordinate_step_equation {height : ℕ}
    (coordinate : F1024TowerFiniteCoordinate (height + 1)) :
    f1024TowerFiniteCoordinateStepZ coordinate ^ 32 +
        f1024TowerFiniteCoordinateStepZ coordinate =
      f1024TowerFiniteCoordinateValue
          (f1024TowerFiniteCoordinatePrefix coordinate) ^ 33 := by
  exact f1024ArtinSchreierSolution_equation
    (f1024TowerFiniteCoordinateValue_ne_zero
      (f1024TowerFiniteCoordinatePrefix coordinate))
    (coordinate.2 (Fin.last height))

private theorem f1024TowerFiniteCoordinateValue_succ {height : ℕ}
    (coordinate : F1024TowerFiniteCoordinate (height + 1)) :
    f1024TowerFiniteCoordinateValue coordinate =
      f1024TowerFiniteCoordinateStepZ coordinate /
        f1024TowerFiniteCoordinateValue
          (f1024TowerFiniteCoordinatePrefix coordinate) :=
  rfl

/-- The evaluated source change of coordinates is exact at every finite
successor. -/
theorem f1024TowerFiniteCoordinate_X_mul_nextX {height : ℕ}
    (coordinate : F1024TowerFiniteCoordinate (height + 1)) :
    f1024TowerFiniteCoordinateValue
          (f1024TowerFiniteCoordinatePrefix coordinate) *
        f1024TowerFiniteCoordinateValue coordinate =
      f1024TowerFiniteCoordinateStepZ coordinate := by
  rw [f1024TowerFiniteCoordinateValue_succ]
  field_simp [f1024TowerFiniteCoordinateValue_ne_zero]

/-! ## The finite split chart -/

/-- The direct Artin--Schreier polynomial at an arbitrary constructed tower
stage.  This is the affine equation used to retain the finite split fibres;
the field tower itself remains defined by the inverse polynomial above. -/
private noncomputable def f1024TowerStageDirectPolynomial
    {height : ℕ} (stage : F1024TowerStageData height) : stage.carrier[X] :=
  X ^ 32 + X - C (stage.x ^ 33)

private theorem f1024TowerStageDirectPolynomial_monic
    {height : ℕ} (stage : F1024TowerStageData height) :
    (f1024TowerStageDirectPolynomial stage).Monic := by
  simpa only [f1024TowerStageDirectPolynomial,
    QEC.Coding.AlgebraicGeometry.ArtinSchreier.artinSchreierPolynomial] using
      (QEC.Coding.AlgebraicGeometry.ArtinSchreier.artinSchreierPolynomial_monic
        (stage.x ^ 33))

private theorem f1024TowerStageDirectPolynomial_natDegree
    {height : ℕ} (stage : F1024TowerStageData height) :
    (f1024TowerStageDirectPolynomial stage).natDegree = 32 := by
  change (X ^ 32 + X - C (stage.x ^ 33) : stage.carrier[X]).natDegree = 32
  calc
    (X ^ 32 + X - C (stage.x ^ 33) : stage.carrier[X]).natDegree =
        (X ^ 32 + X : stage.carrier[X]).natDegree := natDegree_sub_C
    _ = (X ^ 32 : stage.carrier[X]).natDegree :=
      natDegree_add_eq_left_of_natDegree_lt (by norm_num)
    _ = 32 := natDegree_X_pow 32

/-- The direct polynomial defines the same degree-32 field extension as the
inverse polynomial used in `F1024TowerStageStep`.  The proof constructs the
actual map sending its root to `z`, recovers the inverse root as
`x^-32 * (z^31 + 1)`, and compares the two power-basis dimensions. -/
private theorem f1024TowerStageDirectPolynomial_irreducible
    {height : ℕ} (stage : F1024TowerStageData height) :
    Irreducible (f1024TowerStageDirectPolynomial stage) := by
  let g : stage.carrier[X] := f1024TowerStageDirectPolynomial stage
  let E : Type := F1024TowerStageStep stage
  let z : E := f1024TowerStageStepZ stage
  let v : E := f1024TowerStageStepRoot stage
  let u : E := algebraMap stage.carrier E stage.x
  have hu : u ≠ 0 := by
    dsimp [u, E]
    exact (map_ne_zero_iff
      (algebraMap stage.carrier (F1024TowerStageStep stage))
      (algebraMap stage.carrier (F1024TowerStageStep stage)).injective).mpr
        stage.x_ne_zero
  have hv : v ≠ 0 := by
    exact f1024TowerStageStepRoot_ne_zero stage
  have hz : z ≠ 0 := by
    dsimp [z, f1024TowerStageStepZ]
    exact div_ne_zero hu hv
  have hzEquation : z ^ 32 + z = u ^ 33 := by
    simpa only [z, u, map_pow] using f1024TowerStageStepZ_equation stage
  have hgroot : g.eval₂ (algebraMap stage.carrier E) z = 0 := by
    dsimp only [g, f1024TowerStageDirectPolynomial]
    simp only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C]
    rw [map_pow]
    exact sub_eq_zero.mpr hzEquation
  let phi : AdjoinRoot g →ₐ[stage.carrier] E :=
    AdjoinRoot.liftAlgHom g (Algebra.ofId stage.carrier E) z hgroot
  have hphiRoot : phi (AdjoinRoot.root g) = z := by
    exact AdjoinRoot.liftAlgHom_root g (Algebra.ofId stage.carrier E) z hgroot
  let preimageV : AdjoinRoot g :=
    algebraMap stage.carrier (AdjoinRoot g) (stage.x⁻¹ ^ 32) *
      (AdjoinRoot.root g ^ 31 + 1)
  have hpreimageV : phi preimageV = v := by
    have hquotient : u⁻¹ ^ 32 * (z ^ 31 + 1) = u / z := by
      apply (eq_div_iff hz).mpr
      calc
        u⁻¹ ^ 32 * (z ^ 31 + 1) * z =
            u⁻¹ ^ 32 * (z ^ 32 + z) := by ring
        _ = u⁻¹ ^ 32 * u ^ 33 := by rw [hzEquation]
        _ = (u⁻¹ ^ 32 * u ^ 32) * u := by ring
        _ = (u⁻¹ * u) ^ 32 * u := by rw [mul_pow]
        _ = u := by rw [inv_mul_cancel₀ hu, one_pow, one_mul]
    calc
      phi preimageV = u⁻¹ ^ 32 * (z ^ 31 + 1) := by
        calc
          phi preimageV =
              phi (algebraMap stage.carrier (AdjoinRoot g) (stage.x⁻¹ ^ 32)) *
                phi (AdjoinRoot.root g ^ 31 + 1) := by rw [map_mul]
          _ = algebraMap stage.carrier E (stage.x⁻¹ ^ 32) *
                (z ^ 31 + 1) := by
            rw [phi.commutes, map_add, map_pow phi, hphiRoot, map_one]
          _ = u⁻¹ ^ 32 * (z ^ 31 + 1) := by
            rw [map_pow, map_inv₀]
      _ = u / z := hquotient
      _ = v := by
        dsimp [u, z, v, f1024TowerStageStepZ]
        let u' : F1024TowerStageStep stage :=
          algebraMap stage.carrier (F1024TowerStageStep stage) stage.x
        let v' : F1024TowerStageStep stage := f1024TowerStageStepRoot stage
        have hu' : u' ≠ 0 := by simpa [u', u, E] using hu
        change u' / (u' * v'⁻¹) = v'
        rw [div_eq_mul_inv, mul_inv_rev, inv_inv]
        calc
          u' * (v' * u'⁻¹) = v' * (u' * u'⁻¹) := by ring
          _ = v' := by rw [mul_inv_cancel₀ hu', mul_one]
  have hvRange : v ∈ phi.range := ⟨preimageV, hpreimageV⟩
  have hphiSurjective : Function.Surjective phi := by
    rw [← AlgHom.range_eq_top]
    apply top_unique
    rw [← AdjoinRoot.adjoinRoot_eq_top
      (f := f1024TowerStageStepPolynomial stage)]
    apply Algebra.adjoin_le
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact hvRange
  letI : FiniteDimensional stage.carrier (AdjoinRoot g) :=
    (AdjoinRoot.powerBasis'
      (f1024TowerStageDirectPolynomial_monic stage)).basis.finiteDimensional_of_finite
  have hfinrank : Module.finrank stage.carrier (AdjoinRoot g) =
      Module.finrank stage.carrier E := by
    calc
      Module.finrank stage.carrier (AdjoinRoot g) = g.natDegree :=
        by exact finrank_quotient_span_eq_natDegree (f := g)
      _ = 32 := f1024TowerStageDirectPolynomial_natDegree stage
      _ = Module.finrank stage.carrier E :=
        (f1024TowerStageStep_finrank stage).symm
  have hphiInjective : Function.Injective phi :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := phi.toLinearMap) hfinrank).mpr hphiSurjective
  let e : AdjoinRoot g ≃ₐ[stage.carrier] E :=
    AlgEquiv.ofBijective phi ⟨hphiInjective, hphiSurjective⟩
  letI : IsDomain (AdjoinRoot g) := e.toMulEquiv.isDomain E
  have hspan : (Ideal.span ({g} : Set stage.carrier[X])).IsPrime := by
    apply (Ideal.Quotient.isDomain_iff_prime
      (Ideal.span ({g} : Set stage.carrier[X]))).mp
    change IsDomain (AdjoinRoot g)
    infer_instance
  have hgPrime : Prime g :=
    (Ideal.span_singleton_prime
      (f1024TowerStageDirectPolynomial_monic stage).ne_zero).mp hspan
  exact hgPrime.irreducible

/-- Constructed data for the finite split affine chart of one tower level.
Only rings, maps, coordinates, and their proved evaluation behavior are
retained.  In particular this record has no place, place count, genus, or
asymptotic field. -/
private structure F1024TowerFiniteChartData (height : ℕ) where
  carrier : Type
  [commRingInst : CommRing carrier]
  [domainInst : IsDomain carrier]
  [dedekindInst : IsDedekindDomain carrier]
  [constantAlgebraInst : Algebra F1024 carrier]
  [actualAlgebraInst : Algebra carrier (F1024TowerLevel height)]
  [constantTowerInst : IsScalarTower F1024 carrier (F1024TowerLevel height)]
  [fractionRingInst : IsFractionRing carrier (F1024TowerLevel height)]
  baseX : carrier
  baseX_map :
    algebraMap carrier (F1024TowerLevel height) baseX =
      algebraMap F1024TowerF1 (F1024TowerLevel height) RatFunc.X
  xUnit : carrierˣ
  xUnit_map :
    algebraMap carrier (F1024TowerLevel height) (xUnit : carrier) =
      f1024TowerLevelX height
  evaluate : F1024TowerFiniteCoordinate height → carrier →+* F1024
  evaluate_surjective : ∀ coordinate, Function.Surjective (evaluate coordinate)
  evaluate_constants : ∀ coordinate c,
    evaluate coordinate (algebraMap F1024 carrier c) = c
  evaluate_baseX : ∀ coordinate,
    evaluate coordinate baseX = coordinate.1
  evaluate_x : ∀ coordinate,
    evaluate coordinate xUnit = f1024TowerFiniteCoordinateValue coordinate
  evaluate_injective : Function.Injective evaluate

attribute [instance] F1024TowerFiniteChartData.commRingInst
  F1024TowerFiniteChartData.domainInst
  F1024TowerFiniteChartData.dedekindInst
  F1024TowerFiniteChartData.constantAlgebraInst
  F1024TowerFiniteChartData.actualAlgebraInst
  F1024TowerFiniteChartData.constantTowerInst
  F1024TowerFiniteChartData.fractionRingInst

/-- The direct affine polynomial with coefficients in a constructed finite
chart.  Its generic fibre is the direct polynomial over the actual tower
level. -/
private noncomputable def f1024TowerFiniteChartPolynomial {height : ℕ}
    (chart : F1024TowerFiniteChartData height) : chart.carrier[X] :=
  X ^ 32 + X - C ((chart.xUnit : chart.carrier) ^ 33)

private theorem f1024TowerFiniteChartPolynomial_monic {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    (f1024TowerFiniteChartPolynomial chart).Monic := by
  rw [f1024TowerFiniteChartPolynomial]
  convert monic_X_pow_add
    (p := X - C ((chart.xUnit : chart.carrier) ^ 33))
    (show degree (X - C ((chart.xUnit : chart.carrier) ^ 33)) <
        (32 : ℕ) by
      calc
        degree (X - C ((chart.xUnit : chart.carrier) ^ 33)) ≤ 1 :=
          degree_X_sub_C_le _
        _ < (32 : ℕ) := by norm_num) using 1
  all_goals ring

private theorem f1024TowerFiniteChartPolynomial_natDegree {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    (f1024TowerFiniteChartPolynomial chart).natDegree = 32 := by
  change (X ^ 32 + X - C ((chart.xUnit : chart.carrier) ^ 33) :
    chart.carrier[X]).natDegree = 32
  rw [show (X ^ 32 + X - C ((chart.xUnit : chart.carrier) ^ 33) :
      chart.carrier[X]) = X ^ 32 +
        (X - C ((chart.xUnit : chart.carrier) ^ 33)) by ring]
  rw [natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow 32
  · rw [natDegree_X_sub_C, natDegree_X_pow]
    norm_num

private theorem f1024TowerFiniteChartPolynomial_map {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    (f1024TowerFiniteChartPolynomial chart).map
        (algebraMap chart.carrier (F1024TowerLevel height)) =
      f1024TowerStageDirectPolynomial (f1024TowerStage height) := by
  simp only [f1024TowerFiniteChartPolynomial,
    f1024TowerStageDirectPolynomial, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, map_pow,
    chart.xUnit_map, f1024TowerLevelX]

private theorem f1024TowerFiniteChartPolynomial_irreducible {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    Irreducible (f1024TowerFiniteChartPolynomial chart) := by
  rw [(f1024TowerFiniteChartPolynomial_monic chart).irreducible_iff_irreducible_map_fraction_map
    (K := F1024TowerLevel height)]
  rw [f1024TowerFiniteChartPolynomial_map]
  exact f1024TowerStageDirectPolynomial_irreducible (f1024TowerStage height)

/-- The direct and inverse presentations of one generic tower step are the
same actual degree-32 field extension. -/
private noncomputable def f1024TowerStageDirectAlgEquiv
    {height : ℕ} (stage : F1024TowerStageData height) :
    AdjoinRoot (f1024TowerStageDirectPolynomial stage) ≃ₐ[stage.carrier]
      F1024TowerStageStep stage := by
  let g : stage.carrier[X] := f1024TowerStageDirectPolynomial stage
  let z : F1024TowerStageStep stage := f1024TowerStageStepZ stage
  have hz : g.eval₂
      (algebraMap stage.carrier (F1024TowerStageStep stage)) z = 0 := by
    dsimp only [g, f1024TowerStageDirectPolynomial]
    simp only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C]
    rw [map_pow]
    exact sub_eq_zero.mpr (by
      simpa only [z, map_pow] using f1024TowerStageStepZ_equation stage)
  let phi : AdjoinRoot g →ₐ[stage.carrier] F1024TowerStageStep stage :=
    AdjoinRoot.liftAlgHom g (Algebra.ofId stage.carrier _) z hz
  letI : Fact (Irreducible g) :=
    ⟨by simpa only [g] using f1024TowerStageDirectPolynomial_irreducible stage⟩
  letI : FiniteDimensional stage.carrier (AdjoinRoot g) :=
    (AdjoinRoot.powerBasis'
      (f1024TowerStageDirectPolynomial_monic stage)).basis.finiteDimensional_of_finite
  have hfinrank : Module.finrank stage.carrier (AdjoinRoot g) =
      Module.finrank stage.carrier (F1024TowerStageStep stage) := by
    calc
      Module.finrank stage.carrier (AdjoinRoot g) = g.natDegree :=
        by exact finrank_quotient_span_eq_natDegree (f := g)
      _ = 32 := f1024TowerStageDirectPolynomial_natDegree stage
      _ = Module.finrank stage.carrier (F1024TowerStageStep stage) :=
        (f1024TowerStageStep_finrank stage).symm
  have hphiInjective : Function.Injective phi := phi.injective
  have hphiSurjective : Function.Surjective phi :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := phi.toLinearMap) hfinrank).mp hphiInjective
  exact AlgEquiv.ofBijective phi ⟨hphiInjective, hphiSurjective⟩

private theorem f1024TowerStageDirectAlgEquiv_root
    {height : ℕ} (stage : F1024TowerStageData height) :
    f1024TowerStageDirectAlgEquiv stage
        (AdjoinRoot.root (f1024TowerStageDirectPolynomial stage)) =
      f1024TowerStageStepZ stage := by
  dsimp only [f1024TowerStageDirectAlgEquiv, AlgEquiv.ofBijective_apply]
  erw [AlgEquiv.ofBijective_apply, AdjoinRoot.liftAlgHom_root]

/-- The integral direct chart embeds in its generic direct fibre. -/
private noncomputable def f1024TowerFiniteChartGenericMap {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    AdjoinRoot (f1024TowerFiniteChartPolynomial chart) →+*
      AdjoinRoot (f1024TowerStageDirectPolynomial (f1024TowerStage height)) :=
  AdjoinRoot.map (algebraMap chart.carrier (F1024TowerLevel height))
    (f1024TowerFiniteChartPolynomial chart)
    (f1024TowerStageDirectPolynomial (f1024TowerStage height)) (by
      rw [f1024TowerFiniteChartPolynomial_map])

private theorem f1024TowerFiniteChartGenericMap_injective {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    Function.Injective (f1024TowerFiniteChartGenericMap chart) := by
  intro x y hxy
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
  apply AdjoinRoot.mk_eq_mk.mpr
  apply (Polynomial.map_dvd_map
    (algebraMap chart.carrier (F1024TowerLevel height))
    (IsFractionRing.injective chart.carrier (F1024TowerLevel height))
    (f1024TowerFiniteChartPolynomial_monic chart)).mp
  rw [Polynomial.map_sub, f1024TowerFiniteChartPolynomial_map]
  apply AdjoinRoot.mk_eq_mk.mp
  have hxy' := hxy
  simp only [f1024TowerFiniteChartGenericMap, AdjoinRoot.map,
    AdjoinRoot.lift_mk, ← Polynomial.eval₂_map] at hxy'
  change aeval
      (AdjoinRoot.root
        (f1024TowerStageDirectPolynomial (f1024TowerStage height)))
        (p.map (algebraMap chart.carrier (F1024TowerLevel height))) =
    aeval
      (AdjoinRoot.root
        (f1024TowerStageDirectPolynomial (f1024TowerStage height)))
        (q.map (algebraMap chart.carrier (F1024TowerLevel height))) at hxy'
  simpa only [AdjoinRoot.aeval_eq] using hxy'

private noncomputable abbrev F1024TowerFiniteChartStep {height : ℕ}
    (chart : F1024TowerFiniteChartData height) : Type :=
  AdjoinRoot (f1024TowerFiniteChartPolynomial chart)

private noncomputable instance f1024TowerFiniteChartStepDomain {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    IsDomain (F1024TowerFiniteChartStep chart) := by
  letI : Fact (Irreducible
      (f1024TowerStageDirectPolynomial (f1024TowerStage height))) :=
    ⟨f1024TowerStageDirectPolynomial_irreducible (f1024TowerStage height)⟩
  exact (f1024TowerFiniteChartGenericMap_injective chart).isDomain
    (f1024TowerFiniteChartGenericMap chart)

private noncomputable instance f1024TowerFiniteChartStepFinite {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    Module.Finite chart.carrier (F1024TowerFiniteChartStep chart) :=
  (f1024TowerFiniteChartPolynomial_monic chart).finite_adjoinRoot

private theorem f1024TowerFiniteChartPolynomial_derivative {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    derivative (f1024TowerFiniteChartPolynomial chart) = 1 := by
  letI : CharP chart.carrier 2 := charP_of_injective_algebraMap
    (algebraMap F1024 chart.carrier).injective 2
  have h32 : ((32 : ℕ) : chart.carrier) = 0 := by
    rw [CharP.cast_eq_zero_iff chart.carrier 2]
    norm_num
  simp only [f1024TowerFiniteChartPolynomial, derivative_sub, derivative_add,
    derivative_X_pow, derivative_X, derivative_C, h32, C_0, zero_mul,
    zero_add, sub_zero]

private noncomputable def f1024TowerFiniteChartEtalePair {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    StandardEtalePair chart.carrier where
  f := f1024TowerFiniteChartPolynomial chart
  monic_f := f1024TowerFiniteChartPolynomial_monic chart
  g := 1
  cond := ⟨1, 0, 1, by
    rw [f1024TowerFiniteChartPolynomial_derivative]
    simp⟩

private noncomputable def f1024TowerFiniteChartStepEtaleEquiv {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    (f1024TowerFiniteChartEtalePair chart).Ring ≃ₐ[chart.carrier]
      F1024TowerFiniteChartStep chart := by
  let P : StandardEtalePair chart.carrier :=
    f1024TowerFiniteChartEtalePair chart
  let B : Type := F1024TowerFiniteChartStep chart
  let r : B := AdjoinRoot.mk P.f P.g
  have hr : IsUnit r := by
    change IsUnit
      (AdjoinRoot.mk (f1024TowerFiniteChartPolynomial chart)
        (1 : chart.carrier[X]))
    rw [map_one]
    exact isUnit_one
  letI : IsLocalization (Submonoid.powers r) B :=
    IsLocalization.of_le_isUnit (Submonoid.powers_le.mpr hr)
  exact P.equivAwayAdjoinRoot.trans
    ((IsLocalization.algEquiv (Submonoid.powers r)
      (Localization.Away r) B).restrictScalars chart.carrier)

private noncomputable instance f1024TowerFiniteChartStepFormallyUnramified
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    Algebra.FormallyUnramified chart.carrier
      (F1024TowerFiniteChartStep chart) :=
  Algebra.FormallyUnramified.of_equiv
    (f1024TowerFiniteChartStepEtaleEquiv chart)

private noncomputable instance f1024TowerFiniteChartStepDedekind {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    IsDedekindDomain (F1024TowerFiniteChartStep chart) :=
  isDedekindDomain.of_formallyUnramified chart.carrier
    (F1024TowerFiniteChartStep chart)

private noncomputable def f1024TowerFiniteChartStepToActual {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    F1024TowerFiniteChartStep chart →+* F1024TowerLevel (height + 1) :=
  (f1024TowerStageDirectAlgEquiv
    (f1024TowerStage height)).toRingEquiv.toRingHom.comp
      (f1024TowerFiniteChartGenericMap chart)

private theorem f1024TowerFiniteChartStepToActual_injective {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    Function.Injective (f1024TowerFiniteChartStepToActual chart) :=
  (f1024TowerStageDirectAlgEquiv
    (f1024TowerStage height)).injective.comp
      (f1024TowerFiniteChartGenericMap_injective chart)

private noncomputable instance f1024TowerFiniteChartToNextActualAlgebra
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    Algebra chart.carrier (F1024TowerLevel (height + 1)) :=
  ((algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))).comp
    (algebraMap chart.carrier (F1024TowerLevel height))).toAlgebra

private noncomputable instance f1024TowerFiniteChartToNextActualTower
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    IsScalarTower chart.carrier (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  rfl

private noncomputable instance f1024TowerFiniteChartStepActualAlgebra
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    Algebra (F1024TowerFiniteChartStep chart)
      (F1024TowerLevel (height + 1)) :=
  (f1024TowerFiniteChartStepToActual chart).toAlgebra

private noncomputable instance f1024TowerFiniteChartStepActualSMul
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    SMul (F1024TowerFiniteChartStep chart)
      (F1024TowerLevel (height + 1)) :=
  (f1024TowerFiniteChartStepActualAlgebra chart).toSMul

private noncomputable instance f1024TowerFiniteChartStepActualTower
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    IsScalarTower chart.carrier (F1024TowerFiniteChartStep chart)
      (F1024TowerLevel (height + 1)) := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap chart.carrier (F1024TowerLevel (height + 1)) a =
    f1024TowerFiniteChartStepToActual chart
      (algebraMap chart.carrier (F1024TowerFiniteChartStep chart) a)
  have hgeneric :
      f1024TowerFiniteChartGenericMap chart
          (algebraMap chart.carrier (F1024TowerFiniteChartStep chart) a) =
        algebraMap (F1024TowerLevel height)
          (AdjoinRoot
            (f1024TowerStageDirectPolynomial (f1024TowerStage height)))
          (algebraMap chart.carrier (F1024TowerLevel height) a) := by
    change AdjoinRoot.map
        (algebraMap chart.carrier (F1024TowerLevel height))
        (f1024TowerFiniteChartPolynomial chart)
        (f1024TowerStageDirectPolynomial (f1024TowerStage height)) _
        (AdjoinRoot.of (f1024TowerFiniteChartPolynomial chart) a) = _
    rw [AdjoinRoot.map_of, AdjoinRoot.algebraMap_eq]
  change algebraMap chart.carrier (F1024TowerLevel (height + 1)) a =
    f1024TowerStageDirectAlgEquiv (f1024TowerStage height)
      (f1024TowerFiniteChartGenericMap chart
        (algebraMap chart.carrier (F1024TowerFiniteChartStep chart) a))
  rw [hgeneric]
  change algebraMap (F1024TowerLevel height)
      (F1024TowerLevel (height + 1))
      (algebraMap chart.carrier (F1024TowerLevel height) a) =
    f1024TowerStageDirectAlgEquiv (f1024TowerStage height)
      (algebraMap (F1024TowerLevel height)
        (AdjoinRoot
          (f1024TowerStageDirectPolynomial (f1024TowerStage height)))
        (algebraMap chart.carrier (F1024TowerLevel height) a))
  exact ((f1024TowerStageDirectAlgEquiv
    (f1024TowerStage height)).commutes
      (algebraMap chart.carrier (F1024TowerLevel height) a)).symm

/-- The actual next tower field is the fraction field of its finite affine
chart.  Surjectivity is proved from the direct `AdjoinRoot` presentation:
coefficients already lie in the old chart's fraction field, and the direct
root is the image of the new chart root. -/
private noncomputable instance f1024TowerFiniteChartStepFractionRing
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    IsFractionRing (F1024TowerFiniteChartStep chart)
      (F1024TowerLevel (height + 1)) := by
  let B : Type := F1024TowerFiniteChartStep chart
  let L : Type := FractionRing B
  let phi : L →ₐ[B] F1024TowerLevel (height + 1) :=
    IsFractionRing.liftAlgHom
      (g := Algebra.ofId B (F1024TowerLevel (height + 1)))
      (f1024TowerFiniteChartStepToActual_injective chart)
  have hphiSurjective : Function.Surjective phi := by
    intro y
    let direct :
        AdjoinRoot
            (f1024TowerStageDirectPolynomial (f1024TowerStage height)) ≃ₐ[
              F1024TowerLevel height]
          F1024TowerLevel (height + 1) :=
      f1024TowerStageDirectAlgEquiv (f1024TowerStage height)
    have hdirectRoot : direct
        (AdjoinRoot.root
          (f1024TowerStageDirectPolynomial (f1024TowerStage height))) =
        f1024TowerStageStepZ (f1024TowerStage height) := by
      change f1024TowerStageDirectAlgEquiv (f1024TowerStage height)
          (AdjoinRoot.root
            (f1024TowerStageDirectPolynomial (f1024TowerStage height))) = _
      exact f1024TowerStageDirectAlgEquiv_root (f1024TowerStage height)
    obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (direct.symm y)
    let baseMap : chart.carrier →+* L :=
      (algebraMap B L).comp
        (algebraMap chart.carrier B)
    have hchartToActual : Function.Injective
        (algebraMap chart.carrier (F1024TowerLevel (height + 1))) :=
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1))).injective.comp
          (IsFractionRing.injective chart.carrier (F1024TowerLevel height))
    have hchartToB : Function.Injective
        (algebraMap chart.carrier B) := by
      intro a b hab
      apply hchartToActual
      calc
        algebraMap chart.carrier (F1024TowerLevel (height + 1)) a =
            algebraMap B (F1024TowerLevel (height + 1))
              (algebraMap chart.carrier B a) :=
          IsScalarTower.algebraMap_apply chart.carrier B
            (F1024TowerLevel (height + 1)) a
        _ = algebraMap B (F1024TowerLevel (height + 1))
              (algebraMap chart.carrier B b) := by rw [hab]
        _ = algebraMap chart.carrier (F1024TowerLevel (height + 1)) b :=
          (IsScalarTower.algebraMap_apply chart.carrier B
            (F1024TowerLevel (height + 1)) b).symm
    have hbaseMap : Function.Injective baseMap :=
      (IsFractionRing.injective B L).comp hchartToB
    let coeffLift : F1024TowerLevel height →+* L :=
      IsFractionRing.lift hbaseMap
    have hcoeff : phi.toRingHom.comp coeffLift =
        algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1)) := by
      apply IsFractionRing.ringHom_ext (A := chart.carrier)
      intro a
      change phi (coeffLift
          (algebraMap chart.carrier (F1024TowerLevel height) a)) =
        algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1))
          (algebraMap chart.carrier (F1024TowerLevel height) a)
      rw [IsFractionRing.lift_algebraMap hbaseMap]
      change phi
          (algebraMap B L (algebraMap chart.carrier B a)) = _
      rw [phi.commutes]
      rw [← IsScalarTower.algebraMap_apply chart.carrier B
        (F1024TowerLevel (height + 1))]
      rw [← IsScalarTower.algebraMap_apply chart.carrier
        (F1024TowerLevel height) (F1024TowerLevel (height + 1))]
    have hroot : phi
        (algebraMap B L
          (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart))) =
        f1024TowerStageStepZ (f1024TowerStage height) := by
      rw [phi.commutes]
      change f1024TowerFiniteChartStepToActual chart
          (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart)) = _
      rw [f1024TowerFiniteChartStepToActual]
      change f1024TowerStageDirectAlgEquiv (f1024TowerStage height)
          (f1024TowerFiniteChartGenericMap chart
            (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart))) = _
      rw [f1024TowerFiniteChartGenericMap, AdjoinRoot.map_root]
      exact f1024TowerStageDirectAlgEquiv_root (f1024TowerStage height)
    refine ⟨p.eval₂ coeffLift
      (algebraMap B L
        (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart))), ?_⟩
    calc
      phi (p.eval₂ coeffLift
          (algebraMap B L
            (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart)))) =
          p.eval₂ (phi.toRingHom.comp coeffLift)
            (phi (algebraMap B L
                (AdjoinRoot.root
                (f1024TowerFiniteChartPolynomial chart)))) := by
            exact Polynomial.hom_eval₂ (p := p) coeffLift phi.toRingHom _
      _ = p.eval₂
          (algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)))
          (f1024TowerStageStepZ (f1024TowerStage height)) := by
            rw [hcoeff, hroot]
      _ = direct (AdjoinRoot.mk
          (f1024TowerStageDirectPolynomial (f1024TowerStage height)) p) := by
            symm
            rw [← AdjoinRoot.aeval_eq]
            calc
              direct
                  (p.eval₂
                    (algebraMap (F1024TowerLevel height)
                      (AdjoinRoot
                        (f1024TowerStageDirectPolynomial
                          (f1024TowerStage height))))
                    (AdjoinRoot.root
                      (f1024TowerStageDirectPolynomial
                        (f1024TowerStage height)))) =
                  p.eval₂
                    (direct.toRingHom.comp
                      (algebraMap (F1024TowerLevel height)
                        (AdjoinRoot
                          (f1024TowerStageDirectPolynomial
                            (f1024TowerStage height)))))
                    (direct
                      (AdjoinRoot.root
                        (f1024TowerStageDirectPolynomial
                          (f1024TowerStage height)))) :=
                Polynomial.hom_eval₂ (p := p)
                  (algebraMap (F1024TowerLevel height)
                    (AdjoinRoot
                      (f1024TowerStageDirectPolynomial
                        (f1024TowerStage height)))) direct.toRingHom _
              _ = p.eval₂
                  (algebraMap (F1024TowerLevel height)
                    (F1024TowerLevel (height + 1)))
                  (f1024TowerStageStepZ (f1024TowerStage height)) := by
                rw [show direct.toRingHom.comp
                    (algebraMap (F1024TowerLevel height)
                      (AdjoinRoot
                        (f1024TowerStageDirectPolynomial
                          (f1024TowerStage height)))) =
                    algebraMap (F1024TowerLevel height)
                      (F1024TowerLevel (height + 1)) by
                  ext a
                  exact direct.commutes a]
                rw [hdirectRoot]
      _ = y := by rw [hp, direct.apply_symm_apply]
  exact IsFractionRing.of_algEquiv
    (AlgEquiv.ofBijective phi ⟨phi.injective, hphiSurjective⟩)

private theorem f1024TowerFiniteChartStepRoot_equation
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart) ^ 32 +
        AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart) =
      algebraMap chart.carrier (F1024TowerFiniteChartStep chart)
        ((chart.xUnit : chart.carrier) ^ 33) := by
  apply sub_eq_zero.mp
  have hroot := AdjoinRoot.eval₂_root
    (f1024TowerFiniteChartPolynomial chart)
  change (X ^ 32 + X - C ((chart.xUnit : chart.carrier) ^ 33) :
      chart.carrier[X]).eval₂
        (AdjoinRoot.of (f1024TowerFiniteChartPolynomial chart))
        (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart)) = 0 at hroot
  have hport := hroot
  simp only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C] at hport ⊢
  exact hport

private noncomputable def f1024TowerFiniteChartMappedXUnit
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    (F1024TowerFiniteChartStep chart)ˣ :=
  Units.map (algebraMap chart.carrier (F1024TowerFiniteChartStep chart))
    chart.xUnit

private theorem f1024TowerFiniteChartStepRoot_isUnit
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    IsUnit (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart)) := by
  let r : F1024TowerFiniteChartStep chart :=
    AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart)
  let u : (F1024TowerFiniteChartStep chart)ˣ :=
    f1024TowerFiniteChartMappedXUnit chart
  have hfactor : r * (r ^ 31 + 1) = (u : F1024TowerFiniteChartStep chart) ^ 33 := by
    calc
      r * (r ^ 31 + 1) = r ^ 32 + r := by ring
      _ = algebraMap chart.carrier (F1024TowerFiniteChartStep chart)
          ((chart.xUnit : chart.carrier) ^ 33) :=
        f1024TowerFiniteChartStepRoot_equation chart
      _ = (u : F1024TowerFiniteChartStep chart) ^ 33 := by
        simp only [u, f1024TowerFiniteChartMappedXUnit, Units.coe_map, map_pow]
        rfl
  have hrightInverse :
      r * ((r ^ 31 + 1) * ((u⁻¹ :
          (F1024TowerFiniteChartStep chart)ˣ) :
            F1024TowerFiniteChartStep chart) ^ 33) = 1 := by
    calc
      r * ((r ^ 31 + 1) * ((u⁻¹ :
          (F1024TowerFiniteChartStep chart)ˣ) :
            F1024TowerFiniteChartStep chart) ^ 33) =
          (r * (r ^ 31 + 1)) *
            ((u⁻¹ : (F1024TowerFiniteChartStep chart)ˣ) :
              F1024TowerFiniteChartStep chart) ^ 33 := by ring
      _ = (u : F1024TowerFiniteChartStep chart) ^ 33 *
            ((u⁻¹ : (F1024TowerFiniteChartStep chart)ˣ) :
              F1024TowerFiniteChartStep chart) ^ 33 := by rw [hfactor]
      _ = (((u : F1024TowerFiniteChartStep chart) *
            ((u⁻¹ : (F1024TowerFiniteChartStep chart)ˣ) :
              F1024TowerFiniteChartStep chart)) ^ 33) := by rw [mul_pow]
      _ = 1 := by simp
  exact isUnit_of_dvd_one ⟨_, hrightInverse.symm⟩

private noncomputable def f1024TowerFiniteChartStepRootUnit
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    (F1024TowerFiniteChartStep chart)ˣ :=
  (f1024TowerFiniteChartStepRoot_isUnit chart).unit

private theorem f1024TowerFiniteChartStepRootUnit_coe
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    (f1024TowerFiniteChartStepRootUnit chart :
      F1024TowerFiniteChartStep chart) =
        AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart) :=
  IsUnit.unit_spec (f1024TowerFiniteChartStepRoot_isUnit chart)

private noncomputable def f1024TowerFiniteChartStepXUnit
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    (F1024TowerFiniteChartStep chart)ˣ :=
  f1024TowerFiniteChartStepRootUnit chart *
    (f1024TowerFiniteChartMappedXUnit chart)⁻¹

private theorem f1024TowerFiniteChartStepToActual_root
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    f1024TowerFiniteChartStepToActual chart
        (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart)) =
      f1024TowerLevelZ height := by
  rw [f1024TowerFiniteChartStepToActual]
  change f1024TowerStageDirectAlgEquiv (f1024TowerStage height)
      (f1024TowerFiniteChartGenericMap chart
        (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart))) = _
  rw [f1024TowerFiniteChartGenericMap, AdjoinRoot.map_root]
  exact f1024TowerStageDirectAlgEquiv_root (f1024TowerStage height)

private theorem f1024TowerFiniteChartStepXUnit_map
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    algebraMap (F1024TowerFiniteChartStep chart)
        (F1024TowerLevel (height + 1))
        (f1024TowerFiniteChartStepXUnit chart :
          F1024TowerFiniteChartStep chart) =
      f1024TowerLevelX (height + 1) := by
  have hxMap : algebraMap (F1024TowerFiniteChartStep chart)
      (F1024TowerLevel (height + 1))
      (f1024TowerFiniteChartMappedXUnit chart :
        F1024TowerFiniteChartStep chart) =
      algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
        (f1024TowerLevelX height) := by
    calc
      f1024TowerFiniteChartStepToActual chart
          (algebraMap chart.carrier (F1024TowerFiniteChartStep chart)
            (chart.xUnit : chart.carrier)) =
        algebraMap chart.carrier (F1024TowerLevel (height + 1))
          (chart.xUnit : chart.carrier) :=
            (IsScalarTower.algebraMap_apply chart.carrier
              (F1024TowerFiniteChartStep chart)
              (F1024TowerLevel (height + 1)) _).symm
      _ = algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
          (algebraMap chart.carrier (F1024TowerLevel height)
            (chart.xUnit : chart.carrier)) :=
            IsScalarTower.algebraMap_apply chart.carrier
              (F1024TowerLevel height) (F1024TowerLevel (height + 1)) _
      _ = algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
          (f1024TowerLevelX height) := by rw [chart.xUnit_map]
  have hrootMap : algebraMap (F1024TowerFiniteChartStep chart)
      (F1024TowerLevel (height + 1))
      (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart)) =
      f1024TowerLevelZ height := by
    change f1024TowerFiniteChartStepToActual chart
        (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart)) = _
    exact f1024TowerFiniteChartStepToActual_root chart
  rw [f1024TowerFiniteChartStepXUnit, Units.val_mul, map_mul]
  rw [map_units_inv, f1024TowerFiniteChartStepRootUnit_coe,
    hrootMap, hxMap]
  rw [← div_eq_mul_inv]
  apply (div_eq_iff (map_ne_zero_iff
    (algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1)))
    (algebraMap (F1024TowerLevel height)
      (F1024TowerLevel (height + 1))).injective |>.mpr
        (f1024TowerLevelX_ne_zero height))).mpr
  simpa only [mul_comm] using (f1024TowerLevel_X_mul_nextX height).symm

private noncomputable def f1024TowerFiniteChartStepBaseX
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    F1024TowerFiniteChartStep chart :=
  algebraMap chart.carrier (F1024TowerFiniteChartStep chart) chart.baseX

private theorem f1024TowerFiniteChartStepBaseX_map
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    algebraMap (F1024TowerFiniteChartStep chart)
        (F1024TowerLevel (height + 1))
        (f1024TowerFiniteChartStepBaseX chart) =
      algebraMap F1024TowerF1 (F1024TowerLevel (height + 1)) RatFunc.X := by
  calc
    algebraMap (F1024TowerFiniteChartStep chart)
        (F1024TowerLevel (height + 1))
        (f1024TowerFiniteChartStepBaseX chart) =
      algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
        (algebraMap chart.carrier (F1024TowerLevel height) chart.baseX) := by
          rw [f1024TowerFiniteChartStepBaseX,
            ← IsScalarTower.algebraMap_apply chart.carrier
              (F1024TowerFiniteChartStep chart)
              (F1024TowerLevel (height + 1)),
            ← IsScalarTower.algebraMap_apply chart.carrier
              (F1024TowerLevel height) (F1024TowerLevel (height + 1))]
    _ = algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
        (algebraMap F1024TowerF1 (F1024TowerLevel height) RatFunc.X) := by
          rw [chart.baseX_map]
    _ = algebraMap F1024TowerF1 (F1024TowerLevel (height + 1)) RatFunc.X := by
          rfl

private noncomputable instance f1024TowerFiniteChartStepConstantToChartTower
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    IsScalarTower F1024 chart.carrier (F1024TowerFiniteChartStep chart) :=
  inferInstance

private noncomputable instance f1024TowerFiniteChartStepConstantActualTower
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    IsScalarTower F1024 (F1024TowerFiniteChartStep chart)
      (F1024TowerLevel (height + 1)) := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  calc
    algebraMap F1024 (F1024TowerLevel (height + 1)) c =
        algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
          (algebraMap F1024 (F1024TowerLevel height) c) := by rfl
    _ = algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
        (algebraMap chart.carrier (F1024TowerLevel height)
          (algebraMap F1024 chart.carrier c)) := by
            congr 1
            exact IsScalarTower.algebraMap_apply F1024 chart.carrier
              (F1024TowerLevel height) c
    _ = algebraMap chart.carrier (F1024TowerLevel (height + 1))
        (algebraMap F1024 chart.carrier c) :=
          (IsScalarTower.algebraMap_apply chart.carrier
            (F1024TowerLevel height) (F1024TowerLevel (height + 1)) _).symm
    _ = algebraMap (F1024TowerFiniteChartStep chart)
        (F1024TowerLevel (height + 1))
        (algebraMap chart.carrier (F1024TowerFiniteChartStep chart)
          (algebraMap F1024 chart.carrier c)) :=
          IsScalarTower.algebraMap_apply chart.carrier
            (F1024TowerFiniteChartStep chart)
            (F1024TowerLevel (height + 1)) _
    _ = algebraMap (F1024TowerFiniteChartStep chart)
        (F1024TowerLevel (height + 1))
        (algebraMap F1024 (F1024TowerFiniteChartStep chart) c) := by
          rfl

private noncomputable def f1024TowerFiniteChartStepEvaluate
    {height : ℕ} (chart : F1024TowerFiniteChartData height)
    (coordinate : F1024TowerFiniteCoordinate (height + 1)) :
    F1024TowerFiniteChartStep chart →+* F1024 := by
  let previous := f1024TowerFiniteCoordinatePrefix coordinate
  let z := f1024TowerFiniteCoordinateStepZ coordinate
  apply AdjoinRoot.lift (chart.evaluate previous) z
  change (f1024TowerFiniteChartPolynomial chart).eval₂
      (chart.evaluate previous) z = 0
  simp only [f1024TowerFiniteChartPolynomial, eval₂_sub, eval₂_add,
    eval₂_pow, eval₂_X, eval₂_C, map_pow]
  rw [chart.evaluate_x]
  exact sub_eq_zero.mpr (f1024TowerFiniteCoordinate_step_equation coordinate)

private theorem f1024TowerFiniteChartStepEvaluate_of
    {height : ℕ} (chart : F1024TowerFiniteChartData height)
    (coordinate : F1024TowerFiniteCoordinate (height + 1))
    (a : chart.carrier) :
    f1024TowerFiniteChartStepEvaluate chart coordinate
        (algebraMap chart.carrier (F1024TowerFiniteChartStep chart) a) =
      chart.evaluate (f1024TowerFiniteCoordinatePrefix coordinate) a := by
  simp [f1024TowerFiniteChartStepEvaluate]

private theorem f1024TowerFiniteChartStepEvaluate_root
    {height : ℕ} (chart : F1024TowerFiniteChartData height)
    (coordinate : F1024TowerFiniteCoordinate (height + 1)) :
    f1024TowerFiniteChartStepEvaluate chart coordinate
        (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart)) =
      f1024TowerFiniteCoordinateStepZ coordinate := by
  simp [f1024TowerFiniteChartStepEvaluate]

private theorem f1024ArtinSchreierSolution_injective (a : F1024) :
    Function.Injective (f1024ArtinSchreierSolution a) := by
  intro left right heq
  apply f1024TowerStepLabelEmbedding.injective
  exact add_left_cancel (by
    have hport := heq
    simp only [f1024ArtinSchreierSolution] at hport ⊢
    exact hport)

private theorem f1024TowerFiniteChartStepEvaluate_injective
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    Function.Injective (f1024TowerFiniteChartStepEvaluate chart) := by
  intro coordinate other hmaps
  have hprefixMaps :
      chart.evaluate (f1024TowerFiniteCoordinatePrefix coordinate) =
        chart.evaluate (f1024TowerFiniteCoordinatePrefix other) := by
    ext a
    have h := DFunLike.congr_fun hmaps
      (algebraMap chart.carrier (F1024TowerFiniteChartStep chart) a)
    simpa only [f1024TowerFiniteChartStepEvaluate_of] using h
  have hprefix : f1024TowerFiniteCoordinatePrefix coordinate =
      f1024TowerFiniteCoordinatePrefix other :=
    chart.evaluate_injective hprefixMaps
  have hroot := DFunLike.congr_fun hmaps
    (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart))
  have hz : f1024TowerFiniteCoordinateStepZ coordinate =
      f1024TowerFiniteCoordinateStepZ other := by
    simpa only [f1024TowerFiniteChartStepEvaluate_root] using hroot
  have hlast : coordinate.2 (Fin.last height) =
      other.2 (Fin.last height) := by
    apply f1024ArtinSchreierSolution_injective
      (f1024TowerFiniteCoordinateValue
        (f1024TowerFiniteCoordinatePrefix other))
    simpa only [f1024TowerFiniteCoordinateStepZ, hprefix] using hz
  apply Prod.ext
  · exact congrArg
      (fun value : F1024TowerFiniteCoordinate height => value.1) hprefix
  · funext i
    refine Fin.lastCases hlast (fun previousIndex => ?_) i
    have hfunction := congrArg
      (fun value : F1024TowerFiniteCoordinate height => value.2) hprefix
    exact congrFun hfunction previousIndex

private theorem f1024TowerFiniteChartStepEvaluate_constants
    {height : ℕ} (chart : F1024TowerFiniteChartData height)
    (coordinate : F1024TowerFiniteCoordinate (height + 1)) (c : F1024) :
    f1024TowerFiniteChartStepEvaluate chart coordinate
        (algebraMap F1024 (F1024TowerFiniteChartStep chart) c) = c := by
  change f1024TowerFiniteChartStepEvaluate chart coordinate
      (algebraMap chart.carrier (F1024TowerFiniteChartStep chart)
        (algebraMap F1024 chart.carrier c)) = c
  rw [f1024TowerFiniteChartStepEvaluate_of, chart.evaluate_constants]

private theorem f1024TowerFiniteChartStepEvaluate_baseX
    {height : ℕ} (chart : F1024TowerFiniteChartData height)
    (coordinate : F1024TowerFiniteCoordinate (height + 1)) :
    f1024TowerFiniteChartStepEvaluate chart coordinate
        (f1024TowerFiniteChartStepBaseX chart) = coordinate.1 := by
  rw [f1024TowerFiniteChartStepBaseX,
    f1024TowerFiniteChartStepEvaluate_of, chart.evaluate_baseX]
  rfl

private theorem f1024TowerFiniteChartStepEvaluate_xUnit
    {height : ℕ} (chart : F1024TowerFiniteChartData height)
    (coordinate : F1024TowerFiniteCoordinate (height + 1)) :
    f1024TowerFiniteChartStepEvaluate chart coordinate
        (f1024TowerFiniteChartStepXUnit chart :
          F1024TowerFiniteChartStep chart) =
      f1024TowerFiniteCoordinateValue coordinate := by
  have hxPrevious : f1024TowerFiniteChartStepEvaluate chart coordinate
      (f1024TowerFiniteChartMappedXUnit chart :
        F1024TowerFiniteChartStep chart) =
      f1024TowerFiniteCoordinateValue
        (f1024TowerFiniteCoordinatePrefix coordinate) := by
    change f1024TowerFiniteChartStepEvaluate chart coordinate
        (algebraMap chart.carrier (F1024TowerFiniteChartStep chart)
          (chart.xUnit : chart.carrier)) = _
    rw [f1024TowerFiniteChartStepEvaluate_of, chart.evaluate_x]
  rw [f1024TowerFiniteChartStepXUnit, Units.val_mul, map_mul, map_units_inv,
    f1024TowerFiniteChartStepRootUnit_coe,
    f1024TowerFiniteChartStepEvaluate_root, hxPrevious]
  simpa only [div_eq_mul_inv] using
    (f1024TowerFiniteCoordinateValue_succ coordinate).symm

private noncomputable def f1024TowerFiniteChartStepData
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    F1024TowerFiniteChartData (height + 1) where
  carrier := F1024TowerFiniteChartStep chart
  commRingInst := inferInstance
  domainInst := inferInstance
  dedekindInst := inferInstance
  constantAlgebraInst := inferInstance
  actualAlgebraInst := f1024TowerFiniteChartStepActualAlgebra chart
  constantTowerInst := f1024TowerFiniteChartStepConstantActualTower chart
  fractionRingInst := f1024TowerFiniteChartStepFractionRing chart
  baseX := f1024TowerFiniteChartStepBaseX chart
  baseX_map := f1024TowerFiniteChartStepBaseX_map chart
  xUnit := f1024TowerFiniteChartStepXUnit chart
  xUnit_map := f1024TowerFiniteChartStepXUnit_map chart
  evaluate := f1024TowerFiniteChartStepEvaluate chart
  evaluate_surjective := by
    intro coordinate c
    refine ⟨algebraMap F1024 (F1024TowerFiniteChartStep chart) c, ?_⟩
    exact f1024TowerFiniteChartStepEvaluate_constants chart coordinate c
  evaluate_constants := f1024TowerFiniteChartStepEvaluate_constants chart
  evaluate_baseX := f1024TowerFiniteChartStepEvaluate_baseX chart
  evaluate_x := f1024TowerFiniteChartStepEvaluate_xUnit chart
  evaluate_injective := f1024TowerFiniteChartStepEvaluate_injective chart

private noncomputable abbrev F1024TowerFiniteBaseChart : Type :=
  Localization.Away (Polynomial.X : F1024[X])

private theorem f1024TowerFiniteBasePowers_le_nonZeroDivisors :
    Submonoid.powers (Polynomial.X : F1024[X]) ≤
      nonZeroDivisors F1024[X] :=
  powers_le_nonZeroDivisors_of_noZeroDivisors
    (Polynomial.X_ne_zero : (Polynomial.X : F1024[X]) ≠ 0)

private noncomputable instance f1024TowerFiniteBaseChartDomain :
    IsDomain F1024TowerFiniteBaseChart :=
  IsLocalization.isDomain_of_le_nonZeroDivisors F1024TowerFiniteBaseChart
    f1024TowerFiniteBasePowers_le_nonZeroDivisors

private noncomputable instance f1024TowerFiniteBaseChartDedekind :
    IsDedekindDomain F1024TowerFiniteBaseChart := by
  exact IsLocalization.isDedekindDomain F1024[X]
    f1024TowerFiniteBasePowers_le_nonZeroDivisors
    F1024TowerFiniteBaseChart

private noncomputable def f1024TowerFiniteBaseChartToF1 :
    F1024TowerFiniteBaseChart →ₐ[F1024] F1024TowerF1 := by
  apply IsLocalization.liftAlgHom
    (M := Submonoid.powers (Polynomial.X : F1024[X]))
    (f := IsScalarTower.toAlgHom F1024 F1024[X] F1024TowerF1)
  rintro ⟨_, n, rfl⟩
  change IsUnit (algebraMap F1024[X] F1024TowerF1 (Polynomial.X ^ n))
  rw [map_pow, RatFunc.algebraMap_X]
  exact (isUnit_iff_ne_zero).mpr (pow_ne_zero n RatFunc.X_ne_zero)

private noncomputable instance f1024TowerFiniteBaseChartActualAlgebra :
    Algebra F1024TowerFiniteBaseChart F1024TowerF1 :=
  f1024TowerFiniteBaseChartToF1.toRingHom.toAlgebra

private noncomputable instance f1024TowerFiniteBaseChartActualSMul :
    SMul F1024TowerFiniteBaseChart F1024TowerF1 :=
  f1024TowerFiniteBaseChartActualAlgebra.toSMul

private noncomputable instance f1024TowerFiniteBaseChartPolynomialTower :
    IsScalarTower F1024[X] F1024TowerFiniteBaseChart F1024TowerF1 := by
  apply IsScalarTower.of_algebraMap_eq
  intro p
  exact (IsLocalization.lift_eq _ p).symm

private noncomputable instance f1024TowerFiniteBaseChartConstantTower :
    IsScalarTower F1024 F1024TowerFiniteBaseChart F1024TowerF1 := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact (f1024TowerFiniteBaseChartToF1.commutes c).symm

private noncomputable instance f1024TowerFiniteBaseChartFractionRing :
    IsFractionRing F1024TowerFiniteBaseChart F1024TowerF1 :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (Polynomial.X : F1024[X]))
    F1024TowerFiniteBaseChart F1024TowerF1

private noncomputable def f1024TowerFiniteBaseXUnit :
    F1024TowerFiniteBaseChartˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (S := F1024TowerFiniteBaseChart) (Polynomial.X : F1024[X])).unit

private theorem f1024TowerFiniteBaseXUnit_coe :
    (f1024TowerFiniteBaseXUnit : F1024TowerFiniteBaseChart) =
      algebraMap F1024[X] F1024TowerFiniteBaseChart Polynomial.X :=
  IsUnit.unit_spec (IsLocalization.Away.algebraMap_isUnit
    (S := F1024TowerFiniteBaseChart) (Polynomial.X : F1024[X]))

private noncomputable def f1024TowerFiniteBaseEvaluate (a : F1024ˣ) :
    F1024TowerFiniteBaseChart →ₐ[F1024] F1024 := by
  apply IsLocalization.liftAlgHom
    (M := Submonoid.powers (Polynomial.X : F1024[X]))
    (f := aeval (a : F1024))
  rintro ⟨_, n, rfl⟩
  change IsUnit (aeval (a : F1024) (Polynomial.X ^ n))
  rw [map_pow, aeval_X]
  exact (isUnit_iff_ne_zero).mpr (pow_ne_zero n (Units.ne_zero a))

private theorem f1024TowerFiniteBaseEvaluate_X (a : F1024ˣ) :
    f1024TowerFiniteBaseEvaluate a
        (algebraMap F1024[X] F1024TowerFiniteBaseChart Polynomial.X) = a := by
  change IsLocalization.lift _
      (algebraMap F1024[X] F1024TowerFiniteBaseChart Polynomial.X) =
    (a : F1024)
  rw [IsLocalization.lift_eq]
  change aeval (a : F1024) Polynomial.X = (a : F1024)
  exact Polynomial.aeval_X (R := F1024) (A := F1024) (x := (a : F1024))

private noncomputable def f1024TowerFiniteChartBase :
    F1024TowerFiniteChartData 0 where
  carrier := F1024TowerFiniteBaseChart
  commRingInst := inferInstance
  domainInst := inferInstance
  dedekindInst := inferInstance
  constantAlgebraInst := inferInstance
  actualAlgebraInst := f1024TowerFiniteBaseChartActualAlgebra
  constantTowerInst := f1024TowerFiniteBaseChartConstantTower
  fractionRingInst := f1024TowerFiniteBaseChartFractionRing
  baseX := f1024TowerFiniteBaseXUnit
  baseX_map := by
    rw [f1024TowerFiniteBaseXUnit_coe]
    exact IsLocalization.lift_eq _ Polynomial.X
  xUnit := f1024TowerFiniteBaseXUnit
  xUnit_map := by
    rw [f1024TowerFiniteBaseXUnit_coe]
    exact IsLocalization.lift_eq _ Polynomial.X
  evaluate := fun coordinate => (f1024TowerFiniteBaseEvaluate coordinate.1).toRingHom
  evaluate_surjective := by
    intro coordinate c
    refine ⟨algebraMap F1024 F1024TowerFiniteBaseChart c, ?_⟩
    exact (f1024TowerFiniteBaseEvaluate coordinate.1).commutes c
  evaluate_constants := by
    intro coordinate c
    exact (f1024TowerFiniteBaseEvaluate coordinate.1).commutes c
  evaluate_baseX := by
    intro coordinate
    rw [f1024TowerFiniteBaseXUnit_coe]
    change f1024TowerFiniteBaseEvaluate coordinate.1
        (algebraMap F1024[X] F1024TowerFiniteBaseChart Polynomial.X) = _
    exact f1024TowerFiniteBaseEvaluate_X coordinate.1
  evaluate_x := by
    intro coordinate
    rw [f1024TowerFiniteBaseXUnit_coe]
    change f1024TowerFiniteBaseEvaluate coordinate.1
        (algebraMap F1024[X] F1024TowerFiniteBaseChart Polynomial.X) = _
    rw [f1024TowerFiniteBaseEvaluate_X]
    rfl
  evaluate_injective := by
    intro coordinate other hmaps
    apply Prod.ext
    · apply Units.ext
      have h := DFunLike.congr_fun hmaps
        (f1024TowerFiniteBaseXUnit : F1024TowerFiniteBaseChart)
      rw [f1024TowerFiniteBaseXUnit_coe] at h
      change f1024TowerFiniteBaseEvaluate coordinate.1
          (algebraMap F1024[X] F1024TowerFiniteBaseChart Polynomial.X) =
        f1024TowerFiniteBaseEvaluate other.1
          (algebraMap F1024[X] F1024TowerFiniteBaseChart Polynomial.X) at h
      simpa only [f1024TowerFiniteBaseEvaluate_X] using h
    · exact Subsingleton.elim _ _

/-- The actual finite split affine chart at every indexed tower level. -/
private noncomputable def f1024TowerFiniteChart :
    ∀ height : ℕ, F1024TowerFiniteChartData height
  | 0 => f1024TowerFiniteChartBase
  | height + 1 =>
      f1024TowerFiniteChartStepData (f1024TowerFiniteChart height)

private theorem f1024TowerLevelBaseX_transcendental (height : ℕ) :
    Transcendental F1024
      (algebraMap F1024TowerF1 (F1024TowerLevel height) RatFunc.X) :=
  (transcendental_algebraMap_iff
    (algebraMap F1024TowerF1 (F1024TowerLevel height)).injective).mpr
      RatFunc.transcendental_X

/-- The maximal evaluation ideal of a finite split coordinate is nonzero,
and hence is a genuine height-one prime of the constructed Dedekind chart. -/
private noncomputable def f1024TowerFiniteChartPrime
    (height : ℕ) (coordinate : F1024TowerFiniteCoordinate height) :
    IsDedekindDomain.HeightOneSpectrum
      (f1024TowerFiniteChart height).carrier := by
  let chart := f1024TowerFiniteChart height
  let evaluation := chart.evaluate coordinate
  have hmaximal : (RingHom.ker evaluation).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective evaluation
      (chart.evaluate_surjective coordinate)
  have hne : RingHom.ker evaluation ≠ ⊥ := by
    let witness : chart.carrier :=
      chart.baseX - algebraMap F1024 chart.carrier (coordinate.1 : F1024)
    have hwitnessMem : witness ∈ RingHom.ker evaluation := by
      rw [RingHom.mem_ker]
      dsimp only [evaluation, witness]
      rw [map_sub, chart.evaluate_baseX, chart.evaluate_constants, sub_self]
    have hwitnessNe : witness ≠ 0 := by
      have hactual :
          algebraMap chart.carrier (F1024TowerLevel height) witness =
            algebraMap F1024TowerF1 (F1024TowerLevel height) RatFunc.X -
              algebraMap F1024 (F1024TowerLevel height)
                (coordinate.1 : F1024) := by
        dsimp only [witness]
        rw [map_sub, chart.baseX_map,
          IsScalarTower.algebraMap_apply F1024 chart.carrier
            (F1024TowerLevel height)]
      have htarget :
          algebraMap F1024TowerF1 (F1024TowerLevel height) RatFunc.X -
              algebraMap F1024 (F1024TowerLevel height)
                (coordinate.1 : F1024) ≠ 0 := by
        intro hzero
        apply f1024TowerLevelBaseX_transcendental height
        rw [sub_eq_zero.mp hzero]
        exact isAlgebraic_algebraMap (coordinate.1 : F1024)
      intro hzero
      apply htarget
      rw [← hactual, hzero, map_zero]
    intro hbot
    exact hwitnessNe (Ideal.mem_bot.mp (hbot ▸ hwitnessMem))
  exact ⟨RingHom.ker evaluation, hmaximal.isPrime, hne⟩

/-- The normalized adic global place cut out by a finite split coordinate. -/
private noncomputable def f1024TowerFiniteGlobalPlace
    (height : ℕ) (coordinate : F1024TowerFiniteCoordinate height) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) where
  valuation := (f1024TowerFiniteChartPrime height coordinate).valuation
    (F1024TowerLevel height)
  normalized :=
    (f1024TowerFiniteChartPrime height coordinate).valuation_surjective
      (F1024TowerLevel height)

private noncomputable def f1024TowerFiniteLocalizationEquiv
    (height : ℕ) (coordinate : F1024TowerFiniteCoordinate height) :
    Localization.AtPrime
        (f1024TowerFiniteChartPrime height coordinate).asIdeal ≃+*
      (f1024TowerFiniteGlobalPlace height coordinate).valuationRing := by
  let prime := f1024TowerFiniteChartPrime height coordinate
  let e₁ : Localization.AtPrime prime.asIdeal ≃+*
      prime.valuationSubringAtPrime (F1024TowerLevel height) :=
    (Localization.algEquiv prime.asIdeal.primeCompl
      (prime.valuationSubringAtPrime (F1024TowerLevel height))).toRingEquiv
  let e₂ : prime.valuationSubringAtPrime (F1024TowerLevel height) ≃+*
      (f1024TowerFiniteGlobalPlace height coordinate).valuationRing := by
    change prime.valuationSubringAtPrime (F1024TowerLevel height) ≃+*
      (prime.valuation (F1024TowerLevel height)).valuationSubring
    rw [prime.valuationSubringAtPrime_eq_valuationSubring]
  exact e₁.trans e₂

private noncomputable def f1024TowerFiniteQuotientResidueEquiv
    (height : ℕ) (coordinate : F1024TowerFiniteCoordinate height) :
    ((f1024TowerFiniteChart height).carrier ⧸
        (f1024TowerFiniteChartPrime height coordinate).asIdeal) ≃+*
      (f1024TowerFiniteChartPrime height coordinate).asIdeal.ResidueField :=
  RingEquiv.ofBijective
    (algebraMap
      ((f1024TowerFiniteChart height).carrier ⧸
        (f1024TowerFiniteChartPrime height coordinate).asIdeal)
      (f1024TowerFiniteChartPrime height coordinate).asIdeal.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField
      (f1024TowerFiniteChartPrime height coordinate).asIdeal)

/-- An abstract field equivalence witnessing that the coordinate residue field
has the same cardinality as `F1024`.  Rationality itself is packaged below
through the actual constant-reduction map. -/
private noncomputable def f1024TowerFiniteResidueEquiv
    (height : ℕ) (coordinate : F1024TowerFiniteCoordinate height) :
    F1024 ≃+*
      (f1024TowerFiniteGlobalPlace height coordinate).residueField :=
  (RingHom.quotientKerEquivOfSurjective
      ((f1024TowerFiniteChart height).evaluate_surjective coordinate)).symm.trans
    ((f1024TowerFiniteQuotientResidueEquiv height coordinate).trans
      (IsLocalRing.ResidueField.mapEquiv
        (f1024TowerFiniteLocalizationEquiv height coordinate)))

private theorem f1024TowerFiniteConstantsToResidue_bijective
    (height : ℕ) (coordinate : F1024TowerFiniteCoordinate height) :
    Function.Bijective
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.constantsToResidue
        (f1024TowerFiniteGlobalPlace height coordinate)) := by
  let residueEquiv := f1024TowerFiniteResidueEquiv height coordinate
  letI : Fintype F1024 := Fintype.ofFinite F1024
  letI : Finite
      (f1024TowerFiniteGlobalPlace height coordinate).residueField :=
    Finite.of_equiv F1024 residueEquiv.toEquiv
  letI : Fintype
      (f1024TowerFiniteGlobalPlace height coordinate).residueField :=
    Fintype.ofFinite _
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨RingHom.injective _, Fintype.card_congr residueEquiv.toEquiv⟩

/-- The actual rational place associated to a nonzero finite split tower
coordinate.  Its rationality is proved from the evaluation quotient and the
adic localization residue field, rather than stored in the chart data. -/
noncomputable def f1024TowerFiniteRationalPlace
    (height : ℕ) (coordinate : F1024TowerFiniteCoordinate height) :
    QEC.Coding.AlgebraicGeometry.RationalPlace F1024
      (F1024TowerLevel height) where
  place := f1024TowerFiniteGlobalPlace height coordinate
  constantsEquiv := RingEquiv.ofBijective
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.constantsToResidue
      (f1024TowerFiniteGlobalPlace height coordinate))
    (f1024TowerFiniteConstantsToResidue_bijective height coordinate)
  constantsEquiv_apply := fun _ => rfl

/-- Every current tower coordinate is regular at its constructed finite
rational place because it is the image of a unit in the finite chart. -/
theorem f1024TowerFiniteRationalPlace_regular_x
    (height : ℕ) (coordinate : F1024TowerFiniteCoordinate height) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.RegularAt
      (f1024TowerFiniteRationalPlace height coordinate).place
      (f1024TowerLevelX height) := by
  change (f1024TowerFiniteChartPrime height coordinate).valuation
      (F1024TowerLevel height) (f1024TowerLevelX height) ≤ 1
  rw [← (f1024TowerFiniteChart height).xUnit_map]
  exact (f1024TowerFiniteChartPrime height coordinate).valuation_le_one
    (K := F1024TowerLevel height) ((f1024TowerFiniteChart height).xUnit :
      (f1024TowerFiniteChart height).carrier)

private theorem f1024TowerFiniteRationalPlace_evaluate_chart
    (height : ℕ) (coordinate : F1024TowerFiniteCoordinate height)
    (a : (f1024TowerFiniteChart height).carrier) :
    (f1024TowerFiniteRationalPlace height coordinate).evaluateRegular
        (algebraMap (f1024TowerFiniteChart height).carrier
          (F1024TowerLevel height) a)
        ((f1024TowerFiniteChartPrime height coordinate).valuation_le_one
          (K := F1024TowerLevel height) a) =
      (f1024TowerFiniteChart height).evaluate coordinate a := by
  let chart := f1024TowerFiniteChart height
  let prime := f1024TowerFiniteChartPrime height coordinate
  let place := f1024TowerFiniteGlobalPlace height coordinate
  let rationalPlace := f1024TowerFiniteRationalPlace height coordinate
  let value := chart.evaluate coordinate a
  let integralA : place.valuationRing :=
    ⟨algebraMap chart.carrier (F1024TowerLevel height) a,
      prime.valuation_le_one (K := F1024TowerLevel height) a⟩
  let constantValue : place.valuationRing :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.constantsToValuationRing
      place value
  have hker :
      a - algebraMap F1024 chart.carrier value ∈ prime.asIdeal := by
    change chart.evaluate coordinate
      (a - algebraMap F1024 chart.carrier value) = 0
    simp only [map_sub, chart.evaluate_constants, value, sub_self]
  have hmaximal :
      integralA - constantValue ∈
        IsLocalRing.maximalIdeal place.valuationRing := by
    rw [Valuation.mem_maximalIdeal_iff]
    change prime.valuation (F1024TowerLevel height)
      (algebraMap chart.carrier (F1024TowerLevel height) a -
        algebraMap F1024 (F1024TowerLevel height) value) < 1
    rw [IsScalarTower.algebraMap_apply F1024 chart.carrier
      (F1024TowerLevel height), ← map_sub]
    exact (prime.valuation_lt_one_iff_mem
      (K := F1024TowerLevel height) _).mpr hker
  have hresidue :
      QEC.Coding.AlgebraicGeometry.GlobalPlace.residue place integralA =
        QEC.Coding.AlgebraicGeometry.GlobalPlace.constantsToResidue
          place value := by
    change QEC.Coding.AlgebraicGeometry.GlobalPlace.residue place integralA =
      QEC.Coding.AlgebraicGeometry.GlobalPlace.residue place constantValue
    rw [← sub_eq_zero, ← map_sub]
    exact (QEC.Coding.AlgebraicGeometry.GlobalPlace.residue_eq_zero_iff
      place _).mpr hmaximal
  change rationalPlace.constantsEquiv.symm
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.residue place integralA) = value
  rw [hresidue]
  have hcompat : rationalPlace.constantsEquiv value =
      QEC.Coding.AlgebraicGeometry.GlobalPlace.constantsToResidue place value :=
    rationalPlace.constantsEquiv_apply value
  calc
    rationalPlace.constantsEquiv.symm
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.constantsToResidue place value) =
      rationalPlace.constantsEquiv.symm (rationalPlace.constantsEquiv value) := by
        rw [hcompat]
    _ = value := rationalPlace.constantsEquiv.symm_apply_apply value

/-- Genuine residue evaluation recovers the recursively constructed current
coordinate value. -/
theorem f1024TowerFiniteRationalPlace_evaluate_x
    (height : ℕ) (coordinate : F1024TowerFiniteCoordinate height) :
    (f1024TowerFiniteRationalPlace height coordinate).evaluateRegular
        (f1024TowerLevelX height)
        (f1024TowerFiniteRationalPlace_regular_x height coordinate) =
      f1024TowerFiniteCoordinateValue coordinate := by
  simpa only [(f1024TowerFiniteChart height).xUnit_map,
    (f1024TowerFiniteChart height).evaluate_x] using
    f1024TowerFiniteRationalPlace_evaluate_chart height coordinate
      ((f1024TowerFiniteChart height).xUnit :
        (f1024TowerFiniteChart height).carrier)

/-- Distinct finite split coordinates determine distinct normalized rational
places. -/
theorem f1024TowerFiniteRationalPlace_injective (height : ℕ) :
    Function.Injective (f1024TowerFiniteRationalPlace height) := by
  intro coordinate other hplaces
  let chart := f1024TowerFiniteChart height
  let coordinatePrime := f1024TowerFiniteChartPrime height coordinate
  let otherPrime := f1024TowerFiniteChartPrime height other
  have hvaluations :
      coordinatePrime.valuation (F1024TowerLevel height) =
        otherPrime.valuation (F1024TowerLevel height) :=
    congrArg
      (fun place : QEC.Coding.AlgebraicGeometry.RationalPlace F1024
          (F1024TowerLevel height) => place.place.valuation) hplaces
  have hprimes : coordinatePrime = otherPrime := by
    apply IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
      (K := F1024TowerLevel height)
    exact Valuation.IsEquiv.of_eq hvaluations
  have hkernels :
      RingHom.ker (chart.evaluate coordinate) =
        RingHom.ker (chart.evaluate other) :=
    congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hprimes
  apply chart.evaluate_injective
  ext a
  let value := chart.evaluate coordinate a
  have hmem :
      a - algebraMap F1024 chart.carrier value ∈
        RingHom.ker (chart.evaluate coordinate) := by
    change chart.evaluate coordinate
      (a - algebraMap F1024 chart.carrier value) = 0
    simp only [map_sub, chart.evaluate_constants, value, sub_self]
  rw [hkernels] at hmem
  change chart.evaluate other
      (a - algebraMap F1024 chart.carrier value) = 0 at hmem
  rw [map_sub, chart.evaluate_constants] at hmem
  exact (sub_eq_zero.mp hmem).symm

/-- The finite set of all constructed nonzero split rational places at one
tower level. -/
noncomputable def f1024TowerFiniteRationalPlaces (height : ℕ) :
    Finset (QEC.Coding.AlgebraicGeometry.RationalPlace F1024
      (F1024TowerLevel height)) := by
  classical
  exact Finset.univ.image (f1024TowerFiniteRationalPlace height)

/-- The actual finite rational-place family has the exact source-relevant
cardinality `1023 * 32^height`. -/
theorem f1024TowerFiniteRationalPlaces_card (height : ℕ) :
    (f1024TowerFiniteRationalPlaces height).card = 1023 * 32 ^ height := by
  classical
  rw [f1024TowerFiniteRationalPlaces,
    Finset.card_image_of_injective _
      (f1024TowerFiniteRationalPlace_injective height),
    Finset.card_univ, f1024TowerFiniteCoordinate_card]

private theorem isFullConstantField_of_rationalPlace
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    (Q : QEC.Coding.AlgebraicGeometry.RationalPlace k F) :
    QEC.Coding.AlgebraicGeometry.IsFullConstantField k F := by
  refine ⟨fun x hx => ?_⟩
  let E : IntermediateField k F := IntermediateField.adjoin k {x}
  letI : FiniteDimensional k E :=
    IntermediateField.adjoin.finiteDimensional hx.isIntegral
  letI : Finite E := Module.finite_of_finite k
  let integralInclusion : E →+* Q.place.valuationRing :=
    (algebraMap E F).codRestrict Q.place.valuationRing fun y =>
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_valuationRing_iff
        Q.place _).mpr
        (FiniteField.valuation_algebraMap_le_one Q.place.valuation y)
  let evaluateAdjoin : E →+* k := Q.evaluate.comp integralInclusion
  letI : Fintype k := Fintype.ofFinite k
  letI : Fintype E := Fintype.ofFinite E
  have hEk : Fintype.card E ≤ Fintype.card k :=
    Fintype.card_le_of_injective evaluateAdjoin evaluateAdjoin.injective
  have hkE : Fintype.card k ≤ Fintype.card E :=
    Fintype.card_le_of_injective (algebraMap k E) (algebraMap k E).injective
  have hcard : Fintype.card k = Fintype.card E :=
    Nat.le_antisymm hkE hEk
  have hsurjective : Function.Surjective (algebraMap k E) :=
    ((Fintype.bijective_iff_injective_and_card (algebraMap k E)).mpr
      ⟨(algebraMap k E).injective, hcard⟩).2
  have hxmem : x ∈ E :=
    IntermediateField.subset_adjoin k ({x} : Set F) (by simp)
  obtain ⟨c, hc⟩ := hsurjective ⟨x, hxmem⟩
  refine ⟨c, ?_⟩
  have hc' := congrArg (fun y : E => (y : F)) hc
  simpa [E] using hc'.symm

/-- Every concrete recursively constructed tower level has exactly `F1024`
as its full constant field.  The proof is derived from an actual finite split
rational place rather than recorded as tower data. -/
noncomputable instance f1024TowerLevel_isFullConstantField (height : ℕ) :
    QEC.Coding.AlgebraicGeometry.IsFullConstantField F1024
      (F1024TowerLevel height) :=
  isFullConstantField_of_rationalPlace
    (f1024TowerFiniteRationalPlace height (1, fun _ => 0))

/-- The concrete multiplicative group of `F1024` has the source-relevant
order `1024 - 1 = 1023`. -/
theorem f1024_units_card : Nat.card F1024ˣ = 1023 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_units, f1024_card]

/-- Seventh powers permute the actual nonzero elements of the fixed WHY24
field.  This uses the order calculation, not a chosen cyclic generator. -/
theorem f1024_seventh_power_bijective : Function.Bijective (fun x : F1024ˣ => x ^ 7) := by
  apply Nat.Coprime.pow_left_bijective
  rw [f1024_units_card]
  norm_num

/-- A deterministic seventh-root representative for the fixed field.  Since
`7 * 877 = 1 (mod 1023)`, this avoids any choice when later residue weights
are converted into coordinate scalings. -/
def f1024SeventhRoot (x : F1024) : F1024 :=
  x ^ 877

/-- The explicit representative is genuinely a seventh root for every field
element, including zero. -/
theorem f1024SeventhRoot_pow_seven (x : F1024) : (f1024SeventhRoot x) ^ 7 = x := by
  by_cases hx : x = 0
  · simp [f1024SeventhRoot, hx]
  · have hpow : x ^ 1023 = 1 := by
      simpa [f1024_card] using FiniteField.pow_card_sub_one_eq_one x hx
    rw [f1024SeventhRoot, ← pow_mul]
    calc
      x ^ (877 * 7) = x ^ (1023 * 6 + 1) := by norm_num
      _ = (x ^ 1023) ^ 6 * x := by rw [pow_add, pow_mul, pow_one]
      _ = x := by rw [hpow]; simp

/-- Every concrete `F1024` element has a seventh root. -/
theorem exists_f1024_seventh_root (x : F1024) : ∃ y : F1024, y ^ 7 = x := by
  exact ⟨f1024SeventhRoot x, f1024SeventhRoot_pow_seven x⟩

/-- A nonzero residue weight has a nonzero seventh root in the fixed field. -/
theorem exists_f1024_nonzero_seventh_root {x : F1024} (hx : x ≠ 0) :
    ∃ y : F1024, y ≠ 0 ∧ y ^ 7 = x := by
  obtain ⟨y, hy⟩ := exists_f1024_seventh_root x
  refine ⟨y, ?_, hy⟩
  intro hy0
  apply hx
  simpa [hy0] using hy.symm

/-! ## Source-coordinate pole divisors -/

section TowerCoordinateDivisors

open QEC.Coding.AlgebraicGeometry

variable (F : Type*) [Field F]
variable [π : Algebra F1024[X] F] [ρ : Algebra F1024TowerF1 F]
variable [τ : IsScalarTower F1024[X] F1024TowerF1 F]
variable [φ : _root_.FunctionField F1024 F]
variable [s : Algebra.IsSeparable F1024TowerF1 F]

noncomputable local instance f1024TowerCoordinateDivisorAlgebra :
    Algebra F1024 F :=
  @QEC.Coding.AlgebraicGeometry.AffinePlace.constantAlgebra
    F1024 F _ _ π

private theorem f1024Tower_valuation_eq_exp_neg_order
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F)
    {u : F} (hu : u ≠ 0) :
    P.valuation u = WithZero.exp (-P.order u) := by
  have h := (WithZero.exp_log ((P.valuation).ne_zero_iff.mpr hu)).symm
  simpa only [QEC.Coding.AlgebraicGeometry.GlobalPlace.order, neg_neg] using h

private theorem f1024Tower_order_pow
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F)
    (u : F) (s : ℕ) :
    P.order (u ^ s) = (s : ℤ) * P.order u := by
  unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order
  rw [map_pow, WithZero.log_pow]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

private theorem f1024Tower_order_add_eq_left_of_lt
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F)
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (horder : P.order u < P.order v) :
    P.order (u + v) = P.order u := by
  have hνu := f1024Tower_valuation_eq_exp_neg_order F P hu
  have hνv := f1024Tower_valuation_eq_exp_neg_order F P hv
  have hlt : P.valuation v < P.valuation u := by
    rw [hνv, hνu]
    exact WithZero.exp_lt_exp.mpr (by omega)
  unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order
  rw [Valuation.map_add_eq_of_lt_left P.valuation hlt]

private theorem f1024Tower_order_add_eq_right_of_lt
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F)
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (horder : P.order v < P.order u) :
    P.order (u + v) = P.order v := by
  rw [add_comm]
  exact f1024Tower_order_add_eq_left_of_lt F P hv hu horder

/-- The three possible local order branches of one literal source
recurrence.  This is kept private: only the resulting intrinsic divisor
identity is part of the family interface. -/
private theorem f1024Tower_recurrence_order_cases
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F)
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (hrec : u ^ 31 * v ^ 32 + v = u ^ 32) :
    (P.order u < 0 ∧ P.order u = 32 * P.order v) ∨
      (0 < P.order u ∧ P.order v = 32 * P.order u) ∨
      (0 ≤ P.order u ∧ P.order v = -P.order u) := by
  let a : F := u ^ 31 * v ^ 32
  have ha : a ≠ 0 := mul_ne_zero (pow_ne_zero _ hu) (pow_ne_zero _ hv)
  have horderA : P.order a = 31 * P.order u + 32 * P.order v := by
    dsimp only [a]
    rw [P.order_mul (pow_ne_zero _ hu) (pow_ne_zero _ hv),
      f1024Tower_order_pow F, f1024Tower_order_pow F]
    norm_num
  have horderC : P.order (u ^ 32) = 32 * P.order u := by
    rw [f1024Tower_order_pow F]
    norm_num
  rcases lt_trichotomy (P.order a) (P.order v) with hlt | heq | hgt
  · have hsum := f1024Tower_order_add_eq_left_of_lt F P ha hv hlt
    rw [hrec, horderC, horderA] at hsum
    rw [horderA] at hlt
    left
    omega
  · have hνa := f1024Tower_valuation_eq_exp_neg_order F P ha
    have hνv := f1024Tower_valuation_eq_exp_neg_order F P hv
    have hνeq : P.valuation a = P.valuation v := by
      rw [hνa, hνv, heq]
    have hsum_ne : a + v ≠ 0 := by
      rw [hrec]
      exact pow_ne_zero _ hu
    have hsum_le : P.valuation (a + v) ≤ P.valuation a := by
      calc
        P.valuation (a + v) ≤ max (P.valuation a) (P.valuation v) :=
          map_add_le_max P.valuation a v
        _ = P.valuation a := by rw [hνeq, max_self]
    rw [f1024Tower_valuation_eq_exp_neg_order F P hsum_ne,
      hνa, WithZero.exp_le_exp] at hsum_le
    rw [hrec, horderC] at hsum_le
    rw [horderA] at heq hsum_le
    right
    right
    omega
  · have hsum := f1024Tower_order_add_eq_right_of_lt F P ha hv hgt
    rw [hrec, horderC] at hsum
    rw [horderA] at hgt
    right
    left
    omega

/-- The effective zero divisor of a nonzero source coordinate. -/
private noncomputable def f1024TowerZeroDivisor (u : F) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F) := by
  classical
  exact if hu : u = 0 then 0
    else
      QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor
          (k := F1024) (F := F) (Units.mk0 u hu) ⊔ 0

private theorem f1024TowerZeroDivisor_apply_of_ne_zero
    {u : F} (hu : u ≠ 0)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F) :
    f1024TowerZeroDivisor F u P = max (P.order u) 0 := by
  simp only [f1024TowerZeroDivisor, dif_neg hu, Finsupp.sup_apply,
    QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor_apply,
    Units.val_mk0, Finsupp.zero_apply]

private theorem f1024TowerPolarDivisor_apply_of_ne_zero
    {u : F} (hu : u ≠ 0)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
        (k := F1024) (F := F) u P = max (-P.order u) 0 := by
  simp only [QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor,
    dif_neg hu, Finsupp.sup_apply, Finsupp.neg_apply,
    QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor_apply,
    Units.val_mk0, Finsupp.zero_apply]

private theorem f1024TowerZeroDivisor_degree_eq_polarDivisor_degree
    {u : F} (hu : u ≠ 0) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F))
        (f1024TowerZeroDivisor F u) =
      Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F))
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F) u) := by
  have hdivisor :
      QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor
          (k := F1024) (F := F) (Units.mk0 u hu) =
        f1024TowerZeroDivisor F u -
          QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
            (k := F1024) (F := F) u := by
    ext P
    rw [Finsupp.sub_apply,
      QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor_apply,
      f1024TowerZeroDivisor_apply_of_ne_zero F hu,
      f1024TowerPolarDivisor_apply_of_ne_zero F hu]
    simp only [Units.val_mk0]
    omega
  have hdegree := QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor_degree_zero
    (k := F1024) (F := F) (Units.mk0 u hu)
  rw [hdivisor, Divisor.degree_sub] at hdegree
  omega

private noncomputable def f1024TowerSwitchZeroDivisor
    (u v : F) : Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F) := by
  classical
  exact (f1024TowerZeroDivisor F u).filter (fun P => P.order v < 0)

private noncomputable def f1024TowerContinuingZeroDivisor
    (u v : F) : Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F) := by
  classical
  exact (f1024TowerZeroDivisor F u).filter (fun P => 0 ≤ P.order v)

private theorem f1024TowerZeroDivisor_eq_switch_add_continuing
    (u v : F) :
    f1024TowerZeroDivisor F u =
      f1024TowerSwitchZeroDivisor F u v +
        f1024TowerContinuingZeroDivisor F u v := by
  classical
  ext P
  simp only [f1024TowerSwitchZeroDivisor,
    f1024TowerContinuingZeroDivisor, Finsupp.add_apply,
    Finsupp.filter_apply]
  by_cases h : P.order v < 0
  · simp [h, Int.not_le.mpr h]
  · simp [h, le_of_not_gt h]

private theorem f1024TowerPolarDivisor_recurrence_identity
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (hrec : u ^ 31 * v ^ 32 + v = u ^ 32) :
    32 • QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F) v =
      QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F) u +
        32 • f1024TowerSwitchZeroDivisor F u v := by
  classical
  ext P
  obtain hPole | hZero | hCancel :=
    f1024Tower_recurrence_order_cases F P hu hv hrec
  all_goals
    simp only [Finsupp.nsmul_apply, Finsupp.add_apply,
      f1024TowerPolarDivisor_apply_of_ne_zero F hu,
      f1024TowerPolarDivisor_apply_of_ne_zero F hv,
      f1024TowerSwitchZeroDivisor, Finsupp.filter_apply,
      f1024TowerZeroDivisor_apply_of_ne_zero F hu, nsmul_eq_mul]
  · rcases hPole with ⟨hr, hrs⟩
    simp only [if_pos (by omega : P.order v < 0)]
    omega
  · rcases hZero with ⟨hr, hsr⟩
    simp only [if_neg (by omega : ¬P.order v < 0)]
    omega
  · rcases hCancel with ⟨hr, hsr⟩
    by_cases hrzero : P.order u = 0
    · simp [hrzero, hsr]
    · have hsneg : P.order v < 0 := by omega
      simp only [if_pos hsneg]
      omega

private theorem f1024TowerZeroDivisor_recurrence_identity
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (hrec : u ^ 31 * v ^ 32 + v = u ^ 32) :
    f1024TowerZeroDivisor F v =
      32 • f1024TowerContinuingZeroDivisor F u v := by
  classical
  ext P
  obtain hPole | hZero | hCancel :=
    f1024Tower_recurrence_order_cases F P hu hv hrec
  all_goals
    simp only [Finsupp.nsmul_apply,
      f1024TowerZeroDivisor_apply_of_ne_zero F hu,
      f1024TowerZeroDivisor_apply_of_ne_zero F hv,
      f1024TowerContinuingZeroDivisor, Finsupp.filter_apply,
      nsmul_eq_mul]
  · rcases hPole with ⟨hr, hrs⟩
    simp only [if_neg (by omega : ¬0 ≤ P.order v)]
    omega
  · rcases hZero with ⟨hr, hsr⟩
    simp only [if_pos (by omega : 0 ≤ P.order v)]
    omega
  · rcases hCancel with ⟨hr, hsr⟩
    by_cases hrzero : P.order u = 0
    · simp [hrzero, hsr]
    · have hsneg : P.order v < 0 := by omega
      simp only [if_neg (Int.not_le.mpr hsneg)]
      omega

private theorem f1024TowerDivisor_degree_nsmul
    (n : ℕ) (D : Divisor
      (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F)) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F)) (n • D) =
      (n : ℤ) * Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F)) D := by
  simpa only [Divisor.degree, nsmul_eq_mul] using
    (Divisor.degreeHom
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
        (k := F1024) (F := F))).map_nsmul n D

private theorem f1024Tower_polarDivisor_degree_eq_of_recurrence
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (hrec : u ^ 31 * v ^ 32 + v = u ^ 32) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F))
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F) u) =
      Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F))
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F) v) := by
  let degree := Divisor.degree
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
      (k := F1024) (F := F))
  let polarU := QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
    (k := F1024) (F := F) u
  let polarV := QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
    (k := F1024) (F := F) v
  let zeroU := f1024TowerZeroDivisor F u
  let zeroV := f1024TowerZeroDivisor F v
  let switch := f1024TowerSwitchZeroDivisor F u v
  let continuing := f1024TowerContinuingZeroDivisor F u v
  have hzeroU : degree zeroU = degree polarU :=
    f1024TowerZeroDivisor_degree_eq_polarDivisor_degree F hu
  have hzeroV : degree zeroV = degree polarV :=
    f1024TowerZeroDivisor_degree_eq_polarDivisor_degree F hv
  have hsplitDivisor : zeroU = switch + continuing :=
    f1024TowerZeroDivisor_eq_switch_add_continuing F u v
  have hpolarDivisor : 32 • polarV = polarU + 32 • switch :=
    f1024TowerPolarDivisor_recurrence_identity F hu hv hrec
  have hzeroDivisor : zeroV = 32 • continuing :=
    f1024TowerZeroDivisor_recurrence_identity F hu hv hrec
  have hsplit := congrArg degree hsplitDivisor
  have hpolar := congrArg degree hpolarDivisor
  have hzero := congrArg degree hzeroDivisor
  dsimp only [degree, polarU, polarV, zeroU, zeroV, switch, continuing]
    at hzeroU hzeroV hsplit hpolar hzero ⊢
  rw [Divisor.degree_add] at hsplit
  rw [f1024TowerDivisor_degree_nsmul F, Divisor.degree_add,
    f1024TowerDivisor_degree_nsmul F] at hpolar
  rw [f1024TowerDivisor_degree_nsmul F] at hzero
  omega

end TowerCoordinateDivisors

private noncomputable def f1024TowerStageHistoricalX
    {height : ℕ} (stage : F1024TowerStageData height) (i : ℕ) :
    stage.carrier :=
  (stage.inverseCoordinate i)⁻¹

private theorem f1024TowerStageHistoricalX_ne_zero
    {height : ℕ} (stage : F1024TowerStageData height) (i : ℕ) :
    f1024TowerStageHistoricalX stage i ≠ 0 :=
  inv_ne_zero (stage.inverseCoordinate_ne_zero i)

private theorem f1024TowerStageHistoricalX_zero
    {height : ℕ} (stage : F1024TowerStageData height) :
    f1024TowerStageHistoricalX stage 0 =
      algebraMap F1024TowerF1 stage.carrier RatFunc.X := by
  rw [f1024TowerStageHistoricalX, stage.inverseCoordinate_zero, inv_inv]

private theorem f1024TowerStageHistoricalX_current
    {height : ℕ} (stage : F1024TowerStageData height) :
    f1024TowerStageHistoricalX stage height = stage.x := by
  rw [f1024TowerStageHistoricalX, stage.inverseCoordinate_current, inv_inv]

private theorem f1024TowerStageHistoricalX_recurrence
    {height : ℕ} (stage : F1024TowerStageData height)
    (i : ℕ) (hi : i < height) :
    f1024TowerStageHistoricalX stage i ^ 31 *
          f1024TowerStageHistoricalX stage (i + 1) ^ 32 +
        f1024TowerStageHistoricalX stage (i + 1) =
      f1024TowerStageHistoricalX stage i ^ 32 := by
  let a := stage.inverseCoordinate i
  let b := stage.inverseCoordinate (i + 1)
  have ha : a ≠ 0 := stage.inverseCoordinate_ne_zero i
  have hb : b ≠ 0 := stage.inverseCoordinate_ne_zero (i + 1)
  have hrec : b ^ 32 + a ^ 32 * b ^ 31 = a := by
    simpa only [a, b] using stage.inverseCoordinate_recurrence i hi
  have hadd_self (x : stage.carrier) : x + x = 0 := by
    exact CharTwo.add_self_eq_zero x
  change a⁻¹ ^ 31 * b⁻¹ ^ 32 + b⁻¹ = a⁻¹ ^ 32
  field_simp [ha, hb]
  calc
    a * (1 + a ^ 31 * b ^ 31) = a + a ^ 32 * b ^ 31 := by ring
    _ =
        (b ^ 32 + a ^ 32 * b ^ 31) + a ^ 32 * b ^ 31 := by rw [hrec]
    _ = b ^ 32 + (a ^ 32 * b ^ 31 + a ^ 32 * b ^ 31) := by ring
    _ = b ^ 32 := by rw [hadd_self, add_zero]

/-! ## Normalized restriction across a finite tower step -/

private theorem f1024Tower_comapValuation_isNontrivial
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : Valuation L ℤᵐ⁰) (hv : Function.Surjective v) :
    (v.comap (algebraMap K L)).IsNontrivial := by
  let w : Valuation K ℤᵐ⁰ := v.comap (algebraMap K L)
  by_contra htrivial
  have hwTop : w.valuationSubring.toSubring = ⊤ := by
    apply top_unique
    intro x hx
    change w x ≤ 1
    by_contra hxle
    have hxgt : 1 < w x := lt_of_not_ge hxle
    exact htrivial
      (Valuation.IsNontrivial_iff_exists_one_lt.mpr ⟨x, hxgt⟩)
  have hbase : ∀ x : K, algebraMap K L x ∈ v.integer := by
    intro x
    have hx : x ∈ w.valuationSubring := by
      change x ∈ w.valuationSubring.toSubring
      rw [hwTop]
      trivial
    have hport := hx
    simp only [Valuation.mem_integer_iff, w, Valuation.comap_apply] at hport ⊢
    exact hport
  letI : IsIntegrallyClosedIn v.integer L :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn L).mp inferInstance
  have hclosure : (integralClosure K L).toSubring ≤
      v.integer :=
    (Subring.integralClosure_le_iff).mpr hbase
  have hIntegral : Algebra.IsIntegral K L := by infer_instance
  have hclosureTop : integralClosure K L = ⊤ :=
    integralClosure_eq_top_iff.mpr hIntegral
  have hvaluationTop : v.integer = ⊤ := by
    apply top_unique
    intro x hx
    apply hclosure
    change x ∈ (integralClosure K L).toSubring
    rw [hclosureTop]
    trivial
  obtain ⟨uniformizer, huniformizer⟩ :=
    hv (WithZero.exp (-1 : ℤ))
  have huniformizer_ne : uniformizer ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at huniformizer
    exact WithZero.exp_ne_zero huniformizer.symm
  have hinverse : uniformizer⁻¹ ∈ v.integer := by
    rw [hvaluationTop]
    trivial
  rw [Valuation.mem_integer_iff, map_inv₀, huniformizer,
    ← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at hinverse
  omega

private noncomputable def f1024Tower_normalizedRestrictedValuation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : Valuation L ℤᵐ⁰) (hv : Function.Surjective v) :
    Valuation K ℤᵐ⁰ := by
  let w : Valuation K ℤᵐ⁰ := v.comap (algebraMap K L)
  letI : w.IsNontrivial :=
    f1024Tower_comapValuation_isNontrivial (K := K) (L := L) v hv
  letI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass w)) := inferInstance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass w)) := inferInstance
  letI : w.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' w
  exact Valuation.map
    (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt w).toMonoidWithZeroHom
    (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_strictMono w).monotone
    w.restrict

private theorem f1024Tower_normalizedRestrictedValuation_surjective
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : Valuation L ℤᵐ⁰) (hv : Function.Surjective v) :
    Function.Surjective
      (f1024Tower_normalizedRestrictedValuation (K := K) (L := L) v hv) := by
  let w : Valuation K ℤᵐ⁰ := v.comap (algebraMap K L)
  letI : w.IsNontrivial :=
    f1024Tower_comapValuation_isNontrivial (K := K) (L := L) v hv
  letI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass w)) := inferInstance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass w)) := inferInstance
  letI : w.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' w
  let e := Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt w
  intro gamma
  obtain ⟨delta, hdelta⟩ := e.surjective gamma
  obtain ⟨x, hx⟩ :=
    MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective (.ofClass w) delta
  refine ⟨x, ?_⟩
  change e (w.restrict x) = gamma
  rw [Valuation.restrict_def, hx]
  exact hdelta

private theorem f1024Tower_normalizedRestrictedValuation_isEquiv_comap
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : Valuation L ℤᵐ⁰) (hv : Function.Surjective v) :
    (f1024Tower_normalizedRestrictedValuation
        (K := K) (L := L) v hv).IsEquiv
      (v.comap (algebraMap K L)) := by
  let w : Valuation K ℤᵐ⁰ := v.comap (algebraMap K L)
  letI : w.IsNontrivial :=
    f1024Tower_comapValuation_isNontrivial (K := K) (L := L) v hv
  letI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass w)) := inferInstance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass w)) := inferInstance
  letI : w.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' w
  exact
    (Valuation.isEquiv_map_self_of_strictMono
      (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt w).toMonoidWithZeroHom
      (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_strictMono w)).trans
        w.isEquiv_restrict.symm

private noncomputable def f1024Tower_restrictedGlobalPlace
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace k L) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace k K where
  valuation := f1024Tower_normalizedRestrictedValuation
    (K := K) (L := L) Q.valuation Q.normalized
  normalized :=
    f1024Tower_normalizedRestrictedValuation_surjective
      (K := K) (L := L) Q.valuation Q.normalized

private theorem f1024Tower_restrictedGlobalPlace_order_scale
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace k L) :
    ∃ e : ℕ, 0 < e ∧ ∀ x : K, x ≠ 0 →
      Q.order (algebraMap K L x) =
        (e : ℤ) *
          (f1024Tower_restrictedGlobalPlace
            (k := k) (K := K) (L := L) Q).order x := by
  let w : Valuation K ℤᵐ⁰ := Q.valuation.comap (algebraMap K L)
  letI : w.IsNontrivial :=
    f1024Tower_comapValuation_isNontrivial
      (K := K) (L := L) Q.valuation Q.normalized
  letI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass w)) := inferInstance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass w)) := inferInstance
  letI : w.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' w
  let phi := Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt w
  let generatorValue : ℤᵐ⁰ :=
    (Valuation.IsRankOneDiscrete.generator w : ℤᵐ⁰)
  let eInt : ℤ := -WithZero.log generatorValue
  have hgenerator_ne : generatorValue ≠ 0 := by
    exact Valuation.IsRankOneDiscrete.generator_ne_zero (v := w)
  have hgenerator_lt : generatorValue < 1 := by
    have hport := Valuation.IsRankOneDiscrete.generator_lt_one w
    simp only [generatorValue] at hport ⊢
    exact hport
  have hlog_neg : WithZero.log generatorValue < 0 := by
    rw [← WithZero.exp_lt_exp, WithZero.exp_log hgenerator_ne,
      WithZero.exp_zero]
    exact hgenerator_lt
  have heInt_pos : 0 < eInt := by
    dsimp only [eInt]
    omega
  let e : ℕ := eInt.toNat
  have heCast : (e : ℤ) = eInt := by
    exact Int.toNat_of_nonneg heInt_pos.le
  refine ⟨e, ?_, ?_⟩
  · omega
  · intro x hx
    let lower := f1024Tower_normalizedRestrictedValuation
      (K := K) (L := L) Q.valuation Q.normalized
    have hlower_ne : lower x ≠ 0 :=
      (Valuation.ne_zero_iff lower).mpr hx
    let n : ℤ := -WithZero.log (lower x)
    have hphi : phi (w.restrict x) = lower x := by
      rfl
    have hphiPow : phi
        ((Valuation.IsRankOneDiscrete.generator' w :
          MonoidWithZeroHom.ValueGroup₀ (.ofClass w)) ^ n) = lower x := by
      rw [Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_apply_zpow]
      dsimp only [n]
      rw [neg_neg, WithZero.exp_log hlower_ne]
    have hrestrict : w.restrict x =
        (Valuation.IsRankOneDiscrete.generator' w :
          MonoidWithZeroHom.ValueGroup₀ (.ofClass w)) ^ n :=
      phi.injective (hphi.trans hphiPow.symm)
    have hwValue : w x = generatorValue ^ n := by
      calc
        w x = MonoidWithZeroHom.ValueGroup₀.embedding (w.restrict x) :=
          (Valuation.embedding_restrict w x).symm
        _ = MonoidWithZeroHom.ValueGroup₀.embedding
            ((Valuation.IsRankOneDiscrete.generator' w :
              MonoidWithZeroHom.ValueGroup₀ (.ofClass w)) ^ n) := by
          rw [hrestrict]
        _ = generatorValue ^ n := by
          rw [map_zpow₀, Valuation.IsRankOneDiscrete.embedding_generator']
    change -WithZero.log (w x) = (e : ℤ) * (-WithZero.log (lower x))
    rw [hwValue, WithZero.log_zpow, heCast]
    dsimp only [eInt, n]
    ring

private theorem f1024Tower_globalPlace_order_pow
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k F)
    (u : F) (n : ℕ) :
    P.order (u ^ n) = (n : ℤ) * P.order u := by
  unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order
  rw [map_pow, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

private theorem f1024Tower_globalPlace_order_add_eq_left_of_lt
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k F)
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (horder : P.order u < P.order v) :
    P.order (u + v) = P.order u := by
  have hνu : P.valuation u = WithZero.exp (-P.order u) := by
    have h := (WithZero.exp_log ((P.valuation).ne_zero_iff.mpr hu)).symm
    simpa only [QEC.Coding.AlgebraicGeometry.GlobalPlace.order, neg_neg] using h
  have hνv : P.valuation v = WithZero.exp (-P.order v) := by
    have h := (WithZero.exp_log ((P.valuation).ne_zero_iff.mpr hv)).symm
    simpa only [QEC.Coding.AlgebraicGeometry.GlobalPlace.order, neg_neg] using h
  have hlt : P.valuation v < P.valuation u := by
    rw [hνv, hνu]
    exact WithZero.exp_lt_exp.mpr (by omega)
  unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order
  rw [Valuation.map_add_eq_of_lt_left P.valuation hlt]

/-- A root of a degree-32 Artin--Schreier equation with regular right-hand
side is regular at every upper place.  This is the valuation-theoretic first
half of the source's translated unramified-place argument. -/
private theorem f1024Tower_artinSchreierRoot_regular
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace k L)
    (a : K) (y : L)
    (ha : 0 ≤
      (f1024Tower_restrictedGlobalPlace
        (k := k) (K := K) (L := L) Q).order a)
    (hy : y ^ 32 + y = algebraMap K L a) :
    Q.RegularAt y := by
  by_cases hyzero : y = 0
  · subst y
    simp [QEC.Coding.AlgebraicGeometry.GlobalPlace.RegularAt]
  rw [Q.regularAt_iff_order_nonnegative hyzero]
  by_contra hregular
  have hyneg : Q.order y < 0 := lt_of_not_ge hregular
  have hypow_ne : y ^ 32 ≠ 0 := pow_ne_zero 32 hyzero
  have hypowOrder : Q.order (y ^ 32) = 32 * Q.order y := by
    rw [f1024Tower_globalPlace_order_pow Q]
    norm_num
  have hlt : Q.order (y ^ 32) < Q.order y := by
    rw [hypowOrder]
    omega
  have hsum := f1024Tower_globalPlace_order_add_eq_left_of_lt
    Q hypow_ne hyzero hlt
  rw [hy, hypowOrder] at hsum
  have hnegative : 32 * Q.order y < 0 := by omega
  by_cases hazero : a = 0
  · subst a
    have hmapNegative : Q.order (algebraMap K L (0 : K)) < 0 :=
      hsum.trans_lt hnegative
    have hmapZero : Q.order (algebraMap K L (0 : K)) = 0 := by
      simp [QEC.Coding.AlgebraicGeometry.GlobalPlace.order]
    rw [hmapZero] at hmapNegative
    omega
  · obtain ⟨e, he, hscale⟩ :=
      f1024Tower_restrictedGlobalPlace_order_scale
        (k := k) (K := K) (L := L) Q
    rw [hscale a hazero] at hsum
    have hmapNonnegative :
        0 ≤ (e : ℤ) *
          (f1024Tower_restrictedGlobalPlace
            (k := k) (K := K) (L := L) Q).order a :=
      mul_nonneg (Int.ofNat_zero_le e) ha
    have hmapNegative :
        (e : ℤ) *
          (f1024Tower_restrictedGlobalPlace
            (k := k) (K := K) (L := L) Q).order a < 0 :=
      hsum.trans_lt hnegative
    omega

private noncomputable def f1024TowerRegularArtinSchreierPolynomial
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) : P.valuationRing[X] :=
  X ^ 32 + X - C a

private theorem f1024TowerRegularArtinSchreierPolynomial_monic
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) :
    (f1024TowerRegularArtinSchreierPolynomial P a).Monic := by
  rw [f1024TowerRegularArtinSchreierPolynomial,
    show (X ^ 32 + X - C a : P.valuationRing[X]) =
      X ^ 32 + (X - C a) by ring]
  exact monic_X_pow_add
    (show degree (X - C a : P.valuationRing[X]) < (32 : ℕ) by
      calc
        degree (X - C a : P.valuationRing[X]) ≤ 1 := degree_X_sub_C_le a
        _ < (32 : ℕ) := by norm_num)

private theorem f1024TowerRegularArtinSchreierPolynomial_natDegree
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) :
    (f1024TowerRegularArtinSchreierPolynomial P a).natDegree = 32 := by
  change (X ^ 32 + X - C a : P.valuationRing[X]).natDegree = 32
  calc
    (X ^ 32 + X - C a : P.valuationRing[X]).natDegree =
        (X ^ 32 + X : P.valuationRing[X]).natDegree := natDegree_sub_C
    _ = (X ^ 32 : P.valuationRing[X]).natDegree :=
      natDegree_add_eq_left_of_natDegree_lt (by norm_num)
    _ = 32 := natDegree_X_pow 32

private theorem f1024TowerRegularArtinSchreierPolynomial_map
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) :
    (f1024TowerRegularArtinSchreierPolynomial P a).map
        (algebraMap P.valuationRing K) =
      (X ^ 32 + X - C (a : K) : K[X]) := by
  simp only [f1024TowerRegularArtinSchreierPolynomial,
    Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C]
  rfl

private noncomputable def f1024TowerRegularArtinSchreierGenericPolynomial
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) : K[X] :=
  X ^ 32 + X - C (a : K)

private theorem f1024TowerRegularArtinSchreierPolynomial_map_generic
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) :
    (f1024TowerRegularArtinSchreierPolynomial P a).map
        (algebraMap P.valuationRing K) =
      f1024TowerRegularArtinSchreierGenericPolynomial P a := by
  rw [f1024TowerRegularArtinSchreierPolynomial_map]
  rfl

private theorem f1024TowerRegularArtinSchreierPolynomial_irreducible
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    Irreducible (f1024TowerRegularArtinSchreierPolynomial P a) := by
  let g : K[X] := X ^ 32 + X - C (a : K)
  have hgMonic : g.Monic := by
    simpa only [g, QEC.Coding.AlgebraicGeometry.ArtinSchreier.artinSchreierPolynomial]
      using
        (QEC.Coding.AlgebraicGeometry.ArtinSchreier.artinSchreierPolynomial_monic
          (a : K))
  have hgDegree : g.natDegree = 32 := by
    change (X ^ 32 + X - C (a : K) : K[X]).natDegree = 32
    calc
      (X ^ 32 + X - C (a : K) : K[X]).natDegree =
          (X ^ 32 + X : K[X]).natDegree := natDegree_sub_C
      _ = (X ^ 32 : K[X]).natDegree :=
        natDegree_add_eq_left_of_natDegree_lt (by norm_num)
      _ = 32 := natDegree_X_pow 32
  have hgRoot : Polynomial.aeval y g = 0 := by
    dsimp only [g]
    simp only [map_sub, map_add, map_pow, aeval_X, aeval_C]
    exact sub_eq_zero.mpr hy
  have hminDegree : (minpoly K y).natDegree = 32 := by
    rw [(Field.primitive_element_iff_minpoly_natDegree_eq K y).mp hgenerate,
      hfinrank]
  have hminDvd : minpoly K y ∣ g := minpoly.dvd K y hgRoot
  have hgEq : g = minpoly K y := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic (Algebra.IsIntegral.isIntegral y)) hgMonic hminDvd
    rw [hgDegree, hminDegree]
  refine (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (K := K) (f1024TowerRegularArtinSchreierPolynomial_monic P a)).mpr ?_
  rw [f1024TowerRegularArtinSchreierPolynomial_map]
  change Irreducible g
  rw [hgEq]
  exact minpoly.irreducible (Algebra.IsIntegral.isIntegral y)

private theorem f1024TowerRegularArtinSchreierGenericPolynomial_irreducible
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    Irreducible (f1024TowerRegularArtinSchreierGenericPolynomial P a) := by
  have hbase := f1024TowerRegularArtinSchreierPolynomial_irreducible
    P a y hy hgenerate hfinrank
  have hgeneric :=
    (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
      (K := K) (f1024TowerRegularArtinSchreierPolynomial_monic P a)).mp hbase
  rw [f1024TowerRegularArtinSchreierPolynomial_map_generic] at hgeneric
  exact hgeneric

private noncomputable abbrev F1024TowerRegularArtinSchreierModel
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) : Type _ :=
  AdjoinRoot (f1024TowerRegularArtinSchreierPolynomial P a)

private noncomputable def f1024TowerRegularArtinSchreierGenericMap
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) :
    F1024TowerRegularArtinSchreierModel P a →+*
      AdjoinRoot (f1024TowerRegularArtinSchreierGenericPolynomial P a) :=
  AdjoinRoot.map (algebraMap P.valuationRing K)
    (f1024TowerRegularArtinSchreierPolynomial P a)
    (f1024TowerRegularArtinSchreierGenericPolynomial P a) (by
      rw [f1024TowerRegularArtinSchreierPolynomial_map_generic])

private theorem f1024TowerRegularArtinSchreierGenericMap_injective
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) :
    Function.Injective (f1024TowerRegularArtinSchreierGenericMap P a) := by
  intro x y hxy
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
  apply AdjoinRoot.mk_eq_mk.mpr
  apply (Polynomial.map_dvd_map
    (algebraMap P.valuationRing K)
    (IsFractionRing.injective P.valuationRing K)
    (f1024TowerRegularArtinSchreierPolynomial_monic P a)).mp
  rw [Polynomial.map_sub,
    f1024TowerRegularArtinSchreierPolynomial_map_generic]
  apply AdjoinRoot.mk_eq_mk.mp
  have hxy' := hxy
  simp only [f1024TowerRegularArtinSchreierGenericMap, AdjoinRoot.map,
    AdjoinRoot.lift_mk, ← Polynomial.eval₂_map] at hxy'
  change aeval
      (AdjoinRoot.root
        (f1024TowerRegularArtinSchreierGenericPolynomial P a))
        (p.map (algebraMap P.valuationRing K)) =
    aeval
      (AdjoinRoot.root
        (f1024TowerRegularArtinSchreierGenericPolynomial P a))
        (q.map (algebraMap P.valuationRing K)) at hxy'
  simpa only [AdjoinRoot.aeval_eq] using hxy'

private noncomputable def f1024TowerRegularArtinSchreierDirectAlgEquiv
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    AdjoinRoot (f1024TowerRegularArtinSchreierGenericPolynomial P a) ≃ₐ[K] L := by
  let g : K[X] := f1024TowerRegularArtinSchreierGenericPolynomial P a
  have hgRoot : g.eval₂ (algebraMap K L) y = 0 := by
    dsimp only [g, f1024TowerRegularArtinSchreierGenericPolynomial]
    simp only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C]
    exact sub_eq_zero.mpr hy
  let phi : AdjoinRoot g →ₐ[K] L :=
    AdjoinRoot.liftAlgHom g (Algebra.ofId K L) y hgRoot
  letI : Fact (Irreducible g) :=
    ⟨by
      simpa only [g] using
        f1024TowerRegularArtinSchreierGenericPolynomial_irreducible
          P a y hy hgenerate hfinrank⟩
  have hphiRoot : phi (AdjoinRoot.root g) = y := by
    exact AdjoinRoot.liftAlgHom_root g (Algebra.ofId K L) y hgRoot
  have hphiCoeff : phi.toRingHom.comp (algebraMap K (AdjoinRoot g)) =
      algebraMap K L := by
    ext c
    exact phi.commutes c
  have hphiAeval (r : K[X]) :
      phi (Polynomial.aeval (AdjoinRoot.root g) r) =
        Polynomial.aeval y r := by
    change phi
        (r.eval₂ (algebraMap K (AdjoinRoot g)) (AdjoinRoot.root g)) =
      r.eval₂ (algebraMap K L) y
    calc
      phi (r.eval₂ (algebraMap K (AdjoinRoot g)) (AdjoinRoot.root g)) =
          r.eval₂ (phi.toRingHom.comp (algebraMap K (AdjoinRoot g)))
            (phi (AdjoinRoot.root g)) :=
        Polynomial.hom_eval₂ (p := r) (algebraMap K (AdjoinRoot g))
          phi.toRingHom _
      _ = r.eval₂ (algebraMap K L) y := by rw [hphiCoeff, hphiRoot]
  have hphiSurjective : Function.Surjective phi := by
    intro z
    have hzmem : z ∈ IntermediateField.adjoin K {y} := by
      rw [hgenerate]
      trivial
    obtain ⟨p, q, hz⟩ :=
      (IntermediateField.mem_adjoin_simple_iff K z).mp hzmem
    refine ⟨Polynomial.aeval (AdjoinRoot.root g) p /
      Polynomial.aeval (AdjoinRoot.root g) q, ?_⟩
    calc
      phi (Polynomial.aeval (AdjoinRoot.root g) p /
          Polynomial.aeval (AdjoinRoot.root g) q) =
          Polynomial.aeval y p / Polynomial.aeval y q := by
            rw [map_div₀, hphiAeval, hphiAeval]
      _ = z := hz.symm
  exact AlgEquiv.ofBijective phi ⟨phi.injective, hphiSurjective⟩

private theorem f1024TowerRegularArtinSchreierDirectAlgEquiv_root
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    f1024TowerRegularArtinSchreierDirectAlgEquiv
        P a y hy hgenerate hfinrank
        (AdjoinRoot.root
          (f1024TowerRegularArtinSchreierGenericPolynomial P a)) = y := by
  dsimp only [f1024TowerRegularArtinSchreierDirectAlgEquiv, AlgEquiv.ofBijective_apply]
  erw [AlgEquiv.ofBijective_apply, AdjoinRoot.liftAlgHom_root]

private noncomputable def f1024TowerRegularArtinSchreierModelToActual
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    F1024TowerRegularArtinSchreierModel P a →+* L :=
  (f1024TowerRegularArtinSchreierDirectAlgEquiv
      P a y hy hgenerate hfinrank).toRingEquiv.toRingHom.comp
    (f1024TowerRegularArtinSchreierGenericMap P a)

private theorem f1024TowerRegularArtinSchreierModelToActual_injective
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    Function.Injective
      (f1024TowerRegularArtinSchreierModelToActual
        P a y hy hgenerate hfinrank) :=
  (f1024TowerRegularArtinSchreierDirectAlgEquiv
      P a y hy hgenerate hfinrank).injective.comp
    (f1024TowerRegularArtinSchreierGenericMap_injective P a)

private theorem f1024TowerRegularArtinSchreierModelToActual_of
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32)
    (c : P.valuationRing) :
    f1024TowerRegularArtinSchreierModelToActual
        P a y hy hgenerate hfinrank
        (algebraMap P.valuationRing
          (F1024TowerRegularArtinSchreierModel P a) c) =
      algebraMap K L (c : K) := by
  change f1024TowerRegularArtinSchreierDirectAlgEquiv
      P a y hy hgenerate hfinrank
      (f1024TowerRegularArtinSchreierGenericMap P a
        (algebraMap P.valuationRing
          (F1024TowerRegularArtinSchreierModel P a) c)) = _
  rw [AdjoinRoot.algebraMap_eq,
    f1024TowerRegularArtinSchreierGenericMap, AdjoinRoot.map_of]
  exact (f1024TowerRegularArtinSchreierDirectAlgEquiv
    P a y hy hgenerate hfinrank).commutes (c : K)

private theorem f1024TowerRegularArtinSchreierModelToActual_root
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    f1024TowerRegularArtinSchreierModelToActual
        P a y hy hgenerate hfinrank
        (AdjoinRoot.root
          (f1024TowerRegularArtinSchreierPolynomial P a)) = y := by
  change f1024TowerRegularArtinSchreierDirectAlgEquiv
      P a y hy hgenerate hfinrank
      (f1024TowerRegularArtinSchreierGenericMap P a
        (AdjoinRoot.root
          (f1024TowerRegularArtinSchreierPolynomial P a))) = y
  rw [f1024TowerRegularArtinSchreierGenericMap, AdjoinRoot.map_root]
  exact f1024TowerRegularArtinSchreierDirectAlgEquiv_root
    P a y hy hgenerate hfinrank

@[reducible] private noncomputable def
    f1024TowerRegularArtinSchreierModelActualAlgebra
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    Algebra (F1024TowerRegularArtinSchreierModel P a) L :=
  (f1024TowerRegularArtinSchreierModelToActual
    P a y hy hgenerate hfinrank).toAlgebra

private theorem f1024TowerRegularArtinSchreierModelActualTower
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    @IsScalarTower P.valuationRing
      (F1024TowerRegularArtinSchreierModel P a) L
      (inferInstance : SMul P.valuationRing
        (F1024TowerRegularArtinSchreierModel P a))
      (f1024TowerRegularArtinSchreierModelActualAlgebra
        P a y hy hgenerate hfinrank).toSMul
      (inferInstance : SMul P.valuationRing L) := by
  letI : Algebra (F1024TowerRegularArtinSchreierModel P a) L :=
    f1024TowerRegularArtinSchreierModelActualAlgebra
      P a y hy hgenerate hfinrank
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change algebraMap K L (c : K) =
    f1024TowerRegularArtinSchreierModelToActual
      P a y hy hgenerate hfinrank
        (algebraMap P.valuationRing
          (F1024TowerRegularArtinSchreierModel P a) c)
  exact (f1024TowerRegularArtinSchreierModelToActual_of
    P a y hy hgenerate hfinrank c).symm

private theorem f1024TowerRegularArtinSchreierModelFractionRing
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    @IsFractionRing (F1024TowerRegularArtinSchreierModel P a)
      inferInstance L inferInstance
      (f1024TowerRegularArtinSchreierModelActualAlgebra
        P a y hy hgenerate hfinrank) := by
  let model : Type _ := F1024TowerRegularArtinSchreierModel P a
  letI : Fact (Irreducible (f1024TowerRegularArtinSchreierPolynomial P a)) :=
    ⟨f1024TowerRegularArtinSchreierPolynomial_irreducible
      P a y hy hgenerate hfinrank⟩
  letI : IsDomain model := Function.Injective.isDomain
    (f1024TowerRegularArtinSchreierModelToActual
      P a y hy hgenerate hfinrank)
    (f1024TowerRegularArtinSchreierModelToActual_injective
      P a y hy hgenerate hfinrank)
  letI : Algebra model L :=
    f1024TowerRegularArtinSchreierModelActualAlgebra
      P a y hy hgenerate hfinrank
  letI : IsScalarTower P.valuationRing model L :=
    f1024TowerRegularArtinSchreierModelActualTower
      P a y hy hgenerate hfinrank
  let frac : Type _ := FractionRing model
  let phi : frac →ₐ[model] L :=
    IsFractionRing.liftAlgHom
      (g := Algebra.ofId model L)
      (f1024TowerRegularArtinSchreierModelToActual_injective
        P a y hy hgenerate hfinrank)
  have hphiSurjective : Function.Surjective phi := by
    let baseMap : P.valuationRing →+* frac :=
      (algebraMap model frac).comp
        (algebraMap P.valuationRing model)
    have hbaseToModel : Function.Injective
        (algebraMap P.valuationRing model) := by
      change Function.Injective
        (AdjoinRoot.of (f1024TowerRegularArtinSchreierPolynomial P a))
      apply AdjoinRoot.of.injective_of_degree_ne_zero
      rw [Polynomial.degree_eq_natDegree
          (f1024TowerRegularArtinSchreierPolynomial_monic P a).ne_zero,
        f1024TowerRegularArtinSchreierPolynomial_natDegree]
      norm_num
    have hbaseMap : Function.Injective baseMap :=
      (IsFractionRing.injective model frac).comp hbaseToModel
    let coeffLift : K →+* frac := IsFractionRing.lift hbaseMap
    have hcoeff : phi.toRingHom.comp coeffLift = algebraMap K L := by
      apply IsFractionRing.ringHom_ext (A := P.valuationRing)
      intro c
      change phi (coeffLift (algebraMap P.valuationRing K c)) =
        algebraMap K L (algebraMap P.valuationRing K c)
      rw [IsFractionRing.lift_algebraMap hbaseMap]
      change phi
          (algebraMap model frac (algebraMap P.valuationRing model c)) = _
      rw [phi.commutes]
      exact f1024TowerRegularArtinSchreierModelToActual_of
        P a y hy hgenerate hfinrank c
    let rootFrac : frac := algebraMap model frac
      (AdjoinRoot.root (f1024TowerRegularArtinSchreierPolynomial P a))
    have hroot : phi rootFrac = y := by
      dsimp only [rootFrac]
      rw [phi.commutes]
      exact f1024TowerRegularArtinSchreierModelToActual_root
        P a y hy hgenerate hfinrank
    have heval (r : K[X]) :
        phi (r.eval₂ coeffLift rootFrac) = Polynomial.aeval y r := by
      calc
        phi (r.eval₂ coeffLift rootFrac) =
            r.eval₂ (phi.toRingHom.comp coeffLift) (phi rootFrac) :=
          Polynomial.hom_eval₂ (p := r) coeffLift phi.toRingHom _
        _ = r.eval₂ (algebraMap K L) y := by rw [hcoeff, hroot]
        _ = Polynomial.aeval y r := rfl
    intro z
    have hzmem : z ∈ IntermediateField.adjoin K {y} := by
      rw [hgenerate]
      trivial
    obtain ⟨p, q, hz⟩ :=
      (IntermediateField.mem_adjoin_simple_iff K z).mp hzmem
    refine ⟨p.eval₂ coeffLift rootFrac / q.eval₂ coeffLift rootFrac, ?_⟩
    calc
      phi (p.eval₂ coeffLift rootFrac / q.eval₂ coeffLift rootFrac) =
          Polynomial.aeval y p / Polynomial.aeval y q := by
        rw [map_div₀, heval, heval]
      _ = z := hz.symm
  exact IsFractionRing.of_algEquiv
    (AlgEquiv.ofBijective phi ⟨phi.injective, hphiSurjective⟩)

private theorem f1024TowerRegularArtinSchreierPolynomial_derivative
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    [CharP K 2]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) :
    derivative (f1024TowerRegularArtinSchreierPolynomial P a) = 1 := by
  have h32 : ((32 : ℕ) : P.valuationRing) = 0 := by
    apply Subtype.ext
    change ((32 : ℕ) : K) = 0
    rw [CharP.cast_eq_zero_iff K 2]
    norm_num
  simp only [f1024TowerRegularArtinSchreierPolynomial,
    derivative_sub, derivative_add, derivative_X_pow, derivative_X,
    derivative_C, h32, C_0, zero_mul, zero_add, sub_zero]

private noncomputable def f1024TowerRegularArtinSchreierEtalePair
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    [CharP K 2]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) : StandardEtalePair P.valuationRing where
  f := f1024TowerRegularArtinSchreierPolynomial P a
  monic_f := f1024TowerRegularArtinSchreierPolynomial_monic P a
  g := 1
  cond := ⟨1, 0, 1, by
    rw [f1024TowerRegularArtinSchreierPolynomial_derivative]
    simp⟩

private noncomputable def f1024TowerRegularArtinSchreierEtaleEquiv
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    [CharP K 2]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) :
    (f1024TowerRegularArtinSchreierEtalePair P a).Ring ≃ₐ[P.valuationRing]
      F1024TowerRegularArtinSchreierModel P a := by
  let pair : StandardEtalePair P.valuationRing :=
    f1024TowerRegularArtinSchreierEtalePair P a
  let model : Type _ := F1024TowerRegularArtinSchreierModel P a
  let root : model := AdjoinRoot.mk pair.f pair.g
  have hroot : IsUnit root := by
    change IsUnit
      (AdjoinRoot.mk (f1024TowerRegularArtinSchreierPolynomial P a)
        (1 : P.valuationRing[X]))
    rw [map_one]
    exact isUnit_one
  letI : IsLocalization (Submonoid.powers root) model :=
    IsLocalization.of_le_isUnit (Submonoid.powers_le.mpr hroot)
  exact pair.equivAwayAdjoinRoot.trans
    ((IsLocalization.algEquiv (Submonoid.powers root)
      (Localization.Away root) model).restrictScalars P.valuationRing)

private theorem f1024TowerRegularArtinSchreierModel_formallyUnramified
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    [CharP K 2]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) :
    Algebra.FormallyUnramified P.valuationRing
      (F1024TowerRegularArtinSchreierModel P a) :=
  Algebra.FormallyUnramified.of_equiv
    (f1024TowerRegularArtinSchreierEtaleEquiv P a)

private theorem f1024Tower_globalPlace_valuation_isNontrivial
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k F) :
    P.valuation.IsNontrivial := by
  rw [Valuation.isNontrivial_iff_exists_lt_one]
  refine ⟨P.uniformizer, ?_, ?_⟩
  · apply P.valuation.ne_zero_iff.mp
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  · rw [P.valuation_uniformizer, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)

private theorem f1024Tower_globalPlace_valuationRing_ne_top
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k F) :
    P.valuationRing ≠ ⊤ := by
  intro htop
  exact ((Valuation.valuationSubring_eq_top_iff
    (v := P.valuation)).mp htop)
      (f1024Tower_globalPlace_valuation_isNontrivial P)

private theorem f1024TowerRegularArtinSchreierModel_isDomain
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    IsDomain (F1024TowerRegularArtinSchreierModel P a) :=
  Function.Injective.isDomain
    (f1024TowerRegularArtinSchreierModelToActual
      P a y hy hgenerate hfinrank)
    (f1024TowerRegularArtinSchreierModelToActual_injective
      P a y hy hgenerate hfinrank)

private theorem f1024TowerRegularArtinSchreierModel_isDedekindDomain
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    [CharP K 2]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    IsDedekindDomain (F1024TowerRegularArtinSchreierModel P a) := by
  let model : Type _ := F1024TowerRegularArtinSchreierModel P a
  letI : IsDiscreteValuationRing P.valuationRing :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.valuationRing_isDiscreteValuationRing P
  letI : IsDedekindDomain P.valuationRing := inferInstance
  letI : IsDomain model :=
    f1024TowerRegularArtinSchreierModel_isDomain
      P a y hy hgenerate hfinrank
  letI : Module.Finite P.valuationRing model :=
    (f1024TowerRegularArtinSchreierPolynomial_monic P a).finite_adjoinRoot
  letI : Algebra.FormallyUnramified P.valuationRing model :=
    f1024TowerRegularArtinSchreierModel_formallyUnramified P a
  exact isDedekindDomain.of_formallyUnramified P.valuationRing model

/-- A regular translated Artin--Schreier step has ramification index one at
the actual upper place.  The proof uses the integral monogenic model above:
it is finite and formally unramified over the lower DVR, its fraction field is
the actual upper field, and the localization at the upper centre is exactly
the actual upper valuation ring. -/
private theorem f1024Tower_regularArtinSchreier_restriction_order_eq
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [CharP K 2]
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace k L)
    (a : K) (y : L)
    (ha : 0 ≤
      (f1024Tower_restrictedGlobalPlace
        (k := k) (K := K) (L := L) Q).order a)
    (hy : y ^ 32 + y = algebraMap K L a)
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    ∀ x : K, x ≠ 0 →
      Q.order (algebraMap K L x) =
        (f1024Tower_restrictedGlobalPlace
          (k := k) (K := K) (L := L) Q).order x := by
  classical
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K :=
    f1024Tower_restrictedGlobalPlace (k := k) (K := K) (L := L) Q
  have hrestriction : P.valuation.IsEquiv
      (Q.valuation.comap (algebraMap K L)) := by
    have hport := f1024Tower_normalizedRestrictedValuation_isEquiv_comap
      (K := K) (L := L) Q.valuation Q.normalized
    simp only [P] at hport ⊢
    exact hport
  let aP : P.valuationRing := ⟨a, by
    change P.RegularAt a
    by_cases hazero : a = 0
    · subst a
      simp [QEC.Coding.AlgebraicGeometry.GlobalPlace.RegularAt]
    · exact (P.regularAt_iff_order_nonnegative hazero).mpr ha⟩
  have hyP : y ^ 32 + y = algebraMap K L (aP : K) := by
    simpa only [aP] using hy
  let model : Type _ := F1024TowerRegularArtinSchreierModel P aP
  letI : IsDiscreteValuationRing P.valuationRing :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.valuationRing_isDiscreteValuationRing P
  letI : IsDedekindDomain P.valuationRing := inferInstance
  letI : IsDomain model :=
    f1024TowerRegularArtinSchreierModel_isDomain
      P aP y hyP hgenerate hfinrank
  letI : Module.Finite P.valuationRing model :=
    (f1024TowerRegularArtinSchreierPolynomial_monic P aP).finite_adjoinRoot
  letI : Algebra.FormallyUnramified P.valuationRing model :=
    f1024TowerRegularArtinSchreierModel_formallyUnramified P aP
  letI : IsDedekindDomain model :=
    f1024TowerRegularArtinSchreierModel_isDedekindDomain
      P aP y hyP hgenerate hfinrank
  letI : Algebra model L :=
    f1024TowerRegularArtinSchreierModelActualAlgebra
      P aP y hyP hgenerate hfinrank
  letI : IsScalarTower P.valuationRing model L :=
    f1024TowerRegularArtinSchreierModelActualTower
      P aP y hyP hgenerate hfinrank
  letI : IsFractionRing model L :=
    f1024TowerRegularArtinSchreierModelFractionRing
      P aP y hyP hgenerate hfinrank
  have hbaseToModel : Function.Injective
      (algebraMap P.valuationRing model) := by
    change Function.Injective
      (AdjoinRoot.of (f1024TowerRegularArtinSchreierPolynomial P aP))
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    rw [Polynomial.degree_eq_natDegree
        (f1024TowerRegularArtinSchreierPolynomial_monic P aP).ne_zero,
      f1024TowerRegularArtinSchreierPolynomial_natDegree]
    norm_num
  letI : Module.IsTorsionFree P.valuationRing model :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hbaseToModel
  have hyRegular : Q.RegularAt y :=
    f1024Tower_artinSchreierRoot_regular Q a y ha hy
  let yQ : Q.valuationRing := ⟨y, hyRegular⟩
  have hltOne (c : K) :
      Q.valuation (algebraMap K L c) < 1 ↔ P.valuation c < 1 := by
    rw [lt_iff_not_ge, lt_iff_not_ge]
    apply not_congr
    have hport := (hrestriction 1 c).symm
    simp only [map_one] at hport ⊢
    exact hport
  let lowerToUpper : P.valuationRing →+* Q.valuationRing :=
    (algebraMap P.valuationRing L).codRestrict Q.valuationRing fun c => by
      change Q.valuation (algebraMap K L (c : K)) ≤ 1
      have hcP : P.valuation (c : K) ≤ P.valuation 1 := by
        have hport := c.property
        simp only [map_one] at hport ⊢
        exact hport
      have hc := (hrestriction (c : K) 1).mp hcP
      have hport := hc
      simp only [map_one] at hport ⊢
      exact hport
  let modelToQ : model →+* Q.valuationRing :=
    AdjoinRoot.lift lowerToUpper yQ (by
        simp only [f1024TowerRegularArtinSchreierPolynomial,
          eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C]
        apply sub_eq_zero.mpr
        apply Subtype.ext
        exact hyP)
  have hmodelToQTriangle :
      (ValuationSubring.subtype Q.valuationRing).comp modelToQ =
        f1024TowerRegularArtinSchreierModelToActual
          P aP y hyP hgenerate hfinrank := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro c
      simp only [RingHom.comp_apply, modelToQ, AdjoinRoot.lift_of]
      change algebraMap K L (c : K) =
        f1024TowerRegularArtinSchreierModelToActual
          P aP y hyP hgenerate hfinrank
            (algebraMap P.valuationRing model c)
      exact (f1024TowerRegularArtinSchreierModelToActual_of
        P aP y hyP hgenerate hfinrank c).symm
    · simp only [RingHom.comp_apply, modelToQ, AdjoinRoot.lift_root]
      change y =
        f1024TowerRegularArtinSchreierModelToActual
          P aP y hyP hgenerate hfinrank
            (AdjoinRoot.root
              (f1024TowerRegularArtinSchreierPolynomial P aP))
      exact (f1024TowerRegularArtinSchreierModelToActual_root
        P aP y hyP hgenerate hfinrank).symm
  let centre : Ideal model :=
    (IsLocalRing.maximalIdeal Q.valuationRing).comap modelToQ
  have hcentrePrime : centre.IsPrime := by
    dsimp only [centre]
    exact (IsLocalRing.maximalIdeal Q.valuationRing).comap_isPrime _
  have hcentreUnder : centre.under P.valuationRing =
      IsLocalRing.maximalIdeal P.valuationRing := by
    ext c
    change modelToQ (algebraMap P.valuationRing model c) ∈
        IsLocalRing.maximalIdeal Q.valuationRing ↔
      c ∈ IsLocalRing.maximalIdeal P.valuationRing
    rw [Valuation.mem_maximalIdeal_iff, Valuation.mem_maximalIdeal_iff]
    have hmapc : ((modelToQ
        (algebraMap P.valuationRing model c) : Q.valuationRing) : L) =
        algebraMap K L (c : K) := by
      calc
        ((modelToQ (algebraMap P.valuationRing model c) :
            Q.valuationRing) : L) =
            f1024TowerRegularArtinSchreierModelToActual
              P aP y hyP hgenerate hfinrank
                (algebraMap P.valuationRing model c) := by
          exact RingHom.congr_fun hmodelToQTriangle
            (algebraMap P.valuationRing model c)
        _ = algebraMap K L (c : K) :=
          f1024TowerRegularArtinSchreierModelToActual_of
            P aP y hyP hgenerate hfinrank c
    change Q.valuation
        ((modelToQ (algebraMap P.valuationRing model c) :
          Q.valuationRing) : L) < 1 ↔
      P.valuation (c : K) < 1
    rw [hmapc]
    exact hltOne (c : K)
  have hcentreNe : centre ≠ ⊥ := by
    intro hbot
    have hunder := hcentreUnder
    rw [hbot, Ideal.under_bot] at hunder
    exact IsDiscreteValuationRing.not_a_field P.valuationRing hunder.symm
  let centreHeight : IsDedekindDomain.HeightOneSpectrum model :=
    ⟨centre, hcentrePrime, hcentreNe⟩
  have hprimeComplUnits (s : centreHeight.asIdeal.primeCompl) :
      IsUnit (modelToQ s) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hs
    apply s.property
    change modelToQ (s : model) ∈
      IsLocalRing.maximalIdeal Q.valuationRing
    exact hs
  letI : IsLocalization centreHeight.asIdeal.primeCompl
      (centreHeight.valuationSubringAtPrime L) :=
    Localization.subalgebra.isLocalization_ofField L
      centreHeight.asIdeal.primeCompl _
  let localizationToQ : centreHeight.valuationSubringAtPrime L →+*
      Q.valuationRing :=
    IsLocalization.lift
      (M := centreHeight.asIdeal.primeCompl)
      (g := modelToQ) hprimeComplUnits
  have hlocalizationComp : localizationToQ.comp
      (algebraMap model (centreHeight.valuationSubringAtPrime L)) =
        modelToQ := by
    simpa only [localizationToQ] using
      (IsLocalization.lift_comp hprimeComplUnits)
  have hlocalizationTriangle :
      (ValuationSubring.subtype Q.valuationRing).comp localizationToQ =
        ValuationSubring.subtype
          (centreHeight.valuationSubringAtPrime L) := by
    apply IsLocalization.ringHom_ext centreHeight.asIdeal.primeCompl
    apply DFunLike.ext _ _
    intro b
    change ((localizationToQ
        (algebraMap model (centreHeight.valuationSubringAtPrime L) b) :
          Q.valuationRing) : L) = algebraMap model L b
    rw [← RingHom.comp_apply, hlocalizationComp]
    have htriangle := RingHom.congr_fun hmodelToQTriangle b
    have hport := htriangle
    simp only [RingHom.comp_apply, ValuationSubring.coe_subtype] at hport ⊢
    exact hport
  have hlocalizationLe : centreHeight.valuationSubringAtPrime L ≤
      Q.valuationRing := by
    intro z hz
    let zCentre : centreHeight.valuationSubringAtPrime L := ⟨z, hz⟩
    have htriangle := RingHom.congr_fun hlocalizationTriangle zCentre
    have hzEq : ((localizationToQ zCentre : Q.valuationRing) : L) = z := by
      simpa only [RingHom.comp_apply, ValuationSubring.coe_subtype] using htriangle
    rw [← hzEq]
    exact (localizationToQ zCentre).property
  have hlocalizationEq : centreHeight.valuationSubringAtPrime L =
      Q.valuationRing :=
    ValuationSubring.eq_of_le_of_ne_top _ hlocalizationLe
      (f1024Tower_globalPlace_valuationRing_ne_top Q)
  have hcentreValuationEquiv :
      (centreHeight.valuation L).IsEquiv Q.valuation := by
    rw [Valuation.isEquiv_iff_valuationSubring]
    exact centreHeight.valuationSubringAtPrime_eq_valuationSubring.symm.trans
      hlocalizationEq
  have hcentreValuation : centreHeight.valuation L = Q.valuation :=
    QEC.Coding.AlgebraicGeometry.normalizedValuation_eq_of_isEquiv
      (centreHeight.valuation L) Q.valuation
      (centreHeight.valuation_surjective L) Q.normalized
      hcentreValuationEquiv
  letI : Algebra.IsUnramifiedAt P.valuationRing centre :=
    (Algebra.formallyUnramified_iff_forall.mp
      (f1024TowerRegularArtinSchreierModel_formallyUnramified P aP))
        ⟨centre, hcentrePrime⟩
  have hramUnder : Ideal.ramificationIdx'
      (centre.under P.valuationRing) centre = 1 := by
    letI : centre.IsPrime := hcentrePrime
    rw [Ideal.ramificationIdx'_eq_ramificationIdx
      (centre.under P.valuationRing) centre (by
        rw [hcentreUnder]
        exact IsDiscreteValuationRing.not_a_field P.valuationRing)]
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := P.valuationRing)
  have hram : Ideal.ramificationIdx'
      (IsLocalRing.maximalIdeal P.valuationRing) centre = 1 := by
    rwa [hcentreUnder] at hramUnder
  have hmapNe : Ideal.map (algebraMap P.valuationRing model)
      (IsLocalRing.maximalIdeal P.valuationRing) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot
      (IsDiscreteValuationRing.not_a_field P.valuationRing)
  have hmultiplicity : multiplicity centre
      (Ideal.map (algebraMap P.valuationRing model)
        (IsLocalRing.maximalIdeal P.valuationRing)) = 1 := by
    rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
      hmapNe hcentrePrime]
    exact hram
  let uniformizerP : P.valuationRing := P.uniformizerInValuationRing
  let uniformizerModel : model :=
    algebraMap P.valuationRing model uniformizerP
  have huniformizerPNe : (uniformizerP : K) ≠ 0 := by
    intro hzero
    have hvalue := P.valuation_uniformizer
    change P.valuation (uniformizerP : K) = WithZero.exp (-1 : ℤ) at hvalue
    rw [hzero, map_zero] at hvalue
    exact WithZero.exp_ne_zero hvalue.symm
  have huniformizerModelNe : uniformizerModel ≠ 0 := by
    apply (map_ne_zero_iff
      (algebraMap P.valuationRing model) hbaseToModel).mpr
    intro hzero
    apply huniformizerPNe
    exact congrArg Subtype.val hzero
  have hmapSpan : Ideal.map (algebraMap P.valuationRing model)
      (IsLocalRing.maximalIdeal P.valuationRing) =
        Ideal.span ({uniformizerModel} : Set model) := by
    rw [QEC.Coding.AlgebraicGeometry.GlobalPlace.maximalIdeal_eq_span_uniformizer,
      Ideal.map_span, Set.image_singleton]
  have hmultiplicityUniformizer :
      multiplicity centre (Ideal.span ({uniformizerModel} : Set model)) = 1 := by
    rw [← hmapSpan]
    exact hmultiplicity
  have hmodelUniformizerValue :
      centreHeight.valuation L (algebraMap model L uniformizerModel) =
        WithZero.exp (-1 : ℤ) := by
    rw [centreHeight.valuation_of_algebraMap,
      centreHeight.intValuation_eq_exp_neg_multiplicity huniformizerModelNe,
      hmultiplicityUniformizer]
    norm_num
  have hmodelUniformizerMap : algebraMap model L uniformizerModel =
      algebraMap K L (uniformizerP : K) := by
    change f1024TowerRegularArtinSchreierModelToActual
        P aP y hyP hgenerate hfinrank uniformizerModel = _
    exact f1024TowerRegularArtinSchreierModelToActual_of
      P aP y hyP hgenerate hfinrank uniformizerP
  have hupperUniformizerValue :
      Q.valuation (algebraMap K L (uniformizerP : K)) =
        WithZero.exp (-1 : ℤ) := by
    rw [← hmodelUniformizerMap, ← hcentreValuation]
    exact hmodelUniformizerValue
  have hupperUniformizerOrder :
      Q.order (algebraMap K L (uniformizerP : K)) = 1 := by
    unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order
    rw [hupperUniformizerValue]
    norm_num
  obtain ⟨e, he, hscale⟩ :=
    f1024Tower_restrictedGlobalPlace_order_scale
      (k := k) (K := K) (L := L) Q
  have heOne : e = 1 := by
    have h := hscale (uniformizerP : K) huniformizerPNe
    change Q.order (algebraMap K L (uniformizerP : K)) =
      (e : ℤ) * P.order (uniformizerP : K) at h
    rw [hupperUniformizerOrder] at h
    change (1 : ℤ) = (e : ℤ) * P.order P.uniformizer at h
    rw [P.order_uniformizer] at h
    omega
  intro x hx
  have h := hscale x hx
  change Q.order (algebraMap K L x) = (e : ℤ) * P.order x at h
  rw [heOne] at h
  simpa using h

/-- At an actual successor, every upper place over a place where the current
coordinate is regular has restriction multiplier one.  This is the literal
tower specialization of the integral Artin--Schreier model above. -/
private theorem f1024TowerLevel_step_order_eq_of_lowerX_nonnegative
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1)))
    (hregular : 0 ≤
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Q).order
          (f1024TowerLevelX height)) :
    ∀ u : F1024TowerLevel height, u ≠ 0 →
      Q.order
          (algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)) u) =
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q).order u := by
  have hpower : 0 ≤
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Q).order
          (f1024TowerLevelX height ^ 33) := by
    rw [f1024Tower_globalPlace_order_pow]
    exact mul_nonneg (by norm_num) hregular
  apply f1024Tower_regularArtinSchreier_restriction_order_eq
    Q (f1024TowerLevelX height ^ 33) (f1024TowerLevelZ height)
    hpower
  · exact f1024TowerLevel_step_equation height
  · exact f1024TowerStageStepZ_adjoin_eq_top (f1024TowerStage height)
  · exact f1024TowerStageStep_finrank (f1024TowerStage height)

/-- A source-local translated successor equation with regular right-hand side
has restriction multiplier one.  The translated generator is constructed
from the actual `z_(height+1)` and proved to generate the same upper field. -/
private theorem f1024TowerLevel_step_order_eq_of_translated_rhs_regular
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1)))
    (c t : F1024TowerLevel height) (hcFrobenius : c ^ 32 = c)
    (hregular :
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Q).RegularAt
          (f1024TowerLevelX height ^ 33 + c * (t ^ 32 + t))) :
    ∀ u : F1024TowerLevel height, u ≠ 0 →
      Q.order
          (algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)) u) =
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q).order u := by
  classical
  let K : Type := F1024TowerLevel height
  let L : Type := F1024TowerLevel (height + 1)
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 K :=
    f1024Tower_restrictedGlobalPlace (k := F1024) (K := K) (L := L) Q
  let a : K := f1024TowerLevelX height ^ 33 + c * (t ^ 32 + t)
  let m : L := algebraMap K L (c * t)
  let y : L := f1024TowerLevelZ height + m
  have hmAS : m ^ 32 + m =
      algebraMap K L (c * (t ^ 32 + t)) := by
    dsimp only [m]
    calc
      (algebraMap K L (c * t)) ^ 32 + algebraMap K L (c * t) =
          algebraMap K L ((c * t) ^ 32) + algebraMap K L (c * t) := by
            rw [map_pow]
      _ = algebraMap K L ((c * t) ^ 32 + c * t) := by rw [map_add]
      _ = algebraMap K L (c * (t ^ 32 + t)) := by
        congr 1
        rw [mul_pow, hcFrobenius]
        ring
  have hyPow : y ^ 32 = f1024TowerLevelZ height ^ 32 + m ^ 32 := by
    dsimp only [y]
    simpa only [show (2 ^ 5 : ℕ) = 32 by norm_num] using
      (add_pow_char_pow (R := L) (x := f1024TowerLevelZ height) (y := m) 2 5)
  have hyEquation : y ^ 32 + y = algebraMap K L a := by
    dsimp only [a]
    rw [hyPow]
    calc
      f1024TowerLevelZ height ^ 32 + m ^ 32 +
          (f1024TowerLevelZ height + m) =
        (f1024TowerLevelZ height ^ 32 + f1024TowerLevelZ height) +
          (m ^ 32 + m) := by ring
      _ = algebraMap K L (f1024TowerLevelX height ^ 33) +
          algebraMap K L (c * (t ^ 32 + t)) := by
            rw [f1024TowerLevel_step_equation, hmAS]
      _ = algebraMap K L
          (f1024TowerLevelX height ^ 33 + c * (t ^ 32 + t)) := by
            rw [map_add]
  have hgenerate : IntermediateField.adjoin K {y} = ⊤ := by
    let generated : IntermediateField K L := IntermediateField.adjoin K {y}
    have hymem : y ∈ generated :=
      IntermediateField.subset_adjoin K ({y} : Set L) (Set.mem_singleton y)
    have hmmem : m ∈ generated := generated.algebraMap_mem (c * t)
    have hzEq : f1024TowerLevelZ height = y + m := by
      dsimp only [y]
      calc
        f1024TowerLevelZ height = f1024TowerLevelZ height + 0 :=
          (add_zero _).symm
        _ = f1024TowerLevelZ height + (m + m) := by
          rw [CharTwo.add_self_eq_zero]
        _ = (f1024TowerLevelZ height + m) + m := by ring
    have hzmem : f1024TowerLevelZ height ∈ generated := by
      rw [hzEq]
      exact generated.add_mem hymem hmmem
    have hzAdjoinLe :
        IntermediateField.adjoin K {f1024TowerLevelZ height} ≤ generated := by
      apply IntermediateField.adjoin_le_iff.mpr
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact hzmem
    have hzTop : IntermediateField.adjoin K
        {f1024TowerLevelZ height} = ⊤ := by
      exact f1024TowerStageStepZ_adjoin_eq_top (f1024TowerStage height)
    rw [hzTop] at hzAdjoinLe
    exact top_unique hzAdjoinLe
  have haOrder : 0 ≤ P.order a := by
    have hregular' : P.RegularAt a := by
      simpa only [P, a, K, L] using hregular
    by_cases ha : a = 0
    · change 0 ≤ -WithZero.log (P.valuation a)
      rw [ha, map_zero]
      simp
    · exact (P.regularAt_iff_order_nonnegative ha).mp hregular'
  apply f1024Tower_regularArtinSchreier_restriction_order_eq
    Q a y haOrder hyEquation hgenerate
  exact f1024TowerStageStep_finrank (f1024TowerStage height)

/-- The positive order multiplier of a normalized restricted place is bounded
by the degree of the finite field extension.  The proof is the local
ramification-degree argument: powers of an upper uniformizer below the
multiplier have pairwise incongruent orders, hence are linearly independent
over the lower field. -/
private theorem f1024Tower_restrictedGlobalPlace_order_scale_le_finrank
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]
  (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace k L) :
    ∃ e : ℕ, 0 < e ∧ e ≤ Module.finrank K L ∧ ∀ x : K, x ≠ 0 →
      Q.order (algebraMap K L x) =
        (e : ℤ) *
          (f1024Tower_restrictedGlobalPlace
            (k := k) (K := K) (L := L) Q).order x := by
  classical
  obtain ⟨e, he, hscale⟩ :=
    f1024Tower_restrictedGlobalPlace_order_scale
      (k := k) (K := K) (L := L) Q
  letI : NeZero e := ⟨Nat.ne_of_gt he⟩
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K :=
    f1024Tower_restrictedGlobalPlace (k := k) (K := K) (L := L) Q
  have huniformizer : Q.uniformizer ≠ 0 := by
    intro hzero
    have hvalue := Q.valuation_uniformizer
    rw [hzero, map_zero] at hvalue
    exact WithZero.exp_ne_zero hvalue.symm
  have halgebraMap_ne {x : K} (hx : x ≠ 0) :
      algebraMap K L x ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap K L)
      (algebraMap K L).injective).mpr hx
  have hvaluation_exp {x : L} (hx : x ≠ 0) :
      Q.valuation x = WithZero.exp (-Q.order x) := by
    have h := (WithZero.exp_log
      ((Valuation.ne_zero_iff Q.valuation).mpr hx)).symm
    simpa only [QEC.Coding.AlgebraicGeometry.GlobalPlace.order,
      neg_neg] using h
  have hpowerOrder (i : Fin e) :
      Q.order (Q.uniformizer ^ (i : ℕ)) = (i : ℤ) := by
    unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order
    rw [map_pow, Q.valuation_uniformizer, WithZero.log_pow]
    simp only [WithZero.log_exp, nsmul_eq_mul]
    ring
  have htermOrder (coefficient : K) (hcoefficient : coefficient ≠ 0)
      (i : Fin e) :
      Q.order (coefficient • Q.uniformizer ^ (i : ℕ)) =
        (e : ℤ) * P.order coefficient + (i : ℤ) := by
    rw [Algebra.smul_def,
      Q.order_mul (halgebraMap_ne hcoefficient)
        (pow_ne_zero _ huniformizer),
      hscale coefficient hcoefficient, hpowerOrder]
  have htermOrder_ne (coefficient : Fin e → K) {i j : Fin e}
      (hij : i ≠ j) (hi : coefficient i ≠ 0) (hj : coefficient j ≠ 0) :
      Q.order (coefficient i • Q.uniformizer ^ (i : ℕ)) ≠
        Q.order (coefficient j • Q.uniformizer ^ (j : ℕ)) := by
    intro horder
    rw [htermOrder (coefficient i) hi i,
      htermOrder (coefficient j) hj j] at horder
    have hcast := congrArg (fun z : ℤ => (z : ZMod e)) horder
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_self, zero_mul, zero_add] at hcast
    apply hij
    apply Fin.ext
    have hval := congrArg ZMod.val hcast
    simpa only [ZMod.val_natCast_of_lt i.isLt,
      ZMod.val_natCast_of_lt j.isLt] using hval
  let powers : Fin e → L := fun i => Q.uniformizer ^ (i : ℕ)
  have hpowers : LinearIndependent K powers := by
    rw [Fintype.linearIndependent_iff]
    intro coefficient hsum i
    by_contra hi
    let support : Finset (Fin e) :=
      Finset.univ.filter fun j => coefficient j ≠ 0
    have hsupport : support.Nonempty := by
      refine ⟨i, ?_⟩
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi
    obtain ⟨j, hjmem, hjmax⟩ :=
      Finset.exists_max_image support
        (fun j => Q.valuation (coefficient j • powers j)) hsupport
    have hj : coefficient j ≠ 0 := by
      simpa only [support, Finset.mem_filter, Finset.mem_univ,
        true_and] using hjmem
    have hjterm : coefficient j • powers j ≠ 0 := by
      dsimp only [powers]
      rw [Algebra.smul_def]
      exact mul_ne_zero (halgebraMap_ne hj)
        (pow_ne_zero _ huniformizer)
    have hstrict : ∀ m ∈ (Finset.univ : Finset (Fin e)) \ {j},
        Q.valuation (coefficient m • powers m) <
          Q.valuation (coefficient j • powers j) := by
      intro m hm
      have hmj : m ≠ j := by
        simpa using (Finset.mem_sdiff.mp hm).2
      by_cases hmzero : coefficient m = 0
      · rw [hmzero, zero_smul, map_zero]
        exact WithZero.pos_iff_ne_zero.mpr
          ((Valuation.ne_zero_iff Q.valuation).mpr hjterm)
      · have hmmem : m ∈ support := by
          simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hmzero
        have hle := hjmax m hmmem
        apply lt_of_le_of_ne hle
        intro hvalue
        apply htermOrder_ne coefficient hmj hmzero hj
        have hmterm : coefficient m • powers m ≠ 0 := by
          dsimp only [powers]
          rw [Algebra.smul_def]
          exact mul_ne_zero (halgebraMap_ne hmzero)
            (pow_ne_zero _ huniformizer)
        have hmexp : Q.valuation (coefficient m • powers m) =
            WithZero.exp
              (-Q.order (coefficient m • Q.uniformizer ^ (m : ℕ))) := by
          exact hvaluation_exp hmterm
        have hjexp : Q.valuation (coefficient j • powers j) =
            WithZero.exp
              (-Q.order (coefficient j • Q.uniformizer ^ (j : ℕ))) := by
          exact hvaluation_exp hjterm
        dsimp only [powers] at hvalue
        rw [hmexp, hjexp] at hvalue
        have := WithZero.exp_inj.mp hvalue
        omega
    have hvaluation :
        Q.valuation (∑ m : Fin e, coefficient m • powers m) =
          Q.valuation (coefficient j • powers j) := by
      change Q.valuation
          (∑ m ∈ (Finset.univ : Finset (Fin e)), coefficient m • powers m) =
        Q.valuation (coefficient j • powers j)
      exact Q.valuation.map_sum_eq_of_lt (Finset.mem_univ j) hstrict
    rw [hsum, map_zero] at hvaluation
    exact ((Valuation.ne_zero_iff Q.valuation).mpr hjterm) hvaluation.symm
  refine ⟨e, he, ?_, hscale⟩
  simpa only [Fintype.card_fin] using hpowers.fintype_card_le_finrank

/-- A simple pole of the current coordinate is totally ramified in its
literal successor, and the successor coordinate again has a simple pole.
This is the normalized local form of Garcia--Stichtenoth Lemma 2.1: the
recurrence makes `32` divide the restriction multiplier, while the genuine
finite-extension bound makes that multiplier at most `32`. -/
private theorem f1024TowerLevel_step_order_scale_eq_32_of_lowerX_eq_neg_one
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1)))
    (hpole :
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Q).order
          (f1024TowerLevelX height) = -1) :
    (∀ u : F1024TowerLevel height, u ≠ 0 →
      Q.order
          (algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)) u) =
        32 *
          (f1024Tower_restrictedGlobalPlace
            (k := F1024) (K := F1024TowerLevel height)
            (L := F1024TowerLevel (height + 1)) Q).order u) ∧
      Q.order (f1024TowerLevelX (height + 1)) = -1 := by
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) :=
    f1024Tower_restrictedGlobalPlace
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  obtain ⟨e, hepos, hebound, hscale⟩ :=
    f1024Tower_restrictedGlobalPlace_order_scale_le_finrank
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  have hebound32 : e ≤ 32 := by
    change e ≤ Module.finrank (f1024TowerStage height).carrier
      (F1024TowerStageStep (f1024TowerStage height)) at hebound
    rw [f1024TowerStageStep_finrank (f1024TowerStage height)] at hebound
    exact hebound
  let u : F1024TowerLevel (height + 1) :=
    algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
      (f1024TowerLevelX height)
  let v : F1024TowerLevel (height + 1) := f1024TowerLevelX (height + 1)
  have hu : u ≠ 0 :=
    (map_ne_zero_iff
      (algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1)))
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1))).injective).mpr
          (f1024TowerLevelX_ne_zero height)
  have hv : v ≠ 0 := f1024TowerLevelX_ne_zero (height + 1)
  have huOrder : Q.order u = -(e : ℤ) := by
    have h := hscale (f1024TowerLevelX height)
      (f1024TowerLevelX_ne_zero height)
    change Q.order u = (e : ℤ) * P.order (f1024TowerLevelX height) at h
    rw [hpole] at h
    simpa only [mul_neg, mul_one] using h
  let directConstantAlgebra : Algebra F1024 (F1024TowerLevel (height + 1)) :=
    @QEC.Coding.AlgebraicGeometry.AffinePlace.constantAlgebra
      F1024 (F1024TowerLevel (height + 1)) _ _
        (inferInstance : Algebra F1024[X] (F1024TowerLevel (height + 1)))
  let Qdirect :
      @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
        (F1024TowerLevel (height + 1)) _ _ _ directConstantAlgebra :=
    { valuation :=
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024
          (F1024TowerLevel (height + 1)) _ _ _
            (f1024TowerStage (height + 1)).constantAlgebraInst Q
      normalized :=
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized F1024
          (F1024TowerLevel (height + 1)) _ _ _
            (f1024TowerStage (height + 1)).constantAlgebraInst Q }
  have hcasesDirect :=
    f1024Tower_recurrence_order_cases
      (F1024TowerLevel (height + 1)) Qdirect hu hv
        (by simpa only [u, v] using f1024TowerLevel_step_X_recurrence height)
  have hQdirectOrder (x : F1024TowerLevel (height + 1)) :
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024
          (F1024TowerLevel (height + 1)) _ _ _ directConstantAlgebra
          Qdirect x =
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024
          (F1024TowerLevel (height + 1)) _ _ _
          (f1024TowerStage (height + 1)).constantAlgebraInst Q x := by
    rfl
  obtain hPole | hZero | hCancel := hcasesDirect
  · simp only [hQdirectOrder] at hPole
    have he : e = 32 := by
      rcases hPole with ⟨_, hrelation⟩
      rw [huOrder] at hrelation
      omega
    constructor
    · intro x hx
      have h := hscale x hx
      rw [he] at h
      exact h
    · rcases hPole with ⟨_, hrelation⟩
      rw [huOrder, he] at hrelation
      change @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024
        (F1024TowerLevel (height + 1)) _ _ _
          (f1024TowerStage (height + 1)).constantAlgebraInst Q v = -1
      omega
  · simp only [hQdirectOrder] at hZero
    rw [huOrder] at hZero
    omega
  · simp only [hQdirectOrder] at hCancel
    rw [huOrder] at hCancel
    omega

/-- The exact local content of Garcia--Stichtenoth Lemma 2.6.  At a common
zero of two successive source coordinates, the inverse thirty-third power of
the later coordinate differs from the Artin--Schreier image of the preceding
inverse thirty-third power by a regular function.  The proof uses the literal
recurrence: the apparent principal parts combine into the Artin--Schreier
image of `(ab)⁻¹ + (a^33)⁻¹`, whose order is positive. -/
private theorem f1024Tower_inverseThirtyThree_sub_artinSchreier_regular
    {F : Type*} [Field F] [Algebra F1024 F] [CharP F 2]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F)
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrec : a ^ 31 * b ^ 32 + b = a ^ 32)
    (haOrder : 0 < P.order a)
    (hbOrder : P.order b = 32 * P.order a) :
    P.RegularAt
      (b⁻¹ ^ 33 - ((a⁻¹ ^ 33) ^ 32 + a⁻¹ ^ 33)) := by
  let z : F := a * b
  let y : F := a ^ 33
  let t : F := z⁻¹ + y⁻¹
  have hz : z ≠ 0 := mul_ne_zero ha hb
  have hy : y ≠ 0 := pow_ne_zero 33 ha
  have hzy : z ^ 32 + z = y := by
    dsimp only [z, y]
    rw [mul_pow]
    calc
      a ^ 32 * b ^ 32 + a * b =
          a * (a ^ 31 * b ^ 32 + b) := by ring
      _ = a * a ^ 32 := by rw [hrec]
      _ = a ^ 33 := by ring
  have hbInv : b⁻¹ ^ 33 = z⁻¹ ^ 32 + z⁻¹ := by
    calc
      b⁻¹ ^ 33 = a ^ 33 * z⁻¹ ^ 33 := by
        dsimp only [z]
        field_simp [ha, hb]
      _ = y * z⁻¹ ^ 33 := by rfl
      _ = (z ^ 32 + z) * z⁻¹ ^ 33 := by rw [hzy]
      _ = z⁻¹ ^ 32 + z⁻¹ := by field_simp [hz] <;> ring
  have haInv : a⁻¹ ^ 33 = y⁻¹ := by
    dsimp only [y]
    exact inv_pow a 33
  have htForm : t = z ^ 31 * y⁻¹ := by
    dsimp only [t]
    field_simp [hz, hy]
    calc
      y + z = (z ^ 32 + z) + z := by rw [hzy]
      _ = z ^ 32 := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hzOrder : P.order z = 33 * P.order a := by
    dsimp only [z]
    rw [P.order_mul ha hb, hbOrder]
    ring
  have hyOrder : P.order y = 33 * P.order a := by
    dsimp only [y]
    rw [f1024Tower_globalPlace_order_pow P]
    norm_num
  have htNe : t ≠ 0 := by
    rw [htForm]
    exact mul_ne_zero (pow_ne_zero 31 hz) (inv_ne_zero hy)
  have htOrder : P.order t = 990 * P.order a := by
    rw [htForm, P.order_mul (pow_ne_zero 31 hz) (inv_ne_zero hy),
      f1024Tower_globalPlace_order_pow P, P.order_inv, hzOrder, hyOrder]
    ring
  have htRegular : P.RegularAt t :=
    (P.regularAt_iff_order_nonnegative htNe).mpr (by
      rw [htOrder]
      exact mul_nonneg (by norm_num) haOrder.le)
  have hArtinSchreierRegular : P.RegularAt (t ^ 32 + t) := by
    rw [P.regularAt_iff_mem_valuationRing] at htRegular ⊢
    exact P.valuationRing.toSubring.add_mem
      (P.valuationRing.toSubring.pow_mem htRegular 32) htRegular
  convert hArtinSchreierRegular using 1
  rw [hbInv, haInv]
  rw [CharTwo.sub_eq_add]
  dsimp only [t]
  rw [show 32 = 2 ^ 5 by norm_num, add_pow_char_pow]
  ring

/-- Regularity of an Artin--Schreier image forces regularity of its input.
Indeed, a pole of `t` would make the `t^32` term strictly dominant. -/
private theorem f1024Tower_regularAt_of_artinSchreier_regular
    {F : Type*} [Field F] [Algebra F1024 F] [CharP F 2]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F)
    (t : F) (hregular : P.RegularAt (t ^ 32 + t)) :
    P.RegularAt t := by
  by_cases ht : t = 0
  · subst t
    simp [QEC.Coding.AlgebraicGeometry.GlobalPlace.RegularAt]
  · apply (P.regularAt_iff_order_nonnegative ht).mpr
    by_contra hnegative
    have htOrder : P.order t < 0 := by omega
    have htValue : P.valuation t = WithZero.exp (-P.order t) := by
      have h := (WithZero.exp_log
        ((Valuation.ne_zero_iff P.valuation).mpr ht)).symm
      simpa only [QEC.Coding.AlgebraicGeometry.GlobalPlace.order,
        neg_neg] using h
    have hpowValue : P.valuation (t ^ 32) =
        WithZero.exp ((32 : ℤ) * (-P.order t)) := by
      rw [map_pow, htValue, ← WithZero.exp_nsmul, nsmul_eq_mul]
      norm_num
    have hlt : P.valuation t < P.valuation (t ^ 32) := by
      rw [htValue, hpowValue, WithZero.exp_lt_exp]
      omega
    have hsumValue : P.valuation (t ^ 32 + t) =
        P.valuation (t ^ 32) := by
      rw [Valuation.map_add_eq_of_lt_left P.valuation hlt]
    have hpowGt : 1 < P.valuation (t ^ 32) := by
      rw [hpowValue, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    rw [QEC.Coding.AlgebraicGeometry.GlobalPlace.RegularAt,
      hsumValue] at hregular
    exact (not_lt_of_ge hregular) hpowGt

/-- The local translation at the zero-to-pole switch in Garcia--Stichtenoth
Lemma 2.7.  If successive coordinates have opposite nonzero orders, the
residue of their product is one of the actual embedded `F₃₂` roots of
`T^32 + T`.  Translating by that root produces a positive-order correction
and hence a regular remainder in the thirty-third-power relation. -/
private theorem f1024Tower_exists_regular_thirtyThree_translation
    {F : Type*} [Field F] [Algebra F1024 F] [CharP F 2]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F)
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrec : a ^ 31 * b ^ 32 + b = a ^ 32)
    (haOrder : 0 < P.order a)
    (hbOrder : P.order b = -P.order a) :
    ∃ gamma : F1024, gamma ≠ 0 ∧ gamma ^ 32 = gamma ∧
      P.RegularAt
        (b ^ 33 - algebraMap F1024 F gamma * a⁻¹ ^ 33) := by
  classical
  let z : F := a * b
  have hz : z ≠ 0 := mul_ne_zero ha hb
  have hzy : z ^ 32 + z = a ^ 33 := by
    dsimp only [z]
    rw [mul_pow]
    calc
      a ^ 32 * b ^ 32 + a * b =
          a * (a ^ 31 * b ^ 32 + b) := by ring
      _ = a * a ^ 32 := by rw [hrec]
      _ = a ^ 33 := by ring
  have hzOrder : P.order z = 0 := by
    dsimp only [z]
    rw [P.order_mul ha hb, hbOrder]
    ring
  have hzRegular : P.RegularAt z :=
    (P.regularAt_iff_order_nonnegative hz).mpr (by rw [hzOrder])
  have haRegular : P.RegularAt a :=
    (P.regularAt_iff_order_nonnegative ha).mpr haOrder.le
  let zP : P.valuationRing :=
    ⟨z, (P.regularAt_iff_mem_valuationRing z).mp hzRegular⟩
  let aP : P.valuationRing :=
    ⟨a, (P.regularAt_iff_mem_valuationRing a).mp haRegular⟩
  letI : Algebra F1024 P.residueField :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.residueAlgebra P
  letI : CharP P.residueField 2 :=
    charP_of_injective_algebraMap
      (algebraMap F1024 P.residueField).injective 2
  have haMaximal : aP ∈ IsLocalRing.maximalIdeal P.valuationRing := by
    rw [Valuation.mem_maximalIdeal_iff]
    change P.valuation a < 1
    have hvaluation :
        P.valuation a = WithZero.exp (-P.order a) := by
      have h := (WithZero.exp_log
        ((Valuation.ne_zero_iff P.valuation).mpr ha)).symm
      simpa only [QEC.Coding.AlgebraicGeometry.GlobalPlace.order,
        neg_neg] using h
    rw [hvaluation, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have haResidue : P.residue aP = 0 :=
    (P.residue_eq_zero_iff aP).mpr haMaximal
  have hresidueEquation :
      P.residue zP ^ 32 + P.residue zP = 0 := by
    have hsubtype : zP ^ 32 + zP = aP ^ 33 := by
      apply Subtype.ext
      exact hzy
    have hmap := congrArg P.residue hsubtype
    simpa only [map_add, map_pow, haResidue, zero_pow (by norm_num : 33 ≠ 0)]
      using hmap
  let p : (GaloisField 2 5)[X] := X ^ 32 - X
  have hpSplits : p.Splits := by
    rw [Polynomial.splits_iff_card_roots]
    dsimp only [p]
    rw [← f1024TowerStepLabel_card,
      FiniteField.roots_X_pow_card_sub_X,
      ← Finset.card_def, Finset.card_univ,
      FiniteField.X_pow_card_sub_X_natDegree_eq]
    norm_num [f1024TowerStepLabel_card]
  have hpNe : p ≠ 0 := by
    dsimp only [p]
    rw [← f1024TowerStepLabel_card]
    exact FiniteField.X_pow_card_sub_X_ne_zero
      (GaloisField 2 5) Fintype.one_lt_card
  let residueEmbedding : GaloisField 2 5 →+* P.residueField :=
    (algebraMap F1024 P.residueField).comp
      f1024TowerStepLabelEmbedding.toRingHom
  have hroot : (p.map residueEmbedding).IsRoot (P.residue zP) := by
    simp only [Polynomial.IsRoot, p, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [CharTwo.sub_eq_add]
    exact hresidueEquation
  obtain ⟨label, hlabelResidue⟩ :=
    hpSplits.mem_range_of_isRoot hpNe hroot
  let c0 : F1024 := f1024TowerStepLabelEmbedding label
  let c : F := algebraMap F1024 F c0
  let cP : P.valuationRing :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.constantsToValuationRing P c0
  have hc0Kernel : c0 ^ 32 + c0 = 0 := by
    exact f1024TowerStepLabelEmbedding_kernel label
  have hcKernel : c ^ 32 + c = 0 := by
    dsimp only [c]
    rw [← map_pow, ← map_add, hc0Kernel, map_zero]
  have hcFrobenius : c ^ 32 = c := by
    rw [← sub_eq_zero]
    simpa only [CharTwo.sub_eq_add] using hcKernel
  have hconstantResidue : P.residue cP = residueEmbedding label := by
    rfl
  let w : F := z + c
  let wP : P.valuationRing := zP + cP
  have hwResidue : P.residue wP = 0 := by
    rw [map_add, hconstantResidue, hlabelResidue]
    exact CharTwo.add_self_eq_zero (P.residue zP)
  have hwMaximal : wP ∈ IsLocalRing.maximalIdeal P.valuationRing :=
    (P.residue_eq_zero_iff wP).mp hwResidue
  have hwValue : P.valuation w < 1 := by
    rw [Valuation.mem_maximalIdeal_iff] at hwMaximal
    exact hwMaximal
  have hwEquation : w ^ 32 + w = a ^ 33 := by
    dsimp only [w]
    rw [show 32 = 2 ^ 5 by norm_num, add_pow_char_pow]
    linear_combination hzy + hcKernel
  have hw : w ≠ 0 := by
    intro hwZero
    have haPowerZero : a ^ 33 = 0 := by
      rw [← hwEquation, hwZero]
      simp
    exact (pow_ne_zero 33 ha) haPowerZero
  have hwOrderPositive : 0 < P.order w := by
    unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order
    rw [neg_pos, ← WithZero.log_one,
      WithZero.log_lt_log
        ((Valuation.ne_zero_iff P.valuation).mpr hw) one_ne_zero]
    exact hwValue
  have hwOrder : P.order w = 33 * P.order a := by
    have hpowOrder : P.order (w ^ 32) = 32 * P.order w := by
      rw [f1024Tower_globalPlace_order_pow P]
      norm_num
    have hlt : P.order w < P.order (w ^ 32) := by
      rw [hpowOrder]
      omega
    have hpowValue : P.valuation (w ^ 32) =
        WithZero.exp (-P.order (w ^ 32)) := by
      have h := (WithZero.exp_log ((Valuation.ne_zero_iff P.valuation).mpr
        (pow_ne_zero 32 hw))).symm
      simpa only [QEC.Coding.AlgebraicGeometry.GlobalPlace.order,
        neg_neg] using h
    have hwValue' : P.valuation w = WithZero.exp (-P.order w) := by
      have h := (WithZero.exp_log
        ((Valuation.ne_zero_iff P.valuation).mpr hw)).symm
      simpa only [QEC.Coding.AlgebraicGeometry.GlobalPlace.order,
        neg_neg] using h
    have hvaluationLt : P.valuation (w ^ 32) < P.valuation w := by
      rw [hpowValue, hwValue', WithZero.exp_lt_exp]
      omega
    have hsum : P.order (w ^ 32 + w) = P.order w := by
      unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order
      rw [Valuation.map_add_eq_of_lt_right P.valuation hvaluationLt]
    rw [hwEquation, f1024Tower_globalPlace_order_pow P] at hsum
    norm_num at hsum
    exact hsum.symm
  have hlabel : label ≠ 0 := by
    intro hlabelZero
    subst label
    have hcZero : c = 0 := by simp [c, c0]
    have hwEq : w = z := by simp [w, hcZero]
    rw [hwEq, hzOrder] at hwOrderPositive
    omega
  have hc0 : c0 ≠ 0 := by
    have hport := f1024TowerStepLabelEmbedding.injective.ne hlabel
    simp only [c0, map_zero] at hport ⊢
    exact hport
  have hc : c ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap F1024 F)
      (algebraMap F1024 F).injective).mpr hc0
  let gamma : F1024 := c0 ^ 33
  have hgamma : gamma ≠ 0 := pow_ne_zero 33 hc0
  have hgammaFrobenius : gamma ^ 32 = gamma := by
    exact f1024_pow_thirtyThree_frobenius hc0
  have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
  have hpowerIdentity : z ^ 33 - c ^ 33 = c * a ^ 33 + w ^ 33 := by
    rw [CharTwo.sub_eq_add]
    calc
      z ^ 33 + c ^ 33 = z ^ 33 + c ^ 32 * c := by
        congr 1
        rw [show 33 = 32 + 1 by norm_num, pow_add, pow_one]
      _ = c * (z ^ 32 + z) +
          (z ^ 32 + c ^ 32) * (z + c) := by
        rw [hcFrobenius]
        ring_nf
        simp only [htwo, mul_zero, add_zero, zero_add]
      _ = c * a ^ 33 + (z + c) ^ 32 * (z + c) := by
        rw [hzy, show 32 = 2 ^ 5 by norm_num, add_pow_char_pow]
      _ = c * a ^ 33 + w ^ 33 := by
        dsimp only [w]
        congr 1
        rw [show 33 = 32 + 1 by norm_num, pow_add, pow_one]
  have htarget :
      b ^ 33 - algebraMap F1024 F gamma * a⁻¹ ^ 33 =
        c + (w / a) ^ 33 := by
    calc
      b ^ 33 - algebraMap F1024 F gamma * a⁻¹ ^ 33 =
          (z ^ 33 - c ^ 33) * a⁻¹ ^ 33 := by
        dsimp only [gamma, c, z]
        rw [map_pow]
        field_simp [ha]
      _ = (c * a ^ 33 + w ^ 33) * a⁻¹ ^ 33 := by
        rw [hpowerIdentity]
      _ = c + (w / a) ^ 33 := by
        field_simp [ha]
  have hcOrder : P.order c = 0 := by
    exact QEC.Coding.AlgebraicGeometry.GlobalPlace.order_algebraMap P c0 hc0
  have hcRegular : P.RegularAt c :=
    (P.regularAt_iff_order_nonnegative hc).mpr (by rw [hcOrder])
  have hquotient : w / a ≠ 0 := div_ne_zero hw ha
  have hquotientOrder : P.order (w / a) = 32 * P.order a := by
    rw [div_eq_mul_inv, P.order_mul hw (inv_ne_zero ha), P.order_inv,
      hwOrder]
    ring
  have hquotientPowerRegular : P.RegularAt ((w / a) ^ 33) :=
    (P.regularAt_iff_order_nonnegative (pow_ne_zero 33 hquotient)).mpr (by
      rw [f1024Tower_globalPlace_order_pow P, hquotientOrder]
      nlinarith)
  have hsumRegular : P.RegularAt (c + (w / a) ^ 33) := by
    apply (P.regularAt_iff_mem_valuationRing _).mpr
    exact P.valuationRing.toSubring.add_mem
      ((P.regularAt_iff_mem_valuationRing c).mp hcRegular)
      ((P.regularAt_iff_mem_valuationRing ((w / a) ^ 33)).mp
        hquotientPowerRegular)
  refine ⟨gamma, hgamma, hgammaFrobenius, ?_⟩
  rw [htarget]
  exact hsumRegular

/-- The induction step in Garcia--Stichtenoth Lemma 2.7, formulated entirely
inside one ambient tower level.  The pair `(u,v)` is on the positive-order
side of a switch, `(x,y)` is the corresponding pole pair, and the previous
translated thirty-third-power relation advances by one recurrence on each
side. -/
private theorem f1024Tower_regular_thirtyThree_translation_step
    {F : Type*} [Field F] [Algebra F1024 F] [CharP F 2]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F)
    (u v x y : F) (hu : u ≠ 0) (hv : v ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (huv : u ^ 31 * v ^ 32 + v = u ^ 32)
    (hxy : x ^ 31 * y ^ 32 + y = x ^ 32)
    (huOrder : 0 < P.order u)
    (hvOrder : P.order v = 32 * P.order u)
    (hxOrder : P.order x = -P.order v)
    (gamma : F1024) (hgamma : gamma ≠ 0)
    (hgammaFrobenius : gamma ^ 32 = gamma)
    (hprevious : P.RegularAt
      (x ^ 33 - algebraMap F1024 F gamma * v⁻¹ ^ 33)) :
    P.RegularAt
      (y ^ 33 - algebraMap F1024 F gamma * u⁻¹ ^ 33) := by
  let g : F := algebraMap F1024 F gamma
  have hg : g ≠ 0 :=
    (map_ne_zero_iff (algebraMap F1024 F)
      (algebraMap F1024 F).injective).mpr hgamma
  have hgFrobenius : g ^ 32 = g := by
    dsimp only [g]
    rw [← map_pow, hgammaFrobenius]
  have hgOrder : P.order g = 0 :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.order_algebraMap
      P gamma hgamma
  have hgRegular : P.RegularAt g :=
    (P.regularAt_iff_order_nonnegative hg).mpr (by rw [hgOrder])
  have hgInvRegular : P.RegularAt g⁻¹ :=
    (P.regularAt_iff_order_nonnegative (inv_ne_zero hg)).mpr (by
      rw [P.order_inv, hgOrder]
      norm_num)
  have regularAdd {a b : F} (ha : P.RegularAt a) (hb : P.RegularAt b) :
      P.RegularAt (a + b) := by
    apply (P.regularAt_iff_mem_valuationRing _).mpr
    exact P.valuationRing.toSubring.add_mem
      ((P.regularAt_iff_mem_valuationRing a).mp ha)
      ((P.regularAt_iff_mem_valuationRing b).mp hb)
  have regularMul {a b : F} (ha : P.RegularAt a) (hb : P.RegularAt b) :
      P.RegularAt (a * b) := by
    apply (P.regularAt_iff_mem_valuationRing _).mpr
    exact P.valuationRing.toSubring.mul_mem
      ((P.regularAt_iff_mem_valuationRing a).mp ha)
      ((P.regularAt_iff_mem_valuationRing b).mp hb)
  have regularPow {a : F} (ha : P.RegularAt a) (n : ℕ) :
      P.RegularAt (a ^ n) := by
    apply (P.regularAt_iff_mem_valuationRing _).mpr
    exact P.valuationRing.toSubring.pow_mem
      ((P.regularAt_iff_mem_valuationRing a).mp ha) n
  have huRegular : P.RegularAt u :=
    (P.regularAt_iff_order_nonnegative hu).mpr huOrder.le
  have hvOrderPositive : 0 < P.order v := by rw [hvOrder]; omega
  have hvRegular : P.RegularAt v :=
    (P.regularAt_iff_order_nonnegative hv).mpr hvOrderPositive.le
  have hxvOrder : P.order (x * v) = 0 := by
    rw [P.order_mul hx hv, hxOrder]
    ring
  have hxv : x * v ≠ 0 := mul_ne_zero hx hv
  have hxvRegular : P.RegularAt (x * v) :=
    (P.regularAt_iff_order_nonnegative hxv).mpr (by rw [hxvOrder])
  have hxvInvPowerRegular : P.RegularAt ((x * v) ^ 33)⁻¹ :=
    (P.regularAt_iff_order_nonnegative
      (inv_ne_zero (pow_ne_zero 33 hxv))).mpr (by
        rw [P.order_inv, f1024Tower_globalPlace_order_pow P, hxvOrder]
        norm_num)
  have hvDivOrder : P.order (v / u ^ 32) = 0 := by
    rw [div_eq_mul_inv, P.order_mul hv (inv_ne_zero (pow_ne_zero 32 hu)),
      P.order_inv, f1024Tower_globalPlace_order_pow P, hvOrder]
    ring
  have hvDiv : v / u ^ 32 ≠ 0 := div_ne_zero hv (pow_ne_zero 32 hu)
  have hvDivRegular : P.RegularAt (v / u ^ 32) :=
    (P.regularAt_iff_order_nonnegative hvDiv).mpr (by rw [hvDivOrder])
  have huvInverseRegular :=
    f1024Tower_inverseThirtyThree_sub_artinSchreier_regular
      P u v hu hv huv huOrder hvOrder
  let H : F := x ^ 33 + g * v⁻¹ ^ 33
  let L : F := v⁻¹ ^ 33 + ((u⁻¹ ^ 33) ^ 32 + u⁻¹ ^ 33)
  have hHRegular : P.RegularAt H := by
    simpa only [H, g, CharTwo.sub_eq_add] using hprevious
  have hLRegular : P.RegularAt L := by
    simpa only [L, CharTwo.sub_eq_add] using huvInverseRegular
  let z : F := x * y
  have hz : z ≠ 0 := mul_ne_zero hx hy
  have hzEquation : z ^ 32 + z = x ^ 33 := by
    dsimp only [z]
    rw [mul_pow]
    calc
      x ^ 32 * y ^ 32 + x * y =
          x * (x ^ 31 * y ^ 32 + y) := by ring
      _ = x * x ^ 32 := by rw [hxy]
      _ = x ^ 33 := by ring
  let C : F := z + g * u⁻¹ ^ 33
  have hCEquation : C ^ 32 + C = H + g * L := by
    have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
    have hCpow : C ^ 32 = z ^ 32 + (g * u⁻¹ ^ 33) ^ 32 := by
      dsimp only [C]
      simpa only [show (2 ^ 5 : ℕ) = 32 by norm_num] using
        (add_pow_char_pow (R := F) (x := z) (y := g * u⁻¹ ^ 33) 2 5)
    have hgUPow : (g * u⁻¹ ^ 33) ^ 32 =
        g * (u⁻¹ ^ 33) ^ 32 := by
      rw [mul_pow, hgFrobenius]
    dsimp only [C, H, L]
    rw [hCpow, hgUPow]
    calc
      z ^ 32 + g * (u⁻¹ ^ 33) ^ 32 + (z + g * u⁻¹ ^ 33) =
          (z ^ 32 + z) + g * (u⁻¹ ^ 33) ^ 32 + g * u⁻¹ ^ 33 := by
            ring
      _ = x ^ 33 + g * (u⁻¹ ^ 33) ^ 32 + g * u⁻¹ ^ 33 := by
        rw [hzEquation]
      _ = x ^ 33 + g * v⁻¹ ^ 33 +
          g * (v⁻¹ ^ 33 + ((u⁻¹ ^ 33) ^ 32 + u⁻¹ ^ 33)) := by
        ring_nf
        simp only [htwo, mul_zero, add_zero]
  have hCRegular : P.RegularAt C := by
    apply f1024Tower_regularAt_of_artinSchreier_regular P C
    rw [hCEquation]
    exact regularAdd hHRegular (regularMul hgRegular hLRegular)
  have hvFirst : v = u ^ 32 + u ^ 31 * v ^ 32 := by
    calc
      v = v + 0 := (add_zero v).symm
      _ = v + (u ^ 31 * v ^ 32 + u ^ 31 * v ^ 32) := by
        rw [CharTwo.add_self_eq_zero]
      _ = (u ^ 31 * v ^ 32 + v) + u ^ 31 * v ^ 32 := by ring
      _ = u ^ 32 + u ^ 31 * v ^ 32 := by rw [huv]
  have hvPower : v ^ 32 = u ^ 1024 + u ^ 992 * v ^ 1024 := by
    calc
      v ^ 32 = (u ^ 32 + u ^ 31 * v ^ 32) ^ 32 := by rw [← hvFirst]
      _ = (u ^ 32) ^ 32 + (u ^ 31 * v ^ 32) ^ 32 := by
        rw [show 32 = 2 ^ 5 by norm_num, add_pow_char_pow]
      _ = u ^ 1024 + u ^ 992 * v ^ 1024 := by ring
  have hvExpansion :
      v = u ^ 32 * (1 + u ^ 1023 + u ^ 991 * v ^ 1024) := by
    calc
      v = u ^ 32 + u ^ 31 * v ^ 32 := hvFirst
      _ = u ^ 32 + u ^ 31 * (u ^ 1024 + u ^ 992 * v ^ 1024) := by
        rw [hvPower]
      _ = u ^ 32 * (1 + u ^ 1023 + u ^ 991 * v ^ 1024) := by ring
  let A : F := z * v
  let B : F := x * v
  let R : F := A + g * u⁻¹
  let S : F := R * u⁻¹ ^ 32
  have huInvPowMulPow (n : ℕ) : u⁻¹ ^ n * u ^ n = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hu, one_pow]
  have huInvPowThirtyThreeMulThirtyTwo :
      u⁻¹ ^ 33 * u ^ 32 = u⁻¹ := by
    calc
      u⁻¹ ^ 33 * u ^ 32 =
          u⁻¹ * (u⁻¹ ^ 32 * u ^ 32) := by
            rw [show 33 = 1 + 32 by norm_num, pow_add, pow_one]
            ring
      _ = u⁻¹ := by rw [huInvPowMulPow, mul_one]
  have huInvMulPowSucc (n : ℕ) : u⁻¹ * u ^ (n + 1) = u ^ n := by
    rw [pow_succ', ← mul_assoc, inv_mul_cancel₀ hu, one_mul]
  have hvScaled :
      u⁻¹ ^ 33 * v = u⁻¹ + u ^ 1022 + u ^ 990 * v ^ 1024 := by
    calc
      u⁻¹ ^ 33 * v =
          u⁻¹ ^ 33 *
            (u ^ 32 * (1 + u ^ 1023 + u ^ 991 * v ^ 1024)) := by
              exact congrArg (fun w : F => u⁻¹ ^ 33 * w) hvExpansion
      _ = u⁻¹ * (1 + u ^ 1023 + u ^ 991 * v ^ 1024) := by
        rw [← mul_assoc, huInvPowThirtyThreeMulThirtyTwo]
      _ = u⁻¹ + u ^ 1022 + u ^ 990 * v ^ 1024 := by
        rw [show 1023 = 1022 + 1 by norm_num,
          show 991 = 990 + 1 by norm_num,
          mul_add, mul_add, mul_one, huInvMulPowSucc,
          ← mul_assoc, huInvMulPowSucc]
  have hRForm :
      R = C * v + g * u ^ 1022 + g * u ^ 990 * v ^ 1024 := by
    have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
    dsimp only [R, A, C]
    calc
      z * v + g * u⁻¹ =
          (z * v + g * (u⁻¹ ^ 33 * v)) +
            g * u ^ 1022 + g * u ^ 990 * v ^ 1024 := by
              rw [hvScaled]
              ring_nf
              simp only [htwo, mul_zero, add_zero]
      _ = (z + g * u⁻¹ ^ 33) * v +
          g * u ^ 1022 + g * u ^ 990 * v ^ 1024 := by ring
  have huPowMulInvPowThirtyTwo (n : ℕ) :
      u ^ (n + 32) * u⁻¹ ^ 32 = u ^ n := by
    calc
      u ^ (n + 32) * u⁻¹ ^ 32 =
          u ^ n * (u ^ 32 * u⁻¹ ^ 32) := by
            rw [pow_add]
            ring
      _ = u ^ n := by
        rw [← mul_pow, mul_inv_cancel₀ hu, one_pow, mul_one]
  have hSForm :
      S = C * (v / u ^ 32) + g * u ^ 990 +
        g * u ^ 958 * v ^ 1024 := by
    have hu1022 : u ^ 1022 * u⁻¹ ^ 32 = u ^ 990 := by
      exact huPowMulInvPowThirtyTwo 990
    have hu990 : u ^ 990 * u⁻¹ ^ 32 = u ^ 958 := by
      exact huPowMulInvPowThirtyTwo 958
    dsimp only [S]
    rw [hRForm]
    rw [div_eq_mul_inv, ← inv_pow]
    calc
      (C * v + g * u ^ 1022 + g * u ^ 990 * v ^ 1024) * u⁻¹ ^ 32 =
          C * (v * u⁻¹ ^ 32) + g * (u ^ 1022 * u⁻¹ ^ 32) +
            g * (u ^ 990 * u⁻¹ ^ 32) * v ^ 1024 := by ring
      _ = C * (v * u⁻¹ ^ 32) + g * u ^ 990 +
          g * u ^ 958 * v ^ 1024 := by rw [hu1022, hu990]
  have hRRegular : P.RegularAt R := by
    rw [hRForm]
    exact regularAdd
      (regularAdd (regularMul hCRegular hvRegular)
        (regularMul hgRegular (regularPow huRegular 1022)))
      (regularMul (regularMul hgRegular (regularPow huRegular 990))
        (regularPow hvRegular 1024))
  have hSRegular : P.RegularAt S := by
    rw [hSForm]
    exact regularAdd
      (regularAdd (regularMul hCRegular hvDivRegular)
        (regularMul hgRegular (regularPow huRegular 990)))
      (regularMul (regularMul hgRegular (regularPow huRegular 958))
        (regularPow hvRegular 1024))
  let RA : F := A ^ 33 + g ^ 33 * u⁻¹ ^ 33
  have hAFromR : A = R + g * u⁻¹ := by
    dsimp only [R]
    calc
      A = A + 0 := (add_zero A).symm
      _ = A + (g * u⁻¹ + g * u⁻¹) := by
        rw [CharTwo.add_self_eq_zero]
      _ = (A + g * u⁻¹) + g * u⁻¹ := by ring
  have hApowThirtyTwo :
      A ^ 32 = R ^ 32 + (g * u⁻¹) ^ 32 := by
    rw [hAFromR]
    simpa only [show (2 ^ 5 : ℕ) = 32 by norm_num] using
      (add_pow_char_pow (R := F) (x := R) (y := g * u⁻¹) 2 5)
  have hAThirtyThree :
      A ^ 33 = R ^ 33 + g * R ^ 32 * u⁻¹ +
        g ^ 32 * R * u⁻¹ ^ 32 + g ^ 33 * u⁻¹ ^ 33 := by
    calc
      A ^ 33 = A ^ 32 * A := by
        rw [show 33 = 32 + 1 by norm_num, pow_add, pow_one]
      _ = (R ^ 32 + (g * u⁻¹) ^ 32) * (R + g * u⁻¹) := by
        rw [hApowThirtyTwo, hAFromR]
      _ = R ^ 33 + g * R ^ 32 * u⁻¹ +
          g ^ 32 * R * u⁻¹ ^ 32 + g ^ 33 * u⁻¹ ^ 33 := by
        rw [mul_pow]
        ring
  have hRAExpanded :
      RA = R ^ 33 + g * R ^ 32 * u⁻¹ +
        g ^ 32 * R * u⁻¹ ^ 32 := by
    have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
    dsimp only [RA]
    rw [hAThirtyThree]
    ring_nf
    simp only [htwo, mul_zero, add_zero]
  have huPowerRatio : u ^ 1023 * (u⁻¹ ^ 32) ^ 32 = u⁻¹ := by
    field_simp [hu]
  have hgS : g ^ 32 * S = g ^ 32 * R * u⁻¹ ^ 32 := by
    dsimp only [S]
    ring
  have hlast : g * u ^ 1023 * S ^ 32 = g * R ^ 32 * u⁻¹ := by
    dsimp only [S]
    rw [mul_pow]
    calc
      g * u ^ 1023 * (R ^ 32 * (u⁻¹ ^ 32) ^ 32) =
          g * R ^ 32 * (u ^ 1023 * (u⁻¹ ^ 32) ^ 32) := by ring
      _ = g * R ^ 32 * u⁻¹ := by rw [huPowerRatio]
  have hRAForm :
      RA = R ^ 33 + g ^ 32 * S + g * u ^ 1023 * S ^ 32 := by
    rw [hRAExpanded, hgS, hlast]
    ring
  have hRARegular : P.RegularAt RA := by
    rw [hRAForm]
    exact regularAdd
      (regularAdd (regularPow hRRegular 33)
        (regularMul (regularPow hgRegular 32) hSRegular))
      (regularMul (regularMul hgRegular (regularPow huRegular 1023))
        (regularPow hSRegular 32))
  let EB : F := B⁻¹ ^ 33 + g⁻¹
  have hB : B ≠ 0 := by
    exact mul_ne_zero hx hv
  have hEBForm :
      EB = H * v ^ 33 * (g * B ^ 33)⁻¹ := by
    dsimp only [EB, H, B]
    field_simp [hg, hx, hv] <;> ring_nf
  have hDenominatorInvRegular : P.RegularAt (g * B ^ 33)⁻¹ := by
    have hBOrder : P.order B = 0 := by
      dsimp only [B]
      rw [P.order_mul hx hv, hxOrder]
      ring
    have hdenominatorOrder : P.order (g * B ^ 33) = 0 := by
      rw [P.order_mul hg (pow_ne_zero 33 hB), hgOrder,
        f1024Tower_globalPlace_order_pow P, hBOrder]
      norm_num
    exact (P.regularAt_iff_order_nonnegative
      (inv_ne_zero (mul_ne_zero hg (pow_ne_zero 33 hB)))).mpr (by
        rw [P.order_inv, hdenominatorOrder]
        norm_num)
  have hEBRegular : P.RegularAt EB := by
    rw [hEBForm]
    exact regularMul
      (regularMul hHRegular (regularPow hvRegular 33))
      hDenominatorInvRegular
  have huvRatio : v ^ 33 * u⁻¹ ^ 33 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 33 hv) (pow_ne_zero 33 (inv_ne_zero hu))
  have huvRatioOrder : P.order (v ^ 33 * u⁻¹ ^ 33) =
      1023 * P.order u := by
    rw [P.order_mul (pow_ne_zero 33 hv)
      (pow_ne_zero 33 (inv_ne_zero hu)),
      f1024Tower_globalPlace_order_pow P,
      f1024Tower_globalPlace_order_pow P, P.order_inv, hvOrder]
    ring
  have huvRatioRegular : P.RegularAt (v ^ 33 * u⁻¹ ^ 33) :=
    (P.regularAt_iff_order_nonnegative huvRatio).mpr (by
      rw [huvRatioOrder]
      exact mul_nonneg (by norm_num) huOrder.le)
  have huInvEBForm :
      u⁻¹ ^ 33 * EB =
        H * (v ^ 33 * u⁻¹ ^ 33) * (g * B ^ 33)⁻¹ := by
    rw [hEBForm]
    ring
  have huInvEBRegular : P.RegularAt (u⁻¹ ^ 33 * EB) := by
    rw [huInvEBForm]
    exact regularMul (regularMul hHRegular huvRatioRegular)
      hDenominatorInvRegular
  have hyAB : y = A / B := by
    dsimp only [A, B, z]
    field_simp [hx, hv]
  have htarget :
      y ^ 33 + g * u⁻¹ ^ 33 =
        RA * EB + RA * g⁻¹ + g ^ 33 * (u⁻¹ ^ 33 * EB) := by
    have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
    have hgThirtyThree : g ^ 33 = g ^ 2 := by
      rw [show 33 = 32 + 1 by norm_num, pow_add, pow_one, hgFrobenius]
      ring
    have hthree : (3 : F) = 1 := by
      calc
        (3 : F) = 2 + 1 := by norm_num
        _ = 0 + 1 := by rw [htwo]
        _ = 1 := zero_add 1
    rw [hyAB]
    dsimp only [RA, EB, A, B]
    rw [hgThirtyThree]
    field_simp [hg, hx, hv]
    ring_nf
    rw [hthree]
    simp only [htwo, mul_zero, add_zero, mul_one]
  rw [CharTwo.sub_eq_add]
  rw [htarget]
  exact regularAdd
    (regularAdd (regularMul hRARegular hEBRegular)
      (regularMul hRARegular hgInvRegular))
    (regularMul (regularPow hgRegular 33) huInvEBRegular)

section TowerLevelCoordinateDivisors

open QEC.Coding.AlgebraicGeometry

@[reducible] noncomputable def f1024TowerLevelCoordinateDivisorAlgebra
    (height : ℕ) : Algebra F1024 (F1024TowerLevel height) :=
  @QEC.Coding.AlgebraicGeometry.AffinePlace.constantAlgebra
    F1024 (F1024TowerLevel height) _ _
      (inferInstance : Algebra F1024[X] (F1024TowerLevel height))

@[reducible] noncomputable local instance
    f1024TowerLevelCoordinateDivisorAlgebraInst (height : ℕ) :
    Algebra F1024 (F1024TowerLevel height) :=
  f1024TowerLevelCoordinateDivisorAlgebra height

@[reducible] noncomputable def
    f1024TowerLevelCoordinateDivisorRationalScalarTower (height : ℕ) :
    IsScalarTower F1024 F1024TowerF1 (F1024TowerLevel height) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap
        (_root_.FunctionField.ringOfIntegers F1024
          (F1024TowerLevel height))
        (F1024TowerLevel height)
        (algebraMap F1024[X]
          (_root_.FunctionField.ringOfIntegers F1024
            (F1024TowerLevel height)) (C c)) =
      algebraMap F1024TowerF1 (F1024TowerLevel height)
        (algebraMap F1024 F1024TowerF1 c)
    calc
      algebraMap
          (_root_.FunctionField.ringOfIntegers F1024
            (F1024TowerLevel height))
          (F1024TowerLevel height)
          (algebraMap F1024[X]
            (_root_.FunctionField.ringOfIntegers F1024
              (F1024TowerLevel height)) (C c)) =
          algebraMap F1024[X] (F1024TowerLevel height) (C c) :=
        (IsScalarTower.algebraMap_apply F1024[X]
          (_root_.FunctionField.ringOfIntegers F1024
            (F1024TowerLevel height))
          (F1024TowerLevel height) (C c)).symm
      _ = algebraMap F1024TowerF1 (F1024TowerLevel height)
          (algebraMap F1024 F1024TowerF1 c) := by
        simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
          (IsScalarTower.algebraMap_apply F1024[X] F1024TowerF1
            (F1024TowerLevel height) (C c))

noncomputable local instance
    f1024TowerLevelCoordinateDivisorRationalScalarTowerInst (height : ℕ) :
    IsScalarTower F1024 F1024TowerF1 (F1024TowerLevel height) :=
  f1024TowerLevelCoordinateDivisorRationalScalarTower height

private theorem f1024TowerLevelCoordinateDivisorAlgebra_eq_stage
    (height : ℕ) :
    f1024TowerLevelCoordinateDivisorAlgebra height =
      (f1024TowerStage height).constantAlgebraInst := by
  apply Algebra.algebra_ext
  intro c
  have hlocal :
      @algebraMap F1024 (F1024TowerLevel height) _ _
          (f1024TowerLevelCoordinateDivisorAlgebra height) c =
        algebraMap F1024TowerF1 (F1024TowerLevel height)
          (algebraMap F1024 F1024TowerF1 c) := by
    letI : Algebra F1024 (F1024TowerLevel height) :=
      f1024TowerLevelCoordinateDivisorAlgebra height
    letI : IsScalarTower F1024 F1024TowerF1 (F1024TowerLevel height) :=
      f1024TowerLevelCoordinateDivisorRationalScalarTower height
    exact IsScalarTower.algebraMap_apply F1024 F1024TowerF1
      (F1024TowerLevel height) c
  have hstage :
      @algebraMap F1024 (F1024TowerLevel height) _ _
          (f1024TowerStage height).constantAlgebraInst c =
        algebraMap F1024TowerF1 (F1024TowerLevel height)
          (algebraMap F1024 F1024TowerF1 c) := by
    letI : Algebra F1024 (F1024TowerLevel height) :=
      (f1024TowerStage height).constantAlgebraInst
    letI : IsScalarTower F1024 F1024TowerF1 (F1024TowerLevel height) :=
      (f1024TowerStage height).constantRationalTowerInst
    exact IsScalarTower.algebraMap_apply F1024 F1024TowerF1
      (F1024TowerLevel height) c
  exact hlocal.trans hstage.symm

noncomputable instance
    f1024TowerLevelCoordinateDivisorIsFullConstantField (height : ℕ) :
    QEC.Coding.AlgebraicGeometry.IsFullConstantField F1024
      (F1024TowerLevel height) := by
  change @QEC.Coding.AlgebraicGeometry.IsFullConstantField F1024
    (F1024TowerLevel height) _ _
      (f1024TowerLevelCoordinateDivisorAlgebra height)
  rw [f1024TowerLevelCoordinateDivisorAlgebra_eq_stage height]
  exact f1024TowerLevel_isFullConstantField height

noncomputable local instance
    f1024TowerLevelCoordinateDivisorStepConstantScalarTower (height : ℕ) :
    IsScalarTower F1024 (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable def f1024TowerLevelHistoricalX
    (height i : ℕ) : F1024TowerLevel height :=
  f1024TowerStageHistoricalX (f1024TowerStage height) i

private theorem f1024TowerLevelHistoricalX_ne_zero
    (height i : ℕ) : f1024TowerLevelHistoricalX height i ≠ 0 :=
  f1024TowerStageHistoricalX_ne_zero (f1024TowerStage height) i

private theorem f1024TowerLevelHistoricalX_current (height : ℕ) :
    f1024TowerLevelHistoricalX height height = f1024TowerLevelX height :=
  f1024TowerStageHistoricalX_current (f1024TowerStage height)

private theorem f1024TowerLevelHistoricalX_succ_map
    (height i : ℕ) (hi : i ≤ height) :
    algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
        (f1024TowerLevelHistoricalX height i) =
      f1024TowerLevelHistoricalX (height + 1) i := by
  change algebraMap (f1024TowerStage height).carrier
      (F1024TowerStageStep (f1024TowerStage height))
        ((f1024TowerStage height).inverseCoordinate i)⁻¹ =
    (if i ≤ height then
      algebraMap (f1024TowerStage height).carrier
        (F1024TowerStageStep (f1024TowerStage height))
          ((f1024TowerStage height).inverseCoordinate i)
    else f1024TowerStageStepRoot (f1024TowerStage height))⁻¹
  rw [if_pos hi, map_inv₀]

private theorem f1024TowerLevelHistoricalX_recurrence
    (height i : ℕ) (hi : i < height) :
    f1024TowerLevelHistoricalX height i ^ 31 *
          f1024TowerLevelHistoricalX height (i + 1) ^ 32 +
        f1024TowerLevelHistoricalX height (i + 1) =
      f1024TowerLevelHistoricalX height i ^ 32 :=
  f1024TowerStageHistoricalX_recurrence (f1024TowerStage height) i hi

private theorem f1024TowerLevelHistoricalX_order_next_of_pole
    (height i : ℕ) (hi : i < height)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))
    (hpole : P.order (f1024TowerLevelHistoricalX height i) < 0) :
    P.order (f1024TowerLevelHistoricalX height i) =
        32 * P.order (f1024TowerLevelHistoricalX height (i + 1)) ∧
      P.order (f1024TowerLevelHistoricalX height (i + 1)) < 0 := by
  obtain hPole | hZero | hCancel :=
    f1024Tower_recurrence_order_cases (F1024TowerLevel height) P
      (f1024TowerLevelHistoricalX_ne_zero height i)
      (f1024TowerLevelHistoricalX_ne_zero height (i + 1))
      (f1024TowerLevelHistoricalX_recurrence height i hi)
  · exact ⟨hPole.2, by omega⟩
  · omega
  · omega

private theorem f1024TowerLevelHistoricalX_order_iterate_of_pole
    (height i d : ℕ) (hid : i + d ≤ height)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))
    (hpole : P.order (f1024TowerLevelHistoricalX height i) < 0) :
    P.order (f1024TowerLevelHistoricalX height i) =
        (32 : ℤ) ^ d *
          P.order (f1024TowerLevelHistoricalX height (i + d)) ∧
      P.order (f1024TowerLevelHistoricalX height (i + d)) < 0 := by
  induction d generalizing i with
  | zero =>
      constructor
      · simp
      · simpa
  | succ d ih =>
      have hi : i < height := by omega
      obtain ⟨hstep, hnext⟩ :=
        f1024TowerLevelHistoricalX_order_next_of_pole height i hi P hpole
      obtain ⟨hrest, hfinal⟩ := ih (i + 1) (by omega) hnext
      constructor
      · calc
          P.order (f1024TowerLevelHistoricalX height i) =
              32 * P.order
                (f1024TowerLevelHistoricalX height (i + 1)) := hstep
          _ = 32 * ((32 : ℤ) ^ d *
                P.order
                  (f1024TowerLevelHistoricalX height ((i + 1) + d))) := by
                rw [hrest]
          _ = (32 : ℤ) ^ (d + 1) *
                P.order
                  (f1024TowerLevelHistoricalX height (i + (d + 1))) := by
                rw [show i + (d + 1) = (i + 1) + d by omega, pow_succ]
                ring
      · simpa only [show i + (d + 1) = (i + 1) + d by omega] using hfinal

private theorem f1024TowerLevelHistoricalX_order_prev_of_positive
    (height i : ℕ) (hi : i < height)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))
    (hnext : 0 <
      P.order (f1024TowerLevelHistoricalX height (i + 1))) :
    0 < P.order (f1024TowerLevelHistoricalX height i) ∧
      P.order (f1024TowerLevelHistoricalX height (i + 1)) =
        32 * P.order (f1024TowerLevelHistoricalX height i) := by
  obtain hPole | hZero | hCancel :=
    f1024Tower_recurrence_order_cases (F1024TowerLevel height) P
      (f1024TowerLevelHistoricalX_ne_zero height i)
      (f1024TowerLevelHistoricalX_ne_zero height (i + 1))
      (f1024TowerLevelHistoricalX_recurrence height i hi)
  · omega
  · exact hZero
  · omega

private theorem f1024TowerLevelHistoricalX_order_iterate_of_positive
    (height j d : ℕ) (hd : d ≤ j) (hj : j ≤ height)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))
    (hpositive : 0 <
      P.order (f1024TowerLevelHistoricalX height j)) :
    P.order (f1024TowerLevelHistoricalX height j) =
        (32 : ℤ) ^ d *
          P.order (f1024TowerLevelHistoricalX height (j - d)) ∧
      0 < P.order (f1024TowerLevelHistoricalX height (j - d)) := by
  induction d generalizing j with
  | zero =>
      constructor
      · simp
      · simpa
  | succ d ih =>
      have hjpos : 0 < j := by omega
      have hjpred : j - 1 < height := by omega
      have hnext : 0 < P.order
          (f1024TowerLevelHistoricalX height ((j - 1) + 1)) := by
        simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt hjpos))] using hpositive
      obtain ⟨hpredPositive, hstep⟩ :=
        f1024TowerLevelHistoricalX_order_prev_of_positive
          height (j - 1) hjpred P hnext
      obtain ⟨hrest, hfinal⟩ :=
        ih (j - 1) (by omega) (by omega) hpredPositive
      constructor
      · calc
          P.order (f1024TowerLevelHistoricalX height j) =
              32 * P.order
                (f1024TowerLevelHistoricalX height (j - 1)) := by
                simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
                  (Nat.ne_of_gt hjpos))] using hstep
          _ = 32 * ((32 : ℤ) ^ d * P.order
                (f1024TowerLevelHistoricalX height ((j - 1) - d))) := by
                  rw [hrest]
          _ = (32 : ℤ) ^ (d + 1) * P.order
                (f1024TowerLevelHistoricalX height (j - (d + 1))) := by
                  rw [show (j - 1) - d = j - (d + 1) by omega, pow_succ]
                  ring
      · simpa only [show (j - 1) - d = j - (d + 1) by omega] using hfinal

private theorem f1024TowerLevelHistoricalX_switch_matched_orders
    (height j d : ℕ) (hd : d ≤ j)
    (hbound : j + 1 + d ≤ height)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))
    (hpositive : 0 <
      P.order (f1024TowerLevelHistoricalX height j))
    (hpole :
      P.order (f1024TowerLevelHistoricalX height (j + 1)) < 0) :
    P.order (f1024TowerLevelHistoricalX height (j + 1 + d)) =
      -P.order (f1024TowerLevelHistoricalX height (j - d)) := by
  have hj : j < height := by omega
  have hswitch :
      P.order (f1024TowerLevelHistoricalX height (j + 1)) =
        -P.order (f1024TowerLevelHistoricalX height j) := by
    obtain hPole | hZero | hCancel :=
      f1024Tower_recurrence_order_cases (F1024TowerLevel height) P
        (f1024TowerLevelHistoricalX_ne_zero height j)
        (f1024TowerLevelHistoricalX_ne_zero height (j + 1))
        (f1024TowerLevelHistoricalX_recurrence height j hj)
    · omega
    · omega
    · exact hCancel.2
  obtain ⟨hleft, _⟩ :=
    f1024TowerLevelHistoricalX_order_iterate_of_positive
      height j d hd (by omega) P hpositive
  obtain ⟨hright, _⟩ :=
    f1024TowerLevelHistoricalX_order_iterate_of_pole
      height (j + 1) d hbound P hpole
  have hpowNe : (32 : ℤ) ^ d ≠ 0 := pow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ hpowNe
  calc
    (32 : ℤ) ^ d *
          P.order (f1024TowerLevelHistoricalX height (j + 1 + d)) =
        P.order (f1024TowerLevelHistoricalX height (j + 1)) := by
          rw [hright]
    _ = -P.order (f1024TowerLevelHistoricalX height j) := hswitch
    _ = (32 : ℤ) ^ d *
        -P.order (f1024TowerLevelHistoricalX height (j - d)) := by
          rw [hleft]
          ring

/-- The exact indexed form of Garcia--Stichtenoth Lemma 2.7 in a realized
tower level.  A zero-to-pole switch at `j` propagates a translated
thirty-third-power relation symmetrically for `d` recurrences on both sides. -/
private theorem f1024TowerLevelHistoricalX_exists_regular_translation
    (height j d : ℕ) (hd : d ≤ j)
    (hbound : j + 1 + d ≤ height)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))
    (hpositive : 0 <
      P.order (f1024TowerLevelHistoricalX height j))
    (hpole :
      P.order (f1024TowerLevelHistoricalX height (j + 1)) < 0) :
    ∃ gamma : F1024, gamma ≠ 0 ∧ gamma ^ 32 = gamma ∧
      P.RegularAt
        (f1024TowerLevelHistoricalX height (j + 1 + d) ^ 33 -
          algebraMap F1024 (F1024TowerLevel height) gamma *
            (f1024TowerLevelHistoricalX height (j - d))⁻¹ ^ 33) := by
  induction d with
  | zero =>
      have hj : j < height := by omega
      have hswitch :=
        f1024TowerLevelHistoricalX_switch_matched_orders
          height j 0 (by omega) (by simpa using hbound) P hpositive hpole
      simpa only [Nat.add_zero, Nat.sub_zero] using
        f1024Tower_exists_regular_thirtyThree_translation P
          (f1024TowerLevelHistoricalX height j)
          (f1024TowerLevelHistoricalX height (j + 1))
          (f1024TowerLevelHistoricalX_ne_zero height j)
          (f1024TowerLevelHistoricalX_ne_zero height (j + 1))
          (f1024TowerLevelHistoricalX_recurrence height j hj)
          hpositive (by simpa using hswitch)
  | succ d ih =>
      have hd' : d ≤ j := by omega
      have hbound' : j + 1 + d ≤ height := by omega
      obtain ⟨gamma, hgamma, hgammaFrobenius, hprevious⟩ :=
        ih hd' hbound'
      have hleftIndex : (j - (d + 1)) + 1 = j - d := by omega
      have hrightIndex : (j + 1 + d) + 1 = j + 1 + (d + 1) := by omega
      have hleftPositive :=
        (f1024TowerLevelHistoricalX_order_iterate_of_positive
          height j d hd' (by omega) P hpositive).2
      obtain ⟨huOrder, hvOrder⟩ :=
        f1024TowerLevelHistoricalX_order_prev_of_positive
          height (j - (d + 1)) (by omega) P (by
            simpa only [hleftIndex] using hleftPositive)
      have hvOrder' :
          P.order (f1024TowerLevelHistoricalX height (j - d)) =
            32 * P.order
              (f1024TowerLevelHistoricalX height (j - (d + 1))) := by
        simpa only [hleftIndex] using hvOrder
      have hxOrder :=
        f1024TowerLevelHistoricalX_switch_matched_orders
          height j d hd' hbound' P hpositive hpole
      have huv := f1024TowerLevelHistoricalX_recurrence
        height (j - (d + 1)) (by omega)
      rw [hleftIndex] at huv
      have hxy := f1024TowerLevelHistoricalX_recurrence
        height (j + 1 + d) (by omega)
      rw [hrightIndex] at hxy
      refine ⟨gamma, hgamma, hgammaFrobenius, ?_⟩
      exact f1024Tower_regular_thirtyThree_translation_step P
        (f1024TowerLevelHistoricalX height (j - (d + 1)))
        (f1024TowerLevelHistoricalX height (j - d))
        (f1024TowerLevelHistoricalX height (j + 1 + d))
        (f1024TowerLevelHistoricalX height (j + 1 + (d + 1)))
        (f1024TowerLevelHistoricalX_ne_zero height (j - (d + 1)))
        (f1024TowerLevelHistoricalX_ne_zero height (j - d))
        (f1024TowerLevelHistoricalX_ne_zero height (j + 1 + d))
        (f1024TowerLevelHistoricalX_ne_zero height (j + 1 + (d + 1)))
        huv hxy huOrder hvOrder' hxOrder gamma hgamma hgammaFrobenius hprevious

/-- Garcia--Stichtenoth Proposition 2.5 for one realized old switch stratum.
The indexed Lemma 2.7 translation and Lemma 2.6 remove the pole from the
actual successor Artin--Schreier equation, so every upper place has
restriction multiplier one. -/
private theorem f1024TowerLevel_step_order_eq_of_old_switch
    (height j d : ℕ) (hd : d ≤ j)
    (hcurrent : j + 1 + d = height) (hprevious : 1 ≤ j - d)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1)))
    (hpositive : 0 <
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Q).order
          (f1024TowerLevelHistoricalX height j))
    (hpole :
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Q).order
          (f1024TowerLevelHistoricalX height (j + 1)) < 0) :
    ∀ u : F1024TowerLevel height, u ≠ 0 →
      Q.order
          (algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)) u) =
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q).order u := by
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) :=
    f1024Tower_restrictedGlobalPlace
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  obtain ⟨gamma, hgamma, hgammaFrobenius, htranslation⟩ :=
    f1024TowerLevelHistoricalX_exists_regular_translation
      height j d hd (by omega) P hpositive hpole
  have hcurrentHistorical :
      f1024TowerLevelHistoricalX height (j + 1 + d) =
        f1024TowerLevelX height := by
    rw [hcurrent, f1024TowerLevelHistoricalX_current]
  let k : ℕ := j - d
  let a : F1024TowerLevel height :=
    f1024TowerLevelHistoricalX height (k - 1)
  let b : F1024TowerLevel height :=
    f1024TowerLevelHistoricalX height k
  let t : F1024TowerLevel height := a⁻¹ ^ 33
  let c : F1024TowerLevel height :=
    algebraMap F1024 (F1024TowerLevel height) gamma
  have hk : 1 ≤ k := by simpa only [k] using hprevious
  have hkIndex : (k - 1) + 1 = k := Nat.sub_add_cancel hk
  have hbPositive : 0 < P.order b := by
    dsimp only [b, k]
    exact (f1024TowerLevelHistoricalX_order_iterate_of_positive
      height j d hd (by omega) P hpositive).2
  obtain ⟨haPositive, hbOrderRaw⟩ :=
    f1024TowerLevelHistoricalX_order_prev_of_positive
      height (k - 1) (by omega) P (by
        simpa only [hkIndex, b] using hbPositive)
  have hbOrder : P.order b = 32 * P.order a := by
    simpa only [hkIndex, a, b] using hbOrderRaw
  have habRecurrence : a ^ 31 * b ^ 32 + b = a ^ 32 := by
    have hrec := f1024TowerLevelHistoricalX_recurrence
      height (k - 1) (by omega)
    simpa only [hkIndex, a, b] using hrec
  have hlemmaSix :=
    f1024Tower_inverseThirtyThree_sub_artinSchreier_regular
      P a b
        (f1024TowerLevelHistoricalX_ne_zero height (k - 1))
        (f1024TowerLevelHistoricalX_ne_zero height k)
        habRecurrence haPositive hbOrder
  have hLRegular : P.RegularAt (b⁻¹ ^ 33 + (t ^ 32 + t)) := by
    simpa only [t, CharTwo.sub_eq_add] using hlemmaSix
  have hHRegular : P.RegularAt
      (f1024TowerLevelX height ^ 33 + c * b⁻¹ ^ 33) := by
    rw [hcurrentHistorical, CharTwo.sub_eq_add] at htranslation
    simpa only [c, b, k] using htranslation
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact (map_ne_zero_iff (algebraMap F1024 (F1024TowerLevel height))
      (algebraMap F1024 (F1024TowerLevel height)).injective).mpr hgamma
  have hcFrobenius : c ^ 32 = c := by
    dsimp only [c]
    rw [← map_pow, hgammaFrobenius]
  have hcRegular : P.RegularAt c :=
    (P.regularAt_iff_order_nonnegative hc).mpr (by
      rw [QEC.Coding.AlgebraicGeometry.GlobalPlace.order_algebraMap
        P gamma hgamma])
  have hcombined : P.RegularAt
      (f1024TowerLevelX height ^ 33 + c * (t ^ 32 + t)) := by
    have hsum : P.RegularAt
        ((f1024TowerLevelX height ^ 33 + c * b⁻¹ ^ 33) +
          c * (b⁻¹ ^ 33 + (t ^ 32 + t))) := by
      apply (P.regularAt_iff_mem_valuationRing _).mpr
      exact P.valuationRing.toSubring.add_mem
        ((P.regularAt_iff_mem_valuationRing _).mp hHRegular)
        (P.valuationRing.toSubring.mul_mem
          ((P.regularAt_iff_mem_valuationRing _).mp hcRegular)
          ((P.regularAt_iff_mem_valuationRing _).mp hLRegular))
    convert hsum using 1
    have htwo : (2 : F1024TowerLevel height) = 0 := CharTwo.two_eq_zero
    ring_nf
    simp only [htwo, mul_zero, add_zero]
  let Qstage :
      @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
        (F1024TowerLevel (height + 1)) _ _ _
          (f1024TowerStage (height + 1)).constantAlgebraInst :=
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.mk F1024
      (F1024TowerLevel (height + 1)) _ _ _
        (f1024TowerStage (height + 1)).constantAlgebraInst
        (@QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024
          (F1024TowerLevel (height + 1)) _ _ _
            (f1024TowerLevelCoordinateDivisorAlgebra (height + 1)) Q)
        (@QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized F1024
          (F1024TowerLevel (height + 1)) _ _ _
            (f1024TowerLevelCoordinateDivisorAlgebra (height + 1)) Q)
  letI : Algebra F1024 (F1024TowerLevel height) :=
    (f1024TowerStage height).constantAlgebraInst
  letI : Algebra F1024 (F1024TowerLevel (height + 1)) :=
    (f1024TowerStage (height + 1)).constantAlgebraInst
  letI : IsScalarTower F1024 (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) :=
    f1024TowerLevelStepConstantScalarTower height
  have hcombinedStage :
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Qstage).RegularAt
          (f1024TowerLevelX height ^ 33 + c * (t ^ 32 + t)) := by
    unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.RegularAt at hcombined ⊢
    exact hcombined
  have hresult := f1024TowerLevel_step_order_eq_of_translated_rhs_regular
    height Qstage c t hcFrobenius hcombinedStage
  intro u hu
  have h := hresult u hu
  unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order at h ⊢
  exact h

private theorem f1024TowerLevelHistoricalX_polarDivisor_degree
    (height i : ℕ) (hi : i ≤ height) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel height))
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F1024TowerLevel height)
          (f1024TowerLevelHistoricalX height i)) =
      (32 ^ height : ℤ) := by
  have hzero :
      Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel height))
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
            (k := F1024) (F := F1024TowerLevel height)
            (f1024TowerLevelHistoricalX height 0)) =
        (32 ^ height : ℤ) := by
    rw [f1024TowerLevelHistoricalX,
      f1024TowerStageHistoricalX_zero]
    have hchart :=
      QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_chartVariable_degree_eq_finrank
        (k := F1024) (F := F1024TowerLevel height)
    rw [f1024TowerLevel_finrank_over_F1 height] at hchart
    exact hchart
  induction i with
  | zero => exact hzero
  | succ i ih =>
      have hi' : i < height := Nat.lt_of_succ_le hi
      have hdegree := f1024Tower_polarDivisor_degree_eq_of_recurrence
        (F1024TowerLevel height)
        (f1024TowerLevelHistoricalX_ne_zero height i)
        (f1024TowerLevelHistoricalX_ne_zero height (i + 1))
        (f1024TowerLevelHistoricalX_recurrence height i hi')
      exact hdegree.symm.trans (ih (Nat.le_of_lt hi'))

private theorem f1024TowerLevel_residueDegree_pos
    (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) :
    0 < QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
      (k := F1024) (F := F1024TowerLevel height) P := by
  letI : Algebra F1024
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueField P) :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.residueAlgebra P
  letI : FiniteDimensional F1024
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueField P) :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.residueField_finiteDimensional P
  rw [QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree_eq_finrank P]
  exact Module.finrank_pos

private theorem f1024TowerLevel_divisorDegree_mono
    (height : ℕ)
    {D E : Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))} (hDE : D ≤ E) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel height)) D ≤
      Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel height)) E := by
  have hnonnegative : Divisor.Nonnegative (E - D) := by
    intro P
    exact sub_nonneg.mpr (hDE P)
  have hdegreeNonnegative : 0 ≤
      Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel height)) (E - D) :=
    Divisor.degree_nonnegative _ _ hnonnegative
  have heq : D + (E - D) = E := by
    ext P
    simp only [Finsupp.add_apply, Finsupp.sub_apply]
    omega
  rw [← heq, Divisor.degree_add]
  exact le_add_of_nonneg_right hdegreeNonnegative

private theorem f1024TowerLevelHistoricalX_zero_order_eq_one_of_positive
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel 0))
    (hpositive : 0 < P.order (f1024TowerLevelHistoricalX 0 0)) :
    P.order (f1024TowerLevelHistoricalX 0 0) = 1 := by
  classical
  let x : F1024TowerLevel 0 := f1024TowerLevelHistoricalX 0 0
  change 0 < P.order x at hpositive
  change P.order x = 1
  let D : Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel 0)) :=
    f1024TowerZeroDivisor (F1024TowerLevel 0) x
  have hx : x ≠ 0 := f1024TowerLevelHistoricalX_ne_zero 0 0
  have hDdegree :
      Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel 0)) D = 1 := by
    dsimp only [D]
    rw [f1024TowerZeroDivisor_degree_eq_polarDivisor_degree
      (F1024TowerLevel 0) hx]
    simpa only [pow_zero, Nat.cast_one] using
      f1024TowerLevelHistoricalX_polarDivisor_degree 0 0 (by omega)
  have hDnonnegative : Divisor.Nonnegative D := by
    intro Q
    dsimp only [D]
    rw [f1024TowerZeroDivisor_apply_of_ne_zero
      (F1024TowerLevel 0) hx]
    exact le_max_right _ _
  have hsingle : Finsupp.single P (D P) ≤ D := by
    intro Q
    by_cases hPQ : P = Q
    · subst Q
      simp
    · rw [Finsupp.single_apply, if_neg hPQ]
      exact hDnonnegative Q
  have hle := f1024TowerLevel_divisorDegree_mono 0 hsingle
  have hsingleDegree :
      Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel 0))
          (Finsupp.single P (D P)) =
        D P *
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel 0) P : ℤ) := by
    simp [Divisor.degree, Divisor.degreeHom]
  have hcoefficient : D P = P.order x := by
    dsimp only [D]
    rw [f1024TowerZeroDivisor_apply_of_ne_zero
      (F1024TowerLevel 0) hx]
    exact max_eq_left hpositive.le
  have hresidue : 0 <
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
        (k := F1024) (F := F1024TowerLevel 0) P : ℤ) := by
    exact_mod_cast f1024TowerLevel_residueDegree_pos 0 P
  rw [hsingleDegree, hDdegree, hcoefficient] at hle
  nlinarith

private theorem f1024TowerLevelHistoricalX_zero_order_eq_neg_one_of_negative
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel 0))
    (hnegative : P.order (f1024TowerLevelHistoricalX 0 0) < 0) :
    P.order (f1024TowerLevelHistoricalX 0 0) = -1 := by
  classical
  let x : F1024TowerLevel 0 := f1024TowerLevelHistoricalX 0 0
  change P.order x < 0 at hnegative
  change P.order x = -1
  let D : Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel 0)) :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
      (k := F1024) (F := F1024TowerLevel 0) x
  have hx : x ≠ 0 := f1024TowerLevelHistoricalX_ne_zero 0 0
  have hDdegree :
      Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel 0)) D = 1 := by
    dsimp only [D]
    simpa only [pow_zero, Nat.cast_one] using
      f1024TowerLevelHistoricalX_polarDivisor_degree 0 0 (by omega)
  have hDnonnegative : Divisor.Nonnegative D := by
    intro Q
    dsimp only [D]
    rw [f1024TowerPolarDivisor_apply_of_ne_zero
      (F1024TowerLevel 0) hx]
    exact le_max_right _ _
  have hsingle : Finsupp.single P (D P) ≤ D := by
    intro Q
    by_cases hPQ : P = Q
    · subst Q
      simp
    · rw [Finsupp.single_apply, if_neg hPQ]
      exact hDnonnegative Q
  have hle := f1024TowerLevel_divisorDegree_mono 0 hsingle
  have hsingleDegree :
      Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel 0))
          (Finsupp.single P (D P)) =
        D P *
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel 0) P : ℤ) := by
    simp [Divisor.degree, Divisor.degreeHom]
  have hcoefficient : D P = -P.order x := by
    dsimp only [D]
    rw [f1024TowerPolarDivisor_apply_of_ne_zero
      (F1024TowerLevel 0) hx]
    exact max_eq_left (by omega)
  have hresidue : 0 <
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
        (k := F1024) (F := F1024TowerLevel 0) P : ℤ) := by
    exact_mod_cast f1024TowerLevel_residueDegree_pos 0 P
  rw [hsingleDegree, hDdegree, hcoefficient] at hle
  nlinarith

private theorem f1024TowerLevelX_order_eq_pow_of_positive :
    ∀ (height : ℕ)
      (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
        (F1024TowerLevel height)),
      0 < P.order (f1024TowerLevelX height) →
        P.order (f1024TowerLevelX height) = (32 : ℤ) ^ height := by
  intro height
  induction height with
  | zero =>
      intro P hpositive
      rw [← f1024TowerLevelHistoricalX_current 0] at hpositive ⊢
      exact f1024TowerLevelHistoricalX_zero_order_eq_one_of_positive P hpositive
  | succ height ih =>
      intro Q hpositive
      let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
          (F1024TowerLevel height) :=
        f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q
      let u : F1024TowerLevel (height + 1) :=
        algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1)) (f1024TowerLevelX height)
      let v : F1024TowerLevel (height + 1) :=
        f1024TowerLevelX (height + 1)
      have hu : u ≠ 0 :=
        (map_ne_zero_iff
          (algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)))
          (algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1))).injective).mpr
              (f1024TowerLevelX_ne_zero height)
      have hv : v ≠ 0 := f1024TowerLevelX_ne_zero (height + 1)
      change 0 < Q.order v at hpositive
      have hcases := f1024Tower_recurrence_order_cases
          (F1024TowerLevel (height + 1)) Q hu hv
            (by simpa only [u, v] using
              f1024TowerLevel_step_X_recurrence height)
      have hpositiveOrders : 0 < Q.order u ∧
          Q.order v = 32 * Q.order u := by
        rcases hcases with hPole | hZero | hCancel
        · omega
        · exact hZero
        · omega
      obtain ⟨huPositive, hvOrder⟩ := hpositiveOrders
      obtain ⟨e, he, hscale⟩ :=
        f1024Tower_restrictedGlobalPlace_order_scale
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q
      have hscaleX := hscale (f1024TowerLevelX height)
        (f1024TowerLevelX_ne_zero height)
      change Q.order u = (e : ℤ) * P.order (f1024TowerLevelX height)
        at hscaleX
      have heInt : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
      have hPPositive : 0 < P.order (f1024TowerLevelX height) := by
        nlinarith [huPositive]
      have hPOrder := ih P hPPositive
      have hmapOrder : Q.order u = P.order (f1024TowerLevelX height) := by
        let Qstage :
            @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
              (F1024TowerLevel (height + 1)) _ _ _
                (f1024TowerStage (height + 1)).constantAlgebraInst :=
          @QEC.Coding.AlgebraicGeometry.GlobalPlace.mk F1024
            (F1024TowerLevel (height + 1)) _ _ _
              (f1024TowerStage (height + 1)).constantAlgebraInst
              (@QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024
                (F1024TowerLevel (height + 1)) _ _ _
                  (f1024TowerLevelCoordinateDivisorAlgebra (height + 1)) Q)
              (@QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized F1024
                (F1024TowerLevel (height + 1)) _ _ _
                  (f1024TowerLevelCoordinateDivisorAlgebra (height + 1)) Q)
        letI : Algebra F1024 (F1024TowerLevel height) :=
          (f1024TowerStage height).constantAlgebraInst
        letI : Algebra F1024 (F1024TowerLevel (height + 1)) :=
          (f1024TowerStage (height + 1)).constantAlgebraInst
        letI : IsScalarTower F1024 (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)) :=
          f1024TowerLevelStepConstantScalarTower height
        have hregularStage : 0 ≤
            (f1024Tower_restrictedGlobalPlace
              (k := F1024) (K := F1024TowerLevel height)
              (L := F1024TowerLevel (height + 1)) Qstage).order
                (f1024TowerLevelX height) := by
          unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order at hPPositive ⊢
          exact hPPositive.le
        have h := f1024TowerLevel_step_order_eq_of_lowerX_nonnegative
          height Qstage hregularStage (f1024TowerLevelX height)
            (f1024TowerLevelX_ne_zero height)
        unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order at h ⊢
        exact h
      calc
        Q.order (f1024TowerLevelX (height + 1)) = Q.order v := rfl
        _ = 32 * Q.order u := hvOrder
        _ = 32 * P.order (f1024TowerLevelX height) := by rw [hmapOrder]
        _ = 32 * (32 : ℤ) ^ height := by rw [hPOrder]
        _ = (32 : ℤ) ^ (height + 1) := by rw [pow_succ]; ring

private theorem f1024TowerLevelX_order_eq_neg_one_of_base_pole :
    ∀ (height : ℕ)
      (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
        (F1024TowerLevel height)),
      P.order (f1024TowerLevelHistoricalX height 0) < 0 →
        P.order (f1024TowerLevelX height) = -1 := by
  intro height
  induction height with
  | zero =>
      intro P hnegative
      rw [← f1024TowerLevelHistoricalX_current 0]
      exact f1024TowerLevelHistoricalX_zero_order_eq_neg_one_of_negative
        P hnegative
  | succ height ih =>
      intro Q hbasePole
      let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
          (F1024TowerLevel height) :=
        f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q
      obtain ⟨e, he, hscale⟩ :=
        f1024Tower_restrictedGlobalPlace_order_scale
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q
      have hscaleZero := hscale (f1024TowerLevelHistoricalX height 0)
        (f1024TowerLevelHistoricalX_ne_zero height 0)
      rw [f1024TowerLevelHistoricalX_succ_map height 0 (by omega)] at hscaleZero
      change Q.order (f1024TowerLevelHistoricalX (height + 1) 0) =
        (e : ℤ) * P.order (f1024TowerLevelHistoricalX height 0) at hscaleZero
      have heInt : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
      have hPBasePole : P.order
          (f1024TowerLevelHistoricalX height 0) < 0 := by
        nlinarith
      have hPCurrent := ih P hPBasePole
      let Qstage :
          @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
            (F1024TowerLevel (height + 1)) _ _ _
              (f1024TowerStage (height + 1)).constantAlgebraInst :=
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.mk F1024
          (F1024TowerLevel (height + 1)) _ _ _
            (f1024TowerStage (height + 1)).constantAlgebraInst
            (@QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024
              (F1024TowerLevel (height + 1)) _ _ _
                (f1024TowerLevelCoordinateDivisorAlgebra (height + 1)) Q)
            (@QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized F1024
              (F1024TowerLevel (height + 1)) _ _ _
                (f1024TowerLevelCoordinateDivisorAlgebra (height + 1)) Q)
      letI : Algebra F1024 (F1024TowerLevel height) :=
        (f1024TowerStage height).constantAlgebraInst
      letI : Algebra F1024 (F1024TowerLevel (height + 1)) :=
        (f1024TowerStage (height + 1)).constantAlgebraInst
      letI : IsScalarTower F1024 (F1024TowerLevel height)
          (F1024TowerLevel (height + 1)) :=
        f1024TowerLevelStepConstantScalarTower height
      have hPCurrentStage :
          (f1024Tower_restrictedGlobalPlace
            (k := F1024) (K := F1024TowerLevel height)
            (L := F1024TowerLevel (height + 1)) Qstage).order
              (f1024TowerLevelX height) = -1 := by
        unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order at hPCurrent ⊢
        exact hPCurrent
      have hresult :=
        (f1024TowerLevel_step_order_scale_eq_32_of_lowerX_eq_neg_one
          height Qstage hPCurrentStage).2
      unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order at hresult ⊢
      exact hresult

private theorem
    f1024TowerLevelCoordinateDivisor_step_order_eq_of_lowerX_nonnegative
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1)))
    (hregular : 0 ≤
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Q).order
          (f1024TowerLevelX height)) :
    ∀ u : F1024TowerLevel height, u ≠ 0 →
      Q.order
          (algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)) u) =
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q).order u := by
  let Qstage :
      @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
        (F1024TowerLevel (height + 1)) _ _ _
          (f1024TowerStage (height + 1)).constantAlgebraInst :=
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.mk F1024
      (F1024TowerLevel (height + 1)) _ _ _
        (f1024TowerStage (height + 1)).constantAlgebraInst
        (@QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024
          (F1024TowerLevel (height + 1)) _ _ _
            (f1024TowerLevelCoordinateDivisorAlgebra (height + 1)) Q)
        (@QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized F1024
          (F1024TowerLevel (height + 1)) _ _ _
            (f1024TowerLevelCoordinateDivisorAlgebra (height + 1)) Q)
  letI : Algebra F1024 (F1024TowerLevel height) :=
    (f1024TowerStage height).constantAlgebraInst
  letI : Algebra F1024 (F1024TowerLevel (height + 1)) :=
    (f1024TowerStage (height + 1)).constantAlgebraInst
  letI : IsScalarTower F1024 (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) :=
    f1024TowerLevelStepConstantScalarTower height
  have hregularStage : 0 ≤
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Qstage).order
          (f1024TowerLevelX height) := by
    unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order at hregular ⊢
    exact hregular
  intro u hu
  have h := f1024TowerLevel_step_order_eq_of_lowerX_nonnegative
    height Qstage hregularStage u hu
  unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order at h ⊢
  exact h

private theorem
    f1024TowerLevelCoordinateDivisor_step_order_scale_eq_32_of_lowerX_eq_neg_one
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1)))
    (hpole :
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Q).order
          (f1024TowerLevelX height) = -1) :
    (∀ u : F1024TowerLevel height, u ≠ 0 →
      Q.order
          (algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)) u) =
        32 *
          (f1024Tower_restrictedGlobalPlace
            (k := F1024) (K := F1024TowerLevel height)
            (L := F1024TowerLevel (height + 1)) Q).order u) ∧
      Q.order (f1024TowerLevelX (height + 1)) = -1 := by
  let Qstage :
      @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
        (F1024TowerLevel (height + 1)) _ _ _
          (f1024TowerStage (height + 1)).constantAlgebraInst :=
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.mk F1024
      (F1024TowerLevel (height + 1)) _ _ _
        (f1024TowerStage (height + 1)).constantAlgebraInst
        (@QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024
          (F1024TowerLevel (height + 1)) _ _ _
            (f1024TowerLevelCoordinateDivisorAlgebra (height + 1)) Q)
        (@QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized F1024
          (F1024TowerLevel (height + 1)) _ _ _
            (f1024TowerLevelCoordinateDivisorAlgebra (height + 1)) Q)
  letI : Algebra F1024 (F1024TowerLevel height) :=
    (f1024TowerStage height).constantAlgebraInst
  letI : Algebra F1024 (F1024TowerLevel (height + 1)) :=
    (f1024TowerStage (height + 1)).constantAlgebraInst
  letI : IsScalarTower F1024 (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) :=
    f1024TowerLevelStepConstantScalarTower height
  have hpoleStage :
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Qstage).order
          (f1024TowerLevelX height) = -1 := by
    unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order at hpole ⊢
    exact hpole
  have hresult :=
    f1024TowerLevel_step_order_scale_eq_32_of_lowerX_eq_neg_one
      height Qstage hpoleStage
  constructor
  · intro u hu
    have h := hresult.1 u hu
    unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order at h ⊢
    exact h
  · have h := hresult.2
    unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order at h ⊢
    exact h

private theorem f1024TowerLevelX_order_eq_of_switch :
    ∀ (height i : ℕ) (hi : i < height)
      (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
        (F1024TowerLevel height)),
      0 < P.order (f1024TowerLevelHistoricalX height i) →
      P.order (f1024TowerLevelHistoricalX height (i + 1)) < 0 →
      P.order (f1024TowerLevelX height) =
        -(32 : ℤ) ^ (2 * i + 1 - height) := by
  intro height
  induction height with
  | zero =>
      intro i hi
      omega
  | succ height ih =>
      intro i hi Q hpositive hpole
      let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
          (F1024TowerLevel height) :=
        f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q
      obtain ⟨e, he, hscale⟩ :=
        f1024Tower_restrictedGlobalPlace_order_scale
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q
      have heInt : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
      by_cases hinew : i = height
      · subst i
        have hscaleCurrent := hscale (f1024TowerLevelX height)
          (f1024TowerLevelX_ne_zero height)
        rw [← f1024TowerLevelHistoricalX_current height,
          f1024TowerLevelHistoricalX_succ_map height height (by omega)]
          at hscaleCurrent
        have hscaleCurrent' :
            Q.order (f1024TowerLevelHistoricalX (height + 1) height) =
              (e : ℤ) * P.order (f1024TowerLevelX height) := by
          simpa only [P, f1024TowerLevelHistoricalX_current height] using
            hscaleCurrent
        have hPPositive : 0 < P.order (f1024TowerLevelX height) := by
          nlinarith [hscaleCurrent']
        have hPOrder :=
          f1024TowerLevelX_order_eq_pow_of_positive height P hPPositive
        have hmapOrder :=
          f1024TowerLevelCoordinateDivisor_step_order_eq_of_lowerX_nonnegative
            height Q hPPositive.le (f1024TowerLevelX height)
              (f1024TowerLevelX_ne_zero height)
        rw [← f1024TowerLevelHistoricalX_current height,
          f1024TowerLevelHistoricalX_succ_map height height (by omega)]
          at hmapOrder
        have hmapOrderCurrent :
            Q.order (f1024TowerLevelHistoricalX (height + 1) height) =
              P.order (f1024TowerLevelX height) := by
          simpa only [P, f1024TowerLevelHistoricalX_current height] using
            hmapOrder
        have hswitch :
            Q.order (f1024TowerLevelHistoricalX (height + 1) (height + 1)) =
              -Q.order (f1024TowerLevelHistoricalX (height + 1) height) := by
          obtain hPole | hZero | hCancel :=
            f1024Tower_recurrence_order_cases
              (F1024TowerLevel (height + 1)) Q
              (f1024TowerLevelHistoricalX_ne_zero (height + 1) height)
              (f1024TowerLevelHistoricalX_ne_zero
                (height + 1) (height + 1))
              (f1024TowerLevelHistoricalX_recurrence
                (height + 1) height (by omega))
          · omega
          · omega
          · exact hCancel.2
        have hexponent : 2 * height + 1 - (height + 1) = height := by omega
        rw [← f1024TowerLevelHistoricalX_current (height + 1),
          hswitch, hmapOrderCurrent, hPOrder, hexponent]
      · have hiOld : i < height := by omega
        have hscalePositive := hscale
          (f1024TowerLevelHistoricalX height i)
          (f1024TowerLevelHistoricalX_ne_zero height i)
        rw [f1024TowerLevelHistoricalX_succ_map height i (by omega)]
          at hscalePositive
        have hscalePole := hscale
          (f1024TowerLevelHistoricalX height (i + 1))
          (f1024TowerLevelHistoricalX_ne_zero height (i + 1))
        rw [f1024TowerLevelHistoricalX_succ_map height (i + 1) (by omega)]
          at hscalePole
        have hPPositive :
            0 < P.order (f1024TowerLevelHistoricalX height i) := by
          nlinarith
        have hPPole :
            P.order (f1024TowerLevelHistoricalX height (i + 1)) < 0 := by
          nlinarith
        have hPCurrent := ih i hiOld P hPPositive hPPole
        by_cases hearly : 2 * i + 1 ≤ height
        · have hPCurrentSimple :
              P.order (f1024TowerLevelX height) = -1 := by
            simpa only [Nat.sub_eq_zero_of_le hearly, pow_zero] using hPCurrent
          have hQCurrentSimple :=
            (f1024TowerLevelCoordinateDivisor_step_order_scale_eq_32_of_lowerX_eq_neg_one
              height Q hPCurrentSimple).2
          have hexponent : 2 * i + 1 - (height + 1) = 0 := by omega
          simpa only [hexponent, pow_zero] using hQCurrentSimple
        · let d : ℕ := height - (i + 1)
          have hd : d ≤ i := by
            dsimp only [d]
            omega
          have hcurrentIndex : i + 1 + d = height := by
            dsimp only [d]
            omega
          have hprevious : 1 ≤ i - d := by
            dsimp only [d]
            omega
          have hunramified :=
            f1024TowerLevel_step_order_eq_of_old_switch
              height i d hd hcurrentIndex hprevious Q hPPositive hPPole
          have hmapCurrent := hunramified (f1024TowerLevelX height)
            (f1024TowerLevelX_ne_zero height)
          have hmapCurrentHistorical :
              Q.order (f1024TowerLevelHistoricalX (height + 1) height) =
                P.order (f1024TowerLevelX height) := by
            rw [← f1024TowerLevelHistoricalX_succ_map
              height height (by omega),
              f1024TowerLevelHistoricalX_current height]
            simpa only [P] using hmapCurrent
          have hmapPole :
              Q.order (f1024TowerLevelHistoricalX (height + 1) height) < 0 := by
            rw [hmapCurrentHistorical, hPCurrent]
            exact neg_neg_of_pos (pow_pos (by norm_num) _)
          obtain ⟨hstep, _⟩ :=
            f1024TowerLevelHistoricalX_order_next_of_pole
              (height + 1) height (by omega) Q hmapPole
          have hstepCurrent :
              P.order (f1024TowerLevelX height) =
                32 * Q.order (f1024TowerLevelX (height + 1)) := by
            rw [← f1024TowerLevelHistoricalX_current (height + 1)]
            exact hmapCurrentHistorical.symm.trans hstep
          have hexponent :
              2 * i + 1 - height =
                (2 * i + 1 - (height + 1)) + 1 := by
            omega
          apply mul_left_cancel₀ (by norm_num : (32 : ℤ) ≠ 0)
          calc
            32 * Q.order (f1024TowerLevelX (height + 1)) =
                P.order (f1024TowerLevelX height) := hstepCurrent.symm
            _ = -(32 : ℤ) ^ (2 * i + 1 - height) := hPCurrent
            _ = 32 * (-(32 : ℤ) ^
                (2 * i + 1 - (height + 1))) := by
              rw [hexponent, pow_succ]
              ring

/-- The actual pole contribution created at source recurrence `i` inside
the final level `height`.  A place belongs to this stratum precisely when
`x_i` is a zero and `x_(i+1)` is a pole there. -/
noncomputable def f1024TowerLevelPoleStratum
    (height : ℕ) (i : Fin height) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) := by
  classical
  exact (QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
      (k := F1024) (F := F1024TowerLevel height)
      (f1024TowerLevelX height)).filter fun P =>
        0 < P.order (f1024TowerLevelHistoricalX height i) ∧
          P.order (f1024TowerLevelHistoricalX height (i + 1)) < 0

private theorem f1024TowerLevelPoleStratum_nsmul_eq_switch
    (height : ℕ) (i : Fin height) :
    32 ^ (height - ((i : ℕ) + 1)) •
        f1024TowerLevelPoleStratum height i =
      f1024TowerSwitchZeroDivisor (F1024TowerLevel height)
        (f1024TowerLevelHistoricalX height i)
        (f1024TowerLevelHistoricalX height (i + 1)) := by
  classical
  let d : ℕ := height - ((i : ℕ) + 1)
  have hid : (i : ℕ) + 1 + d = height := by
    dsimp only [d]
    omega
  ext P
  obtain hPole | hZero | hCancel :=
    f1024Tower_recurrence_order_cases (F1024TowerLevel height) P
      (f1024TowerLevelHistoricalX_ne_zero height i)
      (f1024TowerLevelHistoricalX_ne_zero height (i + 1))
      (f1024TowerLevelHistoricalX_recurrence height i i.isLt)
  all_goals
    simp only [f1024TowerLevelPoleStratum, Finsupp.nsmul_apply,
      Finsupp.filter_apply, f1024TowerSwitchZeroDivisor,
      f1024TowerZeroDivisor_apply_of_ne_zero
        (F1024TowerLevel height)
        (f1024TowerLevelHistoricalX_ne_zero height i),
      f1024TowerPolarDivisor_apply_of_ne_zero
        (F1024TowerLevel height) (f1024TowerLevelX_ne_zero height),
      nsmul_eq_mul]
  · have hnext :
        P.order (f1024TowerLevelHistoricalX height (i + 1)) < 0 := by
      omega
    have hnotPositive :
        ¬0 < P.order (f1024TowerLevelHistoricalX height i) := by omega
    have hnotStratum : ¬(
        0 < P.order (f1024TowerLevelHistoricalX height i) ∧
          P.order (f1024TowerLevelHistoricalX height (i + 1)) < 0) :=
      fun h => hnotPositive h.1
    rw [if_neg hnotStratum, if_pos hnext,
      max_eq_right (by omega :
        P.order (f1024TowerLevelHistoricalX height i) ≤ 0)]
    simp
  · have hnext :
        0 < P.order (f1024TowerLevelHistoricalX height (i + 1)) := by
      omega
    have hnotNext :
        ¬P.order (f1024TowerLevelHistoricalX height (i + 1)) < 0 := by omega
    have hnotStratum : ¬(
        0 < P.order (f1024TowerLevelHistoricalX height i) ∧
          P.order (f1024TowerLevelHistoricalX height (i + 1)) < 0) :=
      fun h => hnotNext h.2
    rw [if_neg hnotStratum, if_neg hnotNext]
    simp
  · by_cases hzero :
        P.order (f1024TowerLevelHistoricalX height i) = 0
    · simp [hzero, hCancel.2]
    · have hpositive :
          0 < P.order (f1024TowerLevelHistoricalX height i) := by omega
      have hnext :
          P.order (f1024TowerLevelHistoricalX height (i + 1)) < 0 := by
        rw [hCancel.2]
        omega
      have hiter :=
        f1024TowerLevelHistoricalX_order_iterate_of_pole
          height ((i : ℕ) + 1) d (by omega) P hnext
      have hiterOrder :
          P.order (f1024TowerLevelHistoricalX height (i + 1)) =
            (32 : ℤ) ^ d * P.order (f1024TowerLevelX height) := by
        simpa only [hid, f1024TowerLevelHistoricalX_current] using hiter.1
      have hcurrent : P.order (f1024TowerLevelX height) < 0 := by
        simpa only [hid, f1024TowerLevelHistoricalX_current] using hiter.2
      rw [if_pos (show
        0 < P.order (f1024TowerLevelHistoricalX height i) ∧
          P.order (f1024TowerLevelHistoricalX height (i + 1)) < 0 from
            ⟨hpositive, hnext⟩), if_pos hnext]
      rw [max_eq_left (by omega : -P.order (f1024TowerLevelX height) ≥ 0),
        max_eq_left (by omega :
          P.order (f1024TowerLevelHistoricalX height i) ≥ 0)]
      change ((32 ^ d : ℕ) : ℤ) *
          -P.order (f1024TowerLevelX height) =
        P.order (f1024TowerLevelHistoricalX height i)
      rw [Nat.cast_pow]
      calc
        (32 : ℤ) ^ d * -P.order (f1024TowerLevelX height) =
            -P.order
              (f1024TowerLevelHistoricalX height (i + 1)) := by
          rw [hiterOrder]
          ring
        _ = P.order (f1024TowerLevelHistoricalX height i) := by
          rw [hCancel.2]
          ring

private theorem f1024TowerLevelSwitchZeroDivisor_degree
    (height : ℕ) (i : Fin height) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel height))
        (f1024TowerSwitchZeroDivisor (F1024TowerLevel height)
          (f1024TowerLevelHistoricalX height i)
          (f1024TowerLevelHistoricalX height (i + 1))) =
      (31 : ℤ) * (32 : ℤ) ^ (height - 1) := by
  let degree := Divisor.degree
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
      (k := F1024) (F := F1024TowerLevel height))
  have hdivisor := f1024TowerPolarDivisor_recurrence_identity
    (F1024TowerLevel height)
    (f1024TowerLevelHistoricalX_ne_zero height i)
    (f1024TowerLevelHistoricalX_ne_zero height (i + 1))
    (f1024TowerLevelHistoricalX_recurrence height i i.isLt)
  have hdegree := congrArg degree hdivisor
  dsimp only [degree] at hdegree ⊢
  rw [f1024TowerDivisor_degree_nsmul (F1024TowerLevel height),
    Divisor.degree_add,
    f1024TowerDivisor_degree_nsmul (F1024TowerLevel height),
    f1024TowerLevelHistoricalX_polarDivisor_degree height i i.isLt.le,
    f1024TowerLevelHistoricalX_polarDivisor_degree height (i + 1)
      (by omega)] at hdegree
  have hpow : (32 : ℤ) ^ height =
      32 * (32 : ℤ) ^ (height - 1) := by
    have hheightPositive : 0 < height :=
      lt_of_le_of_lt (Nat.zero_le (i : ℕ)) i.isLt
    have hone : 1 ≤ height := hheightPositive
    have hheight : height - 1 + 1 = height := Nat.sub_add_cancel hone
    calc
      (32 : ℤ) ^ height = (32 : ℤ) ^ ((height - 1) + 1) := by
        rw [hheight]
      _ = 32 * (32 : ℤ) ^ (height - 1) := by rw [pow_succ]; ring
  rw [hpow] at hdegree
  norm_num at hdegree ⊢
  nlinarith

/-- The intrinsic degree of the pole stratum created at recurrence `i` is
`31 * 32^i`, exactly the source's `q^i (q-1)` stratum degree at `q = 32`.
The proof derives the coefficient rescaling through every later recurrence
and then uses the all-place principal-divisor degree formula. -/
theorem f1024TowerLevelPoleStratum_degree
    (height : ℕ) (i : Fin height) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel height))
        (f1024TowerLevelPoleStratum height i) =
      (31 : ℤ) * (32 : ℤ) ^ (i : ℕ) := by
  let degree := Divisor.degree
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
      (k := F1024) (F := F1024TowerLevel height))
  have hdivisor :=
    f1024TowerLevelPoleStratum_nsmul_eq_switch height i
  have hdegree := congrArg degree hdivisor
  dsimp only [degree] at hdegree ⊢
  rw [f1024TowerDivisor_degree_nsmul (F1024TowerLevel height),
    f1024TowerLevelSwitchZeroDivisor_degree height i] at hdegree
  let d : ℕ := height - ((i : ℕ) + 1)
  have hexponent : height - 1 = d + (i : ℕ) := by
    dsimp only [d]
    omega
  have hcast : (((32 ^ d : ℕ) : ℤ)) = (32 : ℤ) ^ d := by
    norm_num
  rw [show height - ((i : ℕ) + 1) = d by rfl, hcast,
    hexponent, pow_add] at hdegree
  have hpow_ne : (32 : ℤ) ^ d ≠ 0 := pow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ hpow_ne
  calc
    (32 : ℤ) ^ d *
        Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel height))
          (f1024TowerLevelPoleStratum height i) =
      31 * ((32 : ℤ) ^ d * (32 : ℤ) ^ (i : ℕ)) := hdegree
    _ = (32 : ℤ) ^ d *
        (31 * (32 : ℤ) ^ (i : ℕ)) := by ring

/-- The part of the current-coordinate pole divisor lying above the pole of
the original rational coordinate. -/
noncomputable def f1024TowerLevelBasePoleDivisor (height : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) := by
  classical
  exact (QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
      (k := F1024) (F := F1024TowerLevel height)
      (f1024TowerLevelX height)).filter fun P =>
        P.order (f1024TowerLevelHistoricalX height 0) < 0

private theorem f1024TowerLevelBasePoleDivisor_nsmul_eq
    (height : ℕ) :
    32 ^ height • f1024TowerLevelBasePoleDivisor height =
      QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
        (k := F1024) (F := F1024TowerLevel height)
        (f1024TowerLevelHistoricalX height 0) := by
  classical
  ext P
  simp only [f1024TowerLevelBasePoleDivisor, Finsupp.nsmul_apply,
    Finsupp.filter_apply,
    f1024TowerPolarDivisor_apply_of_ne_zero
      (F1024TowerLevel height) (f1024TowerLevelX_ne_zero height),
    f1024TowerPolarDivisor_apply_of_ne_zero
      (F1024TowerLevel height)
      (f1024TowerLevelHistoricalX_ne_zero height 0),
    nsmul_eq_mul]
  by_cases hpole :
      P.order (f1024TowerLevelHistoricalX height 0) < 0
  · have hiter :=
      f1024TowerLevelHistoricalX_order_iterate_of_pole
        height 0 height (by omega) P hpole
    have horder :
        P.order (f1024TowerLevelHistoricalX height 0) =
          (32 : ℤ) ^ height * P.order (f1024TowerLevelX height) := by
      simpa only [zero_add, f1024TowerLevelHistoricalX_current] using hiter.1
    have hcurrent : P.order (f1024TowerLevelX height) < 0 := by
      simpa only [zero_add, f1024TowerLevelHistoricalX_current] using hiter.2
    rw [if_pos hpole,
      max_eq_left (by omega : -P.order (f1024TowerLevelX height) ≥ 0),
      max_eq_left (by omega :
        -P.order (f1024TowerLevelHistoricalX height 0) ≥ 0),
      Nat.cast_pow]
    rw [horder]
    ring
  · rw [if_neg hpole,
      max_eq_right (by omega :
        -P.order (f1024TowerLevelHistoricalX height 0) ≤ 0)]
    simp

/-- The base-pole contribution has degree one.  This is derived by comparing
its coefficient rescaling with the actual pole divisor of the original chart
coordinate. -/
theorem f1024TowerLevelBasePoleDivisor_degree (height : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel height))
        (f1024TowerLevelBasePoleDivisor height) = 1 := by
  let degree := Divisor.degree
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
      (k := F1024) (F := F1024TowerLevel height))
  have hdivisor := f1024TowerLevelBasePoleDivisor_nsmul_eq height
  have hdegree := congrArg degree hdivisor
  dsimp only [degree] at hdegree ⊢
  rw [f1024TowerDivisor_degree_nsmul (F1024TowerLevel height),
    f1024TowerLevelHistoricalX_polarDivisor_degree height 0
      (Nat.zero_le height)] at hdegree
  have hpow_ne : (((32 ^ height : ℕ) : ℤ)) ≠ 0 := by norm_num
  apply mul_left_cancel₀ hpow_ne
  calc
    ((32 ^ height : ℕ) : ℤ) *
        Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel height))
          (f1024TowerLevelBasePoleDivisor height) =
      (32 : ℤ) ^ height := hdegree
    _ = ((32 ^ height : ℕ) : ℤ) * 1 := by norm_num

private theorem f1024TowerLevelPolarDivisor_telescope
    (height j : ℕ) (hj : j ≤ height) :
    32 ^ j •
        QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F1024TowerLevel height)
          (f1024TowerLevelHistoricalX height j) =
      QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F1024TowerLevel height)
          (f1024TowerLevelHistoricalX height 0) +
        ∑ i ∈ Finset.range j, 32 ^ (i + 1) •
          f1024TowerSwitchZeroDivisor (F1024TowerLevel height)
            (f1024TowerLevelHistoricalX height i)
            (f1024TowerLevelHistoricalX height (i + 1)) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hjlt : j < height := Nat.lt_of_succ_le hj
      have hrec := f1024TowerPolarDivisor_recurrence_identity
        (F1024TowerLevel height)
        (f1024TowerLevelHistoricalX_ne_zero height j)
        (f1024TowerLevelHistoricalX_ne_zero height (j + 1))
        (f1024TowerLevelHistoricalX_recurrence height j hjlt)
      calc
        32 ^ (j + 1) •
              QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
                (k := F1024) (F := F1024TowerLevel height)
                (f1024TowerLevelHistoricalX height (j + 1)) =
            32 ^ j • (32 •
              QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
                (k := F1024) (F := F1024TowerLevel height)
                (f1024TowerLevelHistoricalX height (j + 1))) := by
              rw [pow_succ, Nat.mul_comm, mul_nsmul]
        _ = 32 ^ j •
              (QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
                  (k := F1024) (F := F1024TowerLevel height)
                  (f1024TowerLevelHistoricalX height j) +
                32 • f1024TowerSwitchZeroDivisor (F1024TowerLevel height)
                  (f1024TowerLevelHistoricalX height j)
                  (f1024TowerLevelHistoricalX height (j + 1))) := by
              rw [hrec]
        _ = (QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
                  (k := F1024) (F := F1024TowerLevel height)
                  (f1024TowerLevelHistoricalX height 0) +
                ∑ i ∈ Finset.range j, 32 ^ (i + 1) •
                  f1024TowerSwitchZeroDivisor (F1024TowerLevel height)
                    (f1024TowerLevelHistoricalX height i)
                    (f1024TowerLevelHistoricalX height (i + 1))) +
              32 ^ (j + 1) •
                f1024TowerSwitchZeroDivisor (F1024TowerLevel height)
                  (f1024TowerLevelHistoricalX height j)
                  (f1024TowerLevelHistoricalX height (j + 1)) := by
              rw [nsmul_add, ih (Nat.le_of_lt hjlt)]
              congr 1
              rw [← mul_nsmul, pow_succ, Nat.mul_comm (32 ^ j) 32]
        _ = QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
                (k := F1024) (F := F1024TowerLevel height)
                (f1024TowerLevelHistoricalX height 0) +
              ∑ i ∈ Finset.range (j + 1), 32 ^ (i + 1) •
                f1024TowerSwitchZeroDivisor (F1024TowerLevel height)
                  (f1024TowerLevelHistoricalX height i)
                  (f1024TowerLevelHistoricalX height (i + 1)) := by
              rw [Finset.sum_range_succ, add_assoc]

/-- The current-coordinate pole divisor is the disjoint source partition
into the base-pole contribution and the first zero-to-pole switch strata.
The equality is obtained by telescoping the literal recurrences and
cancelling a nonzero integer scaling on the intrinsic divisor group. -/
theorem f1024TowerLevel_polarDivisor_partition (height : ℕ) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F1024TowerLevel height)
          (f1024TowerLevelX height) =
      f1024TowerLevelBasePoleDivisor height +
        ∑ i : Fin height, f1024TowerLevelPoleStratum height i := by
  apply nsmul_right_injective (pow_ne_zero height (by norm_num : 32 ≠ 0))
  change 32 ^ height •
        QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F1024TowerLevel height)
          (f1024TowerLevelX height) =
      32 ^ height •
        (f1024TowerLevelBasePoleDivisor height +
          ∑ i : Fin height, f1024TowerLevelPoleStratum height i)
  have htelescope :=
    f1024TowerLevelPolarDivisor_telescope height height (le_refl height)
  rw [f1024TowerLevelHistoricalX_current] at htelescope
  rw [nsmul_add, Finset.smul_sum,
    f1024TowerLevelBasePoleDivisor_nsmul_eq height]
  have hsum :
      ∑ i : Fin height,
          32 ^ height • f1024TowerLevelPoleStratum height i =
        ∑ i : Fin height, 32 ^ ((i : ℕ) + 1) •
          f1024TowerSwitchZeroDivisor (F1024TowerLevel height)
            (f1024TowerLevelHistoricalX height (i : ℕ))
            (f1024TowerLevelHistoricalX height ((i : ℕ) + 1)) := by
    apply Fintype.sum_congr
    intro i
    have hscale :=
      f1024TowerLevelPoleStratum_nsmul_eq_switch height i
    have hexponent : (height - ((i : ℕ) + 1)) +
        ((i : ℕ) + 1) = height := by omega
    calc
      32 ^ height • f1024TowerLevelPoleStratum height i =
          32 ^ ((i : ℕ) + 1) •
            (32 ^ (height - ((i : ℕ) + 1)) •
              f1024TowerLevelPoleStratum height i) := by
            rw [← mul_nsmul, ← pow_add, hexponent]
      _ = 32 ^ ((i : ℕ) + 1) •
            f1024TowerSwitchZeroDivisor (F1024TowerLevel height)
              (f1024TowerLevelHistoricalX height (i : ℕ))
              (f1024TowerLevelHistoricalX height ((i : ℕ) + 1)) := by
            rw [hscale]
  rw [hsum]
  rw [Finset.sum_range] at htelescope
  exact htelescope

/-- The actual residual pole divisor used by the source different formula:
the base pole together with the first `(height + 1) / 2` switch strata. -/
noncomputable def f1024TowerLevelResidualPoleDivisor (height : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) :=
  f1024TowerLevelBasePoleDivisor height +
    ∑ i : Fin ((height + 1) / 2),
      f1024TowerLevelPoleStratum height ⟨i, by omega⟩

/-- The source residual divisor has exact degree
`32^((height + 1) / 2)`.  This follows from the realized base pole and the
derived geometric series of actual pole-stratum degrees. -/
theorem f1024TowerLevelResidualPoleDivisor_degree (height : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel height))
        (f1024TowerLevelResidualPoleDivisor height) =
      (32 : ℤ) ^ ((height + 1) / 2) := by
  let degree := Divisor.degree
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
      (k := F1024) (F := F1024TowerLevel height))
  let m : ℕ := (height + 1) / 2
  change degree
      (f1024TowerLevelBasePoleDivisor height +
        ∑ i : Fin m,
          f1024TowerLevelPoleStratum height ⟨i, by dsimp only [m]; omega⟩) =
    (32 : ℤ) ^ m
  dsimp only [degree]
  rw [Divisor.degree_add]
  rw [f1024TowerLevelBasePoleDivisor_degree]
  change 1 +
      (Divisor.degreeHom
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel height)))
        (∑ i : Fin m,
          f1024TowerLevelPoleStratum height ⟨i, by dsimp only [m]; omega⟩) =
    (32 : ℤ) ^ m
  rw [map_sum]
  change 1 + ∑ i : Fin m,
      Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel height))
        (f1024TowerLevelPoleStratum height
          ⟨i, by dsimp only [m]; omega⟩) =
    (32 : ℤ) ^ m
  simp_rw [f1024TowerLevelPoleStratum_degree]
  have hgeom : ∀ n : ℕ,
      1 + ∑ i : Fin n, (31 : ℤ) * (32 : ℤ) ^ (i : ℕ) =
        (32 : ℤ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [← add_assoc, ih, pow_succ]
        ring
  exact hgeom m

private theorem f1024TowerLevelBasePoleDivisor_apply_nonnegative
    (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) :
    0 ≤ f1024TowerLevelBasePoleDivisor height P := by
  classical
  simp only [f1024TowerLevelBasePoleDivisor, Finsupp.filter_apply,
    f1024TowerPolarDivisor_apply_of_ne_zero
      (F1024TowerLevel height) (f1024TowerLevelX_ne_zero height)]
  split
  · exact le_max_right _ _
  · exact le_refl 0

private theorem f1024TowerLevelPoleStratum_apply_nonnegative
    (height : ℕ) (i : Fin height)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) :
    0 ≤ f1024TowerLevelPoleStratum height i P := by
  classical
  simp only [f1024TowerLevelPoleStratum, Finsupp.filter_apply,
    f1024TowerPolarDivisor_apply_of_ne_zero
      (F1024TowerLevel height) (f1024TowerLevelX_ne_zero height)]
  split
  · exact le_max_right _ _
  · exact le_refl 0

private theorem f1024TowerLevel_divisor_fintypeSum_apply
    {height : ℕ} {I : Type*} [Fintype I]
    (D : I → Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)))
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) :
    (∑ i : I, D i) P = ∑ i : I, D i P := by
  classical
  change (Finsupp.applyAddHom P) (∑ i : I, D i) = ∑ i : I, D i P
  exact map_sum (Finsupp.applyAddHom P) D Finset.univ

private theorem f1024TowerLevelResidualPoleDivisor_apply_nonnegative
    (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) :
    0 ≤ f1024TowerLevelResidualPoleDivisor height P := by
  classical
  rw [f1024TowerLevelResidualPoleDivisor, Finsupp.add_apply,
    f1024TowerLevel_divisor_fintypeSum_apply]
  exact add_nonneg
    (f1024TowerLevelBasePoleDivisor_apply_nonnegative height P)
    (Finset.sum_nonneg fun i _ =>
      f1024TowerLevelPoleStratum_apply_nonnegative height
        ⟨i, by omega⟩ P)

private theorem
    f1024TowerLevelX_order_eq_neg_one_of_residualPoleDivisor_positive
    (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))
    (hpositive : 0 < f1024TowerLevelResidualPoleDivisor height P) :
    P.order (f1024TowerLevelX height) = -1 := by
  classical
  have hbaseNonnegative :=
    f1024TowerLevelBasePoleDivisor_apply_nonnegative height P
  by_cases hbasePositive :
      0 < f1024TowerLevelBasePoleDivisor height P
  · have hbasePole :
        P.order (f1024TowerLevelHistoricalX height 0) < 0 := by
      by_contra hnot
      have hzero : f1024TowerLevelBasePoleDivisor height P = 0 := by
        simp only [f1024TowerLevelBasePoleDivisor, Finsupp.filter_apply,
          if_neg hnot]
      rw [hzero] at hbasePositive
      omega
    exact f1024TowerLevelX_order_eq_neg_one_of_base_pole
      height P hbasePole
  · have hbaseZero :
        f1024TowerLevelBasePoleDivisor height P = 0 := by
      exact le_antisymm (le_of_not_gt hbasePositive) hbaseNonnegative
    have hsumPositive : 0 < ∑ i : Fin ((height + 1) / 2),
        f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P := by
      rw [f1024TowerLevelResidualPoleDivisor, Finsupp.add_apply,
        f1024TowerLevel_divisor_fintypeSum_apply,
        hbaseZero, zero_add] at hpositive
      exact hpositive
    have htermNonnegative : ∀ i : Fin ((height + 1) / 2),
        0 ≤ f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P :=
      fun i => f1024TowerLevelPoleStratum_apply_nonnegative
        height ⟨i, by omega⟩ P
    obtain ⟨i, _, hiPositive⟩ :=
      (Finset.sum_pos_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin ((height + 1) / 2))))
        (fun i _ => htermNonnegative i)).mp hsumPositive
    have hswitch :
        0 < P.order (f1024TowerLevelHistoricalX height (i : ℕ)) ∧
          P.order (f1024TowerLevelHistoricalX height ((i : ℕ) + 1)) < 0 := by
      by_contra hnot
      have hzero :
          f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P = 0 := by
        simp only [f1024TowerLevelPoleStratum, Finsupp.filter_apply,
          if_neg hnot]
      rw [hzero] at hiPositive
      omega
    have horder := f1024TowerLevelX_order_eq_of_switch
      height (i : ℕ) (by omega) P hswitch.1 hswitch.2
    have hexponent : 2 * (i : ℕ) + 1 - height = 0 := by
      have hi := i.isLt
      omega
    simpa only [hexponent, pow_zero] using horder

private theorem f1024TowerLevelResidualPoleDivisor_le_polarDivisor
    (height : ℕ) :
    f1024TowerLevelResidualPoleDivisor height ≤
      QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
        (k := F1024) (F := F1024TowerLevel height)
        (f1024TowerLevelX height) := by
  classical
  rw [f1024TowerLevel_polarDivisor_partition height]
  intro P
  simp only [f1024TowerLevelResidualPoleDivisor, Finsupp.add_apply]
  rw [f1024TowerLevel_divisor_fintypeSum_apply,
    f1024TowerLevel_divisor_fintypeSum_apply]
  have hsum :
      (∑ i : Fin ((height + 1) / 2),
          f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P) ≤
        ∑ i : Fin height, f1024TowerLevelPoleStratum height i P := by
    let embed : Fin ((height + 1) / 2) ↪ Fin height :=
      ⟨fun i => ⟨i, by omega⟩, fun i j hij => Fin.ext (by
        simpa using congrArg (fun x : Fin height => (x : ℕ)) hij)⟩
    change (∑ i : Fin ((height + 1) / 2),
        f1024TowerLevelPoleStratum height (embed i) P) ≤
      ∑ i : Fin height, f1024TowerLevelPoleStratum height i P
    have hpartial :
        (∑ i : Fin ((height + 1) / 2),
            f1024TowerLevelPoleStratum height (embed i) P) =
          ∑ j ∈ (Finset.univ.map embed),
            f1024TowerLevelPoleStratum height j P := by
      rw [Finset.sum_map]
    rw [hpartial]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro i hi hnot
    exact f1024TowerLevelPoleStratum_apply_nonnegative height i P
  omega

private theorem f1024TowerLevelResidualPoleDivisor_apply_eq_one_of_ne_zero
    (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))
    (hne : f1024TowerLevelResidualPoleDivisor height P ≠ 0) :
    f1024TowerLevelResidualPoleDivisor height P = 1 := by
  have hnonnegative :=
    f1024TowerLevelResidualPoleDivisor_apply_nonnegative height P
  have hpositive : 0 < f1024TowerLevelResidualPoleDivisor height P :=
    lt_of_le_of_ne hnonnegative (Ne.symm hne)
  have horder :=
    f1024TowerLevelX_order_eq_neg_one_of_residualPoleDivisor_positive
      height P hpositive
  have hle := f1024TowerLevelResidualPoleDivisor_le_polarDivisor height P
  rw [f1024TowerPolarDivisor_apply_of_ne_zero
    (F1024TowerLevel height) (f1024TowerLevelX_ne_zero height), horder] at hle
  norm_num at hle
  omega

private theorem f1024TowerLevelBasePoleDivisor_step_apply
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1))) :
    f1024TowerLevelBasePoleDivisor (height + 1) Q =
      f1024TowerLevelBasePoleDivisor height
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q) := by
  classical
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) :=
    f1024Tower_restrictedGlobalPlace
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  change f1024TowerLevelBasePoleDivisor (height + 1) Q =
    f1024TowerLevelBasePoleDivisor height P
  obtain ⟨e, he, hscale⟩ :=
    f1024Tower_restrictedGlobalPlace_order_scale
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  have heInt : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  have hscaleZero := hscale
    (f1024TowerLevelHistoricalX height 0)
    (f1024TowerLevelHistoricalX_ne_zero height 0)
  rw [f1024TowerLevelHistoricalX_succ_map height 0 (by omega)] at hscaleZero
  change Q.order (f1024TowerLevelHistoricalX (height + 1) 0) =
      (e : ℤ) * P.order (f1024TowerLevelHistoricalX height 0)
    at hscaleZero
  by_cases hpole : P.order (f1024TowerLevelHistoricalX height 0) < 0
  · have hupperPole :
        Q.order (f1024TowerLevelHistoricalX (height + 1) 0) < 0 := by
      nlinarith
    have hlowerCurrent :=
      f1024TowerLevelX_order_eq_neg_one_of_base_pole height P hpole
    have hupperCurrent :=
      f1024TowerLevelX_order_eq_neg_one_of_base_pole
        (height + 1) Q hupperPole
    simp only [f1024TowerLevelBasePoleDivisor, Finsupp.filter_apply,
      f1024TowerPolarDivisor_apply_of_ne_zero
        (F1024TowerLevel (height + 1))
        (f1024TowerLevelX_ne_zero (height + 1)),
      f1024TowerPolarDivisor_apply_of_ne_zero
        (F1024TowerLevel height) (f1024TowerLevelX_ne_zero height),
      if_pos hupperPole, if_pos hpole, hupperCurrent, hlowerCurrent]
  · have hupperRegular :
        ¬Q.order (f1024TowerLevelHistoricalX (height + 1) 0) < 0 := by
      intro hnegative
      have hlowerNegative :
          P.order (f1024TowerLevelHistoricalX height 0) < 0 := by
        nlinarith
      exact hpole hlowerNegative
    simp only [f1024TowerLevelBasePoleDivisor, Finsupp.filter_apply,
      if_neg hupperRegular, if_neg hpole]

private theorem f1024TowerLevelPoleStratum_step_apply
    (height : ℕ) (i : Fin ((height + 1) / 2))
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1))) :
    f1024TowerLevelPoleStratum (height + 1) ⟨i, by omega⟩ Q =
      f1024TowerLevelPoleStratum height ⟨i, by omega⟩
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q) := by
  classical
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) :=
    f1024Tower_restrictedGlobalPlace
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  change f1024TowerLevelPoleStratum (height + 1) ⟨i, by omega⟩ Q =
    f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P
  obtain ⟨e, he, hscale⟩ :=
    f1024Tower_restrictedGlobalPlace_order_scale
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  have heInt : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  have hscaleLeft := hscale
    (f1024TowerLevelHistoricalX height (i : ℕ))
    (f1024TowerLevelHistoricalX_ne_zero height (i : ℕ))
  rw [f1024TowerLevelHistoricalX_succ_map height (i : ℕ) (by omega)]
    at hscaleLeft
  have hscaleRight := hscale
    (f1024TowerLevelHistoricalX height ((i : ℕ) + 1))
    (f1024TowerLevelHistoricalX_ne_zero height ((i : ℕ) + 1))
  rw [f1024TowerLevelHistoricalX_succ_map height ((i : ℕ) + 1) (by omega)]
    at hscaleRight
  change Q.order (f1024TowerLevelHistoricalX (height + 1) (i : ℕ)) =
      (e : ℤ) * P.order (f1024TowerLevelHistoricalX height (i : ℕ))
    at hscaleLeft
  change Q.order (f1024TowerLevelHistoricalX (height + 1) ((i : ℕ) + 1)) =
      (e : ℤ) *
        P.order (f1024TowerLevelHistoricalX height ((i : ℕ) + 1))
    at hscaleRight
  by_cases hswitch :
      0 < P.order (f1024TowerLevelHistoricalX height (i : ℕ)) ∧
        P.order (f1024TowerLevelHistoricalX height ((i : ℕ) + 1)) < 0
  · have hupperSwitch :
        0 < Q.order (f1024TowerLevelHistoricalX (height + 1) (i : ℕ)) ∧
          Q.order
              (f1024TowerLevelHistoricalX (height + 1) ((i : ℕ) + 1)) < 0 :=
      ⟨by nlinarith, by nlinarith⟩
    have hlowerOrder := f1024TowerLevelX_order_eq_of_switch
      height (i : ℕ) (by omega) P hswitch.1 hswitch.2
    have hupperOrder := f1024TowerLevelX_order_eq_of_switch
      (height + 1) (i : ℕ) (by omega) Q hupperSwitch.1 hupperSwitch.2
    have hlowerExponent : 2 * (i : ℕ) + 1 - height = 0 := by
      have hi := i.isLt
      omega
    have hupperExponent : 2 * (i : ℕ) + 1 - (height + 1) = 0 := by
      have hi := i.isLt
      omega
    rw [hlowerExponent, pow_zero] at hlowerOrder
    rw [hupperExponent, pow_zero] at hupperOrder
    simp only [f1024TowerLevelPoleStratum, Finsupp.filter_apply,
      f1024TowerPolarDivisor_apply_of_ne_zero
        (F1024TowerLevel (height + 1))
        (f1024TowerLevelX_ne_zero (height + 1)),
      f1024TowerPolarDivisor_apply_of_ne_zero
        (F1024TowerLevel height) (f1024TowerLevelX_ne_zero height),
      if_pos hupperSwitch, if_pos hswitch, hupperOrder, hlowerOrder]
  · have hupperNotSwitch : ¬(
        0 < Q.order (f1024TowerLevelHistoricalX (height + 1) (i : ℕ)) ∧
          Q.order
              (f1024TowerLevelHistoricalX (height + 1) ((i : ℕ) + 1)) < 0) := by
      intro hupperSwitch
      apply hswitch
      constructor <;> nlinarith
    simp only [f1024TowerLevelPoleStratum, Finsupp.filter_apply,
      if_neg hupperNotSwitch, if_neg hswitch]

private noncomputable def f1024TowerLevelCanonicalDivisorCandidate
    (height : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) :=
  ((32 : ℤ) ^ (height + 1) - 34) •
      f1024TowerLevelBasePoleDivisor height +
    ∑ i : Fin ((height + 1) / 2),
      (34 * ((32 : ℤ) ^ (height - (2 * (i : ℕ) + 1)) - 1)) •
        f1024TowerLevelPoleStratum height ⟨i, by omega⟩

private theorem
    f1024TowerLevelResidualPoleDivisor_components_zero_of_apply_eq_zero
    (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))
    (hzero : f1024TowerLevelResidualPoleDivisor height P = 0) :
    f1024TowerLevelBasePoleDivisor height P = 0 ∧
      ∀ i : Fin ((height + 1) / 2),
        f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P = 0 := by
  classical
  have hbaseNonnegative :=
    f1024TowerLevelBasePoleDivisor_apply_nonnegative height P
  have htermNonnegative : ∀ i : Fin ((height + 1) / 2),
      0 ≤ f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P :=
    fun i => f1024TowerLevelPoleStratum_apply_nonnegative
      height ⟨i, by omega⟩ P
  have hsumNonnegative :
      0 ≤ ∑ i : Fin ((height + 1) / 2),
        f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P :=
    Finset.sum_nonneg fun i _ => htermNonnegative i
  rw [f1024TowerLevelResidualPoleDivisor, Finsupp.add_apply,
    f1024TowerLevel_divisor_fintypeSum_apply] at hzero
  have hbaseZero : f1024TowerLevelBasePoleDivisor height P = 0 := by
    omega
  constructor
  · exact hbaseZero
  · intro i
    have htermLe :
        f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P ≤
          ∑ j : Fin ((height + 1) / 2),
            f1024TowerLevelPoleStratum height ⟨j, by omega⟩ P := by
      exact Finset.single_le_sum
        (fun j _ => htermNonnegative j) (Finset.mem_univ i)
    have hsumZero :
        (∑ j : Fin ((height + 1) / 2),
          f1024TowerLevelPoleStratum height ⟨j, by omega⟩ P) = 0 := by
      omega
    rw [hsumZero] at htermLe
    exact le_antisymm htermLe (htermNonnegative i)

private theorem f1024TowerLevelCanonicalDivisorCandidate_apply_eq_zero
    (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))
    (hzero : f1024TowerLevelResidualPoleDivisor height P = 0) :
    f1024TowerLevelCanonicalDivisorCandidate height P = 0 := by
  classical
  obtain ⟨hbaseZero, hstratumZero⟩ :=
    f1024TowerLevelResidualPoleDivisor_components_zero_of_apply_eq_zero
      height P hzero
  rw [f1024TowerLevelCanonicalDivisorCandidate, Finsupp.add_apply,
    Finsupp.smul_apply, f1024TowerLevel_divisor_fintypeSum_apply]
  simp only [hbaseZero, smul_eq_mul, mul_zero, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finsupp.smul_apply, hstratumZero i, smul_eq_mul, mul_zero]

private theorem f1024TowerLevelCanonicalDivisorCandidate_absorbs_residual
    (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) :
    f1024TowerLevelResidualPoleDivisor height P *
        f1024TowerLevelCanonicalDivisorCandidate height P =
      f1024TowerLevelCanonicalDivisorCandidate height P := by
  by_cases hzero : f1024TowerLevelResidualPoleDivisor height P = 0
  · rw [hzero, zero_mul,
      f1024TowerLevelCanonicalDivisorCandidate_apply_eq_zero height P hzero]
  · rw [f1024TowerLevelResidualPoleDivisor_apply_eq_one_of_ne_zero
      height P hzero, one_mul]

private theorem f1024TowerLevelCanonicalBaseCoefficient_step
    (height : ℕ) :
    (32 : ℤ) ^ (height + 2) - 34 =
      32 * ((32 : ℤ) ^ (height + 1) - 34) + 1054 := by
  rw [show height + 2 = (height + 1) + 1 by omega, pow_succ]
  ring

private theorem f1024TowerLevelCanonicalStratumCoefficient_step
    (height i : ℕ) (hi : 2 * i + 1 ≤ height) :
    34 * ((32 : ℤ) ^ (height + 1 - (2 * i + 1)) - 1) =
      32 * (34 * ((32 : ℤ) ^ (height - (2 * i + 1)) - 1)) + 1054 := by
  have hexponent :
      height + 1 - (2 * i + 1) = height - (2 * i + 1) + 1 := by
    omega
  rw [hexponent, pow_succ]
  ring

private theorem f1024TowerLevelCanonicalDivisorCandidate_step_linear
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1))) :
    f1024TowerLevelCanonicalDivisorCandidate (height + 1) Q =
      32 * f1024TowerLevelCanonicalDivisorCandidate height
          (f1024Tower_restrictedGlobalPlace
            (k := F1024) (K := F1024TowerLevel height)
            (L := F1024TowerLevel (height + 1)) Q) +
        1054 * f1024TowerLevelResidualPoleDivisor height
          (f1024Tower_restrictedGlobalPlace
            (k := F1024) (K := F1024TowerLevel height)
            (L := F1024TowerLevel (height + 1)) Q) := by
  classical
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) :=
    f1024Tower_restrictedGlobalPlace
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  change f1024TowerLevelCanonicalDivisorCandidate (height + 1) Q =
    32 * f1024TowerLevelCanonicalDivisorCandidate height P +
      1054 * f1024TowerLevelResidualPoleDivisor height P
  obtain ⟨r, heven | hodd⟩ := Nat.even_or_odd' height
  · subst height
    rw [f1024TowerLevelCanonicalDivisorCandidate,
      f1024TowerLevelCanonicalDivisorCandidate,
      f1024TowerLevelResidualPoleDivisor,
      Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.smul_apply]
    simp_rw [f1024TowerLevel_divisor_fintypeSum_apply]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    rw [f1024TowerLevelBasePoleDivisor_step_apply (2 * r) Q]
    have hcard : (2 * r + 1 + 1) / 2 = (2 * r + 1) / 2 + 1 := by
      omega
    have hupperReindex :
        (∑ i : Fin ((2 * r + 1 + 1) / 2),
            34 * ((32 : ℤ) ^ (2 * r + 1 - (2 * (i : ℕ) + 1)) - 1) *
              f1024TowerLevelPoleStratum (2 * r + 1) ⟨i, by omega⟩ Q) =
          ∑ i : Fin ((2 * r + 1) / 2 + 1),
            34 * ((32 : ℤ) ^ (2 * r + 1 - (2 * (i : ℕ) + 1)) - 1) *
              f1024TowerLevelPoleStratum (2 * r + 1) ⟨i, by omega⟩ Q := by
      apply Fintype.sum_equiv (finCongr hcard)
      intro i
      rfl
    rw [hupperReindex]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hlastCoefficient :
        34 * ((32 : ℤ) ^
          (2 * r + 1 - (2 * ((2 * r + 1) / 2) + 1)) - 1) = 0 := by
      have hindex : 2 * ((2 * r + 1) / 2) + 1 = 2 * r + 1 := by omega
      rw [hindex]
      norm_num
    rw [hlastCoefficient, zero_mul, add_zero]
    have hterms :
        (∑ i : Fin ((2 * r + 1) / 2),
            34 * ((32 : ℤ) ^ (2 * r + 1 - (2 * (i : ℕ) + 1)) - 1) *
              f1024TowerLevelPoleStratum (2 * r + 1) ⟨i, by omega⟩ Q) =
          ∑ i : Fin ((2 * r + 1) / 2),
            (32 *
                (34 * ((32 : ℤ) ^ (2 * r - (2 * (i : ℕ) + 1)) - 1) *
                  f1024TowerLevelPoleStratum (2 * r) ⟨i, by omega⟩ P) +
              1054 * f1024TowerLevelPoleStratum (2 * r) ⟨i, by omega⟩ P) := by
      apply Fintype.sum_congr
      intro i
      have hstratum :
          f1024TowerLevelPoleStratum (2 * r + 1) ⟨i, by omega⟩ Q =
            f1024TowerLevelPoleStratum (2 * r) ⟨i, by omega⟩ P := by
        let j : Fin ((2 * r + 1) / 2) := ⟨i, by omega⟩
        have h := f1024TowerLevelPoleStratum_step_apply (2 * r) j Q
        change f1024TowerLevelPoleStratum (2 * r + 1) ⟨i, by omega⟩ Q =
          f1024TowerLevelPoleStratum (2 * r) ⟨i, by omega⟩ P at h
        exact h
      rw [hstratum,
        f1024TowerLevelCanonicalStratumCoefficient_step
          (2 * r) (i : ℕ) (by omega)]
      ring
    rw [hterms, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum,
      f1024TowerLevelCanonicalBaseCoefficient_step]
    ring
  · subst height
    rw [f1024TowerLevelCanonicalDivisorCandidate,
      f1024TowerLevelCanonicalDivisorCandidate,
      f1024TowerLevelResidualPoleDivisor,
      Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.smul_apply]
    simp_rw [f1024TowerLevel_divisor_fintypeSum_apply]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    rw [f1024TowerLevelBasePoleDivisor_step_apply (2 * r + 1) Q]
    have hcard :
        (2 * r + 1 + 1 + 1) / 2 = (2 * r + 1 + 1) / 2 := by
      omega
    have hupperReindex :
        (∑ i : Fin ((2 * r + 1 + 1 + 1) / 2),
            34 * ((32 : ℤ) ^ (2 * r + 1 + 1 - (2 * (i : ℕ) + 1)) - 1) *
              f1024TowerLevelPoleStratum (2 * r + 1 + 1)
                ⟨i, by omega⟩ Q) =
          ∑ i : Fin ((2 * r + 1 + 1) / 2),
            34 * ((32 : ℤ) ^ (2 * r + 1 + 1 - (2 * (i : ℕ) + 1)) - 1) *
              f1024TowerLevelPoleStratum (2 * r + 1 + 1)
                ⟨i, by omega⟩ Q := by
      apply Fintype.sum_equiv (finCongr hcard)
      intro i
      rfl
    rw [hupperReindex]
    have hterms :
        (∑ i : Fin ((2 * r + 1 + 1) / 2),
            34 * ((32 : ℤ) ^ (2 * r + 1 + 1 - (2 * (i : ℕ) + 1)) - 1) *
              f1024TowerLevelPoleStratum (2 * r + 1 + 1)
                ⟨i, by omega⟩ Q) =
          ∑ i : Fin ((2 * r + 1 + 1) / 2),
            (32 *
                (34 * ((32 : ℤ) ^ (2 * r + 1 - (2 * (i : ℕ) + 1)) - 1) *
                  f1024TowerLevelPoleStratum (2 * r + 1)
                    ⟨i, by omega⟩ P) +
              1054 * f1024TowerLevelPoleStratum (2 * r + 1)
                ⟨i, by omega⟩ P) := by
      apply Fintype.sum_congr
      intro i
      have hstratum :
          f1024TowerLevelPoleStratum (2 * r + 1 + 1)
              ⟨i, by omega⟩ Q =
            f1024TowerLevelPoleStratum (2 * r + 1)
              ⟨i, by omega⟩ P := by
        let j : Fin ((2 * r + 1 + 1) / 2) := ⟨i, by omega⟩
        have h := f1024TowerLevelPoleStratum_step_apply (2 * r + 1) j Q
        change f1024TowerLevelPoleStratum (2 * r + 1 + 1)
            ⟨i, by omega⟩ Q =
          f1024TowerLevelPoleStratum (2 * r + 1)
            ⟨i, by omega⟩ P at h
        exact h
      rw [hstratum,
        f1024TowerLevelCanonicalStratumCoefficient_step
          (2 * r + 1) (i : ℕ) (by omega)]
      ring
    rw [hterms, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum,
      f1024TowerLevelCanonicalBaseCoefficient_step]
    ring

private theorem f1024TowerLevelCanonicalDivisorCandidate_step
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1))) :
    f1024TowerLevelCanonicalDivisorCandidate (height + 1) Q =
      (1 + 31 *
          f1024TowerLevelResidualPoleDivisor height
            (f1024Tower_restrictedGlobalPlace
              (k := F1024) (K := F1024TowerLevel height)
              (L := F1024TowerLevel (height + 1)) Q)) *
        f1024TowerLevelCanonicalDivisorCandidate height
          (f1024Tower_restrictedGlobalPlace
            (k := F1024) (K := F1024TowerLevel height)
            (L := F1024TowerLevel (height + 1)) Q) +
      1054 * f1024TowerLevelResidualPoleDivisor height
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q) := by
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) :=
    f1024Tower_restrictedGlobalPlace
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  have hlinear :=
    f1024TowerLevelCanonicalDivisorCandidate_step_linear height Q
  have habsorb :=
    f1024TowerLevelCanonicalDivisorCandidate_absorbs_residual height P
  change f1024TowerLevelCanonicalDivisorCandidate (height + 1) Q =
      (1 + 31 * f1024TowerLevelResidualPoleDivisor height P) *
          f1024TowerLevelCanonicalDivisorCandidate height P +
        1054 * f1024TowerLevelResidualPoleDivisor height P
  change f1024TowerLevelCanonicalDivisorCandidate (height + 1) Q =
      32 * f1024TowerLevelCanonicalDivisorCandidate height P +
        1054 * f1024TowerLevelResidualPoleDivisor height P at hlinear
  rw [hlinear]
  rw [add_mul, one_mul]
  nlinarith [habsorb]

private theorem
    f1024Tower_logarithmicDifferential_ne_zero_of_order_eq_one_or_neg_one
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k F) (f : F)
    (hf : f ≠ 0) (horder : P.order f = 1 ∨ P.order f = -1) :
    QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferential
        (k := k) (F := F) f ≠ 0 := by
  intro hzero
  have hresidue :=
    QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_logarithmicDifferential
      (k := k) (F := F) P f hf
  have hsubtype :
      QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferentialAtSimplePole
          (k := k) (F := F) P f hf = 0 := by
    apply Subtype.ext
    exact hzero
  rw [hsubtype, map_zero] at hresidue
  rcases horder with horder | horder <;> rw [horder] at hresidue <;>
    norm_num at hresidue

private theorem
    f1024Tower_differentialOrder_logarithmic_eq_neg_one_of_order_eq_one_or_neg_one
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k F) (f : F)
    (hf : f ≠ 0) (horder : P.order f = 1 ∨ P.order f = -1) :
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
        (k := k) (F := F) P
        (QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferential
          (k := k) (F := F) f)
        (f1024Tower_logarithmicDifferential_ne_zero_of_order_eq_one_or_neg_one
          P f hf horder) = -1 := by
  let omega :=
    QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferential
      (k := k) (F := F) f
  let homega : omega ≠ 0 :=
    f1024Tower_logarithmicDifferential_ne_zero_of_order_eq_one_or_neg_one
      P f hf horder
  change QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
      (k := k) (F := F) P omega homega = -1
  have hsimple : omega ∈
      QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferentialLattice P :=
    QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferential_isGlobalSimplePole
      (k := k) (F := F) f hf P
  have hresidue_ne :
      QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue
          (k := k) (F := F) P
          (QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferentialAtSimplePole
            (k := k) (F := F) P f hf) ≠ 0 := by
    rw [QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_logarithmicDifferential]
    rcases horder with horder | horder <;> rw [horder] <;> norm_num
  have hnotRegular : omega ∉
      QEC.Coding.AlgebraicGeometry.Differential.localDifferentialLattice P := by
    intro hregular
    apply hresidue_ne
    exact
      QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
        (k := k) (F := F) P
        (QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferentialAtSimplePole
          (k := k) (F := F) P f hf) hregular
  have hge : -1 ≤
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
        (k := k) (F := F) P omega homega :=
    (QEC.Coding.AlgebraicGeometry.Differential.mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
      (k := k) (F := F) P omega homega).mp hsimple
  have hnge : ¬ 0 ≤
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
        (k := k) (F := F) P omega homega := by
    intro hnonnegative
    apply hnotRegular
    exact
      (QEC.Coding.AlgebraicGeometry.Differential.mem_localDifferentialLattice_iff_differentialOrder_nonnegative
        (k := k) (F := F) P omega homega).mpr hnonnegative
  apply le_antisymm
  · exact Int.le_sub_one_iff.mpr (lt_of_not_ge hnge)
  · exact hge

private theorem
    f1024Tower_differentialGeneratorOrder_eq_order_sub_one_sub_derivative
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k F) (f : F)
    (hf : f ≠ 0) (horder : P.order f = 1 ∨ P.order f = -1) :
    ∃ hderivative :
        functionFieldDerivation (k := k) (F := F) f ≠ 0,
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
          (k := k) (F := F) P
          (functionFieldDifferentialGenerator (k := k) (F := F))
          (functionFieldDifferentialGenerator_ne_zero (k := k) (F := F)) =
        P.order f - 1 -
          P.order (functionFieldDerivation (k := k) (F := F) f) := by
  let omega :=
    QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferential
      (k := k) (F := F) f
  let homega : omega ≠ 0 :=
    f1024Tower_logarithmicDifferential_ne_zero_of_order_eq_one_or_neg_one
      P f hf horder
  have hlogOrder :
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
          (k := k) (F := F) P omega homega = -1 := by
    simpa only [omega, homega] using
      f1024Tower_differentialOrder_logarithmic_eq_neg_one_of_order_eq_one_or_neg_one
        P f hf horder
  have hcoordinate :
      functionFieldDifferentialCoordinate (k := k) (F := F) omega ≠ 0 :=
    (functionFieldDifferentialCoordinate_ne_zero_iff
      (k := k) (F := F) omega).mpr homega
  have hcoordinateEq :
      functionFieldDifferentialCoordinate (k := k) (F := F) omega =
        f⁻¹ * functionFieldDerivation (k := k) (F := F) f := by
    dsimp only [omega]
    rw [QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferential,
      map_smul, functionFieldDifferentialCoordinate_differential]
    rfl
  have hderivative :
      functionFieldDerivation (k := k) (F := F) f ≠ 0 := by
    intro hzero
    apply hcoordinate
    rw [hcoordinateEq, hzero, mul_zero]
  refine ⟨hderivative, ?_⟩
  have hcutoff :=
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff
      (k := k) (F := F) P
  rw [QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder_eq_coordinate_sub_generatorOrder
      (k := k) (F := F) P omega homega hcutoff] at hlogOrder
  rw [hcoordinateEq,
    QEC.Coding.AlgebraicGeometry.GlobalPlace.order_mul P
      (inv_ne_zero hf) hderivative,
    QEC.Coding.AlgebraicGeometry.GlobalPlace.order_inv] at hlogOrder
  have hone : P.order (1 : F) = 0 := by
    simpa using P.order_algebraMap (1 : k) one_ne_zero
  rw [QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder_eq_coordinate_sub_generatorOrder
      (k := k) (F := F) P
      (functionFieldDifferentialGenerator (k := k) (F := F))
      (functionFieldDifferentialGenerator_ne_zero (k := k) (F := F)) hcutoff,
    functionFieldDifferentialCoordinate_generator, hone]
  omega

private theorem
    f1024TowerLevelCoordinateDivisor_functionFieldDerivation_stepEmbedding
    (height : ℕ) (u : F1024TowerLevel height) :
    functionFieldDerivation (k := F1024)
        (F := F1024TowerLevel (height + 1))
        (algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1)) u) =
      algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1))
        (functionFieldDerivation (k := F1024)
          (F := F1024TowerLevel height) u) := by
  let Dupper : Derivation F1024 (F1024TowerLevel (height + 1))
      (F1024TowerLevel (height + 1)) :=
    functionFieldDerivation (k := F1024)
      (F := F1024TowerLevel (height + 1))
  let Dlower : Derivation F1024 (F1024TowerLevel height)
      (F1024TowerLevel height) :=
    functionFieldDerivation (k := F1024)
      (F := F1024TowerLevel height)
  let Drestricted : Derivation F1024 (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) :=
    Dupper.compAlgebraMap (F1024TowerLevel height)
  let Dtransported : Derivation F1024 (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) :=
    (Algebra.ofId (F1024TowerLevel height)
      (F1024TowerLevel (height + 1))).toLinearMap.compDer Dlower
  have hderivation : Drestricted = Dtransported := by
    apply QEC.Coding.AlgebraicGeometry.SeparableDerivationExtension.extension_unique
    apply (QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv
      (k := F1024) (M := F1024TowerLevel (height + 1))).injective
    change
      Dupper (algebraMap (RatFunc F1024)
          (F1024TowerLevel (height + 1)) RatFunc.X) =
        algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1))
          (Dlower (algebraMap (RatFunc F1024)
            (F1024TowerLevel height) RatFunc.X))
    rw [functionFieldDerivation_apply_X,
      functionFieldDerivation_apply_X, map_one]
  have hu := Derivation.congr_fun hderivation u
  change
    Dupper (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1)) u) =
      algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1)) (Dlower u) at hu
  simpa only [Dupper, Dlower] using hu

private theorem
    f1024TowerLevelCoordinateDivisor_functionFieldDerivation_x_succ
    (height : ℕ) :
    functionFieldDerivation (k := F1024)
        (F := F1024TowerLevel (height + 1))
        (f1024TowerLevelX (height + 1)) =
      algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1))
          (functionFieldDerivation (k := F1024)
            (F := F1024TowerLevel height)
            (f1024TowerLevelX height)) *
        algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1))
          (f1024TowerLevelX height) ^ 30 *
        f1024TowerLevelX (height + 1) ^ 32 := by
  let D : Derivation F1024 (F1024TowerLevel (height + 1))
      (F1024TowerLevel (height + 1)) :=
    functionFieldDerivation (k := F1024)
      (F := F1024TowerLevel (height + 1))
  let x : F1024TowerLevel (height + 1) :=
    algebraMap (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) (f1024TowerLevelX height)
  let z : F1024TowerLevel (height + 1) := f1024TowerLevelZ height
  let dx : F1024TowerLevel (height + 1) :=
    algebraMap (F1024TowerLevel height)
      (F1024TowerLevel (height + 1))
      (functionFieldDerivation (k := F1024)
        (F := F1024TowerLevel height) (f1024TowerLevelX height))
  have hx_ne : x ≠ 0 := by
    exact (map_ne_zero_iff
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1)))
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1))).injective).mpr
          (f1024TowerLevelX_ne_zero height)
  have hnext : f1024TowerLevelX (height + 1) = z / x := by
    apply (eq_div_iff hx_ne).mpr
    simpa only [x, z, mul_comm] using
      f1024TowerLevel_X_mul_nextX height
  have hzDerivative : D z = x ^ 32 * dx := by
    let Dstage : Derivation F1024 (F1024TowerLevel (height + 1))
        (F1024TowerLevel (height + 1)) :=
      functionFieldDerivation (k := F1024)
        (F := F1024TowerLevel (height + 1))
    have hequation : z ^ 32 + z = x ^ 33 := by
      simpa only [x, z, map_pow] using
        f1024TowerLevel_step_equation height
    have hderivative := congrArg Dstage hequation
    rw [map_add, Derivation.leibniz_pow,
      Derivation.leibniz_pow] at hderivative
    simp only [nsmul_eq_mul] at hderivative
    have h32 : ((32 : ℕ) : F1024TowerLevel (height + 1)) = 0 := by
      rw [CharP.cast_eq_zero_iff (F1024TowerLevel (height + 1)) 2]
      norm_num
    have h33 : ((33 : ℕ) : F1024TowerLevel (height + 1)) = 1 := by
      rw [show (33 : ℕ) = 32 + 1 by norm_num, Nat.cast_add, h32]
      simp
    simp only [h32, h33, Nat.reduceSub, zero_mul, zero_add, one_mul]
      at hderivative
    rw [f1024TowerLevelCoordinateDivisor_functionFieldDerivation_stepEmbedding]
      at hderivative
    have hport := hderivative
    simp only [D, Dstage, x, z, dx, zero_mul, zero_add, one_mul, smul_eq_mul] at hport ⊢
    exact hport
  have hxDerivative : D x = dx := by
    simpa only [D, x, dx] using
      f1024TowerLevelCoordinateDivisor_functionFieldDerivation_stepEmbedding
        height (f1024TowerLevelX height)
  have hequation : z ^ 32 + z = x ^ 33 := by
    simpa only [x, z, map_pow] using
      f1024TowerLevel_step_equation height
  rw [hnext]
  change D (z / x) = dx * x ^ 30 * (z / x) ^ 32
  rw [Derivation.leibniz_div, hzDerivative, hxDerivative]
  simp only [smul_eq_mul]
  field_simp [hx_ne]
  linear_combination -dx * hequation

private noncomputable def f1024TowerLevelCanonicalOrder
    (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) : ℤ :=
  QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
    (k := F1024) (F := F1024TowerLevel height) P
    (functionFieldDifferentialGenerator
      (k := F1024) (F := F1024TowerLevel height))
    (functionFieldDifferentialGenerator_ne_zero
      (k := F1024) (F := F1024TowerLevel height))

private theorem
    f1024TowerLevelCoordinateDivisor_functionFieldDerivation_polynomial
    (b : F1024[X]) :
    functionFieldDerivation (k := F1024) (F := F1024TowerLevel 0)
        (algebraMap F1024[X] (F1024TowerLevel 0) b) =
      algebraMap F1024[X] (F1024TowerLevel 0) b.derivative := by
  have h_aeval (c : F1024[X]) :
      Polynomial.aeval
          (algebraMap (RatFunc F1024) (F1024TowerLevel 0) RatFunc.X) c =
        algebraMap (RatFunc F1024) (F1024TowerLevel 0)
          (Polynomial.aeval RatFunc.X c) := by
    simpa only [IsScalarTower.toAlgHom_apply] using
      (Polynomial.aeval_algHom_apply
        (IsScalarTower.toAlgHom F1024 (RatFunc F1024)
          (F1024TowerLevel 0)) RatFunc.X c)
  rw [IsScalarTower.algebraMap_apply F1024[X] (RatFunc F1024)
      (F1024TowerLevel 0) b,
    IsScalarTower.algebraMap_apply F1024[X] (RatFunc F1024)
      (F1024TowerLevel 0) b.derivative]
  calc
    functionFieldDerivation (k := F1024) (F := F1024TowerLevel 0)
        (algebraMap (RatFunc F1024) (F1024TowerLevel 0)
          (algebraMap F1024[X] (RatFunc F1024) b)) =
      functionFieldDerivation (k := F1024) (F := F1024TowerLevel 0)
        (algebraMap (RatFunc F1024) (F1024TowerLevel 0)
          (Polynomial.aeval RatFunc.X b)) := by
            rw [RatFunc.aeval_X_left_eq_algebraMap]
    _ = functionFieldDerivation (k := F1024) (F := F1024TowerLevel 0)
        (Polynomial.aeval
          (algebraMap (RatFunc F1024) (F1024TowerLevel 0) RatFunc.X) b) := by
            rw [h_aeval]
    _ = Polynomial.aeval
        (algebraMap (RatFunc F1024) (F1024TowerLevel 0) RatFunc.X)
        b.derivative := by
          rw [Derivation.map_aeval, functionFieldDerivation_apply_X]
          simp only [smul_eq_mul, mul_one]
    _ = algebraMap (RatFunc F1024) (F1024TowerLevel 0)
        (Polynomial.aeval RatFunc.X b.derivative) := h_aeval b.derivative
    _ = algebraMap (RatFunc F1024) (F1024TowerLevel 0)
        (algebraMap F1024[X] (RatFunc F1024) b.derivative) := by
          rw [RatFunc.aeval_X_left_eq_algebraMap]

private theorem f1024TowerLevelCanonicalOrder_zero
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel 0)) :
    f1024TowerLevelCanonicalOrder 0 P =
      -2 * f1024TowerLevelBasePoleDivisor 0 P := by
  classical
  let Pstandard :
      @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 (RatFunc F1024)
        _ _ _ (f1024TowerStage 0).constantAlgebraInst :=
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.mk
      F1024 (RatFunc F1024) _ _ _
      (f1024TowerStage 0).constantAlgebraInst
      (@QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation
        F1024 (F1024TowerLevel 0) _ _ _
        (f1024TowerLevelCoordinateDivisorAlgebra 0) P)
      (@QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized
        F1024 (F1024TowerLevel 0) _ _ _
        (f1024TowerLevelCoordinateDivisorAlgebra 0) P)
  let standardOrder
      (R : @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 (RatFunc F1024)
        _ _ _ (f1024TowerStage 0).constantAlgebraInst)
      (f : RatFunc F1024) : ℤ :=
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.order
      F1024 (RatFunc F1024) _ _ _
      (f1024TowerStage 0).constantAlgebraInst R f
  have horder (f : RatFunc F1024) :
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order
          F1024 (F1024TowerLevel 0) _ _ _
          (f1024TowerLevelCoordinateDivisorAlgebra 0) P f =
        standardOrder Pstandard f := rfl
  have hlevelX :
      f1024TowerLevelX 0 = (RatFunc.X : RatFunc F1024) := rfl
  obtain ⟨place, hplace⟩ :=
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv
      (k := F1024)).surjective Pstandard
  cases place with
  | none =>
      rw [QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none]
        at hplace
      have hinfinityOrder :
          standardOrder
              (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalInfinity F1024)
              (RatFunc.X : RatFunc F1024) = -1 := by
        dsimp only [standardOrder]
        unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order
          QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalInfinity
        change -WithZero.log
            (RatFunc.inftyValuation F1024 (RatFunc.X : RatFunc F1024)) = -1
        rw [RatFunc.inftyValuation.X]
        simp
      have hXOrder : P.order (RatFunc.X : RatFunc F1024) = -1 := by
        calc
          P.order (RatFunc.X : RatFunc F1024) =
              standardOrder Pstandard (RatFunc.X : RatFunc F1024) := horder _
          _ = standardOrder
              (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalInfinity F1024)
              (RatFunc.X : RatFunc F1024) := by rw [hplace]
          _ = -1 := hinfinityOrder
      obtain ⟨_, hcanonical⟩ :=
        f1024Tower_differentialGeneratorOrder_eq_order_sub_one_sub_derivative
          P (RatFunc.X : RatFunc F1024) RatFunc.X_ne_zero (Or.inr hXOrder)
      have hDX : functionFieldDerivation
          (k := F1024) (F := F1024TowerLevel 0) RatFunc.X = 1 := by
        have hport := (functionFieldDerivation_apply_X
          (k := F1024) (F := F1024TowerLevel 0))
        exact hport
      have hone : P.order (1 : F1024TowerLevel 0) = 0 := by
        simpa using P.order_algebraMap (1 : F1024) one_ne_zero
      rw [hXOrder, hDX, hone] at hcanonical
      norm_num at hcanonical
      have hbasePole : f1024TowerLevelBasePoleDivisor 0 P = 1 := by
        simp only [f1024TowerLevelBasePoleDivisor, Finsupp.filter_apply,
          f1024TowerLevelHistoricalX_current, hlevelX, hXOrder,
          if_pos (by omega)]
        rw [f1024TowerPolarDivisor_apply_of_ne_zero
          (F1024TowerLevel 0) RatFunc.X_ne_zero, hXOrder]
        norm_num
      unfold f1024TowerLevelCanonicalOrder
      rw [hcanonical, hbasePole]
      norm_num
  | some p =>
      rw [QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some]
        at hplace
      let q : RatFunc F1024 := algebraMap F1024[X] (RatFunc F1024)
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial p)
      let q' : RatFunc F1024 := algebraMap F1024[X] (RatFunc F1024)
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial p).derivative
      have hq : q ≠ 0 := RatFunc.algebraMap_ne_zero
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial_irreducible
          p).ne_zero
      have hqDerivative :
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial
            p).derivative ≠ 0 := by
        exact (Polynomial.separable_iff_derivative_ne_zero
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial_irreducible
            p)).mp
          (PerfectField.separable_of_irreducible
            (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial_irreducible
              p))
      have hq' : q' ≠ 0 := RatFunc.algebraMap_ne_zero hqDerivative
      have hqOrderStandard :
          standardOrder
              (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic p) q = 1 := by
        dsimp only [standardOrder]
        unfold q QEC.Coding.AlgebraicGeometry.GlobalPlace.order
          QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic
        change -WithZero.log
            ((p.valuation (RatFunc F1024))
              (algebraMap F1024[X] (RatFunc F1024)
                (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial
                  p))) = 1
        rw [p.valuation_of_algebraMap,
          p.intValuation_singleton
            (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial_irreducible
              p).ne_zero
            (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic_asIdeal_eq_span p)]
        simp
      have hqDerivativeNotMem :
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial
            p).derivative ∉ p.asIdeal := by
        rw [QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic_asIdeal_eq_span p,
          Ideal.mem_span_singleton, Polynomial.dvd_derivative_iff]
        exact hqDerivative
      have hq'OrderStandard :
          standardOrder
              (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic p) q' = 0 := by
        dsimp only [standardOrder]
        have hvaluation :
            (p.valuation (RatFunc F1024))
              (algebraMap F1024[X] (RatFunc F1024)
                (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial
                  p).derivative) = 1 :=
          (p.valuation_eq_one_iff_notMem (K := RatFunc F1024)).mpr
            hqDerivativeNotMem
        unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order
          QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic
        change -WithZero.log
            ((p.valuation (RatFunc F1024))
              (algebraMap F1024[X] (RatFunc F1024)
                (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial
                  p).derivative)) = 0
        rw [hvaluation]
        simp
      have hqOrder : P.order q = 1 := by
        calc
          P.order q = standardOrder Pstandard q := horder q
          _ = standardOrder
              (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic p) q := by
            rw [hplace]
          _ = 1 := hqOrderStandard
      have hq'Order : P.order q' = 0 := by
        calc
          P.order q' = standardOrder Pstandard q' := horder q'
          _ = standardOrder
              (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic p) q' := by
            rw [hplace]
          _ = 0 := hq'OrderStandard
      obtain ⟨_, hcanonical⟩ :=
        f1024Tower_differentialGeneratorOrder_eq_order_sub_one_sub_derivative
          P q hq (Or.inl hqOrder)
      have hDq : functionFieldDerivation
          (k := F1024) (F := F1024TowerLevel 0) q = q' := by
        have hport := f1024TowerLevelCoordinateDivisor_functionFieldDerivation_polynomial
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial p)
        simp only [q, q'] at hport ⊢
        exact hport
      rw [hqOrder, hDq, hq'Order] at hcanonical
      norm_num at hcanonical
      have hXValuation :
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic p).valuation
              (RatFunc.X : RatFunc F1024) ≤ 1 := by
        change (p.valuation (RatFunc F1024))
            (algebraMap F1024[X] (RatFunc F1024) Polynomial.X) ≤ 1
        rw [p.valuation_of_algebraMap]
        exact p.intValuation_le_one Polynomial.X
      have hXOrderStandard : 0 ≤
          standardOrder
            (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic p)
            (RatFunc.X : RatFunc F1024) := by
        exact (@QEC.Coding.AlgebraicGeometry.GlobalPlace.regularAt_iff_order_nonnegative
          F1024 (RatFunc F1024) _ _ _
          (f1024TowerStage 0).constantAlgebraInst
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic p)
          (RatFunc.X : RatFunc F1024) RatFunc.X_ne_zero).mp hXValuation
      have hXOrder : 0 ≤ P.order (RatFunc.X : RatFunc F1024) := by
        calc
          0 ≤ standardOrder
              (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic p)
              (RatFunc.X : RatFunc F1024) := hXOrderStandard
          _ = standardOrder Pstandard (RatFunc.X : RatFunc F1024) := by rw [hplace]
          _ = P.order (RatFunc.X : RatFunc F1024) := (horder _).symm
      have hbasePole : f1024TowerLevelBasePoleDivisor 0 P = 0 := by
        simp only [f1024TowerLevelBasePoleDivisor, Finsupp.filter_apply,
          f1024TowerLevelHistoricalX_current, hlevelX,
          if_neg (not_lt.mpr hXOrder)]
      unfold f1024TowerLevelCanonicalOrder
      rw [hcanonical, hbasePole]
      norm_num

private theorem f1024TowerLevelCanonicalOrder_step_eq_of_order_scale_one
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1)))
    (hscale : ∀ u : F1024TowerLevel height, u ≠ 0 →
      Q.order
          (algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)) u) =
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q).order u) :
    f1024TowerLevelCanonicalOrder (height + 1) Q =
      f1024TowerLevelCanonicalOrder height
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q) := by
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) :=
    f1024Tower_restrictedGlobalPlace
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  let pi : F1024TowerLevel height := P.uniformizer
  have hpi : pi ≠ 0 := by
    apply P.valuation.ne_zero_iff.mp
    change P.valuation P.uniformizer ≠ 0
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  have hpiOrder : P.order pi = 1 := P.order_uniformizer
  have hmapPi :
      algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1)) pi ≠ 0 :=
    (map_ne_zero_iff
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1)))
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1))).injective).mpr hpi
  have hmapPiOrder : Q.order
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1)) pi) = 1 := by
    rw [hscale pi hpi, hpiOrder]
  obtain ⟨hDpi, hLower⟩ :=
    f1024Tower_differentialGeneratorOrder_eq_order_sub_one_sub_derivative
      P pi hpi (Or.inl hpiOrder)
  obtain ⟨_, hUpper⟩ :=
    f1024Tower_differentialGeneratorOrder_eq_order_sub_one_sub_derivative
      Q
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1)) pi)
      hmapPi (Or.inl hmapPiOrder)
  have hDmap :=
    f1024TowerLevelCoordinateDivisor_functionFieldDerivation_stepEmbedding
      height pi
  have hDscale := hscale
    (functionFieldDerivation
      (k := F1024) (F := F1024TowerLevel height) pi) hDpi
  change Q.order
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1))
        (functionFieldDerivation
          (k := F1024) (F := F1024TowerLevel height) pi)) =
    P.order (functionFieldDerivation
      (k := F1024) (F := F1024TowerLevel height) pi) at hDscale
  change
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
        (k := F1024) (F := F1024TowerLevel (height + 1)) Q
        (functionFieldDifferentialGenerator
          (k := F1024) (F := F1024TowerLevel (height + 1)))
        (functionFieldDifferentialGenerator_ne_zero
          (k := F1024) (F := F1024TowerLevel (height + 1))) =
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
        (k := F1024) (F := F1024TowerLevel height) P
        (functionFieldDifferentialGenerator
          (k := F1024) (F := F1024TowerLevel height))
        (functionFieldDifferentialGenerator_ne_zero
          (k := F1024) (F := F1024TowerLevel height))
  rw [hpiOrder] at hLower
  rw [hmapPiOrder, hDmap, hDscale] at hUpper
  omega

private theorem f1024TowerLevelCanonicalOrder_step_eq_of_lowerX_eq_neg_one
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1)))
    (hpole :
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Q).order
          (f1024TowerLevelX height) = -1) :
    f1024TowerLevelCanonicalOrder (height + 1) Q =
      32 * f1024TowerLevelCanonicalOrder height
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q) + 1054 := by
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) :=
    f1024Tower_restrictedGlobalPlace
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  let x : F1024TowerLevel height := f1024TowerLevelX height
  let y : F1024TowerLevel (height + 1) :=
    f1024TowerLevelX (height + 1)
  have hx : x ≠ 0 := f1024TowerLevelX_ne_zero height
  have hy : y ≠ 0 := f1024TowerLevelX_ne_zero (height + 1)
  have hstep :=
    f1024TowerLevelCoordinateDivisor_step_order_scale_eq_32_of_lowerX_eq_neg_one
      height Q hpole
  have hyOrder : Q.order y = -1 := hstep.2
  obtain ⟨hDx, hLower⟩ :=
    f1024Tower_differentialGeneratorOrder_eq_order_sub_one_sub_derivative
      P x hx (Or.inr hpole)
  obtain ⟨hDy, hUpper⟩ :=
    f1024Tower_differentialGeneratorOrder_eq_order_sub_one_sub_derivative
      Q y hy (Or.inr hyOrder)
  have hmapDx :
      algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1))
          (functionFieldDerivation
            (k := F1024) (F := F1024TowerLevel height) x) ≠ 0 :=
    (map_ne_zero_iff
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1)))
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1))).injective).mpr hDx
  have hmapX : algebraMap (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) x ≠ 0 :=
    (map_ne_zero_iff
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1)))
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1))).injective).mpr hx
  have hDxScale := hstep.1
    (functionFieldDerivation
      (k := F1024) (F := F1024TowerLevel height) x) hDx
  have hXScale := hstep.1 x hx
  have hderivative :
      functionFieldDerivation
          (k := F1024) (F := F1024TowerLevel (height + 1)) y =
        algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1))
            (functionFieldDerivation
              (k := F1024) (F := F1024TowerLevel height) x) *
          algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)) x ^ 30 * y ^ 32 := by
    simpa only [x, y] using
      f1024TowerLevelCoordinateDivisor_functionFieldDerivation_x_succ height
  have hDyOrder :
      Q.order (functionFieldDerivation
        (k := F1024) (F := F1024TowerLevel (height + 1)) y) =
      32 * P.order (functionFieldDerivation
        (k := F1024) (F := F1024TowerLevel height) x) - 992 := by
    rw [hderivative,
      QEC.Coding.AlgebraicGeometry.GlobalPlace.order_mul Q
        (mul_ne_zero hmapDx (pow_ne_zero 30 hmapX)) (pow_ne_zero 32 hy),
      QEC.Coding.AlgebraicGeometry.GlobalPlace.order_mul Q
        hmapDx (pow_ne_zero 30 hmapX),
      f1024Tower_globalPlace_order_pow Q,
      f1024Tower_globalPlace_order_pow Q,
      hDxScale, hXScale, hpole, hyOrder]
    ring
  change
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
        (k := F1024) (F := F1024TowerLevel (height + 1)) Q
        (functionFieldDifferentialGenerator
          (k := F1024) (F := F1024TowerLevel (height + 1)))
        (functionFieldDifferentialGenerator_ne_zero
          (k := F1024) (F := F1024TowerLevel (height + 1))) =
      32 *
        QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
          (k := F1024) (F := F1024TowerLevel height) P
          (functionFieldDifferentialGenerator
            (k := F1024) (F := F1024TowerLevel height))
          (functionFieldDifferentialGenerator_ne_zero
            (k := F1024) (F := F1024TowerLevel height)) + 1054
  rw [hpole] at hLower
  rw [hyOrder, hDyOrder] at hUpper
  omega

private theorem
    f1024TowerLevel_step_order_eq_of_residualPoleDivisor_eq_zero
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1)))
    (hresidual :
      f1024TowerLevelResidualPoleDivisor height
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q) = 0) :
    ∀ u : F1024TowerLevel height, u ≠ 0 →
      Q.order
          (algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)) u) =
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q).order u := by
  classical
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) :=
    f1024Tower_restrictedGlobalPlace
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  by_cases hregular : 0 ≤ P.order (f1024TowerLevelX height)
  · exact
      f1024TowerLevelCoordinateDivisor_step_order_eq_of_lowerX_nonnegative
        height Q hregular
  · have hpole : P.order (f1024TowerLevelX height) < 0 :=
      lt_of_not_ge hregular
    have hpolarPositive : 0 <
        QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F1024TowerLevel height)
          (f1024TowerLevelX height) P := by
      rw [f1024TowerPolarDivisor_apply_of_ne_zero
        (F1024TowerLevel height) (f1024TowerLevelX_ne_zero height),
        max_eq_left (by omega : -P.order (f1024TowerLevelX height) ≥ 0)]
      omega
    have hpartition := congrArg (fun D :
        Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
          (F1024TowerLevel height)) => D P)
      (f1024TowerLevel_polarDivisor_partition height)
    simp only [Finsupp.add_apply] at hpartition
    rw [f1024TowerLevel_divisor_fintypeSum_apply] at hpartition
    have hbaseNonnegative :=
      f1024TowerLevelBasePoleDivisor_apply_nonnegative height P
    have hallNonnegative : ∀ i : Fin height,
        0 ≤ f1024TowerLevelPoleStratum height i P :=
      fun i => f1024TowerLevelPoleStratum_apply_nonnegative height i P
    have hlowNonnegative :
        0 ≤ ∑ i : Fin ((height + 1) / 2),
          f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P :=
      Finset.sum_nonneg fun i _ =>
        f1024TowerLevelPoleStratum_apply_nonnegative height
          ⟨i, by omega⟩ P
    change f1024TowerLevelResidualPoleDivisor height P = 0 at hresidual
    rw [f1024TowerLevelResidualPoleDivisor, Finsupp.add_apply,
      f1024TowerLevel_divisor_fintypeSum_apply] at hresidual
    have hbaseZero : f1024TowerLevelBasePoleDivisor height P = 0 := by
      omega
    have hlowZero :
        (∑ i : Fin ((height + 1) / 2),
          f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P) = 0 := by
      omega
    have hallPositive :
        0 < ∑ i : Fin height,
          f1024TowerLevelPoleStratum height i P := by
      rw [hpartition] at hpolarPositive
      omega
    obtain ⟨i, _, hiPositive⟩ :=
      (Finset.sum_pos_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin height)))
        (fun i _ => hallNonnegative i)).mp hallPositive
    have hhalfLe : (height + 1) / 2 ≤ height := by omega
    have hiOld : (height + 1) / 2 ≤ (i : ℕ) := by
      by_contra hnot
      have hiLow : (i : ℕ) < (height + 1) / 2 := by omega
      let j : Fin ((height + 1) / 2) := ⟨i, hiLow⟩
      have htermNonnegative :
          0 ≤ f1024TowerLevelPoleStratum height
            ⟨j, lt_of_lt_of_le j.isLt hhalfLe⟩ P :=
        f1024TowerLevelPoleStratum_apply_nonnegative height
          ⟨j, lt_of_lt_of_le j.isLt hhalfLe⟩ P
      have htermLe :
          f1024TowerLevelPoleStratum height
              ⟨j, lt_of_lt_of_le j.isLt hhalfLe⟩ P ≤
            ∑ a : Fin ((height + 1) / 2),
              f1024TowerLevelPoleStratum height ⟨a, by omega⟩ P := by
        exact Finset.single_le_sum
          (fun (a : Fin ((height + 1) / 2)) _ =>
            f1024TowerLevelPoleStratum_apply_nonnegative height
              ⟨(a : ℕ), lt_of_lt_of_le a.isLt hhalfLe⟩ P)
          (Finset.mem_univ j)
      have htermZero :
          f1024TowerLevelPoleStratum height
              ⟨j, lt_of_lt_of_le j.isLt hhalfLe⟩ P = 0 := by
        rw [hlowZero] at htermLe
        exact le_antisymm htermLe htermNonnegative
      have hij :
          (⟨j, lt_of_lt_of_le j.isLt hhalfLe⟩ : Fin height) = i :=
        Fin.ext (by rfl)
      rw [hij] at htermZero
      omega
    have hswitch :
        0 < P.order (f1024TowerLevelHistoricalX height (i : ℕ)) ∧
          P.order (f1024TowerLevelHistoricalX height ((i : ℕ) + 1)) < 0 := by
      by_contra hnot
      have hzero : f1024TowerLevelPoleStratum height i P = 0 := by
        simp only [f1024TowerLevelPoleStratum, Finsupp.filter_apply,
          if_neg hnot]
      rw [hzero] at hiPositive
      omega
    let d : ℕ := height - ((i : ℕ) + 1)
    have hd : d ≤ (i : ℕ) := by
      dsimp only [d]
      omega
    have hcurrent : (i : ℕ) + 1 + d = height := by
      dsimp only [d]
      omega
    have hprevious : 1 ≤ (i : ℕ) - d := by
      dsimp only [d]
      omega
    exact f1024TowerLevel_step_order_eq_of_old_switch
      height (i : ℕ) d hd hcurrent hprevious Q
        (by simpa only [P] using hswitch.1)
        (by simpa only [P] using hswitch.2)

private theorem f1024TowerLevelCanonicalOrder_step
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1))) :
    f1024TowerLevelCanonicalOrder (height + 1) Q =
      (1 + 31 *
          f1024TowerLevelResidualPoleDivisor height
            (f1024Tower_restrictedGlobalPlace
              (k := F1024) (K := F1024TowerLevel height)
              (L := F1024TowerLevel (height + 1)) Q)) *
        f1024TowerLevelCanonicalOrder height
          (f1024Tower_restrictedGlobalPlace
            (k := F1024) (K := F1024TowerLevel height)
            (L := F1024TowerLevel (height + 1)) Q) +
      1054 * f1024TowerLevelResidualPoleDivisor height
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q) := by
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) :=
    f1024Tower_restrictedGlobalPlace
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  by_cases hzero : f1024TowerLevelResidualPoleDivisor height P = 0
  · have hscale :=
      f1024TowerLevel_step_order_eq_of_residualPoleDivisor_eq_zero
        height Q (by simpa only [P] using hzero)
    have hcanonical :=
      f1024TowerLevelCanonicalOrder_step_eq_of_order_scale_one
        height Q hscale
    rw [show f1024TowerLevelResidualPoleDivisor height
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q) = 0 by
            simpa only [P] using hzero]
    norm_num
    exact hcanonical
  · have hone :=
      f1024TowerLevelResidualPoleDivisor_apply_eq_one_of_ne_zero
        height P hzero
    have hpole :=
      f1024TowerLevelX_order_eq_neg_one_of_residualPoleDivisor_positive
        height P (by
          have hnonnegative :=
            f1024TowerLevelResidualPoleDivisor_apply_nonnegative height P
          omega)
    have hcanonical :=
      f1024TowerLevelCanonicalOrder_step_eq_of_lowerX_eq_neg_one
        height Q (by simpa only [P] using hpole)
    rw [show f1024TowerLevelResidualPoleDivisor height
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q) = 1 by
            simpa only [P] using hone]
    norm_num
    exact hcanonical

private theorem f1024TowerLevelCanonicalOrder_eq_candidate :
    ∀ (height : ℕ)
      (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
        (F1024TowerLevel height)),
      f1024TowerLevelCanonicalOrder height P =
        f1024TowerLevelCanonicalDivisorCandidate height P := by
  intro height
  induction height with
  | zero =>
      intro P
      simpa [f1024TowerLevelCanonicalDivisorCandidate] using
        f1024TowerLevelCanonicalOrder_zero P
  | succ height ih =>
      intro Q
      calc
        f1024TowerLevelCanonicalOrder (height + 1) Q =
            (1 + 31 *
                f1024TowerLevelResidualPoleDivisor height
                  (f1024Tower_restrictedGlobalPlace
                    (k := F1024) (K := F1024TowerLevel height)
                    (L := F1024TowerLevel (height + 1)) Q)) *
              f1024TowerLevelCanonicalOrder height
                (f1024Tower_restrictedGlobalPlace
                  (k := F1024) (K := F1024TowerLevel height)
                  (L := F1024TowerLevel (height + 1)) Q) +
            1054 * f1024TowerLevelResidualPoleDivisor height
              (f1024Tower_restrictedGlobalPlace
                (k := F1024) (K := F1024TowerLevel height)
                (L := F1024TowerLevel (height + 1)) Q) :=
          f1024TowerLevelCanonicalOrder_step height Q
        _ = (1 + 31 *
                f1024TowerLevelResidualPoleDivisor height
                  (f1024Tower_restrictedGlobalPlace
                    (k := F1024) (K := F1024TowerLevel height)
                    (L := F1024TowerLevel (height + 1)) Q)) *
              f1024TowerLevelCanonicalDivisorCandidate height
                (f1024Tower_restrictedGlobalPlace
                  (k := F1024) (K := F1024TowerLevel height)
                  (L := F1024TowerLevel (height + 1)) Q) +
            1054 * f1024TowerLevelResidualPoleDivisor height
              (f1024Tower_restrictedGlobalPlace
                (k := F1024) (K := F1024TowerLevel height)
                (L := F1024TowerLevel (height + 1)) Q) := by
          rw [ih]
        _ = f1024TowerLevelCanonicalDivisorCandidate (height + 1) Q :=
          (f1024TowerLevelCanonicalDivisorCandidate_step height Q).symm

/-- The intrinsic divisor of the actual function-field differential generator
at an indexed tower level. -/
noncomputable def f1024TowerLevelCanonicalDivisor (height : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) :=
  QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor
    (k := F1024) (F := F1024TowerLevel height)
    (functionFieldDifferentialGenerator
      (k := F1024) (F := F1024TowerLevel height))
    (functionFieldDifferentialGenerator_ne_zero
      (k := F1024) (F := F1024TowerLevel height))

/-- The displayed indexed divisor is canonical because it is the divisor of
the actual nonzero function-field differential generator. -/
theorem f1024TowerLevelCanonicalDivisor_isCanonical (height : ℕ) :
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.IsCanonicalDivisor
      (k := F1024) (F := F1024TowerLevel height)
      (f1024TowerLevelCanonicalDivisor height) := by
  exact
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_isCanonical
      (k := F1024) (F := F1024TowerLevel height)
      (functionFieldDifferentialGenerator
        (k := F1024) (F := F1024TowerLevel height))
      (functionFieldDifferentialGenerator_ne_zero
        (k := F1024) (F := F1024TowerLevel height))

private theorem f1024TowerLevelCanonicalDivisor_eq_candidate
    (height : ℕ) :
    f1024TowerLevelCanonicalDivisor height =
      f1024TowerLevelCanonicalDivisorCandidate height := by
  ext P
  rw [f1024TowerLevelCanonicalDivisor,
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_apply]
  exact f1024TowerLevelCanonicalOrder_eq_candidate height P

private theorem f1024TowerLevelCanonicalDivisor_degree_expansion
    (height : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel height))
        (f1024TowerLevelCanonicalDivisor height) =
      ((32 : ℤ) ^ (height + 1) - 34) +
        ∑ i : Fin ((height + 1) / 2),
          (34 * ((32 : ℤ) ^ (height - (2 * (i : ℕ) + 1)) - 1)) *
            (31 * (32 : ℤ) ^ (i : ℕ)) := by
  let degree := Divisor.degreeHom
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
      (k := F1024) (F := F1024TowerLevel height))
  rw [f1024TowerLevelCanonicalDivisor_eq_candidate]
  change degree (f1024TowerLevelCanonicalDivisorCandidate height) = _
  rw [f1024TowerLevelCanonicalDivisorCandidate, map_add, map_zsmul, map_sum]
  simp_rw [map_zsmul]
  simp only [smul_eq_mul]
  change
    ((32 : ℤ) ^ (height + 1) - 34) *
        Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel height))
          (f1024TowerLevelBasePoleDivisor height) +
      ∑ i : Fin ((height + 1) / 2),
        (34 * ((32 : ℤ) ^ (height - (2 * (i : ℕ) + 1)) - 1)) *
          Divisor.degree
            (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
              (k := F1024) (F := F1024TowerLevel height))
            (f1024TowerLevelPoleStratum height ⟨i, by omega⟩) = _
  rw [f1024TowerLevelBasePoleDivisor_degree]
  simp_rw [f1024TowerLevelPoleStratum_degree]
  ring

private theorem f1024TowerLevelCanonicalDegree_geometricSum (m : ℕ) :
    (∑ i : Fin m, (31 : ℤ) * (32 : ℤ) ^ (i : ℕ)) =
      (32 : ℤ) ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih, pow_succ]
      ring

private theorem f1024TowerLevelCanonicalDegree_reverseEvenSum (m : ℕ) :
    (∑ i : Fin m,
        (31 : ℤ) * (32 : ℤ) ^ (2 * m - ((i : ℕ) + 1))) =
      (32 : ℤ) ^ m * ((32 : ℤ) ^ m - 1) := by
  calc
    (∑ i : Fin m,
        (31 : ℤ) * (32 : ℤ) ^ (2 * m - ((i : ℕ) + 1))) =
        ∑ j : Fin m, (31 : ℤ) * (32 : ℤ) ^ (m + (j : ℕ)) := by
      apply Fintype.sum_equiv Fin.revPerm
      intro i
      apply congrArg (fun n : ℕ => (31 : ℤ) * (32 : ℤ) ^ n)
      simp only [Fin.revPerm_apply]
      change 2 * m - ((i : ℕ) + 1) =
        m + (m - ((i : ℕ) + 1))
      omega
    _ = (32 : ℤ) ^ m *
        ∑ j : Fin m, (31 : ℤ) * (32 : ℤ) ^ (j : ℕ) := by
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro j
      rw [pow_add]
      ring
    _ = (32 : ℤ) ^ m * ((32 : ℤ) ^ m - 1) := by
      rw [f1024TowerLevelCanonicalDegree_geometricSum]

private theorem f1024TowerLevelCanonicalDegree_reverseOddSum (m : ℕ) :
    (∑ i : Fin m,
        (31 : ℤ) * (32 : ℤ) ^ (2 * m - (i : ℕ))) =
      (32 : ℤ) ^ (m + 1) * ((32 : ℤ) ^ m - 1) := by
  calc
    (∑ i : Fin m,
        (31 : ℤ) * (32 : ℤ) ^ (2 * m - (i : ℕ))) =
        ∑ j : Fin m, (31 : ℤ) * (32 : ℤ) ^ (m + 1 + (j : ℕ)) := by
      apply Fintype.sum_equiv Fin.revPerm
      intro i
      apply congrArg (fun n : ℕ => (31 : ℤ) * (32 : ℤ) ^ n)
      simp only [Fin.revPerm_apply]
      change 2 * m - (i : ℕ) = m + 1 + (m - ((i : ℕ) + 1))
      omega
    _ = (32 : ℤ) ^ (m + 1) *
        ∑ j : Fin m, (31 : ℤ) * (32 : ℤ) ^ (j : ℕ) := by
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro j
      rw [pow_add]
      ring
    _ = (32 : ℤ) ^ (m + 1) * ((32 : ℤ) ^ m - 1) := by
      rw [f1024TowerLevelCanonicalDegree_geometricSum]

private theorem f1024TowerLevelCanonicalDegreeArithmetic_even (m : ℕ) :
    ((32 : ℤ) ^ (2 * m + 1) - 34) +
        ∑ i : Fin m,
          (34 * ((32 : ℤ) ^ (2 * m - (2 * (i : ℕ) + 1)) - 1)) *
            (31 * (32 : ℤ) ^ (i : ℕ)) =
      66 * (32 : ℤ) ^ (2 * m) - 68 * (32 : ℤ) ^ m := by
  have hsum :
      (∑ i : Fin m,
          (34 * ((32 : ℤ) ^ (2 * m - (2 * (i : ℕ) + 1)) - 1)) *
            (31 * (32 : ℤ) ^ (i : ℕ))) =
        34 *
          ((∑ i : Fin m,
              (31 : ℤ) * (32 : ℤ) ^ (2 * m - ((i : ℕ) + 1))) -
            ∑ i : Fin m, (31 : ℤ) * (32 : ℤ) ^ (i : ℕ)) := by
    calc
      (∑ i : Fin m,
          (34 * ((32 : ℤ) ^ (2 * m - (2 * (i : ℕ) + 1)) - 1)) *
            (31 * (32 : ℤ) ^ (i : ℕ))) =
          ∑ i : Fin m,
            34 *
              ((31 : ℤ) * (32 : ℤ) ^ (2 * m - ((i : ℕ) + 1)) -
                (31 : ℤ) * (32 : ℤ) ^ (i : ℕ)) := by
        apply Fintype.sum_congr
        intro i
        have hexponent :
            2 * m - (2 * (i : ℕ) + 1) + (i : ℕ) =
              2 * m - ((i : ℕ) + 1) := by
          omega
        calc
          (34 * ((32 : ℤ) ^ (2 * m - (2 * (i : ℕ) + 1)) - 1)) *
                (31 * (32 : ℤ) ^ (i : ℕ)) =
              34 *
                (31 * ((32 : ℤ) ^ (2 * m - (2 * (i : ℕ) + 1)) *
                    (32 : ℤ) ^ (i : ℕ)) -
                  31 * (32 : ℤ) ^ (i : ℕ)) := by ring
          _ = 34 *
              ((31 : ℤ) * (32 : ℤ) ^ (2 * m - ((i : ℕ) + 1)) -
                (31 : ℤ) * (32 : ℤ) ^ (i : ℕ)) := by
            rw [← pow_add, hexponent]
      _ = 34 *
          ((∑ i : Fin m,
              (31 : ℤ) * (32 : ℤ) ^ (2 * m - ((i : ℕ) + 1))) -
            ∑ i : Fin m, (31 : ℤ) * (32 : ℤ) ^ (i : ℕ)) := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum, f1024TowerLevelCanonicalDegree_reverseEvenSum,
    f1024TowerLevelCanonicalDegree_geometricSum]
  rw [show 2 * m + 1 = 2 * m + 1 by rfl]
  rw [pow_succ]
  ring_nf

private theorem f1024TowerLevelCanonicalDegreeArithmetic_odd (m : ℕ) :
    ((32 : ℤ) ^ (2 * m + 2) - 34) +
        ∑ i : Fin (m + 1),
          (34 * ((32 : ℤ) ^ (2 * m + 1 - (2 * (i : ℕ) + 1)) - 1)) *
            (31 * (32 : ℤ) ^ (i : ℕ)) =
      66 * (32 : ℤ) ^ (2 * m + 1) - 1122 * (32 : ℤ) ^ m := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  have hlast :
      (34 * ((32 : ℤ) ^ (2 * m + 1 - (2 * m + 1)) - 1)) *
          (31 * (32 : ℤ) ^ m) = 0 := by
    norm_num
  rw [hlast, add_zero]
  have hsum :
      (∑ i : Fin m,
          (34 * ((32 : ℤ) ^ (2 * m + 1 - (2 * (i : ℕ) + 1)) - 1)) *
            (31 * (32 : ℤ) ^ (i : ℕ))) =
        34 *
          ((∑ i : Fin m,
              (31 : ℤ) * (32 : ℤ) ^ (2 * m - (i : ℕ))) -
            ∑ i : Fin m, (31 : ℤ) * (32 : ℤ) ^ (i : ℕ)) := by
    calc
      (∑ i : Fin m,
          (34 * ((32 : ℤ) ^ (2 * m + 1 - (2 * (i : ℕ) + 1)) - 1)) *
            (31 * (32 : ℤ) ^ (i : ℕ))) =
          ∑ i : Fin m,
            34 *
              ((31 : ℤ) * (32 : ℤ) ^ (2 * m - (i : ℕ)) -
                (31 : ℤ) * (32 : ℤ) ^ (i : ℕ)) := by
        apply Fintype.sum_congr
        intro i
        have hexponent :
            2 * m + 1 - (2 * (i : ℕ) + 1) + (i : ℕ) =
              2 * m - (i : ℕ) := by
          omega
        calc
          (34 * ((32 : ℤ) ^ (2 * m + 1 - (2 * (i : ℕ) + 1)) - 1)) *
                (31 * (32 : ℤ) ^ (i : ℕ)) =
              34 *
                (31 * ((32 : ℤ) ^ (2 * m + 1 - (2 * (i : ℕ) + 1)) *
                    (32 : ℤ) ^ (i : ℕ)) -
                  31 * (32 : ℤ) ^ (i : ℕ)) := by ring
          _ = 34 *
              ((31 : ℤ) * (32 : ℤ) ^ (2 * m - (i : ℕ)) -
                (31 : ℤ) * (32 : ℤ) ^ (i : ℕ)) := by
            rw [← pow_add, hexponent]
      _ = 34 *
          ((∑ i : Fin m,
              (31 : ℤ) * (32 : ℤ) ^ (2 * m - (i : ℕ))) -
            ∑ i : Fin m, (31 : ℤ) * (32 : ℤ) ^ (i : ℕ)) := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum, f1024TowerLevelCanonicalDegree_reverseOddSum,
    f1024TowerLevelCanonicalDegree_geometricSum]
  rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, pow_succ,
    show m + 1 = m + 1 by rfl, pow_succ]
  ring_nf

private theorem f1024TowerLevelCanonicalDivisor_degree_even (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024TowerLevelCanonicalDivisor (2 * r + 2)) =
      66 * (32 : ℤ) ^ (2 * r + 2) - 68 * (32 : ℤ) ^ (r + 1) := by
  rw [f1024TowerLevelCanonicalDivisor_degree_expansion]
  rw [show 2 * r + 2 + 1 = 2 * (r + 1) + 1 by omega]
  rw [show (2 * (r + 1) + 1) / 2 = r + 1 by omega]
  rw [show 2 * r + 2 = 2 * (r + 1) by omega]
  exact f1024TowerLevelCanonicalDegreeArithmetic_even (r + 1)

private theorem f1024TowerLevelCanonicalDivisor_degree_odd (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 3)))
        (f1024TowerLevelCanonicalDivisor (2 * r + 3)) =
      66 * (32 : ℤ) ^ (2 * r + 3) - 1122 * (32 : ℤ) ^ (r + 1) := by
  rw [f1024TowerLevelCanonicalDivisor_degree_expansion]
  rw [show 2 * r + 3 + 1 = 2 * (r + 1) + 2 by omega]
  rw [show (2 * (r + 1) + 2) / 2 = (r + 1) + 1 by omega]
  rw [show 2 * r + 3 = 2 * (r + 1) + 1 by omega]
  exact f1024TowerLevelCanonicalDegreeArithmetic_odd (r + 1)

private theorem f1024TowerLevel_oddGenus_subtrahend_le (r : ℕ) :
    34 * 32 ^ (r + 1) ≤ 33 * 32 ^ (2 * r + 2) := by
  let q := 32 ^ (r + 1)
  have hpower : 32 ≤ q := by
    dsimp only [q]
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 32)
      (by omega : 1 ≤ r + 1)
    norm_num at h ⊢
    exact h
  have hbig : 32 ^ (2 * r + 2) = q * q := by
    dsimp only [q]
    rw [show 2 * r + 2 = (r + 1) + (r + 1) by omega, pow_add]
  change 34 * q ≤ 33 * 32 ^ (2 * r + 2)
  rw [hbig]
  have hmul : q * 32 ≤ q * q := Nat.mul_le_mul_left q hpower
  nlinarith

private theorem f1024TowerLevel_evenGenus_subtrahend_le (r : ℕ) :
    561 * 32 ^ (r + 1) ≤ 33 * 32 ^ (2 * r + 3) := by
  let q := 32 ^ (r + 1)
  have hpower : 32 ≤ q := by
    dsimp only [q]
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 32)
      (by omega : 1 ≤ r + 1)
    norm_num at h ⊢
    exact h
  have hbig : 32 ^ (2 * r + 3) = q * q * 32 := by
    dsimp only [q]
    rw [show 2 * r + 3 = (r + 1) + (r + 1) + 1 by omega,
      pow_add, pow_add]
    norm_num
  change 561 * q ≤ 33 * 32 ^ (2 * r + 3)
  rw [hbig]
  have hmul : q * 32 ≤ q * q := Nat.mul_le_mul_left q hpower
  nlinarith

private theorem f1024TowerLevel_oddGenus_cast (r : ℕ) :
    (oddGenus r : ℤ) =
      33 * (32 : ℤ) ^ (2 * r + 2) -
        34 * (32 : ℤ) ^ (r + 1) + 1 := by
  rw [oddGenus, Nat.cast_add,
    Nat.cast_sub (f1024TowerLevel_oddGenus_subtrahend_le r)]
  norm_num

private theorem f1024TowerLevel_evenGenus_cast (r : ℕ) :
    (evenGenus r : ℤ) =
      33 * (32 : ℤ) ^ (2 * r + 3) -
        561 * (32 : ℤ) ^ (r + 1) + 1 := by
  rw [evenGenus, Nat.cast_add,
    Nat.cast_sub (f1024TowerLevel_evenGenus_subtrahend_le r)]
  norm_num

/-- The intrinsic genus of the actual even extension height is the odd-index
GS95/WHY24 genus branch. -/
theorem f1024TowerLevel_functionFieldGenus_even (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.functionFieldGenus F1024
        (F1024TowerLevel (2 * r + 2)) = oddGenus r := by
  apply Nat.cast_injective (R := ℤ)
  rw [f1024TowerLevel_oddGenus_cast]
  have hcanonical :=
    QEC.Coding.AlgebraicGeometry.CanonicalDivisor.degree_eq_two_mul_genus_sub_two
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024TowerLevelCanonicalDivisor_isCanonical (2 * r + 2))
  rw [f1024TowerLevelCanonicalDivisor_degree_even] at hcanonical
  omega

/-- The intrinsic genus of the actual odd extension height is the even-index
GS95/WHY24 genus branch. -/
theorem f1024TowerLevel_functionFieldGenus_odd (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.functionFieldGenus F1024
        (F1024TowerLevel (2 * r + 3)) = evenGenus r := by
  apply Nat.cast_injective (R := ℤ)
  rw [f1024TowerLevel_evenGenus_cast]
  have hcanonical :=
    QEC.Coding.AlgebraicGeometry.CanonicalDivisor.degree_eq_two_mul_genus_sub_two
      (k := F1024) (F := F1024TowerLevel (2 * r + 3))
      (f1024TowerLevelCanonicalDivisor_isCanonical (2 * r + 3))
  rw [f1024TowerLevelCanonicalDivisor_degree_odd] at hcanonical
  omega

private theorem f1024Tower_selectedPlaceCount_le_card_at_height
    (height genus : ℕ) (hheight : 1 ≤ height)
    (hgenus : genus ≤ 33 * 32 ^ height + 1) :
    selectedPlaceCount genus ≤ 1023 * 32 ^ height := by
  rw [selectedPlaceCount]
  apply Nat.div_le_of_le_mul
  have hpower : 32 ≤ 32 ^ height := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 32) hheight
    norm_num at h ⊢
    exact h
  calc
    123 * genus ≤ 123 * (33 * 32 ^ height + 1) :=
      Nat.mul_le_mul_left 123 hgenus
    _ ≤ (1023 * 32 ^ height) * 4 := by nlinarith
    _ = 4 * (1023 * 32 ^ height) := by ring

/-- The explicit finite rational-place family at every selected even height
contains the full WHY24 budget derived from the intrinsic genus. -/
theorem f1024TowerFiniteRationalPlaces_selectedPlaceCount_le_even (r : ℕ) :
    selectedPlaceCount
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.functionFieldGenus F1024
          (F1024TowerLevel (2 * r + 2))) ≤
      (f1024TowerFiniteRationalPlaces (2 * r + 2)).card := by
  rw [f1024TowerLevel_functionFieldGenus_even,
    f1024TowerFiniteRationalPlaces_card]
  apply f1024Tower_selectedPlaceCount_le_card_at_height
    (height := 2 * r + 2) (genus := oddGenus r)
  · omega
  · unfold oddGenus
    omega

/-- The explicit finite rational-place family at every selected odd height
contains the full WHY24 budget derived from the intrinsic genus. -/
theorem f1024TowerFiniteRationalPlaces_selectedPlaceCount_le_odd (r : ℕ) :
    selectedPlaceCount
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.functionFieldGenus F1024
          (F1024TowerLevel (2 * r + 3))) ≤
      (f1024TowerFiniteRationalPlaces (2 * r + 3)).card := by
  rw [f1024TowerLevel_functionFieldGenus_odd,
    f1024TowerFiniteRationalPlaces_card]
  apply f1024Tower_selectedPlaceCount_le_card_at_height
    (height := 2 * r + 3) (genus := evenGenus r)
  · omega
  · unfold evenGenus
    omega

/-- The intrinsic pole divisor of the actual current coordinate at extension
height `height` has degree `32^height`.  The proof starts from the chart
variable degree and transports it through every literal tower recurrence;
the divisor degree is not retained in the recursive tower data. -/
theorem f1024TowerLevel_polarDivisor_degree_x (height : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel height))
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F1024TowerLevel height)
          (f1024TowerLevelX height)) =
      (32 ^ height : ℤ) := by
  simpa only [f1024TowerLevelHistoricalX_current] using
    f1024TowerLevelHistoricalX_polarDivisor_degree height height (le_refl height)

end TowerLevelCoordinateDivisors

open QEC.Coding.AlgebraicGeometry

/-!
## Source-selected odd-level rational places and divisors

WHY24 selects `n' = floor (123g/4)` rational places at every level, reserves
the final two for the one-place divisors `A` and `E`, and evaluates on the
first `n' - 2`.  The definitions below make that selection from the actual
coordinate-indexed rational places constructed above.  We use the odd source
levels `i = 2r + 3` as a cofinal subsequence for the eventual code family;
the tower and genus formulas themselves remain available on both parities.
-/

private theorem f1024Why24OddGenus_lower_bound (r : ℕ) :
    32705 ≤ oddGenus r := by
  let q : ℤ := (32 : ℤ) ^ (r + 1)
  have hqNat : 32 ≤ 32 ^ (r + 1) := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 32)
      (by omega : 1 ≤ r + 1)
    norm_num at h ⊢
    exact h
  have hq : (32 : ℤ) ≤ q := by
    dsimp only [q]
    exact_mod_cast hqNat
  have hpower : (32 : ℤ) ^ (2 * r + 2) = q * q := by
    dsimp only [q]
    rw [show 2 * r + 2 = (r + 1) + (r + 1) by omega, pow_add]
  have hcast := f1024TowerLevel_oddGenus_cast r
  have hbound : (32705 : ℤ) ≤ (oddGenus r : ℤ) := by
    rw [hcast, hpower]
    nlinarith
  exact_mod_cast hbound

private theorem f1024Why24OddSelectedPlaceCount_two_le (r : ℕ) :
    2 ≤ selectedPlaceCount (oddGenus r) := by
  calc
    2 ≤ selectedPlaceCount 32705 := by
      norm_num [selectedPlaceCount]
    _ ≤ selectedPlaceCount (oddGenus r) := by
      unfold selectedPlaceCount
      exact Nat.div_le_div_right
        (Nat.mul_le_mul_left 123 (f1024Why24OddGenus_lower_bound r))

private theorem f1024Why24OddSelectedPlaceCount_le_coordinateCard (r : ℕ) :
    selectedPlaceCount (oddGenus r) ≤
      Fintype.card (F1024TowerFiniteCoordinate (2 * r + 2)) := by
  rw [f1024TowerFiniteCoordinate_card]
  simpa only [f1024TowerLevel_functionFieldGenus_even,
    f1024TowerFiniteRationalPlaces_card] using
      f1024TowerFiniteRationalPlaces_selectedPlaceCount_le_even r

private noncomputable def f1024Why24OddSelectedCoordinateEmbedding (r : ℕ) :
    Fin (selectedPlaceCount (oddGenus r)) ↪
      F1024TowerFiniteCoordinate (2 * r + 2) :=
  (Fin.castLEEmb (f1024Why24OddSelectedPlaceCount_le_coordinateCard r)).trans
    (Fintype.equivFin (F1024TowerFiniteCoordinate (2 * r + 2))).symm.toEmbedding

private theorem f1024TowerFiniteCoordinate_eq_of_place_valuation_eq
    (height : ℕ)
    (coordinate other : F1024TowerFiniteCoordinate height)
    (hvaluations :
      (f1024TowerFiniteRationalPlace height coordinate).place.valuation =
        (f1024TowerFiniteRationalPlace height other).place.valuation) :
    coordinate = other := by
  let chart := f1024TowerFiniteChart height
  let coordinatePrime := f1024TowerFiniteChartPrime height coordinate
  let otherPrime := f1024TowerFiniteChartPrime height other
  change coordinatePrime.valuation (F1024TowerLevel height) =
    otherPrime.valuation (F1024TowerLevel height) at hvaluations
  have hprimes : coordinatePrime = otherPrime := by
    apply IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
      (K := F1024TowerLevel height)
    exact Valuation.IsEquiv.of_eq hvaluations
  have hkernels :
      RingHom.ker (chart.evaluate coordinate) =
        RingHom.ker (chart.evaluate other) :=
    congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hprimes
  apply chart.evaluate_injective
  ext a
  let value := chart.evaluate coordinate a
  have hmem :
      a - algebraMap F1024 chart.carrier value ∈
        RingHom.ker (chart.evaluate coordinate) := by
    change chart.evaluate coordinate
      (a - algebraMap F1024 chart.carrier value) = 0
    simp only [map_sub, chart.evaluate_constants, value, sub_self]
  rw [hkernels] at hmem
  change chart.evaluate other
      (a - algebraMap F1024 chart.carrier value) = 0 at hmem
  rw [map_sub, chart.evaluate_constants] at hmem
  exact (sub_eq_zero.mp hmem).symm

private theorem f1024TowerFiniteRationalPlace_place_injective (height : ℕ) :
    Function.Injective
      (fun coordinate : F1024TowerFiniteCoordinate height =>
        (f1024TowerFiniteRationalPlace height coordinate).place) := by
  intro coordinate other hplaces
  apply f1024TowerFiniteCoordinate_eq_of_place_valuation_eq height
  exact congrArg (fun place => place.valuation) hplaces

private noncomputable def f1024Why24OddDirectRationalPlace
    (height : ℕ)
    (Q : @QEC.Coding.AlgebraicGeometry.RationalPlace F1024
      (F1024TowerLevel height) _ _ _
        (f1024TowerStage height).constantAlgebraInst) :
    @QEC.Coding.AlgebraicGeometry.RationalPlace F1024
      (F1024TowerLevel height) _ _ _
        (f1024TowerLevelCoordinateDivisorAlgebra height) := by
  let P : @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) _ _ _
        (f1024TowerLevelCoordinateDivisorAlgebra height) :=
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.mk F1024
      (F1024TowerLevel height) _ _ _
        (f1024TowerLevelCoordinateDivisorAlgebra height)
        (@QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024
          (F1024TowerLevel height) _ _ _
            (f1024TowerStage height).constantAlgebraInst Q.place)
        (@QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized F1024
          (F1024TowerLevel height) _ _ _
            (f1024TowerStage height).constantAlgebraInst Q.place)
  refine @QEC.Coding.AlgebraicGeometry.RationalPlace.mk F1024
    (F1024TowerLevel height) _ _ _
      (f1024TowerLevelCoordinateDivisorAlgebra height) P
      (@QEC.Coding.AlgebraicGeometry.RationalPlace.constantsEquiv F1024
        (F1024TowerLevel height) _ _ _
          (f1024TowerStage height).constantAlgebraInst Q) ?_
  intro a
  have hmap :
      @algebraMap F1024 (F1024TowerLevel height) _ _
          (f1024TowerLevelCoordinateDivisorAlgebra height) a =
        @algebraMap F1024 (F1024TowerLevel height) _ _
          (f1024TowerStage height).constantAlgebraInst a :=
    congrArg
      (fun A : Algebra F1024 (F1024TowerLevel height) =>
        @algebraMap F1024 (F1024TowerLevel height) _ _ A a)
      (f1024TowerLevelCoordinateDivisorAlgebra_eq_stage height)
  change
    (@QEC.Coding.AlgebraicGeometry.RationalPlace.constantsEquiv F1024
      (F1024TowerLevel height) _ _ _
        (f1024TowerStage height).constantAlgebraInst Q) a =
      (@QEC.Coding.AlgebraicGeometry.GlobalPlace.residue F1024
        (F1024TowerLevel height) _ _ _
          (f1024TowerLevelCoordinateDivisorAlgebra height) P)
    ⟨@algebraMap F1024 (F1024TowerLevel height) _ _
      (f1024TowerLevelCoordinateDivisorAlgebra height) a, _⟩
  rw [@QEC.Coding.AlgebraicGeometry.RationalPlace.constantsEquiv_apply F1024
    (F1024TowerLevel height) _ _ _
      (f1024TowerStage height).constantAlgebraInst Q a]
  change
    (@QEC.Coding.AlgebraicGeometry.GlobalPlace.residue F1024
      (F1024TowerLevel height) _ _ _
        (f1024TowerStage height).constantAlgebraInst Q.place)
        ⟨@algebraMap F1024 (F1024TowerLevel height) _ _
          (f1024TowerStage height).constantAlgebraInst a, _⟩ =
      (@QEC.Coding.AlgebraicGeometry.GlobalPlace.residue F1024
        (F1024TowerLevel height) _ _ _
          (f1024TowerStage height).constantAlgebraInst Q.place)
        ⟨@algebraMap F1024 (F1024TowerLevel height) _ _
          (f1024TowerLevelCoordinateDivisorAlgebra height) a, _⟩
  apply congrArg
  exact Subtype.ext hmap.symm

private theorem f1024Why24OddDirectRationalPlace_valuation
    (height : ℕ)
    (Q : @QEC.Coding.AlgebraicGeometry.RationalPlace F1024
      (F1024TowerLevel height) _ _ _
        (f1024TowerStage height).constantAlgebraInst) :
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024
        (F1024TowerLevel height) _ _ _
          (f1024TowerLevelCoordinateDivisorAlgebra height)
          (@QEC.Coding.AlgebraicGeometry.RationalPlace.place F1024
            (F1024TowerLevel height) _ _ _
              (f1024TowerLevelCoordinateDivisorAlgebra height)
              (f1024Why24OddDirectRationalPlace height Q)) =
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024
        (F1024TowerLevel height) _ _ _
          (f1024TowerStage height).constantAlgebraInst
          (@QEC.Coding.AlgebraicGeometry.RationalPlace.place F1024
            (F1024TowerLevel height) _ _ _
              (f1024TowerStage height).constantAlgebraInst Q) := by
  rfl

-- The source-facing AG construction uses the direct affine constant algebra,
-- exactly as the Riemann--Roch and AG-duality APIs do.  The recursive tower
-- retains a propositionally equal algebra instance; selected coordinate
-- places are transported across that proved equality once, below.
@[reducible] noncomputable local instance (priority := 2000)
    f1024Why24OddDirectConstantAlgebra (height : ℕ) :
    Algebra F1024 (F1024TowerLevel height) :=
  f1024TowerLevelCoordinateDivisorAlgebra height

noncomputable local instance (priority := 2000)
    f1024Why24OddDirectConstantScalarTower (height : ℕ) :
    IsScalarTower F1024 F1024TowerF1 (F1024TowerLevel height) :=
  f1024TowerLevelCoordinateDivisorRationalScalarTower height

/-- The source-selected `n'` actual rational places on the odd cofinal tower
subsequence. -/
noncomputable def f1024Why24OddSelectedRationalPlace (r : ℕ) :
    Fin (selectedPlaceCount (oddGenus r)) →
      @QEC.Coding.AlgebraicGeometry.RationalPlace F1024
        (F1024TowerLevel (2 * r + 2)) _ _ _
          (f1024TowerLevelCoordinateDivisorAlgebra (2 * r + 2)) :=
  fun i => f1024Why24OddDirectRationalPlace (2 * r + 2)
    (f1024TowerFiniteRationalPlace (2 * r + 2)
      (f1024Why24OddSelectedCoordinateEmbedding r i))

/-- Distinct source-selected indices give distinct actual global places. -/
theorem f1024Why24OddSelectedRationalPlace_injective (r : ℕ) :
    Function.Injective
      (fun i => (f1024Why24OddSelectedRationalPlace r i).place) := by
  intro i j hij
  apply (f1024Why24OddSelectedCoordinateEmbedding r).injective
  apply f1024TowerFiniteCoordinate_eq_of_place_valuation_eq (2 * r + 2)
  have hvaluations := congrArg
    (fun place : @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
        (F1024TowerLevel (2 * r + 2)) _ _ _
          (f1024TowerLevelCoordinateDivisorAlgebra (2 * r + 2)) =>
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024
        (F1024TowerLevel (2 * r + 2)) _ _ _
          (f1024TowerLevelCoordinateDivisorAlgebra (2 * r + 2)) place)
    hij
  simpa only [f1024Why24OddSelectedRationalPlace,
    f1024Why24OddDirectRationalPlace_valuation] using hvaluations

private def f1024Why24OddCandidateIndexEmbedding (r : ℕ) :
    Fin (selectedPlaceCount (oddGenus r) - 2) ↪
      Fin (selectedPlaceCount (oddGenus r)) :=
  Fin.castLEEmb (Nat.sub_le _ _)

/-- The first `n' - 2` selected places are the candidate evaluation places
before zero-residue filtering. -/
noncomputable def f1024Why24OddCandidateRationalPlace (r : ℕ) :
    Fin (selectedPlaceCount (oddGenus r) - 2) →
      QEC.Coding.AlgebraicGeometry.RationalPlace F1024
        (F1024TowerLevel (2 * r + 2)) :=
  fun i => f1024Why24OddSelectedRationalPlace r
    (f1024Why24OddCandidateIndexEmbedding r i)

/-- The actual candidate evaluation-place family is pairwise distinct. -/
theorem f1024Why24OddCandidateRationalPlace_injective (r : ℕ) :
    Function.Injective
      (fun i => (f1024Why24OddCandidateRationalPlace r i).place) := by
  intro i j hij
  apply (f1024Why24OddCandidateIndexEmbedding r).injective
  exact f1024Why24OddSelectedRationalPlace_injective r hij

private def f1024Why24OddAIndex (r : ℕ) :
    Fin (selectedPlaceCount (oddGenus r)) :=
  ⟨selectedPlaceCount (oddGenus r) - 2, by
    have htwo := f1024Why24OddSelectedPlaceCount_two_le r
    omega⟩

private def f1024Why24OddEIndex (r : ℕ) :
    Fin (selectedPlaceCount (oddGenus r)) :=
  ⟨selectedPlaceCount (oddGenus r) - 1, by
    have htwo := f1024Why24OddSelectedPlaceCount_two_le r
    omega⟩

/-- The penultimate selected rational place supports the source divisor `A`. -/
noncomputable def f1024Why24OddAPlace (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.RationalPlace F1024
      (F1024TowerLevel (2 * r + 2)) :=
  f1024Why24OddSelectedRationalPlace r (f1024Why24OddAIndex r)

/-- The final selected rational place supports the source divisor `E`. -/
noncomputable def f1024Why24OddEPlace (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.RationalPlace F1024
      (F1024TowerLevel (2 * r + 2)) :=
  f1024Why24OddSelectedRationalPlace r (f1024Why24OddEIndex r)

/-- Candidate evaluation places avoid the reserved `A` place. -/
theorem f1024Why24OddCandidatePlace_ne_APlace (r : ℕ)
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    (f1024Why24OddCandidateRationalPlace r i).place ≠
      (f1024Why24OddAPlace r).place := by
  intro h
  have hindex := f1024Why24OddSelectedRationalPlace_injective r h
  have hval := congrArg Fin.val hindex
  change (i : ℕ) = selectedPlaceCount (oddGenus r) - 2 at hval
  omega

/-- Candidate evaluation places avoid the reserved `E` place. -/
theorem f1024Why24OddCandidatePlace_ne_EPlace (r : ℕ)
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    (f1024Why24OddCandidateRationalPlace r i).place ≠
      (f1024Why24OddEPlace r).place := by
  intro h
  have hindex := f1024Why24OddSelectedRationalPlace_injective r h
  have hval := congrArg Fin.val hindex
  change (i : ℕ) = selectedPlaceCount (oddGenus r) - 1 at hval
  omega

/-- The two source auxiliary places are distinct. -/
theorem f1024Why24OddAPlace_ne_EPlace (r : ℕ) :
    (f1024Why24OddAPlace r).place ≠ (f1024Why24OddEPlace r).place := by
  intro h
  have hindex := f1024Why24OddSelectedRationalPlace_injective r h
  have hval := congrArg Fin.val hindex
  change selectedPlaceCount (oddGenus r) - 2 =
    selectedPlaceCount (oddGenus r) - 1 at hval
  have htwo := f1024Why24OddSelectedPlaceCount_two_le r
  omega

/-- The reduced divisor on all candidate evaluation places. -/
noncomputable def f1024Why24OddEvaluationDivisor (r : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :=
  QEC.Coding.AlgebraicGeometry.evaluationDivisor
    (f1024Why24OddCandidateRationalPlace r)

/-- The source divisor `A = a P_{n'-1}`. -/
noncomputable def f1024Why24OddADivisor (r : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :=
  selectedDivisorDegree (oddGenus r) •
    Finsupp.single (f1024Why24OddAPlace r).place (1 : ℤ)

/-- The source divisor `E = (n' - 4 + g - 7a) P_{n'}`. -/
noncomputable def f1024Why24OddEDivisor (r : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :=
  selectedEDegree (oddGenus r) •
    Finsupp.single (f1024Why24OddEPlace r).place (1 : ℤ)

/-- The source residual divisor `B = D'' - 7A - E`. -/
noncomputable def f1024Why24OddResidualDivisor (r : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :=
  f1024Why24OddEvaluationDivisor r -
    7 • f1024Why24OddADivisor r - f1024Why24OddEDivisor r

/-- The candidate divisor has coefficient one at every candidate place. -/
theorem f1024Why24OddEvaluationDivisor_apply_candidate (r : ℕ)
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    f1024Why24OddEvaluationDivisor r
        (f1024Why24OddCandidateRationalPlace r i).place = 1 := by
  exact QEC.Coding.AlgebraicGeometry.evaluationDivisor_apply_at
    (f1024Why24OddCandidateRationalPlace r)
    (f1024Why24OddCandidateRationalPlace_injective r) i

/-- `A` vanishes at every candidate evaluation place. -/
theorem f1024Why24OddADivisor_apply_candidate (r : ℕ)
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    f1024Why24OddADivisor r
        (f1024Why24OddCandidateRationalPlace r i).place = 0 := by
  simp [f1024Why24OddADivisor,
    f1024Why24OddCandidatePlace_ne_APlace r i]

/-- `E` vanishes at every candidate evaluation place. -/
theorem f1024Why24OddEDivisor_apply_candidate (r : ℕ)
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    f1024Why24OddEDivisor r
        (f1024Why24OddCandidateRationalPlace r i).place = 0 := by
  simp [f1024Why24OddEDivisor,
    f1024Why24OddCandidatePlace_ne_EPlace r i]

/-- The `A` coefficient is its literal selected degree. -/
theorem f1024Why24OddADivisor_apply_APlace (r : ℕ) :
    f1024Why24OddADivisor r (f1024Why24OddAPlace r).place =
      selectedDivisorDegree (oddGenus r) := by
  simp [f1024Why24OddADivisor]

/-- The `E` coefficient is its literal selected degree. -/
theorem f1024Why24OddEDivisor_apply_EPlace (r : ℕ) :
    f1024Why24OddEDivisor r (f1024Why24OddEPlace r).place =
      selectedEDegree (oddGenus r) := by
  simp [f1024Why24OddEDivisor]

/-- `A` vanishes at the distinct `E` place. -/
theorem f1024Why24OddADivisor_apply_EPlace (r : ℕ) :
    f1024Why24OddADivisor r (f1024Why24OddEPlace r).place = 0 := by
  simp [f1024Why24OddADivisor,
    f1024Why24OddAPlace_ne_EPlace r]

/-- `E` vanishes at the distinct `A` place. -/
theorem f1024Why24OddEDivisor_apply_APlace (r : ℕ) :
    f1024Why24OddEDivisor r (f1024Why24OddAPlace r).place = 0 := by
  simp [f1024Why24OddEDivisor,
    (f1024Why24OddAPlace_ne_EPlace r).symm]

private theorem f1024Why24Odd_singleRationalPlace_degree (r : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.RationalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (Finsupp.single Q.place (1 : ℤ)) = 1 := by
  simp [Divisor.degree, Divisor.degreeHom,
    QEC.Coding.AlgebraicGeometry.RationalPlace.globalResidueDegree_eq_one]

private theorem f1024Why24Odd_divisor_degree_nsmul (r n : ℕ)
    (D : Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2)))) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2))) (n • D) =
      (n : ℤ) *
        Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel (2 * r + 2))) D := by
  simpa only [Divisor.degree, nsmul_eq_mul] using
    (Divisor.degreeHom
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)))).map_nsmul n D

/-- The candidate divisor has degree exactly `n' - 2`. -/
theorem f1024Why24OddEvaluationDivisor_degree (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddEvaluationDivisor r) =
      ((selectedPlaceCount (oddGenus r) - 2 : ℕ) : ℤ) := by
  simpa only [f1024Why24OddEvaluationDivisor, Fintype.card_fin] using
    QEC.Coding.AlgebraicGeometry.evaluationDivisor_degree_eq_card
      (f1024Why24OddCandidateRationalPlace r)

/-- The actual divisor `A` has degree exactly `a`. -/
theorem f1024Why24OddADivisor_degree (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddADivisor r) =
      selectedDivisorDegree (oddGenus r) := by
  rw [f1024Why24OddADivisor,
    f1024Why24Odd_divisor_degree_nsmul,
    f1024Why24Odd_singleRationalPlace_degree]
  simp

/-- The actual divisor `E` has the source-selected degree. -/
theorem f1024Why24OddEDivisor_degree (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddEDivisor r) =
      selectedEDegree (oddGenus r) := by
  rw [f1024Why24OddEDivisor,
    f1024Why24Odd_divisor_degree_nsmul,
    f1024Why24Odd_singleRationalPlace_degree]
  simp

private theorem f1024Why24OddGenus_mod_eight (r : ℕ) :
    oddGenus r % 8 = 1 := by
  have hlarge := f1024TowerLevel_oddGenus_subtrahend_le r
  have hhigh : 32 ^ (2 * r + 2) % 8 = 0 := by
    rw [show 2 * r + 2 = (2 * r + 1) + 1 by omega, pow_succ]
    omega
  have hlow : 32 ^ (r + 1) % 8 = 0 := by
    rw [pow_succ]
    omega
  unfold oddGenus
  omega

private theorem f1024Why24Odd_parameter_degree_identity (r : ℕ) :
    ((selectedPlaceCount (oddGenus r) - 2 : ℕ) : ℤ) -
        7 * (selectedDivisorDegree (oddGenus r) : ℤ) -
          (selectedEDegree (oddGenus r) : ℤ) =
      2 - (oddGenus r : ℤ) := by
  have hmod := f1024Why24OddGenus_mod_eight r
  have hlarge := f1024Why24OddGenus_lower_bound r
  simp only [selectedPlaceCount, selectedDivisorDegree, selectedEDegree]
  omega

/-- The actual residual divisor `B = D'' - 7A - E` has degree `2 - g`,
which is the exact Riemann--Roch input in WHY24. -/
theorem f1024Why24OddResidualDivisor_degree (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddResidualDivisor r) =
      2 - (oddGenus r : ℤ) := by
  rw [f1024Why24OddResidualDivisor, Divisor.degree_sub,
    Divisor.degree_sub, f1024Why24OddEvaluationDivisor_degree,
    f1024Why24Odd_divisor_degree_nsmul, f1024Why24OddADivisor_degree,
    f1024Why24OddEDivisor_degree]
  exact f1024Why24Odd_parameter_degree_identity r

/-!
## The source Riemann--Roch differential on the odd cofinal subsequence

The intrinsic canonical-divisor calculation above uses the direct affine
constant algebra, whereas the coordinate-indexed rational places are
constructed with the recursively retained constant algebra.  Those two
algebra structures were proved equal in
`f1024TowerLevelCoordinateDivisorAlgebra_eq_stage`; the wrapper below performs
that transport explicitly before applying Riemann--Roch.  It does not choose
a divisor or differential as an input.
-/

/-- The actual canonical divisor at a source-selected odd level, transported
to the same global-place carrier as the selected rational places. -/
noncomputable def f1024Why24OddCanonicalDivisor (r : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :=
  f1024TowerLevelCanonicalDivisor (2 * r + 2)

/-- The transported odd-level divisor is still the divisor of an actual
nonzero function-field differential. -/
theorem f1024Why24OddCanonicalDivisor_isCanonical (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.IsCanonicalDivisor
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024Why24OddCanonicalDivisor r) :=
  f1024TowerLevelCanonicalDivisor_isCanonical (2 * r + 2)

/-- The transported canonical divisor has its intrinsic degree `2g - 2`. -/
theorem f1024Why24OddCanonicalDivisor_degree (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddCanonicalDivisor r) =
      2 * (oddGenus r : ℤ) - 2 := by
  have hdegree :=
    QEC.Coding.AlgebraicGeometry.CanonicalDivisor.degree_eq_two_mul_genus_sub_two
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024TowerLevelCanonicalDivisor_isCanonical (2 * r + 2))
  rw [f1024TowerLevel_functionFieldGenus_even] at hdegree
  exact hdegree

/-- The literal Riemann--Roch divisor `W + B` used to construct `omega₀`. -/
noncomputable def f1024Why24OddRiemannRochTarget (r : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :=
  f1024Why24OddCanonicalDivisor r + f1024Why24OddResidualDivisor r

/-- The source identity `deg (W + B) = g` for the actual selected divisors. -/
theorem f1024Why24OddRiemannRochTarget_degree (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddRiemannRochTarget r) =
      (oddGenus r : ℤ) := by
  rw [f1024Why24OddRiemannRochTarget, Divisor.degree_add,
    f1024Why24OddCanonicalDivisor_degree,
    f1024Why24OddResidualDivisor_degree]
  ring

private noncomputable instance
    f1024Why24OddRiemannRochTarget_finiteDimensional (r : ℕ) :
    FiniteDimensional F1024
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddRiemannRochTarget r)) :=
  QEC.Coding.AlgebraicGeometry.GlobalPlace.finiteDimensional_riemannRochSubmodule
    (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024Why24OddRiemannRochTarget r)

/-- Riemann's lower bound makes the actual space `L(W + B)` nontrivial. -/
theorem f1024Why24OddRiemannRochDimension_pos (r : ℕ) :
    0 < Module.finrank F1024
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddRiemannRochTarget r)) := by
  have hlower :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_lower_bound
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024Why24OddRiemannRochTarget r)
  rw [f1024Why24OddRiemannRochTarget_degree,
    f1024TowerLevel_functionFieldGenus_even] at hlower
  simp only [QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension]
    at hlower
  have hfinrank : (1 : ℤ) ≤
      (Module.finrank F1024
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          (f1024Why24OddRiemannRochTarget r)) : ℤ) := by
    change (oddGenus r : ℤ) + 1 - oddGenus r ≤ _ at hlower
    omega
  exact_mod_cast hfinrank

private theorem f1024Why24OddRiemannRoch_exists_ne_zero (r : ℕ) :
    ∃ f : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddRiemannRochTarget r),
      f ≠ 0 :=
  (Module.finrank_pos_iff_exists_ne_zero (R := F1024)).mp
    (f1024Why24OddRiemannRochDimension_pos r)

private noncomputable def f1024Why24OddRiemannRochWitness (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddRiemannRochTarget r) :=
  Classical.choose (f1024Why24OddRiemannRoch_exists_ne_zero r)

private theorem f1024Why24OddRiemannRochWitness_ne_zero (r : ℕ) :
    f1024Why24OddRiemannRochWitness r ≠ 0 :=
  Classical.choose_spec (f1024Why24OddRiemannRoch_exists_ne_zero r)

private theorem f1024Why24OddRiemannRochWitness_val_ne_zero (r : ℕ) :
    (f1024Why24OddRiemannRochWitness r :
      F1024TowerLevel (2 * r + 2)) ≠ 0 := by
  intro hzero
  apply f1024Why24OddRiemannRochWitness_ne_zero r
  exact Subtype.ext hzero

/-- A concrete nonzero differential in `Ω(-B)`, obtained by multiplying the
function-field differential generator by the selected nonzero element of
`L(W + B)`. -/
noncomputable def f1024Why24OddDifferential (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.Differential F1024
      (F1024TowerLevel (2 * r + 2)) :=
  (Units.mk0
      (f1024Why24OddRiemannRochWitness r :
        F1024TowerLevel (2 * r + 2))
      (f1024Why24OddRiemannRochWitness_val_ne_zero r) :
      F1024TowerLevel (2 * r + 2)) •
    functionFieldDifferentialGenerator
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))

/-- The chosen source differential is genuinely nonzero. -/
theorem f1024Why24OddDifferential_ne_zero (r : ℕ) :
    f1024Why24OddDifferential r ≠ 0 := by
  apply smul_ne_zero
  · exact Units.ne_zero _
  · exact functionFieldDifferentialGenerator_ne_zero
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))

private theorem f1024Why24OddCanonicalDivisor_eq_generator (r : ℕ) :
    f1024Why24OddCanonicalDivisor r =
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        (functionFieldDifferentialGenerator
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (functionFieldDifferentialGenerator_ne_zero
          (k := F1024) (F := F1024TowerLevel (2 * r + 2))) :=
  rfl

private theorem f1024Why24OddDifferentialDivisor_eq (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        (f1024Why24OddDifferential r)
        (f1024Why24OddDifferential_ne_zero r) =
      QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor
          (k := F1024) (F := F1024TowerLevel (2 * r + 2))
          (Units.mk0
            (f1024Why24OddRiemannRochWitness r :
              F1024TowerLevel (2 * r + 2))
            (f1024Why24OddRiemannRochWitness_val_ne_zero r)) +
        f1024Why24OddCanonicalDivisor r := by
  let u : (F1024TowerLevel (2 * r + 2))ˣ :=
    Units.mk0
      (f1024Why24OddRiemannRochWitness r :
        F1024TowerLevel (2 * r + 2))
      (f1024Why24OddRiemannRochWitness_val_ne_zero r)
  change
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        ((u : F1024TowerLevel (2 * r + 2)) •
          functionFieldDifferentialGenerator
            (k := F1024) (F := F1024TowerLevel (2 * r + 2))) _ =
      QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)) u +
        f1024Why24OddCanonicalDivisor r
  rw [QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_smul,
    ← f1024Why24OddCanonicalDivisor_eq_generator]
  exact functionFieldDifferentialGenerator_ne_zero
    (k := F1024) (F := F1024TowerLevel (2 * r + 2))

/-- The selected differential realizes the exact source lower bound
`7A + E - D'' ≤ (ω₀)`. -/
theorem f1024Why24OddDifferentialDivisor_lower_bound (r : ℕ) :
    7 • f1024Why24OddADivisor r + f1024Why24OddEDivisor r -
        f1024Why24OddEvaluationDivisor r ≤
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        (f1024Why24OddDifferential r)
        (f1024Why24OddDifferential_ne_zero r) := by
  rw [f1024Why24OddDifferentialDivisor_eq]
  intro P
  have hP :=
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
      (f1024Why24OddRiemannRochTarget r)
      (f1024Why24OddRiemannRochWitness_val_ne_zero r)).mp
        (f1024Why24OddRiemannRochWitness r).property P
  simp only [Units.val_mk0, Finsupp.add_apply, Finsupp.sub_apply,
    Finsupp.nsmul_apply,
    QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor_apply] at hP ⊢
  dsimp only [f1024Why24OddRiemannRochTarget,
    f1024Why24OddResidualDivisor] at hP
  simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.nsmul_apply] at hP
  omega

/-!
## Removing the zero-residue evaluation places

WHY24 keeps precisely the candidate places where the local component of
`ω₀` on `1` is nonzero.  The divisor lower bound gives a simple pole at
every candidate.  A zero simple-pole residue is then equivalent to regularity,
and adjoining all regular candidates to the lower divisor bounds their number
by the genus.  Everything below is formed from the actual candidate places and
the actual differential above.
-/

/-- Every candidate place sees at most a simple pole of the selected
differential. -/
theorem f1024Why24OddCandidateDifferentialOrder_lower_bound (r : ℕ)
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    -1 ≤
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        (f1024Why24OddCandidateRationalPlace r i).place
        (f1024Why24OddDifferential r)
        (f1024Why24OddDifferential_ne_zero r) := by
  have hbound := f1024Why24OddDifferentialDivisor_lower_bound r
    (f1024Why24OddCandidateRationalPlace r i).place
  simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.nsmul_apply,
    f1024Why24OddADivisor_apply_candidate,
    f1024Why24OddEDivisor_apply_candidate,
    f1024Why24OddEvaluationDivisor_apply_candidate,
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_apply]
    at hbound
  norm_num at hbound
  exact hbound

private theorem f1024Why24OddCandidateDifferential_mem_simplePole (r : ℕ)
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    f1024Why24OddDifferential r ∈
      QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferentialLattice
        (f1024Why24OddCandidateRationalPlace r i).place := by
  apply
    (QEC.Coding.AlgebraicGeometry.Differential.mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        (f1024Why24OddCandidateRationalPlace r i).place
        (f1024Why24OddDifferential r)
        (f1024Why24OddDifferential_ne_zero r)).mpr
  exact f1024Why24OddCandidateDifferentialOrder_lower_bound r i

/-- The source coefficient `ω₀,P(1)` at an actual candidate rational
place, transported from its residue field back to `F1024`. -/
noncomputable def f1024Why24OddCandidateResidue (r : ℕ)
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) : F1024 :=
  (f1024Why24OddCandidateRationalPlace r i).constantsEquiv.symm
    (QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024Why24OddCandidateRationalPlace r i).place
      ⟨f1024Why24OddDifferential r,
        f1024Why24OddCandidateDifferential_mem_simplePole r i⟩)

private theorem f1024Why24Odd_simplePoleResidue_eq_zero_iff_mem_local
    {r : ℕ}
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2)))
    (eta : QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferentialLattice P) :
    QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)) P eta = 0 ↔
      (eta : QEC.Coding.AlgebraicGeometry.Differential F1024
        (F1024TowerLevel (2 * r + 2))) ∈
        QEC.Coding.AlgebraicGeometry.Differential.localDifferentialLattice P := by
  constructor
  · intro hzero
    have hmk :
        (QEC.Coding.AlgebraicGeometry.Differential.regularDifferentialSubmoduleOfSimplePole
          P).mkQ eta = 0 := by
      apply (QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidueEquiv
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)) P).injective
      have hport := hzero
      simp only [QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue, LinearMap.comp_apply, Submodule.mkQ_apply, map_zero] at hport ⊢
      exact hport
    exact (Submodule.Quotient.mk_eq_zero
      (p := QEC.Coding.AlgebraicGeometry.Differential.regularDifferentialSubmoduleOfSimplePole
        P)
      (x := eta)).mp hmk
  · intro hregular
    exact QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)) P eta hregular

/-- On a candidate place, zero source residue is exactly nonnegative local
differential order. -/
theorem f1024Why24OddCandidateResidue_eq_zero_iff_order_nonnegative
    (r : ℕ) (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    f1024Why24OddCandidateResidue r i = 0 ↔
      0 ≤
        QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
          (k := F1024) (F := F1024TowerLevel (2 * r + 2))
          (f1024Why24OddCandidateRationalPlace r i).place
          (f1024Why24OddDifferential r)
          (f1024Why24OddDifferential_ne_zero r) := by
  let Q := f1024Why24OddCandidateRationalPlace r i
  let eta : QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferentialLattice
      Q.place :=
    ⟨f1024Why24OddDifferential r,
      f1024Why24OddCandidateDifferential_mem_simplePole r i⟩
  change Q.constantsEquiv.symm
      (QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)) Q.place eta) = 0 ↔ _
  rw [← map_zero Q.constantsEquiv.symm]
  rw [Q.constantsEquiv.symm.injective.eq_iff]
  rw [f1024Why24Odd_simplePoleResidue_eq_zero_iff_mem_local Q.place eta]
  exact QEC.Coding.AlgebraicGeometry.Differential.mem_localDifferentialLattice_iff_differentialOrder_nonnegative
      (k := F1024) (F := F1024TowerLevel (2 * r + 2)) Q.place
      (f1024Why24OddDifferential r)
      (f1024Why24OddDifferential_ne_zero r)

/-- Candidate indices at which the actual source residue vanishes. -/
noncomputable def f1024Why24OddBadCandidateIndices (r : ℕ) :
    Finset (Fin (selectedPlaceCount (oddGenus r) - 2)) := by
  classical
  exact Finset.univ.filter fun i => f1024Why24OddCandidateResidue r i = 0

private noncomputable def f1024Why24OddBadCandidateDivisor (r : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :=
  QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor
    (f1024Why24OddCandidateRationalPlace r)
    (f1024Why24OddBadCandidateIndices r)

private theorem f1024Why24OddDifferentialLowerDivisor_apply_candidate
    (r : ℕ) (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    (7 • f1024Why24OddADivisor r + f1024Why24OddEDivisor r -
        f1024Why24OddEvaluationDivisor r)
        (f1024Why24OddCandidateRationalPlace r i).place = -1 := by
  simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.nsmul_apply,
    f1024Why24OddADivisor_apply_candidate,
    f1024Why24OddEDivisor_apply_candidate,
    f1024Why24OddEvaluationDivisor_apply_candidate]
  norm_num

private theorem f1024Why24OddDifferentialLowerDivisor_degree (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (7 • f1024Why24OddADivisor r + f1024Why24OddEDivisor r -
          f1024Why24OddEvaluationDivisor r) =
      (oddGenus r : ℤ) - 2 := by
  rw [Divisor.degree_sub, Divisor.degree_add,
    f1024Why24Odd_divisor_degree_nsmul,
    f1024Why24OddADivisor_degree, f1024Why24OddEDivisor_degree,
    f1024Why24OddEvaluationDivisor_degree]
  have hidentity := f1024Why24Odd_parameter_degree_identity r
  omega

private theorem f1024Why24OddBadCandidateDivisor_augmented_le (r : ℕ) :
    7 • f1024Why24OddADivisor r + f1024Why24OddEDivisor r -
          f1024Why24OddEvaluationDivisor r +
        f1024Why24OddBadCandidateDivisor r ≤
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        (f1024Why24OddDifferential r)
        (f1024Why24OddDifferential_ne_zero r) := by
  classical
  intro P
  by_cases hselected : ∃ i,
      i ∈ f1024Why24OddBadCandidateIndices r ∧
        (f1024Why24OddCandidateRationalPlace r i).place = P
  · obtain ⟨i, hi, rfl⟩ := hselected
    have hregular : 0 ≤
        QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
          (k := F1024) (F := F1024TowerLevel (2 * r + 2))
          (f1024Why24OddCandidateRationalPlace r i).place
          (f1024Why24OddDifferential r)
          (f1024Why24OddDifferential_ne_zero r) :=
      (f1024Why24OddCandidateResidue_eq_zero_iff_order_nonnegative r i).mp
        (Finset.mem_filter.mp hi).2
    rw [Finsupp.add_apply,
      f1024Why24OddDifferentialLowerDivisor_apply_candidate,
      f1024Why24OddBadCandidateDivisor,
      QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor_apply_at
        (f1024Why24OddCandidateRationalPlace r)
        (f1024Why24OddCandidateRationalPlace_injective r)
        (f1024Why24OddBadCandidateIndices r) hi,
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_apply]
    omega
  · have hzero : f1024Why24OddBadCandidateDivisor r P = 0 := by
      apply QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor_apply_eq_zero_of_not_mem
      intro i hi hplace
      exact hselected ⟨i, hi, hplace⟩
    rw [Finsupp.add_apply, hzero, add_zero]
    exact f1024Why24OddDifferentialDivisor_lower_bound r P

private theorem f1024Why24Odd_divisorDegree_mono
    {r : ℕ}
    {D E : Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2)))} (hDE : D ≤ E) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2))) D ≤
      Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2))) E := by
  have hnonnegative : Divisor.Nonnegative (E - D) := by
    intro P
    exact sub_nonneg.mpr (hDE P)
  have hdegreeNonnegative : 0 ≤
      Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2))) (E - D) :=
    Divisor.degree_nonnegative _ _ hnonnegative
  have heq : D + (E - D) = E := by
    ext P
    simp only [Finsupp.add_apply, Finsupp.sub_apply]
    omega
  rw [← heq, Divisor.degree_add]
  exact le_add_of_nonneg_right hdegreeNonnegative

/-- At most `g` candidate rational places have zero source residue. -/
theorem f1024Why24OddBadCandidateIndices_card_le_genus (r : ℕ) :
    (f1024Why24OddBadCandidateIndices r).card ≤ oddGenus r := by
  have hdegree := f1024Why24Odd_divisorDegree_mono
    (f1024Why24OddBadCandidateDivisor_augmented_le r)
  rw [Divisor.degree_add,
    f1024Why24OddDifferentialLowerDivisor_degree,
    f1024Why24OddBadCandidateDivisor,
    QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor_degree_eq_card,
    QEC.Coding.AlgebraicGeometry.CanonicalDivisor.degree_eq_two_mul_genus_sub_two
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_isCanonical
          (f1024Why24OddDifferential r)
          (f1024Why24OddDifferential_ne_zero r)),
    f1024TowerLevel_functionFieldGenus_even] at hdegree
  exact_mod_cast (show ((f1024Why24OddBadCandidateIndices r).card : ℤ) ≤
    oddGenus r by omega)

private noncomputable def f1024Why24OddRetainedCandidateIndices (r : ℕ) :
    Finset (Fin (selectedPlaceCount (oddGenus r) - 2)) := by
  classical
  exact Finset.univ.filter fun i => f1024Why24OddCandidateResidue r i ≠ 0

/-- The actual candidate indices remaining after zero-residue removal. -/
def f1024Why24OddRetainedCandidateIndex (r : ℕ) :=
  {i // i ∈ f1024Why24OddRetainedCandidateIndices r}

noncomputable instance f1024Why24OddRetainedCandidateIndexFintype (r : ℕ) :
    Fintype (f1024Why24OddRetainedCandidateIndex r) := by
  classical
  exact Fintype.subtype (f1024Why24OddRetainedCandidateIndices r) (by simp)

noncomputable instance f1024Why24OddRetainedCandidateIndexDecidableEq (r : ℕ) :
    DecidableEq (f1024Why24OddRetainedCandidateIndex r) :=
  Classical.decEq _

private theorem f1024Why24OddRetainedCandidateIndex_card (r : ℕ) :
    Fintype.card (f1024Why24OddRetainedCandidateIndex r) =
      (f1024Why24OddRetainedCandidateIndices r).card := by
  classical
  have hport := Fintype.card_coe (f1024Why24OddRetainedCandidateIndices r)
  simp only [f1024Why24OddRetainedCandidateIndex] at hport ⊢
  exact hport

/-- WHY24's lower bound `n'' - g ≤ N` for the actual retained set. -/
theorem f1024Why24OddRetainedCandidateIndex_card_lower_bound (r : ℕ) :
    selectedPlaceCount (oddGenus r) - 2 - oddGenus r ≤
      Fintype.card (f1024Why24OddRetainedCandidateIndex r) := by
  classical
  have hpartition :
      (f1024Why24OddBadCandidateIndices r).card +
          (f1024Why24OddRetainedCandidateIndices r).card =
        selectedPlaceCount (oddGenus r) - 2 := by
    unfold f1024Why24OddBadCandidateIndices
      f1024Why24OddRetainedCandidateIndices
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ :
          Finset (Fin (selectedPlaceCount (oddGenus r) - 2))))
        (p := fun i => f1024Why24OddCandidateResidue r i = 0))
  have hbad := f1024Why24OddBadCandidateIndices_card_le_genus r
  rw [f1024Why24OddRetainedCandidateIndex_card]
  omega

private theorem f1024Why24OddRetainedCandidateIndex_card_pos (r : ℕ) :
    0 < Fintype.card (f1024Why24OddRetainedCandidateIndex r) := by
  have hretained := f1024Why24OddRetainedCandidateIndex_card_lower_bound r
  have hlarge := f1024Why24OddGenus_lower_bound r
  simp only [selectedPlaceCount] at hretained
  omega

noncomputable instance f1024Why24OddRetainedCandidateIndexNonempty (r : ℕ) :
    Nonempty (f1024Why24OddRetainedCandidateIndex r) :=
  Fintype.card_pos_iff.mp (f1024Why24OddRetainedCandidateIndex_card_pos r)

/-- The retained set is a subset of the original `n''` candidates. -/
theorem f1024Why24OddRetainedCandidateIndex_card_upper_bound (r : ℕ) :
    Fintype.card (f1024Why24OddRetainedCandidateIndex r) ≤
      selectedPlaceCount (oddGenus r) - 2 := by
  classical
  rw [f1024Why24OddRetainedCandidateIndex_card]
  calc
    (f1024Why24OddRetainedCandidateIndices r).card ≤
        (Finset.univ :
          Finset (Fin (selectedPlaceCount (oddGenus r) - 2))).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = selectedPlaceCount (oddGenus r) - 2 := by
      simp only [Finset.card_univ, Fintype.card_fin]

/-- The actual retained rational-place family. -/
noncomputable def f1024Why24OddRetainedRationalPlace (r : ℕ) :
    f1024Why24OddRetainedCandidateIndex r →
      QEC.Coding.AlgebraicGeometry.RationalPlace F1024
        (F1024TowerLevel (2 * r + 2)) :=
  fun i => f1024Why24OddCandidateRationalPlace r i.1

/-- Retained indices still name pairwise distinct actual global places. -/
theorem f1024Why24OddRetainedRationalPlace_injective (r : ℕ) :
    Function.Injective
      (fun i => (f1024Why24OddRetainedRationalPlace r i).place) := by
  intro i j hij
  apply Subtype.ext
  exact f1024Why24OddCandidateRationalPlace_injective r hij

/-- Every retained place is an exact simple pole of the chosen differential. -/
theorem f1024Why24OddRetainedDifferentialOrder_eq_neg_one (r : ℕ)
    (i : f1024Why24OddRetainedCandidateIndex r) :
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        (f1024Why24OddRetainedRationalPlace r i).place
        (f1024Why24OddDifferential r)
        (f1024Why24OddDifferential_ne_zero r) = -1 := by
  have hlower := f1024Why24OddCandidateDifferentialOrder_lower_bound r i.1
  have hresidue : f1024Why24OddCandidateResidue r i.1 ≠ 0 :=
    (Finset.mem_filter.mp i.2).2
  have hnotRegular : ¬ 0 ≤
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        (f1024Why24OddCandidateRationalPlace r i.1).place
        (f1024Why24OddDifferential r)
        (f1024Why24OddDifferential_ne_zero r) := by
    exact fun hregular => hresidue
      ((f1024Why24OddCandidateResidue_eq_zero_iff_order_nonnegative r i.1).mpr
        hregular)
  change QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024Why24OddCandidateRationalPlace r i.1).place
      (f1024Why24OddDifferential r)
      (f1024Why24OddDifferential_ne_zero r) = -1
  omega

/-- The retained source residue is nonzero by construction. -/
theorem f1024Why24OddRetainedResidue_ne_zero (r : ℕ)
    (i : f1024Why24OddRetainedCandidateIndex r) :
    f1024Why24OddCandidateResidue r i.1 ≠ 0 :=
  (Finset.mem_filter.mp i.2).2

/-!
## The retained AG evaluation code and residue scaling

The source now evaluates `L(A)` on the actual retained rational places.  Its
dimension and dual-distance inputs are consequences of the Riemann--Roch AG
code API and the literal floor arithmetic above.  Coordinate scaling is then
performed by the deterministic seventh roots already constructed in this
module; no code or product identity is stored in family metadata.
-/

/-- The reduced divisor supported on precisely the retained evaluation
places. -/
noncomputable def f1024Why24OddRetainedEvaluationDivisor (r : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :=
  QEC.Coding.AlgebraicGeometry.evaluationDivisor
    (f1024Why24OddRetainedRationalPlace r)

/-- Every retained rational place occurs with coefficient one. -/
theorem f1024Why24OddRetainedEvaluationDivisor_apply (r : ℕ)
    (i : f1024Why24OddRetainedCandidateIndex r) :
    f1024Why24OddRetainedEvaluationDivisor r
        (f1024Why24OddRetainedRationalPlace r i).place = 1 :=
  QEC.Coding.AlgebraicGeometry.evaluationDivisor_apply_at
    (f1024Why24OddRetainedRationalPlace r)
    (f1024Why24OddRetainedRationalPlace_injective r) i

/-- The retained evaluation divisor has degree equal to the actual retained
place count. -/
theorem f1024Why24OddRetainedEvaluationDivisor_degree (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddRetainedEvaluationDivisor r) =
      Fintype.card (f1024Why24OddRetainedCandidateIndex r) := by
  simpa only [f1024Why24OddRetainedEvaluationDivisor] using
    QEC.Coding.AlgebraicGeometry.evaluationDivisor_degree_eq_card
      (f1024Why24OddRetainedRationalPlace r)

/-- `A` is disjoint from every retained evaluation place. -/
theorem f1024Why24OddADivisor_apply_retained (r : ℕ)
    (i : f1024Why24OddRetainedCandidateIndex r) :
    f1024Why24OddADivisor r
        (f1024Why24OddRetainedRationalPlace r i).place = 0 :=
  f1024Why24OddADivisor_apply_candidate r i.1

private theorem f1024Why24Odd_largeDegree (r : ℕ) :
    2 * (oddGenus r : ℤ) - 1 ≤
      (selectedDivisorDegree (oddGenus r) : ℤ) := by
  have hmod := f1024Why24OddGenus_mod_eight r
  have hlarge := f1024Why24OddGenus_lower_bound r
  simp only [selectedDivisorDegree]
  omega

private theorem f1024Why24Odd_divisorDegree_lt_retainedCard (r : ℕ) :
    selectedDivisorDegree (oddGenus r) <
      Fintype.card (f1024Why24OddRetainedCandidateIndex r) := by
  have hretained := f1024Why24OddRetainedCandidateIndex_card_lower_bound r
  have hmod := f1024Why24OddGenus_mod_eight r
  have hlarge := f1024Why24OddGenus_lower_bound r
  simp only [selectedDivisorDegree, selectedPlaceCount] at hretained ⊢
  omega

/-- The genuine retained AG evaluation code `C_L(D,A)`. -/
noncomputable def f1024Why24OddAGCode (r : ℕ) :
    QEC.Coding.LinearCode F1024
      (f1024Why24OddRetainedCandidateIndex r) :=
  QEC.Coding.AlgebraicGeometry.agEvaluationCode
    (f1024Why24OddADivisor r)
    (f1024Why24OddRetainedRationalPlace r)
    (f1024Why24OddADivisor_apply_retained r)

/-- The retained code has the exact large-degree Riemann--Roch dimension
`a + 1 - g`. -/
theorem f1024Why24OddAGCode_dimension (r : ℕ) :
    (QEC.Coding.Dimension (f1024Why24OddAGCode r) : ℤ) =
      (selectedDivisorDegree (oddGenus r) : ℤ) + 1 - oddGenus r := by
  have hlarge :
      2 * (QEC.Coding.AlgebraicGeometry.GlobalPlace.functionFieldGenus F1024
          (F1024TowerLevel (2 * r + 2)) : ℤ) - 1 ≤
        Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
          (f1024Why24OddADivisor r) := by
    rw [f1024TowerLevel_functionFieldGenus_even,
      f1024Why24OddADivisor_degree]
    exact f1024Why24Odd_largeDegree r
  have hsmall :
      Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
          (f1024Why24OddADivisor r) <
        Fintype.card (f1024Why24OddRetainedCandidateIndex r) := by
    rw [f1024Why24OddADivisor_degree]
    exact_mod_cast f1024Why24Odd_divisorDegree_lt_retainedCard r
  simpa only [f1024Why24OddAGCode, f1024Why24OddADivisor_degree,
    f1024TowerLevel_functionFieldGenus_even] using
    QEC.Coding.AlgebraicGeometry.agEvaluation_dimension_eq_of_large_degree
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024Why24OddADivisor r)
      (f1024Why24OddRetainedRationalPlace r)
      (f1024Why24OddRetainedRationalPlace_injective r)
      (f1024Why24OddADivisor_apply_retained r)
      hlarge hsmall

/-- The actual retained AG-code dual satisfies its complementary designed
distance bound. -/
theorem f1024Why24OddAGCode_dual_distance_lower_bound (r : ℕ) :
    (Int.toNat
      ((selectedDivisorDegree (oddGenus r) : ℤ) + 2 -
        2 * (oddGenus r : ℤ)) : WithTop ℕ) ≤
      QEC.Coding.HypergraphProduct.extendedMinimumDistance
        (f1024Why24OddAGCode r).dual := by
  have hlarge :
      2 * (QEC.Coding.AlgebraicGeometry.GlobalPlace.functionFieldGenus F1024
          (F1024TowerLevel (2 * r + 2)) : ℤ) - 1 ≤
        Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
          (f1024Why24OddADivisor r) := by
    rw [f1024TowerLevel_functionFieldGenus_even,
      f1024Why24OddADivisor_degree]
    exact f1024Why24Odd_largeDegree r
  have hsmall :
      Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
          (f1024Why24OddADivisor r) <
        Fintype.card (f1024Why24OddRetainedCandidateIndex r) := by
    rw [f1024Why24OddADivisor_degree]
    exact_mod_cast f1024Why24Odd_divisorDegree_lt_retainedCard r
  simpa only [f1024Why24OddAGCode, f1024Why24OddADivisor_degree,
    f1024TowerLevel_functionFieldGenus_even] using
    QEC.Coding.AlgebraicGeometry.agEvaluation_dual_distance_lower_bound
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024Why24OddADivisor r)
      (f1024Why24OddRetainedRationalPlace r)
      (f1024Why24OddRetainedRationalPlace_injective r)
      (f1024Why24OddADivisor_apply_retained r)
      hlarge hsmall

/-- The deterministic seventh root of the actual nonzero residue at a
retained coordinate. -/
noncomputable def f1024Why24OddCoordinateWeight (r : ℕ)
    (i : f1024Why24OddRetainedCandidateIndex r) : F1024 :=
  f1024SeventhRoot (f1024Why24OddCandidateResidue r i.1)

/-- The seventh power of the coordinate weight is exactly the source
residue. -/
theorem f1024Why24OddCoordinateWeight_pow_seven (r : ℕ)
    (i : f1024Why24OddRetainedCandidateIndex r) :
    (f1024Why24OddCoordinateWeight r i) ^ 7 =
      f1024Why24OddCandidateResidue r i.1 :=
  f1024SeventhRoot_pow_seven _

/-- Every retained coordinate weight is nonzero. -/
theorem f1024Why24OddCoordinateWeight_ne_zero (r : ℕ)
    (i : f1024Why24OddRetainedCandidateIndex r) :
    f1024Why24OddCoordinateWeight r i ≠ 0 := by
  intro hzero
  apply f1024Why24OddRetainedResidue_ne_zero r i
  rw [← f1024Why24OddCoordinateWeight_pow_seven r i]
  simp only [hzero]
  norm_num

/-- Evaluation on retained places followed by the source's invertible
coordinate scaling. -/
noncomputable def f1024Why24OddScaledEvaluationLinearMap (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r) →ₗ[F1024]
      QEC.Coding.Word F1024 (f1024Why24OddRetainedCandidateIndex r) where
  toFun x i := f1024Why24OddCoordinateWeight r i *
    QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
      (f1024Why24OddADivisor r)
      (f1024Why24OddRetainedRationalPlace r)
      (f1024Why24OddADivisor_apply_retained r) x i
  map_add' x y := by
    funext i
    simp only [map_add, Pi.add_apply]
    ring
  map_smul' c x := by
    funext i
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    change f1024Why24OddCoordinateWeight r i *
        (c * QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddRetainedRationalPlace r)
          (f1024Why24OddADivisor_apply_retained r) x i) =
      c * (f1024Why24OddCoordinateWeight r i *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddRetainedRationalPlace r)
          (f1024Why24OddADivisor_apply_retained r) x i)
    ring

/-- The actual coordinate-scaled retained AG code. -/
noncomputable def f1024Why24OddScaledAGCode (r : ℕ) :
    QEC.Coding.LinearCode F1024
      (f1024Why24OddRetainedCandidateIndex r) where
  carrier := (f1024Why24OddScaledEvaluationLinearMap r).range

/-- Every scaled evaluation lies in the actual scaled code. -/
theorem f1024Why24OddScaledEvaluationLinearMap_mem (r : ℕ)
    (x : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r)) :
    f1024Why24OddScaledEvaluationLinearMap r x ∈
      (f1024Why24OddScaledAGCode r).carrier :=
  ⟨x, rfl⟩

private theorem f1024Why24OddADivisor_nonnegative (r : ℕ) :
    Divisor.Nonnegative (f1024Why24OddADivisor r) := by
  intro P
  by_cases hP : P = (f1024Why24OddAPlace r).place
  · subst P
    rw [f1024Why24OddADivisor_apply_APlace]
    exact_mod_cast Nat.zero_le (selectedDivisorDegree (oddGenus r))
  · simp [f1024Why24OddADivisor, hP]

private theorem f1024Why24OddEDivisor_nonnegative (r : ℕ) :
    Divisor.Nonnegative (f1024Why24OddEDivisor r) := by
  intro P
  by_cases hP : P = (f1024Why24OddEPlace r).place
  · subst P
    rw [f1024Why24OddEDivisor_apply_EPlace]
    exact_mod_cast Nat.zero_le (selectedEDegree (oddGenus r))
  · simp [f1024Why24OddEDivisor, hP]

private theorem f1024Why24OddEvaluationDivisor_apply_eq_zero_or_one
    (r : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :
    f1024Why24OddEvaluationDivisor r P = 0 ∨
      f1024Why24OddEvaluationDivisor r P = 1 := by
  by_cases hselected : ∃ i,
      (f1024Why24OddCandidateRationalPlace r i).place = P
  · obtain ⟨i, rfl⟩ := hselected
    exact Or.inr (f1024Why24OddEvaluationDivisor_apply_candidate r i)
  · left
    have hport := QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor_apply_eq_zero_of_not_mem
      (f1024Why24OddCandidateRationalPlace r) Finset.univ P (by
        intro i _ hplace
        exact hselected ⟨i, hplace⟩)
    simp only [f1024Why24OddEvaluationDivisor] at hport ⊢
    exact hport

private theorem f1024Why24OddSevenADivisor_apply_candidate (r : ℕ)
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    (7 • f1024Why24OddADivisor r)
        (f1024Why24OddCandidateRationalPlace r i).place = 0 := by
  simp only [Finsupp.nsmul_apply,
    f1024Why24OddADivisor_apply_candidate, nsmul_zero]

private noncomputable def f1024Why24OddResidueProductDifferential (r : ℕ)
    (f : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (7 • f1024Why24OddADivisor r)) :
    QEC.Coding.AlgebraicGeometry.Differential F1024
      (F1024TowerLevel (2 * r + 2)) :=
  (f : F1024TowerLevel (2 * r + 2)) • f1024Why24OddDifferential r

private theorem f1024Why24OddResidueProduct_isGlobalSimplePole (r : ℕ)
    (f : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (7 • f1024Why24OddADivisor r)) :
    QEC.Coding.AlgebraicGeometry.Differential.IsGlobalSimplePole
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024Why24OddResidueProductDifferential r f) := by
  intro P
  by_cases hf : (f : F1024TowerLevel (2 * r + 2)) = 0
  · simp only [f1024Why24OddResidueProductDifferential, hf, zero_smul]
    exact
      (QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferentialLattice P).zero_mem
  apply
    (QEC.Coding.AlgebraicGeometry.Differential.smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
      (k := F1024) (F := F1024TowerLevel (2 * r + 2)) P
      (f : F1024TowerLevel (2 * r + 2)) hf
      (f1024Why24OddDifferential r)
      (f1024Why24OddDifferential_ne_zero r)).mpr
  have hfP :=
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
      (7 • f1024Why24OddADivisor r) hf).mp f.property P
  have hdifferential := f1024Why24OddDifferentialDivisor_lower_bound r P
  have hE := f1024Why24OddEDivisor_nonnegative r P
  simp only [Finsupp.nsmul_apply, Finsupp.add_apply, Finsupp.sub_apply,
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_apply]
    at hfP hdifferential
  rcases f1024Why24OddEvaluationDivisor_apply_eq_zero_or_one r P with hD | hD
  · rw [hD] at hdifferential
    omega
  · rw [hD] at hdifferential
    omega

private theorem f1024Why24OddResidueProduct_mem_local_of_not_candidate
    (r : ℕ)
    (f : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (7 • f1024Why24OddADivisor r))
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2)))
    (hP : ¬ ∃ i, (f1024Why24OddCandidateRationalPlace r i).place = P) :
    f1024Why24OddResidueProductDifferential r f ∈
      QEC.Coding.AlgebraicGeometry.Differential.localDifferentialLattice P := by
  by_cases hf : (f : F1024TowerLevel (2 * r + 2)) = 0
  · simp only [f1024Why24OddResidueProductDifferential, hf, zero_smul]
    exact
      (QEC.Coding.AlgebraicGeometry.Differential.localDifferentialLattice P).zero_mem
  apply
    (QEC.Coding.AlgebraicGeometry.Differential.smul_mem_localDifferentialLattice_iff_order_add_nonnegative
      (k := F1024) (F := F1024TowerLevel (2 * r + 2)) P
      (f : F1024TowerLevel (2 * r + 2)) hf
      (f1024Why24OddDifferential r)
      (f1024Why24OddDifferential_ne_zero r)).mpr
  have hfP :=
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
      (7 • f1024Why24OddADivisor r) hf).mp f.property P
  have hdifferential := f1024Why24OddDifferentialDivisor_lower_bound r P
  have hE := f1024Why24OddEDivisor_nonnegative r P
  have hD : f1024Why24OddEvaluationDivisor r P = 0 := by
    have hport := QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor_apply_eq_zero_of_not_mem
      (f1024Why24OddCandidateRationalPlace r) Finset.univ P (by
        intro i _ hplace
        exact hP ⟨i, hplace⟩)
    simp only [f1024Why24OddEvaluationDivisor] at hport ⊢
    exact hport
  simp only [Finsupp.nsmul_apply, Finsupp.add_apply, Finsupp.sub_apply,
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_apply,
    hD, sub_zero] at hfP hdifferential
  omega

private theorem f1024Why24Odd_simplePoleTraceResidue_rational_eq_coordinate
    {r : ℕ}
    (Q : QEC.Coding.AlgebraicGeometry.RationalPlace F1024
      (F1024TowerLevel (2 * r + 2)))
    (eta : QEC.Coding.AlgebraicGeometry.Differential F1024
      (F1024TowerLevel (2 * r + 2)))
    (heta : eta ∈
      QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferentialLattice
        Q.place) :
    QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)) Q.place eta heta =
      Q.constantsEquiv.symm
        (QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)) Q.place
          ⟨eta, heta⟩) := by
  letI : Algebra F1024 Q.place.residueField :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.residueAlgebra Q.place
  letI : FiniteDimensional F1024 Q.place.residueField :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.residueField_finiteDimensional Q.place
  obtain ⟨c, hc⟩ := Q.constantsEquiv.surjective
    (QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue
      (k := F1024) (F := F1024TowerLevel (2 * r + 2)) Q.place ⟨eta, heta⟩)
  change Algebra.trace F1024 Q.place.residueField
      (QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)) Q.place
        ⟨eta, heta⟩) = _
  rw [← hc, Q.constantsEquiv_apply]
  have hconstants : Q.place.constantsToResidue c =
      algebraMap F1024 Q.place.residueField c := rfl
  rw [hconstants, Algebra.trace_algebraMap]
  have hcoordinate :
      Q.constantsEquiv.symm (algebraMap F1024 Q.place.residueField c) = c := by
    rw [← hconstants, ← Q.constantsEquiv_apply,
      Q.constantsEquiv.symm_apply_apply]
  have hfinrank : Module.finrank F1024 Q.place.residueField = 1 := by
    apply Module.finrank_of_bijective_algebraMap
    simpa only [QEC.Coding.AlgebraicGeometry.GlobalPlace.residueAlgebra,
      RingHom.algebraMap_toAlgebra] using Q.constantsToResidue_bijective
  rw [hfinrank, hcoordinate]
  simp

private theorem f1024Why24OddResidueProduct_traceResidue_at (r : ℕ)
    (f : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (7 • f1024Why24OddADivisor r))
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        (f1024Why24OddCandidateRationalPlace r i).place
        (f1024Why24OddResidueProductDifferential r f)
        (f1024Why24OddResidueProduct_isGlobalSimplePole r f
          (f1024Why24OddCandidateRationalPlace r i).place) =
      f1024Why24OddCandidateResidue r i *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (7 • f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddSevenADivisor_apply_candidate r) f i := by
  let Q := f1024Why24OddCandidateRationalPlace r i
  let eta := f1024Why24OddDifferential r
  have hetaSimple : eta ∈
      QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferentialLattice
        Q.place :=
    f1024Why24OddCandidateDifferential_mem_simplePole r i
  have hfRegular :
      QEC.Coding.AlgebraicGeometry.GlobalPlace.RegularAt Q.place
        (f : F1024TowerLevel (2 * r + 2)) := by
    have hbound :=
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_riemannRochSubmodule_iff
        (7 • f1024Why24OddADivisor r)
        (f : F1024TowerLevel (2 * r + 2))).mp f.property Q.place
    rw [f1024Why24OddSevenADivisor_apply_candidate r i] at hbound
    have hport := hbound
    simp only [WithZero.exp_zero] at hport ⊢
    exact hport
  let fO : Q.place.valuationRing :=
    ⟨(f : F1024TowerLevel (2 * r + 2)),
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_valuationRing_iff
        Q.place _).mpr hfRegular⟩
  rw [f1024Why24Odd_simplePoleTraceResidue_rational_eq_coordinate Q]
  have hsubtype :
      (⟨f1024Why24OddResidueProductDifferential r f,
          f1024Why24OddResidueProduct_isGlobalSimplePole r f Q.place⟩ :
        QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferentialLattice
          Q.place) =
      fO • (⟨eta, hetaSimple⟩ :
        QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferentialLattice
          Q.place) := by
    rfl
  rw [hsubtype,
    QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_smul, map_mul]
  change Q.evaluate fO * f1024Why24OddCandidateResidue r i =
    f1024Why24OddCandidateResidue r i *
      QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
        (7 • f1024Why24OddADivisor r)
        (f1024Why24OddCandidateRationalPlace r)
        (f1024Why24OddSevenADivisor_apply_candidate r) f i
  rw [mul_comm]
  rfl

private theorem f1024Why24OddResiduePairing_eq_zero (r : ℕ)
    (f : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (7 • f1024Why24OddADivisor r)) :
    (∑ i : Fin (selectedPlaceCount (oddGenus r) - 2),
      f1024Why24OddCandidateResidue r i *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (7 • f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddSevenADivisor_apply_candidate r) f i) = 0 := by
  classical
  let eta := f1024Why24OddResidueProductDifferential r f
  let heta := f1024Why24OddResidueProduct_isGlobalSimplePole r f
  let residues :
      QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
          (F1024TowerLevel (2 * r + 2)) →₀ F1024 :=
    QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidue
      (k := F1024) (F := F1024TowerLevel (2 * r + 2)) eta heta
  have hsupport : residues.support ⊆
      Finset.univ.image
        (fun i => (f1024Why24OddCandidateRationalPlace r i).place) := by
    intro P hP
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    by_contra hnotSelected
    have hregular : eta ∈
        QEC.Coding.AlgebraicGeometry.Differential.localDifferentialLattice P :=
      f1024Why24OddResidueProduct_mem_local_of_not_candidate r f P hnotSelected
    have hzero :=
      QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)) P eta
        (heta P) hregular
    have hcoefficient : residues P = 0 := by
      change QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)) P eta
        (heta P) = 0
      exact hzero
    exact (Finsupp.mem_support_iff.mp hP) hcoefficient
  have hsumSupport :
      residues.sum (fun _ coefficient => coefficient) =
        ∑ P ∈ Finset.univ.image
          (fun i => (f1024Why24OddCandidateRationalPlace r i).place),
          residues P :=
    Finsupp.sum_of_support_subset residues hsupport
      (fun _ coefficient => coefficient) (fun _ _ => rfl)
  have hsumImage :
      (∑ P ∈ Finset.univ.image
          (fun i => (f1024Why24OddCandidateRationalPlace r i).place),
          residues P) =
        ∑ i : Fin (selectedPlaceCount (oddGenus r) - 2),
          residues (f1024Why24OddCandidateRationalPlace r i).place := by
    rw [Finset.sum_image]
    intro i _ j _ hij
    exact f1024Why24OddCandidateRationalPlace_injective r hij
  have hcoefficient (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
      residues (f1024Why24OddCandidateRationalPlace r i).place =
        f1024Why24OddCandidateResidue r i *
          QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
            (7 • f1024Why24OddADivisor r)
            (f1024Why24OddCandidateRationalPlace r)
            (f1024Why24OddSevenADivisor_apply_candidate r) f i := by
    change QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        (f1024Why24OddCandidateRationalPlace r i).place eta
        (heta (f1024Why24OddCandidateRationalPlace r i).place) = _
    exact f1024Why24OddResidueProduct_traceResidue_at r f i
  have hsumZero :=
    QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_eq_zero
      (k := F1024) (F := F1024TowerLevel (2 * r + 2)) eta heta
  change residues.sum (fun _ coefficient => coefficient) = 0 at hsumZero
  calc
    _ = ∑ i : Fin (selectedPlaceCount (oddGenus r) - 2),
        residues (f1024Why24OddCandidateRationalPlace r i).place := by
      apply Finset.sum_congr rfl
      intro i _
      exact (hcoefficient i).symm
    _ = residues.sum (fun _ coefficient => coefficient) :=
      hsumImage.symm.trans hsumSupport.symm
    _ = 0 := hsumZero

private theorem f1024Why24OddA_add_A_le_sevenA (r : ℕ) :
    f1024Why24OddADivisor r + f1024Why24OddADivisor r ≤
      7 • f1024Why24OddADivisor r := by
  intro P
  have hA := f1024Why24OddADivisor_nonnegative r P
  simp only [Finsupp.add_apply, Finsupp.nsmul_apply, nsmul_eq_mul]
  omega

private noncomputable def f1024Why24OddPairFunction (r : ℕ)
    (x y : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r)) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (7 • f1024Why24OddADivisor r) :=
  ⟨(x : F1024TowerLevel (2 * r + 2)) *
      (y : F1024TowerLevel (2 * r + 2)),
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule_mono
      (f1024Why24OddA_add_A_le_sevenA r)
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.mul_mem_riemannRochSubmodule_add
        x.property y.property)⟩

private theorem f1024Why24OddSevenProduct_mem (r : ℕ)
    (x y z : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r)) :
    (x : F1024TowerLevel (2 * r + 2)) ^ 4 *
          (y : F1024TowerLevel (2 * r + 2)) ^ 2 *
            (z : F1024TowerLevel (2 * r + 2)) ∈
      QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (7 • f1024Why24OddADivisor r) := by
  let A := f1024Why24OddADivisor r
  have hx2 :
      (x : F1024TowerLevel (2 * r + 2)) *
          (x : F1024TowerLevel (2 * r + 2)) ∈
        QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          (A + A) :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.mul_mem_riemannRochSubmodule_add
      x.property x.property
  have hx4 :
      ((x : F1024TowerLevel (2 * r + 2)) *
          (x : F1024TowerLevel (2 * r + 2))) *
        ((x : F1024TowerLevel (2 * r + 2)) *
          (x : F1024TowerLevel (2 * r + 2))) ∈
        QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          ((A + A) + (A + A)) :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.mul_mem_riemannRochSubmodule_add
      hx2 hx2
  have hy2 :
      (y : F1024TowerLevel (2 * r + 2)) *
          (y : F1024TowerLevel (2 * r + 2)) ∈
        QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          (A + A) :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.mul_mem_riemannRochSubmodule_add
      y.property y.property
  have hxy :
      (((x : F1024TowerLevel (2 * r + 2)) *
          (x : F1024TowerLevel (2 * r + 2))) *
        ((x : F1024TowerLevel (2 * r + 2)) *
          (x : F1024TowerLevel (2 * r + 2)))) *
        ((y : F1024TowerLevel (2 * r + 2)) *
          (y : F1024TowerLevel (2 * r + 2))) ∈
        QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          (((A + A) + (A + A)) + (A + A)) :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.mul_mem_riemannRochSubmodule_add
      hx4 hy2
  have hxyz :
      ((((x : F1024TowerLevel (2 * r + 2)) *
          (x : F1024TowerLevel (2 * r + 2))) *
        ((x : F1024TowerLevel (2 * r + 2)) *
          (x : F1024TowerLevel (2 * r + 2)))) *
        ((y : F1024TowerLevel (2 * r + 2)) *
          (y : F1024TowerLevel (2 * r + 2)))) *
        (z : F1024TowerLevel (2 * r + 2)) ∈
        QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          ((((A + A) + (A + A)) + (A + A)) + A) :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.mul_mem_riemannRochSubmodule_add
      hxy z.property
  have hdivisor : ((((A + A) + (A + A)) + (A + A)) + A) = 7 • A := by
    abel
  rw [show
      (x : F1024TowerLevel (2 * r + 2)) ^ 4 *
            (y : F1024TowerLevel (2 * r + 2)) ^ 2 *
              (z : F1024TowerLevel (2 * r + 2)) =
        ((((x : F1024TowerLevel (2 * r + 2)) *
            (x : F1024TowerLevel (2 * r + 2))) *
          ((x : F1024TowerLevel (2 * r + 2)) *
            (x : F1024TowerLevel (2 * r + 2)))) *
          ((y : F1024TowerLevel (2 * r + 2)) *
            (y : F1024TowerLevel (2 * r + 2)))) *
          (z : F1024TowerLevel (2 * r + 2)) by ring]
  rw [← hdivisor]
  exact hxyz

private noncomputable def f1024Why24OddSevenProductFunction (r : ℕ)
    (x y z : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r)) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (7 • f1024Why24OddADivisor r) :=
  ⟨(x : F1024TowerLevel (2 * r + 2)) ^ 4 *
      (y : F1024TowerLevel (2 * r + 2)) ^ 2 *
        (z : F1024TowerLevel (2 * r + 2)),
    f1024Why24OddSevenProduct_mem r x y z⟩

private theorem f1024Why24Odd_regularAt_candidate
    (r : ℕ)
    (x : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r))
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.RegularAt
      (f1024Why24OddCandidateRationalPlace r i).place
      (x : F1024TowerLevel (2 * r + 2)) := by
  have hbound :=
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_riemannRochSubmodule_iff
      (f1024Why24OddADivisor r)
      (x : F1024TowerLevel (2 * r + 2))).mp x.property
      (f1024Why24OddCandidateRationalPlace r i).place
  rw [f1024Why24OddADivisor_apply_candidate r i] at hbound
  have hport := hbound
  simp only [WithZero.exp_zero] at hport ⊢
  exact hport

private theorem f1024Why24OddPairFunction_evaluation (r : ℕ)
    (x y : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r))
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
        (7 • f1024Why24OddADivisor r)
        (f1024Why24OddCandidateRationalPlace r)
        (f1024Why24OddSevenADivisor_apply_candidate r)
        (f1024Why24OddPairFunction r x y) i =
      QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddADivisor_apply_candidate r) x i *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddADivisor_apply_candidate r) y i := by
  let Q := f1024Why24OddCandidateRationalPlace r i
  let xO : Q.place.valuationRing :=
    ⟨(x : F1024TowerLevel (2 * r + 2)),
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_valuationRing_iff
        Q.place _).mpr (f1024Why24Odd_regularAt_candidate r x i)⟩
  let yO : Q.place.valuationRing :=
    ⟨(y : F1024TowerLevel (2 * r + 2)),
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_valuationRing_iff
        Q.place _).mpr (f1024Why24Odd_regularAt_candidate r y i)⟩
  change Q.evaluate (xO * yO) = Q.evaluate xO * Q.evaluate yO
  exact map_mul Q.evaluate xO yO

private theorem f1024Why24OddSevenProductFunction_evaluation (r : ℕ)
    (x y z : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r))
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
        (7 • f1024Why24OddADivisor r)
        (f1024Why24OddCandidateRationalPlace r)
        (f1024Why24OddSevenADivisor_apply_candidate r)
        (f1024Why24OddSevenProductFunction r x y z) i =
      QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddADivisor_apply_candidate r) x i ^ 4 *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddADivisor_apply_candidate r) y i ^ 2 *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddADivisor_apply_candidate r) z i := by
  let Q := f1024Why24OddCandidateRationalPlace r i
  let xO : Q.place.valuationRing :=
    ⟨(x : F1024TowerLevel (2 * r + 2)),
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_valuationRing_iff
        Q.place _).mpr (f1024Why24Odd_regularAt_candidate r x i)⟩
  let yO : Q.place.valuationRing :=
    ⟨(y : F1024TowerLevel (2 * r + 2)),
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_valuationRing_iff
        Q.place _).mpr (f1024Why24Odd_regularAt_candidate r y i)⟩
  let zO : Q.place.valuationRing :=
    ⟨(z : F1024TowerLevel (2 * r + 2)),
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_valuationRing_iff
        Q.place _).mpr (f1024Why24Odd_regularAt_candidate r z i)⟩
  change Q.evaluate (xO ^ 4 * yO ^ 2 * zO) =
    Q.evaluate xO ^ 4 * Q.evaluate yO ^ 2 * Q.evaluate zO
  rw [map_mul, map_mul, map_pow, map_pow]

private theorem f1024Why24OddRetained_sum_eq_candidate
    (r : ℕ)
    (summand : Fin (selectedPlaceCount (oddGenus r) - 2) → F1024)
    (hzero : ∀ i, f1024Why24OddCandidateResidue r i = 0 →
      summand i = 0) :
    (∑ i : f1024Why24OddRetainedCandidateIndex r, summand i.1) =
      ∑ i : Fin (selectedPlaceCount (oddGenus r) - 2), summand i := by
  classical
  change (∑ i : {i // i ∈ f1024Why24OddRetainedCandidateIndices r},
      summand i.1) = _
  rw [Finset.sum_coe_sort
    (f1024Why24OddRetainedCandidateIndices r) summand]
  unfold f1024Why24OddRetainedCandidateIndices
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : f1024Why24OddCandidateResidue r i = 0
  · simp [hi, hzero i hi]
  · simp [hi]

@[simp] private theorem f1024Why24OddRetainedEvaluation_apply_candidate
    (r : ℕ)
    (x : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r))
    (i : f1024Why24OddRetainedCandidateIndex r) :
    QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
        (f1024Why24OddADivisor r)
        (f1024Why24OddRetainedRationalPlace r)
        (f1024Why24OddADivisor_apply_retained r) x i =
      QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
        (f1024Why24OddADivisor r)
        (f1024Why24OddCandidateRationalPlace r)
        (f1024Why24OddADivisor_apply_candidate r) x i.1 := by
  rfl

/-- WHY24's residue-scaled retained AG evaluations obey the raw seventh
product equation. -/
theorem f1024Why24OddScaledSeventhPairing_eq_zero (r : ℕ)
    (x y z : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r)) :
    (∑ i : f1024Why24OddRetainedCandidateIndex r,
      f1024Why24OddScaledEvaluationLinearMap r x i ^ 4 *
        f1024Why24OddScaledEvaluationLinearMap r y i ^ 2 *
          f1024Why24OddScaledEvaluationLinearMap r z i) = 0 := by
  let summand : Fin (selectedPlaceCount (oddGenus r) - 2) → F1024 :=
    fun i => f1024Why24OddCandidateResidue r i *
      QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddADivisor_apply_candidate r) x i ^ 4 *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddADivisor_apply_candidate r) y i ^ 2 *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddADivisor_apply_candidate r) z i
  calc
    _ = ∑ i : f1024Why24OddRetainedCandidateIndex r, summand i.1 := by
      apply Finset.sum_congr rfl
      intro i _
      change
        (f1024Why24OddCoordinateWeight r i *
            QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
              (f1024Why24OddADivisor r)
              (f1024Why24OddRetainedRationalPlace r)
              (f1024Why24OddADivisor_apply_retained r) x i) ^ 4 *
          (f1024Why24OddCoordinateWeight r i *
            QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
              (f1024Why24OddADivisor r)
              (f1024Why24OddRetainedRationalPlace r)
              (f1024Why24OddADivisor_apply_retained r) y i) ^ 2 *
          (f1024Why24OddCoordinateWeight r i *
            QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
              (f1024Why24OddADivisor r)
              (f1024Why24OddRetainedRationalPlace r)
              (f1024Why24OddADivisor_apply_retained r) z i) = summand i.1
      rw [f1024Why24OddRetainedEvaluation_apply_candidate r x i,
        f1024Why24OddRetainedEvaluation_apply_candidate r y i,
        f1024Why24OddRetainedEvaluation_apply_candidate r z i]
      dsimp only [summand]
      rw [← f1024Why24OddCoordinateWeight_pow_seven r i]
      ring
    _ = ∑ i : Fin (selectedPlaceCount (oddGenus r) - 2), summand i :=
      f1024Why24OddRetained_sum_eq_candidate r summand (by
        intro i hi
        simp [summand, hi])
    _ = 0 := by
      have hzero := f1024Why24OddResiduePairing_eq_zero r
        (f1024Why24OddSevenProductFunction r x y z)
      calc
        _ = ∑ i : Fin (selectedPlaceCount (oddGenus r) - 2),
            f1024Why24OddCandidateResidue r i *
              QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
                (7 • f1024Why24OddADivisor r)
                (f1024Why24OddCandidateRationalPlace r)
                (f1024Why24OddSevenADivisor_apply_candidate r)
                (f1024Why24OddSevenProductFunction r x y z) i := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp only [summand]
          rw [f1024Why24OddSevenProductFunction_evaluation]
          ring
        _ = 0 := hzero

/-- The same physical scaling obeys WHY24's coordinate-weighted bilinear
equation, with weight `w_i^5`. -/
theorem f1024Why24OddScaledWeightedPairing_eq_zero (r : ℕ)
    (x y : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r)) :
    (∑ i : f1024Why24OddRetainedCandidateIndex r,
      f1024Why24OddCoordinateWeight r i ^ 5 *
        f1024Why24OddScaledEvaluationLinearMap r x i *
          f1024Why24OddScaledEvaluationLinearMap r y i) = 0 := by
  let summand : Fin (selectedPlaceCount (oddGenus r) - 2) → F1024 :=
    fun i => f1024Why24OddCandidateResidue r i *
      QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddADivisor_apply_candidate r) x i *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddADivisor_apply_candidate r) y i
  calc
    _ = ∑ i : f1024Why24OddRetainedCandidateIndex r, summand i.1 := by
      apply Finset.sum_congr rfl
      intro i _
      change f1024Why24OddCoordinateWeight r i ^ 5 *
          (f1024Why24OddCoordinateWeight r i *
            QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
              (f1024Why24OddADivisor r)
              (f1024Why24OddRetainedRationalPlace r)
              (f1024Why24OddADivisor_apply_retained r) x i) *
          (f1024Why24OddCoordinateWeight r i *
            QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
              (f1024Why24OddADivisor r)
              (f1024Why24OddRetainedRationalPlace r)
              (f1024Why24OddADivisor_apply_retained r) y i) = summand i.1
      rw [f1024Why24OddRetainedEvaluation_apply_candidate r x i,
        f1024Why24OddRetainedEvaluation_apply_candidate r y i]
      dsimp only [summand]
      rw [← f1024Why24OddCoordinateWeight_pow_seven r i]
      ring
    _ = ∑ i : Fin (selectedPlaceCount (oddGenus r) - 2), summand i :=
      f1024Why24OddRetained_sum_eq_candidate r summand (by
        intro i hi
        simp [summand, hi])
    _ = 0 := by
      have hzero := f1024Why24OddResiduePairing_eq_zero r
        (f1024Why24OddPairFunction r x y)
      calc
        _ = ∑ i : Fin (selectedPlaceCount (oddGenus r) - 2),
            f1024Why24OddCandidateResidue r i *
              QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
                (7 • f1024Why24OddADivisor r)
                (f1024Why24OddCandidateRationalPlace r)
                (f1024Why24OddSevenADivisor_apply_candidate r)
                (f1024Why24OddPairFunction r x y) i := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp only [summand]
          rw [f1024Why24OddPairFunction_evaluation]
          ring
        _ = 0 := hzero

/-!
## Source-faithful systematic shortening

WHY24 next chooses `k = floor (5g/4)` of the retained evaluation places as
systematic pivots.  The restriction of `L(A)` to those actual rational places
is onto: both `A` and `A` minus the pivot divisor are in the large-degree
Riemann--Roch range, and their dimensions differ by exactly `k`.  We use the
resulting linear section, not a stored information-set conclusion, to remove
the pivot coordinates and form the source's weighted-triorthogonal matrix.
-/

/-- The source-selected logical-coordinate type at the odd level `2r+3`. -/
abbrev f1024Why24OddLogical (r : ℕ) : Type :=
  Fin (selectedLogicalCount (oddGenus r))

private theorem f1024Why24OddLogicalCount_le_retainedCard (r : ℕ) :
    selectedLogicalCount (oddGenus r) ≤
      Fintype.card (f1024Why24OddRetainedCandidateIndex r) := by
  have hretained := f1024Why24OddRetainedCandidateIndex_card_lower_bound r
  have hlarge := f1024Why24OddGenus_lower_bound r
  simp only [selectedLogicalCount, selectedPlaceCount] at hretained ⊢
  omega

/-- A concrete choice of `k` distinct pivots inside the actual retained
evaluation coordinates. -/
noncomputable def f1024Why24OddPivotEmbedding (r : ℕ) :
    f1024Why24OddLogical r ↪ f1024Why24OddRetainedCandidateIndex r :=
  (Fin.castLEEmb (f1024Why24OddLogicalCount_le_retainedCard r)).trans
    (Fintype.equivFin (f1024Why24OddRetainedCandidateIndex r)).symm.toEmbedding

/-- The actual rational place at a systematic pivot. -/
noncomputable def f1024Why24OddPivotRationalPlace (r : ℕ) :
    f1024Why24OddLogical r →
      QEC.Coding.AlgebraicGeometry.RationalPlace F1024
        (F1024TowerLevel (2 * r + 2)) :=
  fun a => f1024Why24OddRetainedRationalPlace r
    (f1024Why24OddPivotEmbedding r a)

private theorem f1024Why24OddPivotRationalPlace_injective (r : ℕ) :
    Function.Injective
      (fun a => (f1024Why24OddPivotRationalPlace r a).place) := by
  intro a b hab
  apply (f1024Why24OddPivotEmbedding r).injective
  apply f1024Why24OddRetainedRationalPlace_injective r
  exact hab

/-- The reduced divisor supported on the chosen systematic pivots. -/
noncomputable def f1024Why24OddPivotDivisor (r : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :=
  QEC.Coding.AlgebraicGeometry.evaluationDivisor
    (f1024Why24OddPivotRationalPlace r)

/-- The systematic pivot divisor has degree exactly `k`. -/
theorem f1024Why24OddPivotDivisor_degree (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddPivotDivisor r) =
      (selectedLogicalCount (oddGenus r) : ℤ) := by
  simpa only [f1024Why24OddPivotDivisor, Fintype.card_fin] using
    QEC.Coding.AlgebraicGeometry.evaluationDivisor_degree_eq_card
      (f1024Why24OddPivotRationalPlace r)

private theorem f1024Why24OddADivisor_apply_pivot (r : ℕ)
    (a : f1024Why24OddLogical r) :
    f1024Why24OddADivisor r
        (f1024Why24OddPivotRationalPlace r a).place = 0 :=
  f1024Why24OddADivisor_apply_retained r
    (f1024Why24OddPivotEmbedding r a)

private theorem f1024Why24OddA_sub_pivots_largeDegree (r : ℕ) :
    2 * (QEC.Coding.AlgebraicGeometry.GlobalPlace.functionFieldGenus F1024
          (F1024TowerLevel (2 * r + 2)) : ℤ) - 1 ≤
      Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) := by
  rw [f1024TowerLevel_functionFieldGenus_even, Divisor.degree_sub,
    f1024Why24OddADivisor_degree, f1024Why24OddPivotDivisor_degree]
  have hmod := f1024Why24OddGenus_mod_eight r
  have hlarge := f1024Why24OddGenus_lower_bound r
  simp only [selectedDivisorDegree, selectedLogicalCount]
  omega

/-- Raw evaluation of `L(A)` on the actual systematic pivot places. -/
noncomputable def f1024Why24OddRawPivotEvaluation (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r) →ₗ[F1024]
      QEC.Coding.Word F1024 (f1024Why24OddLogical r) :=
  QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
    (f1024Why24OddADivisor r)
    (f1024Why24OddPivotRationalPlace r)
    (f1024Why24OddADivisor_apply_pivot r)

private noncomputable instance f1024Why24OddAFiniteDimensional (r : ℕ) :
    FiniteDimensional F1024
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r)) :=
  QEC.Coding.AlgebraicGeometry.GlobalPlace.finiteDimensional_riemannRochSubmodule
    (k := F1024) (F := F1024TowerLevel (2 * r + 2))
    (f1024Why24OddADivisor r)

private noncomputable instance f1024Why24OddA_sub_pivots_finiteDimensional
    (r : ℕ) :
    FiniteDimensional F1024
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)) :=
  QEC.Coding.AlgebraicGeometry.GlobalPlace.finiteDimensional_riemannRochSubmodule
    (k := F1024) (F := F1024TowerLevel (2 * r + 2))
    (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)

private noncomputable def f1024Why24OddPivotKernelRestriction (r : ℕ) :
    (f1024Why24OddRawPivotEvaluation r).ker →ₗ[F1024]
      QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) where
  toFun f := ⟨(f.1 : F1024TowerLevel (2 * r + 2)),
    QEC.Coding.AlgebraicGeometry.evaluationZero_mem_riemannRochSubmodule_sub
      (f1024Why24OddADivisor r)
      (f1024Why24OddPivotRationalPlace r)
      (f1024Why24OddPivotRationalPlace_injective r)
      (f1024Why24OddADivisor_apply_pivot r) f.1 f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem f1024Why24OddPivotKernelRestriction_injective (r : ℕ) :
    Function.Injective (f1024Why24OddPivotKernelRestriction r) := by
  intro x y hxy
  have hval :
      ((x.1 : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          (f1024Why24OddADivisor r)) : F1024TowerLevel (2 * r + 2)) =
        ((y.1 : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          (f1024Why24OddADivisor r)) : F1024TowerLevel (2 * r + 2)) :=
    congrArg
      (fun z : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) =>
        (z : F1024TowerLevel (2 * r + 2))) hxy
  exact Subtype.ext (Subtype.ext hval)

/-- Riemann--Roch dimension loss at the actual pivots proves that their
restriction map is onto. -/
theorem f1024Why24OddRawPivotEvaluation_surjective (r : ℕ) :
    Function.Surjective (f1024Why24OddRawPivotEvaluation r) := by
  let T := f1024Why24OddRawPivotEvaluation r
  have hkerNat : Module.finrank F1024 T.ker ≤
      Module.finrank F1024
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)) :=
    LinearMap.finrank_le_finrank_of_injective
      (f1024Why24OddPivotKernelRestriction_injective r)
  have htotal :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_eq_of_large_degree
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024Why24OddADivisor r) (by
        rw [f1024TowerLevel_functionFieldGenus_even,
          f1024Why24OddADivisor_degree]
        exact f1024Why24Odd_largeDegree r)
  have hbase :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_eq_of_large_degree
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
      (f1024Why24OddA_sub_pivots_largeDegree r)
  change (Module.finrank F1024
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r)) : ℤ) = _ at htotal
  change (Module.finrank F1024
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)) : ℤ) = _
    at hbase
  rw [f1024Why24OddADivisor_degree,
    f1024TowerLevel_functionFieldGenus_even] at htotal
  rw [Divisor.degree_sub, f1024Why24OddADivisor_degree,
    f1024Why24OddPivotDivisor_degree,
    f1024TowerLevel_functionFieldGenus_even] at hbase
  have hrank := T.finrank_range_add_finrank_ker
  have hrankInt := congrArg (fun n : ℕ => (n : ℤ)) hrank
  simp only [Nat.cast_add] at hrankInt
  have hkerInt : (Module.finrank F1024 T.ker : ℤ) ≤
      (Module.finrank F1024
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)) : ℤ) := by
    exact_mod_cast hkerNat
  have hrangeLower : (selectedLogicalCount (oddGenus r) : ℤ) ≤
      (Module.finrank F1024 T.range : ℤ) := by
    omega
  have hrangeUpper : Module.finrank F1024 T.range ≤
      selectedLogicalCount (oddGenus r) := by
    calc
      Module.finrank F1024 T.range ≤
          Module.finrank F1024
            (QEC.Coding.Word F1024 (f1024Why24OddLogical r)) :=
        Submodule.finrank_le _
      _ = selectedLogicalCount (oddGenus r) := by
        simp only [QEC.Coding.Word, Module.finrank_pi, Fintype.card_fin]
  have hrangeEq : Module.finrank F1024 T.range =
      selectedLogicalCount (oddGenus r) := by
    have hlower : selectedLogicalCount (oddGenus r) ≤
        Module.finrank F1024 T.range := by
      exact_mod_cast hrangeLower
    omega
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simpa only [QEC.Coding.Word, Module.finrank_pi, Fintype.card_fin] using hrangeEq

/-- Restriction of an actual residue-scaled AG codeword to the systematic
pivots. -/
def f1024Why24OddScaledPivotRestriction (r : ℕ) :
    (f1024Why24OddScaledAGCode r).carrier →ₗ[F1024]
      QEC.Coding.Word F1024 (f1024Why24OddLogical r) where
  toFun x := fun a => x.1 (f1024Why24OddPivotEmbedding r a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The scaling weights are nonzero, so the actual scaled restriction is
still onto. -/
theorem f1024Why24OddScaledPivotRestriction_surjective (r : ℕ) :
    Function.Surjective (f1024Why24OddScaledPivotRestriction r) := by
  intro u
  let rawTarget : QEC.Coding.Word F1024 (f1024Why24OddLogical r) :=
    fun a => (f1024Why24OddCoordinateWeight r
      (f1024Why24OddPivotEmbedding r a))⁻¹ * u a
  obtain ⟨x, hx⟩ := f1024Why24OddRawPivotEvaluation_surjective r rawTarget
  refine ⟨⟨f1024Why24OddScaledEvaluationLinearMap r x,
    f1024Why24OddScaledEvaluationLinearMap_mem r x⟩, ?_⟩
  funext a
  change f1024Why24OddCoordinateWeight r
      (f1024Why24OddPivotEmbedding r a) *
        (f1024Why24OddRawPivotEvaluation r x) a = u a
  rw [congrFun hx a]
  dsimp only [rawTarget]
  rw [← mul_assoc, mul_inv_cancel₀ (f1024Why24OddCoordinateWeight_ne_zero r
    (f1024Why24OddPivotEmbedding r a)), one_mul]

/-- The noncomputable systematic section derived from the proved
surjectivity. -/
noncomputable def f1024Why24OddPivotSection (r : ℕ) :
    QEC.Coding.Word F1024 (f1024Why24OddLogical r) →ₗ[F1024]
      (f1024Why24OddScaledAGCode r).carrier :=
  (f1024Why24OddScaledPivotRestriction r).splittingOfFunOnFintypeSurjective
    (f1024Why24OddScaledPivotRestriction_surjective r)

/-- The derived section is a right inverse on the actual systematic
coordinates. -/
theorem f1024Why24OddPivotSection_rightInverse (r : ℕ)
    (u : QEC.Coding.Word F1024 (f1024Why24OddLogical r)) :
    f1024Why24OddScaledPivotRestriction r
        (f1024Why24OddPivotSection r u) = u :=
  (f1024Why24OddScaledPivotRestriction r).leftInverse_splittingOfFunOnFintypeSurjective
    (f1024Why24OddScaledPivotRestriction_surjective r) u

/-- The retained coordinates left after removing the chosen pivots. -/
def f1024Why24OddPhysicalSite (r : ℕ) : Type :=
  {i : f1024Why24OddRetainedCandidateIndex r //
    i ∉ Set.range (f1024Why24OddPivotEmbedding r)}

noncomputable instance f1024Why24OddPhysicalSiteFintype (r : ℕ) :
    Fintype (f1024Why24OddPhysicalSite r) := by
  classical
  exact Subtype.fintype _

noncomputable instance f1024Why24OddPhysicalSiteDecidableEq (r : ℕ) :
    DecidableEq (f1024Why24OddPhysicalSite r) :=
  Classical.decEq _

/-- The physical site count is the retained place count minus `k`. -/
theorem f1024Why24OddPhysicalSite_card (r : ℕ) :
    Fintype.card (f1024Why24OddPhysicalSite r) =
      Fintype.card (f1024Why24OddRetainedCandidateIndex r) -
        selectedLogicalCount (oddGenus r) := by
  classical
  have hcomplement :
      Nat.card
          {i : f1024Why24OddRetainedCandidateIndex r //
            i ∉ Set.range (f1024Why24OddPivotEmbedding r)} =
        Nat.card (f1024Why24OddRetainedCandidateIndex r) -
          Nat.card (Set.range (f1024Why24OddPivotEmbedding r)) := by
    let p : f1024Why24OddRetainedCandidateIndex r → Prop :=
      fun i => i ∈ Set.range (f1024Why24OddPivotEmbedding r)
    letI : Fintype {i // p i} := Fintype.ofFinite {i // p i}
    letI : Fintype {i // ¬p i} := Fintype.ofFinite {i // ¬p i}
    have h := Fintype.card_subtype_compl p
    have hport := h
    simp only [← Nat.card_eq_fintype_card] at hport ⊢
    exact hport
  calc
    Fintype.card (f1024Why24OddPhysicalSite r) =
        Nat.card (f1024Why24OddPhysicalSite r) :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card (f1024Why24OddRetainedCandidateIndex r) -
        Nat.card (Set.range (f1024Why24OddPivotEmbedding r)) :=
      hcomplement
    _ = Fintype.card (f1024Why24OddRetainedCandidateIndex r) -
        selectedLogicalCount (oddGenus r) := by
      rw [Nat.card_eq_fintype_card,
        Nat.card_range_of_injective (f1024Why24OddPivotEmbedding r).injective,
        Nat.card_fin]

/-- Puncture a retained word at the actual pivot complement. -/
def f1024Why24OddPuncture (r : ℕ) :
    QEC.Coding.Word F1024 (f1024Why24OddRetainedCandidateIndex r) →ₗ[F1024]
      QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r) where
  toFun x := fun i => x i.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Full codewords whose systematic pivot coordinates vanish. -/
abbrev f1024Why24OddShortenedKernel (r : ℕ) : Type :=
  (f1024Why24OddScaledPivotRestriction r).ker

noncomputable instance f1024Why24OddShortenedKernelFintype (r : ℕ) :
    Fintype (f1024Why24OddShortenedKernel r) :=
  Fintype.ofFinite _

noncomputable instance f1024Why24OddShortenedKernelDecidableEq (r : ℕ) :
    DecidableEq (f1024Why24OddShortenedKernel r) :=
  Classical.decEq _

/-- The physical representative of one logical systematic basis row. -/
noncomputable def f1024Why24OddSystematicLogicalRow (r : ℕ)
    (a : f1024Why24OddLogical r) :
    QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r) :=
  f1024Why24OddPuncture r
    (f1024Why24OddPivotSection r (QEC.Coding.canonicalBasisWord a)).1

/-- The physical representative of one actual shortened-kernel word. -/
def f1024Why24OddStabilizerRow (r : ℕ)
    (h : f1024Why24OddShortenedKernel r) :
    QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r) :=
  f1024Why24OddPuncture r h.1.1

open QEC.Distillation.Why24WeightedTriorthogonalCSS

private def f1024Why24OddFullRow (r : ℕ) :
    f1024Why24OddLogical r ⊕ f1024Why24OddShortenedKernel r →
      QEC.Coding.Word F1024 (f1024Why24OddRetainedCandidateIndex r) :=
  Sum.elim
    (fun a => (f1024Why24OddPivotSection r
      (QEC.Coding.canonicalBasisWord a)).1)
    (fun h => h.1.1)

private theorem f1024Why24OddFullRow_mem (r : ℕ)
    (a : f1024Why24OddLogical r ⊕ f1024Why24OddShortenedKernel r) :
    f1024Why24OddFullRow r a ∈
      (f1024Why24OddScaledAGCode r).carrier := by
  cases a with
  | inl a => exact (f1024Why24OddPivotSection r
      (QEC.Coding.canonicalBasisWord a)).2
  | inr h => exact h.1.2

private theorem f1024Why24OddPivotSection_coordinate (r : ℕ)
    (u : QEC.Coding.Word F1024 (f1024Why24OddLogical r))
    (a : f1024Why24OddLogical r) :
    (f1024Why24OddPivotSection r u).1
        (f1024Why24OddPivotEmbedding r a) = u a :=
  congrFun (f1024Why24OddPivotSection_rightInverse r u) a

private theorem f1024Why24OddShortenedKernel_pivot_zero (r : ℕ)
    (h : f1024Why24OddShortenedKernel r)
    (a : f1024Why24OddLogical r) :
    h.1.1 (f1024Why24OddPivotEmbedding r a) = 0 := by
  have hzero : f1024Why24OddScaledPivotRestriction r h.1 = 0 := h.2
  exact congrFun hzero a

private theorem f1024Why24OddFullRow_pivot (r : ℕ)
    (row : f1024Why24OddLogical r ⊕ f1024Why24OddShortenedKernel r)
    (a : f1024Why24OddLogical r) :
    f1024Why24OddFullRow r row (f1024Why24OddPivotEmbedding r a) =
      Sum.elim
        (fun b => QEC.Coding.canonicalBasisWord b a)
        (fun _ => 0) row := by
  cases row with
  | inl b =>
      change (f1024Why24OddPivotSection r
        (QEC.Coding.canonicalBasisWord b)).1
          (f1024Why24OddPivotEmbedding r a) =
        QEC.Coding.canonicalBasisWord b a
      exact f1024Why24OddPivotSection_coordinate r
        (QEC.Coding.canonicalBasisWord b) a
  | inr h =>
      change h.1.1 (f1024Why24OddPivotEmbedding r a) = 0
      exact f1024Why24OddShortenedKernel_pivot_zero r h a

private theorem f1024Why24OddFullSeventhPairing_eq_zero (r : ℕ)
    (x y z : (f1024Why24OddScaledAGCode r).carrier) :
    (∑ i : f1024Why24OddRetainedCandidateIndex r,
      x.1 i ^ 4 * y.1 i ^ 2 * z.1 i) = 0 := by
  obtain ⟨fx, hfx⟩ := x.2
  obtain ⟨fy, hfy⟩ := y.2
  obtain ⟨fz, hfz⟩ := z.2
  rw [← hfx, ← hfy, ← hfz]
  exact f1024Why24OddScaledSeventhPairing_eq_zero r fx fy fz

private theorem f1024Why24OddFullWeightedPairing_eq_zero (r : ℕ)
    (x y : (f1024Why24OddScaledAGCode r).carrier) :
    (∑ i : f1024Why24OddRetainedCandidateIndex r,
      f1024Why24OddCoordinateWeight r i ^ 5 * x.1 i * y.1 i) = 0 := by
  obtain ⟨fx, hfx⟩ := x.2
  obtain ⟨fy, hfy⟩ := y.2
  rw [← hfx, ← hfy]
  exact f1024Why24OddScaledWeightedPairing_eq_zero r fx fy

private theorem f1024Why24OddSeventhPairing_partition (r : ℕ)
    (x y z : QEC.Coding.Word F1024
      (f1024Why24OddRetainedCandidateIndex r)) :
    (∑ a : f1024Why24OddLogical r,
        x (f1024Why24OddPivotEmbedding r a) ^ 4 *
          y (f1024Why24OddPivotEmbedding r a) ^ 2 *
            z (f1024Why24OddPivotEmbedding r a)) +
      seventhPairing (f1024Why24OddPuncture r x)
        (f1024Why24OddPuncture r y) (f1024Why24OddPuncture r z) =
      ∑ i : f1024Why24OddRetainedCandidateIndex r,
        x i ^ 4 * y i ^ 2 * z i := by
  classical
  letI : Fintype (Set.range (f1024Why24OddPivotEmbedding r)) :=
    Subtype.fintype _
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i : f1024Why24OddRetainedCandidateIndex r =>
      i ∈ Set.range (f1024Why24OddPivotEmbedding r))
    (fun i => x i ^ 4 * y i ^ 2 * z i)
  let rangeEquiv : f1024Why24OddLogical r ≃
      Set.range (f1024Why24OddPivotEmbedding r) :=
    Equiv.ofInjective (f1024Why24OddPivotEmbedding r)
      (f1024Why24OddPivotEmbedding r).injective
  have hrange :
      (∑ point : Set.range (f1024Why24OddPivotEmbedding r),
        x point.1 ^ 4 * y point.1 ^ 2 * z point.1) =
      ∑ a : f1024Why24OddLogical r,
        x (f1024Why24OddPivotEmbedding r a) ^ 4 *
          y (f1024Why24OddPivotEmbedding r a) ^ 2 *
            z (f1024Why24OddPivotEmbedding r a) := by
    exact Fintype.sum_equiv rangeEquiv.symm
      (fun point => x point.1 ^ 4 * y point.1 ^ 2 * z point.1)
      (fun a => x (f1024Why24OddPivotEmbedding r a) ^ 4 *
        y (f1024Why24OddPivotEmbedding r a) ^ 2 *
          z (f1024Why24OddPivotEmbedding r a)) (fun point => by
        have hpoint : f1024Why24OddPivotEmbedding r (rangeEquiv.symm point) =
            point.1 := congrArg Subtype.val (rangeEquiv.apply_symm_apply point)
        change x point.1 ^ 4 * y point.1 ^ 2 * z point.1 =
          x (f1024Why24OddPivotEmbedding r (rangeEquiv.symm point)) ^ 4 *
            y (f1024Why24OddPivotEmbedding r (rangeEquiv.symm point)) ^ 2 *
              z (f1024Why24OddPivotEmbedding r (rangeEquiv.symm point))
        rw [hpoint])
  let complementEquiv :
      {i : f1024Why24OddRetainedCandidateIndex r //
        ¬ i ∈ Set.range (f1024Why24OddPivotEmbedding r)} ≃
        f1024Why24OddPhysicalSite r := Equiv.refl _
  have hcomplement :
      (∑ point : {i : f1024Why24OddRetainedCandidateIndex r //
          ¬ i ∈ Set.range (f1024Why24OddPivotEmbedding r)},
        x point.1 ^ 4 * y point.1 ^ 2 * z point.1) =
      seventhPairing (f1024Why24OddPuncture r x)
        (f1024Why24OddPuncture r y) (f1024Why24OddPuncture r z) := by
    exact Fintype.sum_equiv complementEquiv
      (fun point => x point.1 ^ 4 * y point.1 ^ 2 * z point.1)
      (fun point =>
        (f1024Why24OddPuncture r x point) ^ 4 *
          (f1024Why24OddPuncture r y point) ^ 2 *
            f1024Why24OddPuncture r z point) (fun _ => rfl)
  rw [← hrange, ← hcomplement]
  exact hsplit

private theorem f1024Why24OddWeightedPairing_partition (r : ℕ)
    (x y : QEC.Coding.Word F1024
      (f1024Why24OddRetainedCandidateIndex r)) :
    (∑ a : f1024Why24OddLogical r,
        f1024Why24OddCoordinateWeight r
            (f1024Why24OddPivotEmbedding r a) ^ 5 *
          x (f1024Why24OddPivotEmbedding r a) *
            y (f1024Why24OddPivotEmbedding r a)) +
      weightedPairing
        (fun site : f1024Why24OddPhysicalSite r =>
          f1024Why24OddCoordinateWeight r site.1 ^ 5)
        (f1024Why24OddPuncture r x) (f1024Why24OddPuncture r y) =
      ∑ i : f1024Why24OddRetainedCandidateIndex r,
        f1024Why24OddCoordinateWeight r i ^ 5 * x i * y i := by
  classical
  letI : Fintype (Set.range (f1024Why24OddPivotEmbedding r)) :=
    Subtype.fintype _
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i : f1024Why24OddRetainedCandidateIndex r =>
      i ∈ Set.range (f1024Why24OddPivotEmbedding r))
    (fun i => f1024Why24OddCoordinateWeight r i ^ 5 * x i * y i)
  let rangeEquiv : f1024Why24OddLogical r ≃
      Set.range (f1024Why24OddPivotEmbedding r) :=
    Equiv.ofInjective (f1024Why24OddPivotEmbedding r)
      (f1024Why24OddPivotEmbedding r).injective
  have hrange :
      (∑ point : Set.range (f1024Why24OddPivotEmbedding r),
        f1024Why24OddCoordinateWeight r point.1 ^ 5 *
          x point.1 * y point.1) =
      ∑ a : f1024Why24OddLogical r,
        f1024Why24OddCoordinateWeight r
            (f1024Why24OddPivotEmbedding r a) ^ 5 *
          x (f1024Why24OddPivotEmbedding r a) *
            y (f1024Why24OddPivotEmbedding r a) := by
    exact Fintype.sum_equiv rangeEquiv.symm
      (fun point => f1024Why24OddCoordinateWeight r point.1 ^ 5 *
        x point.1 * y point.1)
      (fun a => f1024Why24OddCoordinateWeight r
          (f1024Why24OddPivotEmbedding r a) ^ 5 *
        x (f1024Why24OddPivotEmbedding r a) *
          y (f1024Why24OddPivotEmbedding r a)) (fun point => by
        have hpoint : f1024Why24OddPivotEmbedding r (rangeEquiv.symm point) =
            point.1 := congrArg Subtype.val (rangeEquiv.apply_symm_apply point)
        change f1024Why24OddCoordinateWeight r point.1 ^ 5 *
            x point.1 * y point.1 =
          f1024Why24OddCoordinateWeight r
              (f1024Why24OddPivotEmbedding r (rangeEquiv.symm point)) ^ 5 *
            x (f1024Why24OddPivotEmbedding r (rangeEquiv.symm point)) *
              y (f1024Why24OddPivotEmbedding r (rangeEquiv.symm point))
        rw [hpoint])
  let complementEquiv :
      {i : f1024Why24OddRetainedCandidateIndex r //
        ¬ i ∈ Set.range (f1024Why24OddPivotEmbedding r)} ≃
        f1024Why24OddPhysicalSite r := Equiv.refl _
  have hcomplement :
      (∑ point : {i : f1024Why24OddRetainedCandidateIndex r //
          ¬ i ∈ Set.range (f1024Why24OddPivotEmbedding r)},
        f1024Why24OddCoordinateWeight r point.1 ^ 5 *
          x point.1 * y point.1) =
      weightedPairing
        (fun site : f1024Why24OddPhysicalSite r =>
          f1024Why24OddCoordinateWeight r site.1 ^ 5)
        (f1024Why24OddPuncture r x) (f1024Why24OddPuncture r y) := by
    exact Fintype.sum_equiv complementEquiv
      (fun point => f1024Why24OddCoordinateWeight r point.1 ^ 5 *
        x point.1 * y point.1)
      (fun point => f1024Why24OddCoordinateWeight r point.1 ^ 5 *
        f1024Why24OddPuncture r x point *
          f1024Why24OddPuncture r y point) (fun _ => rfl)
  rw [← hrange, ← hcomplement]
  exact hsplit

private theorem f1024Why24Odd_neg_eq_self (x : F1024) : -x = x := by
  apply (eq_neg_of_add_eq_zero_left ?_).symm
  have htwo : (2 : F1024) = 0 := CharP.cast_eq_zero F1024 2
  rw [← two_mul, htwo, zero_mul]

private theorem f1024Why24OddCanonicalSeventhSum
    {Logical : Type} [Fintype Logical] [DecidableEq Logical]
    (a b c : Logical) :
    (∑ pivot : Logical,
      QEC.Coding.canonicalBasisWord (F := F1024) a pivot ^ 4 *
        QEC.Coding.canonicalBasisWord (F := F1024) b pivot ^ 2 *
          QEC.Coding.canonicalBasisWord (F := F1024) c pivot) =
      if a = b ∧ b = c then 1 else 0 := by
  classical
  rw [Fintype.sum_eq_single a]
  · by_cases hab : a = b
    · subst b
      by_cases hac : a = c
      · subst c
        simp [QEC.Coding.canonicalBasisWord]
      · simp [QEC.Coding.canonicalBasisWord, hac]
    · simp [QEC.Coding.canonicalBasisWord, hab]
  · intro pivot hpivot
    simp [QEC.Coding.canonicalBasisWord, hpivot]

private theorem f1024Why24OddCanonicalWeightedSum
    {Logical : Type} [Fintype Logical] [DecidableEq Logical]
    (weight : Logical → F1024) (a b : Logical) :
    (∑ pivot : Logical,
      weight pivot *
        QEC.Coding.canonicalBasisWord (F := F1024) a pivot *
          QEC.Coding.canonicalBasisWord (F := F1024) b pivot) =
      if a = b then weight a else 0 := by
  classical
  rw [Fintype.sum_eq_single a]
  · by_cases hab : a = b
    · subst b
      simp [QEC.Coding.canonicalBasisWord]
    · simp [QEC.Coding.canonicalBasisWord, hab]
  · intro pivot hpivot
    simp [QEC.Coding.canonicalBasisWord, hpivot]

private theorem f1024Why24OddPivotSeventh_eq_target (r : ℕ)
    (a b c : f1024Why24OddLogical r ⊕ f1024Why24OddShortenedKernel r) :
    (∑ pivot : f1024Why24OddLogical r,
      f1024Why24OddFullRow r a (f1024Why24OddPivotEmbedding r pivot) ^ 4 *
        f1024Why24OddFullRow r b (f1024Why24OddPivotEmbedding r pivot) ^ 2 *
          f1024Why24OddFullRow r c
            (f1024Why24OddPivotEmbedding r pivot)) =
      seventhTarget a b c := by
  classical
  cases a with
  | inr a => simp [f1024Why24OddFullRow_pivot, seventhTarget]
  | inl a =>
    cases b with
    | inr b => simp [f1024Why24OddFullRow_pivot, seventhTarget]
    | inl b =>
      cases c with
      | inr c => simp [f1024Why24OddFullRow_pivot, seventhTarget]
      | inl c =>
        simpa only [f1024Why24OddFullRow_pivot, Sum.elim_inl,
          seventhTarget] using f1024Why24OddCanonicalSeventhSum a b c

private theorem f1024Why24OddPivotWeighted_eq_target (r : ℕ)
    (a b : f1024Why24OddLogical r ⊕ f1024Why24OddShortenedKernel r) :
    (∑ pivot : f1024Why24OddLogical r,
      f1024Why24OddCoordinateWeight r
          (f1024Why24OddPivotEmbedding r pivot) ^ 5 *
        f1024Why24OddFullRow r a (f1024Why24OddPivotEmbedding r pivot) *
          f1024Why24OddFullRow r b
            (f1024Why24OddPivotEmbedding r pivot)) =
      weightedTarget
        (fun logical => f1024Why24OddCoordinateWeight r
          (f1024Why24OddPivotEmbedding r logical) ^ 5) a b := by
  classical
  cases a with
  | inr a => simp [f1024Why24OddFullRow_pivot, weightedTarget]
  | inl a =>
    cases b with
    | inr b => simp [f1024Why24OddFullRow_pivot, weightedTarget]
    | inl b =>
      simpa only [f1024Why24OddFullRow_pivot, Sum.elim_inl,
        weightedTarget] using f1024Why24OddCanonicalWeightedSum
          (fun pivot => f1024Why24OddCoordinateWeight r
            (f1024Why24OddPivotEmbedding r pivot) ^ 5) a b

private theorem f1024Why24OddPhysicalRow_eq_punctureFullRow (r : ℕ)
    (a : f1024Why24OddLogical r ⊕ f1024Why24OddShortenedKernel r) :
    Sum.elim (f1024Why24OddSystematicLogicalRow r)
        (f1024Why24OddStabilizerRow r) a =
      f1024Why24OddPuncture r (f1024Why24OddFullRow r a) := by
  cases a <;> rfl

private theorem f1024Why24OddMatrixSeventhCondition (r : ℕ)
    (a b c : f1024Why24OddLogical r ⊕ f1024Why24OddShortenedKernel r) :
    seventhPairing
        (Sum.elim (f1024Why24OddSystematicLogicalRow r)
          (f1024Why24OddStabilizerRow r) a)
        (Sum.elim (f1024Why24OddSystematicLogicalRow r)
          (f1024Why24OddStabilizerRow r) b)
        (Sum.elim (f1024Why24OddSystematicLogicalRow r)
          (f1024Why24OddStabilizerRow r) c) =
      seventhTarget a b c := by
  let xa : (f1024Why24OddScaledAGCode r).carrier :=
    ⟨f1024Why24OddFullRow r a, f1024Why24OddFullRow_mem r a⟩
  let xb : (f1024Why24OddScaledAGCode r).carrier :=
    ⟨f1024Why24OddFullRow r b, f1024Why24OddFullRow_mem r b⟩
  let xc : (f1024Why24OddScaledAGCode r).carrier :=
    ⟨f1024Why24OddFullRow r c, f1024Why24OddFullRow_mem r c⟩
  have hfull := f1024Why24OddFullSeventhPairing_eq_zero r xa xb xc
  have hpartition := f1024Why24OddSeventhPairing_partition r
    (f1024Why24OddFullRow r a) (f1024Why24OddFullRow r b)
      (f1024Why24OddFullRow r c)
  have hphysical :
      seventhPairing
          (f1024Why24OddPuncture r (f1024Why24OddFullRow r a))
          (f1024Why24OddPuncture r (f1024Why24OddFullRow r b))
          (f1024Why24OddPuncture r (f1024Why24OddFullRow r c)) =
        -(∑ pivot : f1024Why24OddLogical r,
          f1024Why24OddFullRow r a
              (f1024Why24OddPivotEmbedding r pivot) ^ 4 *
            f1024Why24OddFullRow r b
              (f1024Why24OddPivotEmbedding r pivot) ^ 2 *
              f1024Why24OddFullRow r c
                (f1024Why24OddPivotEmbedding r pivot)) := by
    rw [hfull] at hpartition
    exact eq_neg_of_add_eq_zero_right hpartition
  rw [f1024Why24OddPhysicalRow_eq_punctureFullRow,
    f1024Why24OddPhysicalRow_eq_punctureFullRow,
    f1024Why24OddPhysicalRow_eq_punctureFullRow, hphysical,
    f1024Why24Odd_neg_eq_self,
    f1024Why24OddPivotSeventh_eq_target]

private theorem f1024Why24OddMatrixWeightedCondition (r : ℕ)
    (a b : f1024Why24OddLogical r ⊕ f1024Why24OddShortenedKernel r) :
    weightedPairing
        (fun site : f1024Why24OddPhysicalSite r =>
          f1024Why24OddCoordinateWeight r site.1 ^ 5)
        (Sum.elim (f1024Why24OddSystematicLogicalRow r)
          (f1024Why24OddStabilizerRow r) a)
        (Sum.elim (f1024Why24OddSystematicLogicalRow r)
          (f1024Why24OddStabilizerRow r) b) =
      weightedTarget
        (fun logical => f1024Why24OddCoordinateWeight r
          (f1024Why24OddPivotEmbedding r logical) ^ 5) a b := by
  let xa : (f1024Why24OddScaledAGCode r).carrier :=
    ⟨f1024Why24OddFullRow r a, f1024Why24OddFullRow_mem r a⟩
  let xb : (f1024Why24OddScaledAGCode r).carrier :=
    ⟨f1024Why24OddFullRow r b, f1024Why24OddFullRow_mem r b⟩
  have hfull := f1024Why24OddFullWeightedPairing_eq_zero r xa xb
  have hpartition := f1024Why24OddWeightedPairing_partition r
    (f1024Why24OddFullRow r a) (f1024Why24OddFullRow r b)
  have hphysical :
      weightedPairing
          (fun site : f1024Why24OddPhysicalSite r =>
            f1024Why24OddCoordinateWeight r site.1 ^ 5)
          (f1024Why24OddPuncture r (f1024Why24OddFullRow r a))
          (f1024Why24OddPuncture r (f1024Why24OddFullRow r b)) =
        -(∑ pivot : f1024Why24OddLogical r,
          f1024Why24OddCoordinateWeight r
              (f1024Why24OddPivotEmbedding r pivot) ^ 5 *
            f1024Why24OddFullRow r a
              (f1024Why24OddPivotEmbedding r pivot) *
              f1024Why24OddFullRow r b
                (f1024Why24OddPivotEmbedding r pivot)) := by
    rw [hfull] at hpartition
    exact eq_neg_of_add_eq_zero_right hpartition
  rw [f1024Why24OddPhysicalRow_eq_punctureFullRow,
    f1024Why24OddPhysicalRow_eq_punctureFullRow, hphysical,
    f1024Why24Odd_neg_eq_self,
    f1024Why24OddPivotWeighted_eq_target]

/-- The actual systematic puncture of WHY24's residue-scaled AG code, as a
raw weighted-triorthogonal matrix. -/
noncomputable def f1024Why24OddWeightedMatrix (r : ℕ) :
    WeightedTriorthogonalMatrix
      (f1024Why24OddLogical r)
      (f1024Why24OddShortenedKernel r)
      (f1024Why24OddPhysicalSite r) where
  logicalRow := f1024Why24OddSystematicLogicalRow r
  stabilizerRow := f1024Why24OddStabilizerRow r
  sigma := fun site => f1024Why24OddCoordinateWeight r site.1 ^ 5
  tau := fun logical => f1024Why24OddCoordinateWeight r
    (f1024Why24OddPivotEmbedding r logical) ^ 5
  sigma_ne_zero site := pow_ne_zero 5
    (f1024Why24OddCoordinateWeight_ne_zero r site.1)
  tau_ne_zero logical := pow_ne_zero 5
    (f1024Why24OddCoordinateWeight_ne_zero r
      (f1024Why24OddPivotEmbedding r logical))
  seventh_condition := f1024Why24OddMatrixSeventhCondition r
  weighted_condition := f1024Why24OddMatrixWeightedCondition r

/-- The actual CSS encoding derived from the systematic WHY24 matrix. -/
noncomputable def f1024Why24OddEncodedCode (r : ℕ) :=
  (f1024Why24OddWeightedMatrix r).encodedCode

/-- The literal product of single-site `U₁⁽⁷⁾` gates on the actual
punctured coordinates. -/
noncomputable def f1024Why24OddPhysicalUOneSeven (r : ℕ) :=
  (f1024Why24OddWeightedMatrix r).physicalUOneSeven

/-- The actual physical `U₁⁽⁷⁾` product implements the matrix's logical
`U₁⁽⁷⁾` gate. -/
theorem f1024Why24OddPhysicalUOneSeven_implements_logicalUOneSeven (r : ℕ) :
    (f1024Why24OddEncodedCode r).ImplementsLogicalGate
      (f1024Why24OddPhysicalUOneSeven r)
      (f1024Why24OddWeightedMatrix r).logicalUOneSeven :=
  (f1024Why24OddWeightedMatrix r).physicalUOneSeven_implements_logicalUOneSeven

/-!
## Distance, asymptotic parameters, and the decoder handoff

The stabilizer span below is identified with the coordinate-scaled AG code
obtained by evaluating `L(A - D_pivot)` on the literal pivot complement.
This is the source's shortened code, rather than an abstract classical-code
witness.  Its dual designed-distance bound then controls both CSS sectors.

The final quotient is the intrinsic Z-error syndrome modulo `G₀⊥`.  We
prove only its injectivity on the source radius ball; construction and
correctness of the polynomial decoder remain the responsibility of #888.
-/

/-- The actual rational place at a physical (non-pivot) coordinate. -/
noncomputable def f1024Why24OddPhysicalRationalPlace (r : ℕ) :
    f1024Why24OddPhysicalSite r →
      QEC.Coding.AlgebraicGeometry.RationalPlace F1024
        (F1024TowerLevel (2 * r + 2)) :=
  fun site => f1024Why24OddRetainedRationalPlace r site.1

private theorem f1024Why24OddPhysicalRationalPlace_injective (r : ℕ) :
    Function.Injective
      (fun site => (f1024Why24OddPhysicalRationalPlace r site).place) := by
  intro i j hij
  apply Subtype.ext
  exact f1024Why24OddRetainedRationalPlace_injective r hij

private theorem f1024Why24OddPivotDivisor_apply_pivot (r : ℕ)
    (a : f1024Why24OddLogical r) :
    f1024Why24OddPivotDivisor r
        (f1024Why24OddPivotRationalPlace r a).place = 1 := by
  simpa only [f1024Why24OddPivotDivisor] using
    QEC.Coding.AlgebraicGeometry.evaluationDivisor_apply_at
      (f1024Why24OddPivotRationalPlace r)
      (f1024Why24OddPivotRationalPlace_injective r) a

private theorem f1024Why24OddPivotDivisor_apply_physical (r : ℕ)
    (site : f1024Why24OddPhysicalSite r) :
    f1024Why24OddPivotDivisor r
        (f1024Why24OddPhysicalRationalPlace r site).place = 0 := by
  simpa only [f1024Why24OddPivotDivisor,
    QEC.Coding.AlgebraicGeometry.evaluationDivisor] using
      QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor_apply_eq_zero_of_not_mem
        (f1024Why24OddPivotRationalPlace r) Finset.univ
        (f1024Why24OddPhysicalRationalPlace r site).place (by
          intro a _ hplace
          apply site.2
          refine ⟨a, ?_⟩
          apply f1024Why24OddRetainedRationalPlace_injective r
          exact hplace)

private theorem f1024Why24OddShortenedDivisor_apply_physical (r : ℕ)
    (site : f1024Why24OddPhysicalSite r) :
    (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
        (f1024Why24OddPhysicalRationalPlace r site).place = 0 := by
  change (f1024Why24OddADivisor r)
      (f1024Why24OddRetainedRationalPlace r site.1).place -
    (f1024Why24OddPivotDivisor r)
      (f1024Why24OddPhysicalRationalPlace r site).place = 0
  rw [f1024Why24OddADivisor_apply_retained,
    f1024Why24OddPivotDivisor_apply_physical, sub_zero]

private theorem f1024Why24OddPhysicalSite_card_pos (r : ℕ) :
    0 < Fintype.card (f1024Why24OddPhysicalSite r) := by
  have hlower := f1024Why24OddRetainedCandidateIndex_card_lower_bound r
  have hlarge := f1024Why24OddGenus_lower_bound r
  rw [f1024Why24OddPhysicalSite_card]
  simp only [selectedPlaceCount, selectedLogicalCount] at hlower ⊢
  omega

noncomputable instance f1024Why24OddPhysicalSiteNonempty (r : ℕ) :
    Nonempty (f1024Why24OddPhysicalSite r) :=
  Fintype.card_pos_iff.mp (f1024Why24OddPhysicalSite_card_pos r)

/-- The literal unscaled shortened AG code
`C_L(D_physical, A - D_pivot)`. -/
noncomputable def f1024Why24OddShortenedAGCode (r : ℕ) :
    QEC.Coding.LinearCode F1024 (f1024Why24OddPhysicalSite r) :=
  QEC.Coding.AlgebraicGeometry.agEvaluationCode
    (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
    (f1024Why24OddPhysicalRationalPlace r)
    (f1024Why24OddShortenedDivisor_apply_physical r)

private theorem f1024Why24OddShortenedDivisor_degree (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) =
      (selectedDivisorDegree (oddGenus r) : ℤ) -
        selectedLogicalCount (oddGenus r) := by
  rw [Divisor.degree_sub, f1024Why24OddADivisor_degree,
    f1024Why24OddPivotDivisor_degree]

private theorem f1024Why24OddShortenedDivisor_degree_lt_physicalCard
    (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) <
      Fintype.card (f1024Why24OddPhysicalSite r) := by
  have hdegree := f1024Why24Odd_divisorDegree_lt_retainedCard r
  have hlogical := f1024Why24OddLogicalCount_le_retainedCard r
  have hlogicalDegree : selectedLogicalCount (oddGenus r) ≤
      selectedDivisorDegree (oddGenus r) := by
    have hlarge := f1024Why24OddGenus_lower_bound r
    simp only [selectedLogicalCount, selectedDivisorDegree]
    omega
  rw [f1024Why24OddShortenedDivisor_degree,
    f1024Why24OddPhysicalSite_card]
  omega

private theorem f1024Why24OddDesignedDistance_int_toNat (r : ℕ) :
    Int.toNat
        (((selectedDivisorDegree (oddGenus r) : ℤ) -
            selectedLogicalCount (oddGenus r)) + 2 -
          2 * (oddGenus r : ℤ)) =
      selectedDistanceLowerBound (oddGenus r) := by
  have hmod := f1024Why24OddGenus_mod_eight r
  have hlarge := f1024Why24OddGenus_lower_bound r
  simp only [selectedDivisorDegree, selectedLogicalCount,
    selectedDistanceLowerBound]
  omega

/-- The genuine shortened AG dual has the source designed distance
`a - k - (2g - 2)`. -/
theorem f1024Why24OddShortenedAGCode_dual_distance_lower_bound (r : ℕ) :
    (selectedDistanceLowerBound (oddGenus r) : WithTop ℕ) ≤
      QEC.Coding.HypergraphProduct.extendedMinimumDistance
        (f1024Why24OddShortenedAGCode r).dual := by
  have h :=
    QEC.Coding.AlgebraicGeometry.agEvaluation_dual_distance_lower_bound
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
      (f1024Why24OddPhysicalRationalPlace r)
      (f1024Why24OddPhysicalRationalPlace_injective r)
      (f1024Why24OddShortenedDivisor_apply_physical r)
      (f1024Why24OddA_sub_pivots_largeDegree r)
      (f1024Why24OddShortenedDivisor_degree_lt_physicalCard r)
  rw [f1024Why24OddShortenedDivisor_degree,
    f1024TowerLevel_functionFieldGenus_even,
    f1024Why24OddDesignedDistance_int_toNat] at h
  exact h

/-- Evaluation of `L(A-D_pivot)` on physical sites followed by the actual
WHY24 coordinate scaling. -/
private noncomputable def f1024Why24OddScaledShortenedEvaluationLinearMap
    (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) →ₗ[F1024]
      QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r) where
  toFun f site := f1024Why24OddCoordinateWeight r site.1 *
    QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
      (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
      (f1024Why24OddPhysicalRationalPlace r)
      (f1024Why24OddShortenedDivisor_apply_physical r) f site
  map_add' x y := by
    funext site
    simp only [map_add, Pi.add_apply]
    ring
  map_smul' c x := by
    funext site
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    change f1024Why24OddCoordinateWeight r site.1 *
        (c * QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
          (f1024Why24OddPhysicalRationalPlace r)
          (f1024Why24OddShortenedDivisor_apply_physical r) x site) =
      c * (f1024Why24OddCoordinateWeight r site.1 *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
          (f1024Why24OddPhysicalRationalPlace r)
          (f1024Why24OddShortenedDivisor_apply_physical r) x site)
    ring

/-- The source's coordinate-scaled shortened AG code. -/
noncomputable def f1024Why24OddScaledShortenedAGCode (r : ℕ) :
    QEC.Coding.LinearCode F1024 (f1024Why24OddPhysicalSite r) where
  carrier := (f1024Why24OddScaledShortenedEvaluationLinearMap r).range

private theorem f1024Why24OddPivotDivisor_nonnegative (r : ℕ) :
    Divisor.Nonnegative (f1024Why24OddPivotDivisor r) := by
  intro P
  classical
  unfold f1024Why24OddPivotDivisor
    QEC.Coding.AlgebraicGeometry.evaluationDivisor
    QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_nonneg
  intro a _
  simp only [Finsupp.single_apply]
  split <;> norm_num

private noncomputable def f1024Why24OddShortenedToFull (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) →ₗ[F1024]
      QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r) where
  toFun f := ⟨(f : F1024TowerLevel (2 * r + 2)),
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule_mono
      (sub_le_self _ (f1024Why24OddPivotDivisor_nonnegative r)) f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem f1024Why24OddShortenedToFull_pivotEvaluation_eq_zero
    (r : ℕ)
    (f : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r))
    (a : f1024Why24OddLogical r) :
    QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
        (f1024Why24OddADivisor r)
        (f1024Why24OddPivotRationalPlace r)
        (f1024Why24OddADivisor_apply_pivot r)
        (f1024Why24OddShortenedToFull r f) a = 0 := by
  rw [QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap_apply]
  apply ((f1024Why24OddPivotRationalPlace r a).evaluateRegular_eq_zero_iff
    (f : F1024TowerLevel (2 * r + 2)) _).mpr
  rw [Valuation.mem_maximalIdeal_iff]
  have hbound :=
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_riemannRochSubmodule_iff
      (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
      (f : F1024TowerLevel (2 * r + 2))).mp f.2
      (f1024Why24OddPivotRationalPlace r a).place
  rw [Finsupp.sub_apply, f1024Why24OddADivisor_apply_pivot,
    f1024Why24OddPivotDivisor_apply_pivot] at hbound
  change (f1024Why24OddPivotRationalPlace r a).place.valuation
      (f : F1024TowerLevel (2 * r + 2)) < 1
  calc
    _ ≤ WithZero.exp (0 - 1) := hbound
    _ < 1 := by
      rw [← WithZero.exp_zero, f1024Tower_exp_lt_exp]
      omega

private noncomputable def f1024Why24OddShortenedToKernel (r : ℕ)
    (f : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)) :
    f1024Why24OddShortenedKernel r :=
  ⟨⟨f1024Why24OddScaledEvaluationLinearMap r
      (f1024Why24OddShortenedToFull r f),
    f1024Why24OddScaledEvaluationLinearMap_mem r
      (f1024Why24OddShortenedToFull r f)⟩, by
    funext a
    change f1024Why24OddCoordinateWeight r
        (f1024Why24OddPivotEmbedding r a) *
      QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
        (f1024Why24OddADivisor r)
        (f1024Why24OddPivotRationalPlace r)
        (f1024Why24OddADivisor_apply_pivot r)
        (f1024Why24OddShortenedToFull r f) a = 0
    rw [f1024Why24OddShortenedToFull_pivotEvaluation_eq_zero, mul_zero]⟩

private theorem f1024Why24OddScaledShortenedEvaluation_eq_stabilizerRow
    (r : ℕ)
    (f : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)) :
    f1024Why24OddScaledShortenedEvaluationLinearMap r f =
      f1024Why24OddStabilizerRow r
        (f1024Why24OddShortenedToKernel r f) := by
  rfl

/-- The displayed stabilizer span is exactly the source's scaled shortened
AG code. -/
theorem f1024Why24OddStabilizerCode_eq_scaledShortenedAGCode (r : ℕ) :
    (f1024Why24OddWeightedMatrix r).stabilizerCode =
      f1024Why24OddScaledShortenedAGCode r := by
  apply congrArg (fun carrier : Submodule F1024
      (QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r)) =>
    ({ carrier := carrier } : QEC.Coding.LinearCode F1024
      (f1024Why24OddPhysicalSite r)))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro word hword
    rcases hword with ⟨h, rfl⟩
    change f1024Why24OddStabilizerRow r h ∈
      (f1024Why24OddScaledShortenedEvaluationLinearMap r).range
    rcases h.1.2 with ⟨f, hf⟩
    have hzeroPointwise : ∀ a : f1024Why24OddLogical r,
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddPivotRationalPlace r)
          (f1024Why24OddADivisor_apply_pivot r) f a = 0 := by
      intro a
      have hscaled := congrFun h.2 a
      simp only [Pi.zero_apply] at hscaled
      change h.1.1 (f1024Why24OddPivotEmbedding r a) = 0 at hscaled
      rw [← hf] at hscaled
      change f1024Why24OddCoordinateWeight r
          (f1024Why24OddPivotEmbedding r a) *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddPivotRationalPlace r)
          (f1024Why24OddADivisor_apply_pivot r) f a = 0 at hscaled
      exact (mul_eq_zero.mp hscaled).resolve_left
        (f1024Why24OddCoordinateWeight_ne_zero r
          (f1024Why24OddPivotEmbedding r a))
    have hzero :
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddPivotRationalPlace r)
          (f1024Why24OddADivisor_apply_pivot r) f = 0 := by
      funext a
      exact hzeroPointwise a
    let shortened :
        QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) :=
      ⟨(f : F1024TowerLevel (2 * r + 2)),
        QEC.Coding.AlgebraicGeometry.evaluationZero_mem_riemannRochSubmodule_sub
          (f1024Why24OddADivisor r)
          (f1024Why24OddPivotRationalPlace r)
          (f1024Why24OddPivotRationalPlace_injective r)
          (f1024Why24OddADivisor_apply_pivot r) f hzero⟩
    refine ⟨shortened, ?_⟩
    funext site
    have hcoordinate := congrFun hf site.1
    change f1024Why24OddCoordinateWeight r site.1 *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
          (f1024Why24OddPhysicalRationalPlace r)
          (f1024Why24OddShortenedDivisor_apply_physical r) shortened site =
      h.1.1 site.1
    rw [← hcoordinate]
    rfl
  · intro word hword
    rcases hword with ⟨f, rfl⟩
    rw [f1024Why24OddScaledShortenedEvaluation_eq_stabilizerRow]
    exact Submodule.subset_span
      ⟨f1024Why24OddShortenedToKernel r f, rfl⟩

private noncomputable def f1024Why24OddPhysicalCoordinateScaleEquiv (r : ℕ) :
    QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r) ≃ₗ[F1024]
      QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r) where
  toFun x site := f1024Why24OddCoordinateWeight r site.1 * x site
  invFun x site := (f1024Why24OddCoordinateWeight r site.1)⁻¹ * x site
  left_inv x := by
    funext site
    field_simp [f1024Why24OddCoordinateWeight_ne_zero r site.1]
  right_inv x := by
    funext site
    field_simp [f1024Why24OddCoordinateWeight_ne_zero r site.1]
  map_add' x y := by
    funext site
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    funext site
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

private theorem f1024Why24OddPhysicalCoordinateScale_hammingWeight
    (r : ℕ) (x : QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r)) :
    QEC.Coding.HammingWeight
        (f1024Why24OddPhysicalCoordinateScaleEquiv r x) =
      QEC.Coding.HammingWeight x := by
  unfold QEC.Coding.HammingWeight QEC.Coding.hammingSupport
  congr 1
  ext site
  simp [f1024Why24OddPhysicalCoordinateScaleEquiv,
    f1024Why24OddCoordinateWeight_ne_zero r site.1]

private theorem f1024Why24OddPhysicalCoordinateScale_mem_shortenedDual
    (r : ℕ)
    {x : QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r)}
    (hx : x ∈ (f1024Why24OddScaledShortenedAGCode r).dual.carrier) :
    f1024Why24OddPhysicalCoordinateScaleEquiv r x ∈
      (f1024Why24OddShortenedAGCode r).dual.carrier := by
  refine ((f1024Why24OddShortenedAGCode r).mem_dual _).mpr ?_
  intro word hword
  rcases hword with ⟨f, rfl⟩
  have hscaled : f1024Why24OddScaledShortenedEvaluationLinearMap r f ∈
      (f1024Why24OddScaledShortenedAGCode r).carrier := ⟨f, rfl⟩
  have horth := (f1024Why24OddScaledShortenedAGCode r).orthogonal_of_mem_dual
    hx hscaled
  change (∑ site : f1024Why24OddPhysicalSite r,
      x site * (f1024Why24OddCoordinateWeight r site.1 *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
          (f1024Why24OddPhysicalRationalPlace r)
          (f1024Why24OddShortenedDivisor_apply_physical r) f site)) = 0 at horth
  change (∑ site : f1024Why24OddPhysicalSite r,
      (f1024Why24OddCoordinateWeight r site.1 * x site) *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
          (f1024Why24OddPhysicalRationalPlace r)
          (f1024Why24OddShortenedDivisor_apply_physical r) f site) = 0
  simpa only [mul_assoc, mul_left_comm, mul_comm] using horth

/-- Coordinate scaling preserves weight, so the actual displayed stabilizer
dual inherits the shortened AG designed distance. -/
theorem f1024Why24OddStabilizerCode_dual_distance_lower_bound (r : ℕ) :
    (selectedDistanceLowerBound (oddGenus r) : WithTop ℕ) ≤
      QEC.Coding.HypergraphProduct.extendedMinimumDistance
        (f1024Why24OddWeightedMatrix r).stabilizerCode.dual := by
  classical
  rw [QEC.Coding.HypergraphProduct.extendedMinimumDistance]
  apply QEC.Coding.HypergraphProduct.le_finitePredicateMinimum
  intro x hx
  have hxscaled : x ∈
      (f1024Why24OddScaledShortenedAGCode r).dual.carrier := by
    rw [← f1024Why24OddStabilizerCode_eq_scaledShortenedAGCode]
    exact hx.1
  let y := f1024Why24OddPhysicalCoordinateScaleEquiv r x
  have hy : y ∈ (f1024Why24OddShortenedAGCode r).dual.carrier :=
    f1024Why24OddPhysicalCoordinateScale_mem_shortenedDual r hxscaled
  have hy0 : y ≠ 0 := by
    intro hy0
    apply hx.2
    exact (f1024Why24OddPhysicalCoordinateScaleEquiv r).injective
      (hy0.trans (map_zero _).symm)
  calc
    (selectedDistanceLowerBound (oddGenus r) : WithTop ℕ) ≤
        QEC.Coding.HypergraphProduct.extendedMinimumDistance
          (f1024Why24OddShortenedAGCode r).dual :=
      f1024Why24OddShortenedAGCode_dual_distance_lower_bound r
    _ ≤ (QEC.Coding.HammingWeight y : WithTop ℕ) := by
      rw [QEC.Coding.HypergraphProduct.extendedMinimumDistance]
      exact QEC.Coding.HypergraphProduct.finitePredicateMinimum_le_of ⟨hy, hy0⟩
    _ = (QEC.Coding.HammingWeight x : WithTop ℕ) := by
      rw [f1024Why24OddPhysicalCoordinateScale_hammingWeight]

/-- The physical CSS Z distance has the source lower bound. -/
theorem f1024Why24OddCSSZDistance_lower_bound (r : ℕ) :
    (selectedDistanceLowerBound (oddGenus r) : WithTop ℕ) ≤
      (f1024Why24OddWeightedMatrix r).cssZDistance := by
  classical
  rw [QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.cssZDistance]
  apply QEC.Coding.HypergraphProduct.le_finitePredicateMinimum
  intro x hx
  have hx0 : x ≠ 0 := by
    intro hxzero
    subst x
    exact hx.2 (Submodule.zero_mem _)
  calc
    (selectedDistanceLowerBound (oddGenus r) : WithTop ℕ) ≤
        QEC.Coding.HypergraphProduct.extendedMinimumDistance
          (f1024Why24OddWeightedMatrix r).stabilizerCode.dual :=
      f1024Why24OddStabilizerCode_dual_distance_lower_bound r
    _ ≤ (QEC.Coding.HammingWeight x : WithTop ℕ) := by
      rw [QEC.Coding.HypergraphProduct.extendedMinimumDistance]
      exact QEC.Coding.HypergraphProduct.finitePredicateMinimum_le_of
        ⟨hx.1, hx0⟩

/-- The raw matrix comparison gives the same source lower bound in the X
sector. -/
theorem f1024Why24OddCSSXDistance_lower_bound (r : ℕ) :
    (selectedDistanceLowerBound (oddGenus r) : WithTop ℕ) ≤
      (f1024Why24OddWeightedMatrix r).cssXDistance :=
  (f1024Why24OddCSSZDistance_lower_bound r).trans
    ((f1024Why24OddWeightedMatrix r).cssZDistance_le_cssXDistance)

/-- The actual physical block length `n_r`. -/
def f1024Why24OddLength (r : ℕ) : ℕ :=
  Fintype.card (f1024Why24OddPhysicalSite r)

/-- The actual logical-register size `k_r`. -/
def f1024Why24OddDimension (r : ℕ) : ℕ :=
  selectedLogicalCount (oddGenus r)

/-- The source candidate decoding radius `t_r`. -/
def f1024Why24OddDecodingRadius (r : ℕ) : ℕ :=
  selectedDecodingRadius (oddGenus r)

private theorem f1024Why24OddLogical_nonempty (r : ℕ) :
    0 < selectedLogicalCount (oddGenus r) := by
  have hlarge := f1024Why24OddGenus_lower_bound r
  simp only [selectedLogicalCount]
  omega

private theorem f1024Why24OddCSSZDistance_le_length (r : ℕ) :
    (f1024Why24OddWeightedMatrix r).cssZDistance ≤
      (f1024Why24OddLength r : WithTop ℕ) := by
  classical
  let a : f1024Why24OddLogical r :=
    ⟨0, f1024Why24OddLogical_nonempty r⟩
  let witness := (f1024Why24OddWeightedMatrix r).dualLogicalRow a
  have hwitness :
      witness ∈ (f1024Why24OddWeightedMatrix r).stabilizerCode.dual.carrier :=
    (f1024Why24OddWeightedMatrix r).dualLogicalRow_mem_stabilizerCode_dual a
  have hwitnessOutside :
      witness ∉ (f1024Why24OddWeightedMatrix r).rowCode.dual.carrier := by
    intro hdual
    have horth := (f1024Why24OddWeightedMatrix r).rowCode.orthogonal_of_mem_dual
      hdual (Submodule.subset_span ⟨Sum.inl a, rfl⟩)
    simp only [QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.row_inl]
      at horth
    have hpair :=
      (f1024Why24OddWeightedMatrix r).logicalRow_dualLogicalRow_pairing a a
    have hpair' : QEC.Coding.wordPairing witness
        ((f1024Why24OddWeightedMatrix r).logicalRow a) = 1 := by
      rw [QEC.Coding.wordPairing_apply, dotProduct_comm,
        ← QEC.Coding.wordPairing_apply]
      simpa using hpair
    rw [hpair'] at horth
    exact one_ne_zero horth
  calc
    (f1024Why24OddWeightedMatrix r).cssZDistance ≤
        (QEC.Coding.HammingWeight witness : WithTop ℕ) := by
      rw [QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.cssZDistance]
      exact QEC.Coding.HypergraphProduct.finitePredicateMinimum_le_of
        ⟨hwitness, hwitnessOutside⟩
    _ ≤ (f1024Why24OddLength r : WithTop ℕ) := by
      have hweight : QEC.Coding.HammingWeight witness ≤
          f1024Why24OddLength r := by
        unfold QEC.Coding.HammingWeight f1024Why24OddLength
        exact Finset.card_le_univ (QEC.Coding.hammingSupport witness)
      exact_mod_cast hweight

private theorem f1024Why24OddCSSZDistance_ne_top (r : ℕ) :
    (f1024Why24OddWeightedMatrix r).cssZDistance ≠ ⊤ := by
  intro htop
  have hle := f1024Why24OddCSSZDistance_le_length r
  rw [htop] at hle
  exact WithTop.not_top_le_coe (f1024Why24OddLength r) hle

/-- The finite natural-valued CSS distance `d_r = d_Z`. -/
noncomputable def f1024Why24OddDistance (r : ℕ) : ℕ :=
  Classical.choose
    (WithTop.ne_top_iff_exists.mp (f1024Why24OddCSSZDistance_ne_top r))

private theorem f1024Why24OddDistance_coe (r : ℕ) :
    (f1024Why24OddDistance r : WithTop ℕ) =
      (f1024Why24OddWeightedMatrix r).cssZDistance :=
  Classical.choose_spec
    (WithTop.ne_top_iff_exists.mp (f1024Why24OddCSSZDistance_ne_top r))

/-- The actual CSS distance satisfies the designed lower bound. -/
theorem f1024Why24OddDistance_lower_bound (r : ℕ) :
    selectedDistanceLowerBound (oddGenus r) ≤
      f1024Why24OddDistance r := by
  exact_mod_cast (show
    (selectedDistanceLowerBound (oddGenus r) : WithTop ℕ) ≤
      (f1024Why24OddDistance r : WithTop ℕ) by
        rw [f1024Why24OddDistance_coe]
        exact f1024Why24OddCSSZDistance_lower_bound r)

private theorem f1024Why24OddDistance_le_length (r : ℕ) :
    f1024Why24OddDistance r ≤ f1024Why24OddLength r := by
  exact_mod_cast (show
    (f1024Why24OddDistance r : WithTop ℕ) ≤
      (f1024Why24OddLength r : WithTop ℕ) by
        rw [f1024Why24OddDistance_coe]
        exact f1024Why24OddCSSZDistance_le_length r)

/-- The actual physical length obeys WHY24's finite sandwich. -/
theorem f1024Why24OddLength_bounds (r : ℕ) :
    selectedPhysicalLengthLowerBound (oddGenus r) ≤
        f1024Why24OddLength r ∧
      f1024Why24OddLength r ≤
        selectedPhysicalLengthUpperBound (oddGenus r) := by
  have hlower := f1024Why24OddRetainedCandidateIndex_card_lower_bound r
  have hupper := f1024Why24OddRetainedCandidateIndex_card_upper_bound r
  have hlogical := f1024Why24OddLogicalCount_le_retainedCard r
  have hmod := f1024Why24OddGenus_mod_eight r
  have hlarge := f1024Why24OddGenus_lower_bound r
  rw [f1024Why24OddLength, f1024Why24OddPhysicalSite_card]
  simp only [selectedPhysicalLengthLowerBound,
    selectedPhysicalLengthUpperBound, selectedPlaceCount,
    selectedLogicalCount] at hlower hupper ⊢
  constructor <;> omega

private theorem f1024Why24OddRadius_lt_designedDistance (r : ℕ) :
    2 * selectedDecodingRadius (oddGenus r) <
      selectedDistanceLowerBound (oddGenus r) := by
  have hmod := f1024Why24OddGenus_mod_eight r
  have hlarge := f1024Why24OddGenus_lower_bound r
  simp only [selectedDecodingRadius, selectedDistanceLowerBound,
    selectedDivisorDegree, selectedLogicalCount]
  omega

/-- The source radius is strictly below half the actual CSS distance. -/
theorem f1024Why24OddDecodingRadius_correctable (r : ℕ) :
    2 * f1024Why24OddDecodingRadius r < f1024Why24OddDistance r := by
  unfold f1024Why24OddDecodingRadius
  exact (f1024Why24OddRadius_lt_designedDistance r).trans_le
    (f1024Why24OddDistance_lower_bound r)

private theorem f1024Why24OddGenus_ge_power (r : ℕ) :
    32 ^ (r + 1) ≤ oddGenus r := by
  let q : ℤ := (32 : ℤ) ^ (r + 1)
  have hqNat : 32 ≤ 32 ^ (r + 1) := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 32)
      (by omega : 1 ≤ r + 1)
    norm_num at h ⊢
    exact h
  have hq : (32 : ℤ) ≤ q := by
    dsimp only [q]
    exact_mod_cast hqNat
  have hpower : (32 : ℤ) ^ (2 * r + 2) = q * q := by
    dsimp only [q]
    rw [show 2 * r + 2 = (r + 1) + (r + 1) by omega, pow_add]
  have hcast := f1024TowerLevel_oddGenus_cast r
  have hbound : q ≤ (oddGenus r : ℤ) := by
    rw [hcast, hpower]
    nlinarith
  dsimp only [q] at hbound
  exact_mod_cast hbound

private theorem f1024Why24OddGenus_tendsto_atTop :
    Filter.Tendsto oddGenus Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono
    (f := fun r : ℕ => 32 ^ (r + 1))
    (g := oddGenus)
    (f1024Why24OddGenus_ge_power)
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (32 : ℕ))).comp
    (Filter.tendsto_add_atTop_nat 1)

private theorem f1024Why24OddGenus_le_length (r : ℕ) :
    oddGenus r ≤ f1024Why24OddLength r := by
  calc
    oddGenus r ≤ selectedPhysicalLengthLowerBound (oddGenus r) := by
      have hlarge := f1024Why24OddGenus_lower_bound r
      simp only [selectedPhysicalLengthLowerBound]
      omega
    _ ≤ f1024Why24OddLength r := (f1024Why24OddLength_bounds r).1

/-- The selected physical block lengths diverge. -/
theorem f1024Why24OddLength_tendsto_atTop :
    Filter.Tendsto f1024Why24OddLength Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_mono f1024Why24OddGenus_le_length
    f1024Why24OddGenus_tendsto_atTop

private theorem f1024Why24OddDimension_le_length (r : ℕ) :
    f1024Why24OddDimension r ≤ f1024Why24OddLength r := by
  have hlarge := f1024Why24OddGenus_lower_bound r
  have hlower := (f1024Why24OddLength_bounds r).1
  simp only [f1024Why24OddDimension, selectedLogicalCount,
    selectedPhysicalLengthLowerBound] at hlower ⊢
  omega

private theorem f1024Why24OddLength_le_twentyFour_mul_dimension (r : ℕ) :
    f1024Why24OddLength r ≤ 24 * f1024Why24OddDimension r := by
  have hlarge := f1024Why24OddGenus_lower_bound r
  have hupper := (f1024Why24OddLength_bounds r).2
  simp only [f1024Why24OddDimension, selectedLogicalCount,
    selectedPhysicalLengthUpperBound] at hupper ⊢
  omega

private theorem f1024Why24OddLength_le_twentyFour_mul_distance (r : ℕ) :
    f1024Why24OddLength r ≤ 24 * f1024Why24OddDistance r := by
  have hlarge := f1024Why24OddGenus_lower_bound r
  have hupper := (f1024Why24OddLength_bounds r).2
  have hlower := f1024Why24OddDistance_lower_bound r
  simp only [selectedPhysicalLengthUpperBound,
    selectedDistanceLowerBound, selectedDivisorDegree,
    selectedLogicalCount] at hupper hlower
  omega

private theorem f1024Why24OddRadius_le_length (r : ℕ) :
    f1024Why24OddDecodingRadius r ≤ f1024Why24OddLength r := by
  have hlarge := f1024Why24OddGenus_lower_bound r
  have hlower := (f1024Why24OddLength_bounds r).1
  simp only [f1024Why24OddDecodingRadius, selectedDecodingRadius,
    selectedPhysicalLengthLowerBound] at hlower ⊢
  omega

private theorem f1024Why24OddLength_le_twoForty_mul_radius (r : ℕ) :
    f1024Why24OddLength r ≤ 240 * f1024Why24OddDecodingRadius r := by
  have hlarge := f1024Why24OddGenus_lower_bound r
  have hupper := (f1024Why24OddLength_bounds r).2
  have hmod := f1024Why24OddGenus_mod_eight r
  simp only [f1024Why24OddDecodingRadius, selectedDecodingRadius,
    selectedPhysicalLengthUpperBound] at hupper ⊢
  omega

/-- The actual encoded-logical count is `Theta(n_r)`. -/
theorem f1024Why24OddDimension_isTheta_length :
    Asymptotics.IsTheta Filter.atTop
      (fun r : ℕ => (f1024Why24OddDimension r : ℝ))
      (fun r : ℕ => (f1024Why24OddLength r : ℝ)) := by
  constructor
  · apply Asymptotics.isBigO_of_le Filter.atTop
    intro r
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (f1024Why24OddDimension r : ℝ)),
      abs_of_nonneg (by positivity : 0 ≤ (f1024Why24OddLength r : ℝ))]
    exact_mod_cast f1024Why24OddDimension_le_length r
  · apply Asymptotics.isBigO_of_le' Filter.atTop (c := 24)
    intro r
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (f1024Why24OddLength r : ℝ)),
      abs_of_nonneg (by positivity : 0 ≤ (f1024Why24OddDimension r : ℝ))]
    exact_mod_cast f1024Why24OddLength_le_twentyFour_mul_dimension r

/-- The actual CSS distance is `Theta(n_r)`. -/
theorem f1024Why24OddDistance_isTheta_length :
    Asymptotics.IsTheta Filter.atTop
      (fun r : ℕ => (f1024Why24OddDistance r : ℝ))
      (fun r : ℕ => (f1024Why24OddLength r : ℝ)) := by
  constructor
  · apply Asymptotics.isBigO_of_le Filter.atTop
    intro r
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (f1024Why24OddDistance r : ℝ)),
      abs_of_nonneg (by positivity : 0 ≤ (f1024Why24OddLength r : ℝ))]
    exact_mod_cast f1024Why24OddDistance_le_length r
  · apply Asymptotics.isBigO_of_le' Filter.atTop (c := 24)
    intro r
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (f1024Why24OddLength r : ℝ)),
      abs_of_nonneg (by positivity : 0 ≤ (f1024Why24OddDistance r : ℝ))]
    exact_mod_cast f1024Why24OddLength_le_twentyFour_mul_distance r

/-- The source decoder radius is `Theta(n_r)`. -/
theorem f1024Why24OddDecodingRadius_isTheta_length :
    Asymptotics.IsTheta Filter.atTop
      (fun r : ℕ => (f1024Why24OddDecodingRadius r : ℝ))
      (fun r : ℕ => (f1024Why24OddLength r : ℝ)) := by
  constructor
  · apply Asymptotics.isBigO_of_le Filter.atTop
    intro r
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (f1024Why24OddDecodingRadius r : ℝ)),
      abs_of_nonneg (by positivity : 0 ≤ (f1024Why24OddLength r : ℝ))]
    exact_mod_cast f1024Why24OddRadius_le_length r
  · apply Asymptotics.isBigO_of_le' Filter.atTop (c := 240)
    intro r
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (f1024Why24OddLength r : ℝ)),
      abs_of_nonneg (by positivity : 0 ≤ (f1024Why24OddDecodingRadius r : ℝ))]
    exact_mod_cast f1024Why24OddLength_le_twoForty_mul_radius r

/-- The intrinsic Z-error syndrome: physical words modulo the actual
classical code `G₀⊥`. -/
abbrev f1024Why24OddZSyndrome (r : ℕ) :=
  QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r) ⧸
    (f1024Why24OddWeightedMatrix r).stabilizerCode.dual.carrier

/-- The syndrome occupied by a physical Z-error word. -/
def f1024Why24OddZSyndromeMap (r : ℕ)
    (error : QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r)) :
    f1024Why24OddZSyndrome r :=
  Submodule.Quotient.mk error

/-- The trivial syndrome is exactly membership in `G₀⊥`. -/
theorem f1024Why24OddZSyndrome_eq_zero_iff (r : ℕ)
    (error : QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r)) :
    f1024Why24OddZSyndromeMap r error = 0 ↔
      error ∈ (f1024Why24OddWeightedMatrix r).stabilizerCode.dual.carrier := by
  change Submodule.Quotient.mk error = Submodule.Quotient.mk 0 ↔ _
  rw [Submodule.Quotient.eq]
  simp

private theorem f1024Why24OddHammingWeight_neg (r : ℕ)
    (x : QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r)) :
    QEC.Coding.HammingWeight (-x) = QEC.Coding.HammingWeight x := by
  unfold QEC.Coding.HammingWeight QEC.Coding.hammingSupport
  congr 1
  ext site
  simp

/-- Equal intrinsic syndromes determine equal errors throughout the proved
decoding-radius ball.  This is the exact finite interface consumed by #888's
later polynomial decoder. -/
theorem f1024Why24OddZSyndrome_injective_on_decodingBall (r : ℕ)
    (x y : QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r))
    (hx : QEC.Coding.HammingWeight x ≤ f1024Why24OddDecodingRadius r)
    (hy : QEC.Coding.HammingWeight y ≤ f1024Why24OddDecodingRadius r)
    (hsyndrome : f1024Why24OddZSyndromeMap r x =
      f1024Why24OddZSyndromeMap r y) :
    x = y := by
  classical
  by_contra hxy
  have hmem : x - y ∈
      (f1024Why24OddWeightedMatrix r).stabilizerCode.dual.carrier := by
    change Submodule.Quotient.mk x = Submodule.Quotient.mk y at hsyndrome
    rwa [Submodule.Quotient.eq] at hsyndrome
  have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hminimum :
      QEC.Coding.HypergraphProduct.extendedMinimumDistance
          (f1024Why24OddWeightedMatrix r).stabilizerCode.dual ≤
        (QEC.Coding.HammingWeight (x - y) : WithTop ℕ) := by
    rw [QEC.Coding.HypergraphProduct.extendedMinimumDistance]
    exact QEC.Coding.HypergraphProduct.finitePredicateMinimum_le_of
      ⟨hmem, hne⟩
  have hlower : selectedDistanceLowerBound (oddGenus r) ≤
      QEC.Coding.HammingWeight (x - y) := by
    exact_mod_cast
      (f1024Why24OddStabilizerCode_dual_distance_lower_bound r |>.trans hminimum)
  have hweight : QEC.Coding.HammingWeight (x - y) ≤
      2 * f1024Why24OddDecodingRadius r := by
    calc
      QEC.Coding.HammingWeight (x - y) =
          QEC.Coding.HammingWeight (x + -y) := by rw [sub_eq_add_neg]
      _ ≤ QEC.Coding.HammingWeight x + QEC.Coding.HammingWeight (-y) :=
        QEC.Coding.HammingWeight_add_le x (-y)
      _ = QEC.Coding.HammingWeight x + QEC.Coding.HammingWeight y := by
        rw [f1024Why24OddHammingWeight_neg]
      _ ≤ 2 * f1024Why24OddDecodingRadius r := by omega
  have hradius : 2 * f1024Why24OddDecodingRadius r <
      selectedDistanceLowerBound (oddGenus r) := by
    exact f1024Why24OddRadius_lt_designedDistance r
  omega

end

end QEC.Distillation.Why24AGFamily
