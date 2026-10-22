import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.PolynomialAlgebra

/-!
# Arithmetic parameters for the Cartwright--Steger quotients

This file fixes the two matrix ranks used by the LSV complexes and constructs
their constant fields, rational function field, Laurent-series completion,
finite congruence residue fields, and projective linear groups.  The objects
are definitions, not caller-supplied construction data.

The source uses matrix rank `d`; the corresponding affine building and clique
complex have dimension `d - 1`.  Thus the two cases below are exactly
`3 -> 2` and `4 -> 3`.

The residue characteristic is an explicit prime parameter `q >= 5`.  This is
independent of the coefficient field `F_2` later used for simplicial chains
and CSS codes.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped MatrixGroups RatFunc

/-- Arithmetic input allowed by the LSV construction.  It contains only the
base prime and proofs of the source's elementary characteristic restrictions;
it does not contain matrices, groups, complexes, or property certificates. -/
structure BasePrime where
  q : Nat
  prime : q.Prime
  five_le : 5 <= q

instance (P : BasePrime) : Fact P.q.Prime := ⟨P.prime⟩

theorem BasePrime.two_le (P : BasePrime) : 2 <= P.q :=
  le_trans (by norm_num) P.five_le

theorem BasePrime.one_le (P : BasePrime) : 1 <= P.q :=
  le_trans (by norm_num) P.five_le

/-- The two matrix ranks used by the selected LSV quotient families. -/
inductive Rank where
  | three
  | four
  deriving DecidableEq

instance : Fintype Rank where
  elems := {.three, .four}
  complete := by intro rank; cases rank <;> simp

namespace Rank

/-- Matrix rank in the LSV notation. -/
def matrixRank : Rank -> Nat
  | three => 3
  | four => 4

/-- Dimension of the associated affine building / clique complex. -/
def complexDimension (r : Rank) : Nat := r.matrixRank - 1

@[simp] theorem matrixRank_three : matrixRank three = 3 := rfl
@[simp] theorem matrixRank_four : matrixRank four = 4 := rfl
@[simp] theorem complexDimension_three : complexDimension three = 2 := rfl
@[simp] theorem complexDimension_four : complexDimension four = 3 := rfl

theorem matrixRank_eq_three_or_four (r : Rank) :
    r.matrixRank = 3 \/ r.matrixRank = 4 := by
  cases r <;> simp

theorem two_le_matrixRank (r : Rank) : 2 <= r.matrixRank := by
  cases r <;> simp

/-- The congruence residue degree.  We take the cofinal sequence
`d * (3 + level)`: degree three already supplies the LSV numerical bound,
while divisibility by the matrix rank embeds the degree-`d` constant field in
every residue field.  That embedding is what makes the finite cyclic-algebra
matrix representation compatible with the Cartwright--Steger conjugates. -/
def residueExponent (r : Rank) (level : Nat) : Nat :=
  r.matrixRank * (3 + level)

theorem residueExponent_ne_zero (r : Rank) (level : Nat) :
    Not (r.residueExponent level = 0) := by
  cases r <;> simp [residueExponent, matrixRank]

theorem source_size_condition (P : BasePrime) (r : Rank) (level : Nat) :
    4 * r.matrixRank ^ 2 <= P.q ^ r.residueExponent level := by
  calc
    4 * r.matrixRank ^ 2 <= 64 := by cases r <;> norm_num [matrixRank]
    _ <= 5 ^ 3 := by norm_num
    _ <= P.q ^ 3 := pow_le_pow_left' P.five_le 3
    _ <= P.q ^ (3 + level) :=
      pow_le_pow_right' P.one_le (by omega)
    _ <= P.q ^ r.residueExponent level := by
      apply pow_le_pow_right' P.one_le
      simp [residueExponent]
      have := two_le_matrixRank r
      omega

end Rank

/-- The selected base field `F_q`. -/
abbrev BaseField (P : BasePrime) := ZMod P.q

/-- The degree-`d` constant-field extension `F_(q^d)`. -/
noncomputable abbrev ConstantExtension (P : BasePrime) (r : Rank) :=
  GaloisField P.q r.matrixRank

/-- The rational function field `F_q(y)`. -/
abbrev FunctionField (P : BasePrime) := RatFunc (BaseField P)

/-- The building local field `F_q((y))`. -/
abbrev BuildingLocalField (P : BasePrime) := LaurentSeries (BaseField P)

/-- The ring of integers `F_q[[y]]` inside the selected local field. -/
abbrev BuildingIntegerRing (P : BasePrime) := PowerSeries (BaseField P)

/-- The polynomial coordinate `y`. -/
abbrev PolynomialRing (P : BasePrime) := Polynomial (BaseField P)

/-- The source ring `R_T = F_q[y, 1/(1+y)]`. -/
abbrev IntegralArithmeticRing (P : BasePrime) :=
  Localization.Away (1 + Polynomial.X : PolynomialRing P)

/-- The source ring `R = F_q[y, 1/y, 1/(1+y)]`.  Localizing away
from `y(1+y)` makes both factors invertible. -/
abbrev ArithmeticRing (P : BasePrime) :=
  Localization.Away
    (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P)

/-- The `y`-adic place on the rational function field. -/
noncomputable abbrev yAdicPlace (P : BasePrime) :=
  RatFunc.polynomialValuationX (BaseField P)

/-- The canonical embedding of `F_q(y)` into its `y`-adic Laurent-series
completion. -/
noncomputable def functionFieldToBuildingLocalField (P : BasePrime) :
    RingHom (FunctionField P) (BuildingLocalField P) :=
  algebraMap (FunctionField P) (BuildingLocalField P)

theorem functionFieldToBuildingLocalField_injective (P : BasePrime) :
    Function.Injective (functionFieldToBuildingLocalField P) :=
  RingHom.injective _

/-- The finite field used at a hierarchy level.  Its cardinality grows with
`level`; no finite field or cardinality certificate is accepted from a
caller. -/
noncomputable abbrev ResidueField (P : BasePrime) (r : Rank) (level : Nat) :=
  GaloisField P.q (r.residueExponent level)

noncomputable instance (P : BasePrime) (r : Rank) :
    Fintype (ConstantExtension P r) :=
  Fintype.ofFinite _

noncomputable instance (P : BasePrime) (r : Rank) (level : Nat) :
    Fintype (ResidueField P r level) :=
  Fintype.ofFinite _

theorem natCard_constantExtension (P : BasePrime) (r : Rank) :
    Nat.card (ConstantExtension P r) = P.q ^ r.matrixRank :=
  GaloisField.card P.q r.matrixRank (by cases r <;> simp [Rank.matrixRank])

/-- A basis indexed by the actual matrix rank, rather than by an unspecified
chosen finite type. -/
noncomputable def constantBasis (P : BasePrime) (r : Rank) :
    Module.Basis (Fin r.matrixRank) (BaseField P) (ConstantExtension P r) :=
  Module.finBasisOfFinrankEq (BaseField P) (ConstantExtension P r)
    (GaloisField.finrank P.q (by cases r <;> simp [Rank.matrixRank]))

/-- Arithmetic Frobenius on the constant-field extension. -/
noncomputable def constantFrobenius (P : BasePrime) (r : Rank) :
    AlgEquiv (BaseField P) (ConstantExtension P r) (ConstantExtension P r) :=
  FiniteField.frobeniusAlgEquivOfAlgebraic
    (BaseField P) (ConstantExtension P r)

theorem constantFrobenius_order (P : BasePrime) (r : Rank) :
    orderOf (constantFrobenius P r) = r.matrixRank := by
  rw [constantFrobenius, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
  exact GaloisField.finrank P.q (by cases r <;> simp [Rank.matrixRank])

/-- A source-valid element of nonzero relative trace.  Since the selected
characteristic is at least five and the two ranks are three and four, the
constant `1` itself has trace `d` and is a completely explicit choice. -/
noncomputable def beta (P : BasePrime) (r : Rank) : ConstantExtension P r :=
  1

theorem trace_beta_ne_zero (P : BasePrime) (r : Rank) :
    Not (Algebra.trace (BaseField P) (ConstantExtension P r) (beta P r) = 0) := by
  rw [beta, ← map_one (algebraMap (BaseField P) (ConstantExtension P r)),
    Algebra.trace_algebraMap]
  simp only [nsmul_eq_mul, mul_one]
  rw [GaloisField.finrank P.q (by cases r <;> simp [Rank.matrixRank])]
  rw [ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt
    (lt_of_lt_of_le (by norm_num) (Rank.two_le_matrixRank r))
    (lt_of_le_of_lt (by cases r <;> simp [Rank.matrixRank]) P.five_le)

/-- The factor `1 + beta * X` used to split the cyclic algebra in the
explicit LSV construction. -/
noncomputable def betaLinearPolynomial (P : BasePrime) (r : Rank) :
    Polynomial (ConstantExtension P r) :=
  1 + Polynomial.C (beta P r) * Polynomial.X

/-- The polynomial `1 + y(X)`.  For the explicit choice `beta = 1`, the
relative norm of `1 + beta * X` is `(1 + X)^d`; we use that concrete formula
as the construction rather than storing a norm witness. -/
noncomputable def sourceOnePlusY (P : BasePrime) (r : Rank) :
    Polynomial (BaseField P) :=
  (1 + Polynomial.X) ^ r.matrixRank

/-- The source's explicit polynomial `y(X)`. -/
noncomputable def sourceYPolynomial (P : BasePrime) (r : Rank) :
    Polynomial (BaseField P) :=
  sourceOnePlusY P r - 1

theorem betaLinearPolynomial_eq_map (P : BasePrime) (r : Rank) :
    betaLinearPolynomial P r =
      (1 + Polynomial.X : PolynomialRing P).map
        (algebraMap (BaseField P) (ConstantExtension P r)) := by
  simp [betaLinearPolynomial, beta]

/-- The concrete power formula is exactly the LSV product of all Frobenius
conjugates of `1 + beta*X`; thus choosing `beta = 1` does not omit the norm
identity used by the source. -/
theorem sourceOnePlusY_map_eq_frobeniusProduct (P : BasePrime) (r : Rank) :
    (sourceOnePlusY P r).map
        (algebraMap (BaseField P) (ConstantExtension P r)) =
      ∏ i ∈ Finset.range r.matrixRank,
        (1 + Polynomial.C
          ((constantFrobenius P r ^ i) (beta P r)) * Polynomial.X) := by
  simp [sourceOnePlusY, beta]

/-- For the explicit choice `beta = 1`, the relative norm defining the source
coordinate is the `d`-th power of `1 + X`. -/
theorem sourceOnePlusY_eq_pow (P : BasePrime) (r : Rank) :
    sourceOnePlusY P r =
      (1 + Polynomial.X : PolynomialRing P) ^ r.matrixRank := by
  rfl

theorem sourceYPolynomial_eq_pow_sub_one (P : BasePrime) (r : Rank) :
    sourceYPolynomial P r =
      (1 + Polynomial.X : PolynomialRing P) ^ r.matrixRank - 1 := by
  rw [sourceYPolynomial, sourceOnePlusY_eq_pow]

/-- The LSV substitution polynomial has exactly the matrix rank as its
degree; consequently every fiber has at most `d` elements. -/
theorem sourceYPolynomial_natDegree (P : BasePrime) (r : Rank) :
    (sourceYPolynomial P r).natDegree = r.matrixRank := by
  rw [sourceYPolynomial_eq_pow_sub_one]
  have hmonic :
      (1 + Polynomial.X : PolynomialRing P).Monic := by
    simpa [add_comm] using
      (Polynomial.monic_X_add_C (1 : BaseField P))
  have hpowDegree :
      ((1 + Polynomial.X : PolynomialRing P) ^ r.matrixRank).natDegree =
        r.matrixRank := by
    rw [hmonic.natDegree_pow]
    have hbase :
        (1 + Polynomial.X : PolynomialRing P).natDegree = 1 := by
      simpa [add_comm] using
        (Polynomial.natDegree_X_add_C (1 : BaseField P))
    rw [hbase, Nat.mul_one]
  calc
    ((1 + Polynomial.X : PolynomialRing P) ^ r.matrixRank - 1).natDegree =
        ((1 + Polynomial.X : PolynomialRing P) ^ r.matrixRank).natDegree := by
      apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt
      rw [Polynomial.natDegree_one, hpowDegree]
      exact lt_of_lt_of_le (by norm_num) (Rank.two_le_matrixRank r)
    _ = r.matrixRank := hpowDegree

/-- Matrix of multiplication by a constant-field element in the fixed
rank-indexed basis. -/
noncomputable def constantRegularMatrix (P : BasePrime) (r : Rank) :
    AlgHom (BaseField P) (ConstantExtension P r)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) :=
  Algebra.leftMulMatrix (constantBasis P r)

theorem constantRegularMatrix_injective (P : BasePrime) (r : Rank) :
    Function.Injective (constantRegularMatrix P r) :=
  Algebra.leftMulMatrix_injective (constantBasis P r)

/-- Frobenius as an invertible rank-`d` matrix over the base field. -/
noncomputable def frobeniusGL (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BaseField P) :=
  (Matrix.GeneralLinearGroup.toLin' (constantBasis P r)).symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv
      (constantFrobenius P r).toLinearEquiv)

theorem natCard_residueField (P : BasePrime) (r : Rank) (level : Nat) :
    Nat.card (ResidueField P r level) =
      P.q ^ r.residueExponent level :=
  GaloisField.card P.q (r.residueExponent level)
    (Rank.residueExponent_ne_zero r level)

theorem residueField_unbounded (P : BasePrime) (r : Rank) (bound : Nat) :
    ∃ level, bound < Nat.card (ResidueField P r level) := by
  refine ⟨bound, ?_⟩
  rw [natCard_residueField]
  calc
    bound < 2 ^ bound := bound.lt_two_pow_self
    _ <= P.q ^ bound := pow_le_pow_left' P.two_le bound
    _ <= P.q ^ (3 + bound) :=
      pow_le_pow_right' P.one_le (by omega)
    _ <= P.q ^ r.residueExponent bound := by
      apply pow_le_pow_right' P.one_le
      simp [Rank.residueExponent]
      have := Rank.two_le_matrixRank r
      omega

/-- The actual projective general linear group over a selected residue field. -/
abbrev PGL (P : BasePrime) (r : Rank) (level : Nat) :=
  Matrix.ProjGenLinGroup (Fin r.matrixRank) (ResidueField P r level)

/-- The natural map `SL_d(L) -> PGL_d(L)`. -/
noncomputable def specialToProjective (P : BasePrime) (r : Rank) (level : Nat) :
    MonoidHom
      (Matrix.SpecialLinearGroup (Fin r.matrixRank) (ResidueField P r level))
      (PGL P r level) :=
  Matrix.ProjGenLinGroup.mk.comp Matrix.SpecialLinearGroup.toGL

/-- `PSL_d(L)` is constructed as the image of `SL_d(L)` in `PGL_d(L)`. -/
noncomputable def PSL (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PGL P r level) :=
  (specialToProjective P r level).range

theorem mem_PSL_iff (P : BasePrime) (r : Rank) (level : Nat)
    (g : PGL P r level) :
    g ∈ PSL P r level ↔
      ∃ s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level), specialToProjective P r level s = g := by
  rfl

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
