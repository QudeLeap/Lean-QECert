/-
Affine residue-constant construction.

For a height-one prime of the integral closure of `k[X]`, the constant field
has a canonical map to the actual ideal residue field: constants enter the
polynomial ring, then the integral closure, then reduce modulo the prime.
The resulting `Algebra` is deliberately local to this definition.  The
finite residue-degree construction belongs in `AffinePlaceDegree`: it uses
the finite integral-closure theorem, contraction of a nonzero height-one
prime, and finite quotient modules.  This smaller module contains only the
canonical scalar map on which that construction depends.

-/

import QEC.Coding.AlgebraicGeometry.Places.AffinePlace

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc WithZero

namespace AffinePlace

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]

/-- Constants reduce at an affine place through `k[X]`, the integral closure,
and the actual ideal residue-field map. -/
noncomputable def constantsToResidue (P : carrier k F) :
    k →+* residueField k F P :=
  (algebraMap (_root_.FunctionField.ringOfIntegers k F) (residueField k F P)).comp
    ((algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F)).comp Polynomial.C)

/-- The `k`-algebra on an affine residue field induced by reduction of
constants.  It is not a global instance, so a different ambient scalar map
cannot be selected implicitly. -/
@[reducible] noncomputable def residueAlgebra (P : carrier k F) :
    Algebra k (residueField k F P) :=
  (constantsToResidue k F P).toAlgebra

/-- The scalar map of the explicitly selected affine residue algebra is the
actual constant-reduction map.  This is the public boundary for clients that
need the algebra map itself, rather than the implementation of `toAlgebra`. -/
theorem residueAlgebra_algebraMap (P : carrier k F) :
    letI : Algebra k (residueField k F P) := residueAlgebra k F P
    algebraMap k (residueField k F P) = constantsToResidue k F P :=
  rfl

/-- Unfolding the affine constant-reduction map exposes its two genuine
intermediate maps. -/
theorem constantsToResidue_apply (P : carrier k F) (a : k) :
    constantsToResidue k F P a =
      algebraMap (_root_.FunctionField.ringOfIntegers k F) (residueField k F P)
        (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) (Polynomial.C a)) :=
  rfl

/-- A constant reduces to zero at an affine place precisely when its image in
the integral closure belongs to the selected height-one prime. -/
theorem constantsToResidue_eq_zero_iff (P : carrier k F) (a : k) :
    constantsToResidue k F P a = 0 ↔
      algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) (Polynomial.C a) ∈
        P.asIdeal := by
  simpa only [constantsToResidue_apply] using
    (Ideal.algebraMap_residueField_eq_zero
      (R := _root_.FunctionField.ringOfIntegers k F) (I := P.asIdeal)
      (x := algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) (Polynomial.C a)))

end AffinePlace

end QEC.Coding.AlgebraicGeometry
