/-
Auxiliary affine-place construction.

The carrier in this file consists of height-one primes of the integral closure
of `k[X]` in a separable finite extension of `k(X)`.  Those are genuine
finite/affine places for that chosen coordinate, with actual adic valuations
and residue fields supplied by Mathlib.  They are *not* the all-place set of a
global function field: places above infinity have not yet been constructed.
Accordingly this module does not declare a final `Place` type, a global
divisor degree, a total rational-function evaluation, or an `L(G)` space.

-/

import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc WithZero

namespace AffinePlace

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]

/-- Finite places relative to the chosen affine coordinate `k[X]`. -/
abbrev carrier : Type _ :=
  IsDedekindDomain.HeightOneSpectrum (_root_.FunctionField.ringOfIntegers k F)

/-- The residue field at an auxiliary affine place. -/
abbrev residueField (P : carrier k F) : Type _ := P.asIdeal.ResidueField

/-- The genuine adic valuation attached to an auxiliary affine place. -/
noncomputable def valuation (P : carrier k F) : Valuation F ℤᵐ⁰ := P.valuation F

/-- Reduction of an integral element modulo an auxiliary affine place. -/
noncomputable def residue (P : carrier k F) :
    _root_.FunctionField.ringOfIntegers k F →+ residueField k F P :=
  (algebraMap (_root_.FunctionField.ringOfIntegers k F) (residueField k F P)).toAddMonoidHom

/-- An integral element reduces to zero exactly when it belongs to the prime. -/
theorem residue_eq_zero_iff (P : carrier k F)
    (x : _root_.FunctionField.ringOfIntegers k F) :
    residue k F P x = 0 ↔ x ∈ P.asIdeal := by
  change algebraMap (_root_.FunctionField.ringOfIntegers k F) P.asIdeal.ResidueField x = 0 ↔
    x ∈ P.asIdeal
  exact
    (Ideal.algebraMap_residueField_eq_zero
      (R := _root_.FunctionField.ringOfIntegers k F) (I := P.asIdeal) (x := x))

/-- The affine valuation agrees with its integral-domain adic valuation. -/
theorem valuation_of_integral (P : carrier k F)
    (x : _root_.FunctionField.ringOfIntegers k F) :
    valuation k F P x = P.intValuation x :=
  P.valuation_of_algebraMap (K := F) x

/-- The explicit field-embedding form of the affine valuation comparison.
This is the public boundary for clients whose terms already use the integral
closure map into `F`, such as the affine-to-global order bridge. -/
theorem valuation_algebraMap_of_integral (P : carrier k F)
    (x : _root_.FunctionField.ringOfIntegers k F) :
    valuation k F P
        (algebraMap (_root_.FunctionField.ringOfIntegers k F) F x) =
      P.intValuation x :=
  P.valuation_of_algebraMap (K := F) x

end AffinePlace

end QEC.Coding.AlgebraicGeometry
