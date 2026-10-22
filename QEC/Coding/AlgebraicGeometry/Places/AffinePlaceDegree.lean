/-
Affine residue-degree construction.

For a height-one prime `P` of the integral closure `B` of `k[X]` in a finite
separable function field `F`, the contraction `p = P ∩ k[X]` is nonzero.
Its quotient is finite over the finite field `k`, using the power basis of
`k[X] / (generator p)`.  Mathlib's integral-closure finiteness theorem and
the quotient-under-lies-over theorem then make `B / P`, and hence its actual
ideal residue field, finite.  Thus every *affine* carrier point below has a
genuine finite residue degree.

This is deliberately not a global divisor-degree construction: the carrier
contains only the finite places of the chosen affine coordinate.  Places
above infinity and a complete global degree theory remain separate work.

-/

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import QEC.Coding.AlgebraicGeometry.Places.AffineResidue
import QEC.Coding.AlgebraicGeometry.Divisors.Divisor

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc WithZero

namespace AffinePlace

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]

/-- The prime of `k[X]` below an affine place. -/
noncomputable abbrev basePrime (P : carrier k F) : Ideal k[X] :=
  P.asIdeal.under k[X]

/-- The integral closure defining the affine-place carrier is finite over the
polynomial ring.  This is the direct finite-separable integral-closure API,
not an assumed residue-field finiteness hypothesis. -/
theorem finite_ringOfIntegers :
    Module.Finite k[X] (_root_.FunctionField.ringOfIntegers k F) :=
  IsIntegralClosure.finite k[X] k⟮X⟯ F (_root_.FunctionField.ringOfIntegers k F)

/-- Contracting a nonzero affine prime to `k[X]` remains nonzero. -/
theorem basePrime_ne_bot (P : carrier k F) : basePrime k F P ≠ ⊥ :=
  Ideal.under_ne_bot k[X] P.ne_bot

/-- The contracted polynomial quotient is finite-dimensional over the
constant field.  The generator is nonzero precisely because the contracted
prime is nonzero. -/
theorem finite_basePrime_quotient (P : carrier k F) :
    Module.Finite k (k[X] ⧸ basePrime k F P) := by
  classical
  rw [← Ideal.span_singleton_generator (basePrime k F P)]
  change Module.Finite k (AdjoinRoot (Submodule.IsPrincipal.generator (basePrime k F P)))
  exact
    (AdjoinRoot.powerBasis (by
      rw [Ne, ← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero]
      exact basePrime_ne_bot k F P)).finite

/-- The actual ideal residue field at every affine place is a finite type.
The proof factors through the contracted polynomial quotient and the finite
quotient module supplied by the lies-over API. -/
theorem finite_residueField (P : carrier k F) : Finite (residueField k F P) := by
  let B : Type _ := _root_.FunctionField.ringOfIntegers k F
  let p : Ideal k[X] := basePrime k F P
  letI : Module.Finite k[X] B := finite_ringOfIntegers k F
  letI : Module.Finite k (k[X] ⧸ p) := finite_basePrime_quotient k F P
  letI : Finite (k[X] ⧸ p) := Module.finite_of_finite k
  letI : Module.Finite (k[X] ⧸ p) (B ⧸ P.asIdeal) := by
    change Module.Finite (k[X] ⧸ P.asIdeal.under k[X])
      (_root_.FunctionField.ringOfIntegers k F ⧸ P.asIdeal)
    infer_instance
  letI : Module.Finite (B ⧸ P.asIdeal) (residueField k F P) :=
    Module.Finite.of_surjective (Algebra.linearMap _ _)
      P.asIdeal.bijective_algebraMap_quotient_residueField.surjective
  letI : Algebra (k[X] ⧸ p) (residueField k F P) :=
    ((algebraMap (B ⧸ P.asIdeal) (residueField k F P)).comp
      (algebraMap (k[X] ⧸ p) (B ⧸ P.asIdeal))).toAlgebra
  letI : IsScalarTower (k[X] ⧸ p) (B ⧸ P.asIdeal) (residueField k F P) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Module.Finite (k[X] ⧸ p) (residueField k F P) :=
    Module.Finite.trans (B ⧸ P.asIdeal) (residueField k F P)
  exact Module.finite_of_finite (k[X] ⧸ p)

/-- The canonical affine residue algebra is finite-dimensional, with no
additional hypothesis at the call site.  The `letI` fixes exactly the
constant-reduction algebra from `AffineResidue`. -/
theorem residueField_finiteDimensional (P : carrier k F) :
    letI : Algebra k (residueField k F P) := residueAlgebra k F P
    FiniteDimensional k (residueField k F P) := by
  letI : Algebra k (residueField k F P) := residueAlgebra k F P
  letI : Finite (residueField k F P) := finite_residueField k F P
  exact (Module.finite_iff_finite).mpr inferInstance

/-- The degree of an affine place is the dimension of its actual residue
field over the constant field via constant reduction. -/
noncomputable def residueDegree (P : carrier k F) : ℕ := by
  letI : Algebra k (residueField k F P) := residueAlgebra k F P
  letI : FiniteDimensional k (residueField k F P) :=
    residueField_finiteDimensional k F P
  exact Module.finrank k (residueField k F P)

/-- The affine divisor degree is the existing finitely supported divisor
degree specialized to the actual affine residue degrees. -/
noncomputable def divisorDegree (D : Divisor (carrier k F)) : ℤ :=
  Divisor.degree (residueDegree k F) D

/-- Affine divisor degree is definitionally the generic divisor degree with
the constructed residue-degree coefficient function. -/
theorem divisorDegree_eq (D : Divisor (carrier k F)) :
    divisorDegree k F D = Divisor.degree (residueDegree k F) D :=
  rfl

/-- The constructed affine divisor degree inherits additivity from the
generic finite-support divisor API. -/
theorem divisorDegree_add (D E : Divisor (carrier k F)) :
    divisorDegree k F (D + E) = divisorDegree k F D + divisorDegree k F E :=
  Divisor.degree_add (residueDegree k F) D E

/-- An affine place is rational when its specified constant-reduction map is
an equivalence.  This is affine-only data and does not imply rationality of
any global infinity place. -/
structure Rational (P : carrier k F) where
  constantsEquiv : k ≃+* residueField k F P
  constantsEquiv_apply (a : k) :
    constantsEquiv a = constantsToResidue k F P a

namespace Rational

/-- At an affine rational place, the canonical constant-reduction map is
bijective. -/
theorem constantsToResidue_bijective {P : carrier k F} (Q : Rational k F P) :
    Function.Bijective (constantsToResidue k F P) := by
  constructor
  · intro a b hab
    apply Q.constantsEquiv.injective
    simpa only [Q.constantsEquiv_apply] using hab
  · intro x
    obtain ⟨a, ha⟩ := Q.constantsEquiv.surjective x
    refine ⟨a, ?_⟩
    rw [← Q.constantsEquiv_apply a]
    exact ha

/-- A rational affine place has residue degree one. -/
theorem residueDegree_eq_one {P : carrier k F} (Q : Rational k F P) :
    residueDegree k F P = 1 := by
  unfold residueDegree
  letI : Algebra k (residueField k F P) := residueAlgebra k F P
  letI : FiniteDimensional k (residueField k F P) :=
    residueField_finiteDimensional k F P
  apply Module.finrank_of_bijective_algebraMap
  rw [residueAlgebra_algebraMap k F P]
  exact Q.constantsToResidue_bijective

end Rational

end AffinePlace

end QEC.Coding.AlgebraicGeometry
