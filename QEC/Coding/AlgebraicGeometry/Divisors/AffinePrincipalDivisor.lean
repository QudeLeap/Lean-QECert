/-
Affine principal-divisor construction.

For the finite places in the selected `k[X]` chart, Mathlib represents a
nonzero element of the fraction field by a numerator and denominator in the
integral closure.  The factorizations of their principal ideals have finite
support.  This file packages the resulting difference of factor counts as a
genuine `Finsupp` divisor on `AffinePlace.carrier`.

This is deliberately an *affine* principal divisor.  Its carrier contains
only the height-one primes of the chosen integral closure.  In particular, it
does not include a place over infinity, does not claim to be a divisor on the
all-place carrier, and makes no degree-zero or product-formula assertion.

-/

import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.DedekindDomain.Factorization
import QEC.Coding.AlgebraicGeometry.Places.AffineGlobalPlace
import QEC.Coding.AlgebraicGeometry.Divisors.Divisor

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc WithZero nonZeroDivisors

namespace AffinePlace

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]

noncomputable local instance : Algebra k F := constantAlgebra k F

/-- The finite-chart order coefficient of a nonzero function at an affine
place.  Mathlib's `valuationOfNeZero` is defined by the difference between the
factor counts of a numerator and denominator principal ideal; the sign here
matches `GlobalPlace.order`. -/
noncomputable def affinePrincipalCoefficient (P : carrier k F) (f : Fˣ) : ℤ :=
  -(P.valuationOfNeZero f).toAdd

/-- The numerator and denominator factor-count expression has cofinite zero
set.  This is the finite-support fact used below; it concerns only primes of
the selected affine coordinate ring. -/
theorem affinePrincipalCoefficient_eventually_zero (f : Fˣ) :
    ∀ᶠ P : carrier k F in Filter.cofinite,
      affinePrincipalCoefficient k F P f = 0 := by
  classical
  let B := _root_.FunctionField.ringOfIntegers k F
  let fraction := IsLocalization.sec B⁰ (f : F)
  have hnum : Ideal.span {fraction.1} ≠ (0 : Ideal B) := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact IsLocalization.sec_fst_ne_zero f.ne_zero
  have hden : Ideal.span {(fraction.2 : B)} ≠ (0 : Ideal B) := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.coe_ne_zero fraction.2
  filter_upwards [Associates.finite_factors hnum, Associates.finite_factors hden] with P hnumP hdenP
  unfold affinePrincipalCoefficient
  unfold IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero
  unfold IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroToFun
  change -((Multiplicative.ofAdd
    ((Associates.mk P.asIdeal).count (Associates.mk (Ideal.span {fraction.1})).factors : ℤ))⁻¹ /
    (Multiplicative.ofAdd
      ((Associates.mk P.asIdeal).count (Associates.mk (Ideal.span {(fraction.2 : B)})).factors : ℤ))⁻¹).toAdd = 0
  rw [hnumP, hdenP]
  norm_num

/-- The finite-chart coefficient family of a nonzero function has finite
support.  It is obtained from finite numerator and denominator ideal
factorizations, not from any completeness statement about all places. -/
theorem affinePrincipalCoefficient_finiteSupport (f : Fˣ) :
    (Function.support (fun P : carrier k F => affinePrincipalCoefficient k F P f)).Finite := by
  change {P : carrier k F | ¬affinePrincipalCoefficient k F P f = 0}.Finite
  exact Filter.eventually_cofinite.mp (affinePrincipalCoefficient_eventually_zero k F f)

/-- The principal divisor on the selected affine chart.  It has finite
support by numerator/denominator ideal factorization, but is not a divisor on
the all-place carrier. -/
noncomputable def affinePrincipalDivisor (f : Fˣ) : Divisor (carrier k F) :=
  Finsupp.ofSupportFinite
    (fun P => affinePrincipalCoefficient k F P f)
    (affinePrincipalCoefficient_finiteSupport k F f)

/-- The affine factor-count coefficient agrees with the order of the
corresponding packaged normalized valuation. -/
theorem affinePrincipalCoefficient_eq_order (P : carrier k F) (f : Fˣ) :
    affinePrincipalCoefficient k F P f =
      GlobalPlace.order (globalPlace k F P) (f : F) := by
  change -(P.valuationOfNeZero f).toAdd = -WithZero.log (valuation k F P (f : F))
  exact congrArg (fun x : ℤᵐ⁰ => -WithZero.log x) (P.valuationOfNeZero_eq f)

/-- The coefficient of the affine principal divisor is the normalized order
at that affine place. -/
theorem affinePrincipalDivisor_apply (f : Fˣ) (P : carrier k F) :
    affinePrincipalDivisor k F f P = GlobalPlace.order (globalPlace k F P) (f : F) := by
  change affinePrincipalCoefficient k F P f = GlobalPlace.order (globalPlace k F P) (f : F)
  exact affinePrincipalCoefficient_eq_order k F P f

/-- Affine principal divisors add under multiplication of nonzero functions.
This identity is restricted to the selected affine carrier. -/
theorem affinePrincipalDivisor_mul (f g : Fˣ) :
    affinePrincipalDivisor k F (f * g) =
      affinePrincipalDivisor k F f + affinePrincipalDivisor k F g := by
  ext P
  simp only [Finsupp.add_apply]
  rw [affinePrincipalDivisor_apply k F (f * g) P,
    affinePrincipalDivisor_apply k F f P,
    affinePrincipalDivisor_apply k F g P]
  simpa using GlobalPlace.order_mul (globalPlace k F P)
    (f := (f : F)) (g := (g : F)) f.ne_zero g.ne_zero

/-- Inversion negates the affine principal divisor.  No assertion is made
about the omitted places over infinity. -/
theorem affinePrincipalDivisor_inv (f : Fˣ) :
    affinePrincipalDivisor k F f⁻¹ = -affinePrincipalDivisor k F f := by
  ext P
  simp only [Finsupp.neg_apply]
  rw [affinePrincipalDivisor_apply k F f⁻¹ P,
    affinePrincipalDivisor_apply k F f P]
  simpa using GlobalPlace.order_inv (globalPlace k F P) (f : F)

end AffinePlace

end QEC.Coding.AlgebraicGeometry
