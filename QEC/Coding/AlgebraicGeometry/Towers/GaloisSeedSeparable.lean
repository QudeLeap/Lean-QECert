import QEC.Coding.AlgebraicGeometry.Towers.GaloisBaseField

/-!
# Separability of the Garcia--Stichtenoth seed over F256(z)

The normal-closure family must start from a finite separable extension of the
fixed base `F256(z)`.  This file proves that property from the derivative of
the literal degree-240 equation for `x₀`, then composes it with the already
proved separability of every recursive seed level over `F256(x₀)`.  It does
not construct or assume the normal closure itself.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

open IntermediateField Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

private noncomputable def galoisSeedBasePolynomial : Polynomial F256 :=
  (Polynomial.X ^ 16 + Polynomial.X) ^ 15

private theorem galoisBaseZ_eq_seedPolynomial :
    galoisBaseZ = algebraMap (Polynomial F256) (RatFunc F256)
      galoisSeedBasePolynomial := by
  simp [galoisBaseZ, galoisBaseW, galoisSeedBasePolynomial,
    RatFunc.algebraMap_X]

private theorem galoisBaseZ_num :
    galoisBaseZ.num = galoisSeedBasePolynomial := by
  rw [galoisBaseZ_eq_seedPolynomial, RatFunc.num_algebraMap]

private theorem galoisBaseZ_denom :
    galoisBaseZ.denom = 1 := by
  rw [galoisBaseZ_eq_seedPolynomial, RatFunc.denom_algebraMap]

private theorem galoisSeedBasePolynomial_derivative :
    galoisSeedBasePolynomial.derivative =
      (Polynomial.X ^ 16 + Polynomial.X) ^ 14 := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) F256).injective 2
  rw [galoisSeedBasePolynomial, Polynomial.derivative_pow,
    Polynomial.derivative_add, Polynomial.derivative_X_pow,
    Polynomial.derivative_X]
  reduce_mod_char!
  simp

private theorem galoisBaseZ_ne_constant :
    ¬ ∃ c : F256, galoisBaseZ = RatFunc.C c := by
  rintro ⟨c, hc⟩
  apply galoisBaseZ_transcendental
  rw [hc]
  exact isAlgebraic_algebraMap c

private theorem galoisBaseMinpolyX_derivative_ne_zero :
    (galoisBaseZ.minpolyX GaloisBaseField).derivative ≠ 0 := by
  rw [RatFunc.minpolyX, galoisBaseZ_num, galoisBaseZ_denom,
    Polynomial.derivative_sub, Polynomial.derivative_map,
    galoisSeedBasePolynomial_derivative]
  simp only [Polynomial.map_one, Polynomial.derivative_mul,
    Polynomial.derivative_C, zero_mul, Polynomial.derivative_one,
    mul_zero, add_zero, sub_zero]
  apply Polynomial.map_ne_zero
  apply pow_ne_zero
  exact Polynomial.monic_X_pow_add (by norm_num) |>.ne_zero

/-- The rational seed coordinate `x₀` is separable over the actual fixed
base `F256(z)`. -/
theorem galoisBaseField_X_isSeparable :
    IsSeparable GaloisBaseField (RatFunc.X : RatFunc F256) := by
  have hirreducible :
      Irreducible (galoisBaseZ.minpolyX GaloisBaseField) :=
    galoisBaseZ.irreducible_minpolyX galoisBaseZ_ne_constant
  have hseparable :
      (galoisBaseZ.minpolyX GaloisBaseField).Separable :=
    (Polynomial.separable_iff_derivative_ne_zero hirreducible).2
      galoisBaseMinpolyX_derivative_ne_zero
  exact hseparable.of_dvd
    (minpoly.dvd GaloisBaseField (RatFunc.X : RatFunc F256)
      galoisBaseZ.minpolyX_aeval_X)

noncomputable instance galoisBaseFieldRatFuncSeparable :
    Algebra.IsSeparable GaloisBaseField (RatFunc F256) := by
  letI : Algebra.IsSeparable GaloisBaseField
      GaloisBaseField⟮(RatFunc.X : RatFunc F256)⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
      (F := GaloisBaseField) (E := RatFunc F256)).2
      galoisBaseField_X_isSeparable
  exact AlgEquiv.Algebra.isSeparable
    (RatFunc.IntermediateField.adjoinXEquiv (F256⟮galoisBaseZ⟯))

noncomputable instance galoisBaseFieldSeedSeparable (m : ℕ) :
    Algebra.IsSeparable GaloisBaseField (Field m) :=
  Algebra.IsSeparable.trans GaloisBaseField (RatFunc F256) (Field m)

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
