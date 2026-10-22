import QEC.Coding.AlgebraicGeometry.Towers.Divisors
import QEC.Coding.AlgebraicGeometry.RiemannRoch.PolarDegree

/-!
# The base power parameter in the F256 Garcia--Stichtenoth tower

This file computes the degree of the actual base rational parameter
`X^17` in every recursively constructed tower field.  The recursion gives
the extension degree `16^m`; the generic pole-divisor degree theorem then
shows that the pole divisor of `X^17` has degree `17 * 16^m`.

At the original-family level `Field (i + 2)`, this equals
`selectedLength i / 15`. These are not the `SourceField` normal-closure
coordinates or fibre divisors. No ramification divisor, genus, differential, or
canonical-divisor conclusion is stored here.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [-instance]
  selectedFieldField
  selectedFieldConstantAlgebra
  selectedFieldRatFuncAlgebra
  selectedFieldConstantTower
  selectedFieldFunctionField
  selectedFieldRatFuncSeparable

@[reducible] noncomputable local instance (priority := 2000)
    basePowerParameterConstantAlgebra (m : ℕ) : Algebra F256 (Field m) :=
  @AffinePlace.constantAlgebra F256 (Field m) _ _ (fieldPolynomialAlgebra m)

@[reducible] noncomputable local instance (priority := 2000)
    basePowerParameterRatFuncAlgebra (m : ℕ) :
    Algebra (RatFunc F256) (Field m) :=
  fieldRatFuncAlgebra m

noncomputable local instance (priority := 2000)
    basePowerParameterFunctionField (m : ℕ) :
    _root_.FunctionField F256 (Field m) :=
  fieldFunctionField m

noncomputable local instance (priority := 2000)
    basePowerParameterSeparable (m : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (Field m) :=
  fieldRatFuncSeparable m

/-- The all-place carrier selected by the direct rational chart at recursive
level `m`. -/
abbrev BasePowerParameterPlace (m : ℕ) : Type :=
  @GlobalPlace F256 (Field m) _ _ _
    (riemannRochPolarFamilyAlgebra
      (π := fieldPolynomialAlgebra m) F256 (Field m))

/-- The actual all-place residue-degree function on the direct-chart carrier
used by the pole divisor. -/
noncomputable def basePowerParameterResidueDegree (m : ℕ) :
    BasePowerParameterPlace m → ℕ :=
  fun P => GlobalPlace.residueDegree
    (π := fieldPolynomialAlgebra m)
    (ρ := basePowerParameterRatFuncAlgebra m)
    (τ := fieldPolynomialRatFuncTower m)
    (φ := basePowerParameterFunctionField m)
    (σ := basePowerParameterSeparable m)
    (κ := riemannRochPolarFamilyAlgebra
      (π := fieldPolynomialAlgebra m) F256 (Field m)) P

/-- The actual recursive level has degree `16^m` over the base rational
function field. -/
theorem field_finrank (m : ℕ) :
    Module.finrank (RatFunc F256) (Field m) = 16 ^ m := by
  induction m with
  | zero =>
      change Module.finrank (RatFunc F256) (RatFunc F256) = 1
      simp
  | succ m ih =>
      letI : IsScalarTower (RatFunc F256) (Field m) (Field (m + 1)) :=
        IsScalarTower.of_algebraMap_eq' rfl
      calc
        Module.finrank (RatFunc F256) (Field (m + 1)) =
            Module.finrank (RatFunc F256) (Field m) *
              Module.finrank (Field m) (Field (m + 1)) :=
          (Module.finrank_mul_finrank
            (RatFunc F256) (Field m) (Field (m + 1))).symm
        _ = 16 ^ m * 16 := by rw [ih, step_finrank]
        _ = 16 ^ (m + 1) := by rw [pow_succ]

/-- The image of the concrete base parameter `X^17` in recursive level
`m`. -/
noncomputable def basePowerParameter (m : ℕ) : Field m :=
  GlobalPlace.chartVariable (k := F256) (F := Field m) ^ 17

theorem basePowerParameter_eq (m : ℕ) :
    basePowerParameter m =
      GlobalPlace.chartVariable (k := F256) (F := Field m) ^ 17 :=
  rfl

/-- The base power parameter is nonzero in every recursive level. -/
theorem basePowerParameter_ne_zero (m : ℕ) :
    basePowerParameter m ≠ 0 := by
  rw [basePowerParameter_eq]
  exact pow_ne_zero _
    (GlobalPlace.chartVariable_ne_zero (k := F256) (F := Field m))

/-- The direct chart variable's actual all-place pole divisor at recursive
level `m`, with every chart instance fixed explicitly. -/
noncomputable def chartVariablePoleDivisor (m : ℕ) :
    Divisor (BasePowerParameterPlace m) :=
  GlobalPlace.polarDivisor
    (π := fieldPolynomialAlgebra m)
    (ρ := basePowerParameterRatFuncAlgebra m)
    (τ := fieldPolynomialRatFuncTower m)
    (φ := basePowerParameterFunctionField m)
    (s := basePowerParameterSeparable m)
    (k := F256) (F := Field m)
    (GlobalPlace.chartVariable (k := F256) (F := Field m))

/-- The actual all-place pole divisor of the base power parameter. -/
noncomputable def basePowerParameterPoleDivisor (m : ℕ) :
    Divisor (BasePowerParameterPlace m) :=
  GlobalPlace.polarDivisor
    (π := fieldPolynomialAlgebra m)
    (ρ := basePowerParameterRatFuncAlgebra m)
    (τ := fieldPolynomialRatFuncTower m)
    (φ := basePowerParameterFunctionField m)
    (s := basePowerParameterSeparable m)
    (k := F256) (F := Field m) (basePowerParameter m)

private theorem order_pow (m n : ℕ) {constantAlgebra : Algebra F256 (Field m)}
    (P : @GlobalPlace F256 (Field m) _ _ _ constantAlgebra) (x : Field m) :
    P.order (x ^ n) = (n : ℤ) * P.order x := by
  unfold GlobalPlace.order
  rw [(P.valuation).map_pow, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

/-- Taking the seventeenth power multiplies the chart-variable pole divisor
by seventeen. -/
theorem polarDivisor_basePowerParameter (m : ℕ) :
    basePowerParameterPoleDivisor m =
      17 • chartVariablePoleDivisor m := by
  have hx : GlobalPlace.chartVariable (k := F256) (F := Field m) ≠ 0 :=
    GlobalPlace.chartVariable_ne_zero (k := F256) (F := Field m)
  have hxpow :
      GlobalPlace.chartVariable (k := F256) (F := Field m) ^ 17 ≠ 0 :=
    pow_ne_zero _ hx
  unfold basePowerParameterPoleDivisor chartVariablePoleDivisor
  rw [basePowerParameter_eq]
  ext P
  simp only [GlobalPlace.polarDivisor, dif_neg hxpow, dif_neg hx,
    Finsupp.sup_apply, Finsupp.neg_apply, Finsupp.zero_apply,
    GlobalPlace.principalDivisor_apply, Units.val_mk0,
    Finsupp.smul_apply, nsmul_eq_mul]
  rw [order_pow]
  by_cases horder : 0 ≤ -P.order
      (GlobalPlace.chartVariable (k := F256) (F := Field m))
  · rw [max_eq_left horder]
    rw [max_eq_left]
    · ring
    · omega
  · rw [max_eq_right (le_of_not_ge horder)]
    rw [max_eq_right]
    · simp
    · omega

/-- The base power parameter has pole degree `17 * 16^m`. -/
theorem polarDivisor_basePowerParameter_degree (m : ℕ) :
    Divisor.degree (basePowerParameterResidueDegree m)
        (basePowerParameterPoleDivisor m) =
      (17 * 16 ^ m : ℕ) := by
  rw [polarDivisor_basePowerParameter]
  calc
    Divisor.degree (basePowerParameterResidueDegree m)
        (17 • chartVariablePoleDivisor m) =
        (17 : ℤ) * Divisor.degree (basePowerParameterResidueDegree m)
          (chartVariablePoleDivisor m) := by
      have hdegree :=
        (Divisor.degreeHom (basePowerParameterResidueDegree m)).map_nsmul 17
          (chartVariablePoleDivisor m)
      simp only [Divisor.degree, nsmul_eq_mul] at hdegree ⊢
      exact hdegree
    _ = (17 : ℤ) * Module.finrank (RatFunc F256) (Field m) := by
      unfold basePowerParameterResidueDegree chartVariablePoleDivisor
      rw [GlobalPlace.polarDivisor_chartVariable_degree_eq_finrank
        (π := fieldPolynomialAlgebra m)
        (ρ := basePowerParameterRatFuncAlgebra m)
        (τ := fieldPolynomialRatFuncTower m)
        (φ := basePowerParameterFunctionField m)
        (s := basePowerParameterSeparable m)]
    _ = (17 * 16 ^ m : ℕ) := by rw [field_finrank]; norm_num

/-- For the original-family tail `Field (i + 2)`, the pole degree of `X^17`
equals `selectedLength i / 15`. This arithmetic identity does not identify
the fibre divisors of the source normal-closure family. -/
theorem polarDivisor_basePowerParameter_degree_selectedLevel (i : ℕ) :
    Divisor.degree (basePowerParameterResidueDegree (i + 2))
        (basePowerParameterPoleDivisor (i + 2)) =
      ((selectedLength i / 15 : ℕ) : ℤ) := by
  let m := i + 2
  change
    Divisor.degree (basePowerParameterResidueDegree m)
        (basePowerParameterPoleDivisor m) =
      ((selectedLength i / 15 : ℕ) : ℤ)
  calc
    Divisor.degree (basePowerParameterResidueDegree m)
        (basePowerParameterPoleDivisor m) =
        (17 * 16 ^ m : ℕ) :=
      polarDivisor_basePowerParameter_degree m
    _ = ((selectedLength i / 15 : ℕ) : ℤ) := by
      dsimp only [m]
      rw [selectedLength_eq]
      norm_cast
      omega

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
