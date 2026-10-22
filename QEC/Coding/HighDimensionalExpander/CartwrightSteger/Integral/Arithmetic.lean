import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Arithmetic.Arithmetic
import QEC.Coding.HighDimensionalExpander.Hecke.SphericalHecke
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The integral Cartwright--Steger arithmetic ring at the building place

This module constructs the two canonical realizations of
`R_T = F_q[y, 1 / (1 + y)]`: inside the rational function field and inside
the `y`-adic integer ring.  It proves that the realizations agree after
passing to the Laurent-series completion and that both maps are injective.

These are the global-to-local maps used in the arithmetic intersection
argument for the Cartwright--Steger vertex stabilizer.  In particular, no
embedding or compatibility certificate is supplied by a caller.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

/-- The canonical inclusion `R_T -> F_q(y)`. -/
noncomputable def integralArithmeticToFunctionField (P : BasePrime) :
    IntegralArithmeticRing P →+* FunctionField P :=
  IsLocalization.Away.lift
    (1 + Polynomial.X : PolynomialRing P)
    (S := IntegralArithmeticRing P)
    (g := algebraMap (PolynomialRing P) (FunctionField P)) (by
      rw [isUnit_iff_ne_zero]
      apply RatFunc.algebraMap_ne_zero
      intro h
      have := congrArg (Polynomial.eval (0 : BaseField P)) h
      simp at this)

@[simp] theorem integralArithmeticToFunctionField_algebraMap
    (P : BasePrime) (f : PolynomialRing P) :
    integralArithmeticToFunctionField P
        (algebraMap (PolynomialRing P) (IntegralArithmeticRing P) f) =
      algebraMap (PolynomialRing P) (FunctionField P) f := by
  exact IsLocalization.Away.lift_eq _ _ _

/-- The canonical `y`-adic integral realization `R_T -> F_q[[y]]`.
The denominator `1 + y` is a unit because its constant coefficient is one. -/
noncomputable def integralArithmeticToBuildingIntegerRing (P : BasePrime) :
    IntegralArithmeticRing P →+* BuildingIntegerRing P :=
  IsLocalization.Away.lift
    (1 + Polynomial.X : PolynomialRing P)
    (S := IntegralArithmeticRing P)
    (g := Polynomial.coeToPowerSeries.ringHom) (by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      simp)

@[simp] theorem integralArithmeticToBuildingIntegerRing_algebraMap
    (P : BasePrime) (f : PolynomialRing P) :
    integralArithmeticToBuildingIntegerRing P
        (algebraMap (PolynomialRing P) (IntegralArithmeticRing P) f) =
      Polynomial.coeToPowerSeries.ringHom f := by
  exact IsLocalization.Away.lift_eq _ _ _

/-- The global and integral realizations of `R_T` agree in `F_q((y))`. -/
theorem integralArithmetic_completion_compatibility (P : BasePrime) :
    (SphericalHecke.integerEmbedding (BaseField P)).comp
        (integralArithmeticToBuildingIntegerRing P) =
      (functionFieldToBuildingLocalField P).comp
        (integralArithmeticToFunctionField P) := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (1 + Polynomial.X : PolynomialRing P))
  apply RingHom.ext
  intro f
  simp only [RingHom.comp_apply,
    integralArithmeticToBuildingIntegerRing_algebraMap,
    integralArithmeticToFunctionField_algebraMap]
  exact RatFunc.coe_coe f

/-- Pointwise form of `integralArithmetic_completion_compatibility`. -/
theorem integralArithmetic_completion_compatibility_apply
    (P : BasePrime) (x : IntegralArithmeticRing P) :
    SphericalHecke.integerEmbedding (BaseField P)
        (integralArithmeticToBuildingIntegerRing P x) =
      functionFieldToBuildingLocalField P
        (integralArithmeticToFunctionField P x) := by
  exact RingHom.congr_fun (integralArithmetic_completion_compatibility P) x

/-- The global realization of `R_T` is faithful. -/
theorem integralArithmeticToFunctionField_injective (P : BasePrime) :
    Function.Injective (integralArithmeticToFunctionField P) := by
  rw [IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (1 + Polynomial.X : PolynomialRing P))
    (integralArithmeticToFunctionField P)]
  intro f g
  simp only [integralArithmeticToFunctionField_algebraMap]
  constructor
  · intro h
    simpa only [integralArithmeticToFunctionField_algebraMap] using
      congrArg (integralArithmeticToFunctionField P) h
  · intro h
    have hfg : f = g := RatFunc.algebraMap_injective (BaseField P) h
    subst g
    rfl

/-- The integral realization of `R_T` in `F_q[[y]]` is faithful. -/
theorem integralArithmeticToBuildingIntegerRing_injective (P : BasePrime) :
    Function.Injective (integralArithmeticToBuildingIntegerRing P) := by
  intro x y h
  apply integralArithmeticToFunctionField_injective P
  apply functionFieldToBuildingLocalField_injective P
  rw [← integralArithmetic_completion_compatibility_apply P x,
    ← integralArithmetic_completion_compatibility_apply P y, h]

/-- The coordinate `y` in `R_T`. -/
noncomputable def integralArithmeticY (P : BasePrime) :
    IntegralArithmeticRing P :=
  algebraMap (PolynomialRing P) (IntegralArithmeticRing P) Polynomial.X

/-- The construction-owned inverse of `1 + y` in `R_T`. -/
noncomputable def integralArithmeticOnePlusYInv (P : BasePrime) :
    IntegralArithmeticRing P :=
  IsLocalization.Away.invSelf
    (1 + Polynomial.X : PolynomialRing P)

theorem integralArithmeticOnePlusY_mul_inv (P : BasePrime) :
    (1 + integralArithmeticY P) *
        integralArithmeticOnePlusYInv P = 1 := by
  rw [integralArithmeticY, integralArithmeticOnePlusYInv]
  have hOne :
      1 + algebraMap (PolynomialRing P) (IntegralArithmeticRing P)
          Polynomial.X =
        algebraMap (PolynomialRing P) (IntegralArithmeticRing P)
          (1 + Polynomial.X) := by
    rw [map_add, map_one]
  rw [hOne]
  exact IsLocalization.Away.mul_invSelf
    (S := IntegralArithmeticRing P)
    (1 + Polynomial.X : PolynomialRing P)

theorem integralArithmeticOnePlusY_inv_mul (P : BasePrime) :
    integralArithmeticOnePlusYInv P *
        (1 + integralArithmeticY P) = 1 := by
  rw [mul_comm]
  exact integralArithmeticOnePlusY_mul_inv P

@[simp] theorem integralArithmeticToFunctionField_y (P : BasePrime) :
    integralArithmeticToFunctionField P (integralArithmeticY P) =
      RatFunc.X := by
  simp [integralArithmeticY, RatFunc.algebraMap_X]

@[simp] theorem integralArithmeticToBuildingIntegerRing_y (P : BasePrime) :
    integralArithmeticToBuildingIntegerRing P (integralArithmeticY P) =
      PowerSeries.X := by
  simp [integralArithmeticY]

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
