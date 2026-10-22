/-
Affine-to-global-place bridge.

Every height-one prime of the integral closure defining `AffinePlace.carrier`
has Mathlib's normalized adic valuation on the fraction field.  The
`valuation_surjective` theorem packages that valuation into the existing
`GlobalPlace` representation.  The resulting construction supplies only the
finite-place injection associated to the selected affine chart; it does not
classify the all-place carrier or construct any place above infinity.

The constant-field algebra used for this package is the explicit composite
through the integral closure, matching the affine residue-constant map.  It
is held inside the result type rather than registered as a global instance.

-/

import QEC.Coding.AlgebraicGeometry.Places.AffinePlace
import QEC.Coding.AlgebraicGeometry.Places.GlobalPlace

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc WithZero

namespace AffinePlace

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]

/-- The constant-field map into the function field, factored through the
integral closure.  This is the scalar map used for the affine global-place
package, so it is aligned with `constantsToResidue`. -/
noncomputable def constantsToFunctionField : k →+* F :=
  (algebraMap (_root_.FunctionField.ringOfIntegers k F) F).comp
    ((algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F)).comp Polynomial.C)

/-- The canonical constant algebra for the affine chart.  It remains an
explicit definition to avoid selecting a competing `Algebra k F` globally. -/
@[reducible] noncomputable def constantAlgebra : Algebra k F :=
  (constantsToFunctionField k F).toAlgebra

/-- The affine-chart constant algebra is used only while elaborating this
bridge; it is deliberately not exported as a repository-wide instance. -/
noncomputable local instance : Algebra k F := constantAlgebra k F

/-- The normalized global-place representation of an affine height-one
prime.  Its normalization is supplied by the actual adic valuation, not
assumed as an additional field. -/
noncomputable def globalPlace (P : carrier k F) :
    @GlobalPlace k F _ _ _ (constantAlgebra k F) where
  valuation := valuation k F P
  normalized := P.valuation_surjective F

/-- The packaged global valuation is definitionally the original affine adic
valuation. -/
theorem globalPlace_valuation (P : carrier k F) :
    (globalPlace k F P).valuation = valuation k F P :=
  rfl

/-- The affine global place carries the surjectivity proof supplied by the
height-one-prime adic-valuation API. -/
theorem globalPlace_surjective (P : carrier k F) :
    Function.Surjective (globalPlace k F P).valuation :=
  (globalPlace k F P).normalized

/-- For an integral element, the packaged global order is the negative
logarithm of its genuine adic valuation. -/
theorem globalPlace_order_of_integral (P : carrier k F)
    (x : _root_.FunctionField.ringOfIntegers k F) :
    GlobalPlace.order (globalPlace k F P)
      (algebraMap (_root_.FunctionField.ringOfIntegers k F) F x) =
        -WithZero.log (P.intValuation x) := by
  change -WithZero.log
    (valuation k F P (algebraMap (_root_.FunctionField.ringOfIntegers k F) F x)) = _
  rw [valuation_algebraMap_of_integral k F P x]

/-- The global-place order convention turns the adic valuation of a nonzero
integral element into its positive prime-ideal multiplicity. -/
theorem globalPlace_order_of_integral_eq_multiplicity (P : carrier k F)
    {x : _root_.FunctionField.ringOfIntegers k F} (hx : x ≠ 0) :
    GlobalPlace.order (globalPlace k F P)
      (algebraMap (_root_.FunctionField.ringOfIntegers k F) F x) =
        (multiplicity P.asIdeal (Ideal.span {x}) : ℤ) := by
  rw [globalPlace_order_of_integral k F P x,
    P.intValuation_eq_exp_neg_multiplicity hx]
  simp

end AffinePlace

end QEC.Coding.AlgebraicGeometry
