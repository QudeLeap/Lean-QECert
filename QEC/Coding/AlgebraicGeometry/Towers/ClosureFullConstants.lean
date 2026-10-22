import QEC.Coding.AlgebraicGeometry.Places.RationalPlaceFullConstants
import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisSelectedPlaces

/-!
# Full constants and the literal rational chart of the actual closure

An enumerated rational point proves that the constant field is precisely
F256. The polynomial chart below is the existing literal z-embedding.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

scoped instance sourceClosureFullConstants (m : ℕ) :
    IsFullConstantField F256 (SourceGaloisClosureField m) :=
  isFullConstantField_of_rationalPlace
    (sourceGaloisClosureSelectedRationalPlace m
      ⟨0, lt_of_lt_of_le (by positivity) (sourceGaloisClosureSelectedLength_lower_bound m)⟩)

scoped instance sourceClosurePolynomialAlgebra (m : ℕ) :
    Algebra (Polynomial F256) (SourceGaloisClosureField m) :=
  ((algebraMap (RatFunc F256) (SourceGaloisClosureField m)).comp
    (algebraMap (Polynomial F256) (RatFunc F256))).toAlgebra

scoped instance sourceClosurePolynomialTower (m : ℕ) :
    IsScalarTower (Polynomial F256) (RatFunc F256) (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl

theorem sourceClosureDirectConstant_eq (m : ℕ) :
    @AffinePlace.constantAlgebra F256 (SourceGaloisClosureField m) _ _
      (sourceClosurePolynomialAlgebra m) = sourceGaloisClosureConstantAlgebra m := by
  apply Algebra.algebra_ext
  intro c
  change algebraMap (RatFunc F256) (SourceGaloisClosureField m)
    (algebraMap (Polynomial F256) (RatFunc F256) (Polynomial.C c)) =
      algebraMap F256 (SourceGaloisClosureField m) c
  rw [RatFunc.algebraMap_C]
  exact (IsScalarTower.algebraMap_apply F256 (RatFunc F256) (SourceGaloisClosureField m) c).symm

scoped instance sourceClosureDirectFullConstants (m : ℕ) :
    @IsFullConstantField F256 (SourceGaloisClosureField m) _ _
      (@AffinePlace.constantAlgebra F256 (SourceGaloisClosureField m) _ _
        (sourceClosurePolynomialAlgebra m)) := by
  rw [sourceClosureDirectConstant_eq]
  exact sourceClosureFullConstants m

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
