import QEC.Coding.AlgebraicGeometry.Towers.SourceNormalClosure

/-!
# Function-field structure on the source-facing F256 normal closures

The corrected source-recursion normal closure is finite and Galois over the
literal base `F256((X^16+X)^15)`.  This file transports that construction
across the already proved identification of the base with `RatFunc F256`.

It supplies only the resulting function-field and Galois interfaces, together
with the proved seed-degree lower bound.  No splitting, ramification,
different, divisor, genus, or asymptotic conclusion is inferred here.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

private noncomputable def sourceGaloisClosureConstantMap (m : ℕ) :
    F256 →+* SourceGaloisClosureField m :=
  (algebraMap GaloisBaseField (SourceGaloisClosureField m)).comp
    (algebraMap F256 GaloisBaseField)

noncomputable instance sourceGaloisClosureConstantAlgebra (m : ℕ) :
    Algebra F256 (SourceGaloisClosureField m) :=
  (sourceGaloisClosureConstantMap m).toAlgebra

noncomputable instance (priority := 2000) sourceGaloisClosureConstantSMul
    (m : ℕ) : SMul F256 (SourceGaloisClosureField m) :=
  (sourceGaloisClosureConstantAlgebra m).toSMul

noncomputable instance (priority := 2000) sourceGaloisClosureConstantModule
    (m : ℕ) : Module F256 (SourceGaloisClosureField m) :=
  @Algebra.toModule F256 (SourceGaloisClosureField m) _ _
    (sourceGaloisClosureConstantAlgebra m)

noncomputable instance sourceGaloisClosureConstantBaseScalarTower (m : ℕ) :
    IsScalarTower F256 GaloisBaseField (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The rational-function embedding obtained from the actual fixed-base
embedding into the corrected source normal closure. -/
noncomputable def sourceGaloisClosureRatFuncEmbedding (m : ℕ) :
    RatFunc F256 →ₐ[F256] SourceGaloisClosureField m :=
  (IsScalarTower.toAlgHom F256 GaloisBaseField
    (SourceGaloisClosureField m)).comp
      galoisBaseFieldEquivRatFunc.toAlgHom

noncomputable instance sourceGaloisClosureRatFuncAlgebra (m : ℕ) :
    Algebra (RatFunc F256) (SourceGaloisClosureField m) :=
  (sourceGaloisClosureRatFuncEmbedding m).toRingHom.toAlgebra

noncomputable instance (priority := 2000) sourceGaloisClosureRatFuncSMul
    (m : ℕ) : SMul (RatFunc F256) (SourceGaloisClosureField m) :=
  (sourceGaloisClosureRatFuncAlgebra m).toSMul

noncomputable instance (priority := 2000) sourceGaloisClosureRatFuncModule
    (m : ℕ) : Module (RatFunc F256) (SourceGaloisClosureField m) :=
  @Algebra.toModule (RatFunc F256) (SourceGaloisClosureField m) _ _
    (sourceGaloisClosureRatFuncAlgebra m)

noncomputable instance sourceGaloisClosureRatFuncScalarTower (m : ℕ) :
    IsScalarTower F256 (RatFunc F256) (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq'
    (sourceGaloisClosureRatFuncEmbedding m).comp_algebraMap.symm

private theorem sourceGaloisClosureBaseRatFunc_compatibility (m : ℕ) :
    (algebraMap (RatFunc F256) (SourceGaloisClosureField m)).comp
        galoisBaseFieldEquivRatFunc.symm.toRingEquiv.toRingHom =
      algebraMap GaloisBaseField (SourceGaloisClosureField m) := by
  ext x
  simp [sourceGaloisClosureRatFuncEmbedding,
    RingHom.algebraMap_toAlgebra]

/-- The corrected source normal closure is an actual finite function field
over `F256`. -/
noncomputable instance sourceGaloisClosureFunctionField (m : ℕ) :
    FunctionField F256 (SourceGaloisClosureField m) := by
  exact @Module.Finite.of_equiv_equiv
    GaloisBaseField (SourceGaloisClosureField m)
    (RatFunc F256) (SourceGaloisClosureField m)
    _ _ _ _ (sourceGaloisClosureFieldAlgebra m)
    (sourceGaloisClosureRatFuncAlgebra m)
    galoisBaseFieldEquivRatFunc.symm.toRingEquiv
    (RingEquiv.refl (SourceGaloisClosureField m))
    (sourceGaloisClosureBaseRatFunc_compatibility m)
    (sourceGaloisClosureFieldFiniteDimensional m)

/-- Galoisness over the fixed rational base, transported to the standard
`RatFunc F256` presentation. -/
noncomputable instance sourceGaloisClosureRatFuncIsGalois (m : ℕ) :
    IsGalois (RatFunc F256) (SourceGaloisClosureField m) := by
  exact IsGalois.of_equiv_equiv
    (F := GaloisBaseField) («E» := SourceGaloisClosureField m)
    (f := galoisBaseFieldEquivRatFunc.symm.toRingEquiv)
    (g := RingEquiv.refl (SourceGaloisClosureField m))
    (sourceGaloisClosureBaseRatFunc_compatibility m)

/-- The fixed-base and rational-function presentations have the same closure
degree. -/
theorem sourceGaloisClosureField_ratFunc_finrank (m : ℕ) :
    Module.finrank (RatFunc F256) (SourceGaloisClosureField m) =
      Module.finrank GaloisBaseField (SourceGaloisClosureField m) := by
  exact Algebra.finrank_eq_of_equiv_equiv
    galoisBaseFieldEquivRatFunc.toRingEquiv
    (RingEquiv.refl (SourceGaloisClosureField m))
    (by
      ext x
      simp [sourceGaloisClosureRatFuncEmbedding,
        RingHom.algebraMap_toAlgebra])

/-- The corrected seed-degree growth remains a lower bound in the standard
function-field presentation. -/
theorem sourceGaloisClosureField_ratFunc_finrank_lower_bound (m : ℕ) :
    240 * 16 ^ m ≤
      Module.finrank (RatFunc F256) (SourceGaloisClosureField m) := by
  rw [sourceGaloisClosureField_ratFunc_finrank]
  exact sourceGaloisClosureField_finrank_lower_bound m

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
