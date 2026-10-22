import QEC.Coding.AlgebraicGeometry.Towers.SourceRecursion
import QEC.Coding.AlgebraicGeometry.Towers.GaloisSeedSeparable

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.SeparableClosure

/-!
# Normal closures of the source-facing F256 Garcia--Stichtenoth levels

The fixed rational base is `F256((X^16+X)^15)`.  Replacing that generator by
the source coordinate `u_0 = (X^16+X)^15 + 1` does not change the generated
intermediate field.  This file therefore embeds each corrected source-recursion
level into one absolute separable closure of the already constructed
`GaloisBaseField`, and takes its actual intermediate-field normal closure.

Only finiteness, separability, normality, the literal seed inclusion, and its
degree lower bound are proved here.  No ramification, different, place count,
divisor, genus, or asymptotic conclusion follows merely from the normal-closure
construction.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

/-- The inclusion of the fixed rational base into source-recursion level `m`.
-/
noncomputable def sourceGaloisBaseFieldEmbedding (m : ℕ) :
    GaloisBaseField →ₐ[F256] SourceField m :=
  (IsScalarTower.toAlgHom F256 (RatFunc F256) (SourceField m)).comp
    (IntermediateField.adjoin F256
      ({galoisBaseZ} : Set (RatFunc F256))).val

noncomputable instance sourceGaloisBaseFieldSeedFiniteDimensional (m : ℕ) :
    FiniteDimensional GaloisBaseField (SourceField m) :=
  FiniteDimensional.trans GaloisBaseField (RatFunc F256) (SourceField m)

/-- The corrected source seed has degree `240 * 16^m` over the fixed base. -/
theorem sourceGaloisBaseField_seed_finrank (m : ℕ) :
    Module.finrank GaloisBaseField (SourceField m) = 240 * 16 ^ m := by
  calc
    Module.finrank GaloisBaseField (SourceField m) =
        Module.finrank GaloisBaseField (RatFunc F256) *
          Module.finrank (RatFunc F256) (SourceField m) :=
      (Module.finrank_mul_finrank GaloisBaseField (RatFunc F256)
        (SourceField m)).symm
    _ = 240 * 16 ^ m := by
      rw [galoisBaseField_ratFunc_finrank, sourceField_finrank]

noncomputable instance sourceGaloisBaseFieldSeedSeparable (m : ℕ) :
    Algebra.IsSeparable GaloisBaseField (SourceField m) :=
  Algebra.IsSeparable.trans GaloisBaseField (RatFunc F256) (SourceField m)

/-- One absolute separable closure of the fixed rational base, used for every
source-facing finite level. -/
abbrev SourceGaloisClosureAmbient : Type :=
  SeparableClosure GaloisBaseField

noncomputable instance sourceGaloisClosureAmbientAlgebra :
    Algebra GaloisBaseField SourceGaloisClosureAmbient :=
  (separableClosure GaloisBaseField
    (AlgebraicClosure GaloisBaseField)).toSubalgebra.algebra'

noncomputable instance (priority := 2000) sourceGaloisClosureAmbientSMul :
    SMul GaloisBaseField SourceGaloisClosureAmbient :=
  sourceGaloisClosureAmbientAlgebra.toSMul

noncomputable instance (priority := 2000) sourceGaloisClosureAmbientModule :
    Module GaloisBaseField SourceGaloisClosureAmbient :=
  @Algebra.toModule GaloisBaseField SourceGaloisClosureAmbient _ _
    sourceGaloisClosureAmbientAlgebra

/-- The actual separable embedding of source level `m` into the fixed ambient
separable closure. -/
noncomputable def sourceGaloisSeedSeparableEmbedding (m : ℕ) :
    SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureAmbient :=
  IsSepClosed.lift

noncomputable instance sourceGaloisSeedAmbientEmbeddingNonempty (m : ℕ) :
    Nonempty (SourceField m →ₐ[GaloisBaseField]
      SourceGaloisClosureAmbient) :=
  ⟨sourceGaloisSeedSeparableEmbedding m⟩

noncomputable instance sourceGaloisSeedAmbientAlgebra (m : ℕ) :
    Algebra (SourceField m) SourceGaloisClosureAmbient :=
  (sourceGaloisSeedSeparableEmbedding m).toRingHom.toAlgebra

noncomputable instance sourceGaloisSeedAmbientScalarTower (m : ℕ) :
    IsScalarTower GaloisBaseField (SourceField m)
      SourceGaloisClosureAmbient :=
  IsScalarTower.of_algebraMap_eq'
    (sourceGaloisSeedSeparableEmbedding m).comp_algebraMap.symm

/-- The actual normal closure of corrected source level `m` over the fixed
rational base. -/
abbrev SourceGaloisClosureField (m : ℕ) : Type :=
  IntermediateField.normalClosure GaloisBaseField (SourceField m)
    SourceGaloisClosureAmbient

noncomputable instance sourceGaloisClosureFieldAlgebra (m : ℕ) :
    Algebra GaloisBaseField (SourceGaloisClosureField m) :=
  (IntermediateField.normalClosure GaloisBaseField (SourceField m)
    SourceGaloisClosureAmbient).toSubalgebra.algebra'

noncomputable instance (priority := 2000) sourceGaloisClosureFieldSMul (m : ℕ) :
    SMul GaloisBaseField (SourceGaloisClosureField m) :=
  (sourceGaloisClosureFieldAlgebra m).toSMul

noncomputable instance (priority := 2000) sourceGaloisClosureFieldModule (m : ℕ) :
    Module GaloisBaseField (SourceGaloisClosureField m) :=
  @Algebra.toModule GaloisBaseField (SourceGaloisClosureField m) _ _
    (sourceGaloisClosureFieldAlgebra m)

noncomputable instance sourceGaloisClosureFieldFiniteDimensional (m : ℕ) :
    FiniteDimensional GaloisBaseField (SourceGaloisClosureField m) :=
  normalClosure.is_finiteDimensional GaloisBaseField (SourceField m)
    SourceGaloisClosureAmbient

noncomputable instance sourceGaloisClosureFieldIsNormalClosure (m : ℕ) :
    IsNormalClosure GaloisBaseField (SourceField m)
      (SourceGaloisClosureField m) :=
  isNormalClosure_normalClosure GaloisBaseField (SourceField m)
    SourceGaloisClosureAmbient

noncomputable instance sourceGaloisClosureFieldIsGalois (m : ℕ) :
    IsGalois GaloisBaseField (SourceGaloisClosureField m) :=
  IsGalois.normalClosure GaloisBaseField (SourceField m)
    SourceGaloisClosureAmbient

/-- The literal corrected-seed inclusion into its constructed normal closure.
-/
noncomputable def sourceGaloisSeedToClosure (m : ℕ) :
    SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureField m :=
  IsScalarTower.toAlgHom GaloisBaseField (SourceField m)
    (SourceGaloisClosureField m)

/-- The actual normal-closure degree dominates the proved corrected-seed
degree. -/
theorem sourceGaloisClosureField_finrank_lower_bound (m : ℕ) :
    240 * 16 ^ m ≤
      Module.finrank GaloisBaseField (SourceGaloisClosureField m) := by
  rw [← sourceGaloisBaseField_seed_finrank m]
  exact LinearMap.finrank_le_finrank_of_injective
    (f := (sourceGaloisSeedToClosure m).toLinearMap)
    (sourceGaloisSeedToClosure m).injective

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
