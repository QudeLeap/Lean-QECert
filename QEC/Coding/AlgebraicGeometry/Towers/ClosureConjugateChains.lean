import QEC.Coding.AlgebraicGeometry.Towers.EmbeddedWSeed
import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisWNormal

/-!
# Every actual source conjugate has a chain over the common w-field

The ambient field is the constructed finite normal closure. Its final place
is fixed throughout. Normality of `k(w)/k(z)` identifies the lower field of
every embedded whole-source chain with the same literal intermediate field.
-/

open IntermediateField

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

local instance sourceConstantBaseTower (m : ℕ) :
    IsScalarTower F256 GaloisBaseField (SourceField m) := IsScalarTower.of_algebraMap_eq' (by
  apply RingHom.ext
  intro c
  change algebraMap F256 (SourceField m) c =
    algebraMap (RatFunc F256) (SourceField m) (algebraMap F256 (RatFunc F256) c)
  exact IsScalarTower.algebraMap_apply F256 (RatFunc F256) (SourceField m) c)

local instance wConstantBaseTower :
    IsScalarTower F256 GaloisBaseField SourceGaloisWField := IsScalarTower.of_algebraMap_eq' rfl

/-- The common `k(w)` field, inside the actual finite closure and with its
constant-field scalar convention exposed. -/
abbrev sourceClosureWBase (m : ℕ) : IntermediateField F256 (SourceGaloisClosureField m) :=
  (SourceGaloisWClosureField m).restrictScalars F256

scoped instance sourceClosureWBase_finite (m : ℕ) :
    FiniteDimensional (sourceClosureWBase m) (SourceGaloisClosureField m) :=
  inferInstanceAs (FiniteDimensional (SourceGaloisWClosureField m) (SourceGaloisClosureField m))

scoped instance sourceClosureWBase_separable (m : ℕ) :
    Algebra.IsSeparable (sourceClosureWBase m) (SourceGaloisClosureField m) :=
  inferInstanceAs (Algebra.IsSeparable (SourceGaloisWClosureField m) (SourceGaloisClosureField m))

/-- The existing conjugate-image theorem, now on the finite closure carrier
where the final place and different will actually be measured. -/
theorem sourceClosureConjugateW_fieldRange (m : ℕ)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureField m) :
    (f.comp (sourceGaloisWFieldToSource m)).fieldRange = SourceGaloisWClosureField m := by
  let v := (IntermediateField.normalClosure GaloisBaseField (SourceField m)
    SourceGaloisClosureAmbient).val
  apply IntermediateField.map_injective v
  change (f.comp (sourceGaloisWFieldToSource m)).fieldRange.map v =
    (sourceGaloisWFieldToClosure m).fieldRange.map v
  rw [AlgHom.map_fieldRange, AlgHom.map_fieldRange]
  exact (sourceGaloisWConjugateRestriction_fieldRange_eq m (v.comp f)).trans
    (sourceGaloisWConjugateRestriction_fieldRange_eq m (v.comp (sourceGaloisSeedToClosure m))).symm

/-- The initial rational parameter of each actual conjugate generates
exactly the common `k(w)` subfield; the conjugate need not fix `w` itself. -/
theorem sourceClosureConjugateW_adjoin (m : ℕ)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureField m) :
    F256⟮f (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)⟯ = sourceClosureWBase m := by
  let g := f.comp (sourceGaloisWFieldToSource m)
  have hgen : F256⟮sourceGaloisWFieldGenerator⟯ =
      (⊤ : IntermediateField F256 SourceGaloisWField) :=
    adjoin_simple_gen_eq_top (F := F256) galoisBaseW
  have h := congrArg (fun K : IntermediateField F256 SourceGaloisWField =>
    K.map (g.restrictScalars F256)) hgen
  rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map] at h
  change F256⟮f (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)⟯ =
    (g.fieldRange).restrictScalars F256 at h
  exact h.trans (congrArg (IntermediateField.restrictScalars F256)
    (sourceClosureConjugateW_fieldRange m f))

/-- Every actual source conjugate, on the actual finite closure carrier,
admits the full w-rooted normalized refinement at every final place.
No normalized chain, different formula, or degree is assumed. -/
theorem sourceClosureConjugateW_normalized (m : ℕ)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureField m)
    (Q : GlobalPlace F256 (SourceGaloisClosureField m)) :
    PlaceNormalizedExtension Q (sourceClosureWBase m) (f.restrictScalars F256).fieldRange := by
  let E := SourceGaloisClosureField m
  letI : Algebra (SourceField m) E := f.toRingHom.toAlgebra
  letI : IsScalarTower GaloisBaseField (SourceField m) E :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  letI : IsScalarTower F256 (SourceField m) E :=
    IsScalarTower.of_algebraMap_eq' (f.restrictScalars F256).comp_algebraMap.symm
  letI : FiniteDimensional (SourceField m) E :=
    Module.Finite.of_restrictScalars_finite GaloisBaseField (SourceField m) E
  letI : Algebra.IsSeparable (SourceField m) E :=
    Algebra.isSeparable_tower_top_of_isSeparable GaloisBaseField (SourceField m) E
  letI : Algebra (Polynomial F256) E :=
    ((algebraMap (RatFunc F256) E).comp (algebraMap (Polynomial F256) (RatFunc F256))).toAlgebra
  letI : IsScalarTower (Polynomial F256) (RatFunc F256) E := IsScalarTower.of_algebraMap_eq' rfl
  letI : Finite Q.residueField := GlobalPlace.finite_residueField Q
  have h := embeddedSourceW_normalized m Q
  have hbase := sourceClosureConjugateW_adjoin m f
  change F256⟮algebraMap (SourceField m) E
    (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)⟯ = sourceClosureWBase m at hbase
  exact PlaceNormalizedExtension.congr_base Q hbase h

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
