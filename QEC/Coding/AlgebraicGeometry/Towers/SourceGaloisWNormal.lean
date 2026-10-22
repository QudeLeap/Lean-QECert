import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisWPlaces
import QEC.Coding.AlgebraicGeometry.Towers.SourceNormalClosureFiniteCompositum

import Mathlib.FieldTheory.KummerExtension

/-!
# The common F256(w) field in every source conjugate

The source normal-closure argument composes conjugate copies of the recursive
field over the single intermediate rational field `F256(w)`.  This file proves
that `F256(w) / F256(z)` is the literal degree-fifteen Kummer extension: the
base contains a primitive fifteenth root of unity, `w ^ 15 = z`, and `w`
generates the extension.  It follows that every conjugate source embedding
has the same image of `F256(w)` in the fixed ambient separable closure.

No quadratic refinement, ramification index, different, divisor, genus, or
asymptotic conclusion is asserted here.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

open IntermediateField Polynomial

private theorem f256_has_primitive_root_two_hundred_fifty_five :
    ∃ zeta : F256, IsPrimitiveRoot zeta 255 := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := F256ˣ)
  refine ⟨(u : F256), ?_⟩
  rw [IsPrimitiveRoot.iff_orderOf, orderOf_units, hu,
    Nat.card_eq_fintype_card, Fintype.card_units, QEC.Coding.f256_card]

/-- The fixed rational base `F256(z)` contains a primitive fifteenth root of
unity, inherited from the constant field `F256`. -/
theorem sourceGaloisBaseField_primitiveRoots_fifteen_nonempty :
    (primitiveRoots 15 GaloisBaseField).Nonempty := by
  obtain ⟨zeta, hzeta⟩ := f256_has_primitive_root_two_hundred_fifty_five
  have hzeta15 : IsPrimitiveRoot (zeta ^ 17) 15 :=
    hzeta.pow (by norm_num : 0 < 255) (by norm_num : 255 = 17 * 15)
  let zetaBase : GaloisBaseField :=
    algebraMap F256 GaloisBaseField (zeta ^ 17)
  refine ⟨zetaBase, (mem_primitiveRoots (by norm_num : 0 < 15)).2 ?_⟩
  exact hzeta15.map_of_injective (algebraMap F256 GaloisBaseField).injective

private theorem sourceGaloisWField_adjoin_generator_over_constants_eq_top :
    F256⟮sourceGaloisWFieldGenerator⟯ = ⊤ := by
  let e := sourceGaloisWFieldEquivRatFunc
  calc
    F256⟮sourceGaloisWFieldGenerator⟯ =
        (F256⟮(RatFunc.X : RatFunc F256)⟯).map e.toAlgHom := by
      rw [← sourceGaloisWFieldEquivRatFunc_X,
        IntermediateField.adjoin_map]
      simp only [Set.image_singleton]
      change F256⟮sourceGaloisWFieldEquivRatFunc RatFunc.X⟯ =
        F256⟮sourceGaloisWFieldEquivRatFunc RatFunc.X⟯
      rfl
    _ = (⊤ : IntermediateField F256 (RatFunc F256)).map e.toAlgHom := by
      rw [RatFunc.adjoin_X]
    _ = e.toAlgHom.fieldRange :=
      (AlgHom.fieldRange_eq_map e.toAlgHom).symm
    _ = ⊤ := AlgHom.fieldRange_eq_top.mpr e.surjective

/-- The literal generator `w` also generates `F256(w)` over the larger base
`F256(z)`. -/
theorem sourceGaloisWField_adjoin_generator_eq_top :
    GaloisBaseField⟮sourceGaloisWFieldGenerator⟯ = ⊤ :=
  IntermediateField.adjoin_eq_top_of_adjoin_eq_top F256
    sourceGaloisWField_adjoin_generator_over_constants_eq_top

private theorem sourceGaloisWFieldGenerator_pow_fifteen :
    sourceGaloisWFieldGenerator ^ 15 =
      algebraMap GaloisBaseField SourceGaloisWField
        (AdjoinSimple.gen F256 galoisBaseZ) := by
  apply Subtype.ext
  change galoisBaseW ^ 15 = galoisBaseZ
  rfl

private theorem sourceGaloisWField_isGalois_and_isCyclic :
    IsGalois GaloisBaseField SourceGaloisWField ∧
      IsCyclic Gal(SourceGaloisWField / GaloisBaseField) := by
  let z : GaloisBaseField := AdjoinSimple.gen F256 galoisBaseZ
  have hpow : sourceGaloisWFieldGenerator ^
        Module.finrank GaloisBaseField SourceGaloisWField =
      algebraMap GaloisBaseField SourceGaloisWField z := by
    rw [sourceGaloisWField_finrank]
    exact sourceGaloisWFieldGenerator_pow_fifteen
  have hirreducible : Irreducible
      (Polynomial.X ^ Module.finrank GaloisBaseField SourceGaloisWField -
        Polynomial.C z) :=
    irreducible_X_pow_sub_C_of_root_adjoin_eq_top hpow
      sourceGaloisWField_adjoin_generator_eq_top
  have hroots :
      (primitiveRoots (Module.finrank GaloisBaseField SourceGaloisWField)
        GaloisBaseField).Nonempty := by
    rw [sourceGaloisWField_finrank]
    exact sourceGaloisBaseField_primitiveRoots_fifteen_nonempty
  letI : IsSplittingField GaloisBaseField SourceGaloisWField
      (Polynomial.X ^ Module.finrank GaloisBaseField SourceGaloisWField -
        Polynomial.C z) :=
    isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top
      hroots hpow
        sourceGaloisWField_adjoin_generator_eq_top
  have hne : NeZero (Module.finrank GaloisBaseField SourceGaloisWField) :=
    ⟨by rw [sourceGaloisWField_finrank]; norm_num⟩
  letI := hne
  exact ⟨
    isGalois_of_isSplittingField_X_pow_sub_C
      hroots hirreducible
        SourceGaloisWField,
    isCyclic_of_isSplittingField_X_pow_sub_C
      hroots hirreducible
        SourceGaloisWField⟩

noncomputable instance sourceGaloisWFieldIsGalois :
    IsGalois GaloisBaseField SourceGaloisWField :=
  sourceGaloisWField_isGalois_and_isCyclic.1

noncomputable instance sourceGaloisWFieldAutIsCyclic :
    IsCyclic Gal(SourceGaloisWField / GaloisBaseField) :=
  sourceGaloisWField_isGalois_and_isCyclic.2

/-- The literal intermediate field `F256(w)` embedded into source level `m`.
-/
noncomputable def sourceGaloisWFieldToSource (m : ℕ) :
    SourceGaloisWField →ₐ[GaloisBaseField] SourceField m :=
  (IsScalarTower.toAlgHom GaloisBaseField (RatFunc F256) (SourceField m)).comp
    (IntermediateField.extendScalars
      galoisBaseField_le_sourceGaloisWField).val

private noncomputable def sourceGaloisWFieldToAmbient (m : ℕ) :
    SourceGaloisWField →ₐ[GaloisBaseField] SourceGaloisClosureAmbient :=
  (sourceGaloisSeedSeparableEmbedding m).comp
    (sourceGaloisWFieldToSource m)

/-- The chosen image of `F256(w)` in the fixed ambient separable closure.
The next theorem proves that the image is independent of the source
conjugate embedding. -/
abbrev SourceGaloisWAmbientField (m : ℕ) :
    IntermediateField GaloisBaseField SourceGaloisClosureAmbient :=
  (sourceGaloisWFieldToAmbient m).fieldRange

noncomputable instance (priority := 3000)
    sourceGaloisWAmbientFieldAlgebra (m : ℕ) :
    Algebra GaloisBaseField (SourceGaloisWAmbientField m) :=
  (SourceGaloisWAmbientField m).toSubalgebra.algebra'

noncomputable instance (priority := 3000)
    sourceGaloisWAmbientFieldSMul (m : ℕ) :
    SMul GaloisBaseField (SourceGaloisWAmbientField m) :=
  (sourceGaloisWAmbientFieldAlgebra m).toSMul

noncomputable instance (priority := 3000)
    sourceGaloisWAmbientFieldModule (m : ℕ) :
    Module GaloisBaseField (SourceGaloisWAmbientField m) :=
  @Algebra.toModule GaloisBaseField (SourceGaloisWAmbientField m) _ _
    (sourceGaloisWAmbientFieldAlgebra m)

private noncomputable def sourceGaloisWFieldEquivAmbientField (m : ℕ) :
    SourceGaloisWField ≃ₐ[GaloisBaseField] SourceGaloisWAmbientField m :=
  AlgEquiv.ofInjectiveField (sourceGaloisWFieldToAmbient m)

noncomputable instance sourceGaloisWAmbientFieldIsGalois (m : ℕ) :
    IsGalois GaloisBaseField (SourceGaloisWAmbientField m) :=
  IsGalois.of_algEquiv (sourceGaloisWFieldEquivAmbientField m)

/-- Every fixed-base embedding of source level `m` sends its literal
`F256(w)` subfield onto the same ambient intermediate field. -/
theorem sourceGaloisWConjugateRestriction_fieldRange_eq (m : ℕ)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureAmbient) :
    (f.comp (sourceGaloisWFieldToSource m)).fieldRange =
      SourceGaloisWAmbientField m := by
  let g : SourceGaloisWField →ₐ[GaloisBaseField]
      SourceGaloisClosureAmbient :=
    f.comp (sourceGaloisWFieldToSource m)
  let e := sourceGaloisWFieldEquivAmbientField m
  let g' : SourceGaloisWAmbientField m →ₐ[GaloisBaseField]
      SourceGaloisClosureAmbient := g.comp e.symm.toAlgHom
  have hnormal : g'.fieldRange = SourceGaloisWAmbientField m :=
    AlgHom.fieldRange_of_normal g'
  have heTop : e.symm.toAlgHom.fieldRange = ⊤ :=
    AlgHom.fieldRange_eq_top.mpr e.symm.surjective
  have hrange : g'.fieldRange = g.fieldRange := by
    calc
      g'.fieldRange = e.symm.toAlgHom.fieldRange.map g :=
        (AlgHom.map_fieldRange e.symm.toAlgHom g).symm
      _ = (⊤ : IntermediateField GaloisBaseField
          SourceGaloisWField).map g := by rw [heTop]
      _ = g.fieldRange := (AlgHom.fieldRange_eq_map g).symm
  exact hrange.symm.trans hnormal

/-- Consequently, the common ambient `F256(w)` field is contained in every
actual conjugate source field range used in the finite normal-closure
compositum. -/
theorem sourceGaloisWAmbientField_le_conjugate_fieldRange (m : ℕ)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureAmbient) :
    SourceGaloisWAmbientField m ≤ f.fieldRange := by
  rw [← sourceGaloisWConjugateRestriction_fieldRange_eq m f]
  intro x hx
  rw [AlgHom.mem_fieldRange] at hx ⊢
  obtain ⟨w, rfl⟩ := hx
  exact ⟨sourceGaloisWFieldToSource m w, rfl⟩

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
