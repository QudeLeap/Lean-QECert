import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisFunctionField

import Mathlib.FieldTheory.Relrank

/-!
# The actual F256(w) intermediate field in the source Garcia--Stichtenoth closures

Stichtenoth's ramification calculation factors the normal closure over
`F256(z)` through `F256(w)`, where `w = x₀^16 + x₀` and `z = w^15`.
This file constructs that literal intermediate field, proves its degree is
fifteen, and embeds it through the actual recursive seed field into every
normal closure.

No place, ramification index, different, divisor, genus, or canonical-divisor
formula is asserted here.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

open IntermediateField Polynomial

private theorem galoisBaseW_eq_algebraMap :
    galoisBaseW = algebraMap (Polynomial F256) (RatFunc F256)
      (Polynomial.X ^ 16 + Polynomial.X) := by
  simp [galoisBaseW, RatFunc.algebraMap_X]

/-- The literal inclusion `F256(z) ⊆ F256(w)` coming from `z = w^15`. -/
theorem galoisBaseField_le_sourceGaloisWField :
    (F256⟮galoisBaseZ⟯ : IntermediateField F256 (RatFunc F256)) ≤
      F256⟮galoisBaseW⟯ := by
  rw [IntermediateField.adjoin_simple_le_iff]
  change galoisBaseW ^ 15 ∈ F256⟮galoisBaseW⟯
  exact (F256⟮galoisBaseW⟯).pow_mem
    (IntermediateField.subset_adjoin F256 {galoisBaseW}
      (Set.mem_singleton galoisBaseW)) 15

/-- The actual intermediate field `F256(w)` regarded as an extension of
`F256(z)` inside the rational seed field. -/
abbrev SourceGaloisWField : Type :=
  IntermediateField.extendScalars galoisBaseField_le_sourceGaloisWField

private theorem galoisBaseW_ratFunc_finrank :
    Module.finrank (F256⟮galoisBaseW⟯) (RatFunc F256) = 16 := by
  have hdegree :
      (Polynomial.X ^ 16 + Polynomial.X : Polynomial F256).natDegree = 16 := by
    calc
      (Polynomial.X ^ 16 + Polynomial.X : Polynomial F256).natDegree =
          (Polynomial.X ^ 16 : Polynomial F256).natDegree :=
        Polynomial.natDegree_add_eq_left_of_natDegree_lt (by norm_num)
      _ = 16 := by norm_num
  calc
    Module.finrank (F256⟮galoisBaseW⟯) (RatFunc F256) =
        max galoisBaseW.num.natDegree galoisBaseW.denom.natDegree :=
      RatFunc.finrank_eq_max_natDegree galoisBaseW
    _ = 16 := by
      rw [galoisBaseW_eq_algebraMap, RatFunc.num_algebraMap,
        RatFunc.denom_algebraMap, hdegree]
      norm_num

/-- The intermediate rational extension `F256(w) / F256(z)` has its literal
degree `15`. -/
theorem sourceGaloisWField_finrank :
    Module.finrank GaloisBaseField SourceGaloisWField = 15 := by
  have hmul := IntermediateField.relfinrank_mul_finrank_top
    galoisBaseField_le_sourceGaloisWField
  rw [IntermediateField.relfinrank_eq_finrank_of_le
      galoisBaseField_le_sourceGaloisWField,
    galoisBaseW_ratFunc_finrank, galoisBaseField_ratFunc_finrank] at hmul
  have htarget :
      Module.finrank GaloisBaseField SourceGaloisWField * 16 = 15 * 16 := by
    norm_num
    exact hmul
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) htarget

/-- The actual rational seed embedding into normal-closure level `m`, with
the scalar field fixed to `F256(z)`.  Its variable is the seed coordinate
`x₀`, not the standard rational presentation of the base parameter `z`. -/
noncomputable def sourceGaloisSeedRatFuncToClosure (m : ℕ) :
    RatFunc F256 →ₐ[GaloisBaseField] SourceGaloisClosureField m :=
  (sourceGaloisSeedToClosure m).comp
    (IsScalarTower.toAlgHom GaloisBaseField (RatFunc F256) (SourceField m))

/-- The induced embedding of the actual intermediate field `F256(w)` into
normal-closure level `m`. -/
noncomputable def sourceGaloisWFieldToClosure (m : ℕ) :
    SourceGaloisWField →ₐ[GaloisBaseField] SourceGaloisClosureField m :=
  (sourceGaloisSeedRatFuncToClosure m).comp
    (IntermediateField.extendScalars
      galoisBaseField_le_sourceGaloisWField).val

/-- The image of the actual `F256(w)` intermediate field inside normal-closure
level `m`. -/
abbrev SourceGaloisWClosureField (m : ℕ) :
    IntermediateField GaloisBaseField (SourceGaloisClosureField m) :=
  (sourceGaloisWFieldToClosure m).fieldRange

noncomputable instance (priority := 3000) sourceGaloisWClosureFieldAlgebra (m : ℕ) :
    Algebra GaloisBaseField (SourceGaloisWClosureField m) :=
  (SourceGaloisWClosureField m).toSubalgebra.algebra'

noncomputable instance (priority := 3000) sourceGaloisWClosureFieldSMul (m : ℕ) :
    SMul GaloisBaseField (SourceGaloisWClosureField m) :=
  (sourceGaloisWClosureFieldAlgebra m).toSMul

noncomputable instance (priority := 3000) sourceGaloisWClosureFieldModule (m : ℕ) :
    Module GaloisBaseField (SourceGaloisWClosureField m) :=
  @Algebra.toModule GaloisBaseField (SourceGaloisWClosureField m) _ _
    (sourceGaloisWClosureFieldAlgebra m)

/-- Embedding the intermediate field into the closure preserves its degree
fifteen over `F256(z)`. -/
theorem sourceGaloisWClosureField_finrank (m : ℕ) :
    Module.finrank GaloisBaseField (SourceGaloisWClosureField m) = 15 := by
  let e : SourceGaloisWField ≃ₐ[GaloisBaseField] SourceGaloisWClosureField m :=
    AlgEquiv.ofInjectiveField (sourceGaloisWFieldToClosure m)
  calc
    Module.finrank GaloisBaseField (SourceGaloisWClosureField m) =
        Module.finrank GaloisBaseField SourceGaloisWField :=
      e.toLinearEquiv.finrank_eq.symm
    _ = 15 := sourceGaloisWField_finrank

private noncomputable def sourceGaloisWFieldGenerator : SourceGaloisWField :=
  ⟨galoisBaseW, by
    change galoisBaseW ∈ F256⟮galoisBaseW⟯
    exact IntermediateField.subset_adjoin F256 {galoisBaseW}
      (Set.mem_singleton galoisBaseW)⟩

/-- The literal element `w = x₀^16 + x₀` in the image intermediate field
inside normal-closure level `m`. -/
noncomputable def sourceGaloisWClosureGenerator (m : ℕ) :
    SourceGaloisWClosureField m :=
  ⟨sourceGaloisWFieldToClosure m sourceGaloisWFieldGenerator,
    ⟨sourceGaloisWFieldGenerator, rfl⟩⟩

/-- The embedded generator satisfies the source relation `w^15 = z`. -/
theorem sourceGaloisWClosureGenerator_pow_fifteen (m : ℕ) :
    ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) :
        SourceGaloisClosureField m) ^ 15 =
      algebraMap GaloisBaseField (SourceGaloisClosureField m)
        (AdjoinSimple.gen F256 galoisBaseZ) := by
  change sourceGaloisSeedRatFuncToClosure m galoisBaseW ^ 15 = _
  rw [← map_pow, ← galoisBaseZ]
  simpa using (sourceGaloisSeedRatFuncToClosure m).commutes
    (AdjoinSimple.gen F256 galoisBaseZ)

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
