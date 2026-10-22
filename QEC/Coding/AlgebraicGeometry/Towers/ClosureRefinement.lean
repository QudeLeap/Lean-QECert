import QEC.Coding.AlgebraicGeometry.Towers.ClosureConjugateChains

/-!
# The complete w-rooted normalized chain of the actual normal closure

All actual source conjugates are folded over their common `k(w)` subfield.
The terminal compositum is identified with the existing normal closure by
its defining generated-by-embeddings property, not by an extra assumption.
-/

open IntermediateField

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

attribute [local instance] sourceConstantBaseTower

/-- Every place of the constructed finite normal closure has finite
residue field, derived from its existing function-field structure. -/
scoped instance sourceClosurePlace_finite_residue (m : ℕ)
    (Q : GlobalPlace F256 (SourceGaloisClosureField m)) : Finite Q.residueField := by
  letI : Algebra (Polynomial F256) (SourceGaloisClosureField m) :=
    ((algebraMap (RatFunc F256) (SourceGaloisClosureField m)).comp
      (algebraMap (Polynomial F256) (RatFunc F256))).toAlgebra
  letI : IsScalarTower (Polynomial F256) (RatFunc F256) (SourceGaloisClosureField m) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact GlobalPlace.finite_residueField Q

/-- The source's full F9 normalized chain, on the actual finite normal
closure and at an arbitrary final place. It begins at the common `k(w)`,
includes the whole original source chain and all its conjugates, and ends
at the complete constructed closure. -/
theorem sourceClosureW_normalizedRefinement (m : ℕ)
    (Q : GlobalPlace F256 (SourceGaloisClosureField m)) :
    PlaceNormalizedRefinement (sourceClosureWBase m) Q ⊥ ⊤ := by
  classical
  let E := SourceGaloisClosureField m
  let W := sourceClosureWBase m
  let I := SourceField m →ₐ[GaloisBaseField] E
  letI : Fintype I := Fintype.ofFinite I
  have hchains (f : I) := sourceClosureConjugateW_normalized m f Q
  let D (f : I) : IntermediateField W E :=
    IntermediateField.extendScalars (hchains f).choose
  have hD (f : I) : PlaceNormalizedRefinement W Q ⊥ (D f) := (hchains f).choose_spec
  let S : IntermediateField W E := Finset.univ.sup D
  have hS := PlaceNormalizedRefinement.finset_sup Q Finset.univ D (fun f _ => hD f)
  letI : Algebra GaloisBaseField (sourceClosureWBase m) :=
    inferInstanceAs (Algebra GaloisBaseField (SourceGaloisWClosureField m))
  letI : IsScalarTower GaloisBaseField (sourceClosureWBase m) (SourceGaloisClosureField m) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hbase (b : GaloisBaseField) : algebraMap GaloisBaseField E b ∈ S := by
    rw [IsScalarTower.algebraMap_apply GaloisBaseField W E]
    exact S.algebraMap_mem (algebraMap GaloisBaseField W b)
  let Sbase : IntermediateField GaloisBaseField E := S.toSubfield.toIntermediateField hbase
  have hclosure : IntermediateField.normalClosure GaloisBaseField (SourceField m) E = ⊤ :=
    (Algebra.IsAlgebraic.isNormalClosure_iff.mp
      (inferInstance : IsNormalClosure GaloisBaseField (SourceField m) E)).2
  have hle : IntermediateField.normalClosure GaloisBaseField (SourceField m) E ≤ Sbase := by
    apply normalClosure_le_iff.mpr
    intro f z hz
    exact (show D f ≤ S from Finset.le_sup (Finset.mem_univ f)) hz
  rw [hclosure] at hle
  have htop : S = ⊤ := by
    apply top_unique
    intro z _
    exact hle (show z ∈ (⊤ : IntermediateField GaloisBaseField E) from trivial)
  change PlaceNormalizedRefinement W Q ⊥ S at hS
  rwa [htop] at hS

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
