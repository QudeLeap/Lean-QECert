import QEC.Coding.AlgebraicGeometry.Towers.RegularSourceRefinement
import QEC.Coding.AlgebraicGeometry.Towers.ClosureConjugateChains

/-!
# The actual normal closure is regular away from the two w-fibres

Every conjugate image of w has the same fifteenth power z. A unit w therefore
gives regular coordinates in every actual source conjugate. Their finite
compositum is the already constructed normal closure, by its defining property.
-/

open IntermediateField

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] sourceConstantBaseTower

/-- Every actual conjugate w-parameter is a unit wherever the chosen w is:
both fifteenth powers are the same embedded z. -/
theorem sourceClosureConjugateW_valuation_eq_one (m : ℕ)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureField m)
    (Q : GlobalPlace F256 (SourceGaloisClosureField m))
    (hw : Q.valuation (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) = 1) :
    Q.valuation (f (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)) = 1 := by
  have hp : (algebraMap (RatFunc F256) (SourceField m) galoisBaseW) ^ 15 =
      algebraMap GaloisBaseField (SourceField m) (AdjoinSimple.gen F256 galoisBaseZ) := by
    rw [← map_pow]
    rfl
  have hpow : f (algebraMap (RatFunc F256) (SourceField m) galoisBaseW) ^ 15 =
      (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) ^ 15 := by
    rw [← map_pow, hp, f.commutes, sourceGaloisWClosureGenerator_pow_fifteen]
  have h := congrArg Q.valuation hpow
  rw [map_pow, map_pow, hw, one_pow] at h
  exact (pow_eq_one_iff_of_nonneg zero_le (by norm_num : (15 : ℕ) ≠ 0)).mp h

/-- The full actual source conjugate has a regular w-rooted chain. -/
theorem sourceClosureConjugateW_regularRefinement (m : ℕ)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureField m)
    (Q : GlobalPlace F256 (SourceGaloisClosureField m))
    (hw : Q.valuation (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) = 1) :
    RegularRefinement Q (sourceClosureWBase m) (f.restrictScalars F256).fieldRange := by
  have hbase := sourceClosureConjugateW_adjoin m f
  have hwmem : f (algebraMap (RatFunc F256) (SourceField m) galoisBaseW) ∈ sourceClosureWBase m := by
    rw [← hbase]
    exact mem_adjoin_simple_self F256 _
  have hle : sourceClosureWBase m ≤ (f.restrictScalars F256).fieldRange := by
    rw [← hbase, IntermediateField.adjoin_simple_le_iff]
    exact ⟨_, rfl⟩
  have h := embeddedSourceW_regularRefinement m (f.restrictScalars F256) Q
    (sourceClosureWBase m) hwmem (sourceClosureConjugateW_valuation_eq_one m f Q hw)
  rwa [sup_eq_right.mpr hle] at h

/-- The complete closure admits a regular refinement at every place where
the actual w is a unit. Only this local condition is assumed. -/
theorem sourceClosureW_regularRefinement (m : ℕ)
    (Q : GlobalPlace F256 (SourceGaloisClosureField m))
    (hw : Q.valuation (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) = 1) :
    RegularRefinement Q (⊥ : IntermediateField (sourceClosureWBase m) (SourceGaloisClosureField m)) ⊤ := by
  classical
  let E := SourceGaloisClosureField m
  let W := sourceClosureWBase m
  let I := SourceField m →ₐ[GaloisBaseField] E
  letI : Fintype I := Fintype.ofFinite I
  let D (f : I) := (f.restrictScalars F256).fieldRange
  let S : IntermediateField F256 E := W ⊔ Finset.univ.sup D
  have hS : RegularRefinement Q W S :=
    RegularRefinement.finset_sup Q W Finset.univ D
      (fun f _ => sourceClosureConjugateW_regularRefinement m f Q hw)
  letI : Algebra GaloisBaseField (sourceClosureWBase m) :=
    inferInstanceAs (Algebra GaloisBaseField (SourceGaloisWClosureField m))
  letI : IsScalarTower GaloisBaseField (sourceClosureWBase m) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hbase (b : GaloisBaseField) : algebraMap GaloisBaseField E b ∈ S := by
    rw [IsScalarTower.algebraMap_apply GaloisBaseField W E]
    exact (show W ≤ S from le_sup_left) (algebraMap GaloisBaseField W b).property
  let Sbase : IntermediateField GaloisBaseField E := S.toSubfield.toIntermediateField hbase
  have hclosure : IntermediateField.normalClosure GaloisBaseField (SourceField m) E = ⊤ :=
    (Algebra.IsAlgebraic.isNormalClosure_iff.mp
      (inferInstance : IsNormalClosure GaloisBaseField (SourceField m) E)).2
  have hle : IntermediateField.normalClosure GaloisBaseField (SourceField m) E ≤ Sbase := by
    apply normalClosure_le_iff.mpr
    intro f z hz
    exact (show D f ≤ S from (Finset.le_sup (Finset.mem_univ f)).trans le_sup_right) hz
  rw [hclosure] at hle
  have htop : S = ⊤ := by
    apply top_unique
    intro z _
    exact hle (show z ∈ (⊤ : IntermediateField GaloisBaseField E) from trivial)
  rw [htop] at hS
  apply RegularRefinement.of_restrictScalars (F := F256) Q
  simpa only [IntermediateField.restrictScalars_bot_eq_self,
    IntermediateField.restrictScalars_top] using hS

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
