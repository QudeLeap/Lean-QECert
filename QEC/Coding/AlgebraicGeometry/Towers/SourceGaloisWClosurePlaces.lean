import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisWPlaces

/-!
# Transporting the F256(w) places into each source normal closure

The image of the actual `F256(w)` intermediate field inside a normal closure
is algebraically equivalent to `F256(w)`.  This file transports the genuine
zero and infinity places through that equivalence and verifies their orders
on the embedded generator.  These are the two base places whose upper fibres
enter the Stichtenoth ramification calculation.

No upper prime, ramification index, different, divisor, genus, or canonical
differential is asserted here.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

/-- The actual `F256(w)` field is equivalent to its image inside normal
closure level `m`. -/
noncomputable def sourceGaloisWFieldEquivClosureField (m : ℕ) :
    SourceGaloisWField ≃ₐ[GaloisBaseField] SourceGaloisWClosureField m :=
  AlgEquiv.ofInjectiveField (sourceGaloisWFieldToClosure m)

/-- The intermediate-field equivalence sends the literal generator to the
literal embedded generator. -/
theorem sourceGaloisWFieldEquivClosureField_generator (m : ℕ) :
    ((sourceGaloisWFieldEquivClosureField m sourceGaloisWFieldGenerator :
        SourceGaloisWClosureField m) : SourceGaloisClosureField m) =
      (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) := by
  rfl

private noncomputable instance sourceGaloisWFieldConstantTower :
    IsScalarTower F256 GaloisBaseField SourceGaloisWField :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable instance sourceGaloisWClosureFieldConstantTower (m : ℕ) :
    IsScalarTower F256 GaloisBaseField (SourceGaloisWClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable def sourceGaloisWFieldEquivClosureFieldOverF256 (m : ℕ) :
    SourceGaloisWField ≃ₐ[F256] SourceGaloisWClosureField m :=
  (sourceGaloisWFieldEquivClosureField m).restrictScalars F256

private theorem sourceGaloisWFieldEquivClosureFieldOverF256_generator (m : ℕ) :
    sourceGaloisWFieldEquivClosureFieldOverF256 m sourceGaloisWFieldGenerator =
      sourceGaloisWClosureGenerator m := by
  apply Subtype.ext
  exact sourceGaloisWFieldEquivClosureField_generator m

/-- The zero place transported to the actual image intermediate field in
normal-closure level `m`. -/
noncomputable def sourceGaloisWClosureZeroPlace (m : ℕ) :
    GlobalPlace F256 (SourceGaloisWClosureField m) :=
  GlobalPlace.comapAlgEquiv
    (sourceGaloisWFieldEquivClosureFieldOverF256 m).symm sourceGaloisWZeroPlace

/-- The infinity place transported to the actual image intermediate field in
normal-closure level `m`. -/
noncomputable def sourceGaloisWClosureInfinityPlace (m : ℕ) :
    GlobalPlace F256 (SourceGaloisWClosureField m) :=
  GlobalPlace.comapAlgEquiv
    (sourceGaloisWFieldEquivClosureFieldOverF256 m).symm sourceGaloisWInfinityPlace

/-- The embedded `w` has a normalized simple zero at the transported zero
place. -/
theorem sourceGaloisWClosureZeroPlace_order_generator (m : ℕ) :
    (sourceGaloisWClosureZeroPlace m).order (sourceGaloisWClosureGenerator m) = 1 := by
  rw [sourceGaloisWClosureZeroPlace, GlobalPlace.comapAlgEquiv_order,
    ← sourceGaloisWFieldEquivClosureFieldOverF256_generator,
    (sourceGaloisWFieldEquivClosureFieldOverF256 m).symm_apply_apply]
  exact sourceGaloisWZeroPlace_order_generator

/-- The embedded `w` has a normalized simple pole at the transported infinity
place. -/
theorem sourceGaloisWClosureInfinityPlace_order_generator (m : ℕ) :
    (sourceGaloisWClosureInfinityPlace m).order (sourceGaloisWClosureGenerator m) = -1 := by
  rw [sourceGaloisWClosureInfinityPlace, GlobalPlace.comapAlgEquiv_order,
    ← sourceGaloisWFieldEquivClosureFieldOverF256_generator,
    (sourceGaloisWFieldEquivClosureFieldOverF256 m).symm_apply_apply]
  exact sourceGaloisWInfinityPlace_order_generator

/-- The transported zero and infinity places remain distinct. -/
theorem sourceGaloisWClosureZeroPlace_ne_infinity (m : ℕ) :
    sourceGaloisWClosureZeroPlace m ≠ sourceGaloisWClosureInfinityPlace m := by
  intro hplaces
  have horder := congrArg
    (fun P : GlobalPlace F256 (SourceGaloisWClosureField m) =>
      P.order (sourceGaloisWClosureGenerator m)) hplaces
  change (sourceGaloisWClosureZeroPlace m).order (sourceGaloisWClosureGenerator m) =
    (sourceGaloisWClosureInfinityPlace m).order
      (sourceGaloisWClosureGenerator m) at horder
  rw [sourceGaloisWClosureZeroPlace_order_generator,
    sourceGaloisWClosureInfinityPlace_order_generator] at horder
  norm_num at horder

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
