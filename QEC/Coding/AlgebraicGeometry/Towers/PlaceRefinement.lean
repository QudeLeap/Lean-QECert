import QEC.Coding.AlgebraicGeometry.Towers.AmbientPlaceModels
import QEC.Coding.AlgebraicGeometry.Towers.RefinementBaseTransport
import QEC.Coding.AlgebraicGeometry.Towers.BasicProjectionRefinement

/-!
# Literal normalized chains under one ambient place

Each base uses the concrete restricted valuation ring and actual height-one
centre constructed in `AmbientPlaceModels`. Changing a coordinate-window
base preserves the literal fields and normalized chain. A compositum square
can therefore be returned over either of its two upper base fields.
-/

open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

variable {E : Type*} [_root_.Field E] [Algebra F256 E]

/-- The existing literal normalized-chain predicate on the concrete model
selected by the given ambient place. No new output data is supplied. -/
abbrev PlaceNormalizedRefinement
    (F : Type*) [_root_.Field F] [Algebra F256 F] [Algebra F E]
    [IsScalarTower F256 F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (Q : GlobalPlace F256 E) (J L : IntermediateField F E) : Prop :=
  NormalizedRefinement (AmbientPlaceModels.baseRing F Q) F E
    (AmbientPlaceModels.prime F Q) J L

variable (F K : Type*) [_root_.Field F] [_root_.Field K]
    [Algebra F256 F] [Algebra F256 K] [Algebra F K] [Algebra K E] [Algebra F E]
    [IsScalarTower F K E] [IsScalarTower F256 F E] [IsScalarTower F256 K E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (Q : GlobalPlace F256 E)

/-- Exact change of the initial coordinate-window base, using the same
ambient place. The intermediate orders are derived from its actual centres. -/
theorem PlaceNormalizedRefinement.restrictScalars_iff
    {J L : IntermediateField K E} :
    PlaceNormalizedRefinement K Q J L ↔
      PlaceNormalizedRefinement F Q (J.restrictScalars F) (L.restrictScalars F) := by
  let A := AmbientPlaceModels.baseRing F Q
  let B := AmbientPlaceModels.baseRing K Q
  let QA := AmbientPlaceModels.prime F Q
  let QB := AmbientPlaceModels.prime K Q
  have hupper : (heightOnePlace (k := F256) (K := E) QA).order =
      (heightOnePlace (k := F256) (K := E) QB).order :=
    (AmbientPlaceModels.prime_order F Q).trans (AmbientPlaceModels.prime_order K Q).symm
  exact ⟨fun h => h.restrictScalars_of_common_ambient_order A B F K E QA QB hupper,
    fun h => h.of_restrictScalars_of_common_ambient_order A B F K E QA QB hupper⟩

end

noncomputable section

variable {F E : Type*} [_root_.Field F] [_root_.Field E]
    [Algebra F256 F] [Algebra F256 E] [Algebra F E] [IsScalarTower F256 F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (Q : GlobalPlace F256 E)

scoped instance intermediateBase_separable (L : IntermediateField F E) :
    Algebra.IsSeparable L E := Algebra.isSeparable_tower_top_of_isSeparable F L E

scoped instance intermediateBase_constantTower (L : IntermediateField F E) :
    IsScalarTower F256 L E := IsScalarTower.of_algebraMap_eq' rfl

/-- Sweep the finite quadratic grid at the actual ambient place. Residue
finiteness at its base is derived from the ambient residue field. -/
theorem PlaceNormalizedRefinement.compositum
    [Finite Q.residueField] {J L M : IntermediateField F E}
    (hL : PlaceNormalizedRefinement F Q J L)
    (hM : PlaceNormalizedRefinement F Q J M) :
    PlaceNormalizedRefinement F Q L (L ⊔ M) ∧
      PlaceNormalizedRefinement F Q M (L ⊔ M) := by
  letI : Finite (IsLocalRing.ResidueField (AmbientPlaceModels.baseRing F Q)) :=
    AmbientPlaceModels.baseResidueFieldFinite F Q
  exact NormalizedRefinement.compositum (AmbientPlaceModels.baseRing F Q) F E
    (AmbientPlaceModels.prime F Q) hL hM

/-- One complete pyramid square, returned over its actual left upper base
field. This permits the next square to have a different bottom field. -/
theorem PlaceNormalizedRefinement.compositum_rebase_left
    [Finite Q.residueField] {L M : IntermediateField F E}
    (hL : PlaceNormalizedRefinement F Q ⊥ L)
    (hM : PlaceNormalizedRefinement F Q ⊥ M) :
    PlaceNormalizedRefinement L Q ⊥ (IntermediateField.extendScalars
      (show L ≤ L ⊔ M from le_sup_left)) := by
  have h := (PlaceNormalizedRefinement.compositum Q hL hM).1
  apply (PlaceNormalizedRefinement.restrictScalars_iff F L Q).mpr
  simpa only [IntermediateField.restrictScalars_bot_eq_self,
    IntermediateField.extendScalars_restrictScalars] using h

/-- A finite family of whole normalized chains over the same original
base gives a normalized chain to its literal compositum. -/
theorem PlaceNormalizedRefinement.finset_sup
    [Finite Q.residueField] {ι : Type*} (s : Finset ι)
    (L : ι → IntermediateField F E)
    (h : ∀ i ∈ s, PlaceNormalizedRefinement F Q ⊥ (L i)) :
    PlaceNormalizedRefinement F Q ⊥ (s.sup L) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sup_empty]
  | @insert i s hi ih =>
      rw [Finset.sup_insert]
      have hi := h i (Finset.mem_insert_self i s)
      have hs := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      exact hi.trans (PlaceNormalizedRefinement.compositum Q hi hs).1

end

noncomputable section

variable {E : Type*} [_root_.Field E] [Algebra F256 E]

/-- A normalized refinement of an actual subfield inclusion, expressed
over its own lower field and at the given ambient place. -/
def PlaceNormalizedExtension (Q : GlobalPlace F256 E)
    (K L : IntermediateField F256 E)
    [FiniteDimensional K E] [Algebra.IsSeparable K E] : Prop :=
  ∃ h : K ≤ L, PlaceNormalizedRefinement K Q ⊥ (IntermediateField.extendScalars h)

/-- Equality of actual lower subfields transports the full predicate,
including its finite/separable model instances. -/
theorem PlaceNormalizedExtension.congr_base (Q : GlobalPlace F256 E)
    {K K' L : IntermediateField F256 E}
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    [FiniteDimensional K' E] [Algebra.IsSeparable K' E]
    (heq : K = K') (h : PlaceNormalizedExtension Q K L) :
    PlaceNormalizedExtension Q K' L := by
  subst K'
  exact h

variable (Q : GlobalPlace F256 E) {K L M : IntermediateField F256 E}
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    [FiniteDimensional L E] [Algebra.IsSeparable L E]

/-- One source-pyramid square as an actual inclusion between coordinate
fields. Both incoming refinements produce the outgoing refinement over
the left upper field. -/
theorem PlaceNormalizedExtension.compositum_left [Finite Q.residueField]
    (hL : PlaceNormalizedExtension Q K L) (hM : PlaceNormalizedExtension Q K M) :
    PlaceNormalizedExtension Q L (L ⊔ M) := by
  obtain ⟨hKL, hL⟩ := hL
  obtain ⟨hKM, hM⟩ := hM
  letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
  letI : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq' rfl
  let LK : IntermediateField K E := IntermediateField.extendScalars hKL
  let MK : IntermediateField K E := IntermediateField.extendScalars hKM
  have h := (PlaceNormalizedRefinement.compositum Q hL hM).1
  refine ⟨le_sup_left, ?_⟩
  apply (PlaceNormalizedRefinement.restrictScalars_iff K L Q).mpr
  have hbot : (⊥ : IntermediateField L E).restrictScalars K = LK :=
    IntermediateField.restrictScalars_bot_eq_self LK
  have htop : (IntermediateField.extendScalars (show L ≤ L ⊔ M from le_sup_left)).restrictScalars K =
      LK ⊔ MK := by
    apply IntermediateField.restrictScalars_injective F256
    change L ⊔ M = (LK ⊔ MK).restrictScalars F256
    rw [← IntermediateField.restrictScalars_sup]
    rfl
  rwa [hbot, htop]

/-- Consecutive source-window refinements compose over their actual
original lower field, with all local-model changes accounted for. -/
theorem PlaceNormalizedExtension.trans
    (hKL : PlaceNormalizedExtension Q K L) (hLM : PlaceNormalizedExtension Q L M) :
    PlaceNormalizedExtension Q K M := by
  obtain ⟨hleKL, hKL⟩ := hKL
  obtain ⟨hleLM, hLM⟩ := hLM
  letI : Algebra K L := (IntermediateField.inclusion hleKL).toRingHom.toAlgebra
  letI : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq' rfl
  let LK : IntermediateField K E := IntermediateField.extendScalars hleKL
  have h := (PlaceNormalizedRefinement.restrictScalars_iff K L Q).mp hLM
  have hbot : (⊥ : IntermediateField L E).restrictScalars K = LK :=
    IntermediateField.restrictScalars_bot_eq_self LK
  have htop : (IntermediateField.extendScalars hleLM).restrictScalars K =
      IntermediateField.extendScalars (hleKL.trans hleLM) := rfl
  rw [hbot, htop] at h
  exact ⟨hleKL.trans hleLM, hKL.trans h⟩

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
