import QEC.Coding.AlgebraicGeometry.Towers.Translation
import QEC.Coding.AlgebraicGeometry.Towers.PlaceStep

import Mathlib.FieldTheory.Galois.Basic

/-!
# Galois structure of one Garcia--Stichtenoth step

The sixteen concrete constant translations exhaust the automorphisms of one
degree-sixteen recursion step.  This proves the actual field extension is
Galois; no place splitting, divisor, genus, or tower asymptotic is asserted in
this file.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {K : Type*} [Field K] [Algebra F256 K]

/-- Distinct kernel constants induce distinct translations of the concrete
step field. -/
theorem stepTranslation_injective
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Function.Injective (stepTranslation P x hx) := by
  intro c d hcd
  have haux := congrArg
    (fun e : StepField P x hx ≃ₐ[K] StepField P x hx =>
      e (stepAuxiliaryCoordinate P x hx)) hcd
  change stepTranslation P x hx c (stepAuxiliaryCoordinate P x hx) =
    stepTranslation P x hx d (stepAuxiliaryCoordinate P x hx) at haux
  rw [stepTranslation_apply_auxiliaryCoordinate,
    stepTranslation_apply_auxiliaryCoordinate] at haux
  have hconstants :
      algebraMap F256 (StepField P x hx) (c : F256) =
        algebraMap F256 (StepField P x hx) (d : F256) :=
    add_left_cancel haux
  apply Subtype.ext
  exact (algebraMap F256 (StepField P x hx)).injective hconstants

/-- One step has exactly sixteen `K`-algebra automorphisms. -/
theorem stepField_algEquiv_card
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Nat.card (StepField P x hx ≃ₐ[K] StepField P x hx) = 16 := by
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card (StepField P x hx ≃ₐ[K] StepField P x hx) ≤
          Module.finrank K (StepField P x hx) := AlgEquiv.card_le
      _ = 16 := stepField_finrank P x hx
  · calc
      16 = Nat.card (LinearMap.ker f256ArtinSchreier) := by
        rw [Nat.card_eq_fintype_card, f256ArtinSchreier_ker_card]
      _ ≤ Nat.card (StepField P x hx ≃ₐ[K] StepField P x hx) :=
        Nat.card_le_card_of_injective (stepTranslation P x hx)
          (stepTranslation_injective P x hx)

/-- The concrete degree-sixteen Garcia--Stichtenoth step is Galois over its
preceding function field. -/
noncomputable instance stepField_isGalois
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsGalois K (StepField P x hx) := by
  apply IsGalois.of_card_aut_eq_finrank
  rw [stepField_algEquiv_card, stepField_finrank]

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
