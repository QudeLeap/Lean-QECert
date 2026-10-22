import QEC.Coding.AlgebraicGeometry.Towers.SelectedPlaces
import QEC.Coding.AlgebraicGeometry.Places.RationalPlaceDegree

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Equiv.Fintype

/-!
# Finite coordinates for the selected Garcia--Stichtenoth places

The retained original GS95-family tail uses `Field (i + 2)`, with auxiliary
equation `z^16 + z = x^17`. It is distinct from `SourceField` and the source
normal-closure family. The actual split-place paths are reindexed by a literal
finite interval, and their image is exposed as a finite set of normalized
global places.  The exact cardinality and divergence of the selected lengths
are derived from the recursive path count.
-/

open Filter

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

noncomputable instance selectedFieldField (i : ℕ) :
    _root_.Field (Field (i + 2)) :=
  fieldField (i + 2)

noncomputable instance selectedFieldConstantAlgebra (i : ℕ) :
    Algebra F256 (Field (i + 2)) :=
  fieldConstantAlgebra (i + 2)

noncomputable instance selectedFieldRatFuncAlgebra (i : ℕ) :
    Algebra (RatFunc F256) (Field (i + 2)) :=
  fieldRatFuncAlgebra (i + 2)

noncomputable instance selectedFieldConstantTower (i : ℕ) :
    IsScalarTower F256 (RatFunc F256) (Field (i + 2)) :=
  fieldConstantTower (i + 2)

noncomputable instance selectedFieldFunctionField (i : ℕ) :
    _root_.FunctionField F256 (Field (i + 2)) :=
  fieldFunctionField (i + 2)

noncomputable instance fieldPolynomialAlgebra (i : ℕ) :
    Algebra (Polynomial F256) (Field i) :=
  ((algebraMap (RatFunc F256) (Field i)).comp
    (algebraMap (Polynomial F256) (RatFunc F256))).toAlgebra

noncomputable instance fieldPolynomialRatFuncTower (i : ℕ) :
    IsScalarTower (Polynomial F256) (RatFunc F256) (Field i) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

noncomputable instance fieldRatFuncSeparable (i : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (Field i) := by
  induction i with
  | zero => exact inferInstance
  | succ i ih =>
      letI : Algebra.IsSeparable (RatFunc F256) (Field i) := ih
      exact Algebra.IsSeparable.trans (RatFunc F256) (Field i) (Field (i + 1))

noncomputable instance selectedFieldRatFuncSeparable (i : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (Field (i + 2)) :=
  fieldRatFuncSeparable (i + 2)

/-- The number of selected split places in this original-family tail. -/
def selectedLength (i : ℕ) : ℕ :=
  Fintype.card (SelectedPlaceIndex (i + 2))

/-- The selected length is the literal `255 * 16^(i+2)` path count. -/
theorem selectedLength_eq (i : ℕ) :
    selectedLength i = 255 * 16 ^ (i + 2) :=
  selectedPlaceIndex_card (i + 2)

private noncomputable def selectedPlaceIndexEquiv (i : ℕ) :
    Fin (selectedLength i) ≃ SelectedPlaceIndex (i + 2) :=
  (Fintype.equivFin (SelectedPlaceIndex (i + 2))).symm

/-- The actual rational place at one original-family coordinate, before
forgetting its residue-field identification. -/
noncomputable def selectedRationalPlaceAt (i : ℕ)
    (j : Fin (selectedLength i)) : RationalPlace F256 (Field (i + 2)) :=
  selectedRationalPlace (i + 2) (selectedPlaceIndexEquiv i j)

/-- The original rational coordinate is regular at every enumerated selected
rational place. -/
theorem selectedRationalPlaceAt_baseCoordinate_regular (i : ℕ)
    (j : Fin (selectedLength i)) :
    GlobalPlace.RegularAt (selectedRationalPlaceAt i j).place
      (baseCoordinate (i + 2)) :=
  selectedRationalPlace_baseCoordinate_regular
    (i + 2) (selectedPlaceIndexEquiv i j)

/-- The original rational coordinate has nonzero evaluation at every
enumerated selected rational place. -/
theorem selectedRationalPlaceAt_evaluate_baseCoordinate_ne_zero (i : ℕ)
    (j : Fin (selectedLength i)) :
    (selectedRationalPlaceAt i j).evaluateRegular
        (baseCoordinate (i + 2))
        (selectedRationalPlaceAt_baseCoordinate_regular i j) ≠ 0 :=
  selectedRationalPlace_evaluate_baseCoordinate_ne_zero
    (i + 2) (selectedPlaceIndexEquiv i j)

/-- The actual normalized global place at one original-family coordinate. -/
noncomputable def selectedPlace (i : ℕ) (j : Fin (selectedLength i)) :
    GlobalPlace F256 (Field (i + 2)) :=
  (selectedRationalPlaceAt i j).place

@[simp]
theorem selectedRationalPlaceAt_place (i : ℕ)
    (j : Fin (selectedLength i)) :
    (selectedRationalPlaceAt i j).place = selectedPlace i j :=
  rfl

/-- The finite-coordinate enumeration has no repeated place. -/
theorem selectedPlace_injective (i : ℕ) :
    Function.Injective (selectedPlace i) := by
  intro a b hab
  apply (selectedPlaceIndexEquiv i).injective
  apply selectedRationalPlace_place_injective (i + 2)
  exact hab

/-- Every selected coordinate is a rational global place. -/
theorem selectedPlace_residueDegree (i : ℕ) (j : Fin (selectedLength i)) :
    GlobalPlace.residueDegree (selectedPlace i j) = 1 := by
  exact RationalPlace.globalResidueDegree_eq_one
    (selectedRationalPlaceAt i j)

/-- The finite set of selected normalized global places. -/
noncomputable def selectedPlaces (i : ℕ) :
    Finset (GlobalPlace F256 (Field (i + 2))) := by
  classical
  exact Finset.univ.image (selectedPlace i)

private theorem selectedPlaces_coe (i : ℕ) :
    (selectedPlaces i : Set (GlobalPlace F256 (Field (i + 2)))) =
      Set.range (selectedPlace i) := by
  classical
  ext P
  simp only [selectedPlaces, Finset.coe_image, Finset.coe_univ,
    Set.image_univ]

/-- Coordinate indices are equivalent to the selected-place subtype. -/
noncomputable def selectedPlaceEquiv (i : ℕ) :
    Fin (selectedLength i) ≃ ↥(selectedPlaces i) :=
  (Equiv.ofInjective (selectedPlace i) (selectedPlace_injective i)).trans
    (Equiv.setCongr (selectedPlaces_coe i).symm)

/-- The selected-place Finset has exactly the original-family selected length. -/
theorem selectedPlaces_card (i : ℕ) :
    (selectedPlaces i).card = selectedLength i := by
  classical
  rw [selectedPlaces, Finset.card_image_of_injective _
    (selectedPlace_injective i), Finset.card_univ, Fintype.card_fin]

/-- The selected coordinate lengths tend to infinity. -/
theorem selectedLength_tendsto_atTop : Tendsto selectedLength atTop atTop := by
  have hpow : Tendsto (fun i : ℕ => 16 ^ (i + 2)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (16 : ℕ))).comp
      (tendsto_add_atTop_nat 2)
  have hscaled : Tendsto (fun i : ℕ => 255 * 16 ^ (i + 2)) atTop atTop :=
    hpow.const_mul_atTop' (by norm_num : 0 < (255 : ℕ))
  exact hscaled.congr' (Filter.Eventually.of_forall fun i => (selectedLength_eq i).symm)

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
