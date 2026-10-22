import QEC.Coding.AlgebraicGeometry.Towers.BasePlaces
import QEC.Coding.AlgebraicGeometry.Towers.Recursion
import QEC.Coding.AlgebraicGeometry.Towers.SplitEvaluation

/-!
# Selected rational places at every Garcia--Stichtenoth level

Starting from the 255 nonzero finite base points, each recursive level keeps
all sixteen split upper places.  The construction carries exactly the
regular/nonzero coordinate invariant needed for the next step and proves
that the resulting finite family is injective.  No genus, divisor, or
asymptotic ratio is stored here.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

private theorem globalPlace_eq_of_valuation_eq
    {E : Type*} [_root_.Field E] [Algebra F256 E]
    (P Q : GlobalPlace F256 E) (h : P.valuation = Q.valuation) : P = Q := by
  cases P with
  | mk pv hp =>
      cases Q with
      | mk qv hq =>
          dsimp at h
          subst qv
          rfl

private theorem rationalPlace_eq_of_place_eq
    {E : Type*} [_root_.Field E] [Algebra F256 E]
    (P Q : RationalPlace F256 E) (h : P.place = Q.place) : P = Q := by
  cases P with
  | mk pp pe ph =>
      cases Q with
      | mk qp qe qh =>
          dsimp at h
          subst qp
          have he : pe = qe := by
            apply RingEquiv.ext
            intro a
            rw [ph, qh]
          subst qe
          rfl

private theorem splitAbovePlace_stepEmbedding_regular_iff
    {E : Type*} [_root_.Field E] [Algebra F256 E]
    (Q : RationalPlace F256 E) (P : GlobalPlace F256 E) (x : E)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier) (f : E) :
    GlobalPlace.RegularAt (splitAbovePlace Q P x hx c)
        (stepFieldEmbedding P x hx f) ↔
      GlobalPlace.RegularAt Q.place f := by
  refine ⟨?_, splitAbovePlace_stepEmbedding_regular Q P x hx c f⟩
  intro hupper
  by_contra hbase
  have hgt : 1 < Q.place.valuation f := lt_of_not_ge hbase
  have hfne : f ≠ 0 := by
    intro hfzero
    subst f
    simp at hgt
  have hinvlt : Q.place.valuation f⁻¹ < 1 := by
    rw [Q.place.valuation.map_inv]
    exact inv_lt_one_of_one_lt₀ hgt
  have hinvregular : GlobalPlace.RegularAt Q.place f⁻¹ := hinvlt.le
  let U := splitUpperRationalPlace Q P x hx hregular c
  have hinvupper := splitAbovePlace_stepEmbedding_regular
    Q P x hx c f⁻¹ hinvregular
  have hinvevaluate := splitUpperRationalPlace_evaluate_stepEmbedding
    Q P x hx hregular c f⁻¹ hinvregular
  have hinvzero : U.evaluateRegular
      (stepFieldEmbedding P x hx f⁻¹) hinvupper = 0 := by
    rw [hinvevaluate, Q.evaluateRegular_eq_zero_iff,
      Valuation.mem_maximalIdeal_iff]
    exact hinvlt
  let uf : U.place.valuationRing :=
    ⟨stepFieldEmbedding P x hx f,
      (GlobalPlace.mem_valuationRing_iff U.place _).mpr hupper⟩
  let uinv : U.place.valuationRing :=
    ⟨stepFieldEmbedding P x hx f⁻¹,
      (GlobalPlace.mem_valuationRing_iff U.place _).mpr hinvupper⟩
  have hproduct : uf * uinv = 1 := by
    apply Subtype.ext
    change stepFieldEmbedding P x hx f *
        stepFieldEmbedding P x hx f⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hfne, map_one]
  have hevaluate := congrArg U.evaluate hproduct
  rw [map_mul, map_one] at hevaluate
  change U.evaluateRegular (stepFieldEmbedding P x hx f) hupper *
      U.evaluateRegular (stepFieldEmbedding P x hx f⁻¹) hinvupper = 1 at hevaluate
  rw [hinvzero, mul_zero] at hevaluate
  exact zero_ne_one hevaluate

private theorem splitUpperRationalPlace_parent_eq
    {E : Type*} [_root_.Field E] [Algebra F256 E]
    (Q R : RationalPlace F256 E) (P : GlobalPlace F256 E) (x : E)
    (hx : P.order x = -1)
    (hQregular : GlobalPlace.RegularAt Q.place x)
    (hRregular : GlobalPlace.RegularAt R.place x)
    (c d : LinearMap.ker f256ArtinSchreier)
    (hupper : splitUpperRationalPlace Q P x hx hQregular c =
      splitUpperRationalPlace R P x hx hRregular d) : Q = R := by
  have hplace : splitAbovePlace Q P x hx c =
      splitAbovePlace R P x hx d :=
    congrArg RationalPlace.place hupper
  have hregular_iff (f : E) : GlobalPlace.RegularAt Q.place f ↔
      GlobalPlace.RegularAt R.place f := by
    constructor
    · intro hf
      have hu := splitAbovePlace_stepEmbedding_regular Q P x hx c f hf
      rw [hplace] at hu
      exact (splitAbovePlace_stepEmbedding_regular_iff
        R P x hx hRregular d f).mp hu
    · intro hf
      have hu := splitAbovePlace_stepEmbedding_regular R P x hx d f hf
      rw [← hplace] at hu
      exact (splitAbovePlace_stepEmbedding_regular_iff
        Q P x hx hQregular c f).mp hu
  have hisEquiv : Q.place.valuation.IsEquiv R.place.valuation :=
    (Valuation.isEquiv_iff_val_le_one).2 fun {f} => hregular_iff f
  have hvaluation : Q.place.valuation = R.place.valuation :=
    normalizedValuation_eq_of_isEquiv
      Q.place.valuation R.place.valuation
      Q.place.normalized R.place.normalized hisEquiv
  exact rationalPlace_eq_of_place_eq Q R
    (globalPlace_eq_of_valuation_eq Q.place R.place hvaluation)

/-- Indices of the selected rational places at recursive level `i`. -/
@[reducible] def SelectedPlaceIndex : ℕ → Type
  | 0 => BasePoint
  | i + 1 => SelectedPlaceIndex i × LinearMap.ker f256ArtinSchreier

/-- The initial nonzero coordinate underlying a selected split path. -/
def selectedPlaceIndexBasePoint :
    ∀ i : ℕ, SelectedPlaceIndex i → BasePoint
  | 0, a => a
  | i + 1, index => selectedPlaceIndexBasePoint i index.1

noncomputable instance selectedPlaceIndexFintype :
    ∀ i : ℕ, Fintype (SelectedPlaceIndex i)
  | 0 => inferInstance
  | i + 1 =>
      letI := selectedPlaceIndexFintype i
      inferInstance

/-- The selected-place index set has the exact source-facing cardinality. -/
theorem selectedPlaceIndex_card (i : ℕ) :
    Fintype.card (SelectedPlaceIndex i) = 255 * 16 ^ i := by
  induction i with
  | zero =>
      simpa only [SelectedPlaceIndex, pow_zero, mul_one] using basePoint_card
  | succ i hi =>
      change Fintype.card
        (SelectedPlaceIndex i × LinearMap.ker f256ArtinSchreier) = _
      rw [Fintype.card_prod, hi, f256ArtinSchreier_ker_card, pow_succ]
      ring

private structure SelectedPlaceData (i : ℕ) where
  place : RationalPlace F256 (Field i)
  coordinate_regular :
    GlobalPlace.RegularAt place.place (distinguishedCoordinate i)
  coordinate_evaluate_ne_zero :
    place.evaluateRegular (distinguishedCoordinate i) coordinate_regular ≠ 0

private noncomputable def selectedPlaceData :
    ∀ i : ℕ, SelectedPlaceIndex i → SelectedPlaceData i
  | 0, a =>
      { place := baseRationalPlace a
        coordinate_regular := baseRationalPlace_X_regular a
        coordinate_evaluate_ne_zero := by
          change (baseRationalPlace a).evaluateRegular RatFunc.X
            (baseRationalPlace_X_regular a) ≠ 0
          rw [baseRationalPlace_evaluate_X]
          exact Units.ne_zero a }
  | i + 1, index =>
      let previous := selectedPlaceData i index.1
      { place := splitUpperRationalPlace previous.place
          (distinguishedPlace i) (distinguishedCoordinate i)
          (distinguishedCoordinate_order i) previous.coordinate_regular index.2
        coordinate_regular :=
          splitAbovePlace_stepDistinguishedCoordinate_regular
            previous.place (distinguishedPlace i) (distinguishedCoordinate i)
            (distinguishedCoordinate_order i) previous.coordinate_regular
            previous.coordinate_evaluate_ne_zero index.2
        coordinate_evaluate_ne_zero :=
          splitUpperRationalPlace_evaluate_stepDistinguishedCoordinate_ne_zero
            previous.place (distinguishedPlace i) (distinguishedCoordinate i)
            (distinguishedCoordinate_order i) previous.coordinate_regular
            previous.coordinate_evaluate_ne_zero index.2 }

/-- The actual selected rational place associated to a finite path. -/
noncomputable def selectedRationalPlace (i : ℕ)
    (index : SelectedPlaceIndex i) : RationalPlace F256 (Field i) :=
  (selectedPlaceData i index).place

/-- At level zero, the selected place is the literal rational place attached
to its base point. -/
theorem selectedRationalPlace_zero (a : BasePoint) :
    selectedRationalPlace 0 a = baseRationalPlace a := by
  rfl

/-- The distinguished coordinate is regular at every selected place. -/
theorem selectedRationalPlace_coordinate_regular (i : ℕ)
    (index : SelectedPlaceIndex i) :
    GlobalPlace.RegularAt (selectedRationalPlace i index).place
      (distinguishedCoordinate i) :=
  (selectedPlaceData i index).coordinate_regular

/-- The selected place at a successor level is the literal split upper place
chosen by the last path coordinate. -/
theorem selectedRationalPlace_succ (i : ℕ)
    (index : SelectedPlaceIndex i)
    (c : LinearMap.ker f256ArtinSchreier) :
    selectedRationalPlace (i + 1) (index, c) =
      splitUpperRationalPlace (selectedRationalPlace i index)
        (distinguishedPlace i) (distinguishedCoordinate i)
        (distinguishedCoordinate_order i)
        (selectedRationalPlace_coordinate_regular i index) c := by
  rfl

/-- The distinguished coordinate has nonzero residue at every selected
place. -/
theorem selectedRationalPlace_coordinate_evaluate_ne_zero (i : ℕ)
    (index : SelectedPlaceIndex i) :
    (selectedRationalPlace i index).evaluateRegular
        (distinguishedCoordinate i)
        (selectedRationalPlace_coordinate_regular i index) ≠ 0 :=
  (selectedPlaceData i index).coordinate_evaluate_ne_zero

/-- Distinct finite paths give distinct selected rational places. -/
theorem selectedRationalPlace_injective :
    ∀ i : ℕ, Function.Injective (selectedRationalPlace i)
  | 0 => by
      intro a b hab
      apply baseRationalPlace_injective
      exact congrArg RationalPlace.place hab
  | i + 1 => by
      intro a b hab
      rcases a with ⟨a, c⟩
      rcases b with ⟨b, d⟩
      let A := selectedPlaceData i a
      let B := selectedPlaceData i b
      have hparent : A.place = B.place :=
        splitUpperRationalPlace_parent_eq A.place B.place
          (distinguishedPlace i) (distinguishedCoordinate i)
          (distinguishedCoordinate_order i) A.coordinate_regular
          B.coordinate_regular c d hab
      have habIndex : a = b := selectedRationalPlace_injective i hparent
      subst b
      have hcd : c = d := by
        apply splitUpperRationalPlace_injective A.place
          (distinguishedPlace i) (distinguishedCoordinate i)
          (distinguishedCoordinate_order i) A.coordinate_regular
        exact hab
      exact Prod.ext rfl hcd

/-- Distinct finite paths also have distinct underlying normalized global
places. -/
theorem selectedRationalPlace_place_injective (i : ℕ) :
    Function.Injective (fun index : SelectedPlaceIndex i =>
      (selectedRationalPlace i index).place) := by
  intro a b hab
  apply selectedRationalPlace_injective i
  exact rationalPlace_eq_of_place_eq
    (selectedRationalPlace i a) (selectedRationalPlace i b) hab

/-! ## The base rational coordinate along the selected split paths -/

/-- The image of the original rational coordinate `X` in recursive level
`i`.  This is distinct from the recursively changing distinguished
coordinate. -/
noncomputable def baseCoordinate (i : ℕ) : Field i :=
  algebraMap (RatFunc F256) (Field i) RatFunc.X

@[simp]
theorem baseCoordinate_zero : baseCoordinate 0 = RatFunc.X :=
  rfl

/-- The original rational coordinate is carried to the next level by the
literal tower embedding. -/
theorem baseCoordinate_succ (i : ℕ) :
    baseCoordinate (i + 1) = stepEmbedding i (baseCoordinate i) :=
  rfl

/-- The original rational coordinate remains regular at every selected
split place. -/
theorem selectedRationalPlace_baseCoordinate_regular :
    ∀ (i : ℕ) (index : SelectedPlaceIndex i),
      GlobalPlace.RegularAt (selectedRationalPlace i index).place
        (baseCoordinate i)
  | 0, a => by
      exact baseRationalPlace_X_regular a
  | i + 1, index => by
      rcases index with ⟨index, c⟩
      let previous := selectedPlaceData i index
      have hregular := selectedRationalPlace_baseCoordinate_regular i index
      have hupper := splitAbovePlace_stepEmbedding_regular
        previous.place (distinguishedPlace i) (distinguishedCoordinate i)
        (distinguishedCoordinate_order i) c (baseCoordinate i) hregular
      simp only [selectedRationalPlace, selectedPlaceData,
        baseCoordinate_succ] at hupper ⊢
      exact hupper

/-- The original rational coordinate has nonzero residue at every selected
split place. -/
theorem selectedRationalPlace_evaluate_baseCoordinate_ne_zero :
    ∀ (i : ℕ) (index : SelectedPlaceIndex i),
      (selectedRationalPlace i index).evaluateRegular
          (baseCoordinate i)
          (selectedRationalPlace_baseCoordinate_regular i index) ≠ 0
  | 0, a => by
      have hne : (baseRationalPlace a).evaluateRegular RatFunc.X
          (baseRationalPlace_X_regular a) ≠ 0 := by
        rw [baseRationalPlace_evaluate_X]
        exact Units.ne_zero a
      exact hne
  | i + 1, index => by
      rcases index with ⟨index, c⟩
      let previous := selectedPlaceData i index
      have hregular := selectedRationalPlace_baseCoordinate_regular i index
      have hevaluate := splitUpperRationalPlace_evaluate_stepEmbedding
        previous.place (distinguishedPlace i) (distinguishedCoordinate i)
        (distinguishedCoordinate_order i) previous.coordinate_regular c
        (baseCoordinate i) hregular
      have hne :
          (splitUpperRationalPlace previous.place (distinguishedPlace i)
              (distinguishedCoordinate i) (distinguishedCoordinate_order i)
              previous.coordinate_regular c).evaluateRegular
              (stepFieldEmbedding (distinguishedPlace i)
                (distinguishedCoordinate i) (distinguishedCoordinate_order i)
                (baseCoordinate i))
              (splitAbovePlace_stepEmbedding_regular previous.place
                (distinguishedPlace i) (distinguishedCoordinate i)
                (distinguishedCoordinate_order i) c (baseCoordinate i)
                hregular) ≠ 0 := by
        rw [hevaluate]
        exact selectedRationalPlace_evaluate_baseCoordinate_ne_zero i index
      simp only [selectedRationalPlace, selectedPlaceData,
        baseCoordinate_succ, stepEmbedding] at hne ⊢
      exact hne

/-- Evaluation of the original rational coordinate remembers the literal
initial point along every selected split path. -/
theorem selectedRationalPlace_evaluate_baseCoordinate :
    ∀ (i : ℕ) (index : SelectedPlaceIndex i),
      (selectedRationalPlace i index).evaluateRegular
          (baseCoordinate i)
          (selectedRationalPlace_baseCoordinate_regular i index) =
        (selectedPlaceIndexBasePoint i index : F256)
  | 0, a => by
      simpa only [selectedRationalPlace, selectedPlaceData,
        baseCoordinate_zero, selectedPlaceIndexBasePoint] using
          baseRationalPlace_evaluate_X a
  | i + 1, index => by
      rcases index with ⟨index, c⟩
      let previous := selectedPlaceData i index
      have hevaluate := splitUpperRationalPlace_evaluate_stepEmbedding
        previous.place (distinguishedPlace i) (distinguishedCoordinate i)
        (distinguishedCoordinate_order i) previous.coordinate_regular c
        (baseCoordinate i)
        (selectedRationalPlace_baseCoordinate_regular i index)
      have hprevious := selectedRationalPlace_evaluate_baseCoordinate i index
      have hvalue := hevaluate.trans hprevious
      simp only [selectedRationalPlace, selectedPlaceData,
        baseCoordinate_succ, stepEmbedding, selectedPlaceIndexBasePoint] at hvalue ⊢
      exact hvalue

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
