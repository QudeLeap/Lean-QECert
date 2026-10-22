import QEC.Coding.AlgebraicGeometry.Towers.SourceRecursion
import QEC.Coding.AlgebraicGeometry.Towers.SourceSplitEvaluation

/-!
# Selected rational places in the source Garcia--Stichtenoth levels

Starting from the actual 240 finite values above `z = 1`, each source
recursion level keeps all sixteen selected upper places.  The construction
carries the exact nonzero Artin--Schreier-value invariant needed for the next
step and proves that the resulting finite family is injective.  It also proves
that the original rational base parameter continues to evaluate to one.

No normal-closure splitting, divisor, genus, or asymptotic conclusion is
stored here.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

private theorem sourceGlobalPlace_eq_of_valuation_eq
    {E : Type*} [_root_.Field E] [Algebra F256 E]
    (P Q : GlobalPlace F256 E) (h : P.valuation = Q.valuation) : P = Q := by
  cases P with
  | mk pv hp =>
      cases Q with
      | mk qv hq =>
          dsimp at h
          subst qv
          rfl

private theorem sourceRationalPlace_eq_of_place_eq
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

private theorem sourceSplitAbovePlace_sourceStepEmbedding_regular_iff
    {E : Type*} [_root_.Field E] [Algebra F256 E]
    (Q : RationalPlace F256 E) (P : GlobalPlace F256 E) (x : E)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) (f : E) :
    GlobalPlace.RegularAt (sourceSplitAbovePlace Q P x hx c)
        (sourceStepEmbedding P x hx f) ↔
      GlobalPlace.RegularAt Q.place f := by
  refine ⟨?_, sourceSplitAbovePlace_sourceStepEmbedding_regular
    Q P x hx c f⟩
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
  let U := sourceSplitUpperRationalPlace
    Q P x hx hregular hsplit c
  have hinvupper := sourceSplitAbovePlace_sourceStepEmbedding_regular
    Q P x hx c f⁻¹ hinvregular
  have hinvevaluate :=
    sourceSplitUpperRationalPlace_evaluate_sourceStepEmbedding
      Q P x hx hregular hsplit c f⁻¹ hinvregular
  have hinvzero : U.evaluateRegular
      (sourceStepEmbedding P x hx f⁻¹) hinvupper = 0 := by
    rw [hinvevaluate, Q.evaluateRegular_eq_zero_iff,
      Valuation.mem_maximalIdeal_iff]
    exact hinvlt
  let uf : U.place.valuationRing :=
    ⟨sourceStepEmbedding P x hx f,
      (GlobalPlace.mem_valuationRing_iff U.place _).mpr hupper⟩
  let uinv : U.place.valuationRing :=
    ⟨sourceStepEmbedding P x hx f⁻¹,
      (GlobalPlace.mem_valuationRing_iff U.place _).mpr hinvupper⟩
  have hproduct : uf * uinv = 1 := by
    apply Subtype.ext
    change sourceStepEmbedding P x hx f *
        sourceStepEmbedding P x hx f⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hfne, map_one]
  have hevaluate := congrArg U.evaluate hproduct
  rw [map_mul, map_one] at hevaluate
  change U.evaluateRegular (sourceStepEmbedding P x hx f) hupper *
      U.evaluateRegular (sourceStepEmbedding P x hx f⁻¹) hinvupper = 1 at hevaluate
  rw [hinvzero, mul_zero] at hevaluate
  exact zero_ne_one hevaluate

private theorem sourceSplitUpperRationalPlace_parent_eq
    {E : Type*} [_root_.Field E] [Algebra F256 E]
    (Q R : RationalPlace F256 E) (P : GlobalPlace F256 E) (x : E)
    (hx : P.order x = -1)
    (hQregular : GlobalPlace.RegularAt Q.place x)
    (hQsplit : galoisBaseWValue (Q.evaluateRegular x hQregular) ≠ 0)
    (hRregular : GlobalPlace.RegularAt R.place x)
    (hRsplit : galoisBaseWValue (R.evaluateRegular x hRregular) ≠ 0)
    (c d : LinearMap.ker f256ArtinSchreier)
    (hupper : sourceSplitUpperRationalPlace
        Q P x hx hQregular hQsplit c =
      sourceSplitUpperRationalPlace R P x hx hRregular hRsplit d) :
    Q = R := by
  have hplace : sourceSplitAbovePlace Q P x hx c =
      sourceSplitAbovePlace R P x hx d :=
    congrArg RationalPlace.place hupper
  have hregular_iff (f : E) : GlobalPlace.RegularAt Q.place f ↔
      GlobalPlace.RegularAt R.place f := by
    constructor
    · intro hf
      have hu := sourceSplitAbovePlace_sourceStepEmbedding_regular
        Q P x hx c f hf
      rw [hplace] at hu
      exact (sourceSplitAbovePlace_sourceStepEmbedding_regular_iff
        R P x hx hRregular hRsplit d f).mp hu
    · intro hf
      have hu := sourceSplitAbovePlace_sourceStepEmbedding_regular
        R P x hx d f hf
      rw [← hplace] at hu
      exact (sourceSplitAbovePlace_sourceStepEmbedding_regular_iff
        Q P x hx hQregular hQsplit c f).mp hu
  have hisEquiv : Q.place.valuation.IsEquiv R.place.valuation :=
    (Valuation.isEquiv_iff_val_le_one).2 fun {f} => hregular_iff f
  have hvaluation : Q.place.valuation = R.place.valuation :=
    normalizedValuation_eq_of_isEquiv
      Q.place.valuation R.place.valuation
      Q.place.normalized R.place.normalized hisEquiv
  exact sourceRationalPlace_eq_of_place_eq Q R
    (sourceGlobalPlace_eq_of_valuation_eq Q.place R.place hvaluation)

/-- Indices of the selected rational places at source-recursion level `i`. -/
@[reducible] def SourceSelectedPlaceIndex : ℕ → Type
  | 0 => GaloisBaseSplitPoint
  | i + 1 =>
      SourceSelectedPlaceIndex i × LinearMap.ker f256ArtinSchreier

/-- The initial `z=1` coordinate underlying a selected source split path. -/
def sourceSelectedPlaceIndexBasePoint :
    ∀ i : ℕ, SourceSelectedPlaceIndex i → GaloisBaseSplitPoint
  | 0, a => a
  | i + 1, index => sourceSelectedPlaceIndexBasePoint i index.1

noncomputable instance sourceSelectedPlaceIndexFintype :
    ∀ i : ℕ, Fintype (SourceSelectedPlaceIndex i)
  | 0 => inferInstance
  | i + 1 =>
      letI := sourceSelectedPlaceIndexFintype i
      inferInstance

/-- The selected source path set has exact cardinality `240 * 16^i`. -/
theorem sourceSelectedPlaceIndex_card (i : ℕ) :
    Fintype.card (SourceSelectedPlaceIndex i) = 240 * 16 ^ i := by
  induction i with
  | zero =>
      simpa only [SourceSelectedPlaceIndex, pow_zero, mul_one] using
        galoisBaseSplitPoint_card
  | succ i hi =>
      change Fintype.card
        (SourceSelectedPlaceIndex i × LinearMap.ker f256ArtinSchreier) = _
      rw [Fintype.card_prod, hi, f256ArtinSchreier_ker_card, pow_succ]
      ring

private theorem galoisBaseSplitRationalPlace_X_regular
    (a : GaloisBaseSplitPoint) :
    GlobalPlace.RegularAt (galoisBaseSplitRationalPlace a).place RatFunc.X := by
  change GlobalPlace.RegularAt (baseRationalPlace _).place RatFunc.X
  exact baseRationalPlace_X_regular _

private theorem galoisBaseSplitRationalPlace_evaluate_X
    (a : GaloisBaseSplitPoint) :
    (galoisBaseSplitRationalPlace a).evaluateRegular RatFunc.X
        (galoisBaseSplitRationalPlace_X_regular a) = (a : F256) := by
  change (baseRationalPlace _).evaluateRegular RatFunc.X
      (baseRationalPlace_X_regular _) = (a : F256)
  rw [baseRationalPlace_evaluate_X]
  rfl

private structure SourceSelectedPlaceData (i : ℕ) where
  place : RationalPlace F256 (SourceField i)
  coordinate_regular :
    GlobalPlace.RegularAt place.place (sourceDistinguishedCoordinate i)
  coordinate_split :
    galoisBaseWValue
      (place.evaluateRegular (sourceDistinguishedCoordinate i)
        coordinate_regular) ≠ 0

private noncomputable def sourceSelectedPlaceData :
    ∀ i : ℕ, SourceSelectedPlaceIndex i → SourceSelectedPlaceData i
  | 0, a =>
      { place := galoisBaseSplitRationalPlace a
        coordinate_regular := galoisBaseSplitRationalPlace_X_regular a
        coordinate_split := by
          change galoisBaseWValue
            ((galoisBaseSplitRationalPlace a).evaluateRegular RatFunc.X
              (galoisBaseSplitRationalPlace_X_regular a)) ≠ 0
          rw [galoisBaseSplitRationalPlace_evaluate_X]
          exact a.property }
  | i + 1, index =>
      let previous := sourceSelectedPlaceData i index.1
      { place := sourceSplitUpperRationalPlace previous.place
          (sourceDistinguishedPlace i) (sourceDistinguishedCoordinate i)
          (sourceDistinguishedCoordinate_order i)
          previous.coordinate_regular previous.coordinate_split index.2
        coordinate_regular :=
          sourceSplitAbovePlace_sourceStepCoordinate_regular
            previous.place (sourceDistinguishedPlace i)
            (sourceDistinguishedCoordinate i)
            (sourceDistinguishedCoordinate_order i)
            previous.coordinate_regular previous.coordinate_split index.2
        coordinate_split :=
          sourceSplitUpperRationalPlace_evaluate_sourceStepCoordinate_split
            previous.place (sourceDistinguishedPlace i)
            (sourceDistinguishedCoordinate i)
            (sourceDistinguishedCoordinate_order i)
            previous.coordinate_regular previous.coordinate_split index.2 }

/-- The actual selected rational place associated to a finite source path. -/
noncomputable def sourceSelectedRationalPlace (i : ℕ)
    (index : SourceSelectedPlaceIndex i) : RationalPlace F256 (SourceField i) :=
  (sourceSelectedPlaceData i index).place

@[simp]
theorem sourceSelectedRationalPlace_zero (a : GaloisBaseSplitPoint) :
    sourceSelectedRationalPlace 0 a = galoisBaseSplitRationalPlace a := by
  rfl

/-- The source coordinate is regular at every selected source place. -/
theorem sourceSelectedRationalPlace_coordinate_regular (i : ℕ)
    (index : SourceSelectedPlaceIndex i) :
    GlobalPlace.RegularAt (sourceSelectedRationalPlace i index).place
      (sourceDistinguishedCoordinate i) :=
  (sourceSelectedPlaceData i index).coordinate_regular

/-- The selected source place at a successor level is the literal rational
upper place chosen by the last path coordinate. -/
theorem sourceSelectedRationalPlace_succ (i : ℕ)
    (index : SourceSelectedPlaceIndex i)
    (c : LinearMap.ker f256ArtinSchreier) :
    sourceSelectedRationalPlace (i + 1) (index, c) =
      sourceSplitUpperRationalPlace (sourceSelectedRationalPlace i index)
        (sourceDistinguishedPlace i) (sourceDistinguishedCoordinate i)
        (sourceDistinguishedCoordinate_order i)
        (sourceSelectedRationalPlace_coordinate_regular i index)
        (sourceSelectedPlaceData i index).coordinate_split c := by
  rfl

/-- The source coordinate retains the exact split condition at every selected
place. -/
theorem sourceSelectedRationalPlace_coordinate_split (i : ℕ)
    (index : SourceSelectedPlaceIndex i) :
    galoisBaseWValue
        ((sourceSelectedRationalPlace i index).evaluateRegular
          (sourceDistinguishedCoordinate i)
          (sourceSelectedRationalPlace_coordinate_regular i index)) ≠ 0 :=
  (sourceSelectedPlaceData i index).coordinate_split

/-- Distinct finite source paths give distinct selected rational places. -/
theorem sourceSelectedRationalPlace_injective :
    ∀ i : ℕ, Function.Injective (sourceSelectedRationalPlace i)
  | 0 => galoisBaseSplitRationalPlace_injective
  | i + 1 => by
      intro a b hab
      rcases a with ⟨a, c⟩
      rcases b with ⟨b, d⟩
      let A := sourceSelectedPlaceData i a
      let B := sourceSelectedPlaceData i b
      have hparent : A.place = B.place :=
        sourceSplitUpperRationalPlace_parent_eq A.place B.place
          (sourceDistinguishedPlace i) (sourceDistinguishedCoordinate i)
          (sourceDistinguishedCoordinate_order i)
          A.coordinate_regular A.coordinate_split
          B.coordinate_regular B.coordinate_split c d hab
      have habIndex : a = b :=
        sourceSelectedRationalPlace_injective i hparent
      subst b
      have hcd : c = d := by
        apply sourceSplitUpperRationalPlace_injective A.place
          (sourceDistinguishedPlace i) (sourceDistinguishedCoordinate i)
          (sourceDistinguishedCoordinate_order i)
          A.coordinate_regular A.coordinate_split
        exact hab
      exact Prod.ext rfl hcd

/-- Distinct finite source paths also have distinct normalized global places.
-/
theorem sourceSelectedRationalPlace_place_injective (i : ℕ) :
    Function.Injective (fun index : SourceSelectedPlaceIndex i =>
      (sourceSelectedRationalPlace i index).place) := by
  intro a b hab
  apply sourceSelectedRationalPlace_injective i
  exact sourceRationalPlace_eq_of_place_eq
    (sourceSelectedRationalPlace i a) (sourceSelectedRationalPlace i b) hab

/-! ## The original rational coordinate along selected source paths -/

/-- The image of the original rational coordinate `X` in source level `i`. -/
noncomputable def sourceBaseCoordinate (i : ℕ) : SourceField i :=
  algebraMap (RatFunc F256) (SourceField i) RatFunc.X

@[simp]
theorem sourceBaseCoordinate_zero : sourceBaseCoordinate 0 = RatFunc.X :=
  rfl

/-- The original rational coordinate is carried to the next source level by
the literal recursion embedding. -/
theorem sourceBaseCoordinate_succ (i : ℕ) :
    sourceBaseCoordinate (i + 1) =
      sourceRecursionEmbedding i (sourceBaseCoordinate i) :=
  rfl

/-- The original rational coordinate remains regular at every selected source
place. -/
theorem sourceSelectedRationalPlace_baseCoordinate_regular :
    ∀ (i : ℕ) (index : SourceSelectedPlaceIndex i),
      GlobalPlace.RegularAt (sourceSelectedRationalPlace i index).place
        (sourceBaseCoordinate i)
  | 0, a => by
      exact galoisBaseSplitRationalPlace_X_regular a
  | i + 1, index => by
      rcases index with ⟨index, c⟩
      let previous := sourceSelectedPlaceData i index
      have hregular :=
        sourceSelectedRationalPlace_baseCoordinate_regular i index
      have hupper := sourceSplitAbovePlace_sourceStepEmbedding_regular
        previous.place (sourceDistinguishedPlace i)
        (sourceDistinguishedCoordinate i)
        (sourceDistinguishedCoordinate_order i) c
        (sourceBaseCoordinate i) hregular
      simp only [sourceSelectedRationalPlace, sourceSelectedPlaceData,
        sourceBaseCoordinate_succ] at hupper ⊢
      exact hupper

/-- Evaluation of the original rational coordinate remembers the literal
initial point along every selected source path. -/
theorem sourceSelectedRationalPlace_evaluate_baseCoordinate :
    ∀ (i : ℕ) (index : SourceSelectedPlaceIndex i),
      (sourceSelectedRationalPlace i index).evaluateRegular
          (sourceBaseCoordinate i)
          (sourceSelectedRationalPlace_baseCoordinate_regular i index) =
        (sourceSelectedPlaceIndexBasePoint i index : F256)
  | 0, a => by
      simpa only [sourceSelectedRationalPlace, sourceSelectedPlaceData,
        sourceBaseCoordinate_zero, sourceSelectedPlaceIndexBasePoint] using
          galoisBaseSplitRationalPlace_evaluate_X a
  | i + 1, index => by
      rcases index with ⟨index, c⟩
      let previous := sourceSelectedPlaceData i index
      have hevaluate :=
        sourceSplitUpperRationalPlace_evaluate_sourceStepEmbedding
          previous.place (sourceDistinguishedPlace i)
          (sourceDistinguishedCoordinate i)
          (sourceDistinguishedCoordinate_order i)
          previous.coordinate_regular previous.coordinate_split c
          (sourceBaseCoordinate i)
          (sourceSelectedRationalPlace_baseCoordinate_regular i index)
      have hprevious :=
        sourceSelectedRationalPlace_evaluate_baseCoordinate i index
      have hvalue := hevaluate.trans hprevious
      simp only [sourceSelectedRationalPlace, sourceSelectedPlaceData,
        sourceBaseCoordinate_succ, sourceSelectedPlaceIndexBasePoint] at hvalue ⊢
      exact hvalue

/-! ## The fixed rational base parameter -/

/-- The image of `z = (X^16 + X)^15` in source level `i`. -/
noncomputable def sourceGaloisBaseParameter (i : ℕ) : SourceField i :=
  algebraMap (RatFunc F256) (SourceField i) galoisBaseZ

private theorem sourceGaloisBaseParameter_eq (i : ℕ) :
    sourceGaloisBaseParameter i =
      (sourceBaseCoordinate i ^ 16 + sourceBaseCoordinate i) ^ 15 := by
  simp [sourceGaloisBaseParameter, galoisBaseZ, galoisBaseW,
    sourceBaseCoordinate]

/-- The base parameter `z` is regular at every selected source place. -/
theorem sourceGaloisBaseParameter_regular (i : ℕ)
    (index : SourceSelectedPlaceIndex i) :
    GlobalPlace.RegularAt (sourceSelectedRationalPlace i index).place
      (sourceGaloisBaseParameter i) := by
  let Q := sourceSelectedRationalPlace i index
  have hx : sourceBaseCoordinate i ∈ Q.place.valuationRing :=
    (GlobalPlace.mem_valuationRing_iff Q.place _).mpr
      (sourceSelectedRationalPlace_baseCoordinate_regular i index)
  rw [GlobalPlace.regularAt_iff_mem_valuationRing,
    sourceGaloisBaseParameter_eq]
  exact Q.place.valuationRing.pow_mem
    (Q.place.valuationRing.add_mem _ _
      (Q.place.valuationRing.pow_mem hx 16) hx) 15

/-- Every selected source place has the literal residue value `z = 1`. -/
theorem sourceGaloisBaseParameter_evaluate (i : ℕ)
    (index : SourceSelectedPlaceIndex i) :
    (sourceSelectedRationalPlace i index).evaluateRegular
        (sourceGaloisBaseParameter i)
        (sourceGaloisBaseParameter_regular i index) = 1 := by
  let Q := sourceSelectedRationalPlace i index
  let xO : Q.place.valuationRing :=
    ⟨sourceBaseCoordinate i,
      (GlobalPlace.mem_valuationRing_iff Q.place _).mpr
        (sourceSelectedRationalPlace_baseCoordinate_regular i index)⟩
  have hx : Q.evaluate xO =
      (sourceSelectedPlaceIndexBasePoint i index : F256) := by
    exact sourceSelectedRationalPlace_evaluate_baseCoordinate i index
  have hinput :
      (⟨sourceGaloisBaseParameter i,
        (GlobalPlace.mem_valuationRing_iff Q.place _).mpr
          (sourceGaloisBaseParameter_regular i index)⟩ :
          Q.place.valuationRing) =
        (xO ^ 16 + xO) ^ 15 := by
    apply Subtype.ext
    exact sourceGaloisBaseParameter_eq i
  change Q.evaluate
      ⟨sourceGaloisBaseParameter i,
        (GlobalPlace.mem_valuationRing_iff Q.place _).mpr
          (sourceGaloisBaseParameter_regular i index)⟩ = 1
  rw [hinput, map_pow, map_add, map_pow, hx]
  simpa only [galoisBaseZValue_eq] using
    (galoisBaseZValue_eq_one_iff
      (sourceSelectedPlaceIndexBasePoint i index)).2
      (sourceSelectedPlaceIndexBasePoint i index).property

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
