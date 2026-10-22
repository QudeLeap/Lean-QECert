import QEC.Coding.AlgebraicGeometry.Towers.SourceRationalSplitting

/-!
# Evaluation along a selected source recursion step

Regular base functions stay regular at every selected upper place and retain
their residue values.  The integral successor coordinate is regular, and its
evaluated Artin--Schreier value is the literal source right-hand side at the
parent value.  Its symbolic nonzeroness preserves the exact split condition
needed to iterate the sixteen-way construction.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {K : Type*} [Field K] [Algebra F256 K]

private theorem sourceStepRhs_ne_zero_of_galoisBaseWValue_ne_zero
    (a : F256) (ha : galoisBaseWValue a ≠ 0) :
    sourceStepRhs a ≠ 0 := by
  have ha_ne : a ≠ 0 := by
    intro hzero
    apply ha
    rw [galoisBaseWValue_eq, hzero]
    norm_num
  have hden : a ^ 15 + 1 ≠ 0 := by
    intro hzero
    apply ha
    rw [galoisBaseWValue_eq]
    calc
      a ^ 16 + a = a * (a ^ 15 + 1) := by ring
      _ = 0 := by rw [hzero, mul_zero]
  rw [sourceStepRhs]
  exact div_ne_zero (pow_ne_zero 16 ha_ne) hden

/-- A function regular at the base rational place remains regular at every
selected source upper place. -/
theorem sourceSplitAbovePlace_sourceStepEmbedding_regular
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier)
    (f : K) (hf : GlobalPlace.RegularAt Q.place f) :
    GlobalPlace.RegularAt (sourceSplitAbovePlace Q P x hx c)
      (sourceStepEmbedding P x hx f) := by
  let O := Q.place.valuationRing
  let S := SourceSplitIntegralClosure Q P x hx
  let L := SourceStepField P x hx
  let H := sourceSplitUpperHeightOne Q P x hx c
  let fO : O :=
    ⟨f, (GlobalPlace.mem_valuationRing_iff Q.place f).mpr hf⟩
  have hle := H.valuation_le_one (K := L) (algebraMap O S fO)
  change H.valuation L (sourceStepEmbedding P x hx f) ≤ 1
  exact hle

/-- Evaluation of an embedded regular base function agrees with its original
rational-place evaluation. -/
theorem sourceSplitUpperRationalPlace_evaluate_sourceStepEmbedding
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier)
    (f : K) (hf : GlobalPlace.RegularAt Q.place f) :
    (sourceSplitUpperRationalPlace Q P x hx hregular hsplit c).evaluateRegular
        (sourceStepEmbedding P x hx f)
        (sourceSplitAbovePlace_sourceStepEmbedding_regular
          Q P x hx c f hf) =
      Q.evaluateRegular f hf := by
  let O := Q.place.valuationRing
  let S := SourceSplitIntegralClosure Q P x hx
  let L := SourceStepField P x hx
  let H := sourceSplitUpperHeightOne Q P x hx c
  let U := sourceSplitUpperRationalPlace Q P x hx hregular hsplit c
  let m : Ideal O := IsLocalRing.maximalIdeal O
  letI : H.asIdeal.LiesOver m := by
    change ((sourceSplitUpperPrime Q P x hx c).1).LiesOver m
    infer_instance
  let fO : O :=
    ⟨f, (GlobalPlace.mem_valuationRing_iff Q.place f).mpr hf⟩
  let a : F256 := Q.evaluateRegular f hf
  let fU : U.place.valuationRing :=
    ⟨sourceStepEmbedding P x hx f,
      (GlobalPlace.mem_valuationRing_iff U.place _).mpr
        (sourceSplitAbovePlace_sourceStepEmbedding_regular
          Q P x hx c f hf)⟩
  let aU : U.place.valuationRing :=
    GlobalPlace.constantsToValuationRing U.place a
  have hbase : fO - GlobalPlace.constantsToValuationRing Q.place a ∈
      IsLocalRing.maximalIdeal O := by
    rw [← Q.evaluate_eq_zero_iff, map_sub, Q.evaluate_constants]
    change a - a = 0
    exact sub_self a
  have hupper : algebraMap O S
      (fO - GlobalPlace.constantsToValuationRing Q.place a) ∈ H.asIdeal := by
    rw [← Ideal.mem_under]
    rw [← (inferInstance : H.asIdeal.LiesOver m).over]
    exact hbase
  have hlt : H.valuation L
      (algebraMap S L
        (algebraMap O S
          (fO - GlobalPlace.constantsToValuationRing Q.place a))) < 1 :=
    (H.valuation_lt_one_iff_mem (K := L) _).2 hupper
  change U.constantsEquiv.symm (U.place.residue fU) = a
  apply U.constantsEquiv.injective
  rw [U.constantsEquiv.apply_symm_apply, U.constantsEquiv_apply]
  change U.place.residue fU = U.place.residue aU
  rw [← sub_eq_zero, ← map_sub, GlobalPlace.residue_eq_zero_iff,
    Valuation.mem_maximalIdeal_iff]
  change H.valuation L
    (sourceStepEmbedding P x hx f - algebraMap F256 L a) < 1
  simp only [map_sub, IsScalarTower.algebraMap_apply] at hlt ⊢
  exact hlt

/-- The literal source successor coordinate is regular at every selected
upper place. -/
theorem sourceSplitAbovePlace_sourceStepCoordinate_regular
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    GlobalPlace.RegularAt (sourceSplitAbovePlace Q P x hx c)
      (sourceStepCoordinate P x hx) := by
  let L := SourceStepField P x hx
  let H := sourceSplitUpperHeightOne Q P x hx c
  have hle := H.valuation_le_one (K := L)
    (sourceSplitIntegralCoordinate Q P x hx hregular hsplit)
  change H.valuation L (sourceStepCoordinate P x hx) ≤ 1
  exact hle

/-- Evaluating the successor equation identifies its Artin--Schreier value
with the literal source right-hand side at the parent residue value. -/
theorem sourceSplitUpperRationalPlace_evaluate_sourceStepCoordinate_wValue
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    galoisBaseWValue
        ((sourceSplitUpperRationalPlace Q P x hx hregular hsplit c).evaluateRegular
          (sourceStepCoordinate P x hx)
          (sourceSplitAbovePlace_sourceStepCoordinate_regular
            Q P x hx hregular hsplit c)) =
      sourceStepRhs (Q.evaluateRegular x hregular) := by
  let U := sourceSplitUpperRationalPlace Q P x hx hregular hsplit c
  let y := sourceStepCoordinate P x hx
  let r := sourceStepRhs x
  have hyregular := sourceSplitAbovePlace_sourceStepCoordinate_regular
    Q P x hx hregular hsplit c
  have hrregular := sourceStepRhs_regularAt_of_splitValue
    Q x hregular hsplit
  have hrupper := sourceSplitAbovePlace_sourceStepEmbedding_regular
    Q P x hx c r hrregular
  let yO : U.place.valuationRing :=
    ⟨y, (GlobalPlace.mem_valuationRing_iff U.place y).mpr hyregular⟩
  let rO : U.place.valuationRing :=
    ⟨sourceStepEmbedding P x hx r,
      (GlobalPlace.mem_valuationRing_iff U.place _).mpr hrupper⟩
  have hequation : yO ^ 16 + yO = rO := by
    apply Subtype.ext
    exact sourceStepCoordinate_equation P x hx
  have hevaluate := congrArg U.evaluate hequation
  change galoisBaseWValue (U.evaluate yO) = _
  rw [galoisBaseWValue_eq]
  calc
    U.evaluate yO ^ 16 + U.evaluate yO = U.evaluate rO := by
      simpa only [map_add, map_pow] using hevaluate
    _ = Q.evaluateRegular r hrregular :=
      sourceSplitUpperRationalPlace_evaluate_sourceStepEmbedding
        Q P x hx hregular hsplit c r hrregular
    _ = sourceStepRhs (Q.evaluateRegular x hregular) :=
      sourceStepRhs_evaluateRegular Q x hregular hsplit

/-- The evaluated successor coordinate again satisfies the exact nonzero
split condition. -/
theorem sourceSplitUpperRationalPlace_evaluate_sourceStepCoordinate_split
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    galoisBaseWValue
        ((sourceSplitUpperRationalPlace Q P x hx hregular hsplit c).evaluateRegular
          (sourceStepCoordinate P x hx)
          (sourceSplitAbovePlace_sourceStepCoordinate_regular
            Q P x hx hregular hsplit c)) ≠ 0 := by
  rw [sourceSplitUpperRationalPlace_evaluate_sourceStepCoordinate_wValue]
  exact sourceStepRhs_ne_zero_of_galoisBaseWValue_ne_zero
    (Q.evaluateRegular x hregular) hsplit

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
