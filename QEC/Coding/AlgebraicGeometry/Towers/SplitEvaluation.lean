import QEC.Coding.AlgebraicGeometry.Towers.RationalSplitting

/-!
# Evaluation along a split Garcia--Stichtenoth step

Regular base functions stay regular at every split upper place and retain
their residue values.  When the preceding distinguished coordinate has
nonzero residue, the successor coordinate is regular and again has nonzero
residue.  These are the exact invariants needed to iterate the sixteen-way
splitting construction; no level count or asymptotic conclusion is stored.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {K : Type*} [Field K] [Algebra F256 K]

private theorem stepEmbeddedCoordinate_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    stepFieldEmbedding P x hx x ≠ 0 := by
  have hxne : x ≠ 0 := by
    intro hzero
    subst x
    norm_num [GlobalPlace.order] at hx
  intro hmap
  apply hxne
  apply (stepFieldEmbedding P x hx).injective
  simp only [map_zero] at hmap ⊢
  exact hmap

/-- A function regular at the base rational place remains regular at every
split upper place. -/
theorem splitAbovePlace_stepEmbedding_regular
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier)
    (f : K) (hf : GlobalPlace.RegularAt Q.place f) :
    GlobalPlace.RegularAt (splitAbovePlace Q P x hx c)
      (stepFieldEmbedding P x hx f) := by
  let O := Q.place.valuationRing
  let S := SplitIntegralClosure Q P x hx
  let L := StepField P x hx
  let H := splitUpperHeightOne Q P x hx c
  let fO : O :=
    ⟨f, (GlobalPlace.mem_valuationRing_iff Q.place f).mpr hf⟩
  have hle := H.valuation_le_one (K := L) (algebraMap O S fO)
  change H.valuation L (stepFieldEmbedding P x hx f) ≤ 1
  exact hle

/-- Evaluation of an embedded regular base function agrees with its original
rational-place evaluation. -/
theorem splitUpperRationalPlace_evaluate_stepEmbedding
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier)
    (f : K) (hf : GlobalPlace.RegularAt Q.place f) :
    (splitUpperRationalPlace Q P x hx hregular c).evaluateRegular
        (stepFieldEmbedding P x hx f)
        (splitAbovePlace_stepEmbedding_regular Q P x hx c f hf) =
      Q.evaluateRegular f hf := by
  let O := Q.place.valuationRing
  let S := SplitIntegralClosure Q P x hx
  let L := StepField P x hx
  let H := splitUpperHeightOne Q P x hx c
  let U := splitUpperRationalPlace Q P x hx hregular c
  let m : Ideal O := IsLocalRing.maximalIdeal O
  letI : H.asIdeal.LiesOver m := by
    change ((splitUpperPrime Q P x hx c).1).LiesOver m
    infer_instance
  let fO : O :=
    ⟨f, (GlobalPlace.mem_valuationRing_iff Q.place f).mpr hf⟩
  let a : F256 := Q.evaluateRegular f hf
  let fU : U.place.valuationRing :=
    ⟨stepFieldEmbedding P x hx f,
      (GlobalPlace.mem_valuationRing_iff U.place _).mpr
        (splitAbovePlace_stepEmbedding_regular Q P x hx c f hf)⟩
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
    (stepFieldEmbedding P x hx f - algebraMap F256 L a) < 1
  simp only [map_sub, IsScalarTower.algebraMap_apply] at hlt ⊢
  exact hlt

/-- The integral auxiliary Artin--Schreier coordinate is regular at every
split upper place. -/
theorem splitAbovePlace_auxiliaryCoordinate_regular
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier) :
    GlobalPlace.RegularAt (splitAbovePlace Q P x hx c)
      (stepAuxiliaryCoordinate P x hx) := by
  let L := StepField P x hx
  let H := splitUpperHeightOne Q P x hx c
  have hle := H.valuation_le_one (K := L)
    (splitIntegralAuxiliaryCoordinate Q P x hx hregular)
  change H.valuation L (stepAuxiliaryCoordinate P x hx) ≤ 1
  exact hle

private theorem splitAbovePlace_embeddedCoordinate_valuation_eq_one
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hvalue : Q.evaluateRegular x hregular ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    (splitAbovePlace Q P x hx c).valuation
        (stepFieldEmbedding P x hx x) = 1 := by
  let U := splitUpperRationalPlace Q P x hx hregular c
  have hxregular := splitAbovePlace_stepEmbedding_regular
    Q P x hx c x hregular
  have hxevaluate := splitUpperRationalPlace_evaluate_stepEmbedding
    Q P x hx hregular c x hregular
  have hxevaluate_ne : U.evaluateRegular
      (stepFieldEmbedding P x hx x) hxregular ≠ 0 := by
    rw [hxevaluate]
    exact hvalue
  have hxnotlt : ¬U.place.valuation (stepFieldEmbedding P x hx x) < 1 := by
    intro hxlt
    apply hxevaluate_ne
    erw [U.evaluateRegular_eq_zero_iff]
    rw [Valuation.mem_maximalIdeal_iff]
    exact hxlt
  exact le_antisymm hxregular (not_lt.mp hxnotlt)

/-- A nonzero base residue makes the successor distinguished coordinate
regular at every split upper place. -/
theorem splitAbovePlace_stepDistinguishedCoordinate_regular
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hvalue : Q.evaluateRegular x hregular ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    GlobalPlace.RegularAt (splitAbovePlace Q P x hx c)
      (stepDistinguishedCoordinate P x hx) := by
  let L := StepField P x hx
  let H := splitUpperHeightOne Q P x hx c
  have hz := splitAbovePlace_auxiliaryCoordinate_regular
    Q P x hx hregular c
  have hxval := splitAbovePlace_embeddedCoordinate_valuation_eq_one
    Q P x hx hregular hvalue c
  have hxval' : H.valuation L (stepFieldEmbedding P x hx x) = 1 := hxval
  have hz' : H.valuation L (stepAuxiliaryCoordinate P x hx) ≤ 1 := hz
  change H.valuation L
    (stepAuxiliaryCoordinate P x hx /
      stepFieldEmbedding P x hx x) ≤ 1
  rw [div_eq_mul_inv, (H.valuation L).map_mul, (H.valuation L).map_inv,
    hxval',
    inv_one, mul_one]
  exact hz'

/-- The successor distinguished coordinate has nonzero residue at every
split upper rational place. -/
theorem splitUpperRationalPlace_evaluate_stepDistinguishedCoordinate_ne_zero
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hvalue : Q.evaluateRegular x hregular ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    (splitUpperRationalPlace Q P x hx hregular c).evaluateRegular
        (stepDistinguishedCoordinate P x hx)
        (splitAbovePlace_stepDistinguishedCoordinate_regular
          Q P x hx hregular hvalue c) ≠ 0 := by
  let L := StepField P x hx
  let H := splitUpperHeightOne Q P x hx c
  let U := splitUpperRationalPlace Q P x hx hregular c
  let y := stepDistinguishedCoordinate P x hx
  let z := stepAuxiliaryCoordinate P x hx
  let xL := stepFieldEmbedding P x hx x
  have hyregular := splitAbovePlace_stepDistinguishedCoordinate_regular
    Q P x hx hregular hvalue c
  have hxval := splitAbovePlace_embeddedCoordinate_valuation_eq_one
    Q P x hx hregular hvalue c
  intro hyevaluate
  have hylt : H.valuation L y < 1 := by
    have hymem : (⟨y,
        (GlobalPlace.mem_valuationRing_iff U.place y).mpr hyregular⟩ :
          U.place.valuationRing) ∈
        IsLocalRing.maximalIdeal U.place.valuationRing :=
      (U.evaluateRegular_eq_zero_iff y hyregular).1 hyevaluate
    rw [Valuation.mem_maximalIdeal_iff] at hymem
    exact hymem
  have hxL_ne : xL ≠ 0 := stepEmbeddedCoordinate_ne_zero P x hx
  have hxval' : H.valuation L xL = 1 := hxval
  have hyx : y * xL = z := by
    dsimp [y, z, xL]
    rw [stepDistinguishedCoordinate]
    exact div_mul_cancel₀ _ hxL_ne
  have hzlt : H.valuation L z < 1 := by
    calc
      H.valuation L z = H.valuation L (y * xL) := by rw [hyx]
      _ = H.valuation L y * H.valuation L xL := (H.valuation L).map_mul _ _
      _ = H.valuation L y := by rw [hxval', mul_one]
      _ < 1 := hylt
  have hzpowlt : H.valuation L (z ^ 16) < 1 := by
    rw [(H.valuation L).map_pow]
    exact pow_lt_one₀ zero_le' hzlt (by norm_num)
  have hleftlt : H.valuation L (z ^ 16 + z) < 1 :=
    lt_of_le_of_lt ((H.valuation L).map_add _ _) (max_lt hzpowlt hzlt)
  have hright : H.valuation L (xL ^ 17) = 1 := by
    rw [(H.valuation L).map_pow, hxval', one_pow]
  have hequation : z ^ 16 + z = xL ^ 17 := by
    exact stepAuxiliaryCoordinate_artinSchreier P x hx
  rw [hequation, hright] at hleftlt
  exact lt_irrefl 1 hleftlt

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
