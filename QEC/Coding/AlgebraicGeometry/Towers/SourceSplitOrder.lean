import QEC.Coding.AlgebraicGeometry.Towers.SourceRationalSplitting

import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Orders through a selected source recursion step

Every selected source upper prime is unramified.  Factoring a nonzero lower
function into a power of a DVR uniformizer times a unit therefore shows that
its normalized order is unchanged after the literal source-step embedding.

No recursive place family, normal-closure splitting, divisor, genus, or
asymptotic conclusion is stored here.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {K : Type*} [Field K] [Algebra F256 K]

private theorem sourceOrder_zpow
    {k L : Type*} [_root_.Field k] [Finite k] [_root_.Field L] [Algebra k L]
    (P : GlobalPlace k L) (z : L) (n : ℤ) :
    P.order (z ^ n) = n * P.order z := by
  unfold GlobalPlace.order
  rw [map_zpow₀, WithZero.log_zpow]
  simp only [smul_eq_mul]
  ring

private theorem sourceValuationRingUnit_order
    {k L : Type*} [_root_.Field k] [Finite k] [_root_.Field L] [Algebra k L]
    (P : GlobalPlace k L) (u : P.valuationRingˣ) :
    P.order ((u : P.valuationRing) : L) = 0 := by
  let u' : P.valuationRing.unitGroup :=
    P.valuationRing.unitGroupMulEquiv.symm u
  have hu' : P.valuation ((u' : Lˣ) : L) = 1 :=
    (Valuation.mem_unitGroup_iff L P.valuation (u' : Lˣ)).mp u'.property
  have hu : P.valuation (((u : P.valuationRing) : L)) = 1 := by
    simpa only [u', ValuationSubring.coe_unitGroupMulEquiv_symm_apply] using hu'
  unfold GlobalPlace.order
  rw [hu, WithZero.log_one]
  simp

private theorem sourceSplitAbovePlace_order_integral_eq_multiplicity
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier)
    {y : SourceSplitIntegralClosure Q P x hx} (hy : y ≠ 0) :
    (sourceSplitAbovePlace Q P x hx c).order
        (algebraMap (SourceSplitIntegralClosure Q P x hx)
          (SourceStepField P x hx) y) =
      (multiplicity (sourceSplitUpperHeightOne Q P x hx c).asIdeal
        (Ideal.span {y}) : ℤ) := by
  unfold sourceSplitAbovePlace GlobalPlace.order
  rw [(sourceSplitUpperHeightOne Q P x hx c).valuation_of_algebraMap,
    (sourceSplitUpperHeightOne Q P x hx c).intValuation_eq_exp_neg_multiplicity
      hy,
    WithZero.log_exp]
  ring

private theorem sourceSplitAbovePlace_order_integralUnit
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier)
    (u : Q.place.valuationRingˣ) :
    (sourceSplitAbovePlace Q P x hx c).order
        (algebraMap (SourceSplitIntegralClosure Q P x hx)
          (SourceStepField P x hx)
          (algebraMap Q.place.valuationRing
            (SourceSplitIntegralClosure Q P x hx)
            (u : Q.place.valuationRing))) = 0 := by
  let S := SourceSplitIntegralClosure Q P x hx
  let H := sourceSplitUpperHeightOne Q P x hx c
  let uS : Sˣ := Units.map (algebraMap Q.place.valuationRing S) u
  have huS_ne : (uS : S) ≠ 0 := uS.ne_zero
  change (sourceSplitAbovePlace Q P x hx c).order
    (algebraMap S (SourceStepField P x hx) (uS : S)) = 0
  rw [sourceSplitAbovePlace_order_integral_eq_multiplicity
    Q P x hx c huS_ne]
  have huS_unit : IsUnit (uS : S) := uS.isUnit
  rw [Ideal.span_singleton_eq_top.mpr huS_unit]
  norm_cast
  have hH_nonunit : ¬IsUnit H.asIdeal := by
    rw [Ideal.isUnit_iff]
    exact H.isPrime.ne_top
  simpa only [Ideal.one_eq_top] using multiplicity_of_one_right hH_nonunit

private theorem sourceSplitAbovePlace_order_embeddedUniformizer
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    (sourceSplitAbovePlace Q P x hx c).order
        (sourceStepEmbedding P x hx
          (algebraMap Q.place.valuationRing K
            Q.place.uniformizerInValuationRing)) = 1 := by
  let O := Q.place.valuationRing
  let S := SourceSplitIntegralClosure Q P x hx
  let L := SourceStepField P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let H := sourceSplitUpperHeightOne Q P x hx c
  let R : Ideal S := H.asIdeal
  let t : O := Q.place.uniformizerInValuationRing
  let G := L ≃ₐ[K] L
  letI : IsDiscreteValuationRing O :=
    Q.place.valuationRing_isDiscreteValuationRing
  letI : MulSemiringAction G S :=
    IsIntegralClosure.MulSemiringAction O K L S
  letI : IsGaloisGroup G O S :=
    IsGaloisGroup.of_isFractionRing G O S K L
  letI : R.IsPrime := H.isPrime
  letI : R.LiesOver m := by
    change ((sourceSplitUpperPrime Q P x hx c).1).LiesOver m
    infer_instance
  have hm_ne_bot : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap_ne_bot : Ideal.map (algebraMap O S) m ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm_ne_bot
  have hm_span : m = Ideal.span ({t} : Set O) := by
    simpa only [O, m, t] using Q.place.maximalIdeal_eq_span_uniformizer
  have ht_irreducible : Irreducible t :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr hm_span
  have ht_ne : algebraMap O S t ≠ 0 := by
    simpa only [map_zero] using
      (FaithfulSMul.algebraMap_injective O S).ne ht_irreducible.ne_zero
  have hspan : Ideal.span ({algebraMap O S t} : Set S) =
      Ideal.map (algebraMap O S) m := by
    calc
      Ideal.span ({algebraMap O S t} : Set S) =
          Ideal.map (algebraMap O S) (Ideal.span ({t} : Set O)) := by
        rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.map (algebraMap O S) m := by rw [← hm_span]
  change (sourceSplitAbovePlace Q P x hx c).order
    (algebraMap S L (algebraMap O S t)) = 1
  rw [sourceSplitAbovePlace_order_integral_eq_multiplicity
    Q P x hx c ht_ne]
  norm_cast
  calc
    multiplicity R (Ideal.span ({algebraMap O S t} : Set S)) =
        multiplicity R (Ideal.map (algebraMap O S) m) := by rw [hspan]
    _ = m.ramificationIdx' R :=
      (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
        hmap_ne_bot H.isPrime).symm
    _ = m.ramificationIdxIn S := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx m R hm_ne_bot]
      exact (Ideal.ramificationIdxIn_eq_ramificationIdx m R G).symm
    _ = 1 := by
      simpa only [O, S, m] using
        sourceSplit_ramificationIdxIn_eq_one Q P x hx hregular hsplit

/-- At a selected source upper place, normalized order restricts unchanged to
every nonzero lower-field element. -/
theorem sourceSplitAbovePlace_order_sourceStepEmbedding
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier)
    (y : K) (hy : y ≠ 0) :
    (sourceSplitAbovePlace Q P x hx c).order
        (sourceStepEmbedding P x hx y) = Q.place.order y := by
  let O := Q.place.valuationRing
  let S := SourceSplitIntegralClosure Q P x hx
  let L := SourceStepField P x hx
  let t : O := Q.place.uniformizerInValuationRing
  letI : IsDiscreteValuationRing O :=
    Q.place.valuationRing_isDiscreteValuationRing
  have ht_irreducible : Irreducible t :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr (by
      simpa only [O, t] using Q.place.maximalIdeal_eq_span_uniformizer)
  obtain ⟨n, u, hyfactor⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      ht_irreducible hy
  have hyfactor' :
      y = algebraMap O K (u : O) * algebraMap O K t ^ n := by
    simpa only [Units.smul_def, Algebra.smul_def] using hyfactor
  have ht_lower : Q.place.order (algebraMap O K t) = 1 := by
    change Q.place.order Q.place.uniformizer = 1
    exact Q.place.order_uniformizer
  have hu_lower : Q.place.order (algebraMap O K (u : O)) = 0 := by
    exact sourceValuationRingUnit_order Q.place u
  have htK_ne : algebraMap O K t ≠ 0 := by
    intro ht0
    apply ht_irreducible.ne_zero
    apply Subtype.ext
    exact ht0
  have huK_ne : algebraMap O K (u : O) ≠ 0 := by
    intro hu0
    apply u.ne_zero
    apply Subtype.ext
    exact hu0
  have hn_lower : Q.place.order y = n := by
    rw [hyfactor', Q.place.order_mul huK_ne (zpow_ne_zero n htK_ne),
      sourceOrder_zpow, hu_lower, ht_lower]
    ring
  have hu_map :
      sourceStepEmbedding P x hx (algebraMap O K (u : O)) =
        algebraMap S L (algebraMap O S (u : O)) := by
    rfl
  have ht_map :
      sourceStepEmbedding P x hx (algebraMap O K t) =
        algebraMap S L (algebraMap O S t) := by
    rfl
  have hyfactorUpper := congrArg (sourceStepEmbedding P x hx) hyfactor'
  simp only [map_mul, map_zpow₀] at hyfactorUpper
  have hu_upper :
      (sourceSplitAbovePlace Q P x hx c).order
          (sourceStepEmbedding P x hx (algebraMap O K (u : O))) = 0 := by
    rw [hu_map]
    exact sourceSplitAbovePlace_order_integralUnit Q P x hx c u
  have ht_upper :
      (sourceSplitAbovePlace Q P x hx c).order
          (sourceStepEmbedding P x hx (algebraMap O K t)) = 1 := by
    exact sourceSplitAbovePlace_order_embeddedUniformizer
      Q P x hx hregular hsplit c
  calc
    (sourceSplitAbovePlace Q P x hx c).order
        (sourceStepEmbedding P x hx y) =
      (sourceSplitAbovePlace Q P x hx c).order
        (sourceStepEmbedding P x hx (algebraMap O K (u : O)) *
          sourceStepEmbedding P x hx (algebraMap O K t) ^ n) := by
      rw [hyfactorUpper]
    _ = (sourceSplitAbovePlace Q P x hx c).order
          (sourceStepEmbedding P x hx (algebraMap O K (u : O))) +
        (sourceSplitAbovePlace Q P x hx c).order
          (sourceStepEmbedding P x hx (algebraMap O K t) ^ n) := by
      apply GlobalPlace.order_mul
      · have hne := (sourceStepEmbedding P x hx).injective.ne huK_ne
        simp only [map_zero] at hne
        exact hne
      · exact zpow_ne_zero n (by
          have hne := (sourceStepEmbedding P x hx).injective.ne htK_ne
          simp only [map_zero] at hne
          exact hne)
    _ = 0 + n * 1 := by rw [sourceOrder_zpow, hu_upper, ht_upper]
    _ = Q.place.order y := by rw [hn_lower]; ring

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
