import QEC.Coding.ExpanderCodes.LPSOriginalIntegerLevelMorphism

/-!
# Actual original integral level function fields and generic degree

For the existing original normal integer models, the genuine finite level
morphism preserves the generic point and induces its pullback on generic
stalks. Literal field-valued points identify this map, under the existing
glued function-field equivalences, with the original rational inclusion.
Its generic degree is the original relative index, hence p+1 at a coprime
prime level. No map comparison or degree is supplied as an assumption.

These are internal derived prerequisites of the original modular-curve route
motivated by pinned PK22 main.tex ex:Xpq (lines484–486). They are not claimed
as explicit public statements of that passage. The exact public th:qLDPC
(lines231–238), node pk-good-qldpc and parent issue449 remain unproved here.
This proves no special-fibre degree, second integral Hecke map, smooth good
reduction, Frobenius/Weil estimate or full-level representation spectrum.
-/

namespace QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section

lemma lpsOriginalInjectiveSpecMap_generic
    (R S : CommRingCat) [IsDomain R] [IsDomain S]
    (f : R ⟶ S) (hf : Function.Injective f) :
    Spec.map f (genericPoint (Spec S)) = genericPoint (Spec R) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  change PrimeSpectrum.comap f.hom ⊥ = ⊥
  apply PrimeSpectrum.ext
  ext r
  change f.hom r = 0 ↔ r = 0
  exact ⟨fun h => hf (by simpa only [map_zero] using h), fun h => by rw [h, map_zero]⟩

lemma lpsOriginalIntegerNormalSchemeLevelChartMap_generic
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (b : Bool) :
    letI := lpsOriginalIntegerNormalSchemeChart_integral N hN b
    letI := lpsOriginalIntegerNormalSchemeChart_integral M hM b
    lpsOriginalIntegerNormalSchemeLevelChartMap N M hNM h4N hN hM b
      (genericPoint (lpsOriginalIntegerNormalSchemeChart M hM b)) =
        genericPoint (lpsOriginalIntegerNormalSchemeChart N hN b) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  cases b
  · let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalIntegerBaseToGeneratedField M hM).toAlgebra
    exact lpsOriginalInjectiveSpecMap_generic _ _
      (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM))
      (lpsOriginalIntegerNormalZeroLevelPullback_injective N M hNM h4N hN hM)
  · let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalIntegerReciprocalBaseToGeneratedField M hM).toAlgebra
    exact lpsOriginalInjectiveSpecMap_generic _ _
      (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityLevelPullback N M hNM h4N hN hM))
      (lpsOriginalIntegerNormalInfinityLevelPullback_injective N M hNM h4N hN hM)

lemma lpsOriginalIntegerNormalGluedForgetLevel_generic
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM
      (genericPoint (lpsOriginalIntegerNormalGluedScheme M hM)) =
        genericPoint (lpsOriginalIntegerNormalGluedScheme N hN) := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  let := lpsOriginalIntegerNormalSchemeChart_integral N hN false
  let := lpsOriginalIntegerNormalSchemeChart_integral M hM false
  let := lpsOriginalIntegerNormalGluedChartMap_openImmersion N hN false
  let := lpsOriginalIntegerNormalGluedChartMap_openImmersion M hM false
  have hm := genericPoint_eq_of_isOpenImmersion
    (lpsOriginalIntegerNormalGluedChartMap M hM false)
  have hn := genericPoint_eq_of_isOpenImmersion
    (lpsOriginalIntegerNormalGluedChartMap N hN false)
  have e := congrArg (fun f : lpsOriginalIntegerNormalSchemeChart M hM false ⟶
    lpsOriginalIntegerNormalGluedScheme N hN =>
      f (genericPoint (lpsOriginalIntegerNormalSchemeChart M hM false)))
      (lpsOriginalIntegerNormalGluedForgetLevel_chart N M hNM h4N hN hM false)
  simpa only [Scheme.Hom.comp_apply, hm, hn,
    lpsOriginalIntegerNormalSchemeLevelChartMap_generic] using e

def lpsOriginalIntegerNormalLevelFunctionFieldPullback
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    (lpsOriginalIntegerNormalGluedScheme N hN).functionField →+*
      (lpsOriginalIntegerNormalGluedScheme M hM).functionField := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  let f := lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM
  let X := lpsOriginalIntegerNormalGluedScheme N hN
  let Y := lpsOriginalIntegerNormalGluedScheme M hM
  have hη : f (genericPoint Y) = genericPoint X :=
    lpsOriginalIntegerNormalGluedForgetLevel_generic N M hNM h4N hN hM
  exact (eqToHom (congrArg X.presheaf.stalk hη.symm) ≫
    f.stalkMap (genericPoint Y)).hom

lemma lpsOriginalIntegerNormalLevelFunctionFieldPullback_injective
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    Function.Injective (lpsOriginalIntegerNormalLevelFunctionFieldPullback
      N M hNM h4N hN hM) := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  exact (lpsOriginalIntegerNormalLevelFunctionFieldPullback N M hNM h4N hN hM).injective

lemma lpsOriginalIntegerNormalGluedForgetLevel_dominant
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    IsDominant (lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM) := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  let X := lpsOriginalIntegerNormalGluedScheme N hN
  let Y := lpsOriginalIntegerNormalGluedScheme M hM
  let f := lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM
  rw [isDominant_iff, denseRange_iff_closure_range, ← Set.univ_subset_iff]
  rw [← isGenericPoint_def.mp (genericPoint_spec X)]
  apply closure_mono
  intro z hz
  have hz' : z = genericPoint X := Set.mem_singleton_iff.mp hz
  subst z
  exact ⟨genericPoint Y,
    lpsOriginalIntegerNormalGluedForgetLevel_generic N M hNM h4N hN hM⟩

lemma lpsOriginalIntegerNormalGluedForgetLevel_surjective
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    Function.Surjective (lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM) := by
  let := lpsOriginalIntegerNormalGluedForgetLevel_finite N M hNM h4N hN hM
  let := lpsOriginalIntegerNormalGluedForgetLevel_dominant N M hNM h4N hN hM
  let f := lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM
  exact (surjective_of_isDominant_of_isClosed_range f f.isClosedMap.isClosed_range).surj

/-- Actual field-valued generic point through the existing original zero chart. -/
def lpsOriginalIntegerNormalGeneratedFieldPoint
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Spec (.of (lpsOriginalGeneratedFunctionFieldQ N hN)) ⟶
      lpsOriginalIntegerNormalGluedScheme N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  exact Spec.map (CommRingCat.ofHom (algebraMap
    (lpsOriginalIntegerNormalZeroChart N hN)
      (lpsOriginalGeneratedFunctionFieldQ N hN))) ≫
        lpsOriginalIntegerNormalGluedChartMap N hN false

set_option backward.isDefEq.respectTransparency false in
/-- Literal original field points commute with the actual finite integral level morphism. -/
lemma lpsOriginalIntegerNormalGeneratedFieldPoint_level
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Spec.map (CommRingCat.ofHom
      (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom) ≫
      lpsOriginalIntegerNormalGeneratedFieldPoint N hN =
    lpsOriginalIntegerNormalGeneratedFieldPoint M hM ≫
      lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField M hM).toAlgebra
  have he : CommRingCat.ofHom (algebraMap
        (lpsOriginalIntegerNormalZeroChart N hN)
          (lpsOriginalGeneratedFunctionFieldQ N hN)) ≫
        CommRingCat.ofHom (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom =
      CommRingCat.ofHom (lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM) ≫
        CommRingCat.ofHom (algebraMap (lpsOriginalIntegerNormalZeroChart M hM)
          (lpsOriginalGeneratedFunctionFieldQ M hM)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    apply Subtype.ext
    rfl
  dsimp only [lpsOriginalIntegerNormalGeneratedFieldPoint]
  rw [Category.assoc, lpsOriginalIntegerNormalGluedForgetLevel_chart]
  change Spec.map (CommRingCat.ofHom
      (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap (lpsOriginalIntegerNormalZeroChart N hN)
        (lpsOriginalGeneratedFunctionFieldQ N hN))) ≫
          lpsOriginalIntegerNormalGluedChartMap N hN false) =
    Spec.map (CommRingCat.ofHom (algebraMap (lpsOriginalIntegerNormalZeroChart M hM)
      (lpsOriginalGeneratedFunctionFieldQ M hM))) ≫
      (Spec.map (CommRingCat.ofHom
        (lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM)) ≫
          lpsOriginalIntegerNormalGluedChartMap N hN false)
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, he]

lemma lpsOriginalSpecFromStalk_transport (X : Scheme) (x y : X) (h : x = y) :
    Spec.map (eqToHom (congrArg X.presheaf.stalk h)) ≫ X.fromSpecStalk x =
      X.fromSpecStalk y := by
  subst y
  simp

lemma lpsOriginalGenericStalkMap_fromSpec {X Y : Scheme}
    (f : Y ⟶ X) (y : Y) (x : X) (h : f y = x) :
    Spec.map (eqToHom (congrArg X.presheaf.stalk h.symm) ≫ f.stalkMap y) ≫
      X.fromSpecStalk x = Y.fromSpecStalk y ≫ f := by
  rw [Spec.map_comp, Category.assoc, lpsOriginalSpecFromStalk_transport,
    Scheme.SpecMap_stalkMap_fromSpecStalk]
  exact h.symm

universe u
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalFractionFieldEquiv_fieldPoint (R : CommRingCat.{u}) [IsDomain R]
    (F : Type u) [Field F] [Algebra R F] [IsFractionRing R F] :
    Spec.map (CommRingCat.ofHom (IsFractionRing.ringEquivOfRingEquiv
      (K := (Spec R).functionField) (L := F) (RingEquiv.refl R)).toRingHom) ≫
        (Spec R).fromSpecStalk (genericPoint (Spec R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
  rw [Spec.fromSpecStalk_eq', ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change IsFractionRing.ringEquivOfRingEquiv
    (K := (Spec R).functionField) (L := F) (RingEquiv.refl R)
      (algebraMap R (Spec R).functionField r) = algebraMap R F r
  simpa only [RingEquiv.refl_apply] using
    IsFractionRing.ringEquivOfRingEquiv_algebraMap
      (K := (Spec R).functionField) (L := F) (RingEquiv.refl R) r

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma lpsOriginalIntegerNormalGluedFunctionFieldEquiv_fieldPoint
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    Spec.map (CommRingCat.ofHom
      (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom) ≫
      (lpsOriginalIntegerNormalGluedScheme N hN).fromSpecStalk
        (genericPoint (lpsOriginalIntegerNormalGluedScheme N hN)) =
      lpsOriginalIntegerNormalGeneratedFieldPoint N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerBaseFractionMap.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalSchemeChart_integral N hN false
  let := lpsOriginalIntegerNormalGluedChartMap_openImmersion N hN false
  let X := lpsOriginalIntegerNormalGluedScheme N hN
  let R : CommRingCat := .of (lpsOriginalIntegerNormalZeroChart N hN)
  let : IsDomain R := inferInstanceAs (IsDomain (lpsOriginalIntegerNormalZeroChart N hN))
  let i := lpsOriginalIntegerNormalGluedChartMap N hN false
  let η := genericPoint (lpsOriginalIntegerNormalSchemeChart N hN false)
  have hη : i η = genericPoint X := genericPoint_eq_of_isOpenImmersion i
  let e := eqToIso (congrArg X.presheaf.stalk hη.symm) ≪≫ asIso (i.stalkMap η)
  let : IsFractionRing R (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    lpsOriginalIntegerNormalAffine_fractionField N hN
  let : Algebra R (Spec R).functionField := instAlgebraCarrierFunctionFieldSpec R
  let : IsFractionRing R (Spec R).functionField := functionField_isFractionRing_of_affine R
  let d := IsFractionRing.ringEquivOfRingEquiv
    (K := (Spec R).functionField) (L := lpsOriginalGeneratedFunctionFieldQ N hN)
      (RingEquiv.refl R)
  change Spec.map (e.hom ≫ CommRingCat.ofHom d.toRingHom) ≫
    X.fromSpecStalk (genericPoint X) =
      Spec.map (CommRingCat.ofHom (algebraMap R (lpsOriginalGeneratedFunctionFieldQ N hN))) ≫ i
  rw [Spec.map_comp, Category.assoc]
  have he : Spec.map e.hom ≫ X.fromSpecStalk (genericPoint X) =
      (Spec R).fromSpecStalk η ≫ i :=
    lpsOriginalGenericStalkMap_fromSpec i η (genericPoint X) hη
  rw [he, ← Category.assoc]
  exact congrArg (fun g => g ≫ i)
    (lpsOriginalFractionFieldEquiv_fieldPoint R (lpsOriginalGeneratedFunctionFieldQ N hN))

lemma lpsOriginalIntegerNormalLevelFunctionFieldPullback_fromSpec
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    Spec.map (CommRingCat.ofHom
      (lpsOriginalIntegerNormalLevelFunctionFieldPullback N M hNM h4N hN hM)) ≫
      (lpsOriginalIntegerNormalGluedScheme N hN).fromSpecStalk
        (genericPoint (lpsOriginalIntegerNormalGluedScheme N hN)) =
      (lpsOriginalIntegerNormalGluedScheme M hM).fromSpecStalk
        (genericPoint (lpsOriginalIntegerNormalGluedScheme M hM)) ≫
          lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  exact lpsOriginalGenericStalkMap_fromSpec
    (lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM)
    (genericPoint (lpsOriginalIntegerNormalGluedScheme M hM))
    (genericPoint (lpsOriginalIntegerNormalGluedScheme N hN))
    (lpsOriginalIntegerNormalGluedForgetLevel_generic N M hNM h4N hN hM)

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalLevelFunctionFieldPullback_naturality
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    (lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM).toRingHom.comp
      (lpsOriginalIntegerNormalLevelFunctionFieldPullback N M hNM h4N hN hM) =
    (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom.comp
      (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  have hc : CommRingCat.ofHom
      ((lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM).toRingHom.comp
        (lpsOriginalIntegerNormalLevelFunctionFieldPullback N M hNM h4N hN hM)) =
    CommRingCat.ofHom ((lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom.comp
      (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom) := by
    apply Spec.map_injective
    rw [← cancel_mono ((lpsOriginalIntegerNormalGluedScheme N hN).fromSpecStalk
      (genericPoint (lpsOriginalIntegerNormalGluedScheme N hN)))]
    change Spec.map (CommRingCat.ofHom
      (lpsOriginalIntegerNormalLevelFunctionFieldPullback N M hNM h4N hN hM) ≫
        CommRingCat.ofHom (lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM).toRingHom) ≫ _ =
      Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom ≫
        CommRingCat.ofHom (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom) ≫ _
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      lpsOriginalIntegerNormalLevelFunctionFieldPullback_fromSpec,
      lpsOriginalIntegerNormalGluedFunctionFieldEquiv_fieldPoint,
      ← Category.assoc, lpsOriginalIntegerNormalGluedFunctionFieldEquiv_fieldPoint]
    exact (lpsOriginalIntegerNormalGeneratedFieldPoint_level N M hNM h4N hN hM).symm
  exact congrArg CommRingCat.Hom.hom hc


lemma lpsOriginalIntermediateFieldInclusion_finrank
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A B : IntermediateField K L) (h : A ≤ B) :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    Module.finrank A B = A.relfinrank B := by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  change Module.finrank A (IntermediateField.extendScalars h) = A.relfinrank B
  exact (IntermediateField.relfinrank_eq_finrank_of_le h).symm

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalLevelFunctionField_finrank
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    letI := (lpsOriginalIntegerNormalLevelFunctionFieldPullback N M hNM h4N hN hM).toAlgebra
    Module.finrank (lpsOriginalIntegerNormalGluedScheme N hN).functionField
      (lpsOriginalIntegerNormalGluedScheme M hM).functionField =
        (lpsOriginalGeneratedFunctionFieldQ N hN).relfinrank
          (lpsOriginalGeneratedFunctionFieldQ M hM) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  let := (lpsOriginalIntegerNormalLevelFunctionFieldPullback N M hNM h4N hN hM).toAlgebra
  let := (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom.toAlgebra
  have he : (algebraMap (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGeneratedFunctionFieldQ M hM)).comp
        (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom =
    (lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM).toRingHom.comp
      (algebraMap (lpsOriginalIntegerNormalGluedScheme N hN).functionField
        (lpsOriginalIntegerNormalGluedScheme M hM).functionField) :=
    (lpsOriginalIntegerNormalLevelFunctionFieldPullback_naturality N M hNM h4N hN hM).symm
  rw [Algebra.finrank_eq_of_equiv_equiv
    (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN)
    (lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM) he]
  exact lpsOriginalIntermediateFieldInclusion_finrank
    (lpsOriginalGeneratedFunctionFieldQ N hN) (lpsOriginalGeneratedFunctionFieldQ M hM)
    (lpsOriginalGeneratedFunctionFieldQ_level_le N M hNM h4N hN hM)

lemma lpsOriginalIntegerNormalPrimeLevelFunctionField_finrank
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)
    letI := (lpsOriginalIntegerNormalLevelFunctionFieldPullback N (N*p)
      (dvd_mul_right N p) h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toAlgebra
    Module.finrank (lpsOriginalIntegerNormalGluedScheme N hN).functionField
      (lpsOriginalIntegerNormalGluedScheme (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)).functionField = p+1 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  let := (lpsOriginalIntegerNormalLevelFunctionFieldPullback N (N*p)
    (dvd_mul_right N p) h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toAlgebra
  rw [lpsOriginalIntegerNormalLevelFunctionField_finrank N (N*p)
    (dvd_mul_right N p) h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)]
  exact lpsOriginalPrimeGeneratedFunctionFieldQ_relfinrank N p hNp h4N hN

end
end QEC.Coding.TannerLiftedProduct
