import QEC.Coding.ExpanderCodes.LPSOriginalRationalHeckePullback
import QEC.Coding.ExpanderCodes.LPSOriginalIntegerModelFunctionField

/-!
# LPSOriginalIntegerLevelMorphism

Construct the first finite level morphism on the same original normal integer
models. The actual inclusion Q(j,j_N) into Q(j,j_M) fixes the embedded Q(j).
It therefore induces coefficient-compatible maps of the zero, infinity and
Laurent integral closures. Their overlap identities produce actual Spec maps
and a morphism between the existing two-chart glued models. The chart formulas
prove factorization of the projective j-map and compatibility over Spec Z.
Finiteness follows from the already proved finite upper j-map and separated
lower j-map; no map, glue condition or finiteness conclusion is supplied.

The numeric assumptions are positive levels N and M, N dividing M and
4 dividing N. This derived internal original-family API follows pinned PK22
main.tex ex:Xpq (484–486). Exact public th:qLDPC (231–238), node pk-good-qldpc,
remains unchanged and unproved. This does not establish the second integral
Hecke map, scheme function-field pullback or geometric degree, smooth good
reduction, Frobenius/Weil comparison, full-level/every-representation spectra
or the arbitrary-finite-field/every-rate explicit qLDPC family.
-/

namespace QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

def lpsOriginalRationalLevelInclusion
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGeneratedFunctionFieldQ N hN →ₐ[FractionRing (Polynomial ℚ)]
      lpsOriginalGeneratedFunctionFieldQ M hM := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact IntermediateField.inclusion
    (lpsOriginalGeneratedFunctionFieldQ_level_le N M hNM h4N hN hM)

lemma lpsOriginalRationalLevelInclusion_coe
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (x : lpsOriginalGeneratedFunctionFieldQ N hN) :
    ((lpsOriginalRationalLevelInclusion N M hNM h4N hN hM x :
      lpsOriginalGeneratedFunctionFieldQ M hM) : LPSOriginalHolomorphicFractionField) =
      (x : LPSOriginalHolomorphicFractionField) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact IntermediateField.coe_inclusion
    (lpsOriginalGeneratedFunctionFieldQ_level_le N M hNM h4N hN hM) x

def lpsOriginalIntegerNormalZeroLevelPullback
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalIntegerNormalZeroChart N hN →+*
      lpsOriginalIntegerNormalZeroChart M hM := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField M hM).toAlgebra
  let f : lpsOriginalGeneratedFunctionFieldQ N hN →ₐ[Polynomial ℤ]
      lpsOriginalGeneratedFunctionFieldQ M hM :=
    { (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom with
      commutes' := fun P => by apply Subtype.ext; rfl }
  exact f.mapIntegralClosure.toRingHom

def lpsOriginalIntegerNormalInfinityLevelPullback
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalIntegerNormalInfinityChart N hN →+*
      lpsOriginalIntegerNormalInfinityChart M hM := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField M hM).toAlgebra
  let f : lpsOriginalGeneratedFunctionFieldQ N hN →ₐ[Polynomial ℤ]
      lpsOriginalGeneratedFunctionFieldQ M hM :=
    { (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom with
      commutes' := fun P => by apply Subtype.ext; rfl }
  exact f.mapIntegralClosure.toRingHom

def lpsOriginalIntegerNormalLaurentLevelPullback
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalIntegerNormalLaurentChart N hN →+*
      lpsOriginalIntegerNormalLaurentChart M hM := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  letI := (lpsOriginalIntegerLaurentBaseToGeneratedField M hM).toAlgebra
  let f : lpsOriginalGeneratedFunctionFieldQ N hN →ₐ[LaurentPolynomial ℤ]
      lpsOriginalGeneratedFunctionFieldQ M hM :=
    { (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom with
      commutes' := fun P => by apply Subtype.ext; rfl }
  exact f.mapIntegralClosure.toRingHom

lemma lpsOriginalIntegerNormalZeroLevelPullback_coe
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (x : lpsOriginalIntegerNormalZeroChart N hN) :
    (((lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM x :
      lpsOriginalIntegerNormalZeroChart M hM) :
      lpsOriginalGeneratedFunctionFieldQ M hM) : LPSOriginalHolomorphicFractionField) =
      ((x : lpsOriginalGeneratedFunctionFieldQ N hN) :
        LPSOriginalHolomorphicFractionField) := by
  exact lpsOriginalRationalLevelInclusion_coe N M hNM h4N hN hM
    (x : lpsOriginalGeneratedFunctionFieldQ N hN)

lemma lpsOriginalIntegerNormalInfinityLevelPullback_coe
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (x : lpsOriginalIntegerNormalInfinityChart N hN) :
    (((lpsOriginalIntegerNormalInfinityLevelPullback N M hNM h4N hN hM x :
      lpsOriginalIntegerNormalInfinityChart M hM) :
      lpsOriginalGeneratedFunctionFieldQ M hM) : LPSOriginalHolomorphicFractionField) =
      ((x : lpsOriginalGeneratedFunctionFieldQ N hN) :
        LPSOriginalHolomorphicFractionField) := by
  exact lpsOriginalRationalLevelInclusion_coe N M hNM h4N hN hM
    (x : lpsOriginalGeneratedFunctionFieldQ N hN)

lemma lpsOriginalIntegerNormalLaurentLevelPullback_coe
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (x : lpsOriginalIntegerNormalLaurentChart N hN) :
    (((lpsOriginalIntegerNormalLaurentLevelPullback N M hNM h4N hN hM x :
      lpsOriginalIntegerNormalLaurentChart M hM) :
      lpsOriginalGeneratedFunctionFieldQ M hM) : LPSOriginalHolomorphicFractionField) =
      ((x : lpsOriginalGeneratedFunctionFieldQ N hN) :
        LPSOriginalHolomorphicFractionField) := by
  exact lpsOriginalRationalLevelInclusion_coe N M hNM h4N hN hM
    (x : lpsOriginalGeneratedFunctionFieldQ N hN)

lemma lpsOriginalIntegerNormalZeroLevelPullback_overlap
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    (lpsOriginalIntegerNormalZeroToLaurent M hM).comp
      (lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM) =
    (lpsOriginalIntegerNormalLaurentLevelPullback N M hNM h4N hN hM).comp
      (lpsOriginalIntegerNormalZeroToLaurent N hN) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  rfl

lemma lpsOriginalIntegerNormalInfinityLevelPullback_overlap
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    (lpsOriginalIntegerNormalInfinityToLaurent M hM).comp
      (lpsOriginalIntegerNormalInfinityLevelPullback N M hNM h4N hN hM) =
    (lpsOriginalIntegerNormalLaurentLevelPullback N M hNM h4N hN hM).comp
      (lpsOriginalIntegerNormalInfinityToLaurent N hN) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  rfl


def lpsOriginalIntegerNormalSchemeLevelChartMap
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (b : Bool) :
    lpsOriginalIntegerNormalSchemeChart M hM b ⟶
      lpsOriginalIntegerNormalSchemeChart N hN b := by
  cases b with
  | false => exact Spec.map (CommRingCat.ofHom
      (lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM))
  | true => exact Spec.map (CommRingCat.ofHom
      (lpsOriginalIntegerNormalInfinityLevelPullback N M hNM h4N hN hM))

def lpsOriginalIntegerNormalSchemeLevelOverlapMap
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    Spec (.of (lpsOriginalIntegerNormalLaurentChart M hM)) ⟶
      Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) :=
  Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalLaurentLevelPullback N M hNM h4N hN hM))

lemma lpsOriginalIntegerNormalSchemeLevelChartMap_overlap
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (b : Bool) :
    lpsOriginalIntegerNormalSchemeOverlapMap M hM b ≫
      lpsOriginalIntegerNormalSchemeLevelChartMap N M hNM h4N hN hM b =
    lpsOriginalIntegerNormalSchemeLevelOverlapMap N M hNM h4N hN hM ≫
      lpsOriginalIntegerNormalSchemeOverlapMap N hN b := by
  cases b
  · change Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroToLaurent M hM)) ≫
      Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM)) =
      Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalLaurentLevelPullback N M hNM h4N hN hM)) ≫
      Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroToLaurent N hN))
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f : lpsOriginalIntegerNormalZeroChart N hN →+*
      lpsOriginalIntegerNormalLaurentChart M hM => Spec.map (CommRingCat.ofHom f))
      (lpsOriginalIntegerNormalZeroLevelPullback_overlap N M hNM h4N hN hM)
  · change Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityToLaurent M hM)) ≫
      Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityLevelPullback N M hNM h4N hN hM)) =
      Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalLaurentLevelPullback N M hNM h4N hN hM)) ≫
      Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityToLaurent N hN))
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f : lpsOriginalIntegerNormalInfinityChart N hN →+*
      lpsOriginalIntegerNormalLaurentChart M hM => Spec.map (CommRingCat.ofHom f))
      (lpsOriginalIntegerNormalInfinityLevelPullback_overlap N M hNM h4N hN hM)

def lpsOriginalIntegerNormalLevelToLower
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (b : Bool) :
    lpsOriginalIntegerNormalSchemeChart M hM b ⟶
      lpsOriginalIntegerNormalGluedScheme N hN :=
  lpsOriginalIntegerNormalSchemeLevelChartMap N M hNM h4N hN hM b ≫
    lpsOriginalIntegerNormalGluedChartMap N hN b

lemma lpsOriginalIntegerNormalLevelToLower_overlap
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalIntegerNormalSchemeOverlapMap M hM false ≫
      lpsOriginalIntegerNormalLevelToLower N M hNM h4N hN hM false =
    lpsOriginalIntegerNormalSchemeOverlapMap M hM true ≫
      lpsOriginalIntegerNormalLevelToLower N M hNM h4N hN hM true := by
  unfold lpsOriginalIntegerNormalLevelToLower
  rw [← Category.assoc, lpsOriginalIntegerNormalSchemeLevelChartMap_overlap,
    Category.assoc, lpsOriginalIntegerNormalGluedOverlap_agreement,
    ← Category.assoc, ← lpsOriginalIntegerNormalSchemeLevelChartMap_overlap,
    Category.assoc]
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalLevelToLower_glueCondition
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    let D := (lpsOriginalIntegerNormalSchemeGlueData M hM).toGlueData
    ∀ a : Bool × Bool,
      D.diagram.fst a ≫ lpsOriginalIntegerNormalLevelToLower N M hNM h4N hN hM a.1 =
      D.diagram.snd a ≫ lpsOriginalIntegerNormalLevelToLower N M hNM h4N hN hM a.2 := by
  let D := (lpsOriginalIntegerNormalSchemeGlueData M hM).toGlueData
  change ∀ a : Bool × Bool,
    D.diagram.fst a ≫ lpsOriginalIntegerNormalLevelToLower N M hNM h4N hN hM a.1 =
      D.diagram.snd a ≫ lpsOriginalIntegerNormalLevelToLower N M hNM h4N hN hM a.2
  rintro ⟨i,j⟩
  change D.f i j ≫ lpsOriginalIntegerNormalLevelToLower N M hNM h4N hN hM i =
    (D.t i j ≫ D.f j i) ≫ lpsOriginalIntegerNormalLevelToLower N M hNM h4N hN hM j
  cases i <;> cases j
  · simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime]
  · have e : D.V (false,true)=Spec (.of (lpsOriginalIntegerNormalLaurentChart M hM)) := by
      simp [D,lpsOriginalIntegerNormalSchemeGlueData,
        CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerNormalSchemeGlueDataPrime]
    have h := congrArg (fun f : Spec (.of (lpsOriginalIntegerNormalLaurentChart M hM)) ⟶
      lpsOriginalIntegerNormalGluedScheme N hN => eqToHom e ≫ f)
      (lpsOriginalIntegerNormalLevelToLower_overlap N M hNM h4N hN hM)
    simpa [Category.assoc,eqToHom_trans_assoc,D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime] using h
  · have e : D.V (true,false)=Spec (.of (lpsOriginalIntegerNormalLaurentChart M hM)) := by
      simp [D,lpsOriginalIntegerNormalSchemeGlueData,
        CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerNormalSchemeGlueDataPrime]
    have h := congrArg (fun f : Spec (.of (lpsOriginalIntegerNormalLaurentChart M hM)) ⟶
      lpsOriginalIntegerNormalGluedScheme N hN => eqToHom e ≫ f)
      (lpsOriginalIntegerNormalLevelToLower_overlap N M hNM h4N hN hM).symm
    simpa [Category.assoc,eqToHom_trans_assoc,D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime] using h
  · simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime]

def lpsOriginalIntegerNormalGluedForgetLevel
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalIntegerNormalGluedScheme M hM ⟶
      lpsOriginalIntegerNormalGluedScheme N hN :=
  Multicoequalizer.desc _ _ (lpsOriginalIntegerNormalLevelToLower N M hNM h4N hN hM)
    (lpsOriginalIntegerNormalLevelToLower_glueCondition N M hNM h4N hN hM)

lemma lpsOriginalIntegerNormalGluedForgetLevel_chart
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (b : Bool) :
    lpsOriginalIntegerNormalGluedChartMap M hM b ≫
      lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM =
    lpsOriginalIntegerNormalSchemeLevelChartMap N M hNM h4N hN hM b ≫
      lpsOriginalIntegerNormalGluedChartMap N hN b :=
  Multicoequalizer.π_desc _ _ _ _ _


lemma lpsOriginalIntegerNormalSchemeLevelChartMap_toJ
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (b : Bool) :
    lpsOriginalIntegerNormalSchemeLevelChartMap N M hNM h4N hN hM b ≫
      lpsOriginalIntegerNormalChartToProjectiveJ N hN b =
    lpsOriginalIntegerNormalChartToProjectiveJ M hM b := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  cases b
  · let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalIntegerBaseToGeneratedField M hM).toAlgebra
    have he : CommRingCat.ofHom (algebraMap (Polynomial ℤ)
        (lpsOriginalIntegerNormalZeroChart N hN)) ≫
        CommRingCat.ofHom (lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM) =
        CommRingCat.ofHom (algebraMap (Polynomial ℤ)
          (lpsOriginalIntegerNormalZeroChart M hM)) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro P
      apply Subtype.ext
      apply Subtype.ext
      rfl
    change Spec.map (CommRingCat.ofHom
        (lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM)) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℤ)
        (lpsOriginalIntegerNormalZeroChart N hN))) ≫
        lpsOriginalIntegerProjectiveJChartMap false) =
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℤ)
        (lpsOriginalIntegerNormalZeroChart M hM))) ≫
        lpsOriginalIntegerProjectiveJChartMap false
    rw [← Category.assoc, ← Spec.map_comp, he]
  · let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalIntegerReciprocalBaseToGeneratedField M hM).toAlgebra
    have he : CommRingCat.ofHom (algebraMap (Polynomial ℤ)
        (lpsOriginalIntegerNormalInfinityChart N hN)) ≫
        CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityLevelPullback N M hNM h4N hN hM) =
        CommRingCat.ofHom (algebraMap (Polynomial ℤ)
          (lpsOriginalIntegerNormalInfinityChart M hM)) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro P
      apply Subtype.ext
      apply Subtype.ext
      rfl
    change Spec.map (CommRingCat.ofHom
        (lpsOriginalIntegerNormalInfinityLevelPullback N M hNM h4N hN hM)) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℤ)
        (lpsOriginalIntegerNormalInfinityChart N hN))) ≫
        lpsOriginalIntegerProjectiveJChartMap true) =
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℤ)
        (lpsOriginalIntegerNormalInfinityChart M hM))) ≫
        lpsOriginalIntegerProjectiveJChartMap true
    rw [← Category.assoc, ← Spec.map_comp, he]

lemma lpsOriginalIntegerNormalGluedForgetLevel_toJ
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM ≫
      lpsOriginalIntegerNormalGluedToProjectiveJ N hN =
    lpsOriginalIntegerNormalGluedToProjectiveJ M hM := by
  apply Multicoequalizer.hom_ext
  intro b
  change Bool at b
  change lpsOriginalIntegerNormalGluedChartMap M hM b ≫
      (lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM ≫
        lpsOriginalIntegerNormalGluedToProjectiveJ N hN) =
    lpsOriginalIntegerNormalGluedChartMap M hM b ≫
      lpsOriginalIntegerNormalGluedToProjectiveJ M hM
  rw [← Category.assoc, lpsOriginalIntegerNormalGluedForgetLevel_chart,
    Category.assoc, lpsOriginalIntegerNormalGluedToProjectiveJ_chart,
    lpsOriginalIntegerNormalGluedToProjectiveJ_chart]
  exact lpsOriginalIntegerNormalSchemeLevelChartMap_toJ N M hNM h4N hN hM b

lemma lpsOriginalIntegerNormalGluedForgetLevel_finite
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    IsFinite (lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM) := by
  let := lpsOriginalIntegerNormalGluedToProjectiveJ_finite N hN
  let := lpsOriginalIntegerNormalGluedToProjectiveJ_finite M hM
  let : IsFinite (lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM ≫
      lpsOriginalIntegerNormalGluedToProjectiveJ N hN) := by
    rw [lpsOriginalIntegerNormalGluedForgetLevel_toJ]
    infer_instance
  exact IsFinite.of_comp (lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM)
    (lpsOriginalIntegerNormalGluedToProjectiveJ N hN)

lemma lpsOriginalIntegerNormalGluedForgetLevel_toSpecZ
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM ≫
      lpsOriginalIntegerNormalGluedToSpecZ N hN =
    lpsOriginalIntegerNormalGluedToSpecZ M hM := by
  unfold lpsOriginalIntegerNormalGluedToSpecZ
  rw [← Category.assoc, lpsOriginalIntegerNormalGluedForgetLevel_toJ]


lemma lpsOriginalIntegerNormalZeroLevelPullback_injective
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    Function.Injective (lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg (fun z : lpsOriginalIntegerNormalZeroChart M hM =>
    ((z : lpsOriginalGeneratedFunctionFieldQ M hM) :
      LPSOriginalHolomorphicFractionField)) h
  simpa only [lpsOriginalIntegerNormalZeroLevelPullback_coe] using he

lemma lpsOriginalIntegerNormalInfinityLevelPullback_injective
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    Function.Injective (lpsOriginalIntegerNormalInfinityLevelPullback N M hNM h4N hN hM) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg (fun z : lpsOriginalIntegerNormalInfinityChart M hM =>
    ((z : lpsOriginalGeneratedFunctionFieldQ M hM) :
      LPSOriginalHolomorphicFractionField)) h
  simpa only [lpsOriginalIntegerNormalInfinityLevelPullback_coe] using he

lemma lpsOriginalIntegerNormalLaurentLevelPullback_injective
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    Function.Injective (lpsOriginalIntegerNormalLaurentLevelPullback N M hNM h4N hN hM) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg (fun z : lpsOriginalIntegerNormalLaurentChart M hM =>
    ((z : lpsOriginalGeneratedFunctionFieldQ M hM) :
      LPSOriginalHolomorphicFractionField)) h
  simpa only [lpsOriginalIntegerNormalLaurentLevelPullback_coe] using he

end
end QEC.Coding.TannerLiftedProduct
