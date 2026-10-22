import QEC.Coding.ExpanderCodes.LPSOriginalIntegralFricke

/-!
# Actual second integral Hecke map and generic degree

Construct the genuine second level map on the original normal integer
models as Fricke at the larger level, the existing finite forget-level map,
and Fricke at the smaller level. It is finite and over Z. At prime product
level its literal rational pullback is the already constructed dilation
map. Generic-point preservation, actual generic-stalk maps and the original
function-field equivalences prove naturality and generic degree p+1 for
a coprime prime extension with 4 dividing the smaller level.

No extension, covering, compatibility or degree is supplied as an assumption.
Fricke exchanges j and j_N; no linearity over the fixed Q(j) is claimed.
This is an internal derived prerequisite of the original modular-curve route
motivated by pinned PK22 main.tex ex:Xpq (484–486). Exact public th:qLDPC
(231–238), node pk-good-qldpc and parent issue449 remain unproved. Special-fibre
degree, complete smooth good reduction, Frobenius/Weil identities, principal
full-level representation spectra and the exact quantum family remain further
mathematical obligations.
-/

namespace QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section


def lpsOriginalRationalFrickeLevelPullback
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGeneratedFunctionFieldQ N hN →+* lpsOriginalGeneratedFunctionFieldQ M hM := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (lpsOriginalRationalFrickePullback M hM).comp
    ((lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom.comp
      (lpsOriginalRationalFrickePullback N hN))

/-- Fricke conjugation of the actual level inclusion is literally the original dilation map. -/
lemma lpsOriginalRationalFrickeLevelPullback_eq_hecke
    (N p : ℕ) [NeZero N] [NeZero p] (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalRationalFrickeLevelPullback N (N*p) (dvd_mul_right N p) h4N hN
      (Nat.mul_pos hN hp) = lpsOriginalRationalHeckePullback N p hN hp h4N := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let fN := lpsOriginalPositiveFractionPullback (lpsOriginalFrickeMatrix N hN)
    (lpsOriginalFrickeMatrix_pos N hN)
  let fM := lpsOriginalPositiveFractionPullback
    (lpsOriginalFrickeMatrix (N*p) (Nat.mul_pos hN hp))
    (lpsOriginalFrickeMatrix_pos (N*p) (Nat.mul_pos hN hp))
  have hg : Set.EqOn (fM.toRingHom.comp fN.toRingHom)
      (lpsOriginalDilationFractionPullback p hp).toRingHom
      {lpsOriginalJInFractionField,lpsOriginalJNInFractionField N hN} := by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with hy | hy
    · subst y
      change fM (fN lpsOriginalJInFractionField) =
        lpsOriginalDilationFractionPullback p hp lpsOriginalJInFractionField
      simp only [fN,fM,lpsOriginalPositiveFractionPullback_fricke_j,
        lpsOriginalDilationFractionPullback_j]
      exact lpsOriginalPositiveFractionPullback_fricke_product_jN N p hN hp
    · have he := Set.mem_singleton_iff.mp hy
      subst y
      change fM (fN (lpsOriginalJNInFractionField N hN)) =
        lpsOriginalDilationFractionPullback p hp (lpsOriginalJNInFractionField N hN)
      simp only [fN,fM,lpsOriginalPositiveFractionPullback_fricke_jN,
        lpsOriginalPositiveFractionPullback_fricke_j,lpsOriginalDilationFractionPullback_jN]
  apply RingHom.ext
  intro x
  apply Subtype.ext
  change fM (fN (x : LPSOriginalHolomorphicFractionField)) =
    lpsOriginalDilationFractionPullback p hp x
  apply RingHom.eqOn_field_closure hg
  rw [← lpsOriginalGeneratedFunctionFieldQ_toSubfield_eq_closure N hN]
  exact x.property

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalRationalFrickeLevelPullback_finrank
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI : Algebra (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGeneratedFunctionFieldQ M hM) :=
      (lpsOriginalRationalFrickeLevelPullback N M hNM h4N hN hM).toAlgebra
    letI : Module (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGeneratedFunctionFieldQ M hM) := Algebra.toModule
    Module.finrank (lpsOriginalGeneratedFunctionFieldQ N hN) (lpsOriginalGeneratedFunctionFieldQ M hM) =
      (lpsOriginalGeneratedFunctionFieldQ N hN).relfinrank (lpsOriginalGeneratedFunctionFieldQ M hM) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let f := lpsOriginalRationalFrickeLevelPullback N M hNM h4N hN hM
  let g := (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom
  let eN := lpsOriginalRationalFrickeEquiv N hN
  let eM := lpsOriginalRationalFrickeEquiv M hM
  have he : g.comp eN.toRingHom = eM.toRingHom.comp f := by
    apply RingHom.ext
    intro x
    change g (lpsOriginalRationalFrickePullback N hN x) =
      lpsOriginalRationalFrickePullback M hM
        (lpsOriginalRationalFrickePullback M hM (g (lpsOriginalRationalFrickePullback N hN x)))
    rw [lpsOriginalRationalFrickePullback_involutive]
  have hr := @Algebra.finrank_eq_of_equiv_equiv
    (lpsOriginalGeneratedFunctionFieldQ N hN) (lpsOriginalGeneratedFunctionFieldQ M hM)
    inferInstance inferInstance f.toAlgebra
    (lpsOriginalGeneratedFunctionFieldQ N hN) (lpsOriginalGeneratedFunctionFieldQ M hM)
    inferInstance inferInstance g.toAlgebra eN eM he
  exact hr.trans (lpsOriginalIntermediateFieldInclusion_finrank _ _
    (lpsOriginalGeneratedFunctionFieldQ_level_le N M hNM h4N hN hM))

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalRationalPrimeFrickeLevelPullback_finrank
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI : Algebra (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
      (lpsOriginalRationalFrickeLevelPullback N (N*p) (dvd_mul_right N p) h4N hN
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toAlgebra
    letI : Module (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)) := Algebra.toModule
    Module.finrank (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)) = p+1 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalRationalFrickeLevelPullback N (N*p) (dvd_mul_right N p) h4N hN
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toAlgebra
  rw [lpsOriginalRationalFrickeLevelPullback_finrank]
  exact lpsOriginalPrimeGeneratedFunctionFieldQ_relfinrank N p hNp h4N hN

/-- Actual second integral level map: Fricke at M, forget level, Fricke at N. -/
def lpsOriginalIntegerNormalGluedSecondLevelMap
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalIntegerNormalGluedScheme M hM ⟶ lpsOriginalIntegerNormalGluedScheme N hN :=
  (lpsOriginalIntegerNormalGluedFrickeIso M hM).hom ≫
    lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM ≫
      (lpsOriginalIntegerNormalGluedFrickeIso N hN).hom

lemma lpsOriginalIntegerNormalGluedSecondLevelMap_finite
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    IsFinite (lpsOriginalIntegerNormalGluedSecondLevelMap N M hNM h4N hN hM) := by
  let := lpsOriginalIntegerNormalGluedForgetLevel_finite N M hNM h4N hN hM
  unfold lpsOriginalIntegerNormalGluedSecondLevelMap
  infer_instance

lemma lpsOriginalIntegerNormalGluedFricke_generic
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    lpsOriginalIntegerNormalGluedFricke N hN
      (genericPoint (lpsOriginalIntegerNormalGluedScheme N hN)) =
        genericPoint (lpsOriginalIntegerNormalGluedScheme N hN) := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let : IsIso (lpsOriginalIntegerNormalGluedFricke N hN) :=
    inferInstanceAs (IsIso (lpsOriginalIntegerNormalGluedFrickeIso N hN).hom)
  exact genericPoint_eq_of_isOpenImmersion _

lemma lpsOriginalIntegerNormalGluedSecondLevelMap_generic
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    lpsOriginalIntegerNormalGluedSecondLevelMap N M hNM h4N hN hM
      (genericPoint (lpsOriginalIntegerNormalGluedScheme M hM)) =
        genericPoint (lpsOriginalIntegerNormalGluedScheme N hN) := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  simp only [lpsOriginalIntegerNormalGluedSecondLevelMap,
    lpsOriginalIntegerNormalGluedFrickeIso, Scheme.Hom.comp_apply,
    lpsOriginalIntegerNormalGluedFricke_generic, lpsOriginalIntegerNormalGluedForgetLevel_generic]

set_option backward.isDefEq.respectTransparency false in
/-- The second integral map really acts on the original function field by Fricke conjugation. -/
lemma lpsOriginalIntegerNormalGeneratedFieldPoint_secondLevel
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerNormalGeneratedFieldPoint M hM ≫
      lpsOriginalIntegerNormalGluedSecondLevelMap N M hNM h4N hN hM =
    Spec.map (CommRingCat.ofHom (lpsOriginalRationalFrickeLevelPullback N M hNM h4N hN hM)) ≫
      lpsOriginalIntegerNormalGeneratedFieldPoint N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let fN := lpsOriginalIntegerNormalGluedFricke N hN
  let fM := lpsOriginalIntegerNormalGluedFricke M hM
  let L := lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM
  let u := lpsOriginalIntegerNormalGeneratedFieldPoint M hM
  let v := lpsOriginalIntegerNormalGeneratedFieldPoint N hN
  let pN := Spec.map (CommRingCat.ofHom (lpsOriginalRationalFrickePullback N hN))
  let pM := Spec.map (CommRingCat.ofHom (lpsOriginalRationalFrickePullback M hM))
  let li := Spec.map (CommRingCat.ofHom (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom)
  have hm : u ≫ fM = pM ≫ u := lpsOriginalIntegerNormalGeneratedFieldPoint_fricke M hM
  have hl : u ≫ L = li ≫ v :=
    (lpsOriginalIntegerNormalGeneratedFieldPoint_level N M hNM h4N hN hM).symm
  have hn : v ≫ fN = pN ≫ v := lpsOriginalIntegerNormalGeneratedFieldPoint_fricke N hN
  have he : pM ≫ li ≫ pN =
      Spec.map (CommRingCat.ofHom (lpsOriginalRationalFrickeLevelPullback N M hNM h4N hN hM)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  change u ≫ (fM ≫ L ≫ fN) = _
  calc
    u ≫ (fM ≫ L ≫ fN) = (u ≫ fM) ≫ (L ≫ fN) := (Category.assoc _ _ _).symm
    _ = (pM ≫ u) ≫ (L ≫ fN) := congrArg (fun f => f ≫ (L ≫ fN)) hm
    _ = pM ≫ ((u ≫ L) ≫ fN) := by simp only [Category.assoc]
    _ = pM ≫ ((li ≫ v) ≫ fN) := congrArg (fun f => pM ≫ (f ≫ fN)) hl
    _ = pM ≫ (li ≫ (v ≫ fN)) := by rw [Category.assoc]
    _ = pM ≫ (li ≫ (pN ≫ v)) := congrArg (fun f => pM ≫ (li ≫ f)) hn
    _ = (pM ≫ li ≫ pN) ≫ v := by simp only [Category.assoc]
    _ = _ := congrArg (fun f => f ≫ v) he

/-- Actual generic-stalk pullback of the genuine finite second integral level morphism. -/
def lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    (lpsOriginalIntegerNormalGluedScheme N hN).functionField →+*
      (lpsOriginalIntegerNormalGluedScheme M hM).functionField := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  let f := lpsOriginalIntegerNormalGluedSecondLevelMap N M hNM h4N hN hM
  let X := lpsOriginalIntegerNormalGluedScheme N hN
  let Y := lpsOriginalIntegerNormalGluedScheme M hM
  have hη : f (genericPoint Y) = genericPoint X :=
    lpsOriginalIntegerNormalGluedSecondLevelMap_generic N M hNM h4N hN hM
  exact (eqToHom (congrArg X.presheaf.stalk hη.symm) ≫ f.stalkMap (genericPoint Y)).hom

lemma lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback_fromSpec
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    Spec.map (CommRingCat.ofHom
      (lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback N M hNM h4N hN hM)) ≫
      (lpsOriginalIntegerNormalGluedScheme N hN).fromSpecStalk
        (genericPoint (lpsOriginalIntegerNormalGluedScheme N hN)) =
      (lpsOriginalIntegerNormalGluedScheme M hM).fromSpecStalk
        (genericPoint (lpsOriginalIntegerNormalGluedScheme M hM)) ≫
          lpsOriginalIntegerNormalGluedSecondLevelMap N M hNM h4N hN hM := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  exact lpsOriginalGenericStalkMap_fromSpec
    (lpsOriginalIntegerNormalGluedSecondLevelMap N M hNM h4N hN hM)
    (genericPoint (lpsOriginalIntegerNormalGluedScheme M hM))
    (genericPoint (lpsOriginalIntegerNormalGluedScheme N hN))
    (lpsOriginalIntegerNormalGluedSecondLevelMap_generic N M hNM h4N hN hM)

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback_naturality
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    (lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM).toRingHom.comp
      (lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback N M hNM h4N hN hM) =
    (lpsOriginalRationalFrickeLevelPullback N M hNM h4N hN hM).comp
      (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  have hc : CommRingCat.ofHom
      ((lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM).toRingHom.comp
        (lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback N M hNM h4N hN hM)) =
    CommRingCat.ofHom ((lpsOriginalRationalFrickeLevelPullback N M hNM h4N hN hM).comp
      (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom) := by
    apply Spec.map_injective
    rw [← cancel_mono ((lpsOriginalIntegerNormalGluedScheme N hN).fromSpecStalk
      (genericPoint (lpsOriginalIntegerNormalGluedScheme N hN)))]
    change Spec.map (CommRingCat.ofHom
      (lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback N M hNM h4N hN hM) ≫
        CommRingCat.ofHom (lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM).toRingHom) ≫ _ =
      Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom ≫
        CommRingCat.ofHom (lpsOriginalRationalFrickeLevelPullback N M hNM h4N hN hM)) ≫ _
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback_fromSpec,
      lpsOriginalIntegerNormalGluedFunctionFieldEquiv_fieldPoint,
      ← Category.assoc, lpsOriginalIntegerNormalGluedFunctionFieldEquiv_fieldPoint]
    exact lpsOriginalIntegerNormalGeneratedFieldPoint_secondLevel N M hNM h4N hN hM
  exact congrArg CommRingCat.Hom.hom hc

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalSecondLevelFunctionField_finrank
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    letI := (lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback N M hNM h4N hN hM).toAlgebra
    Module.finrank (lpsOriginalIntegerNormalGluedScheme N hN).functionField
      (lpsOriginalIntegerNormalGluedScheme M hM).functionField =
        (lpsOriginalGeneratedFunctionFieldQ N hN).relfinrank (lpsOriginalGeneratedFunctionFieldQ M hM) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  let := (lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback N M hNM h4N hN hM).toAlgebra
  let := (lpsOriginalRationalFrickeLevelPullback N M hNM h4N hN hM).toAlgebra
  have he : (algebraMap (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGeneratedFunctionFieldQ M hM)).comp
        (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom =
    (lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM).toRingHom.comp
      (algebraMap (lpsOriginalIntegerNormalGluedScheme N hN).functionField
        (lpsOriginalIntegerNormalGluedScheme M hM).functionField) :=
    (lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback_naturality N M hNM h4N hN hM).symm
  rw [Algebra.finrank_eq_of_equiv_equiv
    (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN)
    (lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM) he]
  exact lpsOriginalRationalFrickeLevelPullback_finrank N M hNM h4N hN hM

lemma lpsOriginalIntegerNormalSecondPrimeLevelFunctionField_finrank
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)
    letI := (lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback N (N*p)
      (dvd_mul_right N p) h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toAlgebra
    Module.finrank (lpsOriginalIntegerNormalGluedScheme N hN).functionField
      (lpsOriginalIntegerNormalGluedScheme (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)).functionField = p+1 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  let := (lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback N (N*p)
    (dvd_mul_right N p) h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toAlgebra
  rw [lpsOriginalIntegerNormalSecondLevelFunctionField_finrank N (N*p)
    (dvd_mul_right N p) h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)]
  exact lpsOriginalPrimeGeneratedFunctionFieldQ_relfinrank N p hNp h4N hN

lemma lpsOriginalIntegerNormalGeneratedFieldPoint_secondHecke
    (N p : ℕ) [NeZero N] [NeZero p] (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerNormalGeneratedFieldPoint (N*p) (Nat.mul_pos hN hp) ≫
      lpsOriginalIntegerNormalGluedSecondLevelMap N (N*p) (dvd_mul_right N p) h4N hN
        (Nat.mul_pos hN hp) =
    Spec.map (CommRingCat.ofHom (lpsOriginalRationalHeckePullback N p hN hp h4N)) ≫
      lpsOriginalIntegerNormalGeneratedFieldPoint N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalIntegerNormalGeneratedFieldPoint_secondLevel,
    lpsOriginalRationalFrickeLevelPullback_eq_hecke]

/-- The genuine finite second map is over Z, hence defines integral correspondence data. -/
lemma lpsOriginalIntegerNormalGluedSecondLevelMap_overSpecZ
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalIntegerNormalGluedSecondLevelMap N M hNM h4N hN hM ≫
      lpsOriginalIntegerNormalGluedToSpecZ N hN = lpsOriginalIntegerNormalGluedToSpecZ M hM := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  let := lpsOriginalIntegerNormalGeneratedFieldPoint_dominant M hM
  apply ext_of_isDominant (lpsOriginalIntegerNormalGeneratedFieldPoint M hM)
  exact lpsOriginalIntegerSpecZ_hom_unique (lpsOriginalGeneratedFunctionFieldQ M hM) _ _

end
end QEC.Coding.TannerLiftedProduct
