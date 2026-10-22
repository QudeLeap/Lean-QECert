import QEC.Coding.AlgebraicGeometry.Towers.NormalizedCompositumEdges
import QEC.Coding.AlgebraicGeometry.Places.HeightOneOrderTransport

/-!
# Changing the initial local model of a literal refinement

The source pyramid uses different rational fields at its bottom vertices.
Equal normalized orders at the final ambient prime determine the orders at
all intermediate contractions. Thus a chain constructed over a localized
intermediate base can be used in the original ambient integral model.
-/

open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

variable (A B F K E : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [_root_.Field F] [_root_.Field K] [_root_.Field E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
    [Algebra A F] [IsFractionRing A F] [Algebra A E] [IsScalarTower A F E]
    [Algebra B K] [IsFractionRing B K] [Algebra B E] [IsScalarTower B K E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    [Algebra F256 F] [Algebra F256 K] [Algebra F256 E]
    [IsScalarTower F256 F E] [IsScalarTower F256 K E]
    [Module.Finite A (integralClosure A E)] [Module.Finite B (integralClosure B E)]
    [IsDedekindDomain (integralClosure A E)] [IsDedekindDomain (integralClosure B E)]
    [IsFractionRing (integralClosure A E) E] [IsFractionRing (integralClosure B E) E]
    (QA : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
    (QB : IsDedekindDomain.HeightOneSpectrum (integralClosure B E))

local notation "CA" => IntermediateIntegralModels.Model A F E
local notation "CB" => IntermediateIntegralModels.Model B K E
local notation "PA" => IntermediateIntegralModels.prime A F E QA
local notation "PB" => IntermediateIntegralModels.prime B K E QB

/-- The intermediate normalized orders agree when the final normalized
ambient orders agree. No compatibility is assumed separately at each step. -/
theorem intermediatePrime_order_eq_of_common_ambient_order
    (hupper : (heightOnePlace (k := F256) (K := E) QA).order =
      (heightOnePlace (k := F256) (K := E) QB).order)
    (J : IntermediateField K E) :
    (heightOnePlace (k := F256) (K := J.restrictScalars F) (PA (J.restrictScalars F))).order =
      (heightOnePlace (k := F256) (K := J) (PB J)).order := by
  let JA := J.restrictScalars F
  letI : Algebra (CA JA) J := inferInstanceAs (Algebra (CA JA) JA)
  letI : IsFractionRing (CA JA) J := inferInstanceAs (IsFractionRing (CA JA) JA)
  letI : IsScalarTower (CA JA) J E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (CA JA) (integralClosure A E) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (CB J) (integralClosure B E) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : QA.asIdeal.LiesOver (PA JA).asIdeal := ⟨rfl⟩
  letI : QB.asIdeal.LiesOver (PB J).asIdeal := ⟨rfl⟩
  exact heightOnePlace_order_eq_of_common_extension
    (k := F256) (K := J) (L := E) (PA JA) (PB J) QA QB hupper

/-- Restricting scalars preserves a literal normalized edge when the two
ambient models give the same final place. Its lower normalization is
transported by the proved prime-contraction comparison. -/
theorem NormalizedEdge.restrictScalars_of_common_ambient_order
    (hupper : (heightOnePlace (k := F256) (K := E) QA).order =
      (heightOnePlace (k := F256) (K := E) QB).order)
    {J L : IntermediateField K E} (h : NormalizedEdge B K E QB J L) :
    NormalizedEdge A F E QA (J.restrictScalars F) (L.restrictScalars F) := by
  obtain ⟨a, y, hy, ha, hgen⟩ := h
  refine ⟨a, y, hy, ?_, ?_⟩
  · rwa [intermediatePrime_order_eq_of_common_ambient_order A B F K E QA QB hupper J]
  · change ((J⟮y⟯).restrictScalars K).restrictScalars F = L.restrictScalars F
    rw [hgen]

/-- An entire actual normalized chain can be reused after changing the
initial base model, with the original final prime retained. -/
theorem NormalizedRefinement.restrictScalars_of_common_ambient_order
    (hupper : (heightOnePlace (k := F256) (K := E) QA).order =
      (heightOnePlace (k := F256) (K := E) QB).order)
    {J L : IntermediateField K E} (h : NormalizedRefinement B K E QB J L) :
    NormalizedRefinement A F E QA (J.restrictScalars F) (L.restrictScalars F) := by
  induction h with
  | refl => exact .refl
  | tail hchain hstep ih =>
      exact ih.tail (hstep.restrictScalars_of_common_ambient_order A B F K E QA QB hupper)

/-- Conversely, if both actual edge fields already contain the larger
base, the same edge is normalized in its own base model. This is the return
direction needed after completing one square of the source pyramid. -/
theorem NormalizedEdge.of_restrictScalars_of_common_ambient_order
    (hupper : (heightOnePlace (k := F256) (K := E) QA).order =
      (heightOnePlace (k := F256) (K := E) QB).order)
    {J L : IntermediateField K E}
    (h : NormalizedEdge A F E QA (J.restrictScalars F) (L.restrictScalars F)) :
    NormalizedEdge B K E QB J L := by
  obtain ⟨a, y, hy, ha, hgen⟩ := h
  refine ⟨a, y, hy, ?_, ?_⟩
  · rw [intermediatePrime_order_eq_of_common_ambient_order A B F K E QA QB hupper J] at ha
    exact ha
  · apply IntermediateField.restrictScalars_injective F
    exact hgen

/-- Every intermediate field along an increasing chain contains its
starting field. Hence a chain whose endpoints contain the larger base can
be read over that base, without adding any field or changing any generator. -/
theorem NormalizedRefinement.of_restrictScalars_of_common_ambient_order
    (hupper : (heightOnePlace (k := F256) (K := E) QA).order =
      (heightOnePlace (k := F256) (K := E) QB).order)
    {J L : IntermediateField K E}
    (h : NormalizedRefinement A F E QA (J.restrictScalars F) (L.restrictScalars F)) :
    NormalizedRefinement B K E QB J L := by
  have hlift (N : IntermediateField F E)
      (hchain : NormalizedRefinement A F E QA (J.restrictScalars F) N) :
      ∃ N' : IntermediateField K E, N'.restrictScalars F = N ∧
        NormalizedRefinement B K E QB J N' := by
    induction hchain with
    | refl => exact ⟨J, rfl, .refl⟩
    | @tail N M hchain hstep ih =>
        obtain ⟨N', hN', ih⟩ := ih
        have hJM := NormalizedRefinement.le A F E QA (hchain.tail hstep)
        let M' : IntermediateField K E :=
          M.toSubfield.toIntermediateField (fun x => hJM (J.algebraMap_mem x))
        have hedge : NormalizedEdge A F E QA (N'.restrictScalars F) (M'.restrictScalars F) := by
          change NormalizedEdge A F E QA (N'.restrictScalars F) M
          rwa [hN']
        exact ⟨M', rfl, ih.tail
          (hedge.of_restrictScalars_of_common_ambient_order A B F K E QA QB hupper)⟩
  obtain ⟨L', hL', hchain⟩ := hlift _ h
  have heq : L' = L := IntermediateField.restrictScalars_injective F hL'
  rwa [heq] at hchain

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
