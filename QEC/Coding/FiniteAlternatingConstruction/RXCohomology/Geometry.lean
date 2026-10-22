import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Lifts
import QEC.Coding.FiniteAlternatingConstruction.RXPresentationCochain
import QEC.Coding.FiniteAlternatingConstruction.RZCohomology.Representatives

/-!
# Actual RX cocycle gauge normalization

BDL26 v1 `paper.tex:1821–1935` (approved source gate #840). The argument uses
computed local CX exactness and constructive cylinder connectedness. All
identities are identities of complete words, including auxiliary sectors.
-/

namespace QEC.Coding.BDL26RXCohomology

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open BDL26RXStagedRestriction MultiscaleDecoder
open scoped Classical BigOperators

abbrev Field := BDL26FiniteTannerSquare.Field
noncomputable abbrev complex := BDL26RZCohomology.complex
noncomputable abbrev Cocycle := BDL26RZCohomology.Cocycle
noncomputable abbrev H1 := BDL26RZCohomology.H1
noncomputable abbrev classOf := BDL26RZCohomology.classOf

/-- The materialized actual RX degree-zero differential is the raw matrix map. -/
theorem differential0_eq (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    tannerCoboundary0 (rxReplacementPresentation P S) = rxCoboundary0 P S := by
  exact rxPresentation_coboundary0_eq P A R S

/-- The materialized actual RX degree-one differential is the raw matrix map. -/
theorem differential1_eq (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    tannerCoboundary1 (rxReplacementPresentation P S) = rxCoboundary1 P S := by
  exact rxPresentation_coboundary1_eq P A R S

/-- The literal constant Q lift is injective on complete old words. -/
theorem map1_injective (P : TannerSquarePresentation) (S : OddScale) :
    Function.Injective (rxMap1Coord P S) := by
  intro u v h
  funext q
  exact congrFun h (Sum.inr ⟨q, (0, Sum.inl (Sum.inl ()))⟩)

/-- The actual old-Z diagonal coordinates make map2 injective. -/
theorem map2_injective (P : TannerSquarePresentation) (S : OddScale) :
    Function.Injective (rxMap2Coord P S) := by
  intro u v h
  funext z
  exact congrFun h (Sum.inr (z,0))

/-- Construct local CX potentials from the proved zero first cohomology. -/
theorem local_potentials (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Word Field (RX1 P S)) (hw : rxCoboundary1 P S w = 0) :
    ∃ f : ∀ x : P.X, Word Field (DoubleCylinderVertex P x S),
      ∀ x, wordLinearMapTranspose (localCx P S x).boundary1 (f x) =
        restrictWordLinear ((localX P S).correctionRegion x) w := by
  have hx : ∀ x, ∃ f : Word Field (DoubleCylinderVertex P x S),
      wordLinearMapTranspose (localCx P S x).boundary1 f =
        restrictWordLinear ((localX P S).correctionRegion x) w := by
    intro x
    apply LinearMap.mem_range.mp
    rw [← localCx_exact P A.toTannerSquareAdmissibleV3 R S x]
    apply LinearMap.mem_ker.mpr
    rw [← localCx_global_restriction, hw, map_zero]
  exact ⟨fun x => Classical.choose (hx x), fun x => Classical.choose_spec (hx x)⟩

/-- Subtract the entire actual global coboundary; every X error vanishes. -/
theorem full_gauge_x_zero (P : TannerSquarePresentation) (S : OddScale)
    (w : Word Field (RX1 P S))
    (f : ∀ x : P.X, Word Field (DoubleCylinderVertex P x S))
    (hf : ∀ x, wordLinearMapTranspose (localCx P S x).boundary1 (f x) =
      restrictWordLinear ((localX P S).correctionRegion x) w) :
    ∀ x, restrictWordLinear ((localX P S).correctionRegion x)
      (w - rxCoboundary0 P S (∑ y : P.X, xLift P S y (f y))) = 0 := by
  intro x
  rw [map_sub, localCx_lift_sum_restriction, hf, sub_self]

/-- Read a normalized word at the actual copy-zero Q cone point. -/
def coarseWord (P : TannerSquarePresentation) (S : OddScale)
    (w : Word Field (RX1 P S)) : Word Field P.Q :=
  fun q => w (Sum.inr ⟨q, (0, Sum.inl (Sum.inl ()))⟩)

/-- A normalized actual cocycle is the literal map1 on its full word. -/
theorem normalized_word (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (w : Word Field (RX1 P S))
    (hw : rxCoboundary1 P S w = 0)
    (hx : ∀ x, restrictWordLinear ((localX P S).correctionRegion x) w = 0) :
    rxMap1Coord P S (coarseWord P S w) = w := by
  funext p
  rcases p with ⟨x,e⟩ | ⟨q,v⟩
  · have hz := congrFun (hx x) (xCorrectionEquiv P S x e)
    exact hz.symm
  · symm
    apply word_eq_root_of_graphCoboundary_eq_zero
      (qDoubleCylinderEdgeStart P q S) (qDoubleCylinderEdgeEnd P q S)
      (0, Sum.inl (Sum.inl ())) (qDoubleCylinderPath P A q S)
      (fun vertex => w (Sum.inr ⟨q,vertex⟩))
    change wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
      (fun vertex => w (Sum.inr ⟨q,vertex⟩)) = 0
    funext edge
    rw [← rxCoboundary1_q_of_x_restrictions_zero P S w hx q edge, hw]
    rfl

/-- The old word recovered from a normalized cocycle is itself a cocycle. -/
theorem normalized_cocycle (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (w : Word Field (RX1 P S))
    (hw : rxCoboundary1 P S w = 0)
    (hx : ∀ x, restrictWordLinear ((localX P S).correctionRegion x) w = 0) :
    tannerCoboundary1 P (coarseWord P S w) = 0 := by
  apply map2_injective P S
  have hc := LinearMap.congr_fun (rxMap_commutes_coboundary1 P S) (coarseWord P S w)
  change rxCoboundary1 P S (rxMap1Coord P S (coarseWord P S w)) =
    rxMap2Coord P S (tannerCoboundary1 P (coarseWord P S w)) at hc
  rw [normalized_word P A S w hw hx, hw] at hc
  simpa only [map_zero] using hc.symm

/-- Zero X derivative forces the entire global degree-zero potential to be
an actual constant CX lift, on both copies and every vertex. -/
theorem potential_is_map0 (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (f : Word Field (RX0 P S))
    (hf : ∀ x e, rxCoboundary0 P S f (Sum.inl ⟨x,e⟩) = 0) :
    ∃ old : Word Field P.X, rxMap0Coord P S old = f := by
  let old : Word Field P.X := fun x =>
    f ⟨x, (0, (subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)).1)⟩
  refine ⟨old, ?_⟩
  funext p
  rcases p with ⟨x,v⟩
  symm
  apply rxCxCocycle_eq_boundaryRoot_zeroCopy P A x S (fun v => f ⟨x,v⟩)
  change wordLinearMapTranspose (doubleCylinderBoundary1 P x S) (fun v => f ⟨x,v⟩) = 0
  funext e
  rw [← raw_delta0_x P S f x e, hf]
  rfl

/-- No supplied boundary implication: actual connectedness recovers an old
potential whenever the literal map1 word is an actual full coboundary. -/
theorem raw_boundary_iff (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (v : Word Field P.Q) :
    (∃ f, rxCoboundary0 P S f = rxMap1Coord P S v) ↔
      ∃ old, tannerCoboundary0 P old = v := by
  constructor
  · rintro ⟨f,hf⟩
    have hx : ∀ x e, rxCoboundary0 P S f (Sum.inl ⟨x,e⟩) = 0 := by
      intro x e
      rw [hf, rxMap1Coord_localEdge]
    obtain ⟨old,ho⟩ := potential_is_map0 P A S f hx
    refine ⟨old, map1_injective P S ?_⟩
    have hc := LinearMap.congr_fun (rxMap_commutes_coboundary0 P A S) old
    change rxCoboundary0 P S (rxMap0Coord P S old) =
      rxMap1Coord P S (tannerCoboundary0 P old) at hc
    rw [ho, hf] at hc
    exact hc.symm
  · rintro ⟨old,rfl⟩
    refine ⟨rxMap0Coord P S old, ?_⟩
    exact LinearMap.congr_fun (rxMap_commutes_coboundary0 P A S) old

end QEC.Coding.BDL26RXCohomology
