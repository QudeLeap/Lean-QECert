import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Regions

/-! # Actual RX sectors identities -/

namespace QEC.Coding.BDL26RXDecoderAdapter

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

noncomputable def xSector (P : TannerSquarePresentation) (S : OddScale) : Finset (RX2 P S) :=
  Finset.univ.filter fun p => ∃ x : P.X, rxSyndromeOwner P S p = Vertex.x x

noncomputable def qSector (P : TannerSquarePresentation) (S : OddScale) : Finset (RX2 P S) :=
  Finset.univ.filter fun p => ∃ q : P.Q, rxSyndromeOwner P S p = Vertex.q q

noncomputable def zSector (P : TannerSquarePresentation) (S : OddScale) : Finset (RX2 P S) :=
  Finset.univ.filter fun p => ∃ z : P.Z, rxSyndromeOwner P S p = Vertex.z z

noncomputable def qCorrectionSector (P : TannerSquarePresentation) (S : OddScale) :
    Finset (RX1 P S) :=
  Finset.univ.filter fun p => ∃ q : P.Q, rxCorrectionOwner P S p = Vertex.q q

theorem xSector_regions (P : TannerSquarePresentation) (S : OddScale) :
    xSector P S = rxRegionUnion (localX P S) := by
  ext p
  simp [xSector, rxRegionUnion, localX, fiberRegion]

theorem qSector_regions (P : TannerSquarePresentation) (S : OddScale) :
    qSector P S = rxRegionUnion (localQ P S) := by
  ext p
  simp [qSector, rxRegionUnion, localQ, fiberRegion]

theorem zSector_regions (P : TannerSquarePresentation) (S : OddScale) :
    zSector P S = rxRegionUnion (localZ P S) := by
  ext p
  simp [zSector, rxRegionUnion, localZ, fiberRegion]

theorem qCorrectionSector_regions (P : TannerSquarePresentation) (S : OddScale) :
    qCorrectionSector P S = RXCoarseGraining.correctionRegionUnion (localQ P S) := by
  ext p
  simp [qCorrectionSector, RXCoarseGraining.correctionRegionUnion, localQ, fiberRegion]


private theorem mem_xSector (P : TannerSquarePresentation) (S : OddScale) (p : RX2 P S) :
    p ∈ xSector P S ↔ ∃ x, rxSyndromeOwner P S p = Vertex.x x := by
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ p))

private theorem mem_qSector (P : TannerSquarePresentation) (S : OddScale) (p : RX2 P S) :
    p ∈ qSector P S ↔ ∃ q, rxSyndromeOwner P S p = Vertex.q q := by
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ p))

private theorem mem_zSector (P : TannerSquarePresentation) (S : OddScale) (p : RX2 P S) :
    p ∈ zSector P S ↔ ∃ z, rxSyndromeOwner P S p = Vertex.z z := by
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ p))

private theorem mem_qCorrectionSector (P : TannerSquarePresentation) (S : OddScale) (p : RX1 P S) :
    p ∈ qCorrectionSector P S ↔ ∃ q, rxCorrectionOwner P S p = Vertex.q q := by
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ p))

theorem syndrome_sectors_cover (P : TannerSquarePresentation) (S : OddScale) :
    xSector P S ∪ qSector P S ∪ zSector P S = Finset.univ := by
  apply Finset.ext
  intro p
  constructor
  · intro _; exact Finset.mem_univ p
  · intro _
    rcases p with (⟨x,f⟩ | ⟨q,e⟩) | ⟨z,c⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ ((mem_xSector P S _).mpr ⟨x,rfl⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ ((mem_qSector P S _).mpr ⟨q,rfl⟩))
    · exact Finset.mem_union_right _ ((mem_zSector P S _).mpr ⟨z,rfl⟩)

theorem syndrome_sectors_disjoint (P : TannerSquarePresentation) (S : OddScale) :
    Disjoint (xSector P S) (qSector P S) ∧ Disjoint (xSector P S) (zSector P S) ∧
      Disjoint (qSector P S) (zSector P S) := by
  refine ⟨Finset.disjoint_left.mpr ?_, Finset.disjoint_left.mpr ?_, Finset.disjoint_left.mpr ?_⟩
  · intro p hx hq
    obtain ⟨x,hx⟩ := (mem_xSector P S p).mp hx
    obtain ⟨q,hq⟩ := (mem_qSector P S p).mp hq
    have h := hx.symm.trans hq
    cases h
  · intro p hx hz
    obtain ⟨x,hx⟩ := (mem_xSector P S p).mp hx
    obtain ⟨z,hz⟩ := (mem_zSector P S p).mp hz
    have h := hx.symm.trans hz
    cases h
  · intro p hq hz
    obtain ⟨q,hq⟩ := (mem_qSector P S p).mp hq
    obtain ⟨z,hz⟩ := (mem_zSector P S p).mp hz
    have h := hq.symm.trans hz
    cases h

theorem correction_sectors_cover (P : TannerSquarePresentation) (S : OddScale) :
    RXCoarseGraining.correctionRegionUnion (localX P S) ∪ qCorrectionSector P S =
      Finset.univ := by
  apply Finset.ext
  intro p
  constructor
  · intro _; exact Finset.mem_univ p
  · intro _
    rcases p with ⟨x,e⟩ | ⟨q,v⟩
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      exact ⟨x, Finset.mem_univ _, (xCorrectionEquiv P S x e).2⟩
    · exact Finset.mem_union_right _ ((mem_qCorrectionSector P S _).mpr ⟨q,rfl⟩)

theorem correction_sectors_disjoint (P : TannerSquarePresentation) (S : OddScale) :
    Disjoint (RXCoarseGraining.correctionRegionUnion (localX P S))
      (qCorrectionSector P S) := by
  apply Finset.disjoint_left.mpr
  intro p hx hq
  obtain ⟨x,_,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨q,hq⟩ := (mem_qCorrectionSector P S p).mp hq
  have hx : rxCorrectionOwner P S p = Vertex.x x := (Finset.mem_filter.mp hx).2
  have h := hx.symm.trans hq
  cases h

noncomputable def zPairEquiv (P : TannerSquarePresentation) (S : OddScale) :
    (P.Z × Fin 2) ≃ LocalRegionIndex (zSector P S) :=
  Equiv.ofBijective
    (fun p => ⟨Sum.inr p, (mem_zSector P S _).mpr ⟨p.1,rfl⟩⟩)
    ⟨by
      intro a b h
      exact Sum.inr.inj (congrArg Subtype.val h), by
      intro p
      rcases p with ⟨((⟨x,f⟩ | ⟨q,e⟩) | ⟨z,c⟩),hp⟩
      · obtain ⟨z,hz⟩ := (mem_zSector P S _).mp hp
        cases hz
      · obtain ⟨z,hz⟩ := (mem_zSector P S _).mp hp
        cases hz
      · exact ⟨(z,c), Subtype.ext rfl⟩⟩

@[simp] theorem zPairEquiv_val (P : TannerSquarePresentation) (S : OddScale)
    (p : P.Z × Fin 2) : (zPairEquiv P S p).val = Sum.inr p := rfl

theorem map2_diagonal (P : TannerSquarePresentation) (S : OddScale)
    (w : Word BDL26Field P.Z) (z : P.Z) (c : Fin 2) :
    rxMap2Coord P S w (zPairEquiv P S (z,c)).val = w z := rfl

theorem map2_auxiliary_zero (P : TannerSquarePresentation) (S : OddScale)
    (w : Word BDL26Field P.Z) (p : RX2 P S) (hp : p ∉ zSector P S) :
    rxMap2Coord P S w p = 0 := by
  rcases p with (⟨x,f⟩ | ⟨q,e⟩) | ⟨z,c⟩
  · rfl
  · rfl
  · exact (hp ((mem_zSector P S _).mpr ⟨z,rfl⟩)).elim

end QEC.Coding.BDL26RXDecoderAdapter
