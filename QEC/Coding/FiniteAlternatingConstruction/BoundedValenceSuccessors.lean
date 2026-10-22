import QEC.Coding.FiniteAlternatingConstruction.DecodingGraph

/-!
# Valence bounds for concrete alternating successors

This module gathers constructor-local measured bounds for the recursive
construction. Counts are taken on the materialized incidence fibers.
-/

namespace QEC.Coding.BDL26BoundedValence

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26RXLocalReplacement

open BDL26TannerLocalRegularity

private theorem xq_face_exists (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (x : P.X) (q : P.Q) (h : P.xq x q = true) :
    ∃ f : P.Face, ∃ c : Fin 2, P.faceX f = x ∧ P.faceQ f c = q := by
  let z := A.qzRoot q
  let shared : SharedQ P.data x z.1 := ⟨q, by simp [h, z.2]⟩
  obtain ⟨⟨f, c⟩, hc⟩ := (P.perfectPairing x z.1).2 shared
  exact ⟨f.1, c, f.2.1, congrArg Subtype.val hc⟩

private theorem qz_face_exists (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z) (h : P.qz q z = true) :
    ∃ f : P.Face, ∃ c : Fin 2, P.faceQ f c = q ∧ P.faceZ f = z := by
  let x := A.xqRoot q
  let shared : SharedQ P.data x.1 z := ⟨q, by simp [x.2, h]⟩
  obtain ⟨⟨f, c⟩, hc⟩ := (P.perfectPairing x.1 z).2 shared
  exact ⟨f.1, c, congrArg Subtype.val hc, f.2.2⟩

/-- The actual RZ face tags map to RX tags on the transposed input. -/
private def rzFaceToRX (P : TannerSquarePresentation) (S : OddScale) :
    BDL26RZLocalReplacement.RZFace P S → RXFace (transposePresentation P) S
  | Sum.inl localFace => Sum.inl localFace
  | Sum.inr (Sum.inl ⟨edge, cylinderEdge, endpoint⟩) =>
      Sum.inr (Sum.inl ⟨⟨(edge.1.2, edge.1.1), edge.2⟩, cylinderEdge, endpoint⟩)
  | Sum.inr (Sum.inr oldFace) => Sum.inr (Sum.inr oldFace)

private theorem qToZEdge_eq_rxRaw (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale)
    (q : P.Q) (z : P.Z) (h : P.qz q z = true)
    (edge : QDoubleCylinderEdge (transposePresentation P) q S) :
    qToZDoubleCylinderEdge P A q z h S edge =
      qToXDoubleCylinderEdgeRaw (transposePresentation P) q z h S edge := by
  cases edge <;> rfl

private theorem rzFaceToRX_z (P : TannerSquarePresentation)
    (S : OddScale) (f : BDL26RZLocalReplacement.RZFace P S) :
    rxFaceZ (transposePresentation P) S (rzFaceToRX P S f) =
      BDL26RZLocalReplacement.rzFaceX P S f := by
  rcases f with localFace | glue | oldFace <;> rfl

private theorem rzFaceToRX_q (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale)
    (f : BDL26RZLocalReplacement.RZFace P S) (c : Fin 2) :
    rxFaceQ (transposePresentation P) S (rzFaceToRX P S f) c =
      BDL26RZLocalReplacement.rzFaceQ P A S f c := by
  rcases f with ⟨z, cell, first, second⟩ | ⟨edge, cylinderEdge, endpoint⟩ | oldFace
  · rcases cell with copyFace | rectangle
    all_goals fin_cases first <;> fin_cases second <;> fin_cases c <;> rfl
  · fin_cases c
    · change (Sum.inl ⟨edge.1.2, qToXDoubleCylinderEdgeRaw (transposePresentation P)
        edge.1.1 edge.1.2 edge.2 S cylinderEdge⟩ : RX1 (transposePresentation P) S) =
        Sum.inl ⟨edge.1.2, qToZDoubleCylinderEdge P A
          edge.1.1 edge.1.2 edge.2 S cylinderEdge⟩
      rw [qToZEdge_eq_rxRaw]
    · rfl
  · rfl

private theorem rzFaceToRX_x (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale)
    (f : BDL26RZLocalReplacement.RZFace P S) :
    rxFaceX (transposePresentation P) S (rzFaceToRX P S f) =
      BDL26RZLocalReplacement.rzFaceZ P A S f := by
  rcases f with ⟨z, cell, first, second⟩ | ⟨edge, cylinderEdge, endpoint⟩ | oldFace
  · rcases cell with copyFace | rectangle
    all_goals fin_cases first <;> fin_cases second <;> rfl
  · fin_cases endpoint
    · change (⟨edge.1.2, tannerDoubleCylinderEdgeStart (transposePresentation P)
        edge.1.2 S (qToXDoubleCylinderEdgeRaw (transposePresentation P)
          edge.1.1 edge.1.2 edge.2 S cylinderEdge)⟩ : RX0 (transposePresentation P) S) =
        ⟨edge.1.2, qToZDoubleCylinderVertex P A edge.1.1 edge.1.2 edge.2 S
          (qDoubleCylinderEdgeStart (transposePresentation P) edge.1.1 S cylinderEdge)⟩
      rw [qToZDoubleCylinderEdge_start, qToZEdge_eq_rxRaw]
    · change (⟨edge.1.2, tannerDoubleCylinderEdgeEnd (transposePresentation P)
        edge.1.2 S (qToXDoubleCylinderEdgeRaw (transposePresentation P)
          edge.1.1 edge.1.2 edge.2 S cylinderEdge)⟩ : RX0 (transposePresentation P) S) =
        ⟨edge.1.2, qToZDoubleCylinderVertex P A edge.1.1 edge.1.2 edge.2 S
          (qDoubleCylinderEdgeEnd (transposePresentation P) edge.1.1 S cylinderEdge)⟩
      rw [qToZDoubleCylinderEdge_end, qToZEdge_eq_rxRaw]
  · rfl

private theorem rz_xq_to_rx_qz (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (x : BDL26RZLocalReplacement.RZX P S)
    (q : BDL26RZLocalReplacement.RZQ P S)
    (h : BDL26RZLocalReplacement.rzXQIncidence P A4.toTannerSquareAdmissible S x q = true) :
    rxQZIncidence (transposePresentation P) S q x = true := by
  let successor := BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S
  let admissible := BDL26RZLocalReplacement.rzReplacementAdmissibleV4 P A4 R S
  obtain ⟨f, c, hx, hq⟩ := xq_face_exists successor admissible.toTannerSquareAdmissible x q h
  apply (rxQZIncidence_eq_true_iff (transposePresentation P) S q x).2
  exact ⟨rzFaceToRX P S f, c,
    (rzFaceToRX_q P A4.toTannerSquareAdmissible S f c).trans hq,
    (rzFaceToRX_z P S f).trans hx⟩

private theorem rz_qz_to_rx_xq (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : BDL26RZLocalReplacement.RZQ P S)
    (z : BDL26RZLocalReplacement.RZZ P S)
    (h : BDL26RZLocalReplacement.rzQZIncidence P A4.toTannerSquareAdmissible S q z = true) :
    rxXQIncidence (transposePresentation P) S z q = true := by
  let successor := BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S
  let admissible := BDL26RZLocalReplacement.rzReplacementAdmissibleV4 P A4 R S
  obtain ⟨f, c, hq, hz⟩ := qz_face_exists successor admissible.toTannerSquareAdmissible q z h
  apply (rxXQIncidence_eq_true_iff (transposePresentation P) S z q).2
  exact ⟨rzFaceToRX P S f, c,
    (rzFaceToRX_x P A4.toTannerSquareAdmissible S f).trans hz,
    (rzFaceToRX_q P A4.toTannerSquareAdmissible S f c).trans hq⟩

private theorem rz_xDegree_le_rx_zDegree (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (x : BDL26RZLocalReplacement.RZX P S) :
    xDegree (BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S) x ≤
      zDegree (rxReplacementPresentation (transposePresentation P) S) x := by
  classical
  let source := BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S
  let target := rxReplacementPresentation (transposePresentation P) S
  let f : {v : source.Q // source.xq x v = true} →
      {v : target.Q // target.qz v x = true} :=
    fun v => ⟨v.1, rz_xq_to_rx_qz P A4 R S x v.1 v.2⟩
  exact Fintype.card_le_of_injective f (fun a b h =>
    Subtype.ext (congrArg (fun v : {v : target.Q // target.qz v x = true} => v.1) h))

private theorem rz_zDegree_le_rx_xDegree (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (z : BDL26RZLocalReplacement.RZZ P S) :
    zDegree (BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S) z ≤
      xDegree (rxReplacementPresentation (transposePresentation P) S) z := by
  classical
  let source := BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S
  let target := rxReplacementPresentation (transposePresentation P) S
  let f : {v : source.Q // source.qz v z = true} →
      {v : target.Q // target.xq z v = true} :=
    fun v => ⟨v.1, rz_qz_to_rx_xq P A4 R S v.1 z v.2⟩
  exact Fintype.card_le_of_injective f (fun a b h =>
    Subtype.ext (congrArg (fun v : {v : target.Q // target.xq z v = true} => v.1) h))

private theorem rz_qXDegree_le_rx_qZDegree (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : BDL26RZLocalReplacement.RZQ P S) :
    qXDegree (BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S) q ≤
      qZDegree (rxReplacementPresentation (transposePresentation P) S) q := by
  classical
  let source := BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S
  let target := rxReplacementPresentation (transposePresentation P) S
  let f : {v : source.X // source.xq v q = true} →
      {v : target.Z // target.qz q v = true} :=
    fun v => ⟨v.1, rz_xq_to_rx_qz P A4 R S v.1 q v.2⟩
  exact Fintype.card_le_of_injective f (fun a b h =>
    Subtype.ext (congrArg (fun v : {v : target.Z // target.qz q v = true} => v.1) h))

private theorem rz_qZDegree_le_rx_qXDegree (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : BDL26RZLocalReplacement.RZQ P S) :
    qZDegree (BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S) q ≤
      qXDegree (rxReplacementPresentation (transposePresentation P) S) q := by
  classical
  let source := BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S
  let target := rxReplacementPresentation (transposePresentation P) S
  let f : {v : source.Z // source.qz q v = true} →
      {v : target.X // target.xq v q = true} :=
    fun v => ⟨v.1, rz_qz_to_rx_xq P A4 R S q v.1 v.2⟩
  exact Fintype.card_le_of_injective f (fun a b h =>
    Subtype.ext (congrArg (fun v : {v : target.X // target.xq v q = true} => v.1) h))

/-- The materialized RZ incidence fibers embed into those of RX on the
transposed input. This transports a proved bound without changing carriers. -/
private theorem rz_boundedValence_of_rx (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (hB : BoundedValence (rxReplacementPresentation (transposePresentation P) S)) :
    BoundedValence (BDL26RZLocalReplacement.rzReplacementPresentation
      P A4.toTannerSquareAdmissible S) := by
  classical
  have hx := rz_xDegree_le_rx_zDegree P A4 R S
  have hz := rz_zDegree_le_rx_xDegree P A4 R S
  have hqx := rz_qXDegree_le_rx_qZDegree P A4 R S
  have hqz := rz_qZDegree_le_rx_qXDegree P A4 R S
  refine ⟨fun x => (hx x).trans (hB.2.1 x), fun z => (hz z).trans (hB.1 z), ?_⟩
  intro q
  obtain ⟨hxx, hzz, hsum⟩ := hB.2.2 q
  refine ⟨(hqx q).trans hzz, (hqz q).trans hxx, ?_⟩
  have ha := hqx q
  have hb := hqz q
  omega

/-- Actual RX replacement preserves the fixed measured valence invariant. -/
theorem rx_boundedValence (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (h : BoundedValence P) :
    BoundedValence (rxReplacementPresentation P S) :=
  BDL26RXLocalReplacement.rx_boundedValence P A4 R S h

/-- Actual RZ replacement preserves the fixed measured valence invariant. -/
theorem rz_boundedValence (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (h : BoundedValence P) :
    BoundedValence (BDL26RZLocalReplacement.rzReplacementPresentation
      P A4.toTannerSquareAdmissible S) :=
  rz_boundedValence_of_rx P A4 R S
    (rx_boundedValence (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A4)
      (transposeTannerSquareCellularRegular P R) S (boundedValence_transpose P h))

/-- Every recursively constructed state has uniform valence, independently of
its depth and odd subdivision scale. -/
theorem state_boundedValence (S : OddScale) (n : Nat) :
    BoundedValence (BDL26DecodingGraph.state S n).presentation := by
  induction n with
  | zero => exact base_boundedValence
  | succ n ih =>
      change BoundedValence (BDL26DecodingGraph.nextState S n
        (BDL26DecodingGraph.state S n)).presentation
      unfold BDL26DecodingGraph.nextState
      split
      · exact rx_boundedValence _ (BDL26DecodingGraph.state S n).admissible
          (BDL26DecodingGraph.state S n).regular S ih
      · exact rz_boundedValence _ (BDL26DecodingGraph.state S n).admissible
          (BDL26DecodingGraph.state S n).regular S ih

end QEC.Coding.BDL26BoundedValence
