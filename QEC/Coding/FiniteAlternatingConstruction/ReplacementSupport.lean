import QEC.Coding.FiniteAlternatingConstruction.RZCoordinateBridge
import QEC.Coding.FiniteAlternatingConstruction.QLocalWeight
import QEC.Coding.FourDimensionalToricCode.Decoder.RXLocalCleaning

/-!
# Constructor-derived local support for the two replacements

Local pieces are the fibers of the actual sum/sigma carrier tags. Restriction
followed by zero extension recovers each piece and the disjoint pieces sum to
the original word. No support decomposition is accepted as input.
-/

namespace QEC.Coding.BDL26ReplacementSupport

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped BigOperators Classical

abbrev Field := BDL26FiniteAlternatingCore.Field
abbrev Two := Fin 2

section Fibers

variable {Label Coordinate : Type} [Fintype Label] [Fintype Coordinate]
  [DecidableEq Label] [DecidableEq Coordinate]

/-- Local coordinate region selected by a concrete constructor tag. -/
def fiberRegion (owner : Coordinate → Label) (label : Label) : Finset Coordinate :=
  Finset.univ.filter (fun coordinate => owner coordinate = label)

/-- Restrict to one owner and extend by zero in the ambient carrier. -/
def fiberPart (owner : Coordinate → Label) (label : Label) :
    Word Field Coordinate →ₗ[Field] Word Field Coordinate where
  toFun word coordinate := if owner coordinate = label then word coordinate else 0
  map_add' := by intros; ext coordinate; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' := by
    intros
    ext coordinate
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

@[simp] theorem fiberPart_apply (owner : Coordinate → Label) (label : Label)
    (word : Word Field Coordinate) (coordinate : Coordinate) :
    fiberPart owner label word coordinate =
      if owner coordinate = label then word coordinate else 0 := rfl

theorem fiberRegion_disjoint (owner : Coordinate → Label)
    {first second : Label} (hne : first ≠ second) :
    Disjoint (fiberRegion owner first) (fiberRegion owner second) := by
  apply Finset.disjoint_left.mpr
  intro coordinate hfirst hsecond
  exact hne ((Finset.mem_filter.mp hfirst).2.symm.trans
    (Finset.mem_filter.mp hsecond).2)

theorem fiberPart_support (owner : Coordinate → Label) (label : Label)
    (word : Word Field Coordinate) :
    hammingSupport (fiberPart owner label word) ⊆ fiberRegion owner label := by
  intro coordinate hcoordinate
  simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    fiberPart_apply] at hcoordinate
  by_cases h : owner coordinate = label
  · simp [fiberRegion, h]
  · simp [h] at hcoordinate

theorem sum_fiberPart (owner : Coordinate → Label) (word : Word Field Coordinate) :
    (∑ label : Label, fiberPart owner label word) = word := by
  ext coordinate
  simp only [Finset.sum_apply, fiberPart_apply]
  simp

theorem fiberPart_eq_extend_restrict (owner : Coordinate → Label) (label : Label)
    (word : Word Field Coordinate) :
    fiberPart owner label word =
      zeroExtendWord (fiberRegion owner label)
        (fun coordinate => word coordinate.1) := by
  ext coordinate
  change (if owner coordinate = label then word coordinate else 0) =
    (if h : coordinate ∈ fiberRegion owner label then word coordinate else 0)
  by_cases h : owner coordinate = label
  · have hm : coordinate ∈ fiberRegion owner label :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    simp only [if_pos h, dif_pos hm]
  · have hm : coordinate ∉ fiberRegion owner label :=
      fun hm => h (Finset.mem_filter.mp hm).2
    simp only [if_neg h, dif_neg hm]

end Fibers

/-- RX corrections lie in X-edge or shifted Q-vertex blocks. -/
def rxCorrectionOwner (P : TannerSquarePresentation) (S : OddScale) :
    RX1 P S → Vertex P
  | Sum.inl edge => .x edge.1
  | Sum.inr vertex => .q vertex.1

/-- RX syndromes lie in X-face, shifted Q-edge or two-point Z blocks. -/
def rxSyndromeOwner (P : TannerSquarePresentation) (S : OddScale) :
    RX2 P S → Vertex P
  | Sum.inl (Sum.inl face) => .x face.1
  | Sum.inl (Sum.inr edge) => .q edge.1
  | Sum.inr point => .z point.1

/-- RZ corrections lie in transposed Z-edge or Q-vertex blocks. -/
def rzCorrectionOwner (P : TannerSquarePresentation) (S : OddScale) :
    RZQ P S → Vertex P
  | Sum.inl edge => .z edge.1
  | Sum.inr vertex => .q vertex.1

/-- Every RZ syndrome coordinate belongs to exactly one Z cylinder. -/
def rzSyndromeOwner (P : TannerSquarePresentation) (S : OddScale) :
    RZZ P S → P.Z := Sigma.fst

theorem rxCorrection_partition (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RX1 P S)) :
    (∑ v : Vertex P, fiberPart (rxCorrectionOwner P S) v word) = word := by
  classical
  exact sum_fiberPart _ _

theorem rxSyndrome_partition (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RX2 P S)) :
    (∑ v : Vertex P, fiberPart (rxSyndromeOwner P S) v word) = word := by
  classical
  exact sum_fiberPart _ _

theorem rzCorrection_partition (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RZQ P S)) :
    (∑ v : Vertex P, fiberPart (rzCorrectionOwner P S) v word) = word := by
  classical
  exact sum_fiberPart _ _

theorem rzSyndrome_partition (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RZZ P S)) :
    (∑ z : P.Z, fiberPart (rzSyndromeOwner P S) z word) = word := by
  classical
  exact sum_fiberPart _ _

/-- One RZ local cohomology coordinate is a single parity bit. -/
def parityBit {Coordinate : Type} [Fintype Coordinate]
    (word : Word Field Coordinate) : Word Field Unit :=
  fun _ => totalParity word

theorem parityBit_weight_le_one {Coordinate : Type} [Fintype Coordinate]
    (word : Word Field Coordinate) : HammingWeight (parityBit word) ≤ 1 := by
  classical
  simpa only [HammingWeight, Fintype.card_unit] using
    Finset.card_le_univ (hammingSupport (parityBit word))

theorem parityBit_weight_le {Coordinate : Type} [Fintype Coordinate]
    (word : Word Field Coordinate) :
    HammingWeight (parityBit word) ≤ HammingWeight word := by
  classical
  by_cases hword : word = 0
  · subst word
    simp [parityBit, totalParity, HammingWeight, hammingSupport]
  · have hpos : 0 < HammingWeight word := Nat.pos_of_ne_zero
      (fun h => hword ((HammingWeight_eq_zero_iff word).mp h))
    exact (parityBit_weight_le_one word).trans hpos

/-- Concrete RZ local bound applied to the actual tagged Z cylinder. -/
theorem rzLocalParity_weight_le
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (syndrome : Word Field (RZZ P S)) :
    HammingWeight (parityBit (fun vertex : ZDoubleCylinderVertex P z S =>
      syndrome ⟨z, vertex⟩)) ≤
      HammingWeight (fun vertex : ZDoubleCylinderVertex P z S => syndrome ⟨z, vertex⟩) :=
  parityBit_weight_le _

/-! ## The RX local and connecting coboundary terms -/

/-- The diagonal local blocks of the concrete degree-two boundary matrix. -/
noncomputable def rxLocalBoundary2Matrix (P : TannerSquarePresentation) (S : OddScale) :
    Matrix (RX1 P S) (RX2 P S) Field := by
  classical
  exact fun source target => match target, source with
    | Sum.inl (Sum.inl xFace), Sum.inl xEdge =>
        if h : xEdge.1 = xFace.1 then
          doubleCylinderFaceEdgeMatrix P xFace.1 S (h ▸ xEdge.2) xFace.2 else 0
    | Sum.inl (Sum.inr qEdge), Sum.inr qVertex =>
        if h : qVertex.1 = qEdge.1 then
          qDoubleCylinderEdgeVertexIncidence P qEdge.1 S (h ▸ qVertex.2) qEdge.2 else 0
    | _, _ => 0

/-- The actual adjacent X-to-Q restriction entries. -/
noncomputable def rxXQBoundary2Matrix (P : TannerSquarePresentation) (S : OddScale) :
    Matrix (RX1 P S) (RX2 P S) Field := by
  classical
  exact fun source target => match source, target with
    | Sum.inl xEdge, Sum.inl (Sum.inr qEdge) =>
        qDoubleCylinderEdgeXIncidence P qEdge.1 xEdge.1 S xEdge.2 qEdge.2
    | _, _ => 0

/-- The actual two-terminal Q-to-Z restriction entries. -/
noncomputable def rxQZBoundary2Matrix (P : TannerSquarePresentation) (S : OddScale) :
    Matrix (RX1 P S) (RX2 P S) Field := by
  classical
  exact fun source target => match source, target with
    | Sum.inr qVertex, Sum.inr zPoint =>
        qDoubleCylinderVertexZIncidence P qVertex.1 S qVertex.2 zPoint
    | _, _ => 0

theorem rxBoundary2Matrix_decomposition (P : TannerSquarePresentation) (S : OddScale) :
    rxBoundary2Matrix P S = rxLocalBoundary2Matrix P S +
      rxXQBoundary2Matrix P S + rxQZBoundary2Matrix P S := by
  classical
  ext source target
  rcases source with xEdge | qVertex <;>
    rcases target with (xFace | qEdge) | zPoint <;>
    simp [rxBoundary2Matrix, rxLocalBoundary2Matrix, rxXQBoundary2Matrix,
      rxQZBoundary2Matrix]

noncomputable def rxLocalDelta1 (P : TannerSquarePresentation) (S : OddScale) :
    Word Field (RX1 P S) →ₗ[Field] Word Field (RX2 P S) :=
  wordLinearMapTranspose (Matrix.toLin' (rxLocalBoundary2Matrix P S))

noncomputable def rxConnectingXQ1 (P : TannerSquarePresentation) (S : OddScale) :
    Word Field (RX1 P S) →ₗ[Field] Word Field (RX2 P S) :=
  wordLinearMapTranspose (Matrix.toLin' (rxXQBoundary2Matrix P S))

noncomputable def rxConnectingQZ1 (P : TannerSquarePresentation) (S : OddScale) :
    Word Field (RX1 P S) →ₗ[Field] Word Field (RX2 P S) :=
  wordLinearMapTranspose (Matrix.toLin' (rxQZBoundary2Matrix P S))

/-- The total degree-one coboundary has precisely the audited local and two
adjacent connecting terms. -/
theorem rxDelta1_decomposition (P : TannerSquarePresentation) (S : OddScale) :
    wordLinearMapTranspose (rxBoundary2 P S) =
      rxLocalDelta1 P S + rxConnectingXQ1 P S + rxConnectingQZ1 P S := by
  classical
  unfold rxBoundary2 rxLocalDelta1 rxConnectingXQ1 rxConnectingQZ1
  rw [rxBoundary2Matrix_decomposition, map_add, map_add,
    wordLinearMapTranspose_add, wordLinearMapTranspose_add]

/-- A local X correction cannot create a direct Z-block syndrome. -/
theorem rxConnectingQZ1_zero_on_x (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RX1 P S)) (hQ : ∀ qv, word (Sum.inr qv) = 0) :
    rxConnectingQZ1 P S word = 0 := by
  classical
  ext target
  rw [rxConnectingQZ1, wordLinearMapTranspose_toLin'_apply]
  apply Finset.sum_eq_zero
  intro source _
  rcases source with xEdge | qVertex
  · simp [rxQZBoundary2Matrix]
  · simp [hQ]

/-- A local Q correction cannot create an X-to-Q connecting contribution. -/
theorem rxConnectingXQ1_zero_on_q (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RX1 P S)) (hX : ∀ xe, word (Sum.inl xe) = 0) :
    rxConnectingXQ1 P S word = 0 := by
  classical
  ext target
  rw [rxConnectingXQ1, wordLinearMapTranspose_toLin'_apply]
  apply Finset.sum_eq_zero
  intro source _
  rcases source with xEdge | qVertex
  · simp [hX]
  · simp [rxXQBoundary2Matrix]

/-- The weight of a dependent disjoint union is the sum of its fiber weights. -/
theorem HammingWeight_sigma
    {Label : Type} [Fintype Label] {Coordinate : Label → Type}
    [∀ label, Fintype (Coordinate label)]
    (word : Word Field (Sigma Coordinate)) :
    HammingWeight word = ∑ label : Label,
      HammingWeight (fun coordinate : Coordinate label => word ⟨label, coordinate⟩) := by
  classical
  simp only [HammingWeight, hammingSupport, Finset.card_filter,
    Fintype.sum_sigma]

private theorem sigmaParity_sum_weight_le
    {Label : Type} [Fintype Label] {Coordinate : Label → Type}
    [∀ label, Fintype (Coordinate label)]
    (syndrome : Word Field (Sigma Coordinate)) :
    (∑ label : Label, HammingWeight
      (parityBit (fun coordinate : Coordinate label => syndrome ⟨label, coordinate⟩))) ≤
      HammingWeight syndrome := by
  calc
    _ ≤ ∑ label : Label, HammingWeight
        (fun coordinate : Coordinate label => syndrome ⟨label, coordinate⟩) := by
      apply Finset.sum_le_sum
      intro label _
      exact parityBit_weight_le _
    _ = HammingWeight syndrome := (HammingWeight_sigma syndrome).symm

private theorem sigmaParity_sum_weight_le_with_total
    {Label : Type} [Fintype Label] {Coordinate : Label → Type}
    [∀ label, Fintype (Coordinate label)] [total : Fintype (Sigma Coordinate)]
    (syndrome : Word Field (Sigma Coordinate)) :
    (∑ label : Label, HammingWeight
      (parityBit (fun coordinate : Coordinate label => syndrome ⟨label, coordinate⟩))) ≤
      HammingWeight syndrome := by
  let standard : Fintype (Sigma Coordinate) := Sigma.instFintype
  have ht : total = standard := Subsingleton.elim _ _
  have hw : @HammingWeight Field (Sigma Coordinate) _ _ total syndrome =
      @HammingWeight Field (Sigma Coordinate) _ _ standard syndrome :=
    congrArg (fun inst : Fintype (Sigma Coordinate) =>
      @HammingWeight Field (Sigma Coordinate) _ _ inst syndrome) ht
  exact (sigmaParity_sum_weight_le syndrome).trans_eq hw.symm

/-- All one-bit RZ local coordinates jointly obey the original syndrome budget. -/
theorem rzLocalParity_sum_weight_le
    (P : TannerSquarePresentation) (S : OddScale)
    (syndrome : Word Field (RZZ P S)) :
    (∑ z : P.Z, HammingWeight
      (parityBit (fun vertex : ZDoubleCylinderVertex P z S => syndrome ⟨z, vertex⟩))) ≤
      HammingWeight syndrome := by
  exact @sigmaParity_sum_weight_le_with_total P.Z inferInstance
    (fun z => ZDoubleCylinderVertex P z S) (fun z => inferInstance)
    (inferInstance : Fintype (RZZ P S)) syndrome

/-- The bound is the existing RZ cohomology coordinate applied to an actual
syndrome representative, expressed as its single finite output coordinate. -/
theorem rzCzH2Coordinate_weight_le
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (syndrome : Word Field (ZDoubleCylinderVertex P z S)) :
    HammingWeight (fun _ : Unit => rzCzH2Coordinate P z S
      ((LinearMap.range (wordLinearMapTranspose (rzCz P z S).boundary2)).mkQ syndrome)) ≤
        HammingWeight syndrome := by
  have heq : (fun _ : Unit => rzCzH2Coordinate P z S
      ((LinearMap.range (wordLinearMapTranspose (rzCz P z S).boundary2)).mkQ syndrome)) =
      parityBit syndrome := by
    funext u
    exact rzCzH2Coordinate_mk P z S syndrome
  rw [heq]
  exact parityBit_weight_le syndrome

/-- The concrete RZ edge-endpoint matrix, embedded in the global source tags. -/
noncomputable def rzLocalBoundary1Matrix
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (S : OddScale) :
    Matrix (RZQ P S) (RZZ P S) Field := by
  classical
  exact fun source target => match source with
    | Sum.inl _ => if rzQZIncidence P A S source target then 1 else 0
    | Sum.inr _ => 0

/-- The concrete adjacent Q-to-Z vertex embedding matrix. -/
noncomputable def rzConnectingBoundary1Matrix
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (S : OddScale) :
    Matrix (RZQ P S) (RZZ P S) Field := by
  classical
  exact fun source target => match source with
    | Sum.inl _ => 0
    | Sum.inr _ => if rzQZIncidence P A S source target then 1 else 0

noncomputable def rzLocalDelta1
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (S : OddScale) :
    Word Field (RZQ P S) →ₗ[Field] Word Field (RZZ P S) :=
  wordLinearMapTranspose (Matrix.toLin' (rzLocalBoundary1Matrix P A S))

noncomputable def rzConnectingQZ1
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (S : OddScale) :
    Word Field (RZQ P S) →ₗ[Field] Word Field (RZZ P S) :=
  wordLinearMapTranspose (Matrix.toLin' (rzConnectingBoundary1Matrix P A S))

private theorem tannerDelta1_matrix_split
    (P : TannerSquarePresentation) (M N : Matrix P.Q P.Z Field)
    (h : ∀ q z, (if P.qz q z = true then (1 : Field) else 0) = M q z + N q z) :
    tannerCoboundary1 P = wordLinearMapTranspose (Matrix.toLin' M) +
      wordLinearMapTranspose (Matrix.toLin' N) := by
  classical
  apply LinearMap.ext
  intro word
  funext target
  change (∑ source : P.Q, word source *
      (if P.qz source target = true then (1 : Field) else 0)) =
    wordLinearMapTranspose (Matrix.toLin' M) word target +
      wordLinearMapTranspose (Matrix.toLin' N) word target
  rw [wordLinearMapTranspose_toLin'_apply, wordLinearMapTranspose_toLin'_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro source _
  rw [h, mul_add]

/-- Exact RZ local/connecting decomposition on the materialized presentation. -/
theorem rzDelta1_decomposition
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) :
    tannerCoboundary1 (rzReplacementPresentation P A4.toTannerSquareAdmissible S) =
      rzLocalDelta1 P A4.toTannerSquareAdmissible S +
        rzConnectingQZ1 P A4.toTannerSquareAdmissible S := by
  classical
  apply tannerDelta1_matrix_split
    (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
    (rzLocalBoundary1Matrix P A4.toTannerSquareAdmissible S)
    (rzConnectingBoundary1Matrix P A4.toTannerSquareAdmissible S)
  intro source target
  change (if rzQZIncidence P A4.toTannerSquareAdmissible S source target then
      (1 : Field) else 0) =
    rzLocalBoundary1Matrix P A4.toTannerSquareAdmissible S source target +
      rzConnectingBoundary1Matrix P A4.toTannerSquareAdmissible S source target
  rcases source with localEdge | qVertex <;>
    simp only [rzLocalBoundary1Matrix, rzConnectingBoundary1Matrix, add_zero, zero_add]

/-- The connecting RZ term vanishes on an actual local Z fiber. -/
theorem rzConnectingQZ1_local_fiber_zero
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (S : OddScale)
    (z : P.Z) (word : Word Field (RZQ P S)) :
    rzConnectingQZ1 P A S (fiberPart (rzCorrectionOwner P S) (.z z) word) = 0 := by
  classical
  ext target
  rw [rzConnectingQZ1, wordLinearMapTranspose_toLin'_apply]
  apply Finset.sum_eq_zero
  intro source _
  rcases source with localEdge | qVertex <;>
    simp [rzConnectingBoundary1Matrix, fiberPart_apply, rzCorrectionOwner]

/-- Distinct Z fibers cannot interact through the local endpoint differential. -/
theorem rzLocalDelta1_fiber_support
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (S : OddScale)
    (z : P.Z) (word : Word Field (RZQ P S)) :
    hammingSupport (rzLocalDelta1 P A S
      (fiberPart (rzCorrectionOwner P S) (.z z) word)) ⊆
        fiberRegion (rzSyndromeOwner P S) z := by
  classical
  intro target htarget
  by_contra hnot
  have hz : target.1 ≠ z := by
    intro heq
    apply hnot
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
  have hzero : rzLocalDelta1 P A S
      (fiberPart (rzCorrectionOwner P S) (.z z) word) target = 0 := by
    rw [rzLocalDelta1, wordLinearMapTranspose_toLin'_apply]
    apply Finset.sum_eq_zero
    intro source _
    rcases source with ⟨other, edge⟩ | qVertex
    · by_cases hother : other = z
      · subst other
        simp [rzLocalBoundary1Matrix, rzQZIncidence, hz]
      · simp [fiberPart_apply, rzCorrectionOwner, hother]
    · simp [rzLocalBoundary1Matrix]
  simpa [hammingSupport, hzero] using htarget

/-- The actual Q-to-Z contribution, extended by zero to every old Z label. -/
noncomputable def rxQOutgoing
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (word : Word Field (QDoubleCylinderVertex P q S)) (z : P.Z) : Word Field Two :=
  if hqz : P.qz q z = true then rxQZDegreeOne P q z hqz S word else 0

@[simp] theorem rxQOutgoing_nonincident
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (word : Word Field (QDoubleCylinderVertex P q S))
    (z : P.Z) (hz : P.qz q z ≠ true) : rxQOutgoing P q S word z = 0 := by
  simp [rxQOutgoing, hz]

theorem rxQOutgoing_sum_weight
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (word : Word Field (QDoubleCylinderVertex P q S)) :
    (∑ z : P.Z, HammingWeight (rxQOutgoing P q S word z)) =
      ∑ z : QStarEdge P q, HammingWeight (rxQZDegreeOne P q z.1 z.2 S word) := by
  classical
  let incident : Finset P.Z := Finset.univ.filter fun z => P.qz q z = true
  have hsubtype : (∑ z ∈ incident, HammingWeight (rxQOutgoing P q S word z)) =
      ∑ z : QStarEdge P q, HammingWeight (rxQOutgoing P q S word z.1) :=
    Finset.sum_subtype incident (by simp [incident])
      (fun z => HammingWeight (rxQOutgoing P q S word z))
  calc
    _ = ∑ z ∈ incident, HammingWeight (rxQOutgoing P q S word z) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : P.qz q z = true <;> simp [rxQOutgoing, hz, HammingWeight, hammingSupport]
    _ = ∑ z : QStarEdge P q, HammingWeight (rxQOutgoing P q S word z.1) := hsubtype
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      simp [rxQOutgoing, z.2]

/-- Exact F12 Q-local correction with the budget over every old-Z label. -/
theorem rxCq_exists_global_outgoing_weight_le
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (syndrome : Word Field (QDoubleCylinderEdge P q S))
    (hs : syndrome ∈ LinearMap.range
      (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S))) :
    ∃ correction : Word Field (QDoubleCylinderVertex P q S),
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) correction = syndrome ∧
        (∑ z : P.Z, HammingWeight (rxQOutgoing P q S correction z)) ≤
          HammingWeight syndrome := by
  obtain ⟨correction, hboundary, hweight⟩ := rxCq_exists_local_weight_le P q S syndrome hs
  refine ⟨correction, hboundary, ?_⟩
  rw [rxQOutgoing_sum_weight]
  exact hweight

/-- The X-to-Q matrix term is the sum of the actual adjacent edge restrictions. -/
theorem rxConnectingXQ1_apply_q
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (S : OddScale)
    (word : Word Field (RX1 P S)) (q : P.Q) (edge : QDoubleCylinderEdge P q S) :
    rxConnectingXQ1 P S word (Sum.inl (Sum.inr ⟨q, edge⟩)) =
      ∑ x : P.X, if hxq : P.xq x q = true then
        rxXQDegreeOne P A q x hxq S
          (fun localEdge => word (Sum.inl ⟨x, localEdge⟩)) edge else 0 := by
  classical
  rw [rxConnectingXQ1, wordLinearMapTranspose_toLin'_apply,
    Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [rxXQBoundary2Matrix, mul_zero, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hxq : P.xq x q = true
  · simp only [qDoubleCylinderEdgeXIncidence, dif_pos hxq]
    rw [Fintype.sum_eq_single (qToXDoubleCylinderEdgeRaw P q x hxq S edge)]
    · simp only [ite_true, mul_one, rxXQDegreeOne, wordPullback_apply]
      congr 1
    · intro other hne
      simp [hne]
  · simp [qDoubleCylinderEdgeXIncidence, hxq]

/-- The Q-to-Z matrix term is the sum of the actual two-terminal restrictions. -/
theorem rxConnectingQZ1_apply_z
    (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RX1 P S)) (z : P.Z) (copy : Two) :
    rxConnectingQZ1 P S word (Sum.inr (z, copy)) =
      ∑ q : P.Q, rxQOutgoing P q S
        (fun vertex => word (Sum.inr ⟨q, vertex⟩)) z copy := by
  classical
  rw [rxConnectingQZ1, wordLinearMapTranspose_toLin'_apply,
    Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [rxQZBoundary2Matrix, mul_zero, Finset.sum_const_zero, zero_add]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hqz : P.qz q z = true
  · rw [Fintype.sum_eq_single
      (copy, Sum.inl (Sum.inr (⟨z, hqz⟩ : QStarEdge P q)))]
    · simp [qDoubleCylinderVertexZIncidence, rxQOutgoing, hqz,
        rxQZDegreeOne, wordPullback_apply]
    · rintro ⟨otherCopy, vertex⟩ hne
      rcases vertex with (_ | terminal) | interior
      · simp [qDoubleCylinderVertexZIncidence, hqz]
      · have hne' : ¬ (otherCopy = copy ∧ terminal.1 = z) := by
          rintro ⟨rfl, hz⟩
          apply hne
          exact congrArg (fun t : QStarEdge P q =>
            ((otherCopy, Sum.inl (Sum.inr t)) : QDoubleCylinderVertex P q S))
            (Subtype.ext hz)
        simp [qDoubleCylinderVertexZIncidence, hqz, hne']
      · simp [qDoubleCylinderVertexZIncidence, hqz]
  · simp [qDoubleCylinderVertexZIncidence, rxQOutgoing, hqz]

/-- The X diagonal block is its concrete local cellular coboundary. -/
theorem rxLocalDelta1_apply_x
    (P : TannerSquarePresentation) (S : OddScale) (word : Word Field (RX1 P S))
    (x : P.X) (face : DoubleCylinderFace P x S) :
    rxLocalDelta1 P S word (Sum.inl (Sum.inl ⟨x, face⟩)) =
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
        (fun edge => word (Sum.inl ⟨x, edge⟩)) face := by
  classical
  rw [rxLocalDelta1, wordLinearMapTranspose_toLin'_apply, Fintype.sum_sum_type]
  simp only [rxLocalBoundary2Matrix, mul_zero, Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_sigma, Fintype.sum_eq_single x]
  · simp only [dif_pos rfl]
    rw [doubleCylinderBoundary2, wordLinearMapTranspose_toLin'_apply]
    simp only [dif_pos (show True from trivial)]
  · intro other hne
    simp only [dif_neg hne, mul_zero, Finset.sum_const_zero]

/-- The shifted Q diagonal block is its concrete local graph coboundary. -/
theorem rxLocalDelta1_apply_q
    (P : TannerSquarePresentation) (S : OddScale) (word : Word Field (RX1 P S))
    (q : P.Q) (edge : QDoubleCylinderEdge P q S) :
    rxLocalDelta1 P S word (Sum.inl (Sum.inr ⟨q, edge⟩)) =
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
        (fun vertex => word (Sum.inr ⟨q, vertex⟩)) edge := by
  classical
  rw [rxLocalDelta1, wordLinearMapTranspose_toLin'_apply, Fintype.sum_sum_type]
  simp only [rxLocalBoundary2Matrix, mul_zero, Finset.sum_const_zero, zero_add]
  rw [Fintype.sum_sigma, Fintype.sum_eq_single q]
  · simp only [dif_pos rfl]
    rw [qLocalCoboundary_apply]
    simp [qDoubleCylinderEdgeVertexIncidence, mul_add, Finset.sum_add_distrib]
  · intro other hne
    simp only [dif_neg hne, mul_zero, Finset.sum_const_zero]

end QEC.Coding.BDL26ReplacementSupport
