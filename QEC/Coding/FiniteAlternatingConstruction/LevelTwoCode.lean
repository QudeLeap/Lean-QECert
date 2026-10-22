import QEC.Coding.FiniteAlternatingConstruction.QuantitativeBounds

/-!
# The concrete level-two code and its finite size

The code is exactly one RX/RZ pair on the audited seed. The cardinalities are
exact finite sums of materialized local-cell counts, not evaluated polynomials.
The explicit polynomial upper bound is project-derived from the finite growth
recurrence; BDL26 only states O(ell^4). No distance or decoder is assumed.
-/

namespace QEC.Coding.BDL26LevelTwoCode

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators

/-- The intermediate presentation is the actual RX replacement of the seed. -/
noncomputable def levelOnePresentation (S : OddScale) : TannerSquarePresentation :=
  (rxState S baseState).presentation

/-- The selected stopping code is the actual recursive state at index two. -/
noncomputable def levelTwoState (S : OddScale) : ConstructionState := state S 2

/-- Identify the recursive stopping state with the ordered RX/RZ pair. -/
theorem levelTwoState_eq_pair (S : OddScale) :
    levelTwoState S = rzState S (rxState S baseState) := by
  simp [levelTwoState, state, nextState]

noncomputable def levelTwoPresentation (S : OddScale) : TannerSquarePresentation :=
  (levelTwoState S).presentation

/-- The three code-coordinate sets, with no caller-supplied successor data. -/
noncomputable def levelTwoCarrier (S : OddScale) : FiniteCochainCarrier where
  C0 := (levelTwoPresentation S).X
  C1 := (levelTwoPresentation S).Q
  C2 := (levelTwoPresentation S).Z
  fintypeC0 := inferInstance
  fintypeC1 := inferInstance
  fintypeC2 := inferInstance

/-- The code boundary matrices are the actual Tanner incidences. -/
noncomputable def levelTwoBoundary1 (S : OddScale) :=
  Matrix.toLin' (xqIncidenceMatrix (levelTwoPresentation S))

noncomputable def levelTwoBoundary2 (S : OddScale) :=
  Matrix.toLin' (qzIncidenceMatrix (levelTwoPresentation S))

/-- Perfect pairing of the constructed Tanner squares proves the chain law. -/
theorem levelTwoBoundary_squared (S : OddScale) :
    (levelTwoBoundary1 S).comp (levelTwoBoundary2 S) = 0 := by
  unfold levelTwoBoundary1 levelTwoBoundary2
  rw [← Matrix.toLin'_mul, xqIncidenceMatrix_mul_qzIncidenceMatrix]
  simp

/-- The concrete finite C_2 chain complex, rather than just its carrier. -/
noncomputable def levelTwoChainComplex (S : OddScale) :
    ChainComplexData BDL26FiniteTannerSquare.Field
      (Word BDL26FiniteTannerSquare.Field (levelTwoPresentation S).X)
      (Word BDL26FiniteTannerSquare.Field (levelTwoPresentation S).Q)
      (Word BDL26FiniteTannerSquare.Field (levelTwoPresentation S).Z) where
  boundary1 := levelTwoBoundary1 S
  boundary2 := levelTwoBoundary2 S
  boundary_squared := levelTwoBoundary_squared S

/-! Explicit finite instances keep replacement-carrier inference bounded. -/
private abbrev rzXFintype (P : TannerSquarePresentation) (S : OddScale) :
    Fintype (RZX P S) := by
  dsimp [RZX, ZDoubleCylinderFace, QDoubleCylinderEdge,
    DoubleCylinderFace, transposePresentation, transposeTannerSquareData]
  infer_instance

private abbrev rzQFintype (P : TannerSquarePresentation) (S : OddScale) :
    Fintype (RZQ P S) := by
  dsimp [RZQ, ZDoubleCylinderEdge, QDoubleCylinderVertex,
    DoubleCylinderEdge, transposePresentation, transposeTannerSquareData]
  infer_instance

private abbrev rzZFintype (P : TannerSquarePresentation) (S : OddScale) :
    Fintype (RZZ P S) := by
  dsimp [RZZ, ZDoubleCylinderVertex, DoubleCylinderVertex,
    transposePresentation, transposeTannerSquareData]
  infer_instance

private abbrev rzFaceFintype (P : TannerSquarePresentation) (S : OddScale) :
    Fintype (RZFace P S) := by
  dsimp [RZFace, RZLocalFace, RZQZGlueFace, RZOldXFace,
    ZDoubleCylinderFace, QDoubleCylinderEdge, DoubleCylinderFace,
    transposePresentation, transposeTannerSquareData]
  infer_instance

/-- Exact X-check count: Z-local faces, Q-local edges, and two copies of old X. -/
theorem rzPresentationX_card (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    Fintype.card (BDL26RZLocalReplacement.rzReplacementPresentation P A S).X =
      ((∑ z : P.Z,
        Fintype.card (ZDoubleCylinderFace P z S)) +
       (∑ q : P.Q,
        Fintype.card (QDoubleCylinderEdge (transposePresentation P) q S))) +
      Fintype.card P.X * 2 := by
  let : Fintype (RZX P S) := rzXFintype P S
  have hcarrier :
      Fintype.card (BDL26RZLocalReplacement.rzReplacementPresentation P A S).X =
        Fintype.card (RZX P S) := Fintype.card_congr (Equiv.refl _)
  rw [hcarrier]
  simp only [← Nat.card_eq_fintype_card, RZX, Nat.card_sum, Nat.card_sigma, Nat.card_prod,
        BDL26RZLocalReplacement.Two, BDL26FiniteTannerSquare.Two, Nat.card_fin]

/-- Exact physical-qubit count from both disjoint RZ degree-one families. -/
theorem rzPresentationQ_card (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    Fintype.card (BDL26RZLocalReplacement.rzReplacementPresentation P A S).Q =
      (∑ z : P.Z,
        Fintype.card (ZDoubleCylinderEdge P z S)) +
      (∑ q : P.Q,
        Fintype.card (QDoubleCylinderVertex (transposePresentation P) q S)) := by
  let : Fintype (RZQ P S) := rzQFintype P S
  let : Fintype (Sigma fun z : P.Z => ZDoubleCylinderEdge P z S) := by
    dsimp [ZDoubleCylinderEdge, DoubleCylinderEdge,
      transposePresentation, transposeTannerSquareData]
    infer_instance
  let : Fintype (Sigma fun q : P.Q =>
      QDoubleCylinderVertex (transposePresentation P) q S) := by
    dsimp [QDoubleCylinderVertex, transposePresentation, transposeTannerSquareData]
    infer_instance
  have hcarrier :
      Fintype.card (BDL26RZLocalReplacement.rzReplacementPresentation P A S).Q =
        Fintype.card (RZQ P S) := Fintype.card_congr (Equiv.refl _)
  rw [hcarrier]
  simp only [← Nat.card_eq_fintype_card, RZQ, Nat.card_sum, Nat.card_sigma]

/-- Exact Z-check count from the intrinsic Z-local zero-cell family. -/
theorem rzPresentationZ_card (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    Fintype.card (BDL26RZLocalReplacement.rzReplacementPresentation P A S).Z =
      ∑ z : P.Z,
        Fintype.card (ZDoubleCylinderVertex P z S) := by
  let : Fintype (RZZ P S) := rzZFintype P S
  have hcarrier :
      Fintype.card (BDL26RZLocalReplacement.rzReplacementPresentation P A S).Z =
        Fintype.card (RZZ P S) := Fintype.card_congr (Equiv.refl _)
  rw [hcarrier]
  simp only [← Nat.card_eq_fintype_card, RZZ, Nat.card_sigma]

/-- Exact face count, retaining local, Q-Z glue, and old-X-copy faces. -/
theorem rzPresentationFace_card (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    Fintype.card (BDL26RZLocalReplacement.rzReplacementPresentation P A S).Face =
      (∑ z : P.Z,
        Fintype.card (ZDoubleCylinderFace P z S) * (2 * 2)) +
      ((∑ e : QZEdge P,
        Fintype.card (QDoubleCylinderEdge
          (transposePresentation P) e.1.1 S) * 2) +
       Fintype.card P.Face * 2) := by
  let : Fintype (RZFace P S) := rzFaceFintype P S
  have hcarrier :
      Fintype.card (BDL26RZLocalReplacement.rzReplacementPresentation P A S).Face =
        Fintype.card (RZFace P S) := Fintype.card_congr (Equiv.refl _)
  rw [hcarrier]
  simp only [← Nat.card_eq_fintype_card, RZFace, RZLocalFace, RZQZGlueFace, RZOldXFace,
        Nat.card_sum, Nat.card_sigma, Nat.card_prod,
        BDL26RZLocalReplacement.Two, BDL26FiniteTannerSquare.Two, Nat.card_fin]

/-- Exact X-check count: Z-local faces, Q-local edges, and two copies of old X. -/
theorem levelTwoX_card (S : OddScale) :
    Fintype.card (levelTwoPresentation S).X =
      ((∑ z : (levelOnePresentation S).Z,
        Fintype.card (ZDoubleCylinderFace (levelOnePresentation S) z S)) +
       (∑ q : (levelOnePresentation S).Q,
        Fintype.card (QDoubleCylinderEdge (transposePresentation (levelOnePresentation S)) q S))) +
      Fintype.card (levelOnePresentation S).X * 2 := by
  exact rzPresentationX_card (levelOnePresentation S)
    (rxState S baseState).admissible.toTannerSquareAdmissible S

/-- Exact physical-qubit count from both disjoint RZ degree-one families. -/
theorem levelTwoQ_card (S : OddScale) :
    Fintype.card (levelTwoPresentation S).Q =
      (∑ z : (levelOnePresentation S).Z,
        Fintype.card (ZDoubleCylinderEdge (levelOnePresentation S) z S)) +
      (∑ q : (levelOnePresentation S).Q,
        Fintype.card (QDoubleCylinderVertex (transposePresentation (levelOnePresentation S)) q S)) := by
  exact rzPresentationQ_card (levelOnePresentation S)
    (rxState S baseState).admissible.toTannerSquareAdmissible S

/-- Exact Z-check count from the intrinsic Z-local zero-cell family. -/
theorem levelTwoZ_card (S : OddScale) :
    Fintype.card (levelTwoPresentation S).Z =
      ∑ z : (levelOnePresentation S).Z,
        Fintype.card (ZDoubleCylinderVertex (levelOnePresentation S) z S) := by
  exact rzPresentationZ_card (levelOnePresentation S)
    (rxState S baseState).admissible.toTannerSquareAdmissible S

/-- Exact face count, retaining local, Q-Z glue, and old-X-copy faces. -/
theorem levelTwoFace_card (S : OddScale) :
    Fintype.card (levelTwoPresentation S).Face =
      (∑ z : (levelOnePresentation S).Z,
        Fintype.card (ZDoubleCylinderFace (levelOnePresentation S) z S) * (2 * 2)) +
      ((∑ e : QZEdge (levelOnePresentation S),
        Fintype.card (QDoubleCylinderEdge
          (transposePresentation (levelOnePresentation S)) e.1.1 S) * 2) +
       Fintype.card (levelOnePresentation S).Face * 2) := by
  exact rzPresentationFace_card (levelOnePresentation S)
    (rxState S baseState).admissible.toTannerSquareAdmissible S
/-- The actual five-qubit seed and both root injections give a nonzero size. -/
theorem levelTwoQ_card_lower (S : OddScale) :
    20 ≤ Fintype.card (levelTwoPresentation S).Q := by
  have h := state_qubit_card_lower S 2
  norm_num only at h
  exact h

/-- The exact finite recurrence specializes to the level-two stopping code. -/
theorem levelTwoQ_card_upper (S : OddScale) :
    Fintype.card (levelTwoPresentation S).Q ≤
      8 * (2 * S.ell * (S.ell + 2)) ^ 2 :=
  state_qubit_card_upper S 2

/-- A uniform explicit witness for the source O(ell^4) claim. -/
theorem levelTwoQ_card_le_quartic (S : OddScale) :
    Fintype.card (levelTwoPresentation S).Q ≤ 288 * S.ell ^ 4 := by
  have hthree := S.three_le
  have hsum : S.ell + 2 ≤ 3 * S.ell := by omega
  have hfactor : 2 * S.ell * (S.ell + 2) ≤ 6 * S.ell ^ 2 := by
    calc
      _ ≤ 2 * S.ell * (3 * S.ell) := Nat.mul_le_mul_left _ hsum
      _ = 6 * S.ell ^ 2 := by ring
  calc
    _ ≤ 8 * (2 * S.ell * (S.ell + 2)) ^ 2 := levelTwoQ_card_upper S
    _ ≤ 8 * (6 * S.ell ^ 2) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hfactor 2)
    _ = 288 * S.ell ^ 4 := by ring

/-- The shared graph API has a singleton index zero, hence C_2 is graph index 3. -/
theorem levelTwo_graph_index (S : OddScale) :
    level S 3 = tannerLevel (levelTwoPresentation S) := rfl

/-- The stopping code's local correction regions are exactly its Tanner stars. -/
theorem levelTwo_correctionRegion_mem (S : OddScale)
    (u v : Vertex (levelTwoPresentation S)) :
    u ∈ (correctionRegion S 2 v).vertices ↔
      u = v ∨ tannerDirected (levelTwoPresentation S) u v = true :=
  correctionRegion_mem S 2 u v

end QEC.Coding.BDL26LevelTwoCode
