import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Flow

/-! # Actual RX graph identities -/

namespace QEC.Coding.BDL26RXDecoderAdapter

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

-- Exact relabelling of the existing Tanner graph; no new edges.
noncomputable def vertexEquiv (P : TannerSquarePresentation) :
    RXCoarseGraining.RXVertex P.X P.Q P.Z ≃ Vertex P where
  toFun
    | .inl x => .x x
    | .inr (.inl q) => .q q
    | .inr (.inr z) => .z z
  invFun
    | .x x => .inl x
    | .q q => .inr (.inl q)
    | .z z => .inr (.inr z)
  left_inv := by intro v; rcases v with x | (q | z) <;> rfl
  right_inv := by intro v; cases v <;> rfl

noncomputable def rxLevel (P : TannerSquarePresentation) :
    LevelGraph (RXCoarseGraining.RXVertex P.X P.Q P.Z) where
  skeleton :=
    { adjacent := fun u v => (tannerSkeleton P).adjacent (vertexEquiv P u) (vertexEquiv P v)
      symmetric := fun _ _ h => (tannerSkeleton P).symmetric h
      loopless := fun u => (tannerSkeleton P).loopless (vertexEquiv P u) }
  kind := fun v => vertexKind P (vertexEquiv P v)
  skeletonDecidable := fun u v => tannerAdjacentDecidable P (vertexEquiv P u) (vertexEquiv P v)

theorem rxLevel_edge (P : TannerSquarePresentation) (u v) :
    (rxLevel P).graph.edge u v = (tannerLevel P).graph.edge (vertexEquiv P u) (vertexEquiv P v) := rfl

-- Distance in the existing finite graph, using DirectedDistance equivalence.
theorem distance_le_one_iff {V : Type} [Fintype V] [DecidableEq V]
    (G : DirectedGraph V) (u v : V) :
    G.distance u v ≤ (1 : WithTop Nat) ↔ u = v ∨ G.edge u v = true := by
  letI : Nonempty V := ⟨u⟩
  have hr : G.distance u v ≤ (1 : WithTop Nat) ↔ G.reachableWithin 1 u v = true := by
    simpa using DirectedGraph.distance_le_iff_reachableWithin G u v 1
      (Nat.succ_le_iff.mpr Fintype.card_pos)
  rw [hr]
  simp [DirectedGraph.reachableWithin]

theorem distance_one_comp {V : Type} [Fintype V] [DecidableEq V]
    (G : DirectedGraph V) (u v w : V)
    (huv : G.distance u v ≤ (1 : WithTop Nat))
    (hvw : G.distance v w ≤ (1 : WithTop Nat)) :
    G.distance u w ≤ (2 : WithTop Nat) := by
  by_cases huw : u = w
  · subst w
    exact ((distance_le_one_iff G u u).mpr (Or.inl rfl)).trans (by norm_num)
  rcases (distance_le_one_iff G u v).mp huv with heq | he
  · subst v
    exact hvw.trans (by norm_num)
  rcases (distance_le_one_iff G v w).mp hvw with heq | hf
  · subst w
    exact huv.trans (by norm_num)
  letI : Nontrivial V := ⟨⟨u,w,huw⟩⟩
  have hcard : 2 ≤ Fintype.card V := Fintype.one_lt_card
  have hr : G.reachableWithin 2 u w = true := by
    simp only [DirectedGraph.reachableWithin, Bool.or_eq_true_eq_eq_true_or_eq_true,
      decide_eq_true_eq]
    exact Or.inr ⟨v,he,Or.inr ⟨w,hf,rfl⟩⟩
  have hd := (DirectedGraph.distance_le_iff_reachableWithin G u w 2 hcard).mpr hr
  simpa using hd

noncomputable def topCenter (P : TannerSquarePresentation) (S : OddScale) :
    RX2 P S → RXCoarseGraining.RXVertex P.X P.Q P.Z :=
  fun p => (vertexEquiv P).symm (rxSyndromeOwner P S p)

theorem xFlow_radius_one (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (w : Word BDL26Field (DoubleCylinderEdge P x S))
    (p : RX2 P S) (hp : xFlow P S x w p ≠ 0) :
    DirectedGraph.distance (rxLevel P).graph (Sum.inl x) (topCenter P S p) ≤ 1 := by
  rcases p with (⟨y,f⟩ | ⟨q,e⟩) | ⟨z,c⟩
  · exact (hp (xFlow_at_x P S x y w f)).elim
  · have hxq : P.xq x q = true := by
      by_contra h
      exact hp (by rw [xFlow_at_q P A, dif_neg h])
    apply (distance_le_one_iff _ _ _).mpr
    right
    change (rxLevel P).graph.edge (Sum.inl x) (Sum.inr (Sum.inl q)) = true
    rw [rxLevel_edge, tannerLevel_edge]
    exact hxq
  · exact (hp (xFlow_at_z P S x w z c)).elim

theorem qFlow_radius_one (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (p : RX2 P S) (hp : qFlow P S q w p ≠ 0) :
    DirectedGraph.distance (rxLevel P).graph (Sum.inr (Sum.inl q)) (topCenter P S p) ≤ 1 := by
  rcases p with (⟨x,f⟩ | ⟨r,e⟩) | ⟨z,c⟩
  · exact (hp (qFlow_at_x P S q w x f)).elim
  · exact (hp (qFlow_at_q P S q r w e)).elim
  · have hqz : P.qz q z = true := by
      by_contra h
      exact hp (by rw [qFlow_at_z, rxQOutgoing_nonincident P q S w z h]; rfl)
    apply (distance_le_one_iff _ _ _).mpr
    right
    change (rxLevel P).graph.edge (Sum.inr (Sum.inl q)) (Sum.inr (Sum.inr z)) = true
    rw [rxLevel_edge, tannerLevel_edge]
    exact hqz

end QEC.Coding.BDL26RXDecoderAdapter
