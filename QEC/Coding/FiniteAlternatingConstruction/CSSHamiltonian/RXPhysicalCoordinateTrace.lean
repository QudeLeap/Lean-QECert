import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.RXQEdgePairTransport
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.RXFaceEdgeTower

/-!
# Exhaustive geometric traces of actual physical coordinates

Project-derived constructor analysis for BDL26 paper.tex3398-3418,3445-3480,
SHA256 66d1927b20efccb757da40af3d291e4738c60054799812393e0a739abcc73e5b.
Trace data contain only original coordinates, tags and strictly decreasing
levels. They contain no decoder output, locality, stability or search evidence.
The two residual classes are C3 Q-edge-owner RX edges and all odd-level
old-X-owner RX edges. Their geometric existence is not a failure witness.
-/
noncomputable section
namespace QEC.Coding.BDL26RXPhysicalCoordinateTrace
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26HistorySyndromeSensitivity BDL26TannerLocalRegularity
open scoped Classical

def c2QEdgeOwner (S : OddScale) (q : (RawOne S).Q)
    (e : QDoubleCylinderEdge (transposePresentation (RawOne S)) q S) :
    (state S 2).presentation.X := .inl (.inr ⟨q,e⟩)

/-- Literal C2 old-X tags are kept without descending across the stopping point. -/
def oldXOwner (S : OddScale) : (m : Nat) → (ho : ¬m%2=0) →
    (state S m).presentation.X → BDL26FiniteTannerSquare.Two →
      (state S (m+1)).presentation.X
  | 0,ho,_,_ => False.elim (ho rfl)
  | 1,_,x,c => .inr (x,c)
  | m+2,ho,x,c => BDL26RZPhysicalXStarTransport.upperXChart S (m+3)
      ⟨m+2,by omega⟩ ho (.inr (x,c))

def c2QEdgePhysical (S : OddScale) (q : (RawOne S).Q)
    (e : QDoubleCylinderEdge (transposePresentation (RawOne S)) q S)
    (d : DoubleCylinderEdge (state S 2).presentation (c2QEdgeOwner S q e) S) :
    Physical S 3 :=
  BDL26RXDecoderAdapter.rxPhysicalQEquiv S 3 ⟨2,by omega⟩ (by decide)
    (.inl ⟨c2QEdgeOwner S q e,d⟩)

def oldXPhysical (S : OddScale) (m : Nat) (ho : ¬m%2=0)
    (x : (state S m).presentation.X) (c : BDL26FiniteTannerSquare.Two)
    (d : DoubleCylinderEdge (state S (m+1)).presentation (oldXOwner S m ho x c) S) :
    Physical S (m+2) :=
  BDL26RXDecoderAdapter.rxPhysicalQEquiv S (m+2) ⟨m+1,by omega⟩
    (by change (m+1)%2=0; omega)
    (.inl ⟨oldXOwner S m ho x c,d⟩)

/-- Two coordinate constructors, checked before specializing materialized carriers. -/
inductive PrimitiveCoordinates (Q : Type) (QE : Q → Type)
    (QD : (q : Q) → QE q → Type) (X : Nat → Type)
    (XD : (m : Nat) → (ho : ¬m%2=0) → X m → BDL26FiniteTannerSquare.Two → Type) :
    Nat → Type
  | c2QEdge (q : Q) (e : QE q) (d : QD q e) :
      PrimitiveCoordinates Q QE QD X XD 1
  | oldX (m : Nat) (ho : ¬m%2=0) (x : X m)
      (c : BDL26FiniteTannerSquare.Two)
      (d : XD m ho x c) : PrimitiveCoordinates Q QE QD X XD m

/-- Exact original carriers; no abstract geometry remains in the public seed type. -/
abbrev Primitive (S : OddScale) : Nat → Type :=
  PrimitiveCoordinates (RawOne S).Q
    (fun q => QDoubleCylinderEdge (transposePresentation (RawOne S)) q S)
    (fun q e => DoubleCylinderEdge (state S 2).presentation (c2QEdgeOwner S q e) S)
    (fun m => (state S m).presentation.X)
    (fun m ho x c =>
      DoubleCylinderEdge (state S (m+1)).presentation (oldXOwner S m ho x c) S)

abbrev Primitive.c2QEdge {S : OddScale} (q : (RawOne S).Q)
    (e : QDoubleCylinderEdge (transposePresentation (RawOne S)) q S)
    (d : DoubleCylinderEdge (state S 2).presentation (c2QEdgeOwner S q e) S) :
    Primitive S 1 := PrimitiveCoordinates.c2QEdge q e d

abbrev Primitive.oldX {S : OddScale} (m : Nat) (ho : ¬m%2=0)
    (x : (state S m).presentation.X) (c : BDL26FiniteTannerSquare.Two)
    (d : DoubleCylinderEdge (state S (m+1)).presentation (oldXOwner S m ho x c) S) :
    Primitive S m := PrimitiveCoordinates.oldX m ho x c d

def Primitive.physical {S : OddScale} {b : Nat} : Primitive S b → Physical S (b+2)
  | .c2QEdge q e d => c2QEdgePhysical S q e d
  | .oldX m ho x c d => oldXPhysical S m ho x c d

private def ActualPrimitiveData (S : OddScale) (b : Nat) : Type :=
  (Σ' _h : b=1, Σ q : (RawOne S).Q,
    Σ e : QDoubleCylinderEdge (transposePresentation (RawOne S)) q S,
      DoubleCylinderEdge (state S 2).presentation (c2QEdgeOwner S q e) S) ⊕
  (Σ' ho : ¬b%2=0, Σ x : (state S b).presentation.X,
    Σ c : BDL26FiniteTannerSquare.Two,
      DoubleCylinderEdge (state S (b+1)).presentation (oldXOwner S b ho x c) S)

private def primitiveDataEquiv (S : OddScale) (b : Nat) :
    Primitive S b ≃ ActualPrimitiveData S b where
  toFun := fun p => match p with
    | .c2QEdge q e d => .inl ⟨rfl,q,e,d⟩
    | .oldX _ ho x c d => .inr ⟨ho,x,c,d⟩
  invFun := fun data => match data with
    | .inl ⟨h,q,e,d⟩ => by
        cases h
        exact Primitive.c2QEdge (S:=S) q e d
    | .inr ⟨ho,x,c,d⟩ => Primitive.oldX (S:=S) b ho x c d
  left_inv := by
    intro p
    cases p <;> rfl
  right_inv := by
    intro data
    rcases data with ⟨h,q,e,d⟩ | ⟨ho,x,c,d⟩
    · cases h
      rfl
    · rfl

private theorem primitive_c2_physical {S : OddScale} (q : (RawOne S).Q)
    (e : QDoubleCylinderEdge (transposePresentation (RawOne S)) q S)
    (d : DoubleCylinderEdge (state S 2).presentation (c2QEdgeOwner S q e) S) :
    (Primitive.c2QEdge (S:=S) q e d).physical=c2QEdgePhysical S q e d := rfl

private theorem primitive_oldX_physical {S : OddScale} (m : Nat) (ho : ¬m%2=0)
    (x : (state S m).presentation.X) (c : BDL26FiniteTannerSquare.Two)
    (d : DoubleCylinderEdge (state S (m+1)).presentation (oldXOwner S m ho x c) S) :
    (Primitive.oldX (S:=S) m ho x c d).physical=oldXPhysical S m ho x c d := rfl

theorem primitive_positive {S : OddScale} {b : Nat} (p : Primitive S b) : 1≤b := by
  rcases primitiveDataEquiv S b p with ⟨h,q,e,d⟩ | ⟨ho,x,c,d⟩
  · omega
  · omega

theorem primitive_odd {S : OddScale} {b : Nat} (p : Primitive S b) : ¬b%2=0 := by
  rcases primitiveDataEquiv S b p with ⟨h,q,e,d⟩ | ⟨ho,x,c,d⟩
  · subst b
    decide
  · exact ho

/-- A leaf is geometry data, not a stored semantic conclusion. -/
inductive Leaf (S : OddScale) : Type
  | c2 (q : Physical S 2)
  | face (a : BDL26RXFaceEdgeTower.Seed S)
  | killed (b : Nat)
  | primitive {b : Nat} (p : Primitive S b)

def Leaf.safe {S : OddScale} : Leaf S → Bool
  | .c2 _ => true
  | .face _ => true
  | .killed _ => true
  | .primitive _ => false

inductive Trace (S : OddScale) : (b : Nat) → Physical S (b+2) → Leaf S → Type
  | c2 (q : Physical S 2) : Trace S 0 q (.c2 q)
  | face (a : BDL26RXFaceEdgeTower.Seed S) :
      Trace S 1 (BDL26RXFaceEdgeTower.seedPhysical S a) (.face a)
  | rzEdge (b : Nat) (ho : ¬(b+2)%2=0) (z : (state S (b+2)).presentation.Z)
      (e : ZDoubleCylinderEdge (state S (b+2)).presentation z S) :
      Trace S (b+1) (BDL26RZLocalEdgeTower.rzLocalEdge S (b+2) ho z e) (.killed b)
  | higherFace (j : Nat) (a : BDL26HigherRXFaceTower.SeedData S j) :
      Trace S (2*j+3) (BDL26HigherRXFaceTower.seedPhysical S j a) (.killed (2*j+1))
  | primitive {b : Nat} (p : Primitive S b) : Trace S b p.physical (.primitive p)
  | rx {b : Nat} {q : Physical S (b+2)} {leaf : Leaf S}
      (t : Trace S b q leaf) (he : (b+2)%2=0)
      (v : QDoubleCylinderVertex (state S (b+2)).presentation q S) :
      Trace S (b+1) (BDL26FirstZeroQVertexTower.rxVertex S (b+2) he q v) leaf
  | rz {b : Nat} {q : Physical S (b+2)} {leaf : Leaf S}
      (t : Trace S b q leaf) (ho : ¬(b+2)%2=0)
      (v : QDoubleCylinderVertex (transposePresentation (state S (b+2)).presentation) q S) :
      Trace S (b+1) (BDL26FirstZeroQVertexTower.rzVertex S (b+2) ho q v) leaf
  | qEdgePair (j : Nat) (a : BDL26RXQEdgePairTransport.Seed S j) {leaf : Leaf S}
      (t : Trace S (2*j+1) a.1 leaf) :
      Trace S (2*j+3) (BDL26RXQEdgePairTransport.seedPhysical S j a) leaf

private theorem primitive_trace_of_physical_eq {S : OddScale} {b : Nat}
    (p : Primitive S b) {q : Physical S (b+2)} (h : p.physical=q) :
    Nonempty (Trace S b q (.primitive p)) := by
  subst q
  exact ⟨Trace.primitive p⟩

theorem rx_vertex_chart (S : OddScale) (m : Nat) (he : m%2=0)
    (q : Physical S m) (v : QDoubleCylinderVertex (state S m).presentation q S) :
    BDL26FirstZeroQVertexTower.rxVertex S m he q v=
      BDL26RXDecoderAdapter.rxPhysicalQEquiv S (m+1) ⟨m,by omega⟩ he (.inr ⟨q,v⟩) := by
  simpa only [BDL26FirstZeroQVertexTower.rxVertex] using
    (BDL26RXDecoderAdapter.rxQVertexEquiv_val S (m+1) ⟨m,by omega⟩ he q v)

theorem rz_vertex_chart (S : OddScale) (m : Nat) (ho : ¬m%2=0)
    (q : Physical S m)
    (v : QDoubleCylinderVertex (transposePresentation (state S m).presentation) q S) :
    BDL26FirstZeroQVertexTower.rzVertex S m ho q v=
      BDL26RZPhysicalStarTransport.upperQChart S (m+1) ⟨m,by omega⟩ ho (.inr ⟨q,v⟩) := by
  unfold BDL26FirstZeroQVertexTower.rzVertex BDL26RZPhysicalStarTransport.physicalQ
  rfl

/-- All physical coordinates are reconstructed by the actual chart inverses. -/
theorem trace_total (S : OddScale) (n : Nat) (q : Physical S (n+2)) :
    ∃ leaf : Leaf S, Nonempty (Trace S n q leaf) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n=0
    · subst n
      exact ⟨.c2 q,⟨Trace.c2 q⟩⟩
    by_cases hn1 : n=1
    · subst n
      obtain ⟨r,rfl⟩ := (BDL26RXDecoderAdapter.rxPhysicalQEquiv S 3 ⟨2,by omega⟩
        (by decide)).surjective q
      rcases r with ⟨owner,d⟩ | ⟨r,v⟩
      · rcases owner with (⟨z,f⟩ | ⟨r,e⟩) | ⟨x,c⟩
        · refine ⟨.face ⟨z,f,d⟩,?_⟩
          simpa only [BDL26RXFaceEdgeTower.seedPhysical,BDL26RXFaceEdgeTower.faceOwner]
            using (Nonempty.intro (Trace.face (S:=S) ⟨z,f,d⟩))
        · refine ⟨.primitive (.c2QEdge r e d),?_⟩
          apply primitive_trace_of_physical_eq (Primitive.c2QEdge (S:=S) r e d)
          simpa only [c2QEdgePhysical,c2QEdgeOwner] using
            (primitive_c2_physical (S:=S) r e d)
        · refine ⟨.primitive (.oldX 1 (by decide) x c d),?_⟩
          apply primitive_trace_of_physical_eq (Primitive.oldX (S:=S) 1 (by decide) x c d)
          simpa only [oldXPhysical,oldXOwner] using
            (primitive_oldX_physical (S:=S) 1 (by decide) x c d)
      · obtain ⟨leaf,⟨t⟩⟩ := ih 0 (by omega) r
        refine ⟨leaf,?_⟩
        rw [← rx_vertex_chart S 2 (by decide) r v]
        exact ⟨Trace.rx t (by decide) v⟩
    by_cases he : n%2=0
    · obtain ⟨j,hj⟩ : ∃ j : Nat, n=2*j+2 := ⟨(n-2)/2,by omega⟩
      subst n
      obtain ⟨r,rfl⟩ := (BDL26RZPhysicalStarTransport.upperQChart S (2*j+4)
        ⟨2*j+3,by omega⟩ (by change ¬(2*j+3)%2=0; omega)).surjective q
      rcases r with ⟨z,e⟩ | ⟨r,v⟩
      · refine ⟨.killed (2*j+1),?_⟩
        exact ⟨Trace.rzEdge (2*j+1) (by omega) z e⟩
      · obtain ⟨leaf,⟨t⟩⟩ := ih (2*j+1) (by omega) r
        refine ⟨leaf,?_⟩
        rw [← rz_vertex_chart S (2*j+3) (by omega) r v]
        exact ⟨Trace.rz t (by omega) v⟩
    · obtain ⟨j,hj⟩ : ∃ j : Nat, n=2*j+3 :=
        BDL26RXQEdgePairTransport.odd_ge_three n (by omega) he
      subst n
      obtain ⟨r,rfl⟩ := (BDL26RXDecoderAdapter.rxPhysicalQEquiv S (2*j+5)
        ⟨2*j+4,by omega⟩ (by change (2*j+4)%2=0; omega)).surjective q
      rcases r with ⟨owner,d⟩ | ⟨r,v⟩
      · obtain ⟨x,rfl⟩ := (BDL26RZPhysicalXStarTransport.upperXChart S (2*j+4)
          ⟨2*j+3,by omega⟩ (by change ¬(2*j+3)%2=0; omega)).surjective owner
        rcases x with (⟨z,f⟩ | ⟨r,e⟩) | ⟨x,c⟩
        · refine ⟨.killed (2*j+1),?_⟩
          exact ⟨Trace.higherFace j ⟨z,f,d⟩⟩
        · obtain ⟨leaf,⟨t⟩⟩ := ih (2*j+1) (by omega) r
          exact ⟨leaf,⟨Trace.qEdgePair j ⟨r,e,d⟩ t⟩⟩
        · refine ⟨.primitive (.oldX (2*j+3) (by omega) x c d),?_⟩
          apply primitive_trace_of_physical_eq
            (Primitive.oldX (S:=S) (2*j+3) (by omega) x c d)
          simpa only [oldXPhysical,oldXOwner] using
            (primitive_oldX_physical (S:=S) (2*j+3) (by omega) x c d)
      · obtain ⟨leaf,⟨t⟩⟩ := ih (2*j+2) (by omega) r
        refine ⟨leaf,?_⟩
        rw [← rx_vertex_chart S (2*j+4) (by omega) r v]
        exact ⟨Trace.rx t (by omega) v⟩

def parse (S : OddScale) (n : Nat) (q : Physical S (n+2)) : Leaf S :=
  Classical.choose (trace_total S n q)

def parsedTrace (S : OddScale) (n : Nat) (q : Physical S (n+2)) : Trace S n q (parse S n q) :=
  Classical.choice (Classical.choose_spec (trace_total S n q))

theorem parse_reconstruct (S : OddScale) (n : Nat) (q : Physical S (n+2)) :
    Nonempty (Trace S n q (parse S n q)) := ⟨parsedTrace S n q⟩

/- Every recursive branch removes one or two actual physical levels. -/
end QEC.Coding.BDL26RXPhysicalCoordinateTrace
