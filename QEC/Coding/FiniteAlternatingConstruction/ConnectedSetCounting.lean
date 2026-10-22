import QEC.Locality.Graph.ConnectedSetCounting
import QEC.Coding.FiniteAlternatingConstruction.GraphQuantitativeBounds

/-!
# Actual decoding-graph connected-set enumeration

Internal refinement of BDL26 v1 `bdl26-witness-counting`, paper.tex:3658–3673.
The relation is literally the unchanged level-union decodingGraph adjacency.
The already-proved degree14*ell^2+8 gives alphabet bound14*ell^2+9. Anchors
are precisely the actual nodes at level2, empty at truncation depths0 and1.
No decoder-consistent witness or minimum-size/stability statement is asserted.
-/
noncomputable section
namespace QEC.Coding.BDL26ConnectedSetCounting
open Classical MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26GraphQuantitativeBounds

private theorem family_symmetric {depth : Nat} {V : LevelIndex depth → Type}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] (D : DecodingGraphFamily depth V) :
    Symmetric D.adjacent := by
  rintro ⟨i,x⟩ ⟨j,y⟩ h
  simp only [DecodingGraphFamily.adjacent] at h ⊢
  rcases h with h | h | h
  · by_cases hij : i = j
    · subst j
      left
      simpa only [dif_pos rfl, dite_true] using
        (D.level i).skeleton.symmetric (by simpa only [dif_pos rfl, dite_true] using h)
    · simp only [dif_neg hij] at h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

private theorem family_loopless {depth : Nat} {V : LevelIndex depth → Type}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] (D : DecodingGraphFamily depth V) :
    Irreflexive D.adjacent := by
  rintro ⟨i,x⟩ h
  simp only [DecodingGraphFamily.adjacent, dif_pos rfl] at h
  rcases h with h | h | h
  · exact (D.level i).skeleton.loopless x h
  all_goals
    obtain ⟨s,hs⟩ := h
    by_cases h0 : i = s.castSucc
    · by_cases h1 : i = s.succ
      · have he := congrArg Fin.val (h0.symm.trans h1)
        simp only [Fin.val_castSucc, Fin.val_succ] at he
        omega
      · simpa only [dif_pos h0, dif_neg h1] using hs
    · simpa only [dif_neg h0] using hs

/-- SimpleGraph conversion with EXACT original adjacency and no added edges. -/
def graph (S : OddScale) (depth : Nat) : SimpleGraph (decodingGraph S depth).Node where
  Adj := (decodingGraph S depth).adjacent
  symm := ⟨family_symmetric _⟩
  loopless := ⟨family_loopless _⟩

theorem graph_adj_iff (S : OddScale) (depth : Nat) (u v : (decodingGraph S depth).Node) :
    (graph S depth).Adj u v ↔ (decodingGraph S depth).adjacent u v := Iff.rfl

theorem graph_degree_bound (S : OddScale) (depth : Nat) (u : (decodingGraph S depth).Node) :
    Nat.card {v : (decodingGraph S depth).Node // (graph S depth).Adj u v} ≤ 14*S.ell^2+8 := by
  change Nat.card {v : (decodingGraph S depth).Node //
    (decodingGraph S depth).adjacent u v} ≤ 14*S.ell^2+8
  simpa only [fullGraphDegreeBound,localCoordinateBound] using decodingGraph_degree_bound S depth u

def rootedSets (S : OddScale) (depth : Nat) (r : (decodingGraph S depth).Node) (m : Nat) :=
  Locality.ConnectedSetCounting.rooted (graph S depth) r m

def anchoredSets (S : OddScale) (depth : Nat)
    (R : Finset (decodingGraph S depth).Node) (m : Nat) :=
  Locality.ConnectedSetCounting.anchored (graph S depth) R m

/-- Literal level-two membership, including root/top truncation cases. -/
def levelTwoAnchors (S : OddScale) (depth : Nat) : Finset (decodingGraph S depth).Node := by
  classical
  exact Finset.univ.filter fun v => v.1.val = 2

def levelTwoSets (S : OddScale) (depth m : Nat) :=
  anchoredSets S depth (levelTwoAnchors S depth) m

theorem mem_levelTwoAnchors (S : OddScale) (depth : Nat) (v : (decodingGraph S depth).Node) :
    v ∈ levelTwoAnchors S depth ↔ v.1.val = 2 := by
  classical
  simp [levelTwoAnchors]

/-- The induced connectivity is taken on the complete supplied vertex set. -/
theorem mem_levelTwoSets (S : OddScale) (depth m : Nat)
    (A : Finset (decodingGraph S depth).Node) :
    A ∈ levelTwoSets S depth m ↔ A.card = m ∧
      ((graph S depth).induce (A : Set (decodingGraph S depth).Node)).Connected ∧
      (A ∩ levelTwoAnchors S depth).Nonempty :=
  Locality.ConnectedSetCounting.mem_anchored (graph S depth) _ m A

theorem rootedSets_card_le (S : OddScale) (depth : Nat)
    (r : (decodingGraph S depth).Node) (m : Nat) :
    (rootedSets S depth r m).card ≤ (14*S.ell^2+9)^(2*m) := by
  have h := Locality.ConnectedSetCounting.rooted_card_le (graph S depth)
    (14*S.ell^2+8) (graph_degree_bound S depth) r m
  simpa only [rootedSets, Nat.add_assoc] using h

theorem anchoredSets_card_le (S : OddScale) (depth : Nat)
    (R : Finset (decodingGraph S depth).Node) (m : Nat) :
    (anchoredSets S depth R m).card ≤ R.card * (14*S.ell^2+9)^(2*m) := by
  have h := Locality.ConnectedSetCounting.anchored_card_le (graph S depth)
    (14*S.ell^2+8) (graph_degree_bound S depth) R m
  simpa only [anchoredSets, Nat.add_assoc] using h

/-- The source's |V2| factor, with its actual finite anchor carrier. -/
theorem levelTwoSets_card_le (S : OddScale) (depth m : Nat) :
    (levelTwoSets S depth m).card ≤
      (levelTwoAnchors S depth).card * (14*S.ell^2+9)^(2*m) :=
  anchoredSets_card_le S depth _ m

theorem levelTwoAnchors_empty (S : OddScale) (depth : Nat) (hd : depth < 2) :
    levelTwoAnchors S depth = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro v hv
  have he := (mem_levelTwoAnchors S depth v).mp hv
  have hi := v.1.isLt
  omega

theorem levelTwoSets_empty_below_two (S : OddScale) (depth m : Nat) (hd : depth < 2) :
    levelTwoSets S depth m = ∅ := by
  unfold levelTwoSets
  rw [levelTwoAnchors_empty S depth hd]
  exact Locality.ConnectedSetCounting.anchored_empty (graph S depth) m

theorem levelTwoSets_zero (S : OddScale) (depth : Nat) : levelTwoSets S depth 0 = ∅ :=
  Locality.ConnectedSetCounting.anchored_zero (graph S depth) _

/-- The full rooted formula includes m=1 without a nontriviality premise. -/
theorem rootedSets_one_card_le (S : OddScale) (depth : Nat)
    (r : (decodingGraph S depth).Node) :
    (rootedSets S depth r 1).card ≤ (14*S.ell^2+9)^2 := by
  simpa using rootedSets_card_le S depth r 1

end QEC.Coding.BDL26ConnectedSetCounting
