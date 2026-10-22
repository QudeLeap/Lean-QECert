import QEC.Coding.QuantumTanner.Distance
import QEC.Coding.ExpanderCodes.SmallSetExpansionSquare

/-!
# The weighted square graph of actual link incidences

Each square joins its two vertices on a fixed side. Multiplicities are kept:
the graph need not be simple. The support subgraph has degree exactly the
local Hamming weight, as used in [LZ22, proof of Claim claim:Se].
-/

noncomputable section

namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex

open Classical
open QEC.Coding.SmallSetExpansion

universe v

variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

/-- The full same-side square multigraph, without loops. -/
def squareGraph (X : LeftRightCayleySquareComplex G A B Square) (side : Bool) :
    WeightedGraph G := fun g h =>
  (Finset.univ.filter fun q => X.Incident (g, side) q ∧ X.Incident (h, side) q ∧ g ≠ h).card

/-- The actual subgraph selected by the nonzero square coordinates of a word. -/
def supportSquareGraph (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) : WeightedGraph G := fun g h =>
  (Finset.univ.filter fun q => x q ≠ 0 ∧ X.Incident (g, side) q ∧
    X.Incident (h, side) q ∧ g ≠ h).card

theorem squareGraph_symmetric (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) : IsSymmetric (X.squareGraph side) := by
  intro g h
  unfold squareGraph
  congr 1
  ext q
  simp [squareGraph, and_comm, and_left_comm, and_assoc, ne_comm]

theorem supportSquareGraph_le_squareGraph
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (g h : G) :
    X.supportSquareGraph side x g h ≤ X.squareGraph side g h := by
  apply Finset.card_le_card
  intro q hq
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2.2⟩

/-- Every incident square has precisely one other endpoint on the same side. -/
theorem otherIncidentVertices_card
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool) (g : G) (q : Square)
    (hg : X.Incident (g, side) q) :
    (Finset.univ.filter fun h => X.Incident (h, side) q ∧ g ≠ h).card = 1 := by
  let vertices := Finset.univ.filter fun h => X.Incident (h, side) q
  have hmem : g ∈ vertices := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩
  have hset : (Finset.univ.filter fun h => X.Incident (h, side) q ∧ g ≠ h) =
      vertices.erase g := by
    ext h
    simp [vertices, ne_comm, and_comm]
  rw [hset, Finset.card_erase_of_mem hmem]
  have hcard : vertices.card = 2 := X.incidentVerticesOnSide_card q side
  omega

/-- Degree in the selected square graph is exactly the actual local weight. -/
theorem sum_supportSquareGraph_eq_localWeight
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (g : G) :
    (∑ h : G, X.supportSquareGraph side x g h) =
      HammingWeight (X.localRestriction (g, side) x) := by
  simp only [supportSquareGraph, Finset.card_filter]
  rw [Finset.sum_comm, X.hammingWeight_localRestriction_eq_sum]
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hq : x q ≠ 0 ∧ X.Incident (g, side) q
  · rw [if_pos hq]
    calc
      (∑ h : G, if x q ≠ 0 ∧ X.Incident (g, side) q ∧
          X.Incident (h, side) q ∧ g ≠ h then 1 else 0) =
          ∑ h : G, if X.Incident (h, side) q ∧ g ≠ h then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro h _hh
        simp only [hq.1, hq.2, ne_eq, not_false_eq_true, true_and]
      _ = (Finset.univ.filter fun h => X.Incident (h, side) q ∧ g ≠ h).card :=
        (Finset.card_filter _ _).symm
      _ = 1 := X.otherIncidentVertices_card side g q hq.2
  · rw [if_neg hq]
    apply Finset.sum_eq_zero
    intro h _hh
    exact if_neg (fun hfull => hq ⟨hfull.1, hfull.2.1⟩)

/-- A selected edge ends only at an actually active vertex. -/
theorem supportSquareGraph_eq_zero_of_not_active
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (g h : G)
    (hh : h ∉ X.activeVerticesOnSide side x) : X.supportSquareGraph side x g h = 0 := by
  have hlocal : X.localRestriction (h, side) x = 0 := by
    simpa [activeVerticesOnSide] using hh
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hdata := (Finset.mem_filter.mp hq).2
  obtain ⟨ab, hab⟩ := hdata.2.2.1
  have hz : x (X.link (h, side) ab) = 0 := congrFun hlocal ab
  rw [hab] at hz
  exact hdata.1 hz

/-- All the selected degree is already inside the active set. -/
theorem sum_supportSquareGraph_active_eq_localWeight
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (g : G) :
    (∑ h ∈ X.activeVerticesOnSide side x, X.supportSquareGraph side x g h) =
      HammingWeight (X.localRestriction (g, side) x) := by
  rw [← X.sum_supportSquareGraph_eq_localWeight side x g]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro h _hh hnot
  exact X.supportSquareGraph_eq_zero_of_not_active side x g h hnot

/-- The full square graph has the product of the two local degrees. -/
theorem squareGraph_regular (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) : IsRegular (X.squareGraph side) (Fintype.card A * Fintype.card B) := by
  intro g
  have hgraph : X.supportSquareGraph side (fun _ => 1) = X.squareGraph side := by
    funext g h
    simp [supportSquareGraph, squareGraph]
  rw [← hgraph, X.sum_supportSquareGraph_eq_localWeight]
  simp [HammingWeight, hammingSupport, localRestriction]

/-- Vertices whose actual local degree reaches a given exceptional threshold. -/
def exceptionalVerticesOnSide (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) : Finset G :=
  (X.activeVerticesOnSide side x).filter fun g => cutoff ≤
    HammingWeight (X.localRestriction (g, side) x)

/-- Exceptional local weights give a genuine full-graph cross-edge lower bound. -/
theorem exceptional_card_mul_cutoff_le_crossCount
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (cutoff : Nat) :
    cutoff * (X.exceptionalVerticesOnSide side x cutoff).card ≤
      crossCount (X.squareGraph side) (X.exceptionalVerticesOnSide side x cutoff)
        (X.activeVerticesOnSide side x) := by
  apply degree_mul_card_le_crossCount
  intro g hg
  have hcutoff := (Finset.mem_filter.mp hg).2
  calc
    cutoff ≤ HammingWeight (X.localRestriction (g, side) x) := hcutoff
    _ = ∑ h ∈ X.activeVerticesOnSide side x, X.supportSquareGraph side x g h :=
      (X.sum_supportSquareGraph_active_eq_localWeight side x g).symm
    _ ≤ ∑ h ∈ X.activeVerticesOnSide side x, X.squareGraph side g h :=
      Finset.sum_le_sum fun h _hh => X.supportSquareGraph_le_squareGraph side x g h

end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
