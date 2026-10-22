import QEC.Coding.QuantumTanner.SquareGraph
import QEC.Coding.QuantumTanner.CayleyLink
import QEC.Coding.QuantumTanner.HeavyEdges
import QEC.Coding.ExpanderCodes.SmallSetExpansionOperators

/-!
# The square graph as actual left-right Cayley steps

The four-corner link identities identify the same-side square multigraph with
one left and one right generator step, preserving label multiplicities.
This is the geometric operator bridge in [LZ22, Lemma lem:lambda].
-/

noncomputable section

namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex

open Classical QEC.Coding.SmallSetExpansion

universe v

variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

/-- Rebase a square at its other vertex on the same side. -/
theorem link_rebase_both
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (g : G) (side : Bool) (a : A) (b : B) :
    X.link (g, side) (a, b) =
      X.link (X.leftGenerator a * g * X.rightGenerator b, side)
        (X.leftInverse a, X.rightInverse b) := by
  exact (hX.1 g side a b).trans (by simpa only [Bool.not_not] using
    (hX.2 (X.leftGenerator a * g) (!side) (X.leftInverse a) b))

/-- TNC excludes a same-side loop for every pair of actual generator labels. -/
theorem left_right_step_ne_base
    (X : LeftRightCayleySquareComplex G A B Square) (g : G) (a : A) (b : B) :
    X.leftGenerator a * g * X.rightGenerator b ≠ g := by
  intro h
  apply X.noConjugacy g a (X.rightInverse b)
  rw [X.rightGenerator_inverse]
  exact (eq_mul_inv_iff_mul_eq).2 h

/-- The two known corners exhaust all same-side incidences, by the actual
two-incidence law and TNC. -/
theorem incident_link_iff_same_side_corners
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (g h : G) (side : Bool) (a : A) (b : B) :
    X.Incident (h, side) (X.link (g, side) (a, b)) ↔
      h = g ∨ h = X.leftGenerator a * g * X.rightGenerator b := by
  let vertices := Finset.univ.filter fun k => X.Incident (k, side) (X.link (g, side) (a, b))
  have hSubset : {g, X.leftGenerator a * g * X.rightGenerator b} ⊆ vertices := by
    intro k hk
    have hk' : k = g ∨ k = X.leftGenerator a * g * X.rightGenerator b := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hk
    rcases hk' with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨(a, b), rfl⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨(X.leftInverse a, X.rightInverse b), (X.link_rebase_both hX g side a b).symm⟩⟩
  have hCard : vertices.card = 2 := X.incidentVerticesOnSide_card _ side
  have hPair : ({g, X.leftGenerator a * g * X.rightGenerator b} : Finset G).card = 2 :=
    Finset.card_pair (X.left_right_step_ne_base g a b).symm
  have hEqual := Finset.eq_of_subset_of_card_le hSubset (by omega)
  have hMem : X.Incident (h, side) (X.link (g, side) (a, b)) ↔ h ∈ vertices := by
    simp only [vertices, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hMem, ← hEqual]
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- The weighted square adjacency counts precisely the pairs of left/right
labels taking the base vertex to the target. -/
theorem squareGraph_eq_left_right_steps
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) (g h : G) :
    X.squareGraph side g h =
      (Finset.univ.filter fun ab : A × B => X.leftGenerator ab.1 * g * X.rightGenerator ab.2 = h).card := by
  have hSet : (Finset.univ.filter fun q =>
      X.Incident (g, side) q ∧ X.Incident (h, side) q ∧ g ≠ h) =
      (Finset.univ.filter fun ab : A × B =>
        X.leftGenerator ab.1 * g * X.rightGenerator ab.2 = h).image (X.link (g, side)) := by
    ext q
    constructor
    · intro hq
      obtain ⟨hg, hh, hne⟩ := (Finset.mem_filter.mp hq).2
      obtain ⟨⟨a, b⟩, rfl⟩ := hg
      have hCorner := (X.incident_link_iff_same_side_corners hX g h side a b).mp hh
      refine Finset.mem_image.mpr ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      exact (hCorner.resolve_left hne.symm).symm
    · intro hq
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hq
      have hStep := (Finset.mem_filter.mp hab).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨(a, b), rfl⟩, ?_, ?_⟩
      · exact (X.incident_link_iff_same_side_corners hX g h side a b).mpr (Or.inr hStep.symm)
      · rw [← hStep]
        exact (X.left_right_step_ne_base g a b).symm
  unfold squareGraph
  rw [hSet, Finset.card_image_of_injective _ (X.link_injective (g, side))]

/-- The actual left-generator adjacency, retaining repeated labels. -/
def leftCayleyGraph (X : LeftRightCayleySquareComplex G A B Square) : WeightedGraph G :=
  fun g h => (Finset.univ.filter fun a => X.leftGenerator a * g = h).card

/-- The actual right-generator adjacency, retaining repeated labels. -/
def rightCayleyGraph (X : LeftRightCayleySquareComplex G A B Square) : WeightedGraph G :=
  fun g h => (Finset.univ.filter fun b => g * X.rightGenerator b = h).card

theorem leftCayleyGraph_regular (X : LeftRightCayleySquareComplex G A B Square) :
    IsRegular X.leftCayleyGraph (Fintype.card A) := by
  intro g
  simpa only [leftCayleyGraph, Finset.mem_univ, Finset.filter_true, Finset.card_univ] using
    Finset.sum_card_fiberwise_eq_card_filter Finset.univ Finset.univ (fun a => X.leftGenerator a * g)

theorem rightCayleyGraph_regular (X : LeftRightCayleySquareComplex G A B Square) :
    IsRegular X.rightCayleyGraph (Fintype.card B) := by
  intro g
  simpa only [rightCayleyGraph, Finset.mem_univ, Finset.filter_true, Finset.card_univ] using
    Finset.sum_card_fiberwise_eq_card_filter Finset.univ Finset.univ (fun b => g * X.rightGenerator b)

theorem leftCayleyGraph_symmetric (X : LeftRightCayleySquareComplex G A B Square) :
    IsSymmetric X.leftCayleyGraph := by
  intro g h
  simp only [leftCayleyGraph, Finset.card_filter]
  apply Fintype.sum_equiv X.leftInverse
  intro a
  have hi : X.leftGenerator (X.leftInverse a) * h = g ↔ X.leftGenerator a * g = h := by
    rw [X.leftGenerator_inverse]
    exact eq_comm.trans eq_inv_mul_iff_mul_eq
  simp only [hi]

theorem rightCayleyGraph_symmetric (X : LeftRightCayleySquareComplex G A B Square) :
    IsSymmetric X.rightCayleyGraph := by
  intro g h
  simp only [rightCayleyGraph, Finset.card_filter]
  apply Fintype.sum_equiv X.rightInverse
  intro b
  have hi : h * X.rightGenerator (X.rightInverse b) = g ↔ g * X.rightGenerator b = h := by
    rw [X.rightGenerator_inverse]
    exact eq_comm.trans eq_mul_inv_iff_mul_eq
  simp only [hi]

theorem weightedNeighborSum_leftCayleyGraph
    (X : LeftRightCayleySquareComplex G A B Square) (f : G → ℝ) (g : G) :
    weightedNeighborSum X.leftCayleyGraph f g = ∑ a, f (X.leftGenerator a * g) := by
  simp only [weightedNeighborSum, leftCayleyGraph, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  simp only [eq_comm, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem weightedNeighborSum_rightCayleyGraph
    (X : LeftRightCayleySquareComplex G A B Square) (f : G → ℝ) (g : G) :
    weightedNeighborSum X.rightCayleyGraph f g = ∑ b, f (g * X.rightGenerator b) := by
  simp only [weightedNeighborSum, rightCayleyGraph, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _hb
  simp only [eq_comm, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem weightedNeighborSum_squareGraph
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) (f : G → ℝ) (g : G) :
    weightedNeighborSum (X.squareGraph side) f g =
      ∑ a, ∑ b, f (X.leftGenerator a * g * X.rightGenerator b) := by
  simp only [weightedNeighborSum, X.squareGraph_eq_left_right_steps hX, Finset.card_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_mul,
    ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [eq_comm, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fintype.sum_prod_type]

/-- The actual square adjacency is the product of the two actual Cayley
adjacencies, so the product spectral theorem applies to this graph. -/
theorem squareGraph_eq_compose
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) : X.squareGraph side = compose X.leftCayleyGraph X.rightCayleyGraph := by
  funext g h
  have hOperators : ∀ f : G → ℝ, weightedNeighborSum (X.squareGraph side) f g =
      weightedNeighborSum (compose X.leftCayleyGraph X.rightCayleyGraph) f g := by
    intro f
    rw [X.weightedNeighborSum_squareGraph hX, weightedNeighborSum_compose,
      X.weightedNeighborSum_leftCayleyGraph]
    simp_rw [X.weightedNeighborSum_rightCayleyGraph]
  have hEntry := hOperators (Pi.single h 1)
  simpa [weightedNeighborSum, Pi.single_apply] using hEntry

/-- Actual Cayley spectral bounds imply mixing for the same-side square
graph and union graph, with exactly the unnormalized product/sum constants. -/
theorem mixing_of_cayley_bilinear_bounds
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (lambda mu : ℝ) (hLambda : 0 ≤ lambda) (hMu : 0 ≤ mu)
    (hLeft : HasMeanZeroBilinearBound X.leftCayleyGraph lambda)
    (hRight : HasMeanZeroBilinearBound X.rightCayleyGraph mu) :
    (∀ side, HasExpanderMixingBound (X.squareGraph side)
      (Fintype.card A * Fintype.card B) (lambda * mu)) ∧
    HasExpanderMixingBound X.unionCayleyGraph
      (Fintype.card A + Fintype.card B) (lambda + mu) := by
  constructor
  · intro side
    apply HasMeanZeroBilinearBound.toExpanderMixingBound
      (X.squareGraph_symmetric side) (X.squareGraph_regular side) (mul_nonneg hLambda hMu)
    rw [X.squareGraph_eq_compose hX]
    exact HasMeanZeroBilinearBound.compose (Fintype.card A) (Fintype.card B)
      X.leftCayleyGraph_symmetric X.leftCayleyGraph_regular
      X.rightCayleyGraph_symmetric X.rightCayleyGraph_regular hLambda hMu hLeft hRight
  · apply HasMeanZeroBilinearBound.toExpanderMixingBound
      X.unionCayleyGraph_symmetric X.unionCayleyGraph_regular (add_nonneg hLambda hMu)
    exact hLeft.add hRight

end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
