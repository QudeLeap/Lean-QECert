import QEC.Coding.FiberBundle.TwistGraphSpectral

/-!
# Operator form of HHO20 twist-graph mixing

The Alon--Roichman argument naturally bounds the nonconstant spectrum of the
normalized adjacency operator.  This file connects that analytic statement
to the integer-cleared squared Expander Mixing event used by the deterministic
HHO20 proof.

The bridge is proved from the concrete sampled translations.  In particular,
regularity, the centered-indicator norm formula, and the edge-count identity
are theorems rather than assumptions.
-/

namespace QEC.Coding.FiberBundle.TwistGraph

open scoped BigOperators

/-- Sum of a real function over all `2 * typeCount` directed incidences. -/
noncomputable def undirectedNeighborSum
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (g : ZMod ell → Real)
    (u : ZMod ell) : Real :=
  ∑ τ : Fin typeCount,
    (g (outNeighbor twistSample τ u) +
      g (inNeighbor twistSample τ u))

/-- The bilinear form of the unnormalized undirected adjacency operator. -/
noncomputable def adjacencyPairing
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (f g : ZMod ell → Real) : Real :=
  ∑ u : ZMod ell, f u * undirectedNeighborSum twistSample g u

/--
The operator-norm event corresponding to normalized nonconstant spectrum at
most `1 / 50000`.
-/
def HasHHO20OperatorMixing
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell) : Prop :=
  ∀ f g : ZMod ell → Real,
    (∑ u, f u) = 0 →
    (∑ u, g u) = 0 →
    (50000 * |adjacencyPairing twistSample f g|) ^ 2 ≤
      (2 * typeCount : Real) ^ 2 *
        (∑ u, (f u) ^ 2) *
        ∑ u, (g u) ^ 2

/-- Integer-scaled indicator whose coordinate sum is zero. -/
noncomputable def centeredIndicator
    {ell : Nat}
    (vertices : Finset (ZMod ell))
    (u : ZMod ell) : Real :=
  if u ∈ vertices then ell - vertices.card else -vertices.card

theorem sum_centeredIndicator
    {ell : Nat}
    [NeZero ell]
    (vertices : Finset (ZMod ell)) :
    (∑ u : ZMod ell, centeredIndicator vertices u) = 0 := by
  classical
  simp_rw [centeredIndicator]
  rw [Finset.sum_ite]
  rw [Finset.filter_mem_eq_inter, Finset.filter_notMem_eq_sdiff]
  simp only [Finset.univ_inter]
  have hCard : (Finset.univ \ vertices).card = ell - vertices.card := by
    rw [Finset.card_sdiff]
    simp [ZMod.card]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hCard]
  have hVertices : vertices.card ≤ ell := by
    simpa [ZMod.card] using Finset.card_le_univ vertices
  push_cast [Nat.cast_sub hVertices]
  ring

theorem sum_sq_centeredIndicator
    {ell : Nat}
    [NeZero ell]
    (vertices : Finset (ZMod ell)) :
    (∑ u : ZMod ell, (centeredIndicator vertices u) ^ 2) =
      ell * vertices.card * (ell - vertices.card) := by
  classical
  simp_rw [centeredIndicator, apply_ite (fun x : Real => x ^ 2)]
  rw [Finset.sum_ite]
  rw [Finset.filter_mem_eq_inter, Finset.filter_notMem_eq_sdiff]
  simp only [Finset.univ_inter]
  have hCard : (Finset.univ \ vertices).card = ell - vertices.card := by
    rw [Finset.card_sdiff]
    simp [ZMod.card]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hCard]
  have hVertices : vertices.card ≤ ell := by
    simpa [ZMod.card] using Finset.card_le_univ vertices
  push_cast [Nat.cast_sub hVertices]
  ring

/-- A translated membership indicator has the same total as the set. -/
theorem sum_outNeighbor_indicator
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount)
    (vertices : Finset (ZMod ell)) :
    (∑ u : ZMod ell,
        if outNeighbor twistSample τ u ∈ vertices then 1 else 0) =
      vertices.card := by
  classical
  calc
    _ = ∑ u : ZMod ell, if u ∈ vertices then 1 else 0 := by
      exact
        (Equiv.sum_comp
          (typeTranslation twistSample τ)
          (fun u : ZMod ell => if u ∈ vertices then (1 : Nat) else 0))
    _ = vertices.card := by simp

/-- The inverse translated membership indicator has the same total. -/
theorem sum_inNeighbor_indicator
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount)
    (vertices : Finset (ZMod ell)) :
    (∑ u : ZMod ell,
        if inNeighbor twistSample τ u ∈ vertices then 1 else 0) =
      vertices.card := by
  classical
  calc
    _ = ∑ u : ZMod ell, if u ∈ vertices then 1 else 0 := by
      exact
        (Equiv.sum_comp
          (typeTranslation twistSample τ).symm
          (fun u : ZMod ell => if u ∈ vertices then (1 : Nat) else 0))
    _ = vertices.card := by simp

/-- Every target vertex receives exactly `2 * typeCount` incidences in total. -/
theorem sum_neighborIncidenceCount
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (vertices : Finset (ZMod ell)) :
    (∑ u : ZMod ell,
        neighborIncidenceCount twistSample vertices u) =
      2 * typeCount * vertices.card := by
  classical
  calc
    _ =
        (∑ τ : Fin typeCount, ∑ u : ZMod ell,
          if outNeighbor twistSample τ u ∈ vertices then 1 else 0) +
        (∑ τ : Fin typeCount, ∑ u : ZMod ell,
          if inNeighbor twistSample τ u ∈ vertices then 1 else 0) := by
      simp only [neighborIncidenceCount, Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      congr 1
      rw [Finset.sum_comm]
    _ =
        (∑ _τ : Fin typeCount, vertices.card) +
          ∑ _τ : Fin typeCount, vertices.card := by
      congr 1
      · apply Finset.sum_congr rfl
        intro τ _hτ
        exact sum_outNeighbor_indicator twistSample τ vertices
      · apply Finset.sum_congr rfl
        intro τ _hτ
        exact sum_inNeighbor_indicator twistSample τ vertices
    _ = 2 * typeCount * vertices.card := by simp; ring

/-- Pointwise algebraic form of the centered indicator. -/
theorem centeredIndicator_eq_mul_indicator_sub_card
    {ell : Nat}
    (vertices : Finset (ZMod ell))
    (u : ZMod ell) :
    centeredIndicator vertices u =
      ell * (if u ∈ vertices then (1 : Real) else 0) -
        vertices.card := by
  classical
  by_cases hu : u ∈ vertices <;>
    simp [centeredIndicator, hu]

/-- Centering a target indicator turns its neighbor sum into discrepancy. -/
theorem undirectedNeighborSum_centeredIndicator
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (vertices : Finset (ZMod ell))
    (u : ZMod ell) :
    undirectedNeighborSum twistSample (centeredIndicator vertices) u =
      ell * neighborIncidenceCount twistSample vertices u -
        2 * typeCount * vertices.card := by
  classical
  simp only [undirectedNeighborSum, neighborIncidenceCount]
  simp_rw [centeredIndicator_eq_mul_indicator_sub_card]
  push_cast
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ, Fintype.card_fin]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  ring

/-- Pairing a centered indicator with an arbitrary real function. -/
theorem sum_centeredIndicator_mul
    {ell : Nat}
    [NeZero ell]
    (vertices : Finset (ZMod ell))
    (h : ZMod ell → Real) :
    (∑ u : ZMod ell, centeredIndicator vertices u * h u) =
      ell * (∑ u ∈ vertices, h u) -
        vertices.card * ∑ u : ZMod ell, h u := by
  classical
  simp_rw [centeredIndicator_eq_mul_indicator_sub_card, sub_mul]
  rw [Finset.sum_sub_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite, Finset.filter_mem_eq_inter,
    Finset.filter_notMem_eq_sdiff]
  simp

/-- Exact centered-indicator form of the graph edge discrepancy. -/
theorem adjacencyPairing_centeredIndicator
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (left right : Finset (ZMod ell)) :
    adjacencyPairing twistSample
        (centeredIndicator left) (centeredIndicator right) =
      ell *
        (ell * neighborEdgeCount twistSample left right -
          2 * typeCount * left.card * right.card) := by
  rw [adjacencyPairing]
  simp_rw [undirectedNeighborSum_centeredIndicator]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hFirst :
      (∑ u : ZMod ell,
          centeredIndicator left u *
            (ell * neighborIncidenceCount twistSample right u)) =
        ell * ∑ u : ZMod ell,
          centeredIndicator left u *
            neighborIncidenceCount twistSample right u := by
    calc
      _ = ∑ u : ZMod ell,
          (ell : Real) *
            (centeredIndicator left u *
              neighborIncidenceCount twistSample right u) := by
        apply Finset.sum_congr rfl
        intro u _hu
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hSecond :
      (∑ u : ZMod ell,
          centeredIndicator left u *
            (2 * typeCount * right.card)) =
        (∑ u : ZMod ell, centeredIndicator left u) *
          (2 * typeCount * right.card) := by
    rw [Finset.sum_mul]
  rw [hFirst, hSecond, sum_centeredIndicator]
  simp only [zero_mul, sub_zero]
  rw [sum_centeredIndicator_mul]
  rw [show
      (∑ u ∈ left,
          (neighborIncidenceCount twistSample right u : Real)) =
        neighborEdgeCount twistSample left right by
    simp only [neighborEdgeCount]
    norm_cast]
  rw [show
      (∑ u : ZMod ell,
          (neighborIncidenceCount twistSample right u : Real)) =
        2 * typeCount * right.card by
    norm_cast
    exact sum_neighborIncidenceCount twistSample right]
  ring

/-- Real absolute difference of natural casts is the cast of `Nat.dist`. -/
theorem abs_natCast_sub_natCast (a b : Nat) :
    |(a : Real) - b| = Nat.dist a b := by
  by_cases hab : a ≤ b
  · have habR : (a : Real) ≤ b := by exact_mod_cast hab
    rw [abs_of_nonpos (sub_nonpos.mpr habR)]
    rw [Nat.dist_eq_sub_of_le hab, Nat.cast_sub hab]
    ring
  · have hba : b ≤ a := by omega
    have hbaR : (b : Real) ≤ a := by exact_mod_cast hba
    rw [abs_of_nonneg (sub_nonneg.mpr hbaR)]
    rw [Nat.dist_eq_sub_of_le_right hba, Nat.cast_sub hba]

/--
The concrete nonconstant operator bound implies the integer-cleared squared
Expander Mixing event consumed by `TwistGraphSpectral`.
-/
theorem hasHHO20SquaredExpanderMixing_of_operatorMixing
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hOperator : HasHHO20OperatorMixing twistSample) :
    HasHHO20SquaredExpanderMixing twistSample := by
  intro left right
  have h := hOperator
    (centeredIndicator left) (centeredIndicator right)
    (sum_centeredIndicator left) (sum_centeredIndicator right)
  rw [adjacencyPairing_centeredIndicator,
    abs_mul, abs_of_nonneg (show (0 : Real) ≤ ell by positivity),
    sum_sq_centeredIndicator, sum_sq_centeredIndicator] at h
  have hDist :
      |(ell : Real) * neighborEdgeCount twistSample left right -
          2 * typeCount * left.card * right.card| =
        Nat.dist
          (ell * neighborEdgeCount twistSample left right)
          (2 * typeCount * left.card * right.card) := by
    calc
      _ =
          |((ell * neighborEdgeCount twistSample left right : Nat) : Real) -
            ((2 * typeCount * left.card * right.card : Nat) : Real)| := by
        push_cast
        ring
      _ = _ := abs_natCast_sub_natCast
        (ell * neighborEdgeCount twistSample left right)
        (2 * typeCount * left.card * right.card)
  rw [hDist] at h
  have hEll : (0 : Real) < ell := by
    exact_mod_cast NeZero.pos ell
  have hReal :
      ((50000 *
          Nat.dist
            (ell * neighborEdgeCount twistSample left right)
            (2 * typeCount * left.card * right.card)) ^ 2 : Real) ≤
        (2 * typeCount) ^ 2 *
          left.card * (ell - left.card) *
          right.card * (ell - right.card) := by
    have hScaled :
        (ell : Real) ^ 2 *
            (50000 *
              Nat.dist
                (ell * neighborEdgeCount twistSample left right)
                (2 * typeCount * left.card * right.card)) ^ 2 ≤
          (ell : Real) ^ 2 *
            ((2 * typeCount) ^ 2 *
              left.card * (ell - left.card) *
              right.card * (ell - right.card)) := by
      calc
        _ =
            (50000 *
              ((ell : Real) *
                Nat.dist
                  (ell * neighborEdgeCount twistSample left right)
                  (2 * typeCount * left.card * right.card))) ^ 2 := by ring
        _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_left hScaled (sq_pos_of_pos hEll)
  have hLeftCard : left.card ≤ ell := by
    simpa [ZMod.card] using Finset.card_le_univ left
  have hRightCard : right.card ≤ ell := by
    simpa [ZMod.card] using Finset.card_le_univ right
  rw [← Nat.cast_sub hLeftCard, ← Nat.cast_sub hRightCard] at hReal
  exact_mod_cast hReal

end QEC.Coding.FiberBundle.TwistGraph
