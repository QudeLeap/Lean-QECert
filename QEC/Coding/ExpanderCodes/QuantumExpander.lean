import QEC.Coding.HypergraphProduct.ParametersTheorem

/-!
# Leverrier--Tillich--Zemor quantum expander codes

This module formalizes the finite construction and distance statement of
LTZ15.  The bipartite incidence matrix is constructed from the graph; it is
not supplied as an independent input.  Both vertex parts and both regular
degrees are explicitly nonempty/positive, excluding the zero-degree
degeneracy in which the paper's expansion inequality does not imply its
classical-distance proposition.

Source: `leverrier-tillich-zemor-2015-expander/QEC-arxiv.tex`, especially
lines 169--251 and 406--419.
-/

noncomputable section

namespace QEC.Coding.QuantumExpander

open QEC.Coding.HypergraphProduct
open scoped ENNReal

universe u

/-- A finite biregular bipartite graph with the nondegeneracy conditions used
by the LTZ15 distance argument made explicit. -/
structure BiregularBipartiteGraph (A B : Type u)
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] where
  adjacent : A → B → Bool
  leftDegree : Nat
  rightDegree : Nat
  leftNonempty : Nonempty A
  rightNonempty : Nonempty B
  leftDegree_pos : 0 < leftDegree
  rightDegree_pos : 0 < rightDegree
  left_regular : ∀ a,
    (Finset.univ.filter fun b => adjacent a b = true).card = leftDegree
  right_regular : ∀ b,
    (Finset.univ.filter fun a => adjacent a b = true).card = rightDegree

namespace BiregularBipartiteGraph

variable {A B : Type u}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The binary incidence matrix, constructed internally from the graph. -/
def incidenceMatrix (G : BiregularBipartiteGraph A B) :
    Matrix B A (ZMod 2) :=
  fun b a => if G.adjacent a b = true then 1 else 0

/-- Neighbors on the right of a finite set of left vertices. -/
def leftNeighborhood (G : BiregularBipartiteGraph A B)
    (S : Finset A) : Finset B :=
  Finset.univ.filter fun b => ∃ a ∈ S, G.adjacent a b = true

/-- Exchange the two vertex parts of a bipartite graph. -/
def swap (G : BiregularBipartiteGraph A B) :
    BiregularBipartiteGraph B A where
  adjacent b a := G.adjacent a b
  leftDegree := G.rightDegree
  rightDegree := G.leftDegree
  leftNonempty := G.rightNonempty
  rightNonempty := G.leftNonempty
  leftDegree_pos := G.rightDegree_pos
  rightDegree_pos := G.leftDegree_pos
  left_regular := G.right_regular
  right_regular := G.left_regular

/-- LTZ15 left expansion, with all cardinalities compared in `Real`. -/
def LeftExpanding (G : BiregularBipartiteGraph A B)
    (γ δ : Real) : Prop :=
  ∀ S : Finset A,
    (S.card : Real) ≤ γ * Fintype.card A →
      (1 - δ) * G.leftDegree * S.card ≤
        (G.leftNeighborhood S).card

/-- LTZ15 right expansion, with all cardinalities compared in `Real`. -/
def RightExpanding (G : BiregularBipartiteGraph A B)
    (γ δ : Real) : Prop :=
  G.swap.LeftExpanding γ δ

/-- The conjunction of the left and right LTZ15 expansion conditions. -/
def LeftRightExpanding (G : BiregularBipartiteGraph A B)
    (γA δA γB δB : Real) : Prop :=
  G.LeftExpanding γA δA ∧ G.RightExpanding γB δB

/-- Number of vertices of `S` adjacent to a fixed right vertex. -/
def leftInducedDegree (G : BiregularBipartiteGraph A B)
    (S : Finset A) (b : B) : Nat :=
  (S.filter fun a => G.adjacent a b = true).card

@[simp]
theorem mem_leftNeighborhood_iff_inducedDegree_pos
    (G : BiregularBipartiteGraph A B) (S : Finset A) (b : B) :
    b ∈ G.leftNeighborhood S ↔ 0 < G.leftInducedDegree S b := by
  simp only [leftNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and,
    leftInducedDegree, Finset.card_pos]
  constructor
  · rintro ⟨a, haS, hab⟩
    exact ⟨a, Finset.mem_filter.mpr ⟨haS, hab⟩⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩

/-- Double-count the edges from `S` to its right neighbors. -/
theorem sum_leftInducedDegree
    (G : BiregularBipartiteGraph A B) (S : Finset A) :
    ∑ b, G.leftInducedDegree S b = S.card * G.leftDegree := by
  classical
  rw [show (∑ b, G.leftInducedDegree S b) =
      ∑ b ∈ (Finset.univ : Finset B),
        (S.bipartiteBelow (fun a b => G.adjacent a b = true) b).card by
    simp [leftInducedDegree, Finset.bipartiteBelow]]
  rw [← Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
  simp [Finset.bipartiteAbove, G.left_regular]

/-- If every nonempty induced right degree is at least two, double counting
bounds twice the neighborhood size by the number of incident edges. -/
theorem two_mul_leftNeighborhood_card_le_sum_of_no_unique
    (G : BiregularBipartiteGraph A B) (S : Finset A)
    (hNoUnique : ∀ b, G.leftInducedDegree S b ≠ 1) :
    2 * (G.leftNeighborhood S).card ≤
      ∑ b, G.leftInducedDegree S b := by
  classical
  calc
    2 * (G.leftNeighborhood S).card =
        ∑ b, if b ∈ G.leftNeighborhood S then 2 else 0 := by
      rw [show (G.leftNeighborhood S).card =
          ∑ b, if b ∈ G.leftNeighborhood S then 1 else 0 by
        rw [Finset.sum_boole]
        congr 1
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _hb
      by_cases hb : b ∈ G.leftNeighborhood S <;> simp [hb]
    _ ≤ ∑ b, G.leftInducedDegree S b := by
      apply Finset.sum_le_sum
      intro b _hb
      by_cases hb : b ∈ G.leftNeighborhood S
      · simp only [if_pos hb]
        have hpos : 0 < G.leftInducedDegree S b :=
          (mem_leftNeighborhood_iff_inducedDegree_pos G S b).1 hb
        have hne := hNoUnique b
        omega
      · simp [hb]

/-- A nonempty set below the LTZ15 expansion threshold has a unique right
neighbor when the expansion defect is strictly below one half. -/
theorem exists_left_unique_neighbor
    (G : BiregularBipartiteGraph A B) {γ δ : Real}
    (hExpand : G.LeftExpanding γ δ) (hδ : δ < 1 / 2)
    (S : Finset A) (hS : S.Nonempty)
    (hSmall : (S.card : Real) ≤ γ * Fintype.card A) :
    ∃ b, G.leftInducedDegree S b = 1 := by
  by_contra hUnique
  have hNoUnique : ∀ b, G.leftInducedDegree S b ≠ 1 := by
    intro b hb
    exact hUnique ⟨b, hb⟩
  have hCountNat :
      2 * (G.leftNeighborhood S).card ≤ S.card * G.leftDegree := by
    rw [← sum_leftInducedDegree G S]
    exact two_mul_leftNeighborhood_card_le_sum_of_no_unique G S hNoUnique
  have hCountReal :
      (2 : Real) * (G.leftNeighborhood S).card ≤
        S.card * G.leftDegree := by
    exact_mod_cast hCountNat
  have hExpansion := hExpand S hSmall
  have hPositive : (0 : Real) < G.leftDegree * S.card := by
    exact mul_pos (by exact_mod_cast G.leftDegree_pos)
      (by exact_mod_cast Finset.card_pos.mpr hS)
  have hStrict :
      (1 / 2 : Real) * (G.leftDegree * S.card) <
        (1 - δ) * (G.leftDegree * S.card) := by
    apply mul_lt_mul_of_pos_right _ hPositive
    linarith
  norm_num at hStrict
  nlinarith

/-- A binary kernel word cannot have a unique neighbor in its support. -/
theorem kernel_word_has_no_left_unique_neighbor
    (G : BiregularBipartiteGraph A B) (x : Word (ZMod 2) A)
    (hxKernel : Matrix.toLin' G.incidenceMatrix x = 0) (b : B) :
    G.leftInducedDegree (hammingSupport x) b ≠ 1 := by
  intro hUnique
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hUnique
  have haFiltered : a ∈
      (hammingSupport x).filter (fun a => G.adjacent a b = true) := by
    rw [ha]
    simp
  have haSupport : a ∈ hammingSupport x := (Finset.mem_filter.mp haFiltered).1
  have haAdjacent : G.adjacent a b = true := (Finset.mem_filter.mp haFiltered).2
  have hxa : x a ≠ 0 := (Finset.mem_filter.mp haSupport).2
  have hsum :
      ∑ a', G.incidenceMatrix b a' * x a' = x a := by
    rw [Finset.sum_eq_single a]
    · simp [incidenceMatrix, haAdjacent]
    · intro a' _ha' hne
      by_cases hadj : G.adjacent a' b = true
      · have hxa' : x a' = 0 := by
          by_contra hxa'0
          have ha'Mem : a' ∈
              (hammingSupport x).filter (fun c => G.adjacent c b = true) := by
            simp [hammingSupport, hxa'0, hadj]
          rw [ha] at ha'Mem
          exact hne (Finset.mem_singleton.mp ha'Mem)
        simp [incidenceMatrix, hadj, hxa']
      · simp [incidenceMatrix, hadj]
    · simp
  have hb := congrFun hxKernel b
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct] at hb
  rw [hsum] at hb
  exact hxa hb

/-- The diagonal Tillich--Zemor hypergraph-product data constructed from `G`.
-/
def hypergraphProductData (G : BiregularBipartiteGraph A B) :
    Data (ZMod 2) B A B A :=
  diagonalData G.incidenceMatrix

/-- Embed an extended natural-number distance into `ENNReal`, preserving
infinity. -/
def extendedNatToENNReal : WithTop Nat → ENNReal :=
  WithTop.map fun n : Nat => (n : NNReal)

/-- The embedding of extended natural distances into `ENNReal` is monotone.
-/
theorem extendedNatToENNReal_mono : Monotone extendedNatToENNReal := by
  intro m n hmn
  induction m using WithTop.recTopCoe with
  | top =>
      have hn : n = ⊤ := top_unique hmn
      subst n
      exact le_rfl
  | coe m =>
      induction n using WithTop.recTopCoe with
      | top => exact le_top
      | coe n =>
          change (m : ENNReal) ≤ (n : ENNReal)
          exact_mod_cast (WithTop.coe_le_coe.mp hmn)

omit [DecidableEq A] in
/-- A nonzero finite word has nonempty Hamming support. -/
theorem hammingSupport_nonempty_of_ne_zero
    (x : Word (ZMod 2) A) (hx : x ≠ 0) :
    (hammingSupport x).Nonempty := by
  by_contra hEmpty
  rw [Finset.not_nonempty_iff_eq_empty] at hEmpty
  apply hx
  funext a
  change x a = (0 : ZMod 2)
  by_contra hxa
  have ha : a ∈ hammingSupport x := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxa⟩
  rw [hEmpty] at ha
  simp at ha

/-- LTZ15's classical-distance proposition, first at the level of every
nonzero codeword. -/
theorem left_classical_codeword_weight_ge
    (G : BiregularBipartiteGraph A B) {γ δ : Real}
    (hExpand : G.LeftExpanding γ δ) (hδ : δ < 1 / 2)
    (x : Word (ZMod 2) A)
    (hxCode : x ∈ (firstCode G.hypergraphProductData).carrier)
    (hx0 : x ≠ 0) :
    γ * Fintype.card A ≤ HammingWeight x := by
  have hxKernel : Matrix.toLin' G.incidenceMatrix x = 0 := by
    simpa [hypergraphProductData, diagonalData] using
      (mem_firstCode_iff G.hypergraphProductData x).1 hxCode
  by_contra hBound
  have hSmall :
      ((hammingSupport x).card : Real) ≤ γ * Fintype.card A := by
    exact le_of_lt (lt_of_not_ge (by simpa [HammingWeight] using hBound))
  obtain ⟨b, hb⟩ := exists_left_unique_neighbor G hExpand hδ
    (hammingSupport x) (hammingSupport_nonempty_of_ne_zero x hx0) hSmall
  exact kernel_word_has_no_left_unique_neighbor G x hxKernel b hb

/-- The left expansion bound lifted to the source-convention classical
distance in `WithTop Nat`. -/
theorem ceil_left_expansion_le_extendedMinimumDistance
    (G : BiregularBipartiteGraph A B) {γ δ : Real}
    (hExpand : G.LeftExpanding γ δ) (hδ : δ < 1 / 2) :
    (Nat.ceil (γ * Fintype.card A) : WithTop Nat) ≤
      extendedMinimumDistance (firstCode G.hypergraphProductData) := by
  classical
  rw [extendedMinimumDistance]
  apply le_finitePredicateMinimum
  intro x hx
  have hReal := left_classical_codeword_weight_ge G hExpand hδ x hx.1 hx.2
  have hNat : Nat.ceil (γ * Fintype.card A) ≤ HammingWeight x :=
    Nat.ceil_le.mpr hReal
  exact_mod_cast hNat

/-- The left classical-distance bound in the same `ENNReal` domain used by
the final real-valued LTZ15 conclusion. -/
theorem ofReal_left_expansion_le_extendedMinimumDistance
    (G : BiregularBipartiteGraph A B) {γ δ : Real}
    (hExpand : G.LeftExpanding γ δ) (hδ : δ < 1 / 2) :
    ENNReal.ofReal (γ * Fintype.card A) ≤
      extendedNatToENNReal
        (extendedMinimumDistance (firstCode G.hypergraphProductData)) := by
  calc
    ENNReal.ofReal (γ * Fintype.card A) ≤
        (Nat.ceil (γ * Fintype.card A) : ENNReal) := by
      rw [ENNReal.ofReal_le_natCast]
      exact Nat.le_ceil _
    _ = extendedNatToENNReal
        (Nat.ceil (γ * Fintype.card A) : WithTop Nat) := by rfl
    _ ≤ extendedNatToENNReal
        (extendedMinimumDistance (firstCode G.hypergraphProductData)) :=
      extendedNatToENNReal_mono
        (ceil_left_expansion_le_extendedMinimumDistance G hExpand hδ)

/-- The right expansion bound is the left bound for the transposed incidence
matrix, hence controls LTZ15's transpose distance. -/
theorem ofReal_right_expansion_le_extendedMinimumDistance
    (G : BiregularBipartiteGraph A B) {γ δ : Real}
    (hExpand : G.RightExpanding γ δ) (hδ : δ < 1 / 2) :
    ENNReal.ofReal (γ * Fintype.card B) ≤
      extendedNatToENNReal
        (extendedMinimumDistance (firstTransposeCode G.hypergraphProductData)) := by
  exact ofReal_left_expansion_le_extendedMinimumDistance G.swap hExpand hδ

/-- For diagonal HGP data, the four-input distance minimum reduces exactly
to the minimum of the incidence code and its transpose code. -/
theorem inputDistanceMinimum_hypergraphProductData
    (G : BiregularBipartiteGraph A B) :
    inputDistanceMinimum G.hypergraphProductData =
      min
        (extendedMinimumDistance (firstCode G.hypergraphProductData))
        (extendedMinimumDistance (firstTransposeCode G.hypergraphProductData)) := by
  simp [inputDistanceMinimum, hypergraphProductData, diagonalData,
    firstCode, secondCode, firstTransposeCode, secondTransposeCode,
    min_comm]

/-- The exact LTZ15 diagonal quantum distance, without a full-rank
assumption on the incidence matrix. -/
theorem quantumDistance_eq_min_classicalDistances
    (G : BiregularBipartiteGraph A B) :
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode G.hypergraphProductData).xCode
        (binaryCSSCode G.hypergraphProductData).zCode =
      min
        (extendedMinimumDistance (firstCode G.hypergraphProductData))
        (extendedMinimumDistance (firstTransposeCode G.hypergraphProductData)) := by
  let d := extendedMinimumDistance (firstCode G.hypergraphProductData)
  let dT := extendedMinimumDistance (firstTransposeCode G.hypergraphProductData)
  by_cases hTop : min d dT = ⊤
  · have hLower :=
      inputDistanceMinimum_le_extendedAlgebraicCSSMinimumDistance
        G.hypergraphProductData
    rw [inputDistanceMinimum_hypergraphProductData, hTop] at hLower
    rw [show min
        (extendedMinimumDistance (firstCode G.hypergraphProductData))
        (extendedMinimumDistance (firstTransposeCode G.hypergraphProductData)) = ⊤
      from hTop]
    exact top_unique hLower
  · rw [← inputDistanceMinimum_hypergraphProductData G]
    apply extendedAlgebraicCSSMinimumDistance_eq_inputDistanceMinimum
    change DistanceEqualityCondition G.hypergraphProductData
    by_cases hle : d ≤ dT
    · have hd : d ≠ ⊤ := by
        intro hdTop
        apply hTop
        rw [min_eq_left hle, hdTop]
      left
      constructor
      · simp [d, dT, inputDistanceMinimum_hypergraphProductData,
          min_eq_left hle]
      · simpa [d, hypergraphProductData, diagonalData, firstCode,
          secondCode] using hd
    · have hTle : dT ≤ d := le_of_not_ge hle
      have hdT : dT ≠ ⊤ := by
        intro hdTTop
        apply hTop
        rw [min_eq_right hTle, hdTTop]
      right
      right
      left
      constructor
      · simp [d, dT, inputDistanceMinimum_hypergraphProductData,
          min_eq_right hTle]
      · simpa [dT, hypergraphProductData, diagonalData,
          firstTransposeCode, secondTransposeCode] using hdT

/-- The real-valued embedding preserves binary minima. -/
theorem extendedNatToENNReal_min (m n : WithTop Nat) :
    extendedNatToENNReal (min m n) =
      min (extendedNatToENNReal m) (extendedNatToENNReal n) := by
  by_cases hmn : m ≤ n
  · rw [min_eq_left hmn, min_eq_left (extendedNatToENNReal_mono hmn)]
  · have hnm : n ≤ m := le_of_not_ge hmn
    rw [min_eq_right hnm, min_eq_right (extendedNatToENNReal_mono hnm)]

/-- Double-counting all edges gives the biregular degree-balance identity. -/
theorem card_mul_leftDegree_eq_card_mul_rightDegree
    (G : BiregularBipartiteGraph A B) :
    Fintype.card A * G.leftDegree = Fintype.card B * G.rightDegree := by
  classical
  simpa [Finset.bipartiteAbove, Finset.bipartiteBelow,
    G.left_regular, G.right_regular] using
    (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (Finset.univ : Finset A)) (t := (Finset.univ : Finset B))
      (r := fun a b => G.adjacent a b = true))

/-- With nonempty parts and positive degrees, `n_B ≤ n_A` implies the
degree order `Δ_A ≤ Δ_B` stated by LTZ15. -/
theorem leftDegree_le_rightDegree
    (G : BiregularBipartiteGraph A B)
    (hSize : Fintype.card B ≤ Fintype.card A) :
    G.leftDegree ≤ G.rightDegree := by
  by_contra hDegree
  have hRightCard : 0 < Fintype.card B :=
    Fintype.card_pos_iff.mpr G.rightNonempty
  have hStrict :
      Fintype.card B * G.rightDegree <
        Fintype.card B * G.leftDegree :=
    Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge hDegree) hRightCard
  have hWeak :
      Fintype.card B * G.leftDegree ≤
        Fintype.card A * G.leftDegree :=
    Nat.mul_le_mul_right G.leftDegree hSize
  have hBalance := card_mul_leftDegree_eq_card_mul_rightDegree G
  omega

/-- Every row of the graph incidence matrix has the right degree. -/
theorem rowWeight_incidenceMatrix
    (G : BiregularBipartiteGraph A B) (b : B) :
    rowWeight G.incidenceMatrix b = G.rightDegree := by
  simpa [rowWeight, HammingWeight, hammingSupport, incidenceMatrix] using
    G.right_regular b

/-- Every column of the graph incidence matrix has the left degree. -/
theorem columnWeight_incidenceMatrix
    (G : BiregularBipartiteGraph A B) (a : A) :
    columnWeight G.incidenceMatrix a = G.leftDegree := by
  simpa [columnWeight, HammingWeight, hammingSupport, incidenceMatrix] using
    G.left_regular a

/-- The exact diagonal HGP blocklength for the LTZ15 incidence matrix. -/
theorem card_qubitIndex_hypergraphProductData
    (_G : BiregularBipartiteGraph A B) :
    Fintype.card (QubitIndex B A B A) =
      Fintype.card A ^ 2 + Fintype.card B ^ 2 := by
  simpa [pow_two] using
    (card_qubitIndex (rowOne := B) (colOne := A)
      (rowTwo := B) (colTwo := A))

/-- The diagonal HGP dimension formula implies the LTZ15 lower bound
`K ≥ (n_A - n_B)²` without a rank assumption. -/
theorem finrank_middleHomology_ge_card_sub_sq
    (G : BiregularBipartiteGraph A B)
    (hSize : Fintype.card B ≤ Fintype.card A) :
    (Fintype.card A - Fintype.card B) ^ 2 ≤
      Module.finrank (ZMod 2) (chainComplex G.hypergraphProductData).middleHomology := by
  let k := Dimension (firstCode G.hypergraphProductData)
  let kT := Dimension (firstTransposeCode G.hypergraphProductData)
  have hRelation :=
    first_dimension_add_rows_eq_cols_add_transpose_dimension
      G.hypergraphProductData
  have hRelation' :
      k + Fintype.card B = Fintype.card A + kT := by
    exact hRelation
  have hCardDecomp :
      Fintype.card A =
        (Fintype.card A - Fintype.card B) + Fintype.card B :=
    (Nat.sub_add_cancel hSize).symm
  have hk : Fintype.card A - Fintype.card B ≤ k := by
    omega
  have hSquare :
      (Fintype.card A - Fintype.card B) *
          (Fintype.card A - Fintype.card B) ≤ k * k :=
    Nat.mul_le_mul hk hk
  rw [finrank_middleHomology_eq_dimension_products]
  change (Fintype.card A - Fintype.card B) ^ 2 ≤
    k * k + kT * kT
  rw [pow_two]
  exact hSquare.trans (Nat.le_add_right (k * k) (kT * kT))

/-- The LTZ15 expansion lower bound for the exact diagonal quantum distance.
-/
theorem quantumDistance_expansion_bound
    (G : BiregularBipartiteGraph A B)
    {γA δA γB δB : Real}
    (hExpand : G.LeftRightExpanding γA δA γB δB)
    (hδA : δA < 1 / 2) (hδB : δB < 1 / 2) :
    ENNReal.ofReal
        (min (γA * Fintype.card A) (γB * Fintype.card B)) ≤
      extendedNatToENNReal
        (extendedAlgebraicCSSMinimumDistance
          (binaryCSSCode G.hypergraphProductData).xCode
          (binaryCSSCode G.hypergraphProductData).zCode) := by
  have hLeft := ofReal_left_expansion_le_extendedMinimumDistance
    G hExpand.1 hδA
  have hRight := ofReal_right_expansion_le_extendedMinimumDistance
    G hExpand.2 hδB
  rw [quantumDistance_eq_min_classicalDistances,
    extendedNatToENNReal_min, ENNReal.ofReal_min]
  exact min_le_min hLeft hRight

/-- Exact finite Leverrier--Tillich--Zemor quantum-expander construction and
distance theorem.  The graph supplies its incidence matrix internally; every
parameter and distance conclusion is derived. -/
theorem leverrierTillichZemorQuantumExpanderParameters
    (G : QEC.Coding.QuantumExpander.BiregularBipartiteGraph A B)
    (hSize : Fintype.card B ≤ Fintype.card A)
    {γA δA γB δB : Real}
    (hγA : 0 < γA) (hδApos : 0 < δA)
    (hγB : 0 < γB) (hδBpos : 0 < δB)
    (hExpand : G.LeftRightExpanding γA δA γB δB)
    (hδA : δA < 1 / 2) (hδB : δB < 1 / 2) :
    G.leftDegree ≤ G.rightDegree ∧
    (binaryCSSCode G.hypergraphProductData).stabilizer.IsSourceValidBinary ∧
    Fintype.card (QubitIndex B A B A) =
      Fintype.card A ^ 2 + Fintype.card B ^ 2 ∧
    (Fintype.card A - Fintype.card B) ^ 2 ≤
      Module.finrank (ZMod 2)
        (chainComplex G.hypergraphProductData).middleHomology ∧
    (∀ b a, HammingWeight
        (wordLinearMapTranspose (boundary1 G.hypergraphProductData)
          (Pi.single (b, a) 1)) = G.leftDegree + G.rightDegree) ∧
    (∀ a b, HammingWeight
        (boundary2 G.hypergraphProductData (Pi.single (a, b) 1)) =
          G.leftDegree + G.rightDegree) ∧
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode G.hypergraphProductData).xCode
        (binaryCSSCode G.hypergraphProductData).zCode =
      min
        (extendedMinimumDistance (firstCode G.hypergraphProductData))
        (extendedMinimumDistance
          (firstTransposeCode G.hypergraphProductData)) ∧
    ENNReal.ofReal
        (min (γA * Fintype.card A) (γB * Fintype.card B)) ≤
      extendedNatToENNReal
        (extendedAlgebraicCSSMinimumDistance
          (binaryCSSCode G.hypergraphProductData).xCode
          (binaryCSSCode G.hypergraphProductData).zCode) := by
  have _hSourcePositiveParameters :
      0 < γA ∧ 0 < δA ∧ 0 < γB ∧ 0 < δB :=
    ⟨hγA, hδApos, hγB, hδBpos⟩
  refine ⟨leftDegree_le_rightDegree G hSize,
    binaryCSSCode_stabilizer_isSourceValidBinary G.hypergraphProductData,
    card_qubitIndex_hypergraphProductData G,
    finrank_middleHomology_ge_card_sub_sq G hSize, ?_, ?_,
    quantumDistance_eq_min_classicalDistances G,
    quantumDistance_expansion_bound G hExpand hδA hδB⟩
  · intro b a
    calc
      HammingWeight
          (wordLinearMapTranspose (boundary1 G.hypergraphProductData)
            (Pi.single (b, a) 1)) =
          rowWeight G.incidenceMatrix b +
            columnWeight G.incidenceMatrix a := by
        simpa [hypergraphProductData] using
          (xCheckWeight_diagonal_eq G.incidenceMatrix b a)
      _ = G.leftDegree + G.rightDegree := by
        rw [rowWeight_incidenceMatrix, columnWeight_incidenceMatrix, add_comm]
  · intro a b
    calc
      HammingWeight
          (boundary2 G.hypergraphProductData (Pi.single (a, b) 1)) =
          rowWeight G.incidenceMatrix b +
            columnWeight G.incidenceMatrix a := by
        simpa [hypergraphProductData] using
          (zCheckWeight_diagonal_eq G.incidenceMatrix a b)
      _ = G.leftDegree + G.rightDegree := by
        rw [rowWeight_incidenceMatrix, columnWeight_incidenceMatrix, add_comm]

end BiregularBipartiteGraph

end QEC.Coding.QuantumExpander
