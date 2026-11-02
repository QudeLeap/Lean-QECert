import QEC.Coding.ExpanderCodes.QuantumExpander

/-!
# Quantum-expander parameter theorem

Final LTZ15 parameter assembly. Graphs, incidence, expansion and distance methods
are owned by `QEC.Coding.ExpanderCodes.QuantumExpander`.
-/

noncomputable section

namespace QEC.Coding.QuantumExpander

open QEC.Coding.HypergraphProduct
open scoped ENNReal

universe u

namespace BiregularBipartiteGraph

variable {A B : Type u}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

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
