import QEC.Coding.FiniteAlternatingConstruction.DecodingGraph
import QEC.Coding.FiniteAlternatingConstruction.ReplacementCochainMaps
import QEC.Coding.FiniteAlternatingConstruction.RXPresentationCochain

/-!
# Actual finite alternating cochain maps

The parity-selected steps use the concrete RX and RZ maps on the recursive
presentations already used by the decoding graph. Their composition identities
follow from the proved successor incidence bridges and adjacent cochain equations.
-/

namespace QEC.Coding.BDL26AlternatingCochain

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26DecodingGraph

abbrev Field := BDL26FiniteTannerSquare.Field

noncomputable def nextMap0 (S : OddScale) (n : Nat) (C : ConstructionState) :
    Word Field C.presentation.X →ₗ[Field] Word Field (nextState S n C).presentation.X := by
  classical
  by_cases h : n % 2 = 0
  · exact Eq.mpr
      (congrArg (fun D : ConstructionState =>
        Word Field C.presentation.X →ₗ[Field] Word Field D.presentation.X)
        (show nextState S n C = rxState S C from if_pos h))
      (rxMap0Coord C.presentation S)
  · exact Eq.mpr
      (congrArg (fun D : ConstructionState =>
        Word Field C.presentation.X →ₗ[Field] Word Field D.presentation.X)
        (show nextState S n C = rzState S C from if_neg h))
      (rzMap0Coord C.presentation S)

noncomputable def nextMap1 (S : OddScale) (n : Nat) (C : ConstructionState) :
    Word Field C.presentation.Q →ₗ[Field] Word Field (nextState S n C).presentation.Q := by
  classical
  by_cases h : n % 2 = 0
  · exact Eq.mpr
      (congrArg (fun D : ConstructionState =>
        Word Field C.presentation.Q →ₗ[Field] Word Field D.presentation.Q)
        (show nextState S n C = rxState S C from if_pos h))
      (rxMap1Coord C.presentation S)
  · exact Eq.mpr
      (congrArg (fun D : ConstructionState =>
        Word Field C.presentation.Q →ₗ[Field] Word Field D.presentation.Q)
        (show nextState S n C = rzState S C from if_neg h))
      (map1Coord C.presentation C.admissible S)

noncomputable def nextMap2 (S : OddScale) (n : Nat) (C : ConstructionState) :
    Word Field C.presentation.Z →ₗ[Field] Word Field (nextState S n C).presentation.Z := by
  classical
  by_cases h : n % 2 = 0
  · exact Eq.mpr
      (congrArg (fun D : ConstructionState =>
        Word Field C.presentation.Z →ₗ[Field] Word Field D.presentation.Z)
        (show nextState S n C = rxState S C from if_pos h))
      (rxMap2Coord C.presentation S)
  · exact Eq.mpr
      (congrArg (fun D : ConstructionState =>
        Word Field C.presentation.Z →ₗ[Field] Word Field D.presentation.Z)
        (show nextState S n C = rzState S C from if_neg h))
      (map2Coord C.presentation C.admissible S)

private theorem transport_commutes0
    (C D E : ConstructionState) (h : D = E)
    (m0 : Word Field C.presentation.X →ₗ[Field] Word Field E.presentation.X)
    (m1 : Word Field C.presentation.Q →ₗ[Field] Word Field E.presentation.Q)
    (hc : (tannerCoboundary0 E.presentation).comp m0 =
      m1.comp (tannerCoboundary0 C.presentation)) :
    (tannerCoboundary0 D.presentation).comp
      (Eq.mpr (congrArg (fun B : ConstructionState =>
        Word Field C.presentation.X →ₗ[Field] Word Field B.presentation.X) h) m0) =
    (Eq.mpr (congrArg (fun B : ConstructionState =>
      Word Field C.presentation.Q →ₗ[Field] Word Field B.presentation.Q) h) m1).comp
        (tannerCoboundary0 C.presentation) := by
  cases h
  exact hc

private theorem transport_commutes1
    (C D E : ConstructionState) (h : D = E)
    (m1 : Word Field C.presentation.Q →ₗ[Field] Word Field E.presentation.Q)
    (m2 : Word Field C.presentation.Z →ₗ[Field] Word Field E.presentation.Z)
    (hc : (tannerCoboundary1 E.presentation).comp m1 =
      m2.comp (tannerCoboundary1 C.presentation)) :
    (tannerCoboundary1 D.presentation).comp
      (Eq.mpr (congrArg (fun B : ConstructionState =>
        Word Field C.presentation.Q →ₗ[Field] Word Field B.presentation.Q) h) m1) =
    (Eq.mpr (congrArg (fun B : ConstructionState =>
      Word Field C.presentation.Z →ₗ[Field] Word Field B.presentation.Z) h) m2).comp
        (tannerCoboundary1 C.presentation) := by
  cases h
  exact hc

/-- The actual parity-selected step commutes in degrees zero and one. -/
theorem nextMap_commutes0 (S : OddScale) (n : Nat) (C : ConstructionState) :
    (tannerCoboundary0 (nextState S n C).presentation).comp (nextMap0 S n C) =
      (nextMap1 S n C).comp (tannerCoboundary0 C.presentation) := by
  classical
  by_cases h : n % 2 = 0
  · have hc : (tannerCoboundary0 (rxState S C).presentation).comp
        (rxMap0Coord C.presentation S) =
      (rxMap1Coord C.presentation S).comp (tannerCoboundary0 C.presentation) := by
      change (tannerCoboundary0 (rxReplacementPresentation C.presentation S)).comp _ = _
      erw [rxPresentation_coboundary0_eq C.presentation C.admissible C.regular S]
      exact rxMap_commutes_coboundary0 C.presentation C.admissible.toTannerSquareAdmissible S
    have ht := transport_commutes0 C (nextState S n C) (rxState S C)
      (show nextState S n C = rxState S C from if_pos h) _ _ hc
    simpa only [nextMap0, nextMap1, dif_pos h] using ht
  · have ht := transport_commutes0 C (nextState S n C) (rzState S C)
      (show nextState S n C = rzState S C from if_neg h)
      (rzMap0Coord C.presentation S) (map1Coord C.presentation C.admissible S)
      (rzMap_commutes_coboundary0 C.presentation C.admissible S)
    simpa only [nextMap0, nextMap1, dif_neg h] using ht

/-- The actual parity-selected step commutes in degrees one and two. -/
theorem nextMap_commutes1 (S : OddScale) (n : Nat) (C : ConstructionState) :
    (tannerCoboundary1 (nextState S n C).presentation).comp (nextMap1 S n C) =
      (nextMap2 S n C).comp (tannerCoboundary1 C.presentation) := by
  classical
  by_cases h : n % 2 = 0
  · have hc : (tannerCoboundary1 (rxState S C).presentation).comp
        (rxMap1Coord C.presentation S) =
      (rxMap2Coord C.presentation S).comp (tannerCoboundary1 C.presentation) := by
      change (tannerCoboundary1 (rxReplacementPresentation C.presentation S)).comp _ = _
      erw [rxPresentation_coboundary1_eq C.presentation C.admissible C.regular S]
      exact rxMap_commutes_coboundary1 C.presentation S
    have ht := transport_commutes1 C (nextState S n C) (rxState S C)
      (show nextState S n C = rxState S C from if_pos h) _ _ hc
    simpa only [nextMap1, nextMap2, dif_pos h] using ht
  · have ht := transport_commutes1 C (nextState S n C) (rzState S C)
      (show nextState S n C = rzState S C from if_neg h)
      (map1Coord C.presentation C.admissible S) (map2Coord C.presentation C.admissible S)
      (rzMap_commutes_coboundary1 C.presentation C.admissible S)
    simpa only [nextMap1, nextMap2, dif_neg h] using ht

noncomputable def stepMap0 (S : OddScale) (n : Nat) :
    Word Field (state S n).presentation.X →ₗ[Field]
      Word Field (state S (n + 1)).presentation.X := nextMap0 S n (state S n)

noncomputable def stepMap1 (S : OddScale) (n : Nat) :
    Word Field (state S n).presentation.Q →ₗ[Field]
      Word Field (state S (n + 1)).presentation.Q := nextMap1 S n (state S n)

noncomputable def stepMap2 (S : OddScale) (n : Nat) :
    Word Field (state S n).presentation.Z →ₗ[Field]
      Word Field (state S (n + 1)).presentation.Z := nextMap2 S n (state S n)

/-- Degree-zero map through the first `n` actual replacement steps. -/
noncomputable def map0 (S : OddScale) (n : Nat) := finiteCoordinateComposite (stepMap0 S) n
/-- Degree-one map through the first `n` actual replacement steps. -/
noncomputable def map1 (S : OddScale) (n : Nat) := finiteCoordinateComposite (stepMap1 S) n
/-- Degree-two map through the first `n` actual replacement steps. -/
noncomputable def map2 (S : OddScale) (n : Nat) := finiteCoordinateComposite (stepMap2 S) n

/-- Every finite actual alternating prefix commutes with the zero coboundary. -/
theorem map_commutes0 (S : OddScale) (n : Nat) :
    (tannerCoboundary0 (state S n).presentation).comp (map0 S n) =
      (map1 S n).comp (tannerCoboundary0 (state S 0).presentation) := by
  exact finiteCoordinateComposite_commutes (stepMap0 S) (stepMap1 S)
    (fun k => tannerCoboundary0 (state S k).presentation)
    (fun k => nextMap_commutes0 S k (state S k)) n

/-- Every finite actual alternating prefix commutes with the one coboundary. -/
theorem map_commutes1 (S : OddScale) (n : Nat) :
    (tannerCoboundary1 (state S n).presentation).comp (map1 S n) =
      (map2 S n).comp (tannerCoboundary1 (state S 0).presentation) := by
  exact finiteCoordinateComposite_commutes (stepMap1 S) (stepMap2 S)
    (fun k => tannerCoboundary1 (state S k).presentation)
    (fun k => nextMap_commutes1 S k (state S k)) n

end QEC.Coding.BDL26AlternatingCochain
