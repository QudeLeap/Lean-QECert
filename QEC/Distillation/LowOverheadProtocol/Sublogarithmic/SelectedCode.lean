import QEC.Distillation.LowOverheadProtocol.Sublogarithmic.ParameterSelection
import QEC.Distillation.LowOverheadProtocol.Core.PuncturedReedMuller

/-!
# HH18 sublogarithmic selected punctured Reed--Muller code

This module instantiates the actual punctured Reed--Muller CSS/stabilizer and
encoded-code constructions at the denominator-cleared parameters supplied by
the finite Gamma selector.  It contains no metadata substitute, alternative
code route, or terminal result.
-/

namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy

open Coding
open Coding.PuncturedReedMuller
open QEC.Distillation.HH18PuncturedReedMuller

/-! ## Selected actual CSS and encoded codes -/

/-- The selector's cleared parameters satisfy the actual #759 admissibility
condition; this is proved from the natural sequence, not stored as metadata. -/
theorem selected_parameter_admissible (A D j : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    Admissible (parameterW A j) (parameterR D j) (parameterM D j) :=
  (parameter_sequence_admissible A D j hA hD hwindow hj).2.2

/-- The direct #759 CSS code at the selected punctured Reed--Muller parameters. -/
noncomputable def selectedCSSCode (A D j : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :=
  cssCode (selected_parameter_admissible A D j hA hD hwindow hj)

/-- The direct #759 logical-to-physical encoded code at the same parameters. -/
noncomputable def selectedEncodedCode (A D j : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :=
  encodedCode (selected_parameter_admissible A D j hA hD hwindow hj)

/-- The exact #759 physical, logical, carrier, and semantic-distance counts
are respectively the selector's n, k, 2^k, and d. -/
theorem selectedCSSCode_parameters (A D j : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    Length (ZMod 2) (PhysicalSite (parameterM D j) (parameterW A j)) =
        parameterLength A D j ∧
      Length (ZMod 2) (PhysicalSite (parameterM D j) (parameterW A j)) -
          Dimension (xCode (parameterW A j) (parameterR D j) (parameterM D j)) -
          Dimension (zCode (parameterW A j) (parameterR D j) (parameterM D j)) =
        parameterDimension A D j ∧
      Module.finrank Complex
          (selectedCSSCode A D j hA hD hwindow hj).stabilizer.code.carrier =
        2 ^ parameterDimension A D j ∧
      StabilizerCode.SemanticStabilizerDistance
          (sourceValidStabilizer
            (selected_parameter_admissible A D j hA hD hwindow hj))
          (parameterDistance A D j) := by
  exact cssParameters (selected_parameter_admissible A D j hA hD hwindow hj)

/-- The selected row has exactly the degree condition required by the #759
simultaneous transversal-T theorem. -/
theorem selected_transversal_t_degree (_A D j : Nat) :
    3 * parameterR D j < parameterM D j := by
  unfold parameterR parameterM
  calc
    3 * (2 * D * j) = 6 * D * j := by ring
    _ < 6 * D * j + 1 := Nat.lt_succ_self _

/-! ## Exact simultaneous T orientation -/

/-- The direct #759 sitewise-transversal physical-T implementation has
simultaneous logical T-dagger action. -/
noncomputable def selectedPhysicalT_sitewise_transversal (A D j : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    SitewiseTransversalLogicalGate
      (selectedEncodedCode A D j hA hD hwindow hj)
      (logicalTInv (parameterW A j) (parameterM D j))
      (Triorthogonal.diagonalPhaseGateModel
        (Index := PhysicalSite (parameterM D j) (parameterW A j))) := by
  simpa [selectedEncodedCode] using
    (physicalT_sitewise_transversal
      (selected_parameter_admissible A D j hA hD hwindow hj)
      (selected_transversal_t_degree A D j))

/-- Simultaneous physical T implements simultaneous logical T-dagger. -/
theorem selected_physicalT_implements_logicalTInv (A D j : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    (selectedEncodedCode A D j hA hD hwindow hj).ImplementsLogicalGate
      (physicalT (parameterW A j) (parameterM D j))
      (logicalTInv (parameterW A j) (parameterM D j)) := by
  simpa [selectedEncodedCode] using
    (physicalT_implements_logicalTInv
      (selected_parameter_admissible A D j hA hD hwindow hj)
      (selected_transversal_t_degree A D j))

/-- Logical T is obtained only through the proved inverse physical action. -/
theorem selected_physicalTInv_implements_logicalT (A D j : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    (selectedEncodedCode A D j hA hD hwindow hj).ImplementsLogicalGate
      (physicalTInv (parameterW A j) (parameterM D j))
      (logicalT (parameterW A j) (parameterM D j)) := by
  simpa [selectedEncodedCode] using
    (physicalTInv_implements_logicalT
      (selected_parameter_admissible A D j hA hD hwindow hj)
      (selected_transversal_t_degree A D j))

/-! ## Bridge from the every-eta selector -/

/-- Every finite Gamma-selector witness instantiates the actual #759 encoded
code with its exact n, k, and d, together with the two correctly oriented
simultaneous transversal actions. -/
theorem exists_selected_code_bridge (eta : ℝ) (heta : 0 < eta) :
    ∃ q : ℚ, ∃ A D j : Nat,
      (1 / 6 : ℚ) < q ∧ q < (1 / 3 : ℚ) ∧
        0 < A ∧ 0 < D ∧ 3 * A < D ∧ 0 < j ∧ q = (A : ℚ) / D ∧
        let r := parameterR D j
        let w := parameterW A j
        let m := parameterM D j
        let n := parameterLength A D j
        let k := parameterDimension A D j
        let d := parameterDistance A D j
        ∃ h : Admissible w r m,
          (w : ℚ) = 3 * (r : ℚ) * q ∧
            Length (ZMod 2) (PhysicalSite m w) = n ∧
              Length (ZMod 2) (PhysicalSite m w) -
                  Dimension (xCode w r m) - Dimension (zCode w r m) = k ∧
                Module.finrank Complex (cssCode h).stabilizer.code.carrier = 2 ^ k ∧
                  StabilizerCode.SemanticStabilizerDistance
                    (sourceValidStabilizer h) d ∧
                    (encodedCode h).ImplementsLogicalGate
                      (physicalT w m) (logicalTInv w m) ∧
                    (encodedCode h).ImplementsLogicalGate
                      (physicalTInv w m) (logicalT w m) := by
  rcases exists_finite_subunit_gamma_selector eta heta with
    ⟨q, A, D, j, hqL, hqU, hA, hD, hwindow, hj, hq, hselector⟩
  dsimp [parameterR, parameterW, parameterM, parameterLength,
    parameterDimension, parameterDistance] at hselector
  rcases hselector with ⟨hadmissible, hslope, _, _, _, _⟩
  refine ⟨q, A, D, j, hqL, hqU, hA, hD, hwindow, hj, hq, ?_⟩
  dsimp [parameterR, parameterW, parameterM, parameterLength,
    parameterDimension, parameterDistance]
  rcases cssParameters hadmissible with ⟨hlength, hlogical, hcarrier, hdistance⟩
  refine ⟨hadmissible, hslope, hlength, hlogical, hcarrier, hdistance, ?_, ?_⟩
  · exact physicalT_implements_logicalTInv hadmissible
      (selected_transversal_t_degree A D j)
  · exact physicalTInv_implements_logicalT hadmissible
      (selected_transversal_t_degree A D j)

end QEC.Distillation.HH18.HH18SublogarithmicEntropy
