import QEC.Coding.FiniteAlternatingConstruction.ReplacementSupport
import QEC.Coding.FiniteAlternatingConstruction.ReplacementCochainMaps

/-!
# The staged RX Q restriction

The Q block receives an X-to-Q connecting boundary. Its local differential
therefore describes the global restriction only after the X error vanishes.
The final finite example records why the unrestricted statement is false.
-/

namespace QEC.Coding.BDL26RXStagedRestriction

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26ReplacementSupport BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators

/-- The Q-to-Z connecting term has no Q syndrome coordinates. -/
theorem qzConnecting_at_q (P : TannerSquarePresentation) (S : OddScale)
    (e : Word BDL26Field (RX1 P S)) (q : P.Q) (a : QDoubleCylinderEdge P q S) :
    rxConnectingQZ1 P S e (Sum.inl (Sum.inr ⟨q,a⟩)) = 0 := by
  rw [rxConnectingQZ1, wordLinearMapTranspose_toLin'_apply]
  apply Finset.sum_eq_zero
  intro source _
  rcases source with xEdge | qVertex <;> simp [rxQZBoundary2Matrix]

/-- Actual materialized Q restriction after all X correction coordinates vanish. -/
theorem rxCoboundary1_q_of_x_zero (P : TannerSquarePresentation) (S : OddScale)
    (e : Word BDL26Field (RX1 P S))
    (hX : ∀ x edge, e (Sum.inl ⟨x,edge⟩) = 0)
    (q : P.Q) (a : QDoubleCylinderEdge P q S) :
    rxCoboundary1 P S e (Sum.inl (Sum.inr ⟨q,a⟩)) =
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
        (fun vertex => e (Sum.inr ⟨q,vertex⟩)) a := by
  have hconnect := rxConnectingXQ1_zero_on_q P S e (fun xe => hX xe.1 xe.2)
  rw [rxCoboundary1, rxDelta1_decomposition]
  simp only [LinearMap.add_apply, Pi.add_apply, hconnect, add_zero]
  rw [qzConnecting_at_q, add_zero]
  exact rxLocalDelta1_apply_q P S e q a

/-- Owner-fibre zero is the actual-error premise, not merely zero X syndrome. -/
theorem rxCoboundary1_q_of_x_restrictions_zero
    (P : TannerSquarePresentation) (S : OddScale) (e : Word BDL26Field (RX1 P S))
    (hX : ∀ x, restrictWordLinear (fiberRegion (rxCorrectionOwner P S) (.x x)) e = 0)
    (q : P.Q) (a : QDoubleCylinderEdge P q S) :
    rxCoboundary1 P S e (Sum.inl (Sum.inr ⟨q,a⟩)) =
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
        (fun vertex => e (Sum.inr ⟨q,vertex⟩)) a := by
  apply rxCoboundary1_q_of_x_zero P S e
  intro x edge
  exact congrFun (hX x) ⟨Sum.inl ⟨x,edge⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

/-- A single X-owned basis error has zero restriction to every Q correction block. -/
theorem xBasis_q_restriction_zero (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (b : DoubleCylinderEdge P x S) (q : P.Q) :
    (fun vertex : QDoubleCylinderVertex P q S =>
      canonicalBasisWord (F := BDL26Field) (Sum.inl ⟨x,b⟩ : RX1 P S) (Sum.inr ⟨q,vertex⟩)) = 0 := by
  funext vertex
  simp [canonicalBasisWord]

/-- The actual X-to-Q matrix coefficient survives on the incident basis error. -/
theorem xBasis_q_syndrome_one (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (q : P.Q) (h : P.xq x q = true) (a : QDoubleCylinderEdge P q S) :
    rxCoboundary1 P S
      (canonicalBasisWord (Sum.inl ⟨x,qToXDoubleCylinderEdgeRaw P q x h S a⟩))
      (Sum.inl (Sum.inr ⟨q,a⟩)) = 1 := by
  rw [rxCoboundary1, rxBoundary2, wordLinearMapTranspose_toLin'_apply]
  rw [Fintype.sum_eq_single
    (Sum.inl ⟨x,qToXDoubleCylinderEdgeRaw P q x h S a⟩ : RX1 P S)]
  · simp [canonicalBasisWord, rxBoundary2Matrix, qDoubleCylinderEdgeXIncidence, h]
  · intro other hne
    simp [canonicalBasisWord, Ne.symm hne]

/-- A completely concrete Q edge in the scale-five seed replacement. -/
def seedQEdge : QDoubleCylinderEdge baseTannerSquarePresentation (0 : BaseQubit) scaleFive :=
  Sum.inr ⟨(0 : BaseZ), by decide⟩

noncomputable def seedXEdge :
    DoubleCylinderEdge baseTannerSquarePresentation (0 : BaseX) scaleFive :=
  qToXDoubleCylinderEdgeRaw baseTannerSquarePresentation (0 : BaseQubit)
    (0 : BaseX) (by decide) scaleFive seedQEdge

noncomputable def seedError : Word BDL26Field (RX1 baseTannerSquarePresentation scaleFive) :=
  canonicalBasisWord (Sum.inl ⟨(0 : BaseX),seedXEdge⟩)

theorem seedError_q_restriction_zero (q : BaseQubit) :
    (fun vertex : QDoubleCylinderVertex baseTannerSquarePresentation q scaleFive =>
      seedError (Sum.inr ⟨q,vertex⟩)) = 0 :=
  xBasis_q_restriction_zero baseTannerSquarePresentation scaleFive (0 : BaseX) seedXEdge q

theorem seedError_q_syndrome_one :
    rxCoboundary1 baseTannerSquarePresentation scaleFive seedError
      (Sum.inl (Sum.inr ⟨(0 : BaseQubit),seedQEdge⟩)) = 1 :=
  xBasis_q_syndrome_one _ _ _ _ (by decide) _

/-- The previous unconditional restriction cannot hold for the actual fibres. -/
theorem seed_unrestricted_q_restriction_false :
    ¬ (∀ e : Word BDL26Field (RX1 baseTannerSquarePresentation scaleFive),
      rxCoboundary1 baseTannerSquarePresentation scaleFive e
        (Sum.inl (Sum.inr ⟨(0 : BaseQubit),seedQEdge⟩)) =
      wordLinearMapTranspose (qDoubleCylinderBoundary1 baseTannerSquarePresentation
        (0 : BaseQubit) scaleFive)
        (fun vertex => e (Sum.inr ⟨(0 : BaseQubit),vertex⟩)) seedQEdge) := by
  intro h
  have he := h seedError
  rw [seedError_q_syndrome_one, seedError_q_restriction_zero, map_zero] at he
  exact one_ne_zero he

end QEC.Coding.BDL26RXStagedRestriction
