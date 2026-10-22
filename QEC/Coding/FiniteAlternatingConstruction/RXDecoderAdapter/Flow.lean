import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Coordinates

/-! # Actual RX flow identities -/

namespace QEC.Coding.BDL26RXDecoderAdapter

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

-- Next support layer draft; not yet part of the frozen compiler candidate.
noncomputable def xExtend (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    Word BDL26Field (DoubleCylinderEdge P x S) →ₗ[BDL26Field] Word BDL26Field (RX1 P S) :=
  (extendWordLinear ((localX P S).correctionRegion x)).comp
    (wordEquiv (xCorrectionEquiv P S x)).toLinearMap

noncomputable def qExtend (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    Word BDL26Field (QDoubleCylinderVertex P q S) →ₗ[BDL26Field] Word BDL26Field (RX1 P S) :=
  (extendWordLinear ((localQ P S).correctionRegion q)).comp
    (wordEquiv (qCorrectionEquiv P S q)).toLinearMap

@[simp] theorem regionExtension_apply {A : Type} [Fintype A] [DecidableEq A]
    (Y : Finset A) (w : Word BDL26Field (LocalRegionIndex Y)) (p : A) :
    extendWordLinear Y w p = extendLocalSignal Y w p := rfl

-- General coordinate-extension lemma avoids repeatedly reducing a Finset decider.
theorem extend_reindex_at {A B : Type} [Fintype B] [DecidableEq B]
    (Y : Finset B) (e : A ≃ LocalRegionIndex Y) (w : Word BDL26Field A) (a : A) :
    extendWordLinear Y (wordEquiv e w) (e a).1 = w a := by
  change extendLocalSignal Y (wordEquiv e w) (e a).1 = w a
  simp only [extendLocalSignal, dif_pos (e a).2]
  change w (e.symm (e a)) = w a
  rw [e.symm_apply_apply]

theorem xExtend_at_x (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderEdge P x S)) (a : DoubleCylinderEdge P x S) :
    xExtend P S x w (Sum.inl ⟨x,a⟩) = w a :=
  extend_reindex_at _ (xCorrectionEquiv P S x) w a

theorem qExtend_at_q (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (a : QDoubleCylinderVertex P q S) :
    qExtend P S q w (Sum.inr ⟨q,a⟩) = w a :=
  extend_reindex_at _ (qCorrectionEquiv P S q) w a

theorem xExtend_at_q (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderEdge P x S)) (q : P.Q)
    (v : QDoubleCylinderVertex P q S) : xExtend P S x w (Sum.inr ⟨q,v⟩) = 0 := by
  change extendLocalSignal ((localX P S).correctionRegion x) _ (Sum.inr ⟨q,v⟩) = 0
  rw [extendLocalSignal, dif_neg]
  intro hp
  have h := (Finset.mem_filter.mp hp).2
  cases h

theorem qExtend_at_x (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (x : P.X)
    (e : DoubleCylinderEdge P x S) : qExtend P S q w (Sum.inl ⟨x,e⟩) = 0 := by
  change extendLocalSignal ((localQ P S).correctionRegion q) _ (Sum.inl ⟨x,e⟩) = 0
  rw [extendLocalSignal, dif_neg]
  intro hp
  have h := (Finset.mem_filter.mp hp).2
  cases h

theorem xExtend_other (P : TannerSquarePresentation) (S : OddScale) (x y : P.X)
    (h : y ≠ x) (w : Word BDL26Field (DoubleCylinderEdge P x S))
    (e : DoubleCylinderEdge P y S) : xExtend P S x w (Sum.inl ⟨y,e⟩) = 0 := by
  change extendLocalSignal ((localX P S).correctionRegion x) _ (Sum.inl ⟨y,e⟩) = 0
  rw [extendLocalSignal, dif_neg]
  intro hp
  exact h (Vertex.x.inj (Finset.mem_filter.mp hp).2)

theorem qExtend_other (P : TannerSquarePresentation) (S : OddScale) (q r : P.Q)
    (h : r ≠ q) (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (v : QDoubleCylinderVertex P r S) : qExtend P S q w (Sum.inr ⟨r,v⟩) = 0 := by
  change extendLocalSignal ((localQ P S).correctionRegion q) _ (Sum.inr ⟨r,v⟩) = 0
  rw [extendLocalSignal, dif_neg]
  intro hp
  exact h (Vertex.q.inj (Finset.mem_filter.mp hp).2)

noncomputable def xFlow (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    Word BDL26Field (DoubleCylinderEdge P x S) →ₗ[BDL26Field] Word BDL26Field (RX2 P S) :=
  (rxConnectingXQ1 P S).comp (xExtend P S x)

noncomputable def qFlow (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    Word BDL26Field (QDoubleCylinderVertex P q S) →ₗ[BDL26Field] Word BDL26Field (RX2 P S) :=
  (rxConnectingQZ1 P S).comp (qExtend P S q)

-- Next: use rxConnectingXQ1_apply_q / rxConnectingQZ1_apply_z,
-- reduce finite sums to one owner with xExtend_other / qExtend_other,
-- convert HammingWeight via card_filter + sum_sum_type + sum_sigma.

theorem xFlow_at_q (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (w : Word BDL26Field (DoubleCylinderEdge P x S))
    (q : P.Q) (e : QDoubleCylinderEdge P q S) :
    xFlow P S x w (Sum.inl (Sum.inr ⟨q,e⟩)) =
      if h : P.xq x q = true then rxXQDegreeOne P A q x h S w e else 0 := by
  rw [xFlow, LinearMap.comp_apply, rxConnectingXQ1_apply_q P A]
  rw [Fintype.sum_eq_single x]
  · by_cases h : P.xq x q = true
    · simp only [dif_pos h]
      have hw : (fun a => xExtend P S x w (Sum.inl ⟨x,a⟩)) = w := by
        funext a
        exact xExtend_at_x P S x w a
      rw [hw]
    · simp [h]
  · intro y hy
    by_cases h : P.xq y q = true
    · simp only [dif_pos h]
      have hz : (fun a => xExtend P S x w (Sum.inl ⟨y,a⟩)) = 0 := by
        funext a
        exact xExtend_other P S x y hy w a
      rw [hz, map_zero]
      rfl
    · simp [h]

theorem qFlow_at_z (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (z : P.Z) (c : Fin 2) :
    qFlow P S q w (Sum.inr (z,c)) = rxQOutgoing P q S w z c := by
  rw [qFlow, LinearMap.comp_apply, rxConnectingQZ1_apply_z]
  rw [Fintype.sum_eq_single q]
  · congr 1
    funext v
    exact qExtend_at_q P S q w v
  · intro r hr
    have hz : (fun v => qExtend P S q w (Sum.inr ⟨r,v⟩)) = 0 := by
      funext v
      exact qExtend_other P S q r hr w v
    rw [hz]
    simp [rxQOutgoing]

-- Matrix blocks retain their exact target sector.
theorem xFlow_at_x (P : TannerSquarePresentation) (S : OddScale) (x y : P.X)
    (w : Word BDL26Field (DoubleCylinderEdge P x S)) (f : DoubleCylinderFace P y S) :
    xFlow P S x w (Sum.inl (Sum.inl ⟨y,f⟩)) = 0 := by
  rw [xFlow, LinearMap.comp_apply, rxConnectingXQ1, wordLinearMapTranspose_toLin'_apply]
  apply Finset.sum_eq_zero
  intro source _
  rcases source with xe | qv <;> simp [rxXQBoundary2Matrix]

theorem xFlow_at_z (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderEdge P x S)) (z : P.Z) (c : Fin 2) :
    xFlow P S x w (Sum.inr (z,c)) = 0 := by
  rw [xFlow, LinearMap.comp_apply, rxConnectingXQ1, wordLinearMapTranspose_toLin'_apply]
  apply Finset.sum_eq_zero
  intro source _
  rcases source with xe | qv <;> simp [rxXQBoundary2Matrix]

theorem qFlow_at_x (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (x : P.X)
    (f : DoubleCylinderFace P x S) : qFlow P S q w (Sum.inl (Sum.inl ⟨x,f⟩)) = 0 := by
  rw [qFlow, LinearMap.comp_apply, rxConnectingQZ1, wordLinearMapTranspose_toLin'_apply]
  apply Finset.sum_eq_zero
  intro source _
  rcases source with xe | qv <;> simp [rxQZBoundary2Matrix]

theorem qFlow_at_q (P : TannerSquarePresentation) (S : OddScale) (q r : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (e : QDoubleCylinderEdge P r S) :
    qFlow P S q w (Sum.inl (Sum.inr ⟨r,e⟩)) = 0 :=
  qzConnecting_at_q P S (qExtend P S q w) r e

/-- Count actual tagged coordinates, retaining every adjacent Q label. -/
theorem xFlow_weight (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (w : Word BDL26Field (DoubleCylinderEdge P x S)) :
    HammingWeight (xFlow P S x w) =
      ∑ q : P.Q, if h : P.xq x q = true then
        HammingWeight (rxXQDegreeOne P A q x h S w) else 0 := by
  simp only [HammingWeight, hammingSupport, Finset.card_filter, Fintype.sum_sum_type,
    Fintype.sum_sigma, Fintype.sum_prod_type]
  simp only [xFlow_at_x, xFlow_at_z, ne_eq, not_true_eq_false, ite_false,
    Finset.sum_const_zero, zero_add, add_zero]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : P.xq x q = true
  · simp only [xFlow_at_q P A, dif_pos h]
  · simp only [xFlow_at_q P A, dif_neg h, Pi.zero_apply, ne_eq,
      not_true_eq_false, ite_false, Finset.sum_const_zero, add_zero]

/-- Count both actual copies of every Z label. -/
theorem qFlow_weight (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    HammingWeight (qFlow P S q w) = ∑ z : P.Z, HammingWeight (rxQOutgoing P q S w z) := by
  simp only [HammingWeight, hammingSupport, Finset.card_filter, Fintype.sum_sum_type,
    Fintype.sum_sigma, Fintype.sum_prod_type]
  simp only [qFlow_at_x, qFlow_at_q, qFlow_at_z, ne_eq, not_true_eq_false, ite_false,
    Finset.sum_const_zero, zero_add]

end QEC.Coding.BDL26RXDecoderAdapter
