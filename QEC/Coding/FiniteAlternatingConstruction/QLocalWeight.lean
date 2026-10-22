import QEC.Coding.FiniteAlternatingConstruction.RXLocalReplacement

/-!
# Q-local syndrome cleaning with an exact terminal-weight budget

The concrete Q cylinder consists of two subdivided stars joined at their
leaves.  Distinct leaves use disjoint arms and distinct vertical edges.
This module proves the local budget in BDL26, Lemma
`cleaning-syndrome-CQ`, without assuming a weight bound on a preimage.
-/

namespace QEC.Coding.BDL26RXLocalReplacement

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open scoped BigOperators

private def qBitWeight (a : Field) : Nat := if a = 0 then 0 else 1

private def qBitGap (a b : Field) : Nat := if a = b then 0 else 1

private theorem qBitGap_triangle (a b c : Field) :
    qBitGap a c ≤ qBitGap a b + qBitGap b c := by
  by_cases hab : a = b
  · subst b
    simp [qBitGap]
  · by_cases hbc : b = c
    · subst c
      simp [qBitGap]
    · unfold qBitGap
      split_ifs <;> omega

private theorem qBitGap_symm (a b : Field) : qBitGap a b = qBitGap b a := by
  simp [qBitGap, eq_comm]

private theorem qBitGap_zero (a : Field) : qBitGap 0 a = qBitWeight a := by
  simp [qBitGap, qBitWeight, eq_comm]

private theorem qBitGap_eq_weight_add (a b : Field) :
    qBitGap a b = qBitWeight (a + b) := by
  simp only [qBitGap, qBitWeight, CharTwo.add_eq_zero]

private theorem qBitWeight_complement (a : Field) :
    qBitWeight a + qBitWeight (a + 1) = 1 := by
  fin_cases a <;> decide

private theorem qHammingWeight_eq_sum {I : Type} [Fintype I]
    (f : Word Field I) : HammingWeight f = ∑ i : I, qBitWeight (f i) := by
  classical
  simp [HammingWeight, hammingSupport, Finset.card_filter, qBitWeight]

private theorem qBitGap_path (f : Nat → Field) (n : Nat) :
    qBitGap (f 0) (f n) ≤ ∑ i : Fin n, qBitGap (f i.val) (f (i.val + 1)) := by
  induction n with
  | zero => simp [qBitGap]
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      exact (qBitGap_triangle (f 0) (f n) (f (n + 1))).trans
        (Nat.add_le_add_right ih _)

/-- The actual Q-block coboundary evaluates as the sum of endpoint bits. -/
theorem qLocalCoboundary_apply (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (f : Word Field (QDoubleCylinderVertex P q S))
    (edge : QDoubleCylinderEdge P q S) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f edge =
      f (qDoubleCylinderEdgeStart P q S edge) +
        f (qDoubleCylinderEdgeEnd P q S edge) := by
  unfold qDoubleCylinderBoundary1
  exact wordLinearMapTranspose_graphBoundary_apply _ _ _ _

/-- A constant binary translation preserves the entire Q-local syndrome. -/
theorem qLocalCoboundary_add_constant (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (f : Word Field (QDoubleCylinderVertex P q S)) (a : Field) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) (fun v => f v + a) =
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f := by
  ext edge
  rw [qLocalCoboundary_apply, qLocalCoboundary_apply]
  change (f _ + a) + (f _ + a) = f _ + f _
  rw [add_add_add_comm, ZModModule.add_self, add_zero]

private def qArmValue (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (f : Word Field (QDoubleCylinderVertex P q S)) (copy : Two)
    (z : QStarEdge P q) (i : Nat) : Field :=
  if hi : i < S.half then
    f (copy, qSubdivisionEdgeStart P q S (z, ⟨i, hi⟩))
  else f (copy, Sum.inl (Sum.inr z))

private theorem qArmValue_zero (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (f : Word Field (QDoubleCylinderVertex P q S))
    (copy : Two) (z : QStarEdge P q) :
    qArmValue P q S f copy z 0 = f (copy, Sum.inl (Sum.inl ())) := by
  simp [qArmValue, S.half_pos, qSubdivisionEdgeStart, qStarEdgeStart]

private theorem qArmValue_last (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (f : Word Field (QDoubleCylinderVertex P q S))
    (copy : Two) (z : QStarEdge P q) :
    qArmValue P q S f copy z S.half = f (copy, Sum.inl (Sum.inr z)) := by
  simp [qArmValue]

private theorem qArmValue_step (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (f : Word Field (QDoubleCylinderVertex P q S))
    (copy : Two) (z : QStarEdge P q) (i : Fin S.half) :
    qArmValue P q S f copy z (i.val + 1) =
      f (copy, qSubdivisionEdgeEnd P q S (z, i)) := by
  by_cases hi : i.val + 1 < S.half
  · have hlast : i.val + 1 ≠ S.half := by omega
    have hzero : i.val + 1 ≠ 0 := by omega
    simp [qArmValue, hi, qSubdivisionEdgeStart, qSubdivisionEdgeEnd, hlast, hzero]
  · have hlast : i.val + 1 = S.half := by have := i.isLt; omega
    simp [qArmValue, hi, qSubdivisionEdgeEnd, hlast, qStarEdgeEnd]

private noncomputable def qArmWeight (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (f : Word Field (QDoubleCylinderVertex P q S))
    (copy : Two) (z : QStarEdge P q) : Nat :=
  ∑ i : Fin S.half, qBitWeight
    (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f (Sum.inl (copy, z, i)))

/-- Every differing pair of arm endpoints forces a syndrome on that arm. -/
private theorem qArmWeight_endpoint_le (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (f : Word Field (QDoubleCylinderVertex P q S))
    (copy : Two) (z : QStarEdge P q) :
    qBitGap (f (copy, Sum.inl (Sum.inl ()))) (f (copy, Sum.inl (Sum.inr z))) ≤
      qArmWeight P q S f copy z := by
  have h := qBitGap_path (qArmValue P q S f copy z) S.half
  rw [qArmValue_zero, qArmValue_last] at h
  calc
    _ ≤ ∑ i : Fin S.half,
        qBitGap (qArmValue P q S f copy z i.val)
          (qArmValue P q S f copy z (i.val + 1)) := h
    _ = qArmWeight P q S f copy z := by
      apply Finset.sum_congr rfl
      intro i _
      rw [qArmValue_step, qBitGap_eq_weight_add]
      simp [qArmValue, i.isLt, qLocalCoboundary_apply,
        qDoubleCylinderEdgeStart, qDoubleCylinderEdgeEnd]

private noncomputable def qLeafWeight (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (f : Word Field (QDoubleCylinderVertex P q S))
    (z : QStarEdge P q) : Nat :=
  qArmWeight P q S f 0 z + qArmWeight P q S f 1 z +
    qBitWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f (Sum.inr z))

private theorem qLeafWeight_sum (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (f : Word Field (QDoubleCylinderVertex P q S)) :
    (∑ z : QStarEdge P q, qLeafWeight P q S f z) =
      HammingWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f) := by
  classical
  rw [qHammingWeight_eq_sum]
  simp [qLeafWeight, qArmWeight,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two,
    Finset.sum_add_distrib]

private theorem qTerminalWeight_eq (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (f : Word Field (QDoubleCylinderVertex P q S))
    (z : QStarEdge P q) :
    HammingWeight (rxQZDegreeOne P q z.val z.property S f) =
      qBitWeight (f (0, Sum.inl (Sum.inr z))) +
        qBitWeight (f (1, Sum.inl (Sum.inr z))) := by
  rw [qHammingWeight_eq_sum]
  simp [rxQZDegreeOne, Fin.sum_univ_two]

/-- With both cone points zero, each terminal bit is paid for by its own arm. -/
theorem qLocal_terminal_weight_le_of_centers_zero
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (f : Word Field (QDoubleCylinderVertex P q S))
    (hzero : f (0, Sum.inl (Sum.inl ())) = 0)
    (hone : f (1, Sum.inl (Sum.inl ())) = 0) :
    (∑ z : QStarEdge P q, HammingWeight (rxQZDegreeOne P q z.val z.property S f)) ≤
      HammingWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f) := by
  rw [← qLeafWeight_sum]
  apply Finset.sum_le_sum
  intro z _
  have h0 := qArmWeight_endpoint_le P q S f 0 z
  have h1 := qArmWeight_endpoint_le P q S f 1 z
  rw [hzero, qBitGap_zero] at h0
  rw [hone, qBitGap_zero] at h1
  rw [qTerminalWeight_eq]
  unfold qLeafWeight
  omega

/-- Different cone-point bits force one syndrome per disjoint leaf path. -/
theorem qLocal_card_le_weight_of_centers_ne
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (f : Word Field (QDoubleCylinderVertex P q S))
    (hne : f (0, Sum.inl (Sum.inl ())) ≠ f (1, Sum.inl (Sum.inl ()))) :
    Fintype.card (QStarEdge P q) ≤
      HammingWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f) := by
  rw [← qLeafWeight_sum, Fintype.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro z _
  have h0 := qArmWeight_endpoint_le P q S f 0 z
  have h1 := qArmWeight_endpoint_le P q S f 1 z
  have hleft := qBitGap_triangle
    (f (0, Sum.inl (Sum.inl ()))) (f (0, Sum.inl (Sum.inr z)))
    (f (1, Sum.inl (Sum.inl ())))
  have hright := qBitGap_triangle
    (f (0, Sum.inl (Sum.inr z))) (f (1, Sum.inl (Sum.inr z)))
    (f (1, Sum.inl (Sum.inl ())))
  rw [qBitGap_symm (f (1, Sum.inl (Sum.inr z)))] at hright
  have hvert : qBitGap (f (0, Sum.inl (Sum.inr z))) (f (1, Sum.inl (Sum.inr z))) =
      qBitWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f (Sum.inr z)) := by
    rw [qLocalCoboundary_apply, qBitGap_eq_weight_add]
    rfl
  rw [hvert] at hright
  have hc : qBitGap (f (0, Sum.inl (Sum.inl ())))
      (f (1, Sum.inl (Sum.inl ()))) = 1 := by simp [qBitGap, hne]
  rw [hc] at hleft
  unfold qLeafWeight
  omega

/-- Complementary terminal words have total weight twice the leaf count. -/
theorem qLocal_terminal_weight_complement
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (f : Word Field (QDoubleCylinderVertex P q S)) :
    (∑ z : QStarEdge P q, HammingWeight (rxQZDegreeOne P q z.val z.property S f)) +
        (∑ z : QStarEdge P q, HammingWeight
          (rxQZDegreeOne P q z.val z.property S (fun v => f v + 1))) =
      2 * Fintype.card (QStarEdge P q) := by
  classical
  rw [← Finset.sum_add_distrib]
  simp_rw [qTerminalWeight_eq]
  have hterm : ∀ z : QStarEdge P q,
      (qBitWeight (f (0, Sum.inl (Sum.inr z))) + qBitWeight (f (1, Sum.inl (Sum.inr z)))) +
        (qBitWeight (f (0, Sum.inl (Sum.inr z)) + 1) +
          qBitWeight (f (1, Sum.inl (Sum.inr z)) + 1)) = 2 := by
    intro z
    have h0 := qBitWeight_complement (f (0, Sum.inl (Sum.inr z)))
    have h1 := qBitWeight_complement (f (1, Sum.inl (Sum.inr z)))
    omega
  simp_rw [hterm]
  simp [Nat.mul_comm]

/-- F12 Q-local correction: an actual coboundary preimage with terminal
connecting-map weight bounded by the input syndrome weight. -/
theorem rxCq_exists_local_weight_le
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (syndrome : Word Field (QDoubleCylinderEdge P q S))
    (hs : syndrome ∈ LinearMap.range (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S))) :
    ∃ f : Word Field (QDoubleCylinderVertex P q S),
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f = syndrome ∧
        (∑ z : QStarEdge P q, HammingWeight (rxQZDegreeOne P q z.val z.property S f)) ≤
          HammingWeight syndrome := by
  classical
  obtain ⟨h, rfl⟩ := hs
  by_cases hc : h (0, Sum.inl (Sum.inl ())) = h (1, Sum.inl (Sum.inl ()))
  · let f : Word Field (QDoubleCylinderVertex P q S) :=
      fun v => h v + h (0, Sum.inl (Sum.inl ()))
    have hf : wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f =
        wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) h :=
      qLocalCoboundary_add_constant P q S h _
    refine ⟨f, hf, ?_⟩
    rw [← hf]
    apply qLocal_terminal_weight_le_of_centers_zero P q S f
    · exact ZModModule.add_self _
    · change h (1, Sum.inl (Sum.inl ())) + h (0, Sum.inl (Sum.inl ())) = 0
      rw [← hc]
      exact ZModModule.add_self _
  · have hcard := qLocal_card_le_weight_of_centers_ne P q S h hc
    have hcomp := qLocal_terminal_weight_complement P q S h
    by_cases hsmall : (∑ z : QStarEdge P q,
        HammingWeight (rxQZDegreeOne P q z.val z.property S h)) ≤
          Fintype.card (QStarEdge P q)
    · exact ⟨h, rfl, hsmall.trans hcard⟩
    · refine ⟨fun v => h v + 1, qLocalCoboundary_add_constant P q S h 1, ?_⟩
      omega

end QEC.Coding.BDL26RXLocalReplacement
