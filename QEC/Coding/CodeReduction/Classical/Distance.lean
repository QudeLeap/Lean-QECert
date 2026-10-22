import QEC.Coding.CodeReduction.Classical.Collapse
import QEC.Coding.ChainComplex.HomotopyDistance

/-!
# Distance control for HHO20 classical weight reduction

This module proves the Hamming-Lipschitz estimates needed to transport
homological and cohomological distance through the explicit classical
weight-reduction homotopy equivalence.
-/

namespace QEC.Coding

open scoped BigOperators

universe u v w

theorem hammingSupport_smul_subset
    {F : Type u} [Field F]
    {ι : Type v} [Fintype ι] [DecidableEq F]
    (a : F) (x : Word F ι) :
    hammingSupport (a • x) ⊆ hammingSupport x := by
  intro i hi
  simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Pi.smul_apply, smul_eq_mul] at hi ⊢
  intro hxi
  exact hi (by simp [hxi])

theorem HammingWeight_smul_le
    {F : Type u} [Field F] [DecidableEq F]
    {ι : Type v} [Fintype ι]
    (a : F) (x : Word F ι) :
    HammingWeight (a • x) ≤ HammingWeight x := by
  exact Finset.card_le_card (hammingSupport_smul_subset a x)

theorem HammingWeight_finset_sum_le
    {F : Type u} [AddCommGroup F] [DecidableEq F]
    {ι : Type v} [Fintype ι]
    {κ : Type w} (s : Finset κ) (x : κ → Word F ι) :
    HammingWeight (∑ k ∈ s, x k) ≤ ∑ k ∈ s, HammingWeight (x k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk]
      exact (HammingWeight_add_le (x k) (∑ j ∈ s, x j)).trans
        (Nat.add_le_add_left ih _)

theorem word_eq_sum_hammingSupport_single
    {F : Type u} [Field F] [DecidableEq F]
    {ι : Type v} [Fintype ι] [DecidableEq ι] (x : Word F ι) :
    x = ∑ i ∈ hammingSupport x, Pi.single i (x i) := by
  classical
  ext j
  rw [Finset.sum_apply]
  by_cases hj : x j = 0
  · have hjnot : j ∉ hammingSupport x := by simp [hammingSupport, hj]
    rw [hj]
    simp [hjnot]
  · have hjmem : j ∈ hammingSupport x := by simp [hammingSupport, hj]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hij
      simp [Ne.symm hij]
    · exact fun h => (h hjmem).elim

/-- A linear map whose images of coordinate basis vectors have weight at
most `L` is `L`-Lipschitz for Hamming weight. -/
theorem HammingWeight_linearMap_le_of_basis
    {F : Type u} [Field F] [DecidableEq F]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {κ : Type w} [Fintype κ]
    (f : Word F ι →ₗ[F] Word F κ) (L : Nat)
    (hBasis : ∀ i : ι, HammingWeight (f (Pi.single i 1)) ≤ L)
    (x : Word F ι) :
    HammingWeight (f x) ≤ L * HammingWeight x := by
  classical
  have hx := word_eq_sum_hammingSupport_single x
  calc
    HammingWeight (f x) =
        HammingWeight (f (∑ i ∈ hammingSupport x,
          Pi.single i (x i))) := by rw [← hx]
    _ = HammingWeight (∑ i ∈ hammingSupport x,
          f (Pi.single i (x i))) := by rw [map_sum]
    _ ≤
        ∑ i ∈ hammingSupport x,
          HammingWeight (f (Pi.single i (x i))) :=
      HammingWeight_finset_sum_le _ _
    _ ≤ ∑ _i ∈ hammingSupport x, L := by
      apply Finset.sum_le_sum
      intro i hi
      have hsingle : (Pi.single i (x i) : Word F ι) =
          x i • Pi.single i (1 : F) := by
        ext j
        simp [Pi.single_apply]
      rw [hsingle, f.map_smul]
      exact (HammingWeight_smul_le _ _).trans (hBasis i)
    _ = L * HammingWeight x := by
      simp [HammingWeight, Nat.mul_comm]

namespace ClassicalWeightReduction

variable {F Check Bit : Type u} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]

omit [Fintype F] in
theorem classicalWeightReductionForward_map1_single_weight_le_one
    [CharP F 2] (h : HasNoIsolatedVertices R)
    (q : WeightReducedBit R) :
    HammingWeight
        ((classicalWeightReductionForwardChainMap (F₀ := F) R h).map1
          (Pi.single q 1)) ≤ 1 := by
  cases q with
  | inl e =>
      simp only [classicalWeightReductionForwardChainMap,
        combineForwardChainMap, collapseForwardChainMap,
        ThreeTermChainMap.comp_map1, LinearMap.comp_apply]
      rw [combineForwardMap1_single]
      change HammingWeight (collapseForwardMap1 (F := F) R
        (if bitPosition R e = bitRootPosition R h e.1.2 then
          Pi.single (Sum.inl e.1.2) 1 else 0)) ≤ 1
      by_cases hp : bitPosition R e = bitRootPosition R h e.1.2
      · rw [if_pos hp, collapseForwardMap1_single]
        exact HammingWeight_single_le_one (F := F) e.1.2
      · rw [if_neg hp, map_zero]
        simp
  | inr a =>
      simp only [classicalWeightReductionForwardChainMap,
        combineForwardChainMap, collapseForwardChainMap,
        ThreeTermChainMap.comp_map1, LinearMap.comp_apply]
      rw [combineForwardMap1_single]
      change HammingWeight (collapseForwardMap1 (F := F) R
        (Pi.single (Sum.inr a) 1)) ≤ 1
      rw [collapseForwardMap1_single]
      simp [collapseForwardMap1Basis]

omit [Fintype F] in
/-- The complete forward map of classical weight reduction does not increase
Hamming weight. -/
theorem classicalWeightReductionForward_map1_lipschitz
    [CharP F 2] (h : HasNoIsolatedVertices R)
    (x : Word F (WeightReducedBit R)) :
    HammingWeight
        ((classicalWeightReductionForwardChainMap (F₀ := F) R h).map1 x) ≤
      HammingWeight x := by
  simpa using HammingWeight_linearMap_le_of_basis
    (classicalWeightReductionForwardChainMap (F₀ := F) R h).map1 1
    (classicalWeightReductionForward_map1_single_weight_le_one
      (F := F) R h) x

omit [DecidableEq F] in
theorem transpose_combineInverseMap1_single
    (q : WeightReducedBit R) :
    wordLinearMapTranspose (combineInverseMap1 (F := F) R)
        (Pi.single q 1) =
      match q with
      | Sum.inl e => Pi.single (Sum.inl e.1.2) 1
      | Sum.inr a => Pi.single (Sum.inr a) 1 := by
  unfold combineInverseMap1
  rw [wordLinearMapTranspose_linearMapOfBasisImages_single]
  ext i
  cases q with
  | inl e =>
      cases i with
      | inl b =>
          simp only [combineInverseMap1Basis, allPrimaryBitCopies]
          by_cases heb : e.1.2 = b
          · subst b
            simp
          · have hbe : b ≠ e.1.2 := Ne.symm heb
            simp [heb, hbe]
      | inr a =>
          simp [combineInverseMap1Basis]
  | inr a =>
      cases i with
      | inl b =>
          simp [combineInverseMap1Basis, allPrimaryBitCopies]
      | inr a' =>
          simp only [combineInverseMap1Basis]
          by_cases haa : a = a'
          · subst a'
            simp
          · have haa' : a' ≠ a := Ne.symm haa
            simp [haa, haa']

omit [Fintype F] [DecidableEq F] in
theorem collapseHomotopy0_apply_original
    (x : Word F (BitSplitCheck R)) (b : Bit) :
    collapseHomotopy0 (F := F) R x (Sum.inl b) = 0 := by
  classical
  unfold collapseHomotopy0 linearMapOfBasisImages
  change (∑ e : BitSplitCheck R,
    x e • collapseHomotopy0Basis (F := F) R e) (Sum.inl b) = 0
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro e he
  simp [collapseHomotopy0Basis, checkPathAuxiliaryPrefix]

omit [DecidableEq F] in
theorem transpose_collapseInverseMap1_single_original (b : Bit) :
    wordLinearMapTranspose (collapseInverseMap1 (F := F) R)
        (Pi.single (Sum.inl b) 1) =
      Pi.single b 1 := by
  unfold collapseInverseMap1
  rw [wordLinearMapTranspose_linearMapOfBasisImages_single]
  ext b'
  simp only [collapseInverseMap1Basis, Pi.add_apply,
    collapseHomotopy0_apply_original, add_zero]
  by_cases hbb : b = b'
  · subst b'
    simp
  · have hbb' : b' ≠ b := Ne.symm hbb
    simp [hbb, hbb']

omit [Fintype F] [DecidableEq F] in
theorem collapseInverseMap1Basis_apply_auxiliary_of_not_rel
    (b : Bit) (a : AuxiliaryBit R) (hba : ¬R a.1 b) :
    collapseInverseMap1Basis (F := F) R b (Sum.inr a) = 0 := by
  classical
  unfold collapseInverseMap1Basis
  rw [Pi.add_apply]
  have hsingle :
      (Pi.single (Sum.inl b) 1 : Word F (BitSplitBit R)) (Sum.inr a) = 0 := by
    simp
  rw [hsingle, zero_add]
  unfold collapseHomotopy0 linearMapOfBasisImages
  change (∑ e : BitSplitCheck R,
    bitSplitPrimaryBoundary (F := F) R b e •
      collapseHomotopy0Basis (F := F) R e) (Sum.inr a) = 0
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro e he
  by_cases heb : e.1.2 = b
  · have hec : e.1.1 ≠ a.1 := by
      intro hec
      apply hba
      simpa [hec, heb] using e.2
    simp [bitSplitPrimaryBoundary, heb, collapseHomotopy0Basis,
      checkPathAuxiliaryPrefix, Ne.symm hec]
  · simp [bitSplitPrimaryBoundary, heb]

theorem transpose_collapseInverseMap1_single_auxiliary_weight_le
    (a : AuxiliaryBit R) (L : Nat)
    (hDegree : Fintype.card (CheckNeighbor R a.1) ≤ L) :
    HammingWeight
        (wordLinearMapTranspose (collapseInverseMap1 (F := F) R)
          (Pi.single (Sum.inr a) 1)) ≤ L := by
  classical
  unfold collapseInverseMap1
  rw [wordLinearMapTranspose_linearMapOfBasisImages_single]
  change HammingWeight
      (fun b : Bit => collapseInverseMap1Basis (F := F) R b (Sum.inr a)) ≤ L
  calc
    HammingWeight
          (fun b : Bit => collapseInverseMap1Basis (F := F) R b (Sum.inr a)) =
        (hammingSupport
          (fun b : Bit =>
            collapseInverseMap1Basis (F := F) R b (Sum.inr a))).card := rfl
    _ ≤ (Finset.univ.filter fun b : Bit => R a.1 b).card := by
      apply Finset.card_le_card
      intro b hb
      simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ,
        true_and] at hb ⊢
      by_contra hrel
      exact hb (collapseInverseMap1Basis_apply_auxiliary_of_not_rel
        (F := F) R b a hrel)
    _ = Fintype.card (CheckNeighbor R a.1) := by
      simp [CheckNeighbor, Fintype.card_subtype]
    _ ≤ L := hDegree

theorem classicalWeightReductionInverse_transpose_map1_single_weight_le
    [CharP F 2] (h : HasNoIsolatedVertices R) (L : Nat)
    (hDegree : ∀ c : Check, Fintype.card (CheckNeighbor R c) ≤ L)
    (q : WeightReducedBit R) :
    HammingWeight
        (wordLinearMapTranspose
          (classicalWeightReductionInverseChainMap (F₀ := F) R h).map1
          (Pi.single q 1)) ≤ L := by
  simp only [classicalWeightReductionInverseChainMap,
    combineInverseChainMap, collapseInverseChainMap,
    ThreeTermChainMap.comp_map1]
  rw [wordLinearMapTranspose_comp, LinearMap.comp_apply,
    transpose_combineInverseMap1_single]
  cases q with
  | inl e =>
      rw [transpose_collapseInverseMap1_single_original]
      exact (HammingWeight_single_le_one (F := F) e.1.2).trans (by
        have hpos := h.check_card_pos R e.1.1
        have hle := hDegree e.1.1
        omega)
  | inr a =>
      exact transpose_collapseInverseMap1_single_auxiliary_weight_le
        (F := F) R a L (hDegree a.1)

/-- If original check degree is at most `L`, the transpose of the complete
inverse map is `L`-Lipschitz. -/
theorem classicalWeightReductionInverse_transpose_map1_lipschitz
    [CharP F 2] (h : HasNoIsolatedVertices R) (L : Nat)
    (hDegree : ∀ c : Check, Fintype.card (CheckNeighbor R c) ≤ L)
    (x : Word F (WeightReducedBit R)) :
    HammingWeight
        (wordLinearMapTranspose
          (classicalWeightReductionInverseChainMap (F₀ := F) R h).map1 x) ≤
      L * HammingWeight x := by
  exact HammingWeight_linearMap_le_of_basis _ L
    (classicalWeightReductionInverse_transpose_map1_single_weight_le
      (F := F) R h L hDegree) x

omit [DecidableEq Check] [DecidableEq Bit] in
theorem hasNoIsolatedVertices_of_card_pos
    (hBit : ∀ b : Bit, 0 < Fintype.card (BitNeighbor R b))
    (hCheck : ∀ c : Check, 0 < Fintype.card (CheckNeighbor R c)) :
    HasNoIsolatedVertices R where
  bit_nonempty b := Fintype.card_pos_iff.mp (hBit b)
  check_nonempty c := Fintype.card_pos_iff.mp (hCheck c)

end ClassicalWeightReduction

end QEC.Coding
