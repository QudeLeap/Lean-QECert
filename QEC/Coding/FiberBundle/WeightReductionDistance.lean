import QEC.Coding.FiberBundle.WeightReduction
import QEC.Coding.ChainComplex.HomotopyDistance
import QEC.Coding.FiberBundle.ExplicitFamily.HomologyDimension

/-!
# Distance transport for HHO20 fiber-bundle weight reduction

This module derives the quantitative homology and cohomology consequences of
the explicit bundle chain-homotopy equivalence.  Lipschitz estimates are
proved from the concrete coordinate maps; no distance conclusion is accepted
as construction data.
-/

namespace QEC.Coding.FiberBundle

open scoped BigOperators

universe u

variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)

local notation "R" => baseSupportRelation D

/-- Weight reduction preserves the number of encoded logical qubits exactly. -/
theorem finrank_middleHomology_weightReduced_eq
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    Module.finrank (ZMod 2)
        (chainComplex (weightReducedData D)).middleHomology =
      Module.finrank (ZMod 2) (chainComplex D).middleHomology :=
  (weightReductionHomotopyEquiv D h).finrank_middleHomology_eq

/-- A proved forward Lipschitz bound converts an original-bundle homology
distance bound into the corresponding reduced-bundle bound. -/
theorem homologyDistanceAtLeast_weightReduced_of_forward_lipschitz
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    {d L : Nat}
    (hDistance : HomologyDistanceAtLeast D d)
    (hLipschitz : ∀ z,
      HammingWeight ((weightReductionForwardMap1 D h) z) ≤
        L * HammingWeight z) :
    HomologyDistanceAtLeast (weightReducedData D) (d / L) := by
  exact (weightReductionHomotopyEquiv D h
    ).middleHomologyDistanceAtLeast_of_forward_lipschitz
      hDistance hLipschitz

/-- A proved transpose-inverse Lipschitz bound converts an original-bundle
cohomology distance bound into the corresponding reduced-bundle bound. -/
theorem cohomologyDistanceAtLeast_weightReduced_of_inverse_lipschitz
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    {d L : Nat}
    (hDistance : CohomologyDistanceAtLeast D d)
    (hLipschitz : ∀ x,
      HammingWeight
          (wordLinearMapTranspose (weightReductionInverseMap1 D h) x) ≤
        L * HammingWeight x) :
    CohomologyDistanceAtLeast (weightReducedData D) (d / L) := by
  exact (weightReductionHomotopyEquiv D h
    ).middleCohomologyDistanceAtLeast_of_inverse_transpose_lipschitz
      hDistance hLipschitz

/-! ## Forward-map Lipschitz bound -/

/-- Tanner incidences are equivalently a bit together with an ordered
position in that bit's neighbor fiber. -/
noncomputable def incidenceBitPositionEquiv :
    ClassicalWeightReduction.Incidence R ≃
      ClassicalWeightReduction.BitPositionSigma R where
  toFun := ClassicalWeightReduction.incidenceBitPosition R
  invFun := ClassicalWeightReduction.incidenceAtBitPosition R
  left_inv :=
    ClassicalWeightReduction.incidenceAtBitPosition_incidenceBitPosition R
  right_inv := by
    rintro ⟨b, i⟩
    change ClassicalWeightReduction.incidenceBitPosition R
        (ClassicalWeightReduction.bitIncidenceAt R b i) = ⟨b, i⟩
    unfold ClassicalWeightReduction.incidenceBitPosition
    apply Sigma.ext (show
      (ClassicalWeightReduction.bitIncidenceAt R b i).1.2 = b by rfl)
    simp
    exact HEq.rfl

theorem sum_incidence_eq_sum_bit_positions
    {M : Type*} [AddCommMonoid M]
    (f : ClassicalWeightReduction.Incidence R → M) :
    (∑ e, f e) =
      ∑ b : baseOne,
        ∑ i : Fin (Fintype.card
          (ClassicalWeightReduction.BitNeighbor R b)),
          f (ClassicalWeightReduction.bitIncidenceAt R b i) := by
  calc
    (∑ e, f e) =
        ∑ s : ClassicalWeightReduction.BitPositionSigma R,
          f ((incidenceBitPositionEquiv D).symm s) := by
      exact (Equiv.sum_comp (incidenceBitPositionEquiv D).symm f).symm
    _ = _ := by
      rw [Fintype.sum_sigma]
      rfl

theorem weightReductionForwardMap1_vertical_auxiliary_expansion
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne)
    (k : Fin (Fintype.card
      (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (j : fiberOne) :
    weightReductionForwardMap1 D h
        (reducedQubitBasisWord D
          (Sum.inr
            (Sum.inr
              (⟨b, k⟩ : ClassicalWeightReduction.AuxiliaryCheck R), j))) =
      ∑ i : Fin (Fintype.card
          (ClassicalWeightReduction.BitNeighbor R b)),
        ClassicalWeightReduction.pathVertexSuffix (F := ZMod 2) k i •
          Pi.single
            (Sum.inr
              ((ClassicalWeightReduction.bitIncidenceAt R b i).1.1,
                (D.connection b
                  (ClassicalWeightReduction.bitIncidenceAt R b i).1.1
                  ).onOne j)) 1 := by
  classical
  rw [weightReductionForwardMap1_reducedQubitBasisWord_inr]
  ext target
  cases target with
  | inl bi =>
      simp [weightReductionForwardBaseZeroOneBasis, Pi.single_apply]
  | inr aj =>
      change weightReductionForwardBaseZeroOneBasis D
          (Sum.inr
            (⟨b, k⟩ : ClassicalWeightReduction.AuxiliaryCheck R)) j aj = _
      unfold weightReductionForwardBaseZeroOneBasis
        ClassicalWeightReduction.combineForwardMap0Basis
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [sum_incidence_eq_sum_bit_positions D]
      rw [Fintype.sum_eq_single b]
      · apply Fintype.sum_congr
        intro i
        rw [ClassicalWeightReduction.bitCheckSuffix_bitIncidenceAt]
        have hbit :
            (ClassicalWeightReduction.bitIncidenceAt R b i).1.2 = b := rfl
        rw [hbit]
        simp [Pi.single_apply]
      · intro b' hne
        apply Finset.sum_eq_zero
        intro i _hi
        have hbit :
            (ClassicalWeightReduction.bitIncidenceAt R b' i).1.2 = b' := rfl
        simp [ClassicalWeightReduction.bitCheckSuffix,
          ClassicalWeightReduction.incidenceBitPosition, hbit, hne]

theorem weightReductionForwardMap1_horizontal_basis_weight_le_one
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (q : ClassicalWeightReduction.WeightReducedBit R) (i : fiberZero) :
    HammingWeight
        (weightReductionForwardMap1 D h
          (reducedQubitBasisWord D (Sum.inl (q, i)))) ≤ 1 := by
  classical
  cases q with
  | inl e =>
      by_cases hroot : ClassicalWeightReduction.bitPosition R e =
          ClassicalWeightReduction.bitRootPosition R h e.1.2
      · have hmap :
            weightReductionForwardMap1 D h
                (reducedQubitBasisWord D (Sum.inl (Sum.inl e, i))) =
              Pi.single (Sum.inl (e.1.2, i)) 1 := by
          rw [weightReductionForwardMap1_reducedQubitBasisWord_inl]
          ext target
          cases target with
          | inl target' =>
              simp [weightReductionForwardBaseOneBasis, hroot,
                Pi.single_apply]
          | inr target' => simp [Pi.single_apply]
        rw [hmap]
        exact ClassicalWeightReduction.HammingWeight_single_le_one _
      · have hmap :
            weightReductionForwardMap1 D h
                (reducedQubitBasisWord D (Sum.inl (Sum.inl e, i))) = 0 := by
          rw [weightReductionForwardMap1_reducedQubitBasisWord_inl]
          ext target
          cases target <;>
            simp [weightReductionForwardBaseOneBasis, hroot]
        rw [hmap]
        simp
  | inr a =>
      have hmap :
          weightReductionForwardMap1 D h
              (reducedQubitBasisWord D (Sum.inl (Sum.inr a, i))) = 0 := by
        rw [weightReductionForwardMap1_reducedQubitBasisWord_inl]
        ext target
        cases target <;> simp [weightReductionForwardBaseOneBasis]
      rw [hmap]
      simp

theorem weightReductionForwardMap1_vertical_primary_weight_le_one
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (e : ClassicalWeightReduction.Incidence R) (j : fiberOne) :
    HammingWeight
        (weightReductionForwardMap1 D h
          (reducedQubitBasisWord D (Sum.inr (Sum.inl e, j)))) ≤ 1 := by
  classical
  have hmap :
      weightReductionForwardMap1 D h
          (reducedQubitBasisWord D (Sum.inr (Sum.inl e, j))) =
        Pi.single (Sum.inr (e.1.1, j)) 1 := by
    rw [weightReductionForwardMap1_reducedQubitBasisWord_inr]
    ext target
    cases target with
    | inl target' => simp [Pi.single_apply]
    | inr target' =>
        simp [weightReductionForwardBaseZeroOneBasis, Pi.single_apply]
  rw [hmap]
  exact ClassicalWeightReduction.HammingWeight_single_le_one _

theorem weightReductionForwardMap1_vertical_auxiliary_weight_le
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne)
    (k : Fin (Fintype.card
      (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (j : fiberOne) :
    HammingWeight
        (weightReductionForwardMap1 D h
          (reducedQubitBasisWord D
            (Sum.inr
              (Sum.inr
                (⟨b, k⟩ : ClassicalWeightReduction.AuxiliaryCheck R), j)))) ≤
      Fintype.card (ClassicalWeightReduction.BitNeighbor R b) := by
  classical
  rw [weightReductionForwardMap1_vertical_auxiliary_expansion D h]
  calc
    HammingWeight
        (∑ i : Fin (Fintype.card
            (ClassicalWeightReduction.BitNeighbor R b)),
          ClassicalWeightReduction.pathVertexSuffix (F := ZMod 2) k i •
            Pi.single
              (Sum.inr
                ((ClassicalWeightReduction.bitIncidenceAt R b i).1.1,
                  (D.connection b
                    (ClassicalWeightReduction.bitIncidenceAt R b i).1.1
                    ).onOne j)) 1) ≤
        ∑ _i : Fin (Fintype.card
            (ClassicalWeightReduction.BitNeighbor R b)), 1 := by
      refine (HammingWeight_finset_sum_le Finset.univ _).trans ?_
      apply Finset.sum_le_sum
      intro i _hi
      exact (HammingWeight_smul_le _ _).trans
        (ClassicalWeightReduction.HammingWeight_single_le_one _)
    _ = Fintype.card
        (ClassicalWeightReduction.BitNeighbor R b) := by simp

theorem weightReductionForwardMap1_basis_weight_le
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    {L : Nat} (hOne : 1 ≤ L)
    (hBitDegree : ∀ b : baseOne,
      Fintype.card (ClassicalWeightReduction.BitNeighbor R b) ≤ L)
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne) :
    HammingWeight
        (weightReductionForwardMap1 D h (reducedQubitBasisWord D q)) ≤ L := by
  cases q with
  | inl qi =>
      exact (weightReductionForwardMap1_horizontal_basis_weight_le_one
        D h qi.1 qi.2).trans hOne
  | inr qj =>
      rcases qj with ⟨q, j⟩
      cases q with
      | inl e =>
          exact (weightReductionForwardMap1_vertical_primary_weight_le_one
            D h e j).trans hOne
      | inr a =>
          rcases a with ⟨b, k⟩
          exact (weightReductionForwardMap1_vertical_auxiliary_weight_le
            D h b k j).trans (hBitDegree b)

/-- The concrete HHO20 bundle forward map loses at most the maximum original
bit degree in Hamming weight. -/
theorem weightReductionForwardMap1_lipschitz
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    {L : Nat} (hOne : 1 ≤ L)
    (hBitDegree : ∀ b : baseOne,
      Fintype.card (ClassicalWeightReduction.BitNeighbor R b) ≤ L)
    (x : Word (ZMod 2)
      (QubitIndex
        (ClassicalWeightReduction.WeightReducedCheck R)
        (ClassicalWeightReduction.WeightReducedBit R)
        fiberZero fiberOne)) :
    HammingWeight (weightReductionForwardMap1 D h x) ≤
      L * HammingWeight x := by
  classical
  apply HammingWeight_linearMap_le_of_basis
  intro q
  change HammingWeight
      (weightReductionForwardMap1 D h (reducedQubitBasisWord D q)) ≤ L
  exact weightReductionForwardMap1_basis_weight_le
    D h hOne hBitDegree q

/-- HHO20 weight reduction transports homological distance with only the
explicit maximum-bit-degree loss. -/
theorem homologyDistanceAtLeast_weightReduced
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    {d L : Nat} (hOne : 1 ≤ L)
    (hBitDegree : ∀ b : baseOne,
      Fintype.card (ClassicalWeightReduction.BitNeighbor R b) ≤ L)
    (hDistance : HomologyDistanceAtLeast D d) :
    HomologyDistanceAtLeast (weightReducedData D) (d / L) := by
  exact homologyDistanceAtLeast_weightReduced_of_forward_lipschitz
    D h hDistance (weightReductionForwardMap1_lipschitz
      D h hOne hBitDegree)

/-! ## Transpose-inverse Lipschitz bound -/

theorem inverseAuxiliaryCoefficient_eq_zero_of_not_rel
    (b : baseOne) (a : ClassicalWeightReduction.AuxiliaryBit R)
    (hba : ¬R a.1 b) :
    inverseAuxiliaryCoefficient D b a = 0 := by
  classical
  unfold inverseAuxiliaryCoefficient
    ClassicalWeightReduction.collapseHomotopy0
    ClassicalWeightReduction.linearMapOfBasisImages
  change (∑ e : ClassicalWeightReduction.BitSplitCheck R,
    ClassicalWeightReduction.bitSplitPrimaryBoundary
        (F := ZMod 2) R b e •
      ClassicalWeightReduction.collapseHomotopy0Basis
        (F := ZMod 2) R e) (Sum.inr a) = 0
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro e _he
  by_cases heb : e.1.2 = b
  · have hec : e.1.1 ≠ a.1 := by
      intro hec
      apply hba
      simpa [hec, heb] using e.2
    simp [ClassicalWeightReduction.bitSplitPrimaryBoundary, heb,
      ClassicalWeightReduction.collapseHomotopy0Basis,
      ClassicalWeightReduction.checkPathAuxiliaryPrefix, Ne.symm hec]
  · simp [ClassicalWeightReduction.bitSplitPrimaryBoundary, heb]

theorem weightReductionInverseMap1_transpose_reducedQubitBasisWord
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne) :
    wordLinearMapTranspose (weightReductionInverseMap1 D h)
        (reducedQubitBasisWord D q) =
      fun source : QubitIndex baseZero baseOne fiberZero fiberOne =>
        match source, q with
        | Sum.inl bi, Sum.inl target' =>
            weightReductionInverseBaseOneBasis D bi.1 bi.2 target'
        | Sum.inr aj, Sum.inr target' =>
            weightReductionInverseBaseZeroOneBasis D h aj.1 aj.2 target'
        | _, _ => 0 := by
  classical
  unfold reducedQubitBasisWord weightReductionInverseMap1
  rw [ClassicalWeightReduction.wordLinearMapTranspose_linearMapOfBasisImages_single]
  rfl

theorem weightReductionInverseMap1_transpose_horizontal_auxiliary_expansion
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (a : ClassicalWeightReduction.AuxiliaryBit R) (k : fiberZero) :
    wordLinearMapTranspose (weightReductionInverseMap1 D h)
        (reducedQubitBasisWord D (Sum.inl (Sum.inr a, k))) =
      ∑ nb : ClassicalWeightReduction.CheckNeighbor R a.1,
        inverseAuxiliaryCoefficient D nb.1 a •
          Pi.single
            (Sum.inl
              (nb.1, (D.connection nb.1 a.1).onZero.symm k)) 1 := by
  classical
  rw [weightReductionInverseMap1_transpose_reducedQubitBasisWord]
  ext source
  cases source with
  | inl bi =>
      change weightReductionInverseBaseOneBasis D bi.1 bi.2
          (Sum.inr a, k) = _
      rw [weightReductionInverseBaseOneBasis_apply_auxiliary]
      rw [Finset.sum_apply]
      by_cases hrel : R a.1 bi.1
      · let nb : ClassicalWeightReduction.CheckNeighbor R a.1 :=
          ⟨bi.1, hrel⟩
        rw [Fintype.sum_eq_single nb]
        · simp only [nb, Pi.smul_apply, smul_eq_mul]
          by_cases hk : k = (D.connection bi.1 a.1).onZero bi.2
          · rw [if_pos hk]
            have hi : (D.connection bi.1 a.1).onZero.symm k = bi.2 := by
              simpa [hk]
            have hcoord :
                (Sum.inl
                  (bi.1, (D.connection bi.1 a.1).onZero.symm k) :
                    QubitIndex baseZero baseOne fiberZero fiberOne) =
                  Sum.inl bi := by simp [hi]
            rw [hcoord, Pi.single_eq_same, mul_one]
          · rw [if_neg hk]
            have hcoord :
                (Sum.inl
                  (bi.1, (D.connection bi.1 a.1).onZero.symm k) :
                    QubitIndex baseZero baseOne fiberZero fiberOne) ≠
                  Sum.inl bi := by
              intro heq
              apply hk
              have hi := congrArg Prod.snd (Sum.inl.inj heq)
              rw [← hi]
              simp
            rw [Pi.single_eq_of_ne (Ne.symm hcoord), mul_zero]
        · intro nb' hne
          have hbit : nb'.1 ≠ bi.1 := by
            intro heq
            apply hne
            exact Subtype.ext heq
          have hcoord :
              (Sum.inl
                (nb'.1, (D.connection nb'.1 a.1).onZero.symm k) :
                  QubitIndex baseZero baseOne fiberZero fiberOne) ≠
                Sum.inl bi := by
            intro heq
            apply hbit
            exact congrArg Prod.fst (Sum.inl.inj heq)
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [Pi.single_eq_of_ne (Ne.symm hcoord), mul_zero]
      · rw [show inverseAuxiliaryCoefficient D bi.1 a = 0 from
          inverseAuxiliaryCoefficient_eq_zero_of_not_rel D bi.1 a hrel]
        simp only [ite_self, Pi.smul_apply, smul_eq_mul]
        symm
        apply Finset.sum_eq_zero
        intro nb _hnb
        have hbit : nb.1 ≠ bi.1 := by
          intro heq
          apply hrel
          simpa [heq] using nb.2
        have hcoord :
            (Sum.inl
              (nb.1, (D.connection nb.1 a.1).onZero.symm k) :
                QubitIndex baseZero baseOne fiberZero fiberOne) ≠
              Sum.inl bi := by
          intro heq
          apply hbit
          exact congrArg Prod.fst (Sum.inl.inj heq)
        rw [Pi.single_eq_of_ne (Ne.symm hcoord), mul_zero]
  | inr aj =>
      simp [Pi.single_apply]

theorem weightReductionInverseMap1_transpose_horizontal_primary_weight_le_one
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (e : ClassicalWeightReduction.Incidence R) (k : fiberZero) :
    HammingWeight
        (wordLinearMapTranspose (weightReductionInverseMap1 D h)
          (reducedQubitBasisWord D (Sum.inl (Sum.inl e, k)))) ≤ 1 := by
  classical
  have hmap :
      wordLinearMapTranspose (weightReductionInverseMap1 D h)
          (reducedQubitBasisWord D (Sum.inl (Sum.inl e, k))) =
        Pi.single (Sum.inl (e.1.2, k)) 1 := by
    rw [weightReductionInverseMap1_transpose_reducedQubitBasisWord]
    ext source
    cases source with
    | inl bi =>
        simp only [weightReductionInverseBaseOneBasis_apply_primary,
          Pi.single_apply, Sum.inl.injEq]
        congr 1
        simp [Prod.ext_iff, eq_comm]
    | inr aj => simp [Pi.single_apply]
  rw [hmap]
  exact ClassicalWeightReduction.HammingWeight_single_le_one _

theorem weightReductionInverseMap1_transpose_horizontal_auxiliary_weight_le
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (a : ClassicalWeightReduction.AuxiliaryBit R) (k : fiberZero) :
    HammingWeight
        (wordLinearMapTranspose (weightReductionInverseMap1 D h)
          (reducedQubitBasisWord D (Sum.inl (Sum.inr a, k)))) ≤
      Fintype.card (ClassicalWeightReduction.CheckNeighbor R a.1) := by
  classical
  rw [weightReductionInverseMap1_transpose_horizontal_auxiliary_expansion]
  calc
    HammingWeight
        (∑ nb : ClassicalWeightReduction.CheckNeighbor R a.1,
          inverseAuxiliaryCoefficient D nb.1 a •
            Pi.single
              (Sum.inl
                (nb.1, (D.connection nb.1 a.1).onZero.symm k)) 1) ≤
        ∑ _nb : ClassicalWeightReduction.CheckNeighbor R a.1, 1 := by
      refine (HammingWeight_finset_sum_le Finset.univ _).trans ?_
      apply Finset.sum_le_sum
      intro nb _hnb
      exact (HammingWeight_smul_le _ _).trans
        (ClassicalWeightReduction.HammingWeight_single_le_one _)
    _ = Fintype.card
        (ClassicalWeightReduction.CheckNeighbor R a.1) := by simp

theorem weightReductionInverseMap1_transpose_vertical_primary_weight_le_one
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (e : ClassicalWeightReduction.Incidence R) (k : fiberOne) :
    HammingWeight
        (wordLinearMapTranspose (weightReductionInverseMap1 D h)
          (reducedQubitBasisWord D (Sum.inr (Sum.inl e, k)))) ≤ 1 := by
  classical
  let x := wordLinearMapTranspose (weightReductionInverseMap1 D h)
    (reducedQubitBasisWord D (Sum.inr (Sum.inl e, k)))
  calc
    HammingWeight x = (hammingSupport x).card := rfl
    _ ≤ ({Sum.inr (e.1.1, k)} :
        Finset (QubitIndex baseZero baseOne fiberZero fiberOne)).card := by
      apply Finset.card_le_card
      intro source hs
      simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ,
        true_and] at hs
      have hx := weightReductionInverseMap1_transpose_reducedQubitBasisWord
        D h (Sum.inr (Sum.inl e, k))
      dsimp [x] at hs
      rw [hx] at hs
      cases source with
      | inl bi => simp at hs
      | inr aj =>
          change weightReductionInverseBaseZeroOneBasis D h aj.1 aj.2
              (Sum.inl e, k) ≠ 0 at hs
          unfold weightReductionInverseBaseZeroOneBasis at hs
          by_cases hcoord :
              ((Sum.inl
                  (ClassicalWeightReduction.checkIncidenceAt R aj.1
                    (ClassicalWeightReduction.checkRootPosition R h aj.1)) :
                    ClassicalWeightReduction.WeightReducedCheck R), aj.2) =
                ((Sum.inl e :
                    ClassicalWeightReduction.WeightReducedCheck R), k)
          · have heinc :
                ClassicalWeightReduction.checkIncidenceAt R aj.1
                    (ClassicalWeightReduction.checkRootPosition R h aj.1) = e :=
              Sum.inl.inj (congrArg Prod.fst hcoord)
            have hc : aj.1 = e.1.1 := by
              exact congrArg (fun z => z.1.1) heinc
            have hk : aj.2 = k := congrArg Prod.snd hcoord
            simp only [Finset.mem_singleton]
            have haj : aj = (e.1.1, k) := Prod.ext hc hk
            exact congrArg (fun p : baseZero × fiberOne =>
              (Sum.inr p : QubitIndex baseZero baseOne fiberZero fiberOne)) haj
          · rw [Pi.single_eq_of_ne (Ne.symm hcoord)] at hs
            exact (hs rfl).elim
    _ = 1 := Finset.card_singleton _

theorem weightReductionInverseMap1_transpose_vertical_auxiliary_weight_eq_zero
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (a : ClassicalWeightReduction.AuxiliaryCheck R) (k : fiberOne) :
    HammingWeight
        (wordLinearMapTranspose (weightReductionInverseMap1 D h)
          (reducedQubitBasisWord D (Sum.inr (Sum.inr a, k)))) = 0 := by
  classical
  have hmap :
      wordLinearMapTranspose (weightReductionInverseMap1 D h)
          (reducedQubitBasisWord D (Sum.inr (Sum.inr a, k))) = 0 := by
    rw [weightReductionInverseMap1_transpose_reducedQubitBasisWord]
    ext source
    cases source with
    | inl bi => simp
    | inr aj =>
        simp [weightReductionInverseBaseZeroOneBasis, Pi.single_apply]
  rw [hmap]
  simp

theorem weightReductionInverseMap1_transpose_basis_weight_le
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    {L : Nat} (hOne : 1 ≤ L)
    (hCheckDegree : ∀ c : baseZero,
      Fintype.card (ClassicalWeightReduction.CheckNeighbor R c) ≤ L)
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne) :
    HammingWeight
        (wordLinearMapTranspose (weightReductionInverseMap1 D h)
          (reducedQubitBasisWord D q)) ≤ L := by
  cases q with
  | inl qi =>
      rcases qi with ⟨q, k⟩
      cases q with
      | inl e =>
          exact
            (weightReductionInverseMap1_transpose_horizontal_primary_weight_le_one
              D h e k).trans hOne
      | inr a =>
          exact
            (weightReductionInverseMap1_transpose_horizontal_auxiliary_weight_le
              D h a k).trans (hCheckDegree a.1)
  | inr qj =>
      rcases qj with ⟨q, k⟩
      cases q with
      | inl e =>
          exact
            (weightReductionInverseMap1_transpose_vertical_primary_weight_le_one
              D h e k).trans hOne
      | inr a =>
          rw [weightReductionInverseMap1_transpose_vertical_auxiliary_weight_eq_zero]
          omega

/-- The transpose of the concrete HHO20 bundle inverse loses at most the
maximum original check degree in Hamming weight. -/
theorem weightReductionInverseMap1_transpose_lipschitz
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    {L : Nat} (hOne : 1 ≤ L)
    (hCheckDegree : ∀ c : baseZero,
      Fintype.card (ClassicalWeightReduction.CheckNeighbor R c) ≤ L)
    (x : Word (ZMod 2)
      (QubitIndex
        (ClassicalWeightReduction.WeightReducedCheck R)
        (ClassicalWeightReduction.WeightReducedBit R)
        fiberZero fiberOne)) :
    HammingWeight
        (wordLinearMapTranspose (weightReductionInverseMap1 D h) x) ≤
      L * HammingWeight x := by
  classical
  apply HammingWeight_linearMap_le_of_basis
  intro q
  change HammingWeight
      (wordLinearMapTranspose (weightReductionInverseMap1 D h)
        (reducedQubitBasisWord D q)) ≤ L
  exact weightReductionInverseMap1_transpose_basis_weight_le
    D h hOne hCheckDegree q

/-- HHO20 weight reduction transports cohomological distance with only the
explicit maximum-check-degree loss. -/
theorem cohomologyDistanceAtLeast_weightReduced
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    {d L : Nat} (hOne : 1 ≤ L)
    (hCheckDegree : ∀ c : baseZero,
      Fintype.card (ClassicalWeightReduction.CheckNeighbor R c) ≤ L)
    (hDistance : CohomologyDistanceAtLeast D d) :
    CohomologyDistanceAtLeast (weightReducedData D) (d / L) := by
  exact cohomologyDistanceAtLeast_weightReduced_of_inverse_lipschitz
    D h hDistance (weightReductionInverseMap1_transpose_lipschitz
      D h hOne hCheckDegree)

namespace RandomBase

/-- A fully-good HHO20 sample instantiates the homological weight-reduction
bound with the construction's explicit degree window. -/
theorem homologyDistanceAtLeast_weightReduced_randomFiberBundleData
    {r typeCount ell Delta d : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) baseSample)
    (hDistance : HomologyDistanceAtLeast
      (RandomTwist.fiberBundleData baseSample twistSample) d) :
    HomologyDistanceAtLeast
      (weightReducedData
        (RandomTwist.fiberBundleData baseSample twistSample))
      (d / (101 * Delta)) := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  apply homologyDistanceAtLeast_weightReduced D
    (baseSupport_hasNoIsolatedVertices_of_isFullyGood
      baseSample twistSample hDelta hGood)
  · omega
  · intro b
    have hp :
        (fun c => baseSupportRelation D c b) =
          fun c => incidenceRelation baseSample c b := by
      funext c
      exact propext
        (baseSupportRelation_randomFiberBundleData_iff
          baseSample twistSample c b)
    rw [Fintype.card_congr (Equiv.subtypeEquivProp hp)]
    exact bitNeighbor_card_le_of_degreeWindows
      baseSample hGood.1.1 b
  · exact hDistance

/-- The same fully-good HHO20 sample instantiates the cohomological
weight-reduction bound with no caller-supplied locality premise. -/
theorem cohomologyDistanceAtLeast_weightReduced_randomFiberBundleData
    {r typeCount ell Delta d : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) baseSample)
    (hDistance : CohomologyDistanceAtLeast
      (RandomTwist.fiberBundleData baseSample twistSample) d) :
    CohomologyDistanceAtLeast
      (weightReducedData
        (RandomTwist.fiberBundleData baseSample twistSample))
      (d / (101 * Delta)) := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  apply cohomologyDistanceAtLeast_weightReduced D
    (baseSupport_hasNoIsolatedVertices_of_isFullyGood
      baseSample twistSample hDelta hGood)
  · omega
  · intro c
    have hp :
        (fun b => baseSupportRelation D c b) =
          fun b => incidenceRelation baseSample c b := by
      funext b
      exact propext
        (baseSupportRelation_randomFiberBundleData_iff
          baseSample twistSample c b)
    rw [Fintype.card_congr (Equiv.subtypeEquivProp hp)]
    exact checkNeighbor_card_le_of_degreeWindows
      baseSample hGood.1.1 c
  · exact hDistance

/-- Weight reduction retains the initial HHO20 logical-dimension lower
bound, rather than merely preserving a caller-provided abstract rank. -/
theorem r_le_finrank_middleHomology_weightReduced_randomFiberBundleData
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) baseSample) :
    r ≤ Module.finrank (ZMod 2)
      (chainComplex
        (weightReducedData
          (RandomTwist.fiberBundleData baseSample twistSample))
        ).middleHomology := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  calc
    r ≤ Module.finrank (ZMod 2) (chainComplex D).middleHomology :=
      r_le_finrank_middleHomology baseSample twistSample hGood.1.2.1
    _ = Module.finrank (ZMod 2)
        (chainComplex (weightReducedData D)).middleHomology :=
      (finrank_middleHomology_weightReduced_eq D
        (baseSupport_hasNoIsolatedVertices_of_isFullyGood
          baseSample twistSample hDelta hGood)).symm

end RandomBase

end QEC.Coding.FiberBundle
