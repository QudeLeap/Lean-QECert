import QEC.Coding.ExpanderCodes.ProductExpansionProbability

/-!
# Simultaneous two-orientation PK22 local-code probability

PK22 applies its random local-code lemma twice to the same pair of matrices.
This module performs the finite union bound directly: it excludes kernel- and
row-image-distance failures for both matrices, together with sparse rectangle
witnesses in both product-expansion orientations.
-/

namespace QEC.Coding.ProductExpansion

universe u v

variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']

/-- A candidate ordered pair of PK22 local matrices. -/
abbrev LocalMatrixPair := Matrix R W F × Matrix R' W F

/-- First-matrix kernel-distance failure. -/
def badFirstKernelPairs (d : Nat) :=
  {p : LocalMatrixPair (F := F) (W := W) (R := R) (R' := R') //
    ∃ c : Word F W,
      c ≠ 0 ∧ HammingWeight c < d ∧ p.1.mulVec c = 0}

/-- First-matrix row-image-distance failure. -/
def badFirstImagePairs (d : Nat) :=
  {p : LocalMatrixPair (F := F) (W := W) (R := R) (R' := R') //
    ∃ a : Word F R,
      a ≠ 0 ∧ HammingWeight (p.1.transpose.mulVec a) < d}

/-- Second-matrix kernel-distance failure. -/
def badSecondKernelPairs (d : Nat) :=
  {p : LocalMatrixPair (F := F) (W := W) (R := R) (R' := R') //
    ∃ c : Word F W,
      c ≠ 0 ∧ HammingWeight c < d ∧ p.2.mulVec c = 0}

/-- Second-matrix row-image-distance failure. -/
def badSecondImagePairs (d : Nat) :=
  {p : LocalMatrixPair (F := F) (W := W) (R := R) (R' := R') //
    ∃ a : Word F R',
      a ≠ 0 ∧ HammingWeight (p.2.transpose.mulVec a) < d}

/-- Sparse product-kernel rectangle in the orientation
`(ker h, im g'ᵀ)`. -/
def badForwardRectanglePairs (s m k : Nat) :=
  {p : LocalMatrixPair (F := F) (W := W) (R := R) (R' := R') //
    ∃ A B : Finset W,
      A.card = Fintype.card W - m ∧
      B.card = Fintype.card W - m ∧
      ∃ x : Matrix W W F,
        restrictedWeight x A B < s ∧
        k ≤ (generatorImageParityCheck p.2 * x).rank ∧
        ProductKernel p.1 (generatorImageParityCheck p.2) x}

/-- Sparse product-kernel rectangle in the reverse orientation
`(ker g', im hᵀ)`. -/
def badReverseRectanglePairs (s m k : Nat) :=
  {p : LocalMatrixPair (F := F) (W := W) (R := R) (R' := R') //
    ∃ A B : Finset W,
      A.card = Fintype.card W - m ∧
      B.card = Fintype.card W - m ∧
      ∃ x : Matrix W W F,
        restrictedWeight x A B < s ∧
        k ≤ (generatorImageParityCheck p.1 * x).rank ∧
        ProductKernel p.2 (generatorImageParityCheck p.1) x}

noncomputable instance badFirstKernelPairsFintype (d : Nat) :
    Fintype (badFirstKernelPairs (F := F) (W := W) (R := R) (R' := R') d) := by
  classical
  unfold badFirstKernelPairs LocalMatrixPair
  infer_instance

noncomputable instance badFirstImagePairsFintype (d : Nat) :
    Fintype (badFirstImagePairs (F := F) (W := W) (R := R) (R' := R') d) := by
  classical
  unfold badFirstImagePairs LocalMatrixPair
  infer_instance

noncomputable instance badSecondKernelPairsFintype (d : Nat) :
    Fintype (badSecondKernelPairs (F := F) (W := W) (R := R) (R' := R') d) := by
  classical
  unfold badSecondKernelPairs LocalMatrixPair
  infer_instance

noncomputable instance badSecondImagePairsFintype (d : Nat) :
    Fintype (badSecondImagePairs (F := F) (W := W) (R := R) (R' := R') d) := by
  classical
  unfold badSecondImagePairs LocalMatrixPair
  infer_instance

noncomputable instance badForwardRectanglePairsFintype (s m k : Nat) :
    Fintype (badForwardRectanglePairs
      (F := F) (W := W) (R := R) (R' := R') s m k) := by
  classical
  unfold badForwardRectanglePairs LocalMatrixPair
  infer_instance

noncomputable instance badReverseRectanglePairsFintype (s m k : Nat) :
    Fintype (badReverseRectanglePairs
      (F := F) (W := W) (R := R) (R' := R') s m k) := by
  classical
  unfold badReverseRectanglePairs LocalMatrixPair
  infer_instance

/-- Forget a first-kernel-bad pair into its bad first matrix and arbitrary
second matrix. -/
def badFirstKernelPairsEncoding (d : Nat) :
    badFirstKernelPairs (F := F) (W := W) (R := R) (R' := R') d →
      badChecksForDistance (F := F) (W := W) (R := R) d × Matrix R' W F :=
  fun p => (⟨p.1.1, p.2⟩, p.1.2)

omit [Fintype F] [DecidableEq W] hRFinite hR'Finite in
theorem badFirstKernelPairsEncoding_injective (d : Nat) :
    Function.Injective
      (badFirstKernelPairsEncoding
        (F := F) (W := W) (R := R) (R' := R') d) := by
  intro p q hpq
  apply Subtype.ext
  exact Prod.ext
    (congrArg (fun z => z.1.1) hpq)
    (congrArg (fun z => z.2) hpq)

/-- Forget a first-image-bad pair into its bad first matrix and arbitrary
second matrix. -/
def badFirstImagePairsEncoding (d : Nat) :
    badFirstImagePairs (F := F) (W := W) (R := R) (R' := R') d →
      badGeneratorsForDistance (F := F) (W := W) (R := R) d × Matrix R' W F :=
  fun p => (⟨p.1.1, p.2⟩, p.1.2)

omit [Fintype F] [DecidableEq W] hR'Finite in
theorem badFirstImagePairsEncoding_injective (d : Nat) :
    Function.Injective
      (badFirstImagePairsEncoding
        (F := F) (W := W) (R := R) (R' := R') d) := by
  intro p q hpq
  apply Subtype.ext
  exact Prod.ext
    (congrArg (fun z => z.1.1) hpq)
    (congrArg (fun z => z.2) hpq)

/-- Forget a second-kernel-bad pair into an arbitrary first matrix and its
bad second matrix. -/
def badSecondKernelPairsEncoding (d : Nat) :
    badSecondKernelPairs (F := F) (W := W) (R := R) (R' := R') d →
      Matrix R W F × badChecksForDistance (F := F) (W := W) (R := R') d :=
  fun p => (p.1.1, ⟨p.1.2, p.2⟩)

omit [Fintype F] [DecidableEq W] hRFinite hR'Finite in
theorem badSecondKernelPairsEncoding_injective (d : Nat) :
    Function.Injective
      (badSecondKernelPairsEncoding
        (F := F) (W := W) (R := R) (R' := R') d) := by
  intro p q hpq
  apply Subtype.ext
  exact Prod.ext
    (congrArg (fun z => z.1) hpq)
    (congrArg (fun z => z.2.1) hpq)

/-- Forget a second-image-bad pair into an arbitrary first matrix and its
bad second matrix. -/
def badSecondImagePairsEncoding (d : Nat) :
    badSecondImagePairs (F := F) (W := W) (R := R) (R' := R') d →
      Matrix R W F × badGeneratorsForDistance (F := F) (W := W) (R := R') d :=
  fun p => (p.1.1, ⟨p.1.2, p.2⟩)

omit [Fintype F] [DecidableEq W] hRFinite in
theorem badSecondImagePairsEncoding_injective (d : Nat) :
    Function.Injective
      (badSecondImagePairsEncoding
        (F := F) (W := W) (R := R) (R' := R') d) := by
  intro p q hpq
  apply Subtype.ext
  exact Prod.ext
    (congrArg (fun z => z.1) hpq)
    (congrArg (fun z => z.2.1) hpq)

omit [DecidableEq W] in
/-- Cardinal bound for first-kernel-bad pairs. -/
theorem card_badFirstKernelPairs_le (d : Nat) :
    Nat.card (badFirstKernelPairs
      (F := F) (W := W) (R := R) (R' := R') d) ≤
      Nat.card (badChecksForDistance (F := F) (W := W) (R := R) d) *
        Nat.card (Matrix R' W F) := by
  calc
    Nat.card (badFirstKernelPairs
        (F := F) (W := W) (R := R) (R' := R') d) ≤
        Nat.card
          (badChecksForDistance (F := F) (W := W) (R := R) d ×
            Matrix R' W F) :=
      Nat.card_le_card_of_injective
        (badFirstKernelPairsEncoding
          (F := F) (W := W) (R := R) (R' := R') d)
        (badFirstKernelPairsEncoding_injective
          (F := F) (W := W) (R := R) (R' := R') d)
    _ = _ := by rw [Nat.card_prod]

omit [DecidableEq W] in
/-- Cardinal bound for first-image-bad pairs. -/
theorem card_badFirstImagePairs_le (d : Nat) :
    Nat.card (badFirstImagePairs
      (F := F) (W := W) (R := R) (R' := R') d) ≤
      Nat.card (badGeneratorsForDistance (F := F) (W := W) (R := R) d) *
        Nat.card (Matrix R' W F) := by
  calc
    Nat.card (badFirstImagePairs
        (F := F) (W := W) (R := R) (R' := R') d) ≤
        Nat.card
          (badGeneratorsForDistance (F := F) (W := W) (R := R) d ×
            Matrix R' W F) :=
      Nat.card_le_card_of_injective
        (badFirstImagePairsEncoding
          (F := F) (W := W) (R := R) (R' := R') d)
        (badFirstImagePairsEncoding_injective
          (F := F) (W := W) (R := R) (R' := R') d)
    _ = _ := by rw [Nat.card_prod]

omit [DecidableEq W] in
/-- Cardinal bound for second-kernel-bad pairs. -/
theorem card_badSecondKernelPairs_le (d : Nat) :
    Nat.card (badSecondKernelPairs
      (F := F) (W := W) (R := R) (R' := R') d) ≤
      Nat.card (Matrix R W F) *
        Nat.card (badChecksForDistance (F := F) (W := W) (R := R') d) := by
  calc
    Nat.card (badSecondKernelPairs
        (F := F) (W := W) (R := R) (R' := R') d) ≤
        Nat.card
          (Matrix R W F ×
            badChecksForDistance (F := F) (W := W) (R := R') d) :=
      Nat.card_le_card_of_injective
        (badSecondKernelPairsEncoding
          (F := F) (W := W) (R := R) (R' := R') d)
        (badSecondKernelPairsEncoding_injective
          (F := F) (W := W) (R := R) (R' := R') d)
    _ = _ := by rw [Nat.card_prod]

omit [DecidableEq W] in
/-- Cardinal bound for second-image-bad pairs. -/
theorem card_badSecondImagePairs_le (d : Nat) :
    Nat.card (badSecondImagePairs
      (F := F) (W := W) (R := R) (R' := R') d) ≤
      Nat.card (Matrix R W F) *
        Nat.card (badGeneratorsForDistance (F := F) (W := W) (R := R') d) := by
  calc
    Nat.card (badSecondImagePairs
        (F := F) (W := W) (R := R) (R' := R') d) ≤
        Nat.card
          (Matrix R W F ×
            badGeneratorsForDistance (F := F) (W := W) (R := R') d) :=
      Nat.card_le_card_of_injective
        (badSecondImagePairsEncoding
          (F := F) (W := W) (R := R) (R' := R') d)
        (badSecondImagePairsEncoding_injective
          (F := F) (W := W) (R := R) (R' := R') d)
    _ = _ := by rw [Nat.card_prod]

/-- Forward rectangle-bad pairs are exactly the sigma type of bad first
checks over the chosen second matrix. -/
noncomputable def badForwardRectanglePairsEquivSigma (s m k : Nat) :
    badForwardRectanglePairs
        (F := F) (W := W) (R := R) (R' := R') s m k ≃
      Σ g' : Matrix R' W F,
        badChecksAllExactRectangles (R := R)
          (generatorImageParityCheck g') s m k where
  toFun p := ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
  invFun z := ⟨(z.2.1, z.1), z.2.2⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv z := by cases z; rfl

/-- Reverse rectangle-bad pairs are the corresponding sigma type with the
two matrices interchanged. -/
noncomputable def badReverseRectanglePairsEquivSigma (s m k : Nat) :
    badReverseRectanglePairs
        (F := F) (W := W) (R := R) (R' := R') s m k ≃
      Σ h : Matrix R W F,
        badChecksAllExactRectangles (R := R')
          (generatorImageParityCheck h) s m k where
  toFun p := ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
  invFun z := ⟨(z.1, z.2.1), z.2.2⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv z := by cases z; rfl

include hR'Finite in
/-- Uniform sparse-rectangle count in the forward orientation, summed over
all choices of the second matrix. -/
theorem card_badForwardRectanglePairs_mul_rankPenalty_le
    (s m k : Nat) :
    Nat.card (badForwardRectanglePairs
        (F := F) (W := W) (R := R) (R' := R') s m k) *
        (Nat.card F) ^ (k * Fintype.card R) ≤
      ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) *
        Nat.card (LocalMatrixPair (F := F) (W := W) (R := R) (R' := R')) := by
  classical
  rw [Nat.card_congr (badForwardRectanglePairsEquivSigma
    (F := F) (W := W) (R := R) (R' := R') s m k), Nat.card_sigma,
    Finset.sum_mul]
  calc
    (∑ g' : Matrix R' W F,
        Nat.card (badChecksAllExactRectangles (R := R)
          (generatorImageParityCheck g') s m k) *
          (Nat.card F) ^ (k * Fintype.card R)) ≤
        ∑ _g' : Matrix R' W F,
          (Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
            (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
              (Nat.card F) ^ (2 * m * Fintype.card W + s)) *
            Nat.card (Matrix R W F) := by
      apply Finset.sum_le_sum
      intro g' _hg'
      exact card_badChecksAllExactRectangles_mul_rankPenalty_le
        (R := R) (generatorImageParityCheck g') s m k
    _ = _ := by
      simp [LocalMatrixPair, Nat.card_eq_fintype_card,
        mul_assoc, mul_comm, mul_left_comm]

include hRFinite in
/-- Uniform sparse-rectangle count in the reverse orientation. -/
theorem card_badReverseRectanglePairs_mul_rankPenalty_le
    (s m k : Nat) :
    Nat.card (badReverseRectanglePairs
        (F := F) (W := W) (R := R) (R' := R') s m k) *
        (Nat.card F) ^ (k * Fintype.card R') ≤
      ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) *
        Nat.card (LocalMatrixPair (F := F) (W := W) (R := R) (R' := R')) := by
  classical
  rw [Nat.card_congr (badReverseRectanglePairsEquivSigma
    (F := F) (W := W) (R := R) (R' := R') s m k), Nat.card_sigma,
    Finset.sum_mul]
  calc
    (∑ h : Matrix R W F,
        Nat.card (badChecksAllExactRectangles (R := R')
          (generatorImageParityCheck h) s m k) *
          (Nat.card F) ^ (k * Fintype.card R')) ≤
        ∑ _h : Matrix R W F,
          (Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
            (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
              (Nat.card F) ^ (2 * m * Fintype.card W + s)) *
            Nat.card (Matrix R' W F) := by
      apply Finset.sum_le_sum
      intro h _hh
      exact card_badChecksAllExactRectangles_mul_rankPenalty_le
        (R := R') (generatorImageParityCheck h) s m k
    _ = _ := by
      simp [LocalMatrixPair, Nat.card_eq_fintype_card,
        mul_assoc, mul_comm, mul_left_comm]

/-- The first-kernel bad-pair count inherits the usual low-word factor and
the first matrix's row-syndrome penalty. -/
theorem card_badFirstKernelPairs_mul_penalty_le (d : Nat) :
    Nat.card (badFirstKernelPairs
        (F := F) (W := W) (R := R) (R' := R') d) *
        (Nat.card F) ^ Fintype.card R ≤
      (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) *
        Nat.card (LocalMatrixPair
          (F := F) (W := W) (R := R) (R' := R')) := by
  calc
    Nat.card (badFirstKernelPairs
        (F := F) (W := W) (R := R) (R' := R') d) *
        (Nat.card F) ^ Fintype.card R ≤
      (Nat.card (badChecksForDistance
          (F := F) (W := W) (R := R) d) * Nat.card (Matrix R' W F)) *
        (Nat.card F) ^ Fintype.card R :=
      Nat.mul_le_mul_right _ (card_badFirstKernelPairs_le
        (F := F) (W := W) (R := R) (R' := R') d)
    _ = (Nat.card (badChecksForDistance
          (F := F) (W := W) (R := R) d) *
        (Nat.card F) ^ Fintype.card R) * Nat.card (Matrix R' W F) := by
      ac_rfl
    _ ≤ ((∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) *
        Nat.card (Matrix R W F)) * Nat.card (Matrix R' W F) :=
      Nat.mul_le_mul_right _
        (card_badChecksForDistance_mul_field_pow_rows_le_choose_sum
          (F := F) (W := W) (R := R) d)
    _ = _ := by
      simp only [LocalMatrixPair, Nat.card_prod]
      simp [mul_assoc]

/-- The first row-image bad-pair count inherits the generator-image factor
and the ambient-length penalty. -/
theorem card_badFirstImagePairs_mul_penalty_le (d : Nat) :
    Nat.card (badFirstImagePairs
        (F := F) (W := W) (R := R) (R' := R') d) *
        (Nat.card F) ^ Fintype.card W ≤
      ((Nat.card F) ^ Fintype.card R *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) *
        Nat.card (LocalMatrixPair
          (F := F) (W := W) (R := R) (R' := R')) := by
  calc
    Nat.card (badFirstImagePairs
        (F := F) (W := W) (R := R) (R' := R') d) *
        (Nat.card F) ^ Fintype.card W ≤
      (Nat.card (badGeneratorsForDistance
          (F := F) (W := W) (R := R) d) * Nat.card (Matrix R' W F)) *
        (Nat.card F) ^ Fintype.card W :=
      Nat.mul_le_mul_right _ (card_badFirstImagePairs_le
        (F := F) (W := W) (R := R) (R' := R') d)
    _ = (Nat.card (badGeneratorsForDistance
          (F := F) (W := W) (R := R) d) *
        (Nat.card F) ^ Fintype.card W) * Nat.card (Matrix R' W F) := by
      ac_rfl
    _ ≤ (((Nat.card F) ^ Fintype.card R *
          (∑ t : Fin d,
            Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) *
        Nat.card (Matrix R W F)) * Nat.card (Matrix R' W F) :=
      Nat.mul_le_mul_right _
        (card_badGeneratorsForDistance_mul_field_pow_length_le_choose_sum
          (F := F) (W := W) (R := R) d)
    _ = _ := by
      simp only [LocalMatrixPair, Nat.card_prod]
      simp [mul_assoc]

/-- The second-kernel bad-pair count has the symmetric row-syndrome
penalty. -/
theorem card_badSecondKernelPairs_mul_penalty_le (d : Nat) :
    Nat.card (badSecondKernelPairs
        (F := F) (W := W) (R := R) (R' := R') d) *
        (Nat.card F) ^ Fintype.card R' ≤
      (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) *
        Nat.card (LocalMatrixPair
          (F := F) (W := W) (R := R) (R' := R')) := by
  calc
    Nat.card (badSecondKernelPairs
        (F := F) (W := W) (R := R) (R' := R') d) *
        (Nat.card F) ^ Fintype.card R' ≤
      (Nat.card (Matrix R W F) * Nat.card (badChecksForDistance
          (F := F) (W := W) (R := R') d)) *
        (Nat.card F) ^ Fintype.card R' :=
      Nat.mul_le_mul_right _ (card_badSecondKernelPairs_le
        (F := F) (W := W) (R := R) (R' := R') d)
    _ = Nat.card (Matrix R W F) *
        (Nat.card (badChecksForDistance
          (F := F) (W := W) (R := R') d) *
          (Nat.card F) ^ Fintype.card R') := by ac_rfl
    _ ≤ Nat.card (Matrix R W F) *
        ((∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) *
          Nat.card (Matrix R' W F)) :=
      Nat.mul_le_mul_left _
        (card_badChecksForDistance_mul_field_pow_rows_le_choose_sum
          (F := F) (W := W) (R := R') d)
    _ = _ := by
      simp only [LocalMatrixPair, Nat.card_prod]
      ac_rfl

/-- The second row-image bad-pair count has the symmetric ambient-length
penalty. -/
theorem card_badSecondImagePairs_mul_penalty_le (d : Nat) :
    Nat.card (badSecondImagePairs
        (F := F) (W := W) (R := R) (R' := R') d) *
        (Nat.card F) ^ Fintype.card W ≤
      ((Nat.card F) ^ Fintype.card R' *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) *
        Nat.card (LocalMatrixPair
          (F := F) (W := W) (R := R) (R' := R')) := by
  calc
    Nat.card (badSecondImagePairs
        (F := F) (W := W) (R := R) (R' := R') d) *
        (Nat.card F) ^ Fintype.card W ≤
      (Nat.card (Matrix R W F) * Nat.card (badGeneratorsForDistance
          (F := F) (W := W) (R := R') d)) *
        (Nat.card F) ^ Fintype.card W :=
      Nat.mul_le_mul_right _ (card_badSecondImagePairs_le
        (F := F) (W := W) (R := R) (R' := R') d)
    _ = Nat.card (Matrix R W F) *
        (Nat.card (badGeneratorsForDistance
          (F := F) (W := W) (R := R') d) *
          (Nat.card F) ^ Fintype.card W) := by ac_rfl
    _ ≤ Nat.card (Matrix R W F) *
        (((Nat.card F) ^ Fintype.card R' *
          (∑ t : Fin d,
            Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) *
          Nat.card (Matrix R' W F)) :=
      Nat.mul_le_mul_left _
        (card_badGeneratorsForDistance_mul_field_pow_length_le_choose_sum
          (F := F) (W := W) (R := R') d)
    _ = _ := by
      simp only [LocalMatrixPair, Nat.card_prod]
      ac_rfl

/-- Pairs failing at least one of the six simultaneous PK22 local-code
requirements: kernel and row-image distance for each matrix, or sparse
product-kernel exclusion in either orientation. -/
def badBidirectionalLocalPairs (d s m k : Nat) :=
  {p : LocalMatrixPair (F := F) (W := W) (R := R) (R' := R') //
    (∃ c : Word F W,
      c ≠ 0 ∧ HammingWeight c < d ∧ p.1.mulVec c = 0) ∨
    (∃ a : Word F R,
      a ≠ 0 ∧ HammingWeight (p.1.transpose.mulVec a) < d) ∨
    (∃ c : Word F W,
      c ≠ 0 ∧ HammingWeight c < d ∧ p.2.mulVec c = 0) ∨
    (∃ a : Word F R',
      a ≠ 0 ∧ HammingWeight (p.2.transpose.mulVec a) < d) ∨
    (∃ A B : Finset W,
      A.card = Fintype.card W - m ∧
      B.card = Fintype.card W - m ∧
      ∃ x : Matrix W W F,
        restrictedWeight x A B < s ∧
        k ≤ (generatorImageParityCheck p.2 * x).rank ∧
        ProductKernel p.1 (generatorImageParityCheck p.2) x) ∨
    (∃ A B : Finset W,
      A.card = Fintype.card W - m ∧
      B.card = Fintype.card W - m ∧
      ∃ x : Matrix W W F,
        restrictedWeight x A B < s ∧
        k ≤ (generatorImageParityCheck p.1 * x).rank ∧
        ProductKernel p.2 (generatorImageParityCheck p.1) x)}

noncomputable instance badBidirectionalLocalPairsFintype
    (d s m k : Nat) :
    Fintype (badBidirectionalLocalPairs
      (F := F) (W := W) (R := R) (R' := R') d s m k) := by
  classical
  unfold badBidirectionalLocalPairs LocalMatrixPair
  infer_instance

/-- Split a globally bad pair into its first failing event while retaining
the underlying pair in every branch. -/
noncomputable def badBidirectionalLocalPairsEncoding
    (d s m k : Nat)
    (p : badBidirectionalLocalPairs
      (F := F) (W := W) (R := R) (R' := R') d s m k) :
    badFirstKernelPairs (F := F) (W := W) (R := R) (R' := R') d ⊕
      (badFirstImagePairs (F := F) (W := W) (R := R) (R' := R') d ⊕
      (badSecondKernelPairs (F := F) (W := W) (R := R) (R' := R') d ⊕
      (badSecondImagePairs (F := F) (W := W) (R := R) (R' := R') d ⊕
      (badForwardRectanglePairs
          (F := F) (W := W) (R := R) (R' := R') s m k ⊕
        badReverseRectanglePairs
          (F := F) (W := W) (R := R) (R' := R') s m k)))) := by
  classical
  by_cases h₁ : ∃ c : Word F W,
      c ≠ 0 ∧ HammingWeight c < d ∧ p.1.1.mulVec c = 0
  · exact Sum.inl ⟨p.1, h₁⟩
  · by_cases h₂ : ∃ a : Word F R,
        a ≠ 0 ∧ HammingWeight (p.1.1.transpose.mulVec a) < d
    · exact Sum.inr (Sum.inl ⟨p.1, h₂⟩)
    · by_cases h₃ : ∃ c : Word F W,
          c ≠ 0 ∧ HammingWeight c < d ∧ p.1.2.mulVec c = 0
      · exact Sum.inr (Sum.inr (Sum.inl ⟨p.1, h₃⟩))
      · by_cases h₄ : ∃ a : Word F R',
            a ≠ 0 ∧ HammingWeight (p.1.2.transpose.mulVec a) < d
        · exact Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨p.1, h₄⟩)))
        · by_cases h₅ : ∃ A B : Finset W,
              A.card = Fintype.card W - m ∧
              B.card = Fintype.card W - m ∧
              ∃ x : Matrix W W F,
                restrictedWeight x A B < s ∧
                k ≤ (generatorImageParityCheck p.1.2 * x).rank ∧
                ProductKernel p.1.1
                  (generatorImageParityCheck p.1.2) x
          · exact Sum.inr (Sum.inr (Sum.inr (Sum.inr
              (Sum.inl ⟨p.1, h₅⟩))))
          · have hRest₂ := p.2.resolve_left h₁
            have hRest₃ := hRest₂.resolve_left h₂
            have hRest₄ := hRest₃.resolve_left h₃
            have hRest₅ := hRest₄.resolve_left h₄
            have h₆ := hRest₅.resolve_left h₅
            exact Sum.inr (Sum.inr (Sum.inr (Sum.inr
              (Sum.inr ⟨p.1, h₆⟩))))

/-- Read the matrix pair carried by any branch of the six-event sum. -/
def badBidirectionalLocalPairsSumVal {d s m k : Nat} :
    badFirstKernelPairs (F := F) (W := W) (R := R) (R' := R') d ⊕
      (badFirstImagePairs (F := F) (W := W) (R := R) (R' := R') d ⊕
      (badSecondKernelPairs (F := F) (W := W) (R := R) (R' := R') d ⊕
      (badSecondImagePairs (F := F) (W := W) (R := R) (R' := R') d ⊕
      (badForwardRectanglePairs
          (F := F) (W := W) (R := R) (R' := R') s m k ⊕
        badReverseRectanglePairs
          (F := F) (W := W) (R := R) (R' := R') s m k)))) →
      LocalMatrixPair (F := F) (W := W) (R := R) (R' := R') :=
  Sum.elim Subtype.val
    (Sum.elim Subtype.val
      (Sum.elim Subtype.val
        (Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val))))

theorem badBidirectionalLocalPairsEncoding_val
    (d s m k : Nat)
    (p : badBidirectionalLocalPairs
      (F := F) (W := W) (R := R) (R' := R') d s m k) :
    badBidirectionalLocalPairsSumVal
      (badBidirectionalLocalPairsEncoding
        (F := F) (W := W) (R := R) (R' := R') d s m k p) = p.1 := by
  classical
  unfold badBidirectionalLocalPairsEncoding
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split <;> rfl

/-- The six-event encoding is injective because every branch retains its
underlying matrix pair. -/
theorem badBidirectionalLocalPairsEncoding_injective
    (d s m k : Nat) :
    Function.Injective
      (badBidirectionalLocalPairsEncoding
        (F := F) (W := W) (R := R) (R' := R') d s m k) := by
  intro p q hpq
  apply Subtype.ext
  have hval := congrArg badBidirectionalLocalPairsSumVal hpq
  simpa only [badBidirectionalLocalPairsEncoding_val] using hval

/-- Six-event finite union bound for a uniformly chosen ordered pair of
local matrices. -/
theorem card_badBidirectionalLocalPairs_le_add
    (d s m k : Nat) :
    Nat.card (badBidirectionalLocalPairs
      (F := F) (W := W) (R := R) (R' := R') d s m k) ≤
      Nat.card (badFirstKernelPairs
        (F := F) (W := W) (R := R) (R' := R') d) +
      Nat.card (badFirstImagePairs
        (F := F) (W := W) (R := R) (R' := R') d) +
      Nat.card (badSecondKernelPairs
        (F := F) (W := W) (R := R) (R' := R') d) +
      Nat.card (badSecondImagePairs
        (F := F) (W := W) (R := R) (R' := R') d) +
      Nat.card (badForwardRectanglePairs
        (F := F) (W := W) (R := R) (R' := R') s m k) +
      Nat.card (badReverseRectanglePairs
        (F := F) (W := W) (R := R) (R' := R') s m k) := by
  classical
  calc
    Nat.card (badBidirectionalLocalPairs
        (F := F) (W := W) (R := R) (R' := R') d s m k) ≤
        Nat.card
          (badFirstKernelPairs
              (F := F) (W := W) (R := R) (R' := R') d ⊕
            (badFirstImagePairs
                (F := F) (W := W) (R := R) (R' := R') d ⊕
            (badSecondKernelPairs
                (F := F) (W := W) (R := R) (R' := R') d ⊕
            (badSecondImagePairs
                (F := F) (W := W) (R := R) (R' := R') d ⊕
            (badForwardRectanglePairs
                (F := F) (W := W) (R := R) (R' := R') s m k ⊕
              badReverseRectanglePairs
                (F := F) (W := W) (R := R) (R' := R') s m k))))) :=
      Nat.card_le_card_of_injective
        (badBidirectionalLocalPairsEncoding
          (F := F) (W := W) (R := R) (R' := R') d s m k)
        (badBidirectionalLocalPairsEncoding_injective
          (F := F) (W := W) (R := R) (R' := R') d s m k)
    _ = _ := by
      rw [Nat.card_sum, Nat.card_sum, Nat.card_sum, Nat.card_sum,
        Nat.card_sum]
      omega

private theorem six_mul_lt_of_scaled_bound
    (bad factor penalty total : Nat)
    (hTotalPositive : 0 < total)
    (hBound : bad * penalty ≤ factor * total)
    (hFactor : 6 * factor < penalty) :
    6 * bad < total := by
  have hScaled : (6 * bad) * penalty < total * penalty := by
    calc
      (6 * bad) * penalty = 6 * (bad * penalty) := by simp [mul_assoc]
      _ ≤ 6 * (factor * total) := Nat.mul_le_mul_left 6 hBound
      _ = (6 * factor) * total := by simp [mul_assoc]
      _ < penalty * total :=
        Nat.mul_lt_mul_of_pos_right hFactor hTotalPositive
      _ = total * penalty := Nat.mul_comm _ _
  exact Nat.lt_of_mul_lt_mul_right hScaled

set_option maxHeartbeats 1200000 in
/-- A finite six-event union bound chooses one ordered matrix pair that
simultaneously has kernel and row-image distance in both components and has
no ranked sparse rectangle witness in either product orientation. -/
theorem exists_bidirectional_local_pair_without_bad_events
    (d s m k : Nat)
    (hFirstKernelFactor :
      6 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R)
    (hFirstImageFactor :
      6 * ((Nat.card F) ^ Fintype.card R *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) <
        (Nat.card F) ^ Fintype.card W)
    (hSecondKernelFactor :
      6 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R')
    (hSecondImageFactor :
      6 * ((Nat.card F) ^ Fintype.card R' *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) <
        (Nat.card F) ^ Fintype.card W)
    (hForwardRectangleFactor :
      6 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R))
    (hReverseRectangleFactor :
      6 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R')) :
    ∃ (h : Matrix R W F) (g' : Matrix R' W F),
      (∀ c : Word F W, h.mulVec c = 0 → c ≠ 0 →
        d ≤ HammingWeight c) ∧
      (∀ a : Word F R, a ≠ 0 →
        d ≤ HammingWeight (h.transpose.mulVec a)) ∧
      (∀ c : Word F W, g'.mulVec c = 0 → c ≠ 0 →
        d ≤ HammingWeight c) ∧
      (∀ a : Word F R', a ≠ 0 →
        d ≤ HammingWeight (g'.transpose.mulVec a)) ∧
      (¬∃ A B : Finset W,
        A.card = Fintype.card W - m ∧
        B.card = Fintype.card W - m ∧
        ∃ x : Matrix W W F,
          restrictedWeight x A B < s ∧
          k ≤ (generatorImageParityCheck g' * x).rank ∧
          ProductKernel h (generatorImageParityCheck g') x) ∧
      (¬∃ A B : Finset W,
        A.card = Fintype.card W - m ∧
        B.card = Fintype.card W - m ∧
        ∃ x : Matrix W W F,
          restrictedWeight x A B < s ∧
          k ≤ (generatorImageParityCheck h * x).rank ∧
          ProductKernel g' (generatorImageParityCheck h) x) := by
  classical
  let distanceFactor := ∑ t : Fin d,
    Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1
  let firstKernelPenalty := (Nat.card F) ^ Fintype.card R
  let firstImageFactor := (Nat.card F) ^ Fintype.card R * distanceFactor
  let imagePenalty := (Nat.card F) ^ Fintype.card W
  let secondKernelPenalty := (Nat.card F) ^ Fintype.card R'
  let secondImageFactor := (Nat.card F) ^ Fintype.card R' * distanceFactor
  let rectangleFactor :=
    (Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
      (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
        (Nat.card F) ^ (2 * m * Fintype.card W + s))
  let forwardPenalty := (Nat.card F) ^ (k * Fintype.card R)
  let reversePenalty := (Nat.card F) ^ (k * Fintype.card R')
  let firstKernelBad := Nat.card (badFirstKernelPairs
    (F := F) (W := W) (R := R) (R' := R') d)
  let firstImageBad := Nat.card (badFirstImagePairs
    (F := F) (W := W) (R := R) (R' := R') d)
  let secondKernelBad := Nat.card (badSecondKernelPairs
    (F := F) (W := W) (R := R) (R' := R') d)
  let secondImageBad := Nat.card (badSecondImagePairs
    (F := F) (W := W) (R := R) (R' := R') d)
  let forwardBad := Nat.card (badForwardRectanglePairs
    (F := F) (W := W) (R := R) (R' := R') s m k)
  let reverseBad := Nat.card (badReverseRectanglePairs
    (F := F) (W := W) (R := R) (R' := R') s m k)
  let total := Nat.card (LocalMatrixPair
    (F := F) (W := W) (R := R) (R' := R'))
  have hTotalPositive : 0 < total := Nat.card_pos
  have hFirstKernelBound : firstKernelBad * firstKernelPenalty ≤
      distanceFactor * total := by
    simpa [firstKernelBad, firstKernelPenalty, distanceFactor, total] using
      card_badFirstKernelPairs_mul_penalty_le
        (F := F) (W := W) (R := R) (R' := R') d
  have hFirstImageBound : firstImageBad * imagePenalty ≤
      firstImageFactor * total := by
    simpa [firstImageBad, imagePenalty, firstImageFactor, distanceFactor,
      total] using card_badFirstImagePairs_mul_penalty_le
        (F := F) (W := W) (R := R) (R' := R') d
  have hSecondKernelBound : secondKernelBad * secondKernelPenalty ≤
      distanceFactor * total := by
    simpa [secondKernelBad, secondKernelPenalty, distanceFactor, total] using
      card_badSecondKernelPairs_mul_penalty_le
        (F := F) (W := W) (R := R) (R' := R') d
  have hSecondImageBound : secondImageBad * imagePenalty ≤
      secondImageFactor * total := by
    simpa [secondImageBad, imagePenalty, secondImageFactor, distanceFactor,
      total] using card_badSecondImagePairs_mul_penalty_le
        (F := F) (W := W) (R := R) (R' := R') d
  have hForwardBound : forwardBad * forwardPenalty ≤
      rectangleFactor * total := by
    simpa [forwardBad, forwardPenalty, rectangleFactor, total] using
      card_badForwardRectanglePairs_mul_rankPenalty_le
        (F := F) (W := W) (R := R) (R' := R') s m k
  have hReverseBound : reverseBad * reversePenalty ≤
      rectangleFactor * total := by
    simpa [reverseBad, reversePenalty, rectangleFactor, total] using
      card_badReverseRectanglePairs_mul_rankPenalty_le
        (F := F) (W := W) (R := R) (R' := R') s m k
  have hFirstKernelSix : 6 * firstKernelBad < total :=
    six_mul_lt_of_scaled_bound firstKernelBad distanceFactor
      firstKernelPenalty total hTotalPositive hFirstKernelBound
      (by simpa [distanceFactor, firstKernelPenalty] using hFirstKernelFactor)
  have hFirstImageSix : 6 * firstImageBad < total :=
    six_mul_lt_of_scaled_bound firstImageBad firstImageFactor imagePenalty
      total hTotalPositive hFirstImageBound
      (by simpa [firstImageFactor, imagePenalty, distanceFactor] using
        hFirstImageFactor)
  have hSecondKernelSix : 6 * secondKernelBad < total :=
    six_mul_lt_of_scaled_bound secondKernelBad distanceFactor
      secondKernelPenalty total hTotalPositive hSecondKernelBound
      (by simpa [distanceFactor, secondKernelPenalty] using
        hSecondKernelFactor)
  have hSecondImageSix : 6 * secondImageBad < total :=
    six_mul_lt_of_scaled_bound secondImageBad secondImageFactor imagePenalty
      total hTotalPositive hSecondImageBound
      (by simpa [secondImageFactor, imagePenalty, distanceFactor] using
        hSecondImageFactor)
  have hForwardSix : 6 * forwardBad < total :=
    six_mul_lt_of_scaled_bound forwardBad rectangleFactor forwardPenalty
      total hTotalPositive hForwardBound
      (by simpa [rectangleFactor, forwardPenalty] using
        hForwardRectangleFactor)
  have hReverseSix : 6 * reverseBad < total :=
    six_mul_lt_of_scaled_bound reverseBad rectangleFactor reversePenalty
      total hTotalPositive hReverseBound
      (by simpa [rectangleFactor, reversePenalty] using
        hReverseRectangleFactor)
  have hBadLt : Nat.card (badBidirectionalLocalPairs
      (F := F) (W := W) (R := R) (R' := R') d s m k) < total :=
    (card_badBidirectionalLocalPairs_le_add
      (F := F) (W := W) (R := R) (R' := R') d s m k).trans_lt (by
        dsimp only [firstKernelBad, firstImageBad, secondKernelBad,
          secondImageBad, forwardBad, reverseBad] at *
        omega)
  have hExists : ∃ p : LocalMatrixPair
      (F := F) (W := W) (R := R) (R' := R'),
      ¬((∃ c : Word F W,
          c ≠ 0 ∧ HammingWeight c < d ∧ p.1.mulVec c = 0) ∨
        (∃ a : Word F R,
          a ≠ 0 ∧ HammingWeight (p.1.transpose.mulVec a) < d) ∨
        (∃ c : Word F W,
          c ≠ 0 ∧ HammingWeight c < d ∧ p.2.mulVec c = 0) ∨
        (∃ a : Word F R',
          a ≠ 0 ∧ HammingWeight (p.2.transpose.mulVec a) < d) ∨
        (∃ A B : Finset W,
          A.card = Fintype.card W - m ∧
          B.card = Fintype.card W - m ∧
          ∃ x : Matrix W W F,
            restrictedWeight x A B < s ∧
            k ≤ (generatorImageParityCheck p.2 * x).rank ∧
            ProductKernel p.1 (generatorImageParityCheck p.2) x) ∨
        (∃ A B : Finset W,
          A.card = Fintype.card W - m ∧
          B.card = Fintype.card W - m ∧
          ∃ x : Matrix W W F,
            restrictedWeight x A B < s ∧
            k ≤ (generatorImageParityCheck p.1 * x).rank ∧
            ProductKernel p.2 (generatorImageParityCheck p.1) x)) := by
    by_contra hNo
    have hSurjective : Function.Surjective
        (Subtype.val : badBidirectionalLocalPairs
          (F := F) (W := W) (R := R) (R' := R') d s m k →
            LocalMatrixPair (F := F) (W := W) (R := R) (R' := R')) := by
      intro p
      have hBad :
          (∃ c : Word F W,
            c ≠ 0 ∧ HammingWeight c < d ∧ p.1.mulVec c = 0) ∨
          (∃ a : Word F R,
            a ≠ 0 ∧ HammingWeight (p.1.transpose.mulVec a) < d) ∨
          (∃ c : Word F W,
            c ≠ 0 ∧ HammingWeight c < d ∧ p.2.mulVec c = 0) ∨
          (∃ a : Word F R',
            a ≠ 0 ∧ HammingWeight (p.2.transpose.mulVec a) < d) ∨
          (∃ A B : Finset W,
            A.card = Fintype.card W - m ∧
            B.card = Fintype.card W - m ∧
            ∃ x : Matrix W W F,
              restrictedWeight x A B < s ∧
              k ≤ (generatorImageParityCheck p.2 * x).rank ∧
              ProductKernel p.1 (generatorImageParityCheck p.2) x) ∨
          (∃ A B : Finset W,
            A.card = Fintype.card W - m ∧
            B.card = Fintype.card W - m ∧
            ∃ x : Matrix W W F,
              restrictedWeight x A B < s ∧
              k ≤ (generatorImageParityCheck p.1 * x).rank ∧
              ProductKernel p.2 (generatorImageParityCheck p.1) x) := by
        by_contra hGood
        exact hNo ⟨p, hGood⟩
      exact ⟨⟨p, hBad⟩, rfl⟩
    have hCardLe := Nat.card_le_card_of_surjective
      (Subtype.val : badBidirectionalLocalPairs
        (F := F) (W := W) (R := R) (R' := R') d s m k →
          LocalMatrixPair (F := F) (W := W) (R := R) (R' := R'))
      hSurjective
    have hTotalLe : total ≤ Nat.card (badBidirectionalLocalPairs
        (F := F) (W := W) (R := R) (R' := R') d s m k) := by
      dsimp only [total]
      exact hCardLe
    exact (not_le_of_gt hBadLt) hTotalLe
  obtain ⟨⟨h, g'⟩, hGood⟩ := hExists
  have h₁ := (not_or.mp hGood).1
  have hRest₂ := (not_or.mp hGood).2
  have h₂ := (not_or.mp hRest₂).1
  have hRest₃ := (not_or.mp hRest₂).2
  have h₃ := (not_or.mp hRest₃).1
  have hRest₄ := (not_or.mp hRest₃).2
  have h₄ := (not_or.mp hRest₄).1
  have hRest₅ := (not_or.mp hRest₄).2
  have h₅ := (not_or.mp hRest₅).1
  have h₆ := (not_or.mp hRest₅).2
  refine ⟨h, g', ?_, ?_, ?_, ?_, h₅, h₆⟩
  · intro c hcKernel hcNonzero
    exact Nat.le_of_not_gt (fun hcWeight =>
      h₁ ⟨c, hcNonzero, hcWeight, hcKernel⟩)
  · intro a haNonzero
    exact Nat.le_of_not_gt (fun haWeight =>
      h₂ ⟨a, haNonzero, haWeight⟩)
  · intro c hcKernel hcNonzero
    exact Nat.le_of_not_gt (fun hcWeight =>
      h₃ ⟨c, hcNonzero, hcWeight, hcKernel⟩)
  · intro a haNonzero
    exact Nat.le_of_not_gt (fun haWeight =>
      h₄ ⟨a, haNonzero, haWeight⟩)

set_option maxHeartbeats 1200000 in
/-- The simultaneous random-local-code package used by PK22. One pair
`(h,g')` has maximal row rank, distance at least `d` for both kernels and
both row images, and product expansion in the two orientations required by
the lifted-product argument. -/
theorem exists_bidirectional_productExpanding_pair
    (d s m k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hRankTarget : 36 * k * s ≤ 5 * d * d)
    (hFirstKernelFactor :
      6 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R)
    (hFirstImageFactor :
      6 * ((Nat.card F) ^ Fintype.card R *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) <
        (Nat.card F) ^ Fintype.card W)
    (hSecondKernelFactor :
      6 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R')
    (hSecondImageFactor :
      6 * ((Nat.card F) ^ Fintype.card R' *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) <
        (Nat.card F) ^ Fintype.card W)
    (hForwardRectangleFactor :
      6 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R))
    (hReverseRectangleFactor :
      6 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R')) :
    ∃ (h : Matrix R W F) (g' : Matrix R' W F),
      h.rank = Fintype.card R ∧
      g'.rank = Fintype.card R' ∧
      (∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      (∀ c : Word F W,
        c ∈ (parityCheckCode (generatorImageParityCheck h)).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      (∀ c : Word F W, c ∈ (parityCheckCode g').carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      (∀ c : Word F W,
        c ∈ (parityCheckCode (generatorImageParityCheck g')).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      ProductExpanding h (generatorImageParityCheck g') s m
        ((d : ℝ) / (3 * (Fintype.card W : ℝ))) ∧
      ProductExpanding g' (generatorImageParityCheck h) s m
        ((d : ℝ) / (3 * (Fintype.card W : ℝ))) := by
  obtain ⟨h, g', hKernelDistance, hImageDistance,
      hKernelDistance', hImageDistance', hNoForward, hNoReverse⟩ :=
    exists_bidirectional_local_pair_without_bad_events
      (F := F) (W := W) (R := R) (R' := R') d s m k
      hFirstKernelFactor hFirstImageFactor hSecondKernelFactor
      hSecondImageFactor hForwardRectangleFactor hReverseRectangleFactor
  have hRank := rank_eq_card_rows_of_image_distance
    h d hPositive hImageDistance
  have hRank' := rank_eq_card_rows_of_image_distance
    g' d hPositive hImageDistance'
  have hCheckDistance := parityCheckCode_distance_of_mulVec_distance
    h d hKernelDistance
  have hCheckDistance' := parityCheckCode_distance_of_mulVec_distance
    g' d hKernelDistance'
  have hRowImageDistance := parityCheckCode_generatorImageParityCheck_distance
    h d hImageDistance
  have hRowImageDistance' := parityCheckCode_generatorImageParityCheck_distance
    g' d hImageDistance'
  have hForwardExpand :=
    productExpanding_of_no_ranked_sparse_exactRectangle_witness
      h (generatorImageParityCheck g') d m s k
      hPositive hLength hSmallM hRankTarget
      hCheckDistance hRowImageDistance' hNoForward
  have hReverseExpand :=
    productExpanding_of_no_ranked_sparse_exactRectangle_witness
      g' (generatorImageParityCheck h) d m s k
      hPositive hLength hSmallM hRankTarget
      hCheckDistance' hRowImageDistance hNoReverse
  exact ⟨h, g', hRank, hRank', hCheckDistance, hRowImageDistance,
    hCheckDistance', hRowImageDistance', hForwardExpand, hReverseExpand⟩

end QEC.Coding.ProductExpansion
