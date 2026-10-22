import QEC.Coding.ExpanderCodes.ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection

/-!
# Finite-field counts for random product expansion

The first counting step in the PK22 product-expansion argument treats a
fixed syndrome matrix `M` and varies the other parity-check matrix `h`.
The equation `M * hᵀ = 0` holds exactly when every row of `h` belongs to
the kernel of `M`. No probability measure is needed for this exact count.
-/

namespace QEC.Coding.ProductExpansion

universe u v

variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']

/-- Nonzero entries of a matrix inside a selected row/column rectangle. -/
def rectangleSupport (x : Matrix W W F) (A B : Finset W) : Finset (W × W) :=
  (A ×ˢ B).filter (fun p => x p.1 p.2 ≠ 0)

omit [Fintype F] [Fintype W] [Fintype R] [Fintype R'] in
/-- The rectangle support has exactly the restricted Hamming weight. -/
theorem card_rectangleSupport
    (x : Matrix W W F) (A B : Finset W) :
    (rectangleSupport x A B).card = restrictedWeight x A B := by
  classical
  calc
    (rectangleSupport x A B).card =
        ∑ p ∈ A ×ˢ B, if x p.1 p.2 ≠ 0 then 1 else 0 := by
          rw [rectangleSupport, Finset.card_filter]
    _ = ∑ i ∈ A, ∑ j ∈ B, if x i j = 0 then 0 else 1 := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : x i j = 0 <;> simp [h]
    _ = restrictedWeight x A B := rfl

/-- Support-and-values encoding for matrices sparse on a rectangle. Outside
the rectangle all values are retained; inside it only the nonzero positions
and their values are retained. -/
noncomputable def sparseRectangleEncoding
    [DecidableEq W]
    (A B : Finset W) (s : Nat)
    (x : {x : Matrix W W F // restrictedWeight x A B < s}) :
    Σ S : {S : Finset (W × W) // S ⊆ A ×ˢ B ∧ S.card < s},
      (((Finset.univ \ (A ×ˢ B) : Finset (W × W)) → F) × (S.1 → F)) := by
  classical
  let S := rectangleSupport x.1 A B
  have hSSubset : S ⊆ A ×ˢ B := Finset.filter_subset _ _
  have hSCard : S.card < s := by
    rw [card_rectangleSupport]
    exact x.2
  exact ⟨⟨S, hSSubset, hSCard⟩,
    ⟨(fun p => x.1 p.1.1 p.1.2), fun p => x.1 p.1.1 p.1.2⟩⟩

omit [Fintype F] in
/-- The sparse rectangle encoding loses no matrix information. -/
theorem sparseRectangleEncoding_injective
    [DecidableEq W]
    (A B : Finset W) (s : Nat) :
    Function.Injective (sparseRectangleEncoding (F := F) A B s) := by
  classical
  intro x y hxy
  have hSupport : rectangleSupport x.1 A B = rectangleSupport y.1 A B := by
    exact congrArg (fun z => z.1.1) hxy
  apply Subtype.ext
  ext i j
  by_cases hij : (i, j) ∈ A ×ˢ B
  · by_cases hxij : x.1 i j = 0
    · have hxNotSupport : (i, j) ∉ rectangleSupport x.1 A B := by
        simp [rectangleSupport, hij, hxij]
      have hyNotSupport : (i, j) ∉ rectangleSupport y.1 A B := by
        simpa [hSupport] using hxNotSupport
      have hyij : y.1 i j = 0 := by
        simpa [rectangleSupport, hij] using hyNotSupport
      exact hxij.trans hyij.symm
    · have hxSupport : (i, j) ∈ rectangleSupport x.1 A B := by
        simp [rectangleSupport, hij, hxij]
      have hySupport : (i, j) ∈ rectangleSupport y.1 A B := by
        simpa [hSupport] using hxSupport
      have hInside := congrArg (fun z =>
        if hp : (i, j) ∈ z.1.1 then some (z.2.2 ⟨(i, j), hp⟩) else none) hxy
      simpa [sparseRectangleEncoding, hxSupport, hySupport] using hInside
  · let p : (Finset.univ \ (A ×ˢ B) : Finset (W × W)) :=
      ⟨(i, j), Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hij⟩⟩
    exact congrArg (fun z => z.2.1 p) hxy

/-- Exact support-sum upper bound for the number of matrices with fewer than
`s` nonzero entries on `A × B`. -/
theorem card_sparseRectangle_lt_le_support_sum
    [DecidableEq W] (A B : Finset W) (s : Nat) :
    Nat.card {x : Matrix W W F // restrictedWeight x A B < s} ≤
      ∑ S : {S : Finset (W × W) // S ⊆ A ×ˢ B ∧ S.card < s},
        (Nat.card F) ^
          ((Finset.univ \ (A ×ˢ B) : Finset (W × W)).card + S.1.card) := by
  classical
  calc
    Nat.card {x : Matrix W W F // restrictedWeight x A B < s} ≤
        Nat.card (Σ S : {S : Finset (W × W) // S ⊆ A ×ˢ B ∧ S.card < s},
          (((Finset.univ \ (A ×ˢ B) : Finset (W × W)) → F) × (S.1 → F))) :=
      Nat.card_le_card_of_injective
        (sparseRectangleEncoding (F := F) A B s)
        (sparseRectangleEncoding_injective (F := F) A B s)
    _ = ∑ S : {S : Finset (W × W) // S ⊆ A ×ˢ B ∧ S.card < s},
        (Nat.card F) ^
          ((Finset.univ \ (A ×ˢ B) : Finset (W × W)).card + S.1.card) := by
      rw [Nat.card_sigma]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Nat.card_prod, Nat.card_fun, Nat.card_fun]
      simp only [Nat.card_eq_fintype_card, Fintype.card_coe, pow_add]

/-- Small subsets of `U` are equivalently a size below `s` together with a
member of the corresponding fixed-cardinality powerset. -/
noncomputable def smallSubsetsEquivSigmaPowersetCard
    {α : Type*} (U : Finset α) (s : Nat) :
    {S : Finset α // S ⊆ U ∧ S.card < s} ≃
      Σ t : Fin s, U.powersetCard t.1 := by
  classical
  refine
    { toFun := fun S =>
        ⟨⟨S.1.card, S.2.2⟩,
          ⟨S.1, Finset.mem_powersetCard.mpr ⟨S.2.1, rfl⟩⟩⟩
      invFun := fun z =>
        ⟨z.2.1, (Finset.mem_powersetCard.mp z.2.2).1,
          by
            rw [(Finset.mem_powersetCard.mp z.2.2).2]
            exact z.1.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro S
    apply Subtype.ext
    rfl
  · rintro ⟨t, S⟩
    have hcard : S.1.card = t.1 := (Finset.mem_powersetCard.mp S.2).2
    have ht : (⟨S.1.card,
        by rw [hcard]; exact t.2⟩ : Fin s) = t := by
      apply Fin.ext
      exact hcard
    apply Sigma.ext ht
    apply (Subtype.heq_iff_coe_eq (fun X => by
      change X ∈ U.powersetCard S.1.card ↔ X ∈ U.powersetCard t.1
      rw [hcard])).mpr
    rfl

omit [Field F] [DecidableEq F] in
/-- Regroup the support sum by the number of nonzero rectangle positions. -/
theorem sparseRectangle_support_sum_eq_choose_sum
    [DecidableEq W] (A B : Finset W) (s : Nat) :
    (∑ S : {S : Finset (W × W) // S ⊆ A ×ˢ B ∧ S.card < s},
        (Nat.card F) ^
          ((Finset.univ \ (A ×ˢ B) : Finset (W × W)).card + S.1.card)) =
      ∑ t : Fin s, Nat.choose (A.card * B.card) t.1 *
        (Nat.card F) ^
          ((Finset.univ \ (A ×ˢ B) : Finset (W × W)).card + t.1) := by
  classical
  let U := A ×ˢ B
  let out := (Finset.univ \ U : Finset (W × W)).card
  let e := smallSubsetsEquivSigmaPowersetCard U s
  calc
    (∑ S : {S : Finset (W × W) // S ⊆ A ×ˢ B ∧ S.card < s},
        (Nat.card F) ^
          ((Finset.univ \ (A ×ˢ B) : Finset (W × W)).card + S.1.card)) =
      ∑ z : Σ t : Fin s, U.powersetCard t.1,
        (Nat.card F) ^ (out + z.1.1) := by
          apply Fintype.sum_equiv e
          intro S
          rfl
    _ = ∑ t : Fin s, Nat.choose U.card t.1 *
        (Nat.card F) ^ (out + t.1) := by
          rw [Fintype.sum_sigma]
          apply Finset.sum_congr rfl
          intro t ht
          simp [Finset.card_powersetCard]
    _ = ∑ t : Fin s, Nat.choose (A.card * B.card) t.1 *
        (Nat.card F) ^
          ((Finset.univ \ (A ×ˢ B) : Finset (W × W)).card + t.1) := by
          simp only [U, out, Finset.card_product]

/-- The paper's finite support count, before replacing binomial coefficients
by a coarser elementary upper bound. -/
theorem card_sparseRectangle_lt_le_choose_sum
    [DecidableEq W] (A B : Finset W) (s : Nat) :
    Nat.card {x : Matrix W W F // restrictedWeight x A B < s} ≤
      ∑ t : Fin s, Nat.choose (A.card * B.card) t.1 *
        (Nat.card F) ^
          ((Finset.univ \ (A ×ˢ B) : Finset (W × W)).card + t.1) := by
  exact (card_sparseRectangle_lt_le_support_sum (F := F) A B s).trans_eq
    (sparseRectangle_support_sum_eq_choose_sum (F := F) A B s)

/-- A uniform elementary bound on the binomial/power sum used for sparse
rectangle matrices. -/
theorem choose_power_sum_le
    (n out s q : Nat) (hq : 0 < q) :
    (∑ t : Fin s, Nat.choose n t.1 * q ^ (out + t.1)) ≤
      s * (n + 1) ^ s * q ^ (out + s) := by
  classical
  have hEach (t : Fin s) :
      Nat.choose n t.1 * q ^ (out + t.1) ≤
        (n + 1) ^ s * q ^ (out + s) := by
    have hChoose : Nat.choose n t.1 ≤ (n + 1) ^ s := by
      exact (Nat.choose_le_pow n t.1).trans <|
        (Nat.pow_le_pow_left (Nat.le_add_right n 1) t.1).trans
          (Nat.pow_le_pow_right (by omega : 0 < n + 1) (Nat.le_of_lt t.2))
    have hPow : q ^ (out + t.1) ≤ q ^ (out + s) :=
      Nat.pow_le_pow_right hq (Nat.add_le_add_left (Nat.le_of_lt t.2) out)
    exact Nat.mul_le_mul hChoose hPow
  have hSum := Finset.sum_le_card_nsmul Finset.univ
    (fun t : Fin s => Nat.choose n t.1 * q ^ (out + t.1))
    ((n + 1) ^ s * q ^ (out + s)) (fun t _ => hEach t)
  simpa [nsmul_eq_mul, mul_assoc] using hSum

/-- Support-and-values encoding for a word below a Hamming-weight threshold. -/
noncomputable def sparseWordEncoding
    [DecidableEq W] (d : Nat)
    (c : {c : Word F W // HammingWeight c < d}) :
    Σ S : {S : Finset W // S ⊆ Finset.univ ∧ S.card < d}, S.1 → F := by
  classical
  let S := hammingSupport c.1
  have hS : S.card < d := c.2
  exact ⟨⟨S, Finset.subset_univ S, hS⟩, fun i => c.1 i.1⟩

omit [Fintype F] in
/-- The sparse-word encoding is injective. -/
theorem sparseWordEncoding_injective
    [DecidableEq W] (d : Nat) :
    Function.Injective (sparseWordEncoding (F := F) (W := W) d) := by
  classical
  intro c e hce
  have hSupport : hammingSupport c.1 = hammingSupport e.1 :=
    congrArg (fun z => z.1.1) hce
  apply Subtype.ext
  funext i
  by_cases hci : c.1 i = 0
  · have hiNotC : i ∉ hammingSupport c.1 := by
      simp [hammingSupport, hci]
    have hiNotE : i ∉ hammingSupport e.1 := by simpa [hSupport] using hiNotC
    have hei : e.1 i = 0 := by simpa [hammingSupport] using hiNotE
    exact hci.trans hei.symm
  · have hiC : i ∈ hammingSupport c.1 := by simp [hammingSupport, hci]
    have hiE : i ∈ hammingSupport e.1 := by simpa [hSupport] using hiC
    have hInside := congrArg (fun z =>
      if hi : i ∈ z.1.1 then some (z.2 ⟨i, hi⟩) else none) hce
    simpa [sparseWordEncoding, hiC, hiE] using hInside

/-- Exact binomial support-count upper bound for low-weight words. -/
theorem card_lowWeightWords_lt_le_choose_sum
    [DecidableEq W] (d : Nat) :
    Nat.card {c : Word F W // HammingWeight c < d} ≤
      ∑ t : Fin d, Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1 := by
  classical
  have hEncode : Nat.card {c : Word F W // HammingWeight c < d} ≤
      Nat.card (Σ S : {S : Finset W // S ⊆ Finset.univ ∧ S.card < d},
        S.1 → F) :=
    Nat.card_le_card_of_injective (sparseWordEncoding (F := F) (W := W) d)
      (sparseWordEncoding_injective (F := F) (W := W) d)
  calc
    Nat.card {c : Word F W // HammingWeight c < d} ≤
        Nat.card (Σ S : {S : Finset W // S ⊆ Finset.univ ∧ S.card < d},
          S.1 → F) := hEncode
    _ = ∑ S : {S : Finset W // S ⊆ Finset.univ ∧ S.card < d},
        (Nat.card F) ^ S.1.card := by
      rw [Nat.card_sigma]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Nat.card_fun]
      simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = ∑ z : Σ t : Fin d,
        (Finset.univ : Finset W).powersetCard t.1,
        (Nat.card F) ^ z.1.1 := by
      apply Fintype.sum_equiv
        (smallSubsetsEquivSigmaPowersetCard (Finset.univ : Finset W) d)
      intro S
      rfl
    _ = ∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1 := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro t ht
      simp [Finset.card_powersetCard]

/-- A word viewed as a one-row matrix. -/
def singleRowMatrix (c : Word F W) : Matrix (ULift.{v} Unit) W F := fun _ j => c j

omit [Fintype F] [DecidableEq F] [Fintype R] [Fintype R'] in
/-- A nonzero one-row matrix has rank one. -/
theorem rank_singleRowMatrix_eq_one
    (c : Word F W) (hc : c ≠ 0) : (singleRowMatrix c).rank = 1 := by
  rw [Matrix.rank_eq_finrank_span_row, Set.range_unique]
  change Module.finrank F (F ∙ c) = 1
  exact finrank_span_singleton hc

omit [Fintype F] [DecidableEq F] [Fintype R] [Fintype R'] in
/-- The one-row left-product equation says that every row of `h` is
orthogonal to the fixed word `c`, equivalently `h.mulVec c = 0`. -/
theorem singleRowMatrix_mul_transpose_eq_zero_iff
    (h : Matrix R W F) (c : Word F W) :
    singleRowMatrix c * h.transpose = 0 ↔ h.mulVec c = 0 := by
  constructor
  · intro hZero
    funext r
    have hEntry := congrArg
      (fun M : Matrix (ULift.{v} Unit) R F => M (ULift.up ()) r) hZero
    simpa [singleRowMatrix, Matrix.mul_apply, Matrix.mulVec,
      Matrix.transpose_apply, dotProduct, mul_comm] using hEntry
  · intro hZero
    ext _ r
    have hEntry := congrFun hZero r
    simpa [singleRowMatrix, Matrix.mul_apply, Matrix.mulVec,
      Matrix.transpose_apply, dotProduct, mul_comm] using hEntry

omit [Fintype F] [DecidableEq F] [Fintype R] [Fintype R'] in
/-- If each side of a square rectangle omits at most `m` coordinates, its
complement has at most `2mw` positions. -/
theorem card_complement_rectangle_le_two_mul
    [DecidableEq W] (A B : Finset W) (m : Nat)
    (hA : Fintype.card W - m ≤ A.card)
    (hB : Fintype.card W - m ≤ B.card) :
    (Finset.univ \ (A ×ˢ B) : Finset (W × W)).card ≤
      2 * m * Fintype.card W := by
  have hAle : A.card ≤ Fintype.card W := Finset.card_le_univ A
  have hBle : B.card ≤ Fintype.card W := Finset.card_le_univ B
  have hwA : Fintype.card W ≤ A.card + m := by omega
  have hwB : Fintype.card W ≤ B.card + m := by omega
  have hMissingA : Fintype.card W - A.card ≤ m := by omega
  have hMissingB : Fintype.card W - B.card ≤ m := by omega
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ (A ×ˢ B)),
    Finset.card_univ, Fintype.card_prod, Finset.card_product]
  calc
    Fintype.card W * Fintype.card W - A.card * B.card =
        (Fintype.card W - A.card) * Fintype.card W +
          A.card * (Fintype.card W - B.card) := by
      rw [Nat.sub_mul, Nat.mul_sub_left_distrib]
      exact (Nat.sub_add_sub_cancel
        (Nat.mul_le_mul_right (Fintype.card W) hAle)
        (Nat.mul_le_mul_left A.card hBle)).symm
    _ ≤ m * Fintype.card W + Fintype.card W * m := by
      exact Nat.add_le_add
        (Nat.mul_le_mul_right (Fintype.card W) hMissingA)
        (Nat.mul_le_mul hAle hMissingB)
    _ = 2 * m * Fintype.card W := by ring

omit [Fintype R] [Fintype R'] in
/-- Coarse PK22 count: rectangle-sparse matrices are bounded by a polynomial
support factor times one field-size power for the omitted coordinates and
the nonzero rectangle entries. -/
theorem card_sparseRectangle_lt_le_coarse
    [DecidableEq W] (A B : Finset W) (s m : Nat)
    (hA : Fintype.card W - m ≤ A.card)
    (hB : Fintype.card W - m ≤ B.card) :
    Nat.card {x : Matrix W W F // restrictedWeight x A B < s} ≤
      s * (A.card * B.card + 1) ^ s *
        (Nat.card F) ^ (2 * m * Fintype.card W + s) := by
  have hCount := card_sparseRectangle_lt_le_choose_sum (F := F) A B s
  have hSum := choose_power_sum_le (A.card * B.card)
    (Finset.univ \ (A ×ˢ B) : Finset (W × W)).card s (Nat.card F)
    (Nat.card_pos)
  have hOutside := card_complement_rectangle_le_two_mul A B m hA hB
  have hExponent :
      (Finset.univ \ (A ×ˢ B) : Finset (W × W)).card + s ≤
        2 * m * Fintype.card W + s := Nat.add_le_add_right hOutside s
  have hPow := Nat.pow_le_pow_right (Nat.card_pos (α := F)) hExponent
  exact hCount.trans <| hSum.trans <|
    Nat.mul_le_mul_left (s * (A.card * B.card + 1) ^ s) hPow

omit [Fintype F] [Fintype W] [Fintype R] [Fintype R'] in
/-- Restricting either side of a rectangle cannot increase its weight. -/
theorem restrictedWeight_mono
    (x : Matrix W W F) {A A' B B' : Finset W}
    (hA : A' ⊆ A) (hB : B' ⊆ B) :
    restrictedWeight x A' B' ≤ restrictedWeight x A B := by
  unfold restrictedWeight
  calc
    (∑ i ∈ A', ∑ j ∈ B', if x i j = 0 then 0 else 1) ≤
        ∑ i ∈ A', ∑ j ∈ B, if x i j = 0 then 0 else 1 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum_of_subset_of_nonneg hB
      intro j hjB hjB'
      omega
    _ ≤ ∑ i ∈ A, ∑ j ∈ B, if x i j = 0 then 0 else 1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hA
      intro i hiA hiA'
      omega

/-- Matrices satisfying a fixed left-product constraint are precisely
independent choices of a kernel vector for each row. -/
noncomputable def leftProductKernelEquivRows
    (M : Matrix R' W F) :
    {h : Matrix R W F // M * h.transpose = 0} ≃
      (R → LinearMap.ker M.mulVecLin) := by
  classical
  refine
    { toFun := fun h r => ⟨h.1 r, ?_⟩
      invFun := fun rows => ⟨(fun r w => (rows r).1 w), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change M.mulVec (h.1 r) = 0
    ext i
    have hEntry := congrArg (fun N : Matrix R' R F => N i r) h.2
    simpa [Matrix.mul_apply, Matrix.mulVec, Matrix.transpose_apply, dotProduct] using hEntry
  · ext i r
    have hRow : M.mulVec ((rows r).1) = 0 := (rows r).2
    have hEntry := congrFun hRow i
    change (∑ j : W, M i j * (rows r).1 j) = 0
    simpa [Matrix.mulVec, dotProduct] using hEntry
  · intro h
    apply Subtype.ext
    ext r w
    rfl
  · intro rows
    funext r
    apply Subtype.ext
    funext w
    rfl

omit [Fintype F] [DecidableEq F] [Fintype R'] in
/-- Exact number of parity-check matrices annihilated by a fixed left
syndrome matrix. This is the finite counting form of the PK22 random-matrix
probability calculation. -/
theorem card_leftProductKernel_eq_card_kernel_pow
    (M : Matrix R' W F) :
    Nat.card {h : Matrix R W F // M * h.transpose = 0} =
      (Nat.card (LinearMap.ker M.mulVecLin)) ^ Nat.card R := by
  classical
  rw [Nat.card_congr (leftProductKernelEquivRows (R := R) M)]
  exact Nat.card_fun

omit [DecidableEq F] [Fintype R'] in
/-- Rank-nullity makes the exact constraint count a power of the field size.
For a uniform random `h`, comparison with the total number of matrices will
give one factor of `|F|^{-rank M}` for each row. -/
theorem card_leftProductKernel_eq_field_pow_nullity
    (M : Matrix R' W F) :
    Nat.card {h : Matrix R W F // M * h.transpose = 0} =
      (Nat.card F) ^ ((Fintype.card W - M.rank) * Fintype.card R) := by
  classical
  have hRankNullity := (M.mulVecLin).finrank_range_add_finrank_ker
  have hKer : Module.finrank F (LinearMap.ker M.mulVecLin) =
      Fintype.card W - M.rank := by
    have hRank : Module.finrank F (LinearMap.range M.mulVecLin) = M.rank := rfl
    have hDomain : Module.finrank F (W → F) = Fintype.card W := by simp
    omega
  rw [card_leftProductKernel_eq_card_kernel_pow]
  rw [Module.natCard_eq_pow_finrank (K := F)
    (V := LinearMap.ker M.mulVecLin), hKer]
  simp only [Nat.card_eq_fintype_card, pow_mul]

omit [DecidableEq F] [Fintype R'] in
/-- The exact count of good check matrices times the rank penalty equals
the total number of check matrices. This avoids division by finite
cardinalities until a probability bound actually needs it. -/
theorem card_leftProductKernel_mul_field_pow_rank_eq_total
    (M : Matrix R' W F) :
    Nat.card {h : Matrix R W F // M * h.transpose = 0} *
        (Nat.card F) ^ (M.rank * Fintype.card R) =
      Nat.card (Matrix R W F) := by
  classical
  have hTotal : Nat.card (Matrix R W F) =
      (Nat.card F) ^ (Fintype.card W * Fintype.card R) := by
    change Nat.card (R → W → F) = _
    rw [Nat.card_fun, Nat.card_fun]
    simp only [Nat.card_eq_fintype_card, pow_mul]
  rw [card_leftProductKernel_eq_field_pow_nullity, hTotal]
  have hRank : M.rank ≤ Fintype.card W := M.rank_le_card_width
  have hAdd : (Fintype.card W - M.rank) + M.rank = Fintype.card W :=
    Nat.sub_add_cancel hRank
  calc
    (Nat.card F) ^ ((Fintype.card W - M.rank) * Fintype.card R) *
        (Nat.card F) ^ (M.rank * Fintype.card R) =
      (Nat.card F) ^
        (((Fintype.card W - M.rank) + M.rank) * Fintype.card R) := by
          rw [add_mul, pow_add]
    _ = (Nat.card F) ^ (Fintype.card W * Fintype.card R) := by rw [hAdd]

omit [DecidableEq F] [Fintype R'] in
/-- Exact count of check matrices annihilating one fixed nonzero word. -/
theorem card_checks_annihilating_nonzero_word_mul_field_pow_rows_eq_total
    (c : Word F W) (hc : c ≠ 0) :
    Nat.card {h : Matrix R W F // h.mulVec c = 0} *
        (Nat.card F) ^ Fintype.card R = Nat.card (Matrix R W F) := by
  let e : {h : Matrix R W F // h.mulVec c = 0} ≃
      {h : Matrix R W F // singleRowMatrix c * h.transpose = 0} :=
    Equiv.subtypeEquivRight (fun h =>
      (singleRowMatrix_mul_transpose_eq_zero_iff h c).symm)
  rw [Nat.card_congr e]
  simpa [rank_singleRowMatrix_eq_one c hc, one_mul] using
    card_leftProductKernel_mul_field_pow_rank_eq_total
      (R := R) (singleRowMatrix c)

/-- Check matrices whose parity-check code contains a nonzero word of
Hamming weight strictly below `d`. -/
def badChecksForDistance (d : Nat) :=
  {h : Matrix R W F // ∃ c : Word F W,
    c ≠ 0 ∧ HammingWeight c < d ∧ h.mulVec c = 0}

noncomputable instance badChecksForDistanceFintype (d : Nat) :
    Fintype (badChecksForDistance (F := F) (W := W) (R := R) d) := by
  classical
  unfold badChecksForDistance
  infer_instance

/-- Encode a distance-bad check matrix by one chosen nonzero low-weight
kernel word and the same matrix in that word's annihilator fiber. -/
noncomputable def badChecksForDistanceEncoding (d : Nat)
    (h : badChecksForDistance (F := F) (W := W) (R := R) d) :
    Σ c : {c : Word F W // c ≠ 0 ∧ HammingWeight c < d},
      {g : Matrix R W F // g.mulVec c.1 = 0} := by
  let c := Classical.choose h.2
  have hc := Classical.choose_spec h.2
  exact ⟨⟨c, hc.1, hc.2.1⟩, ⟨h.1, hc.2.2⟩⟩

omit [Fintype F] [Fintype R] [Fintype R'] in
/-- Choosing a low-weight kernel witness retains the check matrix. -/
theorem badChecksForDistanceEncoding_injective (d : Nat) :
    Function.Injective
      (badChecksForDistanceEncoding (F := F) (W := W) (R := R) d) := by
  intro h g heq
  apply Subtype.ext
  exact congrArg (fun z => z.2.1) heq

omit [Fintype R'] in
/-- Gilbert--Varshamov finite union bound: distance-bad checks pay one field
factor for each independently selected row. -/
theorem card_badChecksForDistance_mul_field_pow_rows_le
    [DecidableEq W] (d : Nat) :
    Nat.card (badChecksForDistance (F := F) (W := W) (R := R) d) *
        (Nat.card F) ^ Fintype.card R ≤
      Nat.card {c : Word F W // HammingWeight c < d} *
        Nat.card (Matrix R W F) := by
  classical
  let X := {c : Word F W // c ≠ 0 ∧ HammingWeight c < d}
  let E := Σ c : X, {g : Matrix R W F // g.mulVec c.1 = 0}
  have hEncode :
      Nat.card (badChecksForDistance (F := F) (W := W) (R := R) d) ≤
        Nat.card E := Nat.card_le_card_of_injective
      (badChecksForDistanceEncoding (F := F) (W := W) (R := R) d)
      (badChecksForDistanceEncoding_injective
        (F := F) (W := W) (R := R) d)
  have hFiber (c : X) :
      Nat.card {g : Matrix R W F // g.mulVec c.1 = 0} *
          (Nat.card F) ^ Fintype.card R = Nat.card (Matrix R W F) :=
    card_checks_annihilating_nonzero_word_mul_field_pow_rows_eq_total
      (R := R) c.1 c.2.1
  have hSigma : Nat.card E * (Nat.card F) ^ Fintype.card R =
      Nat.card X * Nat.card (Matrix R W F) := by
    rw [Nat.card_sigma, Finset.sum_mul]
    calc
      (∑ c : X, Nat.card {g : Matrix R W F // g.mulVec c.1 = 0} *
          (Nat.card F) ^ Fintype.card R) =
          ∑ _c : X, Nat.card (Matrix R W F) := by
            apply Finset.sum_congr rfl
            intro c hc
            exact hFiber c
      _ = Nat.card X * Nat.card (Matrix R W F) := by
        simp [Nat.card_eq_fintype_card]
  have hX : Nat.card X ≤
      Nat.card {c : Word F W // HammingWeight c < d} :=
    Nat.card_le_card_of_injective
      (fun c : X =>
        (⟨c.1, c.2.2⟩ : {c : Word F W // HammingWeight c < d}))
      (fun c e hce => by
        apply Subtype.ext
        exact congrArg (fun z : {c : Word F W // HammingWeight c < d} => z.1) hce)
  exact (Nat.mul_le_mul_right _ hEncode).trans_eq hSigma |>.trans
    (Nat.mul_le_mul_right _ hX)

omit [Fintype R'] in
/-- Gilbert--Varshamov union bound with the low-weight-word count expanded
as a finite binomial sum over supports. -/
theorem card_badChecksForDistance_mul_field_pow_rows_le_choose_sum
    [DecidableEq W] (d : Nat) :
    Nat.card (badChecksForDistance (F := F) (W := W) (R := R) d) *
        (Nat.card F) ^ Fintype.card R ≤
      (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) *
        Nat.card (Matrix R W F) := by
  exact (card_badChecksForDistance_mul_field_pow_rows_le
    (F := F) (W := W) (R := R) d).trans
      (Nat.mul_le_mul_right _
        (card_lowWeightWords_lt_le_choose_sum (F := F) (W := W) d))

/-- A concrete preimage of a target word under multiplication by a fixed
nonzero message. It is used only to translate affine generator fibers to
homogeneous annihilator fibers. -/
noncomputable def generatorFiberBase
    (a : Word F R) (ha : a ≠ 0) (y : Word F W) : Matrix W R F := by
  classical
  have hExists : ∃ i, a i ≠ 0 := by
    by_contra hNo
    push Not at hNo
    apply ha
    funext i
    exact hNo i
  let i₀ := Classical.choose hExists
  exact fun j i => if i = i₀ then (a i₀)⁻¹ * y j else 0

omit [Fintype F] [Fintype W] [Fintype R'] in
/-- The chosen affine-fiber base maps to its prescribed target word. -/
theorem generatorFiberBase_mulVec
    (a : Word F R) (ha : a ≠ 0) (y : Word F W) :
    (generatorFiberBase a ha y).mulVec a = y := by
  classical
  have hExists : ∃ i, a i ≠ 0 := by
    by_contra hNo
    push Not at hNo
    apply ha
    funext i
    exact hNo i
  let i₀ := Classical.choose hExists
  have hi₀ : a i₀ ≠ 0 := Classical.choose_spec hExists
  funext j
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i₀]
  · simp only [generatorFiberBase, i₀, if_pos, mul_assoc]
    rw [mul_comm (y j) (a i₀), ← mul_assoc, inv_mul_cancel₀ hi₀, one_mul]
  · intro i hi hne
    simp [generatorFiberBase, i₀, hne]
  · simp

/-- Transposition followed by translation identifies a fixed generator-output
fiber with the homogeneous annihilator fiber for the same nonzero message. -/
noncomputable def generatorFiberEquivAnnihilator
    (a : Word F R) (ha : a ≠ 0) (y : Word F W) :
    {g : Matrix R W F // g.transpose.mulVec a = y} ≃
      {h : Matrix W R F // h.mulVec a = 0} where
  toFun g := ⟨g.1.transpose - generatorFiberBase a ha y, by
    rw [Matrix.sub_mulVec, g.2, generatorFiberBase_mulVec a ha y, sub_self]⟩
  invFun h := ⟨(h.1 + generatorFiberBase a ha y).transpose, by
    rw [Matrix.transpose_transpose, Matrix.add_mulVec, h.2,
      generatorFiberBase_mulVec a ha y, zero_add]⟩
  left_inv g := by
    apply Subtype.ext
    simp
  right_inv h := by
    apply Subtype.ext
    simp

omit [Fintype R'] in
/-- Every fixed nonzero message and target word has the same exact number of
generator matrices mapping the message to that target. -/
theorem card_generatorFiber_mul_field_pow_length_eq_total
    (a : Word F R) (ha : a ≠ 0) (y : Word F W) :
    Nat.card {g : Matrix R W F // g.transpose.mulVec a = y} *
        (Nat.card F) ^ Fintype.card W = Nat.card (Matrix R W F) := by
  rw [Nat.card_congr (generatorFiberEquivAnnihilator a ha y)]
  have hCount :=
    card_checks_annihilating_nonzero_word_mul_field_pow_rows_eq_total
      (F := F) (W := R) (R := W) a ha
  calc
    Nat.card {h : Matrix W R F // h.mulVec a = 0} *
        Nat.card F ^ Fintype.card W =
      Nat.card (Matrix W R F) := hCount
    _ = Nat.card (Matrix R W F) :=
      Nat.card_congr (Matrix.transposeLinearEquiv W R F F).toEquiv

/-- Generator matrices whose image contains a nonzero word below the target
distance. The witness is a nonzero message, so excluding this event also
forces the generator map to be injective when `d > 0`. -/
def badGeneratorsForDistance (d : Nat) :=
  {g : Matrix R W F // ∃ a : Word F R,
    a ≠ 0 ∧ HammingWeight (g.transpose.mulVec a) < d}

noncomputable instance badGeneratorsForDistanceFintype (d : Nat) :
    Fintype (badGeneratorsForDistance (F := F) (W := W) (R := R) d) := by
  classical
  unfold badGeneratorsForDistance
  infer_instance

/-- Encode a generator-distance failure by a chosen nonzero message, its
low-weight output word, and the generator in the corresponding affine fiber. -/
noncomputable def badGeneratorsForDistanceEncoding (d : Nat)
    (g : badGeneratorsForDistance (F := F) (W := W) (R := R) d) :
    Σ a : {a : Word F R // a ≠ 0},
      Σ y : {y : Word F W // HammingWeight y < d},
        {f : Matrix R W F // f.transpose.mulVec a.1 = y.1} := by
  let a := Classical.choose g.2
  have ha := Classical.choose_spec g.2
  exact ⟨⟨a, ha.1⟩, ⟨⟨g.1.transpose.mulVec a, ha.2⟩, ⟨g.1, rfl⟩⟩⟩

omit [Fintype F] [Fintype R'] in
/-- The generator-distance witness encoding retains the generator matrix. -/
theorem badGeneratorsForDistanceEncoding_injective (d : Nat) :
    Function.Injective
      (badGeneratorsForDistanceEncoding (F := F) (W := W) (R := R) d) := by
  intro g f hgf
  apply Subtype.ext
  exact congrArg (fun z => z.2.2.1) hgf

omit [Fintype R'] in
/-- Finite union bound for random generator codes. The penalty has one field
factor per output coordinate, while the witness count has one factor per
message and one low-weight target word. -/
theorem card_badGeneratorsForDistance_mul_field_pow_length_le
    [DecidableEq W] (d : Nat) :
    Nat.card (badGeneratorsForDistance (F := F) (W := W) (R := R) d) *
        (Nat.card F) ^ Fintype.card W ≤
      (Nat.card F) ^ Fintype.card R *
        Nat.card {y : Word F W // HammingWeight y < d} *
        Nat.card (Matrix R W F) := by
  classical
  let A := {a : Word F R // a ≠ 0}
  let Y := {y : Word F W // HammingWeight y < d}
  let E := Σ a : A, Σ y : Y,
    {f : Matrix R W F // f.transpose.mulVec a.1 = y.1}
  let penalty := (Nat.card F) ^ Fintype.card W
  let total := Nat.card (Matrix R W F)
  have hEncode :
      Nat.card (badGeneratorsForDistance (F := F) (W := W) (R := R) d) ≤
        Nat.card E := Nat.card_le_card_of_injective
      (badGeneratorsForDistanceEncoding (F := F) (W := W) (R := R) d)
      (badGeneratorsForDistanceEncoding_injective
        (F := F) (W := W) (R := R) d)
  have hFiber (a : A) (y : Y) :
      Nat.card {f : Matrix R W F // f.transpose.mulVec a.1 = y.1} *
          penalty = total := by
    simpa [penalty, total] using
      card_generatorFiber_mul_field_pow_length_eq_total
        (W := W) a.1 a.2 y.1
  have hSigma : Nat.card E * penalty = Nat.card A * Nat.card Y * total := by
    rw [Nat.card_sigma, Finset.sum_mul]
    simp_rw [Nat.card_sigma, Finset.sum_mul]
    calc
      (∑ a : A, ∑ y : Y,
          Nat.card {f : Matrix R W F // f.transpose.mulVec a.1 = y.1} *
            penalty) = ∑ _a : A, ∑ _y : Y, total := by
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro y hy
              exact hFiber a y
      _ = Nat.card A * Nat.card Y * total := by
        simp [Nat.card_eq_fintype_card, mul_assoc]
  have hMessages : Nat.card A ≤ (Nat.card F) ^ Fintype.card R := by
    calc
      Nat.card A ≤ Nat.card (Word F R) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = (Nat.card F) ^ Fintype.card R := by
        rw [Nat.card_fun]
        simp only [Nat.card_eq_fintype_card]
  exact (Nat.mul_le_mul_right penalty hEncode).trans_eq hSigma |>.trans
    (Nat.mul_le_mul_right total (Nat.mul_le_mul_right (Nat.card Y) hMessages))

omit [Fintype R'] in
/-- Random-generator GV bound with the low-weight output count expanded as a
finite binomial support sum. -/
theorem card_badGeneratorsForDistance_mul_field_pow_length_le_choose_sum
    [DecidableEq W] (d : Nat) :
    Nat.card (badGeneratorsForDistance (F := F) (W := W) (R := R) d) *
        (Nat.card F) ^ Fintype.card W ≤
      ((Nat.card F) ^ Fintype.card R *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) *
        Nat.card (Matrix R W F) := by
  have hBad := card_badGeneratorsForDistance_mul_field_pow_length_le
    (F := F) (W := W) (R := R) d
  have hWords := card_lowWeightWords_lt_le_choose_sum (F := F) (W := W) d
  exact hBad.trans (by
    simpa [mul_assoc, mul_comm, mul_left_comm] using Nat.mul_le_mul_left
      ((Nat.card F) ^ Fintype.card R * Nat.card (Matrix R W F)) hWords)

omit [Fintype R'] in
/-- If the generator-code GV witness factor is smaller than its output-space
penalty, some generator matrix maps every nonzero message to weight at least
`d`. For positive `d`, this conclusion includes full row rank. -/
theorem exists_generator_with_image_distance
    [DecidableEq W] (d : Nat)
    (hFactor :
      (Nat.card F) ^ Fintype.card R *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card W) :
    ∃ g : Matrix R W F,
      ∀ a : Word F R, a ≠ 0 → d ≤ HammingWeight (g.transpose.mulVec a) := by
  classical
  let Bad := badGeneratorsForDistance (F := F) (W := W) (R := R) d
  let factor := (Nat.card F) ^ Fintype.card R *
    (∑ t : Fin d,
      Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)
  let penalty := (Nat.card F) ^ Fintype.card W
  let total := Nat.card (Matrix R W F)
  have hBound : Nat.card Bad * penalty ≤ factor * total := by
    simpa [Bad, factor, penalty, total] using
      card_badGeneratorsForDistance_mul_field_pow_length_le_choose_sum
        (F := F) (W := W) (R := R) d
  have hTotalPositive : 0 < total := Nat.card_pos
  have hBadLt : Nat.card Bad < total := by
    by_contra hNot
    have hTotalLe : total ≤ Nat.card Bad := le_of_not_gt hNot
    have hContradiction : total * penalty < penalty * total :=
      (Nat.mul_le_mul_right penalty hTotalLe).trans_lt <|
        hBound.trans_lt <| by
          simpa [factor, penalty, total] using
            Nat.mul_lt_mul_of_pos_right hFactor hTotalPositive
    simp [mul_comm] at hContradiction
  by_contra hNoGood
  push Not at hNoGood
  have hSurjective : Function.Surjective
      (Subtype.val : badGeneratorsForDistance (F := F) (W := W) (R := R) d →
        Matrix R W F) := by
    intro g
    have hBad : ∃ a : Word F R,
        a ≠ 0 ∧ HammingWeight (g.transpose.mulVec a) < d := by
      exact hNoGood g
    exact ⟨⟨g, hBad⟩, rfl⟩
  have hCardLe := Nat.card_le_card_of_surjective
    (Subtype.val : badGeneratorsForDistance (F := F) (W := W) (R := R) d →
      Matrix R W F) hSurjective
  have hTotalLe : total ≤ Nat.card Bad := by
    change Nat.card (Matrix R W F) ≤
      Nat.card (badGeneratorsForDistance (F := F) (W := W) (R := R) d)
    exact hCardLe
  exact (not_le_of_gt hBadLt) hTotalLe

/-- The image code generated by the rows of `g`. -/
noncomputable def generatorImage (g : Matrix R W F) :
    Submodule F (Word F W) := by
  classical
  exact LinearMap.range (Matrix.toLin' g.transpose)

omit [Fintype F] [DecidableEq F] [Fintype W] [Fintype R'] in
/-- Membership in the row-generated image has an instance-independent
matrix-vector witness. -/
theorem mem_generatorImage_iff
    (g : Matrix R W F) (c : Word F W) :
    c ∈ generatorImage g ↔
      ∃ a : Word F R, g.transpose.mulVec a = c := by
  classical
  unfold generatorImage
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [Matrix.toLin'_apply]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [Matrix.toLin'_apply]⟩

/-- A chosen linear complement to the generator image. -/
noncomputable def generatorImageComplement (g : Matrix R W F) :
    Submodule F (Word F W) :=
  Classical.choose (Submodule.exists_isCompl (generatorImage g))

omit [Fintype F] [DecidableEq F] [Fintype W] [Fintype R'] in
/-- The chosen complement really is complementary to the generator image. -/
theorem generatorImageComplement_isCompl (g : Matrix R W F) :
    IsCompl (generatorImageComplement g) (generatorImage g) :=
  (Classical.choose_spec
    (Submodule.exists_isCompl (generatorImage g))).symm

/-- A square parity-check matrix whose kernel is exactly the row-generated
image code. Extra zero/dependent rows are harmless for the local argument. -/
noncomputable def generatorImageParityCheck (g : Matrix R W F) : Matrix W W F := by
  classical
  exact LinearMap.toMatrix'
    ((generatorImageComplement g).projection (generatorImage g)
      (generatorImageComplement_isCompl g))

omit [DecidableEq F] [Fintype R'] in
/-- The parity-check-code carrier of the constructed matrix is the image of
the original generator matrix. -/
theorem parityCheckCode_generatorImageParityCheck_carrier
    (g : Matrix R W F) :
    (parityCheckCode (generatorImageParityCheck g)).carrier = generatorImage g := by
  classical
  unfold parityCheckCode generatorImageParityCheck
  rw [Matrix.toLin'_toMatrix', Submodule.ker_projection]

omit [Fintype R'] in
/-- A generator-image distance lower bound transfers to the constructed
parity-check presentation of exactly that image code. -/
theorem parityCheckCode_generatorImageParityCheck_distance
    (g : Matrix R W F) (d : Nat)
    (hImage : ∀ a : Word F R, a ≠ 0 →
      d ≤ HammingWeight (g.transpose.mulVec a)) :
    ∀ c : Word F W,
      c ∈ (parityCheckCode (generatorImageParityCheck g)).carrier →
      c ≠ 0 → d ≤ HammingWeight c := by
  classical
  intro c hc hcNonzero
  rw [parityCheckCode_generatorImageParityCheck_carrier] at hc
  rcases hc with ⟨a, rfl⟩
  rw [Matrix.toLin'_apply]
  apply hImage a
  intro ha
  subst a
  simp at hcNonzero

omit [Fintype F] [Fintype R'] in
/-- Positive image distance forces the generator map to be injective. -/
theorem generatorMap_injective_of_image_distance
    (g : Matrix R W F) (d : Nat) (hPositive : 0 < d)
    (hImage : ∀ a : Word F R, a ≠ 0 →
      d ≤ HammingWeight (g.transpose.mulVec a)) :
    Function.Injective (fun a : Word F R => g.transpose.mulVec a) := by
  intro a b hab
  change g.transpose.mulVec a = g.transpose.mulVec b at hab
  apply sub_eq_zero.mp
  by_contra hne
  have hzero : g.transpose.mulVec (a - b) = 0 := by
    rw [Matrix.mulVec_sub, hab, sub_self]
  have hWeight := hImage (a - b) hne
  rw [hzero, HammingWeight_zero] at hWeight
  omega

omit [Fintype F] [Fintype R'] in
/-- Equivalently, a positive-distance generator has maximal row rank. -/
theorem rank_eq_card_rows_of_image_distance
    (g : Matrix R W F) (d : Nat) (hPositive : 0 < d)
    (hImage : ∀ a : Word F R, a ≠ 0 →
      d ≤ HammingWeight (g.transpose.mulVec a)) :
    g.rank = Fintype.card R := by
  classical
  rw [← Matrix.rank_transpose]
  change Module.finrank F (LinearMap.range (Matrix.toLin' g.transpose)) =
    Fintype.card R
  rw [LinearMap.finrank_range_of_inj
    (by
      intro a b hab
      apply generatorMap_injective_of_image_distance g d hPositive hImage
      simpa only [Matrix.toLin'_apply] using hab)]
  simp

omit [DecidableEq F] [Fintype R'] in
/-- For a fixed candidate product word `x`, the exact PK22 constraint
penalty is the rank of its left syndrome `h' * x` times the number of
independently chosen rows of `h`. -/
theorem card_productKernel_fixed_word_mul_field_pow_rank_eq_total
    (h' : Matrix R' W F) (x : Matrix W W F) :
    Nat.card {h : Matrix R W F // ProductKernel h h' x} *
        (Nat.card F) ^ ((h' * x).rank * Fintype.card R) =
      Nat.card (Matrix R W F) := by
  simpa only [ProductKernel] using
    card_leftProductKernel_mul_field_pow_rank_eq_total (R := R) (h' * x)

omit [DecidableEq F] [Fintype R'] in
/-- Replacing the exact syndrome rank by any certified lower bound only
weakens the finite counting penalty. -/
theorem card_productKernel_fixed_word_mul_field_pow_rankLower_le_total
    (h' : Matrix R' W F) (x : Matrix W W F) (k : Nat)
    (hk : k ≤ (h' * x).rank) :
    Nat.card {h : Matrix R W F // ProductKernel h h' x} *
        (Nat.card F) ^ (k * Fintype.card R) ≤
      Nat.card (Matrix R W F) := by
  have hq : 0 < Nat.card F := Nat.card_pos
  have hExponent : k * Fintype.card R ≤
      (h' * x).rank * Fintype.card R := Nat.mul_le_mul_right _ hk
  have hPow := Nat.pow_le_pow_right hq hExponent
  calc
    Nat.card {h : Matrix R W F // ProductKernel h h' x} *
        (Nat.card F) ^ (k * Fintype.card R) ≤
      Nat.card {h : Matrix R W F // ProductKernel h h' x} *
        (Nat.card F) ^ ((h' * x).rank * Fintype.card R) :=
      Nat.mul_le_mul_left _ hPow
    _ = Nat.card (Matrix R W F) :=
      card_productKernel_fixed_word_mul_field_pow_rank_eq_total h' x

/-- Check matrices admitting a rectangle-sparse witness with a certified
left-syndrome rank lower bound. -/
def badChecksForRectangle
    (h' : Matrix R' W F) (A B : Finset W) (s k : Nat) :=
  {h : Matrix R W F // ∃ x : Matrix W W F,
    restrictedWeight x A B < s ∧ k ≤ (h' * x).rank ∧ ProductKernel h h' x}

noncomputable instance badChecksForRectangleFintype
    (h' : Matrix R' W F) (A B : Finset W) (s k : Nat) :
    Fintype (badChecksForRectangle (R := R) h' A B s k) := by
  classical
  unfold badChecksForRectangle
  infer_instance

/-- Encode a bad check matrix by one chosen ranked sparse witness and the
same check matrix in that witness's product-kernel fiber. -/
noncomputable def badChecksForRectangleEncoding
    (h' : Matrix R' W F) (A B : Finset W) (s k : Nat)
    (h : badChecksForRectangle (R := R) h' A B s k) :
    Σ x : {x : Matrix W W F //
        restrictedWeight x A B < s ∧ k ≤ (h' * x).rank},
      {g : Matrix R W F // ProductKernel g h' x.1} := by
  let x := Classical.choose h.2
  have hx := Classical.choose_spec h.2
  exact ⟨⟨x, hx.1, hx.2.1⟩, ⟨h.1, hx.2.2⟩⟩

omit [Fintype F] [Fintype R] [Fintype R'] in
/-- Choosing a witness does not identify two distinct bad check matrices. -/
theorem badChecksForRectangleEncoding_injective
    (h' : Matrix R' W F) (A B : Finset W) (s k : Nat) :
    Function.Injective
      (badChecksForRectangleEncoding (R := R) h' A B s k) := by
  intro h g heq
  apply Subtype.ext
  exact congrArg (fun z => z.2.1) heq

omit [Fintype R'] in
/-- Finite union bound for one rectangle: the number of bad check matrices,
times the rank penalty, is at most the number of sparse candidate matrices
times the total number of check matrices. -/
theorem card_badChecksForRectangle_mul_rankPenalty_le
    (h' : Matrix R' W F) (A B : Finset W) (s k : Nat) :
    Nat.card (badChecksForRectangle (R := R) h' A B s k) *
        (Nat.card F) ^ (k * Fintype.card R) ≤
      Nat.card {x : Matrix W W F // restrictedWeight x A B < s} *
        Nat.card (Matrix R W F) := by
  classical
  let X := {x : Matrix W W F //
    restrictedWeight x A B < s ∧ k ≤ (h' * x).rank}
  let E := Σ x : X, {g : Matrix R W F // ProductKernel g h' x.1}
  have hEncode : Nat.card (badChecksForRectangle (R := R) h' A B s k) ≤
      Nat.card E := Nat.card_le_card_of_injective
    (badChecksForRectangleEncoding (R := R) h' A B s k)
    (badChecksForRectangleEncoding_injective (R := R) h' A B s k)
  have hFiber (x : X) :
      Nat.card {g : Matrix R W F // ProductKernel g h' x.1} *
          (Nat.card F) ^ (k * Fintype.card R) ≤
        Nat.card (Matrix R W F) :=
    card_productKernel_fixed_word_mul_field_pow_rankLower_le_total
      h' x.1 k x.2.2
  have hSigma : Nat.card E * (Nat.card F) ^ (k * Fintype.card R) ≤
      Nat.card X * Nat.card (Matrix R W F) := by
    rw [Nat.card_sigma, Finset.sum_mul]
    have hSum := Finset.sum_le_card_nsmul Finset.univ
      (fun x : X =>
        Nat.card {g : Matrix R W F // ProductKernel g h' x.1} *
          (Nat.card F) ^ (k * Fintype.card R))
      (Nat.card (Matrix R W F)) (fun x _ => hFiber x)
    simpa [nsmul_eq_mul, Nat.card_eq_fintype_card] using hSum
  have hX : Nat.card X ≤
      Nat.card {x : Matrix W W F // restrictedWeight x A B < s} :=
    Nat.card_le_card_of_injective
      (fun x : X => (⟨x.1, x.2.1⟩ :
        {x : Matrix W W F // restrictedWeight x A B < s}))
      (fun x y hxy => by
        apply Subtype.ext
        exact congrArg (fun z :
          {x : Matrix W W F // restrictedWeight x A B < s} => z.1) hxy)
  exact (Nat.mul_le_mul_right _ hEncode).trans <|
    hSigma.trans (Nat.mul_le_mul_right _ hX)

omit [Fintype R'] in
/-- One-rectangle PK22 union bound after inserting the coarse sparse-matrix
count and the certified syndrome-rank penalty. -/
theorem card_badChecksForRectangle_mul_rankPenalty_le_coarse
    [DecidableEq W]
    (h' : Matrix R' W F) (A B : Finset W) (s k m : Nat)
    (hA : Fintype.card W - m ≤ A.card)
    (hB : Fintype.card W - m ≤ B.card) :
    Nat.card (badChecksForRectangle (R := R) h' A B s k) *
        (Nat.card F) ^ (k * Fintype.card R) ≤
      (s * (A.card * B.card + 1) ^ s *
        (Nat.card F) ^ (2 * m * Fintype.card W + s)) *
          Nat.card (Matrix R W F) := by
  have hBad := card_badChecksForRectangle_mul_rankPenalty_le
    (R := R) h' A B s k
  have hSparse := card_sparseRectangle_lt_le_coarse
    (F := F) A B s m hA hB
  exact hBad.trans (Nat.mul_le_mul_right (Nat.card (Matrix R W F)) hSparse)

/-- Coordinate subsets of the exact rectangle side length `w-m`. -/
def exactRectangleSides (W : Type v) [Fintype W] (m : Nat) :=
  {A : Finset W // A.card = Fintype.card W - m}

/-- Exact rectangle sides are fixed-cardinality subsets of the full
coordinate set. -/
noncomputable def exactRectangleSidesEquivPowersetCard
    (W : Type v) [Fintype W] (m : Nat) :
    exactRectangleSides W m ≃
      (Finset.univ : Finset W).powersetCard (Fintype.card W - m) := by
  classical
  refine
    { toFun := fun A =>
        ⟨A.1, Finset.mem_powersetCard.mpr
          ⟨Finset.subset_univ A.1, A.2⟩⟩
      invFun := fun A =>
        ⟨A.1, (Finset.mem_powersetCard.mp A.2).2⟩
      left_inv := fun A => by apply Subtype.ext; rfl
      right_inv := fun A => by apply Subtype.ext; rfl }

noncomputable instance exactRectangleSidesFintype
    (W : Type v) [Fintype W] (m : Nat) : Fintype (exactRectangleSides W m) := by
  classical
  exact Fintype.ofEquiv
    ((Finset.univ : Finset W).powersetCard (Fintype.card W - m))
    (exactRectangleSidesEquivPowersetCard W m).symm

/-- Number of exact rectangle sides. -/
theorem card_exactRectangleSides (W : Type v) [Fintype W] (m : Nat) :
    Nat.card (exactRectangleSides W m) =
      Nat.choose (Fintype.card W) (Fintype.card W - m) := by
  classical
  rw [Nat.card_congr (exactRectangleSidesEquivPowersetCard W m)]
  simp

/-- Check matrices admitting a ranked sparse witness on at least one exact
`(w-m) × (w-m)` rectangle. -/
def badChecksAllExactRectangles
    (h' : Matrix R' W F) (s m k : Nat) :=
  {h : Matrix R W F // ∃ A B : Finset W,
    A.card = Fintype.card W - m ∧
    B.card = Fintype.card W - m ∧
    ∃ x : Matrix W W F,
      restrictedWeight x A B < s ∧
      k ≤ (h' * x).rank ∧ ProductKernel h h' x}

noncomputable instance badChecksAllExactRectanglesFintype
    (h' : Matrix R' W F) (s m k : Nat) :
    Fintype (badChecksAllExactRectangles (R := R) h' s m k) := by
  classical
  unfold badChecksAllExactRectangles
  infer_instance

/-- Choose one exact rectangle witnessing a globally bad check matrix. -/
noncomputable def badChecksAllExactRectanglesEncoding
    (h' : Matrix R' W F) (s m k : Nat)
    (h : badChecksAllExactRectangles (R := R) h' s m k) :
    Σ A : exactRectangleSides W m,
      Σ B : exactRectangleSides W m,
        badChecksForRectangle (R := R) h' A.1 B.1 s k := by
  let A := Classical.choose h.2
  let hA := Classical.choose_spec h.2
  let B := Classical.choose hA
  let hB := Classical.choose_spec hA
  exact ⟨⟨A, hB.1⟩, ⟨⟨B, hB.2.1⟩, ⟨h.1, hB.2.2⟩⟩⟩

omit [Fintype F] [Fintype R] [Fintype R'] in
/-- The all-rectangle witness encoding retains the check matrix. -/
theorem badChecksAllExactRectanglesEncoding_injective
    (h' : Matrix R' W F) (s m k : Nat) :
    Function.Injective
      (badChecksAllExactRectanglesEncoding (R := R) h' s m k) := by
  intro h g heq
  apply Subtype.ext
  exact congrArg (fun z => z.2.2.1) heq

omit [Fintype R] in
/-- Any low-weight local-minimal product-kernel witness yields an exact
rectangle witness with the integer syndrome-rank threshold supplied by the
PK22 local rank lemma. -/
theorem exists_badChecksAllExactRectangles_of_local_failure
    (h : Matrix R W F) (h' : Matrix R' W F) (d m s k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hRankTarget : 36 * k * s ≤ 5 * d * d)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (A B : Finset W)
    (hLargeA : Fintype.card W - m ≤ A.card)
    (hLargeB : Fintype.card W - m ≤ B.card)
    (hWeight : restrictedWeight x A B < s) :
    ∃ bad : badChecksAllExactRectangles (R := R) h' s m k, bad.1 = h := by
  classical
  obtain ⟨A₀, hA₀A, hA₀Card⟩ :=
    Finset.exists_subset_card_eq hLargeA
  obtain ⟨B₀, hB₀B, hB₀Card⟩ :=
    Finset.exists_subset_card_eq hLargeB
  have hWeight₀ : restrictedWeight x A₀ B₀ < s :=
    (restrictedWeight_mono x hA₀A hB₀B).trans_lt hWeight
  have hRank := local_syndrome_rank_weight_inequality_five_thirtysixths
    h h' d m hPositive hLength hSmallM hDistance hDistance'
      x hx hxNonzero hMinimal A₀ B₀
      (by rw [hA₀Card]) (by rw [hB₀Card])
  have hsPositive : 0 < s := lt_of_le_of_lt (Nat.zero_le _) hWeight₀
  have hChain : 36 * k * s ≤ 36 * (h' * x).rank * s := by
    calc
      36 * k * s ≤ 5 * d * d := hRankTarget
      _ ≤ 36 * (h' * x).rank * restrictedWeight x A₀ B₀ := hRank
      _ ≤ 36 * (h' * x).rank * s :=
        Nat.mul_le_mul_left (36 * (h' * x).rank) (Nat.le_of_lt hWeight₀)
  have hKs : k * s ≤ (h' * x).rank * s := by
    apply (Nat.mul_le_mul_left_iff (by omega : 0 < 36)).mp
    simpa [mul_assoc] using hChain
  have hk : k ≤ (h' * x).rank :=
    Nat.le_of_mul_le_mul_right hKs hsPositive
  refine ⟨⟨h, ?_⟩, rfl⟩
  exact ⟨A₀, B₀, hA₀Card, hB₀Card, x, hWeight₀, hk, hx⟩

omit [Fintype R'] in
/-- Full finite PK22 union bound over all exact large rectangles. The squared
binomial coefficient is the exact number of choices for `A` and `B`. -/
theorem card_badChecksAllExactRectangles_mul_rankPenalty_le
    [DecidableEq W]
    (h' : Matrix R' W F) (s m k : Nat) :
    Nat.card (badChecksAllExactRectangles (R := R) h' s m k) *
        (Nat.card F) ^ (k * Fintype.card R) ≤
      (Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s)) *
        Nat.card (Matrix R W F) := by
  classical
  let penalty := (Nat.card F) ^ (k * Fintype.card R)
  let sparseBound :=
    s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
      (Nat.card F) ^ (2 * m * Fintype.card W + s)
  let total := Nat.card (Matrix R W F)
  have hEncode :
      Nat.card (badChecksAllExactRectangles (R := R) h' s m k) ≤
        Nat.card (Σ A : exactRectangleSides W m,
          Σ B : exactRectangleSides W m,
            badChecksForRectangle (R := R) h' A.1 B.1 s k) :=
    Nat.card_le_card_of_injective
      (badChecksAllExactRectanglesEncoding (R := R) h' s m k)
      (badChecksAllExactRectanglesEncoding_injective (R := R) h' s m k)
  have hEach (A B : exactRectangleSides W m) :
      Nat.card (badChecksForRectangle (R := R) h' A.1 B.1 s k) * penalty ≤
        sparseBound * total := by
    have hA : Fintype.card W - m ≤ A.1.card := by rw [A.2]
    have hB : Fintype.card W - m ≤ B.1.card := by rw [B.2]
    simpa [penalty, sparseBound, total, A.2, B.2] using
      card_badChecksForRectangle_mul_rankPenalty_le_coarse
        (R := R) h' A.1 B.1 s k m hA hB
  have hSigma :
      Nat.card (Σ A : exactRectangleSides W m,
          Σ B : exactRectangleSides W m,
            badChecksForRectangle (R := R) h' A.1 B.1 s k) * penalty ≤
      Nat.card (exactRectangleSides W m) *
        Nat.card (exactRectangleSides W m) * (sparseBound * total) := by
    rw [Nat.card_sigma, Finset.sum_mul]
    simp_rw [Nat.card_sigma, Finset.sum_mul]
    calc
      (∑ A : exactRectangleSides W m, ∑ B : exactRectangleSides W m,
          Nat.card (badChecksForRectangle (R := R) h' A.1 B.1 s k) * penalty) ≤
          ∑ _A : exactRectangleSides W m,
            ∑ _B : exactRectangleSides W m, sparseBound * total := by
            apply Finset.sum_le_sum
            intro A hA
            apply Finset.sum_le_sum
            intro B hB
            exact hEach A B
      _ = Nat.card (exactRectangleSides W m) *
          Nat.card (exactRectangleSides W m) * (sparseBound * total) := by
        simp [Nat.card_eq_fintype_card, mul_assoc]
  have hAll := (Nat.mul_le_mul_right penalty hEncode).trans hSigma
  have hSideCard := card_exactRectangleSides W m
  rw [hSideCard] at hAll
  simpa [penalty, sparseBound, total, pow_two, mul_assoc] using hAll

/-- Check matrices that fail either the classical distance target or the
ranked sparse-witness exclusion needed for product expansion. -/
def badChecksDistanceOrRectangles
    (h' : Matrix R' W F) (d s m k : Nat) :=
  {h : Matrix R W F //
    (∃ c : Word F W, c ≠ 0 ∧ HammingWeight c < d ∧ h.mulVec c = 0) ∨
    (∃ A B : Finset W,
      A.card = Fintype.card W - m ∧
      B.card = Fintype.card W - m ∧
      ∃ x : Matrix W W F,
        restrictedWeight x A B < s ∧
        k ≤ (h' * x).rank ∧ ProductKernel h h' x)}

noncomputable instance badChecksDistanceOrRectanglesFintype
    (h' : Matrix R' W F) (d s m k : Nat) :
    Fintype (badChecksDistanceOrRectangles (R := R) h' d s m k) := by
  classical
  unfold badChecksDistanceOrRectangles
  infer_instance

/-- Split a check that is bad for either reason into one of the two bad
subtypes, retaining the underlying matrix in both branches. -/
noncomputable def badChecksDistanceOrRectanglesEncoding
    (h' : Matrix R' W F) (d s m k : Nat)
    (h : badChecksDistanceOrRectangles (R := R) h' d s m k) :
    badChecksForDistance (F := F) (W := W) (R := R) d ⊕
      badChecksAllExactRectangles (R := R) h' s m k := by
  classical
  by_cases hd : ∃ c : Word F W,
      c ≠ 0 ∧ HammingWeight c < d ∧ h.1.mulVec c = 0
  · exact Sum.inl ⟨h.1, hd⟩
  · exact Sum.inr ⟨h.1, h.2.resolve_left hd⟩

omit [Fintype R'] in
/-- The either-bad encoding retains the underlying check matrix. -/
theorem badChecksDistanceOrRectanglesEncoding_val
    (h' : Matrix R' W F) (d s m k : Nat)
    (h : badChecksDistanceOrRectangles (R := R) h' d s m k) :
    Sum.elim Subtype.val Subtype.val
      (badChecksDistanceOrRectanglesEncoding (R := R) h' d s m k h) = h.1 := by
  classical
  unfold badChecksDistanceOrRectanglesEncoding
  split <;> rfl

omit [Fintype R'] in
/-- The either-bad encoding is injective. -/
theorem badChecksDistanceOrRectanglesEncoding_injective
    (h' : Matrix R' W F) (d s m k : Nat) :
    Function.Injective
      (badChecksDistanceOrRectanglesEncoding (R := R) h' d s m k) := by
  intro h g heq
  apply Subtype.ext
  have hval := congrArg (Sum.elim Subtype.val Subtype.val) heq
  simpa only [badChecksDistanceOrRectanglesEncoding_val] using hval

omit [Fintype R'] in
/-- Cardinal union bound for the two bad-check events. -/
theorem card_badChecksDistanceOrRectangles_le_add
    (h' : Matrix R' W F) (d s m k : Nat) :
    Nat.card (badChecksDistanceOrRectangles (R := R) h' d s m k) ≤
      Nat.card (badChecksForDistance (F := F) (W := W) (R := R) d) +
        Nat.card (badChecksAllExactRectangles (R := R) h' s m k) := by
  classical
  calc
    Nat.card (badChecksDistanceOrRectangles (R := R) h' d s m k) ≤
        Nat.card
          (badChecksForDistance (F := F) (W := W) (R := R) d ⊕
            badChecksAllExactRectangles (R := R) h' s m k) :=
      Nat.card_le_card_of_injective
        (badChecksDistanceOrRectanglesEncoding (R := R) h' d s m k)
        (badChecksDistanceOrRectanglesEncoding_injective
          (R := R) h' d s m k)
    _ = Nat.card (badChecksForDistance (F := F) (W := W) (R := R) d) +
        Nat.card (badChecksAllExactRectangles (R := R) h' s m k) := by
      rw [Nat.card_sum]

/-- Check matrices that fail kernel distance, row-image distance, or the
ranked sparse-witness exclusion. The row-image event is included because the
PK22 local-star proof needs the first check to have maximal row rank. -/
def badChecksDistanceImageOrRectangles
    (h' : Matrix R' W F) (d s m k : Nat) :=
  {h : Matrix R W F //
    (∃ c : Word F W, c ≠ 0 ∧ HammingWeight c < d ∧ h.mulVec c = 0) ∨
    (∃ a : Word F R,
      a ≠ 0 ∧ HammingWeight (h.transpose.mulVec a) < d) ∨
    (∃ A B : Finset W,
      A.card = Fintype.card W - m ∧
      B.card = Fintype.card W - m ∧
      ∃ x : Matrix W W F,
        restrictedWeight x A B < s ∧
        k ≤ (h' * x).rank ∧ ProductKernel h h' x)}

noncomputable instance badChecksDistanceImageOrRectanglesFintype
    (h' : Matrix R' W F) (d s m k : Nat) :
    Fintype (badChecksDistanceImageOrRectangles (R := R) h' d s m k) := by
  classical
  unfold badChecksDistanceImageOrRectangles
  infer_instance

/-- Encode each of the three bad events while retaining its matrix. -/
noncomputable def badChecksDistanceImageOrRectanglesEncoding
    (h' : Matrix R' W F) (d s m k : Nat)
    (h : badChecksDistanceImageOrRectangles (R := R) h' d s m k) :
    badChecksForDistance (F := F) (W := W) (R := R) d ⊕
      (badGeneratorsForDistance (F := F) (W := W) (R := R) d ⊕
        badChecksAllExactRectangles (R := R) h' s m k) := by
  classical
  by_cases hd : ∃ c : Word F W,
      c ≠ 0 ∧ HammingWeight c < d ∧ h.1.mulVec c = 0
  · exact Sum.inl ⟨h.1, hd⟩
  · by_cases hi : ∃ a : Word F R,
        a ≠ 0 ∧ HammingWeight (h.1.transpose.mulVec a) < d
    · exact Sum.inr (Sum.inl ⟨h.1, hi⟩)
    · exact Sum.inr (Sum.inr ⟨h.1,
        (h.2.resolve_left hd).resolve_left hi⟩)

omit [Fintype R'] in
theorem badChecksDistanceImageOrRectanglesEncoding_val
    (h' : Matrix R' W F) (d s m k : Nat)
    (h : badChecksDistanceImageOrRectangles (R := R) h' d s m k) :
    Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val)
      (badChecksDistanceImageOrRectanglesEncoding
        (R := R) h' d s m k h) = h.1 := by
  classical
  unfold badChecksDistanceImageOrRectanglesEncoding
  split
  · rfl
  · split <;> rfl

omit [Fintype R'] in
theorem badChecksDistanceImageOrRectanglesEncoding_injective
    (h' : Matrix R' W F) (d s m k : Nat) :
    Function.Injective
      (badChecksDistanceImageOrRectanglesEncoding
        (R := R) h' d s m k) := by
  intro h g heq
  apply Subtype.ext
  have hval := congrArg
    (Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val)) heq
  simpa only [badChecksDistanceImageOrRectanglesEncoding_val] using hval

omit [Fintype R'] in
/-- Three-event union bound for a random first local check. -/
theorem card_badChecksDistanceImageOrRectangles_le_add
    (h' : Matrix R' W F) (d s m k : Nat) :
    Nat.card (badChecksDistanceImageOrRectangles (R := R) h' d s m k) ≤
      Nat.card (badChecksForDistance (F := F) (W := W) (R := R) d) +
      Nat.card (badGeneratorsForDistance (F := F) (W := W) (R := R) d) +
      Nat.card (badChecksAllExactRectangles (R := R) h' s m k) := by
  classical
  calc
    Nat.card (badChecksDistanceImageOrRectangles (R := R) h' d s m k) ≤
        Nat.card
          (badChecksForDistance (F := F) (W := W) (R := R) d ⊕
            (badGeneratorsForDistance (F := F) (W := W) (R := R) d ⊕
              badChecksAllExactRectangles (R := R) h' s m k)) :=
      Nat.card_le_card_of_injective
        (badChecksDistanceImageOrRectanglesEncoding
          (R := R) h' d s m k)
        (badChecksDistanceImageOrRectanglesEncoding_injective
          (R := R) h' d s m k)
    _ = Nat.card (badChecksForDistance (F := F) (W := W) (R := R) d) +
        Nat.card (badGeneratorsForDistance (F := F) (W := W) (R := R) d) +
        Nat.card (badChecksAllExactRectangles (R := R) h' s m k) := by
      rw [Nat.card_sum, Nat.card_sum]
      simp [Nat.add_assoc]

omit [Fintype R'] in
set_option maxHeartbeats 800000 in
/-- Simultaneous random-check existence with the full-rank condition needed
by the local-star syndrome lift. The selected matrix has both kernel distance
and transpose-image distance at least d, hence maximal row rank for d > 0,
and excludes every ranked sparse exact-rectangle witness. -/
theorem exists_fullRank_check_with_distance_without_ranked_sparse_exactRectangle_witness
    [DecidableEq W]
    (h' : Matrix R' W F) (d s m k : Nat)
    (hDistanceFactor :
      3 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R)
    (hImageFactor :
      3 * ((Nat.card F) ^ Fintype.card R *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) <
        (Nat.card F) ^ Fintype.card W)
    (hRectangleFactor :
      3 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R)) :
    ∃ h : Matrix R W F,
      (∀ c : Word F W, h.mulVec c = 0 → c ≠ 0 →
        d ≤ HammingWeight c) ∧
      (∀ a : Word F R, a ≠ 0 →
        d ≤ HammingWeight (h.transpose.mulVec a)) ∧
      ¬∃ A B : Finset W,
        A.card = Fintype.card W - m ∧
        B.card = Fintype.card W - m ∧
        ∃ x : Matrix W W F,
          restrictedWeight x A B < s ∧
          k ≤ (h' * x).rank ∧ ProductKernel h h' x := by
  classical
  let distanceFactor := ∑ t : Fin d,
    Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1
  let distancePenalty := (Nat.card F) ^ Fintype.card R
  let imageFactor := (Nat.card F) ^ Fintype.card R * distanceFactor
  let imagePenalty := (Nat.card F) ^ Fintype.card W
  let rectangleFactor :=
    (Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
      (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
        (Nat.card F) ^ (2 * m * Fintype.card W + s))
  let rectanglePenalty := (Nat.card F) ^ (k * Fintype.card R)
  let distanceBad :=
    Nat.card (badChecksForDistance (F := F) (W := W) (R := R) d)
  let imageBad :=
    Nat.card (badGeneratorsForDistance (F := F) (W := W) (R := R) d)
  let rectangleBad :=
    Nat.card (badChecksAllExactRectangles (R := R) h' s m k)
  let total := Nat.card (Matrix R W F)
  have hTotalPositive : 0 < total := Nat.card_pos
  have hDistanceBound : distanceBad * distancePenalty ≤
      distanceFactor * total := by
    simpa [distanceBad, distancePenalty, distanceFactor, total] using
      card_badChecksForDistance_mul_field_pow_rows_le_choose_sum
        (F := F) (W := W) (R := R) d
  have hImageBound : imageBad * imagePenalty ≤ imageFactor * total := by
    simpa [imageBad, imagePenalty, imageFactor, distanceFactor, total] using
      card_badGeneratorsForDistance_mul_field_pow_length_le_choose_sum
        (F := F) (W := W) (R := R) d
  have hRectangleBound : rectangleBad * rectanglePenalty ≤
      rectangleFactor * total := by
    simpa [rectangleBad, rectanglePenalty, rectangleFactor, total] using
      card_badChecksAllExactRectangles_mul_rankPenalty_le
        (R := R) h' s m k
  have hDistanceThird : 3 * distanceBad < total := by
    have hScaled : (3 * distanceBad) * distancePenalty <
        total * distancePenalty := by
      calc
        (3 * distanceBad) * distancePenalty =
            3 * (distanceBad * distancePenalty) := by simp [mul_assoc]
        _ ≤ 3 * (distanceFactor * total) :=
          Nat.mul_le_mul_left 3 hDistanceBound
        _ = (3 * distanceFactor) * total := by simp [mul_assoc]
        _ < distancePenalty * total :=
          Nat.mul_lt_mul_of_pos_right
            (by simpa [distanceFactor, distancePenalty] using hDistanceFactor)
            hTotalPositive
        _ = total * distancePenalty := Nat.mul_comm _ _
    exact Nat.lt_of_mul_lt_mul_right hScaled
  have hImageThird : 3 * imageBad < total := by
    have hScaled : (3 * imageBad) * imagePenalty <
        total * imagePenalty := by
      calc
        (3 * imageBad) * imagePenalty =
            3 * (imageBad * imagePenalty) := by simp [mul_assoc]
        _ ≤ 3 * (imageFactor * total) :=
          Nat.mul_le_mul_left 3 hImageBound
        _ = (3 * imageFactor) * total := by simp [mul_assoc]
        _ < imagePenalty * total :=
          Nat.mul_lt_mul_of_pos_right
            (by simpa [imageFactor, imagePenalty, distanceFactor] using
              hImageFactor) hTotalPositive
        _ = total * imagePenalty := Nat.mul_comm _ _
    exact Nat.lt_of_mul_lt_mul_right hScaled
  have hRectangleThird : 3 * rectangleBad < total := by
    have hScaled : (3 * rectangleBad) * rectanglePenalty <
        total * rectanglePenalty := by
      calc
        (3 * rectangleBad) * rectanglePenalty =
            3 * (rectangleBad * rectanglePenalty) := by simp [mul_assoc]
        _ ≤ 3 * (rectangleFactor * total) :=
          Nat.mul_le_mul_left 3 hRectangleBound
        _ = (3 * rectangleFactor) * total := by simp [mul_assoc]
        _ < rectanglePenalty * total :=
          Nat.mul_lt_mul_of_pos_right
            (by simpa [rectangleFactor, rectanglePenalty] using hRectangleFactor)
            hTotalPositive
        _ = total * rectanglePenalty := Nat.mul_comm _ _
    exact Nat.lt_of_mul_lt_mul_right hScaled
  have hBadLt : Nat.card
      (badChecksDistanceImageOrRectangles (R := R) h' d s m k) < total :=
    (card_badChecksDistanceImageOrRectangles_le_add
      (R := R) h' d s m k).trans_lt (by omega)
  have hExists : ∃ h : Matrix R W F,
      ¬((∃ c : Word F W,
          c ≠ 0 ∧ HammingWeight c < d ∧ h.mulVec c = 0) ∨
        (∃ a : Word F R,
          a ≠ 0 ∧ HammingWeight (h.transpose.mulVec a) < d) ∨
        (∃ A B : Finset W,
          A.card = Fintype.card W - m ∧
          B.card = Fintype.card W - m ∧
          ∃ x : Matrix W W F,
            restrictedWeight x A B < s ∧
            k ≤ (h' * x).rank ∧ ProductKernel h h' x)) := by
    by_contra hNo
    have hSurjective : Function.Surjective
        (Subtype.val :
          badChecksDistanceImageOrRectangles (R := R) h' d s m k →
            Matrix R W F) := by
      intro h
      have hBad :
          (∃ c : Word F W,
            c ≠ 0 ∧ HammingWeight c < d ∧ h.mulVec c = 0) ∨
          (∃ a : Word F R,
            a ≠ 0 ∧ HammingWeight (h.transpose.mulVec a) < d) ∨
          (∃ A B : Finset W,
            A.card = Fintype.card W - m ∧
            B.card = Fintype.card W - m ∧
            ∃ x : Matrix W W F,
              restrictedWeight x A B < s ∧
              k ≤ (h' * x).rank ∧ ProductKernel h h' x) := by
        by_contra hGood
        exact hNo ⟨h, hGood⟩
      exact ⟨⟨h, hBad⟩, rfl⟩
    have hCardLe := Nat.card_le_card_of_surjective
      (Subtype.val :
        badChecksDistanceImageOrRectangles (R := R) h' d s m k →
          Matrix R W F) hSurjective
    have hTotalLe : total ≤ Nat.card
        (badChecksDistanceImageOrRectangles (R := R) h' d s m k) := by
      dsimp only [total]
      exact hCardLe
    exact (not_le_of_gt hBadLt) hTotalLe
  obtain ⟨h, hGood⟩ := hExists
  have hDistanceGood := (not_or.mp hGood).1
  have hRestGood := (not_or.mp hGood).2
  have hImageGood := (not_or.mp hRestGood).1
  have hRectangleGood := (not_or.mp hRestGood).2
  refine ⟨h, ?_, ?_, hRectangleGood⟩
  · intro c hcKernel hcNonzero
    exact Nat.le_of_not_gt (fun hcWeight =>
      hDistanceGood ⟨c, hcNonzero, hcWeight, hcKernel⟩)
  · intro a haNonzero
    exact Nat.le_of_not_gt (fun haWeight =>
      hImageGood ⟨a, haNonzero, haWeight⟩)

omit [Fintype R'] in
set_option maxHeartbeats 800000 in
/-- Simultaneous finite-field existence: if both union factors are below
half of their respective penalties, one check matrix has classical distance
at least `d` and has no ranked sparse witness on any exact large rectangle. -/
theorem exists_check_with_distance_without_ranked_sparse_exactRectangle_witness
    [DecidableEq W]
    (h' : Matrix R' W F) (d s m k : Nat)
    (hDistanceFactor :
      2 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R)
    (hRectangleFactor :
      2 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R)) :
    ∃ h : Matrix R W F,
      (∀ c : Word F W, h.mulVec c = 0 → c ≠ 0 → d ≤ HammingWeight c) ∧
      ¬∃ A B : Finset W,
        A.card = Fintype.card W - m ∧
        B.card = Fintype.card W - m ∧
        ∃ x : Matrix W W F,
          restrictedWeight x A B < s ∧
          k ≤ (h' * x).rank ∧ ProductKernel h h' x := by
  classical
  let distanceFactor := ∑ t : Fin d,
    Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1
  let distancePenalty := (Nat.card F) ^ Fintype.card R
  let rectangleFactor :=
    (Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
      (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
        (Nat.card F) ^ (2 * m * Fintype.card W + s))
  let rectanglePenalty := (Nat.card F) ^ (k * Fintype.card R)
  let distanceBad :=
    Nat.card (badChecksForDistance (F := F) (W := W) (R := R) d)
  let rectangleBad :=
    Nat.card (badChecksAllExactRectangles (R := R) h' s m k)
  let total := Nat.card (Matrix R W F)
  have hTotalPositive : 0 < total := Nat.card_pos
  have hDistanceBound : distanceBad * distancePenalty ≤ distanceFactor * total := by
    simpa [distanceBad, distancePenalty, distanceFactor, total] using
      card_badChecksForDistance_mul_field_pow_rows_le_choose_sum
        (F := F) (W := W) (R := R) d
  have hRectangleBound : rectangleBad * rectanglePenalty ≤
      rectangleFactor * total := by
    simpa [rectangleBad, rectanglePenalty, rectangleFactor, total] using
      card_badChecksAllExactRectangles_mul_rankPenalty_le
        (R := R) h' s m k
  have hDistanceHalf : 2 * distanceBad < total := by
    have hScaled : (2 * distanceBad) * distancePenalty < total * distancePenalty := by
      calc
        (2 * distanceBad) * distancePenalty =
            2 * (distanceBad * distancePenalty) := by simp [mul_assoc]
        _ ≤ 2 * (distanceFactor * total) := Nat.mul_le_mul_left 2 hDistanceBound
        _ = (2 * distanceFactor) * total := by simp [mul_assoc]
        _ < distancePenalty * total :=
          Nat.mul_lt_mul_of_pos_right (by simpa [distanceFactor, distancePenalty] using
            hDistanceFactor) hTotalPositive
        _ = total * distancePenalty := Nat.mul_comm _ _
    exact Nat.lt_of_mul_lt_mul_right hScaled
  have hRectangleHalf : 2 * rectangleBad < total := by
    have hScaled : (2 * rectangleBad) * rectanglePenalty < total * rectanglePenalty := by
      calc
        (2 * rectangleBad) * rectanglePenalty =
            2 * (rectangleBad * rectanglePenalty) := by simp [mul_assoc]
        _ ≤ 2 * (rectangleFactor * total) := Nat.mul_le_mul_left 2 hRectangleBound
        _ = (2 * rectangleFactor) * total := by simp [mul_assoc]
        _ < rectanglePenalty * total :=
          Nat.mul_lt_mul_of_pos_right
            (by simpa [rectangleFactor, rectanglePenalty] using hRectangleFactor)
            hTotalPositive
        _ = total * rectanglePenalty := Nat.mul_comm _ _
    exact Nat.lt_of_mul_lt_mul_right hScaled
  have hBadLt :
      Nat.card (badChecksDistanceOrRectangles (R := R) h' d s m k) < total :=
    (card_badChecksDistanceOrRectangles_le_add
      (R := R) h' d s m k).trans_lt (by omega)
  have hExists : ∃ h : Matrix R W F,
      ¬((∃ c : Word F W,
          c ≠ 0 ∧ HammingWeight c < d ∧ h.mulVec c = 0) ∨
        (∃ A B : Finset W,
          A.card = Fintype.card W - m ∧
          B.card = Fintype.card W - m ∧
          ∃ x : Matrix W W F,
            restrictedWeight x A B < s ∧
            k ≤ (h' * x).rank ∧ ProductKernel h h' x)) := by
    by_contra hNo
    have hSurjective : Function.Surjective
        (Subtype.val : badChecksDistanceOrRectangles (R := R) h' d s m k →
          Matrix R W F) := by
      intro h
      have hBad :
          (∃ c : Word F W,
            c ≠ 0 ∧ HammingWeight c < d ∧ h.mulVec c = 0) ∨
          (∃ A B : Finset W,
            A.card = Fintype.card W - m ∧
            B.card = Fintype.card W - m ∧
            ∃ x : Matrix W W F,
              restrictedWeight x A B < s ∧
              k ≤ (h' * x).rank ∧ ProductKernel h h' x) := by
        by_contra hGood
        exact hNo ⟨h, hGood⟩
      exact ⟨⟨h, hBad⟩, rfl⟩
    have hCardLe := Nat.card_le_card_of_surjective
      (Subtype.val : badChecksDistanceOrRectangles (R := R) h' d s m k →
        Matrix R W F) hSurjective
    have hTotalLe : total ≤
        Nat.card (badChecksDistanceOrRectangles (R := R) h' d s m k) := by
      dsimp only [total]
      exact hCardLe
    exact (not_le_of_gt hBadLt) hTotalLe
  obtain ⟨h, hGood⟩ := hExists
  have hDistanceGood := (not_or.mp hGood).1
  have hRectangleGood := (not_or.mp hGood).2
  refine ⟨h, ?_, hRectangleGood⟩
  intro c hcKernel hcNonzero
  exact Nat.le_of_not_gt (fun hcWeight =>
    hDistanceGood ⟨c, hcNonzero, hcWeight, hcKernel⟩)

omit [Fintype R] [Fintype R'] in
/-- A kernel-weight lower bound is exactly the distance hypothesis used by
the parity-check-code formulation of product expansion. -/
theorem parityCheckCode_distance_of_mulVec_distance
    (h : Matrix R W F) (d : Nat)
    (hDistance : ∀ c : Word F W,
      h.mulVec c = 0 → c ≠ 0 → d ≤ HammingWeight c) :
    ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c := by
  classical
  intro c hc hcNonzero
  apply hDistance c
  change Matrix.toLin' h c = 0 at hc
  simpa only [Matrix.toLin'_apply] using hc
  exact hcNonzero

omit [Fintype R'] in
/-- If the finite union factor is strictly smaller than the rank penalty,
there is a check matrix with no ranked sparse witness on any exact large
rectangle. -/
theorem exists_check_without_ranked_sparse_exactRectangle_witness
    [DecidableEq W]
    (h' : Matrix R' W F) (s m k : Nat)
    (hFactor :
      (Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s)) <
        (Nat.card F) ^ (k * Fintype.card R)) :
    ∃ h : Matrix R W F,
      ¬∃ A B : Finset W,
        A.card = Fintype.card W - m ∧
        B.card = Fintype.card W - m ∧
        ∃ x : Matrix W W F,
          restrictedWeight x A B < s ∧
          k ≤ (h' * x).rank ∧ ProductKernel h h' x := by
  classical
  let Bad := badChecksAllExactRectangles (R := R) h' s m k
  let factor :=
    (Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
      (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
        (Nat.card F) ^ (2 * m * Fintype.card W + s))
  let penalty := (Nat.card F) ^ (k * Fintype.card R)
  let total := Nat.card (Matrix R W F)
  have hBound : Nat.card Bad * penalty ≤ factor * total := by
    simpa [Bad, factor, penalty, total] using
      card_badChecksAllExactRectangles_mul_rankPenalty_le
        (R := R) h' s m k
  have hTotalPositive : 0 < total := Nat.card_pos
  have hBadLt : Nat.card Bad < total := by
    by_contra hNot
    have hTotalLe : total ≤ Nat.card Bad := le_of_not_gt hNot
    have hContradiction : total * penalty < penalty * total :=
      (Nat.mul_le_mul_right penalty hTotalLe).trans_lt <|
        hBound.trans_lt <| by
          simpa [factor, penalty, total] using
            Nat.mul_lt_mul_of_pos_right hFactor hTotalPositive
    simp [mul_comm] at hContradiction
  by_contra hNoGood
  push Not at hNoGood
  have hSurjective : Function.Surjective
      (Subtype.val : badChecksAllExactRectangles (R := R) h' s m k →
        Matrix R W F) := by
    intro h
    exact ⟨⟨h, hNoGood h⟩, rfl⟩
  have hCardLe : Fintype.card (Matrix R W F) ≤
      Fintype.card (badChecksAllExactRectangles (R := R) h' s m k) :=
    Fintype.card_le_of_surjective
      (Subtype.val : badChecksAllExactRectangles (R := R) h' s m k →
        Matrix R W F) hSurjective
  have hTotalLeBad : total ≤ Nat.card Bad := by
    change Nat.card (Matrix R W F) ≤
      Nat.card (badChecksAllExactRectangles (R := R) h' s m k)
    simpa only [Nat.card_eq_fintype_card] using hCardLe
  exact (not_le_of_gt hBadLt) hTotalLeBad

omit [Fintype R] in
/-- Absence of ranked sparse exact-rectangle witnesses, together with the
classical distance hypotheses used by the local rank lemma, gives the actual
PK22 product-expansion predicate. -/
theorem productExpanding_of_no_ranked_sparse_exactRectangle_witness
    (h : Matrix R W F) (h' : Matrix R' W F) (d m s k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hRankTarget : 36 * k * s ≤ 5 * d * d)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hNoBad : ¬∃ A B : Finset W,
      A.card = Fintype.card W - m ∧
      B.card = Fintype.card W - m ∧
      ∃ x : Matrix W W F,
        restrictedWeight x A B < s ∧
        k ≤ (h' * x).rank ∧ ProductKernel h h' x) :
    ProductExpanding h h' s m
      ((d : ℝ) / (3 * (Fintype.card W : ℝ))) := by
  have hwPositiveNat : 0 < Fintype.card W := hPositive.trans_le hLength
  have hwPositive : (0 : ℝ) < Fintype.card W := by exact_mod_cast hwPositiveNat
  have hBeta :
      ((d : ℝ) / (3 * (Fintype.card W : ℝ))) * Fintype.card W =
        (d : ℝ) / 3 := by
    field_simp
  intro x hx hxNonzero hMinimal A B hLargeA hLargeB
  rw [hBeta] at hMinimal
  by_contra hNotWeight
  have hWeight : restrictedWeight x A B < s := Nat.lt_of_not_ge hNotWeight
  obtain ⟨bad, hbad⟩ := exists_badChecksAllExactRectangles_of_local_failure
    h h' d m s k hPositive hLength hSmallM hRankTarget
      hDistance hDistance' x hx hxNonzero hMinimal A B hLargeA hLargeB hWeight
  subst hbad
  exact hNoBad bad.2

set_option maxHeartbeats 800000 in
/-- Complete finite random-local step of the PK22 argument. Under the two
explicit finite union inequalities and the deterministic integer parameter
conditions, one check matrix simultaneously has classical distance `d` and
forms a product-expanding pair with the fixed check matrix `h'`. -/
theorem exists_distance_and_productExpanding_check
    [DecidableEq W]
    (h' : Matrix R' W F) (d s m k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hRankTarget : 36 * k * s ≤ 5 * d * d)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistanceFactor :
      2 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R)
    (hRectangleFactor :
      2 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R)) :
    ∃ h : Matrix R W F,
      (∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      ProductExpanding h h' s m
        ((d : ℝ) / (3 * (Fintype.card W : ℝ))) := by
  obtain ⟨h, hKernelDistance, hNoBad⟩ :=
    exists_check_with_distance_without_ranked_sparse_exactRectangle_witness
      (R := R) h' d s m k hDistanceFactor hRectangleFactor
  have hDistance := parityCheckCode_distance_of_mulVec_distance h d hKernelDistance
  exact ⟨h, hDistance,
    productExpanding_of_no_ranked_sparse_exactRectangle_witness
      h h' d m s k hPositive hLength hSmallM hRankTarget
        hDistance hDistance' hNoBad⟩

set_option maxHeartbeats 800000 in
/-- Source-aligned random local-code pair. The first matrix `h` is used as a
parity check. The second matrix `g'` is used as a generator; its row image is
presented to `ProductExpanding` by the constructed parity check with exactly
that kernel. Both component codes have distance at least `d`, and `g'` has
maximal row rank when `d > 0`. -/
theorem exists_generator_check_productExpanding_pair
    [DecidableEq W]
    (d s m k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hRankTarget : 36 * k * s ≤ 5 * d * d)
    (hGeneratorFactor :
      (Nat.card F) ^ Fintype.card R' *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card W)
    (hCheckDistanceFactor :
      2 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R)
    (hRectangleFactor :
      2 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R)) :
    ∃ (g' : Matrix R' W F) (h : Matrix R W F),
      g'.rank = Fintype.card R' ∧
      (∀ c : Word F W,
        c ∈ (parityCheckCode (generatorImageParityCheck g')).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      (∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      ProductExpanding h (generatorImageParityCheck g') s m
        ((d : ℝ) / (3 * (Fintype.card W : ℝ))) := by
  obtain ⟨g', hImage⟩ := exists_generator_with_image_distance
    (F := F) (W := W) (R := R') d hGeneratorFactor
  have hGeneratorRank :=
    rank_eq_card_rows_of_image_distance g' d hPositive hImage
  have hImageDistance :=
    parityCheckCode_generatorImageParityCheck_distance g' d hImage
  obtain ⟨h, hCheckDistance, hExpand⟩ :=
    exists_distance_and_productExpanding_check
      (R := R) (generatorImageParityCheck g') d s m k
      hPositive hLength hSmallM hRankTarget hImageDistance
      hCheckDistanceFactor hRectangleFactor
  exact ⟨g', h, hGeneratorRank, hImageDistance, hCheckDistance, hExpand⟩

set_option maxHeartbeats 800000 in
/-- Random first-check construction with the additional maximal-row-rank
certificate consumed by the concrete Tanner-star syndrome lift. -/
theorem exists_fullRank_distance_and_productExpanding_check
    [DecidableEq W]
    (h' : Matrix R' W F) (d s m k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hRankTarget : 36 * k * s ≤ 5 * d * d)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistanceFactor :
      3 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R)
    (hImageFactor :
      3 * ((Nat.card F) ^ Fintype.card R *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) <
        (Nat.card F) ^ Fintype.card W)
    (hRectangleFactor :
      3 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R)) :
    ∃ h : Matrix R W F,
      h.rank = Fintype.card R ∧
      (∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      ProductExpanding h h' s m
        ((d : ℝ) / (3 * (Fintype.card W : ℝ))) := by
  obtain ⟨h, hKernelDistance, hImageDistance, hNoBad⟩ :=
    exists_fullRank_check_with_distance_without_ranked_sparse_exactRectangle_witness
      (R := R) h' d s m k hDistanceFactor hImageFactor hRectangleFactor
  have hDistance := parityCheckCode_distance_of_mulVec_distance
    h d hKernelDistance
  have hRank := rank_eq_card_rows_of_image_distance
    h d hPositive hImageDistance
  exact ⟨h, hRank, hDistance,
    productExpanding_of_no_ranked_sparse_exactRectangle_witness
      h h' d m s k hPositive hLength hSmallM hRankTarget
        hDistance hDistance' hNoBad⟩

set_option maxHeartbeats 800000 in
/-- Source-aligned random local pair with maximal row rank on both the
generator matrix g' and the first parity check h. This is the exact local
package required by the concrete PK22 active-vertex theorem. -/
theorem exists_fullRank_generator_check_productExpanding_pair
    [DecidableEq W]
    (d s m k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hRankTarget : 36 * k * s ≤ 5 * d * d)
    (hGeneratorFactor :
      (Nat.card F) ^ Fintype.card R' *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card W)
    (hCheckDistanceFactor :
      3 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R)
    (hCheckImageFactor :
      3 * ((Nat.card F) ^ Fintype.card R *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) <
        (Nat.card F) ^ Fintype.card W)
    (hRectangleFactor :
      3 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R)) :
    ∃ (g' : Matrix R' W F) (h : Matrix R W F),
      g'.rank = Fintype.card R' ∧
      h.rank = Fintype.card R ∧
      (∀ c : Word F W,
        c ∈ (parityCheckCode (generatorImageParityCheck g')).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      (∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      ProductExpanding h (generatorImageParityCheck g') s m
        ((d : ℝ) / (3 * (Fintype.card W : ℝ))) := by
  obtain ⟨g', hImage⟩ := exists_generator_with_image_distance
    (F := F) (W := W) (R := R') d hGeneratorFactor
  have hGeneratorRank :=
    rank_eq_card_rows_of_image_distance g' d hPositive hImage
  have hImageDistance :=
    parityCheckCode_generatorImageParityCheck_distance g' d hImage
  obtain ⟨h, hCheckRank, hCheckDistance, hExpand⟩ :=
    exists_fullRank_distance_and_productExpanding_check
      (R := R) (generatorImageParityCheck g') d s m k
      hPositive hLength hSmallM hRankTarget hImageDistance
      hCheckDistanceFactor hCheckImageFactor hRectangleFactor
  exact ⟨g', h, hGeneratorRank, hCheckRank,
    hImageDistance, hCheckDistance, hExpand⟩

end QEC.Coding.ProductExpansion
