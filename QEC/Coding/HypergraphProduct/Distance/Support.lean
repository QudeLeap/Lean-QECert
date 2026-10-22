import QEC.Coding.HypergraphProduct.Dimension.Formula
import QEC.Coding.HypergraphProduct.Distance

/-!
# Support restriction for the hypergraph-product distance proof

Tillich--Zémor restrict a Tanner graph to the coordinates touched by a putative
small logical word.  This module supplies the finite-coordinate algebra needed
for that step, including the source convention that a zero code has distance
infinity.
-/

noncomputable section

namespace QEC.Coding.HypergraphProduct

universe u v

/-- Extend a word on a finite coordinate subset by zero. -/
def zeroExtend
    {F : Type v} {I : Type u}
    [Semiring F] [DecidableEq I]
    (A : Finset I) : Word F {i // i ∈ A} →ₗ[F] Word F I where
  toFun x i := if hi : i ∈ A then x ⟨i, hi⟩ else 0
  map_add' x y := by
    funext i
    by_cases hi : i ∈ A <;> simp [hi]
  map_smul' a x := by
    funext i
    by_cases hi : i ∈ A <;> simp [hi]

@[simp]
theorem zeroExtend_apply_mem
    {F : Type v} {I : Type u}
    [Semiring F] [DecidableEq I]
    (A : Finset I) (x : Word F {i // i ∈ A}) (i : {i // i ∈ A}) :
    zeroExtend A x i.1 = x i := by
  simp [zeroExtend, i.2]

theorem zeroExtend_injective
    {F : Type v} {I : Type u}
    [Semiring F] [DecidableEq I]
    (A : Finset I) : Function.Injective (zeroExtend (F := F) A) := by
  intro x y hxy
  funext i
  have hi := congrFun hxy i.1
  simpa using hi

/-- Summing over a finite subtype is the same as summing over the ambient
type when every term outside the selected finset vanishes. -/
theorem sum_subtype_eq_sum_of_not_mem_eq_zero
    {I : Type u} {M : Type v}
    [Fintype I] [DecidableEq I] [AddCommMonoid M]
    (A : Finset I) (f : I → M)
    (hzero : ∀ i, i ∉ A → f i = 0) :
    (∑ i : {i // i ∈ A}, f i.1) = ∑ i : I, f i := by
  let emb : {i // i ∈ A} ↪ I := Function.Embedding.subtype _
  have hmap : Finset.univ.map emb = A := by
    ext i
    simp [emb]
  calc
    (∑ i : {i // i ∈ A}, f i.1) =
        ∑ i ∈ Finset.univ.map emb, f i := by
      rw [Finset.sum_map]
      simp [emb]
    _ = ∑ i ∈ A, f i := by rw [hmap]
    _ = ∑ i : I, f i := by
      apply Finset.sum_subset (Finset.subset_univ A)
      intro i _hiuniv hiA
      exact hzero i hiA

/-- Restrict a matrix to a finite subset of its columns. -/
def restrictColumns
    {F : Type v} {Row I : Type u}
    (H : Matrix Row I F) (A : Finset I) : Matrix Row {i // i ∈ A} F :=
  fun r i => H r i.1

/-- Multiplication by a column-restricted matrix is multiplication by the
original matrix after zero extension. -/
theorem toLin'_restrictColumns
    {F : Type v} {Row I : Type u}
    [Field F]
    [Fintype Row] [Fintype I] [DecidableEq I]
    (H : Matrix Row I F) (A : Finset I) (x : Word F {i // i ∈ A}) :
    Matrix.toLin' (restrictColumns H A) x =
      Matrix.toLin' H (zeroExtend A x) := by
  funext r
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, restrictColumns]
  let emb : {i // i ∈ A} ↪ I := Function.Embedding.subtype _
  have hmap : Finset.univ.map emb = A := by
    ext i
    simp [emb]
  calc
    (∑ i : {i // i ∈ A}, H r i.1 * x i) =
        ∑ i ∈ Finset.univ.map emb, H r i * zeroExtend A x i := by
      rw [Finset.sum_map]
      simp [emb]
    _ = ∑ i ∈ A, H r i * zeroExtend A x i := by rw [hmap]
    _ = ∑ i : I, H r i * zeroExtend A x i := by
      apply Finset.sum_subset (Finset.subset_univ A)
      intro i _hiuniv hiA
      simp [zeroExtend, hiA]

/-- A zero-extended word has support only on the selected coordinates. -/
theorem HammingWeight_zeroExtend_le_card
    {F : Type v} {I : Type u}
    [Semiring F] [DecidableEq F]
    [Fintype I] [DecidableEq I]
    (A : Finset I) (x : Word F {i // i ∈ A}) :
    HammingWeight (zeroExtend A x) ≤ A.card := by
  rw [HammingWeight_eq_card_hammingSupport]
  apply Finset.card_le_card
  intro i hi
  simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ,
    true_and] at hi
  by_contra hiA
  exact hi (by simp [zeroExtend, hiA])

/-- If fewer columns are retained than the source-convention distance, the
column-restricted parity-check matrix has trivial kernel.  This includes the
case of an original zero code, whose extended distance is infinity. -/
theorem ker_restrictColumns_eq_bot_of_card_lt_extendedMinimumDistance
    {F : Type v} {Row I : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Row] [DecidableEq Row]
    [Fintype I] [DecidableEq I]
    (H : Matrix Row I F) (A : Finset I)
    (hA : (A.card : WithTop Nat) <
      extendedMinimumDistance
        (parityCheckKernelCode (Matrix.toLin' H))) :
    LinearMap.ker (Matrix.toLin' (restrictColumns H A)) = ⊥ := by
  classical
  apply le_antisymm
  · intro x hx
    have hxKernel : Matrix.toLin' (restrictColumns H A) x = 0 := hx
    have hExtendedKernel : Matrix.toLin' H (zeroExtend A x) = 0 := by
      rw [← toLin'_restrictColumns]
      exact hxKernel
    by_contra hx0
    have hExtended0 : zeroExtend A x ≠ 0 := by
      intro hzero
      exact hx0 (zeroExtend_injective A (by simpa using hzero))
    have hDistanceLe :
        extendedMinimumDistance
            (parityCheckKernelCode (Matrix.toLin' H)) ≤
          (HammingWeight (zeroExtend A x) : WithTop Nat) :=
      finitePredicateMinimum_le_of ⟨hExtendedKernel, hExtended0⟩
    have hWeightLe :
        (HammingWeight (zeroExtend A x) : WithTop Nat) ≤ A.card := by
      exact_mod_cast HammingWeight_zeroExtend_le_card A x
    exact (not_le_of_gt hA) (hDistanceLe.trans hWeightLe)
  · exact bot_le

end QEC.Coding.HypergraphProduct
