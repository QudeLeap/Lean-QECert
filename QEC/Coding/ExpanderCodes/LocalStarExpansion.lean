import QEC.Coding.ExpanderCodes.ProductExpansionProbability

/-!
# The matrix core of PK22 local-star expansion

This module isolates the two-case rectangle argument inside PK22's key
active-vertex lemma. In the first case many rows are heavy, so their
restriction to a large coordinate set still has weight at least `s`. In the
second case the face word agrees on a large rectangle with a nonzero minimal
product-kernel word, so product expansion supplies the same lower bound.

The geometric step identifying these matrices inside a Tanner lifted-product
star is deliberately separate.
-/

namespace QEC.Coding.ProductExpansion

universe u v

variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']

/-- A minimum-Hamming-weight representative of one parity-check syndrome. -/
def IsCosetLeader (h : Matrix R W F) (y : R → F) (x : Word F W) : Prop :=
  h.mulVec x = y ∧
    ∀ z : Word F W, h.mulVec z = y → HammingWeight x ≤ HammingWeight z

omit [Fintype F] [DecidableEq W] [Fintype R] [Fintype R'] in
/-- Every nonempty syndrome fiber has a coset leader. -/
theorem exists_cosetLeader
    (h : Matrix R W F) (y : R → F) (x₀ : Word F W)
    (hx₀ : h.mulVec x₀ = y) :
    ∃ x : Word F W, IsCosetLeader h y x := by
  let S : Set (Word F W) := {x | h.mulVec x = y}
  have hS : S.Nonempty := ⟨x₀, hx₀⟩
  let x := Function.argminOn HammingWeight S hS
  refine ⟨x, Function.argminOn_mem HammingWeight S hS, ?_⟩
  intro z hz
  exact Function.argminOn_le HammingWeight S hz

omit [Fintype F] [DecidableEq F] [DecidableEq W] [Fintype R'] in
/-- A parity-check matrix of maximal row rank realizes every syndrome. -/
theorem mulVec_surjective_of_rank_eq_card_rows
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R) :
    Function.Surjective h.mulVec := by
  have hRange : LinearMap.range h.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank] using hRank
  intro y
  obtain ⟨x, hx⟩ := (LinearMap.range_eq_top.mp hRange) y
  exact ⟨x, hx⟩

omit [Fintype F] [DecidableEq F] [DecidableEq W] [Fintype R'] in
/-- A chosen preimage of one syndrome under a maximal-row-rank check. -/
noncomputable def fullRowRankPreimage
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R)
    (y : Word F R) : Word F W :=
  Classical.choose (mulVec_surjective_of_rank_eq_card_rows h hRank y)

omit [Fintype F] [DecidableEq F] [DecidableEq W] [Fintype R'] in
@[simp] theorem fullRowRankPreimage_syndrome
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R)
    (y : Word F R) :
    h.mulVec (fullRowRankPreimage h hRank y) = y :=
  Classical.choose_spec (mulVec_surjective_of_rank_eq_card_rows h hRank y)

omit [Fintype R] [Fintype R'] in
/-- Adding a local-code word cannot lighten a syndrome coset leader. -/
theorem IsCosetLeader.weight_le_add_codeword
    {h : Matrix R W F} {y : R → F} {x : Word F W}
    (hx : IsCosetLeader h y x)
    (c : Word F W) (hc : c ∈ (parityCheckCode h).carrier) :
    HammingWeight x ≤ HammingWeight (x + c) := by
  apply hx.2
  rw [Matrix.mulVec_add, hx.1]
  change (Matrix.toLin' h) c = 0 at hc
  rw [Matrix.toLin'_apply] at hc
  simp [hc]

/-- Choose a syndrome coset leader independently in every matrix row. -/
noncomputable def cosetLeaderMatrix
    (h : Matrix R W F) (z : Matrix W R F) (x₀ : Matrix W W F)
    (hx₀ : ∀ i, h.mulVec (row x₀ i) = z i) : Matrix W W F :=
  fun i => Classical.choose (exists_cosetLeader h (z i) (row x₀ i) (hx₀ i))

/-- Choose rowwise syndrome coset leaders when the first check has maximal
row rank, without requiring callers to supply preliminary representatives. -/
noncomputable def fullRowRankCosetLeaderMatrix
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R)
    (z : Matrix W R F) : Matrix W W F :=
  cosetLeaderMatrix h z
    (fun i => fullRowRankPreimage h hRank (z i))
    (fun i => fullRowRankPreimage_syndrome h hRank (z i))

omit [Fintype F] [DecidableEq W] [Fintype R] in
/-- Every selected row is the promised syndrome coset leader. -/
theorem cosetLeaderMatrix_isCosetLeader
    (h : Matrix R W F) (z : Matrix W R F) (x₀ : Matrix W W F)
    (hx₀ : ∀ i, h.mulVec (row x₀ i) = z i) (i : W) :
    IsCosetLeader h (z i) (row (cosetLeaderMatrix h z x₀ hx₀) i) := by
  exact Classical.choose_spec
    (exists_cosetLeader h (z i) (row x₀ i) (hx₀ i))

omit [Fintype F] [DecidableEq W] [Fintype R] in
/-- The chosen row-leader matrix has exactly the prescribed right syndrome. -/
theorem cosetLeaderMatrix_mul_transpose
    (h : Matrix R W F) (z : Matrix W R F) (x₀ : Matrix W W F)
    (hx₀ : ∀ i, h.mulVec (row x₀ i) = z i) :
    cosetLeaderMatrix h z x₀ hx₀ * h.transpose = z := by
  ext i r
  have hi := (cosetLeaderMatrix_isCosetLeader h z x₀ hx₀ i).1
  have hir := congrFun hi r
  simpa [Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    dotProduct, row, mul_comm] using hir

omit [Fintype F] [DecidableEq W] [Fintype R] [Fintype R'] in
/-- If the prescribed syndrome is killed by the second local check, the
row-leader matrix is an actual product-kernel word. -/
theorem cosetLeaderMatrix_productKernel
    (h : Matrix R W F) (h' : Matrix R' W F)
    (z : Matrix W R F) (x₀ : Matrix W W F)
    (hx₀ : ∀ i, h.mulVec (row x₀ i) = z i)
    (hz : h' * z = 0) :
    ProductKernel h h' (cosetLeaderMatrix h z x₀ hx₀) := by
  unfold ProductKernel
  rw [Matrix.mul_assoc, cosetLeaderMatrix_mul_transpose h z x₀ hx₀, hz]

omit [Fintype F] [DecidableEq W] in
/-- Every row selected by the maximal-row-rank constructor is a syndrome
coset leader. -/
theorem fullRowRankCosetLeaderMatrix_isCosetLeader
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R)
    (z : Matrix W R F) (i : W) :
    IsCosetLeader h (z i) (row (fullRowRankCosetLeaderMatrix h hRank z) i) := by
  exact cosetLeaderMatrix_isCosetLeader h z
    (fun i => fullRowRankPreimage h hRank (z i))
    (fun i => fullRowRankPreimage_syndrome h hRank (z i)) i

omit [Fintype F] [DecidableEq W] in
/-- The maximal-row-rank constructor has exactly its prescribed syndrome. -/
theorem fullRowRankCosetLeaderMatrix_mul_transpose
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R)
    (z : Matrix W R F) :
    fullRowRankCosetLeaderMatrix h hRank z * h.transpose = z := by
  exact cosetLeaderMatrix_mul_transpose h z
    (fun i => fullRowRankPreimage h hRank (z i))
    (fun i => fullRowRankPreimage_syndrome h hRank (z i))

omit [Fintype F] [DecidableEq W] [Fintype R'] in
/-- If the prescribed syndrome is killed by the second check, the
maximal-row-rank coset-leader matrix is a product-kernel word. -/
theorem fullRowRankCosetLeaderMatrix_productKernel
    (h : Matrix R W F) (h' : Matrix R' W F)
    (hRank : h.rank = Fintype.card R) (z : Matrix W R F)
    (hz : h' * z = 0) :
    ProductKernel h h' (fullRowRankCosetLeaderMatrix h hRank z) := by
  unfold ProductKernel
  rw [Matrix.mul_assoc,
    fullRowRankCosetLeaderMatrix_mul_transpose h hRank z, hz]

omit [Fintype F] [Fintype W] [DecidableEq W] [Fintype R] [Fintype R'] in
/-- Count the nonzero entries of a rectangle row by row. -/
theorem restrictedWeight_eq_sum_row_restrictedHammingWeight
    (x : Matrix W W F) (A B : Finset W) :
    restrictedWeight x A B =
      ∑ i ∈ A, restrictedHammingWeight B (row x i) := by
  rfl

omit [Fintype F] [Fintype R] [Fintype R'] in
/-- A word's total weight is at most its weight on `A` plus the number of
coordinates omitted by `A`. -/
theorem HammingWeight_le_restrictedHammingWeight_add_complement
    (A : Finset W) (x : Word F W) :
    HammingWeight x ≤
      restrictedHammingWeight A x + (Fintype.card W - A.card) := by
  classical
  unfold HammingWeight hammingSupport restrictedHammingWeight
  let S := Finset.univ.filter fun i => x i ≠ 0
  have hSplit : S = (S ∩ A) ∪ (S \ A) := by
    ext i
    by_cases hiA : i ∈ A <;> simp [hiA]
  calc
    S.card = ((S ∩ A) ∪ (S \ A)).card := congrArg Finset.card hSplit
    _ ≤ (S ∩ A).card + (S \ A).card := Finset.card_union_le _ _
    _ ≤ (S ∩ A).card + (Finset.univ \ A).card := by
      apply Nat.add_le_add_left
      apply Finset.card_le_card
      intro i hi
      rw [Finset.mem_sdiff] at hi ⊢
      exact ⟨Finset.mem_univ i, hi.2⟩
    _ = restrictedHammingWeight A x + (Fintype.card W - A.card) := by
      have hInter : (S ∩ A).card = restrictedHammingWeight A x := by
        have hFilter : S ∩ A = A.filter (fun i => x i ≠ 0) := by
          ext i
          simp [S, and_comm]
        rw [hFilter, Finset.card_filter]
        unfold restrictedHammingWeight
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hxi : x i = 0 <;> simp [hxi]
      rw [hInter, Finset.card_sdiff_of_subset (Finset.subset_univ A)]
      simp

omit [Fintype F] [Fintype R] [Fintype R'] in
/-- A globally heavy row remains quarter-heavy on a set omitting at most `m`
coordinates when `d ≥ 4m`. -/
theorem distance_le_four_mul_restrictedHammingWeight
    (A : Finset W) (x : Word F W) (d m : Nat)
    (hA : Fintype.card W - m ≤ A.card)
    (hHeavy : d ≤ 2 * HammingWeight x)
    (hDistance : 4 * m ≤ d) :
    d ≤ 4 * restrictedHammingWeight A x := by
  have hMissing : Fintype.card W - A.card ≤ m := by
    have hAUniv : A.card ≤ Fintype.card W := Finset.card_le_univ A
    omega
  have hTotal := HammingWeight_le_restrictedHammingWeight_add_complement A x
  omega

omit [Fintype F] [Fintype R] [Fintype R'] in
/-- First branch of the local-star proof: more than `m` rows that are heavy
up to a factor two force at least `s` nonzero entries on the large rectangle. -/
theorem restrictedWeight_ge_of_many_heavy_rows
    (f : Matrix W W F) (A B J₂ : Finset W) (d m s : Nat)
    (hJ₂B : J₂ ⊆ B)
    (hA : Fintype.card W - m ≤ A.card)
    (hCount : m < J₂.card)
    (hHeavy : ∀ i ∈ J₂, d ≤ 2 * HammingWeight (row f i))
    (hDistance : 4 * m ≤ d)
    (hScale : 4 * s ≤ m * d) :
    s ≤ restrictedWeight f B A := by
  have hEach : ∀ i ∈ J₂,
      d ≤ 4 * restrictedHammingWeight A (row f i) := by
    intro i hi
    exact distance_le_four_mul_restrictedHammingWeight
      A (row f i) d m hA (hHeavy i hi) hDistance
  have hSum : J₂.card * d ≤
      4 * ∑ i ∈ J₂, restrictedHammingWeight A (row f i) := by
    calc
      J₂.card * d = ∑ _i ∈ J₂, d := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ J₂, 4 * restrictedHammingWeight A (row f i) := by
        exact Finset.sum_le_sum fun i hi => hEach i hi
      _ = 4 * ∑ i ∈ J₂, restrictedHammingWeight A (row f i) := by
        rw [Finset.mul_sum]
  have hRestricted :
      ∑ i ∈ J₂, restrictedHammingWeight A (row f i) ≤
        restrictedWeight f B A := by
    rw [restrictedWeight_eq_sum_row_restrictedHammingWeight]
    exact Finset.sum_le_sum_of_subset_of_nonneg hJ₂B (by simp)
  have hCountMul : m * d ≤ J₂.card * d :=
    Nat.mul_le_mul_right d (Nat.le_of_lt hCount)
  have hFour : 4 * s ≤ 4 * restrictedWeight f B A :=
    hScale.trans <| hCountMul.trans <|
      hSum.trans (Nat.mul_le_mul_left 4 hRestricted)
  omega

omit [DecidableEq W] [Fintype R] [Fintype R'] in
/-- Second branch of the local-star proof: agreement with a product-expanding
word on a large subrectangle transfers its lower bound to the face word. -/
theorem restrictedWeight_ge_of_productExpanding_agreement
    (h : Matrix R W F) (h' : Matrix R' W F)
    (f t : Matrix W W F) (A B J₃ : Finset W)
    (s m : Nat) (beta : ℝ)
    (hExpand : ProductExpanding h h' s (2 * m) beta)
    (hKernel : ProductKernel h h' t) (hNonzero : t ≠ 0)
    (hMinimal : IsDeltaMinimal h h'
      (beta * Fintype.card W) t)
    (hA : Fintype.card W - 2 * m ≤ A.card)
    (hJ₃ : Fintype.card W - 2 * m ≤ J₃.card)
    (hJ₃B : J₃ ⊆ B)
    (hAgree : ∀ i ∈ J₃, ∀ j ∈ A, f i j = t i j) :
    s ≤ restrictedWeight f B A := by
  have hProduct : s ≤ restrictedWeight t J₃ A :=
    hExpand t hKernel hNonzero hMinimal J₃ A hJ₃ hA
  have hEq : restrictedWeight f J₃ A = restrictedWeight t J₃ A := by
    unfold restrictedWeight
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hAgree i hi j hj]
  calc
    s ≤ restrictedWeight t J₃ A := hProduct
    _ = restrictedWeight f J₃ A := hEq.symm
    _ ≤ restrictedWeight f B A :=
      restrictedWeight_mono f hJ₃B (Finset.Subset.refl A)

omit [DecidableEq W] [Fintype R] [Fintype R'] in
/-- The coset-leader minimality step in PK22's active-vertex argument. Rows of
`t` are exact local-code coset leaders. Its columns agree with the face matrix
`f` on all but `2m` rows, while local minimality of the global chain permits a
face-column decrease of at most two. Hence `t` is `beta*w`-minimal once that
budget dominates `4m+2`. -/
theorem isDeltaMinimal_of_rowLeaders_and_faceColumnMinimal
    (h : Matrix R W F) (h' : Matrix R' W F)
    (f t : Matrix W W F) (J₃ : Finset W)
    (m : Nat) (beta : ℝ)
    (hJ₃ : Fintype.card W - 2 * m ≤ J₃.card)
    (hAgree : ∀ i ∈ J₃, ∀ j, f i j = t i j)
    (hRowLeaders : ∀ i c,
      c ∈ (parityCheckCode h).carrier →
      HammingWeight (row t i) ≤ HammingWeight (row t i + c))
    (hFaceColumns : ∀ j c,
      c ∈ (parityCheckCode h').carrier →
      (HammingWeight (column f j) : ℝ) ≤
        HammingWeight (column f j + c) + 2)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W) :
    IsDeltaMinimal h h' (beta * Fintype.card W) t := by
  constructor
  · intro i c hc
    have hNonnegative : 0 ≤ beta * Fintype.card W := by
      linarith
    have hLeaderReal : (HammingWeight (row t i) : ℝ) ≤
        HammingWeight (row t i + c) := by
      exact_mod_cast hRowLeaders i c hc
    linarith
  · intro j c hc
    let tf := column t j
    let ff := column f j
    have hVanish : ∀ i ∈ J₃, (ff - tf) i = 0 := by
      intro i hi
      simp [ff, tf, column, hAgree i hi j]
    have hDifferenceNat : HammingWeight (ff - tf) ≤ 2 * m := by
      have hComplement := HammingWeight_le_complement_card J₃ (ff - tf) hVanish
      have hMissing : Fintype.card W - J₃.card ≤ 2 * m := by
        have hJ₃Univ : J₃.card ≤ Fintype.card W := Finset.card_le_univ J₃
        omega
      exact hComplement.trans hMissing
    have hDifferenceReverseNat : HammingWeight (tf - ff) ≤ 2 * m := by
      have hNeg : tf - ff = -(ff - tf) := by abel
      rw [hNeg, HammingWeight_neg]
      exact hDifferenceNat
    have hT : HammingWeight tf ≤
        HammingWeight (tf - ff) + HammingWeight ff := by
      have heq : tf = (tf - ff) + ff := by abel
      calc
        HammingWeight tf = HammingWeight ((tf - ff) + ff) :=
          congrArg HammingWeight heq
        _ ≤ HammingWeight (tf - ff) + HammingWeight ff :=
          HammingWeight_add_le _ _
    have hFCorrected : HammingWeight (ff + c) ≤
        HammingWeight (ff - tf) + HammingWeight (tf + c) := by
      have heq : ff + c = (ff - tf) + (tf + c) := by abel
      calc
        HammingWeight (ff + c) =
            HammingWeight ((ff - tf) + (tf + c)) :=
          congrArg HammingWeight heq
        _ ≤ HammingWeight (ff - tf) + HammingWeight (tf + c) :=
          HammingWeight_add_le _ _
    have hTReal : (HammingWeight tf : ℝ) ≤
        HammingWeight (tf - ff) + HammingWeight ff := by
      exact_mod_cast hT
    have hFCorrectedReal : (HammingWeight (ff + c) : ℝ) ≤
        HammingWeight (ff - tf) + HammingWeight (tf + c) := by
      exact_mod_cast hFCorrected
    have hDifferenceReal : (HammingWeight (ff - tf) : ℝ) ≤ 2 * m := by
      exact_mod_cast hDifferenceNat
    have hDifferenceReverseReal : (HammingWeight (tf - ff) : ℝ) ≤ 2 * m := by
      exact_mod_cast hDifferenceReverseNat
    have hFace := hFaceColumns j c hc
    change (HammingWeight tf : ℝ) ≤
      HammingWeight (tf + c) + beta * Fintype.card W
    linarith

omit [Fintype R] [Fintype R'] in
/-- The source's `J₂/J₃` dichotomy: either many heavy rows supply the
rectangle weight, or the large agreement block invokes product expansion. -/
theorem localStar_restrictedWeight_ge
    (h : Matrix R W F) (h' : Matrix R' W F)
    (f t : Matrix W W F) (A B J₂ J₃ : Finset W)
    (d m s : Nat) (beta : ℝ)
    (hExpand : ProductExpanding h h' s (2 * m) beta)
    (hKernel : ProductKernel h h' t) (hNonzero : t ≠ 0)
    (hMinimal : Fintype.card W - 2 * m ≤ J₃.card →
      IsDeltaMinimal h h' (beta * Fintype.card W) t)
    (hA : Fintype.card W - m < A.card)
    (hB : Fintype.card W - m < B.card)
    (hCover : B ⊆ J₂ ∪ J₃)
    (hJ₂B : J₂ ⊆ B) (hJ₃B : J₃ ⊆ B)
    (hHeavy : ∀ i ∈ J₂, d ≤ 2 * HammingWeight (row f i))
    (hDistance : 4 * m ≤ d)
    (hScale : 4 * s ≤ m * d)
    (hAgree : ∀ i ∈ J₃, ∀ j ∈ A, f i j = t i j) :
    s ≤ restrictedWeight f B A := by
  by_cases hJ₃Large : Fintype.card W - 2 * m ≤ J₃.card
  · apply restrictedWeight_ge_of_productExpanding_agreement
      h h' f t A B J₃ s m beta hExpand hKernel hNonzero
        (hMinimal hJ₃Large)
    · omega
    · exact hJ₃Large
    · exact hJ₃B
    · exact hAgree
  · have hCardCover : B.card ≤ J₂.card + J₃.card :=
      (Finset.card_le_card hCover).trans (Finset.card_union_le J₂ J₃)
    have hCount : m < J₂.card := by omega
    apply restrictedWeight_ge_of_many_heavy_rows
      f A B J₂ d m s hJ₂B
    · omega
    · exact hCount
    · exact hHeavy
    · exact hDistance
    · exact hScale

end QEC.Coding.ProductExpansion
