import QEC.Coding.Core.Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Product expansion for finite-field matrix codes

These definitions model the local product-expansion property in
[PK22, Section 3.2]. A product codeword is a square matrix annihilated by
the two parity-check matrices. Row and column minimality and expansion on
large coordinate rectangles retain the source's quantifier order.

This file does not assert that any matrix pair has product expansion; the
probabilistic existence and concrete graph construction remain separate proofs.
-/

namespace QEC.Coding.ProductExpansion

universe u v

variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']

/-- The linear code cut out by a field-valued parity-check matrix. -/
noncomputable def parityCheckCode (h : Matrix R W F) : LinearCode F W := by
  classical
  exact ⟨LinearMap.ker (Matrix.toLin' h)⟩

/-- The source's dual-to-product code, represented as square matrices. -/
def ProductKernel (h : Matrix R W F) (h' : Matrix R' W F)
    (x : Matrix W W F) : Prop :=
  h' * x * h.transpose = 0

omit [DecidableEq F] [Fintype R] [Fintype R'] in
/-- Each row of the first local syndrome is a codeword of the other check code. -/
theorem row_leftProduct_mem_parityCheckCode
    (h : Matrix R W F) (h' : Matrix R' W F)
    (x : Matrix W W F) (hx : ProductKernel h h' x) (i : R') :
    (h' * x) i ∈ (parityCheckCode h).carrier := by
  classical
  change (Matrix.toLin' h) ((h' * x) i) = 0
  ext j
  have hentry := congrArg (fun M : Matrix R' R F => M i j) hx
  simp only [Matrix.zero_apply] at hentry
  simpa [Matrix.toLin'_apply, Matrix.mulVec, Matrix.mul_apply,
    Matrix.transpose_apply, dotProduct, mul_comm] using hentry

omit [DecidableEq F] [Fintype R] [Fintype R'] in
/-- Each column of the second local syndrome is a codeword of the first check code. -/
theorem column_rightProduct_mem_parityCheckCode
    (h : Matrix R W F) (h' : Matrix R' W F)
    (x : Matrix W W F) (hx : ProductKernel h h' x) (j : R) :
    (fun i : W => (x * h.transpose) i j) ∈ (parityCheckCode h').carrier := by
  classical
  change (Matrix.toLin' h') (fun i : W => (x * h.transpose) i j) = 0
  ext i
  change h' * x * h.transpose = 0 at hx
  have hassoc : h' * (x * h.transpose) = 0 := by
    simpa only [Matrix.mul_assoc] using hx
  have hentry := congrArg (fun M : Matrix R' R F => M i j) hassoc
  simpa [Matrix.toLin'_apply, Matrix.mulVec, Matrix.mul_apply,
    dotProduct] using hentry

omit [Fintype R] in
/-- A set larger than `w-d` separates all codewords when the code distance is at least `d`. -/
theorem codeword_eq_zero_of_vanish_on_large_subset
    (h : Matrix R W F) (d : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (A : Finset W) (hLarge : Fintype.card W - d < A.card)
    (c : Word F W) (hc : c ∈ (parityCheckCode h).carrier)
    (hVanish : ∀ i ∈ A, c i = 0) : c = 0 := by
  classical
  by_contra hnonzero
  have hSupport : hammingSupport c ⊆ Finset.univ \ A := by
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hiA
    have hci : c i ≠ 0 := by simpa [hammingSupport] using hi
    exact hci (hVanish i hiA)
  have hCard := Finset.card_le_card hSupport
  have hComplement : (Finset.univ \ A).card = Fintype.card W - A.card := by
    simpa using Finset.card_sdiff_of_subset (Finset.subset_univ A)
  rw [hComplement] at hCard
  have hd := hDistance c hc hnonzero
  unfold HammingWeight at hd
  have hAle : A.card ≤ Fintype.card W := Finset.card_le_univ A
  omega

omit [Fintype R] in
/-- Restriction to a sufficiently large coordinate set determines every codeword. -/
theorem restriction_injective_of_distance
    (h : Matrix R W F) (d : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (A : Finset W) (hLarge : Fintype.card W - d < A.card) :
    Function.Injective (fun c : (parityCheckCode h).carrier =>
      fun i : {i : W // i ∈ A} => c.1 i.1) := by
  intro c e heq
  have hdiff : c.1 - e.1 ∈ (parityCheckCode h).carrier :=
    (parityCheckCode h).carrier.sub_mem c.2 e.2
  have hvanish : ∀ i ∈ A, (c.1 - e.1) i = 0 := by
    intro i hi
    have hvalue := congrFun heq ⟨i, hi⟩
    exact sub_eq_zero.mpr hvalue
  have hzero := codeword_eq_zero_of_vanish_on_large_subset
    h d hDistance A hLarge (c.1 - e.1) hdiff hvanish
  apply Subtype.ext
  exact sub_eq_zero.mp hzero

/-- Restrict a field word to one selected coordinate set. -/
def restrictionLinearMap (A : Finset W) :
    Word F W →ₗ[F] ({i : W // i ∈ A} → F) where
  toFun x i := x i.1
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- The restriction map on the parity-check code itself. -/
noncomputable def codeRestriction (h : Matrix R W F) (A : Finset W) :
    (parityCheckCode h).carrier →ₗ[F] ({i : W // i ∈ A} → F) :=
  (restrictionLinearMap A).comp (parityCheckCode h).carrier.subtype

omit [DecidableEq F] [Fintype R] in
/-- Injective coordinate restriction yields a linear codeword projection using only those coordinates. -/
theorem exists_code_projection_of_restriction_injective
    (h : Matrix R W F) (A : Finset W)
    (hInjective : Function.Injective (codeRestriction h A)) :
    ∃ T : Word F W →ₗ[F] Word F W,
      (∀ c : Word F W, c ∈ (parityCheckCode h).carrier → T c = c) ∧
      (∀ x : Word F W, (∀ i ∈ A, x i = 0) → T x = 0) ∧
      (∀ x : Word F W, T x ∈ (parityCheckCode h).carrier) := by
  let R := codeRestriction h A
  let L := R.leftInverse
  let T := (parityCheckCode h).carrier.subtype.comp
    (L.comp (restrictionLinearMap A))
  have hLeft (c : (parityCheckCode h).carrier) : L (R c) = c :=
    R.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hInjective) c
  refine ⟨T, ?_, ?_, ?_⟩
  · intro c hc
    let cc : (parityCheckCode h).carrier := ⟨c, hc⟩
    change (L (R cc) : Word F W) = c
    rw [hLeft cc]
  · intro x hx
    have hRestriction : restrictionLinearMap A x = 0 := by
      funext i
      exact hx i.1 i.2
    simp [T, hRestriction]
  · intro x
    exact (L (restrictionLinearMap A x)).2

omit [Fintype R] in
/-- A local distance bound supplies the projection used in the nonzero-block proof. -/
theorem exists_code_projection_of_distance
    (h : Matrix R W F) (d : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (A : Finset W) (hLarge : Fintype.card W - d < A.card) :
    ∃ T : Word F W →ₗ[F] Word F W,
      (∀ c : Word F W, c ∈ (parityCheckCode h).carrier → T c = c) ∧
      (∀ x : Word F W, (∀ i ∈ A, x i = 0) → T x = 0) ∧
      (∀ x : Word F W, T x ∈ (parityCheckCode h).carrier) := by
  apply exists_code_projection_of_restriction_injective h A
  change Function.Injective (fun c : (parityCheckCode h).carrier =>
    fun i : {i : W // i ∈ A} => c.1 i.1)
  exact restriction_injective_of_distance h d hDistance A hLarge

/-- Row `i` of a square matrix, as a field word. -/
def row (x : Matrix W W F) (i : W) : Word F W := x i

/-- Column `j` of a square matrix, as a field word. -/
def column (x : Matrix W W F) (j : W) : Word F W := fun i => x i j

/-- Apply one field-linear word operation independently to every matrix row. -/
def mapRows {I : Type v} (T : Word F W →ₗ[F] Word F W)
    (x : Matrix I W F) : Matrix I W F :=
  fun i => T (x i)

omit [Fintype F] [DecidableEq F] [Fintype W] in
/-- A rowwise linear operation commutes with left matrix multiplication. -/
theorem mapRows_left_mul
    {I J : Type v} [Fintype I]
    (T : Word F W →ₗ[F] Word F W)
    (H : Matrix J I F) (x : Matrix I W F) :
    mapRows T (H * x) = H * mapRows T x := by
  ext j k
  have hRow : (H * x) j = ∑ i : I, H j i • x i := by
    funext t
    simp [Matrix.mul_apply, Pi.smul_apply]
  simp [mapRows, hRow, map_sum, Matrix.mul_apply, Pi.smul_apply]

omit [DecidableEq F] [Fintype R] [Fintype R'] in
/-- Projecting every row onto the first local code kills the other matrix syndrome. -/
theorem leftProduct_sub_mapRows_eq_zero
    (h : Matrix R W F) (h' : Matrix R' W F)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (T : Word F W →ₗ[F] Word F W)
    (hFix : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier → T c = c) :
    h' * (x - mapRows T x) = 0 := by
  have hRows : mapRows T (h' * x) = h' * x := by
    ext i j
    exact congrFun (hFix ((h' * x) i)
      (row_leftProduct_mem_parityCheckCode h h' x hx i)) j
  calc
    h' * (x - mapRows T x) = h' * x - h' * mapRows T x := by
      rw [Matrix.mul_sub]
    _ = h' * x - mapRows T (h' * x) := by
      rw [mapRows_left_mul]
    _ = 0 := by rw [hRows]; simp

omit [DecidableEq F] [Fintype R] in
/-- A matrix of projected rows is annihilated by the first parity-check matrix. -/
theorem mapRows_mul_transpose_eq_zero
    (h : Matrix R W F) (T : Word F W →ₗ[F] Word F W)
    (hImage : ∀ y : Word F W, T y ∈ (parityCheckCode h).carrier)
    (x : Matrix W W F) :
    mapRows T x * h.transpose = 0 := by
  classical
  ext i j
  have hm := hImage (x i)
  change (Matrix.toLin' h) (T (x i)) = 0 at hm
  have hentry := congrFun hm j
  simpa [mapRows, Matrix.toLin'_apply, Matrix.mulVec,
    Matrix.mul_apply, Matrix.transpose_apply, dotProduct, mul_comm] using hentry

omit [DecidableEq F] [Fintype R] in
/-- A vanishing left syndrome means that every column belongs to the local code. -/
theorem column_mem_parityCheckCode_of_left_mul_eq_zero
    (h : Matrix R W F) (x : Matrix W W F) (hx : h * x = 0) (j : W) :
    column x j ∈ (parityCheckCode h).carrier := by
  classical
  change (Matrix.toLin' h) (fun i : W => x i j) = 0
  ext i
  have hentry := congrArg (fun M : Matrix R W F => M i j) hx
  simpa [Matrix.toLin'_apply, Matrix.mulVec, Matrix.mul_apply,
    dotProduct, column] using hentry

omit [Fintype F] [DecidableEq F] [Fintype W] [Fintype R] [Fintype R'] in
/-- A row projection depending only on `A` vanishes on rows zero over `A`. -/
theorem mapRows_eq_zero_on_rows_of_vanish_on_rectangle
    (T : Word F W →ₗ[F] Word F W) (A B : Finset W)
    (hVanish : ∀ y : Word F W, (∀ j ∈ A, y j = 0) → T y = 0)
    (x : Matrix W W F) (hx : ∀ i ∈ B, ∀ j ∈ A, x i j = 0) :
    ∀ i ∈ B, mapRows T x i = 0 := by
  intro i hi
  exact hVanish (x i) (hx i hi)

omit [Fintype R] in
/-- After row projection, a zero rectangle and zero left syndrome force the
corrected matrix to vanish on every selected column. -/
theorem corrected_columns_eq_zero_of_rectangle
    (h : Matrix R W F) (d : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (A B : Finset W) (hLarge : Fintype.card W - d < B.card)
    (T : Word F W →ₗ[F] Word F W)
    (hVanish : ∀ y : Word F W, (∀ j ∈ A, y j = 0) → T y = 0)
    (x : Matrix W W F) (hx : ∀ i ∈ B, ∀ j ∈ A, x i j = 0)
    (hLeft : h * (x - mapRows T x) = 0) :
    ∀ j ∈ A, column (x - mapRows T x) j = 0 := by
  intro j hj
  apply codeword_eq_zero_of_vanish_on_large_subset h d hDistance B hLarge
  · exact column_mem_parityCheckCode_of_left_mul_eq_zero
      h (x - mapRows T x) hLeft j
  · intro i hi
    have hProjected : mapRows T x i = 0 :=
      mapRows_eq_zero_on_rows_of_vanish_on_rectangle T A B hVanish x hx i hi
    simp [column, hx i hi j hj, hProjected]

omit [Fintype F] [Fintype R] [Fintype R'] in
/-- A word vanishing on `A` is supported on at most the complement of `A`. -/
theorem HammingWeight_le_complement_card
    (A : Finset W) (x : Word F W) (hVanish : ∀ j ∈ A, x j = 0) :
    HammingWeight x ≤ Fintype.card W - A.card := by
  classical
  have hSupport : hammingSupport x ⊆ Finset.univ \ A := by
    intro j hj
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hjA
    have hxj : x j ≠ 0 := by simpa [hammingSupport] using hj
    exact hxj (hVanish j hjA)
  have hCard := Finset.card_le_card hSupport
  have hComplement : (Finset.univ \ A).card = Fintype.card W - A.card := by
    simpa using Finset.card_sdiff_of_subset (Finset.subset_univ A)
  simpa [HammingWeight, hComplement] using hCard

omit [Fintype F] [Fintype R] [Fintype R'] in
/-- A word supported inside a finite set has weight at most its cardinality. -/
theorem HammingWeight_le_support_set_card
    (S : Finset W) (x : Word F W) (hSupport : ∀ i ∉ S, x i = 0) :
    HammingWeight x ≤ S.card := by
  classical
  have hSubset : hammingSupport x ⊆ S := by
    intro i hi
    by_contra hiS
    have hxi : x i ≠ 0 := by simpa [hammingSupport] using hi
    exact hxi (hSupport i hiS)
  exact Finset.card_le_card hSubset

omit [Fintype F] [Fintype R] [Fintype R'] in
/-- Negation leaves finite-field Hamming weight unchanged. -/
@[simp] theorem HammingWeight_neg (x : Word F W) :
    HammingWeight (-x) = HammingWeight x := by
  classical
  simp [HammingWeight, hammingSupport, Pi.neg_apply, neg_eq_zero]

omit [Fintype F] [Fintype R] [Fintype R'] in
/-- A Hamming-weight triangle inequality for subtraction. -/
theorem HammingWeight_sub_le (x y : Word F W) :
    HammingWeight (x - y) ≤ HammingWeight x + HammingWeight y := by
  rw [sub_eq_add_neg]
  calc
    HammingWeight (x + -y) ≤ HammingWeight x + HammingWeight (-y) :=
      HammingWeight_add_le x (-y)
    _ = HammingWeight x + HammingWeight y := by rw [HammingWeight_neg]

omit [Fintype R] [Fintype R'] in
/-- A near-minimal word cannot be shortened to a light residual by subtracting
a nonzero codeword when twice that residual weight plus the allowed decrease
is below the code distance. -/
theorem codeword_eq_zero_of_minimality_and_small_residual
    (h : Matrix R W F) (d : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (delta : ℝ) (x c : Word F W)
    (hc : c ∈ (parityCheckCode h).carrier)
    (hGap : 2 * (HammingWeight (x - c) : ℝ) + delta < d)
    (hMinimal : (HammingWeight x : ℝ) ≤ HammingWeight (x - c) + delta) :
    c = 0 := by
  by_contra hNonzero
  have hDistanceNat := hDistance c hc hNonzero
  have hCodeword : c = x - (x - c) := by
    ext j
    simp
  have hTriangleNat : HammingWeight c ≤ HammingWeight x + HammingWeight (x - c) := by
    calc
      HammingWeight c = HammingWeight (x - (x - c)) := congrArg HammingWeight hCodeword
      _ ≤ HammingWeight x + HammingWeight (x - c) := HammingWeight_sub_le x (x - c)
  have hDistanceReal : (d : ℝ) ≤ HammingWeight c := by exact_mod_cast hDistanceNat
  have hTriangleReal : (HammingWeight c : ℝ) ≤
      HammingWeight x + HammingWeight (x - c) := by exact_mod_cast hTriangleNat
  linarith

omit [Fintype R] [Fintype R'] in
/-- The numerical core of the nonzero-block proof: a nonzero local codeword
cannot be a near-minimal correction when the residual word is supported outside
a sufficiently large coordinate set. -/
theorem codeword_eq_zero_of_minimality_and_complement_bound
    (h : Matrix R W F) (d : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (A : Finset W) (delta : ℝ)
    (hGap : 2 * (Fintype.card W - A.card : ℝ) + delta < d)
    (x c : Word F W) (hc : c ∈ (parityCheckCode h).carrier)
    (hCorrected : ∀ j ∈ A, (x - c) j = 0)
    (hMinimal : (HammingWeight x : ℝ) ≤ HammingWeight (x - c) + delta) :
    c = 0 := by
  have hResidualNat := HammingWeight_le_complement_card A (x - c) hCorrected
  have hResidualReal : (HammingWeight (x - c) : ℝ) ≤
      ((Fintype.card W - A.card : Nat) : ℝ) := by
    exact_mod_cast hResidualNat
  have hAle : A.card ≤ Fintype.card W := Finset.card_le_univ A
  have hComplementCast : ((Fintype.card W - A.card : Nat) : ℝ) =
      (Fintype.card W : ℝ) - A.card := Nat.cast_sub hAle
  have hResidualGap : 2 * (HammingWeight (x - c) : ℝ) + delta < d := by
    linarith
  exact codeword_eq_zero_of_minimality_and_small_residual
    h d hDistance delta x c hc hResidualGap hMinimal

omit [Fintype R] [Fintype R'] in
/-- The algebraic correction step of the nonzero-block argument. The selected
rectangle is zero, and each local code is determined by its corresponding
selected coordinate set. The correction has local-code rows; after subtracting
it, the second syndrome and all columns in `A` vanish. -/
theorem exists_row_correction_of_zero_rectangle
    (h : Matrix R W F) (h' : Matrix R' W F) (d d' : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d' ≤ HammingWeight c)
    (A B : Finset W) (hLargeA : Fintype.card W - d < A.card)
    (hLargeB : Fintype.card W - d' < B.card)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hRectangle : ∀ i ∈ B, ∀ j ∈ A, x i j = 0) :
    ∃ delta : Matrix W W F,
      h' * (x - delta) = 0 ∧
      (∀ j ∈ A, column (x - delta) j = 0) ∧
      (∀ i : W, row delta i ∈ (parityCheckCode h).carrier) := by
  obtain ⟨T, hFix, hVanish, hImage⟩ :=
    exists_code_projection_of_distance h d hDistance A hLargeA
  refine ⟨mapRows T x, ?_, ?_, ?_⟩
  · exact leftProduct_sub_mapRows_eq_zero h h' x hx T hFix
  · exact corrected_columns_eq_zero_of_rectangle h' d' hDistance'
      A B hLargeB T hVanish x hRectangle
      (leftProduct_sub_mapRows_eq_zero h h' x hx T hFix)
  · intro i
    exact hImage (x i)

omit [Field F] [Fintype F] [DecidableEq F] [Fintype W] in
@[simp] theorem row_transpose (x : Matrix W W F) (i : W) :
    row x.transpose i = column x i := rfl

omit [Field F] [Fintype F] [DecidableEq F] [Fintype W] in
@[simp] theorem column_transpose (x : Matrix W W F) (j : W) :
    column x.transpose j = row x j := rfl

/-- A matrix cannot be lightened by more than `delta` by a single row or column codeword. -/
def IsDeltaMinimal (h : Matrix R W F) (h' : Matrix R' W F)
    (delta : ℝ) (x : Matrix W W F) : Prop :=
  (∀ i : W, ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
    (HammingWeight (row x i) : ℝ) ≤ HammingWeight (row x i + c) + delta) ∧
  (∀ j : W, ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
    (HammingWeight (column x j) : ℝ) ≤ HammingWeight (column x j + c) + delta)

omit [Fintype R] [Fintype R'] in
/-- A `d/3`-minimal column cannot differ by a nonzero local codeword from a
word of weight strictly less than `d/3`. This is the cancellation argument
used twice in the source's rank lower bound. -/
theorem column_adjustment_eq_zero_of_small_residual
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (j : W) (c : Word F W) (hc : c ∈ (parityCheckCode h').carrier)
    (hSmall : (HammingWeight (column x j + c) : ℝ) < (d : ℝ) / 3) :
    c = 0 := by
  have hNegative : -c ∈ (parityCheckCode h').carrier :=
    (parityCheckCode h').carrier.neg_mem hc
  have hGap : 2 * (HammingWeight (column x j - -c) : ℝ) + (d : ℝ) / 3 < d := by
    simpa only [sub_neg_eq_add] using (show
      2 * (HammingWeight (column x j + c) : ℝ) + (d : ℝ) / 3 < d by
        linarith)
  have hMinimalColumn : (HammingWeight (column x j) : ℝ) ≤
      HammingWeight (column x j - -c) + (d : ℝ) / 3 := by
    simpa only [sub_neg_eq_add] using hMinimal.2 j c hc
  have hZero := codeword_eq_zero_of_minimality_and_small_residual
    h' d hDistance' ((d : ℝ) / 3) (column x j) (-c)
      hNegative hGap hMinimalColumn
  simpa using hZero

omit [Fintype R] [Fintype R'] in
/-- A small-support lift of a column's syndrome must equal that column in a
`d/3`-minimal matrix. This is the source's first rank-lemma contradiction. -/
theorem column_eq_small_support_syndrome_lift
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (S : Finset W) (hSmall : (S.card : ℝ) < (d : ℝ) / 3)
    (j : W) (y : Word F W)
    (hSupport : ∀ i ∉ S, y i = 0)
    (hSyndrome : h'.mulVec y = h'.mulVec (column x j)) :
    column x j = y := by
  classical
  let c : Word F W := y - column x j
  have hc : c ∈ (parityCheckCode h').carrier := by
    change (Matrix.toLin' h') c = 0
    simp [Matrix.toLin'_apply, c, Matrix.mulVec_sub, hSyndrome]
  have hWeightNat := HammingWeight_le_support_set_card S y hSupport
  have hWeightReal : (HammingWeight y : ℝ) ≤ S.card := by
    exact_mod_cast hWeightNat
  have hAdjusted : column x j + c = y := by
    ext i
    simp [c]
  have hSmallAdjusted : (HammingWeight (column x j + c) : ℝ) <
      (d : ℝ) / 3 := by
    rw [hAdjusted]
    linarith
  have hZero := column_adjustment_eq_zero_of_small_residual
    h h' d hDistance' x hMinimal j c hc hSmallAdjusted
  have hEq : y - column x j = 0 := hZero
  exact (sub_eq_zero.mp hEq).symm

omit [Fintype R] [Fintype R'] in
/-- If the left syndrome vanishes, local minimality below the local distance
forces every column, hence the whole matrix, to vanish. -/
theorem eq_zero_of_left_mul_eq_zero_and_minimal
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (delta : ℝ) (hDelta : delta < d)
    (x : Matrix W W F) (hLeft : h' * x = 0)
    (hMinimal : IsDeltaMinimal h h' delta x) :
    x = 0 := by
  ext i j
  have hColumn : column x j ∈ (parityCheckCode h').carrier :=
    column_mem_parityCheckCode_of_left_mul_eq_zero h' x hLeft j
  have hColumnZero : column x j = 0 := by
    by_contra hNonzero
    have hDistanceNat := hDistance' (column x j) hColumn hNonzero
    have hNegative : -(column x j) ∈ (parityCheckCode h').carrier :=
      (parityCheckCode h').carrier.neg_mem hColumn
    have hMinimalColumn := hMinimal.2 j (-(column x j)) hNegative
    have hWeight : (HammingWeight (column x j) : ℝ) ≤ delta := by
      simpa using hMinimalColumn
    have hDistanceReal : (d : ℝ) ≤ HammingWeight (column x j) := by
      exact_mod_cast hDistanceNat
    linarith
  exact congrFun hColumnZero i

omit [Fintype R] [Fintype R'] in
/-- The left syndrome of a nonzero minimal matrix must be nonzero. -/
theorem left_mul_ne_zero_of_nonzero_minimal
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (delta : ℝ) (hDelta : delta < d)
    (x : Matrix W W F) (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' delta x) :
    h' * x ≠ 0 := by
  intro hZero
  exact hxNonzero (eq_zero_of_left_mul_eq_zero_and_minimal
    h h' d hDistance' delta hDelta x hZero hMinimal)

omit [Fintype F] [DecidableEq F] [Fintype R] in
/-- Over a field, a nonzero finite matrix has positive matrix rank. -/
theorem matrix_rank_pos_of_ne_zero
    {I : Type v} [Fintype I]
    (M : Matrix I W F) (hM : M ≠ 0) :
    0 < M.rank := by
  classical
  by_contra hNot
  have hRankZero : M.rank = 0 := by omega
  have hRangeBot : LinearMap.range M.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp hRankZero
  have hMapZero : M.mulVecLin = 0 := LinearMap.range_eq_bot.mp hRangeBot
  apply hM
  ext i j
  have hAt := congrArg (fun f : (W → F) →ₗ[F] (I → F) =>
    f (Pi.single j (1 : F)) i) hMapZero
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using hAt

omit [Fintype R] in
/-- The source's syndrome rank parameter is positive for every nonzero
locally minimal matrix, before its quantitative lower bound is established. -/
theorem left_product_rank_pos_of_nonzero_minimal
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (delta : ℝ) (hDelta : delta < d)
    (x : Matrix W W F) (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' delta x) :
    0 < (h' * x).rank :=
  matrix_rank_pos_of_ne_zero (h' * x)
    (left_mul_ne_zero_of_nonzero_minimal h h' d
      hDistance' delta hDelta x hxNonzero hMinimal)

omit [Fintype R] [Fintype R'] in
/-- A large zero column set, a local-code row correction, and delta-minimality
force that correction to vanish whenever the distance gap is large enough. -/
theorem row_correction_eq_zero_of_gap
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (A : Finset W) (delta : ℝ)
    (hGap : 2 * (Fintype.card W - A.card : ℝ) + delta < d)
    (x correction : Matrix W W F)
    (hRows : ∀ i : W, row correction i ∈ (parityCheckCode h).carrier)
    (hCorrected : ∀ j ∈ A, column (x - correction) j = 0)
    (hMinimal : IsDeltaMinimal h h' delta x) :
    correction = 0 := by
  ext i j
  have hZeroRow : row correction i = 0 := by
    apply codeword_eq_zero_of_minimality_and_complement_bound
      h d hDistance A delta hGap (row x i) (row correction i) (hRows i)
    · intro k hk
      have hentry := congrFun (hCorrected k hk) i
      simpa [row, column, Pi.sub_apply, Matrix.sub_apply] using hentry
    · have hNegative : -(row correction i) ∈ (parityCheckCode h).carrier :=
        (parityCheckCode h).carrier.neg_mem (hRows i)
      simpa [sub_eq_add_neg] using hMinimal.1 i (-(row correction i)) hNegative
  exact congrFun hZeroRow j

omit [Fintype R] [Fintype R'] in
/-- Nonzero-block lemma, in the orientation where `A` selects columns and
`B` selects rows. The exact numerical inequalities are exposed so that the
source's `d/3` parameter choice can be instantiated separately. -/
theorem eq_zero_of_zero_rectangle
    (h : Matrix R W F) (h' : Matrix R' W F) (d d' : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d' ≤ HammingWeight c)
    (A B : Finset W)
    (hLargeA : Fintype.card W - d < A.card)
    (hLargeB : Fintype.card W - d' < B.card)
    (delta : ℝ)
    (hGap : 2 * (Fintype.card W - A.card : ℝ) + delta < d)
    (hDelta : delta < d')
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hMinimal : IsDeltaMinimal h h' delta x)
    (hRectangle : ∀ i ∈ B, ∀ j ∈ A, x i j = 0) :
    x = 0 := by
  obtain ⟨correction, hLeft, hColumns, hRows⟩ :=
    exists_row_correction_of_zero_rectangle h h' d d'
      hDistance hDistance' A B hLargeA hLargeB x hx hRectangle
  have hCorrectionZero : correction = 0 :=
    row_correction_eq_zero_of_gap h h' d hDistance A delta hGap
      x correction hRows hColumns hMinimal
  have hLeftZero : h' * x = 0 := by
    simpa [hCorrectionZero] using hLeft
  exact eq_zero_of_left_mul_eq_zero_and_minimal
    h h' d' hDistance' delta hDelta x hLeftZero hMinimal

omit [Fintype R] [Fintype R'] in
/-- A smaller allowed decrease gives a stronger minimality condition. -/
theorem isDeltaMinimal_mono
    (h : Matrix R W F) (h' : Matrix R' W F)
    (x : Matrix W W F) {delta delta' : ℝ}
    (hdelta : delta ≤ delta')
    (hMinimal : IsDeltaMinimal h h' delta x) :
    IsDeltaMinimal h h' delta' x := by
  rcases hMinimal with ⟨hRows, hCols⟩
  constructor
  · intro i c hc
    exact (hRows i c hc).trans (add_le_add_right hdelta _)
  · intro j c hc
    exact (hCols j c hc).trans (add_le_add_right hdelta _)

/-- Hamming weight restricted to a coordinate rectangle. -/
def restrictedWeight (x : Matrix W W F) (A B : Finset W) : Nat :=
  ∑ i ∈ A, ∑ j ∈ B, if x i j = 0 then 0 else 1

/-- Source-faithful `(s,m,beta)` product expansion, with `delta = beta * w`. -/
def ProductExpanding (h : Matrix R W F) (h' : Matrix R' W F)
    (s m : Nat) (beta : ℝ) : Prop :=
  ∀ x : Matrix W W F, ProductKernel h h' x → x ≠ 0 →
    IsDeltaMinimal h h' (beta * Fintype.card W) x →
      ∀ A B : Finset W,
        Fintype.card W - m ≤ A.card → Fintype.card W - m ≤ B.card →
          s ≤ restrictedWeight x A B

omit [Fintype R] [Fintype R'] in
/-- Expansion persists under weaker output and rectangle bounds and stricter minimality. -/
theorem productExpanding_mono
    (h : Matrix R W F) (h' : Matrix R' W F)
    {s s' m m' : Nat} {beta beta' : ℝ}
    (hExpand : ProductExpanding h h' s m beta)
    (hs : s' ≤ s) (hm : m' ≤ m) (hbeta : beta' ≤ beta) :
    ProductExpanding h h' s' m' beta' := by
  intro x hx hx0 hMinimal A B hA hB
  have hDelta : beta' * Fintype.card W ≤ beta * Fintype.card W :=
    mul_le_mul_of_nonneg_right hbeta (Nat.cast_nonneg _)
  have hMinimal' := isDeltaMinimal_mono h h' x hDelta hMinimal
  have hA' : Fintype.card W - m ≤ A.card := by omega
  have hB' : Fintype.card W - m ≤ B.card := by omega
  exact hs.trans (hExpand x hx hx0 hMinimal' A B hA' hB')

omit [Fintype F] [DecidableEq F] [Fintype R] [Fintype R'] in
/-- Transposition exchanges the two product-kernel parity checks. -/
theorem productKernel_transpose_iff
    (h : Matrix R W F) (h' : Matrix R' W F) (x : Matrix W W F) :
    ProductKernel h h' x ↔ ProductKernel h' h x.transpose := by
  unfold ProductKernel
  constructor
  · intro hx
    have ht := congrArg Matrix.transpose hx
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_zero, Matrix.mul_assoc] using ht
  · intro hx
    have ht := congrArg Matrix.transpose hx
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_zero, Matrix.mul_assoc] using ht

omit [Fintype F] [Fintype W] in
/-- Transposition exchanges the two axes of a restricted rectangle. -/
theorem restrictedWeight_transpose (x : Matrix W W F) (A B : Finset W) :
    restrictedWeight x.transpose A B = restrictedWeight x B A := by
  simp only [restrictedWeight, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  rfl

omit [Fintype R] [Fintype R'] in
/-- Row and column minimality are exchanged by matrix transposition. -/
theorem isDeltaMinimal_transpose_iff
    (h : Matrix R W F) (h' : Matrix R' W F)
    (delta : ℝ) (x : Matrix W W F) :
    IsDeltaMinimal h h' delta x.transpose ↔
      IsDeltaMinimal h' h delta x := by
  simp only [IsDeltaMinimal, row_transpose, column_transpose, and_comm]

omit [Fintype R] [Fintype R'] in
/-- Nonzero-block lemma in the opposite rectangle orientation, obtained by
transposing the matrix and exchanging the two local codes. -/
theorem eq_zero_of_zero_rectangle_transpose
    (h : Matrix R W F) (h' : Matrix R' W F) (d d' : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d' ≤ HammingWeight c)
    (A B : Finset W)
    (hLargeA : Fintype.card W - d' < A.card)
    (hLargeB : Fintype.card W - d < B.card)
    (delta : ℝ)
    (hGap : 2 * (Fintype.card W - A.card : ℝ) + delta < d')
    (hDelta : delta < d)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hMinimal : IsDeltaMinimal h h' delta x)
    (hRectangle : ∀ i ∈ A, ∀ j ∈ B, x i j = 0) :
    x = 0 := by
  have hTransposeKernel : ProductKernel h' h x.transpose :=
    (productKernel_transpose_iff h h' x).mp hx
  have hTransposeMinimal : IsDeltaMinimal h' h delta x.transpose :=
    (isDeltaMinimal_transpose_iff h' h delta x).mpr hMinimal
  have hTransposeRectangle :
      ∀ i ∈ B, ∀ j ∈ A, x.transpose i j = 0 := by
    intro i hi j hj
    exact hRectangle j hj i hi
  have hTransposeZero :=
    eq_zero_of_zero_rectangle h' h d' d hDistance' hDistance
      A B hLargeA hLargeB delta hGap hDelta
      x.transpose hTransposeKernel hTransposeMinimal hTransposeRectangle
  have hOriginal := congrArg Matrix.transpose hTransposeZero
  simpa using hOriginal

omit [Fintype R] [Fintype R'] in
/-- The paper's `d/3` numerical choice for the first zero-rectangle orientation.
The explicit `d ≤ w` assumption records that the advertised local distance is
a code length bound; it also makes the natural-number complement inequality
equivalent to its real-valued form. -/
theorem eq_zero_of_zero_rectangle_one_third
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (A B : Finset W)
    (hSizeA : (Fintype.card W : ℝ) - A.card < (d : ℝ) / 3)
    (hSizeB : Fintype.card W - d < B.card)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (hRectangle : ∀ i ∈ B, ∀ j ∈ A, x i j = 0) :
    x = 0 := by
  have hCastComplement : ((Fintype.card W - d : Nat) : ℝ) =
      (Fintype.card W : ℝ) - d := Nat.cast_sub hLength
  have hLargeReal : ((Fintype.card W - d : Nat) : ℝ) < A.card := by
    rw [hCastComplement]
    linarith
  have hLargeA : Fintype.card W - d < A.card := by exact_mod_cast hLargeReal
  have hPositiveReal : (0 : ℝ) < d := by exact_mod_cast hPositive
  have hGap : 2 * (Fintype.card W - A.card : ℝ) + (d : ℝ) / 3 < d := by
    linarith
  have hDelta : (d : ℝ) / 3 < d := by linarith
  exact eq_zero_of_zero_rectangle h h' d d hDistance hDistance'
    A B hLargeA hSizeB ((d : ℝ) / 3) hGap hDelta x hx hMinimal hRectangle

omit [Fintype R] [Fintype R'] in
/-- The source's nonzero-block lemma in both rectangle orientations. -/
theorem eq_zero_of_zero_rectangle_one_third_either
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (A B : Finset W)
    (hSizeA : (Fintype.card W : ℝ) - A.card < (d : ℝ) / 3)
    (hSizeB : Fintype.card W - d < B.card)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (hRectangle : (∀ i ∈ B, ∀ j ∈ A, x i j = 0) ∨
      (∀ i ∈ A, ∀ j ∈ B, x i j = 0)) :
    x = 0 := by
  rcases hRectangle with hFirst | hSecond
  · exact eq_zero_of_zero_rectangle_one_third h h' d hPositive hLength
      hDistance hDistance' A B hSizeA hSizeB x hx hMinimal hFirst
  · have hTransposeKernel : ProductKernel h' h x.transpose :=
      (productKernel_transpose_iff h h' x).mp hx
    have hTransposeMinimal : IsDeltaMinimal h' h ((d : ℝ) / 3) x.transpose :=
      (isDeltaMinimal_transpose_iff h' h ((d : ℝ) / 3) x).mpr hMinimal
    have hTransposeRectangle :
        ∀ i ∈ B, ∀ j ∈ A, x.transpose i j = 0 := by
      intro i hi j hj
      exact hSecond j hj i hi
    have hTransposeZero :=
      eq_zero_of_zero_rectangle_one_third h' h d hPositive hLength
        hDistance' hDistance A B hSizeA hSizeB
        x.transpose hTransposeKernel hTransposeMinimal hTransposeRectangle
    have hOriginal := congrArg Matrix.transpose hTransposeZero
    simpa using hOriginal

/-- Indices of nonzero rows of a product-code matrix. -/
def nonzeroRows (x : Matrix W W F) : Finset W :=
  Finset.univ.filter (fun i => row x i ≠ 0)

/-- Indices of nonzero columns of a product-code matrix. -/
def nonzeroColumns (x : Matrix W W F) : Finset W :=
  Finset.univ.filter (fun j => column x j ≠ 0)

/-- Rows touched by the selected columns of a matrix. -/
noncomputable def nonzeroRowsOnColumns (x : Matrix W W F) (B : Finset W) : Finset W := by
  classical
  exact Finset.univ.filter (fun i => ∃ j ∈ B, x i j ≠ 0)

/-- Columns touched by the selected rows of a matrix. -/
noncomputable def nonzeroColumnsOnRows (x : Matrix W W F) (B : Finset W) : Finset W := by
  classical
  exact Finset.univ.filter (fun j => ∃ i ∈ B, x i j ≠ 0)

/-- Coordinates touched by any member of a finite set of word generators. -/
noncomputable def generatorSupport (C : Finset (Word F W)) : Finset W := by
  classical
  exact C.biUnion hammingSupport

/-- The subspace of words supported inside a selected coordinate set. -/
noncomputable def supportedWords (S : Finset W) : Submodule F (Word F W) := by
  classical
  exact LinearMap.ker (restrictionLinearMap (Finset.univ \ S))

omit [Fintype F] [DecidableEq F] [Fintype R] [Fintype R'] in
/-- Membership in the supported-word subspace is coordinatewise vanishing
outside the selected support. -/
theorem mem_supportedWords_iff (S : Finset W) (y : Word F W) :
    y ∈ supportedWords S ↔ ∀ i ∉ S, y i = 0 := by
  classical
  change restrictionLinearMap (Finset.univ \ S) y = 0 ↔ _
  constructor
  · intro hy i hiS
    have hi : i ∈ Finset.univ \ S := by simp [hiS]
    exact congrFun hy ⟨i, hi⟩
  · intro hy
    funext i
    exact hy i.1 (Finset.mem_sdiff.mp i.2).2

omit [Fintype F] [Fintype R] [Fintype R'] in
/-- The span of finitely many generators is supported inside their support
union. -/
theorem generator_span_le_supportedWords (C : Finset (Word F W)) :
    Submodule.span F (C : Set (Word F W)) ≤ supportedWords (generatorSupport C) := by
  classical
  apply Submodule.span_le.mpr
  intro c hc
  apply (mem_supportedWords_iff (generatorSupport C) c).mpr
  intro i hiS
  by_contra hNonzero
  have hiSupport : i ∈ hammingSupport c := by
    simpa [hammingSupport] using hNonzero
  have hiUnion : i ∈ generatorSupport C := by
    exact Finset.mem_biUnion.mpr ⟨c, hc, hiSupport⟩
  exact hiS hiUnion

/-- The space generated by the syndromes of finitely many word generators. -/
noncomputable def syndromeSpan (h' : Matrix R' W F)
    (C : Finset (Word F W)) : Submodule F (R' → F) :=
  Submodule.span F ((fun y : Word F W => h'.mulVec y) '' (C : Set (Word F W)))

omit [Fintype F] [Fintype R] [Fintype R'] in
/-- Membership in the span of generator syndromes has an actual word lift
supported inside the generators' support union. -/
theorem exists_supported_syndrome_lift_of_mem_span
    (h' : Matrix R' W F) (C : Finset (Word F W)) (z : R' → F)
    (hz : z ∈ syndromeSpan h' C) :
    ∃ y : Word F W,
      (∀ i ∉ generatorSupport C, y i = 0) ∧ h'.mulVec y = z := by
  classical
  have hMapSpan :
      (Submodule.span F (C : Set (Word F W))).map (Matrix.toLin' h') =
        syndromeSpan h' C := by
    unfold syndromeSpan
    have hFun : (fun y : Word F W => (Matrix.toLin' h') y) =
        (fun y : Word F W => h'.mulVec y) := by
      funext y
      exact Matrix.toLin'_apply h' y
    simpa only [hFun] using
      (Submodule.map_span (Matrix.toLin' h') (C : Set (Word F W)))
  rw [← hMapSpan] at hz
  obtain ⟨y, hySpan, hySyndrome⟩ := hz
  refine ⟨y, ?_, ?_⟩
  · exact (mem_supportedWords_iff (generatorSupport C) y).mp
      ((generator_span_le_supportedWords C) hySpan)
  · simpa only [Matrix.toLin'_apply] using hySyndrome

omit [Fintype F] [Fintype R] in
/-- A rank-sized family whose syndromes span every column spans exactly the
column space of `h' * x`; it cannot hide extraneous syndrome directions. -/
theorem syndromeSpan_eq_matrix_range_of_rank_sized
    (h' : Matrix R' W F) (x : Matrix W W F)
    (C : Finset (Word F W))
    (hCard : C.card = (h' * x).rank)
    (hSpanning : ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) :
    syndromeSpan h' C = LinearMap.range (h' * x).mulVecLin := by
  classical
  let M : Matrix R' W F := h' * x
  have hRangeLe : LinearMap.range M.mulVecLin ≤ syndromeSpan h' C := by
    rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro z ⟨j, rfl⟩
    have hColumn : M.col j = h'.mulVec (column x j) := by
      ext i
      simp [M, Matrix.mul_apply, Matrix.mulVec, dotProduct, column]
    rw [hColumn]
    exact hSpanning j
  let G : Finset (R' → F) := C.image (fun y => h'.mulVec y)
  have hSpanG : syndromeSpan h' C = Submodule.span F (G : Set (R' → F)) := by
    simp [syndromeSpan, G]
  have hDimG : Module.finrank F (Submodule.span F (G : Set (R' → F))) ≤
      G.card := by
    exact finrank_span_finset_le_card (R := F) G
  have hGCard : G.card ≤ C.card := Finset.card_image_le
  have hDimS : Module.finrank F (syndromeSpan h' C) ≤
      Module.finrank F (LinearMap.range M.mulVecLin) := by
    rw [hSpanG]
    have hRank : Module.finrank F (LinearMap.range M.mulVecLin) = M.rank := rfl
    rw [hRank]
    change Module.finrank F (Submodule.span F (G : Set (R' → F))) ≤ M.rank
    exact hDimG.trans (hGCard.trans (le_of_eq (by simpa [M] using hCard)))
  have hEq := Submodule.eq_of_le_of_finrank_le hRangeLe hDimS
  simpa [M] using hEq.symm

omit [Fintype F] [Fintype R] in
/-- The syndromes of a rank-sized spanning family are linearly independent,
so they form a genuine basis of the syndrome column space. -/
theorem syndromeGenerators_linearIndependent_of_rank_sized
    (h' : Matrix R' W F) (x : Matrix W W F)
    (C : Finset (Word F W))
    (hCard : C.card = (h' * x).rank)
    (hSpanning : ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) :
    LinearIndependent F (fun c : C => h'.mulVec c.1) := by
  classical
  have hRangeSet : Set.range (fun c : C => h'.mulVec c.1) =
      (fun y : Word F W => h'.mulVec y) '' (C : Set (Word F W)) := by
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c.1, c.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  apply (linearIndependent_iff_card_eq_finrank_span).mpr
  change Fintype.card C = Module.finrank F
    (Submodule.span F (Set.range (fun c : C => h'.mulVec c.1)))
  rw [hRangeSet]
  change Fintype.card C = Module.finrank F (syndromeSpan h' C)
  rw [syndromeSpan_eq_matrix_range_of_rank_sized h' x C hCard hSpanning]
  simpa [Matrix.rank] using hCard

omit [Fintype F] [Fintype R] in
/-- Package the rank-sized generating syndromes as a basis indexed by the
actual representative words. This exposes basis coordinates for the exchange
step of the rank argument. -/
theorem exists_syndromeBasis_of_rank_sized
    (h' : Matrix R' W F) (x : Matrix W W F)
    (C : Finset (Word F W))
    (hCard : C.card = (h' * x).rank)
    (hSpanning : ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) :
    ∃ b : Module.Basis C F (syndromeSpan h' C),
      ∀ c : C, (b c).1 = h'.mulVec c.1 := by
  classical
  let S := syndromeSpan h' C
  have hMem (c : C) : h'.mulVec c.1 ∈ S := by
    apply Submodule.subset_span
    exact ⟨c.1, c.2, rfl⟩
  let v : C → S := fun c => ⟨h'.mulVec c.1, hMem c⟩
  have hLI : LinearIndependent F v := by
    have hAmbient := syndromeGenerators_linearIndependent_of_rank_sized
      h' x C hCard hSpanning
    apply ((S.subtype).linearIndependent_iff (by simp)).mp
    simpa [v, Function.comp_def] using hAmbient
  have hRangeSet : Set.range (fun c : C => h'.mulVec c.1) =
      (fun y : Word F W => h'.mulVec y) '' (C : Set (Word F W)) := by
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c.1, c.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hSpanVal : Submodule.span F (Set.range
      (fun c : C => h'.mulVec c.1)) = S := by
    rw [hRangeSet]
    rfl
  have hSpanTop : ⊤ ≤ Submodule.span F (Set.range v) := by
    rw [(Submodule.span_range_subtype_eq_top_iff S hMem).mpr hSpanVal]
  refine ⟨Module.Basis.mk hLI hSpanTop, ?_⟩
  intro c
  exact congrArg Subtype.val (Module.Basis.mk_apply hLI hSpanTop c)

omit [Fintype F] [DecidableEq F] [Fintype R] [Fintype R'] in
/-- A syndrome outside the span of selected generators has a nonzero basis
coordinate on some generator outside that selection. -/
theorem exists_generator_coordinate_outside_span
    (h' : Matrix R' W F) (C T : Finset (Word F W))
    (b : Module.Basis C F (syndromeSpan h' C))
    (hb : ∀ c : C, (b c).1 = h'.mulVec c.1)
    (z : syndromeSpan h' C)
    (hz : (z.1 : R' → F) ∉ syndromeSpan h' T) :
    ∃ c : C, c.1 ∉ T ∧ (b.repr z) c ≠ 0 := by
  classical
  let I : Set C := {c | c.1 ∈ T}
  have hSpanLe : Submodule.span F (b '' I) ≤
      (syndromeSpan h' T).comap (syndromeSpan h' C).subtype := by
    apply Submodule.span_le.mpr
    rintro v ⟨c, hcI, rfl⟩
    change (b c).1 ∈ syndromeSpan h' T
    rw [hb c]
    apply Submodule.subset_span
    exact ⟨c.1, hcI, rfl⟩
  have hNotSpan : z ∉ Submodule.span F (b '' I) := by
    intro hzSpan
    exact hz (hSpanLe hzSpan)
  have hNotSubset : ¬((b.repr z).support : Set C) ⊆ I := by
    intro hSubset
    exact hNotSpan ((b.mem_span_image).mpr hSubset)
  obtain ⟨c, hcSupport, hcNotI⟩ := Set.not_subset.mp hNotSubset
  exact ⟨c, hcNotI, by simpa using hcSupport⟩

omit [Fintype F] [DecidableEq F] [Fintype R] [Fintype R'] in
/-- A vector with a nonzero coordinate at `c` can replace the corresponding
basis vector without changing the span. This is the linear-algebra exchange
used by the minimum-weight syndrome-generator argument. -/
theorem syndromeBasis_exchange_spans
    (h' : Matrix R' W F) (C : Finset (Word F W))
    (b : Module.Basis C F (syndromeSpan h' C))
    (c : C) (z : syndromeSpan h' C)
    (hCoordinate : (b.repr z) c ≠ 0) :
    Submodule.span F (insert z (b '' {a : C | a ≠ c})) = ⊤ := by
  classical
  let I : Set C := {a | a ≠ c}
  have hNotSpan : z ∉ Submodule.span F (b '' I) := by
    intro hz
    have hSubset := (b.mem_span_image).mp hz
    exact hCoordinate (by
      have hcSupport : c ∈ (b.repr z).support := Finsupp.mem_support_iff.mpr hCoordinate
      exact False.elim ((hSubset hcSupport) rfl))
  have hRangeSubset : Set.range b ⊆ insert (b c) (b '' I) := by
    rintro v ⟨a, rfl⟩
    by_cases ha : a = c
    · simp [ha]
    · exact Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩
  have hzOld : z ∈ Submodule.span F (insert (b c) (b '' I)) :=
    Submodule.span_mono hRangeSubset (b.mem_span z)
  have hcNew : b c ∈ Submodule.span F (insert z (b '' I)) :=
    mem_span_insert_exchange hzOld hNotSpan
  apply (Submodule.eq_top_iff_forall_basis_mem b).mpr
  intro a
  by_cases ha : a = c
  · simpa [I, ha] using hcNew
  · apply Submodule.subset_span
    exact Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩

omit [Fintype F] [Fintype R] [Fintype R'] in
/-- Replacing one word representative by a word whose syndrome has a
nonzero coordinate at that representative preserves the span of all original
syndromes. -/
theorem syndromeSpan_le_of_exchange
    (h' : Matrix R' W F) (C : Finset (Word F W))
    (b : Module.Basis C F (syndromeSpan h' C))
    (hb : ∀ a : C, (b a).1 = h'.mulVec a.1)
    (c : C) (y : Word F W)
    (hy : h'.mulVec y ∈ syndromeSpan h' C)
    (hCoordinate : (b.repr ⟨h'.mulVec y, hy⟩) c ≠ 0) :
    syndromeSpan h' C ≤ syndromeSpan h' (insert y (C.erase c.1)) := by
  classical
  let D := insert y (C.erase c.1)
  let S := syndromeSpan h' C
  let P := (syndromeSpan h' D).comap S.subtype
  let z : S := ⟨h'.mulVec y, hy⟩
  have hExchange : Submodule.span F (insert z (b '' {a : C | a ≠ c})) = ⊤ :=
    syndromeBasis_exchange_spans h' C b c z hCoordinate
  have hGeneratorsNew : insert z (b '' {a : C | a ≠ c}) ⊆ P := by
    rintro v (rfl | ⟨a, ha, rfl⟩)
    · change h'.mulVec y ∈ syndromeSpan h' D
      apply Submodule.subset_span
      exact ⟨y, Finset.mem_insert_self _ _, rfl⟩
    · change (b a).1 ∈ syndromeSpan h' D
      rw [hb a]
      apply Submodule.subset_span
      refine ⟨a.1, Finset.mem_insert_of_mem ?_, rfl⟩
      exact Finset.mem_erase.mpr ⟨by
        intro heq
        exact ha (Subtype.ext heq), a.2⟩
  have hAllBasis (a : C) : (b a).1 ∈ syndromeSpan h' D := by
    have ha : b a ∈ Submodule.span F (insert z (b '' {a : C | a ≠ c})) := by
      rw [hExchange]
      trivial
    exact (Submodule.span_le.mpr hGeneratorsNew) ha
  apply Submodule.span_le.mpr
  rintro v ⟨a, ha, rfl⟩
  change h'.mulVec a ∈ syndromeSpan h' (insert y (C.erase c.1))
  simpa only [D, hb ⟨a, ha⟩] using hAllBasis ⟨a, ha⟩

omit [Fintype F] [Fintype R] [Fintype R'] in
/-- A word with a nonzero replacement coordinate is not among the other
generators, so a single-word exchange preserves cardinality. -/
theorem card_syndromeGenerators_exchange
    (h' : Matrix R' W F) (C : Finset (Word F W))
    (b : Module.Basis C F (syndromeSpan h' C))
    (hb : ∀ a : C, (b a).1 = h'.mulVec a.1)
    (c : C) (y : Word F W)
    (hy : h'.mulVec y ∈ syndromeSpan h' C)
    (hCoordinate : (b.repr ⟨h'.mulVec y, hy⟩) c ≠ 0) :
    (insert y (C.erase c.1)).card = C.card := by
  classical
  have hyNotErase : y ∉ C.erase c.1 := by
    intro hyErase
    let a : C := ⟨y, Finset.mem_of_mem_erase hyErase⟩
    have haNe : a ≠ c := by
      intro heq
      exact (Finset.ne_of_mem_erase hyErase) (congrArg Subtype.val heq)
    have hSame : (⟨h'.mulVec y, hy⟩ : syndromeSpan h' C) = b a := by
      apply Subtype.ext
      exact (hb a).symm
    apply hCoordinate
    rw [hSame, b.repr_self]
    simp [haNe]
  rw [Finset.card_insert_of_notMem hyNotErase]
  have hc : c.1 ∈ C := c.2
  have hErase := Finset.card_erase_add_one hc
  omega

/-- Hamming weight of a word restricted to one coordinate set. -/
def restrictedHammingWeight (A : Finset W) (y : Word F W) : Nat :=
  ∑ i ∈ A, if y i = 0 then 0 else 1

omit [Fintype F] [Fintype W] [Fintype R] [Fintype R'] in
/-- Count the nonzero entries of a rectangle by columns. -/
theorem restrictedWeight_eq_sum_column_restrictedHammingWeight
    (x : Matrix W W F) (A B : Finset W) :
    restrictedWeight x A B =
      ∑ j ∈ B, restrictedHammingWeight A (column x j) := by
  classical
  simp only [restrictedWeight, restrictedHammingWeight, column]
  exact Finset.sum_comm

/-- Total restricted weight of a finite syndrome-generating family. -/
def generatorRestrictedWeight (A : Finset W) (C : Finset (Word F W)) : Nat :=
  ∑ y ∈ C, restrictedHammingWeight A y

/-- Generators lighter than the average threshold `d/(6|C|)` on `A`. -/
noncomputable def lightGenerators (A : Finset W)
    (C : Finset (Word F W)) (d : Nat) : Finset (Word F W) := by
  classical
  exact C.filter (fun y => 6 * C.card * restrictedHammingWeight A y < d)

omit [Fintype F] [Fintype R] [Fintype R'] in
/-- The total restricted weight of the light generators is below `d/6`.
This threshold formulation replaces the paper's sorted-prefix choice. -/
theorem lightGenerators_restrictedWeight_lt_one_sixth
    (A : Finset W) (C : Finset (Word F W)) (d : Nat)
    (hCPositive : 0 < C.card) (hDPositive : 0 < d) :
    (generatorRestrictedWeight A (lightGenerators A C d) : ℝ) < (d : ℝ) / 6 := by
  classical
  let T := lightGenerators A C d
  have hTSubset : T ⊆ C := by
    intro y hy
    exact (Finset.mem_filter.mp hy).1
  have hTCard : (T.card : ℝ) ≤ C.card := by
    exact_mod_cast Finset.card_le_card hTSubset
  have hCPositiveReal : (0 : ℝ) < C.card := by exact_mod_cast hCPositive
  have hDPositiveReal : (0 : ℝ) < d := by exact_mod_cast hDPositive
  by_cases hTEmpty : T = ∅
  · simp [T, hTEmpty, generatorRestrictedWeight]
    positivity
  · have hTNonempty : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hTEmpty
    have hEach (y : Word F W) (hy : y ∈ T) :
        (6 : ℝ) * C.card * restrictedHammingWeight A y < d := by
      have hNat : 6 * C.card * restrictedHammingWeight A y < d :=
        (Finset.mem_filter.mp hy).2
      exact_mod_cast hNat
    have hSum := Finset.sum_lt_sum_of_nonempty hTNonempty hEach
    have hSumLt : (6 : ℝ) * C.card * generatorRestrictedWeight A T <
        (T.card : ℝ) * d := by
      simpa [generatorRestrictedWeight, Finset.mul_sum,
        Nat.cast_sum, Nat.cast_mul] using hSum
    have hCardTimes : (T.card : ℝ) * d ≤ C.card * d :=
      mul_le_mul_of_nonneg_right hTCard hDPositiveReal.le
    have hBound : (C.card : ℝ) *
        ((6 : ℝ) * generatorRestrictedWeight A T) < C.card * d := by
      nlinarith
    have hSmall : (6 : ℝ) * generatorRestrictedWeight A T < d :=
      (mul_lt_mul_iff_of_pos_left hCPositiveReal).mp hBound
    linarith

/-- The union of generator supports inside the selected coordinates. -/
noncomputable def generatorSupportOn (A : Finset W) (C : Finset (Word F W)) :
    Finset W := by
  classical
  exact generatorSupport C ∩ A

omit [Fintype F] [Fintype R] [Fintype R'] in
/-- The support union inside `A` is bounded by the sum of the generators'
restricted Hamming weights. -/
theorem card_generatorSupport_inter_le_generatorRestrictedWeight
    (A : Finset W) (C : Finset (Word F W)) :
    (generatorSupportOn A C).card ≤ generatorRestrictedWeight A C := by
  classical
  unfold generatorSupportOn
  have hSubset : generatorSupport C ∩ A ⊆
      C.biUnion (fun y => hammingSupport y ∩ A) := by
    intro i hi
    obtain ⟨hiSupport, hiA⟩ := Finset.mem_inter.mp hi
    obtain ⟨y, hyC, hiy⟩ := Finset.mem_biUnion.mp hiSupport
    exact Finset.mem_biUnion.mpr ⟨y, hyC,
      Finset.mem_inter.mpr ⟨hiy, hiA⟩⟩
  calc
    (generatorSupport C ∩ A).card ≤
        (C.biUnion (fun y => hammingSupport y ∩ A)).card :=
      Finset.card_le_card hSubset
    _ ≤ ∑ y ∈ C, (hammingSupport y ∩ A).card := Finset.card_biUnion_le
    _ = generatorRestrictedWeight A C := by
      unfold generatorRestrictedWeight
      apply Finset.sum_congr rfl
      intro y _
      have hInter : hammingSupport y ∩ A =
          A.filter (fun i => y i ≠ 0) := by
        ext i
        simp [hammingSupport, and_comm]
      rw [hInter]
      unfold restrictedHammingWeight
      calc
        (A.filter (fun i => y i ≠ 0)).card =
            ∑ i ∈ A, if y i ≠ 0 then 1 else 0 := by
          simpa using (Finset.sum_boole (R := Nat) (fun i => y i ≠ 0) A).symm
        _ = ∑ i ∈ A, if y i = 0 then 0 else 1 := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : y i = 0 <;> simp [hi]

omit [Fintype F] [Fintype R] [Fintype R'] in
/-- The paper's support-union counting step: if the common support has size
at least `d/3` and at most `m ≤ d/6` coordinates lie outside `A`, the total
restricted generator weight is at least `d/6`. -/
theorem generatorRestrictedWeight_ge_one_sixth_of_large_support
    (d m : Nat) (hLength : d ≤ Fintype.card W) (hSmallM : 6 * m ≤ d)
    (A : Finset W) (hLargeA : Fintype.card W - m ≤ A.card)
    (C : Finset (Word F W))
    (hSupport : (d : ℝ) / 3 ≤ (generatorSupport C).card) :
    (d : ℝ) / 6 ≤ generatorRestrictedWeight A C := by
  classical
  let S := generatorSupport C
  have hWeight := card_generatorSupport_inter_le_generatorRestrictedWeight A C
  change (S ∩ A).card ≤ generatorRestrictedWeight A C at hWeight
  have hSdiffSubset : S \ A ⊆ Finset.univ \ A := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, (Finset.mem_sdiff.mp hi).2⟩
  have hSdiffCard := Finset.card_le_card hSdiffSubset
  have hComplement : (Finset.univ \ A).card = Fintype.card W - A.card := by
    simpa using Finset.card_sdiff_of_subset (Finset.subset_univ A)
  rw [hComplement] at hSdiffCard
  have hComplementSmall : Fintype.card W - A.card ≤ m := by omega
  have hSCard : S.card = (S ∩ A).card + (S \ A).card := by
    exact (Finset.card_inter_add_card_sdiff S A).symm
  have hSupportNat : S.card ≤ generatorRestrictedWeight A C + m := by omega
  have hSupportReal : (d : ℝ) / 3 ≤ S.card := hSupport
  have hSupportBoundReal : (S.card : ℝ) ≤ generatorRestrictedWeight A C + m := by
    exact_mod_cast hSupportNat
  have hSmallMReal : (6 : ℝ) * m ≤ d := by exact_mod_cast hSmallM
  linarith

omit [Fintype F] [Fintype R] [Fintype R'] in
/-- The converse counting direction needed for the light-generator prefix:
total restricted weight below `d/6` confines the entire support union to
fewer than `d/3` coordinates. -/
theorem generatorSupport_card_lt_one_third_of_small_restricted_weight
    (d m : Nat) (hLength : d ≤ Fintype.card W) (hSmallM : 6 * m ≤ d)
    (A : Finset W) (hLargeA : Fintype.card W - m ≤ A.card)
    (C : Finset (Word F W))
    (hWeight : (generatorRestrictedWeight A C : ℝ) < (d : ℝ) / 6) :
    ((generatorSupport C).card : ℝ) < (d : ℝ) / 3 := by
  classical
  let S := generatorSupport C
  have hInterWeight := card_generatorSupport_inter_le_generatorRestrictedWeight A C
  change (S ∩ A).card ≤ generatorRestrictedWeight A C at hInterWeight
  have hSdiffSubset : S \ A ⊆ Finset.univ \ A := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, (Finset.mem_sdiff.mp hi).2⟩
  have hSdiffCard := Finset.card_le_card hSdiffSubset
  have hComplement : (Finset.univ \ A).card = Fintype.card W - A.card := by
    simpa using Finset.card_sdiff_of_subset (Finset.subset_univ A)
  rw [hComplement] at hSdiffCard
  have hComplementSmall : Fintype.card W - A.card ≤ m := by omega
  have hSCard : S.card = (S ∩ A).card + (S \ A).card :=
    (Finset.card_inter_add_card_sdiff S A).symm
  have hSupportNat : S.card ≤ generatorRestrictedWeight A C + m := by omega
  have hSupportReal : (S.card : ℝ) ≤ generatorRestrictedWeight A C + m := by
    exact_mod_cast hSupportNat
  have hSmallMReal : (6 : ℝ) * m ≤ d := by exact_mod_cast hSmallM
  linarith

omit [Fintype R] [Fintype R'] in
/-- If the selected generators have total restricted weight below `d/6`,
every matrix column whose syndrome lies in their span is supported inside
their common support union. -/
theorem column_vanish_outside_generatorSupport_of_small_weight
    (h : Matrix R W F) (h' : Matrix R' W F) (d m : Nat)
    (hLength : d ≤ Fintype.card W) (hSmallM : 6 * m ≤ d)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (A : Finset W) (hLargeA : Fintype.card W - m ≤ A.card)
    (C : Finset (Word F W))
    (hWeight : (generatorRestrictedWeight A C : ℝ) < (d : ℝ) / 6)
    (j : W) (hSyndrome : h'.mulVec (column x j) ∈ syndromeSpan h' C) :
    ∀ i ∉ generatorSupport C, x i j = 0 := by
  have hSmallSupport :=
    generatorSupport_card_lt_one_third_of_small_restricted_weight
      d m hLength hSmallM A hLargeA C hWeight
  obtain ⟨y, hSupported, hLift⟩ :=
    exists_supported_syndrome_lift_of_mem_span
      h' C (h'.mulVec (column x j)) hSyndrome
  have hEqual := column_eq_small_support_syndrome_lift
    h h' d hDistance' x hMinimal (generatorSupport C)
      hSmallSupport j y hSupported hLift
  intro i hi
  exact (congrFun hEqual i).trans (hSupported i hi)

/-- Columns whose syndromes lie in the span of a selected generator family. -/
noncomputable def columnsWithSyndromeInSpan
    (h' : Matrix R' W F) (x : Matrix W W F)
    (C : Finset (Word F W)) : Finset W := by
  classical
  exact Finset.univ.filter (fun j =>
    h'.mulVec (column x j) ∈ syndromeSpan h' C)

/-- Columns whose syndromes escape the selected generator span. -/
noncomputable def columnsOutsideSyndromeSpan
    (h' : Matrix R' W F) (x : Matrix W W F)
    (C : Finset (Word F W)) : Finset W := by
  classical
  exact Finset.univ \ columnsWithSyndromeInSpan h' x C

omit [Fintype R] [Fintype R'] in
/-- The first rank-lemma consequence of nonzero-block: a nonzero minimal
product codeword has at least `d` nonzero rows. -/
theorem card_nonzeroRows_ge_distance
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x) :
    d ≤ (nonzeroRows x).card := by
  classical
  by_contra hNot
  have hFew : (nonzeroRows x).card < d := by omega
  let B : Finset W := Finset.univ \ nonzeroRows x
  have hBCard : B.card = Fintype.card W - (nonzeroRows x).card := by
    simpa [B] using Finset.card_sdiff_of_subset (Finset.subset_univ (nonzeroRows x))
  have hSizeB : Fintype.card W - d < B.card := by omega
  have hPositiveReal : (0 : ℝ) < d := by exact_mod_cast hPositive
  have hSizeA : (Fintype.card W : ℝ) - (Finset.univ : Finset W).card <
      (d : ℝ) / 3 := by simp; positivity
  have hRectangle :
      ∀ i ∈ B, ∀ j ∈ (Finset.univ : Finset W), x i j = 0 := by
    intro i hi j _
    have hZeroRow : row x i = 0 := by
      by_contra hRowNonzero
      have hiNonzero : i ∈ nonzeroRows x :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hRowNonzero⟩
      exact (Finset.mem_sdiff.mp hi).2 hiNonzero
    exact congrFun hZeroRow j
  have hZero := eq_zero_of_zero_rectangle_one_third h h' d
    hPositive hLength hDistance hDistance'
    Finset.univ B hSizeA hSizeB x hx hMinimal hRectangle
  exact hxNonzero hZero

omit [Fintype R] [Fintype R'] in
/-- The companion rank-lemma consequence: at least `d` nonzero columns. -/
theorem card_nonzeroColumns_ge_distance
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x) :
    d ≤ (nonzeroColumns x).card := by
  have hxT : ProductKernel h' h x.transpose :=
    (productKernel_transpose_iff h h' x).mp hx
  have hxTNonzero : x.transpose ≠ 0 := by
    intro hZero
    apply hxNonzero
    have hOriginal := congrArg Matrix.transpose hZero
    simpa using hOriginal
  have hMinimalT : IsDeltaMinimal h' h ((d : ℝ) / 3) x.transpose :=
    (isDeltaMinimal_transpose_iff h' h _ x).mpr hMinimal
  have hRows := card_nonzeroRows_ge_distance h' h d hPositive hLength
    hDistance' hDistance x.transpose hxT hxTNonzero hMinimalT
  have hTransposeRows : nonzeroRows x.transpose = nonzeroColumns x := by
    classical
    unfold nonzeroRows nonzeroColumns
    apply Finset.filter_congr
    intro i _
    simp only [row_transpose]
  rw [hTransposeRows] at hRows
  exact hRows

omit [Fintype R] [Fintype R'] in
/-- Every sufficiently large selection of columns of a nonzero minimal
product codeword meets at least `d/3` rows. -/
theorem card_nonzeroRowsOnColumns_ge_one_third_distance
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (B : Finset W) (hSizeB : Fintype.card W - d < B.card) :
    (d : ℝ) / 3 ≤ (nonzeroRowsOnColumns x B).card := by
  classical
  by_contra hNot
  have hFew : ((nonzeroRowsOnColumns x B).card : ℝ) < (d : ℝ) / 3 := by
    exact lt_of_not_ge hNot
  let S := nonzeroRowsOnColumns x B
  let A : Finset W := Finset.univ \ S
  have hSle : S.card ≤ Fintype.card W := Finset.card_le_univ S
  have hAcard : A.card = Fintype.card W - S.card := by
    simpa [A] using Finset.card_sdiff_of_subset (Finset.subset_univ S)
  have hCastComplement : (Fintype.card W : ℝ) - A.card = S.card := by
    rw [hAcard, Nat.cast_sub hSle]
    ring
  have hSizeA : (Fintype.card W : ℝ) - A.card < (d : ℝ) / 3 := by
    rw [hCastComplement]
    exact hFew
  have hRectangle : ∀ i ∈ A, ∀ j ∈ B, x i j = 0 := by
    intro i hi j hj
    by_contra hNonzero
    have hiS : i ∈ S := by
      simpa [S, nonzeroRowsOnColumns] using
        (show ∃ k ∈ B, x i k ≠ 0 from ⟨j, hj, hNonzero⟩)
    exact (Finset.mem_sdiff.mp hi).2 hiS
  have hZero := eq_zero_of_zero_rectangle_one_third_either h h' d
    hPositive hLength hDistance hDistance'
    A B hSizeA hSizeB x hx hMinimal (Or.inr hRectangle)
  exact hxNonzero hZero

omit [Fintype R] [Fintype R'] in
/-- The transposed local form: every sufficiently large selection of rows
meets at least `d/3` columns. -/
theorem card_nonzeroColumnsOnRows_ge_one_third_distance
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (B : Finset W) (hSizeB : Fintype.card W - d < B.card) :
    (d : ℝ) / 3 ≤ (nonzeroColumnsOnRows x B).card := by
  have hxT : ProductKernel h' h x.transpose :=
    (productKernel_transpose_iff h h' x).mp hx
  have hxTNonzero : x.transpose ≠ 0 := by
    intro hZero
    apply hxNonzero
    have hOriginal := congrArg Matrix.transpose hZero
    simpa using hOriginal
  have hMinimalT : IsDeltaMinimal h' h ((d : ℝ) / 3) x.transpose :=
    (isDeltaMinimal_transpose_iff h' h _ x).mpr hMinimal
  have hRows := card_nonzeroRowsOnColumns_ge_one_third_distance
    h' h d hPositive hLength hDistance' hDistance
    x.transpose hxT hxTNonzero hMinimalT B hSizeB
  have hTransposeRows :
      nonzeroRowsOnColumns x.transpose B = nonzeroColumnsOnRows x B := by
    classical
    unfold nonzeroRowsOnColumns nonzeroColumnsOnRows
    apply Finset.filter_congr
    intro i _
    simp only [Matrix.transpose_apply]
  rw [hTransposeRows] at hRows
  exact hRows

omit [Fintype R] [Fintype R'] in
/-- At most `w-d` columns can have syndromes in the span of a generator
family whose restricted total weight is below `d/6`. Thus at least `d`
columns require a generator outside that light family. -/
theorem card_columnsWithSyndromeInSpan_le_complement_distance
    (h : Matrix R W F) (h' : Matrix R' W F) (d m : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (A : Finset W) (hLargeA : Fintype.card W - m ≤ A.card)
    (C : Finset (Word F W))
    (hWeight : (generatorRestrictedWeight A C : ℝ) < (d : ℝ) / 6) :
    (columnsWithSyndromeInSpan h' x C).card ≤ Fintype.card W - d := by
  classical
  let B := columnsWithSyndromeInSpan h' x C
  by_contra hNot
  have hLargeB : Fintype.card W - d < B.card := by
    change Fintype.card W - d < (columnsWithSyndromeInSpan h' x C).card
    omega
  have hRowsBound := card_nonzeroRowsOnColumns_ge_one_third_distance
    h h' d hPositive hLength hDistance hDistance'
      x hx hxNonzero hMinimal B hLargeB
  have hRowsSubset : nonzeroRowsOnColumns x B ⊆ generatorSupport C := by
    intro i hi
    obtain ⟨j, hjB, hxij⟩ : ∃ j ∈ B, x i j ≠ 0 := by
      simpa [nonzeroRowsOnColumns] using hi
    by_contra hiC
    have hjSpan : h'.mulVec (column x j) ∈ syndromeSpan h' C := by
      simpa [B, columnsWithSyndromeInSpan] using hjB
    have hZero := column_vanish_outside_generatorSupport_of_small_weight
      h h' d m hLength hSmallM hDistance' x hMinimal
      A hLargeA C hWeight j hjSpan i hiC
    exact hxij hZero
  have hRowsCard := Finset.card_le_card hRowsSubset
  have hSupportSmall := generatorSupport_card_lt_one_third_of_small_restricted_weight
    d m hLength hSmallM A hLargeA C hWeight
  have hRowsCardReal : ((nonzeroRowsOnColumns x B).card : ℝ) ≤
      (generatorSupport C).card := by exact_mod_cast hRowsCard
  linarith

omit [Fintype R] [Fintype R'] in
/-- Consequently at least `d` columns have syndromes outside the light
generator span. -/
theorem card_columnsOutsideSyndromeSpan_ge_distance
    (h : Matrix R W F) (h' : Matrix R' W F) (d m : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (A : Finset W) (hLargeA : Fintype.card W - m ≤ A.card)
    (C : Finset (Word F W))
    (hWeight : (generatorRestrictedWeight A C : ℝ) < (d : ℝ) / 6) :
    d ≤ (columnsOutsideSyndromeSpan h' x C).card := by
  classical
  have hInside := card_columnsWithSyndromeInSpan_le_complement_distance
    h h' d m hPositive hLength hSmallM hDistance hDistance'
      x hx hxNonzero hMinimal A hLargeA C hWeight
  have hOutsideCard : (columnsOutsideSyndromeSpan h' x C).card =
      Fintype.card W - (columnsWithSyndromeInSpan h' x C).card := by
    simp [columnsOutsideSyndromeSpan,
      Finset.card_sdiff_of_subset (Finset.subset_univ
        (columnsWithSyndromeInSpan h' x C))]
  omega

omit [Fintype R] in
/-- A rank-sized generating family has at least `d` matrix columns whose
syndromes escape the span of its light members. -/
theorem card_columnsOutside_lightGenerators_ge_distance
    (h : Matrix R W F) (h' : Matrix R' W F) (d m : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (A : Finset W) (hLargeA : Fintype.card W - m ≤ A.card)
    (C : Finset (Word F W)) (hCard : C.card = (h' * x).rank) :
    d ≤ (columnsOutsideSyndromeSpan h' x (lightGenerators A C d)).card := by
  have hPositiveReal : (0 : ℝ) < d := by exact_mod_cast hPositive
  have hDelta : (d : ℝ) / 3 < d := by linarith
  have hRankPositive := left_product_rank_pos_of_nonzero_minimal
    h h' d hDistance' ((d : ℝ) / 3) hDelta x hxNonzero hMinimal
  have hCPositive : 0 < C.card := by omega
  have hLightWeight := lightGenerators_restrictedWeight_lt_one_sixth
    A C d hCPositive hPositive
  exact card_columnsOutsideSyndromeSpan_ge_distance
    h h' d m hPositive hLength hSmallM hDistance hDistance'
      x hx hxNonzero hMinimal A hLargeA (lightGenerators A C d) hLightWeight

omit [Fintype R] [Fintype R'] in
/-- The common support of syndrome-spanning lifts has size at least `d/3`.
The rank proof applies this to the support union of its minimum-weight
representative basis, once those representatives are constructed. -/
theorem support_set_card_ge_one_third_of_syndrome_lifts
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (S : Finset W)
    (hLifts : ∀ j : W, ∃ y : Word F W,
      (∀ i ∉ S, y i = 0) ∧ h'.mulVec y = h'.mulVec (column x j)) :
    (d : ℝ) / 3 ≤ S.card := by
  classical
  by_contra hNot
  have hSmall : (S.card : ℝ) < (d : ℝ) / 3 := lt_of_not_ge hNot
  have hAllColumnsSupported : ∀ j : W, ∀ i ∉ S, x i j = 0 := by
    intro j i hiS
    obtain ⟨y, hSupported, hSyndrome⟩ := hLifts j
    have hEqual := column_eq_small_support_syndrome_lift
      h h' d hDistance' x hMinimal S hSmall j y hSupported hSyndrome
    have hentry := congrFun hEqual i
    exact hentry.trans (hSupported i hiS)
  have hRowsSubset : nonzeroRows x ⊆ S := by
    intro i hi
    by_contra hiS
    have hRowNonzero := (Finset.mem_filter.mp hi).2
    apply hRowNonzero
    funext j
    exact hAllColumnsSupported j i hiS
  have hRowsCard := card_nonzeroRows_ge_distance h h' d
    hPositive hLength hDistance hDistance' x hx hxNonzero hMinimal
  have hSupportCard := Finset.card_le_card hRowsSubset
  have hRowsReal : (d : ℝ) ≤ (nonzeroRows x).card := by
    exact_mod_cast hRowsCard
  have hSupportReal : ((nonzeroRows x).card : ℝ) ≤ S.card := by
    exact_mod_cast hSupportCard
  linarith

omit [Fintype R] [Fintype R'] in
/-- A finite family whose syndromes span all columns of `h' * x` must have
support union of size at least `d/3`. This discharges the lift hypothesis of
the preceding lemma using the actual linear span of generators. -/
theorem generatorSupport_card_ge_one_third_of_syndrome_spanning
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (C : Finset (Word F W))
    (hSpanning : ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) :
    (d : ℝ) / 3 ≤ (generatorSupport C).card := by
  have hLifts : ∀ j : W, ∃ y : Word F W,
      (∀ i ∉ generatorSupport C, y i = 0) ∧
      h'.mulVec y = h'.mulVec (column x j) := by
    intro j
    exact exists_supported_syndrome_lift_of_mem_span
      h' C (h'.mulVec (column x j)) (hSpanning j)
  exact support_set_card_ge_one_third_of_syndrome_lifts
    h h' d hPositive hLength hDistance hDistance'
    x hx hxNonzero hMinimal (generatorSupport C) hLifts

omit [Fintype F] [Fintype R] [Fintype R'] in
/-- A syndrome matrix has a finite family of word representatives, with
exactly its matrix rank many members, whose syndromes span all its columns.
This is the algebraic generator choice before the source minimizes their
restricted weights. -/
theorem exists_syndrome_spanning_generators_card_rank
    (h' : Matrix R' W F) (x : Matrix W W F) :
    ∃ C : Finset (Word F W),
      C.card = (h' * x).rank ∧
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) := by
  classical
  let M : Matrix R' W F := h' * x
  let V : Submodule F (R' → F) := LinearMap.range M.mulVecLin
  let b : Module.Basis (Fin (Module.finrank F V)) F V := Module.finBasis F V
  let preimage (i : Fin (Module.finrank F V)) : Word F W :=
    Classical.choose (b i).2
  have hPreimage (i : Fin (Module.finrank F V)) :
      M.mulVec (preimage i) = (b i).1 := by
    exact Classical.choose_spec (b i).2
  let representative (i : Fin (Module.finrank F V)) : Word F W :=
    x.mulVec (preimage i)
  have hRepresentative (i : Fin (Module.finrank F V)) :
      h'.mulVec (representative i) = (b i).1 := by
    simpa [M, representative, Matrix.mulVec_mulVec] using hPreimage i
  have hRepresentativeInjective : Function.Injective representative := by
    intro i j hij
    apply b.injective
    apply Subtype.ext
    calc
      (b i).1 = h'.mulVec (representative i) := (hRepresentative i).symm
      _ = h'.mulVec (representative j) := by rw [hij]
      _ = (b j).1 := hRepresentative j
  let C : Finset (Word F W) := Finset.univ.image representative
  have hCard : C.card = M.rank := by
    simp [C, Finset.card_image_of_injective _ hRepresentativeInjective,
      M, Matrix.rank, V]
  have hBasisInSpan (i : Fin (Module.finrank F V)) :
      ((b i).1 : R' → F) ∈ syndromeSpan h' C := by
    apply Submodule.subset_span
    refine ⟨representative i, ?_, hRepresentative i⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hBasisSpan : Submodule.span F (Set.range b) ≤
      (syndromeSpan h' C).comap V.subtype := by
    apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨i, rfl⟩ := hv
    exact hBasisInSpan i
  refine ⟨C, ?_, ?_⟩
  · simpa [M] using hCard
  · intro j
    have hColumnRange : h'.mulVec (column x j) ∈ V := by
      change h'.mulVec (column x j) ∈ LinearMap.range M.mulVecLin
      refine ⟨Pi.single j (1 : F), ?_⟩
      change M.mulVec (Pi.single j (1 : F)) = h'.mulVec (column x j)
      rw [Matrix.mulVec_single_one]
      ext i
      simp [M, Matrix.mul_apply, Matrix.mulVec, dotProduct, column]
    let v : V := ⟨h'.mulVec (column x j), hColumnRange⟩
    exact hBasisSpan (b.mem_span v)

omit [Fintype R] [Fintype R'] in
/-- Among all rank-sized families whose syndromes span the syndrome columns,
one has minimum total weight on a selected coordinate set. Finite-field
finiteness makes the paper's minimum-weight choice an actual attained minimum. -/
theorem exists_min_weight_syndrome_generators
    (h' : Matrix R' W F) (x : Matrix W W F) (A : Finset W) :
    ∃ C : Finset (Word F W),
      C.card = (h' * x).rank ∧
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) ∧
      (∀ D : Finset (Word F W),
        D.card = (h' * x).rank →
        (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' D) →
        generatorRestrictedWeight A C ≤ generatorRestrictedWeight A D) := by
  classical
  let candidates : Finset (Finset (Word F W)) :=
    Finset.univ.filter (fun C =>
      C.card = (h' * x).rank ∧
      ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C)
  have hNonempty : candidates.Nonempty := by
    obtain ⟨C, hCard, hSpanning⟩ :=
      exists_syndrome_spanning_generators_card_rank h' x
    exact ⟨C, Finset.mem_filter.mpr
      ⟨Finset.mem_univ C, ⟨hCard, hSpanning⟩⟩⟩
  obtain ⟨C, hC, hMinimal⟩ :=
    Finset.exists_min_image candidates (generatorRestrictedWeight A) hNonempty
  have hCProperties := (Finset.mem_filter.mp hC).2
  refine ⟨C, hCProperties.1, hCProperties.2, ?_⟩
  intro D hCard hSpanning
  exact hMinimal D (Finset.mem_filter.mpr
    ⟨Finset.mem_univ D, ⟨hCard, hSpanning⟩⟩)

omit [Fintype F] [Fintype R] [Fintype R'] in
/-- Minimum total restricted weight turns a valid basis exchange into a
pointwise lower bound on the replacement column's restricted weight. -/
theorem generator_weight_le_replacement_of_minimal
    (h' : Matrix R' W F) (x : Matrix W W F) (A : Finset W)
    (C : Finset (Word F W))
    (hCard : C.card = (h' * x).rank)
    (hSpanning : ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C)
    (hMin : ∀ D : Finset (Word F W),
      D.card = (h' * x).rank →
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' D) →
      generatorRestrictedWeight A C ≤ generatorRestrictedWeight A D)
    (b : Module.Basis C F (syndromeSpan h' C))
    (hb : ∀ a : C, (b a).1 = h'.mulVec a.1)
    (c : C) (j : W)
    (hCoordinate : (b.repr ⟨h'.mulVec (column x j), hSpanning j⟩) c ≠ 0) :
    restrictedHammingWeight A c.1 ≤ restrictedHammingWeight A (column x j) := by
  classical
  let y := column x j
  let D := insert y (C.erase c.1)
  have hCardExchange : D.card = C.card :=
    card_syndromeGenerators_exchange h' C b hb c y (hSpanning j) hCoordinate
  have hCardD : D.card = (h' * x).rank := by
    exact hCardExchange.trans hCard
  have hSpanLe : syndromeSpan h' C ≤ syndromeSpan h' D :=
    syndromeSpan_le_of_exchange h' C b hb c y (hSpanning j) hCoordinate
  have hSpanningD (k : W) : h'.mulVec (column x k) ∈ syndromeSpan h' D :=
    hSpanLe (hSpanning k)
  have hWeightMin := hMin D hCardD hSpanningD
  have hyNotErase : y ∉ C.erase c.1 := by
    intro hyErase
    have hInsert := Finset.card_insert_of_mem hyErase
    have hErase := Finset.card_erase_add_one c.2
    change (insert y (C.erase c.1)).card = (C.erase c.1).card at hInsert
    change (insert y (C.erase c.1)).card = C.card at hCardExchange
    omega
  have hWeightD : generatorRestrictedWeight A D =
      restrictedHammingWeight A y + generatorRestrictedWeight A (C.erase c.1) := by
    simp [D, generatorRestrictedWeight, Finset.sum_insert hyNotErase]
  have hWeightC : generatorRestrictedWeight A (C.erase c.1) +
      restrictedHammingWeight A c.1 = generatorRestrictedWeight A C := by
    simpa [generatorRestrictedWeight] using
      Finset.sum_erase_add C (restrictedHammingWeight A) c.2
  change restrictedHammingWeight A c.1 ≤ restrictedHammingWeight A y
  omega

omit [Fintype F] [Fintype R] in
/-- Every column whose syndrome escapes the light-generator span has
restricted weight at least the light/heavy threshold. -/
theorem escaping_column_restrictedWeight_ge_threshold
    (h' : Matrix R' W F) (x : Matrix W W F) (A : Finset W) (d : Nat)
    (C : Finset (Word F W))
    (hCard : C.card = (h' * x).rank)
    (hSpanning : ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C)
    (hMin : ∀ D : Finset (Word F W),
      D.card = (h' * x).rank →
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' D) →
      generatorRestrictedWeight A C ≤ generatorRestrictedWeight A D)
    (j : W) (hj : j ∈ columnsOutsideSyndromeSpan h' x (lightGenerators A C d)) :
    d ≤ 6 * C.card * restrictedHammingWeight A (column x j) := by
  classical
  obtain ⟨b, hb⟩ := exists_syndromeBasis_of_rank_sized h' x C hCard hSpanning
  have hjOutside : h'.mulVec (column x j) ∉ syndromeSpan h' (lightGenerators A C d) := by
    simpa [columnsOutsideSyndromeSpan, columnsWithSyndromeInSpan] using hj
  obtain ⟨c, hcNotLight, hcCoordinate⟩ := exists_generator_coordinate_outside_span
    h' C (lightGenerators A C d) b hb
    ⟨h'.mulVec (column x j), hSpanning j⟩ hjOutside
  have hcWeight := generator_weight_le_replacement_of_minimal
    h' x A C hCard hSpanning hMin b hb c j hcCoordinate
  have hcHeavy : d ≤ 6 * C.card * restrictedHammingWeight A c.1 := by
    by_contra hlt
    apply hcNotLight
    change c.1 ∈ C.filter (fun y => 6 * C.card * restrictedHammingWeight A y < d)
    exact Finset.mem_filter.mpr ⟨c.2, by omega⟩
  exact hcHeavy.trans (Nat.mul_le_mul_left (6 * C.card) hcWeight)

omit [Fintype F] [Fintype R] in
/-- Summing the weight threshold over the escaping columns contained in a
rectangle gives the counting inequality for the PK22 rank bound. -/
theorem rectangle_weight_ge_escaping_columns
    [DecidableEq W]
    (h' : Matrix R' W F) (x : Matrix W W F) (A B : Finset W) (d : Nat)
    (C : Finset (Word F W))
    (hCard : C.card = (h' * x).rank)
    (hSpanning : ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C)
    (hMin : ∀ D : Finset (Word F W),
      D.card = (h' * x).rank →
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' D) →
      generatorRestrictedWeight A C ≤ generatorRestrictedWeight A D) :
    d * ((columnsOutsideSyndromeSpan h' x (lightGenerators A C d)) ∩ B).card ≤
      6 * C.card * restrictedWeight x A B := by
  classical
  let E := columnsOutsideSyndromeSpan h' x (lightGenerators A C d)
  let S := E ∩ B
  have hEach (j : W) (hj : j ∈ S) :
      d ≤ 6 * C.card * restrictedHammingWeight A (column x j) :=
    escaping_column_restrictedWeight_ge_threshold h' x A d C
      hCard hSpanning hMin j (Finset.mem_inter.mp hj).1
  have hSumEach : d * S.card ≤
      (6 * C.card) * ∑ j ∈ S, restrictedHammingWeight A (column x j) := by
    calc
      d * S.card = ∑ _j ∈ S, d := by simp [mul_comm]
      _ ≤ ∑ j ∈ S, (6 * C.card) * restrictedHammingWeight A (column x j) :=
        Finset.sum_le_sum hEach
      _ = (6 * C.card) * ∑ j ∈ S, restrictedHammingWeight A (column x j) := by
        rw [Finset.mul_sum]
  have hSumSubset :
      (∑ j ∈ S, restrictedHammingWeight A (column x j)) ≤
      ∑ j ∈ B, restrictedHammingWeight A (column x j) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    intros
    omega
  change d * S.card ≤ 6 * C.card * restrictedWeight x A B
  rw [restrictedWeight_eq_sum_column_restrictedHammingWeight]
  exact hSumEach.trans (Nat.mul_le_mul_left _ hSumSubset)

omit [Fintype F] [DecidableEq F] [Fintype R] [Fintype R'] in
/-- A coordinate set missing at most `m` positions retains at least `d-m`
of any `d` marked columns. -/
theorem card_inter_ge_distance_sub_missing
    [DecidableEq W] (E B : Finset W) (d m : Nat)
    (hE : d ≤ E.card) (hB : Fintype.card W - m ≤ B.card) :
    d - m ≤ (E ∩ B).card := by
  have hMissingSubset : E \ B ⊆ Finset.univ \ B := by
    intro j hj
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, (Finset.mem_sdiff.mp hj).2⟩
  have hMissingCard := Finset.card_le_card hMissingSubset
  have hUnivMissing : (Finset.univ \ B).card = Fintype.card W - B.card := by
    simpa using Finset.card_sdiff_of_subset (Finset.subset_univ B)
  rw [hUnivMissing] at hMissingCard
  have hBMax : B.card ≤ Fintype.card W := Finset.card_le_univ B
  have hPartition := Finset.card_inter_add_card_sdiff E B
  omega

omit [Fintype R] in
/-- The integer counting form of the source's local rank lemma. This has no
division and remains valid even when the rectangle weight is zero (which the
inequality then excludes for positive distance). -/
theorem local_syndrome_rank_weight_inequality
    (h : Matrix R W F) (h' : Matrix R' W F) (d m : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (A B : Finset W)
    (hLargeA : Fintype.card W - m ≤ A.card)
    (hLargeB : Fintype.card W - m ≤ B.card) :
    d * (d - m) ≤ 6 * (h' * x).rank * restrictedWeight x A B := by
  classical
  obtain ⟨C, hCard, hSpanning, hMin⟩ :=
    exists_min_weight_syndrome_generators h' x A
  let E := columnsOutsideSyndromeSpan h' x (lightGenerators A C d)
  have hOutside : d ≤ E.card := card_columnsOutside_lightGenerators_ge_distance
    h h' d m hPositive hLength hSmallM hDistance hDistance'
    x hx hxNonzero hMinimal A hLargeA C hCard
  have hIntersection : d - m ≤ (E ∩ B).card :=
    card_inter_ge_distance_sub_missing E B d m hOutside hLargeB
  have hRectangle := rectangle_weight_ge_escaping_columns
    h' x A B d C hCard hSpanning hMin
  have hLower := Nat.mul_le_mul_left d hIntersection
  change d * (d - m) ≤ d * (E ∩ B).card at hLower
  change d * (E ∩ B).card ≤ 6 * C.card * restrictedWeight x A B at hRectangle
  rw [hCard] at hRectangle
  exact hLower.trans hRectangle

omit [Fintype R] in
/-- The `5/36` integer form of the PK22 local rank lemma. -/
theorem local_syndrome_rank_weight_inequality_five_thirtysixths
    (h : Matrix R W F) (h' : Matrix R' W F) (d m : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (A B : Finset W)
    (hLargeA : Fintype.card W - m ≤ A.card)
    (hLargeB : Fintype.card W - m ≤ B.card) :
    5 * d * d ≤ 36 * (h' * x).rank * restrictedWeight x A B := by
  have hBase := local_syndrome_rank_weight_inequality
    h h' d m hPositive hLength hSmallM hDistance hDistance'
      x hx hxNonzero hMinimal A B hLargeA hLargeB
  have hmLe : m ≤ d := by omega
  have hSub : d - m + m = d := Nat.sub_add_cancel hmLe
  have hDistanceTimes := Nat.mul_le_mul_left d hSmallM
  have hBaseTimes := Nat.mul_le_mul_left 6 hBase
  nlinarith

omit [Fintype R] in
/-- The source's local rank estimate in its real-valued `5d²/(36s)` form. -/
theorem local_syndrome_rank_ge_five_thirtysixths
    (h : Matrix R W F) (h' : Matrix R' W F) (d m : Nat) (s : ℝ)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
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
    (hSmallWeight : (restrictedWeight x A B : ℝ) < s)
    (hs : 0 < s) :
    (5 : ℝ) / 36 * (d : ℝ) ^ 2 / s ≤ ((h' * x).rank : ℝ) := by
  have hNat := local_syndrome_rank_weight_inequality_five_thirtysixths
    h h' d m hPositive hLength hSmallM hDistance hDistance'
      x hx hxNonzero hMinimal A B hLargeA hLargeB
  have hReal : (5 : ℝ) * d * d ≤
      36 * ((h' * x).rank : ℝ) * restrictedWeight x A B := by
    exact_mod_cast hNat
  have hRankNonneg : (0 : ℝ) ≤ ((h' * x).rank : ℝ) := Nat.cast_nonneg _
  have hProduct : ((h' * x).rank : ℝ) * restrictedWeight x A B ≤
      ((h' * x).rank : ℝ) * s :=
    mul_le_mul_of_nonneg_left hSmallWeight.le hRankNonneg
  rw [div_le_iff₀ hs]
  nlinarith [hProduct]

omit [Fintype R] [Fintype R'] in
/-- For a nonzero `d/3`-minimal product codeword, a rank-sized finite
syndrome-generating family can be chosen and its support union has size at
least `d/3`. The quantitative rank lemma next minimizes this family's
restricted weight and counts its heavy representatives. -/
theorem exists_rank_sized_syndrome_generators_with_large_support
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x) :
    ∃ C : Finset (Word F W),
      C.card = (h' * x).rank ∧
      (d : ℝ) / 3 ≤ (generatorSupport C).card ∧
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) := by
  obtain ⟨C, hCard, hSpanning⟩ :=
    exists_syndrome_spanning_generators_card_rank h' x
  refine ⟨C, hCard, ?_, hSpanning⟩
  exact generatorSupport_card_ge_one_third_of_syndrome_spanning
    h h' d hPositive hLength hDistance hDistance'
    x hx hxNonzero hMinimal C hSpanning

omit [Fintype R] [Fintype R'] in
/-- The source's minimum-weight syndrome representatives exist, have exactly
the syndrome rank many members, and their support union already satisfies the
first `d/3` lower bound used in the rank argument. -/
theorem exists_min_weight_generators_with_large_support
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (A : Finset W) :
    ∃ C : Finset (Word F W),
      C.card = (h' * x).rank ∧
      (d : ℝ) / 3 ≤ (generatorSupport C).card ∧
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) ∧
      (∀ D : Finset (Word F W),
        D.card = (h' * x).rank →
        (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' D) →
        generatorRestrictedWeight A C ≤ generatorRestrictedWeight A D) := by
  obtain ⟨C, hCard, hSpanning, hMin⟩ :=
    exists_min_weight_syndrome_generators h' x A
  refine ⟨C, hCard, ?_, hSpanning, hMin⟩
  exact generatorSupport_card_ge_one_third_of_syndrome_spanning
    h h' d hPositive hLength hDistance hDistance'
    x hx hxNonzero hMinimal C hSpanning

omit [Fintype R] [Fintype R'] in
/-- The minimum-weight rank-sized syndrome generators have total weight on
`A` at least `d/6` when at most `m ≤ d/6` coordinates are omitted. -/
theorem exists_min_weight_generators_with_one_sixth_weight
    (h : Matrix R W F) (h' : Matrix R' W F) (d m : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (A : Finset W) (hLargeA : Fintype.card W - m ≤ A.card) :
    ∃ C : Finset (Word F W),
      C.card = (h' * x).rank ∧
      (d : ℝ) / 6 ≤ generatorRestrictedWeight A C ∧
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) ∧
      (∀ D : Finset (Word F W),
        D.card = (h' * x).rank →
        (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' D) →
        generatorRestrictedWeight A C ≤ generatorRestrictedWeight A D) := by
  obtain ⟨C, hCard, hSupport, hSpanning, hMin⟩ :=
    exists_min_weight_generators_with_large_support
      h h' d hPositive hLength hDistance hDistance'
      x hx hxNonzero hMinimal A
  refine ⟨C, hCard, ?_, hSpanning, hMin⟩
  exact generatorRestrictedWeight_ge_one_sixth_of_large_support
    d m hLength hSmallM A hLargeA C hSupport

omit [Fintype R] [Fintype R'] in
/-- Product expansion is symmetric under exchanging the two parity checks. -/
theorem productExpanding_swap
    (h : Matrix R W F) (h' : Matrix R' W F)
    (s m : Nat) (beta : ℝ) :
    ProductExpanding h h' s m beta ↔ ProductExpanding h' h s m beta := by
  constructor
  · intro hExpand x hx hx0 hMinimal A B hA hB
    have hxT : ProductKernel h h' x.transpose :=
      (productKernel_transpose_iff h h' x.transpose).2 (by simpa using hx)
    have hxT0 : x.transpose ≠ 0 := by
      intro hzero
      apply hx0
      have h := congrArg Matrix.transpose hzero
      simpa using h
    have hMinimalT : IsDeltaMinimal h h'
        (beta * Fintype.card W) x.transpose :=
      (isDeltaMinimal_transpose_iff h h' _ x).2 hMinimal
    have hBound := hExpand x.transpose hxT hxT0 hMinimalT B A hB hA
    simpa only [restrictedWeight_transpose] using hBound
  · intro hExpand x hx hx0 hMinimal A B hA hB
    have hxT : ProductKernel h' h x.transpose :=
      (productKernel_transpose_iff h' h x.transpose).2 (by simpa using hx)
    have hxT0 : x.transpose ≠ 0 := by
      intro hzero
      apply hx0
      have h := congrArg Matrix.transpose hzero
      simpa using h
    have hMinimalT : IsDeltaMinimal h' h
        (beta * Fintype.card W) x.transpose :=
      (isDeltaMinimal_transpose_iff h' h _ x).2 hMinimal
    have hBound := hExpand x.transpose hxT hxT0 hMinimalT B A hB hA
    simpa only [restrictedWeight_transpose] using hBound

end QEC.Coding.ProductExpansion
