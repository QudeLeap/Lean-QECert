import QEC.Distillation.Triorthogonal.Transversal
/-!
# The explicit even-`k` Bravyi--Haah triorthogonal family

This file realizes the literal block matrix in Bravyi--Haah 2012,
`magic.tex:839-925`.  The family is indexed by `q`, with `k = 2q`, and has
`k + 3` rows and `3k + 8` columns.  It consumes the generic row-family,
overlap, span, CSS, and transversal interfaces from the #753 foundation.
-/

noncomputable section

namespace QEC.Distillation.Triorthogonal.BH12EvenFamily

open Coding
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

abbrev OddRow (q : Nat) := Fin q × Fin 2
abbrev EvenRow := Fin 3
abbrev Column (q : Nat) := Sum (Fin 4) (Sum (Fin 4) (Fin q × Fin 6))

/-- The even logical-qubit parameter `k = 2q`. -/
def logicalCount (q : Nat) : Nat := 2 * q

@[simp] theorem card_oddRow (q : Nat) :
    Fintype.card (OddRow q) = logicalCount q := by
  simp [OddRow, logicalCount, Nat.mul_comm]

@[simp] theorem card_evenRow : Fintype.card EvenRow = 3 := by
  simp [EvenRow]

@[simp] theorem card_column (q : Nat) :
    Fintype.card (Column q) = 3 * logicalCount q + 8 := by
  simp [Column, logicalCount]
  omega

@[simp] theorem card_row (q : Nat) :
    Fintype.card (Sum (OddRow q) EvenRow) = logicalCount q + 3 := by
  simp [logicalCount, Nat.mul_comm]

/-- Every even natural `k`, including zero, is represented by this `q`-indexed family. -/
theorem exists_index_of_even {k : Nat} (hk : Even k) :
    ∃ q : Nat, k = logicalCount q := by
  rcases hk with ⟨q, rfl⟩
  exact ⟨q, by simp [logicalCount, two_mul]⟩

/-- Reindexed acceptance form: an even `k` gets exactly `k+3` rows and `3k+8` columns. -/
theorem exists_family_size_of_even {k : Nat} (hk : Even k) :
    ∃ q : Nat, k = logicalCount q ∧
      Fintype.card (Sum (OddRow q) EvenRow) = k + 3 ∧
      Fintype.card (Column q) = 3 * k + 8 := by
  obtain ⟨q, rfl⟩ := exists_index_of_even hk
  exact ⟨q, rfl, card_row q, card_column q⟩

def leftBlock (_ : Fin 2) (_ : Fin 4) : ZMod 2 := 1

def oddBlock : Fin 2 → Fin 6 → ZMod 2 :=
  !![1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

def evenFourBlock : Fin 3 → Fin 4 → ZMod 2 :=
  !![0, 1, 0, 1;
     0, 0, 1, 1;
     1, 1, 1, 1]

def evenSixBlock : Fin 3 → Fin 6 → ZMod 2 :=
  !![1, 0, 1, 1, 0, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 0, 0, 0]

def oddWord {q : Nat} (a : OddRow q) : Word (ZMod 2) (Column q)
  | .inl _ => 0
  | .inr (.inl c) => leftBlock a.2 c
  | .inr (.inr jc) => if jc.1 = a.1 then oddBlock a.2 jc.2 else 0

def evenWord {q : Nat} (r : EvenRow) : Word (ZMod 2) (Column q)
  | .inl c => evenFourBlock r c
  | .inr (.inl c) => evenFourBlock r c
  | .inr (.inr jc) => evenSixBlock r jc.2

def family (q : Nat) : BinaryRowFamily (OddRow q) EvenRow (Column q) where
  oddRow := oddWord
  evenRow := evenWord

private theorem oddBlock_self_sum (b : Fin 2) :
    (∑ c, (oddBlock b c * oddBlock b c).val) = 3 := by
  fin_cases b <;> native_decide

private theorem evenFour_self_sum (r : Fin 3) :
    (∑ c, (evenFourBlock r c * evenFourBlock r c).val) = ![2, 2, 4] r := by
  fin_cases r <;> native_decide

private theorem evenSix_self_sum (r : Fin 3) :
    (∑ c, (evenSixBlock r c * evenSixBlock r c).val) = ![4, 4, 0] r := by
  fin_cases r <;> native_decide

private theorem sum_block_ite_self {q : Nat} (i j : Fin q) (b : Fin 2) :
    (∑ c : Fin 6,
      ((if j = i then oddBlock b c else 0) *
        (if j = i then oddBlock b c else 0)).val) =
      if j = i then 3 else 0 := by
  by_cases h : j = i
  · simp [h, oddBlock_self_sum]
  · simp [h]

/-- The three even rows are independent, detected in the first `S₁` block. -/
theorem evenRows_linearIndependent (q : Nat) :
    LinearIndependent (ZMod 2) (@evenWord q) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  have h0 := congrFun hc (Sum.inl (0 : Fin 4))
  have h1 := congrFun hc (Sum.inl (1 : Fin 4))
  have h2 := congrFun hc (Sum.inl (2 : Fin 4))
  simp [evenWord, evenFourBlock, Fin.sum_univ_succ] at h0 h1 h2
  fin_cases a
  · simpa [h0] using h1
  · simpa [h0] using h2
  · exact h0

private theorem left_pair_sum (b d : Fin 2) :
    (∑ c, (leftBlock b c * leftBlock d c).val) = 4 := by
  fin_cases b <;> fin_cases d <;> native_decide

private theorem left_triple_sum (b d e : Fin 2) :
    (∑ c, (leftBlock b c * leftBlock d c * leftBlock e c).val) = 4 := by
  fin_cases b <;> fin_cases d <;> fin_cases e <;> native_decide

private theorem oddBlock_pair_sum (b d : Fin 2) :
    (∑ c, (oddBlock b c * oddBlock d c).val) = if b = d then 3 else 0 := by
  fin_cases b <;> fin_cases d <;> native_decide

private theorem oddBlock_triple_sum (b d e : Fin 2) :
    (∑ c, (oddBlock b c * oddBlock d c * oddBlock e c).val) =
      if b = d ∧ d = e then 3 else 0 := by
  fin_cases b <;> fin_cases d <;> fin_cases e <;> native_decide

private theorem left_even_pair_sum (b : Fin 2) (r : Fin 3) :
    (∑ c, (leftBlock b c * evenFourBlock r c).val) = ![2, 2, 4] r := by
  fin_cases b <;> fin_cases r <;> native_decide

private theorem odd_even_pair_sum (b : Fin 2) (r : Fin 3) :
    (∑ c, (oddBlock b c * evenSixBlock r c).val) = ![2, 2, 0] r := by
  fin_cases b <;> fin_cases r <;> native_decide

private theorem evenFour_pair_sum (r s : Fin 3) :
    (∑ c, (evenFourBlock r c * evenFourBlock s c).val) =
      !![2, 1, 2; 1, 2, 2; 2, 2, 4] r s := by
  fin_cases r <;> fin_cases s <;> native_decide

private theorem evenSix_pair_sum (r s : Fin 3) :
    (∑ c, (evenSixBlock r c * evenSixBlock s c).val) =
      !![4, 2, 0; 2, 4, 0; 0, 0, 0] r s := by
  fin_cases r <;> fin_cases s <;> native_decide

private theorem left_left_even_triple_sum (b d : Fin 2) (r : Fin 3) :
    (∑ c, (leftBlock b c * leftBlock d c * evenFourBlock r c).val) =
      ![2, 2, 4] r := by
  fin_cases b <;> fin_cases d <;> fin_cases r <;> native_decide

private theorem odd_odd_even_triple_sum (b d : Fin 2) (r : Fin 3) :
    (∑ c, (oddBlock b c * oddBlock d c * evenSixBlock r c).val) =
      if b = d then ![2, 2, 0] r else 0 := by
  fin_cases b <;> fin_cases d <;> fin_cases r <;> native_decide

private theorem left_even_even_triple_sum (b : Fin 2) (r s : Fin 3) :
    (∑ c, (leftBlock b c * evenFourBlock r c * evenFourBlock s c).val) =
      !![2, 1, 2; 1, 2, 2; 2, 2, 4] r s := by
  fin_cases b <;> fin_cases r <;> fin_cases s <;> native_decide

private theorem odd_even_even_triple_sum (b : Fin 2) (r s : Fin 3) :
    (∑ c, (oddBlock b c * evenSixBlock r c * evenSixBlock s c).val) =
      !![2, 1, 0; 1, 2, 0; 0, 0, 0] r s := by
  fin_cases b <;> fin_cases r <;> fin_cases s <;> native_decide

private theorem evenFour_triple_sum_of_distinct (r s t : Fin 3)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    (∑ c, (evenFourBlock r c * evenFourBlock s c * evenFourBlock t c).val) = 1 := by
  fin_cases r <;> fin_cases s <;> fin_cases t <;> simp_all <;> native_decide

private theorem evenSix_triple_sum_of_distinct (r s t : Fin 3)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    (∑ c, (evenSixBlock r c * evenSixBlock s c * evenSixBlock t c).val) = 0 := by
  fin_cases r <;> fin_cases s <;> fin_cases t <;> simp_all <;> native_decide

private theorem oddOdd_block_pair {q : Nat} (i j u : Fin q) (b d : Fin 2) :
    (∑ c : Fin 6,
      ((if u = i then oddBlock b c else 0) *
        (if u = j then oddBlock d c else 0)).val) =
      if u = i ∧ u = j then (if b = d then 3 else 0) else 0 := by
  by_cases hui : u = i
  · subst i
    by_cases huj : u = j
    · subst j
      simp [oddBlock_pair_sum]
    · simp [huj]
  · by_cases huj : u = j
    · subst j
      simp [hui]
    · simp [hui, huj]

private theorem oddEven_block_pair {q : Nat} (i u : Fin q) (b : Fin 2) (r : Fin 3) :
    (∑ c : Fin 6,
      ((if u = i then oddBlock b c else 0) * evenSixBlock r c).val) =
      if u = i then ![2, 2, 0] r else 0 := by
  by_cases hui : u = i <;> simp [hui, odd_even_pair_sum]

private theorem oddOddOdd_block_triple {q : Nat}
    (i j l u : Fin q) (b d e : Fin 2) :
    (∑ c : Fin 6,
      ((if u = i then oddBlock b c else 0) *
        (if u = j then oddBlock d c else 0) *
        (if u = l then oddBlock e c else 0)).val) =
      if u = i ∧ u = j ∧ u = l then
        (if b = d ∧ d = e then 3 else 0) else 0 := by
  by_cases hui : u = i
  · subst i
    by_cases huj : u = j
    · subst j
      by_cases hul : u = l
      · subst l
        simp [oddBlock_triple_sum]
      · simp [hul]
    · simp [huj]
  · simp [hui]

private theorem oddOddEven_block_triple {q : Nat}
    (i j u : Fin q) (b d : Fin 2) (r : Fin 3) :
    (∑ c : Fin 6,
      ((if u = i then oddBlock b c else 0) *
        (if u = j then oddBlock d c else 0) * evenSixBlock r c).val) =
      if u = i ∧ u = j then (if b = d then ![2, 2, 0] r else 0) else 0 := by
  by_cases hui : u = i
  · subst i
    by_cases huj : u = j
    · subst j
      simp [odd_odd_even_triple_sum]
    · simp [huj]
  · simp [hui]

private theorem oddEvenEven_block_triple {q : Nat}
    (i u : Fin q) (b : Fin 2) (r s : Fin 3) :
    (∑ c : Fin 6,
      ((if u = i then oddBlock b c else 0) * evenSixBlock r c *
        evenSixBlock s c).val) =
      if u = i then !![2, 1, 0; 1, 2, 0; 0, 0, 0] r s else 0 := by
  by_cases hui : u = i <;> simp [hui, odd_even_even_triple_sum]

/-- Every top row has the source weight seven. -/
theorem oddWeight {q : Nat} (a : OddRow q) :
    HammingWeight (oddWord a) = 7 := by
  rw [← BinaryRowFamily.pairOverlap_self_eq_hammingWeight]
  simp only [BinaryRowFamily.pairOverlap, oddWord, leftBlock, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp_rw [sum_block_ite_self]
  simp
  decide

/-- The three bottom rows have weights `4+4q`, `4+4q`, and `8`. -/
theorem evenWeight {q : Nat} (r : EvenRow) :
    HammingWeight (evenWord (q := q) r) = ![4 + 4 * q, 4 + 4 * q, 8] r := by
  rw [← BinaryRowFamily.pairOverlap_self_eq_hammingWeight]
  simp only [BinaryRowFamily.pairOverlap, evenWord, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp_rw [evenFour_self_sum, evenSix_self_sum]
  fin_cases r <;> simp <;> omega

theorem evenWeight_in_logicalCount {q : Nat} (r : EvenRow) :
    HammingWeight (evenWord (q := q) r) =
      ![4 + 2 * logicalCount q, 4 + 2 * logicalCount q, 8] r := by
  rw [evenWeight]
  fin_cases r <;> simp [logicalCount] <;> omega

theorem oddOddPairOverlap {q : Nat} (a b : OddRow q) (hab : a ≠ b) :
    BinaryRowFamily.pairOverlap (oddWord a) (oddWord b) = 4 := by
  classical
  rcases a with ⟨i, u⟩
  rcases b with ⟨j, v⟩
  simp only [BinaryRowFamily.pairOverlap, oddWord, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp_rw [oddOdd_block_pair]
  rw [left_pair_sum]
  by_cases hij : i = j
  · have huv : u ≠ v := by
      intro huv
      exact hab (Prod.ext hij huv)
    simp [hij, huv]
  · simp [hij]

theorem oddEvenPairOverlap {q : Nat} (a : OddRow q) (r : EvenRow) :
    BinaryRowFamily.pairOverlap (oddWord a) (evenWord r) = 4 := by
  classical
  rcases a with ⟨i, b⟩
  simp only [BinaryRowFamily.pairOverlap, oddWord, evenWord, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp_rw [oddEven_block_pair]
  rw [left_even_pair_sum]
  fin_cases r <;> simp

theorem evenEvenPairOverlap {q : Nat} (r s : EvenRow) (hrs : r ≠ s) :
    BinaryRowFamily.pairOverlap (evenWord (q := q) r) (evenWord s) =
      !![0, 2 + 2 * q, 4; 2 + 2 * q, 0, 4; 4, 4, 0] r s := by
  simp only [BinaryRowFamily.pairOverlap, evenWord, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp_rw [evenFour_pair_sum, evenSix_pair_sum]
  fin_cases r <;> fin_cases s <;> simp_all <;> omega

theorem oddOddOddTripleOverlap {q : Nat} (a b c : OddRow q)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    BinaryRowFamily.tripleOverlap (oddWord a) (oddWord b) (oddWord c) = 4 := by
  classical
  rcases a with ⟨i, u⟩
  rcases b with ⟨j, v⟩
  rcases c with ⟨l, w⟩
  simp only [BinaryRowFamily.tripleOverlap, oddWord, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp_rw [oddOddOdd_block_triple]
  rw [left_triple_sum]
  have hzero : ∀ x : Fin q,
      (if x = i ∧ x = j ∧ x = l then
        (if u = v ∧ v = w then 3 else 0) else 0) = 0 := by
    intro x
    by_cases hidx : x = i ∧ x = j ∧ x = l
    · rcases hidx with ⟨hxi, hxj, hxl⟩
      have hij : i = j := hxi.symm.trans hxj
      have hil : i = l := hxi.symm.trans hxl
      have huv : u ≠ v := by intro h; exact hab (Prod.ext hij h)
      have huw : u ≠ w := by intro h; exact hac (Prod.ext hil h)
      fin_cases u <;> fin_cases v <;> fin_cases w <;> simp_all
    · simp [hidx]
  simp_rw [hzero]
  simp

theorem oddOddEvenTripleOverlap {q : Nat} (a b : OddRow q) (r : EvenRow)
    (hab : a ≠ b) :
    BinaryRowFamily.tripleOverlap (oddWord a) (oddWord b) (evenWord r) =
      ![2, 2, 4] r := by
  classical
  rcases a with ⟨i, u⟩
  rcases b with ⟨j, v⟩
  simp only [BinaryRowFamily.tripleOverlap, oddWord, evenWord, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp_rw [oddOddEven_block_triple]
  rw [left_left_even_triple_sum]
  by_cases hij : i = j
  · have huv : u ≠ v := by intro h; exact hab (Prod.ext hij h)
    simp [hij, huv]
  · simp [hij]

theorem oddEvenEvenTripleOverlap {q : Nat} (a : OddRow q) (r s : EvenRow)
    (hrs : r ≠ s) :
    BinaryRowFamily.tripleOverlap (oddWord a) (evenWord r) (evenWord s) = 2 := by
  classical
  rcases a with ⟨i, b⟩
  simp only [BinaryRowFamily.tripleOverlap, oddWord, evenWord, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp_rw [oddEvenEven_block_triple]
  rw [left_even_even_triple_sum]
  fin_cases r <;> fin_cases s <;> simp_all

theorem evenEvenEvenTripleOverlap {q : Nat} (r s t : EvenRow)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    BinaryRowFamily.tripleOverlap (evenWord (q := q) r) (evenWord s) (evenWord t) = 2 := by
  simp only [BinaryRowFamily.tripleOverlap, evenWord, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  rw [evenFour_triple_sum_of_distinct r s t hrs hrt hst]
  simp_rw [evenSix_triple_sum_of_distinct r s t hrs hrt hst]
  simp

private theorem pairOverlap_comm {q : Nat} (x y : Word (ZMod 2) (Column q)) :
    BinaryRowFamily.pairOverlap x y = BinaryRowFamily.pairOverlap y x := by
  classical
  simp [BinaryRowFamily.pairOverlap, mul_comm]

private theorem tripleOverlap_swap12 {q : Nat}
    (x y z : Word (ZMod 2) (Column q)) :
    BinaryRowFamily.tripleOverlap x y z = BinaryRowFamily.tripleOverlap y x z := by
  classical
  simp [BinaryRowFamily.tripleOverlap, mul_comm]

private theorem tripleOverlap_swap23 {q : Nat}
    (x y z : Word (ZMod 2) (Column q)) :
    BinaryRowFamily.tripleOverlap x y z = BinaryRowFamily.tripleOverlap x z y := by
  classical
  simp [BinaryRowFamily.tripleOverlap, mul_comm, mul_left_comm]

private theorem even_two_or_four (r : Fin 3) : Even (![2, 2, 4] r) := by
  fin_cases r
  · exact ⟨1, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

/-- The literal BH12 matrix satisfies the actual generic triorthogonality predicate. -/
theorem isTriorthogonal (q : Nat) : (family q).IsTriorthogonal := by
  classical
  refine
    { odd_weight := ?_
      even_weight := ?_
      pair_even := ?_
      triple_even := ?_ }
  · intro a
    change Odd (HammingWeight (oddWord a))
    rw [oddWeight]
    exact ⟨3, rfl⟩
  · intro r
    change Even (HammingWeight (evenWord r))
    rw [evenWeight]
    fin_cases r
    · simpa using (show Even (4 + 4 * q) from ⟨2 + 2 * q, by omega⟩)
    · simpa using (show Even (4 + 4 * q) from ⟨2 + 2 * q, by omega⟩)
    · simpa using (show Even 8 from ⟨4, rfl⟩)
  · intro a b hab
    rcases a with a | r <;> rcases b with b | s
    all_goals simp only [family, BinaryRowFamily.row]
    · rw [oddOddPairOverlap a b (by simpa using hab)]
      exact ⟨2, rfl⟩
    · rw [oddEvenPairOverlap]
      exact ⟨2, rfl⟩
    · rw [pairOverlap_comm, oddEvenPairOverlap]
      exact ⟨2, rfl⟩
    · have hrs : r ≠ s := by simpa using hab
      rw [evenEvenPairOverlap r s hrs]
      fin_cases r <;> fin_cases s <;> simp_all
      all_goals first | exact ⟨1 + q, by omega⟩ | exact ⟨2, rfl⟩
  · intro a b c hab hac hbc
    rcases a with a | r <;> rcases b with b | s <;> rcases c with c | t
    all_goals simp only [family, BinaryRowFamily.row]
    · rw [oddOddOddTripleOverlap a b c (by simpa using hab)
        (by simpa using hac) (by simpa using hbc)]
      exact ⟨2, rfl⟩
    · rw [oddOddEvenTripleOverlap a b t (by simpa using hab)]
      exact even_two_or_four t
    · rw [tripleOverlap_swap23,
        oddOddEvenTripleOverlap a c s (by simpa using hac)]
      exact even_two_or_four s
    · rw [oddEvenEvenTripleOverlap a s t (by simpa using hbc)]
      exact ⟨1, rfl⟩
    · rw [tripleOverlap_swap12, tripleOverlap_swap23,
        oddOddEvenTripleOverlap b c r (by simpa using hbc)]
      exact even_two_or_four r
    · rw [tripleOverlap_swap12,
        oddEvenEvenTripleOverlap b r t (by simpa using hac)]
      exact ⟨1, rfl⟩
    · rw [tripleOverlap_swap12, tripleOverlap_swap23,
        tripleOverlap_swap12, tripleOverlap_swap23,
        oddEvenEvenTripleOverlap c r s (by simpa using hab)]
      exact ⟨1, rfl⟩
    · rw [evenEvenEvenTripleOverlap r s t (by simpa using hab)
        (by simpa using hac) (by simpa using hbc)]
      exact ⟨1, rfl⟩

/-- The full `k+3` row presentation is linearly independent. -/
theorem rows_linearIndependent (q : Nat) :
    LinearIndependent (ZMod 2) (family q).row := by
  have hOdd := (family q).oddRows_linearIndependent (isTriorthogonal q)
  have hDisjoint := (family q).evenCode_disjoint_oddCode (isTriorthogonal q)
  have hd : Disjoint
      (Submodule.span (ZMod 2) (Set.range (@oddWord q)))
      (Submodule.span (ZMod 2) (Set.range (@evenWord q))) := by
    simpa [BinaryRowFamily.oddCode, BinaryRowFamily.evenCode, family] using
      hDisjoint.symm
  have hrow : (family q).row = Sum.elim oddWord evenWord := by
    funext a
    rcases a with a | r <;> rfl
  rw [hrow]
  exact hOdd.sum_type (evenRows_linearIndependent q) hd

/-- `dim G₀ = 3`. -/
theorem dimension_evenCode (q : Nat) : Dimension (family q).evenCode = 3 := by
  change Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range (@evenWord q))) = 3
  simpa using finrank_span_eq_card (evenRows_linearIndependent q)

/-- `dim G₁ = k`. -/
theorem dimension_oddCode (q : Nat) :
    Dimension (family q).oddCode = logicalCount q := by
  simpa [logicalCount, Nat.mul_comm] using
    (family q).dimension_oddCode (isTriorthogonal q)

/-- `dim G = k+3`. -/
theorem dimension_rowCode (q : Nat) :
    Dimension (family q).rowCode = logicalCount q + 3 := by
  change Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range (family q).row)) = logicalCount q + 3
  rw [finrank_span_eq_card (rows_linearIndependent q)]
  simp [logicalCount, Nat.mul_comm]

/-- `dim G⊥ = 2k+5`. -/
theorem dimension_rowCode_dual (q : Nat) :
    Dimension (family q).rowCode.dual = 2 * logicalCount q + 5 := by
  rw [(family q).rowCode.dual_dimension_eq_length_sub_dimension,
    dimension_rowCode]
  change Fintype.card (Column q) - (logicalCount q + 3) = _
  rw [card_column]
  omega

/-- `dim G₀⊥ = 3k+5`. -/
theorem dimension_evenCode_dual (q : Nat) :
    Dimension (family q).evenCode.dual = 3 * logicalCount q + 5 := by
  rw [(family q).evenCode.dual_dimension_eq_length_sub_dimension,
    dimension_evenCode]
  change Fintype.card (Column q) - 3 = _
  rw [card_column]
  omega

/-- The #753 CSS logical exponent specializes to exactly the even parameter `k`. -/
theorem cssLogicalExponent (q : Nat) :
    Length (ZMod 2) (Column q) - Dimension (family q).evenCode -
        Dimension (family q).rowCode.dual = logicalCount q := by
  simpa [logicalCount, Nat.mul_comm] using
    (family q).cssLogicalExponent_eq_card_oddRows (isTriorthogonal q)

/-- The semantic CSS carrier has dimension `2^k`. -/
theorem cssCarrierFinrank (q : Nat) :
    Module.finrank Complex (family q).cssQuantumCode.carrier = 2 ^ logicalCount q := by
  simpa [logicalCount, Nat.mul_comm] using
    (family q).cssQuantumCode_finrank_carrier (isTriorthogonal q)

/-- The source weight-two `Z` representative on matching columns of the two `S₁` blocks. -/
def distanceWitness (q : Nat) : Word (ZMod 2) (Column q) :=
  Pi.single (Sum.inl (0 : Fin 4)) 1 +
    Pi.single (Sum.inr (Sum.inl (0 : Fin 4))) 1

private theorem wordPairing_single_one {q : Nat} (j : Column q)
    (x : Word (ZMod 2) (Column q)) :
    wordPairing (Pi.single j 1) x = x j := by
  classical
  rw [wordPairing_apply, single_one_dotProduct]

private theorem finFourSingle_self_sum :
    (∑ c : Fin 4,
      ((Pi.single (0 : Fin 4) (1 : ZMod 2) : Fin 4 → ZMod 2) c *
        (Pi.single (0 : Fin 4) (1 : ZMod 2) : Fin 4 → ZMod 2) c).val) = 1 := by
  native_decide

theorem distanceWitness_weight (q : Nat) : HammingWeight (distanceWitness q) = 2 := by
  classical
  rw [← BinaryRowFamily.pairOverlap_self_eq_hammingWeight]
  simp only [BinaryRowFamily.pairOverlap, distanceWitness, Fintype.sum_sum_type]
  simp
  have hfirst : (∑ c : Fin 4,
      ((Pi.single (Sum.inl (0 : Fin 4)) (1 : ZMod 2) : Column q → ZMod 2)
          (Sum.inl c) *
        (Pi.single (Sum.inl (0 : Fin 4)) (1 : ZMod 2) : Column q → ZMod 2)
          (Sum.inl c)).val) = 1 := by
    simpa only [Pi.single_apply, Sum.inl.injEq] using finFourSingle_self_sum
  have hsecond : (∑ c : Fin 4,
      ((Pi.single (Sum.inr (Sum.inl (0 : Fin 4))) (1 : ZMod 2) :
          Column q → ZMod 2)
          (Sum.inr (Sum.inl c)) *
        (Pi.single (Sum.inr (Sum.inl (0 : Fin 4))) (1 : ZMod 2) :
          Column q → ZMod 2)
          (Sum.inr (Sum.inl c))).val) = 1 := by
    simpa only [Pi.single_apply, Sum.inr.injEq, Sum.inl.injEq] using finFourSingle_self_sum
  rw [hfirst, hsecond]

theorem distanceWitness_pair_even (q : Nat) (r : EvenRow) :
    wordPairing (distanceWitness q) (evenWord r) = 0 := by
  classical
  rw [distanceWitness, wordPairing.map_add]
  change wordPairing (Pi.single (Sum.inl (0 : Fin 4)) 1) (evenWord r) +
      wordPairing (Pi.single (Sum.inr (Sum.inl (0 : Fin 4))) 1) (evenWord r) = 0
  rw [wordPairing_single_one, wordPairing_single_one]
  change evenFourBlock r 0 + evenFourBlock r 0 = 0
  exact ZModModule.add_self _

/-- Every column meets at least one bottom row, the source no-zero-column condition. -/
theorem exists_evenWord_eq_one {q : Nat} (j : Column q) :
    ∃ r : EvenRow, evenWord r j = 1 := by
  rcases j with c | c
  · fin_cases c
    · exact ⟨2, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
  · rcases c with c | c
    · fin_cases c
      · exact ⟨2, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
    · rcases c with ⟨i, c⟩
      fin_cases c
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩

private theorem eq_single_of_hammingWeight_eq_one {q : Nat}
    (x : Word (ZMod 2) (Column q)) (hx : HammingWeight x = 1) :
    ∃ j, x = Pi.single j 1 := by
  classical
  have hcard : (hammingSupport x).card = 1 := hx
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have hjmem : j ∈ hammingSupport x := by simp [hj]
  have hxj : x j = 1 := by
    have hxj0 : x j ≠ 0 := by simpa [hammingSupport] using hjmem
    apply ZMod.val_injective
    have hlt := ZMod.val_lt (x j)
    have hpos : 0 < (x j).val :=
      Nat.pos_of_ne_zero ((ZMod.val_eq_zero (x j)).not.mpr hxj0)
    change (x j).val = 1
    omega
  refine ⟨j, funext fun c => ?_⟩
  by_cases hc : c = j
  · subst c
    simp [hxj]
  · have hcnot : c ∉ hammingSupport x := by simp [hj, hc]
    have hxc : x c = 0 := by simpa [hammingSupport] using hcnot
    simp [Pi.single, hc, hxc]

/-- No word of weight one is orthogonal to every bottom row. -/
theorem hammingWeight_ne_one_of_mem_evenCode_dual {q : Nat}
    {x : Word (ZMod 2) (Column q)} (hx : x ∈ (family q).evenCode.dual.carrier) :
    HammingWeight x ≠ 1 := by
  classical
  intro hxWeight
  obtain ⟨j, rfl⟩ := eq_single_of_hammingWeight_eq_one x hxWeight
  obtain ⟨r, hr⟩ := exists_evenWord_eq_one j
  have hpair := (family q).evenCode.orthogonal_of_mem_dual hx
    ((family q).evenRow_mem_evenCode r)
  change wordPairing (Pi.single j 1) (evenWord r) = 0 at hpair
  rw [wordPairing_single_one, hr] at hpair
  exact one_ne_zero hpair

/-- The weight-two representative is orthogonal to the full bottom-row span. -/
theorem distanceWitness_mem_evenCode_dual (q : Nat) :
    distanceWitness q ∈ (family q).evenCode.dual.carrier := by
  rw [LinearCode.mem_dual]
  intro y hy
  change y ∈ Submodule.span (ZMod 2) (Set.range (@evenWord q)) at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨r, rfl⟩
      exact distanceWitness_pair_even q r
  | zero => exact (wordPairing (distanceWitness q)).map_zero
  | add y z _ _ hy hz =>
      rw [(wordPairing (distanceWitness q)).map_add, hy, hz, add_zero]
  | smul c y _ hy =>
      rw [(wordPairing (distanceWitness q)).map_smul, hy, smul_zero]

/-- Every top row pairs nontrivially with the weight-two representative. -/
theorem distanceWitness_pair_odd {q : Nat} (a : OddRow q) :
    wordPairing (distanceWitness q) (oddWord a) = 1 := by
  classical
  rw [distanceWitness, wordPairing.map_add]
  change wordPairing (Pi.single (Sum.inl (0 : Fin 4)) 1) (oddWord a) +
      wordPairing (Pi.single (Sum.inr (Sum.inl (0 : Fin 4))) 1) (oddWord a) = 1
  rw [wordPairing_single_one, wordPairing_single_one]
  rfl

/-- For positive `q`, the witness is not in `G⊥`. -/
theorem distanceWitness_not_mem_rowCode_dual {q : Nat} (hq : 0 < q) :
    distanceWitness q ∉ (family q).rowCode.dual.carrier := by
  intro hmem
  let a : OddRow q := (⟨0, hq⟩, 0)
  have hpair := (family q).rowCode.orthogonal_of_mem_dual hmem
    ((family q).row_mem_rowCode (Sum.inl a))
  change wordPairing (distanceWitness q) (oddWord a) = 0 at hpair
  rw [distanceWitness_pair_odd] at hpair
  exact one_ne_zero hpair

private theorem two_le_hammingWeight_of_relative_word {q : Nat}
    {x : Word (ZMod 2) (Column q)}
    (hxDual : x ∈ (family q).evenCode.dual.carrier)
    (hxRow : x ∉ (family q).rowCode.dual.carrier) :
    2 ≤ HammingWeight x := by
  have hx0 : HammingWeight x ≠ 0 := by
    intro hzero
    have hx : x = 0 := (HammingWeight_eq_zero_iff x).mp hzero
    exact hxRow (by simp [hx])
  have hx1 : HammingWeight x ≠ 1 :=
    hammingWeight_ne_one_of_mem_evenCode_dual hxDual
  omega

/-- For `q>0`, the pure-`Z` relative sector has exact minimum distance two. -/
theorem relativeMinimumDistance_two {q : Nat} (hq : 0 < q) :
    RelativeMinimumDistance (family q).evenCode.dual (family q).rowCode.dual 2 := by
  refine ⟨distanceWitness q, distanceWitness_mem_evenCode_dual q,
    distanceWitness_not_mem_rowCode_dual hq, distanceWitness_weight q, ?_⟩
  intro x hxDual hxRow
  exact two_le_hammingWeight_of_relative_word hxDual hxRow

/-- CSS terminology for the exact positive-family pure-`Z` distance statement. -/
theorem pureZLogicalMinimumDistance_two {q : Nat} (hq : 0 < q) :
    PureZLogicalMinimumDistance (family q).evenCode (family q).rowCode.dual 2 :=
  relativeMinimumDistance_two hq

/-- At `q=0`, there is no odd sector and the two relevant dual codes coincide. -/
theorem zero_evenCode_dual_eq_rowCode_dual :
    (family 0).evenCode.dual.carrier = (family 0).rowCode.dual.carrier := by
  have hOdd : (family 0).oddCode.carrier = ⊥ := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro x hx
      rcases hx with ⟨a, rfl⟩
      exact Fin.elim0 a.1
    · exact bot_le
  rw [(family 0).evenCode_dual_eq_oddCode_sup_rowCode_dual (isTriorthogonal 0)]
  simp [hOdd]

/-- Consequently the endpoint `q=0` relative sector is empty. -/
theorem zero_relativeSector_empty (x : Word (ZMod 2) (Column 0)) :
    x ∈ (family 0).evenCode.dual.carrier ↔
      x ∈ (family 0).rowCode.dual.carrier := by
  rw [zero_evenCode_dual_eq_rowCode_dual]

/-- No relative minimum-distance claim is fabricated at the empty endpoint. -/
theorem zero_not_relativeMinimumDistance (d : Nat) :
    ¬ RelativeMinimumDistance (family 0).evenCode.dual (family 0).rowCode.dual d := by
  rintro ⟨x, hxDual, hxRow, _⟩
  exact hxRow (zero_relativeSector_empty x |>.mp hxDual)

@[simp] theorem zero_cssLogicalExponent :
    Length (ZMod 2) (Column 0) - Dimension (family 0).evenCode -
        Dimension (family 0).rowCode.dual = 0 := by
  simpa only [logicalCount, Nat.mul_zero] using cssLogicalExponent 0

@[simp] theorem zero_cssCarrierFinrank :
    Module.finrank Complex (family 0).cssQuantumCode.carrier = 1 := by
  simpa only [logicalCount, Nat.mul_zero, pow_zero] using cssCarrierFinrank 0

/-- A bottom-row coefficient word and its concrete linear combination. -/
def evenCombination (q : Nat) (c : EvenRow → ZMod 2) : Word (ZMod 2) (Column q) :=
  Fintype.linearCombination (ZMod 2) (@evenWord q) c

/-- The eight coefficient words, in binary order with the third bit last. -/
def coefficientBits : Fin 8 → EvenRow → ZMod 2 :=
  !![0, 0, 0;
     1, 0, 0;
     0, 1, 0;
     1, 1, 0;
     0, 0, 1;
     1, 0, 1;
     0, 1, 1;
     1, 1, 1]

private theorem coefficientBits_bijective : Function.Bijective coefficientBits := by
  native_decide

/-- Concrete enumeration of all three-bit bottom-row coefficient words. -/
def coefficientEquiv : Fin 8 ≃ (EvenRow → ZMod 2) :=
  Equiv.ofBijective coefficientBits coefficientBits_bijective

private def combineFour (c : EvenRow → ZMod 2) (j : Fin 4) : ZMod 2 :=
  ∑ r, c r * evenFourBlock r j

private def combineSix (c : EvenRow → ZMod 2) (j : Fin 6) : ZMod 2 :=
  ∑ r, c r * evenSixBlock r j

private theorem combineFour_self_sum (i : Fin 8) :
    (∑ j, (combineFour (coefficientBits i) j *
      combineFour (coefficientBits i) j).val) =
      ![0, 2, 2, 2, 4, 2, 2, 2] i := by
  fin_cases i <;> native_decide

private theorem combineSix_self_sum (i : Fin 8) :
    (∑ j, (combineSix (coefficientBits i) j *
      combineSix (coefficientBits i) j).val) =
      ![0, 4, 4, 4, 0, 4, 4, 4] i := by
  fin_cases i <;> native_decide

@[simp] private theorem evenCombination_first_apply (q : Nat)
    (c : EvenRow → ZMod 2) (j : Fin 4) :
    evenCombination q c (Sum.inl j) = combineFour c j := by
  simp [evenCombination, combineFour, evenWord, Fintype.linearCombination_apply]

@[simp] private theorem evenCombination_second_apply (q : Nat)
    (c : EvenRow → ZMod 2) (j : Fin 4) :
    evenCombination q c (Sum.inr (Sum.inl j)) = combineFour c j := by
  simp [evenCombination, combineFour, evenWord, Fintype.linearCombination_apply]

@[simp] private theorem evenCombination_six_apply (q : Nat)
    (c : EvenRow → ZMod 2) (i : Fin q) (j : Fin 6) :
    evenCombination q c (Sum.inr (Sum.inr (i, j))) = combineSix c j := by
  simp [evenCombination, combineSix, evenWord, Fintype.linearCombination_apply]

theorem evenCombination_weight (q : Nat) (i : Fin 8) :
    HammingWeight (evenCombination q (coefficientBits i)) =
      ![0, 4 + 4 * q, 4 + 4 * q, 4 + 4 * q, 8,
        4 + 4 * q, 4 + 4 * q, 4 + 4 * q] i := by
  rw [← BinaryRowFamily.pairOverlap_self_eq_hammingWeight]
  simp only [BinaryRowFamily.pairOverlap, Fintype.sum_sum_type,
    Fintype.sum_prod_type, evenCombination_first_apply,
    evenCombination_second_apply, evenCombination_six_apply]
  simp_rw [combineFour_self_sum, combineSix_self_sum]
  fin_cases i <;> simp <;> omega

private theorem sum_ite_fin_eq {q : Nat} (a : Fin q) (special regular : Nat) :
    (∑ j : Fin q, if j = a then special else regular) =
      special + (q - 1) * regular := by
  classical
  have hEq : (Finset.univ.filter fun j : Fin q => j = a) = {a} := by
    ext j
    simp
  have hNe : (Finset.univ.filter fun j : Fin q => ¬ j = a) = Finset.univ.erase a := by
    ext j
    simp [and_comm]
  rw [Finset.sum_ite]
  rw [hEq, hNe]
  simp

/-- A fixed odd-row coset representative over an enumerated even combination. -/
def oddCosetWord {q : Nat} (a : OddRow q) (i : Fin 8) :
    Word (ZMod 2) (Column q) :=
  evenCombination q (coefficientBits i) + oddWord a

private theorem oddCoset_four_self_sum (i : Fin 8) :
    (∑ j : Fin 4,
        (combineFour (coefficientBits i) j *
          combineFour (coefficientBits i) j).val) +
      (∑ j : Fin 4,
        ((combineFour (coefficientBits i) j + 1) *
          (combineFour (coefficientBits i) j + 1)).val) = 4 := by
  fin_cases i <;> native_decide

private theorem oddCoset_special_six_self_sum (i : Fin 8) (b : Fin 2) :
    (∑ j : Fin 6,
      ((combineSix (coefficientBits i) j + oddBlock b j) *
        (combineSix (coefficientBits i) j + oddBlock b j)).val) = 3 := by
  fin_cases i <;> fin_cases b <;> native_decide

@[simp] private theorem oddCosetWord_first_apply {q : Nat}
    (a : OddRow q) (i : Fin 8) (j : Fin 4) :
    oddCosetWord a i (Sum.inl j) = combineFour (coefficientBits i) j := by
  simp [oddCosetWord, oddWord]

@[simp] private theorem oddCosetWord_second_apply {q : Nat}
    (a : OddRow q) (i : Fin 8) (j : Fin 4) :
    oddCosetWord a i (Sum.inr (Sum.inl j)) =
      combineFour (coefficientBits i) j + 1 := by
  simp [oddCosetWord, oddWord, leftBlock]

@[simp] private theorem oddCosetWord_six_apply {q : Nat}
    (a : OddRow q) (i : Fin 8) (u : Fin q) (j : Fin 6) :
    oddCosetWord a i (Sum.inr (Sum.inr (u, j))) =
      combineSix (coefficientBits i) j +
        (if u = a.1 then oddBlock a.2 j else 0) := by
  simp [oddCosetWord, oddWord]

private theorem oddCoset_six_block_self_sum {q : Nat}
    (a : OddRow q) (i : Fin 8) (u : Fin q) :
    (∑ j : Fin 6,
      (oddCosetWord a i (Sum.inr (Sum.inr (u, j))) *
        oddCosetWord a i (Sum.inr (Sum.inr (u, j)))).val) =
      if u = a.1 then 3 else ![0, 4, 4, 4, 0, 4, 4, 4] i := by
  by_cases hua : u = a.1
  · simp [hua, oddCoset_special_six_self_sum]
  · simp [hua, combineSix_self_sum]

theorem oddCosetWord_weight {q : Nat} (a : OddRow q) (i : Fin 8) :
    HammingWeight (oddCosetWord a i) =
      ![7, 3 + 4 * q, 3 + 4 * q, 3 + 4 * q, 7,
        3 + 4 * q, 3 + 4 * q, 3 + 4 * q] i := by
  rw [← BinaryRowFamily.pairOverlap_self_eq_hammingWeight]
  simp only [BinaryRowFamily.pairOverlap, Fintype.sum_sum_type,
    Fintype.sum_prod_type, oddCosetWord_first_apply,
    oddCosetWord_second_apply]
  rw [← Nat.add_assoc, oddCoset_four_self_sum]
  simp_rw [oddCoset_six_block_self_sum]
  rw [sum_ite_fin_eq a.1 3 (![0, 4, 4, 4, 0, 4, 4, 4] i)]
  have hq : 0 < q := Nat.zero_lt_of_lt a.1.isLt
  fin_cases i <;> simp <;> omega

theorem evenCoefficient_weightSum {A : Type*} [AddCommMonoid A]
    (q : Nat) (f : Nat → A) :
    (∑ i : Fin 8, f (HammingWeight (evenCombination q (coefficientBits i)))) =
      f 0 + f 8 + 6 • f (4 + 4 * q) := by
  simp_rw [evenCombination_weight]
  simp [Fin.sum_univ_succ]
  abel

theorem oddCosetCoefficient_weightSum {A : Type*} [AddCommMonoid A]
    {q : Nat} (a : OddRow q) (f : Nat → A) :
    (∑ i : Fin 8, f (HammingWeight (oddCosetWord a i))) =
      2 • f 7 + 6 • f (3 + 4 * q) := by
  simp_rw [oddCosetWord_weight]
  simp [Fin.sum_univ_succ]
  abel

theorem evenCombination_mem_evenCode (q : Nat) (c : EvenRow → ZMod 2) :
    evenCombination q c ∈ (family q).evenCode.carrier := by
  rw [evenCombination, Fintype.linearCombination_apply]
  exact Submodule.sum_mem _ fun r _ =>
    (family q).evenCode.carrier.smul_mem _ ((family q).evenRow_mem_evenCode r)

noncomputable def evenCombinationLinearMap (q : Nat) :
    (EvenRow → ZMod 2) →ₗ[ZMod 2] (family q).evenCode.carrier :=
  LinearMap.codRestrict (family q).evenCode.carrier
    (Fintype.linearCombination (ZMod 2) (@evenWord q))
    (evenCombination_mem_evenCode q)

@[simp] theorem coe_evenCombinationLinearMap_apply (q : Nat)
    (c : EvenRow → ZMod 2) :
    (evenCombinationLinearMap q c : Word (ZMod 2) (Column q)) = evenCombination q c :=
  rfl

private theorem evenCombinationLinearMap_bijective (q : Nat) :
    Function.Bijective (evenCombinationLinearMap q) := by
  constructor
  · intro c d hcd
    apply (evenRows_linearIndependent q).fintypeLinearCombination_injective
    exact congrArg Subtype.val hcd
  · intro x
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp x.2
    refine ⟨c, Subtype.ext ?_⟩
    exact hc

/-- Bottom-row coefficients are linearly equivalent to the actual code `G₀`. -/
noncomputable def evenCoefficientLinearEquiv (q : Nat) :
    (EvenRow → ZMod 2) ≃ₗ[ZMod 2] (family q).evenCode.carrier :=
  LinearEquiv.ofBijective (evenCombinationLinearMap q)
    (evenCombinationLinearMap_bijective q)

@[simp] theorem coe_evenCoefficientLinearEquiv_apply (q : Nat)
    (c : EvenRow → ZMod 2) :
    ((evenCoefficientLinearEquiv q c : (family q).evenCode.carrier) :
      Word (ZMod 2) (Column q)) = evenCombination q c :=
  rfl

/-- A finite weighted sum over an actual linear code. -/
def codeWeightSum {A : Type*} [AddCommMonoid A] {I : Type*}
    [Fintype I] [DecidableEq I] (C : LinearCode (ZMod 2) I) (f : Nat → A) : A :=
  letI : Fintype C.carrier := Fintype.ofFinite C.carrier
  ∑ x : C.carrier, f (HammingWeight (x : Word (ZMod 2) I))

set_option maxHeartbeats 800000 in
theorem evenCode_weightSum {A : Type*} [AddCommMonoid A]
    (q : Nat) (f : Nat → A) :
    codeWeightSum (family q).evenCode f =
      f 0 + f 8 + 6 • f (4 + 4 * q) := by
  classical
  letI : Fintype (family q).evenCode.carrier := Fintype.ofFinite _
  unfold codeWeightSum
  calc
    (∑ x : (family q).evenCode.carrier,
        f (HammingWeight (x : Word (ZMod 2) (Column q)))) =
        ∑ c : EvenRow → ZMod 2,
          f (HammingWeight
            (((evenCoefficientLinearEquiv q c : (family q).evenCode.carrier) :
              Word (ZMod 2) (Column q)))) :=
      ((evenCoefficientLinearEquiv q).toEquiv.sum_comp
        (fun x : (family q).evenCode.carrier =>
          f (HammingWeight (x : Word (ZMod 2) (Column q))))).symm
    _ = ∑ i : Fin 8,
        f (HammingWeight (evenCombination q (coefficientBits i))) := by
      simpa [coefficientEquiv] using
        (coefficientEquiv.sum_comp
          (fun c : EvenRow → ZMod 2 =>
            f (HammingWeight (evenCombination q c)))).symm
    _ = _ := evenCoefficient_weightSum q f

/-- The actual affine translate `G₀ + gᵃ`, weighted by Hamming weight. -/
def oddCosetWeightSum {A : Type*} [AddCommMonoid A]
    {q : Nat} (a : OddRow q) (f : Nat → A) : A :=
  letI : Fintype (family q).evenCode.carrier := Fintype.ofFinite _
  ∑ x : (family q).evenCode.carrier,
    f (HammingWeight ((x : Word (ZMod 2) (Column q)) + oddWord a))

set_option maxHeartbeats 800000 in
theorem oddCoset_weightSum {A : Type*} [AddCommMonoid A]
    {q : Nat} (a : OddRow q) (f : Nat → A) :
    oddCosetWeightSum a f = 2 • f 7 + 6 • f (3 + 4 * q) := by
  classical
  letI : Fintype (family q).evenCode.carrier := Fintype.ofFinite _
  unfold oddCosetWeightSum
  calc
    (∑ x : (family q).evenCode.carrier,
        f (HammingWeight ((x : Word (ZMod 2) (Column q)) + oddWord a))) =
        ∑ c : EvenRow → ZMod 2,
          f (HammingWeight
            (((evenCoefficientLinearEquiv q c : (family q).evenCode.carrier) :
              Word (ZMod 2) (Column q)) + oddWord a)) :=
      ((evenCoefficientLinearEquiv q).toEquiv.sum_comp
        (fun x : (family q).evenCode.carrier =>
          f (HammingWeight ((x : Word (ZMod 2) (Column q)) + oddWord a)))).symm
    _ = ∑ i : Fin 8, f (HammingWeight (oddCosetWord a i)) := by
      simpa [coefficientEquiv, oddCosetWord] using
        (coefficientEquiv.sum_comp
          (fun c : EvenRow → ZMod 2 =>
            f (HammingWeight (evenCombination q c + oddWord a)))).symm
    _ = _ := oddCosetCoefficient_weightSum a f

/-- The four-row presentation of the genuine extension `G₀ + ⟨gᵃ⟩`. -/
def extensionRow {q : Nat} (a : OddRow q) :
    Sum Unit EvenRow → Word (ZMod 2) (Column q)
  | .inl _ => oddWord a
  | .inr r => evenWord r

/-- The actual linear code `G₀ + ⟨gᵃ⟩`. -/
def singleOddExtensionCode {q : Nat} (a : OddRow q) : LinearCode (ZMod 2) (Column q) where
  carrier := Submodule.span (ZMod 2) (Set.range (extensionRow a))

private def extensionEmbedding {q : Nat} (a : OddRow q) :
    Sum Unit EvenRow → Sum (OddRow q) EvenRow
  | .inl _ => .inl a
  | .inr r => .inr r

private theorem extensionEmbedding_injective {q : Nat} (a : OddRow q) :
    Function.Injective (extensionEmbedding a) := by
  intro x y hxy
  rcases x with x | r <;> rcases y with y | s <;> simp_all [extensionEmbedding]

theorem extensionRows_linearIndependent {q : Nat} (a : OddRow q) :
    LinearIndependent (ZMod 2) (extensionRow a) := by
  have h := (rows_linearIndependent q).comp (extensionEmbedding a)
    (extensionEmbedding_injective a)
  have heq : extensionRow a = (family q).row ∘ extensionEmbedding a := by
    funext x
    rcases x with x | r <;> rfl
  rw [heq]
  exact h

def extensionCombination {q : Nat} (a : OddRow q)
    (c : Sum Unit EvenRow → ZMod 2) : Word (ZMod 2) (Column q) :=
  Fintype.linearCombination (ZMod 2) (extensionRow a) c

def extensionCoefficientBits : (ZMod 2 × Fin 8) → (Sum Unit EvenRow → ZMod 2)
  | (b, _), .inl _ => b
  | (_, i), .inr r => coefficientBits i r

private theorem extensionCoefficientBits_bijective :
    Function.Bijective extensionCoefficientBits := by
  native_decide

def extensionCoefficientEquiv :
    (ZMod 2 × Fin 8) ≃ (Sum Unit EvenRow → ZMod 2) :=
  Equiv.ofBijective extensionCoefficientBits extensionCoefficientBits_bijective

private theorem extensionCombination_index_zero {q : Nat} (a : OddRow q) (i : Fin 8) :
    extensionCombination a (extensionCoefficientBits (0, i)) =
      evenCombination q (coefficientBits i) := by
  classical
  funext j
  simp [extensionCombination, extensionCoefficientBits, extensionRow,
    evenCombination, Fintype.linearCombination_apply, Fintype.sum_sum_type]

private theorem extensionCombination_index_one {q : Nat} (a : OddRow q) (i : Fin 8) :
    extensionCombination a (extensionCoefficientBits (1, i)) = oddCosetWord a i := by
  classical
  funext j
  simp [extensionCombination, extensionCoefficientBits, extensionRow,
    oddCosetWord, evenCombination, Fintype.linearCombination_apply,
    Fintype.sum_sum_type, add_comm]

theorem extensionCombination_weight {q : Nat} (a : OddRow q)
    (b : ZMod 2) (i : Fin 8) :
    HammingWeight (extensionCombination a (extensionCoefficientBits (b, i))) =
      if b = 0 then
        ![0, 4 + 4 * q, 4 + 4 * q, 4 + 4 * q, 8,
          4 + 4 * q, 4 + 4 * q, 4 + 4 * q] i
      else
        ![7, 3 + 4 * q, 3 + 4 * q, 3 + 4 * q, 7,
          3 + 4 * q, 3 + 4 * q, 3 + 4 * q] i := by
  by_cases hb : b = 0
  · subst b
    rw [extensionCombination_index_zero, evenCombination_weight]
    simp
  · have hb1 : b = 1 := by
      apply ZMod.val_injective
      have hlt := ZMod.val_lt b
      have hpos : 0 < b.val :=
        Nat.pos_of_ne_zero ((ZMod.val_eq_zero b).not.mpr hb)
      change b.val = 1
      omega
    subst b
    rw [extensionCombination_index_one, oddCosetWord_weight]
    simp

theorem extensionCoefficient_weightSum {A : Type*} [AddCommMonoid A]
    {q : Nat} (a : OddRow q) (f : Nat → A) :
    (∑ bi : ZMod 2 × Fin 8,
      f (HammingWeight
        (extensionCombination a (extensionCoefficientBits bi)))) =
      (f 0 + f 8 + 6 • f (4 + 4 * q)) +
        (2 • f 7 + 6 • f (3 + 4 * q)) := by
  rw [Fintype.sum_prod_type]
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by native_decide]
  simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
    Finset.sum_singleton]
  rw [show (∑ i : Fin 8,
      f (HammingWeight
        (extensionCombination a (extensionCoefficientBits (0, i))))) =
      ∑ i : Fin 8, f (HammingWeight (evenCombination q (coefficientBits i))) by
        simp_rw [extensionCombination_index_zero]]
  rw [show (∑ i : Fin 8,
      f (HammingWeight
        (extensionCombination a (extensionCoefficientBits (1, i))))) =
      ∑ i : Fin 8, f (HammingWeight (oddCosetWord a i)) by
        simp_rw [extensionCombination_index_one]]
  rw [evenCoefficient_weightSum, oddCosetCoefficient_weightSum]

theorem extensionCombination_mem {q : Nat} (a : OddRow q)
    (c : Sum Unit EvenRow → ZMod 2) :
    extensionCombination a c ∈ (singleOddExtensionCode a).carrier := by
  rw [extensionCombination, Fintype.linearCombination_apply]
  exact Submodule.sum_mem _ fun r _ =>
    (singleOddExtensionCode a).carrier.smul_mem _
      (Submodule.subset_span ⟨r, rfl⟩)

noncomputable def extensionCombinationLinearMap {q : Nat} (a : OddRow q) :
    (Sum Unit EvenRow → ZMod 2) →ₗ[ZMod 2] (singleOddExtensionCode a).carrier :=
  LinearMap.codRestrict (singleOddExtensionCode a).carrier
    (Fintype.linearCombination (ZMod 2) (extensionRow a))
    (extensionCombination_mem a)

private theorem extensionCombinationLinearMap_bijective {q : Nat} (a : OddRow q) :
    Function.Bijective (extensionCombinationLinearMap a) := by
  constructor
  · intro c d hcd
    apply (extensionRows_linearIndependent a).fintypeLinearCombination_injective
    exact congrArg Subtype.val hcd
  · intro x
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp x.2
    exact ⟨c, Subtype.ext hc⟩

noncomputable def extensionCoefficientLinearEquiv {q : Nat} (a : OddRow q) :
    (Sum Unit EvenRow → ZMod 2) ≃ₗ[ZMod 2] (singleOddExtensionCode a).carrier :=
  LinearEquiv.ofBijective (extensionCombinationLinearMap a)
    (extensionCombinationLinearMap_bijective a)

@[simp] theorem coe_extensionCoefficientLinearEquiv_apply {q : Nat}
    (a : OddRow q) (c : Sum Unit EvenRow → ZMod 2) :
    ((extensionCoefficientLinearEquiv a c : (singleOddExtensionCode a).carrier) :
      Word (ZMod 2) (Column q)) = extensionCombination a c :=
  rfl

set_option maxHeartbeats 800000 in
theorem singleOddExtensionCode_weightSum {A : Type*} [AddCommMonoid A]
    {q : Nat} (a : OddRow q) (f : Nat → A) :
    codeWeightSum (singleOddExtensionCode a) f =
      (f 0 + f 8 + 6 • f (4 + 4 * q)) +
        (2 • f 7 + 6 • f (3 + 4 * q)) := by
  classical
  letI : Fintype (singleOddExtensionCode a).carrier := Fintype.ofFinite _
  unfold codeWeightSum
  calc
    (∑ x : (singleOddExtensionCode a).carrier,
        f (HammingWeight (x : Word (ZMod 2) (Column q)))) =
        ∑ c : Sum Unit EvenRow → ZMod 2,
          f (HammingWeight
            (((extensionCoefficientLinearEquiv a c :
              (singleOddExtensionCode a).carrier) : Word (ZMod 2) (Column q)))) :=
      ((extensionCoefficientLinearEquiv a).toEquiv.sum_comp
        (fun x : (singleOddExtensionCode a).carrier =>
          f (HammingWeight (x : Word (ZMod 2) (Column q))))).symm
    _ = ∑ bi : ZMod 2 × Fin 8,
        f (HammingWeight (extensionCombination a (extensionCoefficientBits bi))) := by
      simpa [extensionCoefficientEquiv] using
        (extensionCoefficientEquiv.sum_comp
          (fun c : Sum Unit EvenRow → ZMod 2 =>
            f (HammingWeight (extensionCombination a c)))).symm
    _ = _ := extensionCoefficient_weightSum a f

/-- The ordinary Hamming-weight enumerator of an actual binary linear code. -/
def codeWeightEnumerator {I : Type*} [Fintype I] [DecidableEq I]
    (C : LinearCode (ZMod 2) I) : Polynomial Nat :=
  codeWeightSum C fun w => Polynomial.X ^ w

/-- The ordinary enumerator of the actual affine coset `G₀ + gᵃ`. -/
def oddCosetWeightEnumerator {q : Nat} (a : OddRow q) : Polynomial Nat :=
  oddCosetWeightSum a fun w => Polynomial.X ^ w

/-- The source formula `W_G₀(x) = 1 + x⁸ + 6x^(4+2k)`. -/
theorem evenCode_weightEnumerator (q : Nat) :
    codeWeightEnumerator (family q).evenCode =
      1 + Polynomial.X ^ 8 + 6 * Polynomial.X ^ (4 + 2 * logicalCount q) := by
  have h := evenCode_weightSum q
    (fun w => (Polynomial.X : Polynomial Nat) ^ w)
  have hExp : 4 + 4 * q = 4 + 2 * logicalCount q := by
    simp [logicalCount]
    omega
  rw [hExp] at h
  simpa [codeWeightEnumerator, nsmul_eq_mul] using h

/-- The source formula `W_(G₀+gᵃ)(x) = 2x⁷ + 6x^(3+2k)`. -/
theorem oddCoset_weightEnumerator {q : Nat} (a : OddRow q) :
    oddCosetWeightEnumerator a =
      2 * Polynomial.X ^ 7 + 6 * Polynomial.X ^ (3 + 2 * logicalCount q) := by
  have h := oddCoset_weightSum a
    (fun w => (Polynomial.X : Polynomial Nat) ^ w)
  have hExp : 3 + 4 * q = 3 + 2 * logicalCount q := by
    simp [logicalCount]
    omega
  rw [hExp] at h
  simpa [oddCosetWeightEnumerator, nsmul_eq_mul] using h

/-- The one-odd-row linear extension enumerator is the sum of the two cosets. -/
theorem singleOddExtensionCode_weightEnumerator {q : Nat} (a : OddRow q) :
    codeWeightEnumerator (singleOddExtensionCode a) =
      (1 + Polynomial.X ^ 8 +
        6 * Polynomial.X ^ (4 + 2 * logicalCount q)) +
      (2 * Polynomial.X ^ 7 +
        6 * Polynomial.X ^ (3 + 2 * logicalCount q)) := by
  have h := singleOddExtensionCode_weightSum a
    (fun w => (Polynomial.X : Polynomial Nat) ^ w)
  have hExpEven : 4 + 4 * q = 4 + 2 * logicalCount q := by
    simp [logicalCount]
    omega
  have hExpOdd : 3 + 4 * q = 3 + 2 * logicalCount q := by
    simp [logicalCount]
    omega
  rw [hExpEven, hExpOdd] at h
  simpa [codeWeightEnumerator, nsmul_eq_mul] using h

end QEC.Distillation.Triorthogonal.BH12EvenFamily
