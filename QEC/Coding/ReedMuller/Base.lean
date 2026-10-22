import QEC.Coding.Core.Definitions

/-!
# Binary Reed--Muller evaluation codes

This module starts the source-neutral finite construction used by the HH18
punctured-code theorem. A polynomial is represented by its coefficients on
squarefree monomials, and a codeword is the actual Boolean-point evaluation of
those coefficients.

The exact dimension and complementary-duality results are proved here from
this concrete evaluation map; distance and divisibility are later layers.
None of these properties is stored in the code definition.
-/

noncomputable section

namespace QEC
namespace Coding
namespace ReedMuller

open scoped BigOperators

/-- A point of the Boolean m-cube, written as a binary word. -/
abbrev BooleanPoint (m : Nat) :=
  Word (ZMod 2) (Fin m)

/-- The Hamming weight of a Boolean point. -/
def pointWeight {m : Nat} (point : BooleanPoint m) : Nat :=
  HammingWeight point

/-- A squarefree monomial of degree at most r in m variables. -/
abbrev SquarefreeMonomial (m r : Nat) :=
  {support : Finset (Fin m) // support.card ≤ r}

/-- Algebraic-normal-form coefficients of degree at most r. -/
abbrev ANFPolynomial (m r : Nat) :=
  Word (ZMod 2) (SquarefreeMonomial m r)

/-- Evaluation of one squarefree monomial at one Boolean point. -/
def monomialValue {m r : Nat}
    (monomial : SquarefreeMonomial m r) (point : BooleanPoint m) : ZMod 2 :=
  ∏ coordinate ∈ monomial.1, point coordinate

/-- Simultaneous evaluation of an ANF polynomial on the Boolean m-cube. -/
def evaluationLinearMap (m r : Nat) :
    ANFPolynomial m r →ₗ[ZMod 2] Word (ZMod 2) (BooleanPoint m) where
  toFun polynomial point :=
    ∑ monomial, polynomial monomial * monomialValue monomial point
  map_add' := by
    intro left right
    funext point
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar polynomial
    funext point
    simp [Finset.mul_sum, mul_assoc]

@[simp]
theorem evaluationLinearMap_apply {m r : Nat}
    (polynomial : ANFPolynomial m r) (point : BooleanPoint m) :
    evaluationLinearMap m r polynomial point =
      ∑ monomial, polynomial monomial * monomialValue monomial point :=
  rfl

/-- The coefficient word with exactly one selected monomial. -/
noncomputable def basisPolynomial {m r : Nat}
    (monomial : SquarefreeMonomial m r) : ANFPolynomial m r :=
  canonicalBasisWord monomial

@[simp]
theorem evaluation_basisPolynomial {m r : Nat}
    (monomial : SquarefreeMonomial m r) (point : BooleanPoint m) :
    evaluationLinearMap m r (basisPolynomial monomial) point =
      monomialValue monomial point := by
  classical
  simp only [evaluationLinearMap_apply, basisPolynomial, canonicalBasisWord]
  rw [Fintype.sum_eq_single monomial]
  · simp
  · intro other hne
    simp [hne]

/-- The binary Reed--Muller code as the range of the concrete ANF evaluation map. -/
def reedMullerCode (r m : Nat) : LinearCode (ZMod 2) (BooleanPoint m) where
  carrier := LinearMap.range (evaluationLinearMap m r)

@[simp]
theorem mem_reedMullerCode {r m : Nat}
    (word : Word (ZMod 2) (BooleanPoint m)) :
    word ∈ (reedMullerCode r m).carrier ↔
      ∃ polynomial : ANFPolynomial m r,
        evaluationLinearMap m r polynomial = word := by
  simp [reedMullerCode]

/-- Every concrete polynomial evaluation belongs to the Reed--Muller code. -/
theorem evaluation_mem_reedMullerCode {r m : Nat}
    (polynomial : ANFPolynomial m r) :
    evaluationLinearMap m r polynomial ∈ (reedMullerCode r m).carrier :=
  (mem_reedMullerCode _).2 ⟨polynomial, rfl⟩

/-- The Boolean point whose support is exactly the supplied variable set. -/
private def supportPoint {m : Nat} (support : Finset (Fin m)) : BooleanPoint m :=
  fun coordinate => if coordinate ∈ support then 1 else 0

private theorem monomialValue_supportPoint {m r : Nat}
    (monomial : SquarefreeMonomial m r) (support : Finset (Fin m)) :
    monomialValue monomial (supportPoint support) =
      if monomial.1 ⊆ support then 1 else 0 := by
  classical
  by_cases hsubset : monomial.1 ⊆ support
  · rw [if_pos hsubset]
    unfold monomialValue
    apply Finset.prod_eq_one
    intro coordinate hcoordinate
    simp [supportPoint, hsubset hcoordinate]
  · rw [if_neg hsubset]
    obtain ⟨coordinate, hcoordinate, hmissing⟩ :
        ∃ coordinate ∈ monomial.1, coordinate ∉ support := by
      simpa only [Finset.not_subset] using hsubset
    unfold monomialValue
    exact Finset.prod_eq_zero hcoordinate (by simp [supportPoint, hmissing])

/-- Boolean ANF evaluation is injective, by triangular elimination on monomial support. -/
theorem evaluationLinearMap_injective (m r : Nat) :
    Function.Injective (evaluationLinearMap m r) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro polynomial hzero
  funext target
  have hcoeff :
      ∀ card : Nat, ∀ monomial : SquarefreeMonomial m r,
        monomial.1.card = card → polynomial monomial = 0 := by
    intro card
    induction card using Nat.strong_induction_on with
    | h card ih =>
        intro monomial hcard
        have happly := congrFun hzero (supportPoint monomial.1)
        rw [evaluationLinearMap_apply] at happly
        have hsingle :
            (∑ other,
              polynomial other * monomialValue other (supportPoint monomial.1)) =
              polynomial monomial := by
          rw [Fintype.sum_eq_single monomial]
          · rw [monomialValue_supportPoint]
            simp
          · intro other hne
            by_cases hsubset : other.1 ⊆ monomial.1
            · have hsupportNe : other.1 ≠ monomial.1 := by
                intro heq
                exact hne (Subtype.ext heq)
              have hstrict : other.1 ⊂ monomial.1 :=
                (Finset.ssubset_iff_subset_ne).2 ⟨hsubset, hsupportNe⟩
              have hcardLt : other.1.card < monomial.1.card :=
                Finset.card_lt_card hstrict
              have hother : polynomial other = 0 :=
                ih other.1.card (by simpa [hcard] using hcardLt) other rfl
              simp [monomialValue_supportPoint, hsubset, hother]
            · simp [monomialValue_supportPoint, hsubset]
        rw [hsingle] at happly
        simpa using happly
  exact hcoeff target.1.card target rfl

/-- The cumulative binomial count through degree `r`. -/
def binomialUpTo (m r : Nat) : Nat :=
  ∑ i ∈ Finset.Icc 0 r, Nat.choose m i

private theorem card_squarefreeMonomial_eq_binomialUpTo (m r : Nat) :
    Fintype.card (SquarefreeMonomial m r) = binomialUpTo m r := by
  classical
  rw [Fintype.card_subtype]
  change ((Finset.univ : Finset (Finset (Fin m))).filter fun support =>
      support.card ≤ r).card = _
  let supports := (Finset.univ : Finset (Fin m)).powerset
  have hall : (Finset.univ : Finset (Finset (Fin m))) = supports := by
    ext support
    simp [supports]
  rw [hall]
  calc
    (supports.filter fun support => support.card ≤ r).card =
        (supports.filter fun support =>
          support.card ∈ Finset.Icc 0 r).card := by
      congr 1
      ext support
      simp
    _ = ∑ i ∈ Finset.Icc 0 r,
        (supports.filter fun support => support.card = i).card := by
      symm
      exact Finset.sum_card_fiberwise_eq_card_filter
        supports (Finset.Icc 0 r) Finset.card
    _ = ∑ i ∈ Finset.Icc 0 r, Nat.choose m i := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← Finset.powersetCard_eq_filter, Finset.card_powersetCard]
      simp
    _ = binomialUpTo m r := rfl

/-- The number of squarefree monomials through degree `r` is the exact
cumulative binomial sum. -/
theorem squarefreeMonomial_card_eq_sum_choose (m r : Nat) :
    Fintype.card (SquarefreeMonomial m r) =
      ∑ i ∈ Finset.Icc 0 r, Nat.choose m i := by
  simpa [binomialUpTo] using card_squarefreeMonomial_eq_binomialUpTo m r

/-- The Reed--Muller code dimension is the number of squarefree ANF monomials. -/
theorem reedMullerCode_dimension_eq_card_squarefree (r m : Nat) :
    Dimension (reedMullerCode r m) = Fintype.card (SquarefreeMonomial m r) := by
  change Module.finrank (ZMod 2) (LinearMap.range (evaluationLinearMap m r)) = _
  rw [LinearMap.finrank_range_of_inj (evaluationLinearMap_injective m r)]
  exact
    (Module.finrank_fintype_fun_eq_card (ZMod 2)
      (η := SquarefreeMonomial m r))

/-- The Reed--Muller code dimension is the source-stated cumulative binomial
sum through its degree bound. -/
theorem reedMullerCode_dimension_eq_binomialUpTo (r m : Nat) :
    Dimension (reedMullerCode r m) = binomialUpTo m r := by
  rw [reedMullerCode_dimension_eq_card_squarefree,
    card_squarefreeMonomial_eq_binomialUpTo]

/-- Raw source form of the Reed--Muller dimension identity. -/
theorem reedMullerCode_dimension_eq_sum_choose (r m : Nat) :
    Dimension (reedMullerCode r m) =
      ∑ i ∈ Finset.Icc 0 r, Nat.choose m i := by
  simpa [binomialUpTo] using reedMullerCode_dimension_eq_binomialUpTo r m

private theorem monomialValue_eq_fullProduct {m r : Nat}
    (monomial : SquarefreeMonomial m r) (point : BooleanPoint m) :
    monomialValue monomial point =
      ∏ coordinate : Fin m,
        if coordinate ∈ monomial.1 then point coordinate else 1 := by
  classical
  simp [monomialValue]

private theorem monomial_pairing_zero {m r s : Nat}
    (left : SquarefreeMonomial m r) (right : SquarefreeMonomial m s)
    (hdegree : r + s < m) :
    ∑ point : BooleanPoint m,
      monomialValue left point * monomialValue right point = 0 := by
  classical
  have hunionCard : (left.1 ∪ right.1).card < m := by
    calc
      (left.1 ∪ right.1).card ≤ left.1.card + right.1.card :=
        Finset.card_union_le _ _
      _ ≤ r + s := Nat.add_le_add left.2 right.2
      _ < m := hdegree
  have hunion : left.1 ∪ right.1 ≠ Finset.univ := by
    intro heq
    have hcard : (left.1 ∪ right.1).card = m := by
      rw [heq]
      simp
    omega
  obtain ⟨free, hfree⟩ : ∃ free : Fin m, free ∉ left.1 ∪ right.1 := by
    by_contra hnone
    apply hunion
    apply Finset.eq_univ_of_forall
    intro coordinate
    by_contra hcoordinate
    exact hnone ⟨coordinate, hcoordinate⟩
  have hfreeLeft : free ∉ left.1 := by
    exact fun hmem => hfree (Finset.mem_union_left _ hmem)
  have hfreeRight : free ∉ right.1 := by
    exact fun hmem => hfree (Finset.mem_union_right _ hmem)
  calc
    ∑ point : BooleanPoint m,
        monomialValue left point * monomialValue right point =
        ∑ point : BooleanPoint m,
          ∏ coordinate : Fin m,
            ((if coordinate ∈ left.1 then point coordinate else 1) *
              (if coordinate ∈ right.1 then point coordinate else 1)) := by
          apply Finset.sum_congr rfl
          intro point _hpoint
          rw [monomialValue_eq_fullProduct, monomialValue_eq_fullProduct,
            ← Finset.prod_mul_distrib]
    _ = ∏ coordinate : Fin m, ∑ bit : ZMod 2,
          ((if coordinate ∈ left.1 then bit else 1) *
            (if coordinate ∈ right.1 then bit else 1)) := by
          rw [Fintype.prod_sum]
    _ = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ free)
          simp [hfreeLeft, hfreeRight]
          exact ZMod.natCast_self 2

private theorem evaluation_eq_sum_basis {m r : Nat}
    (polynomial : ANFPolynomial m r) :
    evaluationLinearMap m r polynomial =
      ∑ monomial, polynomial monomial •
        evaluationLinearMap m r (basisPolynomial monomial) := by
  classical
  simp_rw [← map_smul]
  rw [← map_sum]
  congr 1
  ext target
  simp only [Finset.sum_apply, Pi.smul_apply]
  rw [Fintype.sum_eq_single target]
  · simp [basisPolynomial, canonicalBasisWord]
  · intro other hne
    simp [basisPolynomial, canonicalBasisWord, hne]

/-- Evaluations of total degree below m are orthogonal on the Boolean cube. -/
theorem evaluation_pairing_eq_zero_of_add_lt {m r s : Nat}
    (hdegree : r + s < m)
    (left : ANFPolynomial m r) (right : ANFPolynomial m s) :
    wordPairing (evaluationLinearMap m r left)
      (evaluationLinearMap m s right) = 0 := by
  classical
  rw [evaluation_eq_sum_basis, evaluation_eq_sum_basis]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro rightMonomial _hright
  rw [show (∑ leftMonomial,
      left leftMonomial •
        wordPairing
          (evaluationLinearMap m r (basisPolynomial leftMonomial))
          (evaluationLinearMap m s (basisPolynomial rightMonomial))) = 0 by
    apply Finset.sum_eq_zero
    intro leftMonomial _hleft
    have hpair :
        wordPairing
          (evaluationLinearMap m r (basisPolynomial leftMonomial))
          (evaluationLinearMap m s (basisPolynomial rightMonomial)) = 0 := by
      change
        (∑ point,
          evaluationLinearMap m r (basisPolynomial leftMonomial) point *
            evaluationLinearMap m s (basisPolynomial rightMonomial) point) = 0
      simp_rw [evaluation_basisPolynomial]
      exact monomial_pairing_zero leftMonomial rightMonomial hdegree
    rw [hpair]
    simp]
  simp

/-- Reed--Muller codes whose degrees sum below m satisfy dual containment. -/
theorem reedMullerCode_le_dual_of_add_lt {m r s : Nat}
    (hdegree : r + s < m) :
    (reedMullerCode s m).carrier ≤ (reedMullerCode r m).dual.carrier := by
  intro word hword
  rcases (mem_reedMullerCode word).1 hword with ⟨right, rfl⟩
  refine ((reedMullerCode r m).mem_dual _).2 ?_
  intro codeword hcodeword
  rcases (mem_reedMullerCode codeword).1 hcodeword with ⟨left, rfl⟩
  exact evaluation_pairing_eq_zero_of_add_lt
    (by simpa [Nat.add_comm] using hdegree) right left

/-- The Boolean product attached to an arbitrary finite coordinate support.
Unlike `monomialValue`, the support is not required to satisfy a degree bound:
the extra freedom is used only inside the Ward induction below. -/
private def supportValue {m : Nat} (support : Finset (Fin m))
    (point : BooleanPoint m) : ZMod 2 :=
  ∏ coordinate ∈ support, point coordinate

/-- Restrict a finite binary sum of monomial rows by an arbitrary Boolean
support.  The empty support recovers the ordinary sum of those rows. -/
private def restrictedEvaluation {m r : Nat} (support : Finset (Fin m))
    (monomials : List (SquarefreeMonomial m r)) :
    Word (ZMod 2) (BooleanPoint m) :=
  fun point => supportValue support point *
    (monomials.map fun monomial => monomialValue monomial point).sum

/-- The natural overlap count of two binary words. -/
private def binaryOverlap {m : Nat}
    (left right : Word (ZMod 2) (BooleanPoint m)) : Nat :=
  HammingWeight fun point => left point * right point

private theorem binary_eq_one_of_ne_zero (value : ZMod 2)
    (hvalue : value ≠ 0) : value = 1 := by
  have hvalNe : value.val ≠ 0 :=
    (ZMod.val_eq_zero value).not.mpr hvalue
  have hvalLt : value.val < 2 := ZMod.val_lt value
  apply (ZMod.val_eq_one (by omega) value).mp
  omega

private theorem monomialValue_eq_supportValue {m r : Nat}
    (monomial : SquarefreeMonomial m r) (point : BooleanPoint m) :
    monomialValue monomial point = supportValue monomial.1 point :=
  rfl

/-- Boolean support products are idempotent under union. -/
private theorem supportValue_union {m : Nat}
    (left right : Finset (Fin m)) (point : BooleanPoint m) :
    supportValue left point * supportValue right point =
      supportValue (left ∪ right) point := by
  classical
  unfold supportValue
  have hinter : left ∩ right ⊆ left ∪ right := by
    intro coordinate hcoordinate
    exact Finset.mem_union_left _ (Finset.mem_of_mem_inter_left hcoordinate)
  calc
    (∏ coordinate ∈ left, point coordinate) *
        ∏ coordinate ∈ right, point coordinate =
        (∏ coordinate ∈ left ∪ right, point coordinate) *
          ∏ coordinate ∈ left ∩ right, point coordinate :=
      (Finset.prod_union_inter (f := fun coordinate : Fin m => point coordinate)).symm
    _ = ((∏ coordinate ∈ (left ∪ right) \ (left ∩ right), point coordinate) *
          ∏ coordinate ∈ left ∩ right, point coordinate) *
            ∏ coordinate ∈ left ∩ right, point coordinate := by
      rw [Finset.prod_sdiff hinter]
    _ = (∏ coordinate ∈ (left ∪ right) \ (left ∩ right), point coordinate) *
          ∏ coordinate ∈ left ∩ right, point coordinate := by
      have hidempotent :
          (∏ coordinate ∈ left ∩ right, point coordinate) *
              ∏ coordinate ∈ left ∩ right, point coordinate =
            ∏ coordinate ∈ left ∩ right, point coordinate := by
        have hpoint : ∀ coordinate : Fin m,
            point coordinate * point coordinate = point coordinate := by
          intro coordinate
          by_cases hzero : point coordinate = 0
          · simp [hzero]
          · rw [binary_eq_one_of_ne_zero _ hzero]
            norm_num
        calc
          (∏ coordinate ∈ left ∩ right, point coordinate) *
              ∏ coordinate ∈ left ∩ right, point coordinate =
              ∏ coordinate ∈ left ∩ right,
                point coordinate * point coordinate := by
            rw [← Finset.prod_mul_distrib]
          _ = ∏ coordinate ∈ left ∩ right, point coordinate := by
            apply Finset.prod_congr rfl
            intro coordinate _hcoordinate
            exact hpoint coordinate
      rw [mul_assoc, hidempotent]
    _ = ∏ coordinate ∈ left ∪ right, point coordinate :=
      Finset.prod_sdiff hinter

/-- The raw row associated to a support has its exact Boolean-cube weight. -/
private theorem supportValue_ne_zero_iff {m : Nat}
    (support : Finset (Fin m)) (point : BooleanPoint m) :
    supportValue support point ≠ 0 ↔ support ⊆ hammingSupport point := by
  rw [supportValue, Finset.prod_ne_zero_iff]
  constructor
  · intro h coordinate hcoordinate
    simpa [hammingSupport] using h coordinate hcoordinate
  · intro h coordinate hcoordinate
    simpa [hammingSupport] using h hcoordinate

private def constrainedPointEquiv {m : Nat} (support : Finset (Fin m)) :
    {point : BooleanPoint m // support ⊆ hammingSupport point} ≃
      Word (ZMod 2) {coordinate : Fin m // coordinate ∉ support} where
  toFun point coordinate := point.1 coordinate.1
  invFun complement :=
    ⟨fun coordinate => if h : coordinate ∈ support then 1 else complement ⟨coordinate, h⟩,
      by
        intro coordinate hcoordinate
        simp [hammingSupport, hcoordinate]⟩
  left_inv point := by
    apply Subtype.ext
    funext coordinate
    by_cases hcoordinate : coordinate ∈ support
    · simp only [hcoordinate, dite_true]
      have hnonzero : point.1 coordinate ≠ 0 := by
        simpa [hammingSupport] using point.2 hcoordinate
      exact (binary_eq_one_of_ne_zero _ hnonzero).symm
    · simp [hcoordinate]
  right_inv complement := by
    funext coordinate
    simp [coordinate.2]

private theorem hammingWeight_supportValue {m : Nat}
    (support : Finset (Fin m)) :
    HammingWeight (supportValue support : Word (ZMod 2) (BooleanPoint m)) =
      2 ^ (m - support.card) := by
  classical
  rw [HammingWeight, hammingSupport]
  calc
    ((Finset.univ : Finset (BooleanPoint m)).filter
        fun point => supportValue support point ≠ 0).card =
        Fintype.card {point : BooleanPoint m //
          support ⊆ hammingSupport point} := by
            rw [Fintype.card_subtype]
            congr 1
            ext point
            simp [supportValue_ne_zero_iff]
    _ = Fintype.card
        (Word (ZMod 2) {coordinate : Fin m // coordinate ∉ support}) :=
      Fintype.card_congr (constrainedPointEquiv support)
    _ = 2 ^ (m - support.card) := by
      rw [Fintype.card_fun]
      simp [ZMod.card]

/-- The exact binary inclusion--exclusion step used in Ward's induction. -/
private theorem hammingWeight_add_two_mul_binaryOverlap {m : Nat}
    (left right : Word (ZMod 2) (BooleanPoint m)) :
    HammingWeight left + HammingWeight right =
      HammingWeight (left + right) + 2 * binaryOverlap left right := by
  classical
  have hpoint : ∀ point : BooleanPoint m,
      (if left point ≠ 0 then 1 else 0) + (if right point ≠ 0 then 1 else 0) =
        (if left point + right point ≠ 0 then 1 else 0) +
          2 * (if left point * right point ≠ 0 then 1 else 0) := by
    intro point
    by_cases hleft : left point = 0
    · simp [hleft]
    · rw [binary_eq_one_of_ne_zero _ hleft]
      by_cases hright : right point = 0
      · simp [hright]
      · rw [binary_eq_one_of_ne_zero _ hright]
        decide
  have hsum := Finset.sum_congr rfl
    (fun point (_hpoint : point ∈ (Finset.univ : Finset (BooleanPoint m))) =>
      hpoint point)
  simp only [HammingWeight, hammingSupport, Finset.card_filter, binaryOverlap]
  rw [← Finset.sum_add_distrib, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  simpa only [Pi.add_apply] using hsum

private theorem restrictedEvaluation_cons {m r : Nat}
    (support : Finset (Fin m)) (monomial : SquarefreeMonomial m r)
    (tail : List (SquarefreeMonomial m r)) :
    restrictedEvaluation support (monomial :: tail) =
      supportValue (support ∪ monomial.1) + restrictedEvaluation support tail := by
  funext point
  simp only [restrictedEvaluation, List.map_cons, List.sum_cons, Pi.add_apply]
  rw [mul_add, monomialValue_eq_supportValue, supportValue_union]

private theorem binaryOverlap_restrictedEvaluation_supportValue {m r : Nat}
    (support : Finset (Fin m)) (monomial : SquarefreeMonomial m r)
    (tail : List (SquarefreeMonomial m r)) :
    binaryOverlap (supportValue (support ∪ monomial.1))
      (restrictedEvaluation support tail) =
        HammingWeight (restrictedEvaluation (support ∪ monomial.1) tail) := by
  unfold binaryOverlap
  congr 1
  funext point
  simp only [restrictedEvaluation]
  calc
    supportValue (support ∪ monomial.1) point *
        (supportValue support point *
          (tail.map fun other => monomialValue other point).sum) =
        (supportValue (support ∪ monomial.1) point * supportValue support point) *
          (tail.map fun other => monomialValue other point).sum := by ring
    _ = supportValue (support ∪ monomial.1) point *
          (tail.map fun other => monomialValue other point).sum := by
      rw [supportValue_union]
      have hunion : (support ∪ monomial.1) ∪ support =
          support ∪ monomial.1 := by
        ext coordinate
        simp only [Finset.mem_union]
        tauto
      rw [hunion]

/-- Ward's overlap induction for a finite list of degree-`r` monomial rows.
The list remains explicit: no divisibility fact is stored in the code itself. -/
private theorem restrictedEvaluation_hammingWeight_dvd_pow_two
    {m r : Nat} (hr : 0 < r) :
    ∀ (nu : Nat) (support : Finset (Fin m))
      (monomials : List (SquarefreeMonomial m r)),
      support.card + nu * r < m →
        2 ^ nu ∣ HammingWeight (restrictedEvaluation support monomials) := by
  intro nu
  induction nu with
  | zero =>
      intro support monomials _hbound
      simp
  | succ nu ih =>
      intro support monomials hbound
      induction monomials with
      | nil =>
          rw [show restrictedEvaluation support [] = 0 by
            funext point
            simp [restrictedEvaluation]]
          simp
      | cons monomial tail ihtail =>
          have htail :
              2 ^ (nu + 1) ∣ HammingWeight (restrictedEvaluation support tail) :=
            ihtail
          have hunionBound : (support ∪ monomial.1).card + nu * r < m := by
            have hcard : (support ∪ monomial.1).card ≤ support.card + r := by
              calc
                (support ∪ monomial.1).card ≤ support.card + monomial.1.card :=
                  Finset.card_union_le _ _
                _ ≤ support.card + r := Nat.add_le_add_left monomial.2 _
            rw [Nat.succ_mul] at hbound
            omega
          have hoverlap :
              2 ^ nu ∣ HammingWeight
                (restrictedEvaluation (support ∪ monomial.1) tail) :=
            ih (support ∪ monomial.1) tail hunionBound
          have hheadExponent : nu + 1 ≤ m - (support ∪ monomial.1).card := by
            have hcard : (support ∪ monomial.1).card ≤ support.card + r := by
              calc
                (support ∪ monomial.1).card ≤ support.card + monomial.1.card :=
                  Finset.card_union_le _ _
                _ ≤ support.card + r := Nat.add_le_add_left monomial.2 _
            have hmul : nu ≤ nu * r := Nat.le_mul_of_pos_right nu hr
            rw [Nat.succ_mul] at hbound
            omega
          have hhead :
              2 ^ (nu + 1) ∣ HammingWeight
                (supportValue (support ∪ monomial.1)) := by
            rw [hammingWeight_supportValue]
            exact pow_dvd_pow 2 hheadExponent
          have htwiceOverlap :
              2 ^ (nu + 1) ∣
                2 * binaryOverlap (supportValue (support ∪ monomial.1))
                  (restrictedEvaluation support tail) := by
            rw [binaryOverlap_restrictedEvaluation_supportValue]
            simpa only [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
              (Nat.mul_dvd_mul_left 2 hoverlap)
          have hsum :
              2 ^ (nu + 1) ∣
                HammingWeight (supportValue (support ∪ monomial.1)) +
                  HammingWeight (restrictedEvaluation support tail) :=
            hhead.add htail
          have hidentity :
              HammingWeight (restrictedEvaluation support (monomial :: tail)) +
                2 * binaryOverlap (supportValue (support ∪ monomial.1))
                  (restrictedEvaluation support tail) =
                HammingWeight (supportValue (support ∪ monomial.1)) +
                  HammingWeight (restrictedEvaluation support tail) := by
            rw [restrictedEvaluation_cons]
            simpa [Nat.add_comm] using
              (hammingWeight_add_two_mul_binaryOverlap
                (supportValue (support ∪ monomial.1))
                (restrictedEvaluation support tail)).symm
          rw [← hidentity] at hsum
          exact (Nat.dvd_add_iff_left htwiceOverlap).2 hsum

private noncomputable def activeMonomials {m r : Nat}
    (polynomial : ANFPolynomial m r) : List (SquarefreeMonomial m r) :=
  (Finset.univ.filter fun monomial => polynomial monomial ≠ 0).toList

private theorem evaluation_eq_restrictedEvaluation_activeMonomials {m r : Nat}
    (polynomial : ANFPolynomial m r) :
    evaluationLinearMap m r polynomial =
      restrictedEvaluation ∅ (activeMonomials polynomial) := by
  classical
  funext point
  simp only [evaluationLinearMap_apply, restrictedEvaluation, supportValue,
    Finset.prod_empty, one_mul, activeMonomials]
  rw [Finset.sum_map_toList]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro monomial _hmonomial
  by_cases hzero : polynomial monomial = 0
  · simp [hzero]
  · have hone : polynomial monomial = 1 :=
      binary_eq_one_of_ne_zero _ hzero
    simp [hone]

/-- Every actual word of a nonconstant full Reed--Muller code has the Ward
power-of-two divisibility stated in HH18's full-code input. -/
theorem reedMullerCode_hammingWeight_dvd_pow_two {nu r m : Nat}
    (hr : 0 < r) (hnu : nu * r < m)
    {word : Word (ZMod 2) (BooleanPoint m)}
    (hword : word ∈ (reedMullerCode r m).carrier) :
    2 ^ nu ∣ HammingWeight word := by
  rcases (mem_reedMullerCode word).1 hword with ⟨polynomial, hpolynomial⟩
  rw [← hpolynomial, evaluation_eq_restrictedEvaluation_activeMonomials]
  simpa using restrictedEvaluation_hammingWeight_dvd_pow_two hr nu ∅
    (activeMonomials polynomial) (by simpa using hnu)

/-- The Boolean m-cube has exactly 2^m points. -/
theorem card_booleanPoint (m : Nat) :
    Fintype.card (BooleanPoint m) = 2 ^ m := by
  simp [BooleanPoint, ZMod.card]

private noncomputable def highSquarefreeComplementEquiv {m r : Nat}
    (hrm : r < m) :
    {support : Finset (Fin m) // ¬ support.card ≤ r} ≃
      SquarefreeMonomial m (m - r - 1) where
  toFun support := ⟨support.1ᶜ, by
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega⟩
  invFun support := ⟨support.1ᶜ, by
    intro hcard
    rw [Finset.card_compl] at hcard
    simp only [Fintype.card_fin] at hcard
    omega⟩
  left_inv support := by
    apply Subtype.ext
    simp
  right_inv support := by
    apply Subtype.ext
    simp

private theorem squarefree_card_add_complementary {m r : Nat}
    (hrm : r < m) :
    Fintype.card (SquarefreeMonomial m r) +
      Fintype.card (SquarefreeMonomial m (m - r - 1)) =
        Fintype.card (BooleanPoint m) := by
  classical
  have hhigh :
      Fintype.card {support : Finset (Fin m) // ¬ support.card ≤ r} =
        Fintype.card (SquarefreeMonomial m (m - r - 1)) :=
    Fintype.card_congr (highSquarefreeComplementEquiv hrm)
  calc
    Fintype.card (SquarefreeMonomial m r) +
        Fintype.card (SquarefreeMonomial m (m - r - 1)) =
        Fintype.card {support : Finset (Fin m) // support.card ≤ r} +
          Fintype.card {support : Finset (Fin m) // ¬ support.card ≤ r} := by
            rw [hhigh]
    _ = Fintype.card {support : Finset (Fin m) // support.card ≤ r} +
          (Fintype.card (Finset (Fin m)) -
            Fintype.card {support : Finset (Fin m) // support.card ≤ r}) := by
          rw [Fintype.card_subtype_compl]
    _ = Fintype.card (Finset (Fin m)) := by
          exact Nat.add_sub_of_le (Fintype.card_subtype_le _)
    _ = Fintype.card (BooleanPoint m) := by
          rw [Fintype.card_finset, Fintype.card_fin, card_booleanPoint]

/-- Complementary full Reed--Muller codes are exact duals below the full degree. -/
theorem reedMullerCode_dual_eq_complementary {r m : Nat}
    (hrm : r < m) :
    (reedMullerCode (m - r - 1) m).dual.carrier =
      (reedMullerCode r m).carrier := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact reedMullerCode_le_dual_of_add_lt (r := m - r - 1) (s := r) (by omega)
  · change Dimension (reedMullerCode r m) =
      Dimension (reedMullerCode (m - r - 1) m).dual
    rw [LinearCode.dual_dimension_eq_length_sub_dimension]
    have hdimension :
        Dimension (reedMullerCode r m) +
          Dimension (reedMullerCode (m - r - 1) m) =
            Length (ZMod 2) (BooleanPoint m) := by
      rw [reedMullerCode_dimension_eq_card_squarefree,
        reedMullerCode_dimension_eq_card_squarefree]
      simpa [Length] using squarefree_card_add_complementary hrm
    omega

end ReedMuller
end Coding
end QEC
