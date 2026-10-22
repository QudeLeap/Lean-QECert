import QEC.Coding.ReedMuller.Base

/-!
# Punctured and shortened binary Reed--Muller codes

This module defines the HH18 coordinate cut as actual restriction maps. The
punctured code is the image of Reed--Muller evaluation under kept-coordinate
restriction. The shortened code is the image of the Reed--Muller words whose
low-coordinate restriction is zero.
-/

noncomputable section

namespace QEC
namespace Coding
namespace PuncturedReedMuller

open ReedMuller

/-- Boolean points removed by the HH18 puncture. -/
abbrev LowPoint (m w : Nat) :=
  {point : BooleanPoint m // pointWeight point ≤ w}

/-- Boolean points retained by the HH18 puncture. -/
abbrev KeptPoint (m w : Nat) :=
  {point : BooleanPoint m // w < pointWeight point}

/-- The exact natural-number hypothesis of HH18 Theorem 1. -/
def Admissible (w r m : Nat) : Prop :=
  0 ≤ 2 * w ∧ 2 * w < 2 * r ∧ 2 * r < m

/-- Restrict a full Boolean-cube word to the low coordinates. -/
def restrictLow (m w : Nat) :
    Word (ZMod 2) (BooleanPoint m) →ₗ[ZMod 2]
      Word (ZMod 2) (LowPoint m w) where
  toFun word point := word point.1
  map_add' := by
    intro left right
    rfl
  map_smul' := by
    intro scalar word
    rfl

/-- Restrict a full Boolean-cube word to the kept coordinates. -/
def restrictKept (m w : Nat) :
    Word (ZMod 2) (BooleanPoint m) →ₗ[ZMod 2]
      Word (ZMod 2) (KeptPoint m w) where
  toFun word point := word point.1
  map_add' := by
    intro left right
    rfl
  map_smul' := by
    intro scalar word
    rfl

@[simp]
theorem restrictLow_apply {m w : Nat}
    (word : Word (ZMod 2) (BooleanPoint m)) (point : LowPoint m w) :
    restrictLow m w word point = word point.1 :=
  rfl

@[simp]
theorem restrictKept_apply {m w : Nat}
    (word : Word (ZMod 2) (BooleanPoint m)) (point : KeptPoint m w) :
    restrictKept m w word point = word point.1 :=
  rfl

/-- Extend a kept-coordinate word by zero on every removed coordinate. -/
def zeroExtendKept (m w : Nat) :
    Word (ZMod 2) (KeptPoint m w) →ₗ[ZMod 2]
      Word (ZMod 2) (BooleanPoint m) where
  toFun word point :=
    if hpoint : w < pointWeight point then word ⟨point, hpoint⟩ else 0
  map_add' := by
    intro left right
    funext point
    by_cases hpoint : w < pointWeight point <;> simp [hpoint]
  map_smul' := by
    intro scalar word
    funext point
    by_cases hpoint : w < pointWeight point <;> simp [hpoint]

@[simp]
theorem restrictKept_zeroExtendKept {m w : Nat}
    (word : Word (ZMod 2) (KeptPoint m w)) :
    restrictKept m w (zeroExtendKept m w word) = word := by
  ext point
  simp [zeroExtendKept, point.2]

/-- The actual coordinate restriction of RM(r,m). -/
def puncturedReedMullerCode (r m w : Nat) :
    LinearCode (ZMod 2) (KeptPoint m w) where
  carrier :=
    (reedMullerCode r m).carrier.map (restrictKept m w)

@[simp]
theorem mem_puncturedReedMullerCode {r m w : Nat}
    (word : Word (ZMod 2) (KeptPoint m w)) :
    word ∈ (puncturedReedMullerCode r m w).carrier ↔
      ∃ full : Word (ZMod 2) (BooleanPoint m),
        full ∈ (reedMullerCode r m).carrier ∧
          restrictKept m w full = word := by
  simp [puncturedReedMullerCode]

/-- RM words satisfying the shortening zero condition before restriction. -/
def shortenedReedMullerDomain (r m w : Nat) :
    Submodule (ZMod 2) (Word (ZMod 2) (BooleanPoint m)) :=
  (reedMullerCode r m).carrier ⊓ LinearMap.ker (restrictLow m w)

/-- The shortened Reed--Muller code obtained from the actual zero condition. -/
def shortenedReedMullerCode (r m w : Nat) :
    LinearCode (ZMod 2) (KeptPoint m w) where
  carrier :=
    (shortenedReedMullerDomain r m w).map (restrictKept m w)

@[simp]
theorem mem_shortenedReedMullerCode {r m w : Nat}
    (word : Word (ZMod 2) (KeptPoint m w)) :
    word ∈ (shortenedReedMullerCode r m w).carrier ↔
      ∃ full : Word (ZMod 2) (BooleanPoint m),
        full ∈ (reedMullerCode r m).carrier ∧
          restrictLow m w full = 0 ∧
          restrictKept m w full = word := by
  simp [shortenedReedMullerCode, shortenedReedMullerDomain, and_assoc]

/-- Shortening produces a subcode of the corresponding punctured code. -/
theorem shortenedReedMullerCode_le_puncturedReedMullerCode
    (r m w : Nat) :
    (shortenedReedMullerCode r m w).carrier ≤
      (puncturedReedMullerCode r m w).carrier := by
  intro word hword
  rcases (mem_shortenedReedMullerCode word).1 hword with
    ⟨full, hfull, _hlow, rfl⟩
  exact (mem_puncturedReedMullerCode _).2 ⟨full, hfull, rfl⟩

private theorem binary_eq_one_of_ne_zero (value : ZMod 2)
    (hvalue : value ≠ 0) : value = 1 := by
  have hvalNe : value.val ≠ 0 := by
    exact (ZMod.val_eq_zero value).not.mpr hvalue
  have hvalLt : value.val < 2 := ZMod.val_lt value
  apply (ZMod.val_eq_one (by omega) value).mp
  omega

private theorem booleanPoint_eq_of_hammingSupport_eq {m : Nat}
    {left right : BooleanPoint m}
    (hsupport : hammingSupport left = hammingSupport right) :
    left = right := by
  funext coordinate
  by_cases hleft : left coordinate = 0
  · have hnot : coordinate ∉ hammingSupport left := by
      simp [hammingSupport, hleft]
    have hright : right coordinate = 0 := by
      have : coordinate ∉ hammingSupport right := by
        simpa [hsupport] using hnot
      simpa [hammingSupport] using this
    rw [hleft, hright]
  · have hmem : coordinate ∈ hammingSupport left := by
      simp [hammingSupport, hleft]
    have hright : right coordinate ≠ 0 := by
      have : coordinate ∈ hammingSupport right := by
        simpa [hsupport] using hmem
      simpa [hammingSupport] using this
    rw [binary_eq_one_of_ne_zero _ hleft,
      binary_eq_one_of_ne_zero _ hright]

private theorem monomialValue_eq_ite_support_subset {m r : Nat}
    (monomial : SquarefreeMonomial m r) (point : BooleanPoint m) :
    monomialValue monomial point =
      if monomial.1 ⊆ hammingSupport point then 1 else 0 := by
  classical
  by_cases hsubset : monomial.1 ⊆ hammingSupport point
  · rw [if_pos hsubset]
    unfold monomialValue
    apply Finset.prod_eq_one
    intro coordinate hcoordinate
    apply binary_eq_one_of_ne_zero
    have : coordinate ∈ hammingSupport point := hsubset hcoordinate
    simpa [hammingSupport] using this
  · rw [if_neg hsubset]
    have hmissing : ∃ coordinate ∈ monomial.1,
        coordinate ∉ hammingSupport point := by
      simpa only [Finset.not_subset] using hsubset
    obtain ⟨coordinate, hcoordinate, hmissing⟩ := hmissing
    have hzero : point coordinate = 0 := by
      simpa [hammingSupport] using hmissing
    unfold monomialValue
    exact Finset.prod_eq_zero hcoordinate hzero

private def lowMonomial {m w r : Nat} (hwr : w ≤ r)
    (point : LowPoint m w) : SquarefreeMonomial m r :=
  ⟨hammingSupport point.1, by
    change HammingWeight point.1 ≤ r
    exact point.2.trans hwr⟩

private def lowEvaluation {m w r : Nat} (hwr : w ≤ r) :
    Word (ZMod 2) (LowPoint m w) →ₗ[ZMod 2]
      Word (ZMod 2) (LowPoint m w) :=
  Fintype.linearCombination (ZMod 2) fun point =>
    restrictLow m w
      (evaluationLinearMap m r (basisPolynomial (lowMonomial hwr point)))

private theorem lowEvaluation_apply {m w r : Nat} (hwr : w ≤ r)
    (coefficients : Word (ZMod 2) (LowPoint m w))
    (point : LowPoint m w) :
    lowEvaluation hwr coefficients point =
      ∑ monomialPoint,
        coefficients monomialPoint *
          monomialValue (lowMonomial hwr monomialPoint) point.1 := by
  classical
  rw [lowEvaluation, Fintype.linearCombination_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, restrictLow_apply]
  apply Finset.sum_congr rfl
  intro monomialPoint _hpoint
  rw [evaluation_basisPolynomial]
  simp [smul_eq_mul]

private theorem lowEvaluation_injective {m w r : Nat} (hwr : w ≤ r) :
    Function.Injective (lowEvaluation (m := m) hwr) := by
  rw [injective_iff_map_eq_zero]
  intro coefficients hzero
  funext target
  have hcoeff :
      ∀ weight : Nat, ∀ point : LowPoint m w,
        pointWeight point.1 = weight → coefficients point = 0 := by
    intro weight
    induction weight using Nat.strong_induction_on with
    | h weight ih =>
        intro point hpointWeight
        have happly := congrFun hzero point
        rw [lowEvaluation_apply (m := m)] at happly
        have hsingle :
            (∑ monomialPoint,
              coefficients monomialPoint *
                monomialValue (lowMonomial hwr monomialPoint) point.1) =
              coefficients point := by
          rw [Fintype.sum_eq_single point]
          · rw [monomialValue_eq_ite_support_subset]
            simp [lowMonomial]
          · intro other hne
            by_cases hsubset :
                hammingSupport other.1 ⊆ hammingSupport point.1
            · have hsupportNe :
                  hammingSupport other.1 ≠ hammingSupport point.1 := by
                intro heq
                exact hne (Subtype.ext (booleanPoint_eq_of_hammingSupport_eq heq))
              have hstrict :
                  hammingSupport other.1 ⊂ hammingSupport point.1 :=
                (Finset.ssubset_iff_subset_ne).2 ⟨hsubset, hsupportNe⟩
              have hweightLt :
                  pointWeight other.1 < pointWeight point.1 := by
                exact Finset.card_lt_card hstrict
              have hother : coefficients other = 0 :=
                ih (pointWeight other.1)
                  (by simpa [hpointWeight] using hweightLt) other rfl
              simp [monomialValue_eq_ite_support_subset, lowMonomial,
                hsubset, hother]
            · simp [monomialValue_eq_ite_support_subset, lowMonomial,
                hsubset]
        rw [hsingle] at happly
        simpa using happly
  exact hcoeff (pointWeight target.1) target rfl

private noncomputable def lowEvaluationEquiv {m w r : Nat} (hwr : w ≤ r) :
    Word (ZMod 2) (LowPoint m w) ≃ₗ[ZMod 2]
      Word (ZMod 2) (LowPoint m w) := by
  have hinjective := lowEvaluation_injective (m := m) hwr
  have hsurjective : Function.Surjective (lowEvaluation (m := m) hwr) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinjective
  exact LinearEquiv.ofBijective (lowEvaluation (m := m) hwr)
    ⟨hinjective, hsurjective⟩

private def lowPolynomial {m w r : Nat} (hwr : w ≤ r) :
    Word (ZMod 2) (LowPoint m w) →ₗ[ZMod 2] ANFPolynomial m r :=
  Fintype.linearCombination (ZMod 2) fun point =>
    basisPolynomial (lowMonomial hwr point)

private theorem restrictLow_evaluation_lowPolynomial {m w r : Nat}
    (hwr : w ≤ r)
    (coefficients : Word (ZMod 2) (LowPoint m w)) :
    restrictLow m w
        (evaluationLinearMap m r (lowPolynomial hwr coefficients)) =
      lowEvaluation hwr coefficients := by
  classical
  ext point
  simp [lowPolynomial, lowEvaluation, Fintype.linearCombination_apply,
    Pi.smul_apply]

/-! ## Low-coordinate interpolation

The following map is an actual right inverse to `restrictLow` on the
degree-`r` Reed--Muller evaluation code.  It is deliberately stated with the
minimal degree condition, rather than the HH18 numerical package, since the
complementary-degree argument below needs the same construction independently
of the eventual CSS parameters.
-/

/-- Extend values on all Boolean points of weight at most `w` to a concrete
degree-`r` Reed--Muller word. -/
noncomputable def lowCoordinateExtension {w r m : Nat} (hwr : w ≤ r) :
    Word (ZMod 2) (LowPoint m w) →ₗ[ZMod 2]
      Word (ZMod 2) (BooleanPoint m) :=
  (evaluationLinearMap m r).comp
    ((lowPolynomial hwr).comp (lowEvaluationEquiv hwr).symm.toLinearMap)

/-- The low-coordinate extension is represented by a degree-`r`
Reed--Muller word. -/
theorem lowCoordinateExtension_mem_reedMullerCode {w r m : Nat}
    (hwr : w ≤ r)
    (logical : Word (ZMod 2) (LowPoint m w)) :
    lowCoordinateExtension hwr logical ∈
      (reedMullerCode r m).carrier := by
  rw [lowCoordinateExtension, LinearMap.comp_apply, LinearMap.comp_apply]
  exact evaluation_mem_reedMullerCode _

/-- Restricting the interpolating word recovers its prescribed low values. -/
theorem restrictLow_lowCoordinateExtension {w r m : Nat}
    (hwr : w ≤ r)
    (logical : Word (ZMod 2) (LowPoint m w)) :
    restrictLow m w (lowCoordinateExtension hwr logical) = logical := by
  rw [lowCoordinateExtension, LinearMap.comp_apply, LinearMap.comp_apply,
    restrictLow_evaluation_lowPolynomial]
  change
    lowEvaluationEquiv (m := m) hwr
        ((lowEvaluationEquiv (m := m) hwr).symm logical) = logical
  exact (lowEvaluationEquiv (m := m) hwr).apply_symm_apply logical

/-- The retained block of the systematic interpolation from low-weight points. -/
noncomputable def systematicKeptLift {w r m : Nat}
    (h : Admissible w r m) :
    Word (ZMod 2) (LowPoint m w) →ₗ[ZMod 2]
      Word (ZMod 2) (KeptPoint m w) := by
  have hwr : w ≤ r := by
    have := h.2.1
    omega
  exact (restrictKept m w).comp (lowCoordinateExtension hwr)

/-- Every retained systematic lift belongs to the punctured Reed--Muller code. -/
theorem systematicKeptLift_mem_puncturedReedMullerCode {w r m : Nat}
    (h : Admissible w r m)
    (logical : Word (ZMod 2) (LowPoint m w)) :
    systematicKeptLift h logical ∈
      (puncturedReedMullerCode r m w).carrier := by
  have hwr : w ≤ r := by
    have := h.2.1
    omega
  apply (mem_puncturedReedMullerCode _).2
  exact ⟨lowCoordinateExtension hwr logical,
    lowCoordinateExtension_mem_reedMullerCode hwr logical, rfl⟩

/-- Every punctured word splits into a systematic lift plus a shortened word. -/
theorem exists_systematicKeptLift_add_shortened {w r m : Nat}
    (h : Admissible w r m)
    {word : Word (ZMod 2) (KeptPoint m w)}
    (hword : word ∈ (puncturedReedMullerCode r m w).carrier) :
    ∃ logical shortened,
      shortened ∈ (shortenedReedMullerCode r m w).carrier ∧
        systematicKeptLift h logical + shortened = word := by
  rcases (mem_puncturedReedMullerCode word).1 hword with
    ⟨full, hfull, rfl⟩
  have hwr : w ≤ r := by
    have := h.2.1
    omega
  let logical := restrictLow m w full
  let shortenedFull := full - lowCoordinateExtension hwr logical
  let shortened := restrictKept m w shortenedFull
  have hshortenedFull :
      shortenedFull ∈ (reedMullerCode r m).carrier := by
    exact (reedMullerCode r m).carrier.sub_mem hfull
      (lowCoordinateExtension_mem_reedMullerCode hwr logical)
  have hshortenedLow : restrictLow m w shortenedFull = 0 := by
    simp [shortenedFull, logical, map_sub,
      restrictLow_lowCoordinateExtension]
  have hshortened :
      shortened ∈ (shortenedReedMullerCode r m w).carrier :=
    (mem_shortenedReedMullerCode shortened).2
      ⟨shortenedFull, hshortenedFull, hshortenedLow, rfl⟩
  refine ⟨logical, shortened, hshortened, ?_⟩
  change
    restrictKept m w (lowCoordinateExtension hwr logical) +
        restrictKept m w shortenedFull =
      restrictKept m w full
  simp [shortenedFull, map_sub]

/-- Removing coordinates on which the left word vanishes preserves its pairing. -/
theorem wordPairing_restrictKept_eq_of_restrictLow_eq_zero
    {m w : Nat} (left right : Word (ZMod 2) (BooleanPoint m))
    (hlow : restrictLow m w left = 0) :
    wordPairing (restrictKept m w left) (restrictKept m w right) =
      wordPairing left right := by
  classical
  have hlowPoint (point : LowPoint m w) : left point.1 = 0 := by
    have happly := congrFun hlow point
    simpa using happly
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype
      (fun point : BooleanPoint m => pointWeight point ≤ w)
      (fun point => left point * right point)
  let complementKept :
      {point : BooleanPoint m // ¬ pointWeight point ≤ w} ≃ KeptPoint m w :=
    { toFun := fun point => ⟨point.1, by omega⟩
      invFun := fun point => ⟨point.1, by omega⟩
      left_inv := fun point => Subtype.ext rfl
      right_inv := fun point => Subtype.ext rfl }
  change
    (∑ point : KeptPoint m w, left point.1 * right point.1) =
      ∑ point : BooleanPoint m, left point * right point
  have hlowSum :
      (∑ point : LowPoint m w, left point.1 * right point.1) = 0 := by
    apply Finset.sum_eq_zero
    intro point _hpoint
    rw [hlowPoint]
    simp
  have hcomplement :
      (∑ point : {point : BooleanPoint m // ¬ pointWeight point ≤ w},
        left point.1 * right point.1) =
        ∑ point : BooleanPoint m, left point * right point := by
    simpa only [LowPoint, hlowSum, zero_add] using hsplit
  have hequiv :
      (∑ point : {point : BooleanPoint m // ¬ pointWeight point ≤ w},
        left point.1 * right point.1) =
        ∑ point : KeptPoint m w, left point.1 * right point.1 := by
    exact Fintype.sum_equiv complementKept _ _ (fun _ => rfl)
  exact hequiv.symm.trans hcomplement

/-- Removing coordinates on which the left word vanishes on the retained block
preserves its low-coordinate pairing. -/
private theorem wordPairing_restrictLow_eq_of_restrictKept_eq_zero
    {m w : Nat} (left right : Word (ZMod 2) (BooleanPoint m))
    (hkept : restrictKept m w left = 0) :
    wordPairing (restrictLow m w left) (restrictLow m w right) =
      wordPairing left right := by
  classical
  have hkeptPoint
      (point : {point : BooleanPoint m // ¬ pointWeight point ≤ w}) :
      left point.1 = 0 := by
    have hpoint : w < pointWeight point.1 := by omega
    have happly := congrFun hkept ⟨point.1, hpoint⟩
    simpa using happly
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype
      (fun point : BooleanPoint m => pointWeight point ≤ w)
      (fun point => left point * right point)
  change
    (∑ point : LowPoint m w, left point.1 * right point.1) =
      ∑ point : BooleanPoint m, left point * right point
  have hkeptSum :
      (∑ point : {point : BooleanPoint m // ¬ pointWeight point ≤ w},
        left point.1 * right point.1) = 0 := by
    apply Finset.sum_eq_zero
    intro point _hpoint
    rw [hkeptPoint]
    simp
  calc
    (∑ point : LowPoint m w, left point.1 * right point.1) =
        (∑ point : LowPoint m w, left point.1 * right point.1) + 0 :=
      (add_zero _).symm
    _ = (∑ point : LowPoint m w, left point.1 * right point.1) +
        ∑ point : {point : BooleanPoint m // ¬ pointWeight point ≤ w},
          left point.1 * right point.1 := by rw [hkeptSum]
    _ = ∑ point : BooleanPoint m, left point * right point := by
      simpa only [LowPoint] using hsplit

/-- Extend a low-coordinate word by zero on every retained coordinate. -/
private def zeroExtendLow (m w : Nat) :
    Word (ZMod 2) (LowPoint m w) →ₗ[ZMod 2]
      Word (ZMod 2) (BooleanPoint m) where
  toFun word point :=
    if hpoint : pointWeight point ≤ w then word ⟨point, hpoint⟩ else 0
  map_add' := by
    intro left right
    funext point
    by_cases hpoint : pointWeight point ≤ w <;> simp [hpoint]
  map_smul' := by
    intro scalar word
    funext point
    by_cases hpoint : pointWeight point ≤ w <;> simp [hpoint]

@[simp]
private theorem restrictLow_zeroExtendLow {m w : Nat}
    (word : Word (ZMod 2) (LowPoint m w)) :
    restrictLow m w (zeroExtendLow m w word) = word := by
  ext point
  simp [zeroExtendLow, point.2]

@[simp]
private theorem restrictKept_zeroExtendLow {m w : Nat}
    (word : Word (ZMod 2) (LowPoint m w)) :
    restrictKept m w (zeroExtendLow m w word) = 0 := by
  ext point
  simp [zeroExtendLow, Nat.not_le_of_gt point.2]

@[simp]
private theorem restrictLow_zeroExtendKept {m w : Nat}
    (word : Word (ZMod 2) (KeptPoint m w)) :
    restrictLow m w (zeroExtendKept m w word) = 0 := by
  ext point
  simp [zeroExtendKept, Nat.not_lt_of_ge point.2]

private theorem wordPairing_zeroExtendLow {m w : Nat}
    (low : Word (ZMod 2) (LowPoint m w))
    (full : Word (ZMod 2) (BooleanPoint m)) :
    wordPairing (zeroExtendLow m w low) full =
      wordPairing low (restrictLow m w full) := by
  calc
    wordPairing (zeroExtendLow m w low) full =
        wordPairing (restrictLow m w (zeroExtendLow m w low))
          (restrictLow m w full) :=
      (wordPairing_restrictLow_eq_of_restrictKept_eq_zero
        (zeroExtendLow m w low) full (restrictKept_zeroExtendLow low)).symm
    _ = wordPairing low (restrictLow m w full) := by
      rw [restrictLow_zeroExtendLow]

private theorem wordPairing_zeroExtendKept {m w : Nat}
    (kept : Word (ZMod 2) (KeptPoint m w))
    (full : Word (ZMod 2) (BooleanPoint m)) :
    wordPairing (zeroExtendKept m w kept) full =
      wordPairing kept (restrictKept m w full) := by
  calc
    wordPairing (zeroExtendKept m w kept) full =
        wordPairing (restrictKept m w (zeroExtendKept m w kept))
          (restrictKept m w full) :=
      (wordPairing_restrictKept_eq_of_restrictLow_eq_zero
        (zeroExtendKept m w kept) full (restrictLow_zeroExtendKept kept)).symm
    _ = wordPairing kept (restrictKept m w full) := by
      rw [restrictKept_zeroExtendKept]

private theorem wordPairing_canonicalBasisWord_right
    {ι : Type} [Fintype ι] (word : Word (ZMod 2) ι) (point : ι) :
    wordPairing word (canonicalBasisWord point) = word point := by
  classical
  rw [wordPairing_apply, canonicalBasisWord, dotProduct_single_one]

/-- A low cut strictly below the complementary degree leaves no nonzero
degree-`r` Reed--Muller word supported solely on retained coordinates. -/
private theorem restrictKept_eq_zero_of_mem_reedMullerCode
    {w r m : Nat} (hnoKernel : w < m - r)
    {word : Word (ZMod 2) (BooleanPoint m)}
    (hword : word ∈ (reedMullerCode r m).carrier)
    (hkept : restrictKept m w word = 0) :
    word = 0 := by
  have hrm : r < m := by omega
  have hcomplement : w ≤ m - r - 1 := by omega
  have hwordDual : word ∈
      (reedMullerCode (m - r - 1) m).dual.carrier := by
    rw [reedMullerCode_dual_eq_complementary hrm]
    exact hword
  funext point
  by_cases hlow : pointWeight point ≤ w
  · let lowPoint : LowPoint m w := ⟨point, hlow⟩
    let probe := lowCoordinateExtension hcomplement
      (canonicalBasisWord lowPoint)
    have hprobe : probe ∈
        (reedMullerCode (m - r - 1) m).carrier :=
      lowCoordinateExtension_mem_reedMullerCode hcomplement _
    have hpair : wordPairing word probe = 0 :=
      (reedMullerCode (m - r - 1) m).orthogonal_of_mem_dual hwordDual hprobe
    have hlowPair :
        wordPairing (restrictLow m w word) (restrictLow m w probe) = 0 := by
      rw [wordPairing_restrictLow_eq_of_restrictKept_eq_zero word probe hkept]
      exact hpair
    have hprobeLow : restrictLow m w probe = canonicalBasisWord lowPoint :=
      restrictLow_lowCoordinateExtension hcomplement _
    rw [hprobeLow, wordPairing_canonicalBasisWord_right] at hlowPair
    simpa [lowPoint] using hlowPair
  · let keptPoint : KeptPoint m w := ⟨point, by omega⟩
    have happly := congrFun hkept keptPoint
    simpa [keptPoint] using happly

/-- The systematic retained lift represents a shortened word precisely when
its prescribed low block is zero. -/
theorem systematicKeptLift_mem_shortenedReedMullerCode_iff {w r m : Nat}
    (h : Admissible w r m)
    (logical : Word (ZMod 2) (LowPoint m w)) :
    systematicKeptLift h logical ∈
      (shortenedReedMullerCode r m w).carrier ↔ logical = 0 := by
  have hwr : w ≤ r := by
    have := h.2.1
    omega
  have hnoKernel : w < m - r := by
    have := h.2
    omega
  constructor
  · intro hmem
    rcases (mem_shortenedReedMullerCode _).1 hmem with
      ⟨full, hfull, hlow, hkept⟩
    have hsameKept : restrictKept m w full =
        restrictKept m w (lowCoordinateExtension hwr logical) := by
      simpa [systematicKeptLift, LinearMap.comp_apply] using hkept
    have hdifference : full - lowCoordinateExtension hwr logical ∈
        (reedMullerCode r m).carrier :=
      (reedMullerCode r m).carrier.sub_mem hfull
        (lowCoordinateExtension_mem_reedMullerCode hwr logical)
    have hdifferenceKept : restrictKept m w
        (full - lowCoordinateExtension hwr logical) = 0 := by
      rw [map_sub, hsameKept, sub_self]
    have hdifferenceZero := restrictKept_eq_zero_of_mem_reedMullerCode
      hnoKernel hdifference hdifferenceKept
    have hfullEq : full = lowCoordinateExtension hwr logical :=
      sub_eq_zero.mp hdifferenceZero
    calc
      logical = restrictLow m w (lowCoordinateExtension hwr logical) :=
        (restrictLow_lowCoordinateExtension hwr logical).symm
      _ = restrictLow m w full := by rw [hfullEq]
      _ = 0 := hlow
  · intro hlogical
    subst logical
    refine (mem_shortenedReedMullerCode _).2
      ⟨0, (reedMullerCode r m).carrier.zero_mem, ?_, ?_⟩
    · simp
    · simp [systematicKeptLift]

/-- The two shortened HH18 Reed--Muller codes satisfy CSS dual containment. -/
theorem shortenedReedMullerCode_dualContainment
    {w r m : Nat} (h : Admissible w r m) :
    (shortenedReedMullerCode (m - r - 1) m w).carrier ≤
      (shortenedReedMullerCode r m w).dual.carrier := by
  have hdegree : r + (m - r - 1) < m := by
    have htwo : 2 * r < m := h.2.2
    have hrm : r < m := by omega
    omega
  intro z hz
  refine ((shortenedReedMullerCode r m w).mem_dual z).2 ?_
  intro x hx
  rcases (mem_shortenedReedMullerCode z).1 hz with
    ⟨fullZ, hfullZ, hlowZ, hkeptZ⟩
  rcases (mem_shortenedReedMullerCode x).1 hx with
    ⟨fullX, hfullX, _hlowX, hkeptX⟩
  rw [← hkeptZ, ← hkeptX,
    wordPairing_restrictKept_eq_of_restrictLow_eq_zero fullZ fullX hlowZ]
  exact (reedMullerCode r m).orthogonal_of_mem_dual
    (reedMullerCode_le_dual_of_add_lt hdegree hfullZ) hfullX

/-- Shortening the complementary full Reed--Muller code is exactly dual to
puncturing the degree-`r` code when both complementary parameters are in
range. -/
theorem shortenedReedMullerCode_dual_eq_punctured_of_lt_of_le
    {w r m : Nat} (hrm : r < m) (hcomplement : w ≤ m - r - 1) :
    (shortenedReedMullerCode (m - r - 1) m w).dual.carrier =
      (puncturedReedMullerCode r m w).carrier := by
  apply le_antisymm
  · intro kept hkept
    let retainedExtension :=
      (restrictKept m w).comp (lowCoordinateExtension hcomplement)
    let lowFunctional := wordLinearMapTranspose retainedExtension kept
    let witness := zeroExtendKept m w kept - zeroExtendLow m w lowFunctional
    have hwitnessDual : witness ∈
        (reedMullerCode (m - r - 1) m).dual.carrier := by
      refine ((reedMullerCode (m - r - 1) m).mem_dual witness).2 ?_
      intro full hfull
      let residual := full - lowCoordinateExtension hcomplement
        (restrictLow m w full)
      have hresidual : residual ∈
          (reedMullerCode (m - r - 1) m).carrier := by
        dsimp [residual]
        exact (reedMullerCode (m - r - 1) m).carrier.sub_mem hfull
          (lowCoordinateExtension_mem_reedMullerCode hcomplement _)
      have hresidualLow : restrictLow m w residual = 0 := by
        simp [residual, map_sub, restrictLow_lowCoordinateExtension]
      have hresidualShortened : restrictKept m w residual ∈
          (shortenedReedMullerCode (m - r - 1) m w).carrier :=
        (mem_shortenedReedMullerCode _).2
          ⟨residual, hresidual, hresidualLow, rfl⟩
      have horthogonal : wordPairing kept (restrictKept m w residual) = 0 :=
        (shortenedReedMullerCode (m - r - 1) m w).orthogonal_of_mem_dual
          hkept hresidualShortened
      have htranspose : wordPairing lowFunctional (restrictLow m w full) =
          wordPairing kept
            (restrictKept m w
              (lowCoordinateExtension hcomplement (restrictLow m w full))) := by
        simpa [lowFunctional, retainedExtension, LinearMap.comp_apply] using
          (wordPairing_wordLinearMapTranspose
            ((restrictKept m w).comp (lowCoordinateExtension hcomplement)) kept
            (restrictLow m w full))
      calc
        wordPairing witness full =
            wordPairing (zeroExtendKept m w kept) full +
              wordPairing (zeroExtendLow m w lowFunctional) full := by
          simp [witness, sub_eq_add_neg, ZModModule.neg_eq_self,
            wordPairing.map_add]
        _ = wordPairing kept (restrictKept m w full) +
              wordPairing lowFunctional (restrictLow m w full) := by
          rw [wordPairing_zeroExtendKept, wordPairing_zeroExtendLow]
        _ = wordPairing kept (restrictKept m w full) +
              wordPairing kept
                (restrictKept m w
                  (lowCoordinateExtension hcomplement
                    (restrictLow m w full))) := by
          rw [htranspose]
        _ = wordPairing kept (restrictKept m w residual) := by
          simp [residual, sub_eq_add_neg, ZModModule.neg_eq_self]
        _ = 0 := horthogonal
    have hwitness : witness ∈ (reedMullerCode r m).carrier := by
      rw [← reedMullerCode_dual_eq_complementary hrm]
      exact hwitnessDual
    refine (mem_puncturedReedMullerCode _).2 ⟨witness, hwitness, ?_⟩
    simp [witness, map_sub]
  · intro kept hkept
    refine ((shortenedReedMullerCode (m - r - 1) m w).mem_dual kept).2 ?_
    intro shortened hshortened
    rcases (mem_puncturedReedMullerCode kept).1 hkept with
      ⟨fullKept, hfullKept, hrestrictKept⟩
    rcases (mem_shortenedReedMullerCode shortened).1 hshortened with
      ⟨fullShortened, hfullShortened, hrestrictLow, hrestrictShortened⟩
    have hfullKeptDual : fullKept ∈
        (reedMullerCode (m - r - 1) m).dual.carrier := by
      rw [reedMullerCode_dual_eq_complementary hrm]
      exact hfullKept
    calc
      wordPairing kept shortened =
          wordPairing (restrictKept m w fullKept)
            (restrictKept m w fullShortened) := by
        rw [hrestrictKept, hrestrictShortened]
      _ = wordPairing (restrictKept m w fullShortened)
            (restrictKept m w fullKept) := by
        simp only [wordPairing_apply]
        exact dotProduct_comm _ _
      _ = wordPairing fullShortened fullKept :=
        wordPairing_restrictKept_eq_of_restrictLow_eq_zero
          fullShortened fullKept hrestrictLow
      _ = wordPairing fullKept fullShortened := by
        simp only [wordPairing_apply]
        exact dotProduct_comm _ _
      _ = 0 :=
        (reedMullerCode (m - r - 1) m).orthogonal_of_mem_dual
          hfullKeptDual hfullShortened

/-- Under the punctured shortened Reed--Muller admissibility window, the dual
of the complementary shortened code is exactly the punctured low-degree code. -/
theorem shortenedReedMullerCode_dual_eq_punctured
    {w r m : Nat} (h : Admissible w r m) :
    (shortenedReedMullerCode (m - r - 1) m w).dual.carrier =
      (puncturedReedMullerCode r m w).carrier := by
  have hrm : r < m := by
    have := h.2.2
    omega
  have hcomplement : w ≤ m - r - 1 := by
    have := h.2
    omega
  exact shortenedReedMullerCode_dual_eq_punctured_of_lt_of_le hrm hcomplement

/-- Weight remaining after the HH18 coordinate restriction. -/
def restrictedWeight {m : Nat} (w : Nat)
    (word : Word (ZMod 2) (BooleanPoint m)) : Nat :=
  HammingWeight (restrictKept m w word)

@[simp]
theorem restrictedWeight_eq {m w : Nat}
    (word : Word (ZMod 2) (BooleanPoint m)) :
    restrictedWeight w word = HammingWeight (restrictKept m w word) :=
  rfl

/-- The set of weights retained by actual nonzero degree-`r` RM evaluations.
This is the finite object minimized in the HH18 restricted-support lemma; it
does not include any prospective minimum formula as data. -/
def restrictedNonzeroWeightSet (r m w : Nat) : Set Nat :=
  { weight | ∃ word : Word (ZMod 2) (BooleanPoint m),
      word ∈ (reedMullerCode r m).carrier ∧ word ≠ 0 ∧
        restrictedWeight w word = weight }

/-- The restricted nonzero Reed--Muller weight infimum.  The later induction
layer identifies this concrete minimum with the required binomial tail. -/
def restrictedMinimumWeight (r m w : Nat) : Nat :=
  sInf (restrictedNonzeroWeightSet r m w)

/-- The binomial tail appearing in the HH18 restricted-support formula. -/
def binomialTail (n w : Nat) : Nat :=
  ∑ i ∈ Finset.Icc (w + 1) n, Nat.choose n i

@[simp]
theorem mem_restrictedNonzeroWeightSet {r m w weight : Nat} :
    weight ∈ restrictedNonzeroWeightSet r m w ↔
      ∃ word : Word (ZMod 2) (BooleanPoint m),
        word ∈ (reedMullerCode r m).carrier ∧ word ≠ 0 ∧
          restrictedWeight w word = weight :=
  Iff.rfl

private def constantPolynomial (m r : Nat) : ANFPolynomial m r :=
  basisPolynomial ⟨∅, by simp⟩

private theorem evaluation_constantPolynomial_ne_zero (m r : Nat) :
    evaluationLinearMap m r (constantPolynomial m r) ≠ 0 := by
  intro hzero
  have hvalue := congrFun hzero (0 : BooleanPoint m)
  have hbasis :
      evaluationLinearMap m r (constantPolynomial m r) (0 : BooleanPoint m) = 1 := by
    rw [constantPolynomial, evaluation_basisPolynomial]
    simp [monomialValue]
  rw [hbasis] at hvalue
  exact one_ne_zero hvalue

/-- Actual RM evaluations provide a nonempty spectrum even when the coordinate
restriction itself has no retained support. -/
theorem restrictedNonzeroWeightSet_nonempty (r m w : Nat) :
    (restrictedNonzeroWeightSet r m w).Nonempty := by
  let word := evaluationLinearMap m r (constantPolynomial m r)
  refine ⟨restrictedWeight w word, word, ?_, ?_, rfl⟩
  · exact evaluation_mem_reedMullerCode _
  · simpa [word] using evaluation_constantPolynomial_ne_zero m r

/-- Every actual nonzero RM word contributes its restricted weight to the
minimum spectrum. -/
theorem restrictedWeight_mem_restrictedNonzeroWeightSet
    {r m w : Nat} {word : Word (ZMod 2) (BooleanPoint m)}
    (hword : word ∈ (reedMullerCode r m).carrier) (hnonzero : word ≠ 0) :
    restrictedWeight w word ∈ restrictedNonzeroWeightSet r m w :=
  ⟨word, hword, hnonzero, rfl⟩

/-- The concrete restricted minimum is no larger than the restricted weight of
each actual nonzero Reed--Muller evaluation. -/
theorem restrictedMinimumWeight_le_restrictedWeight
    {r m w : Nat} {word : Word (ZMod 2) (BooleanPoint m)}
    (hword : word ∈ (reedMullerCode r m).carrier) (hnonzero : word ≠ 0) :
    restrictedMinimumWeight r m w ≤ restrictedWeight w word := by
  exact csInf_le' (restrictedWeight_mem_restrictedNonzeroWeightSet hword hnonzero)

private def vanishingSubsetMonomial {r m : Nat}
    (support : Finset (Fin m)) (hcard : support.card ≤ r)
    (subset : support.powerset) : SquarefreeMonomial m r :=
  ⟨subset.1,
    (Finset.card_le_card (Finset.mem_powerset.mp subset.2)).trans hcard⟩

/-- The honest ANF expansion of `∏ i ∈ support, (1 + xᵢ)`. -/
private noncomputable def vanishingPolynomial {r m : Nat}
    (support : Finset (Fin m)) (hcard : support.card ≤ r) :
    ANFPolynomial m r :=
  ∑ subset : support.powerset,
    basisPolynomial (vanishingSubsetMonomial support hcard subset)

private theorem evaluation_vanishingPolynomial {r m : Nat}
    (support : Finset (Fin m)) (hcard : support.card ≤ r)
    (point : BooleanPoint m) :
    evaluationLinearMap m r (vanishingPolynomial support hcard) point =
      ∏ coordinate ∈ support, (1 + point coordinate) := by
  simp only [vanishingPolynomial, map_sum, Finset.sum_apply,
    evaluation_basisPolynomial]
  change (∑ subset : support.powerset,
      ∏ coordinate ∈ subset.1, point coordinate) = _
  rw [Finset.prod_one_add, Finset.univ_eq_attach]
  exact support.powerset.sum_attach
    (fun subset => ∏ coordinate ∈ subset, point coordinate)

private theorem one_add_binary_ne_zero_iff (value : ZMod 2) :
    1 + value ≠ 0 ↔ value = 0 := by
  constructor
  · intro hvalue
    by_contra hzero
    have hone : value = 1 := binary_eq_one_of_ne_zero value hzero
    rw [hone] at hvalue
    exact hvalue (ZModModule.add_self 1)
  · rintro rfl
    norm_num

private theorem evaluation_vanishingPolynomial_ne_zero_iff {r m : Nat}
    (support : Finset (Fin m)) (hcard : support.card ≤ r)
    (point : BooleanPoint m) :
    evaluationLinearMap m r (vanishingPolynomial support hcard) point ≠ 0 ↔
      Disjoint support (hammingSupport point) := by
  rw [evaluation_vanishingPolynomial, Finset.prod_ne_zero_iff]
  simp [one_add_binary_ne_zero_iff, Finset.disjoint_left, hammingSupport]

private def supportIndicatorPoint {m : Nat}
    (support : Finset (Fin m)) : BooleanPoint m :=
  fun coordinate => if coordinate ∈ support then 1 else 0

@[simp]
private theorem hammingSupport_supportIndicatorPoint {m : Nat}
    (support : Finset (Fin m)) :
    hammingSupport (supportIndicatorPoint support) = support := by
  ext coordinate
  simp [hammingSupport, supportIndicatorPoint]

@[simp]
private theorem pointWeight_supportIndicatorPoint {m : Nat}
    (support : Finset (Fin m)) :
    pointWeight (supportIndicatorPoint support) = support.card := by
  simp [pointWeight]

private theorem card_filter_powerset_card_gt {α : Type*}
    [Fintype α] [DecidableEq α] (support : Finset α) (w : Nat) :
    ((support.powerset).filter fun subset => w < subset.card).card =
      binomialTail support.card w := by
  classical
  unfold binomialTail
  calc
    ((support.powerset).filter fun subset => w < subset.card).card =
        ((support.powerset).filter fun subset =>
          subset.card ∈ Finset.Icc (w + 1) support.card).card := by
      congr 1
      ext subset
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_Icc]
      constructor
      · rintro ⟨hsubset, hweight⟩
        exact ⟨hsubset, by omega, Finset.card_le_card hsubset⟩
      · rintro ⟨hsubset, hlower, _hupper⟩
        exact ⟨hsubset, by omega⟩
    _ = ∑ i ∈ Finset.Icc (w + 1) support.card,
        ((support.powerset).filter fun subset => subset.card = i).card := by
      symm
      exact Finset.sum_card_fiberwise_eq_card_filter
        support.powerset (Finset.Icc (w + 1) support.card) Finset.card
    _ = ∑ i ∈ Finset.Icc (w + 1) support.card,
        Nat.choose support.card i := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← Finset.powersetCard_eq_filter, Finset.card_powersetCard]

private theorem restrictedWeight_evaluation_vanishingPolynomial
    {r m w : Nat} (support : Finset (Fin m))
    (hcard : support.card ≤ r) :
    restrictedWeight w
        (evaluationLinearMap m r (vanishingPolynomial support hcard)) =
      binomialTail supportᶜ.card w := by
  classical
  let word := evaluationLinearMap m r (vanishingPolynomial support hcard)
  let active := hammingSupport (restrictKept m w word)
  let target := supportᶜ.powerset.filter fun subset => w < subset.card
  have hcardEq : active.card = target.card := by
    apply Finset.card_bij (s := active) (t := target)
        (fun point _hpoint => hammingSupport point.1)
    · intro point hpoint
      have hvalue : word point.1 ≠ 0 := by
        exact (Finset.mem_filter.mp hpoint).2
      have hdisjoint : Disjoint support (hammingSupport point.1) := by
        exact (evaluation_vanishingPolynomial_ne_zero_iff
          support hcard point.1).mp (by simpa [word] using hvalue)
      have hsubset : hammingSupport point.1 ⊆ supportᶜ := by
        intro coordinate hcoordinate
        rw [Finset.mem_compl]
        intro hsupport
        exact (Finset.disjoint_left.mp hdisjoint) hsupport hcoordinate
      have hweight : w < (hammingSupport point.1).card := by
        simpa [pointWeight] using point.2
      simp [target, hsubset, hweight]
    · intro left _hleft right _hright heq
      apply Subtype.ext
      exact booleanPoint_eq_of_hammingSupport_eq heq
    · intro subset hsubset
      have htarget : subset ⊆ supportᶜ ∧ w < subset.card := by
        simpa [target] using hsubset
      let point : KeptPoint m w :=
        ⟨supportIndicatorPoint subset, by simpa using htarget.2⟩
      have hdisjoint : Disjoint support (hammingSupport point.1) := by
        rw [show point.1 = supportIndicatorPoint subset by rfl,
          hammingSupport_supportIndicatorPoint]
        exact Finset.disjoint_left.mpr fun coordinate hsupport hcoordinate =>
          (Finset.mem_compl.mp (htarget.1 hcoordinate)) hsupport
      have hvalue : word point.1 ≠ 0 := by
        simpa [word] using
          (evaluation_vanishingPolynomial_ne_zero_iff
            support hcard point.1).mpr hdisjoint
      have hpoint : point ∈ active := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvalue⟩
      refine ⟨point, hpoint, ?_⟩
      simp [point]
  calc
    restrictedWeight w word = active.card := by rfl
    _ = target.card := hcardEq
    _ = binomialTail supportᶜ.card w :=
      card_filter_powerset_card_gt supportᶜ w

private noncomputable def witnessSupport {r m : Nat} (hrm : r ≤ m) :
    Finset (Fin m) :=
  Classical.choose
    (Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin m)))
      (n := r) (by simpa using hrm))

@[simp]
private theorem witnessSupport_card {r m : Nat} (hrm : r ≤ m) :
    (witnessSupport hrm).card = r :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin m)))
      (n := r) (by simpa using hrm))).2

private theorem exists_reedMullerCodeword_restrictedWeight_eq_binomialTail_and_low_ne_zero
    {m r w : Nat} (hrm : r ≤ m) :
    ∃ word : Word (ZMod 2) (BooleanPoint m),
      word ∈ (reedMullerCode r m).carrier ∧
        restrictLow m w word ≠ 0 ∧
        restrictedWeight w word = binomialTail (m - r) w := by
  let support := witnessSupport hrm
  have hsupport : support.card ≤ r := by simp [support]
  let polynomial := vanishingPolynomial support hsupport
  let word := evaluationLinearMap m r polynomial
  refine ⟨word, ?_, ?_, ?_⟩
  · exact evaluation_mem_reedMullerCode polynomial
  · let origin : LowPoint m w := ⟨0, by
      simp [pointWeight, HammingWeight]⟩
    have hvalue : word origin.1 ≠ 0 := by
      simpa [word, polynomial] using
        (evaluation_vanishingPolynomial_ne_zero_iff
          support hsupport origin.1).mpr (by simp [origin])
    intro hlow
    exact hvalue (by simpa using congrFun hlow origin)
  · calc
      restrictedWeight w word = binomialTail supportᶜ.card w :=
        restrictedWeight_evaluation_vanishingPolynomial support hsupport
      _ = binomialTail (m - r) w := by
        rw [Finset.card_compl, Fintype.card_fin, witnessSupport_card]

/-- A concrete degree-`r` ANF evaluation realizes the HH18 binomial-tail
restricted weight.  This is the upper-witness half of the later exact minimum
theorem, not a minimum-distance assumption. -/
theorem exists_reedMullerCodeword_restrictedWeight_eq_binomialTail
    {m r w : Nat} (hrm : r ≤ m) :
    ∃ word : Word (ZMod 2) (BooleanPoint m),
      word ∈ (reedMullerCode r m).carrier ∧ word ≠ 0 ∧
        restrictedWeight w word = binomialTail (m - r) w := by
  obtain ⟨word, hword, hlow, hweight⟩ :=
    exists_reedMullerCodeword_restrictedWeight_eq_binomialTail_and_low_ne_zero
      (w := w) hrm
  refine ⟨word, hword, ?_, hweight⟩
  intro hzero
  apply hlow
  simp [hzero]

/-- The actual restricted Reed--Muller minimum is at most the HH18 binomial
tail, witnessed by the concrete ANF word above. -/
theorem restrictedMinimumWeight_le_binomialTail
    {m r w : Nat} (hrm : r ≤ m) :
    restrictedMinimumWeight r m w ≤ binomialTail (m - r) w := by
  obtain ⟨word, hword, hnonzero, hweight⟩ :=
    exists_reedMullerCodeword_restrictedWeight_eq_binomialTail (w := w) hrm
  calc
    restrictedMinimumWeight r m w ≤ restrictedWeight w word :=
      restrictedMinimumWeight_le_restrictedWeight hword hnonzero
    _ = binomialTail (m - r) w := hweight

private def tailSupport {m : Nat} (support : Finset (Fin (m + 1))) :
    Finset (Fin m) :=
  support.preimage Fin.succ
    (Set.injOn_of_injective (Fin.succ_injective m))

@[simp] private theorem mem_tailSupport {m : Nat}
    {support : Finset (Fin (m + 1))} {coordinate : Fin m} :
    coordinate ∈ tailSupport support ↔ coordinate.succ ∈ support := by
  simp [tailSupport]

private def liftTailSupport {m : Nat} (support : Finset (Fin m)) :
    Finset (Fin (m + 1)) :=
  support.map (Fin.succEmb m)

@[simp] private theorem mem_liftTailSupport {m : Nat}
    {support : Finset (Fin m)} {coordinate : Fin m} :
    coordinate.succ ∈ liftTailSupport support ↔ coordinate ∈ support := by
  simp [liftTailSupport]

@[simp] private theorem zero_not_mem_liftTailSupport {m : Nat}
    (support : Finset (Fin m)) :
    (0 : Fin (m + 1)) ∉ liftTailSupport support := by
  simp [liftTailSupport]

@[simp] private theorem tailSupport_liftTailSupport {m : Nat}
    (support : Finset (Fin m)) :
    tailSupport (liftTailSupport support) = support := by
  ext coordinate
  simp

@[simp] private theorem tailSupport_insert_zero_liftTailSupport {m : Nat}
    (support : Finset (Fin m)) :
    tailSupport (insert 0 (liftTailSupport support)) = support := by
  ext coordinate
  simp

private theorem liftTailSupport_tailSupport_of_zero_not_mem {m : Nat}
    (support : Finset (Fin (m + 1)))
    (hzero : (0 : Fin (m + 1)) ∉ support) :
    liftTailSupport (tailSupport support) = support := by
  ext coordinate
  refine Fin.cases ?_ (fun tail => ?_) coordinate
  · simp [hzero]
  · simp

private theorem insert_zero_liftTailSupport_tailSupport_of_mem {m : Nat}
    (support : Finset (Fin (m + 1)))
    (hzero : (0 : Fin (m + 1)) ∈ support) :
    insert 0 (liftTailSupport (tailSupport support)) = support := by
  ext coordinate
  refine Fin.cases ?_ (fun tail => ?_) coordinate
  · simp [hzero]
  · simp

@[simp] private theorem card_liftTailSupport {m : Nat}
    (support : Finset (Fin m)) :
    (liftTailSupport support).card = support.card := by
  simp [liftTailSupport]

private def liftMonomialWithoutZero {m r : Nat}
    (monomial : SquarefreeMonomial m r) : SquarefreeMonomial (m + 1) r :=
  ⟨liftTailSupport monomial.1, by simpa using monomial.2⟩

private def liftMonomialWithZero {m r : Nat}
    (monomial : SquarefreeMonomial m r) : SquarefreeMonomial (m + 1) (r + 1) :=
  ⟨insert 0 (liftTailSupport monomial.1), by
    rw [Finset.card_insert_of_notMem (zero_not_mem_liftTailSupport _)]
    simp only [card_liftTailSupport]
    omega⟩

private def squarefreeMonomialSuccEquiv (m r : Nat) :
    SquarefreeMonomial (m + 1) (r + 1) ≃
      Sum (SquarefreeMonomial m (r + 1)) (SquarefreeMonomial m r) where
  toFun monomial :=
    if hzero : (0 : Fin (m + 1)) ∈ monomial.1 then
      Sum.inr ⟨tailSupport monomial.1, by
        have hreconstruct :=
          insert_zero_liftTailSupport_tailSupport_of_mem monomial.1 hzero
        have hcard : (tailSupport monomial.1).card + 1 = monomial.1.card := by
          calc
            (tailSupport monomial.1).card + 1 =
                (insert 0 (liftTailSupport (tailSupport monomial.1))).card := by
              rw [Finset.card_insert_of_notMem
                (zero_not_mem_liftTailSupport _), card_liftTailSupport]
            _ = monomial.1.card := congrArg Finset.card hreconstruct
        omega⟩
    else
      Sum.inl ⟨tailSupport monomial.1, by
        have hreconstruct :=
          liftTailSupport_tailSupport_of_zero_not_mem monomial.1 hzero
        have hcard := congrArg Finset.card hreconstruct
        rw [card_liftTailSupport] at hcard
        rw [hcard]
        exact monomial.2⟩
  invFun split :=
    match split with
    | Sum.inl monomial => liftMonomialWithoutZero monomial
    | Sum.inr monomial => liftMonomialWithZero monomial
  left_inv monomial := by
    by_cases hzero : (0 : Fin (m + 1)) ∈ monomial.1
    · simp only [hzero, ↓reduceDIte]
      apply Subtype.ext
      exact insert_zero_liftTailSupport_tailSupport_of_mem monomial.1 hzero
    · simp only [hzero, ↓reduceDIte]
      apply Subtype.ext
      exact liftTailSupport_tailSupport_of_zero_not_mem monomial.1 hzero
  right_inv split := by
    cases split with
    | inl monomial =>
        change (if _ : (0 : Fin (m + 1)) ∈ liftTailSupport monomial.1 then _ else _) = _
        rw [dif_neg (zero_not_mem_liftTailSupport _)]
        apply congrArg Sum.inl
        apply Subtype.ext
        exact tailSupport_liftTailSupport monomial.1
    | inr monomial =>
        change (if _ : (0 : Fin (m + 1)) ∈
            insert 0 (liftTailSupport monomial.1) then _ else _) = _
        rw [dif_pos (Finset.mem_insert_self 0 _)]
        apply congrArg Sum.inr
        apply Subtype.ext
        exact tailSupport_insert_zero_liftTailSupport monomial.1


@[simp] private theorem monomialValue_liftMonomialWithoutZero
    {m r : Nat} (monomial : SquarefreeMonomial m r)
    (bit : ZMod 2) (point : BooleanPoint m) :
    monomialValue (liftMonomialWithoutZero monomial) (Fin.cons bit point) =
      monomialValue monomial point := by
  classical
  simp [monomialValue, liftMonomialWithoutZero, liftTailSupport]

@[simp] private theorem monomialValue_liftMonomialWithZero
    {m r : Nat} (monomial : SquarefreeMonomial m r)
    (bit : ZMod 2) (point : BooleanPoint m) :
    monomialValue (liftMonomialWithZero monomial) (Fin.cons bit point) =
      bit * monomialValue monomial point := by
  classical
  simp [monomialValue, liftMonomialWithZero, liftTailSupport]

private def zeroSlicePolynomial {m r : Nat}
    (polynomial : ANFPolynomial (m + 1) (r + 1)) :
    ANFPolynomial m (r + 1) :=
  fun monomial => polynomial (liftMonomialWithoutZero monomial)

private def derivativePolynomial {m r : Nat}
    (polynomial : ANFPolynomial (m + 1) (r + 1)) :
    ANFPolynomial m r :=
  fun monomial => polynomial (liftMonomialWithZero monomial)

private theorem evaluation_succ_split {m r : Nat}
    (polynomial : ANFPolynomial (m + 1) (r + 1))
    (bit : ZMod 2) (point : BooleanPoint m) :
    evaluationLinearMap (m + 1) (r + 1) polynomial (Fin.cons bit point) =
      evaluationLinearMap m (r + 1) (zeroSlicePolynomial polynomial) point +
        bit * evaluationLinearMap m r (derivativePolynomial polynomial) point := by
  classical
  rw [evaluationLinearMap_apply, evaluationLinearMap_apply,
    evaluationLinearMap_apply]
  let e := squarefreeMonomialSuccEquiv m r
  calc
    (∑ monomial,
        polynomial monomial * monomialValue monomial (Fin.cons bit point)) =
        ∑ split : Sum (SquarefreeMonomial m (r + 1))
            (SquarefreeMonomial m r),
          polynomial (e.symm split) *
            monomialValue (e.symm split) (Fin.cons bit point) := by
      symm
      exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
    _ = (∑ monomial : SquarefreeMonomial m (r + 1),
          polynomial (liftMonomialWithoutZero monomial) *
            monomialValue monomial point) +
        ∑ monomial : SquarefreeMonomial m r,
          polynomial (liftMonomialWithZero monomial) *
            (bit * monomialValue monomial point) := by
      simp [e, squarefreeMonomialSuccEquiv]
    _ = (∑ monomial : SquarefreeMonomial m (r + 1),
          zeroSlicePolynomial polynomial monomial * monomialValue monomial point) +
        bit * ∑ monomial : SquarefreeMonomial m r,
          derivativePolynomial polynomial monomial * monomialValue monomial point := by
      rw [Finset.mul_sum]
      apply congrArg₂ (· + ·)
      · rfl
      · apply Finset.sum_congr rfl
        intro monomial _hmonomial
        simp [derivativePolynomial, mul_left_comm]


private def thresholdWeight {m : Nat} (threshold : Nat)
    (word : Word (ZMod 2) (BooleanPoint m)) : Nat :=
  (Finset.univ.filter fun point =>
    threshold ≤ pointWeight point ∧ word point ≠ 0).card

private def binomialFrom (n threshold : Nat) : Nat :=
  ∑ i ∈ Finset.Icc threshold n, Nat.choose n i

private theorem thresholdWeight_eq_sum {m threshold : Nat}
    (word : Word (ZMod 2) (BooleanPoint m)) :
    thresholdWeight threshold word =
      ∑ point, if threshold ≤ pointWeight point ∧ word point ≠ 0 then 1 else 0 := by
  rw [thresholdWeight, Finset.card_filter]

@[simp] private theorem hammingSupport_cons_zero {m : Nat}
    (point : BooleanPoint m) :
    hammingSupport (Fin.cons (0 : ZMod 2) point) =
      liftTailSupport (hammingSupport point) := by
  ext coordinate
  refine Fin.cases ?_ (fun tail => ?_) coordinate
  · simp [hammingSupport]
  · simp [hammingSupport]

@[simp] private theorem hammingSupport_cons_one {m : Nat}
    (point : BooleanPoint m) :
    hammingSupport (Fin.cons (1 : ZMod 2) point) =
      insert 0 (liftTailSupport (hammingSupport point)) := by
  ext coordinate
  refine Fin.cases ?_ (fun tail => ?_) coordinate
  · simp [hammingSupport]
  · simp [hammingSupport]

@[simp] private theorem pointWeight_cons_zero {m : Nat}
    (point : BooleanPoint m) :
    pointWeight (Fin.cons (0 : ZMod 2) point) = pointWeight point := by
  simp [pointWeight, HammingWeight]

@[simp] private theorem pointWeight_cons_one {m : Nat}
    (point : BooleanPoint m) :
    pointWeight (Fin.cons (1 : ZMod 2) point) = pointWeight point + 1 := by
  rw [pointWeight, HammingWeight, hammingSupport_cons_one,
    Finset.card_insert_of_notMem (zero_not_mem_liftTailSupport _),
    card_liftTailSupport]
  rfl

private def booleanPointSuccEquiv (m : Nat) :
    BooleanPoint (m + 1) ≃ ZMod 2 × BooleanPoint m where
  toFun point := (point 0, Fin.tail point)
  invFun split := Fin.cons split.1 split.2
  left_inv point := Fin.cons_self_tail point
  right_inv split := by
    cases split
    simp

private theorem sum_binary (f : ZMod 2 → Nat) :
    (∑ bit, f bit) = f 0 + f 1 := by
  calc
    (∑ bit : ZMod 2, f bit) =
        ∑ index : Fin 2, f (ZMod.finEquiv 2 index) := by
      exact Fintype.sum_equiv (ZMod.finEquiv 2).toEquiv.symm _ _ (fun _ => rfl)
    _ = f 0 + f 1 := by
      rw [Fin.sum_univ_two]
      norm_num

private theorem thresholdWeight_succ_split {m threshold : Nat}
    (word : Word (ZMod 2) (BooleanPoint (m + 1))) :
    thresholdWeight threshold word =
      thresholdWeight threshold (fun point => word (Fin.cons 0 point)) +
        thresholdWeight (threshold - 1)
          (fun point => word (Fin.cons 1 point)) := by
  rw [thresholdWeight_eq_sum, thresholdWeight_eq_sum,
    thresholdWeight_eq_sum]
  calc
    (∑ point : BooleanPoint (m + 1),
        if threshold ≤ pointWeight point ∧ word point ≠ 0 then 1 else 0) =
        ∑ split : ZMod 2 × BooleanPoint m,
          if threshold ≤ pointWeight (Fin.cons split.1 split.2) ∧
              word (Fin.cons split.1 split.2) ≠ 0 then 1 else 0 := by
      exact Fintype.sum_equiv (booleanPointSuccEquiv m) _ _ (fun point => by
        simp [booleanPointSuccEquiv, Fin.cons_self_tail])
    _ = ∑ bit : ZMod 2, ∑ point : BooleanPoint m,
          if threshold ≤ pointWeight (Fin.cons bit point) ∧
              word (Fin.cons bit point) ≠ 0 then 1 else 0 := by
      rw [Fintype.sum_prod_type]
    _ = (∑ point : BooleanPoint m,
          if threshold ≤ pointWeight (Fin.cons 0 point) ∧
              word (Fin.cons 0 point) ≠ 0 then 1 else 0) +
        ∑ point : BooleanPoint m,
          if threshold ≤ pointWeight (Fin.cons 1 point) ∧
              word (Fin.cons 1 point) ≠ 0 then 1 else 0 := by
      rw [sum_binary]
    _ = (∑ point : BooleanPoint m,
          if threshold ≤ pointWeight point ∧
              word (Fin.cons 0 point) ≠ 0 then 1 else 0) +
        ∑ point : BooleanPoint m,
          if threshold - 1 ≤ pointWeight point ∧
              word (Fin.cons 1 point) ≠ 0 then 1 else 0 := by
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro point _hpoint
        simp only [pointWeight_cons_zero]
      · apply Finset.sum_congr rfl
        intro point _hpoint
        congr 1
        apply propext
        constructor <;> rintro ⟨hweight, hword⟩ <;> refine ⟨?_, hword⟩ <;>
          simp only [pointWeight_cons_one] at hweight ⊢ <;> omega


private theorem thresholdWeight_add_le {m threshold : Nat}
    (left right : Word (ZMod 2) (BooleanPoint m)) :
    thresholdWeight threshold (left + right) ≤
      thresholdWeight threshold left + thresholdWeight threshold right := by
  let combined := Finset.univ.filter fun point : BooleanPoint m =>
    threshold ≤ pointWeight point ∧ (left + right) point ≠ 0
  let leftSupport := Finset.univ.filter fun point : BooleanPoint m =>
    threshold ≤ pointWeight point ∧ left point ≠ 0
  let rightSupport := Finset.univ.filter fun point : BooleanPoint m =>
    threshold ≤ pointWeight point ∧ right point ≠ 0
  have hsubset : combined ⊆ leftSupport ∪ rightSupport := by
    intro point hpoint
    have hdata : threshold ≤ pointWeight point ∧
        left point + right point ≠ 0 := by
      simpa [combined] using hpoint
    by_cases hleft : left point = 0
    · have hright : right point ≠ 0 := by
        intro hzero
        exact hdata.2 (by simp [hleft, hzero])
      simp [rightSupport, hdata.1, hright]
    · simp [leftSupport, hdata.1, hleft]
  calc
    thresholdWeight threshold (left + right) = combined.card := rfl
    _ ≤ (leftSupport ∪ rightSupport).card := Finset.card_le_card hsubset
    _ ≤ leftSupport.card + rightSupport.card := Finset.card_union_le _ _
    _ = thresholdWeight threshold left + thresholdWeight threshold right := rfl

private theorem thresholdWeight_antitone {m lower upper : Nat}
    (hthreshold : lower ≤ upper)
    (word : Word (ZMod 2) (BooleanPoint m)) :
    thresholdWeight upper word ≤ thresholdWeight lower word := by
  apply Finset.card_le_card
  intro point hpoint
  have hdata : upper ≤ pointWeight point ∧ word point ≠ 0 := by
    simpa [thresholdWeight] using hpoint
  simpa [thresholdWeight] using ⟨hthreshold.trans hdata.1, hdata.2⟩

private def supportIndicatorPoint' {m : Nat}
    (support : Finset (Fin m)) : BooleanPoint m :=
  fun coordinate => if coordinate ∈ support then 1 else 0

@[simp] private theorem hammingSupport_supportIndicatorPoint' {m : Nat}
    (support : Finset (Fin m)) :
    hammingSupport (supportIndicatorPoint' support) = support := by
  ext coordinate
  simp [hammingSupport, supportIndicatorPoint']

private theorem booleanPoint_eq_of_hammingSupport_eq' {m : Nat}
    {left right : BooleanPoint m}
    (hsupport : hammingSupport left = hammingSupport right) :
    left = right := by
  funext coordinate
  by_cases hleft : left coordinate = 0
  · have hnot : coordinate ∉ hammingSupport left := by
      simp [hammingSupport, hleft]
    have hright : right coordinate = 0 := by
      have : coordinate ∉ hammingSupport right := by
        simpa [hsupport] using hnot
      simpa [hammingSupport] using this
    rw [hleft, hright]
  · have hmem : coordinate ∈ hammingSupport left := by
      simp [hammingSupport, hleft]
    have hright : right coordinate ≠ 0 := by
      have : coordinate ∈ hammingSupport right := by
        simpa [hsupport] using hmem
      simpa [hammingSupport] using this
    have honeLeft : left coordinate = 1 := by
      have hvalNe : (left coordinate).val ≠ 0 :=
        (ZMod.val_eq_zero (left coordinate)).not.mpr hleft
      apply (ZMod.val_eq_one (by omega) (left coordinate)).mp
      have := ZMod.val_lt (left coordinate)
      omega
    have honeRight : right coordinate = 1 := by
      have hvalNe : (right coordinate).val ≠ 0 :=
        (ZMod.val_eq_zero (right coordinate)).not.mpr hright
      apply (ZMod.val_eq_one (by omega) (right coordinate)).mp
      have := ZMod.val_lt (right coordinate)
      omega
    rw [honeLeft, honeRight]

private theorem card_booleanPoints_atLeast (m threshold : Nat) :
    ((Finset.univ : Finset (BooleanPoint m)).filter fun point =>
      threshold ≤ pointWeight point).card = binomialFrom m threshold := by
  classical
  let active := (Finset.univ : Finset (BooleanPoint m)).filter fun point =>
    threshold ≤ pointWeight point
  let target := ((Finset.univ : Finset (Fin m)).powerset).filter fun support =>
    threshold ≤ support.card
  have hcard : active.card = target.card := by
    apply Finset.card_bij (s := active) (t := target)
        (fun point _hpoint => hammingSupport point)
    · intro point hpoint
      have hweight : threshold ≤ (hammingSupport point).card := by
        exact (Finset.mem_filter.mp hpoint).2
      simp [target, hweight]
    · intro left _hleft right _hright heq
      exact booleanPoint_eq_of_hammingSupport_eq' heq
    · intro support hsupport
      have htarget : support ⊆ (Finset.univ : Finset (Fin m)) ∧
          threshold ≤ support.card := by
        simpa [target] using hsupport
      let point := supportIndicatorPoint' support
      have hpoint : point ∈ active := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa [point, pointWeight, HammingWeight] using htarget.2
      refine ⟨point, hpoint, ?_⟩
      simp [point]
  calc
    ((Finset.univ : Finset (BooleanPoint m)).filter fun point =>
        threshold ≤ pointWeight point).card = active.card := rfl
    _ = target.card := hcard
    _ = (((Finset.univ : Finset (Fin m)).powerset).filter fun support =>
        support.card ∈ Finset.Icc threshold m).card := by
      congr 1
      ext support
      simp only [target, Finset.mem_filter, Finset.mem_powerset,
        Finset.mem_Icc]
      constructor
      · rintro ⟨hsubset, hlower⟩
        exact ⟨hsubset, hlower, by simpa using Finset.card_le_univ support⟩
      · rintro ⟨hsubset, hlower, _hupper⟩
        exact ⟨hsubset, hlower⟩
    _ = ∑ i ∈ Finset.Icc threshold m,
        (((Finset.univ : Finset (Fin m)).powerset).filter fun support =>
          support.card = i).card := by
      symm
      exact Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin m)).powerset
        (Finset.Icc threshold m) Finset.card
    _ = ∑ i ∈ Finset.Icc threshold m, Nat.choose m i := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← Finset.powersetCard_eq_filter, Finset.card_powersetCard]
      simp
    _ = binomialFrom m threshold := rfl

private theorem thresholdWeight_const_one (m threshold : Nat) :
    thresholdWeight threshold (fun _ : BooleanPoint m => (1 : ZMod 2)) =
      binomialFrom m threshold := by
  rw [thresholdWeight]
  simpa using card_booleanPoints_atLeast m threshold

private theorem binomialFrom_succ (n threshold : Nat) :
    binomialFrom (n + 1) threshold =
      binomialFrom n threshold + binomialFrom n (threshold - 1) := by
  rw [← thresholdWeight_const_one, thresholdWeight_succ_split]
  rw [thresholdWeight_const_one, thresholdWeight_const_one]

/-- Increasing the ambient Boolean-cube dimension cannot decrease a fixed
binomial tail. -/
theorem binomialTail_mono_left {a b w : Nat} (hab : a ≤ b) :
    binomialTail a w ≤ binomialTail b w := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih =>
      calc
        binomialTail a w ≤ binomialTail b w := ih
        _ ≤ binomialTail (b + 1) w := by
          change binomialFrom b (w + 1) ≤ binomialFrom (b + 1) (w + 1)
          rw [binomialFrom_succ]
          exact Nat.le_add_right _ _

private def emptyMonomial (m : Nat) : SquarefreeMonomial m 0 :=
  ⟨∅, by simp⟩

private theorem squarefreeMonomial_degree_zero_eq {m : Nat}
    (monomial : SquarefreeMonomial m 0) :
    monomial = emptyMonomial m := by
  apply Subtype.ext
  exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero monomial.2)

private theorem evaluation_degree_zero {m : Nat}
    (polynomial : ANFPolynomial m 0) (point : BooleanPoint m) :
    evaluationLinearMap m 0 polynomial point = polynomial (emptyMonomial m) := by
  classical
  rw [evaluationLinearMap_apply, Fintype.sum_eq_single (emptyMonomial m)]
  · simp [monomialValue, emptyMonomial]
  · intro other hne
    exact (hne (squarefreeMonomial_degree_zero_eq other)).elim

private theorem thresholdWeight_evaluation_degree_zero {m threshold : Nat}
    (polynomial : ANFPolynomial m 0) (hnonzero : polynomial ≠ 0) :
    thresholdWeight threshold (evaluationLinearMap m 0 polynomial) =
      binomialFrom m threshold := by
  have hcoefficient : polynomial (emptyMonomial m) ≠ 0 := by
    intro hzero
    apply hnonzero
    funext monomial
    rw [squarefreeMonomial_degree_zero_eq monomial, hzero]
    rfl
  calc
    thresholdWeight threshold (evaluationLinearMap m 0 polynomial) =
        ((Finset.univ : Finset (BooleanPoint m)).filter fun point =>
          threshold ≤ pointWeight point).card := by
      unfold thresholdWeight
      congr 1
      ext point
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [evaluation_degree_zero]
      simp [hcoefficient]
    _ = binomialFrom m threshold := card_booleanPoints_atLeast m threshold


private theorem thresholdWeight_zero {m : Nat}
    (word : Word (ZMod 2) (BooleanPoint m)) :
    thresholdWeight 0 word = HammingWeight word := by
  unfold thresholdWeight HammingWeight hammingSupport
  congr 1
  ext point
  simp

private theorem polynomial_eq_zero_of_slices_eq_zero {m r : Nat}
    (polynomial : ANFPolynomial (m + 1) (r + 1))
    (hzero : zeroSlicePolynomial polynomial = 0)
    (hderivative : derivativePolynomial polynomial = 0) :
    polynomial = 0 := by
  funext monomial
  let e := squarefreeMonomialSuccEquiv m r
  have hinverse : e.symm (e monomial) = monomial := e.symm_apply_apply monomial
  cases hsplit : e monomial with
  | inl lower =>
      have hmonomial : monomial = liftMonomialWithoutZero lower := by
        rw [← hinverse, hsplit]
        rfl
      rw [hmonomial]
      have happly := congrFun hzero lower
      simpa [zeroSlicePolynomial] using happly
  | inr lower =>
      have hmonomial : monomial = liftMonomialWithZero lower := by
        rw [← hinverse, hsplit]
        rfl
      rw [hmonomial]
      have happly := congrFun hderivative lower
      simpa [derivativePolynomial] using happly

private theorem binomialFrom_eq_zero_of_lt {n threshold : Nat}
    (h : n < threshold) :
    binomialFrom n threshold = 0 := by
  rw [binomialFrom, Finset.Icc_eq_empty (by omega)]
  simp

private theorem binomialFrom_le_thresholdWeight_evaluation :
    ∀ {m r threshold : Nat}, r ≤ m →
      ∀ (polynomial : ANFPolynomial m r), polynomial ≠ 0 →
        binomialFrom (m - r) threshold ≤
          thresholdWeight threshold (evaluationLinearMap m r polynomial) := by
  intro m
  induction m with
  | zero =>
      intro r threshold hrm polynomial hnonzero
      have hr : r = 0 := by omega
      subst r
      exact (thresholdWeight_evaluation_degree_zero polynomial hnonzero).ge
  | succ m ih =>
      intro r threshold hrm polynomial hnonzero
      by_cases hthreshold : threshold ≤ (m + 1) - r
      · cases r with
        | zero =>
            exact (thresholdWeight_evaluation_degree_zero polynomial hnonzero).ge
        | succ r =>
            by_cases hdegree : r + 1 ≤ m
            · let zeroPolynomial := zeroSlicePolynomial polynomial
              let derivative := derivativePolynomial polynomial
              let zeroWord := evaluationLinearMap m (r + 1) zeroPolynomial
              let derivativeWord := evaluationLinearMap m r derivative
              have hzeroSlice :
                  (fun point =>
                    evaluationLinearMap (m + 1) (r + 1) polynomial
                      (Fin.cons 0 point)) = zeroWord := by
                funext point
                rw [evaluation_succ_split]
                simp [zeroWord, zeroPolynomial]
              have honeSlice :
                  (fun point =>
                    evaluationLinearMap (m + 1) (r + 1) polynomial
                      (Fin.cons 1 point)) = zeroWord + derivativeWord := by
                funext point
                rw [evaluation_succ_split]
                simp [zeroWord, derivativeWord, zeroPolynomial, derivative]
              have hsplitWeight :
                  thresholdWeight threshold
                      (evaluationLinearMap (m + 1) (r + 1) polynomial) =
                    thresholdWeight threshold zeroWord +
                      thresholdWeight (threshold - 1)
                        (zeroWord + derivativeWord) := by
                rw [thresholdWeight_succ_split, hzeroSlice, honeSlice]
              by_cases hderivative : derivative = 0
              · have hzeroPolynomial : zeroPolynomial ≠ 0 := by
                  intro hzero
                  exact hnonzero
                    (polynomial_eq_zero_of_slices_eq_zero polynomial hzero
                      hderivative)
                have hlowerZero := ih (threshold := threshold)
                  hdegree zeroPolynomial hzeroPolynomial
                have hlowerPred := ih (threshold := threshold - 1)
                  hdegree zeroPolynomial hzeroPolynomial
                have hgap : m - r = (m - (r + 1)) + 1 := by omega
                rw [show (m + 1) - (r + 1) = m - r by omega, hgap,
                  binomialFrom_succ]
                calc
                  binomialFrom (m - (r + 1)) threshold +
                        binomialFrom (m - (r + 1)) (threshold - 1) ≤
                      thresholdWeight threshold zeroWord +
                        thresholdWeight (threshold - 1) zeroWord :=
                    Nat.add_le_add hlowerZero hlowerPred
                  _ = thresholdWeight threshold zeroWord +
                        thresholdWeight (threshold - 1)
                          (zeroWord + derivativeWord) := by
                    simp [derivativeWord, derivative, hderivative]
                  _ = thresholdWeight threshold
                        (evaluationLinearMap (m + 1) (r + 1) polynomial) :=
                    hsplitWeight.symm
              · have hrmDerivative : r ≤ m := by omega
                have hlowerDerivative :=
                  ih (threshold := threshold) hrmDerivative derivative hderivative
                have hxor : zeroWord + (zeroWord + derivativeWord) =
                    derivativeWord := by
                  funext point
                  rw [← add_assoc, ZModModule.add_self, zero_add]
                have hgapDerivative :
                    (m + 1) - (r + 1) = m - r := by omega
                calc
                  binomialFrom ((m + 1) - (r + 1)) threshold =
                      binomialFrom (m - r) threshold :=
                    congrArg (fun gap => binomialFrom gap threshold) hgapDerivative
                  _ ≤ thresholdWeight threshold derivativeWord :=
                    hlowerDerivative
                  _ = thresholdWeight threshold
                        (zeroWord + (zeroWord + derivativeWord)) := by rw [hxor]
                  _ ≤ thresholdWeight threshold zeroWord +
                        thresholdWeight threshold (zeroWord + derivativeWord) :=
                    thresholdWeight_add_le zeroWord (zeroWord + derivativeWord)
                  _ ≤ thresholdWeight threshold zeroWord +
                        thresholdWeight (threshold - 1)
                          (zeroWord + derivativeWord) := by
                    exact Nat.add_le_add_left
                      (thresholdWeight_antitone (Nat.sub_le threshold 1)
                        (zeroWord + derivativeWord)) _
                  _ = thresholdWeight threshold
                        (evaluationLinearMap (m + 1) (r + 1) polynomial) :=
                    hsplitWeight.symm
            · have htop : r + 1 = m + 1 := by omega
              have hthresholdZero : threshold = 0 := by omega
              subst threshold
              have hevaluation :
                  evaluationLinearMap (m + 1) (r + 1) polynomial ≠ 0 := by
                intro hzero
                exact hnonzero
                  ((evaluationLinearMap_injective (m + 1) (r + 1))
                    (by simpa using hzero))
              rw [show (m + 1) - (r + 1) = 0 by omega,
                thresholdWeight_zero]
              have hpositive : 0 < HammingWeight
                  (evaluationLinearMap (m + 1) (r + 1) polynomial) :=
                Nat.pos_of_ne_zero
                  ((HammingWeight_eq_zero_iff _).not.mpr hevaluation)
              simpa [binomialFrom] using hpositive
      · rw [binomialFrom_eq_zero_of_lt (by omega)]
        exact Nat.zero_le _


private theorem thresholdWeight_succ_eq_restrictedWeight {m w : Nat}
    (word : Word (ZMod 2) (BooleanPoint m)) :
    thresholdWeight (w + 1) word = restrictedWeight w word := by
  let fullSupport := (Finset.univ : Finset (BooleanPoint m)).filter fun point =>
    w + 1 ≤ pointWeight point ∧ word point ≠ 0
  let keptSupport := hammingSupport (restrictKept m w word)
  have hcard : keptSupport.card = fullSupport.card := by
    apply Finset.card_bij (s := keptSupport) (t := fullSupport)
        (fun point _hpoint => point.1)
    · intro point hpoint
      have hnonzero : word point.1 ≠ 0 := by
        exact (Finset.mem_filter.mp hpoint).2
      simp [fullSupport, hnonzero]
      omega
    · intro left _hleft right _hright heq
      exact Subtype.ext heq
    · intro point hpoint
      have hdata : w + 1 ≤ pointWeight point ∧ word point ≠ 0 := by
        simpa [fullSupport] using hpoint
      let kept : KeptPoint m w := ⟨point, by omega⟩
      have hkept : kept ∈ keptSupport := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdata.2⟩
      exact ⟨kept, hkept, rfl⟩
  exact hcard.symm

/-- Every nonzero concrete degree-`r` evaluation retains at least the HH18
binomial tail above a cut strictly below the complementary degree. -/
theorem binomialTail_le_restrictedWeight
    {m r w : Nat} (hnoKernel : w < m - r)
    {word : Word (ZMod 2) (BooleanPoint m)}
    (hword : word ∈ (reedMullerCode r m).carrier)
    (hnonzero : word ≠ 0) :
    binomialTail (m - r) w ≤ restrictedWeight w word := by
  rcases (mem_reedMullerCode word).1 hword with ⟨polynomial, rfl⟩
  have hrm : r ≤ m := by omega
  have hpolynomial : polynomial ≠ 0 := by
    intro hzero
    apply hnonzero
    simp [hzero]
  have hlower := binomialFrom_le_thresholdWeight_evaluation
    hrm polynomial hpolynomial (threshold := w + 1)
  change binomialFrom (m - r) (w + 1) ≤
    thresholdWeight (w + 1) (evaluationLinearMap m r polynomial) at hlower
  simpa [binomialTail, binomialFrom,
    thresholdWeight_succ_eq_restrictedWeight] using hlower

/-- The concrete restricted nonzero Reed--Muller spectrum has exactly the
HH18 binomial-tail minimum. -/
theorem restrictedMinimumWeight_eq_binomialTail
    {m r w : Nat} (hnoKernel : w < m - r) :
    restrictedMinimumWeight r m w = binomialTail (m - r) w := by
  apply le_antisymm
  · exact restrictedMinimumWeight_le_binomialTail (by omega)
  · unfold restrictedMinimumWeight
    apply le_csInf (restrictedNonzeroWeightSet_nonempty r m w)
    intro weight hweight
    rcases (mem_restrictedNonzeroWeightSet).1 hweight with
      ⟨word, hword, hnonzero, rfl⟩
    exact binomialTail_le_restrictedWeight hnoKernel hword hnonzero

private theorem HammingWeight_evaluation_vanishingPolynomial
    {r m : Nat} (support : Finset (Fin m))
    (hcard : support.card ≤ r) :
    HammingWeight
        (evaluationLinearMap m r (vanishingPolynomial support hcard)) =
      2 ^ supportᶜ.card := by
  classical
  let word := evaluationLinearMap m r (vanishingPolynomial support hcard)
  let active := hammingSupport word
  let target := supportᶜ.powerset
  have hcardEq : active.card = target.card := by
    apply Finset.card_bij (s := active) (t := target)
        (fun point _hpoint => hammingSupport point)
    · intro point hpoint
      have hvalue : word point ≠ 0 := by
        simpa [active, hammingSupport] using hpoint
      have hdisjoint : Disjoint support (hammingSupport point) := by
        exact (evaluation_vanishingPolynomial_ne_zero_iff
          support hcard point).mp (by simpa [word] using hvalue)
      have hsubset : hammingSupport point ⊆ supportᶜ := by
        intro coordinate hcoordinate
        rw [Finset.mem_compl]
        intro hsupport
        exact (Finset.disjoint_left.mp hdisjoint) hsupport hcoordinate
      simpa [target] using hsubset
    · intro left _hleft right _hright heq
      exact booleanPoint_eq_of_hammingSupport_eq heq
    · intro subset hsubset
      have htarget : subset ⊆ supportᶜ := by
        simpa [target] using hsubset
      let point : BooleanPoint m := supportIndicatorPoint subset
      have hdisjoint : Disjoint support (hammingSupport point) := by
        rw [show point = supportIndicatorPoint subset by rfl,
          hammingSupport_supportIndicatorPoint]
        exact Finset.disjoint_left.mpr fun coordinate hsupport hcoordinate =>
          (Finset.mem_compl.mp (htarget hcoordinate)) hsupport
      have hvalue : word point ≠ 0 := by
        simpa [word] using
          (evaluation_vanishingPolynomial_ne_zero_iff
            support hcard point).mpr hdisjoint
      have hpoint : point ∈ active := by
        simp [active, hammingSupport, hvalue]
      refine ⟨point, hpoint, ?_⟩
      simp [point]
  calc
    HammingWeight word = active.card := by rfl
    _ = target.card := hcardEq
    _ = 2 ^ supportᶜ.card := by simp [target]

private theorem binomialFrom_zero (n : Nat) :
    binomialFrom n 0 = 2 ^ n := by
  rw [binomialFrom, ← Nat.range_succ_eq_Icc_zero]
  exact Nat.sum_range_choose n

private theorem thresholdWeight_zero_eq_HammingWeight {m : Nat}
    (word : Word (ZMod 2) (BooleanPoint m)) :
    thresholdWeight 0 word = HammingWeight word := by
  simp [thresholdWeight, HammingWeight, hammingSupport]

/-- The concrete degree-`r` Reed--Muller evaluation code has its classical
minimum distance `2^(m-r)`, with both attainment and the lower bound derived
from the same ANF/Plotkin machinery as the restricted theorem. -/
theorem reedMullerCode_minimumDistance
    {m r : Nat} (hrm : r ≤ m) :
    MinimumDistance (reedMullerCode r m) (2 ^ (m - r)) := by
  let support := witnessSupport hrm
  have hsupport : support.card ≤ r := by simp [support]
  let polynomial := vanishingPolynomial support hsupport
  let word := evaluationLinearMap m r polynomial
  have hword : word ∈ (reedMullerCode r m).carrier :=
    evaluation_mem_reedMullerCode polynomial
  have hwordNonzero : word ≠ 0 := by
    have hvalue : word (0 : BooleanPoint m) ≠ 0 := by
      simpa [word, polynomial] using
        (evaluation_vanishingPolynomial_ne_zero_iff
          support hsupport (0 : BooleanPoint m)).mpr (by simp)
    intro hzero
    exact hvalue (by simpa using congrFun hzero (0 : BooleanPoint m))
  have hwordWeight : HammingWeight word = 2 ^ (m - r) := by
    calc
      HammingWeight word = 2 ^ supportᶜ.card :=
        HammingWeight_evaluation_vanishingPolynomial support hsupport
      _ = 2 ^ (m - r) := by
        rw [Finset.card_compl, Fintype.card_fin, witnessSupport_card]
  refine ⟨word, hword, hwordNonzero, hwordWeight, ?_⟩
  intro candidate hcandidate hcandidateNonzero
  rcases (mem_reedMullerCode candidate).1 hcandidate with ⟨candidatePolynomial, rfl⟩
  have hpolynomial : candidatePolynomial ≠ 0 := by
    intro hzero
    apply hcandidateNonzero
    simp [hzero]
  have hlower := binomialFrom_le_thresholdWeight_evaluation
    hrm candidatePolynomial hpolynomial (threshold := 0)
  simpa [binomialFrom_zero,
    thresholdWeight_zero_eq_HammingWeight] using hlower

private theorem restrictKept_injective_on_reedMullerCode
    {m r w : Nat} (hnoKernel : w < m - r) :
    Function.Injective
      ((restrictKept m w).domRestrict (reedMullerCode r m).carrier) := by
  rw [injective_iff_map_eq_zero]
  intro word hzero
  apply Subtype.ext
  exact restrictKept_eq_zero_of_mem_reedMullerCode
    hnoKernel word.property (by simpa using hzero)

/-- Puncturing below the no-kernel cut preserves the dimension of the actual
Reed--Muller evaluation code. -/
theorem puncturedReedMullerCode_dimension_eq_card_squarefree
    {m r w : Nat} (hnoKernel : w < m - r) :
    Dimension (puncturedReedMullerCode r m w) =
      Fintype.card (SquarefreeMonomial m r) := by
  change Module.finrank (ZMod 2)
      ((reedMullerCode r m).carrier.map (restrictKept m w)) = _
  rw [← LinearMap.range_domRestrict]
  rw [LinearMap.finrank_range_of_inj
    (restrictKept_injective_on_reedMullerCode hnoKernel)]
  exact reedMullerCode_dimension_eq_card_squarefree r m

/-- The retained HH18 coordinates are counted by the corresponding binomial
tail of Boolean-point weights. -/
theorem keptPoint_card_eq_binomialTail (m w : Nat) :
    Fintype.card (KeptPoint m w) = binomialTail m w := by
  rw [Fintype.card_subtype]
  change ((Finset.univ : Finset (BooleanPoint m)).filter fun point =>
      w < pointWeight point).card = _
  calc
    ((Finset.univ : Finset (BooleanPoint m)).filter fun point =>
        w < pointWeight point).card =
        ((Finset.univ : Finset (BooleanPoint m)).filter fun point =>
          w + 1 ≤ pointWeight point).card := by
      congr 1
    _ = binomialFrom m (w + 1) := card_booleanPoints_atLeast m (w + 1)
    _ = binomialTail m w := rfl

/-- The removed HH18 coordinates are counted by the exact cumulative binomial
sum through weight `w`. -/
theorem lowPoint_card_eq_sum_choose (m w : Nat) :
    Fintype.card (LowPoint m w) =
      ∑ i ∈ Finset.Icc 0 w, Nat.choose m i := by
  classical
  rw [Fintype.card_subtype]
  change ((Finset.univ : Finset (BooleanPoint m)).filter fun point =>
      pointWeight point ≤ w).card = _
  let active := (Finset.univ : Finset (BooleanPoint m)).filter fun point =>
    pointWeight point ≤ w
  let target := ((Finset.univ : Finset (Fin m)).powerset).filter fun support =>
    support.card ∈ Finset.Icc 0 w
  have hcard : active.card = target.card := by
    apply Finset.card_bij (s := active) (t := target)
        (fun point _hpoint => hammingSupport point)
    · intro point hpoint
      have hweight : (hammingSupport point).card ≤ w := by
        exact (Finset.mem_filter.mp hpoint).2
      simp [target, hweight]
    · intro left _hleft right _hright heq
      exact booleanPoint_eq_of_hammingSupport_eq heq
    · intro support hsupport
      have htarget : support ⊆ (Finset.univ : Finset (Fin m)) ∧
          support.card ∈ Finset.Icc 0 w := by
        simpa [target] using hsupport
      have hweight : support.card ≤ w :=
        (Finset.mem_Icc.mp htarget.2).2
      let point := supportIndicatorPoint support
      have hpoint : point ∈ active := by
        simp [active, point, hweight]
      refine ⟨point, hpoint, ?_⟩
      simp [point]
  calc
    ((Finset.univ : Finset (BooleanPoint m)).filter fun point =>
        pointWeight point ≤ w).card = active.card := rfl
    _ = target.card := hcard
    _ = ∑ i ∈ Finset.Icc 0 w,
        (((Finset.univ : Finset (Fin m)).powerset).filter fun support =>
          support.card = i).card := by
      symm
      exact Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin m)).powerset
        (Finset.Icc 0 w) Finset.card
    _ = ∑ i ∈ Finset.Icc 0 w, Nat.choose m i := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← Finset.powersetCard_eq_filter, Finset.card_powersetCard]
      simp

/-- The punctured code has the same source-stated cumulative-binomial
dimension as its unpunctured Reed--Muller parent below the no-kernel cut. -/
theorem puncturedReedMullerCode_dimension_eq_binomialUpTo
    {m r w : Nat} (hnoKernel : w < m - r) :
    Dimension (puncturedReedMullerCode r m w) = binomialUpTo m r := by
  calc
    Dimension (puncturedReedMullerCode r m w) =
        Fintype.card (SquarefreeMonomial m r) :=
      puncturedReedMullerCode_dimension_eq_card_squarefree hnoKernel
    _ = Dimension (reedMullerCode r m) :=
      (reedMullerCode_dimension_eq_card_squarefree r m).symm
    _ = binomialUpTo m r :=
      reedMullerCode_dimension_eq_binomialUpTo r m

/-- Raw source form of punctured Reed--Muller dimension preservation. -/
theorem puncturedReedMullerCode_dimension_eq_sum_choose
    {m r w : Nat} (hnoKernel : w < m - r) :
    Dimension (puncturedReedMullerCode r m w) =
      ∑ i ∈ Finset.Icc 0 r, Nat.choose m i := by
  simpa [binomialUpTo] using
    puncturedReedMullerCode_dimension_eq_binomialUpTo hnoKernel

private theorem binomialTail_pos {n w : Nat} (h : w < n) :
    0 < binomialTail n w := by
  have hn : n ∈ Finset.Icc (w + 1) n := by
    simp
    omega
  have hle : Nat.choose n n ≤
      ∑ i ∈ Finset.Icc (w + 1) n, Nat.choose n i := by
    exact Finset.single_le_sum (fun i _hi => Nat.zero_le (Nat.choose n i)) hn
  have hone : 1 ≤ ∑ i ∈ Finset.Icc (w + 1) n, Nat.choose n i := by
    simpa using hle
  simpa [binomialTail] using (Nat.zero_lt_one.trans_le hone)

/-- The actual punctured Reed--Muller code attains the HH18 restricted-support
minimum; this packages the constructed witness and pointwise lower bound as
the repository's genuine classical `MinimumDistance` interface. -/
theorem puncturedReedMullerCode_minimumDistance
    {m r w : Nat} (hnoKernel : w < m - r) :
    MinimumDistance (puncturedReedMullerCode r m w)
      (binomialTail (m - r) w) := by
  have hrm : r ≤ m := by omega
  obtain ⟨full, hfull, _hfullNonzero, hweight⟩ :=
    exists_reedMullerCodeword_restrictedWeight_eq_binomialTail
      (w := w) hrm
  let kept := restrictKept m w full
  have hkept : kept ∈ (puncturedReedMullerCode r m w).carrier :=
    (mem_puncturedReedMullerCode kept).2 ⟨full, hfull, rfl⟩
  have hkeptWeight : HammingWeight kept = binomialTail (m - r) w :=
    hweight
  have hkeptNonzero : kept ≠ 0 := by
    intro hzero
    have hzeroWeight : HammingWeight kept = 0 := by simp [hzero]
    have hpositive := binomialTail_pos hnoKernel
    omega
  refine ⟨kept, hkept, hkeptNonzero, hkeptWeight, ?_⟩
  intro candidate hcandidate hcandidateNonzero
  rcases (mem_puncturedReedMullerCode candidate).1 hcandidate with
    ⟨candidateFull, hcandidateFull, hrestrict⟩
  have hcandidateFullNonzero : candidateFull ≠ 0 := by
    intro hzero
    apply hcandidateNonzero
    rw [← hrestrict, hzero]
    simp
  calc
    binomialTail (m - r) w ≤ restrictedWeight w candidateFull :=
      binomialTail_le_restrictedWeight hnoKernel hcandidateFull
        hcandidateFullNonzero
    _ = HammingWeight candidate := by
      change HammingWeight (restrictKept m w candidateFull) = _
      rw [hrestrict]

/-- The attained logical coset distance of puncturing modulo shortening is the
same HH18 binomial tail.  The witness is the concrete vanishing-polynomial
word whose low block is nonzero, not merely an arbitrary nonzero punctured
word. -/
theorem puncturedReedMullerCode_relativeMinimumDistance_shortened
    {m r w : Nat} (hnoKernel : w < m - r) :
    RelativeMinimumDistance (puncturedReedMullerCode r m w)
      (shortenedReedMullerCode r m w) (binomialTail (m - r) w) := by
  have hrm : r ≤ m := by omega
  obtain ⟨full, hfull, hfullLow, hweight⟩ :=
    exists_reedMullerCodeword_restrictedWeight_eq_binomialTail_and_low_ne_zero
      (w := w) hrm
  let kept := restrictKept m w full
  have hkept : kept ∈ (puncturedReedMullerCode r m w).carrier :=
    (mem_puncturedReedMullerCode kept).2 ⟨full, hfull, rfl⟩
  have hkeptOutside :
      kept ∉ (shortenedReedMullerCode r m w).carrier := by
    intro hshortened
    rcases (mem_shortenedReedMullerCode kept).1 hshortened with
      ⟨shortenedFull, hshortenedFull, hshortenedLow, hshortenedKept⟩
    have hdifference :
        full - shortenedFull ∈ (reedMullerCode r m).carrier :=
      (reedMullerCode r m).carrier.sub_mem hfull hshortenedFull
    have hdifferenceKept :
        restrictKept m w (full - shortenedFull) = 0 := by
      rw [map_sub, show restrictKept m w full = kept by rfl,
        hshortenedKept, sub_self]
    have hdifferenceZero : full - shortenedFull = 0 :=
      restrictKept_eq_zero_of_mem_reedMullerCode
        hnoKernel hdifference hdifferenceKept
    have hfullEq : full = shortenedFull := sub_eq_zero.mp hdifferenceZero
    apply hfullLow
    rw [hfullEq, hshortenedLow]
  have hkeptWeight :
      HammingWeight kept = binomialTail (m - r) w := by
    simpa [kept, restrictedWeight] using hweight
  rcases puncturedReedMullerCode_minimumDistance hnoKernel with
    ⟨_minimumWitness, _hminimumWitness, _hminimumWitnessNonzero,
      _hminimumWitnessWeight, hleast⟩
  refine ⟨kept, hkept, hkeptOutside, hkeptWeight, ?_⟩
  intro candidate hcandidate hcandidateOutside
  have hcandidateNonzero : candidate ≠ 0 := by
    intro hzero
    apply hcandidateOutside
    rw [hzero]
    exact (shortenedReedMullerCode r m w).carrier.zero_mem
  exact hleast candidate hcandidate hcandidateNonzero

/-- Exact classical parameters of the actual HH18 punctured Reed--Muller code
below the no-kernel cut. -/
noncomputable def puncturedReedMullerCodeParameters
    {m r w : Nat} (hnoKernel : w < m - r) :
    CodeParameters (ZMod 2) (KeptPoint m w) where
  code := puncturedReedMullerCode r m w
  length := binomialTail m w
  dimension := binomialUpTo m r
  minimumDistance := binomialTail (m - r) w
  length_eq := by
    simpa [Length] using (keptPoint_card_eq_binomialTail m w).symm
  dimension_eq :=
    (puncturedReedMullerCode_dimension_eq_binomialUpTo hnoKernel).symm
  distance_spec := puncturedReedMullerCode_minimumDistance hnoKernel

private theorem HammingWeight_eq_restrictLow_add_restrictKept
    {m w : Nat} (word : Word (ZMod 2) (BooleanPoint m)) :
    HammingWeight word =
      HammingWeight (restrictLow m w word) +
        HammingWeight (restrictKept m w word) := by
  classical
  simp only [HammingWeight, hammingSupport, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun point : BooleanPoint m => pointWeight point ≤ w)
    (fun point => if word point ≠ 0 then 1 else 0)]
  congr 1
  · let e : {point : BooleanPoint m // ¬ pointWeight point ≤ w} ≃
        KeptPoint m w := Equiv.subtypeEquivProp (by
          funext point
          apply propext
          omega)
    exact Fintype.sum_equiv e _ _ (fun point => by
      simp [e, Equiv.subtypeEquivProp, restrictKept_apply])

/-- A systematic punctured coset has Ward divisibility after the logical
low-coordinate contribution is restored. -/
theorem systematicCoset_weight_add_logical_dvd {w r m nu : Nat}
    (h : Admissible w r m) (hdegree : nu * r < m)
    (logical : Word (ZMod 2) (LowPoint m w))
    {word : Word (ZMod 2) (KeptPoint m w)}
    (hcoset : word - systematicKeptLift h logical ∈
      (shortenedReedMullerCode r m w).carrier) :
    2 ^ nu ∣ HammingWeight word + HammingWeight logical := by
  have hwr : w ≤ r := by
    have := h.2.1
    omega
  have hr : 0 < r := by
    have := h.2.1
    omega
  rcases (mem_shortenedReedMullerCode _).1 hcoset with
    ⟨shortenedFull, hshortenedFull, hshortenedLow, hshortenedKept⟩
  let full := shortenedFull + lowCoordinateExtension hwr logical
  have hfull : full ∈ (reedMullerCode r m).carrier := by
    exact (reedMullerCode r m).carrier.add_mem hshortenedFull
      (lowCoordinateExtension_mem_reedMullerCode hwr logical)
  have hlow : restrictLow m w full = logical := by
    calc
      restrictLow m w full =
          restrictLow m w shortenedFull +
            restrictLow m w (lowCoordinateExtension hwr logical) := by
              simp [full, map_add]
      _ = logical := by
        simp [hshortenedLow, restrictLow_lowCoordinateExtension]
  have hsystematic : systematicKeptLift h logical =
      restrictKept m w (lowCoordinateExtension hwr logical) := by
    simp [systematicKeptLift, LinearMap.comp_apply]
  have hkeptSum : restrictKept m w shortenedFull +
      systematicKeptLift h logical = word := by
    exact ((sub_eq_iff_eq_add).mp hshortenedKept.symm).symm
  have hkept : restrictKept m w full = word := by
    calc
      restrictKept m w full =
          restrictKept m w shortenedFull +
            restrictKept m w (lowCoordinateExtension hwr logical) := by
              simp [full, map_add]
      _ = restrictKept m w shortenedFull +
          systematicKeptLift h logical := by rw [← hsystematic]
      _ = word := hkeptSum
  have hweight : HammingWeight full =
      HammingWeight logical + HammingWeight word := by
    calc
      HammingWeight full =
          HammingWeight (restrictLow m w full) +
            HammingWeight (restrictKept m w full) :=
        HammingWeight_eq_restrictLow_add_restrictKept full
      _ = HammingWeight logical + HammingWeight word := by
        rw [hlow, hkept]
  have hward : 2 ^ nu ∣ HammingWeight full :=
    reedMullerCode_hammingWeight_dvd_pow_two hr hdegree hfull
  rw [hweight] at hward
  simpa [Nat.add_comm] using hward

private theorem evaluation_basisPolynomial_ne_zero_iff_support_subset
    {m r : Nat} (monomial : SquarefreeMonomial m r)
    (point : BooleanPoint m) :
    evaluationLinearMap m r (basisPolynomial monomial) point ≠ 0 ↔
      monomial.1 ⊆ hammingSupport point := by
  rw [evaluation_basisPolynomial]
  unfold monomialValue
  rw [Finset.prod_ne_zero_iff]
  constructor
  · intro hnonzero coordinate hcoordinate
    simp [hammingSupport, hnonzero coordinate hcoordinate]
  · intro hsubset coordinate hcoordinate
    have := hsubset hcoordinate
    simpa [hammingSupport] using this

private theorem HammingWeight_evaluation_basisPolynomial_le
    {m r : Nat} (monomial : SquarefreeMonomial m r) :
    HammingWeight (evaluationLinearMap m r (basisPolynomial monomial)) ≤
      2 ^ monomial.1ᶜ.card := by
  classical
  let word := evaluationLinearMap m r (basisPolynomial monomial)
  let active := hammingSupport word
  let ComplementCoordinate :=
    {coordinate : Fin m // coordinate ∈ monomial.1ᶜ}
  let project : BooleanPoint m → Word (ZMod 2) ComplementCoordinate :=
    fun point coordinate => point coordinate.1
  have hle : active.card ≤
      (Finset.univ : Finset (Word (ZMod 2) ComplementCoordinate)).card := by
    apply Finset.card_le_card_of_injOn project
    · intro point _hpoint
      simp
    · intro left hleft right hright heq
      funext coordinate
      by_cases hcoordinate : coordinate ∈ monomial.1
      · have hleftValue : word left ≠ 0 := by
          simpa [active, hammingSupport] using hleft
        have hrightValue : word right ≠ 0 := by
          simpa [active, hammingSupport] using hright
        have hleftSupport : monomial.1 ⊆ hammingSupport left :=
          (evaluation_basisPolynomial_ne_zero_iff_support_subset
            monomial left).mp (by simpa [word] using hleftValue)
        have hrightSupport : monomial.1 ⊆ hammingSupport right :=
          (evaluation_basisPolynomial_ne_zero_iff_support_subset
            monomial right).mp (by simpa [word] using hrightValue)
        have hleftNonzero : left coordinate ≠ 0 := by
          simpa [hammingSupport] using hleftSupport hcoordinate
        have hrightNonzero : right coordinate ≠ 0 := by
          simpa [hammingSupport] using hrightSupport hcoordinate
        rw [binary_eq_one_of_ne_zero _ hleftNonzero,
          binary_eq_one_of_ne_zero _ hrightNonzero]
      · let complementCoordinate : ComplementCoordinate :=
          ⟨coordinate, by simp [hcoordinate]⟩
        have happly := congrFun heq complementCoordinate
        simpa [project, complementCoordinate] using happly
  calc
    HammingWeight word = active.card := by rfl
    _ ≤ (Finset.univ : Finset
        (Word (ZMod 2) ComplementCoordinate)).card := hle
    _ = 2 ^ monomial.1ᶜ.card := by
      simp [ComplementCoordinate, ZMod.card]
      rw [Finset.card_compl]
      simp

private theorem evaluation_basisPolynomial_ne_zero {m r : Nat}
    (monomial : SquarefreeMonomial m r) :
    evaluationLinearMap m r (basisPolynomial monomial) ≠ 0 := by
  let point : BooleanPoint m := fun coordinate =>
    if coordinate ∈ monomial.1 then 1 else 0
  have hsupport : monomial.1 ⊆ hammingSupport point := by
    intro coordinate hcoordinate
    simp [point, hammingSupport, hcoordinate]
  have hvalue :=
    (evaluation_basisPolynomial_ne_zero_iff_support_subset
      monomial point).2 hsupport
  intro hzero
  exact hvalue (by simpa using congrFun hzero point)

private theorem HammingWeight_evaluation_basisPolynomial_eq
    {m r : Nat} (hrm : r ≤ m) (monomial : SquarefreeMonomial m r)
    (hcard : monomial.1.card = r) :
    HammingWeight (evaluationLinearMap m r (basisPolynomial monomial)) =
      2 ^ (m - r) := by
  apply le_antisymm
  · calc
      HammingWeight
          (evaluationLinearMap m r (basisPolynomial monomial)) ≤
          2 ^ monomial.1ᶜ.card :=
        HammingWeight_evaluation_basisPolynomial_le monomial
      _ = 2 ^ (m - r) := by
        rw [Finset.card_compl, Fintype.card_fin, hcard]
  · rcases reedMullerCode_minimumDistance hrm with
      ⟨_witness, _hwitness, _hwitnessNonzero, _hwitnessWeight, hleast⟩
    exact hleast _ (evaluation_mem_reedMullerCode _)
      (evaluation_basisPolynomial_ne_zero monomial)

private def witnessMonomial {r m : Nat} (hrm : r ≤ m) :
    SquarefreeMonomial m r :=
  ⟨witnessSupport hrm, by simp⟩

/-- Shortening below degree `r` preserves the classical Reed--Muller minimum
distance.  The upper witness is an actual degree-`r` monomial that vanishes on
every removed low-weight point; the lower bound comes from its full RM lift. -/
theorem shortenedReedMullerCode_minimumDistance
    {m r w : Nat} (hrm : r ≤ m) (hcut : w < r) :
    MinimumDistance (shortenedReedMullerCode r m w) (2 ^ (m - r)) := by
  let monomial := witnessMonomial hrm
  let full := evaluationLinearMap m r (basisPolynomial monomial)
  let kept := restrictKept m w full
  have hfull : full ∈ (reedMullerCode r m).carrier :=
    evaluation_mem_reedMullerCode _
  have hfullNonzero : full ≠ 0 := by
    simpa [full] using evaluation_basisPolynomial_ne_zero monomial
  have hfullWeight : HammingWeight full = 2 ^ (m - r) := by
    exact HammingWeight_evaluation_basisPolynomial_eq hrm monomial
      (by simp [monomial, witnessMonomial])
  have hlow : restrictLow m w full = 0 := by
    funext point
    by_contra hvalue
    have hsupport : monomial.1 ⊆ hammingSupport point.1 :=
      (evaluation_basisPolynomial_ne_zero_iff_support_subset
        monomial point.1).mp (by simpa [full] using hvalue)
    have hcardLe : monomial.1.card ≤ (hammingSupport point.1).card :=
      Finset.card_le_card hsupport
    have hpointWeight : (hammingSupport point.1).card ≤ w := by
      simpa [pointWeight, HammingWeight] using point.2
    have hmonomialCard : monomial.1.card = r := by
      simp [monomial, witnessMonomial]
    omega
  have hkept : kept ∈ (shortenedReedMullerCode r m w).carrier :=
    (mem_shortenedReedMullerCode kept).2 ⟨full, hfull, hlow, rfl⟩
  have hkeptWeight : HammingWeight kept = 2 ^ (m - r) := by
    have hsplit := HammingWeight_eq_restrictLow_add_restrictKept
      (w := w) full
    rw [hlow, HammingWeight_zero, zero_add] at hsplit
    exact hsplit.symm.trans hfullWeight
  have hkeptNonzero : kept ≠ 0 := by
    intro hzero
    have hzeroWeight : HammingWeight kept = 0 := by simp [hzero]
    have hpositive : 0 < 2 ^ (m - r) := by positivity
    omega
  refine ⟨kept, hkept, hkeptNonzero, hkeptWeight, ?_⟩
  intro candidate hcandidate hcandidateNonzero
  rcases (mem_shortenedReedMullerCode candidate).1 hcandidate with
    ⟨candidateFull, hcandidateFull, hcandidateLow, hcandidateKept⟩
  have hcandidateFullNonzero : candidateFull ≠ 0 := by
    intro hzero
    apply hcandidateNonzero
    rw [← hcandidateKept, hzero]
    simp
  rcases reedMullerCode_minimumDistance hrm with
    ⟨_rmWitness, _hrmWitness, _hrmWitnessNonzero, _hrmWitnessWeight,
      hrmLeast⟩
  have hsplit := HammingWeight_eq_restrictLow_add_restrictKept
    (w := w) candidateFull
  rw [hcandidateLow, HammingWeight_zero, zero_add, hcandidateKept] at hsplit
  exact (hrmLeast candidateFull hcandidateFull
    hcandidateFullNonzero).trans_eq hsplit

private def shortenedDomainEquivRestrictLowKernel {r m w : Nat} :
    shortenedReedMullerDomain r m w ≃ₗ[ZMod 2]
      LinearMap.ker
        ((restrictLow m w).domRestrict (reedMullerCode r m).carrier) where
  toFun word :=
    ⟨⟨word.1, word.property.1⟩, by
      change restrictLow m w word.1 = 0
      exact word.property.2⟩
  invFun word :=
    ⟨word.1.1, ⟨word.1.property, by
      change restrictLow m w word.1.1 = 0
      exact word.property⟩⟩
  left_inv word := Subtype.ext rfl
  right_inv word := Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem restrictKept_injective_on_shortenedReedMullerDomain
    {r m w : Nat} :
    Function.Injective
      ((restrictKept m w).domRestrict
        (shortenedReedMullerDomain r m w)) := by
  intro left right heq
  apply Subtype.ext
  funext point
  by_cases hpoint : pointWeight point ≤ w
  · have hleftLow : restrictLow m w left.1 = 0 := by
      exact left.property.2
    have hrightLow : restrictLow m w right.1 = 0 := by
      exact right.property.2
    have hleftApply := congrFun hleftLow ⟨point, hpoint⟩
    have hrightApply := congrFun hrightLow ⟨point, hpoint⟩
    simpa using hleftApply.trans hrightApply.symm
  · have hkept : w < pointWeight point := by omega
    have happly := congrFun heq ⟨point, hkept⟩
    simpa using happly

/-- The actual shortened Reed--Muller code has the source-stated binomial
dimension.  This is rank--nullity for the surjective low-coordinate
restriction, followed by injective restriction of its kernel to kept points. -/
theorem shortenedReedMullerCode_dimension_eq_sum_choose
    {m r w : Nat} (hwr : w ≤ r) :
    Dimension (shortenedReedMullerCode r m w) =
      ∑ i ∈ Finset.Icc (w + 1) r, Nat.choose m i := by
  let lowMap :=
    (restrictLow m w).domRestrict (reedMullerCode r m).carrier
  have hsurjective : Function.Surjective lowMap := by
    intro low
    refine ⟨⟨lowCoordinateExtension hwr low,
      lowCoordinateExtension_mem_reedMullerCode hwr low⟩, ?_⟩
    exact restrictLow_lowCoordinateExtension hwr low
  have hrange : LinearMap.range lowMap = ⊤ :=
    LinearMap.range_eq_top.mpr hsurjective
  have hrank := LinearMap.finrank_range_add_finrank_ker lowMap
  rw [hrange, finrank_top,
    Module.finrank_fintype_fun_eq_card] at hrank
  have hrank' :
      Fintype.card (LowPoint m w) +
          Module.finrank (ZMod 2) (LinearMap.ker lowMap) =
        Dimension (reedMullerCode r m) := by
    simpa [lowMap, Dimension] using hrank
  have hdomain :
      Module.finrank (ZMod 2) (shortenedReedMullerDomain r m w) =
        Module.finrank (ZMod 2) (LinearMap.ker lowMap) := by
    exact LinearEquiv.finrank_eq shortenedDomainEquivRestrictLowKernel
  have hcode :
      Dimension (shortenedReedMullerCode r m w) =
        Module.finrank (ZMod 2) (shortenedReedMullerDomain r m w) := by
    change Module.finrank (ZMod 2)
        ((shortenedReedMullerDomain r m w).map (restrictKept m w)) = _
    rw [← LinearMap.range_domRestrict]
    exact LinearMap.finrank_range_of_inj
      restrictKept_injective_on_shortenedReedMullerDomain
  have hsumSplit :
      (∑ i ∈ Finset.Icc 0 w, Nat.choose m i) +
          (∑ i ∈ Finset.Icc (w + 1) r, Nat.choose m i) =
        ∑ i ∈ Finset.Icc 0 r, Nat.choose m i := by
    have hdisjoint :
        Disjoint (Finset.Icc 0 w) (Finset.Icc (w + 1) r) := by
      exact Finset.disjoint_left.mpr (by
        intro i hiLow hiHigh
        simp only [Finset.mem_Icc] at hiLow hiHigh
        omega)
    have hunion :
        Finset.Icc 0 w ∪ Finset.Icc (w + 1) r = Finset.Icc 0 r := by
      ext i
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega
    rw [← hunion, Finset.sum_union hdisjoint]
  rw [hcode, hdomain]
  have heq :
      (∑ i ∈ Finset.Icc 0 w, Nat.choose m i) +
          Module.finrank (ZMod 2) (LinearMap.ker lowMap) =
        (∑ i ∈ Finset.Icc 0 w, Nat.choose m i) +
          ∑ i ∈ Finset.Icc (w + 1) r, Nat.choose m i := by
    calc
      (∑ i ∈ Finset.Icc 0 w, Nat.choose m i) +
          Module.finrank (ZMod 2) (LinearMap.ker lowMap) =
          Fintype.card (LowPoint m w) +
            Module.finrank (ZMod 2) (LinearMap.ker lowMap) := by
        rw [lowPoint_card_eq_sum_choose]
      _ = Dimension (reedMullerCode r m) := hrank'
      _ = ∑ i ∈ Finset.Icc 0 r, Nat.choose m i :=
        reedMullerCode_dimension_eq_sum_choose r m
      _ = (∑ i ∈ Finset.Icc 0 w, Nat.choose m i) +
          ∑ i ∈ Finset.Icc (w + 1) r, Nat.choose m i :=
        hsumSplit.symm
  exact Nat.add_left_cancel heq

/-- Exact classical parameters of the actual HH18 shortened Reed--Muller code
below the shortening cut. -/
noncomputable def shortenedReedMullerCodeParameters
    {m r w : Nat} (hrm : r ≤ m) (hcut : w < r) :
    CodeParameters (ZMod 2) (KeptPoint m w) where
  code := shortenedReedMullerCode r m w
  length := binomialTail m w
  dimension := ∑ i ∈ Finset.Icc (w + 1) r, Nat.choose m i
  minimumDistance := 2 ^ (m - r)
  length_eq := by
    simpa [Length] using (keptPoint_card_eq_binomialTail m w).symm
  dimension_eq :=
    (shortenedReedMullerCode_dimension_eq_sum_choose
      (m := m) (r := r) (w := w) (by omega)).symm
  distance_spec := shortenedReedMullerCode_minimumDistance hrm hcut



end PuncturedReedMuller
end Coding
end QEC
