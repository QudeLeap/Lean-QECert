import QEC.Coding.ExpanderCodes.LPSEffectiveNormalization
import Mathlib.Data.List.FinRange
import Mathlib.Data.Quot
import Mathlib.Data.List.NodupEquivFin

/-!
# Computed indexing of actual finite PSL vertices

Four explicit finite entry loops enumerate determinant-one matrices. A proved
sign-invariant quotient equality test deduplicates their actual projective
images. Complete enumeration supplies a computable lookup/indexOf equivalence
and semantic group-operation and quaternion-label indexing proofs.
This module does not certify full sparse-output bit/runtime complexity.
-/

namespace QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance : Fact (Even (Fintype.card (Fin 2))) := ⟨by simp⟩

private theorem sl_two_mem_center_iff (q : ℕ) [Fact q.Prime]
    (A : SL(2, ZMod q)) :
    A ∈ Subgroup.center SL(2, ZMod q) ↔ A = 1 ∨ A = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    have hr' : r ^ 2 = 1 := by simpa using hr
    rcases sq_eq_one_iff.mp hr' with h | h
    · left
      apply Subtype.ext
      rw [← hA, h]
      simp
    · right
      apply Subtype.ext
      rw [← hA, h]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  · rintro (h | h)
    · subst A
      exact ⟨1, by simp, by simp⟩
    · subst A
      refine ⟨-1, by simp, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp

theorem lpsPSLMk_eq_iff (q : ℕ) [Fact q.Prime] (A B : SL(2, ZMod q)) :
    (QuotientGroup.mk A : PSL(2, ZMod q)) = QuotientGroup.mk B ↔ A = B ∨ -A = B := by
  change QuotientGroup.mk' (Subgroup.center SL(2, ZMod q)) A =
    QuotientGroup.mk' (Subgroup.center SL(2, ZMod q)) B ↔ _
  rw [QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨z, hz, h⟩
    rcases (sl_two_mem_center_iff q z).mp hz with hz | hz
    · left
      simpa [hz] using h
    · right
      simpa [hz] using h
  · rintro (h | h)
    · exact ⟨1, (sl_two_mem_center_iff q 1).mpr (Or.inl rfl), by simpa using h⟩
    · exact ⟨-1, (sl_two_mem_center_iff q (-1)).mpr (Or.inr rfl), by simpa using h⟩

def lpsPSLDecidableEq (q : ℕ) [Fact q.Prime] : DecidableEq PSL(2, ZMod q) :=
  fun x y => Quotient.recOnSubsingleton₂ x y fun A B =>
    decidable_of_iff (A = B ∨ -A = B) (lpsPSLMk_eq_iff q A B).symm

def lpsEntryMatrix (q : ℕ) (a b c d : Fin q) : Matrix (Fin 2) (Fin 2) (ZMod q) :=
  !![(a.val : ZMod q), (b.val : ZMod q); (c.val : ZMod q), (d.val : ZMod q)]

def lpsSLMatrixCandidate (q : ℕ) (a b c d : Fin q) : Option SL(2, ZMod q) :=
  if h : (lpsEntryMatrix q a b c d).det = 1 then
    some ⟨lpsEntryMatrix q a b c d, h⟩ else none

def lpsSLList (q : ℕ) : List SL(2, ZMod q) :=
  (List.finRange q).flatMap fun a =>
    (List.finRange q).flatMap fun b =>
      (List.finRange q).flatMap fun c =>
        (List.finRange q).filterMap (fun d => lpsSLMatrixCandidate q a b c d)

theorem mem_lpsSLList (q : ℕ) [Fact q.Prime] (A : SL(2, ZMod q)) : A ∈ lpsSLList q := by
  let : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  let a : Fin q := ⟨(A.val 0 0).val, ZMod.val_lt _⟩
  let b : Fin q := ⟨(A.val 0 1).val, ZMod.val_lt _⟩
  let c : Fin q := ⟨(A.val 1 0).val, ZMod.val_lt _⟩
  let d : Fin q := ⟨(A.val 1 1).val, ZMod.val_lt _⟩
  have hM : lpsEntryMatrix q a b c d = A.val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lpsEntryMatrix, a, b, c, d]
  have hdet : (lpsEntryMatrix q a b c d).det = 1 := by rw [hM]; exact A.property
  simp only [lpsSLList, List.mem_flatMap]
  refine ⟨a, List.mem_finRange _, b, List.mem_finRange _, c, List.mem_finRange _, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨d, List.mem_finRange _, ?_⟩
  simp only [lpsSLMatrixCandidate, dif_pos hdet]
  congr 1
  exact Subtype.ext hM

def lpsPSLList (q : ℕ) [Fact q.Prime] : List PSL(2, ZMod q) :=
  letI := lpsPSLDecidableEq q
  ((lpsSLList q).map (fun A => (QuotientGroup.mk A : PSL(2, ZMod q)))).dedup

theorem lpsPSLList_nodup (q : ℕ) [Fact q.Prime] : (lpsPSLList q).Nodup := by
  let := lpsPSLDecidableEq q
  exact List.nodup_dedup _

theorem mem_lpsPSLList (q : ℕ) [Fact q.Prime] (x : PSL(2, ZMod q)) : x ∈ lpsPSLList q := by
  let := lpsPSLDecidableEq q
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
  rw [lpsPSLList, List.mem_dedup]
  exact List.mem_map.mpr ⟨A, mem_lpsSLList q A, rfl⟩

def lpsPSLEnumerationEquiv (q : ℕ) [Fact q.Prime] :
    Fin (lpsPSLList q).length ≃ PSL(2, ZMod q) :=
  letI := lpsPSLDecidableEq q
  List.Nodup.getEquivOfForallMemList (lpsPSLList q) (lpsPSLList_nodup q) (mem_lpsPSLList q)

theorem lpsPSLList_length (q : ℕ) [Fact q.Prime] (hqTwo : q ≠ 2) :
    (lpsPSLList q).length = q * (q ^ 2 - 1) / 2 := by
  have h := Fintype.card_congr (lpsPSLEnumerationEquiv q)
  simpa [card_psl_two_zmod q hqTwo] using h

def lpsPSLIndexMul (q : ℕ) [Fact q.Prime]
    (i j : Fin (lpsPSLList q).length) : Fin (lpsPSLList q).length :=
  (lpsPSLEnumerationEquiv q).symm
    ((lpsPSLEnumerationEquiv q) i * (lpsPSLEnumerationEquiv q) j)

def lpsPSLIndexInv (q : ℕ) [Fact q.Prime]
    (i : Fin (lpsPSLList q).length) : Fin (lpsPSLList q).length :=
  (lpsPSLEnumerationEquiv q).symm ((lpsPSLEnumerationEquiv q) i)⁻¹

def lpsPSLIndexOne (q : ℕ) [Fact q.Prime] : Fin (lpsPSLList q).length :=
  (lpsPSLEnumerationEquiv q).symm 1

theorem lpsPSLIndexMul_decode (q : ℕ) [Fact q.Prime]
    (i j : Fin (lpsPSLList q).length) :
    (lpsPSLEnumerationEquiv q) (lpsPSLIndexMul q i j) =
      (lpsPSLEnumerationEquiv q) i * (lpsPSLEnumerationEquiv q) j := by
  simp [lpsPSLIndexMul]

theorem lpsPSLIndexInv_decode (q : ℕ) [Fact q.Prime]
    (i : Fin (lpsPSLList q).length) :
    (lpsPSLEnumerationEquiv q) (lpsPSLIndexInv q i) =
      ((lpsPSLEnumerationEquiv q) i)⁻¹ := by
  simp [lpsPSLIndexInv]

def lpsQuaternionVertexIndex {p : ℕ} (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) : Fin (lpsPSLList a.q).length :=
  (lpsPSLEnumerationEquiv a.q).symm (lpsEffectiveQuaternionPSL a t ht)

theorem lpsQuaternionVertexIndex_decode {p : ℕ} (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    (lpsPSLEnumerationEquiv a.q) (lpsQuaternionVertexIndex a t ht) =
      lpsQuaternionPSL a t ht := by
  simp [lpsQuaternionVertexIndex, lpsEffectiveQuaternionPSL_eq]

/-- The computed inverse index multiplies back to the actual identity index. -/
theorem lpsPSLIndexInv_mul (q : ℕ) [Fact q.Prime]
    (i : Fin (lpsPSLList q).length) :
    lpsPSLIndexMul q (lpsPSLIndexInv q i) i = lpsPSLIndexOne q := by
  apply (lpsPSLEnumerationEquiv q).injective
  rw [lpsPSLIndexMul_decode, lpsPSLIndexInv_decode]
  simp [lpsPSLIndexOne]

end QEC.Coding.TannerLiftedProduct