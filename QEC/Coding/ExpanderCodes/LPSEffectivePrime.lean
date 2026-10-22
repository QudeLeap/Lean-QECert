import QEC.Coding.ExpanderCodes.LPSFamily
import QEC.Coding.ExpanderCodes.LPSEffectiveNormalization
import QEC.Coding.ExpanderCodes.LPSVertexEnumeration

/-!
# Effective LPS residue-prime selection

A terminating least-prime search replaces dynamic classical choice. The
instrumented bounded scan proves the exact number of predicate queries at
its first successful candidate. This is a query count, not a bit-complexity
certificate for prime testing or for sparse CSS output.
-/

namespace QEC.Coding.TannerLiftedProduct

/-- The effective selector consumes the original computed source-compatible sequence. -/
def lpsEffectiveResiduePrimeAt {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) : LPSResiduePrime p :=
  lpsResiduePrimeAt hp hp4 B

@[simp] theorem lpsEffectiveResiduePrimeAt_q {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) :
    (lpsEffectiveResiduePrimeAt hp hp4 B).q = lpsLeastPrimeAbove hp B := rfl

theorem lt_lpsEffectiveResiduePrimeAt_q {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) :
    B < (lpsEffectiveResiduePrimeAt hp hp4 B).q :=
  lt_lpsResiduePrimeAt hp hp4 B

/-- Both actual family carriers use exactly the same computed arithmetic certificate. -/
theorem lpsEffectiveResiduePrimeAt_eq_sequence {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    lpsEffectiveResiduePrimeAt hp hp4 n = lpsResiduePrimeSequence hp hp4 n := rfl

/-- Instrumented increasing candidate scan. Once successful, later steps retain
both the returned prime and the completed query count. -/
def lpsPrimeScan (p B : ℕ) : ℕ → Option ℕ × ℕ
  | 0 => (none, 0)
  | n + 1 =>
      let prev := lpsPrimeScan p B n
      match prev.1 with
      | some _ => prev
      | none => (if lpsPrimeCandidate p B n then some n else none, prev.2 + 1)

theorem lpsPrimeScan_eq_none_of_forall (p B n : ℕ)
    (h : ∀ q < n, ¬ lpsPrimeCandidate p B q) :
    lpsPrimeScan p B n = (none, n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [lpsPrimeScan, ih (fun q hq => h q (by omega))]
      simp [h n (by omega)]

/-- The measured scan actually returns the computed prime, in precisely q+1
candidate queries; it does not assume an output or a query bound. -/
theorem lpsPrimeScan_leastPrime {p : ℕ} (hp : p.Prime) (B : ℕ) :
    lpsPrimeScan p B (lpsLeastPrimeAbove hp B + 1) =
      (some (lpsLeastPrimeAbove hp B), lpsLeastPrimeAbove hp B + 1) := by
  have hNone : lpsPrimeScan p B (lpsLeastPrimeAbove hp B) =
      (none, lpsLeastPrimeAbove hp B) :=
    lpsPrimeScan_eq_none_of_forall p B _
      (fun q hq => Nat.find_min (exists_lpsPrimeCandidate hp B) hq)
  rw [lpsPrimeScan, hNone]
  simp [lpsLeastPrimeAbove_spec hp B]

open scoped MatrixGroups

/-- A coarse cardinal bound from the proved exact PSL order. -/
theorem LPSResiduePrime.q_le_two_mul_card_psl {p : ℕ}
    (a : LPSResiduePrime p) :
    a.q ≤ 2 * Fintype.card PSL(2, ZMod a.q) := by
  have hsq : 1 ≤ a.q ^ 2 - 1 := by
    have hq := a.prime.two_le
    have hPow := Nat.pow_le_pow_left hq 2
    norm_num at hPow
    omega
  calc
    a.q = a.q * 1 := by simp
    _ ≤ a.q * (a.q ^ 2 - 1) := Nat.mul_le_mul_left a.q hsq
    _ = 2 * Fintype.card PSL(2, ZMod a.q) := a.two_mul_card_psl.symm

/-- The candidate count is linear in the actual PSL output carrier size.
Arithmetic bit costs and sparse-matrix emission still need separate proofs. -/
theorem lpsPrimeScan_queries_le_two_card_psl_add_one {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) :
    (lpsPrimeScan p B ((lpsEffectiveResiduePrimeAt hp hp4 B).q + 1)).2 ≤
      2 * Fintype.card PSL(2, ZMod (lpsEffectiveResiduePrimeAt hp hp4 B).q) + 1 := by
  have hScan := lpsPrimeScan_leastPrime hp B
  rw [← lpsEffectiveResiduePrimeAt_q hp hp4 B] at hScan
  rw [hScan]
  exact Nat.add_le_add_right
    (lpsEffectiveResiduePrimeAt hp hp4 B).q_le_two_mul_card_psl 1

/-- The genuine finite LPS vertex group with the computed quotient prime. -/
abbrev LPSEffectiveVertexGroup {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :=
  PSL(2, ZMod (lpsEffectiveResiduePrimeAt hp hp4 n).q)

/-- These computed-prime groups have unbounded cardinality. -/
theorem lpsEffectiveVertexGroup_card_cofinal {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) :
    ∀ N : ℕ, ∃ n, N ≤ Fintype.card (LPSEffectiveVertexGroup hp hp4 n) := by
  intro N
  refine ⟨2 * N, ?_⟩
  have hLarge := lt_lpsEffectiveResiduePrimeAt_q hp hp4 (2 * N)
  have hCard := (lpsEffectiveResiduePrimeAt hp hp4 (2 * N)).q_le_two_mul_card_psl
  change N ≤ Fintype.card PSL(2, ZMod (lpsEffectiveResiduePrimeAt hp hp4 (2 * N)).q)
  omega

/-- The computed normalized quaternion label of the computed-prime graph.
Numeric family indices below serialize this label into actual PSL vertices. -/
def lpsEffectiveQuaternionFamilyLabel {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    LPSGeneratorIndex p → LPSEffectiveVertexGroup hp hp4 n :=
  fun t => lpsEffectiveQuaternionPSL (lpsEffectiveResiduePrimeAt hp hp4 n) t.1
    (norm_eq_of_mem_lpsQuaternionShell hp.pos t.2)

/-- Computation preserves the actual semantic label at the computed prime. -/
theorem lpsEffectiveQuaternionFamilyLabel_eq {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    lpsEffectiveQuaternionFamilyLabel hp hp4 n =
      lpsQuaternionLabel (lpsEffectiveResiduePrimeAt hp hp4 n) := by
  funext t
  exact lpsEffectiveQuaternionPSL_eq _ t.1 _

theorem lpsEffectiveQuaternionFamilyLabel_injective {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    Function.Injective (lpsEffectiveQuaternionFamilyLabel hp hp4 n) := by
  rw [lpsEffectiveQuaternionFamilyLabel_eq]
  exact lpsQuaternionLabel_injective (lpsEffectiveResiduePrimeAt hp hp4 n)

/-- The computed finite vertex index of an effective-prime generator. -/
def lpsEffectiveQuaternionFamilyIndex {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    LPSGeneratorIndex p → Fin (lpsPSLList (lpsEffectiveResiduePrimeAt hp hp4 n).q).length :=
  fun t => lpsQuaternionVertexIndex (lpsEffectiveResiduePrimeAt hp hp4 n) t.1
    (norm_eq_of_mem_lpsQuaternionShell hp.pos t.2)

/-- Computed vertex numbering decodes to the actual effective family label. -/
theorem lpsEffectiveQuaternionFamilyIndex_decode {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) (t : LPSGeneratorIndex p) :
    (lpsPSLEnumerationEquiv (lpsEffectiveResiduePrimeAt hp hp4 n).q)
      (lpsEffectiveQuaternionFamilyIndex hp hp4 n t) =
        lpsEffectiveQuaternionFamilyLabel hp hp4 n t := by
  exact (lpsPSLEnumerationEquiv _).apply_symm_apply _

/-- Distinct actual directions receive distinct computed vertex indices. -/
theorem lpsEffectiveQuaternionFamilyIndex_injective {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    Function.Injective (lpsEffectiveQuaternionFamilyIndex hp hp4 n) := by
  intro x y h
  apply lpsEffectiveQuaternionFamilyLabel_injective hp hp4 n
  have hDecode := congrArg
    (lpsPSLEnumerationEquiv (lpsEffectiveResiduePrimeAt hp hp4 n).q) h
  simpa only [lpsEffectiveQuaternionFamilyIndex_decode] using hDecode

/-- The computed normalized labels are the semantic labels of the original family. -/
theorem lpsEffectiveQuaternionFamilyLabel_eq_original {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    lpsEffectiveQuaternionFamilyLabel hp hp4 n = lpsQuaternionFamilyLabel hp hp4 n :=
  lpsEffectiveQuaternionFamilyLabel_eq hp hp4 n

/-- Computed indices decode directly into the original cofinal semantic family. -/
theorem lpsEffectiveQuaternionFamilyIndex_decode_original {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) (t : LPSGeneratorIndex p) :
    (lpsPSLEnumerationEquiv (lpsResiduePrimeSequence hp hp4 n).q)
        (lpsEffectiveQuaternionFamilyIndex hp hp4 n t) =
      lpsQuaternionFamilyLabel hp hp4 n t := by
  exact (lpsEffectiveQuaternionFamilyIndex_decode hp hp4 n t).trans
    (congrFun (lpsEffectiveQuaternionFamilyLabel_eq_original hp hp4 n) t)

end QEC.Coding.TannerLiftedProduct
