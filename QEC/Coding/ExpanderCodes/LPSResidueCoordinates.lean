import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Find

/-!
# Computable finite-field quaternion coordinates

A finite encoded pair search computes x,y satisfying x²+y²+1=0. This
module supplies the root identity used by the actual LPS quaternion matrix.
The index bound is a finite search bound, not a full bit-complexity certificate.
-/

namespace QEC.Coding.TannerLiftedProduct

/-- Finite encoded pair test for the quaternion residue coordinates. -/
def lpsResiduePairCandidate (q n : ℕ) : Prop :=
  n < q ^ 2 ∧
    ((n / q : ℕ) : ZMod q) ^ 2 + ((n % q : ℕ) : ZMod q) ^ 2 + 1 = 0

instance (q : ℕ) : DecidablePred (lpsResiduePairCandidate q) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem exists_lpsResiduePairCandidate (q : ℕ) [Fact q.Prime] :
    ∃ n, lpsResiduePairCandidate q n := by
  let : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨x, y, hxy⟩ := ZMod.sq_add_sq q (-1)
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  refine ⟨x.val * q + y.val, ?_, ?_⟩
  · have hx' : x.val + 1 ≤ q := by omega
    calc
      x.val * q + y.val < x.val * q + q := by omega
      _ = (x.val + 1) * q := by ring
      _ ≤ q * q := Nat.mul_le_mul_right q hx'
      _ = q ^ 2 := by ring
  · have hDiv : (x.val * q + y.val) / q = x.val := by
      rw [Nat.add_div (by omega)]
      simp [Nat.div_eq_of_lt hy, Nat.mod_eq_of_lt hy, Nat.not_le_of_lt hy, Nat.mul_div_cancel _ hq]
    have hMod : (x.val * q + y.val) % q = y.val := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt hy]
    rw [hDiv, hMod, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    linear_combination hxy

/-- A finite search with erased existence proof, using a real decidable predicate. -/
def lpsEffectiveResiduePairIndex (q : ℕ) [Fact q.Prime] : ℕ :=
  Nat.find (exists_lpsResiduePairCandidate q)

def lpsEffectiveResidueX (q : ℕ) [Fact q.Prime] : ZMod q :=
  (lpsEffectiveResiduePairIndex q / q : ℕ)

def lpsEffectiveResidueY (q : ℕ) [Fact q.Prime] : ZMod q :=
  (lpsEffectiveResiduePairIndex q % q : ℕ)

theorem lpsEffectiveResiduePairIndex_lt_sq (q : ℕ) [Fact q.Prime] :
    lpsEffectiveResiduePairIndex q < q ^ 2 :=
  (Nat.find_spec (exists_lpsResiduePairCandidate q)).1

theorem lpsEffectiveResidueX_sq_add_lpsEffectiveResidueY_sq_add_one
    (q : ℕ) [Fact q.Prime] :
    lpsEffectiveResidueX q ^ 2 + lpsEffectiveResidueY q ^ 2 + 1 = 0 :=
  (Nat.find_spec (exists_lpsResiduePairCandidate q)).2

end QEC.Coding.TannerLiftedProduct
