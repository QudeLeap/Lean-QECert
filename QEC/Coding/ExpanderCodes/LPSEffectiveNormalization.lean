import QEC.Coding.ExpanderCodes.LPSQuaternion
import Mathlib.Data.Nat.Find

/-!
# Computed normalization of actual LPS quaternion generators

The residue certificate proves that the degree has a nonzero square root.
A finite decidable search computes that root and a determinant-one matrix.
Its projective quotient is proved equal to the existing semantic generator.
Canonical quotient serialization and full runtime costs remain separate.
-/

namespace QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups

def lpsDegreeRootCandidate (a : LPSResiduePrime p) (n : ℕ) : Prop :=
  n < a.q ∧ ((n : ℕ) : ZMod a.q) ^ 2 = (p : ZMod a.q)

instance (a : LPSResiduePrime p) : DecidablePred (lpsDegreeRootCandidate a) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem exists_lpsDegreeRootCandidate (a : LPSResiduePrime p) :
    ∃ n, lpsDegreeRootCandidate a n := by
  let : NeZero a.q := ⟨a.prime.ne_zero⟩
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff' a.q a.degree_nonzero).mp a.residue
  refine ⟨r.val, ZMod.val_lt r, ?_⟩
  rw [ZMod.natCast_zmod_val]
  simpa [pow_two] using hr.symm

def lpsEffectiveDegreeRootIndex (a : LPSResiduePrime p) : ℕ :=
  Nat.find (exists_lpsDegreeRootCandidate a)

def lpsEffectiveDegreeRoot (a : LPSResiduePrime p) : ZMod a.q :=
  (lpsEffectiveDegreeRootIndex a : ℕ)

theorem lpsEffectiveDegreeRootIndex_lt (a : LPSResiduePrime p) :
    lpsEffectiveDegreeRootIndex a < a.q :=
  (Nat.find_spec (exists_lpsDegreeRootCandidate a)).1

theorem lpsEffectiveDegreeRoot_sq (a : LPSResiduePrime p) :
    lpsEffectiveDegreeRoot a ^ 2 = (p : ZMod a.q) :=
  (Nat.find_spec (exists_lpsDegreeRootCandidate a)).2

theorem lpsEffectiveDegreeRoot_ne_zero (a : LPSResiduePrime p) :
    lpsEffectiveDegreeRoot a ≠ 0 := by
  intro h
  have hs := lpsEffectiveDegreeRoot_sq a
  rw [h, zero_pow (by decide)] at hs
  exact a.degree_nonzero hs.symm

/-- Actual computed determinant-one matrix representative. -/
def lpsEffectiveQuaternionSL (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) : SL(2, ZMod a.q) :=
  ⟨(lpsEffectiveDegreeRoot a)⁻¹ • lpsQuaternionMatrix a.q t, by
    have hdet : (lpsQuaternionMatrix a.q t).det = (p : ZMod a.q) := by
      rw [det_lpsQuaternionMatrix, ht]
      norm_cast
    rw [Matrix.det_smul, hdet]
    simp only [Fintype.card_fin]
    rw [← lpsEffectiveDegreeRoot_sq a]
    simp [lpsEffectiveDegreeRoot_ne_zero a]⟩

def lpsEffectiveQuaternionPSL (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) : PSL(2, ZMod a.q) :=
  QuotientGroup.mk (lpsEffectiveQuaternionSL a t ht)

theorem toPGL_lpsEffectiveQuaternionPSL (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (lpsEffectiveQuaternionPSL a t ht) =
      lpsQuaternionPGL a t ht := by
  change Matrix.ProjGenLinGroup.mk
    (Matrix.SpecialLinearGroup.toGL (lpsEffectiveQuaternionSL a t ht)) =
      Matrix.ProjGenLinGroup.mk (lpsQuaternionGL a t ht)
  rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨Units.mk0 (lpsEffectiveDegreeRoot a) (lpsEffectiveDegreeRoot_ne_zero a), ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lpsEffectiveQuaternionSL, lpsQuaternionGL, Matrix.SpecialLinearGroup.toGL,
      Matrix.mul_apply, mul_comm, mul_assoc, lpsEffectiveDegreeRoot_ne_zero a]

theorem lpsEffectiveQuaternionPSL_eq (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    lpsEffectiveQuaternionPSL a t ht = lpsQuaternionPSL a t ht := by
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_lpsEffectiveQuaternionPSL, toPGL_lpsQuaternionPSL]

/-- The computed projective label respects quaternion conjugate inversion. -/
theorem lpsEffectiveQuaternionPSL_conj_eq_inv (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    lpsEffectiveQuaternionPSL a t.conj (by simpa using ht) =
      (lpsEffectiveQuaternionPSL a t ht)⁻¹ := by
  simp only [lpsEffectiveQuaternionPSL_eq]
  exact lpsQuaternionPSL_conj_eq_inv a t ht

end QEC.Coding.TannerLiftedProduct
