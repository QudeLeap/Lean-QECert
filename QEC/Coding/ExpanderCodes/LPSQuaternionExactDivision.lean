import QEC.Coding.ExpanderCodes.LPSTraceNormalForm

/-!
# Exact coordinate division for integral LPS quaternions

The existence step in the LPS quaternion normal form repeatedly divides a
quaternion product by the degree prime.  This file supplies the elementary
integral algebra for that step: coordinate divisibility, exact quotient,
norm descent, and cancellation against a prime-norm right factor.
-/

namespace QEC.Coding.TannerLiftedProduct

variable {p : ℕ}

/-- Every coordinate of an integral quaternion is divisible by `s`. -/
def LPSQuaternion.CoordinatesDvd (s : ℤ) (t : LPSQuaternion) : Prop :=
  s ∣ t.a ∧ s ∣ t.b ∧ s ∣ t.c ∧ s ∣ t.d

/-- Coordinatewise Euclidean quotient.  The intended use always supplies a
proof that all four divisions are exact. -/
def lpsQuaternionDiv (s : ℤ) (t : LPSQuaternion) : LPSQuaternion where
  a := t.a / s
  b := t.b / s
  c := t.c / s
  d := t.d / s

/-- Exact coordinate division is inverse to coordinatewise scaling. -/
theorem lpsScaleQuaternion_div_eq
    {s : ℤ} {t : LPSQuaternion} (h : t.CoordinatesDvd s) :
    lpsScaleQuaternion s (lpsQuaternionDiv s t) = t := by
  apply LPSQuaternion.ext
  · simpa only [lpsScaleQuaternion, lpsQuaternionDiv, mul_comm] using
      Int.ediv_mul_cancel h.1
  · simpa only [lpsScaleQuaternion, lpsQuaternionDiv, mul_comm] using
      Int.ediv_mul_cancel h.2.1
  · simpa only [lpsScaleQuaternion, lpsQuaternionDiv, mul_comm] using
      Int.ediv_mul_cancel h.2.2.1
  · simpa only [lpsScaleQuaternion, lpsQuaternionDiv, mul_comm] using
      Int.ediv_mul_cancel h.2.2.2

/-- Scaling by a nonzero integer is injective on integral quaternions. -/
theorem lpsScaleQuaternion_injective {s : ℤ} (hs : s ≠ 0) :
    Function.Injective (lpsScaleQuaternion s) := by
  intro t u h
  apply LPSQuaternion.ext
  · exact mul_left_cancel₀ hs (congrArg LPSQuaternion.a h)
  · exact mul_left_cancel₀ hs (congrArg LPSQuaternion.b h)
  · exact mul_left_cancel₀ hs (congrArg LPSQuaternion.c h)
  · exact mul_left_cancel₀ hs (congrArg LPSQuaternion.d h)

/-- Coordinatewise scaling commutes with multiplication on the left. -/
theorem lpsScaleQuaternion_mul_left
    (s : ℤ) (t u : LPSQuaternion) :
    lpsScaleQuaternion s (t * u) = lpsScaleQuaternion s t * u := by
  apply LPSQuaternion.ext <;>
    simp [lpsScaleQuaternion] <;> ring

/-- Coordinatewise scaling commutes with multiplication on the right. -/
theorem lpsScaleQuaternion_mul_right
    (s : ℤ) (t u : LPSQuaternion) :
    lpsScaleQuaternion s (t * u) = t * lpsScaleQuaternion s u := by
  apply LPSQuaternion.ext <;>
    simp [lpsScaleQuaternion] <;> ring

/-- Quaternion conjugation times the original quaternion is the central
scalar given by its reduced norm. -/
theorem LPSQuaternion.conj_mul_self (t : LPSQuaternion) :
    t.conj * t = lpsScaleQuaternion t.norm 1 := by
  apply LPSQuaternion.ext <;>
    simp [lpsScaleQuaternion, LPSQuaternion.norm] <;> ring

/-- The right-handed version of the norm identity. -/
theorem LPSQuaternion.mul_conj_self (t : LPSQuaternion) :
    t * t.conj = lpsScaleQuaternion t.norm 1 := by
  apply LPSQuaternion.ext <;>
    simp [lpsScaleQuaternion, LPSQuaternion.norm] <;> ring

/-- Dividing all coordinates by `p` lowers a norm `p^(n+2)` to `p^n`. -/
theorem norm_lpsQuaternionDiv_of_prime_pow
    (hp : p.Prime) {n : ℕ} {t : LPSQuaternion}
    (hdiv : t.CoordinatesDvd (p : ℤ))
    (hnorm : t.norm = (p : ℤ) ^ (n + 2)) :
    (lpsQuaternionDiv (p : ℤ) t).norm = (p : ℤ) ^ n := by
  let u := lpsQuaternionDiv (p : ℤ) t
  have hscale : lpsScaleQuaternion (p : ℤ) u = t :=
    lpsScaleQuaternion_div_eq hdiv
  have hnormScale := congrArg LPSQuaternion.norm hscale
  rw [norm_lpsScaleQuaternion, hnorm] at hnormScale
  have hpSqNe : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  apply mul_left_cancel₀ hpSqNe
  calc
    (p : ℤ) ^ 2 * (lpsQuaternionDiv (p : ℤ) t).norm =
        (p : ℤ) ^ (n + 2) := hnormScale
    _ = (p : ℤ) ^ 2 * (p : ℤ) ^ n := by ring

/-- If `t * β̄` is coordinatewise divisible by `p` and `β` has norm `p`,
the exact quotient is a genuine right factorization of `t`. -/
theorem lpsQuaternionDiv_mul_conj_mul_eq
    (hp : p.Prime) {t beta : LPSQuaternion}
    (hbeta : beta.norm = p)
    (hdiv : (t * beta.conj).CoordinatesDvd (p : ℤ)) :
    lpsQuaternionDiv (p : ℤ) (t * beta.conj) * beta = t := by
  apply lpsScaleQuaternion_injective (s := (p : ℤ))
    (by exact_mod_cast hp.ne_zero)
  rw [lpsScaleQuaternion_mul_left,
    lpsScaleQuaternion_div_eq hdiv]
  rw [mul_assoc, beta.conj_mul_self, hbeta]
  apply LPSQuaternion.ext <;>
    simp [lpsScaleQuaternion, mul_comm]

/-- The quotient in the preceding right factorization has norm one lower
power of `p`. -/
theorem norm_lpsQuaternionDiv_mul_conj
    (hp : p.Prime) {n : ℕ} {t beta : LPSQuaternion}
    (ht : t.norm = (p : ℤ) ^ (n + 1))
    (hbeta : beta.norm = p)
    (hdiv : (t * beta.conj).CoordinatesDvd (p : ℤ)) :
    (lpsQuaternionDiv (p : ℤ) (t * beta.conj)).norm =
      (p : ℤ) ^ n := by
  let u := lpsQuaternionDiv (p : ℤ) (t * beta.conj)
  have hfactor : u * beta = t :=
    lpsQuaternionDiv_mul_conj_mul_eq hp hbeta hdiv
  have hnorm := congrArg LPSQuaternion.norm hfactor
  rw [LPSQuaternion.norm_mul, ht, hbeta] at hnorm
  have hpNe : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  apply mul_right_cancel₀ hpNe
  calc
    (lpsQuaternionDiv (p : ℤ) (t * beta.conj)).norm * (p : ℤ) =
        (p : ℤ) ^ (n + 1) := hnorm
    _ = (p : ℤ) ^ n * (p : ℤ) := by rw [pow_succ]

end QEC.Coding.TannerLiftedProduct
