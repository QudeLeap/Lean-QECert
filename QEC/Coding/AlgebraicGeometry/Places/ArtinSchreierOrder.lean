import QEC.Coding.AlgebraicGeometry.Places.GlobalPlace
import Mathlib.Tactic.Ring

/-!
# Orders of quadratic Artin--Schreier coordinates

The normalized-place calculation needed by the degree-two refinement of
Garcia--Stichtenoth's Property (A). It uses the equation itself and the
ramification-index bound, without a separate degree-sixteen different model.
-/

namespace QEC.Coding.AlgebraicGeometry.GlobalPlace

variable {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L]

/-- A pole of a quadratic Artin--Schreier coordinate doubles its order in
the right-hand side: cancellation cannot occur between unequal orders. -/
theorem order_sq_add_of_neg (Q : GlobalPlace k L) (y : L)
    (hy : Q.order y < 0) : Q.order (y ^ 2 + y) = 2 * Q.order y := by
  have hy0 : y ≠ 0 := by
    intro h
    subst y
    simp [order] at hy
  have hv : Q.valuation y = WithZero.exp (-Q.order y) := by
    simp only [order, neg_neg]
    exact (WithZero.exp_log (Q.valuation.ne_zero_iff.mpr hy0)).symm
  have hv2 : Q.valuation (y ^ 2) = WithZero.exp (-2 * Q.order y) := by
    rw [map_pow, hv, ← WithZero.exp_nsmul]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  have hlt : Q.valuation y < Q.valuation (y ^ 2) := by
    rw [hv, hv2]
    exact WithZero.exp_lt_exp.mpr (by omega)
  change -WithZero.log (Q.valuation (y ^ 2 + y)) = _
  rw [Q.valuation.map_add_eq_of_lt_left hlt, hv2, WithZero.log_exp]
  ring

/-- For a quadratic extension, a normalized simple pole downstairs forces
both total ramification and a normalized simple pole of the root upstairs.
The order-compatibility hypothesis is the ordinary restriction formula for
the actual places; no different or pole conclusion is supplied as input. -/
theorem artinSchreier_root_order_of_simplePole [Algebra K L]
    (P : GlobalPlace k K) (Q : GlobalPlace k L) (a : K) (y : L)
    (e : ℕ) (he0 : 0 < e) (he2 : e ≤ 2)
    (hy : y ^ 2 + y = algebraMap K L a)
    (horder : Q.order (algebraMap K L a) = (e : ℤ) * P.order a)
    (ha : P.order a = -1) : e = 2 ∧ Q.order y = -1 := by
  have ha0 : a ≠ 0 := by
    intro h
    subst a
    simp [order] at ha
  have hmap0 : algebraMap K L a ≠ 0 :=
    by simpa only [map_zero] using (algebraMap K L).injective.ne ha0
  have hrhs : Q.order (y ^ 2 + y) = -(e : ℤ) := by
    rw [hy, horder, ha]
    ring
  have hneg : Q.order y < 0 := by
    by_contra hn
    have hregular : Q.RegularAt y := by
      by_cases hzero : y = 0
      · simp [hzero, RegularAt]
      · exact (Q.regularAt_iff_order_nonnegative hzero).mpr (by omega)
    have hmem := (Q.regularAt_iff_mem_valuationRing y).mp hregular
    have hsum := Q.valuationRing.add_mem
      (y ^ 2) y (Q.valuationRing.pow_mem hmem 2) hmem
    rw [hy] at hsum
    have hnonneg := (Q.regularAt_iff_order_nonnegative hmap0).mp
      ((Q.regularAt_iff_mem_valuationRing _).mpr hsum)
    rw [horder, ha] at hnonneg
    omega
  rw [Q.order_sq_add_of_neg y hneg] at hrhs
  omega

/-- Regular right-hand sides have regular roots at every upper place.
This applies to each stage, not merely to a selected extension of a place. -/
theorem artinSchreier_root_order_nonnegative (Q : GlobalPlace k L)
    (y : L) (ha : 0 ≤ Q.order (y ^ 2 + y)) : 0 ≤ Q.order y := by
  by_contra hn
  have hneg : Q.order y < 0 := by omega
  rw [Q.order_sq_add_of_neg y hneg] at ha
  omega

/-- The dichotomy used to initialize the source's refined basic edges is
preserved by a degree-at-most-two Artin--Schreier step. -/
theorem artinSchreier_root_order_dichotomy [Algebra K L]
    (P : GlobalPlace k K) (Q : GlobalPlace k L) (a : K) (y : L)
    (e : ℕ) (he0 : 0 < e) (he2 : e ≤ 2)
    (hy : y ^ 2 + y = algebraMap K L a)
    (horder : Q.order (algebraMap K L a) = (e : ℤ) * P.order a)
    (ha : P.order a = -1 ∨ 0 ≤ P.order a) :
    Q.order y = -1 ∨ 0 ≤ Q.order y := by
  rcases ha with hpole | hregular
  · exact Or.inl (P.artinSchreier_root_order_of_simplePole Q a y e
      he0 he2 hy horder hpole).2
  · apply Or.inr
    apply Q.artinSchreier_root_order_nonnegative
    rw [hy, horder]
    exact mul_nonneg (Nat.cast_nonneg e) hregular

end QEC.Coding.AlgebraicGeometry.GlobalPlace
