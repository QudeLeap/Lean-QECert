import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Coefficient equivalences of rational-function fields

A coefficient-field equivalence extends to the corresponding rational
function fields while fixing the indeterminate.  The explicit construction
is useful for constant-field descent in the Cartwright--Steger algebra.
-/

namespace RatFunc

/-- Apply a field equivalence coefficientwise to rational functions. -/
noncomputable def coefficientRingEquiv
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L) :
    RatFunc K ≃+* RatFunc L := by
  let ep : Polynomial K ≃+* Polynomial L := Polynomial.mapEquiv e
  let hnonzero : nonZeroDivisors (Polynomial K) ≤
      (nonZeroDivisors (Polynomial L)).comap ep :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective ep ep.injective
  let f : RatFunc K →+* RatFunc L := RatFunc.mapRingHom ep hnonzero
  apply RingEquiv.ofBijective f
  constructor
  · exact RatFunc.map_injective ep hnonzero ep.injective
  · intro x
    let p : Polynomial K := ep.symm x.num
    let q : Polynomial K := ep.symm x.denom
    refine ⟨algebraMap (Polynomial K) (RatFunc K) p /
        algebraMap (Polynomial K) (RatFunc K) q, ?_⟩
    change RatFunc.map ep hnonzero
        (algebraMap (Polynomial K) (RatFunc K) p /
          algebraMap (Polynomial K) (RatFunc K) q) = x
    rw [RatFunc.map_apply_div]
    change algebraMap (Polynomial L) (RatFunc L) (ep p) /
        algebraMap (Polynomial L) (RatFunc L) (ep q) = x
    rw [show ep p = x.num by simp [p], show ep q = x.denom by simp [q]]
    exact x.num_div_denom

@[simp] theorem coefficientRingEquiv_apply_div
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (p q : Polynomial K) :
    coefficientRingEquiv e
        (algebraMap (Polynomial K) (RatFunc K) p /
          algebraMap (Polynomial K) (RatFunc K) q) =
      algebraMap (Polynomial L) (RatFunc L) (Polynomial.mapEquiv e p) /
        algebraMap (Polynomial L) (RatFunc L) (Polynomial.mapEquiv e q) := by
  let ep : Polynomial K ≃+* Polynomial L := Polynomial.mapEquiv e
  let hnonzero : nonZeroDivisors (Polynomial K) ≤
      (nonZeroDivisors (Polynomial L)).comap ep :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective ep ep.injective
  change RatFunc.map ep hnonzero
      (algebraMap (Polynomial K) (RatFunc K) p /
        algebraMap (Polynomial K) (RatFunc K) q) = _
  exact RatFunc.map_apply_div ep hnonzero p q

/-- Normalized denominators are transported coefficientwise. -/
theorem denom_coefficientRingEquiv
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (x : RatFunc K) :
    (coefficientRingEquiv e x).denom =
      x.denom.map e.toRingHom := by
  let y := coefficientRingEquiv e x
  let P := x.num.map e.toRingHom
  let Q := x.denom.map e.toRingHom
  have hQ : Q ≠ 0 := Polynomial.map_ne_zero x.denom_ne_zero
  have hy : y = algebraMap (Polynomial L) (RatFunc L) P /
      algebraMap (Polynomial L) (RatFunc L) Q := by
    change coefficientRingEquiv e x = _
    rw [← x.num_div_denom]
    exact coefficientRingEquiv_apply_div e x.num x.denom
  have hcross : y.num * Q = P * y.denom :=
    (num_mul_eq_mul_denom_iff hQ).mpr hy
  have hPQ : IsCoprime P Q := by
    exact IsCoprime.map x.isCoprime_num_denom
      (Polynomial.mapRingHom e.toRingHom)
  have hyDenom_dvd_Q : y.denom ∣ Q := by
    apply y.isCoprime_num_denom.symm.dvd_of_dvd_mul_left
    exact ⟨P, by simpa [mul_comm] using hcross⟩
  have hQ_dvd_yDenom : Q ∣ y.denom := by
    apply hPQ.symm.dvd_of_dvd_mul_left
    exact ⟨y.num, by simpa [mul_comm] using hcross.symm⟩
  exact Polynomial.eq_of_monic_of_associated y.monic_denom
    (x.monic_denom.map e.toRingHom)
    (associated_of_dvd_dvd hyDenom_dvd_Q hQ_dvd_yDenom)

/-- Normalized numerators are transported coefficientwise. -/
theorem num_coefficientRingEquiv
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (x : RatFunc K) :
    (coefficientRingEquiv e x).num =
      x.num.map e.toRingHom := by
  let y := coefficientRingEquiv e x
  let P := x.num.map e.toRingHom
  let Q := x.denom.map e.toRingHom
  have hQ : Q ≠ 0 := Polynomial.map_ne_zero x.denom_ne_zero
  have hy : y = algebraMap (Polynomial L) (RatFunc L) P /
      algebraMap (Polynomial L) (RatFunc L) Q := by
    change coefficientRingEquiv e x = _
    rw [← x.num_div_denom]
    exact coefficientRingEquiv_apply_div e x.num x.denom
  have hcross : y.num * Q = P * y.denom :=
    (num_mul_eq_mul_denom_iff hQ).mpr hy
  rw [denom_coefficientRingEquiv e x] at hcross
  exact mul_right_cancel₀ hQ hcross

@[simp] theorem coefficientRingEquiv_C
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (a : K) :
    coefficientRingEquiv e (RatFunc.C a) = RatFunc.C (e a) := by
  rw [show RatFunc.C a = algebraMap (Polynomial K) (RatFunc K)
      (Polynomial.C a) / algebraMap (Polynomial K) (RatFunc K) 1 by simp,
    coefficientRingEquiv_apply_div]
  simp

@[simp] theorem coefficientRingEquiv_X
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L) :
    coefficientRingEquiv e (RatFunc.X : RatFunc K) = RatFunc.X := by
  rw [show (RatFunc.X : RatFunc K) = algebraMap (Polynomial K) (RatFunc K)
      Polynomial.X / algebraMap (Polynomial K) (RatFunc K) 1 by simp,
    coefficientRingEquiv_apply_div]
  simp

end RatFunc
