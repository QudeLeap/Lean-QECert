import QEC.Coding.AlgebraicGeometry.Places.HeightOneOrder
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Redundant field steps on actual integral models

A degree-one extension has unit different and ramification index one at
every supplied prime. This treats the redundant cells in a compositum grid.
-/

namespace QEC.Coding.AlgebraicGeometry

noncomputable section

variable (B C K L : Type*) [CommRing B] [CommRing C] [Field K] [Field L]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra B C] [Algebra C L] [IsFractionRing C L] [IsScalarTower B C L]
    [Module.IsTorsionFree B C] [Module.Finite B C]
    [Algebra.IsSeparable K L]

include K L in
/-- A degree-one fraction-field extension has unit different on its actual
integral carrier; the proof uses the minimal polynomial of zero. -/
theorem differentIdeal_eq_top_of_finrank_eq_one
    (hdegree : Module.finrank K L = 1) : differentIdeal B C = ⊤ := by
  letI : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (by rw [hdegree]; norm_num)
  have hgen : Algebra.adjoin K ({algebraMap C L (0 : C)} : Set L) = ⊤ := by
    simpa using (Subalgebra.bot_eq_top_of_finrank_eq_one hdegree)
  have hmem := aeval_derivative_mem_differentIdeal B K L (0 : C) hgen
  have hminpoly : minpoly B (0 : C) = Polynomial.X := by
    simpa using minpoly.eq_X_sub_C_of_algebraMap_inj (0 : B)
      (FaithfulSMul.algebraMap_injective B C)
  apply (differentIdeal B C).eq_top_iff_one.mpr
  simpa only [hminpoly, Polynomial.derivative_X, map_one] using hmem

include K L in
/-- Both invariants of a redundant field step at the supplied upper prime. -/
theorem ramificationIdx_and_weakDifferent_of_finrank_eq_one
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (Q : IsDedekindDomain.HeightOneSpectrum C) [Q.asIdeal.LiesOver H.asIdeal]
    (hdegree : Module.finrank K L = 1) :
    H.asIdeal.ramificationIdx' Q.asIdeal = 1 ∧
      multiplicity Q.asIdeal (differentIdeal B C) =
        2 * (H.asIdeal.ramificationIdx' Q.asIdeal - 1) := by
  letI : NoZeroSMulDivisors B C := ⟨fun {_ _} h => smul_eq_zero.mp h⟩
  letI : H.asIdeal.IsMaximal := H.isPrime.isMaximal H.ne_bot
  letI : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (by rw [hdegree]; norm_num)
  have hepos : H.asIdeal.ramificationIdx' Q.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver Q.asIdeal H.ne_bot
  have hele : H.asIdeal.ramificationIdx' Q.asIdeal ≤ 1 :=
    (Ideal.ramificationIdx_le_finrank C K L Q.asIdeal).trans_eq hdegree
  have he : H.asIdeal.ramificationIdx' Q.asIdeal = 1 := by omega
  refine ⟨he, ?_⟩
  rw [differentIdeal_eq_top_of_finrank_eq_one B C K L hdegree, he,
    Nat.sub_self, Nat.mul_zero]
  apply multiplicity_eq_zero.mpr
  rw [Ideal.dvd_iff_le]
  intro h
  exact Q.isPrime.ne_top (top_unique h)

include K L in
/-- Orders agree under the actual inclusion in a degree-one field step. -/
theorem heightOnePlace_order_algebraMap_of_finrank_eq_one
    {k : Type*} [Field k] [Finite k] [Algebra k K] [Algebra k L]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (Q : IsDedekindDomain.HeightOneSpectrum C) [Q.asIdeal.LiesOver H.asIdeal]
    (hdegree : Module.finrank K L = 1) (x : K) :
    (heightOnePlace (k := k) (K := L) Q).order (algebraMap K L x) =
      (heightOnePlace (k := k) (K := K) H).order x := by
  by_cases hx : x = 0
  · simp [hx, GlobalPlace.order]
  · have he := (ramificationIdx_and_weakDifferent_of_finrank_eq_one
      B C K L H Q hdegree).1
    simpa only [he, Nat.cast_one, one_mul] using
      heightOnePlace_order_algebraMap (k := k) H Q x hx

end

end QEC.Coding.AlgebraicGeometry
