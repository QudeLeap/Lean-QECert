import QEC.Semantics.Dynamics.FourBlockGenerator

/-! # Trace bounds for a finite jump family from its actual square sum -/

namespace QEC.Semantics.Davies

open Classical
open scoped BigOperators
noncomputable section

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]

/-- The actual sum of jump adjoint-squares. -/
def squareSum (J : κ → Operator V) : Operator V := ∑ a, LinearMap.adjoint (J a) * J a

theorem gain_positive (J : κ → Operator V) (F : Operator V) (hF : F.IsPositive) :
    (lindbladJumpGain J F).IsPositive := by
  apply LinearMap.isPositive_sum Finset.univ
  intro a _
  exact hF.conj_adjoint (J a)

theorem trace_gain (J : κ → Operator V) (F : Operator V) :
    LinearMap.trace ℂ V (lindbladJumpGain J F) =
      LinearMap.trace ℂ V (squareSum J * F) := by
  simp only [lindbladJumpGain_apply, squareSum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [LinearMap.trace_mul_comm]
  simp only [mul_assoc]

theorem gain_traceNorm_le_positive (J : κ → Operator V) (F : Operator V)
    (hF : F.IsPositive) :
    traceNorm (lindbladJumpGain J F) ≤ operatorNorm (squareSum J) * traceNorm F := by
  rw [traceNorm_eq_re_trace_of_positive _ (gain_positive J F hF), trace_gain]
  exact (Complex.re_le_norm _).trans ((norm_trace_le_traceNorm _).trans
    (traceNorm_mul_left_le _ _))

theorem traceNorm_neg (F : Operator V) : traceNorm (-F) = traceNorm F := by
  rw [show -F = (-1 : ℂ) • F by simp, traceNorm_smul]
  simp

theorem traceNorm_sub_le (F G : Operator V) :
    traceNorm (F-G) ≤ traceNorm F + traceNorm G := by
  simpa only [sub_eq_add_neg, traceNorm_neg] using traceNorm_add_le F (-G)

theorem gain_traceNorm_le (J : κ → Operator V) (F : Operator V)
    (hF : F.IsSymmetric) :
    traceNorm (lindbladJumpGain J F) ≤ operatorNorm (squareSum J) * traceNorm F := by
  calc
    traceNorm (lindbladJumpGain J F) =
        traceNorm (lindbladJumpGain J (positivePart F) -
          lindbladJumpGain J (negativePart F)) := by
      rw [← map_sub, positivePart_sub_negativePart F hF]
    _ ≤ traceNorm (lindbladJumpGain J (positivePart F)) +
        traceNorm (lindbladJumpGain J (negativePart F)) := traceNorm_sub_le _ _
    _ ≤ operatorNorm (squareSum J) * traceNorm (positivePart F) +
        operatorNorm (squareSum J) * traceNorm (negativePart F) :=
      add_le_add (gain_traceNorm_le_positive J _ (positivePart_positive F))
        (gain_traceNorm_le_positive J _ (negativePart_positive F))
    _ = operatorNorm (squareSum J) * traceNorm F := by
      rw [traceNorm_eq_sum_parts F hF, mul_add]

theorem dissipator_eq_gain_sub (J : κ → Operator V) (F : Operator V) :
    lindbladDissipator J F = lindbladJumpGain J F -
      (2 : ℂ)⁻¹ • (squareSum J * F + F * squareSum J) := by
  simp only [lindbladDissipator_apply, lindbladJumpTerm_apply,
    lindbladJumpGain_apply, squareSum, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_sub_distrib, smul_add, Finset.sum_add_distrib, Finset.smul_sum]

theorem dissipator_traceNorm_le_squareSum (J : κ → Operator V) (F : Operator V)
    (hF : F.IsSymmetric) :
    traceNorm (lindbladDissipator J F) ≤ 2 * operatorNorm (squareSum J) * traceNorm F := by
  rw [dissipator_eq_gain_sub]
  apply (traceNorm_sub_le _ _).trans
  have hgain := gain_traceNorm_le J F hF
  have hloss : traceNorm ((2 : ℂ)⁻¹ • (squareSum J * F + F * squareSum J)) ≤
      operatorNorm (squareSum J) * traceNorm F := by
    rw [traceNorm_smul]
    have hsum := (traceNorm_add_le (squareSum J * F) (F * squareSum J)).trans
      (add_le_add (traceNorm_mul_left_le _ _) (traceNorm_mul_right_le _ _))
    norm_num at *
    linarith
  linarith

/-- Ordinary finite-family bound, later applied to the spectral square sum. -/
theorem dissipatorNorm_le_squareSum (J : κ → Operator V) :
    lindbladDissipatorNorm J ≤ 2 * operatorNorm (squareSum J) := by
  apply csSup_le
  · refine ⟨0, 0, ?_, ?_, ?_⟩
    · intro x y; simp
    · rw [(traceNorm_eq_zero_iff _).mpr rfl]; norm_num
    · rw [map_zero, (traceNorm_eq_zero_iff _).mpr rfl]
  · rintro r ⟨F,hF,hFn,rfl⟩
    exact (dissipator_traceNorm_le_squareSum J F hF).trans
      (by nlinarith [operatorNorm_nonneg (squareSum J)])

end
end QEC.Semantics.Davies
