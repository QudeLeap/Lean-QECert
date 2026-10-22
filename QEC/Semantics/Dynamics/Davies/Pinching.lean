import QEC.Semantics.Dynamics.Davies.Spectral
import QEC.Semantics.Dynamics.Davies.TraceBound

/-! # Spectral pinching and the frequency-independent square-sum bound -/

namespace QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Zero-frequency extraction is the sum of compressions to full energy spaces. -/
theorem frequencyComponent_zero_eq_pinching (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (A : Operator V) :
    frequencyComponent b e A 0 = ∑ E ∈ energyValues e,
      energyProjector b e E * A * energyProjector b e E := by
  rw [frequencyComponent_eq_projector_sum]
  apply Finset.sum_congr rfl
  intro E hE
  simp [sub_eq_zero, hE]

theorem frequencyComponent_zero_positive (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (A : Operator V) (hA : A.IsPositive) :
    (frequencyComponent b e A 0).IsPositive := by
  rw [frequencyComponent_zero_eq_pinching]
  apply LinearMap.isPositive_sum
  intro E _
  have h := hA.conj_adjoint (energyProjector b e E)
  have he : energyProjector b e E * A * energyProjector b e E =
      energyProjector b e E ∘ₗ A ∘ₗ LinearMap.adjoint (energyProjector b e E) := by
    ext x
    simp only [Module.End.mul_apply, LinearMap.comp_apply, energyProjector_adjoint]
  rw [he]
  exact h

/-- Cross terms between different output energies disappear, while terms inside
a degenerate output energy remain together. -/
theorem sum_frequency_adjoint_square (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (A : Operator V) :
    (∑ ω : Frequency e, LinearMap.adjoint (frequencyComponent b e A ω.val) *
      frequencyComponent b e A ω.val) =
      frequencyComponent b e (LinearMap.adjoint A * A) 0 := by
  apply entry_ext b
  intro i j
  simp only [entry_sum, entry_mul, entry_adjoint, entry_frequencyComponent]
  rw [Finset.sum_comm]
  have hs : (if e j-e i = 0 then ∑ k, star (entry b A k i) * entry b A k j else 0) =
      ∑ k, if e j-e i = 0 then star (entry b A k i) * entry b A k j else 0 := by
    split_ifs <;> simp
  rw [hs]
  apply Finset.sum_congr rfl
  intro k _
  let w : Frequency e := ⟨e i-e k, (mem_frequencies _ _).mpr ⟨k,i,rfl⟩⟩
  rw [Finset.sum_eq_single w]
  · dsimp [w]
    by_cases he : e i = e j
    · simp [he]
    · have hd : e j-e k ≠ e i-e k := by intro h; apply he; linarith
      simp [he, Ne.symm he, hd, sub_eq_zero]
  · intro z _ hzw
    have hz : e i-e k ≠ z.val := by
      intro h
      exact hzw (Subtype.ext h.symm)
    simp [hz]
  · simp

theorem frequencyComponent_one_zero (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) :
    frequencyComponent b e 1 0 = 1 := by
  apply entry_ext b
  intro i j
  simp only [entry_frequencyComponent, entry_one]
  by_cases h : i = j
  · subst j; simp
  · simp [h]

theorem one_sub_adjoint_square_positive (A : Operator V) (hA : operatorNorm A ≤ 1) :
    (1 - LinearMap.adjoint A * A).IsPositive := by
  constructor
  · exact (LinearMap.isPositive_one : (1 : Operator V).IsPositive).isSymmetric.sub
      (LinearMap.isSymmetric_adjoint_mul_self A)
  · intro x
    change 0 ≤ (inner ℂ (x - LinearMap.adjoint A (A x)) x).re
    rw [inner_sub_left, Complex.sub_re, LinearMap.adjoint_inner_left]
    rw [show (inner ℂ x x).re = ‖x‖^2 from inner_self_eq_norm_sq (𝕜 := ℂ) x,
      show (inner ℂ (A x) (A x)).re = ‖A x‖^2 from inner_self_eq_norm_sq (𝕜 := ℂ) (A x)]
    have hnorm : ‖A x‖ ≤ ‖x‖ := by
      have h := (LinearMap.toContinuousLinearMap A).le_opNorm x
      exact h.trans (by simpa [operatorNorm] using mul_le_mul_of_nonneg_right hA (norm_nonneg x))
    nlinarith [norm_nonneg x, norm_nonneg (A x)]

theorem one_sub_frequency_squareSum_positive (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (A : Operator V) (hA : operatorNorm A ≤ 1) :
    (1 - squareSum (fun ω : Frequency e => frequencyComponent b e A ω.val)).IsPositive := by
  rw [squareSum, sum_frequency_adjoint_square,
    ← frequencyComponent_one_zero b e, ← frequencyComponent_sub]
  exact frequencyComponent_zero_positive b e _ (one_sub_adjoint_square_positive A hA)

end
end QEC.Semantics.Davies
