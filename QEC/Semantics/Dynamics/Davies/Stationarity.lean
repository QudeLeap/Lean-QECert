import QEC.Semantics.Dynamics.Davies.Spectral

/-! # Gibbs intertwining for coherent spectral frequency components -/

namespace QEC.Semantics.Davies

open Classical ThermalEncoding
open scoped BigOperators
noncomputable section

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The existing Gibbs density is the diagonal spectral operator, with one
Boltzmann weight for each basis vector, including spectral multiplicity. -/
theorem spectralGibbsDensity_diagonal (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (β : ℝ) :
    (spectralGibbsDensity b e β).toOperator = diagonal b (gibbsProbability β e) := rfl

theorem gibbsProbability_gap (e : ι → ℝ) (β : ℝ) (i j : ι) :
    gibbsProbability β e j = Real.exp (-β * (e j-e i)) * gibbsProbability β e i := by
  unfold gibbsProbability
  rw [← mul_div_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The frequency sign matches energy transferred from the system to the bath. -/
theorem frequencyComponent_gibbs (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (β ω : ℝ) (A : Operator V) :
    frequencyComponent b e A ω * (spectralGibbsDensity b e β).toOperator =
      (Real.exp (-β * ω) : ℂ) •
        ((spectralGibbsDensity b e β).toOperator * frequencyComponent b e A ω) := by
  rw [spectralGibbsDensity_diagonal]
  apply entry_ext b
  intro i j
  simp only [entry_mul_diagonal, entry_smul, entry_diagonal_mul, entry_frequencyComponent]
  split_ifs with h
  · have hg := gibbsProbability_gap e β i j
    rw [h] at hg
    rw [hg]
    push_cast
    ring
  · simp

theorem diagonal_commute (b : OrthonormalBasis ι ℂ V) (e f : ι → ℝ) :
    Commute (diagonal b e) (diagonal b f) := by
  change diagonal b e * diagonal b f = diagonal b f * diagonal b e
  apply entry_ext b
  intro i j
  simp only [entry_diagonal_mul, entry_mul_diagonal, entry_diagonal]
  split_ifs with h
  · subst j; ring
  · simp

theorem hamiltonian_commutes_gibbs (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (β : ℝ) :
    Commute (diagonal b e) (spectralGibbsDensity b e β).toOperator := by
  rw [spectralGibbsDensity_diagonal]
  exact diagonal_commute b e _

/-- Rates are numeric data on actual finite Bohr frequencies. -/
def weightedJump {κ : Type*} (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (A : κ → Operator V) (rate : κ → Frequency e → ℝ)
    (a : κ × Frequency e) : Operator V :=
  (Real.sqrt (rate a.1 a.2) : ℂ) • frequencyComponent b e (A a.1) a.2.val

/-- Scaling a genuine jump scales its quadratic dissipator by the squared modulus. -/
theorem lindbladJumpTerm_smul (J : Operator V) (c : ℂ) (F : Operator V) :
    lindbladJumpTerm (c • J) F = (c * star c) • lindbladJumpTerm J F := by
  simp only [lindbladJumpTerm_apply, map_smulₛₗ, starRingEnd_apply, smul_mul_assoc, mul_smul_comm,
    smul_smul, smul_sub, smul_add]
  congr 1 <;> congr 1 <;> ring

theorem weightedJump_term {κ : Type*} (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (A : κ → Operator V) (rate : κ → Frequency e → ℝ)
    (hn : ∀ a w, 0 ≤ rate a w) (a : κ × Frequency e) (F : Operator V) :
    lindbladJumpTerm (weightedJump b e A rate a) F =
      (rate a.1 a.2 : ℂ) • lindbladJumpTerm (frequencyComponent b e (A a.1) a.2.val) F := by
  rw [weightedJump, lindbladJumpTerm_smul]
  congr 1
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [Real.mul_self_sqrt (hn _ _)]

private theorem exp_apply_eigenvector
    (A : ContinuousOperator V) (v : V) (lambda z : ℂ)
    (hv : A v = lambda • v) :
    NormedSpace.exp (z • A) v = Complex.exp (z * lambda) • v := by
  letI : CompleteSpace V := FiniteDimensional.complete ℂ V
  have hpow : ∀ n : ℕ, ((z • A) ^ n) v = (z * lambda) ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, mul_apply_eq_comp]
        simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, hv, smul_smul]
        rw [map_smul, ih]
        simp only [smul_smul]
        congr 1
        ring
  let ev : ContinuousOperator V →L[ℂ] V := (ContinuousLinearMap.apply ℂ V) v
  have hop := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z • A)).map ev ev.continuous
  have hscalar := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z * lambda)).smul_const v
  rw [Complex.exp_eq_exp_ℂ]
  apply HasSum.unique hop
  apply hscalar.congr
  intro s
  apply Finset.sum_congr rfl
  intro n _
  simp [ev, hpow n, mul_smul]

/-- The spectral density is a normalized actual operator exponential for any
actual Hamiltonian eigenbasis, not merely for the chosen canonical basis. -/
theorem spectralGibbsDensity_normalized_exp (H : Operator V)
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (heigen : ∀ i, H (b i) = (e i : ℂ) • b i) (β : ℝ) :
    (spectralGibbsDensity b e β).toOperator =
      ((gibbsPartitionFunction β e : ℂ)⁻¹) •
        (NormedSpace.exp ((-β : ℂ) • LinearMap.toContinuousLinearMap H)).toLinearMap := by
  letI : CompleteSpace V := FiniteDimensional.complete ℂ V
  apply b.toBasis.ext
  intro i
  change (spectralGibbsDensity b e β).toOperator (b i) = _
  rw [spectralGibbsDensity_apply_basis]
  change _ = ((gibbsPartitionFunction β e : ℂ)⁻¹) •
    (NormedSpace.exp ((-β : ℂ) • LinearMap.toContinuousLinearMap H) (b i))
  rw [exp_apply_eigenvector _ _ _ _ (heigen i)]
  simp only [smul_smul]
  congr 1
  rw [gibbsProbability]
  have hexp : Complex.exp ((-β : ℂ) * (e i : ℂ)) = (Real.exp (-β * e i) : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_exp]
  rw [hexp]
  push_cast
  ring

theorem frequencyComponent_gibbs_square_commute (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (β ω : ℝ) (A : Operator V) :
    Commute (LinearMap.adjoint (frequencyComponent b e A ω) * frequencyComponent b e A ω)
      (spectralGibbsDensity b e β).toOperator := by
  let C := frequencyComponent b e A ω
  let R := (spectralGibbsDensity b e β).toOperator
  have hc : C * R = (Real.exp (-β*ω) : ℂ) • (R*C) := frequencyComponent_gibbs b e β ω A
  have hd : LinearMap.adjoint C * R = (Real.exp (-β*(-ω)) : ℂ) • (R*LinearMap.adjoint C) := by
    dsimp [C,R]
    rw [frequencyComponent_adjoint]
    exact frequencyComponent_gibbs b e β (-ω) (LinearMap.adjoint A)
  have hq : (Real.exp (-β*ω) : ℂ) * (Real.exp (-β*(-ω)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    have he : -β*ω + -β*(-ω) = 0 := by ring
    rw [he]; simp
  change LinearMap.adjoint C * C * R = R * (LinearMap.adjoint C*C)
  calc
    _ = LinearMap.adjoint C * (C*R) := mul_assoc _ _ _
    _ = (Real.exp (-β*ω) : ℂ) • ((LinearMap.adjoint C*R)*C) := by rw [hc]; simp [mul_assoc]
    _ = ((Real.exp (-β*ω) : ℂ) * (Real.exp (-β*(-ω)) : ℂ)) •
        (R*(LinearMap.adjoint C*C)) := by rw [hd]; simp [smul_smul, mul_assoc]
    _ = _ := by rw [hq]; simp

theorem weightedJump_gibbs_term {κ : Type*} (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (β : ℝ) (A : κ → Operator V) (rate : κ → Frequency e → ℝ)
    (hn : ∀ a w, 0 ≤ rate a w) (a : κ) (w : Frequency e) :
    lindbladJumpTerm (weightedJump b e A rate (a,w)) (spectralGibbsDensity b e β).toOperator =
      (rate a w * Real.exp (-β*w.val) : ℂ) •
        ((spectralGibbsDensity b e β).toOperator * frequencyComponent b e (A a) w.val *
          LinearMap.adjoint (frequencyComponent b e (A a) w.val)) -
      (rate a w : ℂ) •
        ((spectralGibbsDensity b e β).toOperator * LinearMap.adjoint (frequencyComponent b e (A a) w.val) *
          frequencyComponent b e (A a) w.val) := by
  rw [weightedJump_term b e A rate hn, lindbladJumpTerm_apply,
    frequencyComponent_gibbs b e β w.val (A a),
    (frequencyComponent_gibbs_square_commute b e β w.val (A a)).eq]
  simp only [smul_mul_assoc, ← mul_assoc, smul_sub, smul_add, smul_smul,
    Complex.ofReal_mul]
  module

/-- Detailed balance cancels the gain at frequency `-ω` against loss at `ω`. -/
theorem sum_weightedJump_gibbs_zero {κ : Type*} (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (β : ℝ) (A : κ → Operator V) (rate : κ → Frequency e → ℝ)
    (hn : ∀ a w, 0 ≤ rate a w) (hA : ∀ a, (A a).IsSymmetric)
    (hDB : ∀ a w, rate a (negFrequency e w) = Real.exp (-β*w.val) * rate a w)
    (a : κ) :
    (∑ w : Frequency e, lindbladJumpTerm (weightedJump b e A rate (a,w))
      (spectralGibbsDensity b e β).toOperator) = 0 := by
  simp_rw [weightedJump_gibbs_term b e β A rate hn]
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  let R := (spectralGibbsDensity b e β).toOperator
  let f := fun w : Frequency e => (rate a w : ℂ) •
    (R * LinearMap.adjoint (frequencyComponent b e (A a) w.val) * frequencyComponent b e (A a) w.val)
  change _ = ∑ w, f w
  rw [← (negFrequency e).sum_comp f]
  apply Finset.sum_congr rfl
  intro w _
  dsimp [f,R]
  rw [hDB]
  have hadj : ∀ ω, LinearMap.adjoint (frequencyComponent b e (A a) ω) =
      frequencyComponent b e (A a) (-ω) := by
    intro ω
    rw [frequencyComponent_adjoint, (hA a).adjoint_eq]
  simp only [negFrequency, Equiv.coe_fn_mk, hadj, neg_neg]
  simp only [← Complex.ofReal_mul, mul_comm]
  apply entry_ext b
  intro i j
  simp only [entry_smul, entry_real_smul, Complex.ofReal_mul]

theorem weightedJump_gibbs_stationary {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) (β : ℝ)
    (A : κ → Operator V) (rate : κ → Frequency e → ℝ)
    (hn : ∀ a w, 0 ≤ rate a w) (hA : ∀ a, (A a).IsSymmetric)
    (hDB : ∀ a w, rate a (negFrequency e w) = Real.exp (-β*w.val) * rate a w) :
    lindbladDissipator (weightedJump b e A rate) (spectralGibbsDensity b e β).toOperator = 0 := by
  rw [lindbladDissipator_apply, Fintype.sum_prod_type]
  simp only [sum_weightedJump_gibbs_zero b e β A rate hn hA hDB, Finset.sum_const_zero]

/-- Coupling protection plus Hamiltonian commutation supplies the existing
operator-valued protected-jump predicate. -/
theorem weightedJump_protected {κ : Type*} [Fintype κ] (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (A : κ → Operator V) (rate : κ → Frequency e → ℝ)
    (O P : Operator V) (hO : Commute (diagonal b e) O) (hP : Commute (diagonal b e) P)
    (h : ∀ a, (A a * O - O * A a) * P = 0) :
    JumpProtected (weightedJump b e A rate) O P := by
  intro a
  simp only [weightedJump, smul_mul_assoc, mul_smul_comm, ← smul_sub]
  rw [frequencyComponent_protected b e (A a.1) O P hO hP (h a.1)]
  simp

theorem gibbsPartitionFunction_eq_trace_exp (H : Operator V)
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (heigen : ∀ i, H (b i) = (e i : ℂ) • b i) (β : ℝ) :
    (gibbsPartitionFunction β e : ℂ) = LinearMap.trace ℂ V
      (NormedSpace.exp ((-β : ℂ) • LinearMap.toContinuousLinearMap H)).toLinearMap := by
  have h := congrArg (LinearMap.trace ℂ V) (spectralGibbsDensity_normalized_exp H b e heigen β)
  rw [(spectralGibbsDensity b e β).trace_one, map_smul, smul_eq_mul] at h
  have hz : (gibbsPartitionFunction β e : ℂ) ≠ 0 := by
    exact_mod_cast (gibbsPartitionFunction_pos β e).ne'
  have hm := congrArg (fun z : ℂ => (gibbsPartitionFunction β e : ℂ) * z) h
  simpa only [mul_one, ← mul_assoc, mul_inv_cancel₀ hz, one_mul] using hm

/-- Any two genuine eigenbases produce the same existing Gibbs density. -/
theorem spectralGibbsDensity_basis_independent {ι' : Type} [Fintype ι'] [Nonempty ι']
    (H : Operator V) (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (c : OrthonormalBasis ι' ℂ V) (f : ι' → ℝ)
    (hb : ∀ i, H (b i) = (e i : ℂ) • b i)
    (hc : ∀ j, H (c j) = (f j : ℂ) • c j) (β : ℝ) :
    (spectralGibbsDensity b e β).toOperator = (spectralGibbsDensity c f β).toOperator := by
  rw [spectralGibbsDensity_normalized_exp H b e hb,
    spectralGibbsDensity_normalized_exp H c f hc,
    gibbsPartitionFunction_eq_trace_exp H b e hb,
    gibbsPartitionFunction_eq_trace_exp H c f hc]

/-- The complete weighted dissipator formula retains one coherent operator per gap. -/
theorem weightedJump_dissipator_apply {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) (A : κ → Operator V)
    (rate : κ → Frequency e → ℝ) (hn : ∀ a w, 0 ≤ rate a w) (F : Operator V) :
    lindbladDissipator (weightedJump b e A rate) F =
      ∑ a, ∑ w : Frequency e, (rate a w : ℂ) •
        lindbladJumpTerm (frequencyComponent b e (A a) w.val) F := by
  rw [lindbladDissipator_apply, Fintype.sum_prod_type]
  simp only [weightedJump_term b e A rate hn]

end
end QEC.Semantics.Davies
