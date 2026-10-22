import QEC.Semantics.Dynamics.FourBlockGenerator
import QEC.Semantics.Dynamics.ThermalEncoding
/-!
# The CLBT protected-observable decay theorem

This module completes Chesi--Loss--Bravyi--Terhal's Theorem 1.  It first
derives the all-time trace-norm estimate from the finite Lindblad evolution,
CPTP contraction, and the fundamental theorem of calculus.  It then combines
that bridge with the concrete thermal encoder/decoder and the four-block
generator estimate.

No detailed-balance, gap, barrier, or asymptotic lifetime hypothesis is used.
-/

universe u v

namespace QEC.Semantics

open scoped ComplexOrder

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]

noncomputable local instance clbtFiniteQuantumSystemComplete : CompleteSpace H :=
  FiniteDimensional.complete ℂ H

/-! ## Trace-norm integration -/

/-- A private copy of the finite operator space carrying the Schatten-1 norm. -/
private def CLBTTraceNormedOperator (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteQuantumSystem H] := Operator H

private instance : AddCommGroup (CLBTTraceNormedOperator H) :=
  inferInstanceAs (AddCommGroup (Operator H))

private instance : Module ℂ (CLBTTraceNormedOperator H) :=
  inferInstanceAs (Module ℂ (Operator H))

private instance : Module ℝ (CLBTTraceNormedOperator H) :=
  Module.restrictScalars ℝ ℂ (CLBTTraceNormedOperator H)

private def clbtTraceNormedOperatorSeminorm :
    AddGroupSeminorm (CLBTTraceNormedOperator H) where
  toFun A := traceNorm (H := H) A
  map_zero' := (traceNorm_eq_zero_iff (H := H) 0).2 rfl
  neg' := traceNorm_neg
  add_le' := traceNorm_add_le

private instance clbtTraceNormedOperatorSeminormedAddCommGroup :
    SeminormedAddCommGroup (CLBTTraceNormedOperator H) :=
  clbtTraceNormedOperatorSeminorm.toSeminormedAddCommGroup

private instance clbtTraceNormedOperatorNormedAddCommGroup :
    NormedAddCommGroup (CLBTTraceNormedOperator H) :=
  NormedAddCommGroup.ofSeparation fun A hA =>
    (traceNorm_eq_zero_iff (H := H) A).1 hA

private instance clbtTraceNormedOperatorNormedSpaceComplex :
    NormedSpace ℂ (CLBTTraceNormedOperator H) where
  norm_smul_le c A := by
    change traceNorm (c • (A : Operator H)) ≤ ‖c‖ * traceNorm (A : Operator H)
    exact le_of_eq (traceNorm_smul c A)

private instance clbtTraceNormedOperatorNormedSpaceReal :
    NormedSpace ℝ (CLBTTraceNormedOperator H) :=
  NormedSpace.restrictScalars ℝ ℂ (CLBTTraceNormedOperator H)

private def clbtTraceNormedOperatorToOperator :
    CLBTTraceNormedOperator H →ₗ[ℂ] Operator H :=
  LinearMap.id

private instance clbtTraceNormedOperatorFiniteDimensional :
    FiniteDimensional ℂ (CLBTTraceNormedOperator H) :=
  FiniteDimensional.of_injective clbtTraceNormedOperatorToOperator
    (LinearMap.ker_eq_bot.mp rfl)

private noncomputable instance clbtTraceNormedOperatorComplete :
    CompleteSpace (CLBTTraceNormedOperator H) :=
  FiniteDimensional.complete ℂ (CLBTTraceNormedOperator H)

/-- Forget the operator-norm topology and equip the same operator with trace norm. -/
private noncomputable def continuousOperatorToCLBTTraceNormed :
    ContinuousOperator H →L[ℝ] CLBTTraceNormedOperator H :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A.toLinearMap
      map_add' := by intro A B; rfl
      map_smul' := by
        intro r A
        change ((r : ℂ) • A).toLinearMap = (r : ℂ) • A.toLinearMap
        rfl }

private theorem clbtTraceNorm_intervalIntegral_bound
    (f : ℝ → ContinuousOperator H) (t C : ℝ)
    (hf : IntervalIntegrable f MeasureTheory.volume 0 t)
    (ht : 0 ≤ t)
    (hbound : ∀ s ∈ Set.uIoc 0 t,
      traceNorm ((f s).toLinearMap) ≤ C) :
    traceNorm
        ((continuousOperatorToCLBTTraceNormed (H := H)
          (∫ s in (0 : ℝ)..t, f s) : CLBTTraceNormedOperator H)) ≤
      t * C := by
  change ‖continuousOperatorToCLBTTraceNormed (H := H)
    (∫ s in (0 : ℝ)..t, f s)‖ ≤ t * C
  rw [← intervalIntegral_comp_comm
    (continuousOperatorToCLBTTraceNormed (H := H)) f 0 t hf]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := fun s =>
    continuousOperatorToCLBTTraceNormed (H := H) (f s)) (C := C) (by
      intro s hs
      change traceNorm ((f s).toLinearMap) ≤ C
      exact hbound s hs)
  simpa [abs_of_nonneg ht, mul_comm] using h

/-! ## Evolution from the local generator estimate -/

private theorem lindbladJumpTerm_isSymmetric
    (J A : Operator H) (hA : A.IsSymmetric) :
    (lindbladJumpTerm J A).IsSymmetric := by
  let K : Operator H := LinearMap.adjoint J * J
  have hK : K.IsSymmetric := by
    exact LinearMap.isSymmetric_adjoint_comp_self J
  have hgain : (J * A * LinearMap.adjoint J).IsSymmetric := by
    exact hA.conj_adjoint J
  have hloss : (K * A + A * K).IsSymmetric := by
    intro x y
    simp only [LinearMap.add_apply, Module.End.mul_apply, inner_add_left,
      inner_add_right]
    rw [hK, hA, hA, hK]
    ac_rfl
  rw [lindbladJumpTerm_apply]
  apply hgain.sub
  apply hloss.smul
  rw [map_inv₀]
  congr 1
  change star (2 : ℂ) = 2
  norm_num

private theorem lindbladDissipator_isSymmetric [Fintype ι]
    (J : ι → Operator H) (A : Operator H) (hA : A.IsSymmetric) :
    (lindbladDissipator J A).IsSymmetric := by
  rw [lindbladDissipator_apply]
  exact LinearMap.isSymmetric_sum Finset.univ fun i _ =>
    lindbladJumpTerm_isSymmetric (J i) A hA

/--
For an input commuting with the Hamiltonian, finite Lindblad evolution moves
the input by at most time times the trace norm of its dissipative derivative.
The contraction used here is derived from the CPTP evolution channel.
-/
theorem finiteLindbladEvolution_traceNorm_sub_le_time_mul [Fintype ι]
    [Nontrivial H]
    (hamiltonian : Operator H) (J : ι → Operator H)
    (hhamiltonian : hamiltonian.IsSymmetric)
    (A : Operator H) (hA : A.IsSymmetric)
    (hcomm : Commute hamiltonian A)
    (t : ℝ) (ht : 0 ≤ t) :
    traceNorm (finiteLindbladEvolutionLinearMap hamiltonian J t A - A) ≤
      t * traceNorm (lindbladDissipator J A) := by
  let G := asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)
  let Ac : ContinuousOperator H := LinearMap.toContinuousLinearMap A
  let D : Operator H := lindbladDissipator J A
  have hgenerator : finiteLindbladGenerator hamiltonian J A = D := by
    change hamiltonianCommutator hamiltonian A + lindbladDissipator J A = D
    have hzero : hamiltonianCommutator hamiltonian A = 0 := by
      rw [hamiltonianCommutator_apply, hcomm.eq, sub_self, smul_zero]
    rw [hzero, zero_add]
  have hDsym : D.IsSymmetric := by
    exact lindbladDissipator_isSymmetric J A hA
  have hderiv : ∀ s : ℝ, HasDerivAt
      (fun r : ℝ => finiteLindbladEvolutionContinuous hamiltonian J (r : ℂ))
      (finiteLindbladEvolutionContinuous hamiltonian J (s : ℂ) *
        asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) s :=
    fun s => hasDerivAt_finiteLindbladEvolutionReal hamiltonian J s
  have hE : Continuous (fun s : ℝ =>
      finiteLindbladEvolutionContinuous hamiltonian J (s : ℂ)) :=
    continuous_iff_continuousAt.mpr fun s => (hderiv s).continuousAt
  have hprod : Continuous (fun s : ℝ =>
      finiteLindbladEvolutionContinuous hamiltonian J (s : ℂ) *
        asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) :=
    hE.mul continuous_const
  have hfint : IntervalIntegrable
      (fun s : ℝ =>
        finiteLindbladEvolutionContinuous hamiltonian J (s : ℂ) (G Ac))
      MeasureTheory.volume 0 t := by
    have hconst : Continuous (fun _ : ℝ => Ac) := continuous_const
    simpa [G] using (hprod.clm_apply hconst).intervalIntegrable 0 t
  have hintegral := finiteLindbladEvolutionContinuous_integral hamiltonian J t
  have happly :
      (∫ s in (0 : ℝ)..t,
        finiteLindbladEvolutionContinuous hamiltonian J (s : ℂ) (G Ac)) =
        finiteLindbladEvolutionContinuous hamiltonian J (t : ℂ) Ac - Ac := by
    have heval := intervalIntegral_comp_comm
      ((ContinuousLinearMap.apply ℂ (ContinuousOperator H) Ac).restrictScalars ℝ)
      (fun s : ℝ =>
        finiteLindbladEvolutionContinuous hamiltonian J (s : ℂ) * G)
      0 t (by simpa [G] using hprod.intervalIntegrable 0 t)
    rw [hintegral] at heval
    simpa [G, Ac, sub_apply] using heval
  have hbound := clbtTraceNorm_intervalIntegral_bound
    (fun s : ℝ =>
      finiteLindbladEvolutionContinuous hamiltonian J (s : ℂ) (G Ac))
    t (traceNorm D) hfint ht (by
      intro s hs
      have hsnonneg : 0 ≤ s := by
        have hs' : s ∈ Set.Ioc 0 t := by simpa [Set.uIoc_of_le ht] using hs
        exact hs'.1.le
      have hcontract :=
        (finiteLindbladEvolutionChannel hamiltonian J hhamiltonian s hsnonneg)
          |>.traceNorm_apply_le_of_isSymmetric D hDsym
      have hinput : G Ac = LinearMap.toContinuousLinearMap D := by
        change LinearMap.toContinuousLinearMap
          (finiteLindbladGenerator hamiltonian J A) =
            LinearMap.toContinuousLinearMap D
        rw [hgenerator]
      rw [hinput]
      change traceNorm
        (finiteLindbladEvolutionLinearMap hamiltonian J s D) ≤ traceNorm D
      exact hcontract)
  rw [happly] at hbound
  change traceNorm
      (finiteLindbladEvolutionLinearMap hamiltonian J t A - A) ≤
    t * traceNorm D
  exact hbound

/-! ## Gibbs commutation from the Hamiltonian -/

/--
The positive `Z` eigenspace of a Pauli-like pair is nontrivial whenever the
physical space is nontrivial.  Indeed, `X` identifies the positive and negative
eigenspaces, while those two eigenspaces are complementary in the physical
space.
-/
noncomputable instance
    ThermalEncoding.PauliLikePair.auxiliarySpaceNontrivial
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    [Nontrivial K]
    (logical : ThermalEncoding.PauliLikePair K) :
    Nontrivial logical.AuxiliarySpace := by
  let e : (logical.AuxiliarySpace × logical.AuxiliarySpace) ≃ₗ[ℂ] K :=
    (LinearEquiv.prodCongr (LinearEquiv.refl ℂ logical.AuxiliarySpace)
      logical.xEigenspaceEquiv).trans
        (Submodule.prodEquivOfIsCompl
          (Module.End.eigenspace logical.z (1 : ℂ))
          (Module.End.eigenspace logical.z (-1 : ℂ))
          logical.positive_negative_isCompl)
  have hprod : Nontrivial
      (logical.AuxiliarySpace × logical.AuxiliarySpace) :=
    e.toEquiv.nontrivial
  rw [← not_subsingleton_iff_nontrivial]
  intro haux
  letI : Subsingleton logical.AuxiliarySpace := haux
  exact (not_nontrivial
    (logical.AuxiliarySpace × logical.AuxiliarySpace)) hprod

private theorem continuousOperator_exp_smul_apply_eigenvector
    (A : ContinuousOperator H) (v : H) (lambda z : ℂ)
    (hv : A v = lambda • v) :
    NormedSpace.exp (z • A) v = Complex.exp (z * lambda) • v := by
  have hpow : ∀ n : ℕ, ((z • A) ^ n) v = (z * lambda) ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ContinuousLinearMap.mul_apply]
        simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, hv, smul_smul]
        rw [map_smul, ih]
        simp only [smul_smul]
        congr 1
        ring
  let ev : ContinuousOperator H →L[ℂ] H :=
    (ContinuousLinearMap.apply ℂ H) v
  have hop :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z • A)).map ev ev.continuous
  have hscalar :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z * lambda)).smul_const v
  rw [Complex.exp_eq_exp_ℂ]
  apply HasSum.unique hop
  apply hscalar.congr
  intro s
  apply Finset.sum_congr rfl
  intro n _hn
  simp [ev, hpow n, mul_smul]

/--
The spectral Gibbs density constructed from the Pauli factorization is the
normalized operator exponential of the physical Hamiltonian.
-/
theorem ThermalEncoding.PauliLikePair.physicalGibbsState_toOperator_eq_normalized_exp
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    [Nontrivial logical.AuxiliarySpace]
    (hamiltonian : Operator K)
    (hX : Commute hamiltonian logical.x)
    (hZ : Commute hamiltonian logical.z)
    (hhamiltonian : hamiltonian.IsSymmetric)
    (beta : ℝ) :
    (logical.physicalGibbsState hamiltonian hZ hhamiltonian beta).toOperator =
      ((ThermalEncoding.gibbsPartitionFunction beta
        (logical.physicalHamiltonianEnergies hamiltonian hZ hhamiltonian) : ℂ)⁻¹) •
        (NormedSpace.exp
          ((-beta : ℂ) • LinearMap.toContinuousLinearMap hamiltonian)).toLinearMap := by
  letI : CompleteSpace K := FiniteDimensional.complete ℂ K
  letI : Nonempty (Fin (Module.finrank ℂ logical.AuxiliarySpace)) :=
    Fin.pos_iff_nonempty.mp Module.finrank_pos
  letI : Nonempty
      (Fin 2 × Fin (Module.finrank ℂ logical.AuxiliarySpace)) := inferInstance
  let b := logical.physicalHamiltonianEigenbasis hamiltonian hZ hhamiltonian
  let energy := logical.physicalHamiltonianEnergies hamiltonian hZ hhamiltonian
  apply Module.Basis.ext b.toBasis
  intro i
  change
    (ThermalEncoding.spectralGibbsDensity b energy beta).toOperator (b i) = _
  rw [ThermalEncoding.spectralGibbsDensity_apply_basis]
  change _ =
    ((ThermalEncoding.gibbsPartitionFunction beta energy : ℂ)⁻¹) •
      (NormedSpace.exp
        ((-beta : ℂ) • LinearMap.toContinuousLinearMap hamiltonian) (b i))
  have heigen : (LinearMap.toContinuousLinearMap hamiltonian) (b i) =
      (energy i : ℂ) • b i := by
    change hamiltonian (b i) = (energy i : ℂ) • b i
    exact logical.physicalHamiltonianEigenbasis_apply
      hamiltonian hX hZ hhamiltonian i
  rw [continuousOperator_exp_smul_apply_eigenvector _ _ _ _ heigen]
  simp only [smul_smul]
  congr 1
  rw [ThermalEncoding.gibbsProbability]
  have hexp : Complex.exp ((-beta : ℂ) * (energy i : ℂ)) =
      (Real.exp (-beta * energy i) : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_exp]
  rw [hexp]
  have hreal :
      Real.exp (-beta * energy i) /
          ThermalEncoding.gibbsPartitionFunction beta energy =
        (ThermalEncoding.gibbsPartitionFunction beta energy)⁻¹ *
          Real.exp (-beta * energy i) := by
    field_simp [ThermalEncoding.gibbsPartitionFunction_pos beta energy |>.ne']
  exact_mod_cast hreal

/-- Every symmetric Hamiltonian commutant also commutes with its Gibbs density. -/
theorem ThermalEncoding.PauliLikePair.commute_physicalGibbsState
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    [Nontrivial logical.AuxiliarySpace]
    (hamiltonian A : Operator K)
    (hX : Commute hamiltonian logical.x)
    (hZ : Commute hamiltonian logical.z)
    (hhamiltonian : hamiltonian.IsSymmetric)
    (hA : Commute A hamiltonian)
    (beta : ℝ) :
    Commute A
      (logical.physicalGibbsState hamiltonian hZ hhamiltonian beta).toOperator := by
  letI : CompleteSpace K := FiniteDimensional.complete ℂ K
  rw [logical.physicalGibbsState_toOperator_eq_normalized_exp
    hamiltonian hX hZ hhamiltonian beta]
  let Ac : ContinuousOperator K := LinearMap.toContinuousLinearMap A
  let Hc : ContinuousOperator K := LinearMap.toContinuousLinearMap hamiltonian
  have hcontinuous : Commute Ac Hc := by
    rw [Commute]
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun T : Operator K => T x) hA.eq
  have hexp : Commute Ac (NormedSpace.exp ((-beta : ℂ) • Hc)) :=
    (hcontinuous.smul_right (-beta : ℂ)).exp_right
  rw [Commute]
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun T : ContinuousOperator K => T x) hexp.eq
  have hxscaled := congrArg (fun y : K =>
    ((ThermalEncoding.gibbsPartitionFunction beta
      (logical.physicalHamiltonianEnergies hamiltonian hZ hhamiltonian) : ℂ)⁻¹) • y) hx
  simpa [Ac, Hc, Module.End.mul_apply, mul_smul] using hxscaled

/-! ## Pauli-algebra protection closure -/

private theorem qubitOperator_eq_pauli_span (A : Operator Qubit.QubitSpace) :
    ∃ alpha gamma delta epsilon : ℂ,
      A = alpha • 1 + gamma • Qubit.pauliZ +
        delta • Qubit.pauliX + epsilon • (Qubit.pauliX * Qubit.pauliZ) := by
  let e0 : Qubit.QubitSpace := EuclideanSpace.basisFun (Fin 2) ℂ 0
  let e1 : Qubit.QubitSpace := EuclideanSpace.basisFun (Fin 2) ℂ 1
  refine ⟨(2 : ℂ)⁻¹ * (A e0 0 + A e1 1),
    (2 : ℂ)⁻¹ * (A e0 0 - A e1 1),
    (2 : ℂ)⁻¹ * (A e0 1 + A e1 0),
    (2 : ℂ)⁻¹ * (A e0 1 - A e1 0), ?_⟩
  apply LinearMap.ext
  intro psi
  have hpsi : psi = psi 0 • EuclideanSpace.basisFun (Fin 2) ℂ 0 +
      psi 1 • EuclideanSpace.basisFun (Fin 2) ℂ 1 := by
    ext i
    fin_cases i <;> simp
  rw [hpsi, map_add, map_smul, map_smul]
  ext i
  fin_cases i <;>
    simp [e0, e1, Module.End.mul_apply, Qubit.zPhase] <;>
    ring

theorem JumpProtected.one [Fintype ι] (J : ι → Operator H) (P : Operator H) :
    JumpProtected J 1 P := by
  intro a
  simp

theorem JumpProtected.add [Fintype ι]
    {J : ι → Operator H} {O₁ O₂ P : Operator H}
    (h₁ : JumpProtected J O₁ P) (h₂ : JumpProtected J O₂ P) :
    JumpProtected J (O₁ + O₂) P := by
  intro a
  rw [show (J a * (O₁ + O₂) - (O₁ + O₂) * J a) * P =
      (J a * O₁ - O₁ * J a) * P +
        (J a * O₂ - O₂ * J a) * P by noncomm_ring,
    h₁ a, h₂ a, add_zero]

theorem JumpProtected.smul [Fintype ι]
    {J : ι → Operator H} {O P : Operator H}
    (h : JumpProtected J O P) (c : ℂ) :
    JumpProtected J (c • O) P := by
  intro a
  rw [show (J a * (c • O) - (c • O) * J a) * P =
      c • ((J a * O - O * J a) * P) by
        ext x
        simp [Module.End.mul_apply]
        module,
    h a, smul_zero]

theorem JumpProtected.mul_of_commute_projector [Fintype ι]
    {J : ι → Operator H} {O₁ O₂ P : Operator H}
    (h₁ : JumpProtected J O₁ P) (h₂ : JumpProtected J O₂ P)
    (h₂P : Commute O₂ P) :
    JumpProtected J (O₁ * O₂) P := by
  intro a
  rw [show (J a * (O₁ * O₂) - O₁ * O₂ * J a) * P =
      J a * O₁ * O₂ * P - O₁ * O₂ * J a * P by noncomm_ring]
  have h₁a := h₁.jump_mul_observable_projector a
  have h₂a := h₂.jump_mul_observable_projector a
  calc
    J a * O₁ * O₂ * P - O₁ * O₂ * J a * P =
        J a * O₁ * (O₂ * P) - O₁ * O₂ * J a * P := by noncomm_ring
    _ = J a * O₁ * (P * O₂) - O₁ * O₂ * J a * P := by rw [h₂P.eq]
    _ = J a * O₁ * P * O₂ - O₁ * O₂ * J a * P := by noncomm_ring
    _ = O₁ * J a * P * O₂ - O₁ * O₂ * J a * P := by rw [h₁a]
    _ = O₁ * J a * (P * O₂) - O₁ * O₂ * J a * P := by noncomm_ring
    _ = O₁ * J a * (O₂ * P) - O₁ * O₂ * J a * P := by rw [h₂P.eq]
    _ = O₁ * J a * O₂ * P - O₁ * O₂ * J a * P := by noncomm_ring
    _ = O₁ * (J a * O₂ * P) - O₁ * O₂ * J a * P := by noncomm_ring
    _ = O₁ * (O₂ * J a * P) - O₁ * O₂ * J a * P := by rw [h₂a]
    _ = 0 := by noncomm_ring

private noncomputable def ThermalEncoding.PauliLikePair.liftQubitOperator
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    (A : Operator Qubit.QubitSpace) : Operator K :=
  logical.factorization.conjOperator
    (TensorProduct.map A (1 : Operator logical.AuxiliarySpace))

private theorem ThermalEncoding.PauliLikePair.liftQubitOperator_eq_encodedObservable
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    (eta : DensityOperator Qubit.QubitSpace) :
    logical.liftQubitOperator ((2 : ℂ) • eta.toOperator) =
      logical.encodedObservable eta := by
  rfl

private theorem ThermalEncoding.PauliLikePair.liftQubitOperator_one
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K) :
    logical.liftQubitOperator 1 = 1 := by
  simp [ThermalEncoding.PauliLikePair.liftQubitOperator]

private theorem ThermalEncoding.PauliLikePair.liftQubitOperator_pauliX
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K) :
    logical.liftQubitOperator Qubit.pauliX = logical.x := by
  exact logical.conj_tensorPauliX

private theorem ThermalEncoding.PauliLikePair.liftQubitOperator_pauliZ
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K) :
    logical.liftQubitOperator Qubit.pauliZ = logical.z := by
  exact logical.conj_tensorPauliZ

private theorem ThermalEncoding.PauliLikePair.liftQubitOperator_add
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    (A B : Operator Qubit.QubitSpace) :
    logical.liftQubitOperator (A + B) =
      logical.liftQubitOperator A + logical.liftQubitOperator B := by
  change logical.factorization.conjOperator
      (TensorProduct.map (A + B) 1) = _
  rw [TensorProduct.map_add_left]
  exact map_add logical.factorization.conjOperatorLinearMap _ _

private theorem ThermalEncoding.PauliLikePair.liftQubitOperator_smul
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    (c : ℂ) (A : Operator Qubit.QubitSpace) :
    logical.liftQubitOperator (c • A) =
      c • logical.liftQubitOperator A := by
  change logical.factorization.conjOperator
      (TensorProduct.map (c • A) 1) = _
  rw [TensorProduct.map_smul_left]
  exact map_smul logical.factorization.conjOperatorLinearMap _ _

private theorem ThermalEncoding.PauliLikePair.liftQubitOperator_mul
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    (A B : Operator Qubit.QubitSpace) :
    logical.liftQubitOperator (A * B) =
      logical.liftQubitOperator A * logical.liftQubitOperator B := by
  rw [ThermalEncoding.PauliLikePair.liftQubitOperator,
    ThermalEncoding.PauliLikePair.liftQubitOperator,
    ThermalEncoding.PauliLikePair.liftQubitOperator,
    ← logical.factorization.conjOperator_mul,
    ← TensorProduct.map_mul]
  simp

private theorem ThermalEncoding.PauliLikePair.liftQubitOperator_pauli_span
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    (A : Operator Qubit.QubitSpace) :
    ∃ alpha gamma delta epsilon : ℂ,
      logical.liftQubitOperator A =
        alpha • 1 + gamma • logical.z + delta • logical.x +
          epsilon • (logical.x * logical.z) := by
  rcases qubitOperator_eq_pauli_span A with ⟨alpha, gamma, delta, epsilon, hA⟩
  rw [hA]
  refine ⟨alpha, gamma, delta, epsilon, ?_⟩
  rw [logical.liftQubitOperator_add, logical.liftQubitOperator_add,
    logical.liftQubitOperator_add,
    logical.liftQubitOperator_smul, logical.liftQubitOperator_smul,
    logical.liftQubitOperator_smul, logical.liftQubitOperator_smul,
    logical.liftQubitOperator_one, logical.liftQubitOperator_pauliX,
    logical.liftQubitOperator_pauliZ, logical.liftQubitOperator_mul,
    logical.liftQubitOperator_pauliX, logical.liftQubitOperator_pauliZ]

private theorem commute_smul_right_operator
    (A B : Operator H) (h : Commute A B) (c : ℂ) :
    Commute A (c • B) := by
  rw [Commute]
  ext x
  simpa [Module.End.mul_apply] using
    congrArg (fun T : Operator H => c • T x) h.eq

private theorem commute_smul_left_operator
    (A B : Operator H) (h : Commute A B) (c : ℂ) :
    Commute (c • A) B :=
  (commute_smul_right_operator B A h.symm c).symm

private theorem commute_encodedObservable_projector
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    (P : Operator K) (hPx : Commute P logical.x) (hPz : Commute P logical.z)
    (eta : DensityOperator Qubit.QubitSpace) :
    Commute (logical.encodedObservable eta) P := by
  rcases logical.liftQubitOperator_pauli_span ((2 : ℂ) • eta.toOperator) with
    ⟨cI, cZ, cX, cXZ, hspan⟩
  rw [← logical.liftQubitOperator_eq_encodedObservable eta, hspan]
  have hxP : Commute logical.x P := hPx.symm
  have hzP : Commute logical.z P := hPz.symm
  have hxzP : Commute (logical.x * logical.z) P := hxP.mul_left hzP
  have hIP : Commute (1 : Operator K) P := Commute.one_left P
  have hI := commute_smul_left_operator (1 : Operator K) P hIP cI
  have hZ := commute_smul_left_operator logical.z P hzP cZ
  have hX := commute_smul_left_operator logical.x P hxP cX
  have hXZ := commute_smul_left_operator (logical.x * logical.z) P hxzP cXZ
  exact ((hI.add_left hZ).add_left hX).add_left hXZ

private theorem jumpProtected_encodedObservable
    [Fintype ι]
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    (J : ι → Operator K) (P : Operator K)
    (hPz : Commute P logical.z)
    (hprotectedX : JumpProtected J logical.x P)
    (hprotectedZ : JumpProtected J logical.z P)
    (eta : DensityOperator Qubit.QubitSpace) :
    JumpProtected J (logical.encodedObservable eta) P := by
  rcases logical.liftQubitOperator_pauli_span ((2 : ℂ) • eta.toOperator) with
    ⟨cI, cZ, cX, cXZ, hspan⟩
  rw [← logical.liftQubitOperator_eq_encodedObservable eta, hspan]
  have hXZ : JumpProtected J (logical.x * logical.z) P :=
    hprotectedX.mul_of_commute_projector hprotectedZ hPz.symm
  exact (((JumpProtected.one J P).smul cI).add (hprotectedZ.smul cZ))
    |>.add (hprotectedX.smul cX)
    |>.add (hXZ.smul cXZ)

private theorem encodedObservable_isSymmetric
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    (eta : DensityOperator Qubit.QubitSpace) :
    (logical.encodedObservable eta).IsSymmetric := by
  rw [← logical.liftQubitOperator_eq_encodedObservable eta]
  unfold ThermalEncoding.PauliLikePair.liftQubitOperator
  apply (logical.factorization.isPositive_conjOperator ?_).isSymmetric
  exact ThermalEncoding.tensorMap_positive ((2 : ℂ) • eta.toOperator)
    (1 : Operator logical.AuxiliarySpace)
    (eta.positive.smul_of_nonneg (by norm_num)) LinearMap.isPositive_one

/-! ## CLBT10, Theorem 1 -/

/--
Chesi--Loss--Bravyi--Terhal Theorem 1: protected Pauli-like observables give
TPCP thermal encoding and decoding maps with an exact left inverse and an
all-time factor-eight trace-norm decay bound.
-/
theorem clbtProtectedObservableDecay
    {K ι : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    [Nontrivial K] [Fintype ι]
    (logical : ThermalEncoding.PauliLikePair K)
    (hamiltonian : Operator K) (hhamiltonian : hamiltonian.IsSymmetric)
    (beta : ℝ) (J : ι → Operator K) (P : Operator K)
    (hP : IsStarProjection P)
    (hPx : Commute P logical.x) (hPz : Commute P logical.z)
    (hHx : Commute hamiltonian logical.x)
    (hHz : Commute hamiltonian logical.z)
    (hPH : Commute P hamiltonian)
    (hprotectedX : JumpProtected J logical.x P)
    (hprotectedZ : JumpProtected J logical.z P)
    (hstationary : lindbladDissipator J
      (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta).toOperator = 0) :
    ∃ Enc : QuantumChannel Qubit.QubitSpace K,
      ∃ Dec : QuantumChannel K Qubit.QubitSpace,
        (∀ eta : DensityOperator Qubit.QubitSpace,
          Dec.mapDensity (Enc.mapDensity eta) = eta) ∧
        ∀ (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t),
          traceNorm
              (((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t ht)
                  |>.mapDensity (Enc.mapDensity eta)).toOperator -
                (Enc.mapDensity eta).toOperator) ≤
            8 * t * lindbladDissipatorNorm J *
              clbtGibbsTailMass P
                (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta) := by
  let sigma := logical.auxiliaryGibbsState hamiltonian hHz hhamiltonian beta
  let rho := logical.physicalGibbsState hamiltonian hHz hhamiltonian beta
  let Enc := logical.thermalEncoding sigma
  let Dec := logical.thermalDecoding
  refine ⟨Enc, Dec, ?_, ?_⟩
  · intro eta
    exact logical.thermalDecoding_thermalEncoding_density sigma eta
  · intro eta t ht
    let O := logical.encodedObservable eta
    have hOrhoEq : Enc eta.toOperator = O * rho.toOperator := by
      rw [show rho = logical.thermalReferenceState sigma from
        logical.physicalGibbsState_eq_thermalReferenceState
          hamiltonian hHz hhamiltonian beta]
      exact logical.thermalEncoding_eq_encodedObservable_mul sigma eta
    have hprotectedO : JumpProtected J O P :=
      jumpProtected_encodedObservable logical J P hPz hprotectedX hprotectedZ eta
    have hOsym : O.IsSymmetric := encodedObservable_isSymmetric logical eta
    have hOP : Commute O P :=
      commute_encodedObservable_projector logical P hPx hPz eta
    have hOH : Commute O hamiltonian :=
      commute_encodedObservable_projector logical hamiltonian hHx hHz eta
    have hPrho : Commute P rho.toOperator :=
      logical.commute_physicalGibbsState hamiltonian P hHx hHz
        hhamiltonian hPH beta
    have hOrho : Commute O rho.toOperator :=
      logical.commute_physicalGibbsState hamiltonian O hHx hHz
        hhamiltonian hOH beta
    have hHrho : Commute hamiltonian rho.toOperator :=
      logical.commute_physicalGibbsState hamiltonian hamiltonian hHx hHz
        hhamiltonian (Commute.refl hamiltonian) beta
    have hHencoded : Commute hamiltonian (Enc eta.toOperator) := by
      rw [hOrhoEq]
      exact hOH.symm.mul_right hHrho
    have hencodedSym : (Enc eta.toOperator).IsSymmetric :=
      Enc.map_isSymmetric eta.positive.isSymmetric
    have htime := finiteLindbladEvolution_traceNorm_sub_le_time_mul
      hamiltonian J hhamiltonian (Enc eta.toOperator) hencodedSym hHencoded t ht
    have hlocal :
        traceNorm (lindbladDissipator J (Enc eta.toOperator)) ≤
          8 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by
      rw [hOrhoEq]
      exact clbtFourBlockGeneratorEstimate J O P rho hprotectedO hOsym hP hOP
        hOrho hPrho hstationary
        (logical.encodedObservable_operatorNorm_le_two eta)
    have hscaled := mul_le_mul_of_nonneg_left hlocal ht
    calc
      traceNorm
          (((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t ht)
              |>.mapDensity (Enc.mapDensity eta)).toOperator -
            (Enc.mapDensity eta).toOperator) =
          traceNorm
            (finiteLindbladEvolutionLinearMap hamiltonian J t
              (Enc eta.toOperator) - Enc eta.toOperator) := rfl
      _ ≤ t * traceNorm (lindbladDissipator J (Enc eta.toOperator)) := htime
      _ ≤ t * (8 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho) := hscaled
      _ = 8 * t * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by ring


end

end QEC.Semantics
