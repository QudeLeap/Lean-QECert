import QEC.Coding.CSS.GibbsSyndrome.Spectrum
import QEC.Semantics.Dynamics.Davies.Hamiltonian

/-! # Actual CSS Gibbs normalization at twice the physical inverse temperature -/
noncomputable section
namespace QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics Semantics.Davies Semantics.ThermalEncoding
open scoped BigOperators
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
local instance : Fintype (LinearMap.range P) := Fintype.ofFinite _
local instance : Fintype (LinearMap.range Q) := Fintype.ofFinite _

/-- The row partition function sums only syndromes in the actual image. -/
def rowPartition (t : ℝ) : ℝ := ∑ u : LinearMap.range P, Real.exp (-t * HammingWeight u.val)

theorem rowPartition_pos (t : ℝ) : 0 < rowPartition P t := by
  apply Finset.sum_pos
  · intro u _; exact Real.exp_pos _
  · exact Finset.univ_nonempty

/-- This is the canonical Gibbs density of the literal row Hamiltonian. -/
def gibbs (β : ℝ) : DensityOperator (Qubit.QubitRegister ι) :=
  hamiltonianGibbs (hamiltonian P Q) (hamiltonian_symmetric P Q) β

/-- The actual operator exponential, prior to normalization. -/
def thermalExponential (β : ℝ) : Operator (Qubit.QubitRegister ι) :=
  (NormedSpace.exp ((-β : ℂ) • LinearMap.toContinuousLinearMap (hamiltonian P Q))).toLinearMap

/-- The canonical energy-basis partition function; equality to the syndrome formula is proved below. -/
def physicalPartition (β : ℝ) : ℝ :=
  gibbsPartitionFunction β (hamiltonianEnergies (hamiltonian P Q) (hamiltonian_symmetric P Q))

theorem physicalPartition_pos (β : ℝ) : 0 < physicalPartition P Q β := by
  letI : Nonempty (Fin (Module.finrank ℂ (Qubit.QubitRegister ι))) :=
    Fin.pos_iff_nonempty.mp Module.finrank_pos
  exact gibbsPartitionFunction_pos _ _

theorem physicalPartition_eq_trace (β : ℝ) :
    (physicalPartition P Q β : ℂ) =
      LinearMap.trace ℂ (Qubit.QubitRegister ι) (thermalExponential P Q β) := by
  letI : Nonempty (Fin (Module.finrank ℂ (Qubit.QubitRegister ι))) :=
    Fin.pos_iff_nonempty.mp Module.finrank_pos
  apply gibbsPartitionFunction_eq_trace_exp
  intro i
  exact (hamiltonian_symmetric P Q).apply_eigenvectorBasis rfl i

theorem gibbs_normalized_exp (β : ℝ) :
    (gibbs P Q β).toOperator = (physicalPartition P Q β : ℂ)⁻¹ • thermalExponential P Q β := by
  letI : Nonempty (Fin (Module.finrank ℂ (Qubit.QubitRegister ι))) :=
    Fin.pos_iff_nonempty.mp Module.finrank_pos
  apply spectralGibbsDensity_normalized_exp
  intro i
  exact (hamiltonian_symmetric P Q).apply_eigenvectorBasis rfl i

private theorem exp_on_vector {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteQuantumSystem V] (A : ContinuousOperator V) (v : V) (lambda z : ℂ)
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

theorem thermalExponential_mul_projector (β : ℝ) (s : Word (ZMod 2) (Sum κP κQ)) :
    thermalExponential P Q β * projector P Q horth s =
      (Real.exp (-β * energy P Q s) : ℂ) • projector P Q horth s := by
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun A : Operator (Qubit.QubitRegister ι) => A x)
    (hamiltonian_mul_projector P Q horth s)
  change NormedSpace.exp ((-β : ℂ) • LinearMap.toContinuousLinearMap (hamiltonian P Q))
      (projector P Q horth s x) = _
  rw [exp_on_vector _ _ _ _ hx]
  simp only [← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_exp]
  rfl

theorem thermalExponential_resolution (β : ℝ) :
    thermalExponential P Q β =
      ∑ s, (Real.exp (-β * energy P Q s) : ℂ) • projector P Q horth s := by
  calc
    _ = thermalExponential P Q β * (∑ s, projector P Q horth s) := by rw [sum_projector, mul_one]
    _ = _ := by simp only [Finset.mul_sum, thermalExponential_mul_projector]

include horth in
theorem physicalPartition_syndrome_sum (β : ℝ) : physicalPartition P Q β =
    multiplicity P Q * ∑ s : Realizable P Q,
      Real.exp (-β * energy P Q (joinSyndrome s.1.val s.2.val)) := by
  have ht := physicalPartition_eq_trace P Q β
  rw [thermalExponential_resolution P Q horth, map_sum] at ht
  simp only [map_smul, smul_eq_mul, trace_projector_formula] at ht
  have hs : (∑ s, (Real.exp (-β * energy P Q s) : ℂ) *
      if s ∈ realizableSyndromes P Q then (multiplicity P Q : ℂ) else 0) =
      ∑ s ∈ realizableSyndromes P Q,
        (Real.exp (-β * energy P Q s) : ℂ) * multiplicity P Q := by
    rw [← Finset.sum_subset (Finset.subset_univ (realizableSyndromes P Q))]
    · apply Finset.sum_congr rfl
      intro s hs; rw [if_pos hs]
    · intro s _ hs; rw [if_neg hs, mul_zero]
  rw [hs, realizableSyndromes, Finset.sum_map] at ht
  simp only [realizableEmbedding_apply] at ht
  rw [← Finset.sum_mul] at ht
  have ht' : physicalPartition P Q β =
      (∑ s : Realizable P Q, Real.exp (-β * energy P Q (joinSyndrome s.1.val s.2.val))) *
        multiplicity P Q := by exact_mod_cast ht
  simpa only [mul_comm] using ht'

include horth in
/-- The factor two is forced by the literal check energies, including redundant rows. -/
theorem physicalPartition_formula (β : ℝ) : physicalPartition P Q β =
    multiplicity P Q * Real.exp (β * (Fintype.card κP + Fintype.card κQ : Nat)) *
      rowPartition P (2 * β) * rowPartition Q (2 * β) := by
  rw [physicalPartition_syndrome_sum P Q horth]
  have he (u : LinearMap.range P) (v : LinearMap.range Q) :
      Real.exp (-β * energy P Q (joinSyndrome u.val v.val)) =
        Real.exp (β * (Fintype.card κP + Fintype.card κQ : Nat)) *
          Real.exp (-(2 * β) * HammingWeight u.val) *
          Real.exp (-(2 * β) * HammingWeight v.val) := by
    rw [energy_joinSyndrome]
    push_cast
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  simp only [Realizable, Fintype.sum_prod_type, he]
  rw [rowPartition, rowPartition]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- Real probability of each literal joint syndrome, with unrealizable words excluded. -/
def jointProbability (β : ℝ) (s : Word (ZMod 2) (Sum κP κQ)) : ℝ :=
  if s ∈ realizableSyndromes P Q then
    Real.exp (-(2 * β) * HammingWeight s) / (rowPartition P (2 * β) * rowPartition Q (2 * β))
  else 0

theorem jointProbability_nonneg (β : ℝ) (s : Word (ZMod 2) (Sum κP κQ)) :
    0 ≤ jointProbability P Q β s := by
  unfold jointProbability
  split_ifs
  · exact div_nonneg (Real.exp_pos _).le (mul_pos (rowPartition_pos P _) (rowPartition_pos Q _)).le
  · exact le_rfl

theorem gibbs_joint_trace (β : ℝ) (s : Word (ZMod 2) (Sum κP κQ)) :
    LinearMap.trace ℂ (Qubit.QubitRegister ι) ((gibbs P Q β).toOperator * projector P Q horth s) =
      (jointProbability P Q β s : ℂ) := by
  rw [gibbs_normalized_exp, smul_mul_assoc, thermalExponential_mul_projector,
    smul_smul, map_smul, smul_eq_mul, trace_projector_formula]
  by_cases hs : s ∈ realizableSyndromes P Q
  · rw [if_pos hs, jointProbability, if_pos hs, physicalPartition_formula P Q horth]
    have hd : (multiplicity P Q : ℝ) ≠ 0 := by exact_mod_cast (multiplicity_pos P Q).ne'
    have he : Real.exp (-β * energy P Q s) =
        Real.exp (β * (Fintype.card κP + Fintype.card κQ : Nat)) *
          Real.exp (-(2 * β) * HammingWeight s) := by
      rw [← Real.exp_add]
      congr 1
      simp only [energy]
      ring
    rw [he]
    push_cast
    have hdC : (multiplicity P Q : ℂ) ≠ 0 := by exact_mod_cast hd
    have heC : (Real.exp (β * (Fintype.card κP + Fintype.card κQ : Nat)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
    have hpC : (rowPartition P (2 * β) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (rowPartition_pos P _).ne'
    have hqC : (rowPartition Q (2 * β) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (rowPartition_pos Q _).ne'
    field_simp
  · rw [if_neg hs, mul_zero, jointProbability, if_neg hs, Complex.ofReal_zero]

/-- A row-sector probability uses only the image of its actual parity-check map. -/
def rowProbability (t : ℝ) (u : LinearMap.range P) : ℝ :=
  Real.exp (-t * HammingWeight u.val) / rowPartition P t

theorem sum_rowProbability (t : ℝ) : (∑ u : LinearMap.range P, rowProbability P t u) = 1 := by
  simp only [rowProbability]
  rw [← Finset.sum_div, ← rowPartition]
  exact div_self (rowPartition_pos P t).ne'

theorem jointProbability_product (β : ℝ) (u : LinearMap.range P) (v : LinearMap.range Q) :
    jointProbability P Q β (joinSyndrome u.val v.val) =
      rowProbability P (2 * β) u * rowProbability Q (2 * β) v := by
  have hs : joinSyndrome u.val v.val ∈ realizableSyndromes P Q :=
    (mem_realizableSyndromes_iff P Q _).mpr ⟨u.property, v.property⟩
  rw [jointProbability, if_pos hs, weight_joinSyndrome]
  push_cast
  rw [mul_add, Real.exp_add, rowProbability, rowProbability, div_mul_div_comm]

/-- The actual projector of any finite bad set of joint syndrome words. -/
def badProjector (B : Finset (Word (ZMod 2) (Sum κP κQ))) : Operator (Qubit.QubitRegister ι) :=
  ∑ s ∈ B, projector P Q horth s

@[simp] theorem badProjector_adjoint (B : Finset (Word (ZMod 2) (Sum κP κQ))) :
    LinearMap.adjoint (badProjector P Q horth B) = badProjector P Q horth B := by
  simp [badProjector]

theorem badProjector_square (B : Finset (Word (ZMod 2) (Sum κP κQ))) :
    badProjector P Q horth B * badProjector P Q horth B = badProjector P Q horth B := by
  simp only [badProjector, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.sum_eq_single s]
  · exact projector_square P Q horth s
  · intro t _ hts; exact projector_mul_of_ne P Q horth t s hts
  · intro hnot; exact (hnot hs).elim

include horth in
theorem sum_jointProbability (β : ℝ) : (∑ s, jointProbability P Q β s) = 1 := by
  have ht : (∑ s, (jointProbability P Q β s : ℂ)) = 1 := by
    calc
      _ = LinearMap.trace ℂ (Qubit.QubitRegister ι)
          ((gibbs P Q β).toOperator * (∑ s, projector P Q horth s)) := by
        simp only [Finset.mul_sum, map_sum, gibbs_joint_trace]
      _ = 1 := by rw [sum_projector, mul_one, (gibbs P Q β).trace_one]
  exact_mod_cast ht

theorem gibbs_bad_trace (β : ℝ) (B : Finset (Word (ZMod 2) (Sum κP κQ))) :
    LinearMap.trace ℂ (Qubit.QubitRegister ι) ((gibbs P Q β).toOperator * badProjector P Q horth B) =
      ((∑ s ∈ B, jointProbability P Q β s : ℝ) : ℂ) := by
  simp only [badProjector, Finset.mul_sum, map_sum, gibbs_joint_trace, Complex.ofReal_sum]

/-- P-sector marginal as a sum of actual joint eigenspace projectors. -/
def pMarginalProjector (u : LinearMap.range P) : Operator (Qubit.QubitRegister ι) :=
  ∑ v : LinearMap.range Q, projector P Q horth (joinSyndrome u.val v.val)

/-- Q-sector marginal as a sum of actual joint eigenspace projectors. -/
def qMarginalProjector (v : LinearMap.range Q) : Operator (Qubit.QubitRegister ι) :=
  ∑ u : LinearMap.range P, projector P Q horth (joinSyndrome u.val v.val)

theorem gibbs_pMarginal_trace (β : ℝ) (u : LinearMap.range P) :
    LinearMap.trace ℂ (Qubit.QubitRegister ι)
      ((gibbs P Q β).toOperator * pMarginalProjector P Q horth u) =
      (rowProbability P (2 * β) u : ℂ) := by
  simp only [pMarginalProjector, Finset.mul_sum, map_sum, gibbs_joint_trace,
    jointProbability_product, Complex.ofReal_mul]
  rw [← Finset.mul_sum, ← Complex.ofReal_sum, sum_rowProbability, Complex.ofReal_one, mul_one]

theorem gibbs_qMarginal_trace (β : ℝ) (v : LinearMap.range Q) :
    LinearMap.trace ℂ (Qubit.QubitRegister ι)
      ((gibbs P Q β).toOperator * qMarginalProjector P Q horth v) =
      (rowProbability Q (2 * β) v : ℂ) := by
  simp only [qMarginalProjector, Finset.mul_sum, map_sum, gibbs_joint_trace,
    jointProbability_product, Complex.ofReal_mul]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, sum_rowProbability, Complex.ofReal_one, one_mul]

end QEC.Coding.CSSGibbs
