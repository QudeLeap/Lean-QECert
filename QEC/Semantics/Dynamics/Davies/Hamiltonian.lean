import QEC.Semantics.Dynamics.Davies.NormBound
import QEC.Semantics.Dynamics.ProtectedObservableDecay

/-! # The finite Davies bath constructed from an actual Hamiltonian -/

namespace QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]

/-- Canonical energy gaps of the given self-adjoint Hamiltonian. -/
abbrev HamiltonianFrequency (H : Operator V) (hH : H.IsSymmetric) :=
  Frequency (hamiltonianEnergies H hH)

/-- Actual frequency jumps with square-root rates, before calling the existing
operator-valued Lindblad API. -/
def hamiltonianJump (H : Operator V) (hH : H.IsSymmetric) (A : κ → Operator V)
    (rate : κ → HamiltonianFrequency H hH → ℝ) : κ × HamiltonianFrequency H hH → Operator V :=
  weightedJump (hamiltonianBasis H hH) (hamiltonianEnergies H hH) A rate

/-- A multiplicity-correct Gibbs density of the actual Hamiltonian. -/
def hamiltonianGibbs (H : Operator V) (hH : H.IsSymmetric) (β : ℝ) : DensityOperator V := by
  letI : Nonempty (Fin (Module.finrank ℂ V)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  exact spectralGibbsDensity (hamiltonianBasis H hH) (hamiltonianEnergies H hH) β

/-- The Davies generator here is precisely the dissipative part. -/
def hamiltonianDissipator (H : Operator V) (hH : H.IsSymmetric) (A : κ → Operator V)
    (rate : κ → HamiltonianFrequency H hH → ℝ) : Superoperator V :=
  lindbladDissipator (hamiltonianJump H hH A rate)

theorem hamiltonianGibbs_commutes (H : Operator V) (hH : H.IsSymmetric) (β : ℝ) :
    Commute H (hamiltonianGibbs H hH β).toOperator := by
  letI : Nonempty (Fin (Module.finrank ℂ V)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  simpa only [hamiltonian_diagonal, hamiltonianGibbs] using
    hamiltonian_commutes_gibbs (hamiltonianBasis H hH) (hamiltonianEnergies H hH) β

theorem hamiltonianGibbs_stationary (H : Operator V) (hH : H.IsSymmetric)
    (A : κ → Operator V) (hA : ∀ a, (A a).IsSymmetric)
    (rate : κ → HamiltonianFrequency H hH → ℝ) (β : ℝ)
    (hn : ∀ a w, 0 ≤ rate a w)
    (hDB : ∀ a w, rate a (negFrequency (hamiltonianEnergies H hH) w) =
      Real.exp (-β*w.val) * rate a w) :
    hamiltonianDissipator H hH A rate (hamiltonianGibbs H hH β).toOperator = 0 := by
  letI : Nonempty (Fin (Module.finrank ℂ V)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  exact weightedJump_gibbs_stationary (hamiltonianBasis H hH) (hamiltonianEnergies H hH)
    β A rate hn hA hDB

theorem hamiltonianJump_protected (H : Operator V) (hH : H.IsSymmetric)
    (A : κ → Operator V) (rate : κ → HamiltonianFrequency H hH → ℝ)
    (O P : Operator V) (hO : Commute H O) (hP : Commute H P)
    (hAP : ∀ a, (A a * O - O * A a) * P = 0) :
    JumpProtected (hamiltonianJump H hH A rate) O P := by
  letI : Nonempty (Fin (Module.finrank ℂ V)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  apply weightedJump_protected
  · simpa only [hamiltonian_diagonal] using hO
  · simpa only [hamiltonian_diagonal] using hP
  · exact hAP

/-- The constant counts couplings, even with arbitrarily many or degenerate gaps. -/
theorem hamiltonianDissipator_selfAdjointTraceNorm_le
    (H : Operator V) (hH : H.IsSymmetric) (A : κ → Operator V)
    (hA : ∀ a, operatorNorm (A a) ≤ 1)
    (rate : κ → HamiltonianFrequency H hH → ℝ) (hmax : ℝ)
    (hm : 0 ≤ hmax) (hn : ∀ a w, 0 ≤ rate a w) (hu : ∀ a w, rate a w ≤ hmax) :
    selfAdjointTraceNormOneToOne (hamiltonianDissipator H hH A rate) ≤
      2 * Fintype.card κ * hmax :=
  weightedJump_dissipatorNorm_le (hamiltonianBasis H hH) (hamiltonianEnergies H hH)
    A hA rate hmax hm hn hu

/-- Compatibility with any genuine eigenbasis, including the M11 factorization
basis; no equality of Gibbs states is an input hypothesis. -/
theorem hamiltonianGibbs_eq_spectralGibbsDensity {ι : Type} [Fintype ι] [Nonempty ι]
    (H : Operator V) (hH : H.IsSymmetric) (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (heigen : ∀ i, H (b i) = (e i : ℂ) • b i) (β : ℝ) :
    (hamiltonianGibbs H hH β).toOperator = (spectralGibbsDensity b e β).toOperator := by
  letI : Nonempty (Fin (Module.finrank ℂ V)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  apply spectralGibbsDensity_basis_independent H
  · intro i
    exact hH.apply_eigenvectorBasis rfl i
  · exact heigen

/-- The existing M11 physical Gibbs density is the one fixed by this Davies bath. -/
theorem hamiltonianGibbs_eq_physicalGibbsState (logical : PauliLikePair V)
    (H : Operator V) (hH : H.IsSymmetric) (hX : Commute H logical.x)
    (hZ : Commute H logical.z) (β : ℝ) :
    (hamiltonianGibbs H hH β).toOperator =
      (logical.physicalGibbsState H hZ hH β).toOperator := by
  letI : Nonempty (Fin (Module.finrank ℂ logical.AuxiliarySpace)) :=
    Fin.pos_iff_nonempty.mp Module.finrank_pos
  apply hamiltonianGibbs_eq_spectralGibbsDensity
  exact logical.physicalHamiltonianEigenbasis_apply H hX hZ hH

/-- The complete energy projector of the actual self-adjoint Hamiltonian. -/
def hamiltonianEnergyProjector (H : Operator V) (hH : H.IsSymmetric) (E : ℝ) : Operator V :=
  energyProjector (hamiltonianBasis H hH) (hamiltonianEnergies H hH) E

theorem hamiltonianEnergyProjector_fixed_iff (H : Operator V) (hH : H.IsSymmetric)
    (E : ℝ) (x : V) :
    hamiltonianEnergyProjector H hH E x = x ↔ H x = (E : ℂ) • x := by
  simpa only [hamiltonianEnergyProjector, hamiltonian_diagonal] using
    energyProjector_fixed_iff (hamiltonianBasis H hH) (hamiltonianEnergies H hH) x E

theorem hamiltonianEnergyProjector_commute (H : Operator V) (hH : H.IsSymmetric)
    (O : Operator V) (hO : Commute H O) (E : ℝ) :
    Commute (hamiltonianEnergyProjector H hH E) O := by
  apply energyProjector_commute
  simpa only [hamiltonian_diagonal] using hO

end
end QEC.Semantics.Davies
