import QEC.Semantics.ErrorCorrection.QuditSubsystem
import QEC.Semantics.Channels.Kraus
/-!
# Finite-qudit replacement after erasure

This internal API constructs a CPTP preparation channel for an arbitrary
selected-subsystem density state, then relates its replacement-after-erasure
channel to the concrete finite-qudit partial-trace erasure channel.
-/

noncomputable section

namespace QEC
namespace Semantics
namespace QuditSubsystem

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem quantumChannel_ext {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Phi Psi : QuantumChannel H K) (h : Phi.toLinearMap = Psi.toLinearMap) : Phi = Psi := by
  cases Phi
  cases Psi
  cases h
  rfl

/-- The rank-one preparation branch that inserts `u` on the selected tensor factor. -/
noncomputable def prepareFactorizedBranch (S : QuditSubsystem q) (u : S.selectedSystem) :
    S.complementSystem →ₗ[Complex] S.factorizedSystem :=
  (TensorProduct.mk Complex S.selectedSystem S.complementSystem) u

@[simp]
theorem prepareFactorizedBranch_apply (S : QuditSubsystem q) (u : S.selectedSystem)
    (k : S.complementSystem) :
    S.prepareFactorizedBranch u k = u ⊗ₜ[Complex] k :=
  rfl

/-- A finite rank-one preparation family for a selected-system ensemble. -/
noncomputable def prepareFactorizedKraus (S : QuditSubsystem q) {m : Nat}
    (u : Fin m → S.selectedSystem) :
    FiniteKrausFamily (Fin m) S.complementSystem S.factorizedSystem where
  operator i := S.prepareFactorizedBranch (u i)

@[simp]
theorem prepareFactorizedKraus_operator (S : QuditSubsystem q) {m : Nat}
    (u : Fin m → S.selectedSystem) (i : Fin m) :
    (S.prepareFactorizedKraus u).operator i = S.prepareFactorizedBranch (u i) :=
  rfl

set_option maxHeartbeats 800000 in
theorem adjoint_prepareFactorizedBranch_comp (S : QuditSubsystem q) (u : S.selectedSystem) :
    (LinearMap.adjoint (S.prepareFactorizedBranch u)).comp (S.prepareFactorizedBranch u) =
      (inner Complex u u) • (1 : Operator S.complementSystem) := by
  apply LinearMap.ext
  intro k
  apply (ext_iff_inner_left Complex).mpr
  intro l
  change inner Complex l (LinearMap.adjoint (S.prepareFactorizedBranch u)
    (S.prepareFactorizedBranch u k)) =
      inner Complex l (((inner Complex u u) • (1 : Operator S.complementSystem)) k)
  rw [LinearMap.adjoint_inner_right]
  simp [prepareFactorizedBranch, TensorProduct.inner_tmul]

theorem prepareFactorizedKraus_complete_of_trace_one (S : QuditSubsystem q) {m : Nat}
    (u : Fin m → S.selectedSystem)
    (htrace : ∑ i, inner Complex (u i) (u i) = 1) :
    (S.prepareFactorizedKraus u).Complete := by
  rw [FiniteKrausFamily.Complete]
  simp only [prepareFactorizedKraus_operator, S.adjoint_prepareFactorizedBranch_comp]
  apply LinearMap.ext
  intro k
  calc
    (∑ i, (inner Complex (u i) (u i) • (1 : Operator S.complementSystem))) k =
        (∑ i, inner Complex (u i) (u i)) • k := by
          simp [Finset.sum_smul]
    _ = k := by rw [htrace]; simp

/-- Every finite-dimensional selected density state has a finite rank-one ensemble. -/
theorem density_exists_rankOne_ensemble (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    ∃ (m : Nat) (u : Fin m → S.selectedSystem),
      rho.toOperator = ∑ i, (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap := by
  have hpositive : (LinearMap.toContinuousLinearMap rho.toOperator).IsPositive :=
    (LinearMap.isPositive_toContinuousLinearMap_iff rho.toOperator).2 rho.positive
  rcases (ContinuousLinearMap.isPositive_iff_eq_sum_rankOne).1 hpositive with ⟨m, u, hu⟩
  refine ⟨m, u, ?_⟩
  simpa using congrArg ContinuousLinearMap.toLinearMap hu

/-- The rank-one weights of a density ensemble sum to one. -/
theorem rankOne_ensemble_trace_one (S : QuditSubsystem q) {m : Nat}
    (u : Fin m → S.selectedSystem)
    (rho : DensityOperator S.selectedSystem)
    (hensemble : rho.toOperator =
      ∑ i, (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap) :
    ∑ i, inner Complex (u i) (u i) = 1 := by
  have htrace := rho.trace_one
  rw [hensemble] at htrace
  simpa [map_sum, InnerProductSpace.trace_rankOne] using htrace

noncomputable def densityEnsembleSize (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) : Nat :=
  Classical.choose (S.density_exists_rankOne_ensemble rho)

noncomputable def densityEnsembleVectors (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    Fin (S.densityEnsembleSize rho) → S.selectedSystem :=
  Classical.choose (Classical.choose_spec (S.density_exists_rankOne_ensemble rho))

theorem densityEnsemble_specification (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    rho.toOperator = ∑ i,
      (InnerProductSpace.rankOne Complex (S.densityEnsembleVectors rho i)
        (S.densityEnsembleVectors rho i)).toLinearMap :=
  Classical.choose_spec (Classical.choose_spec (S.density_exists_rankOne_ensemble rho))

theorem densityEnsemble_trace_one (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    ∑ i, inner Complex (S.densityEnsembleVectors rho i) (S.densityEnsembleVectors rho i) = 1 :=
  S.rankOne_ensemble_trace_one (S.densityEnsembleVectors rho) rho
    (S.densityEnsemble_specification rho)

noncomputable def prepareFactorized (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    QuantumChannel S.complementSystem S.factorizedSystem :=
  (S.prepareFactorizedKraus (S.densityEnsembleVectors rho)).toQuantumChannel
    (S.prepareFactorizedKraus_complete_of_trace_one (S.densityEnsembleVectors rho)
      (S.densityEnsemble_trace_one rho))

/-- Prepare the selected tensor factor in `rho`, then return to the global qudit register. -/
noncomputable def prepareSelected (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    QuantumChannel S.complementSystem (Qudit.QuditRegister q) :=
  QuantumChannel.comp (QuantumChannel.unitaryConj S.registerFactorization.symm)
    (S.prepareFactorized rho)

/-- The explicitly normalized maximally mixed density state on the selected qudits. -/
noncomputable def maximallyMixedSelected (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) :
    DensityOperator S.selectedSystem where
  toOperator :=
    ((Module.finrank Complex S.selectedSystem : Complex)⁻¹) •
      (1 : Operator S.selectedSystem)
  positive := by
    have hdim_nonneg : 0 ≤ (Module.finrank Complex S.selectedSystem : Complex) := by
      exact_mod_cast Nat.zero_le (Module.finrank Complex S.selectedSystem)
    exact LinearMap.isPositive_one.smul_of_nonneg ((inv_nonneg).2 hdim_nonneg)
  trace_one := by
    have hdim : (Module.finrank Complex S.selectedSystem : Complex) ≠ 0 :=
      Qudit.finrank_quditRegister_ne_zero S.selectedDimensions (fun i => hq i)
    rw [map_smul, LinearMap.trace_one]
    exact inv_mul_cancel₀ hdim

theorem maximallyMixedSelected_trace_one (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) :
    LinearMap.trace Complex S.selectedSystem (S.maximallyMixedSelected hq).toOperator = 1 :=
  (S.maximallyMixedSelected hq).trace_one

/-- A density-parametric finite-qudit replacement channel is preparation after erasure. -/
noncomputable def replacementAfterErasureWith (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    QuantumChannel (Qudit.QuditRegister q) (Qudit.QuditRegister q) :=
  QuantumChannel.comp (S.prepareSelected rho) S.erasureChannelFromRegister

/-- The canonical same-space replacement channel: maximally mixed preparation after erasure. -/
noncomputable def replacementAfterErasure (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) :
    QuantumChannel (Qudit.QuditRegister q) (Qudit.QuditRegister q) :=
  S.replacementAfterErasureWith (S.maximallyMixedSelected hq)

theorem prepareFactorized_apply_rankOne (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) (k l : S.complementSystem) :
    S.prepareFactorized rho
        (InnerProductSpace.rankOne Complex k l).toLinearMap =
      ∑ i, (InnerProductSpace.rankOne Complex
        (S.densityEnsembleVectors rho i ⊗ₜ[Complex] k)
        (S.densityEnsembleVectors rho i ⊗ₜ[Complex] l)).toLinearMap := by
  unfold prepareFactorized
  rw [FiniteKrausFamily.toQuantumChannel_apply_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply LinearMap.ext
  intro x
  simp [prepareFactorizedKraus_operator, LinearMap.comp_apply,
    InnerProductSpace.rankOne_apply, LinearMap.adjoint_inner_right]

theorem erasureChannel_prepareFactorized_apply_rankOne (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) (k l : S.complementSystem) :
    S.erasureChannel
      (S.prepareFactorized rho (InnerProductSpace.rankOne Complex k l).toLinearMap) =
      (InnerProductSpace.rankOne Complex k l).toLinearMap := by
  rw [S.prepareFactorized_apply_rankOne rho k l]
  simp only [erasureChannel, QuantumChannel.comp_apply, QuantumChannel.unitaryConj_apply, map_sum]
  simp only [conjOperator_rankOne, factorSwap_apply_tmul,
    partialTraceRightRaw_cptp_toLinearMap, partialTraceRightRaw_rankOne_tmul]
  rw [← Finset.sum_smul, S.densityEnsemble_trace_one]
  simp

theorem erasureChannel_prepareFactorized_apply (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) (A : Operator S.complementSystem) :
    S.erasureChannel (S.prepareFactorized rho A) = A := by
  let b := stdOrthonormalBasis Complex S.complementSystem
  rw [operator_eq_sum_rankOne_basis S.complementSystem b A]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact S.erasureChannel_prepareFactorized_apply_rankOne rho (A (b i)) (b i)

theorem erasureChannelFromRegister_prepareSelected_apply (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) (A : Operator S.complementSystem) :
    S.erasureChannelFromRegister (S.prepareSelected rho A) = A := by
  simp only [erasureChannelFromRegister, prepareSelected, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply]
  rw [S.registerFactorization.conjOperator_symm_conjOperator]
  exact S.erasureChannel_prepareFactorized_apply rho A

theorem erasureChannelFromRegister_comp_prepareSelected (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    QuantumChannel.comp S.erasureChannelFromRegister (S.prepareSelected rho) =
      QuantumChannel.id S.complementSystem := by
  apply quantumChannel_ext
  apply LinearMap.ext
  intro A
  exact S.erasureChannelFromRegister_prepareSelected_apply rho A

theorem replacementRecovery_transfers_to_erasure (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) (C : QuantumCode (Qudit.QuditRegister q))
    (replacementRecovery : QuantumChannel (Qudit.QuditRegister q) (Qudit.QuditRegister q)) :
    Correctable (Qudit.QuditRegister q) (Qudit.QuditRegister q) C
      (S.replacementAfterErasureWith rho) replacementRecovery →
    Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister
      (QuantumChannel.comp replacementRecovery (S.prepareSelected rho)) := by
  intro h rhoGlobal hSupported
  change replacementRecovery
    (S.prepareSelected rho (S.erasureChannelFromRegister rhoGlobal.toOperator)) =
      rhoGlobal.toOperator
  exact h rhoGlobal hSupported

theorem erasureRecovery_transfers_to_replacement (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) (C : QuantumCode (Qudit.QuditRegister q))
    (erasureRecovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q)) :
    Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister erasureRecovery →
    Correctable (Qudit.QuditRegister q) (Qudit.QuditRegister q) C
      (S.replacementAfterErasureWith rho)
      (QuantumChannel.comp erasureRecovery S.erasureChannelFromRegister) := by
  intro h rhoGlobal hSupported
  change erasureRecovery (S.erasureChannelFromRegister
    (S.prepareSelected rho (S.erasureChannelFromRegister rhoGlobal.toOperator))) =
      rhoGlobal.toOperator
  rw [S.erasureChannelFromRegister_prepareSelected_apply rho]
  exact h rhoGlobal hSupported

theorem exists_recovery_replacementAfterErasureWith_iff_exists_recovery_erasure
    (S : QuditSubsystem q) (rho : DensityOperator S.selectedSystem)
    (C : QuantumCode (Qudit.QuditRegister q)) :
    (∃ replacementRecovery : QuantumChannel (Qudit.QuditRegister q) (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) (Qudit.QuditRegister q) C
        (S.replacementAfterErasureWith rho) replacementRecovery) ↔
    (∃ erasureRecovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) S.complementSystem C
        S.erasureChannelFromRegister erasureRecovery) := by
  constructor
  · rintro ⟨replacementRecovery, hRecovery⟩
    exact ⟨QuantumChannel.comp replacementRecovery (S.prepareSelected rho),
      S.replacementRecovery_transfers_to_erasure rho C replacementRecovery hRecovery⟩
  · rintro ⟨erasureRecovery, hRecovery⟩
    exact ⟨QuantumChannel.comp erasureRecovery S.erasureChannelFromRegister,
      S.erasureRecovery_transfers_to_replacement rho C erasureRecovery hRecovery⟩

theorem exists_recovery_replacementAfterErasure_iff_exists_recovery_erasure
    (S : QuditSubsystem q) (hq : ∀ i, 0 < q i)
    (C : QuantumCode (Qudit.QuditRegister q)) :
    (∃ replacementRecovery : QuantumChannel (Qudit.QuditRegister q) (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) (Qudit.QuditRegister q) C
        (S.replacementAfterErasure hq) replacementRecovery) ↔
    (∃ erasureRecovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) S.complementSystem C
        S.erasureChannelFromRegister erasureRecovery) := by
  simpa [replacementAfterErasure] using
    S.exists_recovery_replacementAfterErasureWith_iff_exists_recovery_erasure
      (S.maximallyMixedSelected hq) C

end QuditSubsystem
end Semantics
end QEC
