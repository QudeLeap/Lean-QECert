import QEC.Semantics.Channels.Core
import QEC.Semantics.Core.Qubit
/-!
# Finite coordinate subsystems and erasure semantics

This module models a selected finite set of qubit coordinates by its actual
register and the register of its finite complement.  The ambient system is
definitionally their tensor product, so local operators and erasure channels
cannot be introduced on an unrelated Hilbert space.
-/

noncomputable section

namespace QEC
namespace Semantics

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u

/-- A finite selected subsystem of a finite coordinate type. -/
structure FiniteSubsystem (ι : Type u) [Fintype ι] [DecidableEq ι] where
  selected : Finset ι

namespace FiniteSubsystem

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The coordinates retained by a finite subsystem. -/
abbrev SelectedCoordinates (S : FiniteSubsystem ι) : Type u :=
  {i : ι // i ∈ S.selected}

/-- The coordinates discarded by a finite subsystem. -/
abbrev ComplementCoordinates (S : FiniteSubsystem ι) : Type u :=
  {i : ι // i ∉ S.selected}

/-- The selected coordinate register. -/
abbrev selectedSystem (S : FiniteSubsystem ι) : Type u :=
  Qubit.QubitRegister S.SelectedCoordinates

/-- The complement coordinate register. -/
abbrev complementSystem (S : FiniteSubsystem ι) : Type u :=
  Qubit.QubitRegister S.ComplementCoordinates

/--
The ambient system for a selected subsystem.  This is an actual tensor product
of the selected and complement registers, not an arbitrary system equipped
with a support predicate.
-/
abbrev factorizedSystem (S : FiniteSubsystem ι) : Type u :=
  CompositeSystem S.selectedSystem S.complementSystem

/-- Restrict a global computational-basis label to the two coordinate factors. -/
def splitBitstring (S : FiniteSubsystem ι) (bits : Qubit.Bitstring ι) :
    Qubit.Bitstring S.SelectedCoordinates × Qubit.Bitstring S.ComplementCoordinates :=
  (fun i => bits i, fun i => bits i)

/-- Recombine selected and complement computational-basis labels. -/
def recombineBitstring (S : FiniteSubsystem ι)
    (bits : Qubit.Bitstring S.SelectedCoordinates × Qubit.Bitstring S.ComplementCoordinates) :
    Qubit.Bitstring ι :=
  fun i => if hi : i ∈ S.selected then bits.1 ⟨i, hi⟩ else bits.2 ⟨i, hi⟩

/-- The selected/complement coordinate split is a concrete equivalence of basis labels. -/
def bitstringFactorization (S : FiniteSubsystem ι) :
    Qubit.Bitstring ι ≃
      Qubit.Bitstring S.SelectedCoordinates × Qubit.Bitstring S.ComplementCoordinates where
  toFun := S.splitBitstring
  invFun := S.recombineBitstring
  left_inv := by
    intro bits
    funext i
    by_cases hi : i ∈ S.selected <;> simp [splitBitstring, recombineBitstring, hi]
  right_inv := by
    rintro ⟨left, right⟩
    apply Prod.ext
    · funext i
      simp [splitBitstring, recombineBitstring]
    · funext i
      have hi : (i : ι) ∉ S.selected := i.property
      simp [splitBitstring, recombineBitstring, hi]

/--
The concrete unitary factorization from the global coordinate register to the
selected/complement tensor-product system.
-/
noncomputable def registerFactorization (S : FiniteSubsystem ι) :
    UnitaryTransport (Qubit.QubitRegister ι) S.factorizedSystem := by
  let sourceBasis := EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
  let selectedBasis := EuclideanSpace.basisFun (Qubit.Bitstring S.SelectedCoordinates) Complex
  let complementBasis :=
    EuclideanSpace.basisFun (Qubit.Bitstring S.ComplementCoordinates) Complex
  let targetBasis := selectedBasis.tensorProduct complementBasis
  let U := sourceBasis.equiv targetBasis S.bitstringFactorization
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

/-- The unitary coordinate factorization maps each global basis label to its selected/complement tensor. -/
theorem registerFactorization_apply_basis (S : FiniteSubsystem ι)
    (bits : Qubit.Bitstring ι) :
    S.registerFactorization (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex bits) =
      (EuclideanSpace.basisFun (Qubit.Bitstring S.SelectedCoordinates) Complex
        (S.splitBitstring bits).1) ⊗ₜ[Complex]
      (EuclideanSpace.basisFun (Qubit.Bitstring S.ComplementCoordinates) Complex
        (S.splitBitstring bits).2) := by
  dsimp [registerFactorization]
  rw [OrthonormalBasis.equiv_apply_basis]
  rw [OrthonormalBasis.tensorProduct_apply']
  simp [bitstringFactorization]

@[simp]
theorem card_selectedCoordinates (S : FiniteSubsystem ι) :
    Fintype.card S.SelectedCoordinates = S.selected.card := by
  simp [SelectedCoordinates]

@[simp]
theorem card_complementCoordinates (S : FiniteSubsystem ι) :
    Fintype.card S.ComplementCoordinates = S.selectedᶜ.card := by
  simp [ComplementCoordinates]
  exact S.selected.card_compl.symm

/-- Selected and complement coordinate cardinalities partition the full coordinate count. -/
theorem card_selected_add_card_complement (S : FiniteSubsystem ι) :
    Fintype.card S.SelectedCoordinates + Fintype.card S.ComplementCoordinates =
      Fintype.card ι := by
  rw [S.card_selectedCoordinates, S.card_complementCoordinates]
  exact S.selected.card_add_card_compl

/-- A selected finite coordinate set has cardinality at most the full coordinate type. -/
theorem card_selected_le_total (S : FiniteSubsystem ι) :
    Fintype.card S.SelectedCoordinates ≤ Fintype.card ι := by
  simpa using S.selected.card_le_univ

/-- The distinguished complement basis-vector index used for local restriction. -/
def complementBasisIndex (S : FiniteSubsystem ι) :
    Fin (Module.finrank Complex S.complementSystem) :=
  ⟨0, by
    rw [Qubit.finrank_qubitRegister]
    exact Nat.pow_pos (by norm_num : 0 < (2 : Nat))⟩

/-- A unit computational-basis vector in the complement register. -/
noncomputable def complementAnchor (S : FiniteSubsystem ι) : S.complementSystem :=
  (stdOrthonormalBasis Complex S.complementSystem) S.complementBasisIndex

/-- Embed selected-register vectors with the fixed complement anchor. -/
noncomputable def localEmbedding (S : FiniteSubsystem ι) :
    S.selectedSystem →ₗ[Complex] S.factorizedSystem :=
  (TensorProduct.mk Complex S.selectedSystem S.complementSystem).flip S.complementAnchor

@[simp]
theorem localEmbedding_apply (S : FiniteSubsystem ι) (h : S.selectedSystem) :
    S.localEmbedding h = h ⊗ₜ[Complex] S.complementAnchor :=
  rfl

theorem adjoint_localEmbedding_tmul (S : FiniteSubsystem ι)
    (h : S.selectedSystem) (k : S.complementSystem) :
    LinearMap.adjoint S.localEmbedding (h ⊗ₜ[Complex] k) =
      (inner Complex S.complementAnchor k) • h := by
  apply (ext_iff_inner_left Complex).mpr
  intro x
  rw [LinearMap.adjoint_inner_right]
  simp [localEmbedding, TensorProduct.inner_tmul, inner_smul_right, mul_comm]

/-- Extend a selected-register operator by the identity on the complement. -/
noncomputable def extendLocal (S : FiniteSubsystem ι) (A : Operator S.selectedSystem) :
    Operator S.factorizedSystem :=
  TensorProduct.map A (LinearMap.id : S.complementSystem →ₗ[Complex] S.complementSystem)

/-- Extend a local operator all the way to the original global coordinate register. -/
noncomputable def extendLocalToRegister (S : FiniteSubsystem ι)
    (A : Operator S.selectedSystem) : Operator (Qubit.QubitRegister ι) :=
  S.registerFactorization.symm.conjOperator (S.extendLocal A)

@[simp]
theorem extendLocal_apply_localEmbedding (S : FiniteSubsystem ι)
    (A : Operator S.selectedSystem) (h : S.selectedSystem) :
    S.extendLocal A (S.localEmbedding h) = S.localEmbedding (A h) := by
  simp [extendLocal, localEmbedding]

/-- Restrict an ambient operator by compression through the concrete complement anchor. -/
noncomputable def restrictLocal (S : FiniteSubsystem ι) (A : Operator S.factorizedSystem) :
    Operator S.selectedSystem :=
  (LinearMap.adjoint S.localEmbedding).comp (A.comp S.localEmbedding)

/-- Restrict a global-register operator through the concrete coordinate factorization. -/
noncomputable def restrictLocalFromRegister (S : FiniteSubsystem ι)
    (A : Operator (Qubit.QubitRegister ι)) : Operator S.selectedSystem :=
  S.restrictLocal (S.registerFactorization.conjOperator A)

/-- Restriction is a left inverse to identity extension of local operators. -/
theorem restrictLocal_extendLocal (S : FiniteSubsystem ι) (A : Operator S.selectedSystem) :
    S.restrictLocal (S.extendLocal A) = A := by
  apply LinearMap.ext
  intro h
  change LinearMap.adjoint S.localEmbedding
      (S.extendLocal A (S.localEmbedding h)) = A h
  rw [S.extendLocal_apply_localEmbedding, S.localEmbedding_apply,
    S.adjoint_localEmbedding_tmul]
  simp [complementAnchor]

/-- Global-register restriction is a left inverse to local extension. -/
theorem restrictLocalFromRegister_extendLocalToRegister (S : FiniteSubsystem ι)
    (A : Operator S.selectedSystem) :
    S.restrictLocalFromRegister (S.extendLocalToRegister A) = A := by
  unfold restrictLocalFromRegister extendLocalToRegister
  rw [S.registerFactorization.conjOperator_symm_conjOperator]
  exact S.restrictLocal_extendLocal A

/-- Identity extension of local operators is injective. -/
theorem extendLocal_injective (S : FiniteSubsystem ι) : Function.Injective S.extendLocal := by
  intro A B h
  have hrestricted := congrArg S.restrictLocal h
  simpa only [S.restrictLocal_extendLocal] using hrestricted

/-- Local extension to the global coordinate register is injective. -/
theorem extendLocalToRegister_injective (S : FiniteSubsystem ι) :
    Function.Injective S.extendLocalToRegister := by
  intro A B h
  have hrestricted := congrArg S.restrictLocalFromRegister h
  simpa only [S.restrictLocalFromRegister_extendLocalToRegister] using hrestricted

/-- An ambient operator is supported on the selected coordinates when it is an identity extension. -/
def OperatorSupportedOn (S : FiniteSubsystem ι) (A : Operator S.factorizedSystem) : Prop :=
  ∃ A_local : Operator S.selectedSystem, S.extendLocal A_local = A

/-- A global-register operator is supported on the selected coordinates via the concrete factorization. -/
def OperatorSupportedOnRegister (S : FiniteSubsystem ι)
    (A : Operator (Qubit.QubitRegister ι)) : Prop :=
  ∃ A_local : Operator S.selectedSystem, S.extendLocalToRegister A_local = A

theorem extendLocal_operatorSupportedOn (S : FiniteSubsystem ι)
    (A : Operator S.selectedSystem) :
    S.OperatorSupportedOn (S.extendLocal A) :=
  ⟨A, rfl⟩

theorem extendLocalToRegister_operatorSupportedOn (S : FiniteSubsystem ι)
    (A : Operator S.selectedSystem) :
    S.OperatorSupportedOnRegister (S.extendLocalToRegister A) :=
  ⟨A, rfl⟩

/-- The concrete restriction reconstructs exactly the operators supported on the selected system. -/
theorem operatorSupportedOn_iff_extend_restrict (S : FiniteSubsystem ι)
    (A : Operator S.factorizedSystem) :
    S.OperatorSupportedOn A ↔ S.extendLocal (S.restrictLocal A) = A := by
  constructor
  · rintro ⟨A_local, rfl⟩
    rw [S.restrictLocal_extendLocal]
  · intro h
    exact ⟨S.restrictLocal A, h⟩

/-- The register-level restriction reconstructs exactly the selected-supported global operators. -/
theorem operatorSupportedOnRegister_iff_extend_restrict (S : FiniteSubsystem ι)
    (A : Operator (Qubit.QubitRegister ι)) :
    S.OperatorSupportedOnRegister A ↔
      S.extendLocalToRegister (S.restrictLocalFromRegister A) = A := by
  constructor
  · rintro ⟨A_local, rfl⟩
    rw [S.restrictLocalFromRegister_extendLocalToRegister]
  · intro h
    exact ⟨S.restrictLocalFromRegister A, h⟩

/-- The selected-subsystem partial trace, with concrete ambient source and selected target. -/
noncomputable def selectedPartialTrace (S : FiniteSubsystem ι) :
    QuantumChannel S.factorizedSystem S.selectedSystem :=
  partialTraceRightRaw_cptp S.selectedSystem S.complementSystem

/-- Swap the selected and complement tensor factors before tracing out the selected factor. -/
noncomputable def factorSwap (S : FiniteSubsystem ι) :
    UnitaryTransport S.factorizedSystem
      (CompositeSystem S.complementSystem S.selectedSystem) := by
  let U := TensorProduct.commIsometry Complex S.selectedSystem S.complementSystem
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

/--
The erasure channel for the selected coordinates: it discards the selected
factor and retains the concrete complement register.
-/
noncomputable def erasureChannel (S : FiniteSubsystem ι) :
    QuantumChannel S.factorizedSystem S.complementSystem :=
  QuantumChannel.comp
    (partialTraceRightRaw_cptp S.complementSystem S.selectedSystem)
    (QuantumChannel.unitaryConj S.factorSwap)

/-- The selected-subsystem partial trace with the original global register as its source. -/
noncomputable def selectedPartialTraceFromRegister (S : FiniteSubsystem ι) :
    QuantumChannel (Qubit.QubitRegister ι) S.selectedSystem :=
  QuantumChannel.comp S.selectedPartialTrace
    (QuantumChannel.unitaryConj S.registerFactorization)

/-- The selected-coordinate erasure channel with the original global register as its source. -/
noncomputable def erasureChannelFromRegister (S : FiniteSubsystem ι) :
    QuantumChannel (Qubit.QubitRegister ι) S.complementSystem :=
  QuantumChannel.comp S.erasureChannel
    (QuantumChannel.unitaryConj S.registerFactorization)

@[simp]
theorem selectedPartialTrace_toLinearMap (S : FiniteSubsystem ι) :
    S.selectedPartialTrace.toLinearMap =
      partialTraceRightRaw S.selectedSystem S.complementSystem :=
  rfl

/-- The raw partial trace normalized by the finite complement dimension. -/
noncomputable def normalizedSelectedPartialTrace (S : FiniteSubsystem ι) :
    Operator S.factorizedSystem →ₗ[Complex] Operator S.selectedSystem :=
  (Module.finrank Complex S.complementSystem : Complex)⁻¹ •
    partialTraceRightRaw S.selectedSystem S.complementSystem

theorem complementFinrank_ne_zero (S : FiniteSubsystem ι) :
    (Module.finrank Complex S.complementSystem : Complex) ≠ 0 := by
  rw [Qubit.finrank_qubitRegister]
  norm_cast
  exact Nat.ne_of_gt (Nat.pow_pos (by norm_num : 0 < (2 : Nat)))

/-- The normalized selected partial trace recovers an identity-extended local operator. -/
theorem normalizedSelectedPartialTrace_extendLocal (S : FiniteSubsystem ι)
    (A : Operator S.selectedSystem) :
    S.normalizedSelectedPartialTrace (S.extendLocal A) = A := by
  change (Module.finrank Complex S.complementSystem : Complex)⁻¹ •
      (partialTraceRightRaw S.selectedSystem S.complementSystem)
        (TensorProduct.map A
          (LinearMap.id : S.complementSystem →ₗ[Complex] S.complementSystem)) = A
  rw [partialTraceRightRaw_tensor_id]
  rw [← mul_smul, inv_mul_cancel₀ S.complementFinrank_ne_zero, one_smul]

/-- Exact recovery for the selected-subsystem erasure channel, in the M2 channel vocabulary. -/
def ErasureCorrectable (S : FiniteSubsystem ι) (C : QuantumCode S.factorizedSystem)
    (recovery : QuantumChannel S.complementSystem S.factorizedSystem) : Prop :=
  Correctable S.factorizedSystem S.complementSystem C S.erasureChannel recovery

/-- Exact erasure recovery for a code on the original global coordinate register. -/
def ErasureCorrectableFromRegister (S : FiniteSubsystem ι)
    (C : QuantumCode (Qubit.QubitRegister ι))
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι)) : Prop :=
  Correctable (Qubit.QubitRegister ι) S.complementSystem C S.erasureChannelFromRegister recovery

/-- Global-register erasure correctability is definitionally the M2 `Correctable` predicate. -/
theorem erasureCorrectableFromRegister_iff (S : FiniteSubsystem ι)
    (C : QuantumCode (Qubit.QubitRegister ι))
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι)) :
    S.ErasureCorrectableFromRegister C recovery ↔
      Correctable (Qubit.QubitRegister ι) S.complementSystem C
        S.erasureChannelFromRegister recovery :=
  Iff.rfl

/-- Erasure correctability is definitionally the existing M2 `Correctable` predicate. -/
theorem erasureCorrectable_iff (S : FiniteSubsystem ι) (C : QuantumCode S.factorizedSystem)
    (recovery : QuantumChannel S.complementSystem S.factorizedSystem) :
    S.ErasureCorrectable C recovery ↔
      Correctable S.factorizedSystem S.complementSystem C S.erasureChannel recovery :=
  Iff.rfl

/-- A code admits an exact recovery channel after erasing the selected subsystem. -/
def ErasureRecoverable (S : FiniteSubsystem ι) (C : QuantumCode S.factorizedSystem) : Prop :=
  ∃ recovery : QuantumChannel S.complementSystem S.factorizedSystem,
    S.ErasureCorrectable C recovery

/-- A global-register code admits exact recovery after selected-subsystem erasure. -/
def ErasureRecoverableFromRegister (S : FiniteSubsystem ι)
    (C : QuantumCode (Qubit.QubitRegister ι)) : Prop :=
  ∃ recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι),
    S.ErasureCorrectableFromRegister C recovery

/-- Existential erasure recoverability stays in the M2 channel/correctability vocabulary. -/
theorem erasureRecoverable_iff_exists_correctable (S : FiniteSubsystem ι)
    (C : QuantumCode S.factorizedSystem) :
    S.ErasureRecoverable C ↔
      ∃ recovery : QuantumChannel S.complementSystem S.factorizedSystem,
        Correctable S.factorizedSystem S.complementSystem C S.erasureChannel recovery :=
  Iff.rfl

/-- Global-register erasure recoverability is stated directly with M2 `Correctable`. -/
theorem erasureRecoverableFromRegister_iff_exists_correctable (S : FiniteSubsystem ι)
    (C : QuantumCode (Qubit.QubitRegister ι)) :
    S.ErasureRecoverableFromRegister C ↔
      ∃ recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι) S.complementSystem C
          S.erasureChannelFromRegister recovery :=
  Iff.rfl

end FiniteSubsystem

end Semantics
end QEC
