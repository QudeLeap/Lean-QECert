import QEC.Semantics.Channels.Core
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite-qudit coordinate subsystems and erasure semantics

This module supplies the canonical finite-dimensional qudit substrate used by
the M4 locality interfaces.  A register is the computational-basis Hilbert
space indexed by the product of its site-wise finite alphabets.  Every region
is factored concretely into its selected and complementary coordinates before
any local operation or erasure channel is defined.
-/

noncomputable section

namespace QEC
namespace Semantics

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace Qudit

/-- Computational-basis labels for a finite register with site-wise local dimensions. -/
abbrev Label {ι : Type u} (q : ι → Nat) : Type u :=
  ∀ i, Fin (q i)

/-- The canonical finite qudit register with computational basis indexed by `Label q`. -/
abbrev QuditRegister {ι : Type u} [Fintype ι] (q : ι → Nat) : Type u :=
  EuclideanSpace Complex (Label q)

/-- The all-zero computational-basis label supplied by strictly positive local dimensions. -/
def zeroLabel {ι : Type u} (q : ι → Nat) (hq : ∀ i, 0 < q i) : Label q :=
  fun i => ⟨0, hq i⟩

/-- Positive local dimensions make the product computational-basis index nonempty. -/
theorem label_nonempty {ι : Type u} [Fintype ι] (q : ι → Nat) (hq : ∀ i, 0 < q i) :
    Nonempty (Label q) :=
  ⟨zeroLabel q hq⟩

/-- A canonical finite qudit register has nonzero finite complex dimension. -/
theorem finrank_quditRegister_ne_zero {ι : Type u} [Fintype ι]
    (q : ι → Nat) (hq : ∀ i, 0 < q i) :
    (Module.finrank Complex (QuditRegister q) : Complex) ≠ 0 := by
  letI : Nonempty (Label q) := label_nonempty q hq
  rw [finrank_euclideanSpace]
  exact_mod_cast Nat.ne_of_gt Fintype.card_pos

end Qudit

/-- A finite selected subsystem of a finite qudit-coordinate register. -/
structure QuditSubsystem {ι : Type u} [Fintype ι] [DecidableEq ι]
    (q : ι → Nat) where
  selected : Finset ι

namespace QuditSubsystem

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

/-- The raw partial trace of a rank-one tensor operator contracts its right factor. -/
theorem partialTraceRightRaw_rankOne_tmul (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (h h' : H) (k k' : K) :
    partialTraceRightRaw H K
      (InnerProductSpace.rankOne Complex (h ⊗ₜ[Complex] k) (h' ⊗ₜ[Complex] k')).toLinearMap =
      (inner Complex k' k) • (InnerProductSpace.rankOne Complex h h').toLinearMap := by
  let fh : Module.Dual Complex H := (innerSL Complex h').toLinearMap
  let fk : Module.Dual Complex K := (innerSL Complex k').toLinearMap
  have hRank :
      (InnerProductSpace.rankOne Complex (h ⊗ₜ[Complex] k) (h' ⊗ₜ[Complex] k')).toLinearMap =
        dualTensorHom Complex (CompositeSystem H K) (CompositeSystem H K)
          ((TensorProduct.dualDistribEquiv Complex H K) (fh ⊗ₜ[Complex] fk) ⊗ₜ[Complex]
            (h ⊗ₜ[Complex] k)) := by
    ext z
    simp [fh, fk, InnerProductSpace.rankOne_apply, dualTensorHom_apply,
      TensorProduct.dualDistribEquiv, TensorProduct.inner_tmul, mul_smul]
  rw [hRank]
  ext x
  simp [partialTraceRightRaw, fh, fk, InnerProductSpace.rankOne_apply,
    LinearMap.comp_apply, dualTensorHom_apply]

/-- Unitary conjugation sends a rank-one operator to the corresponding transported rank one. -/
theorem conjOperator_rankOne {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (U : UnitaryTransport H K) (x y : H) :
    U.conjOperator (InnerProductSpace.rankOne Complex x y).toLinearMap =
      (InnerProductSpace.rankOne Complex (U x) (U y)).toLinearMap := by
  ext z
  simp [UnitaryTransport.conjOperator, InnerProductSpace.rankOne_apply]
  change inner Complex y (U.toLinearEquiv.symm z) • U x =
    inner Complex (U y) z • U x
  rw [← U.map_inner]
  simp

/-- Expand an arbitrary finite-dimensional operator in rank-one matrix units for an orthonormal basis. -/
theorem operator_eq_sum_rankOne_basis (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex H)
    (A : Operator H) :
    A = ∑ i : κ,
      (InnerProductSpace.rankOne Complex (A (b i)) (b i)).toLinearMap := by
  have hId : (LinearMap.id : Operator H) = ∑ i : κ,
      (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap := by
    ext x
    simpa using
      congrArg (fun f : H →L[Complex] H => f x)
        (OrthonormalBasis.sum_rankOne_eq_id b).symm
  calc
    A = A.comp (LinearMap.id : Operator H) := by rfl
    _ = A.comp (∑ i : κ,
        (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap) := by rw [hId]
    _ = ∑ i : κ,
        (InnerProductSpace.rankOne Complex (A (b i)) (b i)).toLinearMap := by
      ext x
      simp [InnerProductSpace.rankOne_apply]

/- Equality of finite-dimensional operator maps follows from equality on orthonormal rank-one units. -/
set_option maxRecDepth 4096 in
theorem linearMap_ext_of_rankOne_basis {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex H)
    (Φ Ψ : Operator H →ₗ[Complex] Operator K)
    (h : ∀ i j : κ,
      Φ (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap =
        Ψ (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap) : Φ = Ψ := by
  apply LinearMap.ext
  intro A
  rw [operator_eq_sum_rankOne_basis H b A]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hExpand :
      (InnerProductSpace.rankOne Complex (A (b i)) (b i)).toLinearMap =
        ∑ j : κ, inner Complex (b j) (A (b i)) •
          (InnerProductSpace.rankOne Complex (b j) (b i)).toLinearMap := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    change inner Complex (b i) x • A (b i) =
      ∑ j : κ, inner Complex (b j) (A (b i)) • (inner Complex (b i) x • b j)
    calc
      inner Complex (b i) x • A (b i) =
          inner Complex (b i) x •
            ∑ j : κ, inner Complex (b j) (A (b i)) • b j := by
              rw [b.sum_repr']
      _ = ∑ j : κ, inner Complex (b j) (A (b i)) • (inner Complex (b i) x • b j) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp [smul_smul, mul_comm]
  rw [hExpand, map_sum]
  rw [map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun B : Operator K => inner Complex (b j) (A (b i)) • B) (h j i)

/-- The coordinates selected by a finite qudit subsystem. -/
abbrev SelectedCoordinates (S : QuditSubsystem q) : Type u :=
  {i : ι // i ∈ S.selected}

/-- The coordinates complementary to a finite qudit subsystem. -/
abbrev ComplementCoordinates (S : QuditSubsystem q) : Type u :=
  {i : ι // i ∉ S.selected}

/-- The local dimensions restricted to the selected coordinates. -/
abbrev selectedDimensions (S : QuditSubsystem q) : S.SelectedCoordinates → Nat :=
  fun i => q i

/-- The local dimensions restricted to the complementary coordinates. -/
abbrev complementDimensions (S : QuditSubsystem q) : S.ComplementCoordinates → Nat :=
  fun i => q i

/-- The selected coordinate register. -/
abbrev selectedSystem (S : QuditSubsystem q) : Type u :=
  Qudit.QuditRegister S.selectedDimensions

/-- The complement coordinate register. -/
abbrev complementSystem (S : QuditSubsystem q) : Type u :=
  Qudit.QuditRegister S.complementDimensions

/-- The selected/complement tensor-product factorization of a finite qudit register. -/
abbrev factorizedSystem (S : QuditSubsystem q) : Type u :=
  CompositeSystem S.selectedSystem S.complementSystem

/-- Restrict a global computational-basis label to the two coordinate factors. -/
def splitLabel (S : QuditSubsystem q) (labels : Qudit.Label q) :
    Qudit.Label S.selectedDimensions × Qudit.Label S.complementDimensions :=
  (fun i => labels i, fun i => labels i)

/-- Recombine selected and complement computational-basis labels. -/
def recombineLabel (S : QuditSubsystem q)
    (labels : Qudit.Label S.selectedDimensions × Qudit.Label S.complementDimensions) :
    Qudit.Label q :=
  fun i => if hi : i ∈ S.selected then labels.1 ⟨i, hi⟩ else labels.2 ⟨i, hi⟩

/-- The selected/complement split is a concrete equivalence of qudit basis labels. -/
def labelFactorization (S : QuditSubsystem q) :
    Qudit.Label q ≃ Qudit.Label S.selectedDimensions × Qudit.Label S.complementDimensions where
  toFun := S.splitLabel
  invFun := S.recombineLabel
  left_inv := by
    intro labels
    funext i
    by_cases hi : i ∈ S.selected <;> simp [splitLabel, recombineLabel, hi]
  right_inv := by
    rintro ⟨left, right⟩
    apply Prod.ext
    · funext i
      simp [splitLabel, recombineLabel]
    · funext i
      have hi : (i : ι) ∉ S.selected := i.property
      simp [splitLabel, recombineLabel, hi]

/-- The concrete unitary factorization of the global qudit register. -/
noncomputable def registerFactorization (S : QuditSubsystem q) :
    UnitaryTransport (Qudit.QuditRegister q) S.factorizedSystem := by
  let sourceBasis := EuclideanSpace.basisFun (Qudit.Label q) Complex
  let selectedBasis := EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
  let complementBasis := EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
  let targetBasis := selectedBasis.tensorProduct complementBasis
  let U := sourceBasis.equiv targetBasis S.labelFactorization
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

/-- Factorization maps every global basis vector to its selected/complement tensor. -/
theorem registerFactorization_apply_basis (S : QuditSubsystem q) (labels : Qudit.Label q) :
    S.registerFactorization (EuclideanSpace.basisFun (Qudit.Label q) Complex labels) =
      (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
        (S.splitLabel labels).1) ⊗ₜ[Complex]
      (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
        (S.splitLabel labels).2) := by
  dsimp [registerFactorization]
  rw [OrthonormalBasis.equiv_apply_basis]
  rw [OrthonormalBasis.tensorProduct_apply']
  simp [labelFactorization]

/-- Recombining a split label is the inverse of coordinate restriction. -/
theorem recombine_splitLabel (S : QuditSubsystem q) (labels : Qudit.Label q) :
    S.recombineLabel (S.splitLabel labels) = labels :=
  S.labelFactorization.left_inv labels

/-- Splitting a recombined pair returns both selected and complement labels. -/
theorem split_recombineLabel (S : QuditSubsystem q)
    (labels : Qudit.Label S.selectedDimensions × Qudit.Label S.complementDimensions) :
    S.splitLabel (S.recombineLabel labels) = labels :=
  S.labelFactorization.right_inv labels

/-- Recombination maps a selected/complement basis tensor back to its global basis vector. -/
theorem registerFactorization_symm_apply_basis (S : QuditSubsystem q)
    (labels : Qudit.Label S.selectedDimensions × Qudit.Label S.complementDimensions) :
    S.registerFactorization.symm
        ((EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex labels.1) ⊗ₜ[Complex]
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex labels.2)) =
      EuclideanSpace.basisFun (Qudit.Label q) Complex (S.recombineLabel labels) := by
  apply S.registerFactorization.toLinearEquiv.injective
  simp only [UnitaryTransport.symm]
  rw [S.registerFactorization.toLinearEquiv.apply_symm_apply]
  rw [S.registerFactorization_apply_basis]
  simp [S.split_recombineLabel]

/-- A selected finite coordinate set has cardinality at most the full coordinate type. -/
theorem card_selected_le_total (S : QuditSubsystem q) :
    Fintype.card S.SelectedCoordinates ≤ Fintype.card ι := by
  simpa [SelectedCoordinates] using S.selected.card_le_univ

/-- A valid standard-basis index for the nonzero complement register. -/
def complementBasisIndex (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) :
    Fin (Module.finrank Complex S.complementSystem) :=
  ⟨0, by
    letI : Nonempty (Qudit.Label S.complementDimensions) :=
      Qudit.label_nonempty S.complementDimensions (fun i => hq i)
    rw [finrank_euclideanSpace]
    exact Fintype.card_pos⟩

/-- A unit standard-basis anchor in the complement register. -/
noncomputable def complementAnchor (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) :
    S.complementSystem :=
  (stdOrthonormalBasis Complex S.complementSystem) (S.complementBasisIndex hq)

/-- Embed selected-register vectors with a fixed complement computational-basis anchor. -/
noncomputable def localEmbedding (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) :
    S.selectedSystem →ₗ[Complex] S.factorizedSystem :=
  (TensorProduct.mk Complex S.selectedSystem S.complementSystem).flip (S.complementAnchor hq)

@[simp]
theorem localEmbedding_apply (S : QuditSubsystem q) (hq : ∀ i, 0 < q i)
    (h : S.selectedSystem) :
    S.localEmbedding hq h = h ⊗ₜ[Complex] S.complementAnchor hq :=
  rfl

set_option maxHeartbeats 800000 in
theorem adjoint_localEmbedding_tmul (S : QuditSubsystem q) (hq : ∀ i, 0 < q i)
    (h : S.selectedSystem) (k : S.complementSystem) :
    LinearMap.adjoint (S.localEmbedding hq) (h ⊗ₜ[Complex] k) =
      (inner Complex (S.complementAnchor hq) k) • h := by
  apply (ext_iff_inner_left Complex).mpr
  intro x
  rw [LinearMap.adjoint_inner_right]
  simp [localEmbedding, TensorProduct.inner_tmul, inner_smul_right, mul_comm]

/-- Extend a local operator by the identity on the complement factor. -/
noncomputable def extendLocal (S : QuditSubsystem q) (A : Operator S.selectedSystem) :
    Operator S.factorizedSystem :=
  TensorProduct.map A (LinearMap.id : S.complementSystem →ₗ[Complex] S.complementSystem)

/-- A local operator, including an effect operator, acts only on the selected tensor factor. -/
@[simp]
theorem extendLocal_apply_tmul (S : QuditSubsystem q) (A : Operator S.selectedSystem)
    (selected : S.selectedSystem) (complement : S.complementSystem) :
    S.extendLocal A (selected ⊗ₜ[Complex] complement) =
      (A selected) ⊗ₜ[Complex] complement := by
  simp [extendLocal]

/-- Extend a selected local operator to the original global qudit register. -/
noncomputable def extendLocalToRegister (S : QuditSubsystem q) (A : Operator S.selectedSystem) :
    Operator (Qudit.QuditRegister q) :=
  S.registerFactorization.symm.conjOperator (S.extendLocal A)

@[simp]
theorem extendLocal_apply_localEmbedding (S : QuditSubsystem q) (hq : ∀ i, 0 < q i)
    (A : Operator S.selectedSystem) (h : S.selectedSystem) :
    S.extendLocal A (S.localEmbedding hq h) = S.localEmbedding hq (A h) := by
  simp [extendLocal, localEmbedding]

/-- Restrict an ambient operator by compression through the complement anchor. -/
noncomputable def restrictLocal (S : QuditSubsystem q) (hq : ∀ i, 0 < q i)
    (A : Operator S.factorizedSystem) : Operator S.selectedSystem :=
  (LinearMap.adjoint (S.localEmbedding hq)).comp (A.comp (S.localEmbedding hq))

/-- Restrict a global operator through the concrete coordinate factorization. -/
noncomputable def restrictLocalFromRegister (S : QuditSubsystem q) (hq : ∀ i, 0 < q i)
    (A : Operator (Qudit.QuditRegister q)) : Operator S.selectedSystem :=
  S.restrictLocal hq (S.registerFactorization.conjOperator A)

/-- Restriction is a left inverse to identity extension of selected local operators. -/
theorem restrictLocal_extendLocal (S : QuditSubsystem q) (hq : ∀ i, 0 < q i)
    (A : Operator S.selectedSystem) :
    S.restrictLocal hq (S.extendLocal A) = A := by
  apply LinearMap.ext
  intro h
  change LinearMap.adjoint (S.localEmbedding hq)
      (S.extendLocal A (S.localEmbedding hq h)) = A h
  rw [S.extendLocal_apply_localEmbedding hq, S.localEmbedding_apply,
    S.adjoint_localEmbedding_tmul]
  simp [complementAnchor]

/-- Global-register restriction is a left inverse to global local extension. -/
theorem restrictLocalFromRegister_extendLocalToRegister (S : QuditSubsystem q)
    (hq : ∀ i, 0 < q i) (A : Operator S.selectedSystem) :
    S.restrictLocalFromRegister hq (S.extendLocalToRegister A) = A := by
  unfold restrictLocalFromRegister extendLocalToRegister
  rw [S.registerFactorization.conjOperator_symm_conjOperator]
  exact S.restrictLocal_extendLocal hq A

/-- Identity extension of selected local operators is injective. -/
theorem extendLocal_injective (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) :
    Function.Injective S.extendLocal := by
  intro A B h
  have hrestricted := congrArg (S.restrictLocal hq) h
  simpa only [S.restrictLocal_extendLocal] using hrestricted

/-- Global local extension is injective. -/
theorem extendLocalToRegister_injective (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) :
    Function.Injective S.extendLocalToRegister := by
  intro A B h
  have hrestricted := congrArg (S.restrictLocalFromRegister hq) h
  simpa only [S.restrictLocalFromRegister_extendLocalToRegister] using hrestricted

/-- An ambient operator is selected-supported precisely when it is an identity extension. -/
def OperatorSupportedOn (S : QuditSubsystem q) (A : Operator S.factorizedSystem) : Prop :=
  ∃ localOperator : Operator S.selectedSystem, S.extendLocal localOperator = A

/-- A global-register operator is selected-supported through the concrete coordinate factorization. -/
def OperatorSupportedOnRegister (S : QuditSubsystem q)
    (A : Operator (Qudit.QuditRegister q)) : Prop :=
  ∃ localOperator : Operator S.selectedSystem, S.extendLocalToRegister localOperator = A

/-- Every explicitly extended selected operator is selected-supported. -/
theorem extendLocal_operatorSupportedOn (S : QuditSubsystem q) (A : Operator S.selectedSystem) :
    S.OperatorSupportedOn (S.extendLocal A) :=
  ⟨A, rfl⟩

/-- Every global explicitly extended selected operator is selected-supported. -/
theorem extendLocalToRegister_operatorSupportedOn (S : QuditSubsystem q)
    (A : Operator S.selectedSystem) :
    S.OperatorSupportedOnRegister (S.extendLocalToRegister A) :=
  ⟨A, rfl⟩

/-- Restriction reconstructs exactly the selected-supported factored operators. -/
theorem operatorSupportedOn_iff_extend_restrict (S : QuditSubsystem q) (hq : ∀ i, 0 < q i)
    (A : Operator S.factorizedSystem) :
    S.OperatorSupportedOn A ↔ S.extendLocal (S.restrictLocal hq A) = A := by
  constructor
  · rintro ⟨localOperator, rfl⟩
    rw [S.restrictLocal_extendLocal]
  · intro h
    exact ⟨S.restrictLocal hq A, h⟩

/-- Restriction reconstructs exactly the selected-supported global operators. -/
theorem operatorSupportedOnRegister_iff_extend_restrict (S : QuditSubsystem q)
    (hq : ∀ i, 0 < q i) (A : Operator (Qudit.QuditRegister q)) :
    S.OperatorSupportedOnRegister A ↔
      S.extendLocalToRegister (S.restrictLocalFromRegister hq A) = A := by
  constructor
  · rintro ⟨localOperator, rfl⟩
    rw [S.restrictLocalFromRegister_extendLocalToRegister]
  · intro h
    exact ⟨S.restrictLocalFromRegister hq A, h⟩

/-- The selected-subsystem partial trace on the actual factorized qudit system. -/
noncomputable def selectedPartialTrace (S : QuditSubsystem q) :
    QuantumChannel S.factorizedSystem S.selectedSystem :=
  partialTraceRightRaw_cptp S.selectedSystem S.complementSystem

/-- Swap the selected and complementary tensor factors before tracing out the selected factor. -/
noncomputable def factorSwap (S : QuditSubsystem q) :
    UnitaryTransport S.factorizedSystem (CompositeSystem S.complementSystem S.selectedSystem) := by
  let U := TensorProduct.commIsometry Complex S.selectedSystem S.complementSystem
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

/-- The selected/complement swap exchanges pure tensor vectors. -/
@[simp]
theorem factorSwap_apply_tmul (S : QuditSubsystem q)
    (selected : S.selectedSystem) (complement : S.complementSystem) :
    S.factorSwap (selected ⊗ₜ[Complex] complement) = complement ⊗ₜ[Complex] selected :=
  rfl

/--
The concrete erasure channel for the selected coordinates: swap the actual
factors and apply the existing raw CPTP partial trace to discard the selected
factor while retaining the complement.
-/
noncomputable def erasureChannel (S : QuditSubsystem q) :
    QuantumChannel S.factorizedSystem S.complementSystem :=
  QuantumChannel.comp
    (partialTraceRightRaw_cptp S.complementSystem S.selectedSystem)
    (QuantumChannel.unitaryConj S.factorSwap)

/-- The selected-coordinate partial trace with the global qudit register as its source. -/
noncomputable def selectedPartialTraceFromRegister (S : QuditSubsystem q) :
    QuantumChannel (Qudit.QuditRegister q) S.selectedSystem :=
  QuantumChannel.comp S.selectedPartialTrace
    (QuantumChannel.unitaryConj S.registerFactorization)

/--
The concrete qudit erasure channel from the global register to the complementary
coordinate register, obtained by coordinate factorization and raw CPTP partial
trace.
-/
noncomputable def erasureChannelFromRegister (S : QuditSubsystem q) :
    QuantumChannel (Qudit.QuditRegister q) S.complementSystem :=
  QuantumChannel.comp S.erasureChannel
    (QuantumChannel.unitaryConj S.registerFactorization)

/-- The selected partial trace is exactly the existing raw CPTP partial-trace map. -/
@[simp]
theorem selectedPartialTrace_toLinearMap (S : QuditSubsystem q) :
    S.selectedPartialTrace.toLinearMap = partialTraceRightRaw S.selectedSystem S.complementSystem :=
  rfl

/-- The factored erasure channel is exactly factor swap followed by raw CPTP partial trace. -/
theorem erasureChannel_specification (S : QuditSubsystem q) :
    S.erasureChannel =
      QuantumChannel.comp
        (partialTraceRightRaw_cptp S.complementSystem S.selectedSystem)
        (QuantumChannel.unitaryConj S.factorSwap) :=
  rfl

/-- The global erasure channel is exactly coordinate factorization followed by factored erasure. -/
theorem erasureChannelFromRegister_specification (S : QuditSubsystem q) :
    S.erasureChannelFromRegister =
      QuantumChannel.comp S.erasureChannel
        (QuantumChannel.unitaryConj S.registerFactorization) :=
  rfl

/-- Erasure contracts the selected components of global computational matrix units. -/
theorem erasureChannelFromRegister_rankOne_basis (S : QuditSubsystem q)
    (x y : Qudit.Label q) :
    S.erasureChannelFromRegister
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Qudit.Label q) Complex x)
          (EuclideanSpace.basisFun (Qudit.Label q) Complex y)).toLinearMap =
      (inner Complex
        (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex (S.splitLabel y).1)
        (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex (S.splitLabel x).1)) •
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex (S.splitLabel x).2)
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex (S.splitLabel y).2)).toLinearMap := by
  simp only [erasureChannelFromRegister, erasureChannel, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply]
  rw [conjOperator_rankOne S.registerFactorization]
  rw [S.registerFactorization_apply_basis x, S.registerFactorization_apply_basis y]
  rw [conjOperator_rankOne S.factorSwap]
  simp only [S.factorSwap_apply_tmul]
  change partialTraceRightRaw S.complementSystem S.selectedSystem _ = _
  rw [partialTraceRightRaw_rankOne_tmul]

/-- Coordinates retained after erasing `S` but discarded when subsequently erasing `T`. -/
abbrev AdditionalRetainedCoordinates (S T : QuditSubsystem q) : Type u :=
  {i : ι // i ∉ S.selected ∧ i ∈ T.selected}

/-- The local dimensions on coordinates retained by `S` and discarded by `T`. -/
abbrev additionalRetainedDimensions (S T : QuditSubsystem q) :
    S.AdditionalRetainedCoordinates T → Nat :=
  fun i => q i

/-- The Hilbert space of the coordinates retained after `S` erasure and removed for `T` erasure. -/
abbrev additionalRetainedSystem (S T : QuditSubsystem q) : Type u :=
  Qudit.QuditRegister (S.additionalRetainedDimensions T)

/-- Split an `S`-complement basis label into `T \ S` and the `T` complement. -/
def splitComplementLabel (S T : QuditSubsystem q)
    (hST : S.selected ⊆ T.selected) (labels : Qudit.Label S.complementDimensions) :
    Qudit.Label (S.additionalRetainedDimensions T) × Qudit.Label T.complementDimensions :=
  (fun i => labels ⟨i, i.property.1⟩,
    fun i => labels ⟨i, fun hiS => i.property (hST hiS)⟩)

/-- Recombine a `T \ S` and `T`-complement pair into an `S`-complement basis label. -/
def recombineComplementLabel (S T : QuditSubsystem q)
    (labels : Qudit.Label (S.additionalRetainedDimensions T) × Qudit.Label T.complementDimensions) :
    Qudit.Label S.complementDimensions :=
  fun i => if hiT : (i : ι) ∈ T.selected then
    labels.1 ⟨i, ⟨i.property, hiT⟩⟩
  else labels.2 ⟨i, hiT⟩

/-- The complement of `S` is concretely equivalent to `(T \ S)` plus the complement of `T`. -/
def complementLabelFactorization (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected) :
    Qudit.Label S.complementDimensions ≃
      Qudit.Label (S.additionalRetainedDimensions T) × Qudit.Label T.complementDimensions where
  toFun := S.splitComplementLabel T hST
  invFun := S.recombineComplementLabel T
  left_inv := by
    intro labels
    funext i
    by_cases hiT : (i : ι) ∈ T.selected
    · simp [splitComplementLabel, recombineComplementLabel, hiT]
    · simp [splitComplementLabel, recombineComplementLabel, hiT]
  right_inv := by
    rintro ⟨additional, complement⟩
    apply Prod.ext
    · funext i
      simp [splitComplementLabel, recombineComplementLabel, i.property.2]
    · funext i
      simp [splitComplementLabel, recombineComplementLabel, i.property]

/-- Factor the `S` complement into the additional retained subsystem and the `T` complement. -/
noncomputable def complementFactorization (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected) :
    UnitaryTransport S.complementSystem
      (CompositeSystem (S.additionalRetainedSystem T) T.complementSystem) := by
  let sourceBasis := EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
  let additionalBasis :=
    EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
  let complementBasis := EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex
  let targetBasis := additionalBasis.tensorProduct complementBasis
  let U := sourceBasis.equiv targetBasis (S.complementLabelFactorization T hST)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

/-- The complement factorization maps each `S`-complement basis label to its two factors. -/
theorem complementFactorization_apply_basis (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected)
    (labels : Qudit.Label S.complementDimensions) :
    S.complementFactorization T hST
        (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex labels) =
      (EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
        (S.splitComplementLabel T hST labels).1) ⊗ₜ[Complex]
      (EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex
        (S.splitComplementLabel T hST labels).2) := by
  dsimp [complementFactorization]
  rw [OrthonormalBasis.equiv_apply_basis]
  rw [OrthonormalBasis.tensorProduct_apply']
  simp [complementLabelFactorization]

/-- The factorization of the `S` complement recombines its basis labels exactly. -/
theorem complementFactorization_symm_apply_basis (S T : QuditSubsystem q)
    (hST : S.selected ⊆ T.selected)
    (labels : Qudit.Label (S.additionalRetainedDimensions T) × Qudit.Label T.complementDimensions) :
    (S.complementFactorization T hST).symm
        ((EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex labels.1)
          ⊗ₜ[Complex]
          (EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex labels.2)) =
      EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
        (S.recombineComplementLabel T labels) := by
  apply (S.complementFactorization T hST).toLinearEquiv.injective
  simp only [UnitaryTransport.symm]
  rw [(S.complementFactorization T hST).toLinearEquiv.apply_symm_apply]
  rw [S.complementFactorization_apply_basis T hST]
  have hlabels :
      S.splitComplementLabel T hST (S.recombineComplementLabel T labels) = labels := by
    exact (S.complementLabelFactorization T hST).right_inv labels
  rw [hlabels]

/-- Split the selected coordinates of `T` into the selected coordinates of `S` and `T \ S`. -/
def splitSelectedLabel (S T : QuditSubsystem q)
    (hST : S.selected ⊆ T.selected) (labels : Qudit.Label T.selectedDimensions) :
    Qudit.Label S.selectedDimensions × Qudit.Label (S.additionalRetainedDimensions T) :=
  (fun i => labels ⟨i, hST i.property⟩,
    fun i => labels ⟨i, i.property.2⟩)

/-- Recombine labels for `S` and `T \ S` into a label for the selected coordinates of `T`. -/
def recombineSelectedLabel (S T : QuditSubsystem q)
    (labels : Qudit.Label S.selectedDimensions × Qudit.Label (S.additionalRetainedDimensions T)) :
    Qudit.Label T.selectedDimensions :=
  fun i => if hiS : (i : ι) ∈ S.selected then
    labels.1 ⟨i, hiS⟩
  else labels.2 ⟨i, ⟨hiS, i.property⟩⟩

/-- The selected coordinates of `T` concretely factor as the selected coordinates of `S` and `T \ S`. -/
def selectedLabelFactorization (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected) :
    Qudit.Label T.selectedDimensions ≃
      Qudit.Label S.selectedDimensions × Qudit.Label (S.additionalRetainedDimensions T) where
  toFun := S.splitSelectedLabel T hST
  invFun := S.recombineSelectedLabel T
  left_inv := by
    intro labels
    funext i
    by_cases hiS : (i : ι) ∈ S.selected
    · simp [splitSelectedLabel, recombineSelectedLabel, hiS]
    · simp [splitSelectedLabel, recombineSelectedLabel, hiS]
  right_inv := by
    rintro ⟨selected, additional⟩
    apply Prod.ext
    · funext i
      simp [splitSelectedLabel, recombineSelectedLabel]
    · funext i
      simp [splitSelectedLabel, recombineSelectedLabel, i.property.1]

/-- Unitary factorization of the selected coordinates of `T` into `S` and `T \ S`. -/
noncomputable def selectedFactorization (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected) :
    UnitaryTransport T.selectedSystem
      (CompositeSystem S.selectedSystem (S.additionalRetainedSystem T)) := by
  let sourceBasis := EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex
  let selectedBasis := EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
  let additionalBasis :=
    EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
  let targetBasis := selectedBasis.tensorProduct additionalBasis
  let U := sourceBasis.equiv targetBasis (S.selectedLabelFactorization T hST)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

/-- The selected-factorization maps each selected label of `T` to its `S` and `T \ S` factors. -/
theorem selectedFactorization_apply_basis (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected)
    (labels : Qudit.Label T.selectedDimensions) :
    S.selectedFactorization T hST
        (EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex labels) =
      (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
        (S.splitSelectedLabel T hST labels).1) ⊗ₜ[Complex]
      (EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
        (S.splitSelectedLabel T hST labels).2) := by
  dsimp [selectedFactorization]
  rw [OrthonormalBasis.equiv_apply_basis]
  rw [OrthonormalBasis.tensorProduct_apply']
  simp [selectedLabelFactorization]

/-- Inner products of `T` selected basis vectors split into `S` and `T \ S` components. -/
theorem inner_selectedBasis_split (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected)
    (x y : Qudit.Label T.selectedDimensions) :
    inner Complex (EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex y)
        (EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex x) =
      inner Complex
          (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
            (S.splitSelectedLabel T hST y).1)
          (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
            (S.splitSelectedLabel T hST x).1) *
        inner Complex
          (EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
            (S.splitSelectedLabel T hST y).2)
          (EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
            (S.splitSelectedLabel T hST x).2) := by
  rw [← (S.selectedFactorization T hST).map_inner]
  rw [S.selectedFactorization_apply_basis T hST y,
    S.selectedFactorization_apply_basis T hST x]
  rw [TensorProduct.inner_tmul]

/-- Splitting a global label through `T` agrees with the nested `S`, `T \ S`, and `Tᶜ` split. -/
theorem splitSelectedLabel_splitLabel (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected)
    (labels : Qudit.Label q) :
    S.splitSelectedLabel T hST (T.splitLabel labels).1 =
      ((S.splitLabel labels).1, (S.splitComplementLabel T hST (S.splitLabel labels).2).1) := by
  apply Prod.ext
  · funext i
    rfl
  · funext i
    rfl

/-- The final component of the nested split is exactly the complement component of the `T` split. -/
theorem splitComplementLabel_splitLabel_second (S T : QuditSubsystem q)
    (hST : S.selected ⊆ T.selected) (labels : Qudit.Label q) :
    (S.splitComplementLabel T hST (S.splitLabel labels).2).2 = (T.splitLabel labels).2 := by
  funext i
  rfl

/-- The additional-factor swap exposes `T \ S` as the right factor traced by the discard channel. -/
noncomputable def additionalRetainedFactorSwap (S T : QuditSubsystem q) :
    UnitaryTransport (CompositeSystem (S.additionalRetainedSystem T) T.complementSystem)
      (CompositeSystem T.complementSystem (S.additionalRetainedSystem T)) := by
  let U := TensorProduct.commIsometry Complex (S.additionalRetainedSystem T) T.complementSystem
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

/-- The additional-retained swap exchanges pure tensor vectors. -/
@[simp]
theorem additionalRetainedFactorSwap_apply_tmul (S T : QuditSubsystem q)
    (additional : S.additionalRetainedSystem T) (complement : T.complementSystem) :
    S.additionalRetainedFactorSwap T (additional ⊗ₜ[Complex] complement) =
      complement ⊗ₜ[Complex] additional :=
  rfl

/--
The explicit CPTP channel that discards the additional subsystem retained after
erasing `S`, yielding the complement system of a larger erased region `T`.
-/
noncomputable def discardAdditionalRetained (S T : QuditSubsystem q)
    (hST : S.selected ⊆ T.selected) : QuantumChannel S.complementSystem T.complementSystem :=
  QuantumChannel.comp
    (partialTraceRightRaw_cptp T.complementSystem (S.additionalRetainedSystem T))
    (QuantumChannel.comp
      (QuantumChannel.unitaryConj (S.additionalRetainedFactorSwap T))
      (QuantumChannel.unitaryConj (S.complementFactorization T hST)))

/-- The additional-retained discard is concretely factorization, swap, and raw CPTP partial trace. -/
theorem discardAdditionalRetained_specification (S T : QuditSubsystem q)
    (hST : S.selected ⊆ T.selected) :
    S.discardAdditionalRetained T hST =
      QuantumChannel.comp
        (partialTraceRightRaw_cptp T.complementSystem (S.additionalRetainedSystem T))
        (QuantumChannel.comp
          (QuantumChannel.unitaryConj (S.additionalRetainedFactorSwap T))
          (QuantumChannel.unitaryConj (S.complementFactorization T hST))) :=
  rfl

/-- Discarding the additional retained factor contracts its computational matrix units. -/
theorem discardAdditionalRetained_rankOne_basis (S T : QuditSubsystem q)
    (hST : S.selected ⊆ T.selected) (x y : Qudit.Label S.complementDimensions) :
    S.discardAdditionalRetained T hST
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex x)
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex y)).toLinearMap =
      (inner Complex
        (EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
          (S.splitComplementLabel T hST y).1)
        (EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
          (S.splitComplementLabel T hST x).1)) •
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex
            (S.splitComplementLabel T hST x).2)
          (EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex
            (S.splitComplementLabel T hST y).2)).toLinearMap := by
  simp only [discardAdditionalRetained, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply]
  rw [conjOperator_rankOne (S.complementFactorization T hST)]
  rw [S.complementFactorization_apply_basis T hST x,
    S.complementFactorization_apply_basis T hST y]
  rw [conjOperator_rankOne (S.additionalRetainedFactorSwap T)]
  simp only [S.additionalRetainedFactorSwap_apply_tmul]
  change partialTraceRightRaw T.complementSystem (S.additionalRetainedSystem T) _ = _
  rw [partialTraceRightRaw_rankOne_tmul]

/--
Erasing `T` is exactly erasing `S` and then explicitly discarding the retained
coordinates in `T \\ S`.
-/
theorem discardAdditionalRetained_erasureChannelFromRegister_apply
    (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected)
    (A : Operator (Qudit.QuditRegister q)) :
    S.discardAdditionalRetained T hST (S.erasureChannelFromRegister A) =
      T.erasureChannelFromRegister A := by
  let basis := EuclideanSpace.basisFun (Qudit.Label q) Complex
  let Phi : Operator (Qudit.QuditRegister q) →ₗ[Complex] Operator T.complementSystem :=
    (S.discardAdditionalRetained T hST).toLinearMap.comp S.erasureChannelFromRegister.toLinearMap
  let Psi : Operator (Qudit.QuditRegister q) →ₗ[Complex] Operator T.complementSystem :=
    T.erasureChannelFromRegister.toLinearMap
  have hMaps : Phi = Psi := by
    apply linearMap_ext_of_rankOne_basis basis Phi Psi
    intro x y
    dsimp [Phi, Psi]
    rw [S.erasureChannelFromRegister_rankOne_basis x y]
    rw [map_smul]
    rw [S.discardAdditionalRetained_rankOne_basis T hST (S.splitLabel x).2 (S.splitLabel y).2]
    rw [T.erasureChannelFromRegister_rankOne_basis x y]
    rw [S.inner_selectedBasis_split T hST (T.splitLabel x).1 (T.splitLabel y).1]
    simp only [S.splitSelectedLabel_splitLabel T hST,
      S.splitComplementLabel_splitLabel_second T hST]
    simp [smul_smul]
  exact DFunLike.congr_fun hMaps A

/-- Exact recovery for a factored qudit erasure channel. -/
def ErasureCorrectable (S : QuditSubsystem q) (C : QuantumCode S.factorizedSystem)
    (recovery : QuantumChannel S.complementSystem S.factorizedSystem) : Prop :=
  Correctable S.factorizedSystem S.complementSystem C S.erasureChannel recovery

/-- Exact recovery for a concrete global qudit-register erasure channel. -/
def ErasureCorrectableFromRegister (S : QuditSubsystem q)
    (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q)) : Prop :=
  Correctable (Qudit.QuditRegister q) S.complementSystem C S.erasureChannelFromRegister recovery

/-- Typed factored qudit erasure correctability is the existing `Correctable` predicate. -/
theorem erasureCorrectable_iff (S : QuditSubsystem q) (C : QuantumCode S.factorizedSystem)
    (recovery : QuantumChannel S.complementSystem S.factorizedSystem) :
    S.ErasureCorrectable C recovery ↔
      Correctable S.factorizedSystem S.complementSystem C S.erasureChannel recovery :=
  Iff.rfl

/-- Typed global qudit erasure correctability is the existing `Correctable` predicate. -/
theorem erasureCorrectableFromRegister_iff (S : QuditSubsystem q)
    (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q)) :
    S.ErasureCorrectableFromRegister C recovery ↔
      Correctable (Qudit.QuditRegister q) S.complementSystem C
        S.erasureChannelFromRegister recovery :=
  Iff.rfl

/-- A factored qudit code admits exact recovery after erasing the selected coordinates. -/
def ErasureRecoverable (S : QuditSubsystem q) (C : QuantumCode S.factorizedSystem) : Prop :=
  ∃ recovery : QuantumChannel S.complementSystem S.factorizedSystem,
    S.ErasureCorrectable C recovery

/-- A global qudit code admits exact recovery after erasing the selected coordinates. -/
def ErasureRecoverableFromRegister (S : QuditSubsystem q)
    (C : QuantumCode (Qudit.QuditRegister q)) : Prop :=
  ∃ recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q),
    S.ErasureCorrectableFromRegister C recovery

/-- Existential factored erasure recoverability stays in the CPTP channel vocabulary. -/
theorem erasureRecoverable_iff_exists_correctable (S : QuditSubsystem q)
    (C : QuantumCode S.factorizedSystem) :
    S.ErasureRecoverable C ↔
      ∃ recovery : QuantumChannel S.complementSystem S.factorizedSystem,
        Correctable S.factorizedSystem S.complementSystem C S.erasureChannel recovery :=
  Iff.rfl

/-- Existential global qudit erasure recoverability stays in the CPTP channel vocabulary. -/
theorem erasureRecoverableFromRegister_iff_exists_correctable (S : QuditSubsystem q)
    (C : QuantumCode (Qudit.QuditRegister q)) :
    S.ErasureRecoverableFromRegister C ↔
      ∃ recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q),
        Correctable (Qudit.QuditRegister q) S.complementSystem C
          S.erasureChannelFromRegister recovery :=
  Iff.rfl

/--
Recovery after erasing `T` yields recovery after erasing any selected subset
`S`: the recovery first receives the explicit CPTP discard of `T \\ S`.
-/
theorem erasureRecoverableFromRegister_mono (S T : QuditSubsystem q)
    (hST : S.selected ⊆ T.selected) (C : QuantumCode (Qudit.QuditRegister q)) :
    T.ErasureRecoverableFromRegister C → S.ErasureRecoverableFromRegister C := by
  rintro ⟨recovery, hRecovery⟩
  refine ⟨QuantumChannel.comp recovery (S.discardAdditionalRetained T hST), ?_⟩
  change Correctable (Qudit.QuditRegister q) S.complementSystem C
    S.erasureChannelFromRegister (QuantumChannel.comp recovery (S.discardAdditionalRetained T hST))
  change Correctable (Qudit.QuditRegister q) T.complementSystem C
    T.erasureChannelFromRegister recovery at hRecovery
  intro rho hSupported
  rw [QuantumChannel.comp_apply]
  rw [S.discardAdditionalRetained_erasureChannelFromRegister_apply T hST]
  exact hRecovery rho hSupported

end QuditSubsystem

end Semantics
end QEC
