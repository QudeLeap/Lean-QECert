import QEC.Semantics.Core.Subsystem
import QEC.Coding.Stabilizer.PauliSemantics

namespace QEC.Locality

open scoped TensorProduct BigOperators

open QEC Semantics

open Coding

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

abbrev LocalPauliIndex (S : FiniteSubsystem ι) : Type u :=
  Qubit.Bitstring S.SelectedCoordinates × Qubit.Bitstring S.SelectedCoordinates

noncomputable def localPauliAmplitude (S : FiniteSubsystem ι) : Complex :=
  (Fintype.card (Qubit.Bitstring S.SelectedCoordinates) : Complex)⁻¹

noncomputable abbrev ket {α : Type u} [Fintype α] [DecidableEq α]
    (bits : Qubit.Bitstring α) :
    Qubit.QubitRegister α :=
  EuclideanSpace.basisFun (Qubit.Bitstring α) Complex bits

theorem flipSupport_flipSupport {α : Type u} [DecidableEq α]
    (s : Finset α) (bits : Qubit.Bitstring α) :
    Qubit.flipSupport s (Qubit.flipSupport s bits) = bits := by
  funext i
  by_cases hi : i ∈ s <;> simp [Qubit.flipSupport, hi]

noncomputable def tensorRight (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (k : K) : H →ₗ[Complex] CompositeSystem H K :=
  (TensorProduct.mk Complex H K).flip k

theorem tensorRight_adjoint_tmul (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (k k' : K) (h : H) :
    LinearMap.adjoint (tensorRight H K k) (h ⊗ₜ[Complex] k') =
      (inner Complex k k') • h := by
  apply (ext_iff_inner_left Complex).mpr
  intro x
  rw [LinearMap.adjoint_inner_right]
  simp [tensorRight, TensorProduct.inner_tmul, inner_smul_right, mul_comm]

noncomputable def rightCompression (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {β : Type u} [Fintype β] (b : OrthonormalBasis β Complex K) :
    Operator (CompositeSystem H K) →ₗ[Complex] Operator H :=
  ∑ i : β,
    let S := tensorRight H K (b i)
    { toFun := fun A => (LinearMap.adjoint S).comp (A.comp S)
      map_add' := by
        intro A B
        ext x
        simp [LinearMap.comp_apply, map_add]
      map_smul' := by
        intro c A
        ext x
        simp [LinearMap.comp_apply] }

theorem dual_apply_sum_basis (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {β : Type u} [Fintype β] (b : OrthonormalBasis β Complex K)
    (ψ : Module.Dual Complex K) (k : K) :
    (∑ i : β, ψ (b i) * inner Complex (b i) k) = ψ k := by
  calc
    (∑ i : β, ψ (b i) * inner Complex (b i) k) =
        ∑ i : β, ψ (inner Complex (b i) k • b i) := by
          simp [map_smul, mul_comm]
    _ = ψ (∑ i : β, inner Complex (b i) k • b i) := by simp [map_sum]
    _ = ψ k := by rw [b.sum_repr']

theorem partialTraceRightRaw_contract_split (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    (contractLeft Complex H).comp
      ((TensorProduct.rid Complex (Module.Dual Complex H ⊗[Complex] H)).toLinearMap.comp
        ((TensorProduct.map
          (LinearMap.id : Module.Dual Complex H ⊗[Complex] H →ₗ[Complex]
            Module.Dual Complex H ⊗[Complex] H)
          (contractLeft Complex K)).comp
          (TensorProduct.tensorTensorTensorComm Complex
            (Module.Dual Complex H) (Module.Dual Complex K) H K).toLinearMap))
      =
    (contractLeft Complex (CompositeSystem H K)).comp
      (TensorProduct.congr (TensorProduct.dualDistribEquiv Complex H K)
        (LinearEquiv.refl Complex (CompositeSystem H K))).toLinearMap := by
  apply TensorProduct.ext
  ext φ ψ h k
  simp [mul_comm]

theorem partialTraceRightRaw_split_eq_compression_split (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {β : Type u} [Fintype β] (b : OrthonormalBasis β Complex K) :
    ((dualTensorHomEquiv Complex H H).toLinearMap.comp
      ((TensorProduct.rid Complex (Module.Dual Complex H ⊗[Complex] H)).toLinearMap.comp
        ((TensorProduct.map
          (LinearMap.id : Module.Dual Complex H ⊗[Complex] H →ₗ[Complex]
            Module.Dual Complex H ⊗[Complex] H)
          (contractLeft Complex K)).comp
          (TensorProduct.tensorTensorTensorComm Complex
            (Module.Dual Complex H) (Module.Dual Complex K) H K).toLinearMap)))
      =
    (rightCompression H K b).comp
      ((dualTensorHomEquiv Complex (CompositeSystem H K) (CompositeSystem H K)).toLinearMap.comp
        (TensorProduct.congr (TensorProduct.dualDistribEquiv Complex H K)
          (LinearEquiv.refl Complex (CompositeSystem H K))).toLinearMap) := by
  apply TensorProduct.ext
  ext φ ψ h k z
  simp [rightCompression, tensorRight_adjoint_tmul, LinearMap.comp_apply,
    dualTensorHomEquiv, dualTensorHom_apply]
  rw [← dual_apply_sum_basis H K b ψ k]
  simp [tensorRight, Finset.mul_sum, Finset.sum_smul, mul_comm, mul_assoc, smul_smul]

theorem partialTraceRightRaw_eq_rightCompression (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {β : Type u} [Fintype β] (b : OrthonormalBasis β Complex K) :
    partialTraceRightRaw H K = rightCompression H K b := by
  apply LinearMap.ext
  intro A
  let eC := dualTensorHomEquiv Complex (CompositeSystem H K) (CompositeSystem H K)
  let x := eC.symm A
  have hA : A = eC x := by simp [x, eC]
  rw [hA]
  let splitMap :
      (Module.Dual Complex (CompositeSystem H K) ⊗[Complex] CompositeSystem H K) →ₗ[Complex]
        ((Module.Dual Complex H ⊗[Complex] Module.Dual Complex K) ⊗[Complex]
          (H ⊗[Complex] K)) :=
    TensorProduct.map (TensorProduct.dualDistribEquiv Complex H K).symm.toLinearMap
      (LinearMap.id : CompositeSystem H K →ₗ[Complex] CompositeSystem H K)
  have hsplit :=
    congrArg (fun f => f (splitMap x))
      (partialTraceRightRaw_split_eq_compression_split H K b)
  simpa [partialTraceRightRaw, eC, splitMap, LinearMap.comp_apply, TensorProduct.map_map]
    using hsplit

noncomputable def tensorLeft (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (h : H) : K →ₗ[Complex] CompositeSystem H K :=
  TensorProduct.mk Complex H K h

theorem tensorLeft_adjoint_tmul (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (h h' : H) (k : K) :
    LinearMap.adjoint (tensorLeft H K h) (h' ⊗ₜ[Complex] k) =
      (inner Complex h h') • k := by
  apply (ext_iff_inner_left Complex).mpr
  intro x
  rw [LinearMap.adjoint_inner_right]
  simp [tensorLeft, TensorProduct.inner_tmul, inner_smul_right]

theorem inner_ket_self {α : Type u} [Fintype α] [DecidableEq α]
    (bits : Qubit.Bitstring α) :
    inner Complex (ket bits) (ket bits) = 1 := by
  simp [ket]

theorem tensorLeft_ket_adjoint_comp_self (S : FiniteSubsystem ι)
    (bits : Qubit.Bitstring S.SelectedCoordinates) :
    (LinearMap.adjoint (tensorLeft S.selectedSystem S.complementSystem (ket bits))).comp
      (tensorLeft S.selectedSystem S.complementSystem (ket bits)) = 1 := by
  apply LinearMap.ext
  intro k
  change LinearMap.adjoint
      (tensorLeft S.selectedSystem S.complementSystem (ket bits))
      ((ket bits) ⊗ₜ[Complex] k) = k
  rw [tensorLeft_adjoint_tmul, inner_ket_self]
  simp

noncomputable def refillUnnormalizedFamilyFactorized (S : FiniteSubsystem ι) :
    FiniteKrausFamily (LocalPauliIndex S)
      S.complementSystem S.factorizedSystem where
  operator p := tensorLeft S.selectedSystem S.complementSystem (ket p.1)

noncomputable def refillFamilyFactorized (S : FiniteSubsystem ι) :
    FiniteKrausFamily (LocalPauliIndex S)
      S.complementSystem S.factorizedSystem :=
  (refillUnnormalizedFamilyFactorized S).scale (fun _ => localPauliAmplitude S)

theorem refillFamilyFactorized_complete (S : FiniteSubsystem ι) :
    (refillFamilyFactorized S).Complete := by
  apply FiniteKrausFamily.scale_complete_of_adjoint_square_sum
    (refillUnnormalizedFamilyFactorized S) (fun _ => localPauliAmplitude S)
  simp only [refillUnnormalizedFamilyFactorized]
  rw [show (∑ p : LocalPauliIndex S,
      (star (localPauliAmplitude S) * localPauliAmplitude S) •
        ((LinearMap.adjoint
          (tensorLeft S.selectedSystem S.complementSystem (ket p.1))).comp
          (tensorLeft S.selectedSystem S.complementSystem (ket p.1)))) =
      ∑ p : LocalPauliIndex S,
        (star (localPauliAmplitude S) * localPauliAmplitude S) •
          (1 : Operator S.complementSystem) by
        apply Finset.sum_congr rfl
        intro p _
        rw [tensorLeft_ket_adjoint_comp_self]
    ]
  rw [Finset.sum_const, Finset.card_univ]
  let d : Complex := Fintype.card (Qubit.Bitstring S.SelectedCoordinates)
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast Fintype.card_ne_zero
  have hcard : (Fintype.card (LocalPauliIndex S) : Complex) = d * d := by
    simp [LocalPauliIndex, d, Fintype.card_prod]
  have hstar_amplitude : star (localPauliAmplitude S) = localPauliAmplitude S := by
    unfold localPauliAmplitude
    simp
  have hscalar : (Fintype.card (LocalPauliIndex S) : Complex) *
      (star (localPauliAmplitude S) * localPauliAmplitude S) = 1 := by
    rw [hcard, hstar_amplitude]
    change (d * d) * (d⁻¹ * d⁻¹) = 1
    field_simp
  rw [← Nat.cast_smul_eq_nsmul Complex]
  rw [smul_smul, hscalar, one_smul]

noncomputable def refillFactorized (S : FiniteSubsystem ι) :
    QuantumChannel S.complementSystem S.factorizedSystem :=
  (refillFamilyFactorized S).toQuantumChannel (refillFamilyFactorized_complete S)

noncomputable def leftCompression (S : FiniteSubsystem ι) :
    Operator S.factorizedSystem →ₗ[Complex] Operator S.complementSystem :=
  ∑ h : Qubit.Bitstring S.SelectedCoordinates,
    let L := tensorLeft S.selectedSystem S.complementSystem (ket h)
    { toFun := fun A => (LinearMap.adjoint L).comp (A.comp L)
      map_add' := by
        intro A B
        ext x
        simp [LinearMap.comp_apply, map_add]
      map_smul' := by
        intro c A
        ext x
        simp [LinearMap.comp_apply] }

theorem factorSwap_symm_comp_tensorRight (S : FiniteSubsystem ι)
    (h : Qubit.Bitstring S.SelectedCoordinates) :
    S.factorSwap.symm.toLinearEquiv.toLinearMap.comp
      (tensorRight S.complementSystem S.selectedSystem (ket h)) =
      tensorLeft S.selectedSystem S.complementSystem (ket h) := by
  apply LinearMap.ext
  intro k
  rfl

theorem tensorRight_adjoint_comp_factorSwap (S : FiniteSubsystem ι)
    (h : Qubit.Bitstring S.SelectedCoordinates) :
    (LinearMap.adjoint
        (tensorRight S.complementSystem S.selectedSystem (ket h))).comp
      S.factorSwap.toLinearEquiv.toLinearMap =
      LinearMap.adjoint
        (tensorLeft S.selectedSystem S.complementSystem (ket h)) := by
  have hswap := factorSwap_symm_comp_tensorRight S h
  have hadjoint := congrArg LinearMap.adjoint hswap
  simpa [LinearMap.adjoint_comp, S.factorSwap.adjoint_symm_toLinearMap] using hadjoint

theorem erasureChannel_apply_eq_leftCompression (S : FiniteSubsystem ι)
    (A : Operator S.factorizedSystem) :
    S.erasureChannel A = leftCompression S A := by
  change partialTraceRightRaw S.complementSystem S.selectedSystem
      (S.factorSwap.conjOperator A) = leftCompression S A
  rw [partialTraceRightRaw_eq_rightCompression S.complementSystem S.selectedSystem
    (EuclideanSpace.basisFun (Qubit.Bitstring S.SelectedCoordinates) Complex)]
  simp only [rightCompression, leftCompression, LinearMap.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro h _
  change
    (LinearMap.adjoint
        (tensorRight S.complementSystem S.selectedSystem (ket h))).comp
        ((S.factorSwap.conjOperator A).comp
          (tensorRight S.complementSystem S.selectedSystem (ket h))) =
      (LinearMap.adjoint
        (tensorLeft S.selectedSystem S.complementSystem (ket h))).comp
        (A.comp (tensorLeft S.selectedSystem S.complementSystem (ket h)))
  rw [show S.factorSwap.conjOperator A =
      S.factorSwap.toLinearEquiv.toLinearMap.comp
        (A.comp S.factorSwap.symm.toLinearEquiv.toLinearMap) by rfl]
  apply LinearMap.ext
  intro k
  simp only [LinearMap.comp_apply]
  have hright : S.factorSwap.symm.toLinearEquiv.toLinearMap
      ((tensorRight S.complementSystem S.selectedSystem (ket h)) k) =
      (tensorLeft S.selectedSystem S.complementSystem (ket h)) k := by
    exact DFunLike.congr_fun (factorSwap_symm_comp_tensorRight S h) k
  rw [hright]
  simpa only [LinearMap.comp_apply] using DFunLike.congr_fun
    (tensorRight_adjoint_comp_factorSwap S h)
    (A ((tensorLeft S.selectedSystem S.complementSystem (ket h)) k))

theorem zSupportPhase_sq {α : Type u} [DecidableEq α]
    (s : Finset α) (bits : Qubit.Bitstring α) :
    Qubit.zSupportPhase s bits * Qubit.zSupportPhase s bits = 1 := by
  unfold Qubit.zSupportPhase
  rw [← Finset.prod_mul_distrib]
  simp_rw [Qubit.zPhase_sq]
  simp

noncomputable def binaryPairingCharacter {α : Type u} [Fintype α] [DecidableEq α]
    (r : Coding.Word (ZMod 2) α) :
    AddChar (Coding.Word (ZMod 2) α) Complex where
  toFun z := PauliSymplectic.binaryPhaseScalar
    (Coding.wordPairing (F := ZMod 2) (ι := α) z r)
  map_zero_eq_one' := by
    simp [PauliSymplectic.binaryPhaseScalar]
  map_add_eq_mul' z z' := by
    rw [show Coding.wordPairing (F := ZMod 2) (ι := α) (z + z') r =
          Coding.wordPairing (F := ZMod 2) (ι := α) z r +
          Coding.wordPairing (F := ZMod 2) (ι := α) z' r by
          rw [(Coding.wordPairing (F := ZMod 2) (ι := α)).map_add z z']
          rfl,
      PauliSymplectic.binaryPhaseScalar_add]

theorem sum_binaryPhase_wordPairing {α : Type u} [Fintype α] [DecidableEq α]
    (r : Coding.Word (ZMod 2) α) :
    ∑ z : Coding.Word (ZMod 2) α,
      PauliSymplectic.binaryPhaseScalar
        (Coding.wordPairing (F := ZMod 2) (ι := α) z r) =
      if r = 0 then Fintype.card (Coding.Word (ZMod 2) α) else 0 := by
  by_cases hr : r = 0
  · subst r
    simp [PauliSymplectic.binaryPhaseScalar]
  · rw [if_neg hr]
    have hchar : binaryPairingCharacter r ≠ 1 := by
      intro hchar
      have hzero : ∀ z : Coding.Word (ZMod 2) α,
          Coding.wordPairing (F := ZMod 2) (ι := α) z r = 0 := by
        intro z
        apply (PauliSymplectic.binaryPhaseScalar_eq_one_iff _).mp
        have hz : binaryPairingCharacter r z = 1 := by
          rw [hchar]
          rfl
        exact hz
      exact hr ((Coding.wordPairing_nondegenerate (F := ZMod 2) (ι := α)).2 r hzero)
    simpa [binaryPairingCharacter] using
      (AddChar.sum_eq_zero_of_ne_one hchar)

noncomputable def factorizedBasis (S : FiniteSubsystem ι) :
    OrthonormalBasis
      (Qubit.Bitstring S.SelectedCoordinates × Qubit.Bitstring S.ComplementCoordinates)
      Complex S.factorizedSystem :=
  (EuclideanSpace.basisFun (Qubit.Bitstring S.SelectedCoordinates) Complex).tensorProduct
    (EuclideanSpace.basisFun (Qubit.Bitstring S.ComplementCoordinates) Complex)

theorem factorizedBasis_apply (S : FiniteSubsystem ι)
    (p : Qubit.Bitstring S.SelectedCoordinates × Qubit.Bitstring S.ComplementCoordinates) :
    factorizedBasis S p = ket p.1 ⊗ₜ[Complex] ket p.2 := by
  unfold factorizedBasis ket
  rw [OrthonormalBasis.tensorProduct_apply']

theorem operator_ext_factorized_basis (S : FiniteSubsystem ι)
    {A B : Operator S.factorizedSystem}
    (h : ∀ p q : Qubit.Bitstring S.SelectedCoordinates × Qubit.Bitstring S.ComplementCoordinates,
      inner Complex (factorizedBasis S q) (A (factorizedBasis S p)) =
        inner Complex (factorizedBasis S q) (B (factorizedBasis S p))) :
    A = B := by
  let b := factorizedBasis S
  apply LinearMap.ext
  intro x
  apply b.repr.injective
  ext q
  rw [b.repr_apply_apply, b.repr_apply_apply]
  rw [← b.sum_repr' x, map_sum, map_sum]
  simp only [map_smul, inner_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [inner_smul_right (b q) (A (b p)) (inner Complex (b p) x),
    inner_smul_right (b q) (B (b p)) (inner Complex (b p) x)]
  simpa [b] using congrArg (fun t => inner Complex (b p) x * t) (h p q)

abbrev LocalPauliWordIndex (S : FiniteSubsystem ι) : Type u :=
  Coding.Word (ZMod 2) S.SelectedCoordinates × Coding.Word (ZMod 2) S.SelectedCoordinates

noncomputable def wordBinaryPauli (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) : PauliSymplectic.Binary S.SelectedCoordinates :=
  { phase := 0
    vector := { xPart := p.1, zPart := p.2 } }

noncomputable def wordPauliOperatorFactorized (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) : Operator S.factorizedSystem :=
  TensorProduct.map (PauliSymplectic.toQubitOperator (wordBinaryPauli S p))
    (LinearMap.id : S.complementSystem →ₗ[Complex] S.complementSystem)

theorem wordPauliOperatorFactorized_adjoint_comp_self (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) :
    (LinearMap.adjoint (wordPauliOperatorFactorized S p)).comp
      (wordPauliOperatorFactorized S p) = 1 := by
  let P := PauliSymplectic.toQubitOperator (wordBinaryPauli S p)
  let I : Operator S.complementSystem := LinearMap.id
  have hP : (LinearMap.adjoint P).comp P = 1 :=
    PauliSymplectic.toQubitOperator_adjoint_comp_self _
  change (LinearMap.adjoint (TensorProduct.map P I)).comp (TensorProduct.map P I) = 1
  ext h k
  have hPh := congrArg (fun T : Operator S.selectedSystem => T h) hP
  simpa [TensorProduct.map_tmul, P, I, LinearMap.comp_apply] using
    congrArg (fun x : S.selectedSystem => x ⊗ₜ[Complex] k) hPh

theorem card_word_eq_card_bitstring (S : FiniteSubsystem ι) :
    Fintype.card (Coding.Word (ZMod 2) S.SelectedCoordinates) =
      Fintype.card (Qubit.Bitstring S.SelectedCoordinates) := by
  exact Fintype.card_congr (PauliSymplectic.bitstringWordEquiv _).symm

noncomputable def wordPauliUnnormalizedFamilyFactorized (S : FiniteSubsystem ι) :
    FiniteKrausFamily (LocalPauliWordIndex S) S.factorizedSystem S.factorizedSystem where
  operator p := wordPauliOperatorFactorized S p

noncomputable def wordPauliFamilyFactorized (S : FiniteSubsystem ι) :
    FiniteKrausFamily (LocalPauliWordIndex S) S.factorizedSystem S.factorizedSystem :=
  (wordPauliUnnormalizedFamilyFactorized S).scale (fun _ => localPauliAmplitude S)

theorem wordPauliFamilyFactorized_complete (S : FiniteSubsystem ι) :
    (wordPauliFamilyFactorized S).Complete := by
  apply FiniteKrausFamily.scale_complete_of_adjoint_square_sum
    (wordPauliUnnormalizedFamilyFactorized S) (fun _ => localPauliAmplitude S)
  simp only [wordPauliUnnormalizedFamilyFactorized]
  rw [show (∑ p : LocalPauliWordIndex S,
      (star (localPauliAmplitude S) * localPauliAmplitude S) •
        ((LinearMap.adjoint (wordPauliOperatorFactorized S p)).comp
          (wordPauliOperatorFactorized S p))) =
      ∑ _p : LocalPauliWordIndex S,
        (star (localPauliAmplitude S) * localPauliAmplitude S) •
          (1 : Operator S.factorizedSystem) by
        apply Finset.sum_congr rfl
        intro p _
        rw [wordPauliOperatorFactorized_adjoint_comp_self]
    ]
  rw [Finset.sum_const, Finset.card_univ]
  let d : Complex := Fintype.card (Qubit.Bitstring S.SelectedCoordinates)
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast Fintype.card_ne_zero
  have hcard : (Fintype.card (LocalPauliWordIndex S) : Complex) = d * d := by
    simp [LocalPauliWordIndex, Fintype.card_prod, d]
  have hstar_amplitude : star (localPauliAmplitude S) = localPauliAmplitude S := by
    unfold localPauliAmplitude
    simp
  have hscalar : (Fintype.card (LocalPauliWordIndex S) : Complex) *
      (star (localPauliAmplitude S) * localPauliAmplitude S) = 1 := by
    rw [hcard, hstar_amplitude]
    change (d * d) * (d⁻¹ * d⁻¹) = 1
    field_simp
  rw [← Nat.cast_smul_eq_nsmul Complex]
  rw [smul_smul, hscalar, one_smul]

noncomputable def wordPauliTwirlFactorized (S : FiniteSubsystem ι) :
    QuantumChannel S.factorizedSystem S.factorizedSystem :=
  (wordPauliFamilyFactorized S).toQuantumChannel (wordPauliFamilyFactorized_complete S)

theorem wordBinaryPauli_apply_ket (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) (bits : Qubit.Bitstring S.SelectedCoordinates) :
    PauliSymplectic.toQubitOperator (wordBinaryPauli S p) (ket bits) =
      Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2) bits •
        ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) bits) := by
  ext output
  rw [PauliSymplectic.toQubitOperator_apply]
  simp only [wordBinaryPauli, PauliSymplectic.xSupport, PauliSymplectic.zSupport,
    PauliSymplectic.binaryPhaseScalar_zero, one_mul]
  change Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2)
      (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) output) *
      ket bits (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) output) =
    (Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2) bits •
      ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) bits)) output
  simp only [ket, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  by_cases h : Qubit.flipSupport (PauliSymplectic.binarySupport p.1) output = bits
  · have h' : output = Qubit.flipSupport (PauliSymplectic.binarySupport p.1) bits := by
      rw [← h]
      exact (flipSupport_flipSupport (α := S.SelectedCoordinates) _ _).symm
    subst output
    simp [flipSupport_flipSupport (α := S.SelectedCoordinates)]
  · have h' : output ≠ Qubit.flipSupport (PauliSymplectic.binarySupport p.1) bits := by
      intro h'
      apply h
      rw [h', flipSupport_flipSupport (α := S.SelectedCoordinates)]
    simp [h, h']

theorem wordPauliOperatorFactorized_apply_tmul (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) (a : Qubit.Bitstring S.SelectedCoordinates)
    (k : S.complementSystem) :
    wordPauliOperatorFactorized S p (ket a ⊗ₜ[Complex] k) =
      Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2) a •
        (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a) ⊗ₜ[Complex] k) := by
  rw [wordPauliOperatorFactorized, TensorProduct.map_tmul, wordBinaryPauli_apply_ket]
  rw [← TensorProduct.smul_tmul']
  simp

theorem wordPauliOperatorFactorized_adjoint_apply_tmul (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) (a : Qubit.Bitstring S.SelectedCoordinates)
    (k : S.complementSystem) :
    (LinearMap.adjoint (wordPauliOperatorFactorized S p)) (ket a ⊗ₜ[Complex] k) =
      Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2)
        (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a) •
      (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a) ⊗ₜ[Complex] k) := by
  let x := PauliSymplectic.binarySupport p.1
  let z := PauliSymplectic.binarySupport p.2
  let q := Qubit.zSupportPhase z (Qubit.flipSupport x a)
  let y : S.factorizedSystem := q • (ket (Qubit.flipSupport x a) ⊗ₜ[Complex] k)
  have hPy : wordPauliOperatorFactorized S p y = ket a ⊗ₜ[Complex] k := by
    rw [show y = q • (ket (Qubit.flipSupport x a) ⊗ₜ[Complex] k) by rfl,
      map_smul, wordPauliOperatorFactorized_apply_tmul]
    change q • (Qubit.zSupportPhase z (Qubit.flipSupport x a) •
      (ket (Qubit.flipSupport x (Qubit.flipSupport x a)) ⊗ₜ[Complex] k)) = _
    rw [flipSupport_flipSupport, smul_smul]
    rw [show q = Qubit.zSupportPhase z (Qubit.flipSupport x a) by rfl,
      zSupportPhase_sq]
    simp
  rw [← hPy]
  change ((LinearMap.adjoint (wordPauliOperatorFactorized S p)).comp
      (wordPauliOperatorFactorized S p)) y = _
  rw [wordPauliOperatorFactorized_adjoint_comp_self]
  rfl

theorem word_add_self_zero {α : Type u} [Fintype α]
    (x : Coding.Word (ZMod 2) α) : x + x = 0 := by
  ext i
  rw [← two_mul]
  have htwo : (2 : ZMod 2) = 0 := by decide
  change (2 : ZMod 2) * x i = 0
  rw [htwo, zero_mul]

theorem word_neg_eq_self {α : Type u} [Fintype α]
    (x : Coding.Word (ZMod 2) α) : -x = x := by
  exact (eq_neg_of_add_eq_zero_left (word_add_self_zero x)).symm

theorem bitstringWord_add_eq_zero_iff {α : Type u} [Fintype α] [DecidableEq α]
    (a b : Qubit.Bitstring α) :
    PauliSymplectic.bitstringWordEquiv α b +
        PauliSymplectic.bitstringWordEquiv α a = 0 ↔ b = a := by
  constructor
  · intro h
    apply (PauliSymplectic.bitstringWordEquiv α).injective
    rw [eq_neg_of_add_eq_zero_left h, word_neg_eq_self]
  · intro h
    subst b
    exact word_add_self_zero _

theorem wordPauli_phase_product {α : Type u} [Fintype α] [DecidableEq α]
    (x z : Coding.Word (ZMod 2) α) (a b : Qubit.Bitstring α) :
    star (Qubit.zSupportPhase (PauliSymplectic.binarySupport z)
      (Qubit.flipSupport (PauliSymplectic.binarySupport x) b)) *
      Qubit.zSupportPhase (PauliSymplectic.binarySupport z)
        (Qubit.flipSupport (PauliSymplectic.binarySupport x) a) =
      PauliSymplectic.binaryPhaseScalar
        (Coding.wordPairing (F := ZMod 2) (ι := α) z
          ((PauliSymplectic.bitstringWordEquiv α b) +
            PauliSymplectic.bitstringWordEquiv α a)) := by
  rw [PauliSymplectic.zSupportPhase_eq_binaryPhaseScalar_wordPairing,
    PauliSymplectic.zSupportPhase_eq_binaryPhaseScalar_wordPairing,
    PauliSymplectic.binaryPhaseScalar_star, ← PauliSymplectic.binaryPhaseScalar_add]
  congr 1
  rw [← (Coding.wordPairing (F := ZMod 2) (ι := α) z).map_add]
  rw [PauliSymplectic.bitstringWordEquiv_flipSupport,
    PauliSymplectic.bitstringWordEquiv_flipSupport]
  have hx : x + x = 0 := word_add_self_zero x
  calc
    (Coding.wordPairing (F := ZMod 2) (ι := α) z)
        ((PauliSymplectic.bitstringWordEquiv α b) + x +
          ((PauliSymplectic.bitstringWordEquiv α a) + x)) =
      (Coding.wordPairing (F := ZMod 2) (ι := α) z)
        ((PauliSymplectic.bitstringWordEquiv α b +
          PauliSymplectic.bitstringWordEquiv α a) + (x + x)) := by
        congr 1
        abel
    _ = _ := by simp [hx]

theorem wordPauli_contribution_matrix_element (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) (A : Operator S.factorizedSystem)
    (a b : Qubit.Bitstring S.SelectedCoordinates)
    (k l : S.complementSystem) :
    inner Complex (ket b ⊗ₜ[Complex] l)
      (((wordPauliOperatorFactorized S p).comp
        (A.comp (LinearMap.adjoint (wordPauliOperatorFactorized S p))))
        (ket a ⊗ₜ[Complex] k)) =
      (PauliSymplectic.binaryPhaseScalar
        (Coding.wordPairing (F := ZMod 2) (ι := S.SelectedCoordinates) p.2
          ((PauliSymplectic.bitstringWordEquiv _ b) +
            PauliSymplectic.bitstringWordEquiv _ a))) *
        inner Complex
          (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) b) ⊗ₜ[Complex] l)
          (A (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a) ⊗ₜ[Complex] k)) := by
  change inner Complex (ket b ⊗ₜ[Complex] l)
    (wordPauliOperatorFactorized S p
      (A ((LinearMap.adjoint (wordPauliOperatorFactorized S p))
        (ket a ⊗ₜ[Complex] k)))) = _
  rw [← LinearMap.adjoint_inner_left]
  rw [wordPauliOperatorFactorized_adjoint_apply_tmul,
    wordPauliOperatorFactorized_adjoint_apply_tmul]
  rw [map_smul]
  change inner Complex
    (Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2)
      (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) b) •
        (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) b) ⊗ₜ[Complex] l))
    (Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2)
      (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a) •
        A (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a) ⊗ₜ[Complex] k)) = _
  rw [inner_smul_left (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) b) ⊗ₜ[Complex] l)
    _ (Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2)
      (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) b))]
  rw [inner_smul_right
    (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) b) ⊗ₜ[Complex] l)
    (A (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a) ⊗ₜ[Complex] k))
    (Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2)
      (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a))]
  change star (Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2)
      (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) b)) *
    (Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2)
      (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a) * _) = _
  rw [← mul_assoc]
  rw [wordPauli_phase_product]

theorem scaled_wordPauli_contribution_matrix_element (S : FiniteSubsystem ι)
    (c : Complex) (p : LocalPauliWordIndex S) (A : Operator S.factorizedSystem)
    (a b : Qubit.Bitstring S.SelectedCoordinates)
    (k l : S.complementSystem) :
    inner Complex (ket b ⊗ₜ[Complex] l)
      (((c • wordPauliOperatorFactorized S p).comp
        (A.comp (LinearMap.adjoint (c • wordPauliOperatorFactorized S p))))
        (ket a ⊗ₜ[Complex] k)) =
      (star c * c) *
        (PauliSymplectic.binaryPhaseScalar
          (Coding.wordPairing (F := ZMod 2) (ι := S.SelectedCoordinates) p.2
            ((PauliSymplectic.bitstringWordEquiv _ b) +
              PauliSymplectic.bitstringWordEquiv _ a))) *
          inner Complex
            (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) b) ⊗ₜ[Complex] l)
            (A (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a) ⊗ₜ[Complex] k)) := by
  have hadjoint : LinearMap.adjoint (c • wordPauliOperatorFactorized S p) =
      star c • LinearMap.adjoint (wordPauliOperatorFactorized S p) := by
    exact map_smulₛₗ LinearMap.adjoint c (wordPauliOperatorFactorized S p)
  rw [hadjoint]
  change inner Complex (ket b ⊗ₜ[Complex] l)
    (c • wordPauliOperatorFactorized S p
      (A (star c • (LinearMap.adjoint (wordPauliOperatorFactorized S p))
        (ket a ⊗ₜ[Complex] k)))) = _
  rw [map_smul, map_smul]
  rw [smul_smul]
  rw [inner_smul_right]
  change (c * star c) * _ = _
  rw [mul_comm c (star c)]
  have hmatrix := wordPauli_contribution_matrix_element S p A a b k l
  simpa only [LinearMap.comp_apply, mul_assoc] using
    congrArg (fun z : Complex => (star c * c) * z) hmatrix

noncomputable def flipWordEquiv {α : Type u} [Fintype α] [DecidableEq α]
    (bits : Qubit.Bitstring α) :
    Coding.Word (ZMod 2) α ≃ Qubit.Bitstring α :=
  (Equiv.addLeft (PauliSymplectic.bitstringWordEquiv α bits)).trans
    (PauliSymplectic.bitstringWordEquiv α).symm

theorem flipWordEquiv_apply {α : Type u} [Fintype α] [DecidableEq α]
    (bits : Qubit.Bitstring α) (x : Coding.Word (ZMod 2) α) :
    flipWordEquiv bits x =
      Qubit.flipSupport (PauliSymplectic.binarySupport x) bits := by
  apply (PauliSymplectic.bitstringWordEquiv α).injective
  rw [PauliSymplectic.bitstringWordEquiv_flipSupport]
  simp [flipWordEquiv]

theorem wordPauliTwirlFactorized_matrix_element (S : FiniteSubsystem ι)
    (A : Operator S.factorizedSystem)
    (a b : Qubit.Bitstring S.SelectedCoordinates)
    (k l : S.complementSystem) :
    inner Complex (ket b ⊗ₜ[Complex] l)
      (wordPauliTwirlFactorized S A (ket a ⊗ₜ[Complex] k)) =
      if b = a then
        localPauliAmplitude S *
          ∑ h : Qubit.Bitstring S.SelectedCoordinates,
            inner Complex (ket h ⊗ₜ[Complex] l) (A (ket h ⊗ₜ[Complex] k))
      else 0 := by
  let d : Complex := Fintype.card (Qubit.Bitstring S.SelectedCoordinates)
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast Fintype.card_ne_zero
  have hamp : localPauliAmplitude S = d⁻¹ := by rfl
  have hstar_amp : star (localPauliAmplitude S) = localPauliAmplitude S := by
    unfold localPauliAmplitude
    simp
  have hsum :
      inner Complex (ket b ⊗ₜ[Complex] l)
        (wordPauliTwirlFactorized S A (ket a ⊗ₜ[Complex] k)) =
      ∑ x : Coding.Word (ZMod 2) S.SelectedCoordinates,
        ∑ z : Coding.Word (ZMod 2) S.SelectedCoordinates,
          (star (localPauliAmplitude S) * localPauliAmplitude S) *
            PauliSymplectic.binaryPhaseScalar
              (Coding.wordPairing (F := ZMod 2) (ι := S.SelectedCoordinates) z
                ((PauliSymplectic.bitstringWordEquiv _ b) +
                  PauliSymplectic.bitstringWordEquiv _ a)) *
            inner Complex
              (ket (Qubit.flipSupport (PauliSymplectic.binarySupport x) b) ⊗ₜ[Complex] l)
              (A (ket (Qubit.flipSupport (PauliSymplectic.binarySupport x) a) ⊗ₜ[Complex] k)) := by
    change inner Complex (ket b ⊗ₜ[Complex] l)
      ((wordPauliTwirlFactorized S).toLinearMap A (ket a ⊗ₜ[Complex] k)) = _
    unfold wordPauliTwirlFactorized
    rw [FiniteKrausFamily.toQuantumChannel_apply_sum]
    simp only [LinearMap.coe_sum, Finset.sum_apply]
    rw [inner_sum]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro z _
    exact scaled_wordPauli_contribution_matrix_element S (localPauliAmplitude S) (x, z)
      A a b k l
  rw [hsum]
  by_cases hba : b = a
  · subst b
    rw [if_pos rfl]
    simp only [word_add_self_zero, map_zero,
      PauliSymplectic.binaryPhaseScalar_zero, mul_one]
    simp_rw [Finset.sum_const, Finset.card_univ]
    have hcard : (Fintype.card (Coding.Word (ZMod 2) S.SelectedCoordinates) : Complex) = d := by
      rw [card_word_eq_card_bitstring]
    simp_rw [← Nat.cast_smul_eq_nsmul Complex]
    rw [hcard]
    rw [← Finset.smul_sum]
    change d * (∑ x : Coding.Word (ZMod 2) S.SelectedCoordinates,
      star (localPauliAmplitude S) * localPauliAmplitude S *
        inner Complex
          (ket (Qubit.flipSupport (PauliSymplectic.binarySupport x) a) ⊗ₜ[Complex] l)
          (A (ket (Qubit.flipSupport (PauliSymplectic.binarySupport x) a) ⊗ₜ[Complex] k))) = _
    rw [← Finset.mul_sum]
    have hflip :
        (∑ x : Coding.Word (ZMod 2) S.SelectedCoordinates,
          inner Complex
            (ket (Qubit.flipSupport (PauliSymplectic.binarySupport x) a) ⊗ₜ[Complex] l)
            (A (ket (Qubit.flipSupport (PauliSymplectic.binarySupport x) a) ⊗ₜ[Complex] k))) =
          ∑ h : Qubit.Bitstring S.SelectedCoordinates,
            inner Complex (ket h ⊗ₜ[Complex] l) (A (ket h ⊗ₜ[Complex] k)) := by
      apply Fintype.sum_equiv (flipWordEquiv a)
      intro x
      exact congrArg (fun h : Qubit.Bitstring S.SelectedCoordinates =>
        inner Complex (ket h ⊗ₜ[Complex] l) (A (ket h ⊗ₜ[Complex] k)))
        (flipWordEquiv_apply a x).symm
    rw [hflip]
    rw [hstar_amp, hamp]
    field_simp
  · rw [if_neg hba]
    have hzero : PauliSymplectic.bitstringWordEquiv S.SelectedCoordinates b +
        PauliSymplectic.bitstringWordEquiv S.SelectedCoordinates a ≠ 0 := by
      intro hz
      exact hba ((bitstringWord_add_eq_zero_iff a b).1 hz)
    apply Finset.sum_eq_zero
    intro x _
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [sum_binaryPhase_wordPairing, if_neg hzero]
    simp

theorem inner_ket_eq_ite {α : Type u} [Fintype α] [DecidableEq α]
    (a b : Qubit.Bitstring α) :
    inner Complex (ket a) (ket b) = if a = b then 1 else 0 := by
  exact (EuclideanSpace.basisFun (Qubit.Bitstring α) Complex).inner_eq_ite a b

theorem sum_double_delta {α : Type u} [Fintype α] [DecidableEq α]
    (a : α) (c v : Complex) :
    (∑ x : α, c * (if a = x then 1 else 0) * (if x = a then 1 else 0) * v) =
      c * v := by
  classical
  simp

theorem refill_contribution_matrix_element (S : FiniteSubsystem ι)
    (r : Qubit.Bitstring S.SelectedCoordinates)
    (B : Operator S.complementSystem)
    (a b : Qubit.Bitstring S.SelectedCoordinates)
    (k l : S.complementSystem) :
    inner Complex (ket b ⊗ₜ[Complex] l)
      ((tensorLeft S.selectedSystem S.complementSystem (ket r)).comp
        (B.comp (LinearMap.adjoint
          (tensorLeft S.selectedSystem S.complementSystem (ket r))))
        (ket a ⊗ₜ[Complex] k)) =
      inner Complex (ket b) (ket r) * inner Complex (ket r) (ket a) *
        inner Complex l (B k) := by
  change inner Complex (ket b ⊗ₜ[Complex] l)
    (tensorLeft S.selectedSystem S.complementSystem (ket r)
      (B ((LinearMap.adjoint
        (tensorLeft S.selectedSystem S.complementSystem (ket r)))
        (ket a ⊗ₜ[Complex] k)))) = _
  rw [tensorLeft_adjoint_tmul, map_smul, map_smul]
  change inner Complex (ket b ⊗ₜ[Complex] l)
    (inner Complex (ket r) (ket a) • (ket r ⊗ₜ[Complex] B k)) = _
  rw [inner_smul_right (ket b ⊗ₜ[Complex] l) (ket r ⊗ₜ[Complex] B k)
    (inner Complex (ket r) (ket a)), TensorProduct.inner_tmul]
  ring

theorem scaled_refill_contribution_matrix_element (S : FiniteSubsystem ι)
    (c : Complex) (r : Qubit.Bitstring S.SelectedCoordinates)
    (B : Operator S.complementSystem)
    (a b : Qubit.Bitstring S.SelectedCoordinates)
    (k l : S.complementSystem) :
    inner Complex (ket b ⊗ₜ[Complex] l)
      (((c • tensorLeft S.selectedSystem S.complementSystem (ket r)).comp
        (B.comp (LinearMap.adjoint
          (c • tensorLeft S.selectedSystem S.complementSystem (ket r)))))
        (ket a ⊗ₜ[Complex] k)) =
      (star c * c) * inner Complex (ket b) (ket r) * inner Complex (ket r) (ket a) *
        inner Complex l (B k) := by
  have hadjoint : LinearMap.adjoint
      (c • tensorLeft S.selectedSystem S.complementSystem (ket r)) =
      star c • LinearMap.adjoint
        (tensorLeft S.selectedSystem S.complementSystem (ket r)) := by
    exact map_smulₛₗ LinearMap.adjoint c
      (tensorLeft S.selectedSystem S.complementSystem (ket r))
  rw [hadjoint]
  change inner Complex (ket b ⊗ₜ[Complex] l)
    (c • tensorLeft S.selectedSystem S.complementSystem (ket r)
      (B (star c • (LinearMap.adjoint
        (tensorLeft S.selectedSystem S.complementSystem (ket r)))
        (ket a ⊗ₜ[Complex] k)))) = _
  rw [map_smul, map_smul, smul_smul, inner_smul_right]
  change (c * star c) * _ = _
  rw [mul_comm c (star c)]
  have hmatrix := refill_contribution_matrix_element S r B a b k l
  simpa only [LinearMap.comp_apply, mul_assoc] using
    congrArg (fun z : Complex => (star c * c) * z) hmatrix

theorem leftCompression_matrix_element (S : FiniteSubsystem ι)
    (A : Operator S.factorizedSystem) (k l : S.complementSystem) :
    inner Complex l (leftCompression S A k) =
      ∑ h : Qubit.Bitstring S.SelectedCoordinates,
        inner Complex (ket h ⊗ₜ[Complex] l) (A (ket h ⊗ₜ[Complex] k)) := by
  unfold leftCompression
  simp only [LinearMap.coe_sum, Finset.sum_apply]
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro h _
  change inner Complex l
    ((LinearMap.adjoint (tensorLeft S.selectedSystem S.complementSystem (ket h)))
      (A ((tensorLeft S.selectedSystem S.complementSystem (ket h)) k))) = _
  rw [LinearMap.adjoint_inner_right]
  rfl

theorem refill_comp_erasure_matrix_element (S : FiniteSubsystem ι)
    (A : Operator S.factorizedSystem)
    (a b : Qubit.Bitstring S.SelectedCoordinates)
    (k l : S.complementSystem) :
    inner Complex (ket b ⊗ₜ[Complex] l)
      ((QuantumChannel.comp (refillFactorized S) S.erasureChannel).toLinearMap A
        (ket a ⊗ₜ[Complex] k)) =
      if b = a then
        localPauliAmplitude S *
          ∑ h : Qubit.Bitstring S.SelectedCoordinates,
            inner Complex (ket h ⊗ₜ[Complex] l) (A (ket h ⊗ₜ[Complex] k))
      else 0 := by
  let d : Complex := Fintype.card (Qubit.Bitstring S.SelectedCoordinates)
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast Fintype.card_ne_zero
  have hamp : localPauliAmplitude S = d⁻¹ := by rfl
  have hstar_amp : star (localPauliAmplitude S) = localPauliAmplitude S := by
    unfold localPauliAmplitude
    simp
  change inner Complex (ket b ⊗ₜ[Complex] l)
    ((refillFactorized S).toLinearMap (S.erasureChannel A)
      (ket a ⊗ₜ[Complex] k)) = _
  rw [erasureChannel_apply_eq_leftCompression]
  unfold refillFactorized
  rw [FiniteKrausFamily.toQuantumChannel_apply_sum]
  simp only [LinearMap.coe_sum, Finset.sum_apply]
  rw [inner_sum, Fintype.sum_prod_type]
  simp only [refillFamilyFactorized, FiniteKrausFamily.scale_operator,
    refillUnnormalizedFamilyFactorized]
  simp_rw [scaled_refill_contribution_matrix_element S (localPauliAmplitude S)]
  by_cases hba : b = a
  · subst b
    rw [if_pos rfl]
    simp only [inner_ket_eq_ite]
    simp_rw [Finset.sum_const, Finset.card_univ]
    simp_rw [← Nat.cast_smul_eq_nsmul Complex]
    simp only [smul_eq_mul]
    change (∑ x : Qubit.Bitstring S.SelectedCoordinates,
      d * (((star (localPauliAmplitude S) * localPauliAmplitude S *
          (if a = x then 1 else 0)) * (if x = a then 1 else 0)) *
        inner Complex l (leftCompression S A k))) = _
    have hcollapse :
        (∑ x : Qubit.Bitstring S.SelectedCoordinates,
          d * (((star (localPauliAmplitude S) * localPauliAmplitude S *
              (if a = x then 1 else 0)) * (if x = a then 1 else 0)) *
            inner Complex l (leftCompression S A k))) =
          (d * (star (localPauliAmplitude S) * localPauliAmplitude S)) *
            inner Complex l (leftCompression S A k) := by
      calc
        (∑ x : Qubit.Bitstring S.SelectedCoordinates,
          d * (((star (localPauliAmplitude S) * localPauliAmplitude S *
              (if a = x then 1 else 0)) * (if x = a then 1 else 0)) *
            inner Complex l (leftCompression S A k))) =
          ∑ x : Qubit.Bitstring S.SelectedCoordinates,
            (d * (star (localPauliAmplitude S) * localPauliAmplitude S)) *
              (if a = x then 1 else 0) * (if x = a then 1 else 0) *
              inner Complex l (leftCompression S A k) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
        _ = _ := sum_double_delta a
          (d * (star (localPauliAmplitude S) * localPauliAmplitude S))
          (inner Complex l (leftCompression S A k))
    rw [hcollapse, leftCompression_matrix_element]
    rw [hstar_amp, hamp]
    field_simp
  · rw [if_neg hba]
    apply Finset.sum_eq_zero
    intro x _
    apply Finset.sum_eq_zero
    intro z _
    have hprod : inner Complex (ket b) (ket x) * inner Complex (ket x) (ket a) = 0 := by
      by_cases hbx : b = x
      · subst x
        rw [inner_ket_self, inner_ket_eq_ite, if_neg hba]
        simp
      · rw [inner_ket_eq_ite, if_neg hbx]
        simp
    calc
      star (localPauliAmplitude S) * localPauliAmplitude S *
          inner Complex (ket b) (ket x) * inner Complex (ket x) (ket a) *
          inner Complex l (leftCompression S A k) =
        (star (localPauliAmplitude S) * localPauliAmplitude S) *
          (inner Complex (ket b) (ket x) * inner Complex (ket x) (ket a)) *
          inner Complex l (leftCompression S A k) := by ring
      _ = 0 := by rw [hprod]; simp

theorem quantumChannel_ext {H K : Type u} [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {Phi Psi : QuantumChannel H K} (h : Phi.toLinearMap = Psi.toLinearMap) :
    Phi = Psi := by
  cases Phi
  cases Psi
  cases h
  rfl

theorem unitaryTransport_toQuantumChannel {κ : Type v} [Fintype κ]
    {H K Ht Kt : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht]
    [FiniteQuantumSystem Ht] [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt]
    [FiniteQuantumSystem Kt] (E : FiniteKrausFamily κ H K)
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt) (hE : E.Complete) :
    (E.unitaryTransport U V).toQuantumChannel
        (E.unitaryTransport_complete U V hE) =
      QuantumChannel.comp (QuantumChannel.unitaryConj V)
        (QuantumChannel.comp (E.toQuantumChannel hE)
          (QuantumChannel.unitaryConj U.symm)) := by
  apply quantumChannel_ext
  apply LinearMap.ext
  intro A
  rw [FiniteKrausFamily.toQuantumChannel_apply_sum]
  change (E.unitaryTransport U V).inducedMap A = _
  rw [FiniteKrausFamily.unitaryTransport_inducedMap_apply]
  change V.conjOperator (E.inducedMap (U.symm.conjOperator A)) =
    V.conjOperator ((E.toQuantumChannel hE) (U.symm.conjOperator A))
  congr 1

theorem wordPauliTwirlFactorized_eq_refill_comp_erasure (S : FiniteSubsystem ι) :
    wordPauliTwirlFactorized S =
      QuantumChannel.comp (refillFactorized S) S.erasureChannel := by
  apply quantumChannel_ext
  apply LinearMap.ext
  intro A
  apply operator_ext_factorized_basis S
  intro p q
  rw [factorizedBasis_apply, factorizedBasis_apply]
  rw [wordPauliTwirlFactorized_matrix_element,
    refill_comp_erasure_matrix_element]

noncomputable def localPauliFamily (S : FiniteSubsystem ι) :
    FiniteKrausFamily (LocalPauliWordIndex S)
      (Qubit.QubitRegister ι) (Qubit.QubitRegister ι) :=
  (wordPauliFamilyFactorized S).unitaryTransport
    S.registerFactorization.symm S.registerFactorization.symm

theorem localPauliFamily_complete (S : FiniteSubsystem ι) :
    (localPauliFamily S).Complete := by
  exact (wordPauliFamilyFactorized S).unitaryTransport_complete
    S.registerFactorization.symm S.registerFactorization.symm
    (wordPauliFamilyFactorized_complete S)

theorem extendLocal_smul (S : FiniteSubsystem ι) (c : Complex)
    (A : Operator S.selectedSystem) :
    S.extendLocal (c • A) = c • S.extendLocal A := by
  apply TensorProduct.ext'
  intro h k
  simp only [FiniteSubsystem.extendLocal, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearMap.smul_apply]
  rw [← TensorProduct.smul_tmul']

theorem localPauliFamily_operator_supportedOnRegister (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) :
    S.OperatorSupportedOnRegister ((localPauliFamily S).operator p) := by
  refine ⟨localPauliAmplitude S • PauliSymplectic.toQubitOperator (wordBinaryPauli S p), ?_⟩
  rw [FiniteSubsystem.extendLocalToRegister, extendLocal_smul]
  rfl

/-- The normalized local binary-Pauli twirl, represented by its finite Kraus family. -/
noncomputable def localPauliTwirl (S : FiniteSubsystem ι) :
    QuantumChannel (Qubit.QubitRegister ι) (Qubit.QubitRegister ι) :=
  (localPauliFamily S).toQuantumChannel (localPauliFamily_complete S)

theorem localPauliTwirl_eq_transport (S : FiniteSubsystem ι) :
    localPauliTwirl S =
      QuantumChannel.comp (QuantumChannel.unitaryConj S.registerFactorization.symm)
        (QuantumChannel.comp (wordPauliTwirlFactorized S)
          (QuantumChannel.unitaryConj S.registerFactorization)) := by
  exact unitaryTransport_toQuantumChannel (wordPauliFamilyFactorized S)
    S.registerFactorization.symm S.registerFactorization.symm
    (wordPauliFamilyFactorized_complete S)

/-- Refill the selected factor maximally mixed after a concrete erasure. -/
noncomputable def localPauliRefill (S : FiniteSubsystem ι) :
    QuantumChannel S.complementSystem (Qubit.QubitRegister ι) :=
  QuantumChannel.comp (QuantumChannel.unitaryConj S.registerFactorization.symm)
    (refillFactorized S)

theorem quantumChannel_comp_assoc {H K L M : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
    [NormedAddCommGroup M] [InnerProductSpace Complex M] [FiniteQuantumSystem M]
    (Phi : QuantumChannel H K) (Psi : QuantumChannel K L) (Omega : QuantumChannel L M) :
    QuantumChannel.comp Omega (QuantumChannel.comp Psi Phi) =
      QuantumChannel.comp (QuantumChannel.comp Omega Psi) Phi := by
  apply quantumChannel_ext
  rfl

theorem localPauliTwirl_eq_refill_comp_erasureFromRegister (S : FiniteSubsystem ι) :
    localPauliTwirl S =
      QuantumChannel.comp (localPauliRefill S) S.erasureChannelFromRegister := by
  rw [localPauliTwirl_eq_transport,
    wordPauliTwirlFactorized_eq_refill_comp_erasure]
  unfold localPauliRefill FiniteSubsystem.erasureChannelFromRegister
  exact (quantumChannel_comp_assoc
    (QuantumChannel.unitaryConj S.registerFactorization)
    S.erasureChannel
    (QuantumChannel.comp (QuantumChannel.unitaryConj S.registerFactorization.symm)
      (refillFactorized S))).symm

theorem erasureRecoverableFromRegister_of_localPauliTwirl_correctable
    (S : FiniteSubsystem ι) (C : QuantumCode (Qubit.QubitRegister ι))
    (recovery : QuantumChannel (Qubit.QubitRegister ι) (Qubit.QubitRegister ι))
    (h : Correctable (Qubit.QubitRegister ι) (Qubit.QubitRegister ι) C
      (localPauliTwirl S) recovery) :
    S.ErasureRecoverableFromRegister C := by
  refine ⟨QuantumChannel.comp recovery (localPauliRefill S), ?_⟩
  intro rho hrho
  have hcorrected := h rho hrho
  change recovery (localPauliRefill S (S.erasureChannelFromRegister rho.toOperator)) =
    rho.toOperator
  have hnoise := congrArg
    (fun Phi : QuantumChannel (Qubit.QubitRegister ι) (Qubit.QubitRegister ι) =>
      Phi rho.toOperator)
    (localPauliTwirl_eq_refill_comp_erasureFromRegister S)
  change (localPauliTwirl S) rho.toOperator =
    localPauliRefill S (S.erasureChannelFromRegister rho.toOperator) at hnoise
  rw [← hnoise]
  exact hcorrected

end QEC.Locality
