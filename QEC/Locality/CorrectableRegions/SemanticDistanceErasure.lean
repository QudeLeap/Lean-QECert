import QEC.Coding.Stabilizer.Correctability
import QEC.Coding.Stabilizer.Distance
import QEC.Locality.CorrectableRegions.LocalPauliErasureTransfer
/-!
# Semantic stabilizer distance and finite-subsystem erasure

This module bridges the M3 finite binary-Pauli criterion with the concrete
finite-subsystem erasure channel.  The local closure starts by embedding a
selected-coordinate Pauli word into the ambient qubit register.
-/

noncomputable section

namespace QEC
namespace Locality

open QEC Semantics Coding
open scoped TensorProduct

open PauliSymplectic

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Extend a binary word on the selected coordinates by zero on the complement. -/
def embedSelectedWord (S : FiniteSubsystem ι)
    (w : Coding.Word (ZMod 2) S.SelectedCoordinates) : Coding.Word (ZMod 2) ι :=
  fun i => if hi : i ∈ S.selected then w ⟨i, hi⟩ else 0

/-- The inclusion of selected coordinate subtypes into the ambient register. -/
def selectedCoordinateEmbedding (S : FiniteSubsystem ι) : S.SelectedCoordinates ↪ ι where
  toFun := Subtype.val
  inj' := Subtype.val_injective

@[simp]
theorem embedSelectedWord_apply_mem (S : FiniteSubsystem ι)
    (w : Coding.Word (ZMod 2) S.SelectedCoordinates) {i : ι} (hi : i ∈ S.selected) :
    embedSelectedWord S w i = w ⟨i, hi⟩ := by
  simp [embedSelectedWord, hi]

@[simp]
theorem embedSelectedWord_apply_not_mem (S : FiniteSubsystem ι)
    (w : Coding.Word (ZMod 2) S.SelectedCoordinates) {i : ι} (hi : i ∉ S.selected) :
    embedSelectedWord S w i = 0 := by
  simp [embedSelectedWord, hi]

/-- The support of an embedded selected-coordinate word is contained in the selection. -/
theorem binarySupport_embedSelectedWord_subset (S : FiniteSubsystem ι)
    (w : Coding.Word (ZMod 2) S.SelectedCoordinates) :
    binarySupport (embedSelectedWord S w) ⊆ S.selected := by
  intro i hi
  by_contra hnot
  have hzero : embedSelectedWord S w i = 0 :=
    embedSelectedWord_apply_not_mem S w hnot
  exact ((mem_binarySupport (embedSelectedWord S w) i).1 hi) hzero

/-- Embedding a word maps its binary support along the selected-coordinate inclusion. -/
theorem binarySupport_embedSelectedWord (S : FiniteSubsystem ι)
    (w : Coding.Word (ZMod 2) S.SelectedCoordinates) :
    binarySupport (embedSelectedWord S w) =
      (binarySupport w).map (selectedCoordinateEmbedding S) := by
  ext i
  constructor
  · intro hi
    by_cases his : i ∈ S.selected
    · refine Finset.mem_map.2 ⟨⟨i, his⟩, ?_, rfl⟩
      have hnonzero := (mem_binarySupport (embedSelectedWord S w) i).1 hi
      rw [embedSelectedWord_apply_mem S w his] at hnonzero
      exact (mem_binarySupport w ⟨i, his⟩).2 hnonzero
    · have hzero : embedSelectedWord S w i = 0 :=
        embedSelectedWord_apply_not_mem S w his
      exact False.elim (((mem_binarySupport (embedSelectedWord S w) i).1 hi) hzero)
  · rintro hi
    rcases Finset.mem_map.1 hi with ⟨j, hj, rfl⟩
    rw [mem_binarySupport]
    change embedSelectedWord S w (j : ι) ≠ 0
    rw [embedSelectedWord_apply_mem S w j.property]
    exact (mem_binarySupport w j).1 hj

/-- The ambient binary Pauli represented by a local Pauli-twirl branch. -/
noncomputable def embeddedLocalPauli (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) : Binary ι :=
  { phase := 0
    vector :=
      { xPart := embedSelectedWord S p.1
        zPart := embedSelectedWord S p.2 } }

@[simp]
theorem xSupport_embeddedLocalPauli (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) :
    xSupport (embeddedLocalPauli S p) =
      (binarySupport p.1).map (selectedCoordinateEmbedding S) := by
  rw [show xSupport (embeddedLocalPauli S p) =
      binarySupport (embedSelectedWord S p.1) by rfl]
  exact binarySupport_embedSelectedWord S p.1

@[simp]
theorem zSupport_embeddedLocalPauli (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) :
    zSupport (embeddedLocalPauli S p) =
      (binarySupport p.2).map (selectedCoordinateEmbedding S) := by
  rw [show zSupport (embeddedLocalPauli S p) =
      binarySupport (embedSelectedWord S p.2) by rfl]
  exact binarySupport_embedSelectedWord S p.2

/-- Splitting after an embedded local X support flips only the selected factor. -/
theorem splitBitstring_flipSupport_embedSelectedWord (S : FiniteSubsystem ι)
    (w : Coding.Word (ZMod 2) S.SelectedCoordinates) (bits : Qubit.Bitstring ι) :
    S.splitBitstring (Qubit.flipSupport (binarySupport (embedSelectedWord S w)) bits) =
      (Qubit.flipSupport (binarySupport w) (S.splitBitstring bits).1,
        (S.splitBitstring bits).2) := by
  apply Prod.ext
  · funext i
    have hvalue : embedSelectedWord S w (i : ι) = w i :=
      embedSelectedWord_apply_mem S w i.property
    simp only [FiniteSubsystem.splitBitstring, Qubit.flipSupport, mem_binarySupport]
    rw [hvalue]
  · funext i
    have hzero : embedSelectedWord S w (i : ι) = 0 :=
      embedSelectedWord_apply_not_mem S w i.property
    simp only [FiniteSubsystem.splitBitstring, Qubit.flipSupport, mem_binarySupport]
    rw [hzero]
    simp

/-- The Z phase of an embedded selected-coordinate word is computed on the selected factor. -/
theorem zSupportPhase_embedSelectedWord (S : FiniteSubsystem ι)
    (w : Coding.Word (ZMod 2) S.SelectedCoordinates) (bits : Qubit.Bitstring ι) :
    Qubit.zSupportPhase (binarySupport (embedSelectedWord S w)) bits =
      Qubit.zSupportPhase (binarySupport w) (S.splitBitstring bits).1 := by
  rw [binarySupport_embedSelectedWord]
  simp only [Qubit.zSupportPhase, Finset.prod_map]
  rfl

/-- An embedded selected-coordinate X support flips exactly the selected label. -/
theorem flipSupport_embedSelectedWord_eq_recombine (S : FiniteSubsystem ι)
    (w : Coding.Word (ZMod 2) S.SelectedCoordinates) (bits : Qubit.Bitstring ι) :
    Qubit.flipSupport (binarySupport (embedSelectedWord S w)) bits =
      S.recombineBitstring
        (Qubit.flipSupport (binarySupport w) (S.splitBitstring bits).1,
          (S.splitBitstring bits).2) := by
  apply S.bitstringFactorization.injective
  change S.splitBitstring (Qubit.flipSupport (binarySupport (embedSelectedWord S w)) bits) =
    S.splitBitstring
      (S.recombineBitstring
        (Qubit.flipSupport (binarySupport w) (S.splitBitstring bits).1,
          (S.splitBitstring bits).2))
  rw [splitBitstring_flipSupport_embedSelectedWord]
  simpa [FiniteSubsystem.bitstringFactorization] using
    (S.bitstringFactorization.apply_symm_apply
      (Qubit.flipSupport (binarySupport w) (S.splitBitstring bits).1,
        (S.splitBitstring bits).2)).symm

/-- The inverse register factorization recombines factorized computational basis labels. -/
theorem registerFactorization_symm_apply_factorizedBasis (S : FiniteSubsystem ι)
    (left : Qubit.Bitstring S.SelectedCoordinates)
    (right : Qubit.Bitstring S.ComplementCoordinates) :
    S.registerFactorization.symm
      (ket left ⊗ₜ[Complex] ket right) =
      ket (S.recombineBitstring (left, right)) := by
  apply S.registerFactorization.toLinearEquiv.injective
  rw [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply]
  rw [S.registerFactorization_apply_basis]
  have hsplit : S.splitBitstring (S.recombineBitstring (left, right)) = (left, right) := by
    simpa [FiniteSubsystem.bitstringFactorization] using
      S.bitstringFactorization.apply_symm_apply (left, right)
  rw [hsplit]

/-- The concrete basis action of a binary Pauli operator. -/
theorem toQubitOperator_apply_ket (P : Binary ι) (bits : Qubit.Bitstring ι) :
    toQubitOperator P (ket bits) =
      (binaryPhaseScalar P.phase * Qubit.zSupportPhase (zSupport P) bits) •
        ket (Qubit.flipSupport (xSupport P) bits) := by
  ext output
  rw [toQubitOperator_apply]
  by_cases hout : output = Qubit.flipSupport (xSupport P) bits
  · subst output
    rw [flipSupport_flipSupport]
    simp [ket, EuclideanSpace.basisFun_apply]
  · have hflip : Qubit.flipSupport (xSupport P) output ≠ bits := by
      intro hflip
      apply hout
      calc
        output = Qubit.flipSupport (xSupport P)
            (Qubit.flipSupport (xSupport P) output) :=
          (flipSupport_flipSupport (xSupport P) output).symm
        _ = Qubit.flipSupport (xSupport P) bits := by rw [hflip]
    simp [ket, EuclideanSpace.basisFun_apply, hflip, hout]

/-- The embedded local Pauli has the expected global computational-basis action. -/
theorem toQubitOperator_embeddedLocalPauli_apply_ket (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) (bits : Qubit.Bitstring ι) :
    toQubitOperator (embeddedLocalPauli S p) (ket bits) =
      Qubit.zSupportPhase (binarySupport p.2) (S.splitBitstring bits).1 •
        ket (Qubit.flipSupport (binarySupport (embedSelectedWord S p.1)) bits) := by
  rw [toQubitOperator_apply_ket]
  rw [xSupport_embeddedLocalPauli, zSupport_embeddedLocalPauli]
  rw [← binarySupport_embedSelectedWord S p.2,
    ← binarySupport_embedSelectedWord S p.1]
  rw [zSupportPhase_embedSelectedWord]
  simp [embeddedLocalPauli]

/-- Extending a selected-coordinate twirl branch agrees with its embedded global basis action. -/
theorem extendLocalToRegister_wordBinaryPauli_apply_ket (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) (bits : Qubit.Bitstring ι) :
    S.extendLocalToRegister (toQubitOperator (wordBinaryPauli S p)) (ket bits) =
      Qubit.zSupportPhase (binarySupport p.2) (S.splitBitstring bits).1 •
        ket (Qubit.flipSupport (binarySupport (embedSelectedWord S p.1)) bits) := by
  change S.registerFactorization.symm
    (S.extendLocal (toQubitOperator (wordBinaryPauli S p))
      (S.registerFactorization (ket bits))) = _
  rw [S.registerFactorization_apply_basis]
  simp only [FiniteSubsystem.extendLocal, TensorProduct.map_tmul, LinearMap.id_apply]
  rw [wordBinaryPauli_apply_ket]
  rw [← TensorProduct.smul_tmul']
  rw [map_smul]
  rw [registerFactorization_symm_apply_factorizedBasis]
  rw [flipSupport_embedSelectedWord_eq_recombine]

/-- The explicit global binary Pauli is the concrete extension of the local twirl branch. -/
theorem toQubitOperator_embeddedLocalPauli_eq_extendLocalToRegister (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) :
    toQubitOperator (embeddedLocalPauli S p) =
      S.extendLocalToRegister (toQubitOperator (wordBinaryPauli S p)) := by
  let b := EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
  apply LinearMap.ext
  intro psi
  rw [← b.sum_repr' psi, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro bits _
  rw [map_smul, map_smul]
  congr 1
  calc
    toQubitOperator (embeddedLocalPauli S p) (b bits) =
        Qubit.zSupportPhase (binarySupport p.2) (S.splitBitstring bits).1 •
          ket (Qubit.flipSupport (binarySupport (embedSelectedWord S p.1)) bits) := by
      simpa [b] using toQubitOperator_embeddedLocalPauli_apply_ket S p bits
    _ = S.extendLocalToRegister (toQubitOperator (wordBinaryPauli S p)) (b bits) := by
      symm
      simpa [b] using extendLocalToRegister_wordBinaryPauli_apply_ket S p bits

/-- Extension to the original register commutes with scalar multiplication. -/
theorem extendLocalToRegister_smul (S : FiniteSubsystem ι)
    (c : Complex) (A : Operator S.selectedSystem) :
    S.extendLocalToRegister (c • A) = c • S.extendLocalToRegister A := by
  unfold FiniteSubsystem.extendLocalToRegister
  rw [extendLocal_smul]
  ext x
  simp [UnitaryTransport.conjOperator]

/-- Finite Kraus families are determined by their branch operators. -/
theorem finiteKrausFamily_ext
    {α : Type*} [Fintype α]
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
    (E F : FiniteKrausFamily α H K)
    (h : E.operator = F.operator) : E = F := by
  cases E
  cases F
  cases h
  rfl

/-- The exact selected-register operator underlying each #398 twirl branch. -/
theorem localPauliFamily_operator_eq_extendLocalToRegister (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) :
    (localPauliFamily S).operator p =
      S.extendLocalToRegister
        (localPauliAmplitude S • toQubitOperator (wordBinaryPauli S p)) := by
  rw [FiniteSubsystem.extendLocalToRegister, extendLocal_smul]
  rfl

/-- The binary family on embedded local Paulis is exactly #398's local twirl family. -/
theorem embeddedLocalPauliKrausFamily_eq_localPauliFamily (S : FiniteSubsystem ι) :
    binaryPauliKrausFamily (embeddedLocalPauli S) (fun _ => localPauliAmplitude S) =
      localPauliFamily S := by
  apply finiteKrausFamily_ext
  funext p
  rw [binaryPauliKrausFamily_operator]
  rw [localPauliFamily_operator_eq_extendLocalToRegister,
    extendLocalToRegister_smul,
    toQubitOperator_embeddedLocalPauli_eq_extendLocalToRegister]

/-- The embedded local binary-Pauli family is complete because it is #398's twirl family. -/
theorem embeddedLocalPauliKrausFamily_complete (S : FiniteSubsystem ι) :
    (binaryPauliKrausFamily (embeddedLocalPauli S)
      (fun _ => localPauliAmplitude S)).Complete := by
  rw [embeddedLocalPauliKrausFamily_eq_localPauliFamily]
  exact localPauliFamily_complete S

/-- The M3-ready embedded binary-Pauli channel is exactly the concrete local Pauli twirl. -/
theorem embeddedLocalPauliKrausFamily_toQuantumChannel_eq_localPauliTwirl
    (S : FiniteSubsystem ι) :
    (binaryPauliKrausFamily (embeddedLocalPauli S)
      (fun _ => localPauliAmplitude S)).toQuantumChannel
        (embeddedLocalPauliKrausFamily_complete S) =
      localPauliTwirl S := by
  apply quantumChannel_ext
  apply LinearMap.ext
  intro A
  unfold localPauliTwirl
  rw [FiniteKrausFamily.toQuantumChannel_apply_sum,
    FiniteKrausFamily.toQuantumChannel_apply_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hoperator :
      (binaryPauliKrausFamily (embeddedLocalPauli S)
        (fun _ => localPauliAmplitude S)).operator p =
        (localPauliFamily S).operator p :=
    congrFun (congrArg FiniteKrausFamily.operator
      (embeddedLocalPauliKrausFamily_eq_localPauliFamily S)) p
  rw [hoperator]

/-- Every embedded local-Pauli branch is supported in the selected subsystem. -/
theorem support_embeddedLocalPauli_subset (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) :
    support (embeddedLocalPauli S p) ⊆ S.selected := by
  intro i hi
  rcases (mem_support (embeddedLocalPauli S p) i).1 hi with hx | hz
  · exact binarySupport_embedSelectedWord_subset S p.1
      (by simpa [embeddedLocalPauli, xSupport] using hx)
  · exact binarySupport_embedSelectedWord_subset S p.2
      (by simpa [embeddedLocalPauli, zSupport] using hz)

/-- Relative local-Pauli twirl branches remain supported on the selected subsystem. -/
theorem support_relative_embeddedLocalPauli_subset (S : FiniteSubsystem ι)
    (p q : LocalPauliWordIndex S) :
    support (binaryMul (binaryDagger (embeddedLocalPauli S p))
      (embeddedLocalPauli S q)) ⊆ S.selected := by
  refine (support_binaryMul_subset _ _).trans ?_
  rw [support_binaryDagger]
  exact Finset.union_subset
    (support_embeddedLocalPauli_subset S p)
    (support_embeddedLocalPauli_subset S q)

/-- The relative Pauli of any two local twirl branches has weight at most `|U|`. -/
theorem weight_relative_embeddedLocalPauli_le_selected_card (S : FiniteSubsystem ι)
    (p q : LocalPauliWordIndex S) :
    weight (binaryMul (binaryDagger (embeddedLocalPauli S p))
      (embeddedLocalPauli S q)) ≤ S.selected.card := by
  exact Finset.card_le_card (support_relative_embeddedLocalPauli_subset S p q)

/--
Semantic stabilizer-distance leastness gives the exact M3 pair-product
disjunction for every pair of local twirl branches below the selected size.
-/
theorem semanticStabilizerDistance_localPauli_pairProductCriterion
    (Q : StabilizerCode.SourceValidBinary ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance Q d)
    (S : FiniteSubsystem ι) (hSelected : S.selected.card < d) :
    ∀ p q : LocalPauliWordIndex S,
      Q.1.InGeneratedGroupUpToSign
          (binaryMul (binaryDagger (embeddedLocalPauli S p))
            (embeddedLocalPauli S q)) ∨
        ¬ Q.1.InBinaryNormalizer
          (binaryMul (binaryDagger (embeddedLocalPauli S p))
            (embeddedLocalPauli S q)) := by
  rcases
      (StabilizerCode.semanticStabilizerDistance_iff_minWeight_inBinaryNormalizer_diff
        Q d).1 hDistance with
    ⟨_witness, _witnessNormalizer, _witnessOutside, _witnessWeight, hLeast⟩
  intro p q
  by_cases hGenerated : Q.1.InGeneratedGroupUpToSign
      (binaryMul (binaryDagger (embeddedLocalPauli S p))
        (embeddedLocalPauli S q))
  · exact Or.inl hGenerated
  · right
    intro hNormalizer
    have hDistanceLe := hLeast
      (binaryMul (binaryDagger (embeddedLocalPauli S p))
        (embeddedLocalPauli S q)) hNormalizer hGenerated
    have hWeightLe := weight_relative_embeddedLocalPauli_le_selected_card S p q
    exact (Nat.not_le_of_gt hSelected) (hDistanceLe.trans hWeightLe)

/--
Every finite qubit subsystem smaller than a finite semantic stabilizer distance
has a typed CPTP recovery for its concrete erasure channel.
-/
theorem semanticStabilizerDistance_erasureRecoverableFromRegister
    (Q : StabilizerCode.SourceValidBinary ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance Q d)
    (S : FiniteSubsystem ι) (hSelected : S.selected.card < d) :
    ∃ recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) S.complementSystem Q.1.code
        S.erasureChannelFromRegister recovery := by
  have hPairs : ∀ p q : LocalPauliWordIndex S,
      localPauliAmplitude S ≠ 0 → localPauliAmplitude S ≠ 0 →
        Q.1.InGeneratedGroupUpToSign
            (binaryMul (binaryDagger (embeddedLocalPauli S p))
              (embeddedLocalPauli S q)) ∨
          ¬ Q.1.InBinaryNormalizer
            (binaryMul (binaryDagger (embeddedLocalPauli S p))
              (embeddedLocalPauli S q)) := by
    intro p q _ _
    exact semanticStabilizerDistance_localPauli_pairProductCriterion
      Q d hDistance S hSelected p q
  rcases
      (StabilizerCode.exists_finiteKrausCorrectable_iff_pairProductCriterion_on_support
        Q (embeddedLocalPauli S) (fun _ => localPauliAmplitude S)
        (embeddedLocalPauliKrausFamily_complete S)).2 hPairs with
    ⟨twirlRecovery, hTwirlKrausRecovery⟩
  rcases
      (Semantics.exists_finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel
        Q.1.code
        (binaryPauliKrausFamily (embeddedLocalPauli S)
          (fun _ => localPauliAmplitude S))).1
        ⟨twirlRecovery, hTwirlKrausRecovery⟩ with
    ⟨hComplete, twirlRecovery, hTwirlRecovery⟩
  have hTwirlRecovery' : Correctable (Qubit.QubitRegister ι)
      (Qubit.QubitRegister ι) Q.1.code
      ((binaryPauliKrausFamily (embeddedLocalPauli S)
        (fun _ => localPauliAmplitude S)).toQuantumChannel
          (embeddedLocalPauliKrausFamily_complete S)) twirlRecovery := by
    simpa using hTwirlRecovery
  have hLocalTwirlRecovery : Correctable (Qubit.QubitRegister ι)
      (Qubit.QubitRegister ι) Q.1.code (localPauliTwirl S) twirlRecovery := by
    rw [← embeddedLocalPauliKrausFamily_toQuantumChannel_eq_localPauliTwirl]
    exact hTwirlRecovery'
  exact erasureRecoverableFromRegister_of_localPauliTwirl_correctable
    S Q.1.code twirlRecovery hLocalTwirlRecovery

end Locality
end QEC
