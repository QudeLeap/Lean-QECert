import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.LogicalDimension
import QEC.Coding.CSS.Distance
import QEC.Coding.Stabilizer.DecoderDressedLogical

/-!
# A bare logical Pauli pair from the actual finite H1 generator

The X word is literally the selected finite-prefix generator with coefficient1.
Finite symplectic separation supplies a Z-coordinate partner, whose kernel and
pairing properties are proved before choice. All operators act on the original
labelled CSS code and Hamiltonian, including the seed and both parities.
CLBT10 arXiv.02.tex:619–674 motivates the bare pair; BDL26
paper.tex:2202–2211,2221–2225,2240 supplies the seed/even-family motivation.
-/
noncomputable section
namespace QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators

variable (S : OddScale) (m : Nat)

/-- The original labelled stabilizer, with no new code or physical register. -/
abbrev stabilizer := binaryCSSStabilizerCodeOfParityChecks
  (zSyndrome S m) (xSyndrome S m) (row_orthogonal S m)

/-- Source validity is derived by the existing actual parity-check constructor. -/
def sourceValid : StabilizerCode.SourceValidBinary (Physical S m) :=
  binaryCSSSourceValidStabilizerOfParityChecks (zSyndrome S m) (xSyndrome S m) (row_orthogonal S m)

/-- The literal canonical coefficient-one generator, never an arbitrary cocycle. -/
abbrev canonicalGenerator := BDL26FiniteCohomology.generator S m (1 : ZMod 2)

theorem canonical_coefficient :
    BDL26FiniteCohomology.finiteH1Equiv S m
      (BDL26FiniteCohomology.classOf S m (canonicalGenerator S m)) = 1 := by
  have h := BDL26FiniteCohomology.finite_right_inverse S m (1 : ZMod 2)
  rw [BDL26FiniteCohomology.finiteH1Equiv_symm_scalar] at h
  exact h

theorem canonical_class_ne_zero :
    BDL26FiniteCohomology.classOf S m (canonicalGenerator S m) ≠ 0 := by
  intro h
  have hc := canonical_coefficient S m
  rw [h, map_zero] at hc
  exact zero_ne_one hc

theorem canonical_word_ne_zero : (canonicalGenerator S m).val ≠ 0 := by
  intro h
  have he : canonicalGenerator S m = 0 := Subtype.ext h
  apply canonical_class_ne_zero S m
  rw [he, map_zero]

theorem canonical_cocycle : zSyndrome S m (canonicalGenerator S m).val = 0 :=
  (BDL26RZCohomology.mem_cocycle_iff _ _).mp (canonicalGenerator S m).property

theorem canonical_not_row :
    (canonicalGenerator S m).val ∉ (parityCheckRowCode (xSyndrome S m)).carrier := by
  intro hrow
  have hb : canonicalGenerator S m ∈
      (BDL26FiniteCohomology.complex S m).middleCoboundaryInCocycles := by
    change (canonicalGenerator S m).val ∈ (complex S m).firstCoboundaryCheckCode.carrier
    rw [← xRowCode S m]
    exact hrow
  exact canonical_class_ne_zero S m
    ((Submodule.Quotient.mk_eq_zero _).mpr hb)

/-- The full selected word is the existing prefix map of the original seed. -/
theorem canonical_prefix_word : (canonicalGenerator S m).val =
    BDL26AlternatingCochain.map1 S m BDL26SeedCohomology.seedElement.val := by
  simpa only [one_smul] using BDL26FiniteCohomology.generator_value S m (1 : ZMod 2)

theorem canonical_seed_word : (canonicalGenerator S 0).val = BDL26LevelTwoDistance.seedCocycle := by
  have hbase :
      (BDL26AlternatingCochain.map1 S 0 BDL26SeedCohomology.seedElement.val :
        Word (ZMod 2) (Physical S 0)) =
      (BDL26LevelTwoDistance.seedCocycle : Word (ZMod 2) (Physical S 0)) := rfl
  exact Eq.trans (canonical_prefix_word S 0) hbase

/-- Pure X on the actual coefficient-one cohomology representative. -/
def logicalX : Binary (Physical S m) := cssXCheck (canonicalGenerator S m).val

@[simp] theorem logicalX_phase : (logicalX S m).phase = 0 := rfl
@[simp] theorem logicalX_xPart : (logicalX S m).vector.xPart = (canonicalGenerator S m).val := rfl
@[simp] theorem logicalX_zPart : (logicalX S m).vector.zPart = 0 := rfl

theorem logicalX_normalizer : (stabilizer S m).InBinaryNormalizer (logicalX S m) := by
  apply (inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
    (zSyndrome S m) (xSyndrome S m) (row_orthogonal S m) _).mpr
  constructor
  · change zSyndrome S m (canonicalGenerator S m).val = 0
    exact canonical_cocycle S m
  · change xSyndrome S m 0 = 0
    exact map_zero _

theorem logicalX_not_generated : ¬ (stabilizer S m).InGeneratedGroupUpToSign (logicalX S m) := by
  intro h
  have hr := (inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
    (zSyndrome S m) (xSyndrome S m) (row_orthogonal S m) _).mp h
  exact canonical_not_row S m hr.1

/-- A genuine partner is derived from finite separation, then projected to pure Z. -/
theorem exists_zPartner : ∃ z : Word (ZMod 2) (Physical S m),
    xSyndrome S m z = 0 ∧ wordPairing (canonicalGenerator S m).val z = 1 := by
  obtain ⟨F, hF, hanti⟩ := StabilizerCode.exists_inBinaryNormalizer_not_commutes
    (stabilizer S m) (logicalX_normalizer S m) (logicalX_not_generated S m)
  have hk := (inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
    (zSyndrome S m) (xSyndrome S m) (row_orthogonal S m) F).mp hF
  refine ⟨F.vector.zPart, hk.2, ?_⟩
  apply zmod_two_eq_one_of_ne_zero
  intro hp
  apply hanti
  simpa [Commutes, logicalX, cssXCheck, symplecticForm, wordPairing_apply, dotProduct] using hp

/-- Chosen only from the proved actual kernel/pairing existence, with no support claim. -/
def partnerWord : Word (ZMod 2) (Physical S m) := Classical.choose (exists_zPartner S m)

theorem partnerWord_kernel : xSyndrome S m (partnerWord S m) = 0 :=
  (Classical.choose_spec (exists_zPartner S m)).1

theorem partnerWord_pairing : wordPairing (canonicalGenerator S m).val (partnerWord S m) = 1 :=
  (Classical.choose_spec (exists_zPartner S m)).2

theorem partnerWord_ne_zero : partnerWord S m ≠ 0 := by
  intro h
  have hp := partnerWord_pairing S m
  rw [h] at hp
  have hz : wordPairing (canonicalGenerator S m).val 0 = 0 := by
    simp [wordPairing_apply, dotProduct]
  rw [hz] at hp
  exact zero_ne_one hp

/-- Pure Z on the same physical word carrier as the canonical X. -/
def logicalZ : Binary (Physical S m) := cssZCheck (partnerWord S m)

@[simp] theorem logicalZ_phase : (logicalZ S m).phase = 0 := rfl
@[simp] theorem logicalZ_xPart : (logicalZ S m).vector.xPart = 0 := rfl
@[simp] theorem logicalZ_zPart : (logicalZ S m).vector.zPart = partnerWord S m := rfl

theorem logicalZ_normalizer : (stabilizer S m).InBinaryNormalizer (logicalZ S m) := by
  apply (inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
    (zSyndrome S m) (xSyndrome S m) (row_orthogonal S m) _).mpr
  constructor
  · change zSyndrome S m 0 = 0
    exact map_zero _
  · change xSyndrome S m (partnerWord S m) = 0
    exact partnerWord_kernel S m

theorem logical_pairing_one :
    symplecticForm (logicalX S m).vector (logicalZ S m).vector = 1 := by
  simpa [logicalX, logicalZ, cssXCheck, cssZCheck, symplecticForm,
    wordPairing_apply, dotProduct] using partnerWord_pairing S m

theorem logical_not_commutes : ¬ Commutes (logicalX S m) (logicalZ S m) := by
  change symplecticForm (logicalX S m).vector (logicalZ S m).vector ≠ 0
  rw [logical_pairing_one]
  exact one_ne_zero

theorem logicalZ_not_generated : ¬ (stabilizer S m).InGeneratedGroupUpToSign (logicalZ S m) := by
  rintro ⟨g, hg, hv⟩
  have hzg : Commutes (logicalZ S m) (logicalX S m) :=
    (commutes_iff_of_binaryUpToSign_left hv).mpr
      ((commutes_comm g (logicalX S m)).mpr (logicalX_normalizer S m g hg))
  exact logical_not_commutes S m ((commutes_comm (logicalX S m) (logicalZ S m)).mpr hzg)

theorem logicalX_not_identity : ¬ BinaryUpToSign (logicalX S m) binaryOne := by
  intro h
  have hx := congrArg SymplecticVector.xPart h
  exact canonical_word_ne_zero S m hx

theorem logicalZ_not_identity : ¬ BinaryUpToSign (logicalZ S m) binaryOne := by
  intro h
  have hz := congrArg SymplecticVector.zPart h
  exact partnerWord_ne_zero S m hz

theorem logicalX_not_logicalZ : ¬ BinaryUpToSign (logicalX S m) (logicalZ S m) := by
  intro h
  have hx := congrArg SymplecticVector.xPart h
  exact canonical_word_ne_zero S m hx

/-- The original normalized Hermitian realizations on the actual register. -/
abbrev Xbar : Operator (Qubit.QubitRegister (Physical S m)) := toHermitianQubitOperator (logicalX S m)
abbrev Zbar : Operator (Qubit.QubitRegister (Physical S m)) := toHermitianQubitOperator (logicalZ S m)

@[simp] theorem Xbar_adjoint : LinearMap.adjoint (Xbar S m) = Xbar S m :=
  adjoint_toHermitianQubitOperator_eq_self _
@[simp] theorem Zbar_adjoint : LinearMap.adjoint (Zbar S m) = Zbar S m :=
  adjoint_toHermitianQubitOperator_eq_self _
@[simp] theorem Xbar_square : Xbar S m * Xbar S m = 1 := toHermitianQubitOperator_square _
@[simp] theorem Zbar_square : Zbar S m * Zbar S m = 1 := toHermitianQubitOperator_square _

theorem Xbar_Zbar_anticommute : Xbar S m * Zbar S m = -(Zbar S m * Xbar S m) :=
  StabilizerCode.LocalStabilizerHamiltonian.toHermitianQubitOperator_anticommute_of_not_commutes
    _ _ (logical_not_commutes S m)

/-- Ordinary bare normalizer semantics imply commutation with every original row. -/
theorem normalizer_commutes_check (E : Binary (Physical S m))
    (hE : (stabilizer S m).InBinaryNormalizer E) (j : Sum (ZLabel S m) (XLabel S m)) :
    Commute (toHermitianQubitOperator E) (toQubitOperator (check S m j)) := by
  have hj : check S m j ∈ (stabilizer S m).stabilizers :=
    binaryCSSParityCheckGenerator_mem_checkSet (zSyndrome S m) (xSyndrome S m) j
  have hc := hE _ (PauliSymplectic.mem_generatedGroup_of_mem_stabilizers (stabilizer S m) hj)
  have hop := toHermitianQubitOperator_commute_of_commutes E (check S m j) hc
  rw [check_hermitian S m j] at hop
  show toHermitianQubitOperator E * toQubitOperator (check S m j) =
    toQubitOperator (check S m j) * toHermitianQubitOperator E
  exact hop

theorem Xbar_commutes_check (j : Sum (ZLabel S m) (XLabel S m)) :
    Commute (Xbar S m) (toQubitOperator (check S m j)) :=
  normalizer_commutes_check S m _ (logicalX_normalizer S m) j

theorem Zbar_commutes_check (j : Sum (ZLabel S m) (XLabel S m)) :
    Commute (Zbar S m) (toQubitOperator (check S m j)) :=
  normalizer_commutes_check S m _ (logicalZ_normalizer S m) j

theorem Xbar_commutes_hamiltonian : Commute (Xbar S m) (hamiltonian S m) := by
  unfold hamiltonian
  apply Commute.neg_right
  exact Commute.sum_right Finset.univ
    (fun j : Sum (ZLabel S m) (XLabel S m) => toQubitOperator (check S m j))
    (Xbar S m) (fun j _ => Xbar_commutes_check S m j)

theorem Zbar_commutes_hamiltonian : Commute (Zbar S m) (hamiltonian S m) := by
  unfold hamiltonian
  apply Commute.neg_right
  exact Commute.sum_right Finset.univ
    (fun j : Sum (ZLabel S m) (XLabel S m) => toQubitOperator (check S m j))
    (Zbar S m) (fun j _ => Zbar_commutes_check S m j)

/-- The labelled code really has a nonzero vector, internally constructed by source validity. -/
theorem exists_nonzero_code : ∃ ψ : Qubit.QubitRegister (Physical S m),
    ψ ∈ (labelledCode S m).carrier ∧ ψ ≠ 0 :=
  StabilizerCode.exists_nonzero_mem_code (sourceValid S m)

/-- Select an actual nonzero code vector from that proved unconditional existence. -/
def codeVector : Qubit.QubitRegister (Physical S m) := Classical.choose (exists_nonzero_code S m)

theorem codeVector_mem : codeVector S m ∈ (labelledCode S m).carrier :=
  (Classical.choose_spec (exists_nonzero_code S m)).1

theorem codeVector_ne_zero : codeVector S m ≠ 0 :=
  (Classical.choose_spec (exists_nonzero_code S m)).2

theorem Xbar_preserves_code (ψ : Qubit.QubitRegister (Physical S m))
    (hψ : ψ ∈ (labelledCode S m).carrier) : Xbar S m ψ ∈ (labelledCode S m).carrier := by
  change hermitianPhaseScalar (logicalX S m) • (toQubitOperator (logicalX S m) ψ) ∈ _
  exact (labelledCode S m).carrier.smul_mem _
    (StabilizerCode.toQubitOperator_mem_code_of_inBinaryNormalizer
      (sourceValid S m) (logicalX_normalizer S m) hψ)

theorem Zbar_preserves_code (ψ : Qubit.QubitRegister (Physical S m))
    (hψ : ψ ∈ (labelledCode S m).carrier) : Zbar S m ψ ∈ (labelledCode S m).carrier := by
  change hermitianPhaseScalar (logicalZ S m) • (toQubitOperator (logicalZ S m) ψ) ∈ _
  exact (labelledCode S m).carrier.smul_mem _
    (StabilizerCode.toQubitOperator_mem_code_of_inBinaryNormalizer
      (sourceValid S m) (logicalZ_normalizer S m) hψ)

theorem Xbar_action_ne_zero (ψ : Qubit.QubitRegister (Physical S m)) (hψ : ψ ≠ 0) : Xbar S m ψ ≠ 0 := by
  intro h
  have hs := congrArg (fun A : Operator (Qubit.QubitRegister (Physical S m)) => A ψ) (Xbar_square S m)
  change Xbar S m (Xbar S m ψ) = ψ at hs
  rw [h, map_zero] at hs
  exact hψ hs.symm

theorem Zbar_action_ne_zero (ψ : Qubit.QubitRegister (Physical S m)) (hψ : ψ ≠ 0) : Zbar S m ψ ≠ 0 := by
  intro h
  have hs := congrArg (fun A : Operator (Qubit.QubitRegister (Physical S m)) => A ψ) (Zbar_square S m)
  change Zbar S m (Zbar S m ψ) = ψ at hs
  rw [h, map_zero] at hs
  exact hψ hs.symm

theorem product_preserves_code (ψ : Qubit.QubitRegister (Physical S m))
    (hψ : ψ ∈ (labelledCode S m).carrier) : (Xbar S m * Zbar S m) ψ ∈ (labelledCode S m).carrier := by
  exact Xbar_preserves_code S m _ (Zbar_preserves_code S m ψ hψ)

theorem product_action_ne_zero (ψ : Qubit.QubitRegister (Physical S m)) (hψ : ψ ≠ 0) :
    (Xbar S m * Zbar S m) ψ ≠ 0 := Xbar_action_ne_zero S m _ (Zbar_action_ne_zero S m ψ hψ)

/-- The operator identity holds pointwise, including every actual code vector. -/
theorem negative_order_action (ψ : Qubit.QubitRegister (Physical S m)) :
    (Xbar S m * Zbar S m) ψ = -((Zbar S m * Xbar S m) ψ) := by
  have h := congrArg (fun A : Operator (Qubit.QubitRegister (Physical S m)) => A ψ) (Xbar_Zbar_anticommute S m)
  simpa only [LinearMap.neg_apply] using h

theorem commutator_action (ψ : Qubit.QubitRegister (Physical S m)) :
    (Xbar S m * Zbar S m - Zbar S m * Xbar S m) ψ = (2 : ℂ) • ((Xbar S m * Zbar S m) ψ) := by
  have horder : (Zbar S m * Xbar S m) ψ = -((Xbar S m * Zbar S m) ψ) := by
    have h := congrArg Neg.neg (negative_order_action S m ψ)
    simpa only [neg_neg] using h.symm
  change (Xbar S m * Zbar S m) ψ - (Zbar S m * Xbar S m) ψ = _
  rw [horder, sub_neg_eq_add, two_smul]

theorem commutator_action_ne_zero (ψ : Qubit.QubitRegister (Physical S m)) (hψ : ψ ≠ 0) :
    (Xbar S m * Zbar S m - Zbar S m * Xbar S m) ψ ≠ 0 := by
  rw [commutator_action]
  exact smul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (product_action_ne_zero S m ψ hψ)

/-- An unconditional actual code-action witness; no codespace witness is assumed. -/
theorem actual_code_action_witness : ∃ ψ : Qubit.QubitRegister (Physical S m),
    ψ ∈ (labelledCode S m).carrier ∧ ψ ≠ 0 ∧
    Xbar S m ψ ∈ (labelledCode S m).carrier ∧ Zbar S m ψ ∈ (labelledCode S m).carrier ∧
    (Xbar S m * Zbar S m) ψ ∈ (labelledCode S m).carrier ∧
    Xbar S m ψ ≠ 0 ∧ Zbar S m ψ ≠ 0 ∧ (Xbar S m * Zbar S m) ψ ≠ 0 ∧
    (Xbar S m * Zbar S m - Zbar S m * Xbar S m) ψ ≠ 0 :=
  ⟨codeVector S m, codeVector_mem S m, codeVector_ne_zero S m,
    Xbar_preserves_code S m _ (codeVector_mem S m), Zbar_preserves_code S m _ (codeVector_mem S m),
    product_preserves_code S m _ (codeVector_mem S m),
    Xbar_action_ne_zero S m _ (codeVector_ne_zero S m), Zbar_action_ne_zero S m _ (codeVector_ne_zero S m),
    product_action_ne_zero S m _ (codeVector_ne_zero S m),
    commutator_action_ne_zero S m _ (codeVector_ne_zero S m)⟩

/-- All source-even prefixes, including k=0, use this same selected pair. -/
theorem even_pair (k : Nat) :
    (stabilizer S (2*k)).InBinaryNormalizer (logicalX S (2*k)) ∧
    (stabilizer S (2*k)).InBinaryNormalizer (logicalZ S (2*k)) ∧
    ¬ (stabilizer S (2*k)).InGeneratedGroupUpToSign (logicalX S (2*k)) ∧
    ¬ (stabilizer S (2*k)).InGeneratedGroupUpToSign (logicalZ S (2*k)) ∧
    Xbar S (2*k) * Zbar S (2*k) = -(Zbar S (2*k) * Xbar S (2*k)) :=
  ⟨logicalX_normalizer S (2*k), logicalZ_normalizer S (2*k), logicalX_not_generated S (2*k),
    logicalZ_not_generated S (2*k), Xbar_Zbar_anticommute S (2*k)⟩

/-- Exact existing indexed carrier; no pair is reselected at the indexed level. -/
def indexedLogicalX (depth : Nat) (i : MultiscaleDecoder.LevelIndex depth) :
    Binary (BDL26IndexedDecoder.FamilyQ S depth i) := logicalX S i.val

def indexedLogicalZ (depth : Nat) (i : MultiscaleDecoder.LevelIndex depth) :
    Binary (BDL26IndexedDecoder.FamilyQ S depth i) := logicalZ S i.val

theorem indexed_generator_word (depth : Nat) (i : MultiscaleDecoder.LevelIndex depth) :
    (indexedLogicalX S depth i).vector.xPart = (BDL26FiniteCohomology.generator S i.val (1 : ZMod 2)).val := rfl

theorem indexed_pair (depth : Nat) (i : MultiscaleDecoder.LevelIndex depth) :
    (stabilizer S i.val).InBinaryNormalizer (indexedLogicalX S depth i) ∧
    (stabilizer S i.val).InBinaryNormalizer (indexedLogicalZ S depth i) ∧
    ¬ (stabilizer S i.val).InGeneratedGroupUpToSign (indexedLogicalX S depth i) ∧
    ¬ (stabilizer S i.val).InGeneratedGroupUpToSign (indexedLogicalZ S depth i) ∧
    toHermitianQubitOperator (indexedLogicalX S depth i) * toHermitianQubitOperator (indexedLogicalZ S depth i) =
      -(toHermitianQubitOperator (indexedLogicalZ S depth i) * toHermitianQubitOperator (indexedLogicalX S depth i)) :=
  ⟨logicalX_normalizer S i.val, logicalZ_normalizer S i.val,
    logicalX_not_generated S i.val, logicalZ_not_generated S i.val, Xbar_Zbar_anticommute S i.val⟩

theorem indexed_code_action_witness (depth : Nat) (i : MultiscaleDecoder.LevelIndex depth) :
    ∃ ψ : Qubit.QubitRegister (BDL26IndexedDecoder.FamilyQ S depth i),
      ψ ∈ (indexedLabelledCode S depth i).carrier ∧ ψ ≠ 0 ∧
      (toHermitianQubitOperator (indexedLogicalX S depth i) *
        toHermitianQubitOperator (indexedLogicalZ S depth i)) ψ ≠ 0 ∧
      (toHermitianQubitOperator (indexedLogicalX S depth i) * toHermitianQubitOperator (indexedLogicalZ S depth i) -
        toHermitianQubitOperator (indexedLogicalZ S depth i) * toHermitianQubitOperator (indexedLogicalX S depth i)) ψ ≠ 0 :=
  ⟨codeVector S i.val, codeVector_mem S i.val, codeVector_ne_zero S i.val,
    product_action_ne_zero S i.val _ (codeVector_ne_zero S i.val),
    commutator_action_ne_zero S i.val _ (codeVector_ne_zero S i.val)⟩

end QEC.Coding.BDL26BareLogicalPair
end
