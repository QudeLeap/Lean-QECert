import QEC.Coding.CSS.Syndrome
import QEC.Coding.Stabilizer.JointMeasurement
import QEC.Coding.Stabilizer.BasisAction
import QEC.Semantics.Core.OperatorTraceNorm

/-! # Literal CSS joint eigenspaces and Pauli transport

The check family may have dependent, repeated, identity or no rows. Energy
normalization is restricted to pure CSS rows; the transport lemmas themselves
use the existing Hermitian Pauli measurement representation.
-/
noncomputable section
namespace QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics
open scoped BigOperators
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def transportSyndrome
    (checks : κ → Binary ι) (hcomm : ∀ a b, Commutes (checks a) (checks b))
    (error : Binary ι) (syndrome : JointSyndrome κ) :
    JointSyndrome κ := by
  classical
  exact fun check =>
    if Commutes error (checks check) then
      syndrome check
    else
      (syndrome check).opposite

/-- A signed Hermitian Pauli anticommutes concretely when its binary words do. -/
theorem toHermitianQubitOperator_anticommute_of_not_commutes
    (P Q : Binary ι) (h : ¬ Commutes P Q) :
    toHermitianQubitOperator P * toHermitianQubitOperator Q =
      -(toHermitianQubitOperator Q * toHermitianQubitOperator P) := by
  unfold toHermitianQubitOperator
  rw [smul_mul_smul_comm, smul_mul_smul_comm]
  rw [toQubitOperator_anticommute_of_not_commutes P Q h]
  module

/-- One Pauli transports one selected spectral factor to the flipped sector. -/
theorem pauli_mul_jointStabilizerFactor
    (checks : κ → Binary ι) (hcomm : ∀ a b, Commutes (checks a) (checks b))
    (error : Binary ι) (syndrome : JointSyndrome κ) (check : κ) :
    toHermitianQubitOperator error *
        jointStabilizerFactor checks syndrome check =
      jointStabilizerFactor checks
          (transportSyndrome checks hcomm error syndrome) check *
        toHermitianQubitOperator error := by
  classical
  by_cases hcomm : Commutes error (checks check)
  · have hop := toHermitianQubitOperator_commute_of_commutes
      error (checks check) hcomm
    simp only [jointStabilizerFactor, stabilizerProjector, transportSyndrome,
      if_pos hcomm, mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
      mul_one, one_mul]
    rw [hop]
  · have hop := toHermitianQubitOperator_anticommute_of_not_commutes
      error (checks check) hcomm
    cases houtcome : syndrome check <;>
      simp only [jointStabilizerFactor, stabilizerProjector, transportSyndrome,
        if_neg hcomm, houtcome, StabilizerOutcome.opposite,
        StabilizerOutcome.sign, mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
        mul_one, one_mul] <;>
      rw [hop] <;>
      module

/-- Pairwise witness for a restricted product of syndrome factors. -/
theorem syndromeFactor_pairwise
    (checks : κ → Binary ι) (hcomm : ∀ a b, Commutes (checks a) (checks b))
    (syndrome : JointSyndrome κ) (selected : Finset κ) :
    (selected : Set κ).Pairwise
      (Function.onFun Commute (jointStabilizerFactor checks syndrome)) := by
  intro left _ right _ _
  exact jointStabilizerFactor_commute checks hcomm
    left right syndrome syndrome

/-- Pauli transport through any restricted product of syndrome factors. -/
theorem pauli_mul_syndromeProjectorOn
    (checks : κ → Binary ι) (hcomm : ∀ a b, Commutes (checks a) (checks b))
    (error : Binary ι) (syndrome : JointSyndrome κ)
    (selected : Finset κ) :
    toHermitianQubitOperator error *
        selected.noncommProd (jointStabilizerFactor checks syndrome)
          (syndromeFactor_pairwise checks hcomm syndrome selected) =
      selected.noncommProd
          (jointStabilizerFactor checks
            (transportSyndrome checks hcomm error syndrome))
          (syndromeFactor_pairwise checks hcomm
            (transportSyndrome checks hcomm error syndrome) selected) *
        toHermitianQubitOperator error := by
  classical
  induction selected using Finset.induction_on with
  | empty => simp [Finset.noncommProd_empty]
  | @insert check selected hnotmem induction =>
      rw [Finset.noncommProd_insert_of_notMem selected check
        (jointStabilizerFactor checks syndrome)
        (syndromeFactor_pairwise checks hcomm syndrome (insert check selected)) hnotmem]
      rw [Finset.noncommProd_insert_of_notMem selected check
        (jointStabilizerFactor checks
          (transportSyndrome checks hcomm error syndrome))
        (syndromeFactor_pairwise checks hcomm
          (transportSyndrome checks hcomm error syndrome) (insert check selected)) hnotmem]
      calc
        toHermitianQubitOperator error *
            (jointStabilizerFactor checks syndrome check *
              selected.noncommProd (jointStabilizerFactor checks syndrome) _) =
            (toHermitianQubitOperator error *
                jointStabilizerFactor checks syndrome check) *
              selected.noncommProd (jointStabilizerFactor checks syndrome) _ := by
                rw [mul_assoc]
        _ = (jointStabilizerFactor checks
              (transportSyndrome checks hcomm error syndrome) check *
                toHermitianQubitOperator error) *
              selected.noncommProd (jointStabilizerFactor checks syndrome) _ := by
                rw [pauli_mul_jointStabilizerFactor checks hcomm error syndrome check]
        _ = jointStabilizerFactor checks
              (transportSyndrome checks hcomm error syndrome) check *
            (toHermitianQubitOperator error *
              selected.noncommProd (jointStabilizerFactor checks syndrome) _) := by
                rw [mul_assoc]
        _ = jointStabilizerFactor checks
              (transportSyndrome checks hcomm error syndrome) check *
            (selected.noncommProd
                (jointStabilizerFactor checks
                  (transportSyndrome checks hcomm error syndrome)) _ *
              toHermitianQubitOperator error) := by
                rw [induction]
        _ = (jointStabilizerFactor checks
              (transportSyndrome checks hcomm error syndrome) check *
                selected.noncommProd
                  (jointStabilizerFactor checks
                    (transportSyndrome checks hcomm error syndrome)) _) *
              toHermitianQubitOperator error := by
                rw [mul_assoc]

/-- A Pauli error transports the full joint syndrome projector. -/
theorem pauli_mul_syndromeProjector
    (checks : κ → Binary ι) (hcomm : ∀ a b, Commutes (checks a) (checks b))
    (error : Binary ι) (syndrome : JointSyndrome κ) :
    toHermitianQubitOperator error * jointStabilizerProjector checks hcomm syndrome =
      jointStabilizerProjector checks hcomm (transportSyndrome checks hcomm error syndrome) *
        toHermitianQubitOperator error := by
  simpa [jointStabilizerProjector] using
    pauli_mul_syndromeProjectorOn checks hcomm error syndrome Finset.univ


/-- Binary syndrome bits encode the existing signed measurement outcomes. -/
def bitOutcome : ZMod 2 ≃ StabilizerOutcome where
  toFun b := if b = 0 then .positive else .negative
  invFun o := match o with | .positive => 0 | .negative => 1
  left_inv b := by
    change (match (if b = 0 then StabilizerOutcome.positive else StabilizerOutcome.negative) with
      | .positive => (0 : ZMod 2) | .negative => 1) = b
    split_ifs with h
    · exact h.symm
    · exact (zmod_two_eq_one_of_ne_zero h).symm
  right_inv o := by cases o <;> simp

@[simp] theorem bitOutcome_zero : bitOutcome 0 = .positive := by simp [bitOutcome]
@[simp] theorem bitOutcome_one : bitOutcome 1 = .negative := by simp [bitOutcome]

/-- Outcome conversion is bijective even for an empty row family. -/
def syndromeOutcome (κ : Type) : (κ → ZMod 2) ≃ JointSyndrome κ :=
  Equiv.piCongrRight (fun _ => bitOutcome)

@[simp] theorem syndromeOutcome_apply (s : κ → ZMod 2) (j : κ) :
    syndromeOutcome κ s j = bitOutcome (s j) := rfl

@[simp] theorem bitOutcome_sign (b : ZMod 2) :
    (bitOutcome b).sign = binaryPhaseScalar b := by
  by_cases h : b = 0 <;>
    simp only [bitOutcome, Equiv.coe_fn_mk, h, if_true, if_false,
      StabilizerOutcome.sign, binaryPhaseScalar]

/-- The Hermitian correction is trivial on an actual pure X check. -/
@[simp] theorem hermitian_cssX (x : Word (ZMod 2) ι) :
    toHermitianQubitOperator (cssXCheck x) = toQubitOperator (cssXCheck x) := by
  simp [toHermitianQubitOperator, hermitianPhaseScalar, binaryOverlapCount,
    binaryOverlapSupport, cssXCheck, xSupport, zSupport, binarySupport]

/-- The Hermitian correction is trivial on an actual pure Z check. -/
@[simp] theorem hermitian_cssZ (z : Word (ZMod 2) ι) :
    toHermitianQubitOperator (cssZCheck z) = toQubitOperator (cssZCheck z) := by
  simp [toHermitianQubitOperator, hermitianPhaseScalar, binaryOverlapCount,
    binaryOverlapSupport, cssZCheck, xSupport, zSupport, binarySupport]

variable {κP κQ : Type} [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)

include horth in
/-- The literal parity-check row family commutes by row orthogonality. -/
theorem checks_commute (a b : Sum κP κQ) :
    Commutes (binaryCSSParityCheckGenerators P Q a) (binaryCSSParityCheckGenerators P Q b) := by
  exact (binaryCSSStabilizerCodeOfParityChecks P Q horth).isotropic _
    (binaryCSSParityCheckGenerator_mem_checkSet P Q a) _
    (binaryCSSParityCheckGenerator_mem_checkSet P Q b)

/-- This phase equality is deliberately restricted to pure CSS rows. -/
@[simp] theorem hermitian_row (a : Sum κP κQ) :
    toHermitianQubitOperator (binaryCSSParityCheckGenerators P Q a) =
      toQubitOperator (binaryCSSParityCheckGenerators P Q a) := by
  cases a <;> simp [binaryCSSParityCheckGenerators]

/-- Actual common-eigenspace projector for the complete visible row syndrome. -/
def projector (s : Word (ZMod 2) (Sum κP κQ)) : Operator (Qubit.QubitRegister ι) :=
  jointStabilizerProjector (binaryCSSParityCheckGenerators P Q) (checks_commute P Q horth)
    (syndromeOutcome _ s)

@[simp] theorem projector_adjoint (s : Word (ZMod 2) (Sum κP κQ)) :
    LinearMap.adjoint (projector P Q horth s) = projector P Q horth s :=
  jointStabilizerProjector_adjoint _ _ _

@[simp] theorem projector_square (s : Word (ZMod 2) (Sum κP κQ)) :
    projector P Q horth s * projector P Q horth s = projector P Q horth s :=
  jointStabilizerProjector_idempotent _ _ _

theorem projector_positive (s : Word (ZMod 2) (Sum κP κQ)) :
    (projector P Q horth s).IsPositive := by
  have h := LinearMap.isPositive_adjoint_comp_self (projector P Q horth s)
  change (LinearMap.adjoint (projector P Q horth s) * projector P Q horth s).IsPositive at h
  simpa only [projector_adjoint, projector_square] using h

theorem projector_mul_of_ne (s t : Word (ZMod 2) (Sum κP κQ)) (hst : s ≠ t) :
    projector P Q horth s * projector P Q horth t = 0 := by
  apply jointStabilizerProjector_mul_of_ne
  exact fun h => hst ((syndromeOutcome _).injective h)

theorem sum_projector : (∑ s, projector P Q horth s) = 1 := by
  exact ((syndromeOutcome (Sum κP κQ)).sum_comp
    (jointStabilizerProjector (binaryCSSParityCheckGenerators P Q)
      (checks_commute P Q horth))).trans
    (sum_jointStabilizerProjector_eq_one _ _)

theorem row_mul_projector (s : Word (ZMod 2) (Sum κP κQ)) (j : Sum κP κQ) :
    toQubitOperator (binaryCSSParityCheckGenerators P Q j) * projector P Q horth s =
      binaryPhaseScalar (s j) • projector P Q horth s := by
  simpa only [projector, hermitian_row, syndromeOutcome_apply, bitOutcome_sign] using
    jointStabilizerProjector_eigen (binaryCSSParityCheckGenerators P Q)
      (checks_commute P Q horth) (syndromeOutcome _ s) j

theorem projector_fixed_iff (s : Word (ZMod 2) (Sum κP κQ))
    (x : Qubit.QubitRegister ι) :
    projector P Q horth s x = x ↔ ∀ j,
      toQubitOperator (binaryCSSParityCheckGenerators P Q j) x = binaryPhaseScalar (s j) • x := by
  simpa only [projector, hermitian_row, syndromeOutcome_apply, bitOutcome_sign] using
    jointStabilizerProjector_fixed_iff (binaryCSSParityCheckGenerators P Q)
      (checks_commute P Q horth) (syndromeOutcome _ s) x

/-- The projector range is the actual common eigenspace, not supplied metadata. -/
def sector (s : Word (ZMod 2) (Sum κP κQ)) : Submodule ℂ (Qubit.QubitRegister ι) :=
  LinearMap.range (projector P Q horth s)

theorem projector_isProj (s : Word (ZMod 2) (Sum κP κQ)) :
    LinearMap.IsProj (sector P Q horth s) (projector P Q horth s) := by
  constructor
  · intro x; exact ⟨x, rfl⟩
  · rintro x ⟨y, rfl⟩
    exact congrArg (fun A : Operator (Qubit.QubitRegister ι) => A y)
      (projector_square P Q horth s)

theorem trace_projector (s : Word (ZMod 2) (Sum κP κQ)) :
    LinearMap.trace ℂ (Qubit.QubitRegister ι) (projector P Q horth s) =
      (Module.finrank ℂ (sector P Q horth s) : ℂ) :=
  (projector_isProj P Q horth s).trace

theorem trace_projector_zero_iff (s : Word (ZMod 2) (Sum κP κQ)) :
    LinearMap.trace ℂ (Qubit.QubitRegister ι) (projector P Q horth s) = 0 ↔
      projector P Q horth s = 0 := by
  have h := trace_adjoint_mul_self_eq_zero_iff (projector P Q horth s)
  simpa only [projector_adjoint, projector_square] using h

/-- All-plus transport is precisely the existing binary commutation syndrome. -/
theorem transport_zero (E : Binary ι) :
    transportSyndrome (binaryCSSParityCheckGenerators P Q) (checks_commute P Q horth)
      E (syndromeOutcome _ 0) =
      syndromeOutcome _ (stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E) := by
  funext j
  simp [transportSyndrome, syndromeOutcome_apply, bitOutcome, stabilizerSyndrome,
    stabilizerSyndromeBit, Commutes, StabilizerOutcome.opposite]

/-- Real Pauli conjugation constructs every error-reachable sector. -/
theorem projector_error_conjugate (E : Binary ι) :
    projector P Q horth (stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E) =
      toHermitianQubitOperator E * projector P Q horth 0 * toHermitianQubitOperator E := by
  have h := pauli_mul_syndromeProjector (binaryCSSParityCheckGenerators P Q)
    (checks_commute P Q horth) E (syndromeOutcome _ 0)
  rw [transport_zero P Q horth E] at h
  have hm := congrArg (fun A : Operator (Qubit.QubitRegister ι) =>
    A * toHermitianQubitOperator E) h
  simpa only [mul_assoc, toHermitianQubitOperator_square, mul_one, projector] using hm.symm

/-- The trace, hence the rank, is unchanged by actual Pauli sector transport. -/
theorem trace_projector_error (E : Binary ι) :
    LinearMap.trace ℂ (Qubit.QubitRegister ι)
      (projector P Q horth (stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E)) =
      LinearMap.trace ℂ (Qubit.QubitRegister ι) (projector P Q horth 0) := by
  rw [projector_error_conjugate]
  rw [LinearMap.trace_mul_comm]
  simp only [← mul_assoc, toHermitianQubitOperator_square, one_mul]

/-- Actual pairs of row syndromes; no surjectivity is required. -/
abbrev Realizable := (LinearMap.range P) × (LinearMap.range Q)

/-- Rejoin the two oriented row words as one complete visible syndrome. -/
def joinSyndrome (u : Word (ZMod 2) κP) (v : Word (ZMod 2) κQ) :
    Word (ZMod 2) (Sum κP κQ) := Sum.elim u v

theorem trace_projector_realizable (u : LinearMap.range P) (v : LinearMap.range Q) :
    LinearMap.trace ℂ (Qubit.QubitRegister ι) (projector P Q horth (joinSyndrome u.val v.val)) =
      LinearMap.trace ℂ (Qubit.QubitRegister ι) (projector P Q horth 0) := by
  rcases u.property with ⟨x, hx⟩
  rcases v.property with ⟨z, hz⟩
  let E : Binary ι := { phase := 0, vector := { xPart := x, zPart := z } }
  have hs := binaryCSSSyndrome_eq_classicalSyndromes P Q horth E
  change stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E = Sum.elim (P x) (Q z) at hs
  rw [hx, hz] at hs
  simpa only [hs, joinSyndrome] using trace_projector_error P Q horth E

/-- A fixed vector for the rows is fixed by every generated Pauli. -/
theorem fixed_generated_of_rows (x : Qubit.QubitRegister ι)
    (hx : ∀ j, toQubitOperator (binaryCSSParityCheckGenerators P Q j) x = x)
    (G : Binary ι) (hG : GeneratedStabilizer (binaryCSSParityCheckGenerators P Q) G) :
    toQubitOperator G x = x := by
  induction hG with
  | one => rw [toQubitOperator_one]; rfl
  | generator j => exact hx j
  | @mul A B hA hB ihA ihB =>
      rw [toQubitOperator_binaryMul]
      change toQubitOperator A (toQubitOperator B x) = x
      rw [ihB, ihA]
  | @dagger A hA ih =>
      calc
        toQubitOperator (binaryDagger A) x =
            toQubitOperator (binaryDagger A) (toQubitOperator A x) := by rw [ih]
        _ = x := by
          change (toQubitOperator (binaryDagger A) * toQubitOperator A) x = x
          rw [← toQubitOperator_binaryMul, binaryMul_binaryDagger_left, toQubitOperator_one]
          rfl

/-- The zero sector is the actual semantic CSS code carrier. -/
theorem sector_zero_eq_code : sector P Q horth 0 =
    (binaryCSSQuantumCodeOfDualLe (parityCheckRowCode Q) (parityCheckRowCode P)
      ((parityCheckRows_orthogonal_iff_rowCode_le_dual P Q).mp horth)).carrier := by
  ext x
  rw [mem_binaryCSSQuantumCodeOfDualLe_carrier]
  constructor
  · rintro ⟨y, rfl⟩ G hG
    apply fixed_generated_of_rows P Q
    · intro j
      have h := congrArg (fun A : Operator (Qubit.QubitRegister ι) => A y)
        (row_mul_projector P Q horth 0 j)
      simpa [binaryPhaseScalar] using h
    · exact binaryCSSParityCheckGenerators_generate_check P Q hG
  · intro hx
    have hf : projector P Q horth 0 x = x := by
      apply (projector_fixed_iff P Q horth 0 x).mpr
      intro j
      simpa [binaryPhaseScalar] using hx _ (binaryCSSParityCheckGenerator_mem_checkSet P Q j)
    exact ⟨x, hf⟩

end QEC.Coding.CSSGibbs
