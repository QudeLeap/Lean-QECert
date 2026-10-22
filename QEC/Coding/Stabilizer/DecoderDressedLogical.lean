import QEC.Coding.Stabilizer.JointMeasurement
import QEC.Coding.Stabilizer.LocalHamiltonian

/-!
# Decoder-dressed logical observables

This module realizes the stabilizer specialization of the error-corrected
logical observables in CLBT10, Section 4.  A deterministic Pauli correction is
chosen for every joint syndrome.  Its commutation sign with a bare logical
Pauli weights the corresponding joint syndrome projector, producing the
decoder phase operator and hence the dressed logical observable.

The construction deliberately makes no claim that every syndrome is good or
correctable.  Protected sectors, Gibbs tails, and lifetime estimates belong to
later M11 work packages.
-/

noncomputable section

namespace QEC
namespace Coding
namespace StabilizerCode

open PauliSymplectic
open Semantics
open scoped BigOperators

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]

/-- The finite joint syndrome used by a selected stabilizer Hamiltonian. -/
abbrev DecoderSyndrome (κ : Type v) := JointSyndrome κ

namespace LocalStabilizerHamiltonian

/-- The joint spectral projector associated with one visible syndrome. -/
def syndromeProjector
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (syndrome : DecoderSyndrome κ) :
    Operator (Qubit.QubitRegister ι) :=
  jointStabilizerProjector H.generators H.generators_commute syndrome

@[simp]
theorem syndromeProjector_adjoint
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (syndrome : DecoderSyndrome κ) :
    LinearMap.adjoint (H.syndromeProjector syndrome) =
      H.syndromeProjector syndrome :=
  jointStabilizerProjector_adjoint H.generators H.generators_commute syndrome

@[simp]
theorem syndromeProjector_mul_self
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (syndrome : DecoderSyndrome κ) :
    H.syndromeProjector syndrome * H.syndromeProjector syndrome =
      H.syndromeProjector syndrome :=
  jointStabilizerProjector_idempotent H.generators H.generators_commute syndrome

/-- Distinct syndrome sectors are orthogonal. -/
theorem syndromeProjector_mul_of_ne
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (left right : DecoderSyndrome κ) (hne : left ≠ right) :
    H.syndromeProjector left * H.syndromeProjector right = 0 :=
  jointStabilizerProjector_mul_of_ne
    H.generators H.generators_commute left right hne

/-- The full finite syndrome resolution sums to the identity. -/
theorem sum_syndromeProjector_eq_one
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) :
    ∑ syndrome : DecoderSyndrome κ, H.syndromeProjector syndrome = 1 :=
  sum_jointStabilizerProjector_eq_one H.generators H.generators_commute

/-- Multiplication law for the orthogonal syndrome resolution. -/
theorem syndromeProjector_mul
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (left right : DecoderSyndrome κ) :
    H.syndromeProjector left * H.syndromeProjector right =
      if left = right then H.syndromeProjector left else 0 := by
  classical
  by_cases h : left = right
  · subst right
    simp
  · simp [h, H.syndromeProjector_mul_of_ne left right h]

/--
The syndrome reached after applying a Pauli error: commuting checks retain
their outcome and anticommuting checks flip it.
-/
noncomputable def transportSyndrome
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (error : Binary ι) (syndrome : DecoderSyndrome κ) :
    DecoderSyndrome κ := by
  classical
  exact fun check =>
    if Commutes error (H.generators check) then
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
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (error : Binary ι) (syndrome : DecoderSyndrome κ) (check : κ) :
    toHermitianQubitOperator error *
        jointStabilizerFactor H.generators syndrome check =
      jointStabilizerFactor H.generators
          (H.transportSyndrome error syndrome) check *
        toHermitianQubitOperator error := by
  classical
  by_cases hcomm : Commutes error (H.generators check)
  · have hop := toHermitianQubitOperator_commute_of_commutes
      error (H.generators check) hcomm
    simp only [jointStabilizerFactor, stabilizerProjector, transportSyndrome,
      if_pos hcomm, mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
      mul_one, one_mul]
    rw [hop]
  · have hop := toHermitianQubitOperator_anticommute_of_not_commutes
      error (H.generators check) hcomm
    cases houtcome : syndrome check <;>
      simp only [jointStabilizerFactor, stabilizerProjector, transportSyndrome,
        if_neg hcomm, houtcome, StabilizerOutcome.opposite,
        StabilizerOutcome.sign, mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
        mul_one, one_mul] <;>
      rw [hop] <;>
      module

/-- Pairwise witness for a restricted product of syndrome factors. -/
theorem syndromeFactor_pairwise
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (syndrome : DecoderSyndrome κ) (selected : Finset κ) :
    (selected : Set κ).Pairwise
      (Function.onFun Commute (jointStabilizerFactor H.generators syndrome)) := by
  intro left _ right _ _
  exact jointStabilizerFactor_commute H.generators H.generators_commute
    left right syndrome syndrome

/-- Pauli transport through any restricted product of syndrome factors. -/
theorem pauli_mul_syndromeProjectorOn
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (error : Binary ι) (syndrome : DecoderSyndrome κ)
    (selected : Finset κ) :
    toHermitianQubitOperator error *
        selected.noncommProd (jointStabilizerFactor H.generators syndrome)
          (H.syndromeFactor_pairwise syndrome selected) =
      selected.noncommProd
          (jointStabilizerFactor H.generators
            (H.transportSyndrome error syndrome))
          (H.syndromeFactor_pairwise
            (H.transportSyndrome error syndrome) selected) *
        toHermitianQubitOperator error := by
  classical
  induction selected using Finset.induction_on with
  | empty => simp [Finset.noncommProd_empty]
  | @insert check selected hnotmem induction =>
      rw [Finset.noncommProd_insert_of_notMem selected check
        (jointStabilizerFactor H.generators syndrome)
        (H.syndromeFactor_pairwise syndrome (insert check selected)) hnotmem]
      rw [Finset.noncommProd_insert_of_notMem selected check
        (jointStabilizerFactor H.generators
          (H.transportSyndrome error syndrome))
        (H.syndromeFactor_pairwise
          (H.transportSyndrome error syndrome) (insert check selected)) hnotmem]
      calc
        toHermitianQubitOperator error *
            (jointStabilizerFactor H.generators syndrome check *
              selected.noncommProd (jointStabilizerFactor H.generators syndrome) _) =
            (toHermitianQubitOperator error *
                jointStabilizerFactor H.generators syndrome check) *
              selected.noncommProd (jointStabilizerFactor H.generators syndrome) _ := by
                rw [mul_assoc]
        _ = (jointStabilizerFactor H.generators
              (H.transportSyndrome error syndrome) check *
                toHermitianQubitOperator error) *
              selected.noncommProd (jointStabilizerFactor H.generators syndrome) _ := by
                rw [H.pauli_mul_jointStabilizerFactor error syndrome check]
        _ = jointStabilizerFactor H.generators
              (H.transportSyndrome error syndrome) check *
            (toHermitianQubitOperator error *
              selected.noncommProd (jointStabilizerFactor H.generators syndrome) _) := by
                rw [mul_assoc]
        _ = jointStabilizerFactor H.generators
              (H.transportSyndrome error syndrome) check *
            (selected.noncommProd
                (jointStabilizerFactor H.generators
                  (H.transportSyndrome error syndrome)) _ *
              toHermitianQubitOperator error) := by
                rw [induction]
        _ = (jointStabilizerFactor H.generators
              (H.transportSyndrome error syndrome) check *
                selected.noncommProd
                  (jointStabilizerFactor H.generators
                    (H.transportSyndrome error syndrome)) _) *
              toHermitianQubitOperator error := by
                rw [mul_assoc]

/-- A Pauli error transports the full joint syndrome projector. -/
theorem pauli_mul_syndromeProjector
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (error : Binary ι) (syndrome : DecoderSyndrome κ) :
    toHermitianQubitOperator error * H.syndromeProjector syndrome =
      H.syndromeProjector (H.transportSyndrome error syndrome) *
        toHermitianQubitOperator error := by
  simpa [syndromeProjector, jointStabilizerProjector] using
    H.pauli_mul_syndromeProjectorOn error syndrome Finset.univ

/-- A normalizer Pauli leaves every selected joint syndrome unchanged. -/
theorem transportSyndrome_eq_self_of_normalizer
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    {logical : Binary ι} (hlogical : H.code.1.InBinaryNormalizer logical)
    (syndrome : DecoderSyndrome κ) :
    H.transportSyndrome logical syndrome = syndrome := by
  funext check
  simp [transportSyndrome,
    hlogical (H.generators check) (H.generator_mem_generatedGroup check)]

/-- Every normalizer Pauli commutes with every joint syndrome projector. -/
theorem normalizer_commute_syndromeProjector
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    {logical : Binary ι} (hlogical : H.code.1.InBinaryNormalizer logical)
    (syndrome : DecoderSyndrome κ) :
    Commute (toHermitianQubitOperator logical) (H.syndromeProjector syndrome) := by
  change _ * _ = _ * _
  simpa only [H.transportSyndrome_eq_self_of_normalizer hlogical syndrome] using
    H.pauli_mul_syndromeProjector logical syndrome

end LocalStabilizerHamiltonian

/--
Raw decoder data: one deterministic Pauli correction for each syndrome and a
bare anticommuting logical Pauli pair in the existing stabilizer normalizer.
No correctability or protected-sector premise is stored here.
-/
structure DecoderDressedLogical
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) where
  correction : DecoderSyndrome κ → Binary ι
  logicalX : Binary ι
  logicalZ : Binary ι
  logicalX_normalizer : H.code.1.InBinaryNormalizer logicalX
  logicalZ_normalizer : H.code.1.InBinaryNormalizer logicalZ
  logicalX_not_commutes_logicalZ : ¬ Commutes logicalX logicalZ

namespace DecoderDressedLogical

variable {H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)}

/-- The CLBT sign selected by correction conjugation of a bare logical Pauli. -/
noncomputable def phase (D : DecoderDressedLogical H)
    (logical : Binary ι) (syndrome : DecoderSyndrome κ) : Complex :=
  by
    classical
    exact if Commutes (D.correction syndrome) logical then 1 else -1

@[simp]
theorem phase_mul_self (D : DecoderDressedLogical H)
    (logical : Binary ι) (syndrome : DecoderSyndrome κ) :
    D.phase logical syndrome * D.phase logical syndrome = 1 := by
  classical
  by_cases h : Commutes (D.correction syndrome) logical <;>
    simp [phase, h]

@[simp]
theorem star_phase (D : DecoderDressedLogical H)
    (logical : Binary ι) (syndrome : DecoderSyndrome κ) :
    star (D.phase logical syndrome) = D.phase logical syndrome := by
  classical
  by_cases h : Commutes (D.correction syndrome) logical <;>
    simp [phase, h]

/-- The phase is exactly the source conjugation coefficient. -/
theorem correction_conjugates_logical
    (D : DecoderDressedLogical H) (logical : Binary ι)
    (syndrome : DecoderSyndrome κ) :
    LinearMap.adjoint (toHermitianQubitOperator (D.correction syndrome)) *
          toHermitianQubitOperator logical *
        toHermitianQubitOperator (D.correction syndrome) =
      D.phase logical syndrome • toHermitianQubitOperator logical := by
  classical
  rw [adjoint_toHermitianQubitOperator_eq_self]
  by_cases hcomm : Commutes (D.correction syndrome) logical
  · have hop := toHermitianQubitOperator_commute_of_commutes
      (D.correction syndrome) logical hcomm
    simp only [phase, if_pos hcomm]
    calc
      toHermitianQubitOperator (D.correction syndrome) *
            toHermitianQubitOperator logical *
          toHermitianQubitOperator (D.correction syndrome) =
        toHermitianQubitOperator logical *
          (toHermitianQubitOperator (D.correction syndrome) *
            toHermitianQubitOperator (D.correction syndrome)) := by
              rw [hop, mul_assoc]
      _ = toHermitianQubitOperator logical := by
            rw [toHermitianQubitOperator_square, mul_one]
      _ = (1 : Complex) • toHermitianQubitOperator logical := by simp
  · have hop := LocalStabilizerHamiltonian.toHermitianQubitOperator_anticommute_of_not_commutes
      (D.correction syndrome) logical hcomm
    simp only [phase, if_neg hcomm]
    calc
      toHermitianQubitOperator (D.correction syndrome) *
            toHermitianQubitOperator logical *
          toHermitianQubitOperator (D.correction syndrome) =
        -(toHermitianQubitOperator logical *
            toHermitianQubitOperator (D.correction syndrome)) *
          toHermitianQubitOperator (D.correction syndrome) := by rw [hop]
      _ = -(toHermitianQubitOperator logical *
          (toHermitianQubitOperator (D.correction syndrome) *
            toHermitianQubitOperator (D.correction syndrome))) := by
              rw [neg_mul, mul_assoc]
      _ = -toHermitianQubitOperator logical := by
            rw [toHermitianQubitOperator_square, mul_one]
      _ = (-1 : Complex) • toHermitianQubitOperator logical := by simp

/-- The diagonal CLBT decoder phase operator `D_L = ∑_s λ_L(s) P_s`. -/
def phaseOperator (D : DecoderDressedLogical H) (logical : Binary ι) :
    Operator (Qubit.QubitRegister ι) :=
  ∑ syndrome : DecoderSyndrome κ,
    D.phase logical syndrome • H.syndromeProjector syndrome

/-- The literal CLBT error-correcting transformation on an observable. -/
def errorCorrectedObservable (D : DecoderDressedLogical H)
    (observable : Operator (Qubit.QubitRegister ι)) :
    Operator (Qubit.QubitRegister ι) :=
  ∑ syndrome : DecoderSyndrome κ,
    H.syndromeProjector syndrome *
      LinearMap.adjoint (toHermitianQubitOperator (D.correction syndrome)) *
      observable *
      toHermitianQubitOperator (D.correction syndrome) *
      H.syndromeProjector syndrome

/-- Multiplication of decoder phase operators is pointwise on syndrome sectors. -/
theorem phaseOperator_mul
    (D : DecoderDressedLogical H) (left right : Binary ι) :
    D.phaseOperator left * D.phaseOperator right =
      ∑ syndrome : DecoderSyndrome κ,
        (D.phase left syndrome * D.phase right syndrome) •
          H.syndromeProjector syndrome := by
  classical
  rw [phaseOperator, phaseOperator, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro syndrome _
  rw [Finset.sum_eq_single syndrome]
  · rw [smul_mul_smul_comm, H.syndromeProjector_mul_self]
  · intro other _ hne
    rw [smul_mul_smul_comm,
      H.syndromeProjector_mul_of_ne syndrome other hne.symm]
    simp
  · simp

/-- Every decoder phase operator squares to the identity. -/
@[simp]
theorem phaseOperator_square
    (D : DecoderDressedLogical H) (logical : Binary ι) :
    D.phaseOperator logical * D.phaseOperator logical = 1 := by
  rw [D.phaseOperator_mul logical logical]
  simpa only [D.phase_mul_self, one_smul] using H.sum_syndromeProjector_eq_one

/-- Decoder phase operators are self-adjoint. -/
@[simp]
theorem phaseOperator_adjoint
    (D : DecoderDressedLogical H) (logical : Binary ι) :
    LinearMap.adjoint (D.phaseOperator logical) = D.phaseOperator logical := by
  classical
  rw [phaseOperator, map_sum]
  apply Finset.sum_congr rfl
  intro syndrome _
  rw [map_smulₛₗ,
    show starRingEnd Complex (D.phase logical syndrome) =
        D.phase logical syndrome by
          have hphase := D.star_phase logical syndrome
          change starRingEnd Complex (D.phase logical syndrome) =
            D.phase logical syndrome at hphase
          exact hphase,
    H.syndromeProjector_adjoint syndrome]

/-- Any two decoder phase operators commute because they share the resolution. -/
theorem phaseOperator_commute
    (D : DecoderDressedLogical H) (left right : Binary ι) :
    Commute (D.phaseOperator left) (D.phaseOperator right) := by
  change D.phaseOperator left * D.phaseOperator right =
    D.phaseOperator right * D.phaseOperator left
  rw [D.phaseOperator_mul left right, D.phaseOperator_mul right left]
  apply Finset.sum_congr rfl
  intro syndrome _
  rw [mul_comm]

/-- A normalizer logical Pauli commutes with every decoder phase operator. -/
theorem logical_commute_phaseOperator
    (D : DecoderDressedLogical H) {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical)
    (phaseLogical : Binary ι) :
    Commute (toHermitianQubitOperator logical) (D.phaseOperator phaseLogical) := by
  classical
  change toHermitianQubitOperator logical * D.phaseOperator phaseLogical =
    D.phaseOperator phaseLogical * toHermitianQubitOperator logical
  rw [phaseOperator, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro syndrome _
  rw [mul_smul_comm, smul_mul_assoc,
    (H.normalizer_commute_syndromeProjector hlogical syndrome).eq]

/-- The decoder-dressed realization of one bare logical Pauli. -/
def dressedLogical (D : DecoderDressedLogical H) (logical : Binary ι) :
    Operator (Qubit.QubitRegister ι) :=
  toHermitianQubitOperator logical * D.phaseOperator logical

/-- The phase-resolution formula equals the literal correction transformation. -/
theorem errorCorrectedObservable_logical
    (D : DecoderDressedLogical H) {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical) :
    D.errorCorrectedObservable (toHermitianQubitOperator logical) =
      D.dressedLogical logical := by
  classical
  rw [errorCorrectedObservable, dressedLogical, phaseOperator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro syndrome _
  calc
    H.syndromeProjector syndrome *
          LinearMap.adjoint (toHermitianQubitOperator (D.correction syndrome)) *
          toHermitianQubitOperator logical *
          toHermitianQubitOperator (D.correction syndrome) *
        H.syndromeProjector syndrome =
      H.syndromeProjector syndrome *
          (LinearMap.adjoint (toHermitianQubitOperator (D.correction syndrome)) *
            toHermitianQubitOperator logical *
            toHermitianQubitOperator (D.correction syndrome)) *
        H.syndromeProjector syndrome := by simp only [mul_assoc]
    _ = H.syndromeProjector syndrome *
          (D.phase logical syndrome • toHermitianQubitOperator logical) *
        H.syndromeProjector syndrome := by
          rw [D.correction_conjugates_logical logical syndrome]
    _ = D.phase logical syndrome •
        (H.syndromeProjector syndrome * toHermitianQubitOperator logical *
          H.syndromeProjector syndrome) := by
          simp only [mul_smul_comm, smul_mul_assoc]
    _ = D.phase logical syndrome •
        (toHermitianQubitOperator logical * H.syndromeProjector syndrome *
          H.syndromeProjector syndrome) := by
          rw [(H.normalizer_commute_syndromeProjector hlogical syndrome).eq]
    _ = D.phase logical syndrome •
        (toHermitianQubitOperator logical * H.syndromeProjector syndrome) := by
      rw [mul_assoc, H.syndromeProjector_mul_self]
    _ = toHermitianQubitOperator logical *
        (D.phase logical syndrome • H.syndromeProjector syndrome) := by
          rw [mul_smul_comm]

/-- The source's error-corrected logical `X_ec`. -/
def dressedX (D : DecoderDressedLogical H) :
    Operator (Qubit.QubitRegister ι) :=
  D.dressedLogical D.logicalX

/-- The source's error-corrected logical `Z_ec`. -/
def dressedZ (D : DecoderDressedLogical H) :
    Operator (Qubit.QubitRegister ι) :=
  D.dressedLogical D.logicalZ

/-- A dressed normalizer Pauli is self-adjoint. -/
theorem dressedLogical_adjoint
    (D : DecoderDressedLogical H) {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical) :
    LinearMap.adjoint (D.dressedLogical logical) = D.dressedLogical logical := by
  rw [dressedLogical, Module.End.mul_eq_comp, LinearMap.adjoint_comp,
    ← Module.End.mul_eq_comp, D.phaseOperator_adjoint,
    adjoint_toHermitianQubitOperator_eq_self]
  exact (D.logical_commute_phaseOperator hlogical logical).eq.symm

/-- A dressed normalizer Pauli squares to the identity. -/
theorem dressedLogical_square
    (D : DecoderDressedLogical H) {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical) :
    D.dressedLogical logical * D.dressedLogical logical = 1 := by
  have hcomm := D.logical_commute_phaseOperator hlogical logical
  rw [dressedLogical]
  calc
    (toHermitianQubitOperator logical * D.phaseOperator logical) *
        (toHermitianQubitOperator logical * D.phaseOperator logical) =
      toHermitianQubitOperator logical *
        (D.phaseOperator logical * toHermitianQubitOperator logical) *
          D.phaseOperator logical := by simp only [mul_assoc]
    _ = toHermitianQubitOperator logical *
        (toHermitianQubitOperator logical * D.phaseOperator logical) *
          D.phaseOperator logical := by rw [hcomm.eq]
    _ = (toHermitianQubitOperator logical *
          toHermitianQubitOperator logical) *
        (D.phaseOperator logical * D.phaseOperator logical) := by
          simp only [mul_assoc]
    _ = 1 := by
      rw [toHermitianQubitOperator_square, D.phaseOperator_square, one_mul]

@[simp]
theorem dressedX_adjoint (D : DecoderDressedLogical H) :
    LinearMap.adjoint D.dressedX = D.dressedX := by
  exact D.dressedLogical_adjoint D.logicalX_normalizer

@[simp]
theorem dressedZ_adjoint (D : DecoderDressedLogical H) :
    LinearMap.adjoint D.dressedZ = D.dressedZ := by
  exact D.dressedLogical_adjoint D.logicalZ_normalizer

@[simp]
theorem dressedX_square (D : DecoderDressedLogical H) :
    D.dressedX * D.dressedX = 1 :=
  D.dressedLogical_square D.logicalX_normalizer

@[simp]
theorem dressedZ_square (D : DecoderDressedLogical H) :
    D.dressedZ * D.dressedZ = 1 :=
  D.dressedLogical_square D.logicalZ_normalizer

/-- The decoder-dressed logical pair retains the bare Pauli anticommutation. -/
theorem dressedX_anticommute_dressedZ (D : DecoderDressedLogical H) :
    D.dressedX * D.dressedZ = -(D.dressedZ * D.dressedX) := by
  let X := toHermitianQubitOperator D.logicalX
  let Z := toHermitianQubitOperator D.logicalZ
  let DX := D.phaseOperator D.logicalX
  let DZ := D.phaseOperator D.logicalZ
  have hDXZ : Commute DX Z :=
    (D.logical_commute_phaseOperator D.logicalZ_normalizer D.logicalX).symm
  have hXDZ : Commute X DZ :=
    D.logical_commute_phaseOperator D.logicalX_normalizer D.logicalZ
  have hDXDZ : Commute DX DZ := D.phaseOperator_commute D.logicalX D.logicalZ
  have hanti : X * Z = -(Z * X) := by
    exact LocalStabilizerHamiltonian.toHermitianQubitOperator_anticommute_of_not_commutes
      D.logicalX D.logicalZ D.logicalX_not_commutes_logicalZ
  change (X * DX) * (Z * DZ) = -((Z * DZ) * (X * DX))
  calc
    (X * DX) * (Z * DZ) = X * (DX * Z) * DZ := by
      simp only [mul_assoc]
    _ = X * (Z * DX) * DZ := by rw [hDXZ.eq]
    _ = (X * Z) * (DX * DZ) := by simp only [mul_assoc]
    _ = -(Z * X) * (DX * DZ) := by rw [hanti]
    _ = -(Z * X) * (DZ * DX) := by rw [hDXDZ.eq]
    _ = -((Z * DZ) * (X * DX)) := by
      have hinside : (Z * X) * (DZ * DX) = (Z * DZ) * (X * DX) := by
        calc
          (Z * X) * (DZ * DX) = Z * (X * DZ) * DX := by
            simp only [mul_assoc]
          _ = Z * (DZ * X) * DX := by rw [hXDZ.eq]
          _ = (Z * DZ) * (X * DX) := by simp only [mul_assoc]
      rw [neg_mul, hinside]

/-- A bare logical normalizer Pauli commutes with every selected generator. -/
theorem logical_commute_generatorOperator
    (_D : DecoderDressedLogical H) {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical) (check : κ) :
    Commute (toHermitianQubitOperator logical) (H.generatorOperator check) := by
  have hbinary := hlogical (H.generators check)
    (H.generator_mem_generatedGroup check)
  change toHermitianQubitOperator logical * toQubitOperator (H.generators check) =
    toQubitOperator (H.generators check) * toHermitianQubitOperator logical
  unfold toHermitianQubitOperator
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [toQubitOperator_commute_of_commutes logical (H.generators check) hbinary]

/-- Every selected generator preserves every syndrome sector. -/
theorem generatorOperator_commute_syndromeProjector
    (_D : DecoderDressedLogical H) (check : κ)
    (syndrome : DecoderSyndrome κ) :
    Commute (H.generatorOperator check) (H.syndromeProjector syndrome) := by
  have hnormalizer : H.code.1.InBinaryNormalizer (H.generators check) := by
    intro stabilizer hstabilizer
    exact H.code.1.generatedGroup_pairwise_commutes
      (H.generator_mem_generatedGroup check) hstabilizer
  have hhermitian :=
    H.normalizer_commute_syndromeProjector hnormalizer syndrome
  change H.generatorOperator check * H.syndromeProjector syndrome =
    H.syndromeProjector syndrome * H.generatorOperator check
  change toQubitOperator (H.generators check) * H.syndromeProjector syndrome =
    H.syndromeProjector syndrome * toQubitOperator (H.generators check)
  have hphase : hermitianPhaseScalar (H.generators check) ≠ 0 := by
    unfold hermitianPhaseScalar
    exact pow_ne_zero _ Complex.I_ne_zero
  change toHermitianQubitOperator (H.generators check) *
      H.syndromeProjector syndrome =
    H.syndromeProjector syndrome *
      toHermitianQubitOperator (H.generators check) at hhermitian
  unfold toHermitianQubitOperator at hhermitian
  simp only [smul_mul_assoc, mul_smul_comm] at hhermitian
  exact smul_right_injective
    (Operator (Qubit.QubitRegister ι)) hphase hhermitian

/-- Every decoder phase operator commutes with every selected generator. -/
theorem generatorOperator_commute_phaseOperator
    (D : DecoderDressedLogical H) (check : κ) (logical : Binary ι) :
    Commute (H.generatorOperator check) (D.phaseOperator logical) := by
  classical
  change H.generatorOperator check * D.phaseOperator logical =
    D.phaseOperator logical * H.generatorOperator check
  rw [phaseOperator, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro syndrome _
  rw [mul_smul_comm, smul_mul_assoc,
    (D.generatorOperator_commute_syndromeProjector check syndrome).eq]

/-- Every dressed normalizer Pauli commutes with each selected generator. -/
theorem dressedLogical_commute_generatorOperator
    (D : DecoderDressedLogical H) {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical) (check : κ) :
    Commute (D.dressedLogical logical) (H.generatorOperator check) := by
  have hlogicalGenerator := D.logical_commute_generatorOperator hlogical check
  have hphaseGenerator := D.generatorOperator_commute_phaseOperator check logical
  change (toHermitianQubitOperator logical * D.phaseOperator logical) *
      H.generatorOperator check =
    H.generatorOperator check *
      (toHermitianQubitOperator logical * D.phaseOperator logical)
  calc
    (toHermitianQubitOperator logical * D.phaseOperator logical) *
        H.generatorOperator check =
      toHermitianQubitOperator logical *
        (D.phaseOperator logical * H.generatorOperator check) := by
          rw [mul_assoc]
    _ = toHermitianQubitOperator logical *
        (H.generatorOperator check * D.phaseOperator logical) := by
          rw [hphaseGenerator.eq]
    _ = (toHermitianQubitOperator logical * H.generatorOperator check) *
        D.phaseOperator logical := by rw [mul_assoc]
    _ = (H.generatorOperator check * toHermitianQubitOperator logical) *
        D.phaseOperator logical := by rw [hlogicalGenerator.eq]
    _ = H.generatorOperator check *
        (toHermitianQubitOperator logical * D.phaseOperator logical) := by
          rw [mul_assoc]

/-- Every dressed normalizer Pauli commutes with the selected Hamiltonian. -/
theorem dressedLogical_commute_hamiltonian
    (D : DecoderDressedLogical H) {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical) :
    Commute (D.dressedLogical logical) H.operator := by
  classical
  change D.dressedLogical logical * H.operator =
    H.operator * D.dressedLogical logical
  rw [LocalStabilizerHamiltonian.operator, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro check _
  have hgenerator := D.dressedLogical_commute_generatorOperator hlogical check
  change D.dressedLogical logical * (-(H.generatorOperator check)) =
    -(H.generatorOperator check) * D.dressedLogical logical
  rw [mul_neg, neg_mul, hgenerator.eq]

/-- The dressed logical `X_ec` commutes with the selected Hamiltonian. -/
theorem dressedX_commute_hamiltonian (D : DecoderDressedLogical H) :
    Commute D.dressedX H.operator :=
  D.dressedLogical_commute_hamiltonian D.logicalX_normalizer

/-- The dressed logical `Z_ec` commutes with the selected Hamiltonian. -/
theorem dressedZ_commute_hamiltonian (D : DecoderDressedLogical H) :
    Commute D.dressedZ H.operator :=
  D.dressedLogical_commute_hamiltonian D.logicalZ_normalizer

end DecoderDressedLogical
end StabilizerCode
end Coding
end QEC
