import QEC.Coding.Stabilizer.DecoderDressedLogical

/-!
# Good syndromes as a protected sector

This module supplies the stabilizer specialization of the CLBT10 Section 6
good-syndrome adapter.  Goodness is the source condition that the correction
after an elementary Pauli error, followed by that error and the correction
before it, is stabilizer-trivial.  The corresponding sum of joint syndrome
projectors is then proved to be an invariant Hamiltonian-commuting projection,
and the decoder-dressed logical observables are proved protected on it.

No Gibbs-tail estimate, decay theorem, or lifetime conclusion is made here.
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

namespace DecoderDressedLogical

variable {H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)}

/--
The sign acquired when two binary Pauli representatives are exchanged.  The
definition through the symplectic form makes its product law transparent.
-/
def commutationPhase (left right : Binary ι) : Complex :=
  binaryPhaseScalar (symplecticForm left.vector right.vector)

@[simp]
theorem commutationPhase_square (left right : Binary ι) :
    commutationPhase left right * commutationPhase left right = 1 := by
  by_cases h : Commutes left right
  · have hform : symplecticForm left.vector right.vector = 0 := h
    simp [commutationPhase, hform, binaryPhaseScalar]
  · have hform : symplecticForm left.vector right.vector = 1 :=
      zmod_two_eq_one_of_ne_zero (by simpa [Commutes] using h)
    simp [commutationPhase, hform, binaryPhaseScalar]

/-- The commutation sign is multiplicative in a Pauli product. -/
theorem commutationPhase_binaryMul_left
    (left middle right : Binary ι) :
    commutationPhase (binaryMul left middle) right =
      commutationPhase left right * commutationPhase middle right := by
  rw [commutationPhase, commutationPhase, commutationPhase]
  rw [show symplecticForm (binaryMul left middle).vector right.vector =
      symplecticForm left.vector right.vector +
        symplecticForm middle.vector right.vector by
    simp only [binaryMul, symplecticForm, Pi.add_apply, add_mul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro index _
    ring]
  exact binaryPhaseScalar_add _ _

/-- The existing decoder phase is the symplectic commutation sign. -/
theorem phase_eq_commutationPhase
    (D : DecoderDressedLogical H) (logical : Binary ι)
    (syndrome : DecoderSyndrome κ) :
    D.phase logical syndrome =
      commutationPhase (D.correction syndrome) logical := by
  by_cases h : Commutes (D.correction syndrome) logical
  · have hform :
        symplecticForm (D.correction syndrome).vector logical.vector = 0 := h
    simp [phase, h, commutationPhase, hform, binaryPhaseScalar]
  · have hform :
        symplecticForm (D.correction syndrome).vector logical.vector = 1 :=
      zmod_two_eq_one_of_ne_zero (by simpa [Commutes] using h)
    simp [phase, commutationPhase, h, hform, binaryPhaseScalar]

/-- Concrete exchange law for Hermitian Pauli representatives. -/
theorem toHermitianQubitOperator_mul_eq_commutationPhase_smul
    (left right : Binary ι) :
    toHermitianQubitOperator left * toHermitianQubitOperator right =
      commutationPhase left right •
        (toHermitianQubitOperator right * toHermitianQubitOperator left) := by
  by_cases h : Commutes left right
  · have hform : symplecticForm left.vector right.vector = 0 := h
    rw [toHermitianQubitOperator_commute_of_commutes left right h]
    simp [commutationPhase, hform, binaryPhaseScalar]
  · have hform : symplecticForm left.vector right.vector = 1 :=
      zmod_two_eq_one_of_ne_zero (by simpa [Commutes] using h)
    rw [LocalStabilizerHamiltonian.toHermitianQubitOperator_anticommute_of_not_commutes
      left right h]
    simp [commutationPhase, hform, binaryPhaseScalar]

/--
A syndrome is good for the selected elementary errors exactly when the CLBT
composite `C(s+s_E) E C(s)` belongs to the stabilizer group for every selected
error.
-/
def goodSyndrome (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι))
    (syndrome : DecoderSyndrome κ) : Prop :=
  ∀ error ∈ elementaryErrors,
    binaryMul (D.correction (H.transportSyndrome error syndrome))
        (binaryMul error (D.correction syndrome)) ∈ H.code.1.generatedGroup

/--
Goodness forces the decoder phase after an elementary error to equal the old
decoder phase times that error's commutation sign with the logical Pauli.
-/
theorem goodSyndrome_phase_transport
    (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι))
    {syndrome : DecoderSyndrome κ}
    (hgood : D.goodSyndrome elementaryErrors syndrome)
    {error : Binary ι} (herror : error ∈ elementaryErrors)
    {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical) :
    D.phase logical (H.transportSyndrome error syndrome) =
      commutationPhase error logical * D.phase logical syndrome := by
  let transported := H.transportSyndrome error syndrome
  let composite := binaryMul (D.correction transported)
    (binaryMul error (D.correction syndrome))
  have hcomposite_mem : composite ∈ H.code.1.generatedGroup := by
    exact hgood error herror
  have hlogical_composite : Commutes logical composite :=
    hlogical composite hcomposite_mem
  have hcomposite_logical : Commutes composite logical :=
    (commutes_comm composite logical).2 hlogical_composite
  have hcomposite_phase : commutationPhase composite logical = 1 := by
    have hform : symplecticForm composite.vector logical.vector = 0 :=
      hcomposite_logical
    simp [commutationPhase, hform, binaryPhaseScalar]
  have hphase_product :
      commutationPhase (D.correction transported) logical *
          (commutationPhase error logical *
            commutationPhase (D.correction syndrome) logical) = 1 := by
    simpa [composite, commutationPhase_binaryMul_left] using hcomposite_phase
  have htail_square :
      (commutationPhase error logical *
          commutationPhase (D.correction syndrome) logical) *
        (commutationPhase error logical *
          commutationPhase (D.correction syndrome) logical) = 1 := by
    calc
      (commutationPhase error logical *
            commutationPhase (D.correction syndrome) logical) *
          (commutationPhase error logical *
            commutationPhase (D.correction syndrome) logical) =
        (commutationPhase error logical * commutationPhase error logical) *
          (commutationPhase (D.correction syndrome) logical *
            commutationPhase (D.correction syndrome) logical) := by ring
      _ = 1 := by simp
  rw [D.phase_eq_commutationPhase, D.phase_eq_commutationPhase]
  calc
    commutationPhase (D.correction transported) logical =
        commutationPhase (D.correction transported) logical * 1 := by simp
    _ = commutationPhase (D.correction transported) logical *
        ((commutationPhase error logical *
            commutationPhase (D.correction syndrome) logical) *
          (commutationPhase error logical *
            commutationPhase (D.correction syndrome) logical)) := by
          rw [htail_square]
    _ = (commutationPhase (D.correction transported) logical *
          (commutationPhase error logical *
            commutationPhase (D.correction syndrome) logical)) *
        (commutationPhase error logical *
          commutationPhase (D.correction syndrome) logical) := by ring
    _ = commutationPhase error logical *
        commutationPhase (D.correction syndrome) logical := by
          rw [hphase_product, one_mul]

/-- The finite set of syndromes satisfying the source-exact goodness test. -/
def goodSyndromes (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι)) : Finset (DecoderSyndrome κ) := by
  classical
  exact Finset.univ.filter (D.goodSyndrome elementaryErrors)

/-- The complementary finite set of bad syndromes. -/
def badSyndromes (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι)) : Finset (DecoderSyndrome κ) := by
  classical
  exact Finset.univ.filter (fun syndrome =>
    ¬ D.goodSyndrome elementaryErrors syndrome)

/-- The CLBT projector onto the direct sum of all good syndrome sectors. -/
def goodSyndromeProjector (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι)) :
    Operator (Qubit.QubitRegister ι) :=
  ∑ syndrome ∈ D.goodSyndromes elementaryErrors,
    H.syndromeProjector syndrome

/-- The projector onto the complementary bad syndrome sectors. -/
def badSyndromeProjector (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι)) :
    Operator (Qubit.QubitRegister ι) :=
  ∑ syndrome ∈ D.badSyndromes elementaryErrors,
    H.syndromeProjector syndrome

@[simp]
theorem goodSyndromeProjector_adjoint
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    LinearMap.adjoint (D.goodSyndromeProjector elementaryErrors) =
      D.goodSyndromeProjector elementaryErrors := by
  classical
  rw [goodSyndromeProjector, map_sum]
  apply Finset.sum_congr rfl
  intro syndrome _
  exact H.syndromeProjector_adjoint syndrome

@[simp]
theorem goodSyndromeProjector_mul_self
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    D.goodSyndromeProjector elementaryErrors *
        D.goodSyndromeProjector elementaryErrors =
      D.goodSyndromeProjector elementaryErrors := by
  classical
  rw [goodSyndromeProjector, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro syndrome hsyndrome
  rw [Finset.sum_eq_single syndrome]
  · exact H.syndromeProjector_mul_self syndrome
  · intro other hother hne
    exact H.syndromeProjector_mul_of_ne syndrome other hne.symm
  · exact fun hnot => (hnot hsyndrome).elim

/-- The good-sector sum is a genuine self-adjoint projection. -/
theorem goodSyndromeProjector_isStarProjection
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    IsStarProjection (D.goodSyndromeProjector elementaryErrors) := by
  exact ⟨D.goodSyndromeProjector_mul_self elementaryErrors,
    D.goodSyndromeProjector_adjoint elementaryErrors⟩

/-- Good and bad syndrome projectors resolve the identity. -/
theorem goodSyndromeProjector_add_badSyndromeProjector
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    D.goodSyndromeProjector elementaryErrors +
        D.badSyndromeProjector elementaryErrors = 1 := by
  classical
  rw [goodSyndromeProjector, badSyndromeProjector,
    goodSyndromes, badSyndromes,
    Finset.sum_filter_add_sum_filter_not]
  exact H.sum_syndromeProjector_eq_one

/-- The bad-sector projector is literally the complement of `P_good`. -/
theorem one_sub_goodSyndromeProjector_eq_badSyndromeProjector
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    1 - D.goodSyndromeProjector elementaryErrors =
      D.badSyndromeProjector elementaryErrors := by
  have h := D.goodSyndromeProjector_add_badSyndromeProjector elementaryErrors
  rw [sub_eq_iff_eq_add]
  simpa [add_comm] using h.symm

/-- A diagonal decoder phase acts by its scalar on one syndrome sector. -/
theorem phaseOperator_mul_syndromeProjector
    (D : DecoderDressedLogical H) (logical : Binary ι)
    (syndrome : DecoderSyndrome κ) :
    D.phaseOperator logical * H.syndromeProjector syndrome =
      D.phase logical syndrome • H.syndromeProjector syndrome := by
  classical
  rw [phaseOperator, Finset.sum_mul, Finset.sum_eq_single syndrome]
  · rw [smul_mul_assoc, H.syndromeProjector_mul_self]
  · intro other _ hne
    rw [smul_mul_assoc, H.syndromeProjector_mul_of_ne other syndrome hne]
    simp
  · simp

/-- The same diagonal action holds with the syndrome projector on the left. -/
theorem syndromeProjector_mul_phaseOperator
    (D : DecoderDressedLogical H) (logical : Binary ι)
    (syndrome : DecoderSyndrome κ) :
    H.syndromeProjector syndrome * D.phaseOperator logical =
      D.phase logical syndrome • H.syndromeProjector syndrome := by
  classical
  rw [phaseOperator, Finset.mul_sum, Finset.sum_eq_single syndrome]
  · rw [mul_smul_comm, H.syndromeProjector_mul_self]
  · intro other _ hne
    rw [mul_smul_comm, H.syndromeProjector_mul_of_ne syndrome other hne.symm]
    simp
  · simp

/-- Every syndrome projector commutes with every decoder phase operator. -/
theorem syndromeProjector_commute_phaseOperator
    (D : DecoderDressedLogical H) (logical : Binary ι)
    (syndrome : DecoderSyndrome κ) :
    Commute (H.syndromeProjector syndrome) (D.phaseOperator logical) := by
  change H.syndromeProjector syndrome * D.phaseOperator logical =
    D.phaseOperator logical * H.syndromeProjector syndrome
  rw [D.syndromeProjector_mul_phaseOperator,
    D.phaseOperator_mul_syndromeProjector]

/-- Every syndrome sector is invariant under a dressed normalizer Pauli. -/
theorem syndromeProjector_commute_dressedLogical
    (D : DecoderDressedLogical H) {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical)
    (syndrome : DecoderSyndrome κ) :
    Commute (H.syndromeProjector syndrome) (D.dressedLogical logical) := by
  have hbare := H.normalizer_commute_syndromeProjector hlogical syndrome
  have hphase := D.syndromeProjector_commute_phaseOperator logical syndrome
  change H.syndromeProjector syndrome *
      (toHermitianQubitOperator logical * D.phaseOperator logical) =
    (toHermitianQubitOperator logical * D.phaseOperator logical) *
      H.syndromeProjector syndrome
  calc
    H.syndromeProjector syndrome *
          (toHermitianQubitOperator logical * D.phaseOperator logical) =
        (H.syndromeProjector syndrome *
          toHermitianQubitOperator logical) * D.phaseOperator logical := by
            rw [mul_assoc]
    _ = (toHermitianQubitOperator logical *
          H.syndromeProjector syndrome) * D.phaseOperator logical := by
            rw [hbare.eq.symm]
    _ = toHermitianQubitOperator logical *
        (H.syndromeProjector syndrome * D.phaseOperator logical) := by
          rw [mul_assoc]
    _ = toHermitianQubitOperator logical *
        (D.phaseOperator logical * H.syndromeProjector syndrome) := by
          rw [hphase.eq]
    _ = (toHermitianQubitOperator logical * D.phaseOperator logical) *
        H.syndromeProjector syndrome := by rw [mul_assoc]

/-- The selected Hamiltonian preserves every syndrome sector. -/
theorem syndromeProjector_commute_hamiltonian
    (D : DecoderDressedLogical H) (syndrome : DecoderSyndrome κ) :
    Commute (H.syndromeProjector syndrome) H.operator := by
  classical
  change H.syndromeProjector syndrome * H.operator =
    H.operator * H.syndromeProjector syndrome
  rw [LocalStabilizerHamiltonian.operator, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro check _
  rw [LocalStabilizerHamiltonian.term, mul_neg, neg_mul]
  exact congrArg Neg.neg
    (D.generatorOperator_commute_syndromeProjector check syndrome).eq.symm

/-- The good projector commutes with every dressed normalizer Pauli. -/
theorem goodSyndromeProjector_commute_dressedLogical
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι))
    {logical : Binary ι} (hlogical : H.code.1.InBinaryNormalizer logical) :
    Commute (D.goodSyndromeProjector elementaryErrors)
      (D.dressedLogical logical) := by
  classical
  change D.goodSyndromeProjector elementaryErrors * D.dressedLogical logical =
    D.dressedLogical logical * D.goodSyndromeProjector elementaryErrors
  rw [goodSyndromeProjector, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro syndrome _
  exact (D.syndromeProjector_commute_dressedLogical hlogical syndrome).eq

/-- The good projector commutes with the dressed logical `X`. -/
theorem goodSyndromeProjector_commute_dressedX
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    Commute (D.goodSyndromeProjector elementaryErrors) D.dressedX :=
  D.goodSyndromeProjector_commute_dressedLogical elementaryErrors
    D.logicalX_normalizer

/-- The good projector commutes with the dressed logical `Z`. -/
theorem goodSyndromeProjector_commute_dressedZ
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    Commute (D.goodSyndromeProjector elementaryErrors) D.dressedZ :=
  D.goodSyndromeProjector_commute_dressedLogical elementaryErrors
    D.logicalZ_normalizer

/-- The good projector commutes with the selected stabilizer Hamiltonian. -/
theorem goodSyndromeProjector_commute_hamiltonian
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    Commute (D.goodSyndromeProjector elementaryErrors) H.operator := by
  classical
  change D.goodSyndromeProjector elementaryErrors * H.operator =
    H.operator * D.goodSyndromeProjector elementaryErrors
  rw [goodSyndromeProjector, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro syndrome _
  exact (D.syndromeProjector_commute_hamiltonian syndrome).eq

/-- The good sector is invariant under the dressed logical `X`. -/
theorem goodSyndromeProjector_invariant_dressedX
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    D.goodSyndromeProjector elementaryErrors * D.dressedX *
        D.goodSyndromeProjector elementaryErrors =
      D.dressedX * D.goodSyndromeProjector elementaryErrors := by
  change D.goodSyndromeProjector elementaryErrors *
      D.dressedLogical D.logicalX *
        D.goodSyndromeProjector elementaryErrors =
    D.dressedLogical D.logicalX * D.goodSyndromeProjector elementaryErrors
  rw [(D.goodSyndromeProjector_commute_dressedLogical elementaryErrors
      D.logicalX_normalizer).eq, mul_assoc,
    D.goodSyndromeProjector_mul_self]

/-- The good sector is invariant under the dressed logical `Z`. -/
theorem goodSyndromeProjector_invariant_dressedZ
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    D.goodSyndromeProjector elementaryErrors * D.dressedZ *
        D.goodSyndromeProjector elementaryErrors =
      D.dressedZ * D.goodSyndromeProjector elementaryErrors := by
  change D.goodSyndromeProjector elementaryErrors *
      D.dressedLogical D.logicalZ *
        D.goodSyndromeProjector elementaryErrors =
    D.dressedLogical D.logicalZ * D.goodSyndromeProjector elementaryErrors
  rw [(D.goodSyndromeProjector_commute_dressedLogical elementaryErrors
      D.logicalZ_normalizer).eq, mul_assoc,
    D.goodSyndromeProjector_mul_self]

/--
On one good syndrome sector, an elementary error commutes with every dressed
normalizer Pauli.  This is the source protection calculation before summing
over good sectors.
-/
theorem elementaryError_commute_dressedLogical_on_good_syndrome
    (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι))
    {syndrome : DecoderSyndrome κ}
    (hgood : D.goodSyndrome elementaryErrors syndrome)
    {error : Binary ι} (herror : error ∈ elementaryErrors)
    {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical) :
    toHermitianQubitOperator error * D.dressedLogical logical *
        H.syndromeProjector syndrome =
      D.dressedLogical logical * toHermitianQubitOperator error *
        H.syndromeProjector syndrome := by
  have hphase := D.goodSyndrome_phase_transport elementaryErrors hgood herror hlogical
  have hexchange :=
    toHermitianQubitOperator_mul_eq_commutationPhase_smul error logical
  have htransport := H.pauli_mul_syndromeProjector error syndrome
  change toHermitianQubitOperator error *
        (toHermitianQubitOperator logical * D.phaseOperator logical) *
          H.syndromeProjector syndrome =
    (toHermitianQubitOperator logical * D.phaseOperator logical) *
        toHermitianQubitOperator error * H.syndromeProjector syndrome
  calc
    toHermitianQubitOperator error *
          (toHermitianQubitOperator logical * D.phaseOperator logical) *
            H.syndromeProjector syndrome =
        (toHermitianQubitOperator error * toHermitianQubitOperator logical) *
          (D.phaseOperator logical * H.syndromeProjector syndrome) := by
            simp only [mul_assoc]
    _ = (toHermitianQubitOperator error * toHermitianQubitOperator logical) *
        (D.phase logical syndrome • H.syndromeProjector syndrome) := by
          rw [D.phaseOperator_mul_syndromeProjector]
    _ = D.phase logical syndrome •
        ((toHermitianQubitOperator error * toHermitianQubitOperator logical) *
          H.syndromeProjector syndrome) := by rw [mul_smul_comm]
    _ = D.phase logical syndrome •
        ((commutationPhase error logical •
            (toHermitianQubitOperator logical *
              toHermitianQubitOperator error)) *
          H.syndromeProjector syndrome) := by rw [hexchange]
    _ = (commutationPhase error logical * D.phase logical syndrome) •
        ((toHermitianQubitOperator logical *
            toHermitianQubitOperator error) *
          H.syndromeProjector syndrome) := by
            rw [smul_mul_assoc, smul_smul, mul_comm]
    _ = D.phase logical (H.transportSyndrome error syndrome) •
        ((toHermitianQubitOperator logical *
            toHermitianQubitOperator error) *
          H.syndromeProjector syndrome) := by rw [hphase]
    _ = toHermitianQubitOperator logical *
        ((D.phase logical (H.transportSyndrome error syndrome) •
            H.syndromeProjector (H.transportSyndrome error syndrome)) *
          toHermitianQubitOperator error) := by
            rw [mul_assoc,
              H.pauli_mul_syndromeProjector error syndrome]
            rw [smul_mul_assoc, mul_smul_comm]
    _ = toHermitianQubitOperator logical *
        ((D.phaseOperator logical *
            H.syndromeProjector (H.transportSyndrome error syndrome)) *
          toHermitianQubitOperator error) := by
            rw [D.phaseOperator_mul_syndromeProjector]
    _ = (toHermitianQubitOperator logical * D.phaseOperator logical) *
        (H.syndromeProjector (H.transportSyndrome error syndrome) *
          toHermitianQubitOperator error) := by simp only [mul_assoc]
    _ = (toHermitianQubitOperator logical * D.phaseOperator logical) *
        (toHermitianQubitOperator error * H.syndromeProjector syndrome) := by
          rw [htransport]
    _ = (toHermitianQubitOperator logical * D.phaseOperator logical) *
        toHermitianQubitOperator error * H.syndromeProjector syndrome := by
          simp only [mul_assoc]

/--
For every selected elementary error, the dressed normalizer commutator
vanishes after restriction to `P_good`.
-/
theorem elementaryError_commutator_dressedLogical_mul_goodSyndromeProjector_eq_zero
    (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι))
    {error : Binary ι} (herror : error ∈ elementaryErrors)
    {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical) :
    (toHermitianQubitOperator error * D.dressedLogical logical -
        D.dressedLogical logical * toHermitianQubitOperator error) *
      D.goodSyndromeProjector elementaryErrors = 0 := by
  classical
  rw [goodSyndromeProjector, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro syndrome hsyndrome
  rw [sub_mul]
  apply sub_eq_zero.mpr
  apply D.elementaryError_commute_dressedLogical_on_good_syndrome
    elementaryErrors
  · exact (Finset.mem_filter.mp hsyndrome).2
  · exact herror
  · exact hlogical

/-- Every selected elementary error protects the dressed logical `X`. -/
theorem elementaryError_commutator_dressedX_mul_goodSyndromeProjector_eq_zero
    (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι))
    {error : Binary ι} (herror : error ∈ elementaryErrors) :
    (toHermitianQubitOperator error * D.dressedX -
        D.dressedX * toHermitianQubitOperator error) *
      D.goodSyndromeProjector elementaryErrors = 0 :=
  D.elementaryError_commutator_dressedLogical_mul_goodSyndromeProjector_eq_zero
    elementaryErrors herror D.logicalX_normalizer

/-- Every selected elementary error protects the dressed logical `Z`. -/
theorem elementaryError_commutator_dressedZ_mul_goodSyndromeProjector_eq_zero
    (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι))
    {error : Binary ι} (herror : error ∈ elementaryErrors) :
    (toHermitianQubitOperator error * D.dressedZ -
        D.dressedZ * toHermitianQubitOperator error) *
      D.goodSyndromeProjector elementaryErrors = 0 :=
  D.elementaryError_commutator_dressedLogical_mul_goodSyndromeProjector_eq_zero
    elementaryErrors herror D.logicalZ_normalizer

/-- The normalized Gibbs weight assigned to all bad syndrome sectors. -/
def badSyndromeGibbsWeight
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι))
    (rhoBeta : DensityOperator (Qubit.QubitRegister ι)) : Complex :=
  ∑ syndrome ∈ D.badSyndromes elementaryErrors,
    LinearMap.trace Complex (Qubit.QubitRegister ι)
      (H.syndromeProjector syndrome * rhoBeta.toOperator)

/--
The CLBT mass `Tr ((I - P_good) rho_beta)` is exactly the sum of the Gibbs
weights of the bad syndrome sectors.
-/
theorem trace_one_sub_goodSyndromeProjector_mul_eq_badSyndromeGibbsWeight
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι))
    (rhoBeta : DensityOperator (Qubit.QubitRegister ι)) :
    LinearMap.trace Complex (Qubit.QubitRegister ι)
        ((1 - D.goodSyndromeProjector elementaryErrors) * rhoBeta.toOperator) =
      D.badSyndromeGibbsWeight elementaryErrors rhoBeta := by
  rw [D.one_sub_goodSyndromeProjector_eq_badSyndromeProjector,
    badSyndromeGibbsWeight, badSyndromeProjector, Finset.sum_mul, map_sum]

/-- The named proposition collecting the complete M11 good-syndrome adapter. -/
def GoodSyndromeProtectedObservable
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) : Prop :=
  IsStarProjection (D.goodSyndromeProjector elementaryErrors) ∧
    Commute (D.goodSyndromeProjector elementaryErrors) D.dressedX ∧
    Commute (D.goodSyndromeProjector elementaryErrors) D.dressedZ ∧
    Commute (D.goodSyndromeProjector elementaryErrors) H.operator ∧
    D.goodSyndromeProjector elementaryErrors * D.dressedX *
        D.goodSyndromeProjector elementaryErrors =
      D.dressedX * D.goodSyndromeProjector elementaryErrors ∧
    D.goodSyndromeProjector elementaryErrors * D.dressedZ *
        D.goodSyndromeProjector elementaryErrors =
      D.dressedZ * D.goodSyndromeProjector elementaryErrors ∧
    (∀ error ∈ elementaryErrors,
      (toHermitianQubitOperator error * D.dressedX -
          D.dressedX * toHermitianQubitOperator error) *
        D.goodSyndromeProjector elementaryErrors = 0 ∧
      (toHermitianQubitOperator error * D.dressedZ -
          D.dressedZ * toHermitianQubitOperator error) *
        D.goodSyndromeProjector elementaryErrors = 0) ∧
    ∀ rhoBeta : DensityOperator (Qubit.QubitRegister ι),
      LinearMap.trace Complex (Qubit.QubitRegister ι)
          ((1 - D.goodSyndromeProjector elementaryErrors) * rhoBeta.toOperator) =
        D.badSyndromeGibbsWeight elementaryErrors rhoBeta

/--
The complete stabilizer good-syndrome adapter used downstream by M11.  Every
property in the conclusion is derived above from deterministic correction,
the stabilizer normalizer laws, and the source-exact goodness predicate.
-/
theorem stabilizerGoodSyndromeProtectedObservable
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    IsStarProjection (D.goodSyndromeProjector elementaryErrors) ∧
      Commute (D.goodSyndromeProjector elementaryErrors) D.dressedX ∧
      Commute (D.goodSyndromeProjector elementaryErrors) D.dressedZ ∧
      Commute (D.goodSyndromeProjector elementaryErrors) H.operator ∧
      D.goodSyndromeProjector elementaryErrors * D.dressedX *
          D.goodSyndromeProjector elementaryErrors =
        D.dressedX * D.goodSyndromeProjector elementaryErrors ∧
      D.goodSyndromeProjector elementaryErrors * D.dressedZ *
          D.goodSyndromeProjector elementaryErrors =
        D.dressedZ * D.goodSyndromeProjector elementaryErrors ∧
      (∀ error ∈ elementaryErrors,
        (toHermitianQubitOperator error * D.dressedX -
            D.dressedX * toHermitianQubitOperator error) *
          D.goodSyndromeProjector elementaryErrors = 0 ∧
        (toHermitianQubitOperator error * D.dressedZ -
            D.dressedZ * toHermitianQubitOperator error) *
          D.goodSyndromeProjector elementaryErrors = 0) ∧
      ∀ rhoBeta : DensityOperator (Qubit.QubitRegister ι),
        LinearMap.trace Complex (Qubit.QubitRegister ι)
            ((1 - D.goodSyndromeProjector elementaryErrors) *
              rhoBeta.toOperator) =
          D.badSyndromeGibbsWeight elementaryErrors rhoBeta := by
  refine ⟨D.goodSyndromeProjector_isStarProjection elementaryErrors,
    D.goodSyndromeProjector_commute_dressedX elementaryErrors,
    D.goodSyndromeProjector_commute_dressedZ elementaryErrors,
    D.goodSyndromeProjector_commute_hamiltonian elementaryErrors,
    D.goodSyndromeProjector_invariant_dressedX elementaryErrors,
    D.goodSyndromeProjector_invariant_dressedZ elementaryErrors, ?_, ?_⟩
  · intro error herror
    exact ⟨
      D.elementaryError_commutator_dressedX_mul_goodSyndromeProjector_eq_zero
        elementaryErrors herror,
      D.elementaryError_commutator_dressedZ_mul_goodSyndromeProjector_eq_zero
        elementaryErrors herror⟩
  · intro rhoBeta
    exact D.trace_one_sub_goodSyndromeProjector_mul_eq_badSyndromeGibbsWeight
      elementaryErrors rhoBeta

end DecoderDressedLogical
end StabilizerCode
end Coding
end QEC
