import QEC.Coding.Stabilizer.JointMeasurement
import QEC.Distillation.FiveQubitT.Input
import QEC.Distillation.Core.MagicStateProtocol
import QEC.Semantics.Entropy.Purification
/-!
# BK05 five-qubit T-state postselection

This internal module begins the concrete physical layer of the BK05 five-to-one
T-state protocol. It fixes the literal four-check five-qubit code, its
all-positive joint projector, and the coarse accepted/rejected source
instrument. The source rejection decision occurs before decoding.

Any rejected density carried through the shared run and output-postprocessing
interfaces below is only a technical completion of those total interfaces. It
is not a BK05 decoded rejected history: nontrivial source syndromes are
discarded before the coherent logical decoder is applied.

The later decoder and raw-output algebra build on these definitions; no
recurrence, threshold, or convergence claim belongs in this module.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace BK05T

open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open OneQubitMagic
open scoped BigOperators ComplexOrder TensorProduct

/-- The five physical qubit sites in the elementary BK05 protocol. -/
abbrev FiveQubitSite := Fin 5

/-- The four measured stabilizer checks. -/
abbrev FiveQubitCheckIndex := Fin 4

/-- The concrete five-qubit register on which the source syndrome is measured. -/
abbrev FiveQubitSpace := QubitRegister FiveQubitSite

/-- A source error word selects T_0 or T_1 independently at each site. -/
abbrev FiveQubitErrorWord := FiveQubitSite → Fin 2

/-- The local Pauli letters appearing in the four BK05 checks. -/
inductive FiveQubitPauliLetter
  | I
  | X
  | Z
deriving DecidableEq, Repr

/--
The source-order check table

* S₁ = X Z Z X I,
* S₂ = I X Z Z X,
* S₃ = X I X Z Z,
* S₄ = Z X I X Z.
-/
def fiveQubitCheckLetter
    (check : FiveQubitCheckIndex) (site : FiveQubitSite) :
    FiveQubitPauliLetter :=
  match check.1, site.1 with
  | 0, 0 => .X
  | 0, 1 => .Z
  | 0, 2 => .Z
  | 0, 3 => .X
  | 1, 1 => .X
  | 1, 2 => .Z
  | 1, 3 => .Z
  | 1, 4 => .X
  | 2, 0 => .X
  | 2, 2 => .X
  | 2, 3 => .Z
  | 2, 4 => .Z
  | 3, 0 => .Z
  | 3, 1 => .X
  | 3, 3 => .X
  | 3, 4 => .Z
  | _, _ => .I

/-- The source check table is definitionally the advertised four Pauli words. -/
theorem fiveQubitCheckLetter_rows :
    List.ofFn (fiveQubitCheckLetter 0) = [.X, .Z, .Z, .X, .I] ∧
    List.ofFn (fiveQubitCheckLetter 1) = [.I, .X, .Z, .Z, .X] ∧
    List.ofFn (fiveQubitCheckLetter 2) = [.X, .I, .X, .Z, .Z] ∧
    List.ofFn (fiveQubitCheckLetter 3) = [.Z, .X, .I, .X, .Z] := by
  native_decide

/-- The binary X coordinate of one local check letter. -/
def fiveQubitLetterX : FiveQubitPauliLetter → ZMod 2
  | .X => 1
  | _ => 0

/-- The binary Z coordinate of one local check letter. -/
def fiveQubitLetterZ : FiveQubitPauliLetter → ZMod 2
  | .Z => 1
  | _ => 0

/-- One of the four actual signed Hermitian five-qubit stabilizers. -/
def fiveQubitCheck (check : FiveQubitCheckIndex) : Binary FiveQubitSite where
  phase := 0
  vector :=
    { xPart := fun site => fiveQubitLetterX (fiveQubitCheckLetter check site)
      zPart := fun site => fiveQubitLetterZ (fiveQubitCheckLetter check site) }

/-- The four concrete five-qubit checks commute pairwise. -/
theorem fiveQubitChecks_commute (left right : FiveQubitCheckIndex) :
    Commutes (fiveQubitCheck left) (fiveQubitCheck right) := by
  unfold Commutes
  fin_cases left <;> fin_cases right <;> native_decide

/-- The computational-basis bitstring reached by one concrete check. -/
def fiveQubitCheckTarget
    (check : FiveQubitCheckIndex) (bits : Bitstring FiveQubitSite) :
    Bitstring FiveQubitSite :=
  match check.1 with
  | 0 => flipAt 0 (flipAt 3 bits)
  | 1 => flipAt 1 (flipAt 4 bits)
  | 2 => flipAt 0 (flipAt 2 bits)
  | _ => flipAt 1 (flipAt 3 bits)

/-- The real sign acquired by one check on a computational-basis word. -/
def fiveQubitCheckPhase
    (check : FiveQubitCheckIndex) (bits : Bitstring FiveQubitSite) : Complex :=
  match check.1 with
  | 0 => zPhase (bits 1) * zPhase (bits 2)
  | 1 => zPhase (bits 2) * zPhase (bits 3)
  | 2 => zPhase (bits 3) * zPhase (bits 4)
  | _ => zPhase (bits 0) * zPhase (bits 4)

@[simp]
private theorem fiveQubitCheck_overlapCount
    (check : FiveQubitCheckIndex) :
    binaryOverlapCount (fiveQubitCheck check) = 0 := by
  fin_cases check <;> native_decide

@[simp]
private theorem fiveQubitCheck_phase (check : FiveQubitCheckIndex) :
    (fiveQubitCheck check).phase = 0 :=
  rfl

private theorem fiveQubitCheck_xSupport
    (check : FiveQubitCheckIndex) :
    xSupport (fiveQubitCheck check) =
      match check.1 with
      | 0 => {0, 3}
      | 1 => {1, 4}
      | 2 => {0, 2}
      | _ => {1, 3} := by
  fin_cases check <;> native_decide

private theorem fiveQubitCheck_zSupport
    (check : FiveQubitCheckIndex) :
    zSupport (fiveQubitCheck check) =
      match check.1 with
      | 0 => {1, 2}
      | 1 => {2, 3}
      | 2 => {3, 4}
      | _ => {0, 4} := by
  fin_cases check <;> native_decide

@[simp]
private theorem fiveQubitCheck_hermitianPhase
    (check : FiveQubitCheckIndex) :
    hermitianPhaseScalar (fiveQubitCheck check) = 1 := by
  simp [hermitianPhaseScalar]

@[simp]
private theorem fiveQubitCheck_zSupportPhase_any
    (check : FiveQubitCheckIndex) (bits : Bitstring FiveQubitSite) :
    zSupportPhase (zSupport (fiveQubitCheck check)) bits =
      fiveQubitCheckPhase check bits := by
  fin_cases check <;>
    simp [fiveQubitCheck_zSupport, fiveQubitCheckPhase,
      zSupportPhase, supportPhaseSign]

@[simp]
private theorem fiveQubitCheck_flipSupport
    (check : FiveQubitCheckIndex) (bits : Bitstring FiveQubitSite) :
    flipSupport (xSupport (fiveQubitCheck check)) bits =
      fiveQubitCheckTarget check bits := by
  fin_cases check <;> funext site <;> fin_cases site <;>
    simp [fiveQubitCheck_xSupport, fiveQubitCheckTarget,
      flipSupport, flipAt]

@[simp]
private theorem fiveQubitCheck_zSupportPhase
    (check : FiveQubitCheckIndex) (bits : Bitstring FiveQubitSite) :
    zSupportPhase (zSupport (fiveQubitCheck check))
        (flipSupport (xSupport (fiveQubitCheck check)) bits) =
      fiveQubitCheckPhase check bits := by
  fin_cases check <;>
    simp [fiveQubitCheck_xSupport, fiveQubitCheck_zSupport,
      fiveQubitCheckPhase, zSupportPhase_flipSupport,
      supportPhaseSign, zSupportPhase, flipSupport]

@[simp]
private theorem fiveQubitCheck_zSupportPhase_target
    (check : FiveQubitCheckIndex) (bits : Bitstring FiveQubitSite) :
    zSupportPhase (zSupport (fiveQubitCheck check))
        (fiveQubitCheckTarget check bits) =
      fiveQubitCheckPhase check bits := by
  rw [← fiveQubitCheck_flipSupport]
  exact fiveQubitCheck_zSupportPhase check bits

@[simp]
private theorem fiveQubitCheckPhase_target
    (check : FiveQubitCheckIndex) (bits : Bitstring FiveQubitSite) :
    fiveQubitCheckPhase check (fiveQubitCheckTarget check bits) =
      fiveQubitCheckPhase check bits := by
  fin_cases check <;>
    simp [fiveQubitCheckPhase, fiveQubitCheckTarget, flipAt, zPhase]

set_option maxHeartbeats 1200000 in
/-- Each literal check acts by its advertised two flips and two Z signs. -/
theorem fiveQubitCheck_operator_apply
    (check : FiveQubitCheckIndex) (state : FiveQubitSpace)
    (bits : Bitstring FiveQubitSite) :
    toHermitianQubitOperator (fiveQubitCheck check) state bits =
      fiveQubitCheckPhase check bits *
        state (fiveQubitCheckTarget check bits) := by
  rw [toHermitianQubitOperator_apply, toQubitOperator_apply]
  simp only [hermitianPhaseScalar, fiveQubitCheck_overlapCount,
    pow_zero, one_mul]
  simp [binaryPhaseScalar, fiveQubitCheck_phase,
    fiveQubitCheck_flipSupport, fiveQubitCheck_zSupportPhase_target]

/-- The trivial source syndrome: every measured stabilizer has eigenvalue +1. -/
def fiveQubitPositiveSyndrome : JointSyndrome FiveQubitCheckIndex :=
  fun _ => StabilizerOutcome.positive

/-- The literal all-positive projector of the four concrete checks. -/
noncomputable def fiveQubitPositiveProjector : Operator FiveQubitSpace :=
  jointStabilizerProjector fiveQubitCheck fiveQubitChecks_commute
    fiveQubitPositiveSyndrome

/-- The full physical joint-syndrome measurement before any decoding. -/
def fiveQubitSyndromeInstrument :
    FiniteInstrument (JointSyndrome FiveQubitCheckIndex)
      (JointSyndrome FiveQubitCheckIndex) FiveQubitSpace FiveQubitSpace :=
  jointStabilizerInstrument fiveQubitCheck fiveQubitChecks_commute

/-- The all-positive projector is self-adjoint. -/
theorem fiveQubitPositiveProjector_adjoint :
    LinearMap.adjoint fiveQubitPositiveProjector =
      fiveQubitPositiveProjector := by
  simpa [fiveQubitPositiveProjector] using
    jointStabilizerProjector_adjoint fiveQubitCheck
      fiveQubitChecks_commute fiveQubitPositiveSyndrome

/-- The all-positive projector is idempotent. -/
theorem fiveQubitPositiveProjector_idempotent :
    fiveQubitPositiveProjector * fiveQubitPositiveProjector =
      fiveQubitPositiveProjector := by
  simpa [fiveQubitPositiveProjector] using
    jointStabilizerProjector_idempotent fiveQubitCheck
      fiveQubitChecks_commute fiveQubitPositiveSyndrome

/-- The actual unnormalised source branch retained for decoding. -/
noncomputable def fiveQubitAcceptedRawBranch
    (A : Operator FiveQubitSpace) : Operator FiveQubitSpace :=
  fiveQubitPositiveProjector * A * fiveQubitPositiveProjector

/--
The retained raw branch is exactly the branch derived by the physical joint
stabilizer instrument, not separately supplied protocol data.
-/
theorem fiveQubitSyndromeInstrument_positive_branch
    (A : Operator FiveQubitSpace) :
    fiveQubitSyndromeInstrument.branchOperator
        fiveQubitPositiveSyndrome A =
      fiveQubitAcceptedRawBranch A := by
  simpa [fiveQubitSyndromeInstrument, fiveQubitAcceptedRawBranch,
    fiveQubitPositiveProjector] using
    jointStabilizerInstrument_branchOperator fiveQubitCheck
      fiveQubitChecks_commute fiveQubitPositiveSyndrome A

/--
The physical decision made from a source syndrome. Rejected source states are
discarded here and are not passed to the accepted decoder.
-/
inductive FiveQubitSourceDecision
  | keepForDecode
  | discardBeforeDecode
deriving DecidableEq

/-- Only the all-positive source syndrome reaches the decoder. -/
def fiveQubitSourceDecision
    (syndrome : JointSyndrome FiveQubitCheckIndex) :
    FiveQubitSourceDecision :=
  if syndrome = fiveQubitPositiveSyndrome then
    .keepForDecode
  else
    .discardBeforeDecode

@[simp]
theorem fiveQubitSourceDecision_positive :
    fiveQubitSourceDecision fiveQubitPositiveSyndrome = .keepForDecode := by
  simp [fiveQubitSourceDecision]

theorem fiveQubitSourceDecision_eq_discard_iff
    (syndrome : JointSyndrome FiveQubitCheckIndex) :
    fiveQubitSourceDecision syndrome = .discardBeforeDecode ↔
      syndrome ≠ fiveQubitPositiveSyndrome := by
  simp [fiveQubitSourceDecision]

/--
Map the physical syndrome to the shared protocol's two visible outcomes.
The rejected label is only a technical completion label; it makes no decoded
state claim about any rejected source syndrome.
-/
def fiveQubitTechnicalOutcome
    (syndrome : JointSyndrome FiveQubitCheckIndex) :
    DistillationOutcome :=
  if syndrome = fiveQubitPositiveSyndrome then
    .accepted
  else
    .rejected

/--
The complete source measurement with all nontrivial syndromes grouped under
the shared interface's technical rejected outcome.
-/
def fiveQubitPostselectionInstrument :
    FiniteInstrument (JointSyndrome FiveQubitCheckIndex) DistillationOutcome
      FiveQubitSpace FiveQubitSpace where
  kraus := jointStabilizerKrausFamily fiveQubitCheck fiveQubitChecks_commute
  observe := fiveQubitTechnicalOutcome

/-- The coarse source instrument retains the complete joint-measurement Kraus family. -/
theorem fiveQubitPostselectionInstrument_complete :
    fiveQubitPostselectionInstrument.kraus.Complete := by
  change
    (jointStabilizerKrausFamily fiveQubitCheck
      fiveQubitChecks_commute).Complete
  exact jointStabilizerKrausFamily_complete fiveQubitCheck
    fiveQubitChecks_commute

/-- Five identical noisy resources consume the diagonal input exported by #736. -/
noncomputable def fiveQubitNoisyResources
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    Fin 5 → DensityOperator QubitSpace :=
  fun _ => tDiagonalInput epsilon hzero hone

/--
The raw probability weight of a five-site T-basis error word, built only from
the #736 one-site raw weights. No conditional state is manufactured here.
-/
def fiveQubitWordWeight (epsilon : Real) (word : FiveQubitErrorWord) : Real :=
  ∏ site : FiveQubitSite, tInputWeight epsilon (word site)

/-- Admissible #736 component weights give every five-site word nonnegative weight. -/
theorem fiveQubitWordWeight_nonneg
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (word : FiveQubitErrorWord) :
    0 ≤ fiveQubitWordWeight epsilon word := by
  unfold fiveQubitWordWeight
  exact Finset.prod_nonneg fun site _ =>
    tInputWeight_nonneg epsilon hzero hone (word site)

/-! ## Actual five-fold product preparation -/

/-- Five one-qubit Hilbert spaces, associated in physical site order. -/
abbrev FiveQubitTensor : Type :=
  CompositeSystem QubitSpace
    (CompositeSystem QubitSpace
      (CompositeSystem QubitSpace
        (CompositeSystem QubitSpace QubitSpace)))

/-- Computational-basis labels for the right-associated five-fold tensor. -/
abbrev FiveBitTuple : Type :=
  Fin 2 × (Fin 2 × (Fin 2 × (Fin 2 × Fin 2)))

/-- Reassemble a tensor-basis label as a five-site register bitstring. -/
def fiveTupleBitstring (bits : FiveBitTuple) : Bitstring FiveQubitSite :=
  fun site =>
    match site.1 with
    | 0 => bits.1
    | 1 => bits.2.1
    | 2 => bits.2.2.1
    | 3 => bits.2.2.2.1
    | _ => bits.2.2.2.2

/-- Split a five-site register bitstring in physical site order. -/
def splitFiveBitstring (bits : Bitstring FiveQubitSite) : FiveBitTuple :=
  (bits 0, (bits 1, (bits 2, (bits 3, bits 4))))

@[simp]
theorem splitFiveBitstring_fiveTupleBitstring (bits : FiveBitTuple) :
    splitFiveBitstring (fiveTupleBitstring bits) = bits := by
  rcases bits with ⟨b0, b1, b2, b3, b4⟩
  rfl

@[simp]
theorem fiveTupleBitstring_splitFiveBitstring
    (bits : Bitstring FiveQubitSite) :
    fiveTupleBitstring (splitFiveBitstring bits) = bits := by
  funext site
  fin_cases site <;> rfl

/-- The concrete equivalence between tensor and register computational labels. -/
def fiveBitstringEquiv : FiveBitTuple ≃ Bitstring FiveQubitSite where
  toFun := fiveTupleBitstring
  invFun := splitFiveBitstring
  left_inv := splitFiveBitstring_fiveTupleBitstring
  right_inv := fiveTupleBitstring_splitFiveBitstring

/-- The explicit basis-preserving unitary from five tensor factors to Fin-5. -/
noncomputable def fiveTensorRegisterTransport :
    UnitaryTransport FiveQubitTensor FiveQubitSpace := by
  let oneBasis := EuclideanSpace.basisFun (Fin 2) Complex
  let sourceBasis :=
    oneBasis.tensorProduct
      (oneBasis.tensorProduct
        (oneBasis.tensorProduct
          (oneBasis.tensorProduct oneBasis)))
  let targetBasis :=
    EuclideanSpace.basisFun (Bitstring FiveQubitSite) Complex
  let U := sourceBasis.equiv targetBasis fiveBitstringEquiv
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

@[simp]
theorem fiveTensorRegisterTransport_apply_basis
    (b0 b1 b2 b3 b4 : Fin 2) :
    fiveTensorRegisterTransport
        (EuclideanSpace.basisFun (Fin 2) Complex b0 ⊗ₜ[Complex]
          (EuclideanSpace.basisFun (Fin 2) Complex b1 ⊗ₜ[Complex]
            (EuclideanSpace.basisFun (Fin 2) Complex b2 ⊗ₜ[Complex]
              (EuclideanSpace.basisFun (Fin 2) Complex b3 ⊗ₜ[Complex]
                EuclideanSpace.basisFun (Fin 2) Complex b4)))) =
      EuclideanSpace.basisFun (Bitstring FiveQubitSite) Complex
        (fiveTupleBitstring (b0, b1, b2, b3, b4)) := by
  dsimp [fiveTensorRegisterTransport]
  rw [← OrthonormalBasis.tensorProduct_apply
    (EuclideanSpace.basisFun (Fin 2) Complex)
    (EuclideanSpace.basisFun (Fin 2) Complex) b3 b4]
  rw [← OrthonormalBasis.tensorProduct_apply
    (EuclideanSpace.basisFun (Fin 2) Complex)
    ((EuclideanSpace.basisFun (Fin 2) Complex).tensorProduct
      (EuclideanSpace.basisFun (Fin 2) Complex)) b2 (b3, b4)]
  rw [← OrthonormalBasis.tensorProduct_apply
    (EuclideanSpace.basisFun (Fin 2) Complex)
    ((EuclideanSpace.basisFun (Fin 2) Complex).tensorProduct
      ((EuclideanSpace.basisFun (Fin 2) Complex).tensorProduct
        (EuclideanSpace.basisFun (Fin 2) Complex))) b1 (b2, b3, b4)]
  rw [← OrthonormalBasis.tensorProduct_apply
    (EuclideanSpace.basisFun (Fin 2) Complex)
    ((EuclideanSpace.basisFun (Fin 2) Complex).tensorProduct
      ((EuclideanSpace.basisFun (Fin 2) Complex).tensorProduct
        ((EuclideanSpace.basisFun (Fin 2) Complex).tensorProduct
          (EuclideanSpace.basisFun (Fin 2) Complex)))) b0 (b1, b2, b3, b4)]
  rw [OrthonormalBasis.equiv_apply_basis]
  rfl

@[simp]
theorem fiveTensorRegisterTransport_symm_apply_basis
    (bits : Bitstring FiveQubitSite) :
    fiveTensorRegisterTransport.symm
        (EuclideanSpace.basisFun (Bitstring FiveQubitSite) Complex bits) =
      EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
        (EuclideanSpace.basisFun (Fin 2) Complex (bits 1) ⊗ₜ[Complex]
          (EuclideanSpace.basisFun (Fin 2) Complex (bits 2) ⊗ₜ[Complex]
            (EuclideanSpace.basisFun (Fin 2) Complex (bits 3) ⊗ₜ[Complex]
              EuclideanSpace.basisFun (Fin 2) Complex (bits 4)))) := by
  apply fiveTensorRegisterTransport.toLinearEquiv.injective
  simp only [UnitaryTransport.symm]
  rw [fiveTensorRegisterTransport.toLinearEquiv.apply_symm_apply]
  rw [fiveTensorRegisterTransport_apply_basis]
  exact congrArg
    (EuclideanSpace.basisFun (Bitstring FiveQubitSite) Complex)
    (fiveTupleBitstring_splitFiveBitstring bits).symm

/-- The genuine tensor product of five arbitrary one-qubit resource densities. -/
noncomputable def fiveQubitTensorDensity
    (inputs : Fin 5 → DensityOperator QubitSpace) :
    DensityOperator FiveQubitTensor :=
  DensityOperator.tensorDensity (inputs 0)
    (DensityOperator.tensorDensity (inputs 1)
      (DensityOperator.tensorDensity (inputs 2)
        (DensityOperator.tensorDensity (inputs 3) (inputs 4))))

/--
Prepare the actual Fin-5 register product density by transporting the genuine
five-fold tensor product in physical site order.
-/
noncomputable def fiveQubitPrepareInput
    (inputs : Fin 5 → DensityOperator QubitSpace) :
    DensityOperator FiveQubitSpace :=
  fiveTensorRegisterTransport.conjDensity (fiveQubitTensorDensity inputs)

@[simp]
theorem fiveQubitPrepareInput_noisyResources
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    fiveQubitPrepareInput (fiveQubitNoisyResources epsilon hzero hone) =
      fiveTensorRegisterTransport.conjDensity
        (DensityOperator.tensorDensity (tDiagonalInput epsilon hzero hone)
          (DensityOperator.tensorDensity (tDiagonalInput epsilon hzero hone)
            (DensityOperator.tensorDensity (tDiagonalInput epsilon hzero hone)
              (DensityOperator.tensorDensity (tDiagonalInput epsilon hzero hone)
                (tDiagonalInput epsilon hzero hone))))) :=
  rfl

/-! ## Coherent code-space extraction -/

/-- The computational orthonormal basis of the Fin-5 physical register. -/
noncomputable def fiveQubitComputationalBasis :
    OrthonormalBasis (Bitstring FiveQubitSite) Complex FiveQubitSpace :=
  EuclideanSpace.basisFun (Bitstring FiveQubitSite) Complex

@[simp]
private theorem fiveQubitComputationalBasis_inner
    (bits : Bitstring FiveQubitSite) (state : FiveQubitSpace) :
    inner Complex (fiveQubitComputationalBasis bits) state = state bits := by
  simpa [fiveQubitComputationalBasis] using
    (EuclideanSpace.basisFun_inner
      (Bitstring FiveQubitSite) Complex state bits)

@[simp]
private theorem fiveQubitComputationalBasis_apply
    (input output : Bitstring FiveQubitSite) :
    (fiveQubitComputationalBasis input).ofLp output =
      if output = input then 1 else 0 := by
  simp [fiveQubitComputationalBasis, EuclideanSpace.basisFun_apply,
    PiLp.single_apply]

/-- The all-zero computational word. -/
def fiveQubitAllZero : Bitstring FiveQubitSite := fun _ => 0

/-- The all-one computational word. -/
def fiveQubitAllOne : Bitstring FiveQubitSite := fun _ => 1

@[simp]
private theorem fiveQubitAllZero_ne_allOne :
    fiveQubitAllZero ≠ fiveQubitAllOne := by
  native_decide

/--
The first normalized logical computational codeword, obtained by applying the
literal all-positive projector to the all-zero anchor.
-/
noncomputable def fiveQubitLogicalZero : FiveQubitSpace :=
  (4 : Complex) •
    fiveQubitPositiveProjector
      (fiveQubitComputationalBasis fiveQubitAllZero)

/--
The second normalized logical computational codeword, obtained from the
all-one anchor in the opposite logical-Z sector.
-/
noncomputable def fiveQubitLogicalOne : FiveQubitSpace :=
  (4 : Complex) •
    fiveQubitPositiveProjector
      (fiveQubitComputationalBasis fiveQubitAllOne)

private theorem fiveQubitPositiveProjector_eq_four_factors :
    fiveQubitPositiveProjector =
      jointStabilizerFactor fiveQubitCheck fiveQubitPositiveSyndrome 0 *
      (jointStabilizerFactor fiveQubitCheck fiveQubitPositiveSyndrome 1 *
      (jointStabilizerFactor fiveQubitCheck fiveQubitPositiveSyndrome 2 *
       jointStabilizerFactor fiveQubitCheck fiveQubitPositiveSyndrome 3)) := by
  unfold fiveQubitPositiveProjector jointStabilizerProjector
  classical
  simp only [show (Finset.univ : Finset FiveQubitCheckIndex) =
      {0, 1, 2, 3} by decide]
  erw [Finset.noncommProd_insert_of_notMem _ _ _ _ (by decide),
    Finset.noncommProd_insert_of_notMem _ _ _ _ (by decide),
    Finset.noncommProd_insert_of_notMem _ _ _ _ (by decide),
    Finset.noncommProd_singleton]

/-- Explicit computational coordinates of the first normalized codeword. -/
def fiveQubitLogicalZeroAmplitude : FiveBitTuple → Complex
  | (0, 0, 0, 0, 0) => 1 / 4
  | (0, 0, 0, 1, 1) => -1 / 4
  | (0, 0, 1, 0, 1) => 1 / 4
  | (0, 0, 1, 1, 0) => -1 / 4
  | (0, 1, 0, 0, 1) => 1 / 4
  | (0, 1, 0, 1, 0) => 1 / 4
  | (0, 1, 1, 0, 0) => -1 / 4
  | (0, 1, 1, 1, 1) => -1 / 4
  | (1, 0, 0, 0, 1) => -1 / 4
  | (1, 0, 0, 1, 0) => 1 / 4
  | (1, 0, 1, 0, 0) => 1 / 4
  | (1, 0, 1, 1, 1) => -1 / 4
  | (1, 1, 0, 0, 0) => -1 / 4
  | (1, 1, 0, 1, 1) => -1 / 4
  | (1, 1, 1, 0, 1) => -1 / 4
  | (1, 1, 1, 1, 0) => -1 / 4
  | _ => 0

set_option maxHeartbeats 2000000 in
@[simp]
theorem fiveQubitLogicalZero_apply_tuple (bits : FiveBitTuple) :
    fiveQubitLogicalZero (fiveTupleBitstring bits) =
      fiveQubitLogicalZeroAmplitude bits := by
  rcases bits with ⟨b0, b1, b2, b3, b4⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;>
    fin_cases b3 <;> fin_cases b4 <;>
    simp +decide [fiveQubitLogicalZeroAmplitude, fiveQubitLogicalZero,
      fiveQubitPositiveProjector_eq_four_factors,
      jointStabilizerFactor, stabilizerProjector,
      fiveQubitPositiveSyndrome, fiveQubitAllZero,
      fiveQubitCheckTarget, fiveQubitCheckPhase,
      fiveTupleBitstring, flipAt, zPhase,
      StabilizerOutcome.sign, Module.End.mul_apply] <;>
    norm_num

/-- Explicit computational coordinates of the second normalized codeword. -/
def fiveQubitLogicalOneAmplitude : FiveBitTuple → Complex
  | (0, 0, 0, 0, 1) => -1 / 4
  | (0, 0, 0, 1, 0) => -1 / 4
  | (0, 0, 1, 0, 0) => -1 / 4
  | (0, 0, 1, 1, 1) => -1 / 4
  | (0, 1, 0, 0, 0) => -1 / 4
  | (0, 1, 0, 1, 1) => 1 / 4
  | (0, 1, 1, 0, 1) => 1 / 4
  | (0, 1, 1, 1, 0) => -1 / 4
  | (1, 0, 0, 0, 0) => -1 / 4
  | (1, 0, 0, 1, 1) => -1 / 4
  | (1, 0, 1, 0, 1) => 1 / 4
  | (1, 0, 1, 1, 0) => 1 / 4
  | (1, 1, 0, 0, 1) => -1 / 4
  | (1, 1, 0, 1, 0) => 1 / 4
  | (1, 1, 1, 0, 0) => -1 / 4
  | (1, 1, 1, 1, 1) => 1 / 4
  | _ => 0

set_option maxHeartbeats 2000000 in
@[simp]
theorem fiveQubitLogicalOne_apply_tuple (bits : FiveBitTuple) :
    fiveQubitLogicalOne (fiveTupleBitstring bits) =
      fiveQubitLogicalOneAmplitude bits := by
  rcases bits with ⟨b0, b1, b2, b3, b4⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;>
    fin_cases b3 <;> fin_cases b4 <;>
    simp +decide [fiveQubitLogicalOneAmplitude, fiveQubitLogicalOne,
      fiveQubitPositiveProjector_eq_four_factors,
      jointStabilizerFactor, stabilizerProjector,
      fiveQubitPositiveSyndrome, fiveQubitAllOne,
      fiveQubitCheckTarget, fiveQubitCheckPhase,
      fiveTupleBitstring, flipAt, zPhase,
      StabilizerOutcome.sign, Module.End.mul_apply] <;>
    norm_num

private theorem fiveQubitPositiveProjector_isSymmetricProjection :
    fiveQubitPositiveProjector.IsSymmetricProjection := by
  refine ⟨fiveQubitPositiveProjector_idempotent, ?_⟩
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
  exact fiveQubitPositiveProjector_adjoint

private theorem fiveQubitPositiveProjector_inner
    (left right : FiveQubitSpace) :
    inner Complex (fiveQubitPositiveProjector left)
        (fiveQubitPositiveProjector right) =
      inner Complex left (fiveQubitPositiveProjector right) := by
  calc
    inner Complex (fiveQubitPositiveProjector left)
        (fiveQubitPositiveProjector right) =
      inner Complex left
        (fiveQubitPositiveProjector
          (fiveQubitPositiveProjector right)) := by
            simpa [fiveQubitPositiveProjector_adjoint] using
              (LinearMap.adjoint_inner_right (𝕜 := Complex)
                fiveQubitPositiveProjector left
                (fiveQubitPositiveProjector right)).symm
    _ = inner Complex left (fiveQubitPositiveProjector right) := by
      have hidempotent := congrArg
        (fun operator : Operator FiveQubitSpace => operator right)
        fiveQubitPositiveProjector_idempotent
      simpa [Module.End.mul_apply] using
        congrArg (fun value : FiveQubitSpace => inner Complex left value)
          hidempotent

private theorem fiveQubitPositiveProjector_anchor_zero :
    inner Complex
        (fiveQubitComputationalBasis fiveQubitAllZero)
        (fiveQubitPositiveProjector
          (fiveQubitComputationalBasis fiveQubitAllZero)) =
      (1 / 16 : Complex) := by
  unfold fiveQubitComputationalBasis
  rw [EuclideanSpace.basisFun_inner]
  rw [fiveQubitPositiveProjector_eq_four_factors]
  simp +decide [fiveQubitAllZero,
    jointStabilizerFactor, stabilizerProjector,
    fiveQubitPositiveSyndrome, fiveQubitCheck_operator_apply,
    fiveQubitCheckTarget, fiveQubitCheckPhase, flipAt, zPhase,
    Module.End.mul_apply]
  norm_num

private theorem fiveQubitPositiveProjector_anchor_one :
    inner Complex
        (fiveQubitComputationalBasis fiveQubitAllOne)
        (fiveQubitPositiveProjector
          (fiveQubitComputationalBasis fiveQubitAllOne)) =
      (1 / 16 : Complex) := by
  unfold fiveQubitComputationalBasis
  rw [EuclideanSpace.basisFun_inner]
  rw [fiveQubitPositiveProjector_eq_four_factors]
  simp +decide [fiveQubitAllOne,
    jointStabilizerFactor, stabilizerProjector,
    fiveQubitPositiveSyndrome, fiveQubitCheck_operator_apply,
    fiveQubitCheckTarget, fiveQubitCheckPhase, flipAt, zPhase,
    Module.End.mul_apply]
  norm_num

private theorem fiveQubitPositiveProjector_anchor_cross :
    inner Complex
        (fiveQubitComputationalBasis fiveQubitAllZero)
        (fiveQubitPositiveProjector
          (fiveQubitComputationalBasis fiveQubitAllOne)) =
      0 := by
  unfold fiveQubitComputationalBasis
  rw [EuclideanSpace.basisFun_inner]
  rw [fiveQubitPositiveProjector_eq_four_factors]
  simp +decide [fiveQubitAllZero, fiveQubitAllOne,
    jointStabilizerFactor, stabilizerProjector,
    fiveQubitPositiveSyndrome, fiveQubitCheck_operator_apply,
    fiveQubitCheckTarget, fiveQubitCheckPhase, flipAt, zPhase,
    Module.End.mul_apply]

@[simp]
theorem fiveQubitLogicalZero_inner_self :
    inner Complex fiveQubitLogicalZero fiveQubitLogicalZero = 1 := by
  rw [fiveQubitLogicalZero, inner_smul_left, inner_smul_right,
    fiveQubitPositiveProjector_inner,
    fiveQubitPositiveProjector_anchor_zero]
  norm_num [map_ofNat]

@[simp]
theorem fiveQubitLogicalOne_inner_self :
    inner Complex fiveQubitLogicalOne fiveQubitLogicalOne = 1 := by
  rw [fiveQubitLogicalOne, inner_smul_left, inner_smul_right,
    fiveQubitPositiveProjector_inner,
    fiveQubitPositiveProjector_anchor_one]
  norm_num [map_ofNat]

@[simp]
theorem fiveQubitLogicalZero_inner_one :
    inner Complex fiveQubitLogicalZero fiveQubitLogicalOne = 0 := by
  rw [fiveQubitLogicalZero, fiveQubitLogicalOne,
    inner_smul_left, inner_smul_right,
    fiveQubitPositiveProjector_inner,
    fiveQubitPositiveProjector_anchor_cross]
  norm_num [map_ofNat]

@[simp]
theorem fiveQubitLogicalOne_inner_zero :
    inner Complex fiveQubitLogicalOne fiveQubitLogicalZero = 0 := by
  calc
    inner Complex fiveQubitLogicalOne fiveQubitLogicalZero =
        star (inner Complex fiveQubitLogicalZero fiveQubitLogicalOne) := by
          exact
            (inner_conj_symm
              (𝕜 := Complex)
              fiveQubitLogicalOne fiveQubitLogicalZero).symm
    _ = 0 := by simp

@[simp]
theorem fiveQubitLogicalZero_norm : ‖fiveQubitLogicalZero‖ = 1 := by
  have hsquare : ‖fiveQubitLogicalZero‖ ^ 2 = 1 := by
    rw [@InnerProductSpace.norm_sq_eq_re_inner Complex,
      fiveQubitLogicalZero_inner_self]
    norm_num
  nlinarith [norm_nonneg fiveQubitLogicalZero]

@[simp]
theorem fiveQubitLogicalOne_norm : ‖fiveQubitLogicalOne‖ = 1 := by
  have hsquare : ‖fiveQubitLogicalOne‖ ^ 2 = 1 := by
    rw [@InnerProductSpace.norm_sq_eq_re_inner Complex,
      fiveQubitLogicalOne_inner_self]
    norm_num
  nlinarith [norm_nonneg fiveQubitLogicalOne]

@[simp]
theorem fiveQubitPositiveProjector_logicalZero :
    fiveQubitPositiveProjector fiveQubitLogicalZero =
      fiveQubitLogicalZero := by
  unfold fiveQubitLogicalZero
  rw [map_smul]
  congr 1
  change
      ((fiveQubitPositiveProjector * fiveQubitPositiveProjector)
        (fiveQubitComputationalBasis fiveQubitAllZero)) =
      fiveQubitPositiveProjector
        (fiveQubitComputationalBasis fiveQubitAllZero)
  rw [fiveQubitPositiveProjector_idempotent]

@[simp]
theorem fiveQubitPositiveProjector_logicalOne :
    fiveQubitPositiveProjector fiveQubitLogicalOne =
      fiveQubitLogicalOne := by
  unfold fiveQubitLogicalOne
  rw [map_smul]
  congr 1
  change
      ((fiveQubitPositiveProjector * fiveQubitPositiveProjector)
        (fiveQubitComputationalBasis fiveQubitAllOne)) =
      fiveQubitPositiveProjector
        (fiveQubitComputationalBasis fiveQubitAllOne)
  rw [fiveQubitPositiveProjector_idempotent]

/-- The rank-two projector spanned by the two concrete logical codewords. -/
noncomputable def fiveQubitLogicalProjector : Operator FiveQubitSpace :=
  (InnerProductSpace.rankOne Complex
    fiveQubitLogicalZero fiveQubitLogicalZero).toLinearMap +
  (InnerProductSpace.rankOne Complex
    fiveQubitLogicalOne fiveQubitLogicalOne).toLinearMap

private theorem fiveQubitLogicalProjector_isSymmetricProjection :
    fiveQubitLogicalProjector.IsSymmetricProjection := by
  refine ⟨?_, ?_⟩
  · apply LinearMap.ext
    intro state
    simp [fiveQubitLogicalProjector, Module.End.mul_apply,
      InnerProductSpace.rankOne_apply, mul_add, add_mul]
  · unfold fiveQubitLogicalProjector
    exact LinearMap.IsSymmetric.add
      (InnerProductSpace.isSymmetricProjection_rankOne_self
        (𝕜 := Complex) fiveQubitLogicalZero_norm).isSymmetric
      (InnerProductSpace.isSymmetricProjection_rankOne_self
        (𝕜 := Complex) fiveQubitLogicalOne_norm).isSymmetric

private theorem fiveQubitLogicalProjector_range_le :
    LinearMap.range fiveQubitLogicalProjector ≤
      LinearMap.range fiveQubitPositiveProjector := by
  intro state hstate
  rcases hstate with ⟨source, rfl⟩
  refine ⟨fiveQubitLogicalProjector source, ?_⟩
  simp [fiveQubitLogicalProjector, InnerProductSpace.rankOne_apply]

private theorem positiveOperator_eq_zero_of_trace_eq_zero
    {A : Operator FiveQubitSpace} (hA : LinearMap.IsPositive A)
    (htrace : LinearMap.trace Complex FiveQubitSpace A = 0) :
    A = 0 := by
  classical
  let basis := stdOrthonormalBasis Complex FiveQubitSpace
  have hmatrix :
      (LinearMap.toMatrix basis.toBasis basis.toBasis A).PosSemidef :=
    (LinearMap.posSemidef_toMatrix_iff basis).2 hA
  have hmatrixTrace :
      Matrix.trace (LinearMap.toMatrix basis.toBasis basis.toBasis A) = 0 := by
    rw [← LinearMap.trace_eq_matrix_trace Complex basis.toBasis]
    exact htrace
  apply (LinearMap.toMatrix basis.toBasis basis.toBasis).injective
  simpa using (hmatrix.trace_eq_zero_iff).1 hmatrixTrace

set_option maxHeartbeats 1600000 in
private theorem fiveQubitPositiveProjector_trace :
    LinearMap.trace Complex FiveQubitSpace fiveQubitPositiveProjector = 2 := by
  rw [LinearMap.trace_eq_sum_inner
    fiveQubitPositiveProjector fiveQubitComputationalBasis]
  rw [← Equiv.sum_comp fiveBitstringEquiv]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [fiveQubitPositiveProjector_eq_four_factors]
  simp only [jointStabilizerFactor, stabilizerProjector,
    Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
    Module.End.one_apply]
  simp +decide [fiveQubitComputationalBasis_inner,
    fiveQubitPositiveSyndrome,
    fiveQubitCheck_operator_apply,
    fiveQubitCheckTarget, fiveQubitCheckPhase, fiveTupleBitstring,
    fiveBitstringEquiv, flipAt, zPhase,
    Module.End.mul_apply]
  norm_num

/--
The two explicit projected anchors resolve the complete all-positive code
projector. The proof uses its rank-two trace after checking the anchors, not a
stored decoder assumption.
-/
theorem fiveQubitPositiveProjector_eq_logicalBasis :
    fiveQubitPositiveProjector = fiveQubitLogicalProjector := by
  have hcomplement :
      (fiveQubitPositiveProjector -
        fiveQubitLogicalProjector).IsSymmetricProjection :=
    fiveQubitLogicalProjector_isSymmetricProjection.sub_of_range_le_range
      fiveQubitPositiveProjector_isSymmetricProjection
      fiveQubitLogicalProjector_range_le
  have htrace :
      LinearMap.trace Complex FiveQubitSpace
          (fiveQubitPositiveProjector - fiveQubitLogicalProjector) = 0 := by
    rw [map_sub, fiveQubitPositiveProjector_trace]
    simp [fiveQubitLogicalProjector, map_add,
      InnerProductSpace.trace_rankOne]
    norm_num
  have hzero := positiveOperator_eq_zero_of_trace_eq_zero
    hcomplement.isPositive htrace
  exact sub_eq_zero.mp hzero

/-! ## Coherent logical decoding and technical completion -/

/-- The output computational basis used by the coherent code decoder. -/
noncomputable def qubitComputationalBasis :
    OrthonormalBasis (Fin 2) Complex QubitSpace :=
  EuclideanSpace.basisFun (Fin 2) Complex

@[simp]
private theorem qubitComputationalBasis_inner (left right : Fin 2) :
    inner Complex (qubitComputationalBasis left)
        (qubitComputationalBasis right) =
      if left = right then 1 else 0 :=
  qubitComputationalBasis.inner_eq_ite left right

@[simp]
private theorem qubitComputationalBasis_inner_state
    (bit : Fin 2) (state : QubitSpace) :
    inner Complex (qubitComputationalBasis bit) state = state bit := by
  simpa [qubitComputationalBasis] using
    (EuclideanSpace.basisFun_inner (Fin 2) Complex state bit)

private theorem qubitOperator_ext_matrixEntry
    {A B : Operator QubitSpace}
    (hentry : ∀ output input : Fin 2,
      inner Complex (qubitComputationalBasis output)
          (A (qubitComputationalBasis input)) =
        inner Complex (qubitComputationalBasis output)
          (B (qubitComputationalBasis input))) :
    A = B := by
  apply LinearMap.ext
  intro state
  rw [← qubitComputationalBasis.sum_repr' state]
  simp only [map_sum, map_smul]
  apply qubitComputationalBasis.repr.injective
  ext output
  simp only [OrthonormalBasis.repr_apply_apply, inner_sum,
    inner_smul_right]
  apply Finset.sum_congr rfl
  intro input _hinput
  rw [hentry output input]

private theorem qubitDensityOperator_ext
    {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) :
    rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl

/-- One-site matrix entries of the #736 diagonal input in the physical basis. -/
def tDiagonalMatrixEntry
    (epsilon : Real) (output input : Fin 2) : Complex :=
  let d : Complex := ((1 - 2 * epsilon) * (Real.sqrt 3)⁻¹ : Real)
  match output, input with
  | 0, 0 => (1 + d) / 2
  | 0, 1 => d * (1 - Complex.I) / 2
  | 1, 0 => d * (1 + Complex.I) / 2
  | 1, 1 => (1 - d) / 2

@[simp]
private theorem tDiagonalInput_matrixEntry
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (output input : Fin 2) :
    inner Complex (qubitComputationalBasis output)
        ((tDiagonalInput epsilon hzero hone).toOperator
          (qubitComputationalBasis input)) =
      tDiagonalMatrixEntry epsilon output input := by
  rw [tDiagonalInput_toOperator_eq_blochProjector]
  rw [qubitComputationalBasis_inner_state]
  fin_cases output <;> fin_cases input <;>
    simp [tDiagonalMatrixEntry, qubitComputationalBasis,
      blochProjector, blochOperator_apply_zero,
      blochOperator_apply_one, tDiagonalBloch] <;>
    ring

private theorem fiveQubitPrepareInput_matrixEntry
    (inputs : Fin 5 → DensityOperator QubitSpace)
    (output input : Bitstring FiveQubitSite) :
    inner Complex (fiveQubitComputationalBasis output)
        ((fiveQubitPrepareInput inputs).toOperator
          (fiveQubitComputationalBasis input)) =
      inner Complex (qubitComputationalBasis (output 0))
          ((inputs 0).toOperator (qubitComputationalBasis (input 0))) *
      inner Complex (qubitComputationalBasis (output 1))
          ((inputs 1).toOperator (qubitComputationalBasis (input 1))) *
      inner Complex (qubitComputationalBasis (output 2))
          ((inputs 2).toOperator (qubitComputationalBasis (input 2))) *
      inner Complex (qubitComputationalBasis (output 3))
          ((inputs 3).toOperator (qubitComputationalBasis (input 3))) *
      inner Complex (qubitComputationalBasis (output 4))
          ((inputs 4).toOperator (qubitComputationalBasis (input 4))) := by
  have houtput :
      fiveQubitComputationalBasis output =
        fiveTensorRegisterTransport
          (qubitComputationalBasis (output 0) ⊗ₜ[Complex]
            (qubitComputationalBasis (output 1) ⊗ₜ[Complex]
              (qubitComputationalBasis (output 2) ⊗ₜ[Complex]
                (qubitComputationalBasis (output 3) ⊗ₜ[Complex]
                  qubitComputationalBasis (output 4))))) := by
    unfold fiveQubitComputationalBasis qubitComputationalBasis
    symm
    rw [fiveTensorRegisterTransport_apply_basis]
    congr 1
    exact fiveTupleBitstring_splitFiveBitstring output
  have hinput :
      fiveTensorRegisterTransport.symm
          (fiveQubitComputationalBasis input) =
        qubitComputationalBasis (input 0) ⊗ₜ[Complex]
          (qubitComputationalBasis (input 1) ⊗ₜ[Complex]
            (qubitComputationalBasis (input 2) ⊗ₜ[Complex]
              (qubitComputationalBasis (input 3) ⊗ₜ[Complex]
                qubitComputationalBasis (input 4)))) := by
    simpa [fiveQubitComputationalBasis, qubitComputationalBasis] using
      fiveTensorRegisterTransport_symm_apply_basis input
  rw [fiveQubitPrepareInput, UnitaryTransport.conjDensity_toOperator]
  change inner Complex (fiveQubitComputationalBasis output)
      (fiveTensorRegisterTransport
        ((fiveQubitTensorDensity inputs).toOperator
          (fiveTensorRegisterTransport.symm
            (fiveQubitComputationalBasis input)))) = _
  rw [houtput, hinput, fiveTensorRegisterTransport.map_inner]
  simp [fiveQubitTensorDensity, DensityOperator.tensorDensity_toOperator,
    TensorProduct.map_tmul, TensorProduct.inner_tmul]
  ring

private theorem fiveQubit_inner_operator_eq_sum
    (left right : FiveQubitSpace) (A : Operator FiveQubitSpace) :
    inner Complex left (A right) =
      ∑ output : Bitstring FiveQubitSite,
        ∑ input : Bitstring FiveQubitSite,
          star (left output) *
            inner Complex (fiveQubitComputationalBasis output)
              (A (fiveQubitComputationalBasis input)) *
            right input := by
  calc
    inner Complex left (A right) =
        inner Complex
          (∑ output : Bitstring FiveQubitSite,
            inner Complex (fiveQubitComputationalBasis output) left •
              fiveQubitComputationalBasis output)
          (A (∑ input : Bitstring FiveQubitSite,
            inner Complex (fiveQubitComputationalBasis input) right •
              fiveQubitComputationalBasis input)) := by
            rw [fiveQubitComputationalBasis.sum_repr',
              fiveQubitComputationalBasis.sum_repr']
    _ = _ := by
      simp only [map_sum, map_smul, sum_inner, inner_sum,
        inner_smul_left, inner_smul_right,
        fiveQubitComputationalBasis_inner]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro output _houtput
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro input _hinput
      simp only [starRingEnd_apply]
      ring

/--
The coherent code-space extraction map. It sends the two explicit logical
codewords to the corresponding one-qubit computational basis vectors and is
zero on the orthogonal complement.
-/
noncomputable def fiveQubitLogicalDecoderOperator :
    FiveQubitSpace →ₗ[Complex] QubitSpace :=
  (InnerProductSpace.rankOne Complex
    (qubitComputationalBasis 0) fiveQubitLogicalZero).toLinearMap +
  (InnerProductSpace.rankOne Complex
    (qubitComputationalBasis 1) fiveQubitLogicalOne).toLinearMap

@[simp]
theorem fiveQubitLogicalDecoderOperator_logicalZero :
    fiveQubitLogicalDecoderOperator fiveQubitLogicalZero =
      qubitComputationalBasis 0 := by
  simp [fiveQubitLogicalDecoderOperator,
    InnerProductSpace.rankOne_apply]

@[simp]
theorem fiveQubitLogicalDecoderOperator_logicalOne :
    fiveQubitLogicalDecoderOperator fiveQubitLogicalOne =
      qubitComputationalBasis 1 := by
  simp [fiveQubitLogicalDecoderOperator,
    InnerProductSpace.rankOne_apply]

private theorem adjoint_rankOne_output_logical
    (output : QubitSpace) (logical : FiveQubitSpace) :
    LinearMap.adjoint
        (InnerProductSpace.rankOne Complex output logical).toLinearMap =
      (InnerProductSpace.rankOne Complex logical output).toLinearMap := by
  rw [LinearMap.adjoint_eq_toCLM_adjoint]
  exact congrArg ContinuousLinearMap.toLinearMap
    (InnerProductSpace.adjoint_rankOne (𝕜 := Complex) output logical)

/-- The coherent decoder's accepted effect is exactly the physical code projector. -/
theorem fiveQubitLogicalDecoderOperator_adjoint_comp :
    (LinearMap.adjoint fiveQubitLogicalDecoderOperator).comp
        fiveQubitLogicalDecoderOperator =
      fiveQubitPositiveProjector := by
  rw [fiveQubitPositiveProjector_eq_logicalBasis]
  unfold fiveQubitLogicalDecoderOperator
  rw [map_add, adjoint_rankOne_output_logical,
    adjoint_rankOne_output_logical]
  apply LinearMap.ext
  intro state
  simp [fiveQubitLogicalProjector,
    LinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    inner_add_right, inner_smul_right]

/-- The orthogonal complement of the accepted code space. -/
noncomputable def fiveQubitRejectedProjection : Operator FiveQubitSpace :=
  1 - fiveQubitPositiveProjector

private theorem fiveQubitRejectedProjection_adjoint :
    LinearMap.adjoint fiveQubitRejectedProjection =
      fiveQubitRejectedProjection := by
  simp [fiveQubitRejectedProjection, fiveQubitPositiveProjector_adjoint]

private theorem fiveQubitRejectedProjection_idempotent :
    fiveQubitRejectedProjection * fiveQubitRejectedProjection =
      fiveQubitRejectedProjection := by
  apply LinearMap.ext
  intro state
  have hproject := congrArg
    (fun operator : Operator FiveQubitSpace => operator state)
    fiveQubitPositiveProjector_idempotent
  simp only [Module.End.mul_apply] at hproject
  simp [fiveQubitRejectedProjection, hproject]

/--
A rejected-complement branch records one physical basis coordinate in a fixed
technical output vector. It does not apply the accepted logical decoder.
-/
noncomputable def fiveQubitTechnicalRejectOperator
    (bits : Bitstring FiveQubitSite) :
    FiveQubitSpace →ₗ[Complex] QubitSpace :=
  (InnerProductSpace.rankOne Complex
    (qubitComputationalBasis 0)
    (fiveQubitRejectedProjection (fiveQubitComputationalBasis bits))).toLinearMap

private theorem fiveQubitTechnicalRejectOperator_adjoint_comp
    (bits : Bitstring FiveQubitSite) :
    (LinearMap.adjoint (fiveQubitTechnicalRejectOperator bits)).comp
        (fiveQubitTechnicalRejectOperator bits) =
      (InnerProductSpace.rankOne Complex
        (fiveQubitRejectedProjection (fiveQubitComputationalBasis bits))
        (fiveQubitRejectedProjection
          (fiveQubitComputationalBasis bits))).toLinearMap := by
  unfold fiveQubitTechnicalRejectOperator
  rw [adjoint_rankOne_output_logical]
  apply LinearMap.ext
  intro state
  simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    inner_smul_right]

private theorem fiveQubitRejectedProjection_sum_rankOne :
    (∑ bits : Bitstring FiveQubitSite,
      (InnerProductSpace.rankOne Complex
        (fiveQubitRejectedProjection (fiveQubitComputationalBasis bits))
        (fiveQubitRejectedProjection
          (fiveQubitComputationalBasis bits))).toLinearMap) =
      fiveQubitRejectedProjection := by
  apply LinearMap.ext
  intro state
  simp only [LinearMap.sum_apply, InnerProductSpace.rankOne_apply]
  calc
    (∑ bits : Bitstring FiveQubitSite,
        inner Complex
            (fiveQubitRejectedProjection (fiveQubitComputationalBasis bits))
            state •
          fiveQubitRejectedProjection (fiveQubitComputationalBasis bits)) =
        fiveQubitRejectedProjection
          (∑ bits : Bitstring FiveQubitSite,
            inner Complex (fiveQubitComputationalBasis bits)
                (fiveQubitRejectedProjection state) •
              fiveQubitComputationalBasis bits) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro bits _hbits
      rw [map_smul]
      congr 1
      simpa [fiveQubitRejectedProjection_adjoint] using
        (LinearMap.adjoint_inner_right (𝕜 := Complex)
          fiveQubitRejectedProjection
          (fiveQubitComputationalBasis bits) state).symm
    _ = fiveQubitRejectedProjection (fiveQubitRejectedProjection state) := by
      rw [fiveQubitComputationalBasis.sum_repr']
    _ = fiveQubitRejectedProjection state := by
      have hidempotent := congrArg
        (fun operator : Operator FiveQubitSpace => operator state)
        fiveQubitRejectedProjection_idempotent
      simpa [Module.End.mul_apply] using hidempotent

/-- Internal Kraus indices: one accepted decoder and basis-indexed rejects. -/
abbrev FiveQubitDecodingIndex := Option (Bitstring FiveQubitSite)

/-- The complete accepted-decoder/technical-reject Kraus family. -/
noncomputable def fiveQubitDecodingKraus :
    FiniteKrausFamily FiveQubitDecodingIndex FiveQubitSpace QubitSpace where
  operator
    | none => fiveQubitLogicalDecoderOperator
    | some bits => fiveQubitTechnicalRejectOperator bits

/-- The technical completion is trace preserving on the entire physical input. -/
theorem fiveQubitDecodingKraus_complete :
    fiveQubitDecodingKraus.Complete := by
  rw [FiniteKrausFamily.Complete, Fintype.sum_option]
  change
    (LinearMap.adjoint fiveQubitLogicalDecoderOperator).comp
          fiveQubitLogicalDecoderOperator +
        ∑ bits : Bitstring FiveQubitSite,
          (LinearMap.adjoint (fiveQubitTechnicalRejectOperator bits)).comp
            (fiveQubitTechnicalRejectOperator bits) = 1
  rw [fiveQubitLogicalDecoderOperator_adjoint_comp]
  simp_rw [fiveQubitTechnicalRejectOperator_adjoint_comp]
  rw [fiveQubitRejectedProjection_sum_rankOne]
  simp [fiveQubitRejectedProjection]

/-- Only the coherent code decoder is reported as accepted. -/
def fiveQubitDecodingOutcome : FiveQubitDecodingIndex → DistillationOutcome
  | none => .accepted
  | some _ => .rejected

/-- The complete one-qubit extraction instrument. -/
noncomputable def fiveQubitDecodingInstrument :
    FiniteInstrument FiveQubitDecodingIndex DistillationOutcome
      FiveQubitSpace QubitSpace where
  kraus := fiveQubitDecodingKraus
  observe := fiveQubitDecodingOutcome

theorem fiveQubitDecodingInstrument_complete :
    fiveQubitDecodingInstrument.kraus.Complete :=
  fiveQubitDecodingKraus_complete

/-- The visible accepted branch contains only the coherent logical decoder. -/
theorem fiveQubitDecodingInstrument_accepted_branch
    (A : Operator FiveQubitSpace) :
    fiveQubitDecodingInstrument.branchOperator .accepted A =
      fiveQubitLogicalDecoderOperator.comp
        (A.comp (LinearMap.adjoint fiveQubitLogicalDecoderOperator)) := by
  rw [FiniteInstrument.branchOperator_apply, Fintype.sum_option]
  simp [fiveQubitDecodingInstrument, fiveQubitDecodingKraus,
    fiveQubitDecodingOutcome]

/-- The logical codeword selected by a one-qubit computational label. -/
noncomputable def fiveQubitLogicalCodeword : Fin 2 → FiveQubitSpace
  | 0 => fiveQubitLogicalZero
  | 1 => fiveQubitLogicalOne

/-- The corresponding explicit physical-basis amplitude table. -/
def fiveQubitLogicalAmplitude : Fin 2 → FiveBitTuple → Complex
  | 0 => fiveQubitLogicalZeroAmplitude
  | 1 => fiveQubitLogicalOneAmplitude

@[simp]
theorem fiveQubitLogicalCodeword_apply_tuple
    (logical : Fin 2) (bits : FiveBitTuple) :
    fiveQubitLogicalCodeword logical (fiveTupleBitstring bits) =
      fiveQubitLogicalAmplitude logical bits := by
  fin_cases logical <;>
    simp [fiveQubitLogicalCodeword, fiveQubitLogicalAmplitude]

@[simp]
private theorem fiveQubitLogicalDecoderOperator_adjoint_basis
    (input : Fin 2) :
    LinearMap.adjoint fiveQubitLogicalDecoderOperator
        (qubitComputationalBasis input) =
      fiveQubitLogicalCodeword input := by
  fin_cases input <;>
    simp [fiveQubitLogicalDecoderOperator, fiveQubitLogicalCodeword,
      map_add, adjoint_rankOne_output_logical,
      InnerProductSpace.rankOne_apply]

private theorem fiveQubitDecodingInstrument_accepted_matrixEntry
    (A : Operator FiveQubitSpace) (output input : Fin 2) :
    inner Complex (qubitComputationalBasis output)
        (fiveQubitDecodingInstrument.branchOperator .accepted A
          (qubitComputationalBasis input)) =
      inner Complex (fiveQubitLogicalCodeword output)
        (A (fiveQubitLogicalCodeword input)) := by
  rw [fiveQubitDecodingInstrument_accepted_branch]
  simp only [LinearMap.comp_apply,
    fiveQubitLogicalDecoderOperator_adjoint_basis]
  fin_cases output <;>
    simp [fiveQubitLogicalCodeword, fiveQubitLogicalDecoderOperator,
      InnerProductSpace.rankOne_apply]

/-! ## The source-specified `YH` output swap -/

/--
The physical Clifford word `H Z H Z H`, with each `Z` realized as `S S`.
Up to its irrelevant global phase this is the source's `Y H` operation.
-/
noncomputable def tOutputSwapTransport :
    UnitaryTransport QubitSpace QubitSpace :=
  hadamardTransport.trans
    (phaseTransport.trans
      (phaseTransport.trans
        (hadamardTransport.trans
          (phaseTransport.trans
            (phaseTransport.trans hadamardTransport)))))

private theorem trans_conjDensity
    (U V : UnitaryTransport QubitSpace QubitSpace)
    (rho : DensityOperator QubitSpace) :
    (U.trans V).conjDensity rho = V.conjDensity (U.conjDensity rho) := by
  apply DensityOperator.ext_toOperator
  rfl

/-- The explicit `YH` word swaps the ideal source component to the error component. -/
theorem tOutputSwapTransport_tZero :
    tOutputSwapTransport.conjDensity tZero = tOne := by
  unfold tOutputSwapTransport tZero tOne
  simp only [trans_conjDensity, hadamard_conj_tMagicState,
    phase_conj_tMagicState]
  congr 1
  native_decide

/-- The same physical Clifford word swaps the error component back to the ideal one. -/
theorem tOutputSwapTransport_tOne :
    tOutputSwapTransport.conjDensity tOne = tZero := by
  unfold tOutputSwapTransport tZero tOne
  simp only [trans_conjDensity, hadamard_conj_tMagicState,
    phase_conj_tMagicState]
  congr 1
  native_decide

/-! ## Source-exact raw branch coefficients -/

/-- Raw logical-`T₀` coefficient before the final `YH` swap. -/
def fiveQubitRawTZeroCoefficient (epsilon : Real) : Real :=
  (epsilon ^ 5 + 5 * epsilon ^ 2 * (1 - epsilon) ^ 3) / 6

/-- Raw logical-`T₁` coefficient before the final `YH` swap. -/
def fiveQubitRawTOneCoefficient (epsilon : Real) : Real :=
  ((1 - epsilon) ^ 5 + 5 * epsilon ^ 3 * (1 - epsilon) ^ 2) / 6

/-- The source-exact probability of the all-positive syndrome. -/
def fiveQubitSuccessProbability (epsilon : Real) : Real :=
  fiveQubitRawTZeroCoefficient epsilon +
    fiveQubitRawTOneCoefficient epsilon

private theorem fiveQubitLogicalPrepared_matrixEntry_sum
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (output input : Fin 2) :
    inner Complex (fiveQubitLogicalCodeword output)
        ((fiveQubitPrepareInput
          (fiveQubitNoisyResources epsilon hzero hone)).toOperator
          (fiveQubitLogicalCodeword input)) =
      ∑ left : FiveBitTuple, ∑ right : FiveBitTuple,
        star (fiveQubitLogicalAmplitude output left) *
          (tDiagonalMatrixEntry epsilon left.1 right.1 *
            tDiagonalMatrixEntry epsilon left.2.1 right.2.1 *
            tDiagonalMatrixEntry epsilon left.2.2.1 right.2.2.1 *
            tDiagonalMatrixEntry epsilon left.2.2.2.1 right.2.2.2.1 *
            tDiagonalMatrixEntry epsilon left.2.2.2.2 right.2.2.2.2) *
          fiveQubitLogicalAmplitude input right := by
  rw [fiveQubit_inner_operator_eq_sum]
  rw [← Equiv.sum_comp fiveBitstringEquiv]
  apply Finset.sum_congr rfl
  intro left _hleft
  rw [← Equiv.sum_comp fiveBitstringEquiv]
  apply Finset.sum_congr rfl
  intro right _hright
  change
    star (fiveQubitLogicalCodeword output (fiveTupleBitstring left)) *
          inner Complex
            (fiveQubitComputationalBasis (fiveTupleBitstring left))
            ((fiveQubitPrepareInput
              (fiveQubitNoisyResources epsilon hzero hone)).toOperator
              (fiveQubitComputationalBasis (fiveTupleBitstring right))) *
          fiveQubitLogicalCodeword input (fiveTupleBitstring right) = _
  rw [fiveQubitLogicalCodeword_apply_tuple,
    fiveQubitLogicalCodeword_apply_tuple,
    fiveQubitPrepareInput_matrixEntry]
  simp only [fiveQubitNoisyResources, tDiagonalInput_matrixEntry]
  rfl

set_option maxHeartbeats 8000000 in
private theorem fiveQubitLogicalPrepared_matrixEntry_exact
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (output input : Fin 2) :
    inner Complex (fiveQubitLogicalCodeword output)
        ((fiveQubitPrepareInput
          (fiveQubitNoisyResources epsilon hzero hone)).toOperator
          (fiveQubitLogicalCodeword input)) =
      (fiveQubitRawTZeroCoefficient epsilon : Complex) *
          tDiagonalMatrixEntry 0 output input +
        (fiveQubitRawTOneCoefficient epsilon : Complex) *
          tDiagonalMatrixEntry 1 output input := by
  rw [fiveQubitLogicalPrepared_matrixEntry_sum]
  have hsqrtInv :
      (((Real.sqrt 3)⁻¹ : Real) : Complex) ^ 2 = 1 / 3 := by
    norm_cast
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 3)]
    norm_num
  have hsqrtInv' :
      ((Real.sqrt 3 : Complex)⁻¹) ^ 2 = 1 / 3 := by
    simpa using hsqrtInv
  have hsqrtInvCube :
      ((Real.sqrt 3 : Complex)⁻¹) ^ 3 =
        (Real.sqrt 3 : Complex)⁻¹ / 3 := by
    calc
      ((Real.sqrt 3 : Complex)⁻¹) ^ 3 =
          ((Real.sqrt 3 : Complex)⁻¹) ^ 2 *
            (Real.sqrt 3 : Complex)⁻¹ := by ring
      _ = (Real.sqrt 3 : Complex)⁻¹ / 3 := by
        rw [hsqrtInv']
        ring
  have hsqrtInvFourth :
      ((Real.sqrt 3 : Complex)⁻¹) ^ 4 = 1 / 9 := by
    calc
      ((Real.sqrt 3 : Complex)⁻¹) ^ 4 =
          ((Real.sqrt 3 : Complex)⁻¹) ^ 2 *
            ((Real.sqrt 3 : Complex)⁻¹) ^ 2 := by ring
      _ = 1 / 9 := by
        rw [hsqrtInv']
        ring
  have hsqrtInvFifth :
      ((Real.sqrt 3 : Complex)⁻¹) ^ 5 =
        (Real.sqrt 3 : Complex)⁻¹ / 9 := by
    calc
      ((Real.sqrt 3 : Complex)⁻¹) ^ 5 =
          ((Real.sqrt 3 : Complex)⁻¹) ^ 4 *
            (Real.sqrt 3 : Complex)⁻¹ := by ring
      _ = (Real.sqrt 3 : Complex)⁻¹ / 9 := by
        rw [hsqrtInvFourth]
        ring
  have hIfifth : Complex.I ^ 5 = Complex.I := by
    norm_num [pow_succ, Complex.I_sq]
  fin_cases output <;> fin_cases input <;>
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    simp [fiveQubitLogicalAmplitude, fiveQubitLogicalZeroAmplitude,
      fiveQubitLogicalOneAmplitude, tDiagonalMatrixEntry,
      fiveQubitRawTZeroCoefficient, fiveQubitRawTOneCoefficient] <;>
    ring_nf <;>
    simp only [hsqrtInvCube, hsqrtInvFourth, hsqrtInvFifth] <;>
    simp only [hIfifth, Complex.I_sq] <;>
    ring

/-- The unnormalised logical branch produced by the actual accepted decoder. -/
noncomputable def fiveQubitDecodedAcceptedRaw
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    Operator QubitSpace :=
  fiveQubitDecodingInstrument.branchOperator .accepted
    (fiveQubitPrepareInput
      (fiveQubitNoisyResources epsilon hzero hone)).toOperator

@[simp]
private theorem tZero_matrixEntry (output input : Fin 2) :
    inner Complex (qubitComputationalBasis output)
        (tZero.toOperator (qubitComputationalBasis input)) =
      tDiagonalMatrixEntry 0 output input := by
  simpa only [tDiagonalInput_zero] using
    tDiagonalInput_matrixEntry 0 (by norm_num) (by norm_num) output input

@[simp]
private theorem tOne_matrixEntry (output input : Fin 2) :
    inner Complex (qubitComputationalBasis output)
        (tOne.toOperator (qubitComputationalBasis input)) =
      tDiagonalMatrixEntry 1 output input := by
  have hentry :=
    tDiagonalInput_matrixEntry 1 (by norm_num) (by norm_num) output input
  rw [tDiagonalInput_toOperator] at hentry
  simpa [tRawInputBranch, tInputWeight, tInputComponent] using hentry

@[simp]
private theorem tZero_apply_basis (output input : Fin 2) :
    (tZero.toOperator (qubitComputationalBasis input)) output =
      tDiagonalMatrixEntry 0 output input := by
  simpa only [qubitComputationalBasis_inner_state] using
    tZero_matrixEntry output input

@[simp]
private theorem tOne_apply_basis (output input : Fin 2) :
    (tOne.toOperator (qubitComputationalBasis input)) output =
      tDiagonalMatrixEntry 1 output input := by
  simpa only [qubitComputationalBasis_inner_state] using
    tOne_matrixEntry output input

/--
The accepted raw branch has the two source-exact logical coefficients. This is
derived from the physical product density and coherent decoder, before the
source-specified output swap.
-/
theorem fiveQubitDecodedAcceptedRaw_eq
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    fiveQubitDecodedAcceptedRaw epsilon hzero hone =
      (fiveQubitRawTZeroCoefficient epsilon : Complex) • tZero.toOperator +
        (fiveQubitRawTOneCoefficient epsilon : Complex) • tOne.toOperator := by
  apply qubitOperator_ext_matrixEntry
  intro output input
  rw [fiveQubitDecodedAcceptedRaw,
    fiveQubitDecodingInstrument_accepted_matrixEntry,
    fiveQubitLogicalPrepared_matrixEntry_exact]
  simp

/-- The physical accepted Born weight is the source-exact success probability. -/
theorem fiveQubitAcceptedBornWeight_eq_success
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    fiveQubitDecodingInstrument.bornWeight .accepted
        (fiveQubitPrepareInput
          (fiveQubitNoisyResources epsilon hzero hone)) =
      fiveQubitSuccessProbability epsilon := by
  change Complex.re
      (LinearMap.trace Complex QubitSpace
        (fiveQubitDecodedAcceptedRaw epsilon hzero hone)) = _
  rw [fiveQubitDecodedAcceptedRaw_eq, map_add, map_smul, map_smul,
    tZero.trace_one, tOne.trace_one]
  simp [fiveQubitSuccessProbability]

theorem fiveQubitRawTZeroCoefficient_nonneg
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    0 ≤ fiveQubitRawTZeroCoefficient epsilon := by
  unfold fiveQubitRawTZeroCoefficient
  have hcomplement : 0 ≤ 1 - epsilon := sub_nonneg.mpr hone
  positivity

theorem fiveQubitRawTOneCoefficient_nonneg
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    0 ≤ fiveQubitRawTOneCoefficient epsilon := by
  unfold fiveQubitRawTOneCoefficient
  have hcomplement : 0 ≤ 1 - epsilon := sub_nonneg.mpr hone
  positivity

theorem fiveQubitSuccessProbability_pos
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    0 < fiveQubitSuccessProbability epsilon := by
  unfold fiveQubitSuccessProbability fiveQubitRawTZeroCoefficient
    fiveQubitRawTOneCoefficient
  have hcomplement : 0 ≤ 1 - epsilon := sub_nonneg.mpr hone
  by_cases hhalf : epsilon ≤ 1 / 2
  · have hpositive : 0 < (1 - epsilon) ^ 5 := by
      exact pow_pos (by linarith) _
    positivity
  · have hpositive : 0 < epsilon ^ 5 := by
      exact pow_pos (by linarith) _
    positivity

theorem fiveQubitSuccessProbability_le_one_sixth
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    fiveQubitSuccessProbability epsilon ≤ 1 / 6 := by
  let q := epsilon * (1 - epsilon)
  have hqzero : 0 ≤ q := mul_nonneg hzero (sub_nonneg.mpr hone)
  have hqquarter : q ≤ 1 / 4 := by
    dsimp [q]
    nlinarith [sq_nonneg (epsilon - 1 / 2)]
  have hfactor : 0 ≤ q * (1 - 2 * q) :=
    mul_nonneg hqzero (by linarith)
  have hrewrite :
      fiveQubitSuccessProbability epsilon =
        (1 - 5 * q + 10 * q ^ 2) / 6 := by
    dsimp [q]
    unfold fiveQubitSuccessProbability fiveQubitRawTZeroCoefficient
      fiveQubitRawTOneCoefficient
    ring
  rw [hrewrite]
  nlinarith

theorem fiveQubitSuccessProbability_nonneg
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    0 ≤ fiveQubitSuccessProbability epsilon :=
  (fiveQubitSuccessProbability_pos epsilon hzero hone).le

theorem fiveQubitSuccessProbability_le_one
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    fiveQubitSuccessProbability epsilon ≤ 1 := by
  linarith [fiveQubitSuccessProbability_le_one_sixth epsilon hzero hone]

theorem fiveQubitRejectedBornWeight_eq_rejection
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    fiveQubitDecodingInstrument.bornWeight .rejected
        (fiveQubitPrepareInput
          (fiveQubitNoisyResources epsilon hzero hone)) =
      1 - fiveQubitSuccessProbability epsilon := by
  have hsum :=
    fiveQubitDecodingInstrument.sum_bornWeight_eq_one
      fiveQubitDecodingInstrument_complete
      (fiveQubitPrepareInput
        (fiveQubitNoisyResources epsilon hzero hone))
  rw [show (Finset.univ : Finset DistillationOutcome) =
    {DistillationOutcome.accepted, DistillationOutcome.rejected} by decide]
    at hsum
  rw [Finset.sum_insert (by decide), Finset.sum_singleton] at hsum
  rw [fiveQubitAcceptedBornWeight_eq_success] at hsum
  linarith

theorem fiveQubitRejectionProbability_pos
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    0 < 1 - fiveQubitSuccessProbability epsilon := by
  linarith [fiveQubitSuccessProbability_le_one_sixth epsilon hzero hone]

theorem fiveQubitAcceptedBornWeight_pos
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    0 < fiveQubitDecodingInstrument.bornWeight .accepted
      (fiveQubitPrepareInput
        (fiveQubitNoisyResources epsilon hzero hone)) := by
  rw [fiveQubitAcceptedBornWeight_eq_success]
  exact fiveQubitSuccessProbability_pos epsilon hzero hone

theorem fiveQubitRejectedBornWeight_pos
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    0 < fiveQubitDecodingInstrument.bornWeight .rejected
      (fiveQubitPrepareInput
        (fiveQubitNoisyResources epsilon hzero hone)) := by
  rw [fiveQubitRejectedBornWeight_eq_rejection]
  exact fiveQubitRejectionProbability_pos epsilon hzero hone

/-- The normalized accepted decoder output before the source `YH` swap. -/
noncomputable def fiveQubitAcceptedConditionalBeforeSwap
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    DensityOperator QubitSpace :=
  fiveQubitDecodingInstrument.conditionalDensity .accepted
    (fiveQubitPrepareInput
      (fiveQubitNoisyResources epsilon hzero hone))
    (fiveQubitAcceptedBornWeight_pos epsilon hzero hone)

/-- The normalized technical completion branch before output postprocessing. -/
noncomputable def fiveQubitRejectedConditionalBeforeSwap
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    DensityOperator QubitSpace :=
  fiveQubitDecodingInstrument.conditionalDensity .rejected
    (fiveQubitPrepareInput
      (fiveQubitNoisyResources epsilon hzero hone))
    (fiveQubitRejectedBornWeight_pos epsilon hzero hone)

theorem fiveQubitAcceptedConditionalBeforeSwap_toOperator
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (fiveQubitAcceptedConditionalBeforeSwap epsilon hzero hone).toOperator =
      ((fiveQubitSuccessProbability epsilon : Complex)⁻¹) •
        ((fiveQubitRawTZeroCoefficient epsilon : Complex) • tZero.toOperator +
          (fiveQubitRawTOneCoefficient epsilon : Complex) •
            tOne.toOperator) := by
  rw [fiveQubitAcceptedConditionalBeforeSwap,
    FiniteInstrument.conditionalDensity_toOperator,
    fiveQubitAcceptedBornWeight_eq_success]
  change
    ((fiveQubitSuccessProbability epsilon : Complex)⁻¹) •
        fiveQubitDecodedAcceptedRaw epsilon hzero hone = _
  rw [fiveQubitDecodedAcceptedRaw_eq]

private theorem fiveQubitDecodingOutput_decomposition_beforeSwap
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (fiveQubitDecodingInstrument.kraus.toQuantumChannel
      fiveQubitDecodingInstrument_complete).mapDensity
        (fiveQubitPrepareInput
          (fiveQubitNoisyResources epsilon hzero hone)) =
      outcomeMixture (fiveQubitSuccessProbability epsilon)
        (fiveQubitSuccessProbability_nonneg epsilon hzero hone)
        (fiveQubitSuccessProbability_le_one epsilon hzero hone)
        (fiveQubitAcceptedConditionalBeforeSwap epsilon hzero hone)
        (fiveQubitRejectedConditionalBeforeSwap epsilon hzero hone) := by
  apply qubitDensityOperator_ext
  let prepared := fiveQubitPrepareInput
    (fiveQubitNoisyResources epsilon hzero hone)
  calc
    ((fiveQubitDecodingInstrument.kraus.toQuantumChannel
        fiveQubitDecodingInstrument_complete).mapDensity prepared).toOperator =
        ∑ outcome : DistillationOutcome,
          fiveQubitDecodingInstrument.branchOperator outcome
            prepared.toOperator :=
      (fiveQubitDecodingInstrument.sum_branchOperator_eq_mapDensity_toOperator
        fiveQubitDecodingInstrument_complete prepared).symm
    _ = fiveQubitDecodingInstrument.branchOperator .accepted
          prepared.toOperator +
        fiveQubitDecodingInstrument.branchOperator .rejected
          prepared.toOperator := by
      rw [show (Finset.univ : Finset DistillationOutcome) =
        {DistillationOutcome.accepted, DistillationOutcome.rejected} by decide]
      rw [Finset.sum_insert (by decide), Finset.sum_singleton]
    _ = (fiveQubitSuccessProbability epsilon : Complex) •
          (fiveQubitAcceptedConditionalBeforeSwap
            epsilon hzero hone).toOperator +
        ((1 - fiveQubitSuccessProbability epsilon : Real) : Complex) •
          (fiveQubitRejectedConditionalBeforeSwap
            epsilon hzero hone).toOperator := by
      unfold fiveQubitAcceptedConditionalBeforeSwap
        fiveQubitRejectedConditionalBeforeSwap
      rw [← fiveQubitDecodingInstrument.bornWeight_smul_conditionalDensity_toOperator
          .accepted prepared (fiveQubitAcceptedBornWeight_pos epsilon hzero hone),
        ← fiveQubitDecodingInstrument.bornWeight_smul_conditionalDensity_toOperator
          .rejected prepared (fiveQubitRejectedBornWeight_pos epsilon hzero hone),
        fiveQubitAcceptedBornWeight_eq_success,
        fiveQubitRejectedBornWeight_eq_rejection]
    _ = (outcomeMixture (fiveQubitSuccessProbability epsilon)
          (fiveQubitSuccessProbability_nonneg epsilon hzero hone)
          (fiveQubitSuccessProbability_le_one epsilon hzero hone)
          (fiveQubitAcceptedConditionalBeforeSwap epsilon hzero hone)
          (fiveQubitRejectedConditionalBeforeSwap
            epsilon hzero hone)).toOperator := by
      simp [outcomeMixture, DensityOperator.convexCombinationOperator,
        branchState, outcomeWeight,
        show (Finset.univ : Finset DistillationOutcome) =
          {DistillationOutcome.accepted, DistillationOutcome.rejected} by decide]
      simp only [RCLike.real_smul_eq_coe_smul (K := Complex)]
      norm_num

/-- The complete decoder run before the source-specified output Clifford. -/
noncomputable def fiveQubitDecodingRunBeforeSwap
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    DistillationRun QubitSpace FiveQubitSpace QubitSpace where
  resourceCount := 5
  noisyInput := fiveQubitNoisyResources epsilon hzero hone
  prepareInput := fiveQubitPrepareInput
  operation := fiveQubitDecodingInstrument.kraus.toQuantumChannel
    fiveQubitDecodingInstrument_complete
  successProbability := fiveQubitSuccessProbability epsilon
  success_nonneg := fiveQubitSuccessProbability_nonneg epsilon hzero hone
  success_le_one := fiveQubitSuccessProbability_le_one epsilon hzero hone
  acceptedOutput := fiveQubitAcceptedConditionalBeforeSwap epsilon hzero hone
  rejectedOutput := fiveQubitRejectedConditionalBeforeSwap epsilon hzero hone
  output_decomposition :=
    fiveQubitDecodingOutput_decomposition_beforeSwap epsilon hzero hone

/-- The source `YH` swap regarded as the output postprocessing channel. -/
noncomputable def fiveQubitOutputSwapChannel :
    QuantumChannel QubitSpace QubitSpace :=
  QuantumChannel.unitaryConj tOutputSwapTransport

@[simp]
theorem fiveQubitOutputSwapChannel_tZero :
    fiveQubitOutputSwapChannel.mapDensity tZero = tOne := by
  apply qubitDensityOperator_ext
  simpa [fiveQubitOutputSwapChannel,
    UnitaryTransport.conjDensity_toOperator] using
    congrArg DensityOperator.toOperator tOutputSwapTransport_tZero

@[simp]
theorem fiveQubitOutputSwapChannel_tOne :
    fiveQubitOutputSwapChannel.mapDensity tOne = tZero := by
  apply qubitDensityOperator_ext
  simpa [fiveQubitOutputSwapChannel,
    UnitaryTransport.conjDensity_toOperator] using
    congrArg DensityOperator.toOperator tOutputSwapTransport_tOne

/--
The actual five-to-one postselected run, including the source output swap.
Its accepted output is the BK05 decoded branch. The postprocessed rejected
density remains the interface-only technical completion and does not represent
a decoded BK05 rejected history.
-/
noncomputable def fiveQubitDistillationRun
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    DistillationRun QubitSpace FiveQubitSpace QubitSpace :=
  (fiveQubitDecodingRunBeforeSwap epsilon hzero hone).postprocess
    fiveQubitOutputSwapChannel

@[simp]
theorem fiveQubitDistillationRun_resourceCount
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (fiveQubitDistillationRun epsilon hzero hone).resourceCount = 5 :=
  rfl

@[simp]
theorem fiveQubitDistillationRun_successProbability
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (fiveQubitDistillationRun epsilon hzero hone).successProbability =
      fiveQubitSuccessProbability epsilon :=
  rfl

/-- Normalized post-swap logical weights, with `0 = T₀` and `1 = T₁`. -/
def fiveQubitAcceptedOutputWeight (epsilon : Real) : Fin 2 → Real
  | 0 => fiveQubitRawTOneCoefficient epsilon /
      fiveQubitSuccessProbability epsilon
  | 1 => fiveQubitRawTZeroCoefficient epsilon /
      fiveQubitSuccessProbability epsilon

theorem fiveQubitAcceptedOutputWeight_nonneg
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (word : Fin 2) :
    0 ≤ fiveQubitAcceptedOutputWeight epsilon word := by
  fin_cases word <;>
    simp only [fiveQubitAcceptedOutputWeight] <;>
    exact div_nonneg
      (by first
        | exact fiveQubitRawTOneCoefficient_nonneg epsilon hzero hone
        | exact fiveQubitRawTZeroCoefficient_nonneg epsilon hzero hone)
      (fiveQubitSuccessProbability_nonneg epsilon hzero hone)

theorem fiveQubitAcceptedOutputWeight_sum
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    ∑ word : Fin 2, fiveQubitAcceptedOutputWeight epsilon word = 1 := by
  rw [Fin.sum_univ_two]
  simp only [fiveQubitAcceptedOutputWeight]
  have hne :=
    (fiveQubitSuccessProbability_pos epsilon hzero hone).ne'
  field_simp [hne]
  unfold fiveQubitSuccessProbability
  ring

/-- The explicit normalized accepted density after the output swap. -/
noncomputable def fiveQubitAcceptedOutput
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    DensityOperator QubitSpace :=
  DensityOperator.convexCombination Finset.univ
    (fiveQubitAcceptedOutputWeight epsilon) tInputComponent
    (by
      intro word _hword
      exact fiveQubitAcceptedOutputWeight_nonneg
        epsilon hzero hone word)
    (by simpa using
      fiveQubitAcceptedOutputWeight_sum epsilon hzero hone)

theorem fiveQubitAcceptedOutput_toOperator
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (fiveQubitAcceptedOutput epsilon hzero hone).toOperator =
      ((fiveQubitRawTOneCoefficient epsilon /
          fiveQubitSuccessProbability epsilon : Real) : Complex) •
        tZero.toOperator +
      ((fiveQubitRawTZeroCoefficient epsilon /
          fiveQubitSuccessProbability epsilon : Real) : Complex) •
        tOne.toOperator := by
  rw [fiveQubitAcceptedOutput,
    DensityOperator.convexCombination_toOperator]
  simp [DensityOperator.convexCombinationOperator,
    fiveQubitAcceptedOutputWeight, tInputComponent]
  simp only [RCLike.real_smul_eq_coe_smul (K := Complex)]
  norm_num

theorem fiveQubitDistillationRun_acceptedOutput_toOperator
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (fiveQubitDistillationRun epsilon hzero hone).acceptedOutput.toOperator =
      ((fiveQubitSuccessProbability epsilon : Complex)⁻¹) •
        ((fiveQubitRawTOneCoefficient epsilon : Complex) • tZero.toOperator +
          (fiveQubitRawTZeroCoefficient epsilon : Complex) •
            tOne.toOperator) := by
  change fiveQubitOutputSwapChannel
      (fiveQubitAcceptedConditionalBeforeSwap
        epsilon hzero hone).toOperator = _
  rw [fiveQubitAcceptedConditionalBeforeSwap_toOperator]
  simp only [map_smul, map_add]
  have hzeroSwap := congrArg DensityOperator.toOperator
    fiveQubitOutputSwapChannel_tZero
  have honeSwap := congrArg DensityOperator.toOperator
    fiveQubitOutputSwapChannel_tOne
  change fiveQubitOutputSwapChannel tZero.toOperator = tOne.toOperator
    at hzeroSwap
  change fiveQubitOutputSwapChannel tOne.toOperator = tZero.toOperator
    at honeSwap
  rw [hzeroSwap, honeSwap, add_comm]

/-- The run's reported accepted density is the explicit normalized mixture. -/
theorem fiveQubitDistillationRun_acceptedOutput
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (fiveQubitDistillationRun epsilon hzero hone).acceptedOutput =
      fiveQubitAcceptedOutput epsilon hzero hone := by
  apply qubitDensityOperator_ext
  rw [fiveQubitDistillationRun_acceptedOutput_toOperator,
    fiveQubitAcceptedOutput_toOperator]
  simp only [RCLike.real_smul_eq_coe_smul (K := Complex),
    div_eq_mul_inv]
  module

/-- Independent identical diagonal resources admitted by this concrete run. -/
noncomputable def fiveQubitIndependentInputErrorModel
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    IndependentInputErrorModel 5 QubitSpace where
  rate := fun _ => epsilon
  rate_nonneg := fun _ => hzero
  rate_le_one := fun _ => hone
  admissible := fun rates inputs =>
    rates = (fun _ => epsilon) ∧
      inputs = fiveQubitNoisyResources epsilon hzero hone

/-- The concrete BK05 five-to-one T-state postselection protocol. -/
noncomputable def fiveQubitMagicStateProtocol
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    MagicStateDistillationProtocol QubitSpace FiveQubitSpace QubitSpace where
  run := fiveQubitDistillationRun epsilon hzero hone
  inputErrorModel := .independent
    (fiveQubitIndependentInputErrorModel epsilon hzero hone)
  inputPermitted := by
    exact ⟨rfl, rfl⟩
  behavior := .postselected
  idealOutput := tZero
  outputError := fun rho _sigma => tInputError rho
  outputError_nonneg := by
    intro rho _sigma
    unfold tInputError tInputSquaredOverlap
    linarith [projectionSquaredOverlap_le_one
      (tProjector tZeroDirection) rho
      (tProjector_isSymmetricProjection tZeroDirection)]

@[simp]
theorem fiveQubitMagicStateProtocol_reportedOutput
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (fiveQubitMagicStateProtocol epsilon hzero hone).run.reportedOutput
        (fiveQubitMagicStateProtocol epsilon hzero hone).behavior =
      fiveQubitAcceptedOutput epsilon hzero hone := by
  change (fiveQubitDistillationRun epsilon hzero hone).acceptedOutput = _
  exact fiveQubitDistillationRun_acceptedOutput epsilon hzero hone

end BK05T
end Distillation
end QEC
