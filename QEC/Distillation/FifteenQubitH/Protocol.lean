import QEC.Coding.Stabilizer.JointMeasurement
import QEC.Distillation.FifteenQubitH.NoisyInput
import QEC.Distillation.Triorthogonal.CSS
/-!
# Literal BK15 syndrome route

This internal module fixes the source order of the Bravyi--Kitaev fifteen
qubit H-state route.  It deliberately models the source's omitted final
correction literally:

`P_Z(mu) -> A(w(mu))^† -> P_X(eta)`.

The source declares failure before decoding.  A later section of this module
will therefore keep rejected endpoints raw until a positive-mass proof is
available; no conditional density is assigned at the zero-error endpoint.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace BK15
namespace Protocol

open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput
open scoped BigOperators TensorProduct

attribute [local instance 100] Fintype.ofFinite

/-! ## The physical A-error-word basis -/

/-- The normalized one-qubit vector underlying one diagonal A-basis component. -/
def aInputState : Fin 2 → QubitSpace
  | 0 => aZeroState
  | 1 => aOneState

@[simp] theorem aInputState_norm (bit : Fin 2) : ‖aInputState bit‖ = 1 := by
  fin_cases bit
  · exact aZeroState_norm
  · exact aOneState_norm

/-- Each existing diagonal input component is the rank-one density of its
actual A-basis vector. -/
theorem aInputComponent_toOperator_rankOne (bit : Fin 2) :
    (aInputComponent bit).toOperator =
      (InnerProductSpace.rankOne Complex (aInputState bit) (aInputState bit)).toLinearMap := by
  fin_cases bit
  · change aZeroDensity.toOperator =
      (InnerProductSpace.rankOne Complex aZeroState aZeroState).toLinearMap
    rw [aZeroDensity_eq_phaseStateDensity,
      OneQubitMagic.phaseStateDensity_toOperator]
    rfl
  · change aOneDensity.toOperator =
      (InnerProductSpace.rankOne Complex aOneState aOneState).toLinearMap
    rw [aOneDensity, UnitaryTransport.conjDensity_toOperator,
      aZeroDensity_eq_phaseStateDensity,
      OneQubitMagic.phaseStateDensity_toOperator,
      QuditSubsystem.conjOperator_rankOne]
    rfl

/-- The one-qubit A eigenbasis in the source bit convention. -/
noncomputable def aInputBasis : OrthonormalBasis (Fin 2) Complex QubitSpace :=
  (EuclideanSpace.basisFun (Fin 2) Complex).map
    aBasisTransport.toLinearIsometryEquiv

@[simp] theorem aInputBasis_apply (bit : Fin 2) :
    aInputBasis bit = aInputState bit := by
  fin_cases bit
  · change aBasisTransport
      (EuclideanSpace.basisFun (Fin 2) Complex 0) = aZeroState
    exact aBasisTransport_basis_zero
  · change aBasisTransport
      (EuclideanSpace.basisFun (Fin 2) Complex 1) = aOneState
    exact aBasisTransport_basis_one

/-- Convert a binary code word back to the computational-bit label used by a
qubit-register basis. -/
noncomputable def wordBits (word : Word) : Bitstring (Fin 15) :=
  (bitstringWordEquiv (Fin 15)).symm word

@[simp] theorem wordBits_toWord (word : Word) :
    bitstringWordEquiv (Fin 15) (wordBits word) = word :=
  (bitstringWordEquiv (Fin 15)).apply_symm_apply word

@[simp] theorem wordBits_apply_cast (word : Word) (site : Fin 15) :
    ((wordBits word site : Fin 2) : ZMod 2) = word site := by
  have h := congrFun (wordBits_toWord word) site
  exact h

@[simp] theorem wordBits_apply (word : Word) (site : Fin 15) :
    wordBits word site = word site := by
  change (if word site = 0 then 0 else 1) = word site
  generalize hbit : word site = bit
  fin_cases bit <;> rfl

/-- The literal right-associated tensor vector selected by one A-error word. -/
noncomputable def bk15TensorErrorState (word : Word) : BK15Tensor :=
  aInputState (wordBits word 0) ⊗ₜ[Complex]
    (aInputState (wordBits word 1) ⊗ₜ[Complex]
      (aInputState (wordBits word 2) ⊗ₜ[Complex]
        (aInputState (wordBits word 3) ⊗ₜ[Complex]
          (aInputState (wordBits word 4) ⊗ₜ[Complex]
            (aInputState (wordBits word 5) ⊗ₜ[Complex]
              (aInputState (wordBits word 6) ⊗ₜ[Complex]
                (aInputState (wordBits word 7) ⊗ₜ[Complex]
                  (aInputState (wordBits word 8) ⊗ₜ[Complex]
                    (aInputState (wordBits word 9) ⊗ₜ[Complex]
                      (aInputState (wordBits word 10) ⊗ₜ[Complex]
                        (aInputState (wordBits word 11) ⊗ₜ[Complex]
                          (aInputState (wordBits word 12) ⊗ₜ[Complex]
                            (aInputState (wordBits word 13) ⊗ₜ[Complex]
                              aInputState (wordBits word 14))))))))))))))

/-- The corresponding normalized physical Fin-15 A-error vector. -/
noncomputable def bk15ErrorWordState (word : Word) : BK15Register :=
  bk15TensorRegisterTransport (bk15TensorErrorState word)

set_option maxRecDepth 65536 in
/-- The right-associated tensor product of the fifteen one-qubit A bases. -/
noncomputable def bk15TensorAInputBasis :
    OrthonormalBasis BK15BitTuple Complex BK15Tensor :=
  aInputBasis.tensorProduct
    (aInputBasis.tensorProduct
      (aInputBasis.tensorProduct
        (aInputBasis.tensorProduct
          (aInputBasis.tensorProduct
            (aInputBasis.tensorProduct
              (aInputBasis.tensorProduct
                (aInputBasis.tensorProduct
                  (aInputBasis.tensorProduct
                    (aInputBasis.tensorProduct
                      (aInputBasis.tensorProduct
                        (aInputBasis.tensorProduct
                          (aInputBasis.tensorProduct
                            (aInputBasis.tensorProduct aInputBasis)))))))))))))

/-- The actual full A-error-word basis on the physical Fin-15 register. -/
noncomputable def bk15AErrorBasis : OrthonormalBasis Word Complex BK15Register :=
  ((bk15TensorAInputBasis.map
      bk15TensorRegisterTransport.toLinearIsometryEquiv).reindex
    (bk15BitstringEquiv.trans (bitstringWordEquiv (Fin 15))))

set_option maxRecDepth 65536 in
@[simp] theorem bk15AErrorBasis_apply (word : Word) :
    bk15AErrorBasis word = bk15ErrorWordState word := by
  rw [bk15AErrorBasis, OrthonormalBasis.reindex_apply, OrthonormalBasis.map_apply]
  change bk15TensorRegisterTransport
      (bk15TensorAInputBasis
        (splitBK15Bitstring (wordBits word))) =
    bk15TensorRegisterTransport (bk15TensorErrorState word)
  congr 1
  simp only [bk15TensorAInputBasis, bk15TensorErrorState, splitBK15Bitstring,
    OrthonormalBasis.tensorProduct_apply', aInputBasis_apply]

set_option maxRecDepth 65536 in
/-- The previously constructed physical error-word density is exactly the
rank-one projector on the corresponding member of the A-error basis. -/
theorem bk15ErrorWordDensity_toOperator_rankOne (word : Word) :
    (bk15ErrorWordDensity word).toOperator =
      (InnerProductSpace.rankOne Complex
        (bk15ErrorWordState word) (bk15ErrorWordState word)).toLinearMap := by
  have hcomponent (bit : Bit) :
      (aInputComponent bit).toOperator =
        (InnerProductSpace.rankOne Complex (aInputState bit) (aInputState bit)).toLinearMap :=
    aInputComponent_toOperator_rankOne bit
  unfold bk15ErrorWordDensity bk15PrepareInput bk15TensorDensity bk15WordResources
  simp only [UnitaryTransport.conjDensity_toOperator,
    DensityOperator.tensorDensity_toOperator,
    hcomponent, DensityOperator.tensorMap_rankOne]
  rw [QuditSubsystem.conjOperator_rankOne]
  simp only [bk15ErrorWordState, bk15TensorErrorState, wordBits_apply]

/-- The ten literal source `Z`-check labels. -/
abbrev ZCheckIndex := Sum (Fin 4) QuadraticIndex

/-- The four literal source `X`-check labels. -/
abbrev XCheckIndex := Fin 4

/-- Full sign-valued outcomes of the first, `Z`-type joint measurement. -/
abbrev ZJointSyndrome := JointSyndrome ZCheckIndex

/-- Full sign-valued outcomes of the second, `X`-type joint measurement. -/
abbrev XJointSyndrome := JointSyndrome XCheckIndex

/-- Convert a projective sign outcome to the source's binary syndrome bit. -/
def signToBit : StabilizerOutcome -> Bit
  | .positive => 0
  | .negative => 1

/-- Convert a binary source syndrome bit to the corresponding projector sign. -/
def bitToSign (bit : Bit) : StabilizerOutcome :=
  if bit = 0 then .positive else .negative

@[simp] theorem signToBit_bitToSign (bit : Bit) : signToBit (bitToSign bit) = bit := by
  fin_cases bit <;> rfl

@[simp] theorem bitToSign_signToBit (sign : StabilizerOutcome) :
    bitToSign (signToBit sign) = sign := by
  cases sign <;> rfl

/-- The binary coordinates extracted from a full joint sign syndrome. -/
def binarySyndrome {Index : Type} (outcome : JointSyndrome Index) : Index -> Bit :=
  fun check => signToBit (outcome check)

/-- The sign outcome corresponding to a binary syndrome vector. -/
def signSyndrome {Index : Type} (syndrome : Index -> Bit) : JointSyndrome Index :=
  fun check => bitToSign (syndrome check)

@[simp] theorem binarySyndrome_signSyndrome {Index : Type}
    (syndrome : Index -> Bit) : binarySyndrome (signSyndrome syndrome) = syndrome := by
  funext check
  exact signToBit_bitToSign (syndrome check)

@[simp] theorem signSyndrome_binarySyndrome {Index : Type}
    (outcome : JointSyndrome Index) : signSyndrome (binarySyndrome outcome) = outcome := by
  funext check
  exact bitToSign_signToBit (outcome check)

/-- The literal binary syndrome read from the first measurement. -/
abbrev zBinarySyndrome (outcome : ZJointSyndrome) : ZCheckIndex -> Bit :=
  binarySyndrome outcome

/-- The literal binary syndrome read from the second measurement. -/
abbrev xBinarySyndrome (outcome : XJointSyndrome) : XCheckIndex -> Bit :=
  binarySyndrome outcome

/-- A finite right-section exists for the concrete ten-bit `l2Syndrome` map. -/
theorem l2Syndrome_surjective : Function.Surjective l2Syndrome := by
  native_decide

/-- The route-local correction representative selected for a `Z` syndrome. -/
noncomputable def l2SyndromeSection (syndrome : ZCheckIndex -> Bit) : Word :=
  if syndrome = 0 then 0 else Classical.choose (l2Syndrome_surjective syndrome)

@[simp] theorem l2SyndromeSection_zero :
    l2SyndromeSection (0 : ZCheckIndex -> Bit) = 0 := by
  simp [l2SyndromeSection]

@[simp] theorem l2SyndromeSection_apply (syndrome : ZCheckIndex -> Bit) :
    l2Syndrome (l2SyndromeSection syndrome) = syndrome :=
  by
    by_cases hsyndrome : syndrome = 0
    · subst syndrome
      simp [l2SyndromeSection, l2Syndrome]
      rfl
    · simpa [l2SyndromeSection, hsyndrome] using
        Classical.choose_spec (l2Syndrome_surjective syndrome)

/-- The single-site binary word used for the physical nonzero-syndrome witness. -/
def oneSiteWord (site : Fin 15) : Word := Pi.single site 1

/-- Every one-site word has a nonzero first-stage syndrome. -/
theorem oneSiteWord_l2Syndrome_ne_zero (site : Fin 15) :
    l2Syndrome (oneSiteWord site) ≠ 0 := by
  native_decide +revert

/-- Every one-site physical error also has a nonzero acceptance syndrome. -/
theorem oneSiteWord_l1Syndrome_ne_zero (site : Fin 15) :
    l1Syndrome (oneSiteWord site) ≠ 0 := by
  native_decide +revert

/-- The source's first, quadratic-and-linear `Z` check family. -/
def zChecks (check : ZCheckIndex) : Binary (Fin 15) :=
  cssZCheck (l2Generator check)

/-- The source's second, linear `X` check family. -/
def xChecks (check : XCheckIndex) : Binary (Fin 15) :=
  cssXCheck (linearGenerator check)

theorem zChecks_commute (left right : ZCheckIndex) :
    Commutes (zChecks left) (zChecks right) :=
  cssZCheck_commutes_cssZCheck _ _

theorem xChecks_commute (left right : XCheckIndex) :
    Commutes (xChecks left) (xChecks right) :=
  cssXCheck_commutes_cssXCheck _ _

/-- The literal first-stage `P_Z(mu)` projector. -/
def zProjector (outcome : ZJointSyndrome) : Operator BK15Register :=
  jointStabilizerProjector zChecks zChecks_commute outcome

/-- The literal second-stage `P_X(eta)` projector. -/
def xProjector (outcome : XJointSyndrome) : Operator BK15Register :=
  jointStabilizerProjector xChecks xChecks_commute outcome

@[simp] theorem zProjector_adjoint (outcome : ZJointSyndrome) :
    LinearMap.adjoint (zProjector outcome) = zProjector outcome :=
  jointStabilizerProjector_adjoint zChecks zChecks_commute outcome

@[simp] theorem xProjector_adjoint (outcome : XJointSyndrome) :
    LinearMap.adjoint (xProjector outcome) = xProjector outcome :=
  jointStabilizerProjector_adjoint xChecks xChecks_commute outcome

@[simp] theorem zProjector_idempotent (outcome : ZJointSyndrome) :
    zProjector outcome * zProjector outcome = zProjector outcome :=
  jointStabilizerProjector_idempotent zChecks zChecks_commute outcome

@[simp] theorem xProjector_idempotent (outcome : XJointSyndrome) :
    xProjector outcome * xProjector outcome = xProjector outcome :=
  jointStabilizerProjector_idempotent xChecks xChecks_commute outcome

theorem sum_zProjector_eq_one :
    ∑ outcome : ZJointSyndrome, zProjector outcome = 1 :=
  sum_jointStabilizerProjector_eq_one zChecks zChecks_commute

theorem sum_xProjector_eq_one :
    ∑ outcome : XJointSyndrome, xProjector outcome = 1 :=
  sum_jointStabilizerProjector_eq_one xChecks xChecks_commute

/-- The one-qubit Hermitian `A` observable as a unitary transport.

It is `U_A Z U_A^†`, with `U_A` the already proved A-basis transport; this is
the physical operator used below rather than the unrelated H-resource bridge.
-/
noncomputable def aObservableTransport : UnitaryTransport QubitSpace QubitSpace :=
  aBasisTransport.symm.trans (zTransport.trans aBasisTransport)

/-- A selected local factor of the source correction. -/
noncomputable def aBitTransport (bit : Bit) : UnitaryTransport QubitSpace QubitSpace :=
  if bit = 0 then UnitaryTransport.identity QubitSpace else aObservableTransport

/-- The one-qubit basis after the selected local correction factor. -/
noncomputable def aBitBasis (bit : Bit) : OrthonormalBasis (Fin 2) Complex QubitSpace :=
  (EuclideanSpace.basisFun (Fin 2) Complex).map
    (aBitTransport bit).toLinearIsometryEquiv

/-- A selected local correction acts diagonally on the physical A-error basis. -/
@[simp] theorem aBitTransport_aInputState (word error : Bit) :
    aBitTransport word (aInputState error) =
      binaryPhaseScalar (word * error) • aInputState error := by
  fin_cases word <;> fin_cases error <;>
    simp only [aInputState, aOneState_eq_pauliZ]
  · change (UnitaryTransport.identity QubitSpace) aZeroState =
      (1 : Complex) • aZeroState
    simp
  · change (UnitaryTransport.identity QubitSpace) aOneState =
      (1 : Complex) • aOneState
    simp
  · change aObservableTransport aZeroState = (1 : Complex) • aZeroState
    change aBasisObservable aZeroState = _
    simp
  · change aObservableTransport aOneState = (-1 : Complex) • aOneState
    change aBasisObservable aOneState = _
    simpa using aBasisObservable_aOneState

set_option maxRecDepth 65536 in
/-- The actual tensor-product correction `A(word)` before transport to Fin-15. -/
noncomputable def aWordCorrectionTensor (word : Word) :
    UnitaryTransport BK15Tensor BK15Tensor := by
  let U14 : BK1Tensor ≃ₗᵢ[Complex] BK1Tensor :=
    (aBitTransport (word 14)).toLinearIsometryEquiv
  let U13 : BK2Tensor ≃ₗᵢ[Complex] BK2Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 13)).toLinearIsometryEquiv U14
  let U12 : BK3Tensor ≃ₗᵢ[Complex] BK3Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 12)).toLinearIsometryEquiv U13
  let U11 : BK4Tensor ≃ₗᵢ[Complex] BK4Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 11)).toLinearIsometryEquiv U12
  let U10 : BK5Tensor ≃ₗᵢ[Complex] BK5Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 10)).toLinearIsometryEquiv U11
  let U9 : BK6Tensor ≃ₗᵢ[Complex] BK6Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 9)).toLinearIsometryEquiv U10
  let U8 : BK7Tensor ≃ₗᵢ[Complex] BK7Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 8)).toLinearIsometryEquiv U9
  let U7 : BK8Tensor ≃ₗᵢ[Complex] BK8Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 7)).toLinearIsometryEquiv U8
  let U6 : BK9Tensor ≃ₗᵢ[Complex] BK9Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 6)).toLinearIsometryEquiv U7
  let U5 : BK10Tensor ≃ₗᵢ[Complex] BK10Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 5)).toLinearIsometryEquiv U6
  let U4 : BK11Tensor ≃ₗᵢ[Complex] BK11Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 4)).toLinearIsometryEquiv U5
  let U3 : BK12Tensor ≃ₗᵢ[Complex] BK12Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 3)).toLinearIsometryEquiv U4
  let U2 : BK13Tensor ≃ₗᵢ[Complex] BK13Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 2)).toLinearIsometryEquiv U3
  let U1 : BK14Tensor ≃ₗᵢ[Complex] BK14Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 1)).toLinearIsometryEquiv U2
  let U0 : BK15Tensor ≃ₗᵢ[Complex] BK15Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 0)).toLinearIsometryEquiv U1
  exact { toLinearEquiv := U0.toLinearEquiv, map_inner := U0.inner_map_map }

/-- The physical Fin-15 realization of the source correction `A(word)`. -/
noncomputable def aWordCorrectionTransport (word : Word) :
    UnitaryTransport BK15Register BK15Register :=
  bk15TensorRegisterTransport.symm.trans
    ((aWordCorrectionTensor word).trans bk15TensorRegisterTransport)

set_option maxRecDepth 65536 in
@[simp] theorem aWordCorrectionTransport_zero_apply (psi : BK15Register) :
    aWordCorrectionTransport (0 : Word) psi = psi := by
  change bk15TensorRegisterTransport
      (aWordCorrectionTensor 0
        (bk15TensorRegisterTransport.toLinearEquiv.symm psi)) = psi
  simp [aWordCorrectionTensor, aBitTransport, UnitaryTransport.identity]

set_option maxRecDepth 65536 in
/-- The physical correction has the source binary character on every
A-error-word basis vector. -/
theorem aWordCorrectionTransport_eigen (word error : Word) :
    aWordCorrectionTransport word (bk15ErrorWordState error) =
      binaryPhaseScalar (word ⬝ᵥ error) • bk15ErrorWordState error := by
  simp [aWordCorrectionTransport, aWordCorrectionTensor, bk15ErrorWordState,
    bk15TensorErrorState, dotProduct,
    binaryPhaseScalar_sum, aBitTransport_aInputState]
  simp_rw [← TensorProduct.smul_tmul']
  simp_rw [TensorProduct.tmul_smul]
  simp_rw [map_smul]
  simp_rw [smul_smul]
  simp only [Fin.isValue, Fin.prod_univ_succ, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Fin.reduceSucc, Finset.univ_unique,
    Fin.default_eq_zero, Finset.prod_singleton]
  congr 1
  ring

set_option maxRecDepth 65536 in
private noncomputable def bk15TensorComputationalBasis :
    OrthonormalBasis BK15BitTuple Complex BK15Tensor :=
  let oneBasis := EuclideanSpace.basisFun (Fin 2) Complex
  oneBasis.tensorProduct
    (oneBasis.tensorProduct
      (oneBasis.tensorProduct
        (oneBasis.tensorProduct
          (oneBasis.tensorProduct
            (oneBasis.tensorProduct
              (oneBasis.tensorProduct
                (oneBasis.tensorProduct
                  (oneBasis.tensorProduct
                    (oneBasis.tensorProduct
                      (oneBasis.tensorProduct
                        (oneBasis.tensorProduct
                          (oneBasis.tensorProduct
                            (oneBasis.tensorProduct oneBasis)))))))))))))

set_option maxRecDepth 65536 in
private noncomputable def tensor15Vector
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : QubitSpace) :
    BK15Tensor :=
  v0 ⊗ₜ[Complex]
    (v1 ⊗ₜ[Complex]
      (v2 ⊗ₜ[Complex]
        (v3 ⊗ₜ[Complex]
          (v4 ⊗ₜ[Complex]
            (v5 ⊗ₜ[Complex]
              (v6 ⊗ₜ[Complex]
                (v7 ⊗ₜ[Complex]
                  (v8 ⊗ₜ[Complex]
                    (v9 ⊗ₜ[Complex]
                      (v10 ⊗ₜ[Complex]
                        (v11 ⊗ₜ[Complex]
                          (v12 ⊗ₜ[Complex]
                            (v13 ⊗ₜ[Complex] v14)))))))))))))

set_option maxRecDepth 65536 in
@[simp] private theorem bk15TensorComputationalBasis_apply
    (bits : BK15BitTuple) :
    bk15TensorComputationalBasis bits =
      tensor15Vector
        (EuclideanSpace.basisFun (Fin 2) Complex bits.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.2.2.2.2.2.2) := by
  simp only [bk15TensorComputationalBasis,
    OrthonormalBasis.tensorProduct_apply', tensor15Vector]

set_option maxRecDepth 65536 in
@[simp] private theorem bk15TensorRegisterTransport_apply_computationalBasis
    (bits : BK15BitTuple) :
    bk15TensorRegisterTransport (bk15TensorComputationalBasis bits) =
      EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex
        (bk15TupleBitstring bits) := by
  dsimp [bk15TensorRegisterTransport, bk15TensorComputationalBasis]
  rw [OrthonormalBasis.equiv_apply_basis]
  rfl

private noncomputable def bk15TensorErrorVector
    (error : Word) : BK15Tensor :=
  tensor15Vector
    (aInputState (wordBits error 0))
    (aInputState (wordBits error 1))
    (aInputState (wordBits error 2))
    (aInputState (wordBits error 3))
    (aInputState (wordBits error 4))
    (aInputState (wordBits error 5))
    (aInputState (wordBits error 6))
    (aInputState (wordBits error 7))
    (aInputState (wordBits error 8))
    (aInputState (wordBits error 9))
    (aInputState (wordBits error 10))
    (aInputState (wordBits error 11))
    (aInputState (wordBits error 12))
    (aInputState (wordBits error 13))
    (aInputState (wordBits error 14))

private theorem bk15TensorErrorState_eq_errorVector (error : Word) :
    bk15TensorErrorState error = bk15TensorErrorVector error := by
  rfl

private def fin15Nested (f : Fin 15 → Complex) : Complex :=
    f 0 * (f 1 * (f 2 * (f 3 * (f 4 * (f 5 * (f 6 *
      (f 7 * (f 8 * (f 9 * (f 10 * (f 11 * (f 12 *
        (f 13 * f 14)))))))))))))

private theorem fin15Nested_eq_prod (f : Fin 15 → Complex) :
    fin15Nested f = ∏ site, f site := by
  simp [fin15Nested, Fin.prod_univ_succ]

private theorem inner_tmul_complex
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Complex E]
    [NormedAddCommGroup F] [InnerProductSpace Complex F]
    (x x' : E) (y y' : F) :
    inner Complex (x ⊗ₜ[Complex] y) (x' ⊗ₜ[Complex] y') =
      inner Complex x x' * inner Complex y y' := by
  exact TensorProduct.inner_tmul Complex x x' y y'

set_option maxRecDepth 65536 in
private theorem bk15Tensor_inner_nested
    (error : Word) (bits : Bitstring (Fin 15)) :
    inner Complex
        (bk15TensorComputationalBasis (splitBK15Bitstring bits))
        (bk15TensorErrorState error) =
      fin15Nested
        (fun site => aInputState (error site) (bits site)) := by
  calc
    inner Complex
        (bk15TensorComputationalBasis (splitBK15Bitstring bits))
        (bk15TensorErrorState error) =
      inner Complex
        (bk15TensorComputationalBasis (splitBK15Bitstring bits))
        (bk15TensorErrorVector error) := by
          exact congrArg
            (fun psi : BK15Tensor => inner Complex
              (bk15TensorComputationalBasis
                (splitBK15Bitstring bits)) psi)
            (bk15TensorErrorState_eq_errorVector error)
    _ = fin15Nested
        (fun site => aInputState (error site) (bits site)) := by
      unfold fin15Nested bk15TensorErrorVector
      rw [bk15TensorComputationalBasis_apply]
      unfold tensor15Vector
      simp only [splitBK15Bitstring]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      simp only [EuclideanSpace.basisFun_inner, wordBits_apply]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
private theorem bk15ErrorWordState_apply_product
    (error : Word) (bits : Bitstring (Fin 15)) :
    bk15ErrorWordState error bits =
      ∏ site : Fin 15, aInputState (error site) (bits site) := by
  have hinner := bk15TensorRegisterTransport.map_inner
    (bk15TensorComputationalBasis (splitBK15Bitstring bits))
    (bk15TensorErrorState error)
  rw [bk15TensorRegisterTransport_apply_computationalBasis,
    bk15TupleBitstring_splitBK15Bitstring,
    EuclideanSpace.basisFun_inner] at hinner
  change bk15ErrorWordState error bits =
    inner Complex
      (bk15TensorComputationalBasis (splitBK15Bitstring bits))
      (bk15TensorErrorState error) at hinner
  rw [bk15Tensor_inner_nested] at hinner
  exact hinner.trans (fin15Nested_eq_prod _)

private def finBitToBit (bit : Fin 2) : Bit :=
  if bit = 0 then 0 else 1

private theorem bitstringWordEquiv_apply_eq_finBitToBit
    (bits : Bitstring (Fin 15)) (site : Fin 15) :
    bitstringWordEquiv (Fin 15) bits site = finBitToBit (bits site) := by
  rw [bitstringWordEquiv_apply]
  generalize hbit : bits site = bit
  fin_cases bit <;> rfl

private theorem binaryPhaseScalar_finBitToBit (bit : Fin 2) :
    binaryPhaseScalar (finBitToBit bit) = zPhase bit := by
  fin_cases bit <;> rfl

private theorem binaryPhaseScalar_mul_aInputState_apply
    (check error : Bit) (bit : Fin 2) :
    binaryPhaseScalar (check * finBitToBit bit) * aInputState error bit =
      aInputState (error + check) bit := by
  by_cases hcheck : check = 0
  · subst check
    simp
  · have hcheck_one : check = 1 := zmod_two_eq_one_of_ne_zero hcheck
    subst check
    by_cases herror : error = 0
    · subst error
      simpa [aInputState, aOneState_eq_pauliZ,
        binaryPhaseScalar_finBitToBit] using
          (pauliZ_apply aZeroState bit).symm
    · have herror_one : error = 1 := zmod_two_eq_one_of_ne_zero herror
      subst error
      have hone : (1 : Bit) + 1 = 0 := by decide
      rw [hone]
      simp [aInputState, aOneState_eq_pauliZ,
        binaryPhaseScalar_finBitToBit, pauliZ_apply, ← mul_assoc]

set_option maxRecDepth 65536 in
private theorem cssZCheck_errorWord (check error : Word) :
    toHermitianQubitOperator (cssZCheck check) (bk15ErrorWordState error) =
      bk15ErrorWordState (error + check) := by
  ext bits
  simp [toHermitianQubitOperator, hermitianPhaseScalar,
    toQubitOperator, xSupport, zSupport, binaryOverlapCount,
    binaryOverlapSupport, bk15ErrorWordState_apply_product]
  rw [zSupportPhase_eq_binaryPhaseScalar_wordPairing,
    Coding.wordPairing_apply, dotProduct, binaryPhaseScalar_sum,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro site _
  rw [bitstringWordEquiv_apply_eq_finBitToBit]
  exact binaryPhaseScalar_mul_aInputState_apply
    (check site) (error site) (bits site)

@[simp] private theorem binaryPhaseScalar_mul_self (bit : ZMod 2) :
    binaryPhaseScalar bit * binaryPhaseScalar bit = 1 := by
  rw [← binaryPhaseScalar_add]
  have h : bit + bit = 0 := by
    fin_cases bit <;> decide
  rw [h, binaryPhaseScalar_zero]

private theorem aWordCorrectionTransport_symm_eigen (word error : Word) :
    (aWordCorrectionTransport word).symm (bk15ErrorWordState error) =
      binaryPhaseScalar (word ⬝ᵥ error) • bk15ErrorWordState error := by
  let U := aWordCorrectionTransport word
  let scalar := binaryPhaseScalar (word ⬝ᵥ error)
  have hforward : U (bk15ErrorWordState error) =
      scalar • bk15ErrorWordState error := by
    exact aWordCorrectionTransport_eigen word error
  have hback := congrArg (fun psi : BK15Register => U.symm psi) hforward
  simp only [map_smul] at hback
  have hstate : bk15ErrorWordState error =
      scalar • U.symm (bk15ErrorWordState error) := by
    simpa [U, UnitaryTransport.symm] using hback
  calc
    U.symm (bk15ErrorWordState error) =
        1 • U.symm (bk15ErrorWordState error) := by simp
    _ = (scalar * scalar) • U.symm (bk15ErrorWordState error) := by
      simp [scalar, binaryPhaseScalar_mul_self]
    _ = scalar • (scalar • U.symm (bk15ErrorWordState error)) := by
      rw [smul_smul]
    _ = scalar • bk15ErrorWordState error := by rw [← hstate]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
private theorem aWordCorrectionTransport_symm_cssZCheck
    (word check : Word) :
    (aWordCorrectionTransport word).symm.toLinearEquiv.toLinearMap *
        toHermitianQubitOperator (cssZCheck check) =
      binaryPhaseScalar (word ⬝ᵥ check) •
        (toHermitianQubitOperator (cssZCheck check) *
          (aWordCorrectionTransport word).symm.toLinearEquiv.toLinearMap) := by
  apply Module.Basis.ext bk15AErrorBasis.toBasis
  intro error
  simp only [Module.End.mul_apply, LinearMap.smul_apply]
  change (aWordCorrectionTransport word).symm
      (toHermitianQubitOperator (cssZCheck check)
        (bk15AErrorBasis error)) =
    binaryPhaseScalar (word ⬝ᵥ check) •
      toHermitianQubitOperator (cssZCheck check)
        ((aWordCorrectionTransport word).symm
          (bk15AErrorBasis error))
  rw [bk15AErrorBasis_apply, cssZCheck_errorWord,
    aWordCorrectionTransport_symm_eigen,
    aWordCorrectionTransport_symm_eigen, map_smul,
    cssZCheck_errorWord]
  rw [dotProduct_add, binaryPhaseScalar_add]
  module

/-- A complete literal record of both joint measurement outcomes. -/
abbrev History := ZJointSyndrome × XJointSyndrome

/-- The source acceptance rule: only the all-zero `X` syndrome is accepted. -/
def historyOutcome (history : History) : DistillationOutcome :=
  if xBinarySyndrome history.2 = 0 then .accepted else .rejected

/-- The source correction selected by the observed first-stage syndrome. -/
noncomputable def historyCorrection (outcome : ZJointSyndrome) :
    UnitaryTransport BK15Register BK15Register :=
  aWordCorrectionTransport (l2SyndromeSection (zBinarySyndrome outcome))

private theorem jointStabilizerProjector_intertwines_operator
    {index checkIndex : Type} [Fintype index] [DecidableEq index]
    [Fintype checkIndex] [DecidableEq checkIndex]
    (checks : checkIndex → Binary index)
    (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (T : Operator (QubitRegister index))
    (source target : JointSyndrome checkIndex)
    (hfactor : ∀ check,
      T * jointStabilizerFactor checks source check =
        jointStabilizerFactor checks target check * T) :
    T * jointStabilizerProjector checks hcomm source =
      jointStabilizerProjector checks hcomm target * T := by
  classical
  let pairFactor : checkIndex →
      Operator (QubitRegister index) × Operator (QubitRegister index) :=
    fun check =>
      (jointStabilizerFactor checks source check,
        jointStabilizerFactor checks target check)
  have hpairwise :
      (↑(Finset.univ : Finset checkIndex) : Set checkIndex).Pairwise
      (Function.onFun Commute pairFactor) := by
    intro left _ right _ hne
    change pairFactor left * pairFactor right =
      pairFactor right * pairFactor left
    apply Prod.ext
    · exact
        (jointStabilizerFactor_commute checks hcomm left right source source).eq
    · exact
        (jointStabilizerFactor_commute checks hcomm left right target target).eq
  let productPair := Finset.univ.noncommProd pairFactor hpairwise
  have hintertwines : T * productPair.1 = productPair.2 * T := by
    dsimp only [productPair]
    refine Finset.noncommProd_induction Finset.univ pairFactor hpairwise
      (fun pair => T * pair.1 = pair.2 * T) ?_ ?_ ?_
    · intro left right hleft hright
      change T * (left.1 * right.1) = (left.2 * right.2) * T
      calc
        T * (left.1 * right.1) = (T * left.1) * right.1 := by
          rw [mul_assoc]
        _ = (left.2 * T) * right.1 := by rw [hleft]
        _ = left.2 * (T * right.1) := by rw [mul_assoc]
        _ = left.2 * (right.2 * T) := by rw [hright]
        _ = (left.2 * right.2) * T := by rw [mul_assoc]
    · simp
    · intro check _
      exact hfactor check
  have hfst : productPair.1 =
      jointStabilizerProjector checks hcomm source := by
    dsimp only [productPair]
    unfold jointStabilizerProjector
    simpa [pairFactor] using
      (Finset.map_noncommProd Finset.univ pairFactor hpairwise
        (MonoidHom.fst _ _))
  have hsnd : productPair.2 =
      jointStabilizerProjector checks hcomm target := by
    dsimp only [productPair]
    unfold jointStabilizerProjector
    simpa [pairFactor] using
      (Finset.map_noncommProd Finset.univ pairFactor hpairwise
        (MonoidHom.snd _ _))
  simpa [hfst, hsnd] using hintertwines

@[simp] private theorem binaryPhaseScalar_signToBit
    (outcome : StabilizerOutcome) :
    binaryPhaseScalar (signToBit outcome) = outcome.sign := by
  cases outcome <;> norm_num [signToBit, binaryPhaseScalar,
    StabilizerOutcome.sign]

private theorem historyCorrection_phase
    (outcome : ZJointSyndrome) (check : ZCheckIndex) :
    binaryPhaseScalar
        (l2SyndromeSection (zBinarySyndrome outcome) ⬝ᵥ l2Generator check) =
      (outcome check).sign := by
  have hsection := congrFun
    (l2SyndromeSection_apply (zBinarySyndrome outcome)) check
  change Coding.wordPairing (l2SyndromeSection (zBinarySyndrome outcome))
      (l2Generator check) = zBinarySyndrome outcome check at hsection
  rw [Coding.wordPairing_apply] at hsection
  rw [hsection]
  exact binaryPhaseScalar_signToBit (outcome check)

private theorem historyCorrection_symm_zCheck
    (outcome : ZJointSyndrome) (check : ZCheckIndex) :
    (historyCorrection outcome).symm.toLinearEquiv.toLinearMap *
        toHermitianQubitOperator (zChecks check) =
      (outcome check).sign •
        (toHermitianQubitOperator (zChecks check) *
          (historyCorrection outcome).symm.toLinearEquiv.toLinearMap) := by
  change
    (aWordCorrectionTransport
        (l2SyndromeSection
          (zBinarySyndrome outcome))).symm.toLinearEquiv.toLinearMap *
        toHermitianQubitOperator (cssZCheck (l2Generator check)) =
      (outcome check).sign •
        (toHermitianQubitOperator (cssZCheck (l2Generator check)) *
          (aWordCorrectionTransport
            (l2SyndromeSection
              (zBinarySyndrome outcome))).symm.toLinearEquiv.toLinearMap)
  rw [aWordCorrectionTransport_symm_cssZCheck,
    historyCorrection_phase]

private theorem historyCorrection_symm_zFactor
    (outcome : ZJointSyndrome) (check : ZCheckIndex) :
    (historyCorrection outcome).symm.toLinearEquiv.toLinearMap *
        jointStabilizerFactor zChecks outcome check =
      jointStabilizerFactor zChecks
          (signSyndrome (0 : ZCheckIndex → Bit)) check *
        (historyCorrection outcome).symm.toLinearEquiv.toLinearMap := by
  let T := (historyCorrection outcome).symm.toLinearEquiv.toLinearMap
  let S := toHermitianQubitOperator (zChecks check)
  let scalar := (outcome check).sign
  have hcheck : T * S = scalar • (S * T) := by
    exact historyCorrection_symm_zCheck outcome check
  have hscalar : scalar * scalar = 1 := by
    exact StabilizerOutcome.sign_mul_self (outcome check)
  simp only [jointStabilizerFactor, stabilizerProjector, signSyndrome,
    bitToSign, StabilizerOutcome.sign, Pi.zero_apply, if_pos, one_smul]
  change T * ((1 / 2 : Complex) • (1 + scalar • S)) =
    ((1 / 2 : Complex) • (1 + S)) * T
  calc
    T * ((1 / 2 : Complex) • (1 + scalar • S)) =
        (1 / 2 : Complex) • (T + scalar • (T * S)) := by
      simp only [mul_smul_comm, mul_add, mul_one]
    _ = (1 / 2 : Complex) •
        (T + scalar • (scalar • (S * T))) := by rw [hcheck]
    _ = (1 / 2 : Complex) • (T + S * T) := by
      rw [smul_smul, hscalar, one_smul]
    _ = ((1 / 2 : Complex) • (1 + S)) * T := by
      simp only [smul_mul_assoc, add_mul, one_mul]

private theorem historyCorrection_symm_zProjector
    (outcome : ZJointSyndrome) :
    (historyCorrection outcome).symm.toLinearEquiv.toLinearMap *
        zProjector outcome =
      zProjector (signSyndrome (0 : ZCheckIndex → Bit)) *
        (historyCorrection outcome).symm.toLinearEquiv.toLinearMap := by
  exact jointStabilizerProjector_intertwines_operator
    zChecks zChecks_commute
    (historyCorrection outcome).symm.toLinearEquiv.toLinearMap
    outcome (signSyndrome (0 : ZCheckIndex → Bit))
    (historyCorrection_symm_zFactor outcome)

private theorem zCheck_computationalBasis_eigen
    (check : ZCheckIndex) (bits : Bitstring (Fin 15)) :
    toHermitianQubitOperator (zChecks check)
        (EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits) =
      (signSyndrome
          (l2Syndrome (bitstringWordEquiv (Fin 15) bits)) check).sign •
        EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits := by
  have hphase (z : Word) :
      zSupportPhase (binarySupport z) bits =
        (bitToSign (Coding.wordPairing (F := ZMod 2) z
          (bitstringWordEquiv (Fin 15) bits))).sign := by
    rw [zSupportPhase_eq_binaryPhaseScalar_wordPairing]
    by_cases hzero : Coding.wordPairing (F := ZMod 2) z
        (bitstringWordEquiv (Fin 15) bits) = 0 <;>
      simp only [binaryPhaseScalar, bitToSign, hzero, if_true, if_false,
        StabilizerOutcome.sign]
  have hphaseCheck := hphase (l2Generator check)
  rw [Coding.wordPairing_apply, dotProduct_comm] at hphaseCheck
  have hoperator (z : Word) :
      toHermitianQubitOperator (cssZCheck z) = localZSupport (binarySupport z) := by
    simp [toHermitianQubitOperator, hermitianPhaseScalar, binaryOverlapCount,
      binaryOverlapSupport, xSupport, zSupport, cssZCheck, toQubitOperator,
      binaryPhaseScalar]
  have hbasis (s : Finset (Fin 15)) :
      localZSupport s (EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits) =
        zSupportPhase s bits •
          EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits := by
    ext candidate
    by_cases hcandidate : candidate = bits
    · subst candidate
      simp [EuclideanSpace.basisFun_apply, PiLp.single_apply]
    · simp [EuclideanSpace.basisFun_apply, PiLp.single_apply, hcandidate]
  change toHermitianQubitOperator (cssZCheck (l2Generator check)) _ = _
  rw [hoperator, hbasis]
  apply congrArg (fun c : Complex =>
    c • EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits)
  exact hphaseCheck

private theorem zProjector_computationalBasis_matching
    (bits : Bitstring (Fin 15)) :
    zProjector
        (signSyndrome (l2Syndrome (bitstringWordEquiv (Fin 15) bits)))
        (EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits) =
      EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits := by
  apply (jointStabilizerProjector_fixed_iff zChecks zChecks_commute
    (signSyndrome (l2Syndrome (bitstringWordEquiv (Fin 15) bits)))
    (EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits)).2
  intro check
  exact zCheck_computationalBasis_eigen check bits

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
private theorem zProjector_zero_computationalBasis_of_zero
    (bits : Bitstring (Fin 15))
    (hzero : l2Syndrome (bitstringWordEquiv (Fin 15) bits) = 0) :
    zProjector (signSyndrome (0 : ZCheckIndex → Bit))
        (EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits) =
      EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits := by
  apply (jointStabilizerProjector_fixed_iff zChecks zChecks_commute
    (signSyndrome (0 : ZCheckIndex → Bit))
    (EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits)).2
  intro check
  have hcheck := congrFun hzero check
  have hsign : (signSyndrome
      (l2Syndrome (bitstringWordEquiv (Fin 15) bits)) check).sign = 1 := by
    simp [signSyndrome, bitToSign, hcheck, StabilizerOutcome.sign]
  have heigen := zCheck_computationalBasis_eigen check bits
  rw [hsign, one_smul] at heigen
  have hzeroSign :
      (signSyndrome (0 : ZCheckIndex → Bit) check).sign = 1 := by
    simp [signSyndrome, bitToSign, StabilizerOutcome.sign]
  rw [hzeroSign, one_smul]
  exact heigen

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
private theorem zProjector_zero_mul_zCheck (check : ZCheckIndex) :
    zProjector (signSyndrome (0 : ZCheckIndex → Bit)) *
        toHermitianQubitOperator (zChecks check) =
      zProjector (signSyndrome (0 : ZCheckIndex → Bit)) := by
  have hleft :
      toHermitianQubitOperator (zChecks check) *
          zProjector (signSyndrome (0 : ZCheckIndex → Bit)) =
        zProjector (signSyndrome (0 : ZCheckIndex → Bit)) := by
    have hsign :
        (signSyndrome (0 : ZCheckIndex → Bit) check).sign = 1 := by
      simp [signSyndrome, bitToSign, StabilizerOutcome.sign]
    have heigen := jointStabilizerProjector_eigen zChecks zChecks_commute
      (signSyndrome (0 : ZCheckIndex → Bit)) check
    rw [hsign, one_smul] at heigen
    exact heigen
  have hadjoint := congrArg LinearMap.adjoint hleft
  simpa only [Module.End.mul_eq_comp, LinearMap.adjoint_comp,
    adjoint_toHermitianQubitOperator_eq_self, zProjector_adjoint] using hadjoint

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
private theorem zCheck_computationalBasis_negative
    (check : ZCheckIndex) (bits : Bitstring (Fin 15))
    (hcheck : l2Syndrome (bitstringWordEquiv (Fin 15) bits) check ≠ 0) :
    toHermitianQubitOperator (zChecks check)
        (EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits) =
      -EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits := by
  have hsign :
      (signSyndrome
        (l2Syndrome (bitstringWordEquiv (Fin 15) bits)) check).sign = -1 := by
    simp [signSyndrome, bitToSign, hcheck, StabilizerOutcome.sign]
  have heigen := zCheck_computationalBasis_eigen check bits
  rw [hsign, neg_one_smul] at heigen
  exact heigen

private theorem eq_zero_of_neg_eq_self_complex
    {V : Type} [AddCommGroup V] [Module Complex V]
    (value : V) (hneg : -value = value) : value = 0 := by
  have hsum : value + value = 0 := neg_eq_iff_add_eq_zero.mp hneg
  have htwo : (2 : Complex) • value = 0 := by
    simpa [two_smul] using hsum
  rcases smul_eq_zero.mp htwo with hscalar | hvalue
  · norm_num at hscalar
  · exact hvalue

private theorem projector_apply_eq_zero_of_neg_eigen
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace Complex V]
    (projector observable : Module.End Complex V) (value : V)
    (hmul : projector * observable = projector)
    (heigen : observable value = -value) : projector value = 0 := by
  have happly := LinearMap.congr_fun hmul value
  simp only [Module.End.mul_apply] at happly
  rw [heigen] at happly
  simp only [map_neg] at happly
  exact eq_zero_of_neg_eq_self_complex _ happly

private theorem exists_l2Syndrome_check_ne_zero
    (bits : Bitstring (Fin 15))
    (hzero : l2Syndrome (bitstringWordEquiv (Fin 15) bits) ≠ 0) :
    ∃ check, l2Syndrome (bitstringWordEquiv (Fin 15) bits) check ≠ 0 := by
  classical
  by_contra hall
  apply hzero
  funext check
  by_contra hcheck
  exact hall ⟨check, hcheck⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
private theorem zProjector_zero_computationalBasis_of_ne
    (bits : Bitstring (Fin 15))
    (hzero : l2Syndrome (bitstringWordEquiv (Fin 15) bits) ≠ 0) :
    zProjector (signSyndrome (0 : ZCheckIndex → Bit))
        (EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits) = 0 := by
  obtain ⟨check, hcheck⟩ := exists_l2Syndrome_check_ne_zero bits hzero
  exact projector_apply_eq_zero_of_neg_eigen
    (zProjector (signSyndrome (0 : ZCheckIndex → Bit)))
    (toHermitianQubitOperator (zChecks check))
    (EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits)
    (zProjector_zero_mul_zCheck check)
    (zCheck_computationalBasis_negative check bits hcheck)

private theorem zProjector_zero_computationalBasis
    (bits : Bitstring (Fin 15)) :
    zProjector (signSyndrome (0 : ZCheckIndex → Bit))
        (EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits) =
      if l2Syndrome (bitstringWordEquiv (Fin 15) bits) = 0 then
        EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits
      else 0 := by
  by_cases hzero : l2Syndrome (bitstringWordEquiv (Fin 15) bits) = 0
  · rw [if_pos hzero]
    exact zProjector_zero_computationalBasis_of_zero bits hzero
  · rw [if_neg hzero]
    exact zProjector_zero_computationalBasis_of_ne bits hzero

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
private theorem zProjector_zero_apply
    (psi : BK15Register) (bits : Bitstring (Fin 15)) :
    zProjector (signSyndrome (0 : ZCheckIndex → Bit)) psi bits =
      if l2Syndrome (bitstringWordEquiv (Fin 15) bits) = 0 then
        psi bits
      else 0 := by
  have hinner := LinearMap.adjoint_inner_right
    (zProjector (signSyndrome (0 : ZCheckIndex → Bit)))
    (EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits) psi
  rw [zProjector_adjoint] at hinner
  rw [zProjector_zero_computationalBasis] at hinner
  by_cases hzero : l2Syndrome (bitstringWordEquiv (Fin 15) bits) = 0
  · rw [if_pos hzero]
    rw [if_pos hzero] at hinner
    rw [EuclideanSpace.basisFun_inner,
      EuclideanSpace.basisFun_inner] at hinner
    exact hinner
  · rw [if_neg hzero]
    rw [if_neg hzero] at hinner
    rw [EuclideanSpace.basisFun_inner] at hinner
    simpa using hinner

/-- One literal history Kraus operator, in source order.

The middle factor is the adjoint of the selected `A(w(mu))`; no final
correction occurs after `P_X(eta)`.
-/
noncomputable def historyKraus (history : History) : Operator BK15Register :=
  xProjector history.2 *
    (historyCorrection history.1).symm.toLinearEquiv.toLinearMap *
    zProjector history.1

/-- The finite family of literal physical histories. -/
noncomputable def historyKrausFamily :
    FiniteKrausFamily History BK15Register BK15Register where
  operator := historyKraus

private theorem historyCorrection_comp_symm (outcome : ZJointSyndrome) :
    (historyCorrection outcome).toLinearEquiv.toLinearMap *
      (historyCorrection outcome).symm.toLinearEquiv.toLinearMap = 1 := by
  ext psi
  simp [Module.End.mul_apply, UnitaryTransport.symm]

private theorem adjoint_comp_projective_history
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (Z X : Operator H) (U : UnitaryTransport H H)
    (hZ : LinearMap.adjoint Z = Z) (hX : LinearMap.adjoint X = X) :
    (LinearMap.adjoint (X * U.symm.toLinearEquiv.toLinearMap * Z)).comp
        (X * U.symm.toLinearEquiv.toLinearMap * Z) =
      Z * U.toLinearEquiv.toLinearMap * X * X *
        U.symm.toLinearEquiv.toLinearMap * Z := by
  have hU : LinearMap.adjoint U.symm.toLinearEquiv.toLinearMap =
      U.toLinearEquiv.toLinearMap := by
    change LinearMap.adjoint U.toLinearEquiv.symm.toLinearMap = _
    exact U.adjoint_symm_toLinearMap
  simp only [Module.End.mul_eq_comp, LinearMap.adjoint_comp, hZ, hX, hU,
    LinearMap.comp_assoc]

private theorem historyKraus_adjoint_comp
    (zOutcome : ZJointSyndrome) (xOutcome : XJointSyndrome) :
    (LinearMap.adjoint (historyKraus (zOutcome, xOutcome))).comp
        (historyKraus (zOutcome, xOutcome)) =
      zProjector zOutcome *
        (historyCorrection zOutcome).toLinearEquiv.toLinearMap *
        xProjector xOutcome * xProjector xOutcome *
        (historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap *
      zProjector zOutcome := by
  simpa only [historyKraus] using
    adjoint_comp_projective_history
      (zProjector zOutcome) (xProjector xOutcome) (historyCorrection zOutcome)
      (zProjector_adjoint zOutcome) (xProjector_adjoint xOutcome)

/-- Both literal projective measurements and the syndrome-controlled unitary
correction form a complete physical history family. -/
theorem historyKrausFamily_complete : historyKrausFamily.Complete := by
  classical
  rw [FiniteKrausFamily.Complete, Fintype.sum_prod_type]
  calc
    (∑ zOutcome : ZJointSyndrome, ∑ xOutcome : XJointSyndrome,
        (LinearMap.adjoint (historyKrausFamily.operator (zOutcome, xOutcome))).comp
          (historyKrausFamily.operator (zOutcome, xOutcome))) =
        ∑ zOutcome : ZJointSyndrome, zProjector zOutcome := by
      apply Finset.sum_congr rfl
      intro zOutcome _
      simp only [historyKrausFamily, historyKraus_adjoint_comp]
      calc
        (∑ xOutcome : XJointSyndrome,
            zProjector zOutcome *
              (historyCorrection zOutcome).toLinearEquiv.toLinearMap *
              xProjector xOutcome * xProjector xOutcome *
              (historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap *
              zProjector zOutcome) =
            zProjector zOutcome *
              (historyCorrection zOutcome).toLinearEquiv.toLinearMap *
              (∑ xOutcome : XJointSyndrome,
                xProjector xOutcome * xProjector xOutcome) *
              (historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap *
              zProjector zOutcome := by
                simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        _ = zProjector zOutcome *
              (historyCorrection zOutcome).toLinearEquiv.toLinearMap *
              (∑ xOutcome : XJointSyndrome, xProjector xOutcome) *
              (historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap *
              zProjector zOutcome := by
                congr 3
                apply Finset.sum_congr rfl
                intro xOutcome _
                exact xProjector_idempotent xOutcome
        _ = zProjector zOutcome := by
          rw [show (∑ xOutcome : XJointSyndrome, xProjector xOutcome) = 1 by
            exact sum_xProjector_eq_one]
          calc
            zProjector zOutcome *
                (historyCorrection zOutcome).toLinearEquiv.toLinearMap * 1 *
                (historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap *
                zProjector zOutcome =
              zProjector zOutcome *
                ((historyCorrection zOutcome).toLinearEquiv.toLinearMap *
                  (historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap) *
                zProjector zOutcome := by simp only [mul_one, mul_assoc]
            _ = zProjector zOutcome * zProjector zOutcome := by
              rw [historyCorrection_comp_symm]
              simp
            _ = zProjector zOutcome :=
              zProjector_idempotent zOutcome
    _ = 1 := sum_zProjector_eq_one

/-- The two coarse source endpoints, retaining every raw rejected history. -/
noncomputable def historyInstrument :
    FiniteInstrument History DistillationOutcome BK15Register BK15Register where
  kraus := historyKrausFamily
  observe := historyOutcome

theorem historyInstrument_complete : historyInstrument.kraus.Complete := by
  change historyKrausFamily.Complete
  exact historyKrausFamily_complete

/-- The actual noisy physical input to which a source history is applied. -/
noncomputable def rawInput (epsilon : BK15Epsilon) : DensityOperator BK15Register :=
  bk15ErrorWordMixture epsilon

/-- The unnormalized accepted or rejected aggregate before any decoder. -/
noncomputable def rawEndpoint (epsilon : BK15Epsilon) (outcome : DistillationOutcome) :
    Operator BK15Register :=
  historyInstrument.branchOperator outcome (rawInput epsilon).toOperator

/-- The actual Born mass of a coarse endpoint. -/
noncomputable def endpointWeight (epsilon : BK15Epsilon) (outcome : DistillationOutcome) : Real :=
  historyInstrument.bornWeight outcome (rawInput epsilon)

/-- The complete, trace-preserving physical operation obtained by forgetting
the visible syndrome history. -/
noncomputable def historyChannel : QuantumChannel BK15Register BK15Register :=
  historyInstrument.kraus.toQuantumChannel historyInstrument_complete

theorem endpointWeight_nonneg (epsilon : BK15Epsilon)
    (outcome : DistillationOutcome) : 0 ≤ endpointWeight epsilon outcome :=
  historyInstrument.bornWeight_nonneg outcome (rawInput epsilon)

/-- The two coarse physical endpoint probabilities exhaust the complete
history instrument. -/
theorem endpointWeights_sum (epsilon : BK15Epsilon) :
    endpointWeight epsilon .accepted + endpointWeight epsilon .rejected = 1 := by
  have h := historyInstrument.sum_bornWeight_eq_one
    historyInstrument_complete (rawInput epsilon)
  rw [show (Finset.univ : Finset DistillationOutcome) =
    {.accepted, .rejected} by decide] at h
  simpa [endpointWeight] using h

set_option maxRecDepth 65536 in
@[simp] theorem rawEndpoint_eq_branchOperator (epsilon : BK15Epsilon)
    (outcome : DistillationOutcome) :
    rawEndpoint epsilon outcome =
      historyInstrument.branchOperator outcome (rawInput epsilon).toOperator :=
  rfl

/-- The two concrete branch operators reconstruct the output of the complete
physical history channel. -/
theorem historyBranchOperators_reconstruct (epsilon : BK15Epsilon) :
    historyInstrument.branchOperator .accepted (rawInput epsilon).toOperator +
        historyInstrument.branchOperator .rejected (rawInput epsilon).toOperator =
      ((historyInstrument.kraus.toQuantumChannel historyInstrument_complete).mapDensity
        (rawInput epsilon)).toOperator := by
  have h := historyInstrument.sum_branchOperator_eq_mapDensity_toOperator
    historyInstrument_complete (rawInput epsilon)
  rw [show (Finset.univ : Finset DistillationOutcome) =
    {.accepted, .rejected} by decide] at h
  simpa only [Finset.sum_insert, Finset.mem_singleton, reduceCtorEq,
    not_false_eq_true, Finset.sum_singleton] using h

/-- The accepted and rejected raw endpoint wrappers reconstruct the same
complete physical output. -/
theorem rawEndpoints_reconstruct (epsilon : BK15Epsilon) :
    rawEndpoint epsilon .accepted + rawEndpoint epsilon .rejected =
      ((historyInstrument.kraus.toQuantumChannel historyInstrument_complete).mapDensity
        (rawInput epsilon)).toOperator := by
  rw [rawEndpoint_eq_branchOperator, rawEndpoint_eq_branchOperator]
  exact historyBranchOperators_reconstruct epsilon

/-! ## Local CSS encoding and total decoder -/

/-- The source row presentation: one odd all-ones row and four even linear rows. -/
def bk15CSSRows : Triorthogonal.BinaryRowFamily Unit (Fin 4) (Fin 15) where
  oddRow _ := allOnes
  evenRow := linearGenerator

/-- The finite source rows are triorthogonal in the fixed Fin-15 convention. -/
theorem bk15CSSRows_triorthogonal : bk15CSSRows.IsTriorthogonal := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide +revert

/-- The local logical register carried by the one odd source row. -/
abbrev LogicalRegister := QubitRegister Unit

/-- The actual CSS code and normalized source-row encoding. -/
noncomputable def bk15EncodedCode : EncodedCode LogicalRegister BK15Register :=
  bk15CSSRows.encodedCode bk15CSSRows_triorthogonal

/-- The local CSS encoding viewed in the ambient fifteen-qubit register. -/
def ambientEncodingIsometry : LogicalRegister →ₗᵢ[Complex] BK15Register :=
  bk15EncodedCode.code.carrier.subtypeₗᵢ.comp
    bk15EncodedCode.encoding.toLinearIsometry

@[simp] theorem ambientEncodingIsometry_apply (psi : LogicalRegister) :
    ambientEncodingIsometry psi = (bk15EncodedCode.encoding psi : BK15Register) :=
  rfl

/-- The coherent inverse-encoding branch on the actual CSS carrier. -/
def codeDecoderBranch : BK15Register →ₗ[Complex] LogicalRegister :=
  LinearMap.adjoint ambientEncodingIsometry.toLinearMap

@[simp] theorem codeDecoderBranch_encoded (psi : LogicalRegister) :
    codeDecoderBranch (ambientEncodingIsometry psi) = psi := by
  change LinearMap.adjoint ambientEncodingIsometry.toLinearMap
    (ambientEncodingIsometry.toLinearMap psi) = psi
  exact LinearMap.congr_fun ambientEncodingIsometry.adjoint_comp_self' psi

theorem adjoint_codeDecoderBranch : LinearMap.adjoint codeDecoderBranch =
    ambientEncodingIsometry.toLinearMap := by
  rw [codeDecoderBranch, LinearMap.adjoint_adjoint]

/-- Projector onto the coherently decoded CSS carrier. -/
def decoderCodeProjector : Operator BK15Register :=
  (LinearMap.adjoint codeDecoderBranch).comp codeDecoderBranch

@[simp] theorem decoderCodeProjector_encoded (psi : LogicalRegister) :
    decoderCodeProjector (ambientEncodingIsometry psi) = ambientEncodingIsometry psi := by
  change LinearMap.adjoint codeDecoderBranch
    (codeDecoderBranch (ambientEncodingIsometry psi)) = ambientEncodingIsometry psi
  rw [codeDecoderBranch_encoded, adjoint_codeDecoderBranch]
  rfl

theorem codeDecoderBranch_comp_adjoint :
    codeDecoderBranch.comp (LinearMap.adjoint codeDecoderBranch) = 1 := by
  rw [adjoint_codeDecoderBranch, codeDecoderBranch]
  exact ambientEncodingIsometry.adjoint_comp_self'

theorem decoderCodeProjector_idempotent :
    decoderCodeProjector.comp decoderCodeProjector = decoderCodeProjector := by
  rw [decoderCodeProjector]
  calc
    ((LinearMap.adjoint codeDecoderBranch).comp codeDecoderBranch).comp
        ((LinearMap.adjoint codeDecoderBranch).comp codeDecoderBranch) =
      (LinearMap.adjoint codeDecoderBranch).comp
        ((codeDecoderBranch.comp (LinearMap.adjoint codeDecoderBranch)).comp
          codeDecoderBranch) := by
            ext psi
            rfl
    _ = (LinearMap.adjoint codeDecoderBranch).comp
          ((1 : Operator LogicalRegister).comp codeDecoderBranch) := by
            rw [codeDecoderBranch_comp_adjoint]
    _ = (LinearMap.adjoint codeDecoderBranch).comp codeDecoderBranch := by
      ext psi
      rfl

theorem decoderCodeProjector_adjoint :
    LinearMap.adjoint decoderCodeProjector = decoderCodeProjector := by
  simp [decoderCodeProjector, LinearMap.adjoint_comp]

/-- Orthogonal complement handled by the total-decoder fallback. -/
def decoderComplementProjector : Operator BK15Register := 1 - decoderCodeProjector

theorem decoderComplementProjector_adjoint :
    LinearMap.adjoint decoderComplementProjector = decoderComplementProjector := by
  simp [decoderComplementProjector, decoderCodeProjector_adjoint]

theorem decoderComplementProjector_idempotent :
    decoderComplementProjector.comp decoderComplementProjector = decoderComplementProjector := by
  ext psi
  have hprojector := LinearMap.congr_fun decoderCodeProjector_idempotent psi
  simp only [decoderComplementProjector, LinearMap.comp_apply,
    LinearMap.sub_apply, Module.End.one_apply, map_sub] at hprojector ⊢
  rw [hprojector]
  abel_nf

@[simp] theorem decoderComplementProjector_encoded (psi : LogicalRegister) :
    decoderComplementProjector (ambientEncodingIsometry psi) = 0 := by
  simp only [decoderComplementProjector, LinearMap.sub_apply, Module.End.one_apply]
  rw [decoderCodeProjector_encoded]
  abel_nf

/-- A neutral logical state used solely off the code carrier. -/
noncomputable def decoderFallbackState : LogicalRegister :=
  EuclideanSpace.basisFun (Bitstring Unit) Complex (fun _ => 0)

theorem decoderFallbackState_inner_self :
    inner Complex decoderFallbackState decoderFallbackState = 1 := by
  simp [decoderFallbackState]

private theorem decoderFallbackState_normSq : ‖decoderFallbackState‖ ^ 2 = 1 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex), decoderFallbackState_inner_self]
  norm_num

private noncomputable def decoderPhysicalBasis :=
  stdOrthonormalBasis Complex BK15Register

/-- One complement Kraus branch prepares the neutral logical state. -/
def complementDecoderBranch
    (i : Fin (Module.finrank Complex BK15Register)) :
    BK15Register →ₗ[Complex] LogicalRegister :=
  (InnerProductSpace.rankOne Complex decoderFallbackState
    (decoderComplementProjector (decoderPhysicalBasis i))).toLinearMap

theorem complementDecoderBranch_adjoint_comp
    (i : Fin (Module.finrank Complex BK15Register)) :
    (LinearMap.adjoint (complementDecoderBranch i)).comp (complementDecoderBranch i) =
      (InnerProductSpace.rankOne Complex
        (decoderComplementProjector (decoderPhysicalBasis i))
        (decoderComplementProjector (decoderPhysicalBasis i))).toLinearMap := by
  have hadjoint : LinearMap.adjoint
      ((InnerProductSpace.rankOne Complex decoderFallbackState
        (decoderComplementProjector (decoderPhysicalBasis i))).toLinearMap) =
      (InnerProductSpace.rankOne Complex
        (decoderComplementProjector (decoderPhysicalBasis i))
        decoderFallbackState).toLinearMap := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex decoderFallbackState
      (decoderComplementProjector (decoderPhysicalBasis i))).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  apply LinearMap.ext
  intro psi
  simp only [complementDecoderBranch]
  rw [hadjoint]
  have hnormSq : (↑‖decoderFallbackState‖ : Complex) ^ 2 = 1 := by
    norm_cast
    exact decoderFallbackState_normSq
  simp [LinearMap.comp_apply, hnormSq]

theorem sum_complementDecoderBranch_adjoint_comp :
    ∑ i : Fin (Module.finrank Complex BK15Register),
      (LinearMap.adjoint (complementDecoderBranch i)).comp (complementDecoderBranch i) =
        decoderComplementProjector := by
  simp_rw [complementDecoderBranch_adjoint_comp]
  calc
    (∑ i, (InnerProductSpace.rankOne Complex
      (decoderComplementProjector (decoderPhysicalBasis i))
      (decoderComplementProjector (decoderPhysicalBasis i))).toLinearMap) =
      decoderComplementProjector.comp (LinearMap.adjoint decoderComplementProjector) := by
        apply LinearMap.ext
        intro psi
        simp only [LinearMap.sum_apply, LinearMap.comp_apply]
        rw [← decoderPhysicalBasis.sum_repr'
          (LinearMap.adjoint decoderComplementProjector psi)]
        simp only [map_sum, map_smul]
        apply Finset.sum_congr rfl
        intro i _
        rw [LinearMap.adjoint_inner_right]
        rfl
    _ = decoderComplementProjector.comp decoderComplementProjector := by
      rw [decoderComplementProjector_adjoint]
    _ = decoderComplementProjector := decoderComplementProjector_idempotent

/-- Finite Kraus completion of inverse encoding to a total CSS decoder. -/
def decoderKrausFamily :
    FiniteKrausFamily (Sum Unit (Fin (Module.finrank Complex BK15Register)))
      BK15Register LogicalRegister where
  operator
    | .inl _ => codeDecoderBranch
    | .inr i => complementDecoderBranch i

theorem decoderKrausFamily_complete : decoderKrausFamily.Complete := by
  rw [FiniteKrausFamily.Complete, Fintype.sum_sum_type]
  change (∑ _ : Unit, decoderCodeProjector) +
      (∑ i : Fin (Module.finrank Complex BK15Register),
        (LinearMap.adjoint (complementDecoderBranch i)).comp (complementDecoderBranch i)) = 1
  rw [Fintype.sum_unique, sum_complementDecoderBranch_adjoint_comp]
  simp [decoderComplementProjector]

/-- The total decoder: inverse encoding on the CSS carrier and a neutral
off-carrier fallback. -/
noncomputable def decoderChannel : QuantumChannel BK15Register LogicalRegister :=
  decoderKrausFamily.toQuantumChannel decoderKrausFamily_complete

private theorem sandwich_rankOne {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (L : H →ₗ[Complex] K) (psi : H) :
    L.comp ((InnerProductSpace.rankOne Complex psi psi).toLinearMap.comp
      (LinearMap.adjoint L)) =
      (InnerProductSpace.rankOne Complex (L psi) (L psi)).toLinearMap := by
  ext x
  simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    LinearMap.adjoint_inner_right]

theorem decoderChannel_rankOne_encoded (psi : LogicalRegister) :
    decoderChannel (InnerProductSpace.rankOne Complex
      (ambientEncodingIsometry psi) (ambientEncodingIsometry psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  rw [decoderChannel, FiniteKrausFamily.toQuantumChannel_apply_sum,
    Fintype.sum_sum_type]
  simp only [decoderKrausFamily]
  simp_rw [sandwich_rankOne]
  rw [Fintype.sum_unique]
  simp only [codeDecoderBranch_encoded]
  have hcomplement : ∀ i, complementDecoderBranch i (ambientEncodingIsometry psi) = 0 := by
    intro i
    have hinner : inner Complex (decoderComplementProjector (decoderPhysicalBasis i))
        (ambientEncodingIsometry psi) = 0 := by
      rw [← LinearMap.adjoint_inner_right, decoderComplementProjector_adjoint,
        decoderComplementProjector_encoded]
      simp
    change inner Complex (decoderComplementProjector (decoderPhysicalBasis i))
      (ambientEncodingIsometry psi) • decoderFallbackState = 0
    rw [hinner]
    simp
  simp_rw [hcomplement]
  simp

/-! ## Honest positive-mass history witnesses -/

/-- A concrete nonzero state in the local CSS carrier. -/
private noncomputable def cssWitnessState : BK15Register :=
  ambientEncodingIsometry decoderFallbackState

private theorem cssWitnessState_ne_zero : cssWitnessState ≠ 0 := by
  intro hzero
  have hlogical : decoderFallbackState = 0 :=
    ambientEncodingIsometry.injective (by simpa [cssWitnessState] using hzero)
  have hinner := decoderFallbackState_inner_self
  rw [hlogical] at hinner
  simp at hinner

private theorem cssWitness_fixed (P : Binary (Fin 15))
    (hP : P ∈ binaryCSSCheckSet bk15CSSRows.evenCode
      bk15CSSRows.rowCode.dual) :
    toQubitOperator P cssWitnessState = cssWitnessState := by
  have hmem : cssWitnessState ∈ bk15EncodedCode.code.carrier := by
    change (bk15EncodedCode.encoding decoderFallbackState : BK15Register) ∈
      bk15EncodedCode.code.carrier
    exact (bk15EncodedCode.encoding decoderFallbackState).property
  exact (mem_binaryCSSQuantumCodeOfDualLe_carrier
    bk15CSSRows.evenCode bk15CSSRows.rowCode.dual
    bk15CSSRows.cssDualContainment cssWitnessState).1 hmem P hP

private theorem cssWitness_xCheck_fixed (check : XCheckIndex) :
    toHermitianQubitOperator (xChecks check) cssWitnessState = cssWitnessState := by
  have hP : xChecks check ∈ binaryCSSCheckSet bk15CSSRows.evenCode
      bk15CSSRows.rowCode.dual := by
    exact Or.inl ⟨linearGenerator check,
      bk15CSSRows.evenRow_mem_evenCode check, rfl⟩
  simpa [xChecks, toHermitianQubitOperator, hermitianPhaseScalar,
    binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport,
    binarySupport] using cssWitness_fixed (xChecks check) hP

set_option maxHeartbeats 800000 in
private theorem l2Generator_mem_cssRowCodeDual (check : ZCheckIndex) :
    l2Generator check ∈ bk15CSSRows.rowCode.dual.carrier := by
  rw [Coding.LinearCode.mem_dual]
  intro word hword
  change word ∈ Submodule.span (ZMod 2) (Set.range bk15CSSRows.row) at hword
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hword
  · intro generator hgenerator
    rcases hgenerator with ⟨tag, rfl⟩
    rcases tag with logical | stabilizer
    · cases logical
      native_decide +revert
    · native_decide +revert
  · simp
  · intro left right _hleft _hright hleft hright
    calc
      Coding.wordPairing (l2Generator check) (left + right) =
          Coding.wordPairing (l2Generator check) left +
            Coding.wordPairing (l2Generator check) right := by
              exact map_add (Coding.wordPairing (l2Generator check)) left right
      _ = 0 := by rw [hleft, hright, add_zero]
  · intro scalar word _hword hword
    calc
      Coding.wordPairing (l2Generator check) (scalar • word) =
          scalar • Coding.wordPairing (l2Generator check) word := by
            exact map_smul (Coding.wordPairing (l2Generator check)) scalar word
      _ = 0 := by rw [hword, smul_zero]

set_option maxRecDepth 65536 in
private theorem bk15IdealState_apply_product
    (bits : Bitstring (Fin 15)) :
    bk15ErrorWordState (0 : Word) bits =
      ∏ site : Fin 15, aZeroState (bits site) := by
  simpa [aInputState] using
    bk15ErrorWordState_apply_product (0 : Word) bits

@[simp] private theorem phaseState_apply_bit
    (theta : Real) (bit : Fin 2) :
    OneQubitMagic.phaseState theta bit =
      (Real.sqrt 2 : Complex)⁻¹ *
        OneQubitMagic.phaseAmplitude theta ^ bit.val := by
  fin_cases bit <;>
    simp [OneQubitMagic.phaseState_apply_zero,
      OneQubitMagic.phaseState_apply_one]

private theorem bit_sum_eq_hammingWeight
    (bits : Bitstring (Fin 15)) :
    (∑ site : Fin 15, (bits site).val) =
      Coding.HammingWeight (bitstringWordEquiv (Fin 15) bits) := by
  classical
  rw [Coding.HammingWeight, Coding.hammingSupport,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro site _
  generalize hbit : bits site = bit
  fin_cases bit
  · simp [hbit]
    rfl
  · simp [hbit]
    exact one_ne_zero

set_option maxRecDepth 65536 in
private theorem bk15IdealState_apply
    (bits : Bitstring (Fin 15)) :
    bk15ErrorWordState (0 : Word) bits =
      (Real.sqrt 2 : Complex)⁻¹ ^ 15 *
        OneQubitMagic.phaseAmplitude (Real.pi / 4) ^
          Coding.HammingWeight (bitstringWordEquiv (Fin 15) bits) := by
  rw [bk15IdealState_apply_product]
  simp_rw [aZeroState, phaseState_apply_bit]
  rw [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_pow_eq_pow_sum, Finset.card_univ, Fintype.card_fin,
    bit_sum_eq_hammingWeight]

private theorem bk15_evenCode_eq_L1 :
    bk15CSSRows.evenCode.carrier = L1.carrier := by
  change Submodule.span Bit (Set.range linearGenerator) =
    LinearMap.range l1CoefficientMap
  ext word
  constructor
  · intro hword
    obtain ⟨a, ha⟩ :=
      (Submodule.mem_span_range_iff_exists_fun Bit).1 hword
    refine ⟨a, ?_⟩
    rw [l1CoefficientMap_eq_sum]
    exact ha
  · rintro ⟨a, rfl⟩
    apply (Submodule.mem_span_range_iff_exists_fun Bit).2
    exact ⟨a, (l1CoefficientMap_eq_sum a).symm⟩

private theorem bk15_evenCode_card :
    Nat.card bk15CSSRows.evenCode.carrier = 16 := by
  rw [bk15_evenCode_eq_L1,
    Module.natCard_eq_pow_finrank (K := Bit) (V := L1.carrier)]
  change Nat.card Bit ^ Coding.Dimension L1 = 16
  rw [l1_dimension]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

private theorem bk15_cssNormalizationScalar :
    bk15CSSRows.cssNormalizationScalar = (4 : Complex)⁻¹ := by
  rw [Triorthogonal.BinaryRowFamily.cssNormalizationScalar,
    bk15_evenCode_card]
  norm_num

private theorem logicalUniformScalar_unit :
    Triorthogonal.BinaryRowFamily.logicalUniformScalar Unit =
      (Real.sqrt 2 : Complex)⁻¹ := by
  rw [Triorthogonal.BinaryRowFamily.logicalUniformScalar]
  norm_num [Nat.card_eq_fintype_card]

private noncomputable def logicalNegativeAState : LogicalRegister :=
  WithLp.toLp 2 fun bits =>
    (Real.sqrt 2 : Complex)⁻¹ *
      OneQubitMagic.phaseAmplitude (-Real.pi / 4) ^ (bits ()).val

@[simp] private theorem logicalNegativeAState_apply
    (bits : Bitstring Unit) :
    logicalNegativeAState bits =
      (Real.sqrt 2 : Complex)⁻¹ *
        OneQubitMagic.phaseAmplitude (-Real.pi / 4) ^ (bits ()).val :=
  rfl

private theorem logical_const_bit_val (c : Bit) :
    (((bitstringWordEquiv Unit).symm (fun _ => c)) ()).val = c.val := by
  fin_cases c <;> rfl

private theorem logicalLabel_l1_plus_allOnes
    (a : Fin 4 → Bit) (c : Bit)
    (hmem : l1CoefficientMap a + c • allOnes ∈
      bk15CSSRows.rowCode.dual.dual.carrier) :
    (bk15CSSRows.logicalBasisEquivLogicalQuotient
        bk15CSSRows_triorthogonal).symm
        (Submodule.Quotient.mk
          (⟨l1CoefficientMap a + c • allOnes, hmem⟩ :
            bk15CSSRows.rowCode.dual.dual.carrier)) =
      (bitstringWordEquiv Unit).symm (fun _ => c) := by
  apply (bk15CSSRows.logicalBasisEquivLogicalQuotient
    bk15CSSRows_triorthogonal).injective
  rw [Equiv.apply_symm_apply]
  simp only [Triorthogonal.BinaryRowFamily.logicalBasisEquivLogicalQuotient,
    LinearEquiv.coe_toEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply]
  rw [Triorthogonal.BinaryRowFamily.oddWordToLogicalQuotient]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq]
  have hl1 : l1CoefficientMap a ∈ bk15CSSRows.evenCode.carrier := by
    rw [bk15_evenCode_eq_L1]
    exact ⟨a, rfl⟩
  change l1CoefficientMap a + c • allOnes -
      bk15CSSRows.oddCombination (fun _ => c) ∈
    bk15CSSRows.evenCode.carrier
  have hodd : bk15CSSRows.oddCombination (fun _ => c) =
      c • allOnes := by
    rw [Triorthogonal.BinaryRowFamily.oddCombination_apply]
    simp [bk15CSSRows]
  rw [hodd, add_sub_cancel_right]
  exact hl1

private theorem phaseAmplitude_two_pi_mul_int_bk15 (k : Int) :
    OneQubitMagic.phaseAmplitude ((2 * Real.pi) * (k : Real)) = 1 := by
  unfold OneQubitMagic.phaseAmplitude
  convert Complex.exp_int_mul_two_pi_mul_I k using 1
  all_goals push_cast
  all_goals ring_nf

private theorem phaseAmplitude_pi_div_four_int_eq_of_cast_eq_bk15
    (m n : Int) (h : (m : ZMod 8) = (n : ZMod 8)) :
    OneQubitMagic.phaseAmplitude (Real.pi / 4 * (m : Real)) =
      OneQubitMagic.phaseAmplitude (Real.pi / 4 * (n : Real)) := by
  have hmod : m ≡ n [ZMOD (8 : Int)] :=
    (ZMod.intCast_eq_intCast_iff m n 8).mp h
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod
  have hnm : n = m + 8 * k := by omega
  have hangle :
      Real.pi / 4 * (n : Real) =
        Real.pi / 4 * (m : Real) + (2 * Real.pi) * (k : Real) := by
    rw [hnm]
    push_cast
    ring
  rw [hangle, OneQubitMagic.phaseAmplitude_add,
    phaseAmplitude_two_pi_mul_int_bk15, mul_one]

private theorem phaseAmplitude_pow_bk15 (theta : Real) (n : Nat) :
    OneQubitMagic.phaseAmplitude theta ^ n =
      OneQubitMagic.phaseAmplitude ((n : Real) * theta) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ← OneQubitMagic.phaseAmplitude_add]
      congr 2
      push_cast
      ring

private theorem l1_weight_cast8 (a : Fin 4 → Bit) :
    (Coding.HammingWeight (l1CoefficientMap a) : ZMod 8) = 0 := by
  native_decide +revert

private theorem l1_plus_allOnes_weight_cast8 (a : Fin 4 → Bit) :
    (Coding.HammingWeight (l1CoefficientMap a + allOnes) : ZMod 8) = -1 := by
  native_decide +revert

private theorem l1_plus_allOnes_phase (a : Fin 4 → Bit) (c : Bit) :
    OneQubitMagic.phaseAmplitude (Real.pi / 4) ^
        Coding.HammingWeight (l1CoefficientMap a + c • allOnes) =
      OneQubitMagic.phaseAmplitude (-Real.pi / 4) ^ c.val := by
  by_cases hc : c = 0
  · rw [hc]
    simp only [zero_smul, add_zero, ZMod.val_zero, pow_zero]
    rw [phaseAmplitude_pow_bk15]
    have hphase := phaseAmplitude_pi_div_four_int_eq_of_cast_eq_bk15
      (Coding.HammingWeight (l1CoefficientMap a) : Int) 0 (by
        simpa using l1_weight_cast8 a)
    simpa [mul_comm] using hphase
  · have hc1 : c = 1 := by
      fin_cases c
      · exact (hc rfl).elim
      · rfl
    rw [hc1]
    simp only [one_smul, ZMod.val_one, pow_one]
    rw [phaseAmplitude_pow_bk15]
    have hphase := phaseAmplitude_pi_div_four_int_eq_of_cast_eq_bk15
      (Coding.HammingWeight (l1CoefficientMap a + allOnes) : Int) (-1) (by
        simpa using l1_plus_allOnes_weight_cast8 a)
    calc
      OneQubitMagic.phaseAmplitude
          ((Coding.HammingWeight (l1CoefficientMap a + allOnes) : Real) *
            (Real.pi / 4)) =
        OneQubitMagic.phaseAmplitude
          (Real.pi / 4 *
            ((Coding.HammingWeight (l1CoefficientMap a + allOnes) : Int) : Real)) := by
              congr 1
              push_cast
              ring
      _ = OneQubitMagic.phaseAmplitude
          (Real.pi / 4 * ((-1 : Int) : Real)) := hphase
      _ = OneQubitMagic.phaseAmplitude (-Real.pi / 4) := by
        congr 1
        norm_num
        ring

private theorem inv_sqrt_two_pow_fifteen :
    (Real.sqrt 2 : Complex)⁻¹ ^ 15 =
      (32 : Complex)⁻¹ *
        ((4 : Complex)⁻¹ * (Real.sqrt 2 : Complex)⁻¹) := by
  have hsqrt_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
    exact_mod_cast OneQubitMagic.sqrt_two_pos.ne'
  have hsqrt_sq :
      (Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex) = 2 := by
    exact_mod_cast OneQubitMagic.sqrt_two_mul_self
  field_simp [hsqrt_ne]
  calc
    (32 : Complex) * 4 = 128 := by norm_num
    _ = (Real.sqrt 2 : Complex) ^ 14 := by
      symm
      calc
        (Real.sqrt 2 : Complex) ^ 14 =
            ((Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex)) ^ 7 := by ring
        _ = 128 := by rw [hsqrt_sq]; norm_num

private theorem l2Syndrome_eq_zero_of_mem_rowCode_doubleDual
    {word : Word} (hword : word ∈
      bk15CSSRows.rowCode.dual.dual.carrier) :
    l2Syndrome word = 0 := by
  funext check
  change Coding.wordPairing word (l2Generator check) = 0
  exact bk15CSSRows.rowCode.dual.orthogonal_of_mem_dual hword
    (l2Generator_mem_cssRowCodeDual check)

private theorem mem_rowCode_doubleDual_of_mem_L2_dual
    {word : Word} (hword : word ∈ L2.dual.carrier) :
    word ∈ bk15CSSRows.rowCode.dual.dual.carrier := by
  obtain ⟨a, c, rfl⟩ :=
    (mem_l2_dual_iff_exists_l1_plus_allOnes word).1 hword
  have hl1Even : l1CoefficientMap a ∈ bk15CSSRows.evenCode.carrier := by
    rw [bk15_evenCode_eq_L1]
    exact ⟨a, rfl⟩
  have hl1Row : l1CoefficientMap a ∈ bk15CSSRows.rowCode.carrier := by
    rw [bk15CSSRows.rowCode_eq_evenCode_sup_oddCode]
    exact Submodule.mem_sup_left hl1Even
  have hallRow : allOnes ∈ bk15CSSRows.rowCode.carrier := by
    change bk15CSSRows.oddRow () ∈ bk15CSSRows.rowCode.carrier
    exact bk15CSSRows.row_mem_rowCode (.inl ())
  have hrow : l1CoefficientMap a + c • allOnes ∈
      bk15CSSRows.rowCode.carrier :=
    bk15CSSRows.rowCode.carrier.add_mem hl1Row
      (bk15CSSRows.rowCode.carrier.smul_mem c hallRow)
  refine (bk15CSSRows.rowCode.dual.mem_dual _).2 ?_
  intro dualWord hdualWord
  exact bk15CSSRows.rowCode.dual_orthogonal hrow hdualWord

private theorem zeroZProjectedIdeal :
    zProjector (signSyndrome (0 : ZCheckIndex → Bit))
        (bk15ErrorWordState (0 : Word)) =
      (32 : Complex)⁻¹ •
        ambientEncodingIsometry logicalNegativeAState := by
  ext bits
  rw [zProjector_zero_apply, bk15IdealState_apply]
  by_cases hzero : l2Syndrome (bitstringWordEquiv (Fin 15) bits) = 0
  · rw [if_pos hzero]
    have hL2 : bitstringWordEquiv (Fin 15) bits ∈ L2.dual.carrier := by
      rw [l2_dual_carrier_eq_l2Syndrome_ker]
      exact hzero
    have hrow : bitstringWordEquiv (Fin 15) bits ∈
        bk15CSSRows.rowCode.dual.dual.carrier :=
      mem_rowCode_doubleDual_of_mem_L2_dual hL2
    obtain ⟨a, c, hac⟩ :=
      (mem_l2_dual_iff_exists_l1_plus_allOnes
        (bitstringWordEquiv (Fin 15) bits)).1 hL2
    simp only [PiLp.smul_apply, smul_eq_mul, ambientEncodingIsometry_apply]
    change _ = (32 : Complex)⁻¹ *
      (bk15CSSRows.encoding bk15CSSRows_triorthogonal
        logicalNegativeAState : BK15Register) bits
    rw [bk15CSSRows.encoding_apply_of_mem
      bk15CSSRows_triorthogonal logicalNegativeAState hrow]
    have hrowDecomp : l1CoefficientMap a + c • allOnes ∈
        bk15CSSRows.rowCode.dual.dual.carrier := by
      rw [← hac]
      exact hrow
    have hsubtype :
        (⟨bitstringWordEquiv (Fin 15) bits, hrow⟩ :
            bk15CSSRows.rowCode.dual.dual.carrier) =
          ⟨l1CoefficientMap a + c • allOnes, hrowDecomp⟩ :=
      Subtype.ext hac
    have hlabel :
        (bk15CSSRows.logicalBasisEquivLogicalQuotient
            bk15CSSRows_triorthogonal).symm
            (Submodule.Quotient.mk
              (⟨bitstringWordEquiv (Fin 15) bits, hrow⟩ :
                bk15CSSRows.rowCode.dual.dual.carrier)) =
          (bitstringWordEquiv Unit).symm (fun _ => c) := by
      calc
        _ = (bk15CSSRows.logicalBasisEquivLogicalQuotient
              bk15CSSRows_triorthogonal).symm
              (Submodule.Quotient.mk
                (⟨l1CoefficientMap a + c • allOnes, hrowDecomp⟩ :
                  bk15CSSRows.rowCode.dual.dual.carrier)) :=
            congrArg
              (fun value : bk15CSSRows.rowCode.dual.dual.carrier =>
                (bk15CSSRows.logicalBasisEquivLogicalQuotient
                  bk15CSSRows_triorthogonal).symm
                  (Submodule.Quotient.mk value)) hsubtype
        _ = _ := logicalLabel_l1_plus_allOnes a c hrowDecomp
    have hweight :
        Coding.HammingWeight (bitstringWordEquiv (Fin 15) bits) =
          Coding.HammingWeight (l1CoefficientMap a + c • allOnes) :=
      congrArg Coding.HammingWeight hac
    rw [hweight, hlabel, logicalNegativeAState_apply,
      l1_plus_allOnes_phase, bk15_cssNormalizationScalar,
      inv_sqrt_two_pow_fifteen, logical_const_bit_val]
    ring
  · rw [if_neg hzero]
    have hrow : bitstringWordEquiv (Fin 15) bits ∉
        bk15CSSRows.rowCode.dual.dual.carrier := by
      intro hmem
      exact hzero (l2Syndrome_eq_zero_of_mem_rowCode_doubleDual hmem)
    simp only [PiLp.smul_apply, smul_eq_mul, ambientEncodingIsometry_apply]
    change 0 = (32 : Complex)⁻¹ *
      (bk15CSSRows.encoding bk15CSSRows_triorthogonal
        logicalNegativeAState : BK15Register) bits
    rw [bk15CSSRows.encoding_apply_of_not_mem
      bk15CSSRows_triorthogonal logicalNegativeAState hrow]
    simp

private theorem cssWitness_zCheck_fixed (check : ZCheckIndex) :
    toHermitianQubitOperator (zChecks check) cssWitnessState = cssWitnessState := by
  have hz : l2Generator check ∈ bk15CSSRows.rowCode.dual.carrier :=
    l2Generator_mem_cssRowCodeDual check
  have hP : zChecks check ∈ binaryCSSCheckSet bk15CSSRows.evenCode
      bk15CSSRows.rowCode.dual := by
    exact Or.inr ⟨l2Generator check, hz, rfl⟩
  simpa [zChecks, toHermitianQubitOperator, hermitianPhaseScalar,
    binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport,
    binarySupport] using cssWitness_fixed (zChecks check) hP

private theorem cssWitness_zProjector_zero :
    zProjector (signSyndrome (0 : ZCheckIndex → Bit)) cssWitnessState =
      cssWitnessState := by
  apply (jointStabilizerProjector_fixed_iff zChecks zChecks_commute
    (signSyndrome (0 : ZCheckIndex → Bit)) cssWitnessState).2
  intro check
  simpa [signSyndrome, bitToSign, StabilizerOutcome.sign] using
    cssWitness_zCheck_fixed check

private theorem cssWitness_xProjector_zero :
    xProjector (signSyndrome (0 : XCheckIndex → Bit)) cssWitnessState =
      cssWitnessState := by
  apply (jointStabilizerProjector_fixed_iff xChecks xChecks_commute
    (signSyndrome (0 : XCheckIndex → Bit)) cssWitnessState).2
  intro check
  simpa [signSyndrome, bitToSign, StabilizerOutcome.sign] using
    cssWitness_xCheck_fixed check

private theorem aWordCorrectionTransport_zero_symm_apply (psi : BK15Register) :
    (aWordCorrectionTransport (0 : Word)).symm psi = psi := by
  have hfix := aWordCorrectionTransport_zero_apply
    ((aWordCorrectionTransport (0 : Word)).symm psi)
  simpa [UnitaryTransport.symm] using hfix.symm

private theorem historyCorrection_zero_symm_apply (psi : BK15Register) :
    (historyCorrection (signSyndrome (0 : ZCheckIndex → Bit))).symm psi = psi := by
  simpa [historyCorrection] using aWordCorrectionTransport_zero_symm_apply psi

private noncomputable def acceptedWitnessHistory : History :=
  (signSyndrome (0 : ZCheckIndex → Bit),
    signSyndrome (0 : XCheckIndex → Bit))

private theorem acceptedWitnessHistory_outcome :
    historyOutcome acceptedWitnessHistory = .accepted := by
  simp [acceptedWitnessHistory, historyOutcome]

private theorem acceptedWitnessHistory_apply :
    historyKraus acceptedWitnessHistory cssWitnessState = cssWitnessState := by
  simp only [acceptedWitnessHistory, historyKraus, Module.End.mul_apply]
  rw [cssWitness_zProjector_zero]
  change xProjector (signSyndrome (0 : XCheckIndex → Bit))
    ((historyCorrection (signSyndrome (0 : ZCheckIndex → Bit))).symm
      cssWitnessState) = cssWitnessState
  rw [historyCorrection_zero_symm_apply, cssWitness_xProjector_zero]

private theorem acceptedWitnessHistory_nonzero :
    historyKraus acceptedWitnessHistory ≠ 0 := by
  intro hzero
  have happly := LinearMap.congr_fun hzero cssWitnessState
  rw [acceptedWitnessHistory_apply] at happly
  exact cssWitnessState_ne_zero happly

private noncomputable def cssZErrorState (error : Word) : BK15Register :=
  toQubitOperator (cssZCheck error) cssWitnessState

private theorem cssZErrorState_ne_zero (error : Word) :
    cssZErrorState error ≠ 0 := by
  intro hzero
  have happly := LinearMap.congr_fun
    (toQubitOperator_adjoint_comp_self (cssZCheck error)) cssWitnessState
  simp only [LinearMap.comp_apply, Module.End.one_apply] at happly
  rw [show toQubitOperator (cssZCheck error) cssWitnessState = 0 by
    simpa [cssZErrorState] using hzero] at happly
  simp at happly
  exact cssWitnessState_ne_zero happly.symm

private theorem cssZErrorState_zCheck_fixed (error : Word)
    (check : ZCheckIndex) :
    toHermitianQubitOperator (zChecks check) (cssZErrorState error) =
      cssZErrorState error := by
  have hHermitian :
      toHermitianQubitOperator (zChecks check) =
        toQubitOperator (zChecks check) := by
    simp [zChecks, toHermitianQubitOperator, hermitianPhaseScalar,
      binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport,
      binarySupport]
  rw [hHermitian]
  have hfixed :
      toQubitOperator (zChecks check) cssWitnessState = cssWitnessState := by
    simpa [zChecks, toHermitianQubitOperator, hermitianPhaseScalar,
      binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport,
      binarySupport] using cssWitness_zCheck_fixed check
  have hcomm := toQubitOperator_commute_of_commutes
    (zChecks check) (cssZCheck error)
    (cssZCheck_commutes_cssZCheck _ _)
  have happly := LinearMap.congr_fun hcomm cssWitnessState
  simp only [Module.End.mul_apply] at happly
  rw [hfixed] at happly
  simpa [cssZErrorState] using happly

private theorem cssZErrorState_xCheck_eigen (error : Word)
    (check : XCheckIndex) :
    toHermitianQubitOperator (xChecks check) (cssZErrorState error) =
      (signSyndrome (l1Syndrome error) check).sign • cssZErrorState error := by
  have hfixed := cssWitness_xCheck_fixed check
  have hHermitian :
      toHermitianQubitOperator (xChecks check) =
        toQubitOperator (xChecks check) := by
    simp [xChecks, toHermitianQubitOperator, hermitianPhaseScalar,
      binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport,
      binarySupport]
  rw [hHermitian]
  have hfixed' :
      toQubitOperator (cssXCheck (linearGenerator check)) cssWitnessState =
        cssWitnessState := by
    simpa [xChecks, toHermitianQubitOperator, hermitianPhaseScalar,
      binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport,
      binarySupport] using hfixed
  by_cases hpair : Coding.wordPairing error (linearGenerator check) = 0
  · have hdot : error ⬝ᵥ linearGenerator check = 0 := by
      simpa [Coding.wordPairing_apply] using hpair
    have hpair' : Coding.wordPairing (linearGenerator check) error = 0 := by
      simpa [Coding.wordPairing_apply, dotProduct_comm] using hpair
    have hcomm :=
      cssXCheck_toQubitOperator_commute_cssZCheck_of_wordPairing_eq_zero hpair'
    have happly := LinearMap.congr_fun hcomm cssWitnessState
    rw [Module.End.mul_apply, Module.End.mul_apply, hfixed'] at happly
    have hsign :
        (signSyndrome (l1Syndrome error) check).sign = 1 := by
      simp [signSyndrome, bitToSign, l1Syndrome, hdot,
        StabilizerOutcome.sign]
    rw [hsign]
    simp only [one_smul]
    change toQubitOperator (xChecks check)
        (toQubitOperator (cssZCheck error) cssWitnessState) = _
    simpa [xChecks, cssZErrorState] using happly
  · have hdot : error ⬝ᵥ linearGenerator check ≠ 0 := by
      simpa [Coding.wordPairing_apply] using hpair
    have hpair' : Coding.wordPairing (linearGenerator check) error ≠ 0 := by
      simpa [Coding.wordPairing_apply, dotProduct_comm] using hpair
    have hnotcomm :
        ¬ Commutes (cssXCheck (linearGenerator check)) (cssZCheck error) := by
      simpa [cssXCheck, cssZCheck, Commutes,
        Coding.symplecticForm_x_zero_zero_z_eq_wordPairing] using hpair'
    have hanti := toQubitOperator_anticommute_of_not_commutes
      (cssXCheck (linearGenerator check)) (cssZCheck error) hnotcomm
    have happly := LinearMap.congr_fun hanti cssWitnessState
    simp only [LinearMap.neg_apply, Module.End.mul_apply] at happly
    rw [hfixed'] at happly
    have hsign :
        (signSyndrome (l1Syndrome error) check).sign = -1 := by
      simp [signSyndrome, bitToSign, l1Syndrome, hdot,
        StabilizerOutcome.sign]
    rw [hsign]
    simp only [neg_one_smul]
    change toQubitOperator (xChecks check)
        (toQubitOperator (cssZCheck error) cssWitnessState) = _
    simpa [xChecks, cssZErrorState] using happly

private theorem cssZErrorState_zProjector_zero (error : Word) :
    zProjector (signSyndrome (0 : ZCheckIndex → Bit)) (cssZErrorState error) =
      cssZErrorState error := by
  apply (jointStabilizerProjector_fixed_iff zChecks zChecks_commute
    (signSyndrome (0 : ZCheckIndex → Bit)) (cssZErrorState error)).2
  intro check
  simpa [signSyndrome, bitToSign, StabilizerOutcome.sign] using
    cssZErrorState_zCheck_fixed error check

private theorem cssZErrorState_xProjector_matching (error : Word) :
    xProjector (signSyndrome (l1Syndrome error)) (cssZErrorState error) =
      cssZErrorState error := by
  apply (jointStabilizerProjector_fixed_iff xChecks xChecks_commute
    (signSyndrome (l1Syndrome error)) (cssZErrorState error)).2
  exact cssZErrorState_xCheck_eigen error

private noncomputable def rejectedWitnessHistory (site : Fin 15) : History :=
  (signSyndrome (0 : ZCheckIndex → Bit),
    signSyndrome (l1Syndrome (oneSiteWord site)))

private theorem rejectedWitnessHistory_outcome (site : Fin 15) :
    historyOutcome (rejectedWitnessHistory site) = .rejected := by
  simp [rejectedWitnessHistory, historyOutcome,
    oneSiteWord_l1Syndrome_ne_zero site]

private theorem rejectedWitnessHistory_apply (site : Fin 15) :
    historyKraus (rejectedWitnessHistory site)
        (cssZErrorState (oneSiteWord site)) =
      cssZErrorState (oneSiteWord site) := by
  simp only [rejectedWitnessHistory, historyKraus, Module.End.mul_apply]
  rw [cssZErrorState_zProjector_zero]
  change xProjector (signSyndrome (l1Syndrome (oneSiteWord site)))
    ((historyCorrection (signSyndrome (0 : ZCheckIndex → Bit))).symm
      (cssZErrorState (oneSiteWord site))) = _
  rw [historyCorrection_zero_symm_apply, cssZErrorState_xProjector_matching]

private theorem rejectedWitnessHistory_nonzero (site : Fin 15) :
    historyKraus (rejectedWitnessHistory site) ≠ 0 := by
  intro hzero
  have happly := LinearMap.congr_fun hzero
    (cssZErrorState (oneSiteWord site))
  rw [rejectedWitnessHistory_apply] at happly
  exact cssZErrorState_ne_zero (oneSiteWord site) happly

/-- The actual noisy input is the finite rank-one A-basis mixture with its
literal independent-word weights. -/
theorem rawInput_toOperator_sum (epsilon : BK15Epsilon) :
    (rawInput epsilon).toOperator =
      ∑ word : Word, (bk15WordWeight epsilon word : Complex) •
        (InnerProductSpace.rankOne Complex
          (bk15ErrorWordState word) (bk15ErrorWordState word)).toLinearMap := by
  simp [rawInput, bk15ErrorWordMixture, bk15FlatErrorWordMixture,
    DensityOperator.convexCombination_toOperator,
    DensityOperator.convexCombinationOperator,
    bk15ErrorWordDensity_toOperator_rankOne]

private theorem comp_sum {H K L : Type*} {index : Type*}
    [Fintype index]
    [AddCommMonoid H] [AddCommMonoid K] [AddCommMonoid L]
    [Module Complex H] [Module Complex K] [Module Complex L]
    (A : K →ₗ[Complex] L) (B : index → H →ₗ[Complex] K) :
    A.comp (∑ i, B i) = ∑ i, A.comp (B i) := by
  ext x
  simp

private theorem sum_comp {H K L : Type*} {index : Type*}
    [Fintype index]
    [AddCommMonoid H] [AddCommMonoid K] [AddCommMonoid L]
    [Module Complex H] [Module Complex K] [Module Complex L]
    (A : index → K →ₗ[Complex] L) (B : H →ₗ[Complex] K) :
    (∑ i, A i).comp B = ∑ i, (A i).comp B := by
  ext x
  simp

/-- Each coarse Born weight is the sum of the physical wordwise squared
history amplitudes selected by that outcome. -/
theorem endpointWeight_eq_history_word_sum (epsilon : BK15Epsilon)
    (outcome : DistillationOutcome) :
    endpointWeight epsilon outcome =
      ∑ history : History, if historyOutcome history = outcome then
        ∑ word : Word, bk15WordWeight epsilon word *
          ‖historyKraus history (bk15ErrorWordState word)‖ ^ 2
      else 0 := by
  classical
  unfold endpointWeight FiniteInstrument.bornWeight
  rw [FiniteInstrument.branchOperator_apply, rawInput_toOperator_sum]
  simp only [historyInstrument, historyKrausFamily]
  rw [map_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro history _
  by_cases hvisible : historyOutcome history = outcome
  · erw [if_pos hvisible, if_pos hvisible]
    rw [sum_comp, comp_sum, map_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro word _
    rw [LinearMap.smul_comp, LinearMap.comp_smul,
      sandwich_rankOne, map_smul, InnerProductSpace.trace_rankOne,
      inner_self_eq_norm_sq_to_K]
    simp
    left
    simp [pow_two, Complex.mul_re]
  · erw [if_neg hvisible, if_neg hvisible]
    simp

/-- Every A-basis bit has positive weight in the strict physical interval. -/
theorem aInputWeight_pos (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) (bit : Fin 2) :
    0 < aInputWeight epsilon bit := by
  fin_cases bit
  · change 0 < epsilon.cleanWeight
    unfold BK15Epsilon.cleanWeight
    linarith [epsilon.le_half]
  · exact hpositive

/-- Every physical A-error word has positive independent probability when the
site error parameter is positive. -/
theorem bk15WordWeight_pos (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) (word : Word) :
    0 < bk15WordWeight epsilon word := by
  unfold bk15WordWeight
  exact Finset.prod_pos fun site _ =>
    aInputWeight_pos epsilon hpositive (word site)

private theorem exists_basis_word_not_annihilated (L : Operator BK15Register)
    (hL : L ≠ 0) :
    ∃ word : Word, L (bk15ErrorWordState word) ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hL
  apply Module.Basis.ext bk15AErrorBasis.toBasis
  intro word
  simpa using hall word

set_option maxRecDepth 65536 in
private theorem endpointWeight_pos_of_history_nonzero
    (epsilon : BK15Epsilon) (hpositive : 0 < epsilon.epsilon)
    (outcome : DistillationOutcome) (history : History)
    (hvisible : historyOutcome history = outcome)
    (hnonzero : historyKraus history ≠ 0) :
    0 < endpointWeight epsilon outcome := by
  rw [endpointWeight_eq_history_word_sum]
  apply Finset.sum_pos'
  · intro candidate _
    by_cases hcandidate : historyOutcome candidate = outcome
    · rw [if_pos hcandidate]
      exact Finset.sum_nonneg fun word _ =>
        mul_nonneg (bk15WordWeight_nonneg epsilon word) (sq_nonneg _)
    · simp [hcandidate]
  · refine ⟨history, Finset.mem_univ history, ?_⟩
    rw [if_pos hvisible]
    obtain ⟨word, hword⟩ :=
      exists_basis_word_not_annihilated (historyKraus history) hnonzero
    apply Finset.sum_pos'
    · intro candidate _
      exact mul_nonneg (bk15WordWeight_nonneg epsilon candidate) (sq_nonneg _)
    · refine ⟨word, Finset.mem_univ word, ?_⟩
      exact mul_pos (bk15WordWeight_pos epsilon hpositive word)
        (sq_pos_of_pos (norm_pos_iff.mpr hword))

/-- The accepted physical aggregate has strictly positive mass throughout the
strict source interval. -/
theorem accepted_endpointWeight_pos (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) :
    0 < endpointWeight epsilon .accepted :=
  endpointWeight_pos_of_history_nonzero epsilon hpositive .accepted
    acceptedWitnessHistory acceptedWitnessHistory_outcome
    acceptedWitnessHistory_nonzero

/-- The actual rejected aggregate also has strictly positive mass; the
witness is a genuine single-site Z error with nonzero `l1Syndrome`. -/
theorem rejected_endpointWeight_pos (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) :
    0 < endpointWeight epsilon .rejected :=
  endpointWeight_pos_of_history_nonzero epsilon hpositive .rejected
    (rejectedWitnessHistory 0) (rejectedWitnessHistory_outcome 0)
    (rejectedWitnessHistory_nonzero 0)

/-- Evaluation at the unique logical site, followed by the source-required
logical `X`, identifies the decoded computational label with the ordinary
one-qubit label.  The flip is the genuine BK15 logical correction: the zero-`Z`
projection carries logical phase `-π/4`, while the reported `A₀` direction has
phase `π/4`. -/
def logicalBitEquiv : Bitstring Unit ≃ Fin 2 where
  toFun bits := flipBit (bits ())
  invFun bit := fun _ => flipBit bit
  left_inv := by
    intro bits
    funext site
    cases site
    simp
  right_inv := by
    intro bit
    simp

/-- Basis-preserving identification of the decoded one-site register with the
ordinary one-qubit Hilbert space. -/
noncomputable def logicalRegisterToQubit :
    UnitaryTransport LogicalRegister QubitSpace := by
  let sourceBasis := EuclideanSpace.basisFun (Bitstring Unit) Complex
  let targetBasis := EuclideanSpace.basisFun (Fin 2) Complex
  let U := sourceBasis.equiv targetBasis logicalBitEquiv
  exact { toLinearEquiv := U.toLinearEquiv, map_inner := U.inner_map_map }

@[simp] theorem logicalRegisterToQubit_basis (bit : Fin 2) :
    logicalRegisterToQubit
        (EuclideanSpace.basisFun (Bitstring Unit) Complex (fun _ => bit)) =
      EuclideanSpace.basisFun (Fin 2) Complex (flipBit bit) := by
  change ((EuclideanSpace.basisFun (Bitstring Unit) Complex).equiv
    (EuclideanSpace.basisFun (Fin 2) Complex) logicalBitEquiv)
      (EuclideanSpace.basisFun (Bitstring Unit) Complex (fun _ => bit)) = _
  rw [OrthonormalBasis.equiv_apply_basis]
  rfl

/-- The total CSS decoder followed by the concrete one-qubit basis
identification. -/
noncomputable def decoderToQubitChannel : QuantumChannel BK15Register QubitSpace :=
  QuantumChannel.comp (QuantumChannel.unitaryConj logicalRegisterToQubit)
    decoderChannel

/-- The complete BK15 physical history, decoding, discard fallback, and final
one-qubit basis identification as one CPTP operation. -/
noncomputable def decodedOperation : QuantumChannel BK15Register QubitSpace :=
  QuantumChannel.comp decoderToQubitChannel historyChannel

/-! ## Raw and positive-mass endpoint states -/

/-- A normalized physical endpoint exists only after its actual positive Born
mass has been supplied.  This is intentionally unavailable at a zero-mass
endpoint. -/
noncomputable def endpointConditional (epsilon : BK15Epsilon)
    (outcome : DistillationOutcome) (hpositive : 0 < endpointWeight epsilon outcome) :
    DensityOperator BK15Register :=
  historyInstrument.conditionalDensity outcome (rawInput epsilon) hpositive

set_option maxRecDepth 262144 in
set_option maxHeartbeats 800000 in
@[simp] theorem endpointConditional_toOperator (epsilon : BK15Epsilon)
    (outcome : DistillationOutcome) (hpositive : 0 < endpointWeight epsilon outcome) :
    (endpointConditional epsilon outcome hpositive).toOperator =
      ((endpointWeight epsilon outcome : Complex)⁻¹) • rawEndpoint epsilon outcome := by
  rfl

set_option maxRecDepth 262144 in
set_option maxHeartbeats 800000 in
/-- Weighting a positive conditional endpoint reconstructs its literal raw
branch. -/
theorem endpointWeight_smul_endpointConditional (epsilon : BK15Epsilon)
    (outcome : DistillationOutcome) (hpositive : 0 < endpointWeight epsilon outcome) :
    (endpointWeight epsilon outcome : Complex) •
      (endpointConditional epsilon outcome hpositive).toOperator =
        rawEndpoint epsilon outcome := by
  rw [endpointConditional_toOperator]
  simp [smul_smul, hpositive.ne']

/-- Weighting both honest positive conditionals reconstructs the literal
complete physical history output. -/
theorem weighted_endpointConditionals_reconstruct
    (epsilon : BK15Epsilon)
    (haccepted : 0 < endpointWeight epsilon .accepted)
    (hrejected : 0 < endpointWeight epsilon .rejected) :
    (endpointWeight epsilon .accepted : Complex) •
        (endpointConditional epsilon .accepted haccepted).toOperator +
      (endpointWeight epsilon .rejected : Complex) •
        (endpointConditional epsilon .rejected hrejected).toOperator =
      (historyChannel.mapDensity (rawInput epsilon)).toOperator := by
  rw [endpointWeight_smul_endpointConditional,
    endpointWeight_smul_endpointConditional]
  exact rawEndpoints_reconstruct epsilon

/-- The total decoder/discard acts on a normalized positive endpoint, including
the rejected endpoint when it has positive mass.  This post-source decoding is
a Lean-QEC extension; the source itself stops at failure. -/
noncomputable def decodedEndpointConditional (epsilon : BK15Epsilon)
    (outcome : DistillationOutcome) (hpositive : 0 < endpointWeight epsilon outcome) :
    DensityOperator LogicalRegister :=
  decoderChannel.mapDensity (endpointConditional epsilon outcome hpositive)

/-- A normalized positive endpoint after total decoding and the concrete
one-qubit basis identification. -/
noncomputable def qubitEndpointConditional (epsilon : BK15Epsilon)
    (outcome : DistillationOutcome) (hpositive : 0 < endpointWeight epsilon outcome) :
    DensityOperator QubitSpace :=
  logicalRegisterToQubit.conjDensity
    (decodedEndpointConditional epsilon outcome hpositive)

private theorem physicalRun_output_decomposition
    (epsilon : BK15Epsilon) (hpositive : 0 < epsilon.epsilon) :
    historyChannel.mapDensity
        (bk15PrepareInput (bk15NoisyResources epsilon)) =
      outcomeMixture (endpointWeight epsilon .accepted)
        (endpointWeight_nonneg epsilon .accepted)
        (by
          linarith [endpointWeight_nonneg epsilon .rejected,
            endpointWeights_sum epsilon])
        (endpointConditional epsilon .accepted
          (accepted_endpointWeight_pos epsilon hpositive))
        (endpointConditional epsilon .rejected
          (rejected_endpointWeight_pos epsilon hpositive)) := by
  have hmixture (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1)
      (rho sigma : DensityOperator BK15Register) :
      (outcomeMixture p h0 h1 rho sigma).toOperator =
        (p : Complex) • rho.toOperator + ((1 - p : ℝ) : Complex) • sigma.toOperator := by
    simp [outcomeMixture, DensityOperator.convexCombinationOperator,
      branchState, outcomeWeight,
      show (Finset.univ : Finset DistillationOutcome) =
        {.accepted, .rejected} by decide]
    rw [RCLike.real_smul_eq_coe_smul (K := Complex)]
    change ((1 - p : ℝ) : Complex) • sigma.toOperator =
      (1 - (p : Complex)) • sigma.toOperator
    exact congrArg (fun c : Complex => c • sigma.toOperator)
      (by simp only [Complex.ofReal_sub, Complex.ofReal_one])
  apply DensityOperator.ext_toOperator
  rw [bk15PrepareInput_noisyResources_eq_bk15ErrorWordMixture]
  change (historyChannel.mapDensity (rawInput epsilon)).toOperator = _
  rw [← weighted_endpointConditionals_reconstruct epsilon
    (accepted_endpointWeight_pos epsilon hpositive)
    (rejected_endpointWeight_pos epsilon hpositive)]
  have hreject :
      1 - endpointWeight epsilon .accepted =
        endpointWeight epsilon .rejected := by
    linarith [endpointWeights_sum epsilon]
  rw [hmixture, hreject]

/-- The physical BK15 run before its proved total decoder and one-qubit basis
identification are postcomposed. -/
private noncomputable def physicalRun (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) :
    DistillationRun QubitSpace BK15Register BK15Register where
  resourceCount := 15
  noisyInput := bk15NoisyResources epsilon
  prepareInput := bk15PrepareInput
  operation := historyChannel
  successProbability := endpointWeight epsilon .accepted
  success_nonneg := endpointWeight_nonneg epsilon .accepted
  success_le_one := by
    linarith [endpointWeight_nonneg epsilon .rejected,
      endpointWeights_sum epsilon]
  acceptedOutput := endpointConditional epsilon .accepted
    (accepted_endpointWeight_pos epsilon hpositive)
  rejectedOutput := endpointConditional epsilon .rejected
    (rejected_endpointWeight_pos epsilon hpositive)
  output_decomposition := physicalRun_output_decomposition epsilon hpositive

/-- The actual fifteen-resource BK15 experiment, with both normalized physical
aggregates decoded by the same total CPTP operation. -/
noncomputable def bk15Run (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) :
    DistillationRun QubitSpace BK15Register QubitSpace :=
  (physicalRun epsilon hpositive).postprocess decoderToQubitChannel

@[simp] theorem bk15Run_resourceCount (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) :
    (bk15Run epsilon hpositive).resourceCount = 15 :=
  rfl

@[simp] theorem bk15Run_operation (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) :
    (bk15Run epsilon hpositive).operation = decodedOperation :=
  rfl

@[simp] theorem bk15Run_successProbability (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) :
    (bk15Run epsilon hpositive).successProbability =
      endpointWeight epsilon .accepted :=
  rfl

/-- The packaged success probability is genuinely positive in the strict
source interval. -/
theorem bk15Run_successProbability_pos (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) :
    0 < (bk15Run epsilon hpositive).successProbability :=
  accepted_endpointWeight_pos epsilon hpositive

@[simp] theorem bk15Run_acceptedOutput (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) :
    (bk15Run epsilon hpositive).acceptedOutput =
      qubitEndpointConditional epsilon .accepted
        (accepted_endpointWeight_pos epsilon hpositive) := by
  rfl

@[simp] theorem bk15Run_rejectedOutput (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) :
    (bk15Run epsilon hpositive).rejectedOutput =
      qubitEndpointConditional epsilon .rejected
        (rejected_endpointWeight_pos epsilon hpositive) := by
  rfl

/-- The independent error model permits exactly the concrete diagonal A-basis
resources consumed by this run at their common physical error rate. -/
def bk15InputErrorModel (epsilon : BK15Epsilon) :
    InputErrorModel 15 QubitSpace :=
  .independent
    { rate := fun _ => epsilon.epsilon
      rate_nonneg := fun _ => epsilon.nonneg
      rate_le_one := fun _ => epsilon.le_one
      admissible := fun rates inputs =>
        ∀ site, rates site = epsilon.epsilon ∧
          inputs site = bk15NoisyResources epsilon site }

theorem bk15InputErrorModel_permits (epsilon : BK15Epsilon) :
    (bk15InputErrorModel epsilon).Permits
      (bk15NoisyResources epsilon) := by
  change ∀ site, (fun _ => epsilon.epsilon) site = epsilon.epsilon ∧
    bk15NoisyResources epsilon site = bk15NoisyResources epsilon site
  intro site
  exact ⟨rfl, rfl⟩

/-- State-dependent negative-A weight of the reported output. -/
def bk15OutputError
    (rho _ideal : DensityOperator QubitSpace) : Real :=
  aInputError rho

theorem aInputError_nonneg (rho : DensityOperator QubitSpace) :
    0 ≤ aInputError rho := by
  unfold aInputError
  exact sub_nonneg.mpr
    (OneQubitMagic.projectionSquaredOverlap_le_one
      (aBasisProjector .positive) rho
      (aBasisProjector_isSymmetricProjection .positive))

theorem bk15OutputError_nonneg
    (rho ideal : DensityOperator QubitSpace) :
    0 ≤ bk15OutputError rho ideal :=
  aInputError_nonneg rho

/-- The source-order physical construction packaged through the shared
postselected magic-state protocol interface. -/
noncomputable def bk15MagicStateProtocol (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) :
    MagicStateDistillationProtocol QubitSpace BK15Register QubitSpace where
  run := bk15Run epsilon hpositive
  inputErrorModel := bk15InputErrorModel epsilon
  inputPermitted := bk15InputErrorModel_permits epsilon
  behavior := .postselected
  idealOutput := aZeroDensity
  outputError := bk15OutputError
  outputError_nonneg := bk15OutputError_nonneg

/-! ## Closed zero-error input witness -/

/-- The raw physical zero-error endpoint belongs to the closed input domain. -/
def zeroEpsilon : BK15Epsilon where
  epsilon := 0
  nonneg := le_rfl
  le_half := by norm_num

/-- The all-zero physical error word. -/
def zeroErrorWord : Word := 0

theorem zeroEpsilon_cleanWeight : zeroEpsilon.cleanWeight = 1 := by
  norm_num [zeroEpsilon, BK15Epsilon.cleanWeight]

theorem zeroEpsilon_zeroErrorWord_weight :
    bk15WordWeight zeroEpsilon zeroErrorWord = 1 := by
  unfold bk15WordWeight zeroErrorWord
  simp [aInputWeight, zeroEpsilon, BK15Epsilon.cleanWeight]

private theorem zeroZProjectedIdeal_zeroErrorWord :
    zProjector (signSyndrome (0 : ZCheckIndex → Bit))
        (bk15ErrorWordState zeroErrorWord) =
      (32 : Complex)⁻¹ •
        ambientEncodingIsometry logicalNegativeAState := by
  simpa [zeroErrorWord] using zeroZProjectedIdeal

private theorem historyCorrection_symm_ideal
    (outcome : ZJointSyndrome) :
    (historyCorrection outcome).symm
        (bk15ErrorWordState zeroErrorWord) =
      bk15ErrorWordState zeroErrorWord := by
  change (aWordCorrectionTransport
    (l2SyndromeSection (zBinarySyndrome outcome))).symm
      (bk15ErrorWordState zeroErrorWord) = _
  rw [aWordCorrectionTransport_symm_eigen]
  simp [zeroErrorWord, binaryPhaseScalar]

private theorem historyCorrection_symm_ideal_linear
    (outcome : ZJointSyndrome) :
    (historyCorrection outcome).symm.toLinearEquiv.toLinearMap
        (bk15ErrorWordState zeroErrorWord) =
      bk15ErrorWordState zeroErrorWord := by
  exact historyCorrection_symm_ideal outcome

set_option maxRecDepth 65536 in
private theorem correctedZHistory_ideal
    (outcome : ZJointSyndrome) :
    ((historyCorrection outcome).symm.toLinearEquiv.toLinearMap *
        zProjector outcome) (bk15ErrorWordState zeroErrorWord) =
      zProjector (signSyndrome (0 : ZCheckIndex → Bit))
        (bk15ErrorWordState zeroErrorWord) := by
  rw [historyCorrection_symm_zProjector]
  simp only [Module.End.mul_apply]
  rw [historyCorrection_symm_ideal_linear]

private theorem encoded_xCheck_fixed
    (psi : LogicalRegister) (check : XCheckIndex) :
    toHermitianQubitOperator (xChecks check)
        (ambientEncodingIsometry psi) =
      ambientEncodingIsometry psi := by
  have hmem : ambientEncodingIsometry psi ∈ bk15EncodedCode.code.carrier := by
    change (bk15EncodedCode.encoding psi : BK15Register) ∈
      bk15EncodedCode.code.carrier
    exact (bk15EncodedCode.encoding psi).property
  have hP : xChecks check ∈ binaryCSSCheckSet bk15CSSRows.evenCode
      bk15CSSRows.rowCode.dual := by
    exact Or.inl ⟨linearGenerator check,
      bk15CSSRows.evenRow_mem_evenCode check, rfl⟩
  have hfix := (mem_binaryCSSQuantumCodeOfDualLe_carrier
    bk15CSSRows.evenCode bk15CSSRows.rowCode.dual
    bk15CSSRows.cssDualContainment (ambientEncodingIsometry psi)).1 hmem
      (xChecks check) hP
  simpa [xChecks, toHermitianQubitOperator, hermitianPhaseScalar,
    binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport,
    binarySupport] using hfix

private theorem encoded_xProjector_zero (psi : LogicalRegister) :
    xProjector (signSyndrome (0 : XCheckIndex → Bit))
        (ambientEncodingIsometry psi) =
      ambientEncodingIsometry psi := by
  apply (jointStabilizerProjector_fixed_iff xChecks xChecks_commute
    (signSyndrome (0 : XCheckIndex → Bit))
    (ambientEncodingIsometry psi)).2
  intro check
  simpa [signSyndrome, bitToSign, StabilizerOutcome.sign] using
    encoded_xCheck_fixed psi check

private theorem xProjector_zeroProjectedIdeal
    (outcome : XJointSyndrome) :
    xProjector outcome
        (zProjector (signSyndrome (0 : ZCheckIndex → Bit))
          (bk15ErrorWordState zeroErrorWord)) =
      if outcome = signSyndrome (0 : XCheckIndex → Bit) then
        zProjector (signSyndrome (0 : ZCheckIndex → Bit))
          (bk15ErrorWordState zeroErrorWord)
      else 0 := by
  classical
  rw [zeroZProjectedIdeal_zeroErrorWord]
  by_cases houtcome : outcome = signSyndrome (0 : XCheckIndex → Bit)
  · rw [if_pos houtcome, houtcome]
    simp only [map_smul]
    rw [encoded_xProjector_zero]
  · rw [if_neg houtcome]
    have hmul := jointStabilizerProjector_mul_of_ne xChecks xChecks_commute
      outcome (signSyndrome (0 : XCheckIndex → Bit)) houtcome
    have happly := LinearMap.congr_fun hmul
      (ambientEncodingIsometry logicalNegativeAState)
    simp only [Module.End.mul_apply, LinearMap.zero_apply] at happly
    change xProjector outcome
        (xProjector (signSyndrome (0 : XCheckIndex → Bit))
          (ambientEncodingIsometry logicalNegativeAState)) = 0 at happly
    rw [encoded_xProjector_zero] at happly
    simp only [map_smul]
    rw [happly, smul_zero]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000 in
private theorem historyKraus_ideal (history : History) :
    historyKraus history (bk15ErrorWordState zeroErrorWord) =
      if history.2 = signSyndrome (0 : XCheckIndex → Bit) then
        zProjector (signSyndrome (0 : ZCheckIndex → Bit))
          (bk15ErrorWordState zeroErrorWord)
      else 0 := by
  rcases history with ⟨zOutcome, xOutcome⟩
  simp only [historyKraus, Module.End.mul_apply]
  change xProjector xOutcome
      (((historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap *
        zProjector zOutcome) (bk15ErrorWordState zeroErrorWord)) = _
  rw [correctedZHistory_ideal, xProjector_zeroProjectedIdeal]

private theorem zeroEpsilon_word_weight (word : Word) :
    bk15WordWeight zeroEpsilon word =
      if word = zeroErrorWord then 1 else 0 := by
  classical
  by_cases hword : word = zeroErrorWord
  · rw [if_pos hword, hword, zeroEpsilon_zeroErrorWord_weight]
  · rw [if_neg hword]
    have hexists : ∃ site : Fin 15, word site ≠ 0 := by
      by_contra hnone
      simp only [not_exists, not_not] at hnone
      apply hword
      apply funext
      intro site
      simpa [zeroErrorWord] using hnone site
    obtain ⟨site, hsite⟩ := hexists
    unfold bk15WordWeight
    apply Finset.prod_eq_zero (Finset.mem_univ site)
    generalize hbit : word site = bit
    fin_cases bit
    · exact (hsite hbit).elim
    · simp [aInputWeight, zeroEpsilon]

private theorem rawInput_zeroEpsilon :
    (rawInput zeroEpsilon).toOperator =
      (InnerProductSpace.rankOne Complex
        (bk15ErrorWordState zeroErrorWord)
        (bk15ErrorWordState zeroErrorWord)).toLinearMap := by
  rw [rawInput_toOperator_sum]
  rw [Fintype.sum_eq_single zeroErrorWord]
  · rw [zeroEpsilon_zeroErrorWord_weight]
    simp
  · intro word hword
    have hweight : bk15WordWeight zeroEpsilon word = 0 := by
      rw [zeroEpsilon_word_weight]
      simp [hword]
    rw [hweight]
    simp

private theorem rawRejected_zeroEpsilon :
    rawEndpoint zeroEpsilon .rejected = 0 := by
  classical
  rw [rawEndpoint_eq_branchOperator,
    FiniteInstrument.branchOperator_apply, rawInput_zeroEpsilon]
  apply Finset.sum_eq_zero
  intro history _
  by_cases hvisible : historyOutcome history = .rejected
  · have hvisibleObserve : historyInstrument.observe history = .rejected :=
      hvisible
    rw [if_pos hvisibleObserve]
    simp only [historyInstrument, historyKrausFamily]
    have hx : history.2 ≠ signSyndrome (0 : XCheckIndex → Bit) := by
      intro hx
      have hzero : xBinarySyndrome history.2 = 0 := by
        rw [hx]
        simp
      simp [historyOutcome, hzero] at hvisible
    rw [sandwich_rankOne, historyKraus_ideal, if_neg hx]
    simp
  · change historyInstrument.observe history ≠ .rejected at hvisible
    rw [if_neg hvisible]

private theorem endpointWeight_rejected_zeroEpsilon :
    endpointWeight zeroEpsilon .rejected = 0 := by
  unfold endpointWeight FiniteInstrument.bornWeight
  rw [show historyInstrument.branchOperator .rejected
      (rawInput zeroEpsilon).toOperator = 0 by
    exact rawRejected_zeroEpsilon]
  simp

private theorem endpointWeight_accepted_zeroEpsilon :
    endpointWeight zeroEpsilon .accepted = 1 := by
  linarith [endpointWeights_sum zeroEpsilon,
    endpointWeight_rejected_zeroEpsilon]

private theorem historyChannel_zeroEpsilon :
    (historyChannel.mapDensity (rawInput zeroEpsilon)).toOperator =
      (InnerProductSpace.rankOne Complex
        (ambientEncodingIsometry logicalNegativeAState)
        (ambientEncodingIsometry logicalNegativeAState)).toLinearMap := by
  rw [QuantumChannel.mapDensity_toOperator, historyChannel,
    FiniteKrausFamily.toQuantumChannel_apply_sum,
    rawInput_zeroEpsilon, Fintype.sum_prod_type]
  simp_rw [sandwich_rankOne]
  simp only [historyInstrument, historyKrausFamily]
  simp_rw [historyKraus_ideal]
  have hstabilizer : Fintype.card StabilizerOutcome = 2 := by native_decide
  have hquadratic : Fintype.card QuadraticIndex = 6 := by native_decide
  simp only [zeroZProjectedIdeal_zeroErrorWord]
  erw [Finset.sum_const]
  rw [Finset.card_univ]
  have hcardZ : Fintype.card ZJointSyndrome = 1024 := by
    simp [ZJointSyndrome, JointSyndrome, ZCheckIndex, hstabilizer, hquadratic]
  rw [hcardZ]
  erw [Fintype.sum_eq_single
    (signSyndrome (0 : XCheckIndex → Bit))]
  · ext psi bits
    simp [InnerProductSpace.rankOne_apply, PiLp.smul_apply,
      inner_smul_left, smul_eq_mul]
    have hstar : (starRingEnd Complex) (32 : Complex) = 32 := by
      simpa only [starRingEnd_apply] using (star_ofNat (R := Complex) 32)
    rw [hstar]
    norm_num
    ring
  · intro outcome houtcome
    simp [houtcome]

@[simp] private theorem logicalRegisterToQubit_apply
    (psi : LogicalRegister) (bit : Fin 2) :
    logicalRegisterToQubit psi bit = psi (fun _ => flipBit bit) := by
  rfl

private theorem logicalRegisterToQubit_negativeA :
    logicalRegisterToQubit logicalNegativeAState =
      OneQubitMagic.phaseAmplitude (-Real.pi / 4) • aZeroState := by
  ext bit
  rw [logicalRegisterToQubit_apply]
  fin_cases bit
  · simp [logicalNegativeAState, aZeroState,
      OneQubitMagic.phaseState_apply_zero]
    ring
  · simp [logicalNegativeAState, aZeroState,
      OneQubitMagic.phaseState_apply_one]
    have hphase :
        OneQubitMagic.phaseAmplitude (-Real.pi / 4) *
            OneQubitMagic.phaseAmplitude (Real.pi / 4) = 1 := by
      rw [← OneQubitMagic.phaseAmplitude_add]
      convert OneQubitMagic.phaseAmplitude_zero using 1 <;> ring
    calc
      _ = (OneQubitMagic.phaseAmplitude (-Real.pi / 4) *
          OneQubitMagic.phaseAmplitude (Real.pi / 4)) *
          (Real.sqrt 2 : Complex)⁻¹ := by rw [hphase]; ring
      _ = _ := by ring

private theorem rankOne_global_phase
    (z : Complex) (psi : QubitSpace) (hz : z * star z = 1) :
    (InnerProductSpace.rankOne Complex (z • psi) (z • psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  ext x bit
  change ((InnerProductSpace.rankOne Complex (z • psi) (z • psi)) x).ofLp bit =
    ((InnerProductSpace.rankOne Complex psi psi) x).ofLp bit
  rw [InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply]
  simp only [PiLp.smul_apply, inner_smul_left, smul_eq_mul]
  calc
    (star z * inner Complex psi x) * (z * psi bit) =
        (z * star z) * inner Complex psi x * psi bit := by ring
    _ = inner Complex psi x * psi bit := by rw [hz]; ring

private theorem decodedWithFlip_zeroEpsilon :
    logicalRegisterToQubit.conjDensity
        (decoderChannel.mapDensity
          (historyChannel.mapDensity (rawInput zeroEpsilon))) =
      aZeroDensity := by
  apply DensityOperator.ext_toOperator
  rw [UnitaryTransport.conjDensity_toOperator,
    QuantumChannel.mapDensity_toOperator,
    historyChannel_zeroEpsilon,
    decoderChannel_rankOne_encoded,
    QuditSubsystem.conjOperator_rankOne,
    logicalRegisterToQubit_negativeA,
    aZeroDensity_eq_phaseStateDensity,
    OneQubitMagic.phaseStateDensity_toOperator]
  exact rankOne_global_phase
    (OneQubitMagic.phaseAmplitude (-Real.pi / 4)) aZeroState
    (OneQubitMagic.phaseAmplitude_mul_conj (-Real.pi / 4))

/-- The complete concrete BK15 operation sends the closed zero-noise physical
input to the reported ideal `A₀` density after syndrome processing, correction,
total CSS decoding, and the logical one-qubit basis identification. -/
theorem decodedOperation_zeroEpsilon :
    decodedOperation.mapDensity (rawInput zeroEpsilon) = aZeroDensity := by
  rw [decodedOperation, Semantics.QuantumChannel.comp_mapDensity,
    decoderToQubitChannel, Semantics.QuantumChannel.comp_mapDensity]
  apply DensityOperator.ext_toOperator
  rw [QuantumChannel.mapDensity_toOperator, QuantumChannel.unitaryConj_apply]
  rw [← UnitaryTransport.conjDensity_toOperator]
  exact congrArg
    (fun rho : DensityOperator QubitSpace => rho.toOperator)
    decodedWithFlip_zeroEpsilon

end Protocol
end BK15
end Distillation
end QEC
