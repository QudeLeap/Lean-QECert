import QEC.Distillation.FifteenQubitH.Protocol

/-!
# BK15 recurrence prerequisites

This module derives the Bravyi--Kitaev fifteen-to-one recurrence from the
concrete finite-history protocol.  The first layer records the physical input
change of variables and the strict normalization facts used by the later
history and enumerator calculations.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace BK15
namespace Recurrence

open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput Protocol
open scoped BigOperators TensorProduct

/-- The source's signed A-basis bias for an admissible BK15 input error. -/
def bk15_r (epsilon : BK15Epsilon) : Real := 1 - 2 * epsilon.epsilon

/-- The physical source interval puts the signed bias in the nonnegative half
of the unit interval. -/
theorem bk15_r_nonneg (epsilon : BK15Epsilon) : 0 ≤ bk15_r epsilon := by
  unfold bk15_r
  linarith [epsilon.le_half]

/-- The same physical interval bounds the signed bias above by one. -/
theorem bk15_r_le_one (epsilon : BK15Epsilon) : bk15_r epsilon ≤ 1 := by
  unfold bk15_r
  linarith [epsilon.nonneg]

/-- Positivity of the unscaled BK15 normalization polynomial. -/
theorem bk15_recurrence_denominator_pos (epsilon : BK15Epsilon) :
    0 < 1 + 15 * bk15_r epsilon ^ 8 := by
  have hpow : 0 ≤ bk15_r epsilon ^ 8 :=
    pow_nonneg (bk15_r_nonneg epsilon) _
  nlinarith

/-- Positivity of the exact denominator used by the accepted output error. -/
theorem bk15_recurrence_scaled_denominator_pos (epsilon : BK15Epsilon) :
    0 < 2 * (1 + 15 * bk15_r epsilon ^ 8) := by
  nlinarith [bk15_recurrence_denominator_pos epsilon]

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
  ext candidate
  simp [zChecks, toHermitianQubitOperator, hermitianPhaseScalar,
    cssZCheck, toQubitOperator, xSupport, zSupport, binaryOverlapCount,
    binaryOverlapSupport, binarySupport, signSyndrome, bitToSign,
    StabilizerOutcome.sign, l2Syndrome, Coding.wordPairing_apply,
    EuclideanSpace.basisFun_apply, PiLp.single_apply]
  by_cases hcandidate : candidate = bits
  · subst candidate
    simp only [if_pos]
    have hsupport : ({x | ¬l2Generator check x = 0} : Finset (Fin 15)) =
        binarySupport (l2Generator check) := by
      ext site
      simp [binarySupport]
    erw [hsupport]
    rw [zSupportPhase_eq_binaryPhaseScalar_wordPairing,
      Coding.wordPairing_apply, dotProduct_comm]
    by_cases hzero :
        (bitstringWordEquiv (Fin 15)) bits ⬝ᵥ l2Generator check = 0 <;>
      simp [hzero, binaryPhaseScalar]
  · simp [hcandidate]

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

private theorem cssZCheck_xCheck_relation (error : Word)
    (check : XCheckIndex) :
    toHermitianQubitOperator (cssZCheck error) *
        toHermitianQubitOperator (xChecks check) =
      (signSyndrome (l1Syndrome error) check).sign •
        (toHermitianQubitOperator (xChecks check) *
          toHermitianQubitOperator (cssZCheck error)) := by
  have hHermitianZ :
      toHermitianQubitOperator (cssZCheck error) =
        toQubitOperator (cssZCheck error) := by
    simp [toHermitianQubitOperator, hermitianPhaseScalar,
      binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport,
      binarySupport]
  have hHermitianX :
      toHermitianQubitOperator (xChecks check) =
        toQubitOperator (xChecks check) := by
    simp [xChecks, toHermitianQubitOperator, hermitianPhaseScalar,
      binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport,
      binarySupport]
  rw [hHermitianZ, hHermitianX]
  by_cases hpair : Coding.wordPairing error (linearGenerator check) = 0
  · have hdot : error ⬝ᵥ linearGenerator check = 0 := by
      simpa [Coding.wordPairing_apply] using hpair
    have hpair' : Coding.wordPairing (linearGenerator check) error = 0 := by
      simpa [Coding.wordPairing_apply, dotProduct_comm] using hpair
    have hcomm := cssXCheck_toQubitOperator_commute_cssZCheck_of_wordPairing_eq_zero
      hpair'
    have hsign :
        (signSyndrome (l1Syndrome error) check).sign = 1 := by
      simp [signSyndrome, bitToSign, l1Syndrome, hdot,
        StabilizerOutcome.sign]
    simpa [xChecks, cssZCheck, hsign] using hcomm.symm
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
    have hsign :
        (signSyndrome (l1Syndrome error) check).sign = -1 := by
      simp [signSyndrome, bitToSign, l1Syndrome, hdot,
        StabilizerOutcome.sign]
    rw [hsign]
    simp only [neg_one_smul]
    calc
      toQubitOperator (cssZCheck error) *
          toQubitOperator (xChecks check) =
        -(- (toQubitOperator (cssZCheck error) *
          toQubitOperator (xChecks check))) := by simp
      _ = -(toQubitOperator (xChecks check) *
          toQubitOperator (cssZCheck error)) := by
        simpa [xChecks] using (congrArg Neg.neg hanti).symm

set_option maxHeartbeats 0 in
private theorem cssZCheck_xFactor_intertwines (error : Word)
    (check : XCheckIndex) :
    toHermitianQubitOperator (cssZCheck error) *
        jointStabilizerFactor xChecks
          (signSyndrome (l1Syndrome error)) check =
      jointStabilizerFactor xChecks
          (signSyndrome (0 : XCheckIndex → Bit)) check *
        toHermitianQubitOperator (cssZCheck error) := by
  let T := toHermitianQubitOperator (cssZCheck error)
  let S := toHermitianQubitOperator (xChecks check)
  let scalar := (signSyndrome (l1Syndrome error) check).sign
  have hcheck : T * S = scalar • (S * T) := by
    exact cssZCheck_xCheck_relation error check
  have hscalar : scalar * scalar = 1 := by
    exact StabilizerOutcome.sign_mul_self
      (signSyndrome (l1Syndrome error) check)
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

private theorem cssZCheck_xProjector_intertwines (error : Word) :
    toHermitianQubitOperator (cssZCheck error) *
        xProjector (signSyndrome (l1Syndrome error)) =
      xProjector (signSyndrome (0 : XCheckIndex → Bit)) *
        toHermitianQubitOperator (cssZCheck error) := by
  exact jointStabilizerProjector_intertwines_operator
    xChecks xChecks_commute (toHermitianQubitOperator (cssZCheck error))
    (signSyndrome (l1Syndrome error))
    (signSyndrome (0 : XCheckIndex → Bit))
    (cssZCheck_xFactor_intertwines error)

private theorem cssZCheck_zCheck_commute (error : Word)
    (check : ZCheckIndex) :
    toHermitianQubitOperator (cssZCheck error) *
        toHermitianQubitOperator (zChecks check) =
      toHermitianQubitOperator (zChecks check) *
        toHermitianQubitOperator (cssZCheck error) := by
  have hcomm := toQubitOperator_commute_of_commutes
    (cssZCheck error) (cssZCheck (l2Generator check))
    (cssZCheck_commutes_cssZCheck _ _)
  simpa [zChecks, toHermitianQubitOperator, hermitianPhaseScalar,
    binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport,
    binarySupport] using hcomm

private theorem cssZCheck_zFactor_commute (error : Word)
    (outcome : ZJointSyndrome) (check : ZCheckIndex) :
    toHermitianQubitOperator (cssZCheck error) *
        jointStabilizerFactor zChecks outcome check =
      jointStabilizerFactor zChecks outcome check *
        toHermitianQubitOperator (cssZCheck error) := by
  let T := toHermitianQubitOperator (cssZCheck error)
  let S := toHermitianQubitOperator (zChecks check)
  let scalar := (outcome check).sign
  have hcheck : T * S = S * T := cssZCheck_zCheck_commute error check
  simp only [jointStabilizerFactor, stabilizerProjector]
  change T * ((1 / 2 : Complex) • (1 + scalar • S)) =
    ((1 / 2 : Complex) • (1 + scalar • S)) * T
  calc
    T * ((1 / 2 : Complex) • (1 + scalar • S)) =
        (1 / 2 : Complex) • (T + scalar • (T * S)) := by
          simp only [mul_smul_comm, mul_add, mul_one]
    _ = (1 / 2 : Complex) • (T + scalar • (S * T)) := by rw [hcheck]
    _ = ((1 / 2 : Complex) • (1 + scalar • S)) * T := by
      simp only [smul_mul_assoc, add_mul, one_mul]

private theorem cssZCheck_zProjector_commute (error : Word)
    (outcome : ZJointSyndrome) :
    toHermitianQubitOperator (cssZCheck error) * zProjector outcome =
      zProjector outcome * toHermitianQubitOperator (cssZCheck error) := by
  exact jointStabilizerProjector_intertwines_operator
    zChecks zChecks_commute (toHermitianQubitOperator (cssZCheck error))
    outcome outcome (cssZCheck_zFactor_commute error outcome)

private theorem historyCorrection_symm_cssZCheck (outcome : ZJointSyndrome)
    (error : Word) :
    (historyCorrection outcome).symm.toLinearEquiv.toLinearMap *
        toHermitianQubitOperator (cssZCheck error) =
      binaryPhaseScalar
          (l2SyndromeSection (zBinarySyndrome outcome) ⬝ᵥ error) •
        (toHermitianQubitOperator (cssZCheck error) *
          (historyCorrection outcome).symm.toLinearEquiv.toLinearMap) := by
  change (aWordCorrectionTransport
      (l2SyndromeSection (zBinarySyndrome outcome))).symm.toLinearEquiv.toLinearMap *
        toHermitianQubitOperator (cssZCheck error) =
      binaryPhaseScalar
          (l2SyndromeSection (zBinarySyndrome outcome) ⬝ᵥ error) •
        (toHermitianQubitOperator (cssZCheck error) *
          (aWordCorrectionTransport
            (l2SyndromeSection (zBinarySyndrome outcome))).symm.toLinearEquiv.toLinearMap)
  exact aWordCorrectionTransport_symm_cssZCheck
    (l2SyndromeSection (zBinarySyndrome outcome)) error

private theorem cssZCheck_zeroErrorWord (error : Word) :
    toHermitianQubitOperator (cssZCheck error)
        (bk15ErrorWordState zeroErrorWord) =
      bk15ErrorWordState error := by
  simpa [zeroErrorWord] using cssZCheck_errorWord error (0 : Word)

set_option maxRecDepth 65536 in
private theorem cssZCheck_zProjector_zeroErrorWord_apply
    (zOutcome : ZJointSyndrome) (error : Word) :
    zProjector zOutcome
        (toHermitianQubitOperator (cssZCheck error)
          (bk15ErrorWordState zeroErrorWord)) =
      toHermitianQubitOperator (cssZCheck error)
        (zProjector zOutcome (bk15ErrorWordState zeroErrorWord)) := by
  rw [← Module.End.mul_apply,
    (cssZCheck_zProjector_commute error zOutcome).symm,
    Module.End.mul_apply]

set_option maxRecDepth 65536 in
private theorem historyCorrection_cssZCheck_zeroErrorWord_apply
    (zOutcome : ZJointSyndrome) (error : Word) :
    (historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap
        (toHermitianQubitOperator (cssZCheck error)
          (zProjector zOutcome (bk15ErrorWordState zeroErrorWord))) =
      binaryPhaseScalar
          (l2SyndromeSection (zBinarySyndrome zOutcome) ⬝ᵥ error) •
        toHermitianQubitOperator (cssZCheck error)
          ((historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap
            (zProjector zOutcome (bk15ErrorWordState zeroErrorWord))) := by
  exact LinearMap.congr_fun
    (historyCorrection_symm_cssZCheck zOutcome error)
    (zProjector zOutcome (bk15ErrorWordState zeroErrorWord))

set_option maxRecDepth 65536 in
private theorem xProjector_zero_cssZCheck_zeroErrorWord_apply
    (zOutcome : ZJointSyndrome) (error : Word) :
    xProjector (signSyndrome (0 : XCheckIndex → Bit))
        (toHermitianQubitOperator (cssZCheck error)
          ((historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap
            (zProjector zOutcome (bk15ErrorWordState zeroErrorWord)))) =
      toHermitianQubitOperator (cssZCheck error)
        (xProjector (signSyndrome (l1Syndrome error))
          ((historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap
            (zProjector zOutcome (bk15ErrorWordState zeroErrorWord)))) := by
  exact LinearMap.congr_fun
    ((cssZCheck_xProjector_intertwines error).symm)
    ((historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap
      (zProjector zOutcome (bk15ErrorWordState zeroErrorWord)))

set_option maxRecDepth 65536 in
private theorem historyKraus_apply_explicit
    (zOutcome : ZJointSyndrome) (xOutcome : XJointSyndrome)
    (psi : BK15Register) :
    historyKraus (zOutcome, xOutcome) psi =
      xProjector xOutcome
        ((historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap
          (zProjector zOutcome psi)) := by
  simp only [historyKraus, Module.End.mul_apply]

set_option maxRecDepth 65536 in
private theorem accepted_historyKraus_error_unfolded
    (zOutcome : ZJointSyndrome) (error : Word) :
    xProjector (signSyndrome (0 : XCheckIndex → Bit))
        ((historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap
          (zProjector zOutcome (bk15ErrorWordState error))) =
      binaryPhaseScalar
          (l2SyndromeSection (zBinarySyndrome zOutcome) ⬝ᵥ error) •
        toHermitianQubitOperator (cssZCheck error)
          (xProjector (signSyndrome (l1Syndrome error))
            ((historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap
              (zProjector zOutcome (bk15ErrorWordState zeroErrorWord)))) := by
  rw [← cssZCheck_zeroErrorWord error,
    cssZCheck_zProjector_zeroErrorWord_apply,
    historyCorrection_cssZCheck_zeroErrorWord_apply,
    map_smul,
    xProjector_zero_cssZCheck_zeroErrorWord_apply]

set_option maxRecDepth 65536 in
private theorem accepted_historyKraus_error (zOutcome : ZJointSyndrome)
    (error : Word) :
    historyKraus
        (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
        (bk15ErrorWordState error) =
      binaryPhaseScalar
          (l2SyndromeSection (zBinarySyndrome zOutcome) ⬝ᵥ error) •
        toHermitianQubitOperator (cssZCheck error)
          (historyKraus
            (zOutcome, signSyndrome (l1Syndrome error))
            (bk15ErrorWordState zeroErrorWord)) := by
  rw [historyKraus_apply_explicit, historyKraus_apply_explicit]
  exact accepted_historyKraus_error_unfolded zOutcome error

private theorem binaryPhaseScalar_norm (phase : Bit) :
    ‖binaryPhaseScalar phase‖ = 1 := by
  by_cases hzero : phase = 0
  · rw [hzero, binaryPhaseScalar_zero]
    norm_num
  · rw [zmod_two_eq_one_of_ne_zero hzero, binaryPhaseScalar_one]
    norm_num

set_option maxRecDepth 65536 in
private theorem cssZCheck_norm_sq (error : Word) (psi : BK15Register) :
    ‖toHermitianQubitOperator (cssZCheck error) psi‖ ^ 2 = ‖psi‖ ^ 2 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex)
      (toHermitianQubitOperator (cssZCheck error) psi),
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex) psi]
  rw [(LinearMap.adjoint_inner_right
    (toHermitianQubitOperator (cssZCheck error)) psi
    (toHermitianQubitOperator (cssZCheck error) psi)).symm,
    adjoint_toHermitianQubitOperator_eq_self]
  have hsquare := LinearMap.congr_fun
    (toHermitianQubitOperator_square (cssZCheck error)) psi
  simp only [Module.End.mul_apply, Module.End.one_apply] at hsquare
  rw [hsquare, inner_self_eq_norm_sq_to_K]

private theorem accepted_historyKraus_norm_sq (zOutcome : ZJointSyndrome)
    (error : Word) :
    ‖historyKraus
        (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
        (bk15ErrorWordState error)‖ ^ 2 =
      if l1Syndrome error = 0 then
        ‖historyKraus
          (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
          (bk15ErrorWordState zeroErrorWord)‖ ^ 2
      else 0 := by
  classical
  by_cases hsyndrome : l1Syndrome error = 0
  · rw [if_pos hsyndrome]
    rw [accepted_historyKraus_error]
    simp only [hsyndrome, map_zero, signSyndrome]
    rw [norm_smul, binaryPhaseScalar_norm, one_mul, cssZCheck_norm_sq]
  · rw [if_neg hsyndrome]
    have hmatching : signSyndrome (l1Syndrome error) ≠
        signSyndrome (0 : XCheckIndex → Bit) := by
      intro hsign
      apply hsyndrome
      have := congrArg binarySyndrome hsign
      simpa using this
    rw [accepted_historyKraus_error,
      historyKraus_ideal (zOutcome, signSyndrome (l1Syndrome error))]
    simp [hmatching]

set_option maxRecDepth 262144 in
private theorem sum_historyKraus_norm_sq (psi : BK15Register) :
    ∑ history : History, ‖historyKraus history psi‖ ^ 2 = ‖psi‖ ^ 2 := by
  classical
  have hcomplete := historyKrausFamily_complete
  change (∑ history : History,
      (LinearMap.adjoint (historyKraus history)).comp
        (historyKraus history)) = 1 at hcomplete
  have hinner :
      ∑ history : History,
        inner Complex (historyKraus history psi) (historyKraus history psi) =
      inner Complex psi psi := by
    calc
      ∑ history : History,
          inner Complex (historyKraus history psi) (historyKraus history psi) =
        ∑ history : History,
          inner Complex psi
            ((LinearMap.adjoint (historyKraus history)).comp
              (historyKraus history) psi) := by
            apply Finset.sum_congr rfl
            intro history _
            rw [LinearMap.comp_apply]
            exact (LinearMap.adjoint_inner_right
              (historyKraus history) psi (historyKraus history psi)).symm
      _ = inner Complex psi
          ((∑ history : History,
            (LinearMap.adjoint (historyKraus history)).comp
              (historyKraus history)) psi) := by
            rw [LinearMap.sum_apply, inner_sum]
      _ = inner Complex psi psi := by
            rw [LinearMap.congr_fun hcomplete psi]
            simp
  calc
    ∑ history : History, ‖historyKraus history psi‖ ^ 2 =
        ∑ history : History,
          (inner Complex (historyKraus history psi)
            (historyKraus history psi)).re := by
              apply Finset.sum_congr rfl
              intro history _
              rw [inner_self_eq_norm_sq_to_K]
              simp [pow_two, Complex.mul_re]
    _ = (∑ history : History,
          inner Complex (historyKraus history psi)
            (historyKraus history psi)).re := by
              rw [Complex.re_sum]
    _ = (inner Complex psi psi).re := congrArg Complex.re hinner
    _ = ‖psi‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      simp [pow_two, Complex.mul_re]

private theorem zeroErrorWord_norm_sq :
    ‖bk15ErrorWordState zeroErrorWord‖ ^ 2 = 1 := by
  rw [← bk15AErrorBasis_apply zeroErrorWord]
  have hnorm : ‖bk15AErrorBasis zeroErrorWord‖ = 1 :=
    bk15AErrorBasis.norm_eq_one zeroErrorWord
  rw [hnorm]
  norm_num

private theorem sum_ideal_acceptedHistory_norm_sq :
    ∑ zOutcome : ZJointSyndrome,
      ‖historyKraus
        (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
        (bk15ErrorWordState zeroErrorWord)‖ ^ 2 = 1 := by
  classical
  calc
    ∑ zOutcome : ZJointSyndrome,
        ‖historyKraus
          (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
          (bk15ErrorWordState zeroErrorWord)‖ ^ 2 =
      ∑ zOutcome : ZJointSyndrome, ∑ xOutcome : XJointSyndrome,
        ‖historyKraus (zOutcome, xOutcome)
          (bk15ErrorWordState zeroErrorWord)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro zOutcome _
            rw [Fintype.sum_eq_single
              (signSyndrome (0 : XCheckIndex → Bit))]
            · intro xOutcome hxOutcome
              rw [historyKraus_ideal (zOutcome, xOutcome)]
              simp [hxOutcome]
    _ = ∑ history : History,
        ‖historyKraus history (bk15ErrorWordState zeroErrorWord)‖ ^ 2 := by
          rw [Fintype.sum_prod_type]
    _ = ‖bk15ErrorWordState zeroErrorWord‖ ^ 2 :=
      sum_historyKraus_norm_sq (bk15ErrorWordState zeroErrorWord)
    _ = 1 := zeroErrorWord_norm_sq

set_option maxRecDepth 65536 in
private theorem accepted_history_mass_eq_l1Dual_indicator (error : Word) :
    ∑ zOutcome : ZJointSyndrome,
      ‖historyKraus
        (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
        (bk15ErrorWordState error)‖ ^ 2 =
      if error ∈ l1DualWords then 1 else 0 := by
  classical
  have hmembership : error ∈ l1DualWords ↔ l1Syndrome error = 0 := by
    rw [mem_l1DualWords_iff, l1_dual_carrier_eq_l1Syndrome_ker]
    rfl
  by_cases hsyndrome : l1Syndrome error = 0
  · have hmember : error ∈ l1DualWords := hmembership.mpr hsyndrome
    rw [if_pos hmember]
    calc
      ∑ zOutcome : ZJointSyndrome,
          ‖historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState error)‖ ^ 2 =
        ∑ zOutcome : ZJointSyndrome,
          ‖historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState zeroErrorWord)‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro zOutcome _
              rw [accepted_historyKraus_norm_sq, if_pos hsyndrome]
      _ = 1 := sum_ideal_acceptedHistory_norm_sq
  · have hnotmember : error ∉ l1DualWords := by
      intro hmember
      exact hsyndrome (hmembership.mp hmember)
    rw [if_neg hnotmember]
    calc
      ∑ zOutcome : ZJointSyndrome,
          ‖historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState error)‖ ^ 2 =
        ∑ _zOutcome : ZJointSyndrome, 0 := by
              apply Finset.sum_congr rfl
              intro zOutcome _
              rw [accepted_historyKraus_norm_sq, if_neg hsyndrome]
      _ = 0 := by simp

private theorem historyOutcome_accepted_iff
    (zOutcome : ZJointSyndrome) (xOutcome : XJointSyndrome) :
    historyOutcome (zOutcome, xOutcome) = .accepted ↔
      xOutcome = signSyndrome (0 : XCheckIndex → Bit) := by
  constructor
  · intro haccepted
    change (if binarySyndrome xOutcome = 0 then DistillationOutcome.accepted
      else DistillationOutcome.rejected) = DistillationOutcome.accepted at haccepted
    by_cases hzero : binarySyndrome xOutcome = 0
    ·
      calc
        xOutcome = signSyndrome (binarySyndrome xOutcome) :=
          (signSyndrome_binarySyndrome xOutcome).symm
        _ = signSyndrome 0 := by rw [hzero]
    · simp [hzero] at haccepted
  · intro hzero
    subst xOutcome
    simp [historyOutcome, binarySyndrome_signSyndrome]

set_option maxRecDepth 262144 in
private theorem accepted_history_word_sum (weight : Word → Real) :
    ∑ history : History,
      (if historyOutcome history = .accepted then
        ∑ word : Word, weight word *
          ‖historyKraus history (bk15ErrorWordState word)‖ ^ 2
      else 0) =
      ∑ word : Word, weight word *
        ∑ zOutcome : ZJointSyndrome,
          ‖historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState word)‖ ^ 2 := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    ∑ zOutcome : ZJointSyndrome, ∑ xOutcome : XJointSyndrome,
        (if historyOutcome (zOutcome, xOutcome) = .accepted then
          ∑ word : Word, weight word *
            ‖historyKraus (zOutcome, xOutcome)
              (bk15ErrorWordState word)‖ ^ 2
        else 0) =
      ∑ zOutcome : ZJointSyndrome, ∑ word : Word, weight word *
        ‖historyKraus
          (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
          (bk15ErrorWordState word)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro zOutcome _
            rw [Fintype.sum_eq_single
              (signSyndrome (0 : XCheckIndex → Bit))]
            · simp [historyOutcome_accepted_iff]
            · intro xOutcome hxOutcome
              have hnotaccepted :
                  historyOutcome (zOutcome, xOutcome) ≠ .accepted := by
                intro haccepted
                exact hxOutcome (historyOutcome_accepted_iff zOutcome xOutcome |>.mp
                  haccepted)
              simp [hnotaccepted]
    _ = ∑ word : Word, weight word *
        ∑ zOutcome : ZJointSyndrome,
          ‖historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState word)‖ ^ 2 := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro word _
              rw [← Finset.mul_sum]

set_option linter.constructorNameAsVariable false in
/-- The concrete accepted endpoint is exactly the independent word-weight
sum over the enumerated dual of the four linear checks. -/
theorem accepted_endpointWeight_eq_l1Dual_wordSum (epsilon : BK15Epsilon) :
    endpointWeight epsilon .accepted =
      ∑ word ∈ l1DualWords, bk15WordWeight epsilon word := by
  classical
  rw [endpointWeight_eq_history_word_sum,
    accepted_history_word_sum (bk15WordWeight epsilon)]
  simp_rw [accepted_history_mass_eq_l1Dual_indicator]
  have hfilter :
      (Finset.univ.filter fun word : Word => word ∈ l1DualWords) =
        l1DualWords := by
    ext word
    simp
  calc
    ∑ word : Word, bk15WordWeight epsilon word *
        (if word ∈ l1DualWords then 1 else 0) =
      ∑ word : Word,
        if word ∈ l1DualWords then bk15WordWeight epsilon word else 0 := by
          apply Finset.sum_congr rfl
          intro word _
          by_cases hmember : word ∈ l1DualWords <;> simp [hmember]
    _ = ∑ word ∈ Finset.univ.filter
        (fun word : Word => word ∈ l1DualWords),
        bk15WordWeight epsilon word := by
          symm
          rw [Finset.sum_filter]
    _ = ∑ word ∈ l1DualWords, bk15WordWeight epsilon word := by
          rw [hfilter]

/-! ## Decoded negative-A raw numerator -/

/-- The single decoded logical A-state after the `L2 + c[1]` transport. -/
private noncomputable def logicalAErrorState (c : Bit) : LogicalRegister :=
  WithLp.toLp 2 fun bits =>
    binaryPhaseScalar (c * (bitstringWordEquiv Unit bits) ()) *
      logicalNegativeAState bits

private theorem l2_coset_pairing_l2dual_decomposition
    (b : Sum (Fin 4) QuadraticIndex → Bit) (c : Bit)
    (a : Fin 4 → Bit) (d : Bit) :
    Coding.wordPairing (l2CoefficientMap b + c • allOnes)
      (l1CoefficientMap a + d • allOnes) = c * d := by
  native_decide +revert

private theorem logicalAErrorState_label (c d : Bit) :
    logicalAErrorState c ((bitstringWordEquiv Unit).symm (fun _ => d)) =
      binaryPhaseScalar (c * d) *
        logicalNegativeAState ((bitstringWordEquiv Unit).symm (fun _ => d)) := by
  unfold logicalAErrorState
  change binaryPhaseScalar
      (c * (bitstringWordEquiv Unit
        ((bitstringWordEquiv Unit).symm (fun _ => d)) ())) *
        logicalNegativeAState ((bitstringWordEquiv Unit).symm (fun _ => d)) = _
  rw [Equiv.apply_symm_apply]

private theorem cssZCheck_l2_plus_allOnes_encoded
    (b : Sum (Fin 4) QuadraticIndex → Bit) (c : Bit) :
    toHermitianQubitOperator (cssZCheck (l2CoefficientMap b + c • allOnes))
        (ambientEncodingIsometry logicalNegativeAState) =
      ambientEncodingIsometry (logicalAErrorState c) := by
  change toHermitianQubitOperator
      (cssZCheck (l2CoefficientMap b + c • allOnes))
      (bk15CSSRows.encoding bk15CSSRows_triorthogonal logicalNegativeAState :
        BK15Register) =
    (bk15CSSRows.encoding bk15CSSRows_triorthogonal (logicalAErrorState c) :
      BK15Register)
  ext bits
  simp [toHermitianQubitOperator, hermitianPhaseScalar, toQubitOperator,
    xSupport, zSupport, binaryOverlapCount, binaryOverlapSupport]
  by_cases hbits : bitstringWordEquiv (Fin 15) bits ∈
      bk15CSSRows.rowCode.dual.dual.carrier
  · have hsyndrome : l2Syndrome (bitstringWordEquiv (Fin 15) bits) = 0 :=
      l2Syndrome_eq_zero_of_mem_rowCode_doubleDual hbits
    have hdual : bitstringWordEquiv (Fin 15) bits ∈ L2.dual.carrier := by
      rw [l2_dual_carrier_eq_l2Syndrome_ker]
      exact hsyndrome
    obtain ⟨a, d, had⟩ :=
      (mem_l2_dual_iff_exists_l1_plus_allOnes
        (bitstringWordEquiv (Fin 15) bits)).1 hdual
    have hlabel :
        (bk15CSSRows.logicalBasisEquivLogicalQuotient
            bk15CSSRows_triorthogonal).symm
            (Submodule.Quotient.mk
              (⟨bitstringWordEquiv (Fin 15) bits, hbits⟩ :
                bk15CSSRows.rowCode.dual.dual.carrier)) =
          (bitstringWordEquiv Unit).symm (fun _ => d) := by
      have hrowDecomp : l1CoefficientMap a + d • allOnes ∈
          bk15CSSRows.rowCode.dual.dual.carrier := by
        rw [← had]
        exact hbits
      have hsubtype :
          (⟨bitstringWordEquiv (Fin 15) bits, hbits⟩ :
              bk15CSSRows.rowCode.dual.dual.carrier) =
            ⟨l1CoefficientMap a + d • allOnes, hrowDecomp⟩ :=
        Subtype.ext had
      calc
        _ = (bk15CSSRows.logicalBasisEquivLogicalQuotient
              bk15CSSRows_triorthogonal).symm
              (Submodule.Quotient.mk
                (⟨l1CoefficientMap a + d • allOnes, hrowDecomp⟩ :
                  bk15CSSRows.rowCode.dual.dual.carrier)) :=
            congrArg
              (fun value : bk15CSSRows.rowCode.dual.dual.carrier =>
                (bk15CSSRows.logicalBasisEquivLogicalQuotient
                  bk15CSSRows_triorthogonal).symm
                  (Submodule.Quotient.mk value)) hsubtype
        _ = _ := logicalLabel_l1_plus_allOnes a d hrowDecomp
    rw [bk15CSSRows.encoding_apply_of_mem
      bk15CSSRows_triorthogonal logicalNegativeAState hbits,
      bk15CSSRows.encoding_apply_of_mem
        bk15CSSRows_triorthogonal (logicalAErrorState c) hbits,
      hlabel, logicalAErrorState_label,
      zSupportPhase_eq_binaryPhaseScalar_wordPairing,
      had, l2_coset_pairing_l2dual_decomposition]
    ring
  · rw [bk15CSSRows.encoding_apply_of_not_mem
      bk15CSSRows_triorthogonal logicalNegativeAState hbits,
      bk15CSSRows.encoding_apply_of_not_mem
        bk15CSSRows_triorthogonal (logicalAErrorState c) hbits]
    simp

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

private theorem logicalRegisterToQubit_logicalAErrorState_zero :
    logicalRegisterToQubit (logicalAErrorState 0) =
      OneQubitMagic.phaseAmplitude (-Real.pi / 4) • aZeroState := by
  rw [show logicalAErrorState 0 = logicalNegativeAState by
    ext bits
    change binaryPhaseScalar ((0 : Bit) * (bitstringWordEquiv Unit bits) ()) *
      logicalNegativeAState bits = logicalNegativeAState bits
    rw [zero_mul, binaryPhaseScalar_zero, one_mul]]
  exact logicalRegisterToQubit_negativeA

private theorem logicalRegisterToQubit_logicalAErrorState_one :
    logicalRegisterToQubit (logicalAErrorState 1) =
      (-OneQubitMagic.phaseAmplitude (-Real.pi / 4)) • aOneState := by
  ext bit
  rw [logicalRegisterToQubit_apply]
  fin_cases bit
  · simp [logicalAErrorState, logicalNegativeAState, aOneState_eq_pauliZ,
      aZeroState, OneQubitMagic.phaseState_apply_zero,
      OneQubitMagic.phaseState_apply_one, pauliZ_apply, zPhase]
    unfold binaryPhaseScalar
    split
    · rename_i h
      exact (one_ne_zero h).elim
    · ring
  · simp [logicalAErrorState, logicalNegativeAState, aOneState_eq_pauliZ,
      aZeroState, OneQubitMagic.phaseState_apply_zero,
      OneQubitMagic.phaseState_apply_one, pauliZ_apply, zPhase]
    have hphase :
        OneQubitMagic.phaseAmplitude (-Real.pi / 4) *
            OneQubitMagic.phaseAmplitude (Real.pi / 4) = 1 := by
      rw [← OneQubitMagic.phaseAmplitude_add]
      convert OneQubitMagic.phaseAmplitude_zero using 1 <;> ring
    calc
      _ = (OneQubitMagic.phaseAmplitude (-Real.pi / 4) *
          OneQubitMagic.phaseAmplitude (Real.pi / 4)) *
          (Real.sqrt 2 : Complex)⁻¹ := by
            unfold binaryPhaseScalar
            split
            · rw [hphase]
            · rename_i h
              exact (h rfl).elim
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

private theorem decoded_logicalAErrorState_rankOne (c : Bit) :
    (InnerProductSpace.rankOne Complex
      (logicalRegisterToQubit (logicalAErrorState c))
      (logicalRegisterToQubit (logicalAErrorState c))).toLinearMap =
      if c = 0 then
        (InnerProductSpace.rankOne Complex aZeroState aZeroState).toLinearMap
      else
        (InnerProductSpace.rankOne Complex aOneState aOneState).toLinearMap := by
  by_cases hzero : c = 0
  · rw [if_pos hzero, hzero, logicalRegisterToQubit_logicalAErrorState_zero]
    exact rankOne_global_phase
      (OneQubitMagic.phaseAmplitude (-Real.pi / 4)) aZeroState
      (OneQubitMagic.phaseAmplitude_mul_conj (-Real.pi / 4))
  · have hone : c = 1 := zmod_two_eq_one_of_ne_zero hzero
    rw [if_neg hzero, hone, logicalRegisterToQubit_logicalAErrorState_one]
    apply rankOne_global_phase
    calc
      (-OneQubitMagic.phaseAmplitude (-Real.pi / 4)) *
          star (-OneQubitMagic.phaseAmplitude (-Real.pi / 4)) =
        OneQubitMagic.phaseAmplitude (-Real.pi / 4) *
          star (OneQubitMagic.phaseAmplitude (-Real.pi / 4)) := by
            rw [star_neg]
            ring
      _ = 1 := OneQubitMagic.phaseAmplitude_mul_conj (-Real.pi / 4)

private theorem rankOne_smul_self
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    (scalar : Complex) (psi : H) :
    (InnerProductSpace.rankOne Complex (scalar • psi) (scalar • psi)).toLinearMap =
      (star scalar * scalar) •
        (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  ext x
  simp [InnerProductSpace.rankOne_apply]
  rw [smul_smul]
  rw [mul_comm scalar (starRingEnd Complex scalar)]

private theorem decoderToQubitChannel_rankOne_encoded
    (psi : LogicalRegister) :
    decoderToQubitChannel
        (InnerProductSpace.rankOne Complex
          (ambientEncodingIsometry psi) (ambientEncodingIsometry psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex
        (logicalRegisterToQubit psi) (logicalRegisterToQubit psi)).toLinearMap := by
  rw [decoderToQubitChannel, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply, decoderChannel_rankOne_encoded,
    QuditSubsystem.conjOperator_rankOne]

set_option maxHeartbeats 0 in
private theorem accepted_historyKraus_error_encoded
    (zOutcome : ZJointSyndrome) (error : Word)
    (hsyndrome : l1Syndrome error = 0) :
    historyKraus
        (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
        (bk15ErrorWordState error) =
      (binaryPhaseScalar
          (l2SyndromeSection (zBinarySyndrome zOutcome) ⬝ᵥ error) *
        (32 : Complex)⁻¹) •
        toHermitianQubitOperator (cssZCheck error)
          (ambientEncodingIsometry logicalNegativeAState) := by
  rw [accepted_historyKraus_error,
    historyKraus_ideal]
  simp only [hsyndrome, map_zero, signSyndrome, if_pos]
  rw [zeroZProjectedIdeal_zeroErrorWord, map_smul]
  rw [smul_smul]

set_option maxHeartbeats 0 in
private theorem accepted_historyKraus_error_zero
    (zOutcome : ZJointSyndrome) (error : Word)
    (hsyndrome : l1Syndrome error ≠ 0) :
    historyKraus
        (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
        (bk15ErrorWordState error) = 0 := by
  have hmatching : signSyndrome (l1Syndrome error) ≠
      signSyndrome (0 : XCheckIndex → Bit) := by
    intro hsign
    apply hsyndrome
    have hbinary := congrArg binarySyndrome hsign
    simpa using hbinary
  rw [accepted_historyKraus_error,
    historyKraus_ideal, if_neg hmatching]
  simp

set_option maxHeartbeats 0 in
set_option maxRecDepth 262144 in
private theorem decoded_accepted_history_rankOne_of_l1Dual
    (zOutcome : ZJointSyndrome) (error : Word)
    (b : Sum (Fin 4) QuadraticIndex → Bit) (c : Bit)
    (herror : error = l2CoefficientMap b + c • allOnes) :
    decoderToQubitChannel
        (InnerProductSpace.rankOne Complex
          (historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState error))
          (historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState error))).toLinearMap =
      (1024 : Complex)⁻¹ •
        (if c = 0 then
          (InnerProductSpace.rankOne Complex aZeroState aZeroState).toLinearMap
        else
          (InnerProductSpace.rankOne Complex aOneState aOneState).toLinearMap) := by
  have hsyndrome : l1Syndrome error = 0 := by
    rw [herror]
    have hmember : l2CoefficientMap b + c • allOnes ∈ L1.dual.carrier := by
      rw [l1_dual_carrier_eq_model]
      exact ⟨(b, c), rfl⟩
    rw [l1_dual_carrier_eq_l1Syndrome_ker] at hmember
    exact hmember
  rw [accepted_historyKraus_error_encoded zOutcome error hsyndrome,
    herror, cssZCheck_l2_plus_allOnes_encoded,
    rankOne_smul_self, map_smul,
    decoderToQubitChannel_rankOne_encoded,
    decoded_logicalAErrorState_rankOne]
  generalize hphase : l2SyndromeSection (zBinarySyndrome zOutcome) ⬝ᵥ
    (l2CoefficientMap b + c • allOnes) = phase
  have hphaseStar : star (binaryPhaseScalar phase) = binaryPhaseScalar phase := by
    exact binaryPhaseScalar_star phase
  have hinv : star ((32 : Complex)⁻¹) = (32 : Complex)⁻¹ := by
    norm_num
  have hscalar :
      star (binaryPhaseScalar phase * (32 : Complex)⁻¹) *
        (binaryPhaseScalar phase * (32 : Complex)⁻¹) =
        (1024 : Complex)⁻¹ := by
    rw [star_mul, hphaseStar, hinv]
    calc
      ((32 : Complex)⁻¹ * binaryPhaseScalar phase) *
          (binaryPhaseScalar phase * (32 : Complex)⁻¹) =
        (binaryPhaseScalar phase * binaryPhaseScalar phase) *
          ((32 : Complex)⁻¹ * (32 : Complex)⁻¹) := by ring
      _ = (1024 : Complex)⁻¹ := by
        rw [binaryPhaseScalar_mul_self]
        norm_num
  rw [hscalar]

private theorem trace_negativeA_rankOne_aZero :
    (LinearMap.trace Complex QubitSpace
      (aBasisProjector .negative *
        (InnerProductSpace.rankOne Complex aZeroState aZeroState).toLinearMap)).re = 0 := by
  rw [OneQubitMagic.trace_mul_rankOne]
  have hprojector : aBasisProjector .negative aZeroState = 0 := by
    simp [aBasisProjector, Coding.PauliSymplectic.StabilizerOutcome.sign,
      aBasisObservable_aZeroState]
  rw [hprojector]
  simp

private theorem trace_negativeA_rankOne_aOne :
    (LinearMap.trace Complex QubitSpace
      (aBasisProjector .negative *
        (InnerProductSpace.rankOne Complex aOneState aOneState).toLinearMap)).re = 1 := by
  rw [OneQubitMagic.trace_mul_rankOne]
  have hprojector : aBasisProjector .negative aOneState = aOneState := by
    simp only [aBasisProjector, Coding.PauliSymplectic.StabilizerOutcome.sign,
      LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
      aBasisObservable_aOneState]
    module
  rw [hprojector, inner_self_eq_norm_sq_to_K, aOneState_norm]
  norm_num

set_option maxRecDepth 262144 in
private theorem mem_l1DualWords_iff_exists_l2_plus_allOnes
    (error : Word) :
    error ∈ l1DualWords ↔
      ∃ b : Sum (Fin 4) QuadraticIndex → Bit, ∃ c : Bit,
        error = l2CoefficientMap b + c • allOnes := by
  rw [mem_l1DualWords_iff, mem_l1_dual_iff_exists_l2_plus_allOnes]

set_option maxRecDepth 262144 in
private theorem l2LogicalCosetWords_subset_l1DualWords
    {error : Word} (herror : error ∈ l2LogicalCosetWords) :
    error ∈ l1DualWords := by
  rw [mem_l2LogicalCosetWords_iff] at herror
  rcases herror with ⟨b, rfl⟩
  rw [mem_l1DualWords_iff_exists_l2_plus_allOnes]
  exact ⟨b, 1, by simp⟩

set_option maxRecDepth 262144 in
/-- The complex raw negative-A functional after the concrete decoder. -/
private noncomputable def negativeADecodedTrace :
    Operator BK15Register →ₗ[Complex] Complex where
  toFun A := LinearMap.trace Complex QubitSpace
    (aBasisProjector .negative * decoderToQubitChannel A)
  map_add' A B := by simp [mul_add]
  map_smul' scalar A := by simp [mul_smul_comm]

set_option maxRecDepth 262144 in
private theorem negativeA_trace_decoded_accepted_history
    (zOutcome : ZJointSyndrome) (error : Word) :
    (negativeADecodedTrace
      (InnerProductSpace.rankOne Complex
        (historyKraus
          (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
          (bk15ErrorWordState error))
        (historyKraus
          (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
          (bk15ErrorWordState error))).toLinearMap).re =
      if error ∈ l2LogicalCosetWords then (1024 : Real)⁻¹ else 0 := by
  classical
  by_cases haccepted : error ∈ l1DualWords
  · obtain ⟨b, c, herror⟩ :=
      (mem_l1DualWords_iff_exists_l2_plus_allOnes error).mp haccepted
    unfold negativeADecodedTrace
    change (LinearMap.trace Complex QubitSpace
      (aBasisProjector .negative * decoderToQubitChannel
        (InnerProductSpace.rankOne Complex
          (historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState error))
          (historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState error))).toLinearMap)).re = _
    rw [decoded_accepted_history_rankOne_of_l1Dual zOutcome error b c herror]
    by_cases hzero : c = 0
    · have hnotlogical : error ∉ l2LogicalCosetWords := by
        intro hlogical
        have hinL2 : error ∈ l2Words := by
          rw [l2Words, Finset.mem_image]
          exact ⟨b, Finset.mem_univ _, by simpa [hzero] using herror.symm⟩
        exact Finset.disjoint_left.mp l2Words_disjoint_l2LogicalCosetWords
          hinL2 hlogical
      rw [if_neg hnotlogical, if_pos hzero, mul_smul_comm, map_smul]
      simp only [smul_eq_mul, Complex.mul_re]
      rw [trace_negativeA_rankOne_aZero]
      norm_num
    · have hone : c = 1 := zmod_two_eq_one_of_ne_zero hzero
      have hlogical : error ∈ l2LogicalCosetWords := by
        rw [mem_l2LogicalCosetWords_iff]
        exact ⟨b, by simpa [hone] using herror⟩
      rw [if_pos hlogical, if_neg hzero, mul_smul_comm, map_smul]
      simp only [smul_eq_mul, Complex.mul_re]
      rw [trace_negativeA_rankOne_aOne]
      norm_num
  · have hsyndrome : l1Syndrome error ≠ 0 := by
      intro hzero
      apply haccepted
      rw [mem_l1DualWords_iff, l1_dual_carrier_eq_l1Syndrome_ker]
      exact hzero
    have hnotlogical : error ∉ l2LogicalCosetWords := by
      intro hlogical
      exact haccepted (l2LogicalCosetWords_subset_l1DualWords hlogical)
    rw [accepted_historyKraus_error_zero zOutcome error hsyndrome,
      if_neg hnotlogical]
    have hrankZero :
        (InnerProductSpace.rankOne Complex (0 : BK15Register)
          (0 : BK15Register)).toLinearMap = (0 : Operator BK15Register) := by
      have hrankZeroCL :
          InnerProductSpace.rankOne Complex (0 : BK15Register) (0 : BK15Register) = 0 := by
        rw [InnerProductSpace.rankOne_eq_zero]
        exact Or.inl rfl
      rw [hrankZeroCL]
      rfl
    rw [hrankZero]
    have htraceZero : negativeADecodedTrace (0 : Operator BK15Register) = (0 : Complex) :=
      negativeADecodedTrace.map_zero
    rw [htraceZero]
    rfl

set_option maxRecDepth 262144 in
private theorem zJointSyndrome_card : Fintype.card ZJointSyndrome = 1024 := by
  have hstabilizer : Fintype.card StabilizerOutcome = 2 := by native_decide
  change Fintype.card StabilizerOutcome ^ (4 + Fintype.card QuadraticIndex) = 1024
  rw [hstabilizer, quadraticIndex_card]
  norm_num

private theorem sum_negativeA_trace_decoded_accepted_history
    (error : Word) :
    ∑ zOutcome : ZJointSyndrome,
      (negativeADecodedTrace
        (InnerProductSpace.rankOne Complex
          (historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState error))
          (historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState error))).toLinearMap).re =
      if error ∈ l2LogicalCosetWords then 1 else 0 := by
  classical
  simp_rw [negativeA_trace_decoded_accepted_history]
  by_cases hlogical : error ∈ l2LogicalCosetWords
  · simp only [if_pos hlogical, Finset.sum_const, Finset.card_univ]
    rw [zJointSyndrome_card]
    norm_num
  · simp [hlogical]

set_option maxRecDepth 262144 in
/-- The unnormalised negative-A numerator of the literal accepted physical
branch after the concrete total decoder. -/
noncomputable def acceptedNegativeAWeight (epsilon : BK15Epsilon) : Real :=
  (negativeADecodedTrace (rawEndpoint epsilon .accepted)).re

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

private theorem acceptedNegativeAWeight_eq_history_word_sum
    (epsilon : BK15Epsilon) :
    acceptedNegativeAWeight epsilon =
      ∑ history : History,
        (if historyOutcome history = .accepted then
          ∑ word : Word, bk15WordWeight epsilon word *
            (negativeADecodedTrace
              (InnerProductSpace.rankOne Complex
                (historyKraus history (bk15ErrorWordState word))
                (historyKraus history (bk15ErrorWordState word))).toLinearMap).re
        else 0) := by
  classical
  unfold acceptedNegativeAWeight
  rw [rawEndpoint_eq_branchOperator,
    FiniteInstrument.branchOperator_apply, rawInput_toOperator_sum]
  simp only [historyInstrument, historyKrausFamily]
  rw [map_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro history _
  by_cases hvisible : historyOutcome history = .accepted
  · erw [if_pos hvisible, if_pos hvisible]
    rw [sum_comp, comp_sum, map_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro word _
    rw [LinearMap.smul_comp, LinearMap.comp_smul,
      sandwich_rankOne, map_smul]
    simp [Complex.mul_re]
  · erw [if_neg hvisible, if_neg hvisible]
    simp

private theorem acceptedNegativeAWeight_eq_word_z_sum
    (epsilon : BK15Epsilon) :
    acceptedNegativeAWeight epsilon =
      ∑ word : Word, bk15WordWeight epsilon word *
        ∑ zOutcome : ZJointSyndrome,
          (negativeADecodedTrace
            (InnerProductSpace.rankOne Complex
              (historyKraus
                (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
                (bk15ErrorWordState word))
              (historyKraus
                (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
                (bk15ErrorWordState word))).toLinearMap).re := by
  classical
  rw [acceptedNegativeAWeight_eq_history_word_sum, Fintype.sum_prod_type]
  calc
    ∑ zOutcome : ZJointSyndrome, ∑ xOutcome : XJointSyndrome,
        (if historyOutcome (zOutcome, xOutcome) = .accepted then
          ∑ word : Word, bk15WordWeight epsilon word *
            (negativeADecodedTrace
              (InnerProductSpace.rankOne Complex
                (historyKraus (zOutcome, xOutcome)
                  (bk15ErrorWordState word))
                (historyKraus (zOutcome, xOutcome)
                  (bk15ErrorWordState word))).toLinearMap).re
        else 0) =
      ∑ zOutcome : ZJointSyndrome, ∑ word : Word,
        bk15WordWeight epsilon word *
          (negativeADecodedTrace
            (InnerProductSpace.rankOne Complex
              (historyKraus
                (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
                (bk15ErrorWordState word))
              (historyKraus
                (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
                (bk15ErrorWordState word))).toLinearMap).re := by
          apply Finset.sum_congr rfl
          intro zOutcome _
          rw [Fintype.sum_eq_single
            (signSyndrome (0 : XCheckIndex → Bit))]
          · simp [historyOutcome_accepted_iff]
          · intro xOutcome hxOutcome
            have hnotaccepted :
              historyOutcome (zOutcome, xOutcome) ≠ .accepted := by
                intro haccepted
                exact hxOutcome (historyOutcome_accepted_iff zOutcome xOutcome |>.mp
                  haccepted)
            simp [hnotaccepted]
    _ = ∑ word : Word, bk15WordWeight epsilon word *
        ∑ zOutcome : ZJointSyndrome,
          (negativeADecodedTrace
            (InnerProductSpace.rankOne Complex
              (historyKraus
                (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
                (bk15ErrorWordState word))
              (historyKraus
                (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
                (bk15ErrorWordState word))).toLinearMap).re := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro word _
          rw [← Finset.mul_sum]

set_option linter.constructorNameAsVariable false in
/-- The accepted physical branch, decoded by the total CSS decoder and tested
against the literal negative-A projector, is exactly the nontrivial `L2`
logical-coset word numerator. -/
theorem accepted_negativeA_weight_eq_l2LogicalCoset_wordSum
    (epsilon : BK15Epsilon) :
    acceptedNegativeAWeight epsilon =
      ∑ word ∈ l2LogicalCosetWords, bk15WordWeight epsilon word := by
  classical
  rw [acceptedNegativeAWeight_eq_word_z_sum]
  simp_rw [sum_negativeA_trace_decoded_accepted_history]
  have hfilter :
      (Finset.univ.filter fun word : Word => word ∈ l2LogicalCosetWords) =
        l2LogicalCosetWords := by
    ext word
    simp
  calc
    ∑ word : Word, bk15WordWeight epsilon word *
        (if word ∈ l2LogicalCosetWords then 1 else 0) =
      ∑ word : Word,
        if word ∈ l2LogicalCosetWords then bk15WordWeight epsilon word else 0 := by
          apply Finset.sum_congr rfl
          intro word _
          by_cases hmember : word ∈ l2LogicalCosetWords <;> simp [hmember]
    _ = ∑ word ∈ Finset.univ.filter
        (fun word : Word => word ∈ l2LogicalCosetWords),
          bk15WordWeight epsilon word := by
            rw [Finset.sum_filter]
    _ = ∑ word ∈ l2LogicalCosetWords, bk15WordWeight epsilon word := by
          rw [hfilter]

/-! ## Enumerator collection -/

private theorem hammingWeight_le_fifteen (word : Word) :
    Coding.HammingWeight word ≤ 15 := by
  rw [Coding.HammingWeight_eq_card_hammingSupport]
  calc
    (Coding.hammingSupport word).card ≤ (Finset.univ : Finset (Fin 15)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = 15 := by simp

private def bk15WeightIndex (word : Word) : Fin 16 :=
  ⟨Coding.HammingWeight word, by
    have hweight := hammingWeight_le_fifteen word
    omega⟩

private theorem bk15WordWeight_eq_hammingWeight
    (epsilon : BK15Epsilon) (word : Word) :
    bk15WordWeight epsilon word =
      epsilon.epsilon ^ Coding.HammingWeight word *
        epsilon.cleanWeight ^ (15 - Coding.HammingWeight word) := by
  classical
  have hfactor : ∀ site : Fin 15,
      aInputWeight epsilon (word site) =
        if word site = 0 then epsilon.cleanWeight else epsilon.epsilon := by
    intro site
    generalize hbit : word site = bit
    fin_cases bit <;> rfl
  unfold bk15WordWeight
  simp_rw [hfactor]
  rw [Finset.prod_ite]
  have hnonzero :
      (Finset.univ.filter fun site : Fin 15 => ¬ word site = 0) =
        Coding.hammingSupport word := by
    ext site
    simp [Coding.hammingSupport]
  have hzeroCard :
      (Finset.univ.filter fun site : Fin 15 => word site = 0).card =
        15 - Coding.HammingWeight word := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (fun site : Fin 15 => word site = 0)
    rw [hnonzero, ← Coding.HammingWeight_eq_card_hammingSupport] at hpartition
    have hunivCard : (Finset.univ : Finset (Fin 15)).card = 15 := by simp
    rw [hunivCard] at hpartition
    exact Nat.eq_sub_of_add_eq hpartition
  have hnonzeroCard :
      (Finset.univ.filter fun site : Fin 15 => ¬ word site = 0).card =
        Coding.HammingWeight word := by
    rw [hnonzero, Coding.HammingWeight_eq_card_hammingSupport]
  rw [Finset.prod_const, Finset.prod_const, hzeroCard, hnonzeroCard]
  ring

private theorem sum_bk15WordWeight_eq_weightEnumerator
    (epsilon : BK15Epsilon) (words : Finset Word) :
    ∑ word ∈ words, bk15WordWeight epsilon word =
      ∑ weight : Fin 16,
        (weightCount words weight.1 : Real) *
          (epsilon.epsilon ^ weight.1 * epsilon.cleanWeight ^ (15 - weight.1)) := by
  classical
  calc
    ∑ word ∈ words, bk15WordWeight epsilon word =
        ∑ weight : Fin 16, ∑ word ∈ words with bk15WeightIndex word = weight,
          bk15WordWeight epsilon word := by
            symm
            exact Finset.sum_fiberwise_of_maps_to
              (fun word _ => Finset.mem_univ _) _
    _ = ∑ weight : Fin 16,
        (weightCount words weight.1 : Real) *
          (epsilon.epsilon ^ weight.1 * epsilon.cleanWeight ^ (15 - weight.1)) := by
            apply Finset.sum_congr rfl
            intro weight _
            have hfilter :
                words.filter (fun word => bk15WeightIndex word = weight) =
                  words.filter (fun word => Coding.HammingWeight word = weight.1) := by
              ext word
              simp only [Finset.mem_filter]
              exact and_congr_right (fun _ => Fin.ext_iff)
            rw [show (∑ word ∈ words with bk15WeightIndex word = weight,
                bk15WordWeight epsilon word) =
                ∑ word ∈ words with bk15WeightIndex word = weight,
                  epsilon.epsilon ^ weight.1 * epsilon.cleanWeight ^ (15 - weight.1) by
                apply Finset.sum_congr rfl
                intro word hword
                rw [Finset.mem_filter] at hword
                rw [bk15WordWeight_eq_hammingWeight]
                have hweight : Coding.HammingWeight word = weight.1 := by
                  simpa [bk15WeightIndex, Fin.ext_iff] using hword.2
                rw [hweight]]
            rw [Finset.sum_const, nsmul_eq_mul, hfilter]
            rfl

private theorem l1Dual_wordWeight_sum_expanded (epsilon : BK15Epsilon) :
    ∑ word ∈ l1DualWords, bk15WordWeight epsilon word =
      epsilon.cleanWeight ^ 15 +
        35 * (epsilon.epsilon ^ 3 * epsilon.cleanWeight ^ 12) +
        105 * (epsilon.epsilon ^ 4 * epsilon.cleanWeight ^ 11) +
        168 * (epsilon.epsilon ^ 5 * epsilon.cleanWeight ^ 10) +
        280 * (epsilon.epsilon ^ 6 * epsilon.cleanWeight ^ 9) +
        435 * (epsilon.epsilon ^ 7 * epsilon.cleanWeight ^ 8) +
        435 * (epsilon.epsilon ^ 8 * epsilon.cleanWeight ^ 7) +
        280 * (epsilon.epsilon ^ 9 * epsilon.cleanWeight ^ 6) +
        168 * (epsilon.epsilon ^ 10 * epsilon.cleanWeight ^ 5) +
        105 * (epsilon.epsilon ^ 11 * epsilon.cleanWeight ^ 4) +
        35 * (epsilon.epsilon ^ 12 * epsilon.cleanWeight ^ 3) +
        epsilon.epsilon ^ 15 := by
  rw [sum_bk15WordWeight_eq_weightEnumerator]
  simp [Fin.sum_univ_succ, l1Dual_weight_enumerator]
  ring

private theorem l2LogicalCoset_wordWeight_sum_expanded (epsilon : BK15Epsilon) :
    ∑ word ∈ l2LogicalCosetWords, bk15WordWeight epsilon word =
      35 * (epsilon.epsilon ^ 3 * epsilon.cleanWeight ^ 12) +
        168 * (epsilon.epsilon ^ 5 * epsilon.cleanWeight ^ 10) +
        435 * (epsilon.epsilon ^ 7 * epsilon.cleanWeight ^ 8) +
        280 * (epsilon.epsilon ^ 9 * epsilon.cleanWeight ^ 6) +
        105 * (epsilon.epsilon ^ 11 * epsilon.cleanWeight ^ 4) +
        epsilon.epsilon ^ 15 := by
  rw [sum_bk15WordWeight_eq_weightEnumerator]
  simp [Fin.sum_univ_succ, l2LogicalCoset_weight_enumerator]
  ring

set_option linter.constructorNameAsVariable false in
/-- The accepted physical Born mass has the BK15 closed form derived from the
literal dual-word enumerator. -/
theorem accepted_endpointWeight_eq_closedForm (epsilon : BK15Epsilon) :
    endpointWeight epsilon .accepted =
      (1 + 15 * bk15_r epsilon ^ 8) / 16 := by
  rw [accepted_endpointWeight_eq_l1Dual_wordSum,
    l1Dual_wordWeight_sum_expanded]
  unfold bk15_r BK15Epsilon.cleanWeight
  ring

set_option linter.constructorNameAsVariable false in
/-- The decoded negative-A raw numerator has the BK15 logical-coset closed
form derived from its exact finite weight enumerator. -/
theorem accepted_negativeA_weight_eq_closedForm (epsilon : BK15Epsilon) :
    acceptedNegativeAWeight epsilon =
      (1 - 15 * bk15_r epsilon ^ 7 + 15 * bk15_r epsilon ^ 8 -
        bk15_r epsilon ^ 15) / 32 := by
  rw [accepted_negativeA_weight_eq_l2LogicalCoset_wordSum,
    l2LogicalCoset_wordWeight_sum_expanded]
  unfold bk15_r BK15Epsilon.cleanWeight
  ring

/-! ## Actual accepted-run normalization -/

/-- The A-frame error of a normalized one-qubit density is its literal
negative-A Born weight.  This is kept private because #707 exports only the
BK15 physical specialization below. -/
private theorem aInputError_eq_negativeA_trace
    (rho : DensityOperator QubitSpace) :
    aInputError rho =
      (LinearMap.trace Complex QubitSpace
        (aBasisProjector .negative * rho.toOperator)).re := by
  have hsum : aInputSquaredOverlap rho +
      OneQubitMagic.projectionSquaredOverlap
        (aBasisProjector .negative) rho = 1 := by
    unfold aInputSquaredOverlap OneQubitMagic.projectionSquaredOverlap
    have htrace :
        LinearMap.trace Complex QubitSpace
            (aBasisProjector .positive * rho.toOperator) +
          LinearMap.trace Complex QubitSpace
            (aBasisProjector .negative * rho.toOperator) = 1 := by
      calc
        LinearMap.trace Complex QubitSpace
            (aBasisProjector .positive * rho.toOperator) +
          LinearMap.trace Complex QubitSpace
            (aBasisProjector .negative * rho.toOperator) =
            LinearMap.trace Complex QubitSpace
              ((aBasisProjector .positive + aBasisProjector .negative) *
                rho.toOperator) := by
              rw [add_mul, map_add]
        _ = LinearMap.trace Complex QubitSpace rho.toOperator := by
              rw [aBasisProjector_add, one_mul]
        _ = 1 := rho.trace_one
    have hre := congrArg Complex.re htrace
    exact_mod_cast hre
  unfold aInputError
  have hnegative :
      OneQubitMagic.projectionSquaredOverlap
          (aBasisProjector .negative) rho =
        1 - aInputSquaredOverlap rho := by
    linarith
  rw [← hnegative]
  rfl

/-- The actual positive accepted endpoint, after the concrete decoder and
one-qubit basis identification, is the raw decoded endpoint divided by its
physical Born mass. -/
private theorem qubitEndpointConditional_accepted_toOperator
    (epsilon : BK15Epsilon)
    (hpositive : 0 < endpointWeight epsilon .accepted) :
    (qubitEndpointConditional epsilon .accepted hpositive).toOperator =
      ((endpointWeight epsilon .accepted : Complex)⁻¹) •
        decoderToQubitChannel (rawEndpoint epsilon .accepted) := by
  have hdecode (rho : DensityOperator BK15Register) :
      (logicalRegisterToQubit.conjDensity (decoderChannel.mapDensity rho)).toOperator =
        decoderToQubitChannel rho.toOperator := by
    rw [UnitaryTransport.conjDensity_toOperator,
      QuantumChannel.mapDensity_toOperator]
    rfl
  change (logicalRegisterToQubit.conjDensity
    (decoderChannel.mapDensity (endpointConditional epsilon .accepted hpositive))).toOperator = _
  rw [hdecode, endpointConditional_toOperator]
  exact decoderToQubitChannel.toLinearMap.map_smul _ _

/-- Normalizing the concrete accepted endpoint scales its literal decoded
negative-A numerator by the same positive physical accepted mass. -/
private theorem acceptedOutput_error_eq_raw_normalization
    (epsilon : BK15Epsilon)
    (hpositive : 0 < endpointWeight epsilon .accepted) :
    aInputError (qubitEndpointConditional epsilon .accepted hpositive) =
      acceptedNegativeAWeight epsilon / endpointWeight epsilon .accepted := by
  rw [aInputError_eq_negativeA_trace,
    qubitEndpointConditional_accepted_toOperator]
  unfold acceptedNegativeAWeight negativeADecodedTrace
  rw [mul_smul_comm, map_smul]
  have hscalar :
      ((endpointWeight epsilon .accepted : Complex)⁻¹) =
        ((endpointWeight epsilon .accepted)⁻¹ : Real) := by
    norm_cast
  rw [hscalar]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  simp only [zero_mul, sub_zero, div_eq_mul_inv]
  change (endpointWeight epsilon .accepted)⁻¹ *
      (LinearMap.trace Complex QubitSpace
        (aBasisProjector .negative *
          decoderToQubitChannel (rawEndpoint epsilon .accepted))).re =
    (LinearMap.trace Complex QubitSpace
      (aBasisProjector .negative *
        decoderToQubitChannel (rawEndpoint epsilon .accepted))).re *
      (endpointWeight epsilon .accepted)⁻¹
  ring

/-- The packaged BK15 run has the source acceptance probability, derived from
the literal accepted physical endpoint rather than stored as a formula. -/
theorem bk15Run_successProbability_closed_form
    (epsilon : BK15Epsilon) (hpositive : 0 < epsilon.epsilon) :
    (bk15Run epsilon hpositive).successProbability =
      (1 + 15 * bk15_r epsilon ^ 8) / 16 := by
  rw [bk15Run_successProbability, accepted_endpointWeight_eq_closedForm]

/-- The actual decoded accepted output of the packaged BK15 run has the
Bravyi--Kitaev negative-A error recurrence on the strict source interval. -/
theorem bk15_acceptedOutputError_closed_form
    (epsilon : BK15Epsilon) (hpositive : 0 < epsilon.epsilon) :
    bk15OutputError (bk15Run epsilon hpositive).acceptedOutput aZeroDensity =
      (1 - 15 * bk15_r epsilon ^ 7 + 15 * bk15_r epsilon ^ 8 -
        bk15_r epsilon ^ 15) / (2 * (1 + 15 * bk15_r epsilon ^ 8)) := by
  rw [bk15Run_acceptedOutput, bk15OutputError,
    acceptedOutput_error_eq_raw_normalization,
    accepted_negativeA_weight_eq_closedForm,
    accepted_endpointWeight_eq_closedForm]
  have hdenom : 1 + 15 * bk15_r epsilon ^ 8 ≠ 0 :=
    (bk15_recurrence_denominator_pos epsilon).ne'
  field_simp [hdenom]
  ring

/-- The closed zero-noise input has accepted raw physical mass one.  This is
an endpoint statement, not a normalized rejected branch. -/
theorem zeroEpsilon_accepted_endpointWeight :
    endpointWeight zeroEpsilon .accepted = 1 := by
  rw [accepted_endpointWeight_eq_closedForm]
  norm_num [bk15_r, zeroEpsilon]

/-- The actual full decoded BK15 operation sends the closed zero-noise input
to the ideal A-frame density, so its physical output error is zero. -/
theorem zeroEpsilon_decoded_output_error :
    bk15OutputError (decodedOperation.mapDensity (rawInput zeroEpsilon))
      aZeroDensity = 0 := by
  rw [decodedOperation_zeroEpsilon]
  unfold bk15OutputError aInputError aInputSquaredOverlap
    OneQubitMagic.projectionSquaredOverlap
  rw [aBasisProjector_positive_eq_aZeroDensity_toOperator,
    aZeroDensity_eq_phaseStateDensity,
    OneQubitMagic.phaseStateDensity_toOperator,
    OneQubitMagic.trace_mul_rankOne]
  simp [InnerProductSpace.rankOne_apply,
    OneQubitMagic.phaseState_inner_self]

end Recurrence
end BK15
end Distillation
end QEC
