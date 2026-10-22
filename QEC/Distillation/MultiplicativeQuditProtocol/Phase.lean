import QEC.Coding.Stabilizer.PauliSemantics
import QEC.Distillation.MultiplicativeQuditProtocol.Register
import Mathlib.RingTheory.Trace.Basic

/-!
# Local finite-field phase coordinates for Ngu24

This compile-free #725 layer fixes the literal characteristic-two trace and
the corresponding local three-qudit diagonal CCZ action.  It deliberately
stops before multi-site products and encoding.
-/

noncomputable section

namespace QEC.Distillation

open Semantics

universe u

variable {F ι : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]

/-- The finite-field trace used in the Ngu24 characteristic-two phase. -/
def fieldTrace (x : F) : ZMod 2 := Algebra.trace (ZMod 2) F x

omit [Fintype F] in
/-- The field trace is additive because it is Mathlib's algebra trace map. -/
theorem fieldTrace_add (x y : F) :
    fieldTrace (x + y) = fieldTrace x + fieldTrace y := by
  simp [fieldTrace]

/-- The sign character induced by the actual finite-field trace. -/
def additiveCharacter (x : F) : Complex :=
  Coding.PauliSymplectic.binaryPhaseScalar (fieldTrace x)

omit [Fintype F] in
/-- The trace-induced sign is multiplicative under addition. -/
theorem additiveCharacter_add (x y : F) :
    additiveCharacter (x + y) = additiveCharacter x * additiveCharacter y := by
  rw [additiveCharacter, fieldTrace_add]
  exact Coding.PauliSymplectic.binaryPhaseScalar_add (fieldTrace x) (fieldTrace y)

omit [Fintype F] in
/-- Every value of the trace-induced sign is its own multiplicative inverse. -/
theorem additiveCharacter_square (x : F) :
    additiveCharacter x * additiveCharacter x = 1 := by
  rw [additiveCharacter]
  by_cases hzero : fieldTrace x = 0
  · simp [Coding.PauliSymplectic.binaryPhaseScalar, hzero]
  · have hone : fieldTrace x = 1 :=
      Coding.PauliSymplectic.zmod_two_eq_one_of_ne_zero hzero
    simp [Coding.PauliSymplectic.binaryPhaseScalar, hone]

omit [Fintype F] in
/-- The trace-induced sign is fixed by complex conjugation. -/
theorem additiveCharacter_conj (x : F) :
    starRingEnd Complex (additiveCharacter x) = additiveCharacter x := by
  rw [additiveCharacter]
  by_cases hzero : fieldTrace x = 0
  · simp [Coding.PauliSymplectic.binaryPhaseScalar, hzero]
  · have hone : fieldTrace x = 1 :=
      Coding.PauliSymplectic.zmod_two_eq_one_of_ne_zero hzero
    simp [Coding.PauliSymplectic.binaryPhaseScalar, hone]

/-- The source's local degree-three phase amplitude. -/
def cczAmplitude (x y z : F) : Complex :=
  additiveCharacter (x * y * z)

omit [Fintype F] in
/-- The local degree-three amplitude is a sign. -/
theorem cczAmplitude_square (x y z : F) :
    cczAmplitude x y z * cczAmplitude x y z = 1 :=
  additiveCharacter_square (x * y * z)

omit [Fintype F] in
/-- The local degree-three amplitude has unit complex norm. -/
theorem cczAmplitude_mul_conj (x y z : F) :
    cczAmplitude x y z * starRingEnd Complex (cczAmplitude x y z) = 1 := by
  rw [cczAmplitude, additiveCharacter_conj]
  exact additiveCharacter_square (x * y * z)

/-- Pointwise multiplication by the Ngu24 local degree-three phase. -/
def cczDiagonalOperator :
    Operator (EuclideanSpace Complex (F × F × F)) where
  toFun psi := WithLp.toLp 2 fun label =>
    cczAmplitude label.1 label.2.1 label.2.2 * psi label
  map_add' := by
    intro psi chi
    ext label
    change cczAmplitude label.1 label.2.1 label.2.2 * (psi label + chi label) =
      cczAmplitude label.1 label.2.1 label.2.2 * psi label +
        cczAmplitude label.1 label.2.1 label.2.2 * chi label
    ring
  map_smul' := by
    intro scalar psi
    ext label
    change cczAmplitude label.1 label.2.1 label.2.2 * (scalar * psi label) =
      scalar * (cczAmplitude label.1 label.2.1 label.2.2 * psi label)
    ring

@[simp]
theorem cczDiagonalOperator_apply (psi : EuclideanSpace Complex (F × F × F))
    (label : F × F × F) :
    cczDiagonalOperator psi label =
      cczAmplitude label.1 label.2.1 label.2.2 * psi label :=
  rfl

/-- Applying the local diagonal operation twice is the identity. -/
theorem cczDiagonalOperator_square :
    cczDiagonalOperator (F := F) * cczDiagonalOperator =
      (1 : Operator (EuclideanSpace Complex (F × F × F))) := by
  ext psi label
  simp only [Module.End.mul_apply, cczDiagonalOperator_apply]
  rw [← mul_assoc, cczAmplitude_square]
  simp

/-- The local diagonal operation preserves the Hilbert inner product. -/
theorem cczDiagonalOperator_map_inner
    (psi chi : EuclideanSpace Complex (F × F × F)) :
    inner Complex (cczDiagonalOperator psi) (cczDiagonalOperator chi) =
      inner Complex psi chi := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro label _
  simp only [cczDiagonalOperator_apply, RCLike.inner_apply, map_mul]
  calc
    (cczAmplitude label.1 label.2.1 label.2.2 * chi label) *
        (starRingEnd Complex (cczAmplitude label.1 label.2.1 label.2.2) *
          starRingEnd Complex (psi label)) =
        (cczAmplitude label.1 label.2.1 label.2.2 *
          starRingEnd Complex (cczAmplitude label.1 label.2.1 label.2.2)) *
          (chi label * starRingEnd Complex (psi label)) := by ring
    _ = chi label * starRingEnd Complex (psi label) := by
      rw [cczAmplitude_mul_conj]
      ring

/-- The local phase with the same sign diagonal map supplied as its explicit inverse. -/
noncomputable def cczLinearEquiv :
    EuclideanSpace Complex (F × F × F) ≃ₗ[Complex]
      EuclideanSpace Complex (F × F × F) where
  toFun psi := cczDiagonalOperator psi
  invFun psi := cczDiagonalOperator psi
  left_inv := by
    intro psi
    have h := LinearMap.congr_fun (cczDiagonalOperator_square (F := F)) psi
    simpa only [Module.End.mul_apply, Module.End.one_apply] using h
  right_inv := by
    intro psi
    have h := LinearMap.congr_fun (cczDiagonalOperator_square (F := F)) psi
    simpa only [Module.End.mul_apply, Module.End.one_apply] using h
  map_add' := cczDiagonalOperator.map_add
  map_smul' := cczDiagonalOperator.map_smul

@[simp]
theorem cczLinearEquiv_apply (psi : EuclideanSpace Complex (F × F × F))
    (label : F × F × F) :
    cczLinearEquiv psi label = cczAmplitude label.1 label.2.1 label.2.2 * psi label :=
  rfl

@[simp]
theorem cczLinearEquiv_symm_apply (psi : EuclideanSpace Complex (F × F × F))
    (label : F × F × F) :
    (cczLinearEquiv (F := F)).symm psi label =
      cczAmplitude label.1 label.2.1 label.2.2 * psi label :=
  rfl

/-- The concrete source-local three-qudit CCZ transport. -/
noncomputable def cczTransport :
    UnitaryTransport (EuclideanSpace Complex (F × F × F))
      (EuclideanSpace Complex (F × F × F)) where
  toLinearEquiv := cczLinearEquiv
  map_inner := cczDiagonalOperator_map_inner

@[simp]
theorem cczTransport_apply (psi : EuclideanSpace Complex (F × F × F))
    (label : F × F × F) :
    cczTransport psi label = cczAmplitude label.1 label.2.1 label.2.2 * psi label :=
  rfl

/-- Named inner-product preservation for the concrete CCZ transport. -/
theorem cczTransport_map_inner
    (psi chi : EuclideanSpace Complex (F × F × F)) :
    inner Complex (cczTransport psi) (cczTransport chi) = inner Complex psi chi :=
  cczDiagonalOperator_map_inner psi chi

/-- The concrete transport acts by the source-prescribed phase on each basis ket. -/
theorem cczTransport_apply_basis (x y z : F) :
    cczTransport (EuclideanSpace.basisFun (F × F × F) Complex (x, y, z)) =
      cczAmplitude x y z • EuclideanSpace.basisFun (F × F × F) Complex (x, y, z) := by
  classical
  ext label
  by_cases hlabel : label = (x, y, z)
  · subst label
    simp [cczTransport_apply, EuclideanSpace.basisFun_apply]
  · simp [cczTransport_apply, EuclideanSpace.basisFun_apply, hlabel]

/-- The three field labels selected from one tagged coordinate of the register. -/
def taggedCczAmplitude [Fintype ι] [DecidableEq ι]
    (site : ι) (label : TaggedThreeCopyRegisterLabel F ι) : Complex :=
  cczAmplitude (label (ThreeCopyTag.first, site))
    (label (ThreeCopyTag.second, site))
    (label (ThreeCopyTag.third, site))

omit [Fintype F] in
/-- The selected tagged phase is exactly the already-defined local CCZ phase. -/
theorem taggedCczAmplitude_eq_local [Fintype ι] [DecidableEq ι]
    (site : ι) (label : TaggedThreeCopyRegisterLabel F ι) :
    taggedCczAmplitude site label =
      cczAmplitude (label (ThreeCopyTag.first, site))
        (label (ThreeCopyTag.second, site))
        (label (ThreeCopyTag.third, site)) :=
  rfl

omit [Fintype F] in
/-- The selected tagged phase is a sign. -/
theorem taggedCczAmplitude_square [Fintype ι] [DecidableEq ι]
    (site : ι) (label : TaggedThreeCopyRegisterLabel F ι) :
    taggedCczAmplitude site label * taggedCczAmplitude site label = 1 :=
  cczAmplitude_square _ _ _

omit [Fintype F] in
/-- The selected tagged phase has unit complex norm. -/
theorem taggedCczAmplitude_mul_conj [Fintype ι] [DecidableEq ι]
    (site : ι) (label : TaggedThreeCopyRegisterLabel F ι) :
    taggedCczAmplitude site label * starRingEnd Complex (taggedCczAmplitude site label) = 1 := by
  exact cczAmplitude_mul_conj _ _ _

/-- Pointwise multiplication by the CCZ phase at one tagged coordinate. -/
def taggedCczDiagonalOperator [Fintype ι] [DecidableEq ι] (site : ι) :
    Operator (TaggedThreeCopyRegister F ι) where
  toFun psi := WithLp.toLp 2 fun label =>
    taggedCczAmplitude site label * psi label
  map_add' := by
    intro psi chi
    ext label
    change taggedCczAmplitude site label * (psi label + chi label) =
      taggedCczAmplitude site label * psi label + taggedCczAmplitude site label * chi label
    ring
  map_smul' := by
    intro scalar psi
    ext label
    change taggedCczAmplitude site label * (scalar * psi label) =
      scalar * (taggedCczAmplitude site label * psi label)
    ring

@[simp]
theorem taggedCczDiagonalOperator_apply [Fintype ι] [DecidableEq ι]
    (site : ι) (psi : TaggedThreeCopyRegister F ι)
    (label : TaggedThreeCopyRegisterLabel F ι) :
    taggedCczDiagonalOperator site psi label = taggedCczAmplitude site label * psi label :=
  rfl

/-- Applying the selected tagged diagonal operation twice is the identity. -/
theorem taggedCczDiagonalOperator_square [Fintype ι] [DecidableEq ι] (site : ι) :
    taggedCczDiagonalOperator (F := F) site * taggedCczDiagonalOperator site =
      (1 : Operator (TaggedThreeCopyRegister F ι)) := by
  ext psi label
  simp only [Module.End.mul_apply]
  change taggedCczAmplitude site label * (taggedCczAmplitude site label * psi label) = psi label
  rw [← mul_assoc, taggedCczAmplitude_square]
  simp

/-- The selected tagged diagonal operation preserves the Hilbert inner product. -/
theorem taggedCczDiagonalOperator_map_inner [Fintype ι] [DecidableEq ι]
    (site : ι) (psi chi : TaggedThreeCopyRegister F ι) :
    inner Complex (taggedCczDiagonalOperator site psi) (taggedCczDiagonalOperator site chi) =
      inner Complex psi chi := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro label _
  simp only [taggedCczDiagonalOperator_apply, RCLike.inner_apply, map_mul]
  calc
    (taggedCczAmplitude site label * chi label) *
        (starRingEnd Complex (taggedCczAmplitude site label) * starRingEnd Complex (psi label)) =
        (taggedCczAmplitude site label * starRingEnd Complex (taggedCczAmplitude site label)) *
          (chi label * starRingEnd Complex (psi label)) := by ring
    _ = chi label * starRingEnd Complex (psi label) := by
      rw [taggedCczAmplitude_mul_conj]
      ring

/-- The tagged diagonal phase with the same map supplied as its explicit inverse. -/
noncomputable def taggedCczLinearEquiv [Fintype ι] [DecidableEq ι] (site : ι) :
    TaggedThreeCopyRegister F ι ≃ₗ[Complex] TaggedThreeCopyRegister F ι where
  toFun psi := taggedCczDiagonalOperator site psi
  invFun psi := taggedCczDiagonalOperator site psi
  left_inv := by
    intro psi
    have h := LinearMap.congr_fun (taggedCczDiagonalOperator_square (F := F) site) psi
    simpa only [Module.End.mul_apply, Module.End.one_apply] using h
  right_inv := by
    intro psi
    have h := LinearMap.congr_fun (taggedCczDiagonalOperator_square (F := F) site) psi
    simpa only [Module.End.mul_apply, Module.End.one_apply] using h
  map_add' := (taggedCczDiagonalOperator site).map_add
  map_smul' := (taggedCczDiagonalOperator site).map_smul

@[simp]
theorem taggedCczLinearEquiv_apply [Fintype ι] [DecidableEq ι]
    (site : ι) (psi : TaggedThreeCopyRegister F ι)
    (label : TaggedThreeCopyRegisterLabel F ι) :
    taggedCczLinearEquiv site psi label = taggedCczAmplitude site label * psi label :=
  rfl

@[simp]
theorem taggedCczLinearEquiv_symm_apply [Fintype ι] [DecidableEq ι]
    (site : ι) (psi : TaggedThreeCopyRegister F ι)
    (label : TaggedThreeCopyRegisterLabel F ι) :
    (taggedCczLinearEquiv (F := F) site).symm psi label =
      taggedCczAmplitude site label * psi label :=
  rfl

/-- The concrete CCZ transport lifted to one tagged three-copy coordinate. -/
noncomputable def taggedCczTransport [Fintype ι] [DecidableEq ι] (site : ι) :
    UnitaryTransport (TaggedThreeCopyRegister F ι) (TaggedThreeCopyRegister F ι) where
  toLinearEquiv := taggedCczLinearEquiv site
  map_inner := taggedCczDiagonalOperator_map_inner site

@[simp]
theorem taggedCczTransport_apply [Fintype ι] [DecidableEq ι]
    (site : ι) (psi : TaggedThreeCopyRegister F ι)
    (label : TaggedThreeCopyRegisterLabel F ι) :
    taggedCczTransport site psi label = taggedCczAmplitude site label * psi label :=
  rfl

/-- Named inner-product preservation for the tagged single-coordinate transport. -/
theorem taggedCczTransport_map_inner [Fintype ι] [DecidableEq ι]
    (site : ι) (psi chi : TaggedThreeCopyRegister F ι) :
    inner Complex (taggedCczTransport site psi) (taggedCczTransport site chi) =
      inner Complex psi chi :=
  taggedCczDiagonalOperator_map_inner site psi chi

/-- The tagged lift acts by the local CCZ phase on each tagged basis ket. -/
theorem taggedCczTransport_apply_basis [Fintype ι] [DecidableEq ι]
    (site : ι) (label : TaggedThreeCopyRegisterLabel F ι) :
    taggedCczTransport site (EuclideanSpace.basisFun (TaggedThreeCopyRegisterLabel F ι) Complex label) =
      taggedCczAmplitude site label •
        EuclideanSpace.basisFun (TaggedThreeCopyRegisterLabel F ι) Complex label := by
  classical
  ext target
  by_cases htarget : target = label
  · subst target
    simp [taggedCczTransport_apply, EuclideanSpace.basisFun_apply]
  · simp [taggedCczTransport_apply, EuclideanSpace.basisFun_apply, htarget]

end QEC.Distillation
