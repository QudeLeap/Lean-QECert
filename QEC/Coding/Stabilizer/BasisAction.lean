import QEC.Coding.Stabilizer.PauliSemantics

/-!
# Computational-basis action of binary CSS checks

The binary-word and bitstring labels are related explicitly before deriving
the actual X-translation and Z-pairing phases of the existing Pauli operators.
-/

noncomputable section

namespace QEC.Coding.PauliSymplectic

open Semantics

universe u
variable {J : Type u} [Fintype J] [DecidableEq J]

omit [DecidableEq J] in
/-- The concrete bitstring-to-word cast preserves the binary coordinate values. -/
theorem bitstringWordEquiv_eq_self (x : Word (ZMod 2) J) : bitstringWordEquiv J x = x := by
  funext j
  exact bitstringWordEquiv_apply x j

/-- Flipping the support of a binary word is its literal additive translation. -/
theorem flipSupport_binarySupport_eq_add (x y : Word (ZMod 2) J) :
    Qubit.flipSupport (binarySupport x) y = y + x := by
  have h := bitstringWordEquiv_flipSupport x y
  erw [bitstringWordEquiv_eq_self, bitstringWordEquiv_eq_self] at h
  exact h

/-- The actual X-check sends a computational word to its translate. -/
theorem cssXCheck_apply_basis (x y : Word (ZMod 2) J) :
    toQubitOperator (cssXCheck x) (EuclideanSpace.basisFun (Word (ZMod 2) J) Complex y) =
      EuclideanSpace.basisFun (Word (ZMod 2) J) Complex (y + x) := by
  classical
  ext z
  let w : Word (ZMod 2) J := z
  have hxx : x + x = 0 := by
    ext j
    change x j + x j = (0 : ZMod 2)
    generalize x j = b
    fin_cases b <;> rfl
  have hiff : w + x = y ↔ w = y + x := by
    constructor
    · intro h
      rw [← h, add_assoc, hxx, add_zero]
    · intro h
      rw [h, add_assoc, hxx, add_zero]
  erw [toQubitOperator_apply]
  simp [cssXCheck, xSupport, zSupport,
    Qubit.zSupportPhase, flipSupport_binarySupport_eq_add,
    EuclideanSpace.basisFun_apply, binaryPhaseScalar_zero, one_mul,
    Pi.single_apply]
  change Pi.single (M := fun _ : Word (ZMod 2) J => Complex)
      y (1 : Complex) (Qubit.flipSupport (binarySupport x) w) =
    Pi.single (M := fun _ : Word (ZMod 2) J => Complex) (y + x) (1 : Complex) w
  erw [flipSupport_binarySupport_eq_add]
  simp only [Pi.single_apply, hiff]

/-- The actual Z-check multiplies a computational word by its pairing phase. -/
theorem cssZCheck_apply_basis (z y : Word (ZMod 2) J) :
    toQubitOperator (cssZCheck z) (EuclideanSpace.basisFun (Word (ZMod 2) J) Complex y) =
      binaryPhaseScalar (wordPairing z y) •
        EuclideanSpace.basisFun (Word (ZMod 2) J) Complex y := by
  classical
  have hphase := zSupportPhase_eq_binaryPhaseScalar_wordPairing z y
  rw [bitstringWordEquiv_eq_self] at hphase
  ext bits
  let w : Word (ZMod 2) J := bits
  erw [toQubitOperator_apply]
  simp only [cssZCheck, xSupport, zSupport, binaryPhaseScalar_zero, one_mul,
    EuclideanSpace.basisFun_apply, PiLp.smul_apply]
  change Qubit.zSupportPhase (binarySupport z) (Qubit.flipSupport (binarySupport 0) w) *
    Pi.single (M := fun _ : Word (ZMod 2) J => Complex)
      y (1 : Complex) (Qubit.flipSupport (binarySupport 0) w) =
    (binaryPhaseScalar (wordPairing z y) •
      Pi.single (M := fun _ : Word (ZMod 2) J => Complex) y (1 : Complex)) w
  erw [show binarySupport (0 : Word (ZMod 2) J) = ∅ by simp [binarySupport]]
  erw [Qubit.flipSupport_empty]
  by_cases hw : y = w
  · erw [← hw]
    simp [cssZCheck, xSupport, zSupport, EuclideanSpace.basisFun_apply]
    exact hphase
  · simp [toQubitOperator_apply, cssZCheck, xSupport, zSupport,
      EuclideanSpace.basisFun_apply, hw]

end QEC.Coding.PauliSymplectic
