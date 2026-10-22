import QEC.Semantics.Instruments.NestedTensor.Power
import QEC.Semantics.Instruments.TensorPower.Basis
/-!
# Bases and finite slots for nested instrument tensor powers

This module identifies a literal nested qubit tensor-power carrier with a
finite qubit register.  Its slot type is derived recursively from the carrier
construction, and its unitary sends each nested computational basis vector to
the corresponding flattened bitstring.  It introduces no selection,
probability, or count metadata.
-/

universe u v w

namespace QEC
namespace Semantics

noncomputable section

namespace FiniteInstrument

/-- Apply an equivalence pointwise to a right-nested tensor-power history. -/
def tensorPowerHistoryCongr {alpha : Type v} {beta : Type w}
    (equiv : alpha ≃ beta) : (attempts : Nat) ->
    tensorPowerHistory alpha attempts ≃ tensorPowerHistory beta attempts
  | 0 =>
      { toFun := fun _ => PUnit.unit
        invFun := fun _ => PUnit.unit
        left_inv := by intro value; cases value; rfl
        right_inv := by intro value; cases value; rfl }
  | attempts + 1 =>
      Equiv.prodCongr equiv (tensorPowerHistoryCongr equiv attempts)

/-- Apply an equivalence at every recursively nested tensor-power level. -/
def nestedTensorHistoryCongr {alpha : Type v} {beta : Type w}
    (equiv : alpha ≃ beta) (branches : Nat) : (depth : Nat) ->
    nestedTensorHistory alpha branches depth ≃
      nestedTensorHistory beta branches depth
  | 0 => equiv
  | depth + 1 =>
      nestedTensorHistoryCongr
        (tensorPowerHistoryCongr equiv branches) branches depth

/-- The finite qubit coordinates induced by repeated homogeneous tensor
powers of one finite register. -/
def nestedTensorQubitSlots (iota : Type u) (branches : Nat) : Nat -> Type u
  | 0 => iota
  | depth + 1 => nestedTensorQubitSlots (Fin branches × iota) branches depth

/-- Recursively derived nested qubit slots are finite. -/
instance nestedTensorQubitSlotsFintype (iota : Type u) [Fintype iota]
    (branches depth : Nat) : Fintype (nestedTensorQubitSlots iota branches depth) := by
  induction depth generalizing iota with
  | zero =>
      simpa [nestedTensorQubitSlots] using (inferInstance : Fintype iota)
  | succ depth ih =>
      change Fintype (nestedTensorQubitSlots (Fin branches × iota) branches depth)
      exact ih (iota := Fin branches × iota)

/-- Recursively derived nested qubit slots have decidable equality. -/
noncomputable instance nestedTensorQubitSlotsDecidableEq
    (iota : Type u) [DecidableEq iota] (branches depth : Nat) :
    DecidableEq (nestedTensorQubitSlots iota branches depth) :=
  Classical.decEq _

/-- A depth-`d` nested carrier has exactly the base slot count multiplied by
`branches ^ d`. -/
theorem nestedTensorQubitSlots_card (iota : Type u) [Fintype iota]
    (branches depth : Nat) :
    Fintype.card (nestedTensorQubitSlots iota branches depth) =
      Fintype.card iota * branches ^ depth := by
  induction depth generalizing iota with
  | zero =>
      change Fintype.card iota = Fintype.card iota * branches ^ 0
      simp
  | succ depth ih =>
      calc
        Fintype.card (nestedTensorQubitSlots iota branches (depth + 1)) =
            Fintype.card
              (nestedTensorQubitSlots (Fin branches × iota) branches depth) := rfl
        _ = Fintype.card (Fin branches × iota) * branches ^ depth :=
          ih (iota := Fin branches × iota)
        _ = Fintype.card iota * branches ^ (depth + 1) := by
          simp only [Fintype.card_prod, Fintype.card_fin, pow_succ]
          ac_rfl

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable {beta : Type v} [Fintype beta]

/-- The recursively nested orthonormal basis induced by a base basis. -/
noncomputable def nestedTensorBasis (basis : OrthonormalBasis beta Complex H)
    (branches depth : Nat) :
    OrthonormalBasis (nestedTensorHistory beta branches depth) Complex
      (nestedTensorCarrier H branches depth) := by
  induction depth generalizing beta H with
  | zero => exact basis
  | succ depth ih => exact ih (tensorPowerBasis basis branches)

/-- Flatten nested computational histories to bitstrings on the recursively
derived finite slots. -/
def nestedTensorQubitBitstringEquiv (iota : Type u) [Fintype iota]
    (branches : Nat) : (depth : Nat) ->
    nestedTensorHistory (Qubit.Bitstring iota) branches depth ≃
      Qubit.Bitstring (nestedTensorQubitSlots iota branches depth)
  | 0 => Equiv.refl _
  | depth + 1 =>
      (nestedTensorHistoryCongr
        (tensorPowerQubitBitstringEquiv iota branches) branches depth).trans
      (nestedTensorQubitBitstringEquiv (Fin branches × iota) branches depth)

/-- The basis-preserving unitary from the literal nested tensor carrier to its
derived finite qubit register. -/
noncomputable def nestedTensorQubitRegisterTransport
    (iota : Type u) [Fintype iota] [DecidableEq iota]
    (branches depth : Nat) :
    UnitaryTransport (nestedTensorCarrier (Qubit.QubitRegister iota) branches depth)
      (Qubit.QubitRegister (nestedTensorQubitSlots iota branches depth)) := by
  let sourceBasis := nestedTensorBasis
    (EuclideanSpace.basisFun (Qubit.Bitstring iota) Complex) branches depth
  let targetBasis := EuclideanSpace.basisFun
    (Qubit.Bitstring (nestedTensorQubitSlots iota branches depth)) Complex
  let transport := sourceBasis.equiv targetBasis
    (nestedTensorQubitBitstringEquiv iota branches depth)
  exact
    { toLinearEquiv := transport.toLinearEquiv
      map_inner := transport.inner_map_map }

/-- The nested-register transport maps every computational basis vector to
the bitstring selected by the flattening equivalence. -/
theorem nestedTensorQubitRegisterTransport_apply_basis
    (iota : Type u) [Fintype iota] [DecidableEq iota]
    (branches depth : Nat)
    (history : nestedTensorHistory (Qubit.Bitstring iota) branches depth) :
    nestedTensorQubitRegisterTransport iota branches depth
      (nestedTensorBasis
        (EuclideanSpace.basisFun (Qubit.Bitstring iota) Complex)
        branches depth history) =
      EuclideanSpace.basisFun
        (Qubit.Bitstring (nestedTensorQubitSlots iota branches depth)) Complex
        (nestedTensorQubitBitstringEquiv iota branches depth history) := by
  dsimp [nestedTensorQubitRegisterTransport]
  rw [OrthonormalBasis.equiv_apply_basis]

end FiniteInstrument

end

end Semantics
end QEC
