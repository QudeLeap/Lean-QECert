import QEC.Semantics.Instruments.Selection.Selection
import QEC.Semantics.Core.Qubit
/-!
# Tensor-power bases for finite instruments

This module constructs the computational data needed to identify the literal
right-nested tensor-power carrier with a finite qubit register.  It provides
only basis-preserving transports; it does not select, discard, or assign any
probabilistic interpretation to tensor-power factors.
-/

universe u v

namespace QEC
namespace Semantics

noncomputable section

namespace FiniteInstrument

open scoped TensorProduct

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable {β : Type v} [Fintype β]

/-- The recursively constructed orthonormal basis of a literal tensor-power
carrier, indexed by the corresponding right-nested history type. -/
noncomputable def tensorPowerBasis (b : OrthonormalBasis β Complex H) : (attempts : Nat) →
    OrthonormalBasis (tensorPowerHistory β attempts) Complex (tensorPowerCarrier H attempts)
  | 0 =>
      (EuclideanSpace.basisFun (ULift.{u} (Fin 1)) Complex).reindex
        (Equiv.ofUnique (ULift.{u} (Fin 1)) PUnit)
  | attempts + 1 => b.tensorProduct (tensorPowerBasis b attempts)

/-- The zero-level tensor-power basis uses the unique basis index of the
literal one-dimensional tensor unit. -/
@[simp] theorem tensorPowerBasis_zero_apply (b : OrthonormalBasis β Complex H)
    (index : PUnit) :
    tensorPowerBasis b 0 index =
      EuclideanSpace.basisFun (ULift.{u} (Fin 1)) Complex
        ((Equiv.ofUnique (ULift.{u} (Fin 1)) PUnit).symm index) := by
  change ((EuclideanSpace.basisFun (ULift.{u} (Fin 1)) Complex).reindex
    (Equiv.ofUnique (ULift.{u} (Fin 1)) PUnit)) index = _
  rw [OrthonormalBasis.reindex_apply]

/-- A successor tensor-power basis vector is the literal tensor product of
the new factor's basis vector and the recursive tail basis vector. -/
@[simp] theorem tensorPowerBasis_succ_apply (b : OrthonormalBasis β Complex H)
    (attempts : Nat) (head : β) (tail : tensorPowerHistory β attempts) :
    tensorPowerBasis b (attempts + 1) (head, tail) =
      b head ⊗ₜ[Complex] tensorPowerBasis b attempts tail := by
  change (b.tensorProduct (tensorPowerBasis b attempts)) (head, tail) =
    b head ⊗ₜ[Complex] tensorPowerBasis b attempts tail
  exact OrthonormalBasis.tensorProduct_apply b (tensorPowerBasis b attempts) head tail

/-- The exact history-label curry equivalence used to flatten a qubit tensor
power into a register indexed by trial and local coordinate. -/
def tensorPowerQubitBitstringEquiv (ι : Type u) [Fintype ι] (attempts : Nat) :
    tensorPowerHistory (Qubit.Bitstring ι) attempts ≃
      Qubit.Bitstring (Fin attempts × ι) :=
  (tensorPowerHistoryEquiv (Qubit.Bitstring ι) attempts).trans
    (Equiv.curry (Fin attempts) ι (Fin 2)).symm

/-- The flattened label evaluates at a trial/local-coordinate pair by reading
the corresponding value from the recursive history. -/
@[simp] theorem tensorPowerQubitBitstringEquiv_apply
    (ι : Type u) [Fintype ι] (attempts : Nat)
    (history : tensorPowerHistory (Qubit.Bitstring ι) attempts)
    (trial : Fin attempts) (coordinate : ι) :
    tensorPowerQubitBitstringEquiv ι attempts history (trial, coordinate) =
      tensorPowerHistoryAt (Qubit.Bitstring ι) attempts history trial coordinate :=
  rfl

/-- The basis-preserving unitary transport from the actual right-nested qubit
tensor-power carrier to the register with coordinates `Fin attempts × ι`. -/
noncomputable def tensorPowerQubitRegisterTransport (ι : Type u) [Fintype ι] [DecidableEq ι]
    (attempts : Nat) :
    UnitaryTransport (tensorPowerCarrier (Qubit.QubitRegister ι) attempts)
      (Qubit.QubitRegister (Fin attempts × ι)) := by
  let sourceBasis :=
    tensorPowerBasis (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) attempts
  let targetBasis :=
    EuclideanSpace.basisFun (Qubit.Bitstring (Fin attempts × ι)) Complex
  let U := sourceBasis.equiv targetBasis (tensorPowerQubitBitstringEquiv ι attempts)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

/-- The flattened transport sends every recursive computational basis vector
to the computational basis vector labelled by the history/coordinate curry
equivalence. -/
@[simp] theorem tensorPowerQubitRegisterTransport_apply_basis
    (ι : Type u) [Fintype ι] [DecidableEq ι] (attempts : Nat)
    (history : tensorPowerHistory (Qubit.Bitstring ι) attempts) :
    tensorPowerQubitRegisterTransport ι attempts
      (tensorPowerBasis (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex)
        attempts history) =
      EuclideanSpace.basisFun (Qubit.Bitstring (Fin attempts × ι)) Complex
        (tensorPowerQubitBitstringEquiv ι attempts history) := by
  dsimp [tensorPowerQubitRegisterTransport]
  rw [OrthonormalBasis.equiv_apply_basis]

end FiniteInstrument

end
end Semantics
end QEC
