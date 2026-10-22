import QEC.Semantics.Instruments.Selection.SelectedBranchOperator
/-!
# Tensor-power product densities on flattened qubit registers

The recursively tensorized density is transported to the flattened register
whose coordinates are trial/port pairs.  Its computational entries are the
literal products of the local density entries.
-/

universe u v

namespace QEC
namespace Semantics

open Classical
open scoped BigOperators TensorProduct

noncomputable section

namespace FiniteInstrument

/-- The recursive observed-history Born product is the finite product of its
actual trial Born weights. -/
theorem tensorPowerBornProduct_eq_prod
    {κ Ω : Type v} [Fintype κ] [Fintype Ω]
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
    (I : FiniteInstrument κ Ω H K) (rho : DensityOperator H) :
    ∀ (attempts : Nat) (history : tensorPowerHistory Ω attempts),
      tensorPowerBornProduct I rho attempts history =
        ∏ trial : Fin attempts,
          I.bornWeight (tensorPowerHistoryAt Ω attempts history trial) rho := by
  intro attempts
  induction attempts with
  | zero =>
      intro history
      cases history
      simp [tensorPowerBornProduct]
  | succ attempts ih =>
      rintro ⟨head, tail⟩
      rw [Fin.prod_univ_succ]
      simp only [tensorPowerBornProduct, tensorPowerHistoryAt, Fin.cases_zero,
        Fin.cases_succ]
      rw [ih tail]

/-- Computational entries of a recursively tensorized density factor over
the actual trial indices. -/
theorem tensorPowerProductInput_matrixEntry_eq_prod
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
    {β : Type v} [Fintype β]
    (basis : OrthonormalBasis β Complex H)
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0)) :
    ∀ (attempts : Nat) (left right : tensorPowerHistory β attempts),
      inner Complex (tensorPowerBasis basis attempts left)
          ((tensorPowerProductInput rho rhoUnit attempts).toOperator
            (tensorPowerBasis basis attempts right)) =
        ∏ trial : Fin attempts,
          inner Complex
            (basis (tensorPowerHistoryAt β attempts left trial))
            (rho.toOperator
              (basis (tensorPowerHistoryAt β attempts right trial))) := by
  intro attempts
  induction attempts with
  | zero =>
      intro left right
      cases left
      cases right
      simpa [tensorPowerProductInput] using
        (tensorPowerUnitDensity_matrixEntry_eq_one basis rhoUnit)
  | succ attempts ih =>
      rintro ⟨leftHead, leftTail⟩ ⟨rightHead, rightTail⟩
      rw [Fin.prod_univ_succ]
      simp only [tensorPowerProductInput, DensityOperator.tensorDensity_toOperator,
        tensorPowerBasis_succ_apply, tensorPowerHistoryAt, Fin.cases_zero,
        Fin.cases_succ]
      change inner Complex
        ((basis.tensorProduct (tensorPowerBasis basis attempts)) (leftHead, leftTail))
        ((TensorProduct.map rho.toOperator (tensorPowerProductInput rho rhoUnit attempts).toOperator)
          ((basis.tensorProduct (tensorPowerBasis basis attempts)) (rightHead, rightTail))) =
        inner Complex (basis leftHead) (rho.toOperator (basis rightHead)) *
          ∏ i, inner Complex (basis (tensorPowerHistoryAt β attempts leftTail i))
            (rho.toOperator (basis (tensorPowerHistoryAt β attempts rightTail i)))
      rw [OrthonormalBasis.tensorProduct_apply, OrthonormalBasis.tensorProduct_apply]
      rw [TensorProduct.map_tmul, TensorProduct.inner_tmul,
        ih leftTail rightTail]

/-- The recursively tensorized qubit density, transported to the register
indexed by actual trial/port coordinates. -/
noncomputable def tensorPowerRegisterProductDensity
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (rho : DensityOperator (Qubit.QubitRegister ι))
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (Qubit.QubitRegister ι) 0))
    (attempts : Nat) :
    DensityOperator (Qubit.QubitRegister (Fin attempts × ι)) :=
  (tensorPowerQubitRegisterTransport ι attempts).conjDensity
    (tensorPowerProductInput rho rhoUnit attempts)

/-- Computational entries of the flattened product density are the products
of the corresponding local density entries. -/
theorem tensorPowerRegisterProductDensity_matrixEntry
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (rho : DensityOperator (Qubit.QubitRegister ι))
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (Qubit.QubitRegister ι) 0))
    (attempts : Nat)
    (left right : Qubit.Bitstring (Fin attempts × ι)) :
    inner Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin attempts × ι)) Complex left)
        ((tensorPowerRegisterProductDensity ι rho rhoUnit attempts).toOperator
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin attempts × ι)) Complex
            right)) =
      ∏ trial : Fin attempts,
        inner Complex
          (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
            (fun port => left (trial, port)))
          (rho.toOperator
            (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
              (fun port => right (trial, port)))) := by
  let leftHistory :=
    (tensorPowerQubitBitstringEquiv ι attempts).symm left
  let rightHistory :=
    (tensorPowerQubitBitstringEquiv ι attempts).symm right
  have hleftHistoryAt (trial : Fin attempts) :
      tensorPowerHistoryAt (Qubit.Bitstring ι) attempts leftHistory trial =
        fun port => left (trial, port) := by
    funext port
    exact congrFun
      ((tensorPowerQubitBitstringEquiv ι attempts).apply_symm_apply left)
      (trial, port)
  have hrightHistoryAt (trial : Fin attempts) :
      tensorPowerHistoryAt (Qubit.Bitstring ι) attempts rightHistory trial =
        fun port => right (trial, port) := by
    funext port
    exact congrFun
      ((tensorPowerQubitBitstringEquiv ι attempts).apply_symm_apply right)
      (trial, port)
  calc
    inner Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin attempts × ι)) Complex left)
        ((tensorPowerRegisterProductDensity ι rho rhoUnit attempts).toOperator
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin attempts × ι)) Complex
            right)) =
      inner Complex
        (tensorPowerQubitRegisterTransport ι attempts
          (tensorPowerBasis
            (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) attempts
            leftHistory))
        ((tensorPowerQubitRegisterTransport ι attempts).conjOperator
          (tensorPowerProductInput rho rhoUnit attempts).toOperator
          (tensorPowerQubitRegisterTransport ι attempts
            (tensorPowerBasis
              (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) attempts
              rightHistory))) := by
        simp only [tensorPowerRegisterProductDensity,
          UnitaryTransport.conjDensity_toOperator,
          tensorPowerQubitRegisterTransport_apply_basis]
        simp [leftHistory, rightHistory]
    _ = inner Complex
        (tensorPowerBasis
          (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) attempts
          leftHistory)
        ((tensorPowerProductInput rho rhoUnit attempts).toOperator
          (tensorPowerBasis
            (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) attempts
            rightHistory)) := by
      rw [UnitaryTransport.conjOperator_apply]
      simp only [LinearEquiv.symm_apply_apply]
      exact (tensorPowerQubitRegisterTransport ι attempts).map_inner _ _
    _ = _ := by
      rw [tensorPowerProductInput_matrixEntry_eq_prod]
      apply Finset.prod_congr rfl
      intro trial _
      rw [hleftHistoryAt trial, hrightHistoryAt trial]

end FiniteInstrument

end
end Semantics
end QEC
