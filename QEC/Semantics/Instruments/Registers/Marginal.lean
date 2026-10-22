import QEC.Semantics.Instruments.Tensor.MarginalChannel
/-!
# Coordinate marginals of flattened tensor-power registers

Selecting one complete trial from a flattened tensor-power register is a
physical CPTP operation.  We first undo the basis-preserving flattening and
then recursively trace out every tensor factor except the requested one.  The
result is exactly the true recursive tensor marginal, for an arbitrary input
density; no product-state premise is used.
-/

universe u

namespace QEC
namespace Semantics

open scoped TensorProduct

noncomputable section

namespace FiniteInstrument

private theorem partialTraceRightRaw_tensorMap
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (A : Operator H) (B : Operator K) :
    partialTraceRightRaw H K (TensorProduct.map A B) =
      (LinearMap.trace Complex K B) • A := by
  apply operator_ext_of_trace_comp_right_eq
  intro X
  let basis : OrthonormalBasis
      (ULift.{u} (Fin (Module.finrank Complex K))) Complex K :=
    (stdOrthonormalBasis Complex K).reindex Equiv.ulift.symm
  calc
    LinearMap.trace Complex H
          (X.comp (partialTraceRightRaw H K (TensorProduct.map A B))) =
        LinearMap.trace Complex H
          ((partialTraceRightRaw H K (TensorProduct.map A B)).comp X) :=
      (LinearMap.trace_comp_comm' X
        (partialTraceRightRaw H K (TensorProduct.map A B))).symm
    _ = LinearMap.trace Complex (CompositeSystem H K)
          ((TensorProduct.map A B).comp
            (TensorProduct.map X (LinearMap.id : K →ₗ[Complex] K))) :=
      FiniteMatrixEntropy.partialTraceRightRaw_trace_pairing
        basis (TensorProduct.map A B) X
    _ = LinearMap.trace Complex H
          (((LinearMap.trace Complex K B) • A).comp X) := by
      rw [← TensorProduct.map_comp, LinearMap.trace_tensorProduct']
      simp [LinearMap.smul_comp]
      ring
    _ = LinearMap.trace Complex H
          (X.comp ((LinearMap.trace Complex K B) • A)) :=
      LinearMap.trace_comp_comm' X ((LinearMap.trace Complex K B) • A)

private theorem partialTraceLeftRaw_tensorMap
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (A : Operator H) (B : Operator K) :
    FiniteMatrixEntropy.partialTraceLeftRaw H K (TensorProduct.map A B) =
      (LinearMap.trace Complex H A) • B := by
  apply operator_ext_of_trace_comp_right_eq
  intro Y
  calc
    LinearMap.trace Complex K
          (Y.comp
            (FiniteMatrixEntropy.partialTraceLeftRaw H K
              (TensorProduct.map A B))) =
        LinearMap.trace Complex K
          ((FiniteMatrixEntropy.partialTraceLeftRaw H K
            (TensorProduct.map A B)).comp Y) :=
      (LinearMap.trace_comp_comm' Y
        (FiniteMatrixEntropy.partialTraceLeftRaw H K
          (TensorProduct.map A B))).symm
    _ = LinearMap.trace Complex (CompositeSystem H K)
          ((TensorProduct.map A B).comp
            (TensorProduct.map (LinearMap.id : H →ₗ[Complex] H) Y)) :=
      FiniteMatrixEntropy.partialTraceLeftRaw_trace_pairing
        (TensorProduct.map A B) Y
    _ = LinearMap.trace Complex K
          (((LinearMap.trace Complex H A) • B).comp Y) := by
      rw [← TensorProduct.map_comp, LinearMap.trace_tensorProduct']
      simp [LinearMap.smul_comp]
    _ = LinearMap.trace Complex K
          (Y.comp ((LinearMap.trace Complex H A) • B)) :=
      LinearMap.trace_comp_comm' Y ((LinearMap.trace Complex H A) • B)

/-- Tracing the right factor of a product density returns its left factor. -/
@[simp]
theorem partialTraceRightRaw_mapDensity_tensorDensity
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K) :
    partialTraceRightRaw_mapDensity H K
        (DensityOperator.tensorDensity rho sigma) = rho := by
  apply DensityOperator.ext_toOperator
  simp only [partialTraceRightRaw_mapDensity_toOperator,
    DensityOperator.tensorDensity_toOperator]
  rw [partialTraceRightRaw_tensorMap, sigma.trace_one]
  simp

/-- Tracing the left factor of a product density returns its right factor. -/
@[simp]
theorem leftMarginal_tensorDensity
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K) :
    DensityOperator.leftMarginal
        (DensityOperator.tensorDensity rho sigma) = sigma := by
  apply DensityOperator.ext_toOperator
  change FiniteMatrixEntropy.partialTraceLeftRaw H K
      (TensorProduct.map rho.toOperator sigma.toOperator) = sigma.toOperator
  rw [partialTraceLeftRaw_tensorMap, rho.trace_one]
  simp

/-- Every coordinate of a recursively constructed product density has the
original one-factor density as its true marginal. -/
@[simp]
theorem tensorPowerInputMarginal_productInput
    {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0)) :
    forall (attempts : Nat) (trial : Fin attempts),
      tensorPowerInputMarginal attempts
          (tensorPowerProductInput rho rhoUnit attempts) trial = rho := by
  intro attempts
  induction attempts with
  | zero =>
      intro trial
      exact Fin.elim0 trial
  | succ attempts ih =>
      intro trial
      refine Fin.cases ?_ ?_ trial
      · exact partialTraceRightRaw_mapDensity_tensorDensity rho
          (tensorPowerProductInput rho rhoUnit attempts)
      · intro tailTrial
        change tensorPowerInputMarginal attempts
            (DensityOperator.leftMarginal
              (DensityOperator.tensorDensity rho
                (tensorPowerProductInput rho rhoUnit attempts))) tailTrial = rho
        rw [leftMarginal_tensorDensity]
        exact ih tailTrial

/-- The actual CPTP operation retaining one requested factor of a recursive
tensor-power carrier. -/
noncomputable def tensorPowerCoordinateOperator
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] :
    (attempts : Nat) -> Fin attempts ->
      QuantumChannel (tensorPowerCarrier H attempts) H
  | 0, trial => Fin.elim0 trial
  | attempts + 1, trial =>
      Fin.cases
        (partialTraceRightRaw_cptp H (tensorPowerCarrier H attempts))
        (fun tailTrial =>
          QuantumChannel.comp
            (tensorPowerCoordinateOperator attempts tailTrial)
            (QuantumChannel.comp
              (partialTraceRightRaw_cptp (tensorPowerCarrier H attempts) H)
              (QuantumChannel.unitaryConj
                (DensityOperator.tensorSwap H
                  (tensorPowerCarrier H attempts)))))
        trial

private theorem tensorPowerBasis_inner_eq_prod
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
    {beta : Type u} [Fintype beta]
    (basis : OrthonormalBasis beta Complex H) :
    forall (attempts : Nat)
      (left right : tensorPowerHistory beta attempts),
      inner Complex (tensorPowerBasis basis attempts right)
          (tensorPowerBasis basis attempts left) =
        ∏ coordinate : Fin attempts,
          inner Complex
            (basis (tensorPowerHistoryAt beta attempts right coordinate))
            (basis (tensorPowerHistoryAt beta attempts left coordinate)) := by
  intro attempts
  induction attempts with
  | zero =>
      intro left right
      cases left
      cases right
      erw [(tensorPowerBasis basis 0).inner_eq_one]
      simp
  | succ attempts ih =>
      rintro ⟨leftHead, leftTail⟩ ⟨rightHead, rightTail⟩
      rw [tensorPowerBasis_succ_apply, tensorPowerBasis_succ_apply,
        TensorProduct.inner_tmul, Fin.prod_univ_succ]
      simp only [tensorPowerHistoryAt, Fin.cases_zero, Fin.cases_succ]
      rw [ih leftTail rightTail]

/-- On a computational matrix unit, selecting one recursive tensor coordinate
retains that coordinate's matrix unit and contracts every discarded
coordinate by its exact computational-basis inner product. -/
theorem tensorPowerCoordinateOperator_rankOne_basis
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
    {beta : Type u} [Fintype beta]
    (basis : OrthonormalBasis beta Complex H) :
    forall (attempts : Nat) (trial : Fin attempts)
      (left right : tensorPowerHistory beta attempts),
      tensorPowerCoordinateOperator attempts trial
          (InnerProductSpace.rankOne Complex
            (tensorPowerBasis basis attempts left)
            (tensorPowerBasis basis attempts right)).toLinearMap =
        (∏ coordinate : Fin attempts,
            if coordinate = trial then 1
            else inner Complex
              (basis (tensorPowerHistoryAt beta attempts right coordinate))
              (basis (tensorPowerHistoryAt beta attempts left coordinate))) •
          (InnerProductSpace.rankOne Complex
            (basis (tensorPowerHistoryAt beta attempts left trial))
            (basis (tensorPowerHistoryAt beta attempts right trial))).toLinearMap := by
  intro attempts
  induction attempts with
  | zero =>
      intro trial
      exact Fin.elim0 trial
  | succ attempts ih =>
      intro trial
      refine Fin.cases ?_ ?_ trial
      · rintro left right
        rcases left with ⟨leftHead, leftTail⟩
        rcases right with ⟨rightHead, rightTail⟩
        simp only [tensorPowerCoordinateOperator, Fin.cases_zero,
          tensorPowerBasis_succ_apply, partialTraceRightRaw_cptp_toLinearMap]
        erw [tensorPowerBasis_succ_apply, tensorPowerBasis_succ_apply]
        change partialTraceRightRaw H (tensorPowerCarrier H attempts)
            (InnerProductSpace.rankOne Complex
              (basis leftHead ⊗ₜ[Complex] tensorPowerBasis basis attempts leftTail)
              (basis rightHead ⊗ₜ[Complex] tensorPowerBasis basis attempts rightTail)
            ).toLinearMap = _
        rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
        simp only [Fin.prod_univ_succ, tensorPowerHistoryAt, Fin.cases_zero,
          Fin.cases_succ, if_pos, one_mul, Fin.succ_ne_zero, if_false]
        rw [tensorPowerBasis_inner_eq_prod basis attempts leftTail rightTail]
      · intro tailTrial left right
        rcases left with ⟨leftHead, leftTail⟩
        rcases right with ⟨rightHead, rightTail⟩
        simp only [tensorPowerCoordinateOperator, Fin.cases_succ,
          QuantumChannel.comp_apply, QuantumChannel.unitaryConj_apply,
          tensorPowerBasis_succ_apply, partialTraceRightRaw_cptp_toLinearMap]
        erw [tensorPowerBasis_succ_apply, tensorPowerBasis_succ_apply]
        change tensorPowerCoordinateOperator attempts tailTrial
            (partialTraceRightRaw (tensorPowerCarrier H attempts) H
              ((DensityOperator.tensorSwap H (tensorPowerCarrier H attempts)).conjOperator
                (InnerProductSpace.rankOne Complex
                  (basis leftHead ⊗ₜ[Complex] tensorPowerBasis basis attempts leftTail)
                  (basis rightHead ⊗ₜ[Complex] tensorPowerBasis basis attempts rightTail)
                ).toLinearMap)) = _
        rw [QuditSubsystem.conjOperator_rankOne,
          DensityOperator.tensorSwap_apply_tmul,
          DensityOperator.tensorSwap_apply_tmul,
          QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
        rw [map_smul]
        rw [ih tailTrial leftTail rightTail]
        rw [Fin.prod_univ_succ]
        simp only [tensorPowerHistoryAt, Fin.cases_zero, Fin.cases_succ]
        have hzero : (0 : Fin (attempts + 1)) ≠ tailTrial.succ :=
          (Fin.succ_ne_zero tailTrial).symm
        simp only [hzero, if_false, Fin.succ_inj]
        rw [smul_smul]

/-- The recursive coordinate operation returns the definitionally selected
true marginal of every density operator. -/
theorem tensorPowerCoordinateOperator_mapDensity
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] :
    forall (attempts : Nat)
      (rho : DensityOperator (tensorPowerCarrier H attempts))
      (trial : Fin attempts),
      (tensorPowerCoordinateOperator attempts trial).mapDensity rho =
        tensorPowerInputMarginal attempts rho trial := by
  intro attempts
  induction attempts with
  | zero =>
      intro rho trial
      exact Fin.elim0 trial
  | succ attempts ih =>
      intro rho trial
      refine Fin.cases ?_ ?_ trial
      · rfl
      · intro tailTrial
        change
          (tensorPowerCoordinateOperator attempts tailTrial).mapDensity
              (DensityOperator.leftMarginal rho) =
            tensorPowerInputMarginal attempts
              (DensityOperator.leftMarginal rho) tailTrial
        exact ih (DensityOperator.leftMarginal rho) tailTrial

/-- Undoing the standard tensor-power register transport sends a flattened
computational basis vector to the recursive tensor basis vector with the
exact inverse history label. -/
@[simp] theorem tensorPowerQubitRegisterTransport_symm_apply_basis
    (iota : Type u) [Fintype iota] [DecidableEq iota]
    (attempts : Nat) (bits : Qubit.Bitstring (Fin attempts × iota)) :
    (tensorPowerQubitRegisterTransport iota attempts).symm
        (EuclideanSpace.basisFun
          (Qubit.Bitstring (Fin attempts × iota)) Complex bits) =
      tensorPowerBasis
        (EuclideanSpace.basisFun (Qubit.Bitstring iota) Complex) attempts
        ((tensorPowerQubitBitstringEquiv iota attempts).symm bits) := by
  apply (tensorPowerQubitRegisterTransport iota attempts).toLinearEquiv.injective
  simp only [UnitaryTransport.symm]
  rw [(tensorPowerQubitRegisterTransport iota attempts).toLinearEquiv.apply_symm_apply]
  rw [tensorPowerQubitRegisterTransport_apply_basis]
  simp only [Equiv.apply_symm_apply]

/-- Reading a coordinate of an inverse-flattened history returns the literal
bit stored at that flattened trial/site coordinate. -/
@[simp] theorem tensorPowerQubitBitstringEquiv_symm_at
    (iota : Type u) [Fintype iota] (attempts : Nat)
    (bits : Qubit.Bitstring (Fin attempts × iota))
    (trial : Fin attempts) (site : iota) :
    tensorPowerHistoryAt (Qubit.Bitstring iota) attempts
        ((tensorPowerQubitBitstringEquiv iota attempts).symm bits) trial site =
      bits (trial, site) := by
  exact congrFun
    ((tensorPowerQubitBitstringEquiv iota attempts).apply_symm_apply bits)
    (trial, site)

/-- Select one complete trial block from the ordinary flattened tensor-power
register: undo the canonical flattening, then apply its physical coordinate
operation. -/
noncomputable def tensorPowerRegisterTrialChannel
    (iota : Type u) [Fintype iota] [DecidableEq iota]
    (attempts : Nat) (trial : Fin attempts) :
    QuantumChannel
      (Qubit.QubitRegister (Fin attempts × iota))
      (Qubit.QubitRegister iota) :=
  QuantumChannel.comp
    (tensorPowerCoordinateOperator attempts trial)
    (QuantumChannel.unitaryConj
      (tensorPowerQubitRegisterTransport iota attempts).symm)

/-- On a flattened computational matrix unit, selecting one complete trial
retains exactly that trial's register matrix unit and contracts all other
trial blocks by their literal computational-basis inner products. -/
theorem tensorPowerRegisterTrialChannel_rankOne_basis
    (iota : Type u) [Fintype iota] [DecidableEq iota]
    (attempts : Nat) (trial : Fin attempts)
    (left right : Qubit.Bitstring (Fin attempts × iota)) :
    tensorPowerRegisterTrialChannel iota attempts trial
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun
            (Qubit.Bitstring (Fin attempts × iota)) Complex left)
          (EuclideanSpace.basisFun
            (Qubit.Bitstring (Fin attempts × iota)) Complex right)).toLinearMap =
      (∏ coordinate : Fin attempts,
          if coordinate = trial then 1
          else inner Complex
            (EuclideanSpace.basisFun (Qubit.Bitstring iota) Complex
              (fun site => right (coordinate, site)))
            (EuclideanSpace.basisFun (Qubit.Bitstring iota) Complex
              (fun site => left (coordinate, site)))) •
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Qubit.Bitstring iota) Complex
            (fun site => left (trial, site)))
          (EuclideanSpace.basisFun (Qubit.Bitstring iota) Complex
            (fun site => right (trial, site)))).toLinearMap := by
  simp only [tensorPowerRegisterTrialChannel, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply]
  rw [QuditSubsystem.conjOperator_rankOne,
    tensorPowerQubitRegisterTransport_symm_apply_basis,
    tensorPowerQubitRegisterTransport_symm_apply_basis,
    tensorPowerCoordinateOperator_rankOne_basis]
  have hleftAt (coordinate : Fin attempts) :
      tensorPowerHistoryAt (Qubit.Bitstring iota) attempts
          ((tensorPowerQubitBitstringEquiv iota attempts).symm left) coordinate =
        fun site => left (coordinate, site) := by
    funext site
    exact tensorPowerQubitBitstringEquiv_symm_at iota attempts left coordinate site
  have hrightAt (coordinate : Fin attempts) :
      tensorPowerHistoryAt (Qubit.Bitstring iota) attempts
          ((tensorPowerQubitBitstringEquiv iota attempts).symm right) coordinate =
        fun site => right (coordinate, site) := by
    funext site
    exact tensorPowerQubitBitstringEquiv_symm_at iota attempts right coordinate site
  simp_rw [hleftAt, hrightAt]

/-- Selecting one flattened trial after the standard tensor-power transport
is exactly the true recursive coordinate marginal. -/
theorem tensorPowerRegisterTrialChannel_mapDensity_transport
    (iota : Type u) [Fintype iota] [DecidableEq iota]
    (attempts : Nat)
    (rho : DensityOperator
      (tensorPowerCarrier (Qubit.QubitRegister iota) attempts))
    (trial : Fin attempts) :
    (tensorPowerRegisterTrialChannel iota attempts trial).mapDensity
        ((tensorPowerQubitRegisterTransport iota attempts).conjDensity rho) =
      tensorPowerInputMarginal attempts rho trial := by
  change
    (tensorPowerCoordinateOperator attempts trial).mapDensity
        ((QuantumChannel.unitaryConj
          (tensorPowerQubitRegisterTransport iota attempts).symm).mapDensity
            ((tensorPowerQubitRegisterTransport iota attempts).conjDensity rho)) =
      tensorPowerInputMarginal attempts rho trial
  have hundo :
      (QuantumChannel.unitaryConj
          (tensorPowerQubitRegisterTransport iota attempts).symm).mapDensity
          ((tensorPowerQubitRegisterTransport iota attempts).conjDensity rho) =
        rho := by
    apply DensityOperator.ext_toOperator
    simp only [QuantumChannel.mapDensity_toOperator,
      QuantumChannel.unitaryConj_apply,
      UnitaryTransport.conjDensity_toOperator]
    exact (tensorPowerQubitRegisterTransport iota attempts).symm_conjOperator_conjOperator
      rho.toOperator
  rw [hundo]
  exact tensorPowerCoordinateOperator_mapDensity attempts rho trial

end FiniteInstrument

end
end Semantics
end QEC
