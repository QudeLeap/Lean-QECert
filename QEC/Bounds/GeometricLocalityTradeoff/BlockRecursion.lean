import QEC.Bounds.BPTDisentangling
import QEC.Bounds.GeometricLocalityTradeoff.Entropy
/-!
# BPT correctable-block recursion

The internal, source-faithful recovery construction for BPT Corollary
`cor:recursion`.  The proof keeps the physical `A B C D` coordinate changes,
the boundary-supported disentangler, and every CPTP recovery map explicit.
-/

noncomputable section

namespace QEC
namespace Bounds
namespace BPTCommutingProjectorModel

open Classical
open Semantics
open Semantics.DensityOperator
open scoped BigOperators ComplexOrder TensorProduct

universe u v

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/-!
## Restored proof closure

The following preparation channel is the local CPTP operation in the source
proof: it inserts a density operator on a left tensor factor and retains the
right factor.  It is deliberately internal to the recursion proof because the
source uses this operation only after the concrete `B C` complement has been
factored as `A tensor D`.
-/

/-- Insert a vector on the left tensor factor. -/
noncomputable def prepareLeftBranch (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (v : H) : K →ₗ[Complex] CompositeSystem H K :=
  TensorProduct.mk Complex H K v

@[simp] theorem prepareLeftBranch_apply (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (v : H) (k : K) :
    prepareLeftBranch H K v k = v ⊗ₜ[Complex] k := rfl

theorem adjoint_prepareLeftBranch_comp (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (v : H) :
    (LinearMap.adjoint (prepareLeftBranch H K v)).comp (prepareLeftBranch H K v) =
      (inner Complex v v) • (1 : Operator K) := by
  apply LinearMap.ext
  intro k
  apply (ext_iff_inner_left Complex).mpr
  intro l
  change inner Complex l (LinearMap.adjoint (prepareLeftBranch H K v)
    (prepareLeftBranch H K v k)) =
      inner Complex l (((inner Complex v v) • (1 : Operator K)) k)
  rw [LinearMap.adjoint_inner_right]
  simp [prepareLeftBranch, TensorProduct.inner_tmul]

/-- A finite rank-one Kraus family which prepares a left-factor ensemble. -/
noncomputable def prepareLeftKraus (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {m : Nat} (vectors : Fin m -> H) :
    FiniteKrausFamily (Fin m) K (CompositeSystem H K) where
  operator i := prepareLeftBranch H K (vectors i)

theorem prepareLeftKraus_complete (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {m : Nat} (vectors : Fin m -> H)
    (htrace : ∑ i, inner Complex (vectors i) (vectors i) = 1) :
    (prepareLeftKraus H K vectors).Complete := by
  rw [FiniteKrausFamily.Complete]
  simp only [prepareLeftKraus, adjoint_prepareLeftBranch_comp]
  apply LinearMap.ext
  intro k
  calc
    (∑ i, (inner Complex (vectors i) (vectors i) • (1 : Operator K))) k =
        (∑ i, inner Complex (vectors i) (vectors i)) • k := by
          simp [Finset.sum_smul]
    _ = k := by rw [htrace]; simp

/-- Every finite-dimensional density operator has a finite rank-one ensemble. -/
theorem density_exists_rankOne_ensemble {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (rho : DensityOperator H) :
    ∃ (m : Nat) (vectors : Fin m -> H),
      rho.toOperator = ∑ i,
        (InnerProductSpace.rankOne Complex (vectors i) (vectors i)).toLinearMap := by
  have hpositive : (LinearMap.toContinuousLinearMap rho.toOperator).IsPositive :=
    (LinearMap.isPositive_toContinuousLinearMap_iff rho.toOperator).2 rho.positive
  rcases (ContinuousLinearMap.isPositive_iff_eq_sum_rankOne).1 hpositive with
    ⟨m, vectors, hvectors⟩
  refine ⟨m, vectors, ?_⟩
  simpa using congrArg ContinuousLinearMap.toLinearMap hvectors

noncomputable def densityEnsembleSize (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (rho : DensityOperator H) : Nat :=
  Classical.choose (density_exists_rankOne_ensemble rho)

noncomputable def densityEnsembleVectors (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (rho : DensityOperator H) : Fin (densityEnsembleSize H rho) -> H :=
  Classical.choose (Classical.choose_spec (density_exists_rankOne_ensemble rho))

theorem densityEnsemble_specification (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (rho : DensityOperator H) :
    rho.toOperator = ∑ i,
      (InnerProductSpace.rankOne Complex (densityEnsembleVectors H rho i)
        (densityEnsembleVectors H rho i)).toLinearMap :=
  Classical.choose_spec (Classical.choose_spec (density_exists_rankOne_ensemble rho))

theorem densityEnsemble_trace_one (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (rho : DensityOperator H) :
    ∑ i, inner Complex (densityEnsembleVectors H rho i)
      (densityEnsembleVectors H rho i) = 1 := by
  have htrace := rho.trace_one
  rw [densityEnsemble_specification] at htrace
  simpa [map_sum, InnerProductSpace.trace_rankOne] using htrace

/-- CPTP insertion of an arbitrary left-factor density operator. -/
noncomputable def prepareLeft (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) : QuantumChannel K (CompositeSystem H K) :=
  (prepareLeftKraus H K (densityEnsembleVectors H rho)).toQuantumChannel
    (prepareLeftKraus_complete H K (densityEnsembleVectors H rho)
      (densityEnsemble_trace_one H rho))

theorem prepareLeft_apply_rankOne (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (k l : K) :
    prepareLeft H K rho (InnerProductSpace.rankOne Complex k l).toLinearMap =
      ∑ i, (InnerProductSpace.rankOne Complex
        (densityEnsembleVectors H rho i ⊗ₜ[Complex] k)
        (densityEnsembleVectors H rho i ⊗ₜ[Complex] l)).toLinearMap := by
  unfold prepareLeft
  rw [FiniteKrausFamily.toQuantumChannel_apply_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply LinearMap.ext
  intro x
  simp [prepareLeftKraus, prepareLeftBranch, LinearMap.comp_apply,
    InnerProductSpace.rankOne_apply, LinearMap.adjoint_inner_right]

/-- The left preparation channel is exactly tensoring with its input density. -/
theorem prepareLeft_apply (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (A : Operator K) :
    prepareLeft H K rho A = TensorProduct.map rho.toOperator A := by
  let basis := stdOrthonormalBasis Complex K
  rw [Semantics.QuditSubsystem.operator_eq_sum_rankOne_basis K basis A]
  rw [map_sum]
  rw [Semantics.QuditSubsystem.tensorMap_sum_right_reference]
  apply Finset.sum_congr rfl
  intro i _
  rw [prepareLeft_apply_rankOne]
  calc
    (∑ j,
      (InnerProductSpace.rankOne Complex
        (densityEnsembleVectors H rho j ⊗ₜ[Complex] (A (basis i)))
        (densityEnsembleVectors H rho j ⊗ₜ[Complex] (basis i))).toLinearMap) =
        ∑ j, TensorProduct.map
          (InnerProductSpace.rankOne Complex (densityEnsembleVectors H rho j)
            (densityEnsembleVectors H rho j)).toLinearMap
          (InnerProductSpace.rankOne Complex (A (basis i)) (basis i)).toLinearMap := by
            apply Finset.sum_congr rfl
            intro j _
            rw [tensorMap_rankOne]
    _ = TensorProduct.map (∑ j,
        (InnerProductSpace.rankOne Complex (densityEnsembleVectors H rho j)
          (densityEnsembleVectors H rho j)).toLinearMap)
        (InnerProductSpace.rankOne Complex (A (basis i)) (basis i)).toLinearMap := by
          rw [Semantics.QuditSubsystem.tensorMap_sum_left_reference]
    _ = TensorProduct.map rho.toOperator
        (InnerProductSpace.rankOne Complex (A (basis i)) (basis i)).toLinearMap := by
          rw [← densityEnsemble_specification]

/-- Extend an operator on the literal complement of a qudit subsystem. -/
noncomputable def complementExtension {ι : Type u} [Fintype ι] [DecidableEq ι]
    {q : ι -> Nat} (S : QuditSubsystem q) (A : Operator S.complementSystem) :
    Operator (Qudit.QuditRegister q) :=
  S.registerFactorization.symm.conjOperator
    (TensorProduct.map (1 : Operator S.selectedSystem) A)

private theorem extendLocalToRegister_commutes_complementExtension
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι -> Nat}
    (S : QuditSubsystem q) (A : Operator S.selectedSystem)
    (B : Operator S.complementSystem) :
    (S.extendLocalToRegister A).comp (complementExtension S B) =
      (complementExtension S B).comp (S.extendLocalToRegister A) := by
  unfold QuditSubsystem.extendLocalToRegister QuditSubsystem.extendLocal complementExtension
  rw [← S.registerFactorization.symm.conjOperator_comp]
  rw [← S.registerFactorization.symm.conjOperator_comp]
  rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
  simp [Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]

set_option maxRecDepth 8192 in
private theorem erasureChannelFromRegister_trace_pairing
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι -> Nat}
    (S : QuditSubsystem q) (A : Operator (Qudit.QuditRegister q))
    (X : Operator S.complementSystem) :
    LinearMap.trace Complex S.complementSystem
      ((S.erasureChannelFromRegister A).comp X) =
      LinearMap.trace Complex (Qudit.QuditRegister q)
        (A.comp (complementExtension S X)) := by
  let U := S.registerFactorization
  change LinearMap.trace Complex S.complementSystem
      ((FiniteMatrixEntropy.partialTraceLeftRaw S.selectedSystem S.complementSystem
        (U.conjOperator A)).comp X) = _
  rw [FiniteMatrixEntropy.partialTraceLeftRaw_trace_pairing]
  have hconj : (U.conjOperator A).comp
      (TensorProduct.map (LinearMap.id : S.selectedSystem →ₗ[Complex] S.selectedSystem) X) =
      U.conjOperator (A.comp
        (U.symm.conjOperator
          (TensorProduct.map (LinearMap.id : S.selectedSystem →ₗ[Complex] S.selectedSystem) X))) := by
    simp [U, UnitaryTransport.conjOperator, LinearMap.comp_assoc]
  rw [hconj, U.trace_conjOperator]
  rfl

set_option maxRecDepth 8192 in
private theorem erasureChannelFromRegister_conjOperator_eq_of_supported
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι -> Nat}
    (S : QuditSubsystem q) (U : UnitaryTransport (Qudit.QuditRegister q)
      (Qudit.QuditRegister q))
    (hU : S.OperatorSupportedOnRegister U.toLinearEquiv.toLinearMap)
    (A : Operator (Qudit.QuditRegister q)) :
    S.erasureChannelFromRegister (U.conjOperator A) = S.erasureChannelFromRegister A := by
  apply Semantics.operator_ext_of_trace_comp_right_eq
  intro X
  rcases hU with ⟨localU, hlocalU⟩
  have hcomm : U.toLinearEquiv.toLinearMap.comp (complementExtension S X) =
      (complementExtension S X).comp U.toLinearEquiv.toLinearMap := by
    rw [← hlocalU]
    exact extendLocalToRegister_commutes_complementExtension S localU X
  have hmiddle : (U.toLinearEquiv.symm.toLinearMap.comp
      (complementExtension S X)).comp U.toLinearEquiv.toLinearMap =
      complementExtension S X := by
    calc
      (U.toLinearEquiv.symm.toLinearMap.comp
          (complementExtension S X)).comp U.toLinearEquiv.toLinearMap =
          U.toLinearEquiv.symm.toLinearMap.comp
            ((complementExtension S X).comp U.toLinearEquiv.toLinearMap) := by
              rw [LinearMap.comp_assoc]
      _ = U.toLinearEquiv.symm.toLinearMap.comp
            (U.toLinearEquiv.toLinearMap.comp (complementExtension S X)) := by rw [hcomm]
      _ = (U.toLinearEquiv.symm.toLinearMap.comp U.toLinearEquiv.toLinearMap).comp
            (complementExtension S X) := by rw [LinearMap.comp_assoc]
      _ = complementExtension S X := by simp
  calc
    LinearMap.trace Complex S.complementSystem
        (X.comp (S.erasureChannelFromRegister (U.conjOperator A))) =
        LinearMap.trace Complex S.complementSystem
          ((S.erasureChannelFromRegister (U.conjOperator A)).comp X) :=
            (LinearMap.trace_comp_comm' X
              (S.erasureChannelFromRegister (U.conjOperator A))).symm
    _ = LinearMap.trace Complex (Qudit.QuditRegister q)
        ((U.conjOperator A).comp (complementExtension S X)) :=
          erasureChannelFromRegister_trace_pairing S (U.conjOperator A) X
    _ = LinearMap.trace Complex (Qudit.QuditRegister q)
          ((A.comp (U.toLinearEquiv.symm.toLinearMap.comp
            (complementExtension S X))).comp U.toLinearEquiv.toLinearMap) := by
              rw [UnitaryTransport.conjOperator, LinearMap.comp_assoc]
              exact (LinearMap.trace_comp_comm' U.toLinearEquiv.toLinearMap
                (A.comp (U.toLinearEquiv.symm.toLinearMap.comp
                  (complementExtension S X)))).symm
    _ = LinearMap.trace Complex (Qudit.QuditRegister q)
          (A.comp (complementExtension S X)) := by
            congr 1
            rw [← LinearMap.comp_assoc]
            exact congrArg (fun T : Operator (Qudit.QuditRegister q) => A.comp T) hmiddle
    _ = LinearMap.trace Complex S.complementSystem
          ((S.erasureChannelFromRegister A).comp X) :=
            (erasureChannelFromRegister_trace_pairing S A X).symm
    _ = LinearMap.trace Complex S.complementSystem
          (X.comp (S.erasureChannelFromRegister A)) :=
            LinearMap.trace_comp_comm' X (S.erasureChannelFromRegister A)

private theorem tensorMap_rankOne_left_range
    (H K : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] (phi : H) (P : Operator K)
    (z : CompositeSystem H K) :
    TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap P z ∈
      LinearMap.range (prepareLeftBranch H K phi) := by
  induction z using TensorProduct.induction_on with
  | zero =>
      refine ⟨0, ?_⟩
      simp [prepareLeftBranch]
  | tmul h k =>
      refine ⟨(inner Complex phi h) • P k, ?_⟩
      simp [prepareLeftBranch, InnerProductSpace.rankOne_apply,
        TensorProduct.smul_tmul]
  | add x y hx hy =>
      rcases hx with ⟨x, hx⟩
      rcases hy with ⟨y, hy⟩
      refine ⟨x + y, ?_⟩
      simpa [map_add, hx, hy] using congrArg₂ (· + ·) hx hy

/-
The #388 disentangler fixes every code density after erasing the disentangled
region and preparing its source-provided pure state.  This is the exact
code-support use of the projector factorization, not an assumed recovery.
-/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem disentangled_prepareSelected_fixed
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (unitary : UnitaryTransport L.Register L.Register)
    (regionalState : (M.regionSubsystem region).selectedSystem)
    (complementProjector : Operator (M.regionSubsystem region).complementSystem)
    (unitary_supported : M.UnitarySupportedOn (M.boundary region) unitary)
    (regionalState_normalized : ‖regionalState‖ = 1)
    (projector_factorization :
      unitary.conjOperator M.fullCodeProjector =
        M.pureFactorTensorComplementProjector region regionalState complementProjector)
    (rho : DensityOperator L.Register)
    (hsupported : DensityOperator.SupportedOn M.codeSpace rho) :
    (M.regionSubsystem region).prepareSelected
      (pureDensity regionalState (by rw [regionalState_normalized]; norm_num))
      ((M.regionSubsystem region).erasureChannelFromRegister
        (unitary.conjOperator rho.toOperator)) =
      unitary.conjOperator rho.toOperator := by
  let S := M.regionSubsystem region
  let rhoU := unitary.conjDensity rho
  have hcode : M.fullCodeProjector.comp rho.toOperator = rho.toOperator :=
    DensityOperator.supportedOn_projector_comp_eq_self M.codeSpace rho hsupported
  have hunitaryCode : (unitary.conjOperator M.fullCodeProjector).comp rhoU.toOperator =
      rhoU.toOperator := by
    change (unitary.conjOperator M.fullCodeProjector).comp
        (unitary.conjOperator rho.toOperator) = unitary.conjOperator rho.toOperator
    rw [← unitary.conjOperator_comp, hcode]
  have hcoordinateCode :
      (TensorProduct.map (InnerProductSpace.rankOne Complex regionalState regionalState).toLinearMap
        complementProjector).comp (S.registerFactorization.conjOperator rhoU.toOperator) =
        S.registerFactorization.conjOperator rhoU.toOperator := by
    calc
      (TensorProduct.map
          (InnerProductSpace.rankOne Complex regionalState regionalState).toLinearMap
          complementProjector).comp (S.registerFactorization.conjOperator rhoU.toOperator) =
          S.registerFactorization.conjOperator
            ((M.pureFactorTensorComplementProjector region regionalState complementProjector).comp
              rhoU.toOperator) := by
            symm
            unfold BPTCommutingProjectorModel.pureFactorTensorComplementProjector
            rw [S.registerFactorization.conjOperator_comp]
            rw [S.registerFactorization.conjOperator_symm_conjOperator]
      _ = S.registerFactorization.conjOperator
            ((unitary.conjOperator M.fullCodeProjector).comp rhoU.toOperator) := by
            rw [projector_factorization]
      _ = S.registerFactorization.conjOperator rhoU.toOperator := by rw [hunitaryCode]
  have hbranch : ∀ z : S.factorizedSystem,
      (S.registerFactorization.conjOperator rhoU.toOperator) z ∈
        LinearMap.range (S.prepareFactorizedBranch regionalState) := by
    intro z
    rw [← hcoordinateCode]
    simp only [LinearMap.comp_apply]
    exact tensorMap_rankOne_left_range S.selectedSystem S.complementSystem
      regionalState complementProjector (S.registerFactorization.conjOperator rhoU.toOperator z)
  have hprepared := S.prepareFactorized_erasure_fixed_of_supportedOn_branch
    regionalState (by rw [regionalState_normalized]; norm_num)
    (S.registerFactorization.conjDensity rhoU) hbranch
  change S.registerFactorization.symm.conjOperator
      (S.prepareFactorized (pureDensity regionalState (by rw [regionalState_normalized]; norm_num))
        (S.erasureChannel (S.registerFactorization.conjOperator rhoU.toOperator))) =
      rhoU.toOperator
  rw [← S.registerFactorization.conjDensity_toOperator]
  rw [hprepared]
  exact S.registerFactorization.symm_conjOperator_conjOperator rhoU.toOperator

/-- Tracing the right factor of an operator tensor product multiplies by its trace. -/
theorem partialTraceRightRaw_tensorMap (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (A : Operator H) (B : Operator K) :
    partialTraceRightRaw H K (TensorProduct.map A B) =
      (LinearMap.trace Complex K B) • A := by
  apply Semantics.operator_ext_of_trace_comp_right_eq
  intro X
  let basis : OrthonormalBasis
      (ULift.{u} (Fin (Module.finrank Complex K))) Complex K :=
    (stdOrthonormalBasis Complex K).reindex Equiv.ulift.symm
  calc
    LinearMap.trace Complex H (X.comp
        (partialTraceRightRaw H K (TensorProduct.map A B))) =
        LinearMap.trace Complex H
          ((partialTraceRightRaw H K (TensorProduct.map A B)).comp X) :=
            (LinearMap.trace_comp_comm' X
              (partialTraceRightRaw H K (TensorProduct.map A B))).symm
    _ = LinearMap.trace Complex (CompositeSystem H K)
        ((TensorProduct.map A B).comp
          (TensorProduct.map X (LinearMap.id : K →ₗ[Complex] K))) :=
            FiniteMatrixEntropy.partialTraceRightRaw_trace_pairing
              basis (TensorProduct.map A B) X
    _ = LinearMap.trace Complex H (((LinearMap.trace Complex K B) • A).comp X) := by
          rw [← TensorProduct.map_comp, LinearMap.trace_tensorProduct']
          simp [LinearMap.smul_comp]
          ring
    _ = LinearMap.trace Complex H (X.comp ((LinearMap.trace Complex K B) • A)) :=
          LinearMap.trace_comp_comm' X ((LinearMap.trace Complex K B) • A)

/-- Tracing the left factor of an operator tensor product multiplies by its trace. -/
theorem partialTraceLeftRaw_tensorMap (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (A : Operator H) (B : Operator K) :
    FiniteMatrixEntropy.partialTraceLeftRaw H K (TensorProduct.map A B) =
      (LinearMap.trace Complex H A) • B := by
  apply Semantics.operator_ext_of_trace_comp_right_eq
  intro Y
  calc
    LinearMap.trace Complex K (Y.comp
        (FiniteMatrixEntropy.partialTraceLeftRaw H K (TensorProduct.map A B))) =
        LinearMap.trace Complex K
          ((FiniteMatrixEntropy.partialTraceLeftRaw H K (TensorProduct.map A B)).comp Y) :=
            (LinearMap.trace_comp_comm' Y
              (FiniteMatrixEntropy.partialTraceLeftRaw H K (TensorProduct.map A B))).symm
    _ = LinearMap.trace Complex (CompositeSystem H K)
        ((TensorProduct.map A B).comp
          (TensorProduct.map (LinearMap.id : H →ₗ[Complex] H) Y)) :=
            FiniteMatrixEntropy.partialTraceLeftRaw_trace_pairing (TensorProduct.map A B) Y
    _ = LinearMap.trace Complex K (((LinearMap.trace Complex H A) • B).comp Y) := by
          rw [← TensorProduct.map_comp, LinearMap.trace_tensorProduct']
          simp [LinearMap.smul_comp]
    _ = LinearMap.trace Complex K (Y.comp ((LinearMap.trace Complex H A) • B)) :=
          LinearMap.trace_comp_comm' Y ((LinearMap.trace Complex H A) • B)

/-!
## Concrete `A B C D` coordinates

The source proof names the four factors implicitly.  The declarations below
make that coordinate calculation an internal Lean API: `A = M \\ B`, the
two cover pieces are `B` and `C`, and `D = (M union C)^c`.
-/

/-- Reorder `A tensor (B tensor (C tensor D))` into
`B tensor (C tensor (A tensor D))` before tracing the source cover factors. -/
private noncomputable def abcdToBcad
    (A B C D : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [FiniteQuantumSystem D] :
    UnitaryTransport
      (CompositeSystem A (CompositeSystem B (CompositeSystem C D)))
      (CompositeSystem B (CompositeSystem C (CompositeSystem A D))) :=
  composeUnitaryTransport
    (BPTEntropy.abcToBac A B (CompositeSystem C D))
    (unitaryLTensor B (BPTEntropy.abcToBac A C D))

@[simp] private theorem abcdToBcad_apply_tmul
    (A B C D : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [FiniteQuantumSystem D]
    (a : A) (b : B) (c : C) (d : D) :
    abcdToBcad A B C D (a ⊗ₜ[Complex] (b ⊗ₜ[Complex] (c ⊗ₜ[Complex] d))) =
      b ⊗ₜ[Complex] (c ⊗ₜ[Complex] (a ⊗ₜ[Complex] d)) := by
  simp [abcdToBcad, composeUnitaryTransport_apply]

private theorem tensorComm_conj_rankOne
    (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (h h' : H) (k k' : K) :
    (TensorProduct.comm Complex H K).conj
        (InnerProductSpace.rankOne Complex (h ⊗ₜ[Complex] k)
          (h' ⊗ₜ[Complex] k')).toLinearMap =
      (InnerProductSpace.rankOne Complex (k ⊗ₜ[Complex] h)
        (k' ⊗ₜ[Complex] h')).toLinearMap := by
  change (tensorSwap H K).conjOperator
      (InnerProductSpace.rankOne Complex (h ⊗ₜ[Complex] k)
        (h' ⊗ₜ[Complex] k')).toLinearMap = _
  rw [QuditSubsystem.conjOperator_rankOne]
  rfl

private theorem partialTraceLeftRaw_rankOne_tmul
    (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (h h' : H) (k k' : K) :
    FiniteMatrixEntropy.partialTraceLeftRaw H K
        (InnerProductSpace.rankOne Complex (h ⊗ₜ[Complex] k)
          (h' ⊗ₜ[Complex] k')).toLinearMap =
      (inner Complex h' h) •
        (InnerProductSpace.rankOne Complex k k').toLinearMap := by
  unfold FiniteMatrixEntropy.partialTraceLeftRaw
  simp only [LinearMap.comp_apply]
  change partialTraceRightRaw K H
      ((tensorSwap H K).conjOperator
        (InnerProductSpace.rankOne Complex (h ⊗ₜ[Complex] k)
          (h' ⊗ₜ[Complex] k')).toLinearMap) = _
  rw [QuditSubsystem.conjOperator_rankOne]
  simp only [tensorSwap_apply_tmul]
  rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]

/-- Trace the `B` and `C` factors after the concrete `A,B,C,D` regrouping. -/
private noncomputable def traceBCToAD
    (A B C D : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [FiniteQuantumSystem D] :
    Operator (CompositeSystem A (CompositeSystem B (CompositeSystem C D))) →ₗ[Complex]
      Operator (CompositeSystem A D) :=
  (FiniteMatrixEntropy.partialTraceLeftRaw C (CompositeSystem A D)).comp
    ((FiniteMatrixEntropy.partialTraceLeftRaw B (CompositeSystem C (CompositeSystem A D))).comp
      (abcdToBcad A B C D).conjOperatorLinearMap)

set_option maxHeartbeats 4000000 in
/-- The source `B,C` trace formula on a four-factor matrix unit. -/
private theorem traceBCToAD_four_rankOne
    (A B C D : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [FiniteQuantumSystem D]
    (a a' : A) (b b' : B) (c c' : C) (d d' : D) :
    traceBCToAD A B C D
      (show Operator (CompositeSystem A (CompositeSystem B (CompositeSystem C D))) from
        (InnerProductSpace.rankOne Complex
        (show CompositeSystem A (CompositeSystem B (CompositeSystem C D)) from
          a ⊗ₜ[Complex] (b ⊗ₜ[Complex] (c ⊗ₜ[Complex] d)))
        (show CompositeSystem A (CompositeSystem B (CompositeSystem C D)) from
          a' ⊗ₜ[Complex] (b' ⊗ₜ[Complex] (c' ⊗ₜ[Complex] d')))).toLinearMap) =
      (inner Complex b' b * inner Complex c' c) •
        (InnerProductSpace.rankOne Complex (a ⊗ₜ[Complex] d)
          (a' ⊗ₜ[Complex] d')).toLinearMap := by
  change FiniteMatrixEntropy.partialTraceLeftRaw C (CompositeSystem A D)
      (FiniteMatrixEntropy.partialTraceLeftRaw B (CompositeSystem C (CompositeSystem A D))
        ((abcdToBcad A B C D).conjOperator
          (InnerProductSpace.rankOne Complex
            (show CompositeSystem A (CompositeSystem B (CompositeSystem C D)) from
              a ⊗ₜ[Complex] (b ⊗ₜ[Complex] (c ⊗ₜ[Complex] d)))
            (show CompositeSystem A (CompositeSystem B (CompositeSystem C D)) from
              a' ⊗ₜ[Complex] (b' ⊗ₜ[Complex] (c' ⊗ₜ[Complex] d')))).toLinearMap)) = _
  rw [QuditSubsystem.conjOperator_rankOne]
  simp only [abcdToBcad_apply_tmul]
  rw [partialTraceLeftRaw_rankOne_tmul]
  rw [map_smul]
  rw [partialTraceLeftRaw_rankOne_tmul]
  simp [smul_smul]

set_option maxHeartbeats 2000000 in
/-- The source `B,C` trace formula for arbitrary finite operators. -/
private theorem traceBCToAD_tensorMap
    (A B C D : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [FiniteQuantumSystem D]
    (eta : Operator (CompositeSystem A B)) (sigma : Operator (CompositeSystem C D)) :
    traceBCToAD A B C D
      ((tensorAssociatorUnitary A B (CompositeSystem C D)).conjOperator
        (TensorProduct.map eta sigma)) =
      TensorProduct.map (partialTraceRightRaw A B eta)
        (FiniteMatrixEntropy.partialTraceLeftRaw C D sigma) := by
  let bA := stdOrthonormalBasis Complex A
  let bB := stdOrthonormalBasis Complex B
  let bC := stdOrthonormalBasis Complex C
  let bD := stdOrthonormalBasis Complex D
  let bAB := bA.tensorProduct bB
  let bCD := bC.tensorProduct bD
  rw [QuditSubsystem.operator_eq_sum_rankOne_matrix_basis bAB eta]
  rw [QuditSubsystem.operator_eq_sum_rankOne_matrix_basis bCD sigma]
  simp_rw [QuditSubsystem.tensorMap_sum_left_reference,
    QuditSubsystem.tensorMap_sum_right_reference]
  simp only [TensorProduct.map_smul_left, TensorProduct.map_smul_right, map_sum, map_smul]
  change ((traceBCToAD A B C D).comp
    (tensorAssociatorUnitary A B (CompositeSystem C D)).conjOperatorLinearMap) _ = _
  simp only [LinearMap.comp_apply, map_sum, map_smul]
  simp_rw [QuditSubsystem.tensorMap_sum_left_reference,
    QuditSubsystem.tensorMap_sum_right_reference]
  simp only [TensorProduct.map_smul_left, TensorProduct.map_smul_right, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  rcases k with ⟨ic, id⟩
  rcases l with ⟨jc, jd⟩
  simp only [bAB, bCD, OrthonormalBasis.tensorProduct_apply']
  simp only [UnitaryTransport.conjOperatorLinearMap_apply]
  rw [tensorMap_rankOne]
  rw [QuditSubsystem.conjOperator_rankOne]
  simp only [tensorAssociatorUnitary_apply_tmul]
  rw [traceBCToAD_four_rankOne A B C D]
  rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  rw [partialTraceLeftRaw_rankOne_tmul]
  rw [TensorProduct.map_smul_left, TensorProduct.map_smul_right]
  rw [tensorMap_rankOne]
  simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]

private abbrev recursionA (M : BPTCommutingProjectorModel L kappa)
    (region inside : Finset L.Site) : QuditSubsystem L.localDimension :=
  M.regionSubsystem (region \ inside)

private abbrev recursionAB (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : QuditSubsystem L.localDimension :=
  M.regionSubsystem region

private abbrev recursionABC (M : BPTCommutingProjectorModel L kappa)
    (region inside outside : Finset L.Site) : QuditSubsystem L.localDimension :=
  BPTEntropy.QuditSubsystem.unionSubsystem
    (M.regionSubsystem (region \ inside)) (M.regionSubsystem (inside ∪ outside))

private theorem recursionA_subset_region
    (M : BPTCommutingProjectorModel L kappa) (region inside : Finset L.Site) :
    (recursionA M region inside).selected ⊆ (recursionAB M region).selected := by
  simpa [recursionA, recursionAB] using
    fun site hsite => (Finset.mem_sdiff.mp hsite).1

private theorem recursionAB_subset_ABC
    (M : BPTCommutingProjectorModel L kappa) (region inside outside : Finset L.Site)
    (hinside : inside ⊆ region) :
    (recursionAB M region).selected ⊆ (recursionABC M region inside outside).selected := by
  change region ⊆ (region \ inside) ∪ (inside ∪ outside)
  intro site hsite
  by_cases hsiteInside : site ∈ inside
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ hsiteInside)
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hsite, hsiteInside⟩)

private theorem recursion_unionSubsystem_eq_target
    (M : BPTCommutingProjectorModel L kappa)
    (region inside outside : Finset L.Site) (hinside : inside ⊆ region) :
    BPTEntropy.QuditSubsystem.unionSubsystem (M.regionSubsystem (region \ inside))
      (M.regionSubsystem (inside ∪ outside)) = M.regionSubsystem (region ∪ outside) := by
  change ({ selected := (region \ inside) ∪ (inside ∪ outside) } : QuditSubsystem L.localDimension) =
    { selected := region ∪ outside }
  congr 1
  ext site
  constructor
  · intro hsite
    rcases Finset.mem_union.mp hsite with hleft | hcover
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hleft).1
    · rcases Finset.mem_union.mp hcover with hinsideSite | houtsideSite
      · exact Finset.mem_union_left _ (hinside hinsideSite)
      · exact Finset.mem_union_right _ houtsideSite
  · intro hsite
    rcases Finset.mem_union.mp hsite with hregion | houtsideSite
    · by_cases hinsideSite : site ∈ inside
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ hinsideSite)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hregion, hinsideSite⟩)
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ houtsideSite)

/-- The concrete four-factor coordinate transport for the source partition
`A = M \\ B`, `B`, `C`, `D = (M union C)^c`. -/
private noncomputable def recursionFourFactorTransport
    (M : BPTCommutingProjectorModel L kappa)
    (region inside outside : Finset L.Site)
    (hinside : inside ⊆ region) :
    UnitaryTransport L.Register
      (CompositeSystem
        (M.regionSubsystem (region \ inside)).selectedSystem
        (CompositeSystem
          ((M.regionSubsystem (region \ inside)).additionalRetainedSystem
            (M.regionSubsystem region))
          (CompositeSystem
            ((M.regionSubsystem region).additionalRetainedSystem
              (recursionABC M region inside outside))
            (recursionABC M region inside outside).complementSystem))) := by
  let A := M.regionSubsystem (region \ inside)
  let AB := M.regionSubsystem region
  let ABC := recursionABC M region inside outside
  have hAAB : A.selected ⊆ AB.selected := by
    simpa [A, AB] using fun site hsite => (Finset.mem_sdiff.mp hsite).1
  have hABABC : AB.selected ⊆ ABC.selected := by
    simpa [AB, ABC] using recursionAB_subset_ABC M region inside outside hinside
  let splitAB := A.selectedFactorization AB hAAB
  let splitCD := AB.complementFactorization ABC hABABC
  exact composeUnitaryTransport
    (composeUnitaryTransport
      (composeUnitaryTransport AB.registerFactorization
        (unitaryRTensor splitAB AB.complementSystem))
      (unitaryLTensor (CompositeSystem A.selectedSystem
        (A.additionalRetainedSystem AB)) splitCD))
    (tensorAssociatorUnitary A.selectedSystem (A.additionalRetainedSystem AB)
      (CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem))

set_option maxHeartbeats 1000000 in
private theorem recursionFourFactorTransport_apply_basis
    (M : BPTCommutingProjectorModel L kappa)
    (region inside outside : Finset L.Site)
    (hinside : inside ⊆ region) (labels : Qudit.Label L.localDimension) :
    recursionFourFactorTransport M region inside outside hinside
      (EuclideanSpace.basisFun (Qudit.Label L.localDimension) Complex labels) =
      (EuclideanSpace.basisFun
        (Qudit.Label (recursionA M region inside).selectedDimensions) Complex
        ((recursionA M region inside).splitSelectedLabel (recursionAB M region)
          (recursionA_subset_region M region inside)
          ((recursionAB M region).splitLabel labels).1).1) ⊗ₜ[Complex]
      ((EuclideanSpace.basisFun
          (Qudit.Label
            ((recursionA M region inside).additionalRetainedDimensions (recursionAB M region)))
          Complex
          ((recursionA M region inside).splitSelectedLabel (recursionAB M region)
            (recursionA_subset_region M region inside)
            ((recursionAB M region).splitLabel labels).1).2) ⊗ₜ[Complex]
        ((EuclideanSpace.basisFun
            (Qudit.Label
              ((recursionAB M region).additionalRetainedDimensions
                (recursionABC M region inside outside))) Complex
            ((recursionAB M region).splitComplementLabel (recursionABC M region inside outside)
              (recursionAB_subset_ABC M region inside outside hinside)
              ((recursionAB M region).splitLabel labels).2).1) ⊗ₜ[Complex]
          (EuclideanSpace.basisFun
            (Qudit.Label (recursionABC M region inside outside).complementDimensions) Complex
            ((recursionAB M region).splitComplementLabel (recursionABC M region inside outside)
              (recursionAB_subset_ABC M region inside outside hinside)
              ((recursionAB M region).splitLabel labels).2).2))) := by
  dsimp [recursionFourFactorTransport]
  rw [(recursionAB M region).registerFactorization_apply_basis]
  rw [unitaryRTensor_apply_tmul]
  rw [(recursionA M region inside).selectedFactorization_apply_basis
    (recursionAB M region) (recursionA_subset_region M region inside)]
  rw [unitaryLTensor_apply_tmul]
  rw [(recursionAB M region).complementFactorization_apply_basis
    (recursionABC M region inside outside)
    (recursionAB_subset_ABC M region inside outside hinside)]
  rw [tensorAssociatorUnitary_apply_tmul]

private noncomputable def recursionABState
    (M : BPTCommutingProjectorModel L kappa)
    (region inside : Finset L.Site)
    (regionalState : (M.regionSubsystem region).selectedSystem)
    (hregionalState : ‖regionalState‖ = 1) :
    DensityOperator (CompositeSystem
      (recursionA M region inside).selectedSystem
      ((recursionA M region inside).additionalRetainedSystem (recursionAB M region))) :=
  ((recursionA M region inside).selectedFactorization (recursionAB M region)
    (recursionA_subset_region M region inside)).conjDensity
      (pureDensity regionalState (by simpa [hregionalState]))

private noncomputable def recursionCDOperator
    (M : BPTCommutingProjectorModel L kappa)
    (region inside outside : Finset L.Site) (hinside : inside ⊆ region)
    (A : Operator (M.regionSubsystem region).complementSystem) :
    Operator (CompositeSystem
      ((recursionAB M region).additionalRetainedSystem (recursionABC M region inside outside))
      (recursionABC M region inside outside).complementSystem) :=
  ((recursionAB M region).complementFactorization (recursionABC M region inside outside)
    (recursionAB_subset_ABC M region inside outside hinside)).conjOperator A

set_option maxHeartbeats 1000000 in
/-- In the explicit `A,B,C,D` coordinates, preparation of the regional pure
   state is exactly the source product `eta_AB tensor sigma_CD`. -/
private theorem recursionFourFactor_conj_prepareSelected
    (M : BPTCommutingProjectorModel L kappa)
    (region inside outside : Finset L.Site)
    (hinside : inside ⊆ region)
    (regionalState : (M.regionSubsystem region).selectedSystem)
    (hregionalState : ‖regionalState‖ = 1)
    (A : Operator (M.regionSubsystem region).complementSystem) :
    (recursionFourFactorTransport M region inside outside hinside).conjOperator
      ((M.regionSubsystem region).prepareSelected
        (pureDensity regionalState (by simpa [hregionalState])) A) =
      (tensorAssociatorUnitary
        (recursionA M region inside).selectedSystem
        ((recursionA M region inside).additionalRetainedSystem (recursionAB M region))
        (CompositeSystem
          ((recursionAB M region).additionalRetainedSystem (recursionABC M region inside outside))
          (recursionABC M region inside outside).complementSystem)).conjOperator
        (TensorProduct.map
          (recursionABState M region inside regionalState hregionalState).toOperator
          (recursionCDOperator M region inside outside hinside A)) := by
  unfold recursionFourFactorTransport recursionABState recursionCDOperator
  simp only [composeUnitaryTransport_conjOperator]
  rw [QuditSubsystem.prepareSelected_pureDensity_apply]
  rw [(M.regionSubsystem region).registerFactorization.conjOperator_symm_conjOperator]
  rw [unitaryRTensor_conj_tensorMap, unitaryLTensor_conj_tensorMap]
  simp only [UnitaryTransport.conjDensity_toOperator, pureDensity_toOperator]

set_option maxRecDepth 8192 in
private theorem recursionCDOperator_traceC_eq_target_erasure
    (M : BPTCommutingProjectorModel L kappa)
    (region inside outside : Finset L.Site) (hinside : inside ⊆ region)
    (A : Operator L.Register) :
    FiniteMatrixEntropy.partialTraceLeftRaw
      ((recursionAB M region).additionalRetainedSystem (recursionABC M region inside outside))
      (recursionABC M region inside outside).complementSystem
      (recursionCDOperator M region inside outside hinside
        ((recursionAB M region).erasureChannelFromRegister A)) =
      (recursionABC M region inside outside).erasureChannelFromRegister A := by
  have hdiscard := (recursionAB M region).discardAdditionalRetained_erasureChannelFromRegister_apply
    (recursionABC M region inside outside)
    (recursionAB_subset_ABC M region inside outside hinside) A
  simpa [recursionCDOperator, QuditSubsystem.discardAdditionalRetained,
    QuditSubsystem.additionalRetainedFactorSwap,
    FiniteMatrixEntropy.partialTraceLeftRaw, UnitaryTransport.conjOperator,
    LinearEquiv.conj_apply, LinearMap.comp_assoc] using hdiscard

private noncomputable def recursionLeftState
    (M : BPTCommutingProjectorModel L kappa)
    (region inside : Finset L.Site) (hinside : inside ⊆ region)
    (regionalState : (M.regionSubsystem region).selectedSystem)
    (hregionalState : ‖regionalState‖ = 1) :
    DensityOperator (M.regionSubsystem (region \ inside)).selectedSystem := by
  let A := M.regionSubsystem (region \ inside)
  let AB := M.regionSubsystem region
  have hAAB : A.selected ⊆ AB.selected := by
    simpa [A, AB] using fun site hsite => (Finset.mem_sdiff.mp hsite).1
  exact DensityOperator.rightMarginal
    ((A.selectedFactorization AB hAAB).conjDensity
      (pureDensity regionalState (by simpa [hregionalState])))

/-- The concrete CPTP preparation used by BPT's recursion proof. -/
private noncomputable def recursionPreparation
    (M : BPTCommutingProjectorModel L kappa)
    (region inside outside : Finset L.Site)
    (hinside : inside ⊆ region) (houtside : outside ⊆ regionᶜ)
    (regionalState : (M.regionSubsystem region).selectedSystem)
    (hregionalState : ‖regionalState‖ = 1) :
    QuantumChannel
      (BPTEntropy.QuditSubsystem.unionSubsystem
        (M.regionSubsystem (region \ inside))
        (M.regionSubsystem (inside ∪ outside))).complementSystem
      (M.regionSubsystem (inside ∪ outside)).complementSystem := by
  let A := M.regionSubsystem (region \ inside)
  let BC := M.regionSubsystem (inside ∪ outside)
  have hdisjoint : Disjoint A.selected BC.selected := by
    rw [Finset.disjoint_left]
    intro site hA hBC
    rcases Finset.mem_union.mp hBC with hinsideSite | houtsideSite
    · exact (Finset.mem_sdiff.mp hA).2 hinsideSite
    · exact (Finset.mem_compl.mp (houtside houtsideSite)) (Finset.mem_sdiff.mp hA).1
  exact QuantumChannel.comp
    (QuantumChannel.unitaryConj
      (BPTEntropy.QuditSubsystem.complementBACFactorization A BC hdisjoint).symm)
    (prepareLeft _ _ (recursionLeftState M region inside hinside regionalState hregionalState))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
/--
The physical cover erasure, transported by its concrete complement
factorization, is exactly the `A tensor D` coordinate obtained by tracing the
literal `B` and `C` factors.  This is the bridge that prevents the recursion
argument from silently replacing a physical erasure by a set-theoretic one.
-/
theorem recursion_cover_erasure_coordinates
    (M : BPTCommutingProjectorModel L kappa)
    (region inside outside : Finset L.Site)
    (hinside : inside ⊆ region) (houtside : outside ⊆ regionᶜ)
    (rho : Operator L.Register) :
    let A := M.regionSubsystem (region \ inside)
    let BC := M.regionSubsystem (inside ∪ outside)
    let hdisjoint : Disjoint A.selected BC.selected := by
      rw [Finset.disjoint_left]
      intro site hA hBC
      rcases Finset.mem_union.mp hBC with hinsideSite | houtsideSite
      · exact (Finset.mem_sdiff.mp hA).2 hinsideSite
      · exact (Finset.mem_compl.mp (houtside houtsideSite)) (Finset.mem_sdiff.mp hA).1
    (BPTEntropy.QuditSubsystem.complementBACFactorization A BC hdisjoint).conjOperator
      (BC.erasureChannelFromRegister rho) =
      traceBCToAD A.selectedSystem
        ((M.regionSubsystem (region \ inside)).additionalRetainedSystem
          (M.regionSubsystem region))
        ((M.regionSubsystem region).additionalRetainedSystem
          (recursionABC M region inside outside))
        (recursionABC M region inside outside).complementSystem
        ((recursionFourFactorTransport M region inside outside hinside).conjOperator rho) := by
  dsimp
  let A := M.regionSubsystem (region \ inside)
  let BC := M.regionSubsystem (inside ∪ outside)
  have hdisjoint : Disjoint A.selected BC.selected := by
    rw [Finset.disjoint_left]
    intro site hA hBC
    rcases Finset.mem_union.mp hBC with hinsideSite | houtsideSite
    · exact (Finset.mem_sdiff.mp hA).2 hinsideSite
    · exact (Finset.mem_compl.mp (houtside houtsideSite)) (Finset.mem_sdiff.mp hA).1
  let basis := EuclideanSpace.basisFun (Qudit.Label L.localDimension) Complex
  let Phi : Operator L.Register →ₗ[Complex]
      Operator (CompositeSystem A.selectedSystem
        (recursionABC M region inside outside).complementSystem) :=
    (BPTEntropy.QuditSubsystem.complementBACFactorization A BC hdisjoint).conjOperatorLinearMap.comp
      BC.erasureChannelFromRegister.toLinearMap
  let Psi : Operator L.Register →ₗ[Complex]
      Operator (CompositeSystem A.selectedSystem
        (recursionABC M region inside outside).complementSystem) :=
    (traceBCToAD A.selectedSystem
      (A.additionalRetainedSystem (M.regionSubsystem region))
      ((M.regionSubsystem region).additionalRetainedSystem (recursionABC M region inside outside))
      (recursionABC M region inside outside).complementSystem).comp
      (recursionFourFactorTransport M region inside outside hinside).conjOperatorLinearMap
  change Phi rho = Psi rho
  have hmaps : Phi = Psi := by
    apply QuditSubsystem.linearMap_ext_of_rankOne_basis basis Phi Psi
    intro x y
    simp only [Phi, Psi, LinearMap.comp_apply]
    rw [BC.erasureChannelFromRegister_rankOne_basis x y]
    rw [map_smul]
    simp only [UnitaryTransport.conjOperatorLinearMap_apply]
    rw [QuditSubsystem.conjOperator_rankOne]
    rw [BPTEntropy.QuditSubsystem.complementBACFactorization_apply_basis]
    rw [BPTEntropy.QuditSubsystem.complementBACFactorization_apply_basis]
    rw [QuditSubsystem.conjOperator_rankOne]
    symm
    have hx := recursionFourFactorTransport_apply_basis M region inside outside hinside x
    have hy := recursionFourFactorTransport_apply_basis M region inside outside hinside y
    have hrank := congrArg₂
      (fun p q => (InnerProductSpace.rankOne Complex p q).toLinearMap) hx hy
    simp only [basis]
    refine (congrArg
      (traceBCToAD A.selectedSystem
        (A.additionalRetainedSystem (M.regionSubsystem region))
        ((M.regionSubsystem region).additionalRetainedSystem (recursionABC M region inside outside))
        (recursionABC M region inside outside).complementSystem) hrank).trans ?_
    rw [traceBCToAD_four_rankOne A.selectedSystem
      (A.additionalRetainedSystem (M.regionSubsystem region))
      ((M.regionSubsystem region).additionalRetainedSystem (recursionABC M region inside outside))
      (recursionABC M region inside outside).complementSystem]
    simp only [QuditSubsystem.splitSelectedLabel_splitLabel,
      QuditSubsystem.splitComplementLabel_splitLabel_second,
      BPTEntropy.QuditSubsystem.splitComplementBACLabel_splitLabel]
    let AB := M.regionSubsystem region
    let ABC := recursionABC M region inside outside
    have hAAB : A.selected ⊆ AB.selected := by
      simpa [A, AB] using recursionA_subset_region M region inside
    have hABABC : AB.selected ⊆ ABC.selected := by
      simpa [AB, ABC] using recursionAB_subset_ABC M region inside outside hinside
    let bx := (A.splitComplementLabel AB hAAB (A.splitLabel x).2).1
    let byLabel := (A.splitComplementLabel AB hAAB (A.splitLabel y).2).1
    let cx := (AB.splitComplementLabel ABC hABABC (AB.splitLabel x).2).1
    let cy := (AB.splitComplementLabel ABC hABABC (AB.splitLabel y).2).1
    let bcx := (BC.splitLabel x).1
    let bcy := (BC.splitLabel y).1
    have hlabels : bcy = bcx ↔ byLabel = bx ∧ cy = cx := by
      constructor
      · intro hbc
        constructor
        · funext i
          have hiInside : (i : L.Site) ∈ inside := by
            by_contra hiInside
            exact i.property.1 (by
              change (i : L.Site) ∈ region \ inside
              exact Finset.mem_sdiff.mpr ⟨i.property.2, hiInside⟩)
          have hiBC : (i : L.Site) ∈ BC.selected := by
            change (i : L.Site) ∈ inside ∪ outside
            exact Finset.mem_union_left _ hiInside
          have hi := congrFun hbc ⟨i, hiBC⟩
          simpa [bcy, bcx, byLabel, bx, QuditSubsystem.splitLabel,
            QuditSubsystem.splitComplementLabel] using hi
        · funext i
          have hiABC : (i : L.Site) ∈ ABC.selected := i.property.2
          have hiBC : (i : L.Site) ∈ BC.selected := by
            change (i : L.Site) ∈ (region \ inside) ∪ (inside ∪ outside) at hiABC
            rcases Finset.mem_union.mp hiABC with hiA | hiBC
            · exact False.elim (i.property.1 (Finset.mem_sdiff.mp hiA).1)
            · exact hiBC
          have hi := congrFun hbc ⟨i, hiBC⟩
          simpa [bcy, bcx, cy, cx, QuditSubsystem.splitLabel,
            QuditSubsystem.splitComplementLabel] using hi
      · rintro ⟨hb, hc⟩
        funext i
        change y i = x i
        have hiBC : (i : L.Site) ∈ inside ∪ outside := i.property
        rcases Finset.mem_union.mp hiBC with hiInside | hiOutside
        · have hiRegion : (i : L.Site) ∈ region := hinside hiInside
          have hiNotA : (i : L.Site) ∉ A.selected := by
            intro hiA
            exact (Finset.mem_sdiff.mp hiA).2 hiInside
          let ib : A.AdditionalRetainedCoordinates AB :=
            ⟨i, ⟨hiNotA, by simpa [AB] using hiRegion⟩⟩
          have hi := congrFun hb ib
          simpa [byLabel, bx, ib, QuditSubsystem.splitLabel,
            QuditSubsystem.splitComplementLabel] using hi
        · have hiNotRegion : (i : L.Site) ∉ region :=
            Finset.mem_compl.mp (houtside hiOutside)
          have hiABC : (i : L.Site) ∈ ABC.selected := by
            change (i : L.Site) ∈ (region \ inside) ∪ (inside ∪ outside)
            exact Finset.mem_union_right _ (Finset.mem_union_right _ hiOutside)
          let ic : AB.AdditionalRetainedCoordinates ABC :=
            ⟨i, ⟨by simpa [AB] using hiNotRegion, hiABC⟩⟩
          have hi := congrFun hc ic
          simpa [cy, cx, ic, QuditSubsystem.splitLabel,
            QuditSubsystem.splitComplementLabel] using hi
    have hcoefficient :
        inner Complex
            (EuclideanSpace.basisFun (Qudit.Label (A.additionalRetainedDimensions AB)) Complex byLabel)
            (EuclideanSpace.basisFun (Qudit.Label (A.additionalRetainedDimensions AB)) Complex bx) *
          inner Complex
            (EuclideanSpace.basisFun (Qudit.Label (AB.additionalRetainedDimensions ABC)) Complex cy)
            (EuclideanSpace.basisFun (Qudit.Label (AB.additionalRetainedDimensions ABC)) Complex cx) =
        inner Complex (EuclideanSpace.basisFun (Qudit.Label BC.selectedDimensions) Complex bcy)
          (EuclideanSpace.basisFun (Qudit.Label BC.selectedDimensions) Complex bcx) := by
      rw [(EuclideanSpace.basisFun (Qudit.Label (A.additionalRetainedDimensions AB))
        Complex).inner_eq_ite]
      rw [(EuclideanSpace.basisFun (Qudit.Label (AB.additionalRetainedDimensions ABC))
        Complex).inner_eq_ite]
      rw [(EuclideanSpace.basisFun (Qudit.Label BC.selectedDimensions) Complex).inner_eq_ite]
      by_cases hb : byLabel = bx
      · by_cases hc : cy = cx
        · have hbc := hlabels.mpr ⟨hb, hc⟩
          simp [hb, hc, hbc]
        · have hbc : bcy ≠ bcx := fun h => hc (hlabels.mp h).2
          simp [hb, hc, hbc]
      · have hbc : bcy ≠ bcx := fun h => hb (hlabels.mp h).1
        simp [hb, hbc]
    have hAx : (A.splitLabel x).1 = (BPTEntropy.QuditSubsystem.splitABCLabel A BC x).1 := by
      funext i
      rfl
    have hAy : (A.splitLabel y).1 = (BPTEntropy.QuditSubsystem.splitABCLabel A BC y).1 := by
      funext i
      rfl
    have hDx : (ABC.splitLabel x).2 =
        (BPTEntropy.QuditSubsystem.splitABCLabel A BC x).2.2 := by
      funext i
      rfl
    have hDy : (ABC.splitLabel y).2 =
        (BPTEntropy.QuditSubsystem.splitABCLabel A BC y).2.2 := by
      funext i
      rfl
    simpa [A, AB, ABC, recursionA, recursionAB,
      bx, byLabel, cx, cy, bcx, bcy, hAx, hAy, hDx, hDy] using
      congrArg (fun z => z •
        (InnerProductSpace.rankOne Complex
          ((EuclideanSpace.basisFun (Qudit.Label A.selectedDimensions) Complex
              (BPTEntropy.QuditSubsystem.splitABCLabel A BC x).1) ⊗ₜ[Complex]
            (EuclideanSpace.basisFun
              (Qudit.Label (BPTEntropy.QuditSubsystem.unionSubsystem A BC).complementDimensions)
              Complex (BPTEntropy.QuditSubsystem.splitABCLabel A BC x).2.2))
          ((EuclideanSpace.basisFun (Qudit.Label A.selectedDimensions) Complex
              (BPTEntropy.QuditSubsystem.splitABCLabel A BC y).1) ⊗ₜ[Complex]
            (EuclideanSpace.basisFun
              (Qudit.Label (BPTEntropy.QuditSubsystem.unionSubsystem A BC).complementDimensions)
              Complex (BPTEntropy.QuditSubsystem.splitABCLabel A BC y).2.2))).toLinearMap)
        hcoefficient
  exact LinearMap.congr_fun hmaps rho

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/--
Specializing the coordinate bridge to the #388 factorization: cover erasure
after the boundary disentangler is preparation of the reduced `A` state from
the literal `M union C` erasure.  Both erasure equalities below use the
concrete support witness of that same disentangler.
-/
private theorem recursion_preparation_cover_erasure
    (M : BPTCommutingProjectorModel L kappa)
    (region inside outside : Finset L.Site)
    (hinside : inside ⊆ region) (houtside : outside ⊆ regionᶜ)
    (hboundary : M.boundary region ⊆ inside ∪ outside)
    (unitary : UnitaryTransport L.Register L.Register)
    (regionalState : (M.regionSubsystem region).selectedSystem)
    (complementProjector : Operator (M.regionSubsystem region).complementSystem)
    (unitary_supported : M.UnitarySupportedOn (M.boundary region) unitary)
    (regionalState_normalized : ‖regionalState‖ = 1)
    (projector_factorization :
      unitary.conjOperator M.fullCodeProjector =
        M.pureFactorTensorComplementProjector region regionalState complementProjector)
    (rho : DensityOperator L.Register)
    (hsupported : DensityOperator.SupportedOn M.codeSpace rho) :
    let A := M.regionSubsystem (region \ inside)
    let BC := M.regionSubsystem (inside ∪ outside)
    let target := BPTEntropy.QuditSubsystem.unionSubsystem A BC
    recursionPreparation M region inside outside hinside houtside regionalState regionalState_normalized
      (target.erasureChannelFromRegister rho.toOperator) =
      BC.erasureChannelFromRegister (unitary.conjOperator rho.toOperator) := by
  dsimp
  let A := M.regionSubsystem (region \ inside)
  let BC := M.regionSubsystem (inside ∪ outside)
  have hdisjoint : Disjoint A.selected BC.selected := by
    rw [Finset.disjoint_left]
    intro site hA hBC
    rcases Finset.mem_union.mp hBC with hinsideSite | houtsideSite
    · exact (Finset.mem_sdiff.mp hA).2 hinsideSite
    · exact (Finset.mem_compl.mp (houtside houtsideSite)) (Finset.mem_sdiff.mp hA).1
  have htarget_supported : M.UnitarySupportedOn
      ((region \ inside) ∪ (inside ∪ outside)) unitary :=
    unitarySupportedOn_of_subset M (M.boundary region)
      ((region \ inside) ∪ (inside ∪ outside))
      (fun site hsite => Finset.mem_union_right _ (hboundary hsite)) unitary_supported
  have hcover_supported : M.UnitarySupportedOn (inside ∪ outside) unitary :=
    unitarySupportedOn_of_subset M (M.boundary region) (inside ∪ outside)
      hboundary unitary_supported
  unfold recursionPreparation
  simp only [QuantumChannel.comp_apply, QuantumChannel.unitaryConj_apply]
  rw [← Semantics.UnitaryTransport.symm_conjOperator_conjOperator
    (BPTEntropy.QuditSubsystem.complementBACFactorization A BC hdisjoint)
    (BC.erasureChannelFromRegister (unitary.conjOperator rho.toOperator))]
  congr 1
  rw [prepareLeft_apply]
  have hcoordinates := recursion_cover_erasure_coordinates M region inside outside hinside houtside
    (unitary.conjOperator rho.toOperator)
  rw [hcoordinates]
  rw [← disentangled_prepareSelected_fixed M region unitary regionalState complementProjector
    unitary_supported regionalState_normalized projector_factorization rho hsupported]
  rw [recursionFourFactor_conj_prepareSelected M region inside outside hinside regionalState
    regionalState_normalized]
  rw [traceBCToAD_tensorMap]
  rw [recursionCDOperator_traceC_eq_target_erasure M region inside outside hinside
    (unitary.conjOperator rho.toOperator)]
  rw [erasureChannelFromRegister_conjOperator_eq_of_supported
    (recursionABC M region inside outside) unitary htarget_supported rho.toOperator]
  rfl

/--
The actual external projector boundary is recoverable whenever a recoverable
boundary-cover region contains it.  This is the exact monotonicity bridge for
the merged Disentangling Lemma, not a cardinality or graph-closure argument.
-/
theorem externalBoundary_recoverable_of_boundary_cover
    (M : BPTCommutingProjectorModel L kappa) (region cover : Finset L.Site)
    (hcover : M.RegionErasureRecoverable cover)
    (hboundary : M.boundary region ⊆ cover) :
    M.RegionErasureRecoverable (M.externalBoundary region) := by
  apply (M.regionSubsystem (M.externalBoundary region)).erasureRecoverableFromRegister_mono
    (M.regionSubsystem cover) ?_ M.codeSpace hcover
  simp only [M.regionSubsystem_selected, externalBoundary]
  intro site hsite
  exact hboundary (Finset.mem_sdiff.mp hsite).1

/--
BPT Corollary `cor:recursion` (`2Dgeneral_codes08.tex:454-459`).

For the source partition `A = M \\ B`, `B`, `C`,
`D = (M union C)^c`, compose the concrete preparation bridge with the typed
`B union C` recovery.  The only use of #388 is its actual boundary-supported
unitary and projector factorization, exposed through
`disentangled_prepareSelected_fixed`.
-/
theorem regionErasureRecoverable_union_of_boundary_cover
    (M : BPTCommutingProjectorModel L kappa)
    (region inside outside : Finset L.Site)
    (hregion : M.RegionErasureRecoverable region)
    (hinside : inside ⊆ region)
    (houtside : outside ⊆ regionᶜ)
    (hcover : M.RegionErasureRecoverable (inside ∪ outside))
    (hboundary : M.boundary region ⊆ inside ∪ outside) :
    M.RegionErasureRecoverable (region ∪ outside) := by
  have hexternal : M.RegionErasureRecoverable (M.externalBoundary region) :=
    M.externalBoundary_recoverable_of_boundary_cover region (inside ∪ outside) hcover hboundary
  have hdisentangled :=
    M.disentangled_of_region_and_externalBoundary_recoverable region hregion hexternal
  rcases hdisentangled with
    ⟨unitary, regionalState, complementProjector, hunitary, hregionalState,
      hcomplementProjector, hfactorization⟩
  let A := M.regionSubsystem (region \ inside)
  let BC := M.regionSubsystem (inside ∪ outside)
  let target := BPTEntropy.QuditSubsystem.unionSubsystem A BC
  have htargetEq := recursion_unionSubsystem_eq_target M region inside outside hinside
  have hcover_supported : M.UnitarySupportedOn (inside ∪ outside) unitary :=
    unitarySupportedOn_of_subset M (M.boundary region) (inside ∪ outside) hboundary hunitary
  have htargetRecovery : target.ErasureRecoverableFromRegister M.codeSpace := by
    change BC.ErasureRecoverableFromRegister M.codeSpace at hcover
    rcases hcover with ⟨recovery, hrecovery⟩
    change Correctable L.Register BC.complementSystem M.codeSpace
      BC.erasureChannelFromRegister recovery at hrecovery
    refine ⟨QuantumChannel.comp recovery
      (recursionPreparation M region inside outside hinside houtside regionalState hregionalState), ?_⟩
    intro rho hsupported
    rw [QuantumChannel.comp_apply]
    rw [recursion_preparation_cover_erasure M region inside outside hinside houtside hboundary
      unitary regionalState complementProjector hunitary hregionalState hfactorization rho hsupported]
    rw [erasureChannelFromRegister_conjOperator_eq_of_supported BC unitary hcover_supported
      rho.toOperator]
    exact hrecovery rho hsupported
  change (M.regionSubsystem (region ∪ outside)).ErasureRecoverableFromRegister M.codeSpace
  exact htargetEq ▸ htargetRecovery

end BPTCommutingProjectorModel
end Bounds
end QEC
