import QEC.Bounds.BPTDisentangling.NoCloning.Core

/-!
# BPT final coordinate transport

Cacheable tensor-coordinate intertwining used by the physical disentangling
assembly.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

-- Internal cache boundary; do not index its large dependent type as an automated premise.
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "secondCutActiveCoordinateTransport_intertwinesCore"

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- The selected middle action is the literal `N tensor X` coordinate action. -/
theorem secondCutActiveCoordinateTransport_intertwinesCore
    {A B C D W N X N2 : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup N2] [InnerProductSpace Complex N2] [Semantics.FiniteQuantumSystem N2]
    {pB : Submodule Complex B} {pC : Submodule Complex C}
    (UB : Semantics.UnitaryTransport pB (Semantics.CompositeSystem W N))
    (UC : Semantics.UnitaryTransport pC (Semantics.CompositeSystem X N2))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem N X)
      (Semantics.CompositeSystem N X)) :
    let T := composeUnitaryTransport
      (isotypicSectorBlockTransportLeft A pB W N (Semantics.CompositeSystem pC D) UB)
      (composeUnitaryTransport
        (unitaryLTensor (Semantics.CompositeSystem A W)
          (unitaryLTensor N
            (composeUnitaryTransport (unitaryRTensor UC D)
              (tensorAssociatorUnitary X N2 D))))
        (unitaryLTensor (Semantics.CompositeSystem A W)
          (tensorAssociatorUnitary N X (Semantics.CompositeSystem N2 D)).symm))
    T.toLinearEquiv.toLinearMap.comp
        (jointBCSectorActiveUnitary (A := A) pB pC
          (activeSectorJointBCUnitary pB pC UB UC U)).toLinearEquiv.toLinearMap =
      (unitaryLTensor (Semantics.CompositeSystem A W)
        (unitaryRTensor U (Semantics.CompositeSystem N2 D))).toLinearEquiv.toLinearMap.comp
        T.toLinearEquiv.toLinearMap := by
  dsimp
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul ab cd =>
      induction ab using TensorProduct.induction_on with
      | zero => simp only [map_zero, TensorProduct.zero_tmul]
      | tmul a b =>
          induction cd using TensorProduct.induction_on with
          | zero => simp only [map_zero, TensorProduct.tmul_zero]
          | tmul c d =>
              rcases UB.symm.toLinearEquiv.surjective b with ⟨wn, hwn⟩
              subst b
              rcases UC.symm.toLinearEquiv.surjective c with ⟨xn, hxn⟩
              subst c
              induction wn using TensorProduct.induction_on with
              | zero =>
                  simp [jointBCSectorActiveUnitary, activeSectorJointBCUnitary,
                    activeSectorCoordinateTransport, jointBCSectorMiddleTransport,
                    conjugateUnitaryTransport_apply, isotypicSectorBlockTransportLeft,
                    composeUnitaryTransport, unitaryRTensor, unitaryLTensor,
                    tensorAssociatorUnitary]
              | tmul w n =>
                  induction xn using TensorProduct.induction_on with
                  | zero =>
                      simp [jointBCSectorActiveUnitary, activeSectorJointBCUnitary,
                        activeSectorCoordinateTransport, jointBCSectorMiddleTransport,
                        conjugateUnitaryTransport_apply, isotypicSectorBlockTransportLeft,
                        composeUnitaryTransport, unitaryRTensor, unitaryLTensor,
                        tensorAssociatorUnitary]
                  | tmul x n2 =>
                      simp [jointBCSectorActiveUnitary, activeSectorJointBCUnitary,
                        activeSectorCoordinateTransport, jointBCSectorMiddleTransport,
                        conjugateUnitaryTransport_apply, isotypicSectorBlockTransportLeft,
                        composeUnitaryTransport, unitaryRTensor, unitaryLTensor,
                        tensorAssociatorUnitary]
                      generalize hUvector : U.toLinearEquiv (n ⊗ₜ[Complex] x) = Uvector
                      clear hUvector
                      induction Uvector using TensorProduct.induction_on with
                      | zero =>
                          simp [jointBCSectorActiveUnitary, activeSectorJointBCUnitary,
                            activeSectorCoordinateTransport, jointBCSectorMiddleTransport,
                            conjugateUnitaryTransport_apply, isotypicSectorBlockTransportLeft,
                            composeUnitaryTransport, unitaryRTensor, unitaryLTensor,
                            tensorAssociatorUnitary]
                      | tmul n' x' =>
                          simp [jointBCSectorActiveUnitary, activeSectorJointBCUnitary,
                            activeSectorCoordinateTransport, jointBCSectorMiddleTransport,
                            conjugateUnitaryTransport_apply, isotypicSectorBlockTransportLeft,
                            composeUnitaryTransport, unitaryRTensor, unitaryLTensor,
                            tensorAssociatorUnitary]
                      | add first second hfirst hsecond =>
                          simpa only [map_add, TensorProduct.tmul_add,
                            TensorProduct.add_tmul] using congrArg₂ (· + ·) hfirst hsecond
                  | add first second hfirst hsecond =>
                      simpa only [map_add, TensorProduct.tmul_add,
                        TensorProduct.add_tmul] using congrArg₂ (· + ·) hfirst hsecond
              | add first second hfirst hsecond =>
                  simpa only [map_add, TensorProduct.tmul_add,
                    TensorProduct.add_tmul] using congrArg₂ (· + ·) hfirst hsecond
          | add first second hfirst hsecond =>
              simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hfirst hsecond
      | add first second hfirst hsecond =>
          simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hfirst hsecond
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

end BPTCommutingProjectorModel

end Bounds
end QEC
