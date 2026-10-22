import QEC.Bounds.BPTDisentangling.Joint.Sequential.Compression

/-!
# BPT transport-compatible factorization core

Internal proof layer for the finite-dimensional BPT Disentangling Lemma.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u

namespace BPTCommutingProjectorModel

/--
Transport-compatible realizations of one operator block determine the common
rank-one factorization.  This isolates the model-independent transport step
from the large BPT sector types used to instantiate it.
-/
theorem commonFactorization_of_transport_equivalent_blocks
    {X Y A B C D : Type u}
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup Y] [InnerProductSpace Complex Y] [Semantics.FiniteQuantumSystem Y]
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (V : Semantics.UnitaryTransport X Y)
    (Gsecond : Semantics.UnitaryTransport Y
      (Semantics.CompositeSystem A
        (Semantics.CompositeSystem (Semantics.CompositeSystem B C) D)))
    (Gfirst : Semantics.UnitaryTransport X
      (Semantics.CompositeSystem A
        (Semantics.CompositeSystem (Semantics.CompositeSystem B C) D)))
    (Rsecond : Semantics.Operator Y) (Rfirst : Semantics.Operator X)
    (phi : A) (hphi : ‖phi‖ = 1)
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem A (Semantics.CompositeSystem B C)))
    (Qright : Semantics.Operator
      (Semantics.CompositeSystem B (Semantics.CompositeSystem C D)))
    (P_D : Semantics.Operator D)
    (hsequential : Rsecond = V.conjOperator Rfirst)
    (htransport : composeUnitaryTransport V Gsecond = Gfirst)
    (hsecond :
      Gsecond.conjOperator Rsecond =
        (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).conjOperator
          (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright))
    (hfirst :
      Gfirst.conjOperator Rfirst =
        (tensorAssociatorUnitary A (Semantics.CompositeSystem B C) D).conjOperator
          (TensorProduct.map Pleft P_D)) :
    (tensorAssociatorUnitary B C D).symm.conjOperator Qright =
      TensorProduct.map (leftTensorCompression phi Pleft) P_D := by
  have hjoint :
      (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).conjOperator
          (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright) =
        (tensorAssociatorUnitary A (Semantics.CompositeSystem B C) D).conjOperator
          (TensorProduct.map Pleft P_D) := by
    calc
      _ = Gsecond.conjOperator Rsecond := hsecond.symm
      _ = Gsecond.conjOperator (V.conjOperator Rfirst) :=
        congrArg Gsecond.conjOperator hsequential
      _ = (composeUnitaryTransport V Gsecond).conjOperator Rfirst :=
        (composeUnitaryTransport_conjOperator V Gsecond Rfirst).symm
      _ = Gfirst.conjOperator Rfirst :=
        congrArg (fun transport => transport.conjOperator Rfirst) htransport
      _ = _ := hfirst
  exact tensor_factor_eq_of_rankOne_joint_block_associator
    phi hphi Pleft Qright P_D hjoint

end BPTCommutingProjectorModel

end Bounds
end QEC
