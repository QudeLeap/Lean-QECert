import QEC.Bounds.BPTDisentangling.Joint.Regrouping

/-!
# BPT joint-sector compression transport

Internal proof layer for the finite-dimensional BPT Disentangling Lemma.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/--
The physical first/second-cut associator intertwines the two simultaneous
sector embeddings.  This makes the joint compressed code block a concrete
operator independent of whether it is reached from the first or second cut.
-/
theorem tensorAssociatorUnitary_comp_jointBCSectorEmbeddingLeft
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C) :
    (tensorAssociatorUnitary (Semantics.CompositeSystem A B) C D).toLinearEquiv.toLinearMap.comp
        (jointBCSectorEmbeddingLeft pB pC) =
      (jointBCSectorEmbeddingRight pB pC).comp
        (tensorAssociatorUnitary (Semantics.CompositeSystem A pB) pC D).toLinearEquiv.toLinearMap := by
  let leftMap :=
    (tensorAssociatorUnitary (Semantics.CompositeSystem A B) C D).toLinearEquiv.toLinearMap.comp
      (jointBCSectorEmbeddingLeft pB pC)
  let rightMap :=
    (jointBCSectorEmbeddingRight pB pC).comp
      (tensorAssociatorUnitary
        (Semantics.CompositeSystem A pB) pC D).toLinearEquiv.toLinearMap
  change leftMap = rightMap
  apply LinearMap.ext
  intro vector
  change leftMap vector = rightMap vector
  induction vector using TensorProduct.induction_on with
  | zero => exact leftMap.map_zero.trans rightMap.map_zero.symm
  | tmul abc d =>
      induction abc using TensorProduct.induction_on with
      | zero =>
          simpa only [TensorProduct.zero_tmul] using
            leftMap.map_zero.trans rightMap.map_zero.symm
      | tmul ab c =>
          induction ab using TensorProduct.induction_on with
          | zero =>
              simpa only [TensorProduct.zero_tmul] using
                leftMap.map_zero.trans rightMap.map_zero.symm
          | tmul a b => rfl
          | add first second hfirst hsecond =>
              simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hfirst hsecond
      | add first second hfirst hsecond =>
          simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hfirst hsecond
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

set_option maxHeartbeats 4000000 in
/--
Compressing a real four-factor operator to both active boundary sectors
commutes with the physical first/second-cut reassociation.  This is an
operator equality, not a support statement: it is the common block on which
the two source tensor factorizations are compared.
-/
theorem jointBCSectorCompression_conj_tensorAssociator
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (T : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem (Semantics.CompositeSystem A B) C) D)) :
    let U := tensorAssociatorUnitary (Semantics.CompositeSystem A B) C D
    let V := tensorAssociatorUnitary (Semantics.CompositeSystem A pB) pC D
    let Jleft := jointBCSectorEmbeddingLeft pB pC
    let Jright := jointBCSectorEmbeddingRight pB pC
    (LinearMap.adjoint Jright).comp ((U.conjOperator T).comp Jright) =
      V.conjOperator ((LinearMap.adjoint Jleft).comp (T.comp Jleft)) := by
  dsimp
  let U := tensorAssociatorUnitary (Semantics.CompositeSystem A B) C D
  let V := tensorAssociatorUnitary (Semantics.CompositeSystem A pB) pC D
  let Jleft := jointBCSectorEmbeddingLeft (A := A) (D := D) pB pC
  let Jright := jointBCSectorEmbeddingRight (A := A) (D := D) pB pC
  have hUV : U.toLinearEquiv.toLinearMap.comp Jleft =
      Jright.comp V.toLinearEquiv.toLinearMap := by
    simpa [U, V, Jleft, Jright] using
      tensorAssociatorUnitary_comp_jointBCSectorEmbeddingLeft (A := A) pB pC
  have hleft : U.symm.toLinearEquiv.toLinearMap.comp Jright =
      Jleft.comp V.symm.toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    intro vector
    calc
      U.symm.toLinearEquiv.toLinearMap (Jright vector) =
          U.symm.toLinearEquiv.toLinearMap
            (U.toLinearEquiv.toLinearMap
              (Jleft (V.symm.toLinearEquiv.toLinearMap vector))) := by
        have happly := congrArg (fun map => map (V.symm.toLinearEquiv.toLinearMap vector)) hUV
        simpa [LinearMap.comp_apply] using congrArg U.symm.toLinearEquiv.toLinearMap happly.symm
      _ = Jleft (V.symm.toLinearEquiv.toLinearMap vector) := by simp
  have hleft' : U.toLinearEquiv.symm.toLinearMap.comp Jright =
      Jleft.comp V.toLinearEquiv.symm.toLinearMap := by
    simpa only [← Semantics.UnitaryTransport.symm_toLinearEquiv] using hleft
  have hUadj : LinearMap.adjoint U.symm.toLinearEquiv.toLinearMap = U.toLinearEquiv.toLinearMap := by
    simpa [Semantics.UnitaryTransport.symm_toLinearEquiv] using
      (Semantics.UnitaryTransport.adjoint_toLinearMap U.symm)
  have hVadj : LinearMap.adjoint V.symm.toLinearEquiv.toLinearMap = V.toLinearEquiv.toLinearMap := by
    simpa [Semantics.UnitaryTransport.symm_toLinearEquiv] using
      (Semantics.UnitaryTransport.adjoint_toLinearMap V.symm)
  have hright : (LinearMap.adjoint Jright).comp U.toLinearEquiv.toLinearMap =
      V.toLinearEquiv.toLinearMap.comp (LinearMap.adjoint Jleft) := by
    have hadj := congrArg LinearMap.adjoint hleft
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, hUadj, hVadj] at hadj
    exact hadj
  unfold Semantics.UnitaryTransport.conjOperator
  change (LinearMap.adjoint Jright).comp
      ((U.toLinearEquiv.toLinearMap.comp
        (T.comp U.toLinearEquiv.symm.toLinearMap)).comp Jright) =
      V.toLinearEquiv.toLinearMap.comp
        (((LinearMap.adjoint Jleft).comp (T.comp Jleft)).comp
          V.toLinearEquiv.symm.toLinearMap)
  calc
    (LinearMap.adjoint Jright).comp
        ((U.toLinearEquiv.toLinearMap.comp
          (T.comp U.toLinearEquiv.symm.toLinearMap)).comp Jright) =
        ((LinearMap.adjoint Jright).comp U.toLinearEquiv.toLinearMap).comp
          (T.comp (U.toLinearEquiv.symm.toLinearMap.comp Jright)) := by
      simp only [LinearMap.comp_assoc]
    _ = (V.toLinearEquiv.toLinearMap.comp (LinearMap.adjoint Jleft)).comp
          (T.comp (Jleft.comp V.toLinearEquiv.symm.toLinearMap)) := by
      rw [hright, hleft']
    _ = V.toLinearEquiv.toLinearMap.comp
        (((LinearMap.adjoint Jleft).comp (T.comp Jleft)).comp
          V.toLinearEquiv.symm.toLinearMap) := by
      simp only [LinearMap.comp_assoc]

set_option maxHeartbeats 4000000 in
/--
The common first/second-cut block equality for the actual BPT code lift.
Both sides are literal simultaneous `B,C` sector compressions of the same
full code projector, expressed in their respective block parenthesizations.
-/
theorem jointBCSectorCompression_secondCutCodeLift_eq_firstCutCodeLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    let A := M.fourFactorA region
    let D := M.fourFactorD region
    let V := tensorAssociatorUnitary (Semantics.CompositeSystem A pB) pC D
    let Jleft := jointBCSectorEmbeddingLeft (A := A) pB pC
    let Jright := jointBCSectorEmbeddingRight (A := A) pB pC
    (LinearMap.adjoint Jright).comp ((M.secondCutCodeLift region).comp Jright) =
      V.conjOperator ((LinearMap.adjoint Jleft).comp ((M.firstCutCodeLift region).comp Jleft)) := by
  dsimp
  let A := M.fourFactorA region
  let D := M.fourFactorD region
  let U := tensorAssociatorUnitary
    (Semantics.CompositeSystem A (M.fourFactorB region)) (M.fourFactorC region) D
  let V := tensorAssociatorUnitary (Semantics.CompositeSystem A pB) pC D
  let Jleft := jointBCSectorEmbeddingLeft (A := A) (D := D) pB pC
  let Jright := jointBCSectorEmbeddingRight (A := A) (D := D) pB pC
  have hcode : U.conjOperator (M.firstCutCodeLift region) = M.secondCutCodeLift region := by
    simpa [A, D, U] using M.secondCutCodeLift_eq_reassociate_firstCutCodeLift region
  calc
    (LinearMap.adjoint Jright).comp ((M.secondCutCodeLift region).comp Jright) =
        (LinearMap.adjoint Jright).comp ((U.conjOperator (M.firstCutCodeLift region)).comp Jright) := by
      rw [hcode]
    _ = V.conjOperator
        ((LinearMap.adjoint Jleft).comp ((M.firstCutCodeLift region).comp Jleft)) := by
      simpa [A, D, U, V, Jleft, Jright] using
        jointBCSectorCompression_conj_tensorAssociator
          (A := A) (B := M.fourFactorB region) (C := M.fourFactorC region)
          (D := D) pB pC (M.firstCutCodeLift region)



end BPTCommutingProjectorModel

end Bounds
end QEC
