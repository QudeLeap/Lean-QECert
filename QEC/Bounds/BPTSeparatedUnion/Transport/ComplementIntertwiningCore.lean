import QEC.Bounds.BPTSeparatedUnion.Transport.TensorCoordinates

/-!
# Complement-coordinate intertwining core

The tensor-coordinate calculation is independent of BPT sectors.  Keeping it
generic prevents downstream transport declarations from elaborating a concrete
dependent embedding merely to move a residual final-factor operator.
-/

noncomputable section

namespace QEC
namespace Bounds

open scoped TensorProduct

universe u

set_option maxHeartbeats 180000 in
set_option synthInstance.maxHeartbeats 60000 in
theorem complementEmbedding_intertwines_coordinates
    {W N C D H : Type u}
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    (split : Semantics.UnitaryTransport H (Semantics.CompositeSystem C D))
    (eC : Semantics.CompositeSystem W N →ₗ[Complex] C)
    (Z : Semantics.Operator D) :
    let reassociate := BPTCommutingProjectorModel.tensorAssociatorUnitary W N D
    let J := TensorProduct.map eC (1 : Semantics.Operator D)
    let Ecd := J.comp reassociate.symm.toLinearEquiv.toLinearMap
    let P : Semantics.Operator (Semantics.CompositeSystem C D) :=
      TensorProduct.map (1 : Semantics.Operator C) Z
    let Pin : Semantics.Operator (Semantics.CompositeSystem W
        (Semantics.CompositeSystem N D)) :=
      TensorProduct.map (1 : Semantics.Operator W)
        (TensorProduct.map (1 : Semantics.Operator N) Z)
    (split.symm.conjOperator P).comp
        (split.symm.toLinearEquiv.toLinearMap.comp Ecd) =
      (split.symm.toLinearEquiv.toLinearMap.comp Ecd).comp Pin := by
  dsimp
  let reassociate := BPTCommutingProjectorModel.tensorAssociatorUnitary W N D
  let J := TensorProduct.map eC (1 : Semantics.Operator D)
  let Ecd := J.comp reassociate.symm.toLinearEquiv.toLinearMap
  let P : Semantics.Operator (Semantics.CompositeSystem C D) :=
    TensorProduct.map (1 : Semantics.Operator C) Z
  let Pmid : Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem W N) D) :=
    TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem W N)) Z
  let Pin : Semantics.Operator (Semantics.CompositeSystem W
      (Semantics.CompositeSystem N D)) :=
    TensorProduct.map (1 : Semantics.Operator W)
      (TensorProduct.map (1 : Semantics.Operator N) Z)
  have hOuter : (split.symm.conjOperator P).comp
      split.symm.toLinearEquiv.toLinearMap =
      split.symm.toLinearEquiv.toLinearMap.comp P := by
    unfold Semantics.UnitaryTransport.conjOperator
    simp only [LinearMap.comp_assoc]
    simp
  have hTensor : P.comp J = J.comp Pmid := by
    apply LinearMap.ext
    intro vector
    induction vector using TensorProduct.induction_on with
    | zero => rfl
    | tmul wn d =>
        induction wn using TensorProduct.induction_on with
        | zero => rfl
        | tmul w n => rfl
        | add first second hfirst hsecond =>
            simpa only [TensorProduct.add_tmul, map_add] using
              congrArg₂ (· + ·) hfirst hsecond
    | add first second hfirst hsecond =>
        simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond
  have hAssociator : Pmid.comp reassociate.symm.toLinearEquiv.toLinearMap =
      reassociate.symm.toLinearEquiv.toLinearMap.comp Pin := by
    simpa [Pmid, Pin, reassociate] using
      (tensorAssociator_symm_right_intertwines
        (H := W) (K := N) Z)
  have hEcd : P.comp Ecd = Ecd.comp Pin := by
    calc
      P.comp Ecd = (P.comp J).comp reassociate.symm.toLinearEquiv.toLinearMap := by
        rfl
      _ = (J.comp Pmid).comp reassociate.symm.toLinearEquiv.toLinearMap := by
        rw [hTensor]
      _ = J.comp (Pmid.comp reassociate.symm.toLinearEquiv.toLinearMap) := by
        rw [← LinearMap.comp_assoc]
      _ = J.comp (reassociate.symm.toLinearEquiv.toLinearMap.comp Pin) := by
        rw [hAssociator]
      _ = Ecd.comp Pin := by
        rfl
  calc
    (split.symm.conjOperator P).comp
        (split.symm.toLinearEquiv.toLinearMap.comp Ecd) =
      (split.symm.toLinearEquiv.toLinearMap.comp P).comp Ecd := by
        rw [← LinearMap.comp_assoc, hOuter]
    _ = split.symm.toLinearEquiv.toLinearMap.comp (P.comp Ecd) := by
      rw [LinearMap.comp_assoc]
    _ = split.symm.toLinearEquiv.toLinearMap.comp (Ecd.comp Pin) := by
      rw [hEcd]
    _ = (split.symm.toLinearEquiv.toLinearMap.comp Ecd).comp Pin := by
      rw [← LinearMap.comp_assoc]

end Bounds
end QEC
