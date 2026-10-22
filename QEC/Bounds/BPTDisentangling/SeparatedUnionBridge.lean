import QEC.Bounds.BPTDisentangling.Assembly.AssemblyTransport

/-!
# BPT separated-union factorization bridge

This companion to the final BPT assembly exposes the elementary rank-one
calculation used by the source union lemma.  It intentionally states only the
finite-dimensional coordinate fact: concrete locality of the two probes is
provided by the separated-union theorem, while the fixed-active product from
the #388 construction supplies the rank-one projector.
-/

noncomputable section

namespace QEC
namespace Bounds
namespace BPTCommutingProjectorModel

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u

/-- Sandwiching an operator by a normalized rank-one projector is scalar on that line. -/
theorem rankOne_sandwich
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    (phi : H) (hphi : ‖phi‖ = 1) (A : Semantics.Operator H) :
    (InnerProductSpace.rankOne Complex phi phi).toLinearMap * A *
        (InnerProductSpace.rankOne Complex phi phi).toLinearMap =
      (inner Complex phi (A phi)) •
        (InnerProductSpace.rankOne Complex phi phi).toLinearMap := by
  have hinner : inner Complex phi phi = 1 := by
    rw [inner_self_eq_norm_sq_to_K]
    simpa [hphi]
  ext vector
  simp [Module.End.mul_eq_comp, LinearMap.comp_apply,
    InnerProductSpace.rankOne_apply, hinner]
  module

/-- The source rank-one sandwich calculation in two concrete tensor factors. -/
theorem rankOneTensor_sourceFactorization
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (phi : H) (hphi : ‖phi‖ = 1) (Q : Semantics.Operator K)
    (A : Semantics.Operator H) (B : Semantics.Operator K) :
    let rankOne := (InnerProductSpace.rankOne Complex phi phi).toLinearMap
    let codeProjector := TensorProduct.map rankOne Q
    codeProjector * TensorProduct.map A (1 : Semantics.Operator K) *
        TensorProduct.map (1 : Semantics.Operator H) B * codeProjector =
      (inner Complex phi (A phi)) •
        (codeProjector * TensorProduct.map (1 : Semantics.Operator H) B *
          codeProjector) := by
  dsimp
  let rankOne := (InnerProductSpace.rankOne Complex phi phi).toLinearMap
  have hsandwich : rankOne * A * rankOne =
      (inner Complex phi (A phi)) • rankOne := by
    simpa [rankOne] using rankOne_sandwich phi hphi A
  have hidempotent : rankOne * rankOne = rankOne := by
    simpa [rankOne, hphi] using rankOne_sandwich phi hphi (1 : Semantics.Operator H)
  have tensorMap_mul (f₁ f₂ : Semantics.Operator H) (g₁ g₂ : Semantics.Operator K) :
      TensorProduct.map f₁ g₁ * TensorProduct.map f₂ g₂ =
        TensorProduct.map (f₁ * f₂) (g₁ * g₂) := by
    simp only [Module.End.mul_eq_comp]
    rw [← TensorProduct.map_comp]
  have hright : TensorProduct.map rankOne Q *
      TensorProduct.map (1 : Semantics.Operator H) B * TensorProduct.map rankOne Q =
      TensorProduct.map rankOne (Q * B * Q) := by
    calc
      TensorProduct.map rankOne Q * TensorProduct.map (1 : Semantics.Operator H) B *
          TensorProduct.map rankOne Q =
        TensorProduct.map (rankOne * (1 : Semantics.Operator H)) (Q * B) *
          TensorProduct.map rankOne Q := by
            rw [tensorMap_mul]
      _ = TensorProduct.map ((rankOne * (1 : Semantics.Operator H)) * rankOne)
          ((Q * B) * Q) := by
            rw [tensorMap_mul]
      _ = TensorProduct.map rankOne (Q * B * Q) := by
            simpa [hidempotent, mul_assoc]
  calc
    TensorProduct.map rankOne Q * TensorProduct.map A (1 : Semantics.Operator K) *
        TensorProduct.map (1 : Semantics.Operator H) B * TensorProduct.map rankOne Q =
      TensorProduct.map (rankOne * A) (Q * (1 : Semantics.Operator K)) *
        TensorProduct.map (1 : Semantics.Operator H) B * TensorProduct.map rankOne Q := by
          rw [tensorMap_mul]
    _ = TensorProduct.map ((rankOne * A) * (1 : Semantics.Operator H))
        ((Q * (1 : Semantics.Operator K)) * B) * TensorProduct.map rankOne Q := by
          rw [tensorMap_mul]
    _ = TensorProduct.map (((rankOne * A) * (1 : Semantics.Operator H)) * rankOne)
        (((Q * (1 : Semantics.Operator K)) * B) * Q) := by
          rw [tensorMap_mul]
    _ = TensorProduct.map (rankOne * A * rankOne) (Q * B * Q) := by
      simp [mul_assoc]
    _ = TensorProduct.map ((inner Complex phi (A phi)) • rankOne) (Q * B * Q) := by
      rw [hsandwich]
    _ = (inner Complex phi (A phi)) • TensorProduct.map rankOne (Q * B * Q) := by
      rw [TensorProduct.map_smul_left]
    _ = (inner Complex phi (A phi)) •
        (TensorProduct.map rankOne Q * TensorProduct.map (1 : Semantics.Operator H) B *
          TensorProduct.map rankOne Q) := by rw [hright]

/-- Compressing a left tensor action through two isometric embeddings leaves the right identity. -/
theorem tensorEmbedding_compression_left
    {H K H' K' : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K] [NormedAddCommGroup H'] [InnerProductSpace Complex H']
    [Semantics.FiniteQuantumSystem H'] [NormedAddCommGroup K'] [InnerProductSpace Complex K']
    [Semantics.FiniteQuantumSystem K']
    (eH : H →ₗ[Complex] H') (eK : K →ₗ[Complex] K')
    (heK : (LinearMap.adjoint eK).comp eK = (1 : Semantics.Operator K))
    (A : Semantics.Operator H') :
    (LinearMap.adjoint (TensorProduct.map eH eK)).comp
        ((TensorProduct.map A (1 : Semantics.Operator K')).comp
          (TensorProduct.map eH eK)) =
      TensorProduct.map ((LinearMap.adjoint eH).comp (A.comp eH))
        (1 : Semantics.Operator K) := by
  rw [TensorProduct.adjoint_map]
  rw [← TensorProduct.map_comp]
  rw [← TensorProduct.map_comp]
  simpa only [Module.End.one_eq_id, LinearMap.id_comp] using congrArg
    (TensorProduct.map ((LinearMap.adjoint eH).comp (A.comp eH))) heK

/-- Compressing a right tensor action through two isometric embeddings leaves the left identity. -/
theorem tensorEmbedding_compression_right
    {H K H' K' : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K] [NormedAddCommGroup H'] [InnerProductSpace Complex H']
    [Semantics.FiniteQuantumSystem H'] [NormedAddCommGroup K'] [InnerProductSpace Complex K']
    [Semantics.FiniteQuantumSystem K']
    (eH : H →ₗ[Complex] H') (eK : K →ₗ[Complex] K')
    (heH : (LinearMap.adjoint eH).comp eH = (1 : Semantics.Operator H))
    (B : Semantics.Operator K') :
    (LinearMap.adjoint (TensorProduct.map eH eK)).comp
        ((TensorProduct.map (1 : Semantics.Operator H') B).comp
          (TensorProduct.map eH eK)) =
      TensorProduct.map (1 : Semantics.Operator H)
        ((LinearMap.adjoint eK).comp (B.comp eK)) := by
  rw [TensorProduct.adjoint_map]
  rw [← TensorProduct.map_comp]
  rw [← TensorProduct.map_comp]
  simpa only [Module.End.one_eq_id, LinearMap.id_comp] using congrArg
    (fun map => TensorProduct.map map ((LinearMap.adjoint eK).comp (B.comp eK))) heH

/-- Precomposing an embedding by a unitary conjugates its compressed operator. -/
theorem compression_precompose_unitary
    {S H K : Type u} [NormedAddCommGroup S] [InnerProductSpace Complex S]
    [Semantics.FiniteQuantumSystem S] [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport S H) (J : H →ₗ[Complex] K)
    (P : Semantics.Operator K) :
    (LinearMap.adjoint (J.comp U.toLinearEquiv.toLinearMap)).comp
        (P.comp (J.comp U.toLinearEquiv.toLinearMap)) =
      U.symm.conjOperator ((LinearMap.adjoint J).comp (P.comp J)) := by
  unfold Semantics.UnitaryTransport.conjOperator
  rw [LinearMap.adjoint_comp, U.adjoint_toLinearMap]
  simp [Semantics.UnitaryTransport.symm_toLinearEquiv, LinearMap.comp_assoc]

/-- Move an operator compression across an intertwining of an isometric lift. -/
theorem compression_conjOperator_of_embedding_intertwines
    {S H K : Type u} [NormedAddCommGroup S] [InnerProductSpace Complex S]
    [Semantics.FiniteQuantumSystem S] [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (embedding : S →ₗ[Complex] K) (V : Semantics.UnitaryTransport K K)
    (W : Semantics.UnitaryTransport S S) (P : Semantics.Operator K)
    (hintertwines : V.toLinearEquiv.toLinearMap.comp embedding =
      embedding.comp W.toLinearEquiv.toLinearMap) :
    (LinearMap.adjoint embedding).comp ((V.conjOperator P).comp embedding) =
      W.conjOperator ((LinearMap.adjoint embedding).comp (P.comp embedding)) := by
  have hinverse : V.symm.toLinearEquiv.toLinearMap.comp embedding =
      embedding.comp W.symm.toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    intro vector
    apply V.toLinearEquiv.injective
    have h := congrArg (fun map : S →ₗ[Complex] K =>
      map (W.symm.toLinearEquiv vector)) hintertwines
    simpa [LinearMap.comp_apply] using h.symm
  have hleft : (LinearMap.adjoint embedding).comp V.toLinearEquiv.toLinearMap =
      W.toLinearEquiv.toLinearMap.comp (LinearMap.adjoint embedding) := by
    have hadjoint := congrArg LinearMap.adjoint hinverse
    simpa [LinearMap.adjoint_comp, Semantics.UnitaryTransport.symm_toLinearEquiv,
      V.adjoint_symm_toLinearMap, W.adjoint_symm_toLinearMap] using hadjoint
  have hinverse' : V.toLinearEquiv.symm.toLinearMap.comp embedding =
      embedding.comp W.toLinearEquiv.symm.toLinearMap := by
    simpa [Semantics.UnitaryTransport.symm_toLinearEquiv] using hinverse
  unfold Semantics.UnitaryTransport.conjOperator
  calc
    (LinearMap.adjoint embedding).comp
        ((V.toLinearEquiv.toLinearMap.comp
          (P.comp V.toLinearEquiv.symm.toLinearMap)).comp embedding) =
      ((LinearMap.adjoint embedding).comp V.toLinearEquiv.toLinearMap).comp
        (P.comp (V.toLinearEquiv.symm.toLinearMap.comp embedding)) := by
          simp only [LinearMap.comp_assoc]
    _ = (W.toLinearEquiv.toLinearMap.comp (LinearMap.adjoint embedding)).comp
        (P.comp (embedding.comp W.toLinearEquiv.symm.toLinearMap)) := by
          rw [hleft, hinverse']
    _ = W.toLinearEquiv.toLinearMap.comp
        (((LinearMap.adjoint embedding).comp (P.comp embedding)).comp
          W.toLinearEquiv.symm.toLinearMap) := by
          simp only [LinearMap.comp_assoc]

/-- Invert an intertwining equation between unitary coordinate transports. -/
theorem unitary_intertwining_symm
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (T : Semantics.UnitaryTransport H K) (W : Semantics.UnitaryTransport H H)
    (V : Semantics.UnitaryTransport K K)
    (hintertwines : T.toLinearEquiv.toLinearMap.comp W.toLinearEquiv.toLinearMap =
      V.toLinearEquiv.toLinearMap.comp T.toLinearEquiv.toLinearMap) :
    W.toLinearEquiv.toLinearMap.comp T.symm.toLinearEquiv.toLinearMap =
      T.symm.toLinearEquiv.toLinearMap.comp V.toLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro vector
  apply T.toLinearEquiv.injective
  have h := congrArg (fun map : H →ₗ[Complex] K =>
    map (T.symm.toLinearEquiv vector)) hintertwines
  simpa [LinearMap.comp_apply] using h

/-- A coordinate conjugate intertwines its original and transported unitaries. -/
theorem conjugateUnitaryTransport_intertwines
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (T : Semantics.UnitaryTransport H K) (V : Semantics.UnitaryTransport K K) :
    T.toLinearEquiv.toLinearMap.comp
        (conjugateUnitaryTransport T V).toLinearEquiv.toLinearMap =
      V.toLinearEquiv.toLinearMap.comp T.toLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro vector
  simp [conjugateUnitaryTransport, composeUnitaryTransport,
    LinearMap.comp_apply]

/-- Reassociate an isometric lift together with its compressed projector. -/
theorem reassociated_isometric_lift
    {H K X : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    (T : Semantics.UnitaryTransport H K) (embedding : K →ₗ[Complex] X)
    (P : Semantics.Operator K) :
    let reassociatedEmbedding := embedding.comp T.toLinearEquiv.toLinearMap
    reassociatedEmbedding.comp
        ((T.symm.conjOperator P).comp (LinearMap.adjoint reassociatedEmbedding)) =
      embedding.comp (P.comp (LinearMap.adjoint embedding)) := by
  dsimp
  unfold Semantics.UnitaryTransport.conjOperator
  rw [LinearMap.adjoint_comp, T.adjoint_toLinearMap]
  simp [Semantics.UnitaryTransport.symm_toLinearEquiv, LinearMap.comp_assoc]

/--
The final #388 regrouping carries the active `N tensor X` unitary entirely on
the left of the source split `((S tensor N) tensor X) tensor D`.
-/
theorem finalAssembly_regrouping_intertwines
    {A W N X D : Type u} [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [Semantics.FiniteQuantumSystem A] [NormedAddCommGroup W] [InnerProductSpace Complex W]
    [Semantics.FiniteQuantumSystem W] [NormedAddCommGroup N] [InnerProductSpace Complex N]
    [Semantics.FiniteQuantumSystem N] [NormedAddCommGroup X] [InnerProductSpace Complex X]
    [Semantics.FiniteQuantumSystem X] [NormedAddCommGroup D] [InnerProductSpace Complex D]
    [Semantics.FiniteQuantumSystem D]
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem N X)
      (Semantics.CompositeSystem N X)) :
    let S := Semantics.CompositeSystem A W
    let regrouping := productBlockRegrouping (A := A) (W := W) (N := N) (X := X) (D := D)
    let commonAssociator := tensorAssociatorUnitary S (Semantics.CompositeSystem N X) D
    let commonCoordinates := composeUnitaryTransport regrouping.symm commonAssociator
    let commonUnitary := unitaryLTensor S (unitaryRTensor U D)
    let rawUnitary := conjugateUnitaryTransport commonCoordinates commonUnitary
    let outerAssociator := tensorAssociatorUnitary (Semantics.CompositeSystem S N) X D
    let leftUnitary := conjugateUnitaryTransport
      (tensorAssociatorUnitary S N X) (unitaryLTensor S U)
    rawUnitary.toLinearEquiv.toLinearMap.comp outerAssociator.toLinearEquiv.toLinearMap =
      outerAssociator.toLinearEquiv.toLinearMap.comp
        (unitaryRTensor leftUnitary D).toLinearEquiv.toLinearMap := by
  dsimp
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => rfl
  | tmul snx d =>
      induction snx using TensorProduct.induction_on with
      | zero => rfl
      | tmul sn x =>
          induction sn using TensorProduct.induction_on with
          | zero => rfl
          | tmul s n =>
              rfl
          | add first second hfirst hsecond =>
              simpa only [TensorProduct.add_tmul, map_add] using
                congrArg₂ (· + ·) hfirst hsecond
      | add first second hfirst hsecond =>
          simpa only [TensorProduct.add_tmul, map_add] using
            congrArg₂ (· + ·) hfirst hsecond
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

/-- Reassociating a rank-one selected factor and a rank-one boundary factor. -/
theorem tensorAssociator_symm_conj_rankOneTensor
    {H K J : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K] [NormedAddCommGroup J] [InnerProductSpace Complex J]
    [Semantics.FiniteQuantumSystem J]
    (phi : H) (chi : K) (Q : Semantics.Operator J) :
    (tensorAssociatorUnitary H K J).symm.conjOperator
      (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap
        (TensorProduct.map (InnerProductSpace.rankOne Complex chi chi).toLinearMap Q)) =
      TensorProduct.map
        (InnerProductSpace.rankOne Complex (phi ⊗ₜ[Complex] chi)
          (phi ⊗ₜ[Complex] chi)).toLinearMap Q := by
  rw [tensorAssociatorUnitary_symm_conj_tensorMap]
  rw [Semantics.DensityOperator.tensorMap_rankOne]

/--
The BPT source equation survives a common ambient isometric lift.  The first
probe is supplied as a compression, while the exterior probe has the stronger
range-intertwining identity that prevents an unproved insertion of the range
projection between the two source operators.
-/
theorem sourceFactorization_of_rankOneLift
    {H K X : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    (embedding : Semantics.CompositeSystem H K →ₗ[Complex] X)
    (phi : H) (hphi : ‖phi‖ = 1) (Q : Semantics.Operator K)
    (leftAmbient rightAmbient : Semantics.Operator X)
    (leftLocal : Semantics.Operator H) (rightLocal : Semantics.Operator K)
    (hisometry : (LinearMap.adjoint embedding).comp embedding =
      (1 : Semantics.Operator (Semantics.CompositeSystem H K)))
    (hleft : (LinearMap.adjoint embedding).comp (leftAmbient.comp embedding) =
      TensorProduct.map leftLocal (1 : Semantics.Operator K))
    (hright : rightAmbient.comp embedding = embedding.comp
      (TensorProduct.map (1 : Semantics.Operator H) rightLocal)) :
    let rankOne := (InnerProductSpace.rankOne Complex phi phi).toLinearMap
    let productProjector := TensorProduct.map rankOne Q
    let liftedProjector := embedding.comp (productProjector.comp (LinearMap.adjoint embedding))
    liftedProjector * leftAmbient * rightAmbient * liftedProjector =
      (inner Complex phi (leftLocal phi)) •
        (liftedProjector * rightAmbient * liftedProjector) := by
  dsimp
  let rankOne := (InnerProductSpace.rankOne Complex phi phi).toLinearMap
  let productProjector := TensorProduct.map rankOne Q
  have hproduct := rankOneTensor_sourceFactorization phi hphi Q leftLocal rightLocal
  let rightTensor := TensorProduct.map (1 : Semantics.Operator H) rightLocal
  have hisometry_apply (vector : Semantics.CompositeSystem H K) :
      (LinearMap.adjoint embedding) (embedding vector) = vector := by
    have h := congrArg (fun map : Semantics.Operator (Semantics.CompositeSystem H K) =>
      map vector) hisometry
    simpa [LinearMap.comp_apply] using h
  have hright_apply (vector : Semantics.CompositeSystem H K) :
      rightAmbient (embedding vector) = embedding (rightTensor vector) := by
    have h := congrArg (fun map : Semantics.CompositeSystem H K →ₗ[Complex] X =>
      map vector) hright
    simpa [LinearMap.comp_apply] using h
  have hleft_apply (vector : Semantics.CompositeSystem H K) :
      (LinearMap.adjoint embedding) (leftAmbient (embedding vector)) =
        (TensorProduct.map leftLocal (1 : Semantics.Operator K)) vector := by
    have h := congrArg (fun map : Semantics.Operator (Semantics.CompositeSystem H K) =>
      map vector) hleft
    simpa [LinearMap.comp_apply] using h
  have hrightLift :
      embedding.comp ((productProjector * rightTensor * productProjector).comp
        (LinearMap.adjoint embedding)) =
          embedding.comp (productProjector.comp (LinearMap.adjoint embedding)) * rightAmbient *
          embedding.comp (productProjector.comp (LinearMap.adjoint embedding)) := by
    symm
    ext vector
    simp only [Module.End.mul_eq_comp, LinearMap.comp_apply]
    rw [hright_apply, hisometry_apply]
  have hmiddle :
      embedding.comp (productProjector.comp (LinearMap.adjoint embedding)) * leftAmbient *
          rightAmbient * embedding.comp (productProjector.comp (LinearMap.adjoint embedding)) =
        embedding.comp
          ((productProjector * TensorProduct.map leftLocal (1 : Semantics.Operator K) *
            rightTensor * productProjector).comp (LinearMap.adjoint embedding)) := by
    ext vector
    simp only [Module.End.mul_eq_comp, LinearMap.comp_apply]
    rw [hright_apply, hleft_apply]
  calc
    embedding.comp (productProjector.comp (LinearMap.adjoint embedding)) * leftAmbient *
          rightAmbient *
          embedding.comp (productProjector.comp (LinearMap.adjoint embedding)) =
        embedding.comp
          ((productProjector * TensorProduct.map leftLocal (1 : Semantics.Operator K) *
            rightTensor * productProjector).comp
            (LinearMap.adjoint embedding)) := hmiddle
    _ = embedding.comp
          (((inner Complex phi (leftLocal phi)) •
            (productProjector * TensorProduct.map
              (1 : Semantics.Operator H) rightLocal * productProjector)).comp
            (LinearMap.adjoint embedding)) := by
          congr 2
    _ = (inner Complex phi (leftLocal phi)) •
          (embedding.comp ((productProjector * rightTensor * productProjector).comp
            (LinearMap.adjoint embedding))) := by
          simp only [rightTensor, LinearMap.comp_smul, LinearMap.smul_comp]
    _ = (inner Complex phi (leftLocal phi)) •
          (embedding.comp (productProjector.comp (LinearMap.adjoint embedding)) * rightAmbient *
            embedding.comp (productProjector.comp (LinearMap.adjoint embedding))) := by
          rw [hrightLift]

end BPTCommutingProjectorModel
end Bounds
end QEC
