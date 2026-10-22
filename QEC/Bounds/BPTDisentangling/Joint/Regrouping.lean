import QEC.Bounds.BPTDisentangling.Joint.ActiveTransport

/-!
# BPT joint product regrouping

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

/-- Reassociate `((A tensor W) tensor (N tensor X)) tensor D` as
`((A tensor W) tensor N) tensor (X tensor D)`. -/
noncomputable def productBlockRegrouping
    {A W N X D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D] :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (Semantics.CompositeSystem A W)
          (Semantics.CompositeSystem N X)) D)
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (Semantics.CompositeSystem A W) N)
          (Semantics.CompositeSystem X D)) := by
  let e1 := (TensorProduct.assocIsometry Complex (Semantics.CompositeSystem A W) N X).symm.rTensor D
  let e2 := TensorProduct.assocIsometry Complex (Semantics.CompositeSystem (Semantics.CompositeSystem A W) N) X D
  let e := e1.trans e2
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := by
        intro x y
        exact e.inner_map_map x y }

@[simp]
theorem productBlockRegrouping_apply_tmul
    {A W N X D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (a : A) (w : W) (n : N) (x : X) (d : D) :
    productBlockRegrouping
      (((a ⊗ₜ[Complex] w) ⊗ₜ[Complex] (n ⊗ₜ[Complex] x)) ⊗ₜ[Complex] d) =
      ((a ⊗ₜ[Complex] w) ⊗ₜ[Complex] n) ⊗ₜ[Complex] (x ⊗ₜ[Complex] d) := by
  rfl

@[simp]
theorem productBlockRegrouping_apply_tmul_tmul
    {A W N X D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (phi : Semantics.CompositeSystem A W) (n : N) (x : X) (d : D) :
    productBlockRegrouping
      ((phi ⊗ₜ[Complex] (n ⊗ₜ[Complex] x)) ⊗ₜ[Complex] d) =
      (phi ⊗ₜ[Complex] n) ⊗ₜ[Complex] (x ⊗ₜ[Complex] d) := by
  rfl

set_option maxHeartbeats 800000 in
/-- Regroup a product rank-one block past an arbitrary operator on the final factor. -/
theorem conjOperator_productBlockRegrouping
    {A W N X D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (phi : Semantics.CompositeSystem A W) (n0 : N) (c0 : X) (P_D : Semantics.Operator D) :
    productBlockRegrouping.conjOperator
      (TensorProduct.map
        (TensorProduct.map
          (InnerProductSpace.rankOne Complex phi phi).toLinearMap
          (InnerProductSpace.rankOne Complex
            (n0 ⊗ₜ[Complex] c0) (n0 ⊗ₜ[Complex] c0)).toLinearMap)
        P_D) =
      TensorProduct.map
        (InnerProductSpace.rankOne Complex
          (phi ⊗ₜ[Complex] n0) (phi ⊗ₜ[Complex] n0)).toLinearMap
        (TensorProduct.map (InnerProductSpace.rankOne Complex c0 c0).toLinearMap P_D) := by
  classical
  let Phi : Semantics.Operator D →ₗ[Complex]
      Semantics.Operator (Semantics.CompositeSystem
        (Semantics.CompositeSystem (Semantics.CompositeSystem A W) N)
          (Semantics.CompositeSystem X D)) :=
    { toFun := fun P =>
        productBlockRegrouping.conjOperator
          (TensorProduct.map
            (TensorProduct.map
              (InnerProductSpace.rankOne Complex phi phi).toLinearMap
              (InnerProductSpace.rankOne Complex
                (n0 ⊗ₜ[Complex] c0) (n0 ⊗ₜ[Complex] c0)).toLinearMap)
            P)
      map_add' := by
        intro P Q
        rw [TensorProduct.map_add_right]
        exact productBlockRegrouping.conjOperatorLinearMap.map_add
          (TensorProduct.map
            (TensorProduct.map
              (InnerProductSpace.rankOne Complex phi phi).toLinearMap
              (InnerProductSpace.rankOne Complex
                (n0 ⊗ₜ[Complex] c0) (n0 ⊗ₜ[Complex] c0)).toLinearMap)
            P)
          (TensorProduct.map
            (TensorProduct.map
              (InnerProductSpace.rankOne Complex phi phi).toLinearMap
              (InnerProductSpace.rankOne Complex
                (n0 ⊗ₜ[Complex] c0) (n0 ⊗ₜ[Complex] c0)).toLinearMap)
            Q)
      map_smul' := by
        intro a P
        rw [TensorProduct.map_smul_right]
        exact productBlockRegrouping.conjOperatorLinearMap.map_smul a
          (TensorProduct.map
            (TensorProduct.map
              (InnerProductSpace.rankOne Complex phi phi).toLinearMap
              (InnerProductSpace.rankOne Complex
                (n0 ⊗ₜ[Complex] c0) (n0 ⊗ₜ[Complex] c0)).toLinearMap)
            P) }
  let Psi : Semantics.Operator D →ₗ[Complex]
      Semantics.Operator (Semantics.CompositeSystem
        (Semantics.CompositeSystem (Semantics.CompositeSystem A W) N)
          (Semantics.CompositeSystem X D)) :=
    { toFun := fun P =>
        TensorProduct.map
          (InnerProductSpace.rankOne Complex
            (phi ⊗ₜ[Complex] n0) (phi ⊗ₜ[Complex] n0)).toLinearMap
          (TensorProduct.map (InnerProductSpace.rankOne Complex c0 c0).toLinearMap P)
      map_add' := by
        intro P Q
        rw [TensorProduct.map_add_right, TensorProduct.map_add_right]
      map_smul' := by
        intro a P
        calc
          TensorProduct.map
              (InnerProductSpace.rankOne Complex
                (phi ⊗ₜ[Complex] n0) (phi ⊗ₜ[Complex] n0)).toLinearMap
              (TensorProduct.map
                (InnerProductSpace.rankOne Complex c0 c0).toLinearMap (a • P)) =
            TensorProduct.map
              (InnerProductSpace.rankOne Complex
                (phi ⊗ₜ[Complex] n0) (phi ⊗ₜ[Complex] n0)).toLinearMap
              (a • TensorProduct.map
                (InnerProductSpace.rankOne Complex c0 c0).toLinearMap P) := by
                  rw [TensorProduct.map_smul_right]
          _ = a • TensorProduct.map
              (InnerProductSpace.rankOne Complex
                (phi ⊗ₜ[Complex] n0) (phi ⊗ₜ[Complex] n0)).toLinearMap
              (TensorProduct.map
                (InnerProductSpace.rankOne Complex c0 c0).toLinearMap P) := by
                  exact TensorProduct.map_smul_right _ _ _ }
  have hPhiPsi : Phi = Psi := by
    apply Semantics.QuditSubsystem.linearMap_ext_of_rankOne_basis
      (stdOrthonormalBasis Complex D) Phi Psi
    intro d d'
    dsimp [Phi, Psi]
    rw [Semantics.DensityOperator.tensorMap_rankOne]
    rw [Semantics.DensityOperator.tensorMap_rankOne]
    rw [Semantics.QuditSubsystem.conjOperator_rankOne]
    simp only [productBlockRegrouping_apply_tmul_tmul]
    rw [Semantics.DensityOperator.tensorMap_rankOne]
    rw [Semantics.DensityOperator.tensorMap_rankOne]
  exact congrArg (fun F => F P_D) hPhiPsi

/--
Conjugating an operator before compressing along the transported embedding is
exactly the original compression.  This is the algebraic core of the D5
comparison between a four-factor active block and its second-cut coordinates.
-/
theorem unitaryTransport_conj_compression_comp
    {H K S : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    (T : Semantics.UnitaryTransport H K) (J : S →ₗ[Complex] H)
    (P : Semantics.Operator H) :
    (LinearMap.adjoint (T.toLinearEquiv.toLinearMap.comp J)).comp
        ((T.conjOperator P).comp (T.toLinearEquiv.toLinearMap.comp J)) =
      (LinearMap.adjoint J).comp (P.comp J) := by
  have hTadj : LinearMap.adjoint T.toLinearEquiv.toLinearMap =
      T.symm.toLinearEquiv.toLinearMap := by
    rw [Semantics.UnitaryTransport.symm_toLinearEquiv]
    exact Semantics.UnitaryTransport.adjoint_toLinearMap T
  unfold Semantics.UnitaryTransport.conjOperator
  rw [LinearMap.adjoint_comp, hTadj]
  simp only [LinearMap.comp_assoc]
  simp

/--
The canonical simultaneous-sector embedding has `J J†` equal to the literal
product of the `B` and `C` sector projections.
-/
theorem fourFactorJointBCSectorEmbedding_comp_adjoint_eq_sectorProjectorProduct
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C) :
    (fourFactorJointBCSectorEmbedding pB pC).comp
      (LinearMap.adjoint (fourFactorJointBCSectorEmbedding pB pC)) =
      TensorProduct.map (1 : Semantics.Operator A)
        (TensorProduct.map pB.starProjection.toLinearMap
          (TensorProduct.map pC.starProjection.toLinearMap (1 : Semantics.Operator D))) := by
  let T := tensorAssociatorUnitary A B (Semantics.CompositeSystem C D)
  let J := jointBCSectorEmbeddingRight (A := A) (D := D) pB pC
  have hJ := jointBCSectorEmbeddingRight_comp_adjoint_eq_sectorProjectorProduct
    (A := A) (D := D) pB pC
  have hTadj : LinearMap.adjoint T.toLinearEquiv.toLinearMap =
      T.symm.toLinearEquiv.toLinearMap := by
    rw [Semantics.UnitaryTransport.symm_toLinearEquiv]
    exact Semantics.UnitaryTransport.adjoint_toLinearMap T
  change (T.toLinearEquiv.toLinearMap.comp J).comp
      (LinearMap.adjoint (T.toLinearEquiv.toLinearMap.comp J)) = _
  rw [LinearMap.adjoint_comp, hTadj]
  calc
    (T.toLinearEquiv.toLinearMap.comp J).comp
        ((LinearMap.adjoint J).comp T.symm.toLinearEquiv.toLinearMap) =
        T.conjOperator (J.comp (LinearMap.adjoint J)) := by
      unfold Semantics.UnitaryTransport.conjOperator
      rw [Semantics.UnitaryTransport.symm_toLinearEquiv]
      simp only [LinearMap.comp_assoc]
    _ = T.conjOperator
        (TensorProduct.map
          (TensorProduct.map (1 : Semantics.Operator A) pB.starProjection.toLinearMap)
          (TensorProduct.map pC.starProjection.toLinearMap (1 : Semantics.Operator D))) := by
      rw [hJ]
    _ = TensorProduct.map (1 : Semantics.Operator A)
        (TensorProduct.map pB.starProjection.toLinearMap
          (TensorProduct.map pC.starProjection.toLinearMap (1 : Semantics.Operator D))) := by
      exact tensorAssociatorUnitary_conj_tensorMap
        (1 : Semantics.Operator A) pB.starProjection.toLinearMap
        (TensorProduct.map pC.starProjection.toLinearMap (1 : Semantics.Operator D))

/--
The product of the two literal four-factor sector lifts is the simultaneous
active-sector projection `J J†`.
-/
theorem fourFactor_sectorProjectorProduct_eq_jointBCSectorEmbedding_comp_adjoint
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C) :
    TensorProduct.map (1 : Semantics.Operator A)
      (TensorProduct.map pB.starProjection.toLinearMap
        (TensorProduct.map (1 : Semantics.Operator C) (1 : Semantics.Operator D))) *
      TensorProduct.map (1 : Semantics.Operator A)
        (TensorProduct.map (1 : Semantics.Operator B)
          (TensorProduct.map pC.starProjection.toLinearMap (1 : Semantics.Operator D))) =
      (fourFactorJointBCSectorEmbedding pB pC).comp
        (LinearMap.adjoint (fourFactorJointBCSectorEmbedding pB pC)) := by
  rw [fourFactorJointBCSectorEmbedding_comp_adjoint_eq_sectorProjectorProduct]
  rw [← TensorProduct.map_mul, ← TensorProduct.map_mul, ← TensorProduct.map_mul]
  simp

/--
A symmetric projection supported on the literal simultaneous `B,C` sector is
reconstructed from its compression to that same sector.
-/
theorem fourFactorJointBCSector_reconstruction_of_active_support
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (P4 : Semantics.Operator
      (Semantics.CompositeSystem A (Semantics.CompositeSystem B (Semantics.CompositeSystem C D))))
    (hP4 : P4.IsSymmetricProjection)
    (hactive :
      P4 *
          TensorProduct.map (1 : Semantics.Operator A)
            (TensorProduct.map pB.starProjection.toLinearMap
              (TensorProduct.map (1 : Semantics.Operator C) (1 : Semantics.Operator D))) *
          TensorProduct.map (1 : Semantics.Operator A)
            (TensorProduct.map (1 : Semantics.Operator B)
              (TensorProduct.map pC.starProjection.toLinearMap
                (1 : Semantics.Operator D))) = P4) :
    let J := fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC
    P4 = J.comp (((LinearMap.adjoint J).comp (P4.comp J)).comp (LinearMap.adjoint J)) := by
  dsimp
  let J := fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC
  let E := J.comp (LinearMap.adjoint J)
  let LB : Semantics.Operator
      (Semantics.CompositeSystem A (Semantics.CompositeSystem B (Semantics.CompositeSystem C D))) :=
    TensorProduct.map (1 : Semantics.Operator A)
      (TensorProduct.map pB.starProjection.toLinearMap
        (TensorProduct.map (1 : Semantics.Operator C) (1 : Semantics.Operator D)))
  let LC : Semantics.Operator
      (Semantics.CompositeSystem A (Semantics.CompositeSystem B (Semantics.CompositeSystem C D))) :=
    TensorProduct.map (1 : Semantics.Operator A)
      (TensorProduct.map (1 : Semantics.Operator B)
        (TensorProduct.map pC.starProjection.toLinearMap (1 : Semantics.Operator D)))
  have hsectorProduct : LB * LC = E := by
    simpa [LB, LC, E, J] using
      (fourFactor_sectorProjectorProduct_eq_jointBCSectorEmbedding_comp_adjoint
        (A := A) (D := D) pB pC)
  have hright : P4 * E = P4 := by
    calc
      P4 * E = P4 * (LB * LC) := by rw [hsectorProduct]
      _ = P4 * LB * LC := (mul_assoc P4 LB LC).symm
      _ = P4 := by simpa [LB, LC] using hactive
  have hP4self : LinearMap.adjoint P4 = P4 := hP4.isSymmetric.adjoint_eq
  have hEself : LinearMap.adjoint E = E := by
    dsimp only [E]
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
  have hleft : E * P4 = P4 := by
    have hadjoint := congrArg LinearMap.adjoint hright
    change LinearMap.adjoint (P4.comp E) = LinearMap.adjoint P4 at hadjoint
    rw [LinearMap.adjoint_comp, hP4self, hEself] at hadjoint
    simpa [Module.End.mul_eq_comp] using hadjoint
  have hcommute : Commute P4 E := hright.trans hleft.symm
  exact embedding_compression_of_right_absorption J P4 hcommute hright

set_option maxHeartbeats 2000000 in
/--
For fixed active BPT components, the two retained cut-absorption equations
give the four-factor reconstruction through their common simultaneous-sector
compression.  This is the D5 reconstruction bridge; it does not select new
components.
-/
theorem fourFactorJointBCSector_reconstruction_of_active_cuts
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (hCactive : M.firstCutCodeLift region * M.firstCutSectorLift region ccomponent =
      M.firstCutCodeLift region)
    (hBactive : M.secondCutCodeLift region * M.secondCutSectorLift region bcomponent =
      M.secondCutCodeLift region) :
    let pB := bcomponent.1.restrictScalars Complex
    let pC := ccomponent.1.restrictScalars Complex
    let J := fourFactorJointBCSectorEmbedding
      (A := M.fourFactorA region) (D := M.fourFactorD region) pB pC
    let P4 := (M.fourFactorTransport region).conjOperator M.fullCodeProjector
    P4 = J.comp (((LinearMap.adjoint J).comp (P4.comp J)).comp (LinearMap.adjoint J)) := by
  dsimp
  let A := M.fourFactorA region
  let B := M.fourFactorB region
  let C := M.fourFactorC region
  let D := M.fourFactorD region
  let F := M.fourFactorTransport region
  let pB := bcomponent.1.restrictScalars Complex
  let pC := ccomponent.1.restrictScalars Complex
  let P4 := F.conjOperator M.fullCodeProjector
  let ZB : Semantics.Operator B :=
    leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) bcomponent
  let ZC : Semantics.Operator C :=
    leftIsotypicSectorProjector (M.firstCutProjectorMC region) ccomponent
  let XB : Semantics.Operator L.Register :=
    (M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
      ((M.fourFactorBCoordinateRelabel region).symm.conjOperator ZB)
  let XC : Semantics.Operator L.Register :=
    (M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
      ((M.fourFactorCCoordinateRelabel region).symm.conjOperator ZC)
  let LB : Semantics.Operator
      (Semantics.CompositeSystem A (Semantics.CompositeSystem B (Semantics.CompositeSystem C D))) :=
    TensorProduct.map (1 : Semantics.Operator A)
      (TensorProduct.map ZB
        (TensorProduct.map (1 : Semantics.Operator C) (1 : Semantics.Operator D)))
  let LC : Semantics.Operator
      (Semantics.CompositeSystem A (Semantics.CompositeSystem B (Semantics.CompositeSystem C D))) :=
    TensorProduct.map (1 : Semantics.Operator A)
      (TensorProduct.map (1 : Semantics.Operator B)
        (TensorProduct.map ZC (1 : Semantics.Operator D)))
  have hraw := M.joint_active_sector_code_support_of_active_cuts
    region ccomponent bcomponent hCactive hBactive
  have hZB : ZB = pB.starProjection.toLinearMap := by
    simp [ZB, pB, leftIsotypicSectorProjector]
  have hZC : ZC = pC.starProjection.toLinearMap := by
    simp [ZC, pC, leftIsotypicSectorProjector]
  have hBtransport : F.conjOperator XB = LB := by
    simpa [F, XB, LB, A, B, C, D] using
      M.fourFactorTransport_conj_internalBoundaryLift region ZB
  have hCtransport : F.conjOperator XC = LC := by
    simpa [F, XC, LB, LC, A, B, C, D] using
      M.fourFactorTransport_conj_externalBoundaryLift region ZC
  have hactiveRaw : P4 * F.conjOperator XB * F.conjOperator XC = P4 := by
    simpa [P4, F, XB, XC, ZB, ZC] using hraw
  have hactiveMapped : P4 * LB * LC = P4 := by
    calc
      P4 * LB * LC = P4 * F.conjOperator XB * F.conjOperator XC := by
        rw [← hBtransport, ← hCtransport]
      _ = P4 := hactiveRaw
  have hactive :
      P4 *
          TensorProduct.map (1 : Semantics.Operator A)
            (TensorProduct.map pB.starProjection.toLinearMap
              (TensorProduct.map (1 : Semantics.Operator C) (1 : Semantics.Operator D))) *
          TensorProduct.map (1 : Semantics.Operator A)
            (TensorProduct.map (1 : Semantics.Operator B)
              (TensorProduct.map pC.starProjection.toLinearMap
                (1 : Semantics.Operator D))) = P4 := by
    simpa [LB, LC, hZB, hZC] using hactiveMapped
  have hfull : M.fullCodeProjector.IsSymmetricProjection := by
    constructor
    · exact M.fullCodeProjector_idempotent
    · exact (LinearMap.isSymmetric_iff_isSelfAdjoint M.fullCodeProjector).mpr
        M.fullCodeProjector_adjoint_eq_self
  have hP4 : P4.IsSymmetricProjection := by
    change (F.conjOperator M.fullCodeProjector).IsSymmetricProjection
    exact (isSymmetricProjection_conjOperator_iff F M.fullCodeProjector).mpr hfull
  simpa [A, B, C, D, pB, pC, P4] using
    (fourFactorJointBCSector_reconstruction_of_active_support
      (A := A) (B := B) (C := C) (D := D) pB pC P4 hP4 hactive)


end BPTCommutingProjectorModel

end Bounds
end QEC
