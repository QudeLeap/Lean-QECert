import QEC.Bounds.BPTDisentangling.Joint.Factorization

/-!
# BPT active-block projection support

Cacheable internal proof layer for the finite-dimensional BPT Disentangling Lemma.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

-- Model-specific cache bridges are too large to be useful as automated premises.
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "secondCut_Qright_ne_zero_of_nonzero_code_active_block"
    let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "secondCut_Qright_mul_firstCut_active_sector"
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "secondCutQrightOnFirstCutActiveSector_isSymmetricProjection_and_ne_zero"

set_option maxHeartbeats 800000

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/--
An orthogonal projection supported on an isometric sector is supported from
both sides.  This is the algebraic form needed before compressing the actual
second-cut right block to the active first-cut `C` sector.
-/
theorem isometricCompression_left_support_of_right_support
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (Jadj : K →ₗ[Complex] H)
    (Q : Semantics.Operator K)
    (hJadj_eq : LinearMap.adjoint J = Jadj)
    (hQ : Q.IsSymmetricProjection)
    (hright : Q.comp (J.comp Jadj) = Q) :
    (J.comp Jadj).comp Q = Q := by
  have hJadjadj : LinearMap.adjoint Jadj = J := by
    calc
      LinearMap.adjoint Jadj = LinearMap.adjoint (LinearMap.adjoint J) := by
        rw [hJadj_eq]
      _ = J := LinearMap.adjoint_adjoint J
  have hSself : LinearMap.adjoint (J.comp Jadj) = J.comp Jadj := by
    rw [LinearMap.adjoint_comp, hJadjadj, hJadj_eq]
  have hQself : LinearMap.adjoint Q = Q := hQ.isSymmetric.adjoint_eq
  calc
    (J.comp Jadj).comp Q = LinearMap.adjoint (Q.comp (J.comp Jadj)) := by
      rw [LinearMap.adjoint_comp, hSself, hQself]
    _ = LinearMap.adjoint Q := congrArg LinearMap.adjoint hright
    _ = Q := hQself

/--
Compressing an active orthogonal projection to an isometric sector preserves
orthogonal-projection structure.  Unlike a bare compression statement, the
active-sector hypothesis supplies the required invariance.
-/
theorem isSymmetricProjection_of_active_isometric_compression
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (Jadj : K →ₗ[Complex] H)
    (Q : Semantics.Operator K)
    (hJadj : Jadj.comp J = (1 : Semantics.Operator H))
    (hJadj_eq : LinearMap.adjoint J = Jadj)
    (hQ : Q.IsSymmetricProjection)
    (hright : Q.comp (J.comp Jadj) = Q) :
    (Jadj.comp (Q.comp J)).IsSymmetricProjection := by
  have hleft := isometricCompression_left_support_of_right_support
    J Jadj Q hJadj_eq hQ hright
  apply isSymmetricProjection_of_isometric_compression_commuting J Jadj Q hJadj hJadj_eq hQ
  exact hright.trans hleft.symm

/--
An active nonzero projection remains nonzero after compression to its active
isometric sector.  This prevents the residual `Theta` block from disappearing
when the common `B,C` sector is formed.
-/
theorem isometricCompression_ne_zero_of_active_projection
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (Jadj : K →ₗ[Complex] H)
    (Q : Semantics.Operator K)
    (hJadj_eq : LinearMap.adjoint J = Jadj)
    (hQ : Q.IsSymmetricProjection)
    (hQ0 : Q ≠ 0)
    (hright : Q.comp (J.comp Jadj) = Q) :
    Jadj.comp (Q.comp J) ≠ 0 := by
  intro hzero
  have hleft := isometricCompression_left_support_of_right_support
    J Jadj Q hJadj_eq hQ hright
  apply hQ0
  calc
    Q = Q.comp (J.comp Jadj) := hright.symm
    _ = ((J.comp Jadj).comp Q).comp (J.comp Jadj) := by
      rw [hleft]
    _ = J.comp ((Jadj.comp (Q.comp J)).comp Jadj) := by
      simp only [LinearMap.comp_assoc]
    _ = J.comp ((0 : Semantics.Operator H).comp Jadj) := by rw [hzero]
    _ = 0 := by simp

/--
Scalar compression descends through an active isometric-sector compression
when the probe intertwines the ambient and sector coordinates.  The probe is
not required to preserve the sector, which is essential for the later `C'`
transfer from arbitrary external-boundary probes.
-/
theorem isometricCompression_scalar_of_intertwining
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (Jadj : K →ₗ[Complex] H)
    (Q R : Semantics.Operator K) (Rsub : Semantics.Operator H) (scalar : Complex)
    (hleft : (J.comp Jadj).comp Q = Q)
    (hscalar : Q * R * Q = scalar • Q)
    (hintertwines : J.comp Rsub = R.comp J) :
    (Jadj.comp (Q.comp J)) * Rsub * (Jadj.comp (Q.comp J)) =
      scalar • (Jadj.comp (Q.comp J)) := by
  calc
    (Jadj.comp (Q.comp J)) * Rsub * (Jadj.comp (Q.comp J)) =
        Jadj.comp (Q.comp ((J.comp Rsub).comp (Jadj.comp (Q.comp J)))) := by
      simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
    _ = Jadj.comp (Q.comp ((R.comp J).comp (Jadj.comp (Q.comp J)))) := by
      rw [hintertwines]
    _ = Jadj.comp ((Q.comp (R.comp ((J.comp Jadj).comp Q))).comp J) := by
      simp only [LinearMap.comp_assoc]
    _ = Jadj.comp ((Q.comp (R.comp Q)).comp J) := by rw [hleft]
    _ = Jadj.comp (((Q * R * Q).comp J)) := by
      simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
    _ = Jadj.comp ((scalar • Q).comp J) := by rw [hscalar]
    _ = scalar • (Jadj.comp (Q.comp J)) := by
      rw [LinearMap.smul_comp, LinearMap.comp_smul]

/--
The actual second-cut right block is nonzero on the active `B` sector whenever
the physical code is nonempty.  This keeps the later `C`-sector compression
honest: nonzeroness is obtained from the active code block, not from the
common factorization equality alone.
-/
theorem secondCut_Qright_ne_zero_of_nonzero_code_active_block
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (Semantics.CompositeSystem (W.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} n)))
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (W.restrictScalars Complex)))
    (Qright : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} n)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hactive : M.secondCutCodeLift region * M.secondCutSectorLift region component =
      M.secondCutCodeLift region)
    (hleft :
      (unitaryLTensor (M.fourFactorA region) U).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) component) =
        rightTensorExtensionAfterLeft (M.fourFactorA region)
          (W.restrictScalars Complex) (isotypicLiftedMultiplicity.{0} n) Pleft)
    (hright :
      (unitaryRTensor U
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region) component) =
        leftTensorExtensionBeforeRight (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} n)
          (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) Qright) :
    Qright ≠ 0 := by
  let A := M.fourFactorA region
  let H := component.1.restrictScalars Complex
  let N := isotypicLiftedMultiplicity.{0} n
  let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
  let J := tensorTripleSubtypeEmbedding (A := A) (C := CD) H
  let R := M.secondCutCodeLift region
  let Rcompressed : Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem A H) CD) :=
    (LinearMap.adjoint J).comp (R.comp J)
  let T := isotypicSectorBlockTransportLeft A H (W.restrictScalars Complex) N CD U
  have hR : R ≠ 0 := by
    simpa [R] using M.secondCutCodeLift_ne_zero_of_nonzero_code region hcode
  have hself : LinearMap.adjoint (M.fourFactorProjectorABLocal region) =
      M.fourFactorProjectorABLocal region :=
    (M.secondCutProjectorAB_isSymmetricProjection region).isSymmetric.adjoint_eq
  have hover : Commute
      (overlapLiftLeft (C := CD) (M.fourFactorProjectorABLocal region))
      (overlapLiftRight (A := A) (M.secondCutProjectorBbarM region)) :=
    M.secondCut_overlap_commute region
  have hreconstruct : R = J.comp (Rcompressed.comp (LinearMap.adjoint J)) := by
    dsimp [Rcompressed, R, J, A, H, CD]
    apply active_overlap_product_eq_isotypic_embedding_compression
      (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region)
      hself hover component
    simpa [secondCutCodeLift, secondCutSectorLift] using hactive
  have hblock : T.conjOperator Rcompressed = TensorProduct.map Pleft Qright := by
    simpa [T, Rcompressed, R, J, A, H, N, CD] using
      M.secondCut_compressed_overlap_block_product region component W U Pleft Qright hleft hright
  intro hzero
  have htransportedZero : T.conjOperator Rcompressed = 0 := by
    calc
      T.conjOperator Rcompressed = TensorProduct.map Pleft Qright := hblock
      _ = TensorProduct.map Pleft 0 := congrArg (TensorProduct.map Pleft) hzero
      _ = 0 := TensorProduct.map_zero_right Pleft
  have hcompressedZero : Rcompressed = 0 := by
    calc
      Rcompressed = T.symm.conjOperator (T.conjOperator Rcompressed) :=
        (T.symm_conjOperator_conjOperator Rcompressed).symm
      _ = T.symm.conjOperator 0 := congrArg T.symm.conjOperator htransportedZero
      _ = 0 := by simp [Semantics.UnitaryTransport.conjOperator]
  apply hR
  rw [hreconstruct, hcompressedZero]
  simp

set_option maxHeartbeats 4000000 in
/--
The first-cut active `C` sector acts as the identity on the actual second-cut
right block.  This is obtained by reassociating the physical first-cut active
equation, compressing it through the active `B` sector, and cancelling the
nonzero `Pleft` factor; no support property of `Qright` is postulated.
-/
theorem secondCut_Qright_mul_firstCut_active_sector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (U : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (W.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} n)))
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (W.restrictScalars Complex)))
    (Qright : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} n)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hCactive : M.firstCutCodeLift region * M.firstCutSectorLift region ccomponent =
      M.firstCutCodeLift region)
    (hBactive : M.secondCutCodeLift region * M.secondCutSectorLift region bcomponent =
      M.secondCutCodeLift region)
    (hleft :
      (unitaryLTensor (M.fourFactorA region) U).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) bcomponent) =
        rightTensorExtensionAfterLeft (M.fourFactorA region)
          (W.restrictScalars Complex) (isotypicLiftedMultiplicity.{0} n) Pleft)
    (hright :
      (unitaryRTensor U
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region)
            bcomponent) =
        leftTensorExtensionBeforeRight (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} n)
          (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) Qright) :
    Qright * TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} n))
        (TensorProduct.map
          (leftIsotypicSectorProjector (M.firstCutProjectorMC region) ccomponent)
          (1 : Semantics.Operator (M.fourFactorD region))) = Qright := by
  let A := M.fourFactorA region
  let B := M.fourFactorB region
  let AB := Semantics.CompositeSystem A B
  let H := bcomponent.1.restrictScalars Complex
  let N := isotypicLiftedMultiplicity.{0} n
  let C := M.fourFactorC region
  let D := M.fourFactorD region
  let CD := Semantics.CompositeSystem C D
  let Z : Semantics.Operator C :=
    leftIsotypicSectorProjector (M.firstCutProjectorMC region) ccomponent
  let J := tensorTripleSubtypeEmbedding (A := A) (C := CD) H
  let Jadj := LinearMap.adjoint J
  let R := M.secondCutCodeLift region
  let Rcompressed : Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem A H) CD) :=
    Jadj.comp (R.comp J)
  let T := isotypicSectorBlockTransportLeft A H (W.restrictScalars Complex) N CD U
  let Sfirst := M.firstCutSectorLift region ccomponent
  let Ssecond : Semantics.Operator (Semantics.CompositeSystem AB CD) :=
    TensorProduct.map (1 : Semantics.Operator AB)
      (TensorProduct.map Z (1 : Semantics.Operator D))
  let Ssub : Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem A H) CD) :=
    TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A H))
      (TensorProduct.map Z (1 : Semantics.Operator D))
  let Sright : Semantics.Operator (Semantics.CompositeSystem N CD) :=
    TensorProduct.map (1 : Semantics.Operator N)
      (TensorProduct.map Z (1 : Semantics.Operator D))
  have hsectorTransport :
      (tensorAssociatorUnitary AB C D).conjOperator Sfirst = Ssecond := by
    simpa [Sfirst, Ssecond, Z, AB, C, D, firstCutSectorLift, overlapLiftLeft] using
      (tensorAssociatorUnitary_conj_tensorMap
        (1 : Semantics.Operator AB) Z (1 : Semantics.Operator D))
  have hRsecondC : R.comp Ssecond = R := by
    change R * Ssecond = R
    calc
      R * Ssecond =
          (tensorAssociatorUnitary AB C D).conjOperator (M.firstCutCodeLift region) *
            (tensorAssociatorUnitary AB C D).conjOperator Sfirst := by
              rw [M.secondCutCodeLift_eq_reassociate_firstCutCodeLift, hsectorTransport]
      _ = (tensorAssociatorUnitary AB C D).conjOperator
          (M.firstCutCodeLift region * Sfirst) := by
            rw [Semantics.UnitaryTransport.conjOperator_mul]
      _ = (tensorAssociatorUnitary AB C D).conjOperator (M.firstCutCodeLift region) := by
            rw [hCactive]
      _ = R := M.secondCutCodeLift_eq_reassociate_firstCutCodeLift region
  have hScompJ : Ssecond.comp J = J.comp Ssub := by
    dsimp [Ssecond, J, Ssub, AB, CD, tensorTripleSubtypeEmbedding]
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
    change TensorProduct.map
        (TensorProduct.map (1 : Semantics.Operator A) H.subtype)
        (TensorProduct.map Z (1 : Semantics.Operator D)) =
      TensorProduct.map
        (TensorProduct.map (1 : Semantics.Operator A) H.subtype)
        (TensorProduct.map Z (1 : Semantics.Operator D))
    rfl
  have hRcompressedSupport : Rcompressed * Ssub = Rcompressed := by
    change (Jadj.comp (R.comp J)).comp Ssub = Jadj.comp (R.comp J)
    calc
      (Jadj.comp (R.comp J)).comp Ssub = Jadj.comp (R.comp (J.comp Ssub)) := by
        simp only [LinearMap.comp_assoc]
      _ = Jadj.comp (R.comp (Ssecond.comp J)) := by rw [hScompJ]
      _ = Jadj.comp ((R.comp Ssecond).comp J) := by rw [LinearMap.comp_assoc]
      _ = Jadj.comp (R.comp J) :=
        congrArg
          (fun operator : Semantics.Operator (Semantics.CompositeSystem AB CD) =>
            Jadj.comp (operator.comp J))
          hRsecondC
  have hblock : T.conjOperator Rcompressed = TensorProduct.map Pleft Qright := by
    simpa [T, Rcompressed, R, J, Jadj, A, H, N, CD] using
      M.secondCut_compressed_overlap_block_product region bcomponent W U Pleft Qright hleft hright
  have hTsector : T.conjOperator Ssub =
      TensorProduct.map (1 : Semantics.Operator
        (Semantics.CompositeSystem A (W.restrictScalars Complex))) Sright := by
    simpa [T, Ssub, Sright, A, H, N, CD] using
      (isotypicSectorBlockTransportLeft_conj_tensorMap_right
        (A := A) (H := H) (W := W.restrictScalars Complex) (N := N) (C := CD)
        U (TensorProduct.map Z (1 : Semantics.Operator D)))
  have hblockSupport :
      TensorProduct.map Pleft Qright *
          TensorProduct.map (1 : Semantics.Operator
            (Semantics.CompositeSystem A (W.restrictScalars Complex))) Sright =
        TensorProduct.map Pleft Qright := by
    calc
      TensorProduct.map Pleft Qright *
          TensorProduct.map (1 : Semantics.Operator
            (Semantics.CompositeSystem A (W.restrictScalars Complex))) Sright =
          T.conjOperator Rcompressed * T.conjOperator Ssub :=
        congrArg₂ (fun left right => left * right) hblock.symm hTsector.symm
      _ = T.conjOperator (Rcompressed * Ssub) :=
        (T.conjOperator_mul Rcompressed Ssub).symm
      _ = T.conjOperator Rcompressed := congrArg T.conjOperator hRcompressedSupport
      _ = TensorProduct.map Pleft Qright := hblock
  have hfactor : TensorProduct.map Pleft (Qright * Sright) =
      TensorProduct.map Pleft Qright := by
    calc
      TensorProduct.map Pleft (Qright * Sright) =
          TensorProduct.map
            (Pleft * (1 : Semantics.Operator
              (Semantics.CompositeSystem A (W.restrictScalars Complex))))
            (Qright * Sright) :=
        congrArg (fun left => TensorProduct.map left (Qright * Sright))
          (mul_one Pleft).symm
      _ = TensorProduct.map Pleft Qright *
          TensorProduct.map (1 : Semantics.Operator
            (Semantics.CompositeSystem A (W.restrictScalars Complex))) Sright :=
        TensorProduct.map_mul Pleft _ Qright Sright
      _ = TensorProduct.map Pleft Qright := hblockSupport
  have hPleft0 := M.secondCut_Pleft_ne_zero_of_nonzero_code
    region hcode bcomponent W U Pleft Qright hBactive hleft hright
  obtain ⟨vector, hvector⟩ := DFunLike.ne_iff.mp hPleft0
  apply LinearMap.ext
  intro rightVector
  apply tmul_right_eq_of_tmul_left_eq_of_ne_zero (Pleft vector) hvector
  have happly := congrArg (fun operator => operator (vector ⊗ₜ[Complex] rightVector)) hfactor
  simpa [Sright, TensorProduct.map_tmul] using happly

set_option maxHeartbeats 4000000 in
/--
After the actual active `C` support equation is established, the `C`-sector
compression and its isotypic coordinates carry the second-cut right block to
a nonzero orthogonal projection.  This is the precise projection/nonzero input
for the residual `Theta_{B''C'}` construction.
-/
theorem secondCutQrightOnFirstCutActiveSector_isSymmetricProjection_and_ne_zero
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥) (hM : M.RegionErasureRecoverable region)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {nC nB : Nat} [NeZero nC] [NeZero nB]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hCactive : M.firstCutCodeLift region * M.firstCutSectorLift region ccomponent =
      M.firstCutCodeLift region)
    (hBactive : M.secondCutCodeLift region * M.secondCutSectorLift region bcomponent =
      M.secondCutCodeLift region)
    (hBleft :
      (unitaryLTensor (M.fourFactorA region) UB).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) bcomponent) =
        rightTensorExtensionAfterLeft (M.fourFactorA region)
          (WB.restrictScalars Complex) (isotypicLiftedMultiplicity.{0} nB) Pleft)
    (hBright :
      (unitaryRTensor UB
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region)
            bcomponent) =
        leftTensorExtensionBeforeRight (WB.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} nB)
          (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) Qsecond) :
    LinearMap.IsSymmetricProjection
        (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond) ∧
      M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond ≠ 0 := by
  let H := ccomponent.1.restrictScalars Complex
  let N := isotypicLiftedMultiplicity.{0} nB
  let NC := isotypicLiftedMultiplicity.{0} nC
  let C := M.fourFactorC region
  let D := M.fourFactorD region
  let K : (Semantics.CompositeSystem N (Semantics.CompositeSystem H D)) →ₗ[Complex]
      (Semantics.CompositeSystem N (Semantics.CompositeSystem C D)) :=
    TensorProduct.map (1 : Semantics.Operator N)
      (TensorProduct.map H.subtype (1 : Semantics.Operator D))
  let Kadj := LinearMap.adjoint K
  let V := composeUnitaryTransport (unitaryRTensor UC D)
    (tensorAssociatorUnitary (WC.restrictScalars Complex) NC D)
  let T := unitaryLTensor N V
  let Z : Semantics.Operator C :=
    leftIsotypicSectorProjector (M.firstCutProjectorMC region) ccomponent
  let S : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem C D)) :=
    TensorProduct.map (1 : Semantics.Operator N)
      (TensorProduct.map Z (1 : Semantics.Operator D))
  let Qcompressed : Semantics.Operator
      (Semantics.CompositeSystem N (Semantics.CompositeSystem H D)) :=
    Kadj.comp (Qsecond.comp K)
  have hQ : Qsecond.IsSymmetricProjection :=
    M.secondCut_Qright_isSymmetricProjection_of_region_recoverable
      region hcode hM bcomponent WB UB Pleft Qsecond hBactive hBleft hBright
  have hQ0 : Qsecond ≠ 0 :=
    M.secondCut_Qright_ne_zero_of_nonzero_code_active_block
      region hcode bcomponent WB UB Pleft Qsecond hBactive hBleft hBright
  have hsupport : Qsecond.comp S = Qsecond := by
    exact M.secondCut_Qright_mul_firstCut_active_sector
      region hcode ccomponent bcomponent WB UB Pleft Qsecond hCactive hBactive hBleft hBright
  have hKadj_eq : LinearMap.adjoint K = Kadj := rfl
  have hKadjK : Kadj.comp K =
      (1 : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem H D))) := by
    dsimp [Kadj, K]
    rw [TensorProduct.adjoint_map, LinearMap.adjoint_one,
      TensorProduct.adjoint_map, LinearMap.adjoint_one]
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
    rw [adjoint_submoduleSubtype_comp_subtype_eq_one H]
    change TensorProduct.map (LinearMap.id.comp LinearMap.id)
      (TensorProduct.map (LinearMap.id.comp LinearMap.id) LinearMap.id) = LinearMap.id
    rw [LinearMap.id_comp, LinearMap.id_comp]
    rw [show TensorProduct.map LinearMap.id LinearMap.id =
      (1 : Semantics.Operator (Semantics.CompositeSystem H D)) from TensorProduct.map_one]
    exact TensorProduct.map_one
  have hKKadj : K.comp Kadj = S := by
    dsimp [Kadj, K, S, Z]
    rw [TensorProduct.adjoint_map, LinearMap.adjoint_one,
      TensorProduct.adjoint_map, LinearMap.adjoint_one]
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
    rw [submoduleSubtype_comp_adjoint_eq_starProjection H]
    change TensorProduct.map (LinearMap.id.comp LinearMap.id)
      (TensorProduct.map H.starProjection.toLinearMap (LinearMap.id.comp LinearMap.id)) =
        TensorProduct.map LinearMap.id
          (TensorProduct.map
            (leftIsotypicSectorProjector (M.firstCutProjectorMC region) ccomponent)
            LinearMap.id)
    rw [LinearMap.id_comp, LinearMap.id_comp]
    rfl
  have hcompressed : Qcompressed.IsSymmetricProjection := by
    dsimp [Qcompressed]
    apply isSymmetricProjection_of_active_isometric_compression K Kadj Qsecond
      hKadjK hKadj_eq hQ
    rw [hKKadj]
    exact hsupport
  have hcompressed0 : Qcompressed ≠ 0 := by
    dsimp [Qcompressed]
    apply isometricCompression_ne_zero_of_active_projection K Kadj Qsecond hKadj_eq hQ hQ0
    rw [hKKadj]
    exact hsupport
  constructor
  · change (T.conjOperator Qcompressed).IsSymmetricProjection
    exact (isSymmetricProjection_conjOperator_iff T _).mpr hcompressed
  · change T.conjOperator Qcompressed ≠ 0
    intro hzero
    apply hcompressed0
    have hback :
        T.symm.conjOperator (T.conjOperator Qcompressed) = T.symm.conjOperator 0 :=
      congrArg T.symm.conjOperator hzero
    calc
      Qcompressed = T.symm.conjOperator (T.conjOperator Qcompressed) :=
        (T.symm_conjOperator_conjOperator _).symm
      _ = T.symm.conjOperator 0 := hback
      _ = 0 := by simp [Semantics.UnitaryTransport.conjOperator]

end BPTCommutingProjectorModel

end Bounds
end QEC
