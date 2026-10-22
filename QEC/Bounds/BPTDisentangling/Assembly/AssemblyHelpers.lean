import QEC.Bounds.BPTDisentangling.Assembly.Embeddings

/-!
# BPT final assembly helpers

Small reusable bridges used by the final disentangling theorem.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

-- These internal bridges are too large to be useful as automated premises.
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "secondCutActiveCoordinateTransport_intertwines"

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/--
The fixed second-cut sector coordinates turn the active middle-sector action
into the literal `N tensor X` operation, with the outer factors untouched.
-/
theorem secondCutActiveCoordinateTransport_intertwines
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
  exact secondCutActiveCoordinateTransport_intertwinesCore UB UC U

set_option maxHeartbeats 1600000 in
/-- BPT-specialized form of the active second-cut coordinate intertwining identity. -/
theorem secondCutJointActiveBlockTransport_intertwines_activeSectorUnitary
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (U : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex))
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex))) :
    let T := M.secondCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC
    let Wactive := jointBCSectorActiveUnitary (A := M.fourFactorA region)
      (D := M.fourFactorD region) (bcomponent.1.restrictScalars Complex)
      (ccomponent.1.restrictScalars Complex)
      (activeSectorJointBCUnitary
        (bcomponent.1.restrictScalars Complex) (ccomponent.1.restrictScalars Complex) UB UC U)
    let Vcommon := unitaryLTensor
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
      (unitaryRTensor U
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
          (M.fourFactorD region)))
    T.conjOperator Wactive.toLinearEquiv.toLinearMap =
      Vcommon.toLinearEquiv.toLinearMap := by
  apply unitaryTransport_conjOperator_eq_of_intertwines
  simpa [secondCutJointActiveBlockTransport] using
    (secondCutActiveCoordinateTransport_intertwines UB UC U)

/--
Embed the selected `A tensor W_B tensor N_B` coordinates of the active block
back into the concrete selected subsystem of `region`.
-/
noncomputable def activeSelectedEmbedding
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {nB : Nat} [NeZero nB]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB))) :
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
      (isotypicLiftedMultiplicity.{0} nB)) →ₗᵢ[Complex]
      (M.regionSubsystem region).selectedSystem :=
  M.activeSelectedEmbeddingCore region bcomponent WB UB

/--
Embed the complement `C' tensor (C'' tensor D)` coordinates of the active
block back into the concrete complement subsystem of `region`.
-/
noncomputable def activeComplementEmbedding
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC : Nat} [NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC))) :
    (Semantics.CompositeSystem (WC.restrictScalars Complex)
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region))) →ₗᵢ[Complex]
      (M.regionSubsystem region).complementSystem :=
  M.activeComplementEmbeddingCore region ccomponent WC UC

set_option maxHeartbeats 1600000 in
/-- The selected/complement embedding expressed in the original region coordinates. -/
noncomputable def finalAssemblyInputEmbedding
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC))) :=
  (M.fourFactorTransport region).toLinearEquiv.toLinearMap.comp
    ((M.regionSubsystem region).registerFactorization.symm.toLinearEquiv.toLinearMap.comp
      (TensorProduct.map
        (M.activeSelectedEmbeddingCore region bcomponent WB UB).toLinearMap
        (M.activeComplementEmbeddingCore region ccomponent WC UC).toLinearMap))

set_option maxHeartbeats 1600000 in
/-- The same embedding expressed through the active block and final product regrouping. -/
noncomputable def finalAssemblyOutputEmbedding
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC))) :=
  (fourFactorJointBCSectorEmbedding (A := M.fourFactorA region)
    (D := M.fourFactorD region) (bcomponent.1.restrictScalars Complex)
    (ccomponent.1.restrictScalars Complex)).comp
    ((M.secondCutJointActiveBlockTransport
      region bcomponent ccomponent WB WC UB UC).symm.toLinearEquiv.toLinearMap.comp
      ((tensorAssociatorUnitary
        (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
          (WC.restrictScalars Complex))
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
          (M.fourFactorD region))).toLinearEquiv.toLinearMap.comp
        (productBlockRegrouping (A := M.fourFactorA region)
          (W := WB.restrictScalars Complex) (N := isotypicLiftedMultiplicity.{0} nB)
          (X := WC.restrictScalars Complex)
          (D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
            (M.fourFactorD region))).symm.toLinearEquiv.toLinearMap))

set_option maxHeartbeats 1600000 in
/-- The two named final-assembly embeddings are the same coordinate map. -/
theorem finalAssemblyInputEmbedding_eq_outputEmbedding
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC))) :
    M.finalAssemblyInputEmbedding region bcomponent ccomponent WB WC UB UC =
      M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC := by
  simpa only [finalAssemblyInputEmbedding, finalAssemblyOutputEmbedding] using
    (M.fourFactorTransport_comp_activeRegionEmbeddingsCore
      region bcomponent ccomponent WB WC UB UC)

set_option maxHeartbeats 4000000 in
/-- The input embedding in the exact two-transport normal form used by final assembly. -/
theorem finalAssemblyInputEmbedding_eq_twoTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC))) :
    (M.fourFactorTransport region).toLinearEquiv.toLinearMap.comp
        ((M.regionSubsystem region).registerFactorization.symm.toLinearEquiv.toLinearMap.comp
          (TensorProduct.map
            (M.activeSelectedEmbedding region bcomponent WB UB).toLinearMap
            (M.activeComplementEmbedding region ccomponent WC UC).toLinearMap)) =
      M.finalAssemblyInputEmbedding region bcomponent ccomponent WB WC UB UC := by
  rfl

/-- Transporting an isometric lift through a unitary transports its embedding. -/
theorem unitaryTransport_conj_isometric_lift
    {S H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (T : Semantics.UnitaryTransport H K) (J : S →ₗ[Complex] H)
    (P : Semantics.Operator S) :
    T.conjOperator (J.comp (P.comp (LinearMap.adjoint J))) =
      (T.toLinearEquiv.toLinearMap.comp J).comp
        (P.comp (LinearMap.adjoint (T.toLinearEquiv.toLinearMap.comp J))) := by
  unfold Semantics.UnitaryTransport.conjOperator
  rw [LinearMap.adjoint_comp, Semantics.UnitaryTransport.adjoint_toLinearMap]
  simp only [LinearMap.comp_assoc]

/--
Transport an already factored isometric lift through two unitary coordinate
changes without reopening the concrete operator definitions.
-/
theorem two_unitary_conj_isometric_lift_of_factorization
    {S H K R : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup R] [InnerProductSpace Complex R] [Semantics.FiniteQuantumSystem R]
    (Tinner : Semantics.UnitaryTransport H K)
    (Touter : Semantics.UnitaryTransport K R)
    (J : S →ₗ[Complex] H) (P : Semantics.Operator S)
    (Q : Semantics.Operator H)
    (E : S →ₗ[Complex] R)
    (hQ : Q = J.comp (P.comp (LinearMap.adjoint J)))
    (hE : Touter.toLinearEquiv.toLinearMap.comp
        (Tinner.toLinearEquiv.toLinearMap.comp J) = E) :
    Touter.conjOperator (Tinner.conjOperator Q) =
      E.comp (P.comp (LinearMap.adjoint E)) := by
  rw [hQ]
  rw [unitaryTransport_conj_isometric_lift Tinner J P]
  rw [unitaryTransport_conj_isometric_lift Touter
    (Tinner.toLinearEquiv.toLinearMap.comp J) P]
  rw [hE]

/-- Two operators are equal when their factorizations differ only by a named embedding equality. -/
theorem eq_of_common_isometric_factorization
    {S H : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    (A B : Semantics.Operator H) (P : Semantics.Operator S)
    (Eout Eleft : S →ₗ[Complex] H)
    (hA : A = Eout.comp (P.comp (LinearMap.adjoint Eout)))
    (hE : Eleft = Eout)
    (hB : B = Eleft.comp (P.comp (LinearMap.adjoint Eleft))) :
    A = B := by
  calc
    A = Eout.comp (P.comp (LinearMap.adjoint Eout)) := hA
    _ = Eleft.comp (P.comp (LinearMap.adjoint Eleft)) := by rw [hE]
    _ = B := hB.symm

/-- Pull a common isometric factorization back through a unitary coordinate change. -/
theorem eq_of_common_isometric_factorization_under_unitary
    {S H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (F : Semantics.UnitaryTransport H K)
    (A B : Semantics.Operator H) (P : Semantics.Operator S)
    (Eout Eleft : S →ₗ[Complex] K)
    (hA : F.conjOperator A = Eout.comp (P.comp (LinearMap.adjoint Eout)))
    (hE : Eleft = Eout)
    (hB : F.conjOperator B = Eleft.comp (P.comp (LinearMap.adjoint Eleft))) :
    A = B := by
  have hConj : F.conjOperator A = F.conjOperator B :=
    eq_of_common_isometric_factorization
      (F.conjOperator A) (F.conjOperator B) P Eout Eleft hA hE hB
  calc
    A = F.symm.conjOperator (F.conjOperator A) :=
      (F.symm_conjOperator_conjOperator _).symm
    _ = F.symm.conjOperator (F.conjOperator B) := congrArg F.symm.conjOperator hConj
    _ = B := F.symm_conjOperator_conjOperator _

/--
Tensoring a selected rank-one isometric lift with an arbitrary complement
operator is the corresponding joint isometric lift.
-/
theorem tensorMap_rankOne_isometric_lift
    {S T H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup T] [InnerProductSpace Complex T] [Semantics.FiniteQuantumSystem T]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (eSel : S →ₗ[Complex] H) (heSel : (LinearMap.adjoint eSel).comp eSel =
      (1 : Semantics.Operator S))
    (eComp : T →ₗ[Complex] K) (phi : S) (P : Semantics.Operator T) :
    TensorProduct.map (InnerProductSpace.rankOne Complex (eSel phi) (eSel phi)).toLinearMap
        (eComp.comp (P.comp (LinearMap.adjoint eComp))) =
      (TensorProduct.map eSel eComp).comp
        ((TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap P).comp
          (LinearMap.adjoint (TensorProduct.map eSel eComp))) := by
  rw [← isometric_lift_rankOne_self eSel heSel phi]
  rw [TensorProduct.adjoint_map, ← TensorProduct.map_comp, ← TensorProduct.map_comp]

/-- Recover inner-product preservation from concrete linearity and norm preservation. -/
theorem inner_map_map_of_map_add_map_sub_map_smul_norm
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    (f : H → K)
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsub : ∀ x y, f (x - y) = f x - f y)
    (hsmul : ∀ (c : Complex) x, f (c • x) = c • f x)
    (hnorm : ∀ x, ‖f x‖ = ‖x‖)
    (x y : H) : inner Complex (f x) (f y) = inner Complex x y := by
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
  have hsubI : f x - (RCLike.I : Complex) • f y =
      f (x - (RCLike.I : Complex) • y) := by
    calc
      f x - (RCLike.I : Complex) • f y =
          f x - f ((RCLike.I : Complex) • y) := by rw [hsmul]
      _ = f (x - (RCLike.I : Complex) • y) :=
        (hsub x ((RCLike.I : Complex) • y)).symm
  have haddI : f x + (RCLike.I : Complex) • f y =
      f (x + (RCLike.I : Complex) • y) := by
    calc
      f x + (RCLike.I : Complex) • f y =
          f x + f ((RCLike.I : Complex) • y) := by rw [hsmul]
      _ = f (x + (RCLike.I : Complex) • y) :=
        (hadd x ((RCLike.I : Complex) • y)).symm
  rw [← hadd, ← hsub, hsubI, haddI]
  rw [hnorm, hnorm, hnorm, hnorm]

/-- A norm-preserving linear map is a left inverse to its finite-dimensional adjoint. -/
theorem adjoint_comp_self_of_norm_map
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (hnorm : ∀ x, ‖J x‖ = ‖x‖) :
    (LinearMap.adjoint J).comp J = (1 : Semantics.Operator H) := by
  apply LinearMap.ext
  intro x
  apply ext_inner_right Complex
  intro y
  simp only [LinearMap.comp_apply, Module.End.one_apply]
  rw [LinearMap.adjoint_inner_left]
  exact inner_map_map_of_map_add_map_sub_map_smul_norm
    (fun z => J z)
    (fun a b => J.map_add a b)
    (fun a b => J.map_sub a b)
    (fun c z => J.map_smul c z)
    hnorm x y

/-- A norm-preserving linear lift preserves symmetric projections. -/
theorem isSymmetricProjection_lift_of_norm_map
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (hnorm : ∀ x, ‖J x‖ = ‖x‖)
    (P : Semantics.Operator H) (hP : P.IsSymmetricProjection) :
    (J.comp (P.comp (LinearMap.adjoint J))).IsSymmetricProjection :=
  isSymmetricProjection_isometric_lift J (adjoint_comp_self_of_norm_map J hnorm) P hP

/-- Compressing a conjugated operator through the transported embedding changes no block data. -/
theorem compression_conjOperator_comp_unitary
    {S H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (J : S →ₗ[Complex] H)
    (P : Semantics.Operator H) :
    (LinearMap.adjoint (U.toLinearEquiv.toLinearMap.comp J)).comp
        ((U.conjOperator P).comp (U.toLinearEquiv.toLinearMap.comp J)) =
      (LinearMap.adjoint J).comp (P.comp J) := by
  rw [LinearMap.adjoint_comp, Semantics.UnitaryTransport.adjoint_toLinearMap]
  apply LinearMap.ext
  intro x
  simp [Semantics.UnitaryTransport.conjOperator, LinearMap.comp_apply]

/-- Tensor a rank-one operator on the left with an arbitrary finite-system operator. -/
noncomputable def rankOneTensorOperator
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (v : H) (P : Semantics.Operator K) :
    Semantics.Operator (Semantics.CompositeSystem H K) :=
  TensorProduct.map (InnerProductSpace.rankOne Complex v v).toLinearMap P

/-- A normalized rank-one tensor a symmetric projection is a symmetric projection. -/
theorem rankOneTensorOperator_isSymmetricProjection
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (v : H) (hv : ‖v‖ = 1) (P : Semantics.Operator K)
    (hP : P.IsSymmetricProjection) :
    (rankOneTensorOperator v P).IsSymmetricProjection := by
  exact tensorMap_isSymmetricProjection
    (InnerProductSpace.isSymmetricProjection_rankOne_self (𝕜 := Complex) hv) hP

/-- Short name for the active complement coordinates used in final assembly. -/
abbrev ActiveComplementDomain
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (nC : Nat)
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) : Type :=
  Semantics.CompositeSystem (WC.restrictScalars Complex)
    (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region))

/-- Short name for the physical complement system used in final assembly. -/
abbrev ActiveComplementCodomain
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) : Type :=
  (M.regionSubsystem region).complementSystem

/-- Common coordinates after the middle active unitary and before product regrouping. -/
abbrev FinalActiveProductDomain
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (nB nC : Nat)
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) : Type :=
  Semantics.CompositeSystem
    (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex))
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region)))

set_option maxHeartbeats 1600000 in
/-- The final common-coordinate rank-one product before regrouping. -/
noncomputable def finalActiveProductOperator
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (phi : Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
    (n0 : isotypicLiftedMultiplicity.{0} nB)
    (c0 : WC.restrictScalars Complex)
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region))) :
    Semantics.Operator (FinalActiveProductDomain M region nB nC WB WC) :=
  TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap
    (TensorProduct.map
      (InnerProductSpace.rankOne Complex
        (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
          (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex))
        (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
          (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex))).toLinearMap P_D)

/-- Abstract algebra behind the two fixed active transports in final assembly. -/
theorem finalProductTransport
    {A N X R : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup R] [InnerProductSpace Complex R] [Semantics.FiniteQuantumSystem R]
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem N X)
      (Semantics.CompositeSystem N X))
    (phi : A) (Q : Semantics.Operator (Semantics.CompositeSystem N
      (Semantics.CompositeSystem X R)))
    (Z : Semantics.Operator (Semantics.CompositeSystem A
      (Semantics.CompositeSystem (Semantics.CompositeSystem N X) R)))
    (n0 : N) (c0 : X) (P : Semantics.Operator R)
    (hjoint : Z = (unitaryLTensor A (tensorAssociatorUnitary N X R).symm).conjOperator
      (rankOneTensorOperator phi Q))
    (hproduct : (unitaryRTensor U R).conjOperator
      ((tensorAssociatorUnitary N X R).symm.conjOperator Q) =
        TensorProduct.map (InnerProductSpace.rankOne Complex
          (n0 ⊗ₜ[Complex] c0) (n0 ⊗ₜ[Complex] c0)).toLinearMap P) :
    (unitaryLTensor A (unitaryRTensor U R)).conjOperator Z =
      TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap
        (TensorProduct.map (InnerProductSpace.rankOne Complex
          (n0 ⊗ₜ[Complex] c0) (n0 ⊗ₜ[Complex] c0)).toLinearMap P) := by
  rw [hjoint]
  dsimp only [rankOneTensorOperator]
  rw [unitaryLTensor_conj_tensorMap, unitaryLTensor_conj_tensorMap]
  exact congrArg
    (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap) hproduct

set_option maxHeartbeats 800000 in
/-- The two fixed active transports assemble the final common-coordinate product operator. -/
theorem finalActiveProductOperator_of_joint_product
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (U : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex))
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex)))
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region)))
    (Qprime : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (WC.restrictScalars Complex)
          (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
            (M.fourFactorD region)))))
    (Z : Semantics.Operator (FinalActiveProductDomain M region nB nC WB WC))
    (phi : Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
    (n0 : isotypicLiftedMultiplicity.{0} nB)
    (c0 : WC.restrictScalars Complex)
    (hjoint : Z =
        (unitaryLTensor
          (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
          (tensorAssociatorUnitary (isotypicLiftedMultiplicity.{0} nB)
            (WC.restrictScalars Complex)
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
              (M.fourFactorD region))).symm).conjOperator
          (rankOneTensorOperator phi Qprime))
    (hproduct :
      (unitaryRTensor U
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
          (M.fourFactorD region))).conjOperator
          ((tensorAssociatorUnitary (isotypicLiftedMultiplicity.{0} nB)
            (WC.restrictScalars Complex)
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
              (M.fourFactorD region))).symm.conjOperator Qprime) =
        TensorProduct.map
          (InnerProductSpace.rankOne Complex
            (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
              (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex))
            (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
              (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex))).toLinearMap P_D) :
    let Vcommon := unitaryLTensor
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
      (unitaryRTensor U
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
          (M.fourFactorD region)))
    Vcommon.conjOperator Z =
      M.finalActiveProductOperator region WB WC phi n0 c0 P_D := by
  simpa only [finalActiveProductOperator] using
    (@finalProductTransport
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
      (isotypicLiftedMultiplicity.{0} nB)
      (WC.restrictScalars Complex)
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region))
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      U phi Qprime Z n0 c0 P_D hjoint hproduct)

set_option maxHeartbeats 1600000 in
/-- The canonical four-factor joint block is the literal second-cut joint compression. -/
theorem fourFactorJointBCSectorCompression_eq_secondCutCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    let J := fourFactorJointBCSectorEmbedding (A := M.fourFactorA region)
      (D := M.fourFactorD region) pB pC
    let Jright := jointBCSectorEmbeddingRight (A := M.fourFactorA region)
      (D := M.fourFactorD region) pB pC
    let P4 := (M.fourFactorTransport region).conjOperator M.fullCodeProjector
    (LinearMap.adjoint J).comp (P4.comp J) =
      (LinearMap.adjoint Jright).comp ((M.secondCutCodeLift region).comp Jright) := by
  let U := M.secondCutCoordinateTransport region
  let J := fourFactorJointBCSectorEmbedding (A := M.fourFactorA region)
    (D := M.fourFactorD region) pB pC
  let Jright := jointBCSectorEmbeddingRight (A := M.fourFactorA region)
    (D := M.fourFactorD region) pB pC
  let P4 := (M.fourFactorTransport region).conjOperator M.fullCodeProjector
  change (LinearMap.adjoint J).comp (P4.comp J) =
    (LinearMap.adjoint Jright).comp ((M.secondCutCodeLift region).comp Jright)
  have hcode : U.conjOperator (M.secondCutCodeLift region) = P4 := by
    simpa [U, P4] using M.secondCutCoordinateTransport_conj_source_overlap_product region
  calc
    (LinearMap.adjoint J).comp (P4.comp J) =
        (LinearMap.adjoint J).comp
          ((U.conjOperator (M.secondCutCodeLift region)).comp J) := by
      exact congrArg
        (fun Q : Semantics.Operator (M.fourFactorSystem region) =>
          (LinearMap.adjoint J).comp (Q.comp J)) hcode.symm
    _ = (LinearMap.adjoint Jright).comp ((M.secondCutCodeLift region).comp Jright) := by
      simpa [J, Jright, U, fourFactorJointBCSectorEmbedding,
        secondCutCoordinateTransport] using
        (@compression_conjOperator_comp_unitary
          (Semantics.CompositeSystem
            (Semantics.CompositeSystem (M.fourFactorA region) pB)
            (Semantics.CompositeSystem pC (M.fourFactorD region)))
          (Semantics.CompositeSystem
            (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
            (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))
          (M.fourFactorSystem region)
          inferInstance inferInstance inferInstance
          inferInstance inferInstance inferInstance
          inferInstance inferInstance inferInstance
          U Jright (M.secondCutCodeLift region))

/-- The active complement embedding with canonical Hilbert-space module instances. -/
noncomputable def activeComplementEmbeddingLinearMap
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC : Nat} [NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC))) :
    ActiveComplementDomain M region nC WC →ₗ[Complex]
      ActiveComplementCodomain M region := by
  let eComp := M.activeComplementEmbedding region ccomponent WC UC
  exact
    { toFun := fun x => eComp x
      map_add' := fun x y => eComp.map_add x y
      map_smul' := fun c x => by
        change eComp.toLinearMap (c • x) = c • eComp.toLinearMap x
        exact eComp.toLinearMap.map_smul c x }

set_option maxHeartbeats 200000 in
/-- The canonical active complement map is a left inverse to its adjoint. -/
theorem activeComplementEmbedding_adjoint_comp_self
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC : Nat} [NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC))) :
    let E := M.activeComplementEmbedding region ccomponent WC UC
    (LinearMap.adjoint E.toLinearMap).comp E.toLinearMap =
      (1 : Semantics.Operator
        (ActiveComplementDomain M region nC WC)) := by
  dsimp only
  exact @linearIsometry_adjoint_comp_self
    (ActiveComplementDomain M region nC WC) (ActiveComplementCodomain M region)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (M.activeComplementEmbedding region ccomponent WC UC)


/-- Lift a complement operator through the concrete active-sector embedding. -/
noncomputable def activeComplementProjector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC : Nat} [NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (P : Semantics.Operator (ActiveComplementDomain M region nC WC)) :
    Semantics.Operator (ActiveComplementCodomain M region) :=
  let E := M.activeComplementEmbedding region ccomponent WC UC
  E.toLinearMap.comp (P.comp (LinearMap.adjoint E.toLinearMap))

set_option maxHeartbeats 200000 in
/-- The active complement lift preserves symmetric projections. -/
theorem activeComplementProjector_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC : Nat} [NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (P : Semantics.Operator (ActiveComplementDomain M region nC WC))
    (hP : @LinearMap.IsSymmetricProjection Complex
      (ActiveComplementDomain M region nC WC) _ _ _ P) :
    @LinearMap.IsSymmetricProjection Complex
      (ActiveComplementCodomain M region) _ _ _
      (M.activeComplementProjector region ccomponent WC UC P) := by
  let E := M.activeComplementEmbedding region ccomponent WC UC
  exact @isSymmetricProjection_isometric_lift
    (ActiveComplementDomain M region nC WC) (ActiveComplementCodomain M region)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    E.toLinearMap
    (@linearIsometry_adjoint_comp_self
      (ActiveComplementDomain M region nC WC) (ActiveComplementCodomain M region)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance E)
    P hP

end BPTCommutingProjectorModel

end Bounds
end QEC
