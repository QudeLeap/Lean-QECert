import QEC.Bounds.BPTDisentangling.FourFactor

/-!
# BPT first- and second-cut sector decomposition

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
The zero-code branch is discharged by the existing degenerate disentangling
theorem; otherwise the first BV03 decomposition has a unique active sector.
-/
theorem firstCut_unique_active_leftIsotypicSector_or_disentangled
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region)) :
    M.Disentangled region ∨
      ∃ component : isotypicComponents
          (leftInteractionAlgebra (M.firstCutProjectorMC region))
          (M.fourFactorC region),
        M.firstCutCodeLift region * M.firstCutSectorLift region component =
            M.firstCutCodeLift region ∧
          ∀ other : isotypicComponents
              (leftInteractionAlgebra (M.firstCutProjectorMC region))
              (M.fourFactorC region),
            other ≠ component →
            M.firstCutCodeLift region * M.firstCutSectorLift region other = 0 := by
  by_cases hzero : M.codeSpace.carrier = ⊥
  · exact Or.inl (M.disentangled_of_codeSpace_carrier_eq_bot region hzero)
  · exact Or.inr
      (M.firstCut_exists_unique_active_leftIsotypicSector_of_nonzero_code region hzero hC)

set_option maxHeartbeats 800000 in
/--
The unique external-boundary-active first-cut sector carries the concrete BV03
tensor-block equations for `Pi_MC` and `Pi_CD`.  It is the `C = C' tensor C''`
half of the source factorization and is consumed jointly with the second cut
below.
-/
theorem firstCut_active_sector_tensor_blocks_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region)) :
    ∃ component : isotypicComponents
        (leftInteractionAlgebra (M.firstCutProjectorMC region))
        (M.fourFactorC region),
      M.firstCutCodeLift region * M.firstCutSectorLift region component =
          M.firstCutCodeLift region ∧
      (∀ other : isotypicComponents
          (leftInteractionAlgebra (M.firstCutProjectorMC region))
          (M.fourFactorC region),
        other ≠ component →
        M.firstCutCodeLift region * M.firstCutSectorLift region other = 0) ∧
      OverlapProjectorTensorBlockFactorization
        (M.firstCutProjectorMC region) (M.fourFactorProjectorCDLocal region) component := by
  rcases M.firstCut_exists_unique_active_leftIsotypicSector_of_nonzero_code
    region hcode hC with ⟨component, hactive, hother⟩
  have hself : LinearMap.adjoint (M.firstCutProjectorMC region) =
      M.firstCutProjectorMC region := by
    apply LinearMap.isSelfAdjoint_iff'.mp
    exact (LinearMap.isSymmetric_iff_isSelfAdjoint _).mp
      (M.firstCutProjectorMC_isSymmetric region)
  have hover : Commute
      (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region))
      (overlapLiftRight
        (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (M.fourFactorProjectorCDLocal region)) :=
    M.firstCut_overlap_commute region
  exact ⟨component, hactive, hother,
    overlapProjectorTensorBlockFactorization_of_commuting
      (M.firstCutProjectorMC region) (M.fourFactorProjectorCDLocal region)
      hself hover component⟩

/--
The `B bar(M)` projector of the second BPT cut, built from the actual `BC`
and `CD` source factors after only the explicit `B,C,D` reassociation.
-/
noncomputable def secondCutProjectorBbarM
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.Operator (Semantics.CompositeSystem (M.fourFactorB region)
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) :=
  (tensorAssociatorUnitary (M.fourFactorB region) (M.fourFactorC region)
    (M.fourFactorD region)).conjOperator
      (TensorProduct.map (M.fourFactorProjectorBCLocal region)
        (1 : Semantics.Operator (M.fourFactorD region))) *
    TensorProduct.map (1 : Semantics.Operator (M.fourFactorB region))
      (M.fourFactorProjectorCDLocal region)

/--
The second BPT cut exposes `AB` against `B tensor bar(M)`, retaining the
canonical four-factor target order `A tensor (B tensor (C tensor D))`.
-/
noncomputable def secondCutCoordinateTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))
      (M.fourFactorSystem region) :=
  tensorAssociatorUnitary (M.fourFactorA region) (M.fourFactorB region)
    (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))

/-- The full source code product in the literal second-cut overlap coordinates. -/
noncomputable def secondCutCodeLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) :=
  overlapLiftLeft
      (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
      (M.fourFactorProjectorABLocal region) *
    overlapLiftRight (A := M.fourFactorA region)
      (M.secondCutProjectorBbarM region)

/-- The physical internal-boundary isotypic measurement in second-cut coordinates. -/
noncomputable def secondCutSectorLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) :=
  overlapLiftLeft
    (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
    (TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
      (leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component))

/-- Global-to-second-cut coordinates, used to carry `hM` back to a virtual `B` sector. -/
noncomputable def secondCutGlobalCoordinateTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport L.Register
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) :=
  composeUnitaryTransport (M.fourFactorTransport region)
    (M.secondCutCoordinateTransport region).symm

/-- The second-cut associator sends the literal `AB` lift to the source `AB` factor. -/
theorem secondCutCoordinateTransport_conj_overlapLiftLeft_AB
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) :
    (M.secondCutCoordinateTransport region).conjOperator
      (overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) P) =
      M.fourFactorExtendAB region P := by
  unfold secondCutCoordinateTransport overlapLiftLeft fourFactorExtendAB
  rfl

/-- The second-cut associator sends a virtual internal-boundary lift to `B`. -/
theorem secondCutCoordinateTransport_conj_internalBoundarySectorLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorB region)) :
    (M.secondCutCoordinateTransport region).conjOperator
      (overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region)) Z)) =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map Z
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
            (1 : Semantics.Operator (M.fourFactorD region)))) := by
  unfold secondCutCoordinateTransport overlapLiftLeft
  rw [show (1 : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
        (1 : Semantics.Operator (M.fourFactorD region)) by
      symm
      exact TensorProduct.map_one]
  exact tensorAssociatorUnitary_conj_tensorMap
    (1 : Semantics.Operator (M.fourFactorA region)) Z
    (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
      (1 : Semantics.Operator (M.fourFactorD region)))

/--
Returning the physical internal-boundary lift through the second-cut
associator gives the exact `AB / B bar(M)` sector lift.
-/
theorem secondCutCoordinateTransport_symm_conj_internalBoundaryLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorB region)) :
    (M.secondCutCoordinateTransport region).symm.conjOperator
      ((M.fourFactorTransport region).conjOperator
        ((M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
          ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z))) =
      overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region)) Z) := by
  let U := M.secondCutCoordinateTransport region
  let sectorLift := overlapLiftLeft
    (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
    (TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region)) Z)
  have hfour := M.fourFactorTransport_conj_internalBoundaryLift region Z
  have hsecond := M.secondCutCoordinateTransport_conj_internalBoundarySectorLift region Z
  calc
    U.symm.conjOperator
        ((M.fourFactorTransport region).conjOperator
          ((M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
            ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z))) =
        U.symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
            (TensorProduct.map Z
              (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
                (1 : Semantics.Operator (M.fourFactorD region))))) :=
      congrArg U.symm.conjOperator hfour
    _ = U.symm.conjOperator (U.conjOperator sectorLift) := by
      exact congrArg U.symm.conjOperator hsecond.symm
    _ = sectorLift := U.symm_conjOperator_conjOperator sectorLift

/--
The literal second-cut right overlap lift is exactly the product of the
source `BC` and `CD` factors in common four-factor coordinates.
-/
theorem secondCutCoordinateTransport_conj_overlapLiftRight_BbarM
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.secondCutCoordinateTransport region).conjOperator
      (overlapLiftRight (A := M.fourFactorA region)
        (M.secondCutProjectorBbarM region)) =
      M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) *
        M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) := by
  have hmiddle : (M.fourFactorMiddleReassociate region).symm =
      unitaryLTensor (M.fourFactorA region)
        (tensorAssociatorUnitary (M.fourFactorB region) (M.fourFactorC region)
          (M.fourFactorD region)) := by
    apply unitaryTransport_ext
    rfl
  unfold secondCutCoordinateTransport overlapLiftRight
  rw [Semantics.UnitaryTransport.conjOperator_symm_conjOperator]
  unfold secondCutProjectorBbarM fourFactorExtendBC fourFactorExtendCD
  rw [hmiddle, unitaryLTensor_conj_tensorMap_left]
  simpa using
    (TensorProduct.map_mul
      (1 : Semantics.Operator (M.fourFactorA region))
      (1 : Semantics.Operator (M.fourFactorA region))
      ((tensorAssociatorUnitary (M.fourFactorB region) (M.fourFactorC region)
        (M.fourFactorD region)).conjOperator
          (TensorProduct.map (M.fourFactorProjectorBCLocal region)
            (1 : Semantics.Operator (M.fourFactorD region))))
      (TensorProduct.map (1 : Semantics.Operator (M.fourFactorB region))
        (M.fourFactorProjectorCDLocal region)))

/--
The second `AB / B bar(M)` overlap product is the full BPT code projector
after the explicit second-cut coordinate transport.
-/
theorem secondCutCoordinateTransport_conj_source_overlap_product
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.secondCutCoordinateTransport region).conjOperator
      (M.secondCutCodeLift region) =
      (M.fourFactorTransport region).conjOperator M.fullCodeProjector := by
  calc
    (M.secondCutCoordinateTransport region).conjOperator
        (M.secondCutCodeLift region) =
        (M.secondCutCoordinateTransport region).conjOperator
            (overlapLiftLeft
              (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
              (M.fourFactorProjectorABLocal region)) *
          (M.secondCutCoordinateTransport region).conjOperator
            (overlapLiftRight (A := M.fourFactorA region)
              (M.secondCutProjectorBbarM region)) := by
      unfold secondCutCodeLift
      exact Semantics.UnitaryTransport.conjOperator_mul _ _ _
    _ = M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) *
          (M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) *
            M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region)) := by
      rw [M.secondCutCoordinateTransport_conj_overlapLiftLeft_AB,
        M.secondCutCoordinateTransport_conj_overlapLiftRight_BbarM]
    _ = (M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) *
          M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region)) *
          M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) := by
      exact (mul_assoc
        (M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region))
        (M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region))
        (M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region))).symm
    _ = (M.fourFactorTransport region).conjOperator M.fullCodeProjector :=
      (M.fourFactor_codeProjector_eq_source_products region).symm

/-- The global second-cut coordinates carry the full code projector to its overlap product. -/
theorem secondCutGlobalCoordinateTransport_conj_fullCodeProjector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.secondCutGlobalCoordinateTransport region).conjOperator M.fullCodeProjector =
      M.secondCutCodeLift region := by
  change (composeUnitaryTransport (M.fourFactorTransport region)
    (M.secondCutCoordinateTransport region).symm).conjOperator M.fullCodeProjector =
      M.secondCutCodeLift region
  rw [composeUnitaryTransport_conjOperator]
  calc
    (M.secondCutCoordinateTransport region).symm.conjOperator
        ((M.fourFactorTransport region).conjOperator M.fullCodeProjector) =
        (M.secondCutCoordinateTransport region).symm.conjOperator
          ((M.secondCutCoordinateTransport region).conjOperator
            (M.secondCutCodeLift region)) := by
      exact congrArg (M.secondCutCoordinateTransport region).symm.conjOperator
        (M.secondCutCoordinateTransport_conj_source_overlap_product region).symm
    _ = M.secondCutCodeLift region :=
      (M.secondCutCoordinateTransport region).symm_conjOperator_conjOperator _

/-- The second-cut left overlap lift is the transported source `Pi_AB`. -/
theorem secondCutCoordinateTransport_conj_AB_eq_sourceAB
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.secondCutCoordinateTransport region).conjOperator
      (overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (M.fourFactorProjectorABLocal region)) =
      (M.fourFactorTransport region).conjOperator (M.projectorAB region) := by
  calc
    (M.secondCutCoordinateTransport region).conjOperator
        (overlapLiftLeft
          (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
          (M.fourFactorProjectorABLocal region)) =
        M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) :=
      M.secondCutCoordinateTransport_conj_overlapLiftLeft_AB region _
    _ = (M.fourFactorTransport region).conjOperator (M.projectorAB region) :=
      (M.fourFactorTransport_conj_projectorAB region).symm

/-- The second-cut right overlap lift is the transported source `Pi_BC Pi_CD`. -/
theorem secondCutCoordinateTransport_conj_BbarM_eq_sourceBC_mul_CD
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.secondCutCoordinateTransport region).conjOperator
      (overlapLiftRight (A := M.fourFactorA region)
        (M.secondCutProjectorBbarM region)) =
      (M.fourFactorTransport region).conjOperator
        (M.projectorBC region * M.projectorCD region) := by
  calc
    (M.secondCutCoordinateTransport region).conjOperator
        (overlapLiftRight (A := M.fourFactorA region)
          (M.secondCutProjectorBbarM region)) =
        M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) *
          M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) :=
      M.secondCutCoordinateTransport_conj_overlapLiftRight_BbarM region
    _ = (M.fourFactorTransport region).conjOperator (M.projectorBC region) *
          (M.fourFactorTransport region).conjOperator (M.projectorCD region) := by
      exact (congrArg₂ (· * ·)
        (M.fourFactorTransport_conj_projectorBC region)
        (M.fourFactorTransport_conj_projectorCD region)).symm
    _ = (M.fourFactorTransport region).conjOperator
          (M.projectorBC region * M.projectorCD region) :=
      (Semantics.UnitaryTransport.conjOperator_mul
        (M.fourFactorTransport region) (M.projectorBC region) (M.projectorCD region)).symm

/-- A concrete normalized vector in the second-cut exterior `C tensor D` factor. -/
theorem exists_normalized_fourFactorCD_vector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    ∃ eta : Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region),
      ‖eta‖ = 1 := by
  let etaC : M.fourFactorC region := EuclideanSpace.basisFun
    (Semantics.Qudit.Label
      ((M.regionSubsystem region).additionalRetainedDimensions
        (M.regionSubsystem (region ∪ M.externalBoundary region))) ) Complex
    (Semantics.Qudit.zeroLabel
      ((M.regionSubsystem region).additionalRetainedDimensions
        (M.regionSubsystem (region ∪ M.externalBoundary region))) (by
        intro site
        exact L.localDimension_positive site))
  have hetaC : ‖etaC‖ = 1 := by
    dsimp [etaC]
    simp
  rcases M.exists_normalized_fourFactorD_vector region with ⟨etaD, hetaD⟩
  refine ⟨etaC ⊗ₜ[Complex] etaD, ?_⟩
  simp [hetaC, hetaD]

/-- The literal `AB` projector used by the second cut is symmetric. -/
theorem secondCutProjectorAB_isSymmetric
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.fourFactorProjectorABLocal region).IsSymmetric := by
  let U := M.secondCutCoordinateTransport region
  let P := overlapLiftLeft
    (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
    (M.fourFactorProjectorABLocal region)
  have hP : U.conjOperator P =
      (M.fourFactorTransport region).conjOperator (M.projectorAB region) := by
    simpa [U, P] using M.secondCutCoordinateTransport_conj_AB_eq_sourceAB region
  have hsource : (M.projectorAB region).IsSymmetric :=
    (M.projectorAB_isSymmetricProjection region).isSymmetric
  have hTransport : (U.conjOperator P).IsSymmetric := by
    rw [hP]
    exact (isSymmetric_conjOperator_iff (M.fourFactorTransport region)
      (M.projectorAB region)).mpr hsource
  have hLift : P.IsSymmetric :=
    (isSymmetric_conjOperator_iff U P).mp hTransport
  rcases M.exists_normalized_fourFactorCD_vector region with ⟨eta, heta⟩
  apply isSymmetric_of_overlapLiftLeft
    (A := M.fourFactorA region) (B := M.fourFactorB region)
    (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
    (M.fourFactorProjectorABLocal region) eta heta
  simpa [P] using hLift

/-- The concrete `AB / B bar(M)` overlap pair commutes in second-cut coordinates. -/
theorem secondCut_overlap_commute
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Commute
      (overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (M.fourFactorProjectorABLocal region))
      (overlapLiftRight (A := M.fourFactorA region)
        (M.secondCutProjectorBbarM region)) := by
  let U := M.secondCutCoordinateTransport region
  let P := overlapLiftLeft
    (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
    (M.fourFactorProjectorABLocal region)
  let Q := overlapLiftRight (A := M.fourFactorA region)
    (M.secondCutProjectorBbarM region)
  have hP : U.conjOperator P =
      (M.fourFactorTransport region).conjOperator (M.projectorAB region) := by
    simpa [U, P] using M.secondCutCoordinateTransport_conj_AB_eq_sourceAB region
  have hQ : U.conjOperator Q =
      (M.fourFactorTransport region).conjOperator
        (M.projectorBC region * M.projectorCD region) := by
    simpa [U, Q] using
      M.secondCutCoordinateTransport_conj_BbarM_eq_sourceBC_mul_CD region
  change Commute P Q
  apply commute_of_conjOperator_commute U
  rw [hP, hQ]
  calc
    (M.fourFactorTransport region).conjOperator (M.projectorAB region) *
        (M.fourFactorTransport region).conjOperator
          (M.projectorBC region * M.projectorCD region) =
        (M.fourFactorTransport region).conjOperator
          (M.projectorAB region * (M.projectorBC region * M.projectorCD region)) :=
      (Semantics.UnitaryTransport.conjOperator_mul
        (M.fourFactorTransport region) (M.projectorAB region)
        (M.projectorBC region * M.projectorCD region)).symm
    _ = (M.fourFactorTransport region).conjOperator
          ((M.projectorBC region * M.projectorCD region) * M.projectorAB region) :=
      congrArg (M.fourFactorTransport region).conjOperator
        (M.projectorAB_commute_projectorBC_mul_CD region).eq
    _ = (M.fourFactorTransport region).conjOperator
          (M.projectorBC region * M.projectorCD region) *
        (M.fourFactorTransport region).conjOperator (M.projectorAB region) :=
      Semantics.UnitaryTransport.conjOperator_mul
        (M.fourFactorTransport region) (M.projectorBC region * M.projectorCD region)
        (M.projectorAB region)

/-- The physical internal-boundary measurement for a second-cut isotypic sector. -/
noncomputable def secondCutPhysicalSectorProjector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    Semantics.Operator L.Register :=
  (M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
    ((M.fourFactorBCoordinateRelabel region).symm.conjOperator
      (leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component))

/-- A physical second-cut sector is an orthogonal projection. -/
theorem secondCutPhysicalSectorProjector_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    (M.secondCutPhysicalSectorProjector region component).IsSymmetricProjection := by
  let A := M.fourFactorA region
  let B := M.fourFactorB region
  let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
  let P : Semantics.Operator (Semantics.CompositeSystem A B) :=
    M.fourFactorProjectorABLocal region
  let sector : Semantics.Operator B := leftIsotypicSectorProjector P component
  let H := composeUnitaryTransport (M.fourFactorTransport region)
    (M.secondCutCoordinateTransport region).symm
  let sectorLift : Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem A B) CD) :=
    overlapLiftLeft (C := CD)
      (TensorProduct.map (1 : Semantics.Operator A) sector)
  have hsectorProjection : sector.IsSymmetricProjection := by
    simpa [sector, P] using
      leftIsotypicSectorProjector_isSymmetricProjection P component
  have hsectorLiftProjection : sectorLift.IsSymmetricProjection := by
    dsimp [sectorLift, overlapLiftLeft]
    exact tensorMap_isSymmetricProjection
      (tensorMap_isSymmetricProjection (one_isSymmetricProjection A) hsectorProjection)
      (one_isSymmetricProjection CD)
  have hHsector :
      H.conjOperator (M.secondCutPhysicalSectorProjector region component) = sectorLift := by
    change (composeUnitaryTransport (M.fourFactorTransport region)
      (M.secondCutCoordinateTransport region).symm).conjOperator
        ((M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
          ((M.fourFactorBCoordinateRelabel region).symm.conjOperator sector)) = sectorLift
    rw [composeUnitaryTransport_conjOperator]
    simpa [A, B, CD, sectorLift] using
      M.secondCutCoordinateTransport_symm_conj_internalBoundaryLift region sector
  apply (isSymmetricProjection_conjOperator_iff H
    (M.secondCutPhysicalSectorProjector region component)).mp
  rw [hHsector]
  exact hsectorLiftProjection

/-- The full code projector commutes with every physical second-cut sector. -/
theorem fullCodeProjector_commute_secondCutPhysicalSectorProjector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    Commute M.fullCodeProjector
      (M.secondCutPhysicalSectorProjector region component) := by
  let A := M.fourFactorA region
  let B := M.fourFactorB region
  let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
  let P : Semantics.Operator (Semantics.CompositeSystem A B) :=
    M.fourFactorProjectorABLocal region
  let Q : Semantics.Operator (Semantics.CompositeSystem B CD) :=
    M.secondCutProjectorBbarM region
  let sector : Semantics.Operator B := leftIsotypicSectorProjector P component
  let H := composeUnitaryTransport (M.fourFactorTransport region)
    (M.secondCutCoordinateTransport region).symm
  let sectorLift : Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem A B) CD) :=
    overlapLiftLeft (C := CD)
      (TensorProduct.map (1 : Semantics.Operator A) sector)
  let codeLift : Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem A B) CD) :=
    overlapLiftLeft (C := CD) P * overlapLiftRight (A := A) Q
  have hself : LinearMap.adjoint P = P := by
    apply LinearMap.isSelfAdjoint_iff'.mp
    apply (LinearMap.isSymmetric_iff_isSelfAdjoint P).mp
    simpa [P] using M.secondCutProjectorAB_isSymmetric region
  have hover : Commute (overlapLiftLeft (C := CD) P)
      (overlapLiftRight (A := A) Q) := by
    simpa [A, B, CD, P, Q] using M.secondCut_overlap_commute region
  have hcodeLiftCommutes : Commute codeLift sectorLift := by
    simpa [codeLift, sectorLift] using
      (overlap_product_commutes_leftIsotypicSectorLift P Q hself hover component)
  have hHsector :
      H.conjOperator (M.secondCutPhysicalSectorProjector region component) = sectorLift := by
    change (composeUnitaryTransport (M.fourFactorTransport region)
      (M.secondCutCoordinateTransport region).symm).conjOperator
        ((M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
          ((M.fourFactorBCoordinateRelabel region).symm.conjOperator sector)) = sectorLift
    rw [composeUnitaryTransport_conjOperator]
    simpa [A, B, CD, sectorLift] using
      M.secondCutCoordinateTransport_symm_conj_internalBoundaryLift region sector
  have hHcode : H.conjOperator M.fullCodeProjector = codeLift := by
    exact M.secondCutGlobalCoordinateTransport_conj_fullCodeProjector region
  apply commute_of_conjOperator_commute H
  rw [hHcode, hHsector]
  exact hcodeLiftCommutes

/-- A physical second-cut sector is supported on the recovered region. -/
theorem secondCutPhysicalSectorProjector_supportedOnRegion
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    (M.regionSubsystem region).OperatorSupportedOnRegister
      (M.secondCutPhysicalSectorProjector region component) := by
  apply operatorSupportedOnRegister_of_subset
    (M.regionSubsystem (M.internalBoundary region)) (M.regionSubsystem region)
  · intro site hsite
    change site ∈ region
    exact (Finset.mem_inter.mp hsite).2
  · refine ⟨(M.fourFactorBCoordinateRelabel region).symm.conjOperator
      (leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component), ?_⟩
    rfl

/--
Region correctability collapses each physical internal-boundary sector in the
second `AB / B bar(M)` BV03 cut to zero or the full code projector.
-/
theorem secondCut_region_sector_dichotomy
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    M.fullCodeProjector * M.secondCutPhysicalSectorProjector region component = 0 ∨
    M.fullCodeProjector * M.secondCutPhysicalSectorProjector region component =
      M.fullCodeProjector := by
  have hInformation := M.regionErasureRecoverable_implies_noInformationOn region hM
  change M.codeSpace.projector * M.secondCutPhysicalSectorProjector region component = 0 ∨
    M.codeSpace.projector * M.secondCutPhysicalSectorProjector region component =
      M.codeSpace.projector
  exact local_commutingProjection_codeSector_eq_zero_or_codeProjector
    (M.regionSubsystem region) M.codeSpace hInformation
    (M.secondCutPhysicalSectorProjector_supportedOnRegion region component)
    (M.secondCutPhysicalSectorProjector_isSymmetricProjection region component)
    (M.fullCodeProjector_commute_secondCutPhysicalSectorProjector region component)

/--
The hM-driven physical sector dichotomy transported into literal second-cut
coordinates.  This is the `hsector` input for the second BV03 collapse.
-/
theorem secondCutCodeLift_sector_dichotomy
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    M.secondCutCodeLift region * M.secondCutSectorLift region component = 0 ∨
      M.secondCutCodeLift region * M.secondCutSectorLift region component =
        M.secondCutCodeLift region := by
  let H := M.secondCutGlobalCoordinateTransport region
  let Zx : Semantics.Operator L.Register :=
    (M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
      ((M.fourFactorBCoordinateRelabel region).symm.conjOperator
        (leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component))
  have hHcode : H.conjOperator M.fullCodeProjector = M.secondCutCodeLift region := by
    simpa [H] using M.secondCutGlobalCoordinateTransport_conj_fullCodeProjector region
  have hHsector : H.conjOperator Zx = M.secondCutSectorLift region component := by
    change (composeUnitaryTransport (M.fourFactorTransport region)
      (M.secondCutCoordinateTransport region).symm).conjOperator
        ((M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
          ((M.fourFactorBCoordinateRelabel region).symm.conjOperator
            (leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component))) =
      M.secondCutSectorLift region component
    rw [composeUnitaryTransport_conjOperator]
    simpa [secondCutSectorLift] using
      M.secondCutCoordinateTransport_symm_conj_internalBoundaryLift region
        (leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component)
  rcases M.secondCut_region_sector_dichotomy region hM component with hzero | hfull
  · left
    change M.fullCodeProjector * Zx = 0 at hzero
    calc
      M.secondCutCodeLift region * M.secondCutSectorLift region component =
          H.conjOperator M.fullCodeProjector * H.conjOperator Zx := by
        exact congrArg₂ (· * ·) hHcode.symm hHsector.symm
      _ = H.conjOperator (M.fullCodeProjector * Zx) :=
        (Semantics.UnitaryTransport.conjOperator_mul H _ _).symm
      _ = H.conjOperator 0 := congrArg H.conjOperator hzero
      _ = 0 := by
        ext vector
        simp [Semantics.UnitaryTransport.conjOperator]
  · right
    change M.fullCodeProjector * Zx = M.fullCodeProjector at hfull
    calc
      M.secondCutCodeLift region * M.secondCutSectorLift region component =
          H.conjOperator M.fullCodeProjector * H.conjOperator Zx := by
        exact congrArg₂ (· * ·) hHcode.symm hHsector.symm
      _ = H.conjOperator (M.fullCodeProjector * Zx) :=
        (Semantics.UnitaryTransport.conjOperator_mul H _ _).symm
      _ = H.conjOperator M.fullCodeProjector :=
        congrArg H.conjOperator hfull
      _ = M.secondCutCodeLift region := hHcode

/-- A double interaction coefficient of the second-cut full code overlap product. -/
noncomputable def secondCutDoubleInteractionCoefficient
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (cd cd' : Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
    (a a' : M.fourFactorA region) :
    Semantics.Operator (M.fourFactorB region) :=
  leftInteractionCoefficient
    (rightInteractionCoefficient (M.secondCutCodeLift region) cd cd') a a'

/--
Region correctability supplies the exact second-cut coefficient-sector
dichotomy required by finite isotypic-sector collapse.
-/
theorem secondCut_doubleInteractionCoefficient_sector_dichotomy
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (cd cd' : Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
    (a a' : M.fourFactorA region) :
    M.secondCutDoubleInteractionCoefficient region cd cd' a a' *
        leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component = 0 ∨
      M.secondCutDoubleInteractionCoefficient region cd cd' a a' *
        leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component =
        M.secondCutDoubleInteractionCoefficient region cd cd' a a' := by
  rcases M.secondCutCodeLift_sector_dichotomy region hM component with hzero | hfull
  · left
    have hcoeff := congrArg (fun operator =>
      leftInteractionCoefficient (rightInteractionCoefficient operator cd cd') a a') hzero
    simp only [secondCutSectorLift, overlapLiftLeft] at hcoeff
    rw [rightInteractionCoefficient_mul_leftTensor,
      leftInteractionCoefficient_mul_rightTensor] at hcoeff
    rw [rightInteractionCoefficient_zero, leftInteractionCoefficient_zero] at hcoeff
    exact hcoeff
  · right
    have hcoeff := congrArg (fun operator =>
      leftInteractionCoefficient (rightInteractionCoefficient operator cd cd') a a') hfull
    simp only [secondCutSectorLift, overlapLiftLeft] at hcoeff
    rw [rightInteractionCoefficient_mul_leftTensor,
      leftInteractionCoefficient_mul_rightTensor] at hcoeff
    exact hcoeff

/-- A zero second-cut code sector forces every corresponding coefficient to vanish. -/
theorem secondCutCodeLift_sector_eq_zero_implies_doubleInteractionCoefficient_zero
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (cd cd' : Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
    (a a' : M.fourFactorA region)
    (hzero : M.secondCutCodeLift region * M.secondCutSectorLift region component = 0) :
    M.secondCutDoubleInteractionCoefficient region cd cd' a a' *
        leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component = 0 := by
  have hcoeff := congrArg (fun operator =>
    leftInteractionCoefficient (rightInteractionCoefficient operator cd cd') a a') hzero
  simp only [secondCutSectorLift, overlapLiftLeft] at hcoeff
  rw [rightInteractionCoefficient_mul_leftTensor,
    leftInteractionCoefficient_mul_rightTensor] at hcoeff
  rw [rightInteractionCoefficient_zero, leftInteractionCoefficient_zero] at hcoeff
  exact hcoeff

/-- A full second-cut code sector fixes every corresponding coefficient. -/
theorem secondCutCodeLift_sector_eq_codeLift_implies_doubleInteractionCoefficient_eq
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (cd cd' : Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
    (a a' : M.fourFactorA region)
    (hfull : M.secondCutCodeLift region * M.secondCutSectorLift region component =
      M.secondCutCodeLift region) :
    M.secondCutDoubleInteractionCoefficient region cd cd' a a' *
        leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component =
      M.secondCutDoubleInteractionCoefficient region cd cd' a a' := by
  have hcoeff := congrArg (fun operator =>
    leftInteractionCoefficient (rightInteractionCoefficient operator cd cd') a a') hfull
  simp only [secondCutSectorLift, overlapLiftLeft] at hcoeff
  rw [rightInteractionCoefficient_mul_leftTensor,
    leftInteractionCoefficient_mul_rightTensor] at hcoeff
  exact hcoeff

/--
For a nonzero second-cut double coefficient, an inactive coefficient sector
cannot arise from a full code sector, so the physical code sector is zero.
-/
theorem secondCut_doubleInteractionCoefficient_sector_eq_zero_implies_codeLift_sector_eq_zero
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (cd cd' : Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
    (a a' : M.fourFactorA region)
    (hnonzero : M.secondCutDoubleInteractionCoefficient region cd cd' a a' ≠ 0)
    (hzero : M.secondCutDoubleInteractionCoefficient region cd cd' a a' *
      leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component = 0) :
    M.secondCutCodeLift region * M.secondCutSectorLift region component = 0 := by
  rcases M.secondCutCodeLift_sector_dichotomy region hM component with hcodeZero | hcodeFull
  · exact hcodeZero
  · exfalso
    have hcoefficientFull :=
      M.secondCutCodeLift_sector_eq_codeLift_implies_doubleInteractionCoefficient_eq
        region component cd cd' a a' hcodeFull
    rw [hzero] at hcoefficientFull
    exact hnonzero hcoefficientFull.symm

set_option maxHeartbeats 800000 in
/--
For a nonempty code, region correctability leaves exactly one second-cut
left-isotypic sector active in the actual `AB / B bar(M)` overlap product.
-/
theorem secondCut_exists_unique_active_leftIsotypicSector_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region) :
    ∃ component : isotypicComponents
        (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
        (M.fourFactorB region),
      M.secondCutCodeLift region * M.secondCutSectorLift region component =
          M.secondCutCodeLift region ∧
        ∀ other : isotypicComponents
            (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
            (M.fourFactorB region),
          other ≠ component →
          M.secondCutCodeLift region * M.secondCutSectorLift region other = 0 := by
  have hfullNonzero : M.fullCodeProjector ≠ 0 := by
    intro hzero
    apply hcode
    apply le_antisymm
    · intro vector hvector
      have hfixed : M.fullCodeProjector vector = vector :=
        M.codeSpace.projector_eq_self_of_mem hvector
      rw [hzero] at hfixed
      simpa using hfixed.symm
    · exact bot_le
  have hcodeLiftNonzero : M.secondCutCodeLift region ≠ 0 := by
    intro hzero
    apply hfullNonzero
    calc
      M.fullCodeProjector =
          (M.secondCutGlobalCoordinateTransport region).symm.conjOperator
            ((M.secondCutGlobalCoordinateTransport region).conjOperator
              M.fullCodeProjector) :=
        (M.secondCutGlobalCoordinateTransport region).symm_conjOperator_conjOperator _ |>.symm
      _ = (M.secondCutGlobalCoordinateTransport region).symm.conjOperator
            (M.secondCutCodeLift region) := by
        rw [M.secondCutGlobalCoordinateTransport_conj_fullCodeProjector]
      _ = (M.secondCutGlobalCoordinateTransport region).symm.conjOperator 0 :=
        congrArg (M.secondCutGlobalCoordinateTransport region).symm.conjOperator hzero
      _ = 0 := by simp [Semantics.UnitaryTransport.conjOperator]
  rcases exists_nonzero_doubleInteractionCoefficient_of_ne_zero
    (M.secondCutCodeLift region) hcodeLiftNonzero with ⟨cd, cd', a, a', hcoefficient⟩
  have hself : LinearMap.adjoint (M.fourFactorProjectorABLocal region) =
      M.fourFactorProjectorABLocal region := by
    apply LinearMap.isSelfAdjoint_iff'.mp
    exact (LinearMap.isSymmetric_iff_isSelfAdjoint _).mp
      (M.secondCutProjectorAB_isSymmetric region)
  have hover : Commute
      (overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (M.fourFactorProjectorABLocal region))
      (overlapLiftRight (A := M.fourFactorA region)
        (M.secondCutProjectorBbarM region)) :=
    M.secondCut_overlap_commute region
  let coefficient := M.secondCutDoubleInteractionCoefficient region cd cd' a a'
  have hcoefficient' : coefficient ≠ 0 := by
    change leftInteractionCoefficient
      (rightInteractionCoefficient (M.secondCutCodeLift region) cd cd') a a' ≠ 0
    exact hcoefficient
  have hcommute : ∀ component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region),
      Commute coefficient
        (leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component) := by
    intro component
    simpa [coefficient, secondCutDoubleInteractionCoefficient, secondCutCodeLift] using
      (doubleInteractionCoefficient_commutes_leftIsotypicSector
        (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region)
        hself hover component cd cd' a a')
  have hsector : ∀ component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region),
      coefficient * leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component = 0 ∨
        coefficient * leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component =
          coefficient := by
    intro component
    simpa [coefficient] using
      M.secondCut_doubleInteractionCoefficient_sector_dichotomy
        region hM component cd cd' a a'
  rcases exists_unique_active_leftIsotypicSector
    (M.fourFactorProjectorABLocal region) coefficient hcoefficient' hcommute hsector with
    ⟨component, hactive, hother⟩
  refine ⟨component, ?_, ?_⟩
  · rcases M.secondCutCodeLift_sector_dichotomy region hM component with hzero | hfull
    · exfalso
      have hvanish : coefficient *
          leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component = 0 := by
        change M.secondCutDoubleInteractionCoefficient region cd cd' a a' *
          leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component = 0
        exact M.secondCutCodeLift_sector_eq_zero_implies_doubleInteractionCoefficient_zero
          region component cd cd' a a' hzero
      rw [hactive] at hvanish
      exact hcoefficient' hvanish
    · exact hfull
  · intro other hne
    have hvanish : coefficient *
        leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) other = 0 :=
      hother other hne
    change M.secondCutCodeLift region * M.secondCutSectorLift region other = 0
    apply M.secondCut_doubleInteractionCoefficient_sector_eq_zero_implies_codeLift_sector_eq_zero
      region hM other cd cd' a a' hcoefficient'
    change coefficient * leftIsotypicSectorProjector
      (M.fourFactorProjectorABLocal region) other = 0
    exact hvanish

/-- The zero-code branch is already disentangled; otherwise the second cut has one active sector. -/
theorem secondCut_unique_active_leftIsotypicSector_or_disentangled
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region) :
    M.Disentangled region ∨
      ∃ component : isotypicComponents
          (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
          (M.fourFactorB region),
        M.secondCutCodeLift region * M.secondCutSectorLift region component =
            M.secondCutCodeLift region ∧
          ∀ other : isotypicComponents
              (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
              (M.fourFactorB region),
            other ≠ component →
            M.secondCutCodeLift region * M.secondCutSectorLift region other = 0 := by
  by_cases hzero : M.codeSpace.carrier = ⊥
  · exact Or.inl (M.disentangled_of_codeSpace_carrier_eq_bot region hzero)
  · exact Or.inr
      (M.secondCut_exists_unique_active_leftIsotypicSector_of_nonzero_code region hzero hM)

set_option maxHeartbeats 800000 in
/--
The unique hM-active second-cut sector carries the actual BV03 tensor-block
projector equalities.  This consumes the isotypic polar unitary rather than
recording a desired factorization as data.
-/
theorem secondCut_active_sector_tensor_blocks_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region) :
    ∃ component : isotypicComponents
        (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
        (M.fourFactorB region),
      M.secondCutCodeLift region * M.secondCutSectorLift region component =
          M.secondCutCodeLift region ∧
      (∀ other : isotypicComponents
          (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
          (M.fourFactorB region),
        other ≠ component →
        M.secondCutCodeLift region * M.secondCutSectorLift region other = 0) ∧
      OverlapProjectorTensorBlockFactorization
        (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region) component := by
  rcases M.secondCut_exists_unique_active_leftIsotypicSector_of_nonzero_code
    region hcode hM with ⟨component, hactive, hother⟩
  have hself : LinearMap.adjoint (M.fourFactorProjectorABLocal region) =
      M.fourFactorProjectorABLocal region := by
    apply LinearMap.isSelfAdjoint_iff'.mp
    exact (LinearMap.isSymmetric_iff_isSelfAdjoint _).mp
      (M.secondCutProjectorAB_isSymmetric region)
  have hover : Commute
      (overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (M.fourFactorProjectorABLocal region))
      (overlapLiftRight (A := M.fourFactorA region)
        (M.secondCutProjectorBbarM region)) :=
    M.secondCut_overlap_commute region
  exact ⟨component, hactive, hother,
    overlapProjectorTensorBlockFactorization_of_commuting
      (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region)
      hself hover component⟩

set_option maxHeartbeats 800000 in
/--
After the two correctability-driven sector collapses, the transported full
code is supported on the simultaneous active `B` and `C` sectors.  This is the
common four-factor support equation needed to compose the two BV03 block
coordinates into the source residual `B'' tensor C'` code; it is stronger than
merely exhibiting the two blocks separately.
-/
theorem joint_active_sector_code_support_of_active_cuts
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
    (M.fourFactorTransport region).conjOperator M.fullCodeProjector *
        (M.fourFactorTransport region).conjOperator
          ((M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
            ((M.fourFactorBCoordinateRelabel region).symm.conjOperator
              (leftIsotypicSectorProjector
                (M.fourFactorProjectorABLocal region) bcomponent))) *
        (M.fourFactorTransport region).conjOperator
          ((M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
            ((M.fourFactorCCoordinateRelabel region).symm.conjOperator
              (leftIsotypicSectorProjector
                (M.firstCutProjectorMC region) ccomponent))) =
      (M.fourFactorTransport region).conjOperator M.fullCodeProjector := by
  let Pi := M.fullCodeProjector
  let ZC : Semantics.Operator L.Register :=
    (M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
      ((M.fourFactorCCoordinateRelabel region).symm.conjOperator
        (leftIsotypicSectorProjector (M.firstCutProjectorMC region) ccomponent))
  let ZB : Semantics.Operator L.Register :=
    (M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
      ((M.fourFactorBCoordinateRelabel region).symm.conjOperator
        (leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) bcomponent))
  let HC := M.firstCutGlobalCoordinateTransport region
  have hHCcode : HC.conjOperator Pi = M.firstCutCodeLift region := by
    simpa [HC, Pi] using M.firstCutGlobalCoordinateTransport_conj_fullCodeProjector region
  have hHCsector : HC.conjOperator ZC = M.firstCutSectorLift region ccomponent := by
    simpa [HC, ZC] using
      M.firstCutGlobalCoordinateTransport_conj_externalBoundarySector region ccomponent
  have hCactiveTransport :
      HC.conjOperator Pi * HC.conjOperator ZC = HC.conjOperator Pi := by
    calc
      HC.conjOperator Pi * HC.conjOperator ZC =
          M.firstCutCodeLift region * M.firstCutSectorLift region ccomponent :=
        congrArg₂ (· * ·) hHCcode hHCsector
      _ = M.firstCutCodeLift region := hCactive
      _ = HC.conjOperator Pi := hHCcode.symm
  have hCphysical : Pi * ZC = Pi := by
    calc
      Pi * ZC = HC.symm.conjOperator (HC.conjOperator (Pi * ZC)) :=
        (HC.symm_conjOperator_conjOperator _).symm
      _ = HC.symm.conjOperator (HC.conjOperator Pi * HC.conjOperator ZC) := by
        rw [Semantics.UnitaryTransport.conjOperator_mul]
      _ = HC.symm.conjOperator (HC.conjOperator Pi) :=
        congrArg HC.symm.conjOperator hCactiveTransport
      _ = Pi := HC.symm_conjOperator_conjOperator Pi
  let HB := M.secondCutGlobalCoordinateTransport region
  have hHBcode : HB.conjOperator Pi = M.secondCutCodeLift region := by
    simpa [HB, Pi] using M.secondCutGlobalCoordinateTransport_conj_fullCodeProjector region
  have hHBsector : HB.conjOperator ZB = M.secondCutSectorLift region bcomponent := by
    change (composeUnitaryTransport (M.fourFactorTransport region)
      (M.secondCutCoordinateTransport region).symm).conjOperator ZB =
        M.secondCutSectorLift region bcomponent
    rw [composeUnitaryTransport_conjOperator]
    simpa [ZB, secondCutSectorLift] using
      M.secondCutCoordinateTransport_symm_conj_internalBoundaryLift region
        (leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) bcomponent)
  have hBactiveTransport :
      HB.conjOperator Pi * HB.conjOperator ZB = HB.conjOperator Pi := by
    calc
      HB.conjOperator Pi * HB.conjOperator ZB =
          M.secondCutCodeLift region * M.secondCutSectorLift region bcomponent :=
        congrArg₂ (· * ·) hHBcode hHBsector
      _ = M.secondCutCodeLift region := hBactive
      _ = HB.conjOperator Pi := hHBcode.symm
  have hBphysical : Pi * ZB = Pi := by
    calc
      Pi * ZB = HB.symm.conjOperator (HB.conjOperator (Pi * ZB)) :=
        (HB.symm_conjOperator_conjOperator _).symm
      _ = HB.symm.conjOperator (HB.conjOperator Pi * HB.conjOperator ZB) := by
        rw [Semantics.UnitaryTransport.conjOperator_mul]
      _ = HB.symm.conjOperator (HB.conjOperator Pi) :=
        congrArg HB.symm.conjOperator hBactiveTransport
      _ = Pi := HB.symm_conjOperator_conjOperator Pi
  let F := M.fourFactorTransport region
  have hjoint : Pi * ZB * ZC = Pi := by
    calc
      Pi * ZB * ZC = (Pi * ZB) * ZC := rfl
      _ = Pi * ZC := by rw [hBphysical]
      _ = Pi := hCphysical
  change F.conjOperator Pi * F.conjOperator ZB * F.conjOperator ZC = F.conjOperator Pi
  calc
    F.conjOperator Pi * F.conjOperator ZB * F.conjOperator ZC =
        F.conjOperator (Pi * ZB) * F.conjOperator ZC :=
      congrArg (fun operator => operator * F.conjOperator ZC)
        (Semantics.UnitaryTransport.conjOperator_mul F Pi ZB).symm
    _ = F.conjOperator (Pi * ZB * ZC) :=
      (Semantics.UnitaryTransport.conjOperator_mul F (Pi * ZB) ZC).symm
    _ = F.conjOperator Pi := congrArg F.conjOperator hjoint

/--
The existential active-sector statement is the preceding fixed-witness
support transport applied to the components selected by correctability.
-/
theorem twoCuts_joint_active_sector_code_support_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region)) :
    ∃ ccomponent : isotypicComponents
        (leftInteractionAlgebra (M.firstCutProjectorMC region))
        (M.fourFactorC region),
      ∃ bcomponent : isotypicComponents
          (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
          (M.fourFactorB region),
        (M.fourFactorTransport region).conjOperator M.fullCodeProjector *
            (M.fourFactorTransport region).conjOperator
              ((M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
                ((M.fourFactorBCoordinateRelabel region).symm.conjOperator
                  (leftIsotypicSectorProjector
                    (M.fourFactorProjectorABLocal region) bcomponent))) *
            (M.fourFactorTransport region).conjOperator
              ((M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
                ((M.fourFactorCCoordinateRelabel region).symm.conjOperator
                  (leftIsotypicSectorProjector
                    (M.firstCutProjectorMC region) ccomponent))) =
          (M.fourFactorTransport region).conjOperator M.fullCodeProjector := by
  let hCsector := M.firstCut_exists_unique_active_leftIsotypicSector_of_nonzero_code
    region hcode hC
  let ccomponent := Classical.choose hCsector
  have hcactive : M.firstCutCodeLift region * M.firstCutSectorLift region ccomponent =
      M.firstCutCodeLift region :=
    (Classical.choose_spec hCsector).1
  let hBsector := M.secondCut_exists_unique_active_leftIsotypicSector_of_nonzero_code
    region hcode hM
  let bcomponent := Classical.choose hBsector
  have hbactive : M.secondCutCodeLift region * M.secondCutSectorLift region bcomponent =
      M.secondCutCodeLift region :=
    (Classical.choose_spec hBsector).1
  exact ⟨ccomponent, bcomponent,
    M.joint_active_sector_code_support_of_active_cuts region ccomponent bcomponent hcactive hbactive⟩


end BPTCommutingProjectorModel

end Bounds
end QEC
