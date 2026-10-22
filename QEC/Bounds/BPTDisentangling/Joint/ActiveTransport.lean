import QEC.Bounds.BPTDisentangling.Joint.Sector

/-!
# BPT joint active-sector transport

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
The prescribed active `pB tensor pC` operation underlying the ambient
`activeSectorPhysicalUnitary`.
-/
noncomputable def activeSectorJointBCUnitary
    {B C WB NB WC NC : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup WB] [InnerProductSpace Complex WB] [Semantics.FiniteQuantumSystem WB]
    [NormedAddCommGroup NB] [InnerProductSpace Complex NB] [Semantics.FiniteQuantumSystem NB]
    [NormedAddCommGroup WC] [InnerProductSpace Complex WC] [Semantics.FiniteQuantumSystem WC]
    [NormedAddCommGroup NC] [InnerProductSpace Complex NC] [Semantics.FiniteQuantumSystem NC]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (UB : Semantics.UnitaryTransport pB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport pC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    Semantics.UnitaryTransport (Semantics.CompositeSystem pB pC)
      (Semantics.CompositeSystem pB pC) :=
  conjugateUnitaryTransport (activeSectorCoordinateTransport pB pC UB UC)
    (unitaryLTensor WB (unitaryRTensor U NC))

/--
The physical active-sector extension has exactly the prescribed action on the
joint subtype embedding.  Its unconstrained orthogonal complement never
enters this equality.
-/
theorem activeSectorPhysicalUnitary_intertwines_submoduleTensorEmbedding
    {B C WB NB WC NC : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup WB] [InnerProductSpace Complex WB] [Semantics.FiniteQuantumSystem WB]
    [NormedAddCommGroup NB] [InnerProductSpace Complex NB] [Semantics.FiniteQuantumSystem NB]
    [NormedAddCommGroup WC] [InnerProductSpace Complex WC] [Semantics.FiniteQuantumSystem WC]
    [NormedAddCommGroup NC] [InnerProductSpace Complex NC] [Semantics.FiniteQuantumSystem NC]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (UB : Semantics.UnitaryTransport pB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport pC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    (activeSectorPhysicalUnitary pB pC UB UC U).toLinearEquiv.toLinearMap.comp
        (submoduleTensorEmbedding pB pC).toLinearMap =
      (submoduleTensorEmbedding pB pC).toLinearMap.comp
        (activeSectorJointBCUnitary pB pC UB UC U).toLinearEquiv.toLinearMap := by
  simpa [activeSectorJointBCUnitary] using
    (activeSectorPhysicalUnitary_intertwines_embedding pB pC UB UC U)

/--
The D3 physical BC lift intertwines the D4 joint active embedding with the
same coordinate action on its retained sector.
-/
theorem fourFactorBCUnitaryTransport_activeSector_intertwines_jointBCSectorEmbedding
    {A B C D WB NB WC NC : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    [NormedAddCommGroup WB] [InnerProductSpace Complex WB] [Semantics.FiniteQuantumSystem WB]
    [NormedAddCommGroup NB] [InnerProductSpace Complex NB] [Semantics.FiniteQuantumSystem NB]
    [NormedAddCommGroup WC] [InnerProductSpace Complex WC] [Semantics.FiniteQuantumSystem WC]
    [NormedAddCommGroup NC] [InnerProductSpace Complex NC] [Semantics.FiniteQuantumSystem NC]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (UB : Semantics.UnitaryTransport pB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport pC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    (fourFactorBCUnitaryTransport (A := A) (D := D)
      (activeSectorPhysicalUnitary pB pC UB UC U)).toLinearEquiv.toLinearMap.comp
        (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC) =
      (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC).comp
        (jointBCSectorActiveUnitary (A := A) pB pC
          (activeSectorJointBCUnitary pB pC UB UC U)).toLinearEquiv.toLinearMap := by
  exact fourFactorBCUnitaryTransport_intertwines_jointBCSectorEmbedding
    (A := A) (D := D) pB pC (activeSectorPhysicalUnitary pB pC UB UC U)
    (activeSectorJointBCUnitary pB pC UB UC U)
    (activeSectorPhysicalUnitary_intertwines_submoduleTensorEmbedding pB pC UB UC U)

/--
The D3 physical lift transports the D4 joint compression by the corresponding
active-sector coordinate unitary.
-/
theorem fourFactorBCUnitaryTransport_activeSector_conjOperator_compression
    {A B C D WB NB WC NC : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    [NormedAddCommGroup WB] [InnerProductSpace Complex WB] [Semantics.FiniteQuantumSystem WB]
    [NormedAddCommGroup NB] [InnerProductSpace Complex NB] [Semantics.FiniteQuantumSystem NB]
    [NormedAddCommGroup WC] [InnerProductSpace Complex WC] [Semantics.FiniteQuantumSystem WC]
    [NormedAddCommGroup NC] [InnerProductSpace Complex NC] [Semantics.FiniteQuantumSystem NC]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (UB : Semantics.UnitaryTransport pB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport pC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC))
    (P : Semantics.Operator
      (Semantics.CompositeSystem A (Semantics.CompositeSystem B (Semantics.CompositeSystem C D)))) :
    (LinearMap.adjoint (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC)).comp
        (((fourFactorBCUnitaryTransport (A := A) (D := D)
          (activeSectorPhysicalUnitary pB pC UB UC U)).conjOperator P).comp
          (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC)) =
      (jointBCSectorActiveUnitary (A := A) pB pC
        (activeSectorJointBCUnitary pB pC UB UC U)).conjOperator
        ((LinearMap.adjoint (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC)).comp
          (P.comp (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC))) := by
  exact fourFactorBCUnitaryTransport_conjOperator_compression
    (A := A) (D := D) pB pC (activeSectorPhysicalUnitary pB pC UB UC U)
    (activeSectorJointBCUnitary pB pC UB UC U)
    (activeSectorPhysicalUnitary_intertwines_submoduleTensorEmbedding pB pC UB UC U) P

/--
The four-factor BC unitary transport has the literal `R† (1 tensor E tensor
1) R` operator as its linear map.
-/
theorem fourFactorBCUnitaryTransport_toLinearMap_eq_middleExtension
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (E : Semantics.UnitaryTransport (Semantics.CompositeSystem B C)
      (Semantics.CompositeSystem B C)) :
    (fourFactorBCUnitaryTransport (A := A) (D := D) E).toLinearEquiv.toLinearMap =
      (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).symm.conjOperator
        (TensorProduct.map (1 : Semantics.Operator A)
          (TensorProduct.map E.toLinearEquiv.toLinearMap
            (1 : Semantics.Operator D))) := by
  rfl

/--
The model's named middle reassociation is definitionally the generic tensor
associator transport used by `fourFactorBCUnitaryTransport`.
-/
theorem fourFactorMiddleReassociate_eq_unitaryLTensor_associator_symm
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.fourFactorMiddleReassociate region =
      unitaryLTensor (M.fourFactorA region)
        (tensorAssociatorUnitary (M.fourFactorB region)
          (M.fourFactorC region) (M.fourFactorD region)).symm := by
  rfl

/--
The D3/D4 four-factor BC unitary is exactly `fourFactorExtendBC` applied to
its physical middle unitary.  This is an equality of maps, not merely an
agreement on the active sector.
-/
theorem fourFactorBCUnitaryTransport_toLinearMap_eq_fourFactorExtendBC
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (E : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region))
      (Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region))) :
    (fourFactorBCUnitaryTransport (A := M.fourFactorA region)
      (D := M.fourFactorD region) E).toLinearEquiv.toLinearMap =
      M.fourFactorExtendBC region E.toLinearEquiv.toLinearMap := by
  unfold fourFactorExtendBC
  rw [M.fourFactorMiddleReassociate_eq_unitaryLTensor_associator_symm]
  exact fourFactorBCUnitaryTransport_toLinearMap_eq_middleExtension E

/--
Transporting the physical boundary unitary to four-factor coordinates gives
the exact D3/D4 BC unitary transport, rather than only its active restriction.
-/
theorem fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary_eq_fourFactorBCUnitaryTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {WB NB WC NC : Type} [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC]
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport pB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport pC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    (M.fourFactorTransport region).conjOperator
      (M.activeSectorBoundaryGlobalUnitary region pB pC UB UC U).toLinearEquiv.toLinearMap =
      (fourFactorBCUnitaryTransport (A := M.fourFactorA region)
        (D := M.fourFactorD region)
        (activeSectorPhysicalUnitary pB pC UB UC U)).toLinearEquiv.toLinearMap := by
  rw [M.fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary]
  exact (M.fourFactorBCUnitaryTransport_toLinearMap_eq_fourFactorExtendBC
    region (activeSectorPhysicalUnitary pB pC UB UC U)).symm

/--
If a transport carries an ambient unitary map to a second ambient unitary map,
then transporting a conjugated operator is conjugation of the transported
operator.  This is stated at the map level so it applies to the physical
boundary lift and its four-factor representative without any assertion about
the orthogonal complement of an active sector.
-/
theorem transport_conjOperator_conjOperator_of_conj_toLinearMap_eq
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (T : Semantics.UnitaryTransport H K) (U : Semantics.UnitaryTransport H H)
    (V : Semantics.UnitaryTransport K K)
    (htransport : T.conjOperator U.toLinearEquiv.toLinearMap =
      V.toLinearEquiv.toLinearMap)
    (P : Semantics.Operator H) :
    T.conjOperator (U.conjOperator P) = V.conjOperator (T.conjOperator P) := by
  have hmap : T.toLinearEquiv.toLinearMap.comp
      (U.toLinearEquiv.toLinearMap.comp T.symm.toLinearEquiv.toLinearMap) =
      V.toLinearEquiv.toLinearMap := by
    simpa [Semantics.UnitaryTransport.conjOperator,
      Semantics.UnitaryTransport.symm_toLinearEquiv] using htransport
  have hVinv : V.toLinearEquiv.symm.toLinearMap =
      T.toLinearEquiv.toLinearMap.comp
        (U.toLinearEquiv.symm.toLinearMap.comp T.toLinearEquiv.symm.toLinearMap) := by
    have hadj := congrArg LinearMap.adjoint hmap
    simp only [LinearMap.adjoint_comp,
      Semantics.UnitaryTransport.symm_toLinearEquiv,
      T.adjoint_symm_toLinearMap, U.adjoint_toLinearMap,
      T.adjoint_toLinearMap, V.adjoint_toLinearMap] at hadj
    simpa only [LinearMap.comp_assoc] using hadj.symm
  unfold Semantics.UnitaryTransport.conjOperator
  rw [← hmap, hVinv]
  ext x
  simp [LinearMap.comp_apply]

/--
The physical boundary unitary and the canonical four-factor BC unitary have
the same conjugation action after four-factor transport.
-/
theorem fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary_conjOperator
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {WB NB WC NC : Type} [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC]
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport pB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport pC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC))
    (P : Semantics.Operator L.Register) :
    (M.fourFactorTransport region).conjOperator
        ((M.activeSectorBoundaryGlobalUnitary region pB pC UB UC U).conjOperator P) =
      (fourFactorBCUnitaryTransport (A := M.fourFactorA region)
        (D := M.fourFactorD region)
        (activeSectorPhysicalUnitary pB pC UB UC U)).conjOperator
          ((M.fourFactorTransport region).conjOperator P) := by
  exact transport_conjOperator_conjOperator_of_conj_toLinearMap_eq
    (M.fourFactorTransport region)
    (M.activeSectorBoundaryGlobalUnitary region pB pC UB UC U)
    (fourFactorBCUnitaryTransport (A := M.fourFactorA region)
      (D := M.fourFactorD region)
      (activeSectorPhysicalUnitary pB pC UB UC U))
    (M.fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary_eq_fourFactorBCUnitaryTransport
      region pB pC UB UC U) P

/-- The preceding physical/global conjugation equality applied to the code projector. -/
theorem fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary_conj_fullCodeProjector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {WB NB WC NC : Type} [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC]
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport pB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport pC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    (M.fourFactorTransport region).conjOperator
        ((M.activeSectorBoundaryGlobalUnitary region pB pC UB UC U).conjOperator
          M.fullCodeProjector) =
      (fourFactorBCUnitaryTransport (A := M.fourFactorA region)
        (D := M.fourFactorD region)
        (activeSectorPhysicalUnitary pB pC UB UC U)).conjOperator
          ((M.fourFactorTransport region).conjOperator M.fullCodeProjector) := by
  exact M.fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary_conjOperator
    region pB pC UB UC U M.fullCodeProjector


end BPTCommutingProjectorModel

end Bounds
end QEC
