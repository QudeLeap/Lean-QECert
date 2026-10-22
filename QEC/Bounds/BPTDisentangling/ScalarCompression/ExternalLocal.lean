import QEC.Bounds.BPTDisentangling.ScalarCompression.InternalResidual

/-!
# BPT external-boundary local scalar compression

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

set_option maxHeartbeats 2000000 in
/--
External-boundary recoverability gives scalar compression by every literal
`C` probe in the second-cut coordinates.  This is the physical hC relation
needed for the same `Qright` residual that already receives the hM relation.
-/
theorem secondCut_all_externalLocal_scalar_compression_of_externalBoundary_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region))
    (E : Semantics.Operator (M.fourFactorC region)) :
    ∃ scalar : Complex,
      M.secondCutCodeLift region *
          TensorProduct.map
            (1 : Semantics.Operator
              (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)))
            (TensorProduct.map E (1 : Semantics.Operator (M.fourFactorD region))) *
          M.secondCutCodeLift region = scalar • M.secondCutCodeLift region := by
  let S := M.regionSubsystem (M.externalBoundary region)
  let A := M.fourFactorA region
  let B := M.fourFactorB region
  let AB := Semantics.CompositeSystem A B
  let D := M.fourFactorD region
  let Elocal : Semantics.Operator S.selectedSystem :=
    (M.fourFactorCCoordinateRelabel region).symm.conjOperator E
  let Ephysical : Semantics.Operator L.Register := S.extendLocalToRegister Elocal
  let G := M.secondCutGlobalCoordinateTransport region
  let R := M.secondCutCodeLift region
  have hInformation := M.regionErasureRecoverable_implies_noInformationOn
    (M.externalBoundary region) hC
  have hAll := (S.noInformationOn_iff_allLocalScalarCompression M.codeSpace).mp hInformation
  rcases hAll Elocal with ⟨scalar, hscalar⟩
  have hscalar' : M.fullCodeProjector * Ephysical * M.fullCodeProjector =
      scalar • M.fullCodeProjector := by
    change (M.fullCodeProjector.comp Ephysical).comp M.fullCodeProjector = _
    rw [LinearMap.comp_assoc]
    exact hscalar
  have hGcode : G.conjOperator M.fullCodeProjector = R := by
    simpa [G, R] using M.secondCutGlobalCoordinateTransport_conj_fullCodeProjector region
  have hGlocal : G.conjOperator Ephysical =
      TensorProduct.map (1 : Semantics.Operator AB)
        (TensorProduct.map E (1 : Semantics.Operator D)) := by
    let U := M.secondCutCoordinateTransport region
    have hfour : (M.fourFactorTransport region).conjOperator Ephysical =
        TensorProduct.map (1 : Semantics.Operator A)
          (TensorProduct.map (1 : Semantics.Operator B)
            (TensorProduct.map E (1 : Semantics.Operator D))) := by
      simpa [Ephysical, Elocal] using
        M.fourFactorTransport_conj_externalBoundaryLift region E
    have hsecond : U.conjOperator
        (TensorProduct.map (1 : Semantics.Operator AB)
          (TensorProduct.map E (1 : Semantics.Operator D))) =
        TensorProduct.map (1 : Semantics.Operator A)
          (TensorProduct.map (1 : Semantics.Operator B)
            (TensorProduct.map E (1 : Semantics.Operator D))) := by
      change (tensorAssociatorUnitary A B
        (Semantics.CompositeSystem (M.fourFactorC region) D)).conjOperator
          (TensorProduct.map (1 : Semantics.Operator AB)
            (TensorProduct.map E (1 : Semantics.Operator D))) = _
      rw [show (1 : Semantics.Operator AB) =
          TensorProduct.map (1 : Semantics.Operator A) (1 : Semantics.Operator B) by
        symm
        exact TensorProduct.map_one]
      exact tensorAssociatorUnitary_conj_tensorMap
        (1 : Semantics.Operator A) (1 : Semantics.Operator B)
        (TensorProduct.map E (1 : Semantics.Operator D))
    calc
      G.conjOperator Ephysical =
          U.symm.conjOperator ((M.fourFactorTransport region).conjOperator Ephysical) := by
        simpa only [G, U, secondCutGlobalCoordinateTransport] using
          (composeUnitaryTransport_conjOperator (M.fourFactorTransport region)
            (M.secondCutCoordinateTransport region).symm Ephysical)
      _ =
          U.symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A)
              (TensorProduct.map (1 : Semantics.Operator B)
                (TensorProduct.map E (1 : Semantics.Operator D)))) :=
        congrArg U.symm.conjOperator hfour
      _ = U.symm.conjOperator
          (U.conjOperator
            (TensorProduct.map (1 : Semantics.Operator AB)
              (TensorProduct.map E (1 : Semantics.Operator D)))) :=
        congrArg U.symm.conjOperator hsecond.symm
      _ = TensorProduct.map (1 : Semantics.Operator AB)
          (TensorProduct.map E (1 : Semantics.Operator D)) :=
        U.symm_conjOperator_conjOperator _
  refine ⟨scalar, ?_⟩
  calc
    R * TensorProduct.map (1 : Semantics.Operator AB)
        (TensorProduct.map E (1 : Semantics.Operator D)) * R =
        G.conjOperator M.fullCodeProjector * G.conjOperator Ephysical *
          G.conjOperator M.fullCodeProjector := by
      rw [hGcode, hGlocal]
    _ = G.conjOperator (M.fullCodeProjector * Ephysical * M.fullCodeProjector) := by
      rw [Semantics.UnitaryTransport.conjOperator_mul,
        Semantics.UnitaryTransport.conjOperator_mul]
    _ = G.conjOperator (scalar • M.fullCodeProjector) :=
      congrArg G.conjOperator hscalar'
    _ = scalar • G.conjOperator M.fullCodeProjector := by
      exact G.conjOperatorLinearMap.map_smul scalar M.fullCodeProjector
    _ = scalar • R := congrArg (fun operator => scalar • operator) hGcode
    _ = scalar • M.secondCutCodeLift region := rfl

/-- Compressing a literal exterior tensor lift through an active isotypic sector
leaves the exterior operator intact. -/
theorem adjoint_tensorTripleSubtypeEmbedding_comp_tensorMap_right_comp_tensorTripleSubtypeEmbedding
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (p : Submodule Complex B) (Z : Semantics.Operator C) :
    (LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C) p)).comp
      ((TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A B)) Z).comp
        (tensorTripleSubtypeEmbedding (A := A) (C := C) p)) =
      TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A p)) Z := by
  unfold tensorTripleSubtypeEmbedding
  simp only [TensorProduct.adjoint_map, LinearMap.adjoint_one]
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul middle exterior =>
      induction middle using TensorProduct.induction_on with
      | zero => simp
      | tmul interior sectorVector =>
          simp only [LinearMap.comp_apply, TensorProduct.map_tmul, Module.End.one_apply]
          rw [adjoint_submoduleSubtype_apply_subtype]
      | add first second hfirst hsecond =>
          simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hfirst hsecond
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

/-- The active-sector block transport leaves a literal right exterior probe on
the right of the resulting `A tensor W` factor. -/
theorem isotypicSectorBlockTransportLeft_conj_tensorMap_right
    {A H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (Z : Semantics.Operator C) :
    (isotypicSectorBlockTransportLeft A H W N C U).conjOperator
        (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A H)) Z) =
      TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A W))
        (TensorProduct.map (1 : Semantics.Operator N) Z) := by
  unfold isotypicSectorBlockTransportLeft
  rw [composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator]
  rw [unitaryRTensor_conj_tensorMap_right (unitaryLTensor A U) C Z]
  rw [show (1 : Semantics.Operator (Semantics.CompositeSystem A
      (Semantics.CompositeSystem W N))) =
      TensorProduct.map (1 : Semantics.Operator A)
        (1 : Semantics.Operator (Semantics.CompositeSystem W N)) by
      symm
      exact TensorProduct.map_one]
  rw [tensorAssociatorUnitary_conj_tensorMap]
  rw [unitaryLTensor_conj_tensorMap_left]
  rw [show (1 : Semantics.Operator (Semantics.CompositeSystem W N)) =
      TensorProduct.map (1 : Semantics.Operator W) (1 : Semantics.Operator N) by
      symm
      exact TensorProduct.map_one]
  rw [tensorAssociatorUnitary_conj_tensorMap]
  rw [tensorAssociatorUnitary_symm_conj_tensorMap]
  rw [show TensorProduct.map (1 : Semantics.Operator A) (1 : Semantics.Operator W) =
      (1 : Semantics.Operator (Semantics.CompositeSystem A W)) from TensorProduct.map_one]


end BPTCommutingProjectorModel

end Bounds
end QEC
