import QEC.Bounds.BPTSeparatedUnion.Assembly.SourceLift

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v
namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "sourceFactorization_of_finalAssemblyWitness"

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 2000 in
theorem sourceFactorization_of_finalAssemblyWitness
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
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region)))
    (phi : Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
    (n0 : isotypicLiftedMultiplicity.{0} nB)
    (c0 : WC.restrictScalars Complex)
    (U : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex))
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex)))
    (hphi : ‖phi‖ = 1) (hn0 : ‖n0‖ = 1) (hc0 : ‖c0‖ = 1)
    (htransport :
      let pB := bcomponent.1.restrictScalars Complex
      let pC := ccomponent.1.restrictScalars Complex
      let Uglobal := M.activeSectorBoundaryGlobalUnitary region pB pC UB UC U
      let Eout := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
      let Pproduct : Semantics.Operator
          (Semantics.CompositeSystem
            (Semantics.CompositeSystem
              (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
              (isotypicLiftedMultiplicity.{0} nB))
            (Semantics.CompositeSystem (WC.restrictScalars Complex)
              (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
                (M.fourFactorD region)))) :=
        rankOneTensorOperator
          (phi ⊗ₜ[Complex] n0 : Semantics.CompositeSystem
            (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
            (isotypicLiftedMultiplicity.{0} nB))
          (rankOneTensorOperator c0 P_D)
      (M.fourFactorTransport region).conjOperator
          (Uglobal.conjOperator M.fullCodeProjector) =
        Eout.comp (Pproduct.comp (LinearMap.adjoint Eout)))
    (A : Semantics.Operator (M.regionSubsystem region).selectedSystem)
    (B : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem)
    (hBfixed :
      (M.activeSectorBoundaryGlobalUnitary region
        (bcomponent.1.restrictScalars Complex) (ccomponent.1.restrictScalars Complex) UB UC U).conjOperator
          ((M.regionSubsystem (M.exterior region)).extendLocalToRegister B) =
        (M.regionSubsystem (M.exterior region)).extendLocalToRegister B) :
    ∃ coefficient : Complex,
      M.fullCodeProjector * (M.regionSubsystem region).extendLocalToRegister A *
          (M.regionSubsystem (M.exterior region)).extendLocalToRegister B *
          M.fullCodeProjector = coefficient •
        (M.fullCodeProjector *
          (M.regionSubsystem (M.exterior region)).extendLocalToRegister B *
          M.fullCodeProjector) := by
  let pB := bcomponent.1.restrictScalars Complex
  let pC := ccomponent.1.restrictScalars Complex
  let Uglobal := M.activeSectorBoundaryGlobalUnitary region pB pC UB UC U
  let F := M.fourFactorTransport region
  have hSource := M.finalAssemblySourceFactorization
    region bcomponent ccomponent WB WC UB UC P_D phi n0 c0 U
    hphi hn0 hc0 htransport A B
  dsimp only at hSource
  have hFourFactor := hSource.conjOperator F.symm
  simp only [F, Semantics.UnitaryTransport.symm_conjOperator_conjOperator] at hFourFactor
  change SourceFactorization
    (Uglobal.conjOperator M.fullCodeProjector)
    (Uglobal.conjOperator ((M.regionSubsystem region).extendLocalToRegister A))
    ((M.regionSubsystem (M.exterior region)).extendLocalToRegister B) _ at hFourFactor
  have hBfixedSymm : Uglobal.symm.conjOperator
      ((M.regionSubsystem (M.exterior region)).extendLocalToRegister B) =
      (M.regionSubsystem (M.exterior region)).extendLocalToRegister B := by
    calc
      Uglobal.symm.conjOperator
          ((M.regionSubsystem (M.exterior region)).extendLocalToRegister B) =
        Uglobal.symm.conjOperator
          (Uglobal.conjOperator
            ((M.regionSubsystem (M.exterior region)).extendLocalToRegister B)) :=
              congrArg Uglobal.symm.conjOperator hBfixed.symm
      _ = (M.regionSubsystem (M.exterior region)).extendLocalToRegister B :=
        Uglobal.symm_conjOperator_conjOperator _
  have hPhysical := hFourFactor.conjOperator Uglobal.symm
  simp only [Semantics.UnitaryTransport.symm_conjOperator_conjOperator,
    hBfixedSymm] at hPhysical
  exact ⟨_, hPhysical.eq⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "scalarCompression_product_of_source_factorization"

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2000 in
/--
The source equation `Pi O_M1 O_M2 Pi = f(O_M1) Pi O_M2 Pi`, combined with
the #402 no-information consequence for `M2`, gives scalar compression of
every separated local product.  This is the semantic tail of the BPT union
argument; its factorization premise is discharged below from #388 data.
-/
theorem scalarCompression_product_of_source_factorization
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hright : M.RegionErasureRecoverable right)
    (hfactor : ∀ (A : Semantics.Operator (M.regionSubsystem left).selectedSystem)
      (B : Semantics.Operator (M.regionSubsystem right).selectedSystem),
      ∃ coefficient : Complex,
        M.fullCodeProjector * (M.regionSubsystem left).extendLocalToRegister A *
            (M.regionSubsystem right).extendLocalToRegister B * M.fullCodeProjector =
          coefficient •
            (M.fullCodeProjector * (M.regionSubsystem right).extendLocalToRegister B *
              M.fullCodeProjector))
    (A : Semantics.Operator (M.regionSubsystem left).selectedSystem)
    (B : Semantics.Operator (M.regionSubsystem right).selectedSystem) :
    Semantics.QuditSubsystem.ScalarCompression M.codeSpace
      ((M.regionSubsystem left).extendLocalToRegister A *
        (M.regionSubsystem right).extendLocalToRegister B) := by
  have hInformation := M.regionErasureRecoverable_implies_noInformationOn right hright
  have hAll := ((M.regionSubsystem right).noInformationOn_iff_allLocalScalarCompression
    M.codeSpace).mp hInformation
  rcases hAll B with ⟨rightScalar, hrightScalar⟩
  rcases hfactor A B with ⟨leftScalar, hfactorization⟩
  refine ⟨leftScalar * rightScalar, ?_⟩
  change M.fullCodeProjector *
      ((M.regionSubsystem left).extendLocalToRegister A *
        (M.regionSubsystem right).extendLocalToRegister B) * M.fullCodeProjector =
    (leftScalar * rightScalar) • M.fullCodeProjector
  have hrightScalar' : M.fullCodeProjector *
      (M.regionSubsystem right).extendLocalToRegister B * M.fullCodeProjector =
    rightScalar • M.fullCodeProjector := by
    have hport := hrightScalar
    simp [Module.End.mul_eq_comp, mul_assoc] at hport ⊢
    exact hport
  calc
    M.fullCodeProjector *
        ((M.regionSubsystem left).extendLocalToRegister A *
          (M.regionSubsystem right).extendLocalToRegister B) * M.fullCodeProjector =
      M.fullCodeProjector * (M.regionSubsystem left).extendLocalToRegister A *
        (M.regionSubsystem right).extendLocalToRegister B * M.fullCodeProjector := by
          simp only [mul_assoc]
    _ = leftScalar •
        (M.fullCodeProjector * (M.regionSubsystem right).extendLocalToRegister B *
          M.fullCodeProjector) := hfactorization
    _ = leftScalar • (rightScalar • M.fullCodeProjector) := by rw [hrightScalar']
    _ = (leftScalar * rightScalar) • M.fullCodeProjector := by module

/-
The BPT separated-union lemma (`2Dgeneral_codes08.tex`, lines 698--727).
`ActualProjectorSeparated` refers to the supports of the concrete commuting
projectors supplied by #378.  The proof follows the source's rank-one
disentangling calculation through the retained #388 final-assembly witness,
then uses the finite-qudit no-information/recovery equivalence from #402.
-/
end BPTCommutingProjectorModel
end Bounds
end QEC
