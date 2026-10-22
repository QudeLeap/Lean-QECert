import QEC.Bounds.BPTDisentangling.InteractionAlgebra

/-!
# BPT four-factor geometry and physical support

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
The exact source conclusion, stated through the concrete selected/complement
register factorization.  Every constructor field is source-level evidence: a
proof must provide the boundary unitary, normalized regional state, complement
projection, support certificate, and exact projector equality.
-/
inductive Disentangled (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Prop where
  | intro
      (unitary : Semantics.UnitaryTransport L.Register L.Register)
      (regionalState : (M.regionSubsystem region).selectedSystem)
      (complementProjector : Semantics.Operator (M.regionSubsystem region).complementSystem)
      (unitary_supported : M.UnitarySupportedOn (M.boundary region) unitary)
      (regionalState_normalized : ‖regionalState‖ = 1)
      (complementProjector_isSymmetricProjection : complementProjector.IsSymmetricProjection)
      (projector_factorization :
        unitary.conjOperator M.fullCodeProjector =
          M.pureFactorTensorComplementProjector region regionalState complementProjector)

/-- The identity transport of a finite register. -/
noncomputable def identityUnitary (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H] :
    Semantics.UnitaryTransport H H where
  toLinearEquiv := LinearEquiv.refl Complex H
  map_inner := by simp

/-- Conjugation by the identity transport leaves every operator unchanged. -/
theorem identityUnitary_conjOperator (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    (A : Semantics.Operator H) :
    (identityUnitary H).conjOperator A = A := by
  rfl

/-- The computational all-zero basis vector of any concrete BPT region is normalized. -/
noncomputable def regionZeroVector (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : (M.regionSubsystem region).selectedSystem :=
  EuclideanSpace.basisFun
    (Semantics.Qudit.Label (M.regionSubsystem region).selectedDimensions) Complex
    (Semantics.Qudit.zeroLabel (M.regionSubsystem region).selectedDimensions (by
      intro site
      exact L.localDimension_positive site))

/-- The canonical all-zero regional basis vector has unit norm. -/
theorem norm_regionZeroVector (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : ‖M.regionZeroVector region‖ = 1 := by
  simp [regionZeroVector]

/-- A BPT model with an empty code carrier has zero full code projector. -/
theorem fullCodeProjector_eq_zero_of_codeSpace_carrier_eq_bot
    (M : BPTCommutingProjectorModel L kappa) (hcode : M.codeSpace.carrier = ⊥) :
    M.fullCodeProjector = 0 := by
  apply LinearMap.ext
  intro vector
  unfold fullCodeProjector
  have hmem : M.codeSpace.projector vector ∈ M.codeSpace.carrier :=
    M.codeSpace.projector_mem_carrier vector
  rw [hcode] at hmem
  simpa using hmem

/--
The exact BPT conclusion is constructible in the degenerate empty-code case.
This isolates the genuinely nontrivial branch for the later finite interaction
algebra proof: the zero projector factors through every normalized regional
vector and the zero complement projector, with the boundary identity unitary.
-/
theorem disentangled_of_codeSpace_carrier_eq_bot
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier = ⊥) : M.Disentangled region := by
  let U := identityUnitary L.Register
  let phi := M.regionZeroVector region
  refine ⟨U, phi, 0, ?_, M.norm_regionZeroVector region, ?_, ?_⟩
  · refine ⟨1, ?_⟩
    change (M.regionSubsystem (M.boundary region)).extendLocalToRegister 1 =
      U.toLinearEquiv.toLinearMap
    unfold Semantics.QuditSubsystem.extendLocalToRegister
      Semantics.QuditSubsystem.extendLocal
    change (M.regionSubsystem (M.boundary region)).registerFactorization.symm.conjOperator
      (TensorProduct.map (1 : Semantics.Operator
        (M.regionSubsystem (M.boundary region)).selectedSystem)
        (1 : Semantics.Operator
          (M.regionSubsystem (M.boundary region)).complementSystem)) = 1
    rw [TensorProduct.map_one]
    exact (M.regionSubsystem (M.boundary region)).registerFactorization.symm.conjOperator_one
  · constructor
    · exact zero_mul _
    · simp
  · have hzero := M.fullCodeProjector_eq_zero_of_codeSpace_carrier_eq_bot hcode
    rw [hzero]
    change 0 = (M.regionSubsystem region).registerFactorization.symm.conjOperator
      (TensorProduct.map _ (0 : Semantics.Operator
        (M.regionSubsystem region).complementSystem))
    rw [TensorProduct.map_zero_right]
    ext vector
    simp [Semantics.UnitaryTransport.conjOperator]

/--
Split a global register first into `S` and its complement, then split that
complement into the retained coordinates of `T \ S` and the complement of
`T`.  This is the first concrete nested-coordinate factorization used to lift
local operators along a support inclusion.
-/
noncomputable def nestedFactorizationLeft
    (S T : Semantics.QuditSubsystem L.localDimension) (hST : S.selected ⊆ T.selected) :
    Semantics.UnitaryTransport L.Register
      (Semantics.CompositeSystem S.selectedSystem
        (Semantics.CompositeSystem (S.additionalRetainedSystem T) T.complementSystem)) := by
  let e := S.registerFactorization.toLinearIsometryEquiv.trans
    ((S.complementFactorization T hST).toLinearIsometryEquiv.lTensor S.selectedSystem)
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := e.inner_map_map }

/--
Split a global register first into `T` and its complement, then split the
selected factor of `T` into `S` and `T \ S`.  Tensor associativity puts this
route in the same three-factor coordinate order as `nestedFactorizationLeft`.
-/
noncomputable def nestedFactorizationRight
    (S T : Semantics.QuditSubsystem L.localDimension) (hST : S.selected ⊆ T.selected) :
    Semantics.UnitaryTransport L.Register
      (Semantics.CompositeSystem S.selectedSystem
        (Semantics.CompositeSystem (S.additionalRetainedSystem T) T.complementSystem)) := by
  let splitSelected :=
    (S.selectedFactorization T hST).toLinearIsometryEquiv.rTensor T.complementSystem
  let reassociate := TensorProduct.assocIsometry Complex S.selectedSystem
    (S.additionalRetainedSystem T) T.complementSystem
  let e := T.registerFactorization.toLinearIsometryEquiv.trans
    (splitSelected.trans reassociate)
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := e.inner_map_map }

/--
The left nested coordinate factorization maps a global computational basis
vector to its `S`, `T \ S`, and `Tᶜ` basis factors.
-/
theorem nestedFactorizationLeft_apply_basis
    (S T : Semantics.QuditSubsystem L.localDimension) (hST : S.selected ⊆ T.selected)
    (labels : Semantics.Qudit.Label L.localDimension) :
    nestedFactorizationLeft S T hST
        (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
      (EuclideanSpace.basisFun (Semantics.Qudit.Label S.selectedDimensions) Complex
        (S.splitLabel labels).1) ⊗ₜ[Complex]
      ((EuclideanSpace.basisFun
          (Semantics.Qudit.Label (S.additionalRetainedDimensions T)) Complex
          (S.splitComplementLabel T hST (S.splitLabel labels).2).1) ⊗ₜ[Complex]
        (EuclideanSpace.basisFun (Semantics.Qudit.Label T.complementDimensions) Complex
          (S.splitComplementLabel T hST (S.splitLabel labels).2).2)) := by
  dsimp [nestedFactorizationLeft]
  rw [S.registerFactorization_apply_basis]
  simp only [LinearEquiv.lTensor_tmul]
  rw [S.complementFactorization_apply_basis T hST]

/--
The right nested coordinate factorization produces the same three basis
factors, this time by splitting the larger selected subsystem first.
-/
theorem nestedFactorizationRight_apply_basis
    (S T : Semantics.QuditSubsystem L.localDimension) (hST : S.selected ⊆ T.selected)
    (labels : Semantics.Qudit.Label L.localDimension) :
    nestedFactorizationRight S T hST
        (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
      (EuclideanSpace.basisFun (Semantics.Qudit.Label S.selectedDimensions) Complex
        (S.splitSelectedLabel T hST (T.splitLabel labels).1).1) ⊗ₜ[Complex]
      ((EuclideanSpace.basisFun
          (Semantics.Qudit.Label (S.additionalRetainedDimensions T)) Complex
          (S.splitSelectedLabel T hST (T.splitLabel labels).1).2) ⊗ₜ[Complex]
        (EuclideanSpace.basisFun (Semantics.Qudit.Label T.complementDimensions) Complex
          (T.splitLabel labels).2)) := by
  dsimp [nestedFactorizationRight]
  rw [T.registerFactorization_apply_basis]
  simp only [LinearEquiv.rTensor_tmul]
  rw [S.selectedFactorization_apply_basis T hST]
  rw [TensorProduct.assoc_tmul]

/--
The two nested coordinate routes are the same unitary transport.  Equality on
the finite computational basis is enough because those vectors form a basis of
the full register; the two coordinate label-splitting identities close the
comparison.
-/
theorem nestedFactorization_toLinearEquiv_eq
    (S T : Semantics.QuditSubsystem L.localDimension) (hST : S.selected ⊆ T.selected) :
    (nestedFactorizationLeft S T hST).toLinearEquiv =
      (nestedFactorizationRight S T hST).toLinearEquiv := by
  apply LinearEquiv.toLinearMap_injective
  apply (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex).toBasis.ext
  intro labels
  change nestedFactorizationLeft S T hST
      (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
    nestedFactorizationRight S T hST
      (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels)
  rw [nestedFactorizationLeft_apply_basis, nestedFactorizationRight_apply_basis]
  simp only [S.splitSelectedLabel_splitLabel T hST,
    S.splitComplementLabel_splitLabel_second T hST]

/--
Conjugating an `S`-local identity extension through the left cumulative
factorization `S subset T` acts on `S` alone and is the identity on both
`T \\ S` and `T^c`.  This is the operator-level recombination identity used
to transport the three BPT source products into common coordinates.
-/
theorem nestedFactorizationLeft_conj_extendLocalToRegister
    (S T : Semantics.QuditSubsystem L.localDimension) (hST : S.selected ⊆ T.selected)
    (A : Semantics.Operator S.selectedSystem) :
    (nestedFactorizationLeft S T hST).conjOperator (S.extendLocalToRegister A) =
      TensorProduct.map A
        (1 : Semantics.Operator
          (Semantics.CompositeSystem (S.additionalRetainedSystem T) T.complementSystem)) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul selected residual =>
      induction residual using TensorProduct.induction_on with
      | zero => simp
      | tmul additional complement =>
          simp [nestedFactorizationLeft, Semantics.QuditSubsystem.extendLocalToRegister,
            Semantics.QuditSubsystem.extendLocal, Semantics.UnitaryTransport.conjOperator]
      | add x y hx hy =>
          simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  | add x y hx hy => simp [map_add, hx, hy]

/--
Lift an operator on `S` to a larger selected region `T` by splitting the
selected coordinates of `T` into `S` and `T \ S`, acting on `S`, and restoring
the original selected-coordinate order.
-/
noncomputable def liftLocalToLarger
    (S T : Semantics.QuditSubsystem L.localDimension) (hST : S.selected ⊆ T.selected)
    (A : Semantics.Operator S.selectedSystem) : Semantics.Operator T.selectedSystem :=
  (S.selectedFactorization T hST).symm.conjOperator
    (TensorProduct.map A (1 : Semantics.Operator (S.additionalRetainedSystem T)))

/--
Identity extension is coherent under inclusion of selected coordinate sets.
The proof compares the two concrete nested coordinate factorizations on the
global computational basis, then uses their established equality to transport
the operator action through the common three-factor representation.
-/
theorem extendLocalToRegister_liftLocalToLarger
    (S T : Semantics.QuditSubsystem L.localDimension) (hST : S.selected ⊆ T.selected)
    (A : Semantics.Operator S.selectedSystem) :
    T.extendLocalToRegister (liftLocalToLarger S T hST A) = S.extendLocalToRegister A := by
  let basis := EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex
  apply basis.toBasis.ext
  intro labels
  apply (nestedFactorizationLeft S T hST).toLinearEquiv.injective
  have hNested := nestedFactorization_toLinearEquiv_eq S T hST
  conv_lhs => rw [hNested]
  dsimp [nestedFactorizationLeft, nestedFactorizationRight,
    Semantics.QuditSubsystem.extendLocalToRegister,
    Semantics.QuditSubsystem.extendLocal, liftLocalToLarger]
  simp only [LinearEquiv.apply_symm_apply]
  rw [T.registerFactorization_apply_basis, S.registerFactorization_apply_basis]
  simp only [TensorProduct.map_tmul, LinearEquiv.rTensor_tmul, LinearEquiv.lTensor_tmul,
    Semantics.UnitaryTransport.conjOperator_apply]
  simp only [Semantics.UnitaryTransport.symm_toLinearEquiv,
    LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm, LinearMap.id_apply]
  rw [S.selectedFactorization_apply_basis T hST,
    S.complementFactorization_apply_basis T hST]
  simp only [TensorProduct.map_tmul, Module.End.one_apply]
  rw [TensorProduct.assoc_tmul]
  simp only [S.splitSelectedLabel_splitLabel T hST,
    S.splitComplementLabel_splitLabel_second T hST]

/--
Support is monotone under inclusion of concrete selected coordinate sets.  The
larger-region witness is the explicit `liftLocalToLarger` operator, and the
preceding coherence theorem proves that its global extension is unchanged.
-/
theorem operatorSupportedOnRegister_of_subset
    (S T : Semantics.QuditSubsystem L.localDimension) (hST : S.selected ⊆ T.selected)
    {A : Semantics.Operator L.Register}
    (hA : S.OperatorSupportedOnRegister A) : T.OperatorSupportedOnRegister A := by
  rcases hA with ⟨localA, hlocalA⟩
  refine ⟨liftLocalToLarger S T hST localA, ?_⟩
  rw [extendLocalToRegister_liftLocalToLarger]
  exact hlocalA

/-- Boundary support is monotone along a proved inclusion of concrete site sets. -/
theorem unitarySupportedOn_of_subset
    (M : BPTCommutingProjectorModel L kappa) (S T : Finset L.Site)
    {U : Semantics.UnitaryTransport L.Register L.Register}
    (hST : S ⊆ T) (hU : M.UnitarySupportedOn S U) :
    M.UnitarySupportedOn T U :=
  operatorSupportedOnRegister_of_subset (M.regionSubsystem S) (M.regionSubsystem T)
    (by simpa [BPTCommutingProjectorModel.regionSubsystem]) hU

/--
An actual BPT check can be regarded as supported on any larger region that
contains its recorded support.  This transports the model's local projector
through the explicit selected-coordinate inclusion above.
-/
theorem projector_supportedOnRegister_of_support_subset
    (M : BPTCommutingProjectorModel L kappa) (check : kappa) (region : Finset L.Site)
    (hsupport : M.support check ⊆ region) :
    (M.regionSubsystem region).OperatorSupportedOnRegister (M.projector check) := by
  apply operatorSupportedOnRegister_of_subset (L.subsystem (M.support check))
    (M.regionSubsystem region)
  · simpa [BPTCommutingProjectorModel.regionSubsystem] using hsupport
  · exact M.projector_supported_on check

/-- The source interior `M \\ partial_- M`, expressed using actual supports. -/
noncomputable def interior (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Finset L.Site :=
  region \ M.internalBoundary region

/-- The source exterior `bar M \\ partial_+ M`, expressed using actual supports. -/
noncomputable def exterior (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Finset L.Site :=
  regionᶜ \ M.externalBoundary region

/-- The source interior is the portion of `M` outside the full boundary. -/
theorem interior_eq_region_sdiff_boundary (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    M.interior region = region \ M.boundary region := by
  ext site
  simp [interior, internalBoundary]

/-- The region is the disjoint union of its source interior and internal boundary. -/
theorem region_eq_interior_union_internalBoundary
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    region = M.interior region ∪ M.internalBoundary region := by
  ext site
  constructor
  · intro hregion
    by_cases hboundary : site ∈ M.internalBoundary region
    · exact Finset.mem_union_right _ hboundary
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hregion, hboundary⟩)
  · intro h
    rcases Finset.mem_union.mp h with hinterior | hboundary
    · exact (Finset.mem_sdiff.mp hinterior).1
    · exact (Finset.mem_inter.mp hboundary).2

/-- The complement of a region is the disjoint union of external boundary and exterior. -/
theorem complement_eq_externalBoundary_union_exterior
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    regionᶜ = M.externalBoundary region ∪ M.exterior region := by
  ext site
  constructor
  · intro hcomplement
    by_cases hboundary : site ∈ M.externalBoundary region
    · exact Finset.mem_union_left _ hboundary
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hcomplement, hboundary⟩)
  · intro h
    rcases Finset.mem_union.mp h with hboundary | hexterior
    · exact Finset.mem_compl.mpr ((M.mem_externalBoundary_iff region site).mp hboundary |>.1)
    · exact (Finset.mem_sdiff.mp hexterior).1

/-- The source interior and external boundary are disjoint. -/
theorem interior_disjoint_externalBoundary
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Disjoint (M.interior region) (M.externalBoundary region) := by
  rw [Finset.disjoint_left]
  intro site hinterior hexternal
  exact (M.mem_externalBoundary_iff region site).mp hexternal |>.1
    ((Finset.mem_sdiff.mp hinterior).1)

/-- The internal boundary and source exterior are disjoint. -/
theorem internalBoundary_disjoint_exterior
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Disjoint (M.internalBoundary region) (M.exterior region) := by
  rw [Finset.disjoint_left]
  intro site hinternal hexterior
  exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hexterior).1)
    ((Finset.mem_inter.mp hinternal).2)

/--
The concrete four-factor coordinate transport for the source partition
`A B C D`: source interior, internal boundary, external boundary, and source
exterior.  It is assembled through the cumulative coordinate regions
`A subset AB subset ABC`; consequently the two virtual middle factors carry
the exact `AB \ A` and `ABC \ AB` site coordinates needed by the two
overlapping BV03 cuts.
-/
noncomputable def fourFactorTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport L.Register
      (Semantics.CompositeSystem
        (M.regionSubsystem (M.interior region)).selectedSystem
        (Semantics.CompositeSystem
          ((M.regionSubsystem (M.interior region)).additionalRetainedSystem
            (M.regionSubsystem region))
          (Semantics.CompositeSystem
            ((M.regionSubsystem region).additionalRetainedSystem
              (M.regionSubsystem (region ∪ M.externalBoundary region)))
            (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem))) := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  let splitAB : Semantics.UnitaryTransport AB.selectedSystem
      (Semantics.CompositeSystem A.selectedSystem (A.additionalRetainedSystem AB)) := by
    let e := A.selectedFactorization AB hAAB
    exact
      { toLinearEquiv := e.toLinearEquiv
        map_inner := e.map_inner }
  exact composeUnitaryTransport
    (composeUnitaryTransport (nestedFactorizationLeft AB ABC hABABC)
      (unitaryRTensor splitAB
        (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem)))
    (tensorAssociatorUnitary A.selectedSystem (A.additionalRetainedSystem AB)
      (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem))

set_option maxHeartbeats 800000 in
/--
On computational basis vectors, `fourFactorTransport` is exactly the ordered
coordinate split `A`, `B = AB \ A`, `C = ABC \ AB`, `D = ABC^c`.  This basis
equation is the transport certificate used below to compare the `AB`, `BC`,
and `CD` local support presentations on one common four-factor register.
-/
theorem fourFactorTransport_apply_basis
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (labels : Semantics.Qudit.Label L.localDimension) :
    M.fourFactorTransport region
        (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
      (EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            (M.regionSubsystem (M.interior region)).selectedDimensions) Complex
          ((M.regionSubsystem (M.interior region)).splitSelectedLabel
            (M.regionSubsystem region)
            (by
              intro site hsite
              exact (Finset.mem_sdiff.mp hsite).1)
            ((M.regionSubsystem region).splitLabel labels).1).1)
        ⊗ₜ[Complex]
      ((EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            ((M.regionSubsystem (M.interior region)).additionalRetainedDimensions
              (M.regionSubsystem region))) Complex
          ((M.regionSubsystem (M.interior region)).splitSelectedLabel
            (M.regionSubsystem region)
            (by
              intro site hsite
              exact (Finset.mem_sdiff.mp hsite).1)
            ((M.regionSubsystem region).splitLabel labels).1).2)
        ⊗ₜ[Complex]
        ((EuclideanSpace.basisFun
            (Semantics.Qudit.Label
              ((M.regionSubsystem region).additionalRetainedDimensions
                (M.regionSubsystem (region ∪ M.externalBoundary region)))) Complex
            ((M.regionSubsystem region).splitComplementLabel
              (M.regionSubsystem (region ∪ M.externalBoundary region))
              (by
                intro site hsite
                exact Finset.mem_union_left _ hsite)
              ((M.regionSubsystem region).splitLabel labels).2).1)
          ⊗ₜ[Complex]
          (EuclideanSpace.basisFun
            (Semantics.Qudit.Label
              (M.regionSubsystem (region ∪ M.externalBoundary region)).complementDimensions) Complex
            ((M.regionSubsystem region).splitComplementLabel
              (M.regionSubsystem (region ∪ M.externalBoundary region))
              (by
                intro site hsite
                exact Finset.mem_union_left _ hsite)
              ((M.regionSubsystem region).splitLabel labels).2).2))) := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  dsimp [fourFactorTransport]
  rw [nestedFactorizationLeft_apply_basis AB ABC hABABC]
  simp only [unitaryRTensor_apply_tmul]
  rw [A.selectedFactorization_apply_basis AB hAAB]
  simp only [tensorAssociatorUnitary_apply_tmul]
  rfl

/--
An equivalent cumulative construction of the source `A B C D` transport:
first split the register into `AB` and its complement, then split the two
halves independently.  This presentation exposes operators supported on
`CD` as an identity on `AB` tensored with a `CD` operator.
-/
noncomputable def fourFactorTransportFromRegion
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport L.Register
      (Semantics.CompositeSystem
        (M.regionSubsystem (M.interior region)).selectedSystem
        (Semantics.CompositeSystem
          ((M.regionSubsystem (M.interior region)).additionalRetainedSystem
            (M.regionSubsystem region))
          (Semantics.CompositeSystem
            ((M.regionSubsystem region).additionalRetainedSystem
              (M.regionSubsystem (region ∪ M.externalBoundary region)))
            (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem))) := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  let splitAB : Semantics.UnitaryTransport AB.selectedSystem
      (Semantics.CompositeSystem A.selectedSystem (A.additionalRetainedSystem AB)) := by
    let e := A.selectedFactorization AB hAAB
    exact
      { toLinearEquiv := e.toLinearEquiv
        map_inner := e.map_inner }
  let splitCD := AB.complementFactorization ABC hABABC
  exact composeUnitaryTransport
    (composeUnitaryTransport
      (composeUnitaryTransport AB.registerFactorization
        (unitaryRTensor splitAB AB.complementSystem))
      (unitaryLTensor (Semantics.CompositeSystem A.selectedSystem
        (A.additionalRetainedSystem AB)) splitCD))
    (tensorAssociatorUnitary A.selectedSystem (A.additionalRetainedSystem AB)
      (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem))

set_option maxHeartbeats 800000 in
/-- The alternate `AB`-first transport has the same computational-basis action. -/
theorem fourFactorTransportFromRegion_apply_basis
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (labels : Semantics.Qudit.Label L.localDimension) :
    M.fourFactorTransportFromRegion region
        (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
      (EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            (M.regionSubsystem (M.interior region)).selectedDimensions) Complex
          ((M.regionSubsystem (M.interior region)).splitSelectedLabel
            (M.regionSubsystem region)
            (by
              intro site hsite
              exact (Finset.mem_sdiff.mp hsite).1)
            ((M.regionSubsystem region).splitLabel labels).1).1)
        ⊗ₜ[Complex]
      ((EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            ((M.regionSubsystem (M.interior region)).additionalRetainedDimensions
              (M.regionSubsystem region))) Complex
          ((M.regionSubsystem (M.interior region)).splitSelectedLabel
            (M.regionSubsystem region)
            (by
              intro site hsite
              exact (Finset.mem_sdiff.mp hsite).1)
            ((M.regionSubsystem region).splitLabel labels).1).2)
        ⊗ₜ[Complex]
        ((EuclideanSpace.basisFun
            (Semantics.Qudit.Label
              ((M.regionSubsystem region).additionalRetainedDimensions
                (M.regionSubsystem (region ∪ M.externalBoundary region)))) Complex
            ((M.regionSubsystem region).splitComplementLabel
              (M.regionSubsystem (region ∪ M.externalBoundary region))
              (by
                intro site hsite
                exact Finset.mem_union_left _ hsite)
              ((M.regionSubsystem region).splitLabel labels).2).1)
          ⊗ₜ[Complex]
          (EuclideanSpace.basisFun
            (Semantics.Qudit.Label
              (M.regionSubsystem (region ∪ M.externalBoundary region)).complementDimensions) Complex
            ((M.regionSubsystem region).splitComplementLabel
              (M.regionSubsystem (region ∪ M.externalBoundary region))
              (by
                intro site hsite
                exact Finset.mem_union_left _ hsite)
              ((M.regionSubsystem region).splitLabel labels).2).2))) := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  dsimp [fourFactorTransportFromRegion]
  rw [AB.registerFactorization_apply_basis]
  simp only [unitaryRTensor_apply_tmul, unitaryLTensor_apply_tmul,
    tensorAssociatorUnitary_apply_tmul]
  rw [A.selectedFactorization_apply_basis AB hAAB,
    AB.complementFactorization_apply_basis ABC hABABC]
  rfl

/-- Both cumulative constructions are exactly the same four-factor unitary. -/
theorem fourFactorTransport_eq_fourFactorTransportFromRegion
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.fourFactorTransport region = M.fourFactorTransportFromRegion region := by
  apply unitaryTransport_ext
  apply LinearEquiv.toLinearMap_injective
  apply (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex).toBasis.ext
  intro labels
  change M.fourFactorTransport region
      (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
    M.fourFactorTransportFromRegion region
      (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels)
  rw [M.fourFactorTransport_apply_basis, M.fourFactorTransportFromRegion_apply_basis]

/-- The `A` factor of the concrete source four-factor transport. -/
abbrev fourFactorA (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) : Type :=
  (M.regionSubsystem (M.interior region)).selectedSystem

/-- The `B = AB \\ A` factor of the concrete source four-factor transport. -/
abbrev fourFactorB (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) : Type :=
  (M.regionSubsystem (M.interior region)).additionalRetainedSystem (M.regionSubsystem region)

/-- The `C = ABC \\ AB` factor of the concrete source four-factor transport. -/
abbrev fourFactorC (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) : Type :=
  (M.regionSubsystem region).additionalRetainedSystem
    (M.regionSubsystem (region ∪ M.externalBoundary region))

/-- The `D = ABC^c` factor of the concrete source four-factor transport. -/
abbrev fourFactorD (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) : Type :=
  (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem

/-- The common `A tensor (B tensor (C tensor D))` coordinate register. -/
abbrev fourFactorSystem (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Type :=
  Semantics.CompositeSystem (M.fourFactorA region)
    (Semantics.CompositeSystem (M.fourFactorB region)
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))

/-- The literal computational-basis vector in the source `A B C D` coordinates. -/
noncomputable def fourFactorBasisVector (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) (labels : Semantics.Qudit.Label L.localDimension) :
    M.fourFactorSystem region :=
  (EuclideanSpace.basisFun
      (Semantics.Qudit.Label
        (M.regionSubsystem (M.interior region)).selectedDimensions) Complex
      ((M.regionSubsystem (M.interior region)).splitSelectedLabel
        (M.regionSubsystem region)
        (by
          intro site hsite
          exact (Finset.mem_sdiff.mp hsite).1)
        ((M.regionSubsystem region).splitLabel labels).1).1)
    ⊗ₜ[Complex]
  ((EuclideanSpace.basisFun
      (Semantics.Qudit.Label
        ((M.regionSubsystem (M.interior region)).additionalRetainedDimensions
          (M.regionSubsystem region))) Complex
      ((M.regionSubsystem (M.interior region)).splitSelectedLabel
        (M.regionSubsystem region)
        (by
          intro site hsite
          exact (Finset.mem_sdiff.mp hsite).1)
        ((M.regionSubsystem region).splitLabel labels).1).2)
    ⊗ₜ[Complex]
    ((EuclideanSpace.basisFun
        (Semantics.Qudit.Label
          ((M.regionSubsystem region).additionalRetainedDimensions
            (M.regionSubsystem (region ∪ M.externalBoundary region)))) Complex
        ((M.regionSubsystem region).splitComplementLabel
          (M.regionSubsystem (region ∪ M.externalBoundary region))
          (by
            intro site hsite
            exact Finset.mem_union_left _ hsite)
          ((M.regionSubsystem region).splitLabel labels).2).1)
      ⊗ₜ[Complex]
      (EuclideanSpace.basisFun
        (Semantics.Qudit.Label
          (M.regionSubsystem (region ∪ M.externalBoundary region)).complementDimensions) Complex
        ((M.regionSubsystem region).splitComplementLabel
          (M.regionSubsystem (region ∪ M.externalBoundary region))
          (by
            intro site hsite
            exact Finset.mem_union_left _ hsite)
          ((M.regionSubsystem region).splitLabel labels).2).2)))

/-- The canonical transport sends each global basis vector to its named `A B C D` split. -/
theorem fourFactorTransport_apply_fourFactorBasisVector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (labels : Semantics.Qudit.Label L.localDimension) :
    M.fourFactorTransport region
        (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
      M.fourFactorBasisVector region labels := by
  unfold fourFactorBasisVector
  exact M.fourFactorTransport_apply_basis region labels

/--
The concrete internal-boundary coordinates are equivalent to the virtual
`B = AB \\ A` coordinates of the cumulative four-factor transport.  The
equivalence preserves the underlying lattice site; only its membership proof
changes.
-/
def fourFactorBCoordinateEquiv (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    {site : L.Site // site ∈ M.internalBoundary region} ≃
      (M.regionSubsystem (M.interior region)).AdditionalRetainedCoordinates
        (M.regionSubsystem region) where
  toFun := fun site => ⟨site, by
    constructor
    · intro hinterior
      exact (Finset.mem_sdiff.mp hinterior).2 site.property
    · exact (Finset.mem_inter.mp site.property).2⟩
  invFun := fun site => ⟨site, by
    by_contra hnotinternal
    exact site.property.1 (Finset.mem_sdiff.mpr ⟨site.property.2, hnotinternal⟩)⟩
  left_inv := by
    intro site
    exact Subtype.ext rfl
  right_inv := by
    intro site
    exact Subtype.ext rfl

/--
The concrete external-boundary coordinates are equivalent to the virtual
`C = ABC \\ AB` coordinates.  This is the coordinate bridge used to move the
external-boundary correctability hypothesis into the source `C` factor.
-/
def fourFactorCCoordinateEquiv (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    {site : L.Site // site ∈ M.externalBoundary region} ≃
      (M.regionSubsystem region).AdditionalRetainedCoordinates
        (M.regionSubsystem (region ∪ M.externalBoundary region)) where
  toFun := fun site => ⟨site, by
    constructor
    · intro hregion
      exact (Finset.disjoint_left.mp (M.externalBoundary_disjoint_region region))
        site.property hregion
    · exact Finset.mem_union_right _ site.property⟩
  invFun := fun site => ⟨site, by
    rcases Finset.mem_union.mp site.property.2 with hregion | hexternal
    · exact False.elim (site.property.1 hregion)
    · exact hexternal⟩
  left_inv := by
    intro site
    exact Subtype.ext rfl
  right_inv := by
    intro site
    exact Subtype.ext rfl

/--
The source exterior coordinates are equivalent to the final virtual `D`
coordinate system, namely the complement of `AB union C`.
-/
def fourFactorDCoordinateEquiv (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    {site : L.Site // site ∈ M.exterior region} ≃
      (M.regionSubsystem (region ∪ M.externalBoundary region)).ComplementCoordinates where
  toFun := fun site => ⟨site, by
    intro hunion
    rcases Finset.mem_union.mp hunion with hregion | hexternal
    · exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp site.property).1) hregion
    · exact (Finset.mem_sdiff.mp site.property).2 hexternal⟩
  invFun := fun site => ⟨site, by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr ?_, ?_⟩
    · intro hregion
      exact site.property (Finset.mem_union_left _ hregion)
    · intro hexternal
      exact site.property (Finset.mem_union_right _ hexternal)⟩
  left_inv := by
    intro site
    exact Subtype.ext rfl
  right_inv := by
    intro site
    exact Subtype.ext rfl

set_option maxHeartbeats 800000 in
/-- The concrete internal-boundary register relabeled as the virtual `B` factor. -/
noncomputable def fourFactorBCoordinateRelabel (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (M.regionSubsystem (M.internalBoundary region)).selectedSystem
      ((M.regionSubsystem (M.interior region)).additionalRetainedSystem
        (M.regionSubsystem region)) :=
  quditCoordinateRelabel
    (q := (M.regionSubsystem (M.internalBoundary region)).selectedDimensions)
    (r := (M.regionSubsystem (M.interior region)).additionalRetainedDimensions
      (M.regionSubsystem region))
    (M.fourFactorBCoordinateEquiv region) (by
    intro site
    rfl)

set_option maxHeartbeats 800000 in
/-- The concrete external-boundary register relabeled as the virtual `C` factor. -/
noncomputable def fourFactorCCoordinateRelabel (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (M.regionSubsystem (M.externalBoundary region)).selectedSystem
      ((M.regionSubsystem region).additionalRetainedSystem
        (M.regionSubsystem (region ∪ M.externalBoundary region))) :=
  quditCoordinateRelabel
    (q := (M.regionSubsystem (M.externalBoundary region)).selectedDimensions)
    (r := (M.regionSubsystem region).additionalRetainedDimensions
      (M.regionSubsystem (region ∪ M.externalBoundary region)))
    (M.fourFactorCCoordinateEquiv region) (by
    intro site
    rfl)

set_option maxHeartbeats 800000 in
/-- The source exterior register relabeled as the virtual `D` factor. -/
noncomputable def fourFactorDCoordinateRelabel (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (M.regionSubsystem (M.exterior region)).selectedSystem
      (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem :=
  quditCoordinateRelabel
    (q := (M.regionSubsystem (M.exterior region)).selectedDimensions)
    (r := (M.regionSubsystem (region ∪ M.externalBoundary region)).complementDimensions)
    (M.fourFactorDCoordinateEquiv region) (by
    intro site
    rfl)

/--
The selected coordinates of the literal finite-set complement are the
complement coordinates of the original region.  This site-preserving
equivalence is needed because the two subsystem APIs carry distinct subtype
proofs even though they describe the same physical qudits.
-/
def regionComplementCoordinateEquiv (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    (M.regionSubsystem regionᶜ).SelectedCoordinates ≃
      (M.regionSubsystem region).ComplementCoordinates where
  toFun := fun site => ⟨site, Finset.mem_compl.mp site.property⟩
  invFun := fun site => ⟨site, Finset.mem_compl.mpr site.property⟩
  left_inv := by
    intro site
    exact Subtype.ext rfl
  right_inv := by
    intro site
    exact Subtype.ext rfl

/--
The complement coordinates of the literal complement are the selected
coordinates of the original region.
-/
def regionDoubleComplementCoordinateEquiv (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    (M.regionSubsystem regionᶜ).ComplementCoordinates ≃
      (M.regionSubsystem region).SelectedCoordinates where
  toFun := fun site => ⟨site, by
    by_contra hnotregion
    exact site.property (Finset.mem_compl.mpr hnotregion)⟩
  invFun := fun site => ⟨site, by
    intro hcomplement
    exact (Finset.mem_compl.mp hcomplement) site.property⟩
  left_inv := by
    intro site
    exact Subtype.ext rfl
  right_inv := by
    intro site
    exact Subtype.ext rfl

set_option maxHeartbeats 800000 in
/-- Relabel the selected register of `regionᶜ` as the complement register of `region`. -/
noncomputable def regionComplementCoordinateRelabel (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (M.regionSubsystem regionᶜ).selectedSystem
      (M.regionSubsystem region).complementSystem :=
  quditCoordinateRelabel
    (q := (M.regionSubsystem regionᶜ).selectedDimensions)
    (r := (M.regionSubsystem region).complementDimensions)
    (M.regionComplementCoordinateEquiv region) (by
    intro site
    rfl)

set_option maxHeartbeats 800000 in
/-- Relabel the complement register of `regionᶜ` as the selected register of `region`. -/
noncomputable def regionDoubleComplementCoordinateRelabel
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (M.regionSubsystem regionᶜ).complementSystem
      (M.regionSubsystem region).selectedSystem :=
  quditCoordinateRelabel
    (q := (M.regionSubsystem regionᶜ).complementDimensions)
    (r := (M.regionSubsystem region).selectedDimensions)
    (M.regionDoubleComplementCoordinateEquiv region) (by
    intro site
    rfl)

/-- Extend an operator on a subsystem's complement back to the global register. -/
noncomputable def extendComplementToRegister
    (S : Semantics.QuditSubsystem L.localDimension)
    (P : Semantics.Operator S.complementSystem) : Semantics.Operator L.Register :=
  S.registerFactorization.symm.conjOperator
    (TensorProduct.map (1 : Semantics.Operator S.selectedSystem) P)

/--
The post-factorization coordinate change from the `regionᶜ` split to the
`region` split: relabel both factors and swap their order.  It is the precise
operator-level bridge between an external local representative and a
complement-local representative.
-/
noncomputable def complementPartitionPostTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem
        (M.regionSubsystem regionᶜ).selectedSystem
        (M.regionSubsystem regionᶜ).complementSystem)
      (Semantics.CompositeSystem
        (M.regionSubsystem region).selectedSystem
        (M.regionSubsystem region).complementSystem) :=
  composeUnitaryTransport
    (composeUnitaryTransport
      (unitaryRTensor (M.regionComplementCoordinateRelabel region)
        (M.regionSubsystem regionᶜ).complementSystem)
      (unitaryLTensor (M.regionSubsystem region).complementSystem
        (M.regionDoubleComplementCoordinateRelabel region)))
    (tensorSwapUnitary (M.regionSubsystem region).complementSystem
      (M.regionSubsystem region).selectedSystem)

/--
Factor the global register through `regionᶜ`, then relabel and swap to the
same selected/complement order as the direct `region` factorization.
-/
noncomputable def complementPartitionTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport L.Register
      (Semantics.CompositeSystem
        (M.regionSubsystem region).selectedSystem
        (M.regionSubsystem region).complementSystem) :=
  composeUnitaryTransport (M.regionSubsystem regionᶜ).registerFactorization
    (M.complementPartitionPostTransport region)

/-- The complement-first and region-first register factorizations agree on basis labels. -/
theorem complementPartitionTransport_eq_registerFactorization
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.complementPartitionTransport region =
      (M.regionSubsystem region).registerFactorization := by
  apply unitaryTransport_ext
  apply LinearEquiv.toLinearMap_injective
  apply (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex).toBasis.ext
  intro labels
  let S := M.regionSubsystem region
  let C := M.regionSubsystem regionᶜ
  change M.complementPartitionTransport region
      (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
    S.registerFactorization
      (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels)
  dsimp [complementPartitionTransport, complementPartitionPostTransport]
  rw [C.registerFactorization_apply_basis]
  simp only [unitaryRTensor_apply_tmul, unitaryLTensor_apply_tmul]
  dsimp [regionComplementCoordinateRelabel, regionDoubleComplementCoordinateRelabel]
  erw [quditCoordinateRelabel_apply_basis, quditCoordinateRelabel_apply_basis]
  change
    (EuclideanSpace.basisFun (Semantics.Qudit.Label S.selectedDimensions) Complex
      (quditLabelRelabel (M.regionDoubleComplementCoordinateEquiv region) _
        (C.splitLabel labels).2)) ⊗ₜ[Complex]
      (EuclideanSpace.basisFun (Semantics.Qudit.Label S.complementDimensions) Complex
        (quditLabelRelabel (M.regionComplementCoordinateEquiv region) _
          (C.splitLabel labels).1)) = _
  rw [S.registerFactorization_apply_basis]
  congr 1 <;> funext site <;> rfl

/--
An operator local on the literal complement `regionᶜ` is exactly an identity
on `region` tensored with its explicitly relabeled complement operator.
This is the complement-side support transport used by the `CD` equation.
-/
theorem extendLocalToRegister_complement_eq_extendComplementToRegister
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem regionᶜ).selectedSystem) :
    (M.regionSubsystem regionᶜ).extendLocalToRegister P =
      extendComplementToRegister (M.regionSubsystem region)
        ((M.regionComplementCoordinateRelabel region).conjOperator P) := by
  let S := M.regionSubsystem region
  let C := M.regionSubsystem regionᶜ
  let U := M.regionComplementCoordinateRelabel region
  let V := M.regionDoubleComplementCoordinateRelabel region
  have hfactor : M.complementPartitionTransport region = S.registerFactorization :=
    M.complementPartitionTransport_eq_registerFactorization region
  calc
    C.extendLocalToRegister P =
        S.registerFactorization.symm.conjOperator
          (S.registerFactorization.conjOperator (C.extendLocalToRegister P)) := by
      rw [S.registerFactorization.symm_conjOperator_conjOperator]
    _ = S.registerFactorization.symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator S.selectedSystem)
            (U.conjOperator P)) := by
      congr 1
      rw [← hfactor]
      dsimp [complementPartitionTransport]
      rw [composeUnitaryTransport_conjOperator]
      rw [registerFactorization_conj_extendLocalToRegister]
      dsimp [complementPartitionPostTransport]
      rw [composeUnitaryTransport_conjOperator,
        composeUnitaryTransport_conjOperator]
      rw [unitaryRTensor_conj_tensorMap_left,
        unitaryLTensor_conj_tensorMap_right,
        tensorSwapUnitary_conj_tensorMap]
    _ = extendComplementToRegister S (U.conjOperator P) := rfl

/--
Embed an `AB` operator into the common source four-factor register.  The
associator is explicit: the operator is never redefined by its intended global
conclusion.
-/
noncomputable def fourFactorExtendAB
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (Semantics.CompositeSystem
      (M.fourFactorA region) (M.fourFactorB region))) :
    Semantics.Operator (M.fourFactorSystem region) := by
  let reassociate := TensorProduct.assocIsometry Complex (M.fourFactorA region)
    (M.fourFactorB region)
    (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
  let U : Semantics.UnitaryTransport
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))
      (M.fourFactorSystem region) :=
    { toLinearEquiv := reassociate.toLinearEquiv
      map_inner := reassociate.inner_map_map }
  exact U.conjOperator (TensorProduct.map P
    (1 : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))

/--
The reassociation exposing the middle `BC` factor.  It is a concrete unitary
between two parenthesizations of the same four source coordinates.
-/
noncomputable def fourFactorMiddleReassociate
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport (M.fourFactorSystem region)
      (Semantics.CompositeSystem (M.fourFactorA region)
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region))
          (M.fourFactorD region))) := by
  let reassociate := (TensorProduct.assocIsometry Complex (M.fourFactorB region)
    (M.fourFactorC region) (M.fourFactorD region)).symm
  let e := reassociate.lTensor (M.fourFactorA region)
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := e.inner_map_map }

/-- The inverse middle reassociation restores the canonical `A tensor (B tensor (C tensor D))` order. -/
@[simp]
theorem fourFactorMiddleReassociate_symm_toLinearEquiv_apply_tmul
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (a : M.fourFactorA region) (b : M.fourFactorB region)
    (c : M.fourFactorC region) (d : M.fourFactorD region) :
    (M.fourFactorMiddleReassociate region).symm.toLinearEquiv
        (a ⊗ₜ[Complex] ((b ⊗ₜ[Complex] c) ⊗ₜ[Complex] d)) =
      a ⊗ₜ[Complex] (b ⊗ₜ[Complex] (c ⊗ₜ[Complex] d)) := by
  rfl

/-- Embed a `BC` operator into the common source four-factor register. -/
noncomputable def fourFactorExtendBC
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (Semantics.CompositeSystem
      (M.fourFactorB region) (M.fourFactorC region))) :
    Semantics.Operator (M.fourFactorSystem region) :=
  (M.fourFactorMiddleReassociate region).symm.conjOperator
    (TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
      (TensorProduct.map P (1 : Semantics.Operator (M.fourFactorD region))))

/-- Embed a `CD` operator into the common source four-factor register. -/
noncomputable def fourFactorExtendCD
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (Semantics.CompositeSystem
      ((M.regionSubsystem region).additionalRetainedSystem
        (M.regionSubsystem (region ∪ M.externalBoundary region)))
      (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem)) :
    Semantics.Operator (Semantics.CompositeSystem
      (M.regionSubsystem (M.interior region)).selectedSystem
      (Semantics.CompositeSystem
        ((M.regionSubsystem (M.interior region)).additionalRetainedSystem
          (M.regionSubsystem region))
        (Semantics.CompositeSystem
          ((M.regionSubsystem region).additionalRetainedSystem
            (M.regionSubsystem (region ∪ M.externalBoundary region)))
          (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem))) :=
  TensorProduct.map (1 : Semantics.Operator
    (M.regionSubsystem (M.interior region)).selectedSystem)
    (TensorProduct.map (1 : Semantics.Operator
      ((M.regionSubsystem (M.interior region)).additionalRetainedSystem
        (M.regionSubsystem region))) P)

/--
Split the literal complement of `region` into the source `C D` coordinates.
The first stage identifies `regionᶜ` with the complement register of `region`;
the second is the cumulative #400 complement factorization `AB subset ABC`.
-/
noncomputable def fourFactorCDCoordinateTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (M.regionSubsystem regionᶜ).selectedSystem
      (Semantics.CompositeSystem
        ((M.regionSubsystem region).additionalRetainedSystem
          (M.regionSubsystem (region ∪ M.externalBoundary region)))
        (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem) := by
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  exact composeUnitaryTransport (M.regionComplementCoordinateRelabel region)
    (AB.complementFactorization ABC hABABC)

/--
The coordinates added when splitting the concrete boundary after its internal
part are exactly the virtual external `C` coordinates.  This is the selected
half of the middle-overlap coordinate transport.
-/
def boundaryAdditionalCoordinateEquiv (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    (M.regionSubsystem (M.internalBoundary region)).AdditionalRetainedCoordinates
      (M.regionSubsystem (M.boundary region)) ≃
      (M.regionSubsystem region).AdditionalRetainedCoordinates
        (M.regionSubsystem (region ∪ M.externalBoundary region)) where
  toFun := fun site => ⟨site, by
    have hboundary : (site : L.Site) ∈
        M.internalBoundary region ∪ M.externalBoundary region := by
      rw [← M.boundary_eq_internal_union_external region]
      exact site.property.2
    rcases Finset.mem_union.mp hboundary with hinternal | hexternal
    · exact False.elim (site.property.1 hinternal)
    · constructor
      · intro hregion
        exact (Finset.disjoint_left.mp (M.externalBoundary_disjoint_region region))
          hexternal hregion
      · exact Finset.mem_union_right _ hexternal⟩
  invFun := fun site => ⟨site, by
    have hexternal : (site : L.Site) ∈ M.externalBoundary region := by
      rcases Finset.mem_union.mp site.property.2 with hregion | hexternal
      · exact False.elim (site.property.1 hregion)
      · exact hexternal
    constructor
    · intro hinternal
      exact site.property.1 (Finset.mem_inter.mp hinternal).2
    · rw [M.boundary_eq_internal_union_external region]
      exact Finset.mem_union_right _ hexternal⟩
  left_inv := by
    intro site
    exact Subtype.ext rfl
  right_inv := by
    intro site
    exact Subtype.ext rfl

/--
The coordinates retained after removing the boundary from `ABC` are exactly
the source interior `A` coordinates.  This is the complement half of the
middle-overlap coordinate transport.
-/
def boundaryComplementAdditionalCoordinateEquiv
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem (M.boundary region)).AdditionalRetainedCoordinates
      (M.regionSubsystem (region ∪ M.externalBoundary region)) ≃
      (M.regionSubsystem (M.interior region)).SelectedCoordinates where
  toFun := fun site => ⟨site, by
    have hnotBoundary : (site : L.Site) ∉ M.boundary region := site.property.1
    rcases Finset.mem_union.mp site.property.2 with hregion | hexternal
    · refine Finset.mem_sdiff.mpr ⟨hregion, ?_⟩
      intro hinternal
      have hboundary : (site : L.Site) ∈ M.boundary region :=
        Eq.mp
          (congrArg (fun s : Finset L.Site => (site : L.Site) ∈ s)
            (M.boundary_eq_internal_union_external region)).symm
          (Finset.mem_union_left _ hinternal)
      exact hnotBoundary hboundary
    · have hboundary : (site : L.Site) ∈ M.boundary region :=
        Eq.mp
          (congrArg (fun s : Finset L.Site => (site : L.Site) ∈ s)
            (M.boundary_eq_internal_union_external region)).symm
          (Finset.mem_union_right _ hexternal)
      exact False.elim (hnotBoundary hboundary)⟩
  invFun := fun site => ⟨site, by
    constructor
    · have hinterior' : (site : L.Site) ∈ region \ M.boundary region := by
        rw [← M.interior_eq_region_sdiff_boundary region]
        exact site.property
      exact (Finset.mem_sdiff.mp hinterior').2
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp site.property).1⟩
  left_inv := by
    intro site
    exact Subtype.ext rfl
  right_inv := by
    intro site
    exact Subtype.ext rfl

/-- Split the concrete boundary register into the virtual source `B tensor C` register. -/
noncomputable def boundarySelectedToBCTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (M.regionSubsystem (M.boundary region)).selectedSystem
      (Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region)) := by
  let B := M.regionSubsystem (M.internalBoundary region)
  let BC := M.regionSubsystem (M.boundary region)
  have hBBC : B.selected ⊆ BC.selected := by
    intro site hsite
    have hinternal : site ∈ M.internalBoundary region := hsite
    change site ∈ M.boundary region
    rw [M.boundary_eq_internal_union_external region]
    exact Finset.mem_union_left _ hinternal
  let splitB := B.selectedFactorization BC hBBC
  let relabelC := quditCoordinateRelabel
    (q := B.additionalRetainedDimensions BC)
    (r := (M.regionSubsystem region).additionalRetainedDimensions
      (M.regionSubsystem (region ∪ M.externalBoundary region)))
    (M.boundaryAdditionalCoordinateEquiv region) (by
    intro site
    rfl)
  exact composeUnitaryTransport
    (composeUnitaryTransport splitB
      (unitaryRTensor (M.fourFactorBCoordinateRelabel region)
        (B.additionalRetainedSystem BC)))
    (unitaryLTensor (M.fourFactorB region) relabelC)

/-- Split the concrete boundary complement into the virtual source `A tensor D` register. -/
noncomputable def boundaryComplementToADTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (M.regionSubsystem (M.boundary region)).complementSystem
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorD region)) := by
  let BC := M.regionSubsystem (M.boundary region)
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hBCABC : BC.selected ⊆ ABC.selected := by
    intro site hsite
    have hboundary : site ∈ M.boundary region := hsite
    change site ∈ region ∪ M.externalBoundary region
    rw [M.boundary_eq_internal_union_external region] at hboundary
    rcases Finset.mem_union.mp hboundary with hinternal | hexternal
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp hinternal).2
    · exact Finset.mem_union_right _ hexternal
  let splitAD := BC.complementFactorization ABC hBCABC
  let relabelA := quditCoordinateRelabel
    (q := BC.additionalRetainedDimensions ABC)
    (r := (M.regionSubsystem (M.interior region)).selectedDimensions)
    (M.boundaryComplementAdditionalCoordinateEquiv region) (by
      intro site
      rfl)
  exact composeUnitaryTransport splitAD
    (unitaryRTensor relabelA ABC.complementSystem)

/-- The selected boundary split is the literal `B tensor C` basis relabeling. -/
theorem boundarySelectedToBCTransport_toLinearEquiv_apply_basis
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (labels : Semantics.Qudit.Label
      (M.regionSubsystem (M.boundary region)).selectedDimensions) :
    (M.boundarySelectedToBCTransport region).toLinearEquiv
        (EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            (M.regionSubsystem (M.boundary region)).selectedDimensions) Complex labels) =
      M.fourFactorBCoordinateRelabel region
        (EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            (M.regionSubsystem (M.internalBoundary region)).selectedDimensions) Complex
          ((M.regionSubsystem (M.internalBoundary region)).splitSelectedLabel
            (M.regionSubsystem (M.boundary region))
            (by
              intro site hsite
              change site ∈ M.boundary region
              rw [M.boundary_eq_internal_union_external region]
              exact Finset.mem_union_left _ hsite)
            labels).1) ⊗ₜ[Complex]
      (quditCoordinateRelabel
          (q := (M.regionSubsystem (M.internalBoundary region)).additionalRetainedDimensions
            (M.regionSubsystem (M.boundary region)))
          (r := (M.regionSubsystem region).additionalRetainedDimensions
            (M.regionSubsystem (region ∪ M.externalBoundary region)))
          (M.boundaryAdditionalCoordinateEquiv region) (by
            intro site
            rfl))
        (EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            ((M.regionSubsystem (M.internalBoundary region)).additionalRetainedDimensions
              (M.regionSubsystem (M.boundary region))))
          Complex
          ((M.regionSubsystem (M.internalBoundary region)).splitSelectedLabel
            (M.regionSubsystem (M.boundary region))
            (by
              intro site hsite
              change site ∈ M.boundary region
              rw [M.boundary_eq_internal_union_external region]
              exact Finset.mem_union_left _ hsite)
            labels).2) := by
  let B := M.regionSubsystem (M.internalBoundary region)
  let BC := M.regionSubsystem (M.boundary region)
  have hBBC : B.selected ⊆ BC.selected := by
    intro site hsite
    change site ∈ M.boundary region
    rw [M.boundary_eq_internal_union_external region]
    exact Finset.mem_union_left _ hsite
  dsimp [boundarySelectedToBCTransport]
  rw [B.selectedFactorization_apply_basis BC hBBC]
  simp only [composeUnitaryTransport_toLinearEquiv_apply,
    unitaryRTensor_toLinearEquiv_apply_tmul,
    unitaryLTensor_toLinearEquiv_apply_tmul]
  rfl

/-- The complementary boundary split is the literal `A tensor D` basis relabeling. -/
theorem boundaryComplementToADTransport_toLinearEquiv_apply_basis
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (labels : Semantics.Qudit.Label
      (M.regionSubsystem (M.boundary region)).complementDimensions) :
    (M.boundaryComplementToADTransport region).toLinearEquiv
        (EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            (M.regionSubsystem (M.boundary region)).complementDimensions) Complex labels) =
      (quditCoordinateRelabel
          (q := (M.regionSubsystem (M.boundary region)).additionalRetainedDimensions
            (M.regionSubsystem (region ∪ M.externalBoundary region)))
          (r := (M.regionSubsystem (M.interior region)).selectedDimensions)
          (M.boundaryComplementAdditionalCoordinateEquiv region) (by
            intro site
            rfl))
        (EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            ((M.regionSubsystem (M.boundary region)).additionalRetainedDimensions
              (M.regionSubsystem (region ∪ M.externalBoundary region))))
          Complex
          ((M.regionSubsystem (M.boundary region)).splitComplementLabel
            (M.regionSubsystem (region ∪ M.externalBoundary region))
            (by
              intro site hsite
              change site ∈ region ∪ M.externalBoundary region
              rw [M.boundary_eq_internal_union_external region] at hsite
              rcases Finset.mem_union.mp hsite with hinternal | hexternal
              · exact Finset.mem_union_left _ (Finset.mem_inter.mp hinternal).2
              · exact Finset.mem_union_right _ hexternal)
            labels).1) ⊗ₜ[Complex]
      EuclideanSpace.basisFun
        (Semantics.Qudit.Label
          (M.regionSubsystem (region ∪ M.externalBoundary region)).complementDimensions) Complex
        ((M.regionSubsystem (M.boundary region)).splitComplementLabel
          (M.regionSubsystem (region ∪ M.externalBoundary region))
          (by
            intro site hsite
            change site ∈ region ∪ M.externalBoundary region
            rw [M.boundary_eq_internal_union_external region] at hsite
            rcases Finset.mem_union.mp hsite with hinternal | hexternal
            · exact Finset.mem_union_left _ (Finset.mem_inter.mp hinternal).2
            · exact Finset.mem_union_right _ hexternal)
          labels).2 := by
  let BC := M.regionSubsystem (M.boundary region)
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hBCABC : BC.selected ⊆ ABC.selected := by
    intro site hsite
    have hboundary : site ∈ M.boundary region := hsite
    change site ∈ region ∪ M.externalBoundary region
    rw [M.boundary_eq_internal_union_external region] at hboundary
    rcases Finset.mem_union.mp hboundary with hinternal | hexternal
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp hinternal).2
    · exact Finset.mem_union_right _ hexternal
  dsimp [boundaryComplementToADTransport]
  rw [BC.complementFactorization_apply_basis ABC hBCABC]
  simp only [composeUnitaryTransport_toLinearEquiv_apply,
    unitaryRTensor_toLinearEquiv_apply_tmul]
  rfl

/-- The named `A tensor D` computational vector produced by the complementary boundary split. -/
noncomputable def boundaryComplementToADBasisVector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (labels : Semantics.Qudit.Label
      (M.regionSubsystem (M.boundary region)).complementDimensions) :
    Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorD region) :=
  (quditCoordinateRelabel
      (q := (M.regionSubsystem (M.boundary region)).additionalRetainedDimensions
        (M.regionSubsystem (region ∪ M.externalBoundary region)))
      (r := (M.regionSubsystem (M.interior region)).selectedDimensions)
      (M.boundaryComplementAdditionalCoordinateEquiv region) (by
        intro site
        rfl))
    (EuclideanSpace.basisFun
      (Semantics.Qudit.Label
        ((M.regionSubsystem (M.boundary region)).additionalRetainedDimensions
          (M.regionSubsystem (region ∪ M.externalBoundary region))))
      Complex
      ((M.regionSubsystem (M.boundary region)).splitComplementLabel
        (M.regionSubsystem (region ∪ M.externalBoundary region))
        (by
          intro site hsite
          change site ∈ region ∪ M.externalBoundary region
          rw [M.boundary_eq_internal_union_external region] at hsite
          rcases Finset.mem_union.mp hsite with hinternal | hexternal
          · exact Finset.mem_union_left _ (Finset.mem_inter.mp hinternal).2
          · exact Finset.mem_union_right _ hexternal)
        labels).1) ⊗ₜ[Complex]
  EuclideanSpace.basisFun
    (Semantics.Qudit.Label
      (M.regionSubsystem (region ∪ M.externalBoundary region)).complementDimensions) Complex
    ((M.regionSubsystem (M.boundary region)).splitComplementLabel
      (M.regionSubsystem (region ∪ M.externalBoundary region))
      (by
        intro site hsite
        change site ∈ region ∪ M.externalBoundary region
        rw [M.boundary_eq_internal_union_external region] at hsite
        rcases Finset.mem_union.mp hsite with hinternal | hexternal
        · exact Finset.mem_union_left _ (Finset.mem_inter.mp hinternal).2
        · exact Finset.mem_union_right _ hexternal)
      labels).2

/-- The complementary boundary transport has the compact named `A tensor D` basis output. -/
theorem boundaryComplementToADTransport_apply_boundaryComplementToADBasisVector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (labels : Semantics.Qudit.Label
      (M.regionSubsystem (M.boundary region)).complementDimensions) :
    (M.boundaryComplementToADTransport region).toLinearEquiv
        (EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            (M.regionSubsystem (M.boundary region)).complementDimensions) Complex labels) =
      M.boundaryComplementToADBasisVector region labels := by
  unfold boundaryComplementToADBasisVector
  exact M.boundaryComplementToADTransport_toLinearEquiv_apply_basis region labels

/-- Reorder `(B tensor C) tensor (A tensor D)` into `A tensor ((B tensor C) tensor D)`. -/
noncomputable def boundaryToMiddleReorder
    (A B C D : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D] :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem (Semantics.CompositeSystem B C)
        (Semantics.CompositeSystem A D))
      (Semantics.CompositeSystem A
        (Semantics.CompositeSystem (Semantics.CompositeSystem B C) D)) :=
  composeUnitaryTransport
    (composeUnitaryTransport
      (tensorAssociatorUnitary (Semantics.CompositeSystem B C) A D).symm
    (unitaryRTensor (tensorSwapUnitary (Semantics.CompositeSystem B C) A) D))
    (tensorAssociatorUnitary A (Semantics.CompositeSystem B C) D)

/-- The boundary permutation has its literal four-vector action. -/
@[simp]
theorem boundaryToMiddleReorder_toLinearEquiv_apply_tmul
    (A B C D : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (a : A) (b : B) (c : C) (d : D) :
    (boundaryToMiddleReorder A B C D).toLinearEquiv
        ((b ⊗ₜ[Complex] c) ⊗ₜ[Complex] (a ⊗ₜ[Complex] d)) =
      a ⊗ₜ[Complex] ((b ⊗ₜ[Complex] c) ⊗ₜ[Complex] d) := by
  simp only [boundaryToMiddleReorder, composeUnitaryTransport_toLinearEquiv_apply,
    tensorAssociatorUnitary_symm_toLinearEquiv_apply_tmul,
    unitaryRTensor_toLinearEquiv_apply_tmul,
    tensorSwapUnitary_toLinearEquiv_apply_tmul,
    tensorAssociatorUnitary_toLinearEquiv_apply_tmul]

/-- The boundary ordering followed by the middle reassociation is the canonical four-factor order. -/
theorem boundaryToFourFactorReorder_toLinearEquiv_apply_tmul
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (a : M.fourFactorA region) (b : M.fourFactorB region)
    (c : M.fourFactorC region) (d : M.fourFactorD region) :
    (M.fourFactorMiddleReassociate region).symm.toLinearEquiv
        ((boundaryToMiddleReorder (M.fourFactorA region) (M.fourFactorB region)
            (M.fourFactorC region) (M.fourFactorD region)).toLinearEquiv
          ((b ⊗ₜ[Complex] c) ⊗ₜ[Complex] (a ⊗ₜ[Complex] d))) =
      a ⊗ₜ[Complex] (b ⊗ₜ[Complex] (c ⊗ₜ[Complex] d)) := by
  rw [boundaryToMiddleReorder_toLinearEquiv_apply_tmul]
  exact M.fourFactorMiddleReassociate_symm_toLinearEquiv_apply_tmul region a b c d

/--
Put the global register into the parenthesization exposing the true middle
overlap `BC`.  It is built entirely from the concrete boundary factorization,
the two coordinate splits above, and tensor associativity/symmetry.
-/
noncomputable def boundaryGlobalToMiddleTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport L.Register
      (Semantics.CompositeSystem (M.fourFactorA region)
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region))
          (M.fourFactorD region))) := by
  let BC := M.regionSubsystem (M.boundary region)
  let splitSelected := M.boundarySelectedToBCTransport region
  let splitComplement := M.boundaryComplementToADTransport region
  exact composeUnitaryTransport
    (composeUnitaryTransport
      (composeUnitaryTransport BC.registerFactorization
        (unitaryRTensor splitSelected BC.complementSystem))
      (unitaryLTensor (Semantics.CompositeSystem (M.fourFactorB region)
        (M.fourFactorC region)) splitComplement))
    (boundaryToMiddleReorder (M.fourFactorA region) (M.fourFactorB region)
      (M.fourFactorC region) (M.fourFactorD region))

/-- The boundary-based middle transport followed by reassociation gives the common four factors. -/
noncomputable def boundaryGlobalToFourFactorTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport L.Register (M.fourFactorSystem region) :=
  composeUnitaryTransport (M.boundaryGlobalToMiddleTransport region)
    (M.fourFactorMiddleReassociate region).symm

/--
The boundary-based coordinate route and the cumulative source route agree on
every global computational basis vector.  This is the transport certificate
that lets the genuine boundary-overlap support equation be stated on the one
canonical four-factor register.
-/
theorem boundaryGlobalToFourFactorTransport_apply_basis_eq_fourFactorTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (labels : Semantics.Qudit.Label L.localDimension) :
    (M.boundaryGlobalToFourFactorTransport region).toLinearEquiv
        (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
      (M.fourFactorTransport region).toLinearEquiv
        (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) := by
  let B := M.regionSubsystem (M.internalBoundary region)
  let BC := M.regionSubsystem (M.boundary region)
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hBBC : B.selected ⊆ BC.selected := by
    intro site hsite
    have hinternal : site ∈ M.internalBoundary region := hsite
    change site ∈ M.boundary region
    rw [M.boundary_eq_internal_union_external region]
    exact Finset.mem_union_left _ hinternal
  have hBCABC : BC.selected ⊆ ABC.selected := by
    intro site hsite
    have hboundary : site ∈ M.boundary region := hsite
    change site ∈ region ∪ M.externalBoundary region
    rw [M.boundary_eq_internal_union_external region] at hboundary
    rcases Finset.mem_union.mp hboundary with hinternal | hexternal
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp hinternal).2
    · exact Finset.mem_union_right _ hexternal
  rw [M.fourFactorTransport_apply_fourFactorBasisVector]
  simp only [boundaryGlobalToFourFactorTransport,
    composeUnitaryTransport_toLinearEquiv_apply]
  simp only [boundaryGlobalToMiddleTransport,
    composeUnitaryTransport_toLinearEquiv_apply]
  rw [BC.registerFactorization_apply_basis]
  simp only [unitaryRTensor_toLinearEquiv_apply_tmul,
    unitaryLTensor_toLinearEquiv_apply_tmul]
  dsimp only [BC]
  have hAD := M.boundaryComplementToADTransport_apply_boundaryComplementToADBasisVector
    region ((M.regionSubsystem (M.boundary region)).splitLabel labels).2
  refine (congrArg
    (fun vector : Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorD region) =>
      (M.fourFactorMiddleReassociate region).symm.toLinearEquiv
        ((boundaryToMiddleReorder (M.fourFactorA region) (M.fourFactorB region)
            (M.fourFactorC region) (M.fourFactorD region)).toLinearEquiv
          ((M.boundarySelectedToBCTransport region).toLinearEquiv
              (EuclideanSpace.basisFun
                (Semantics.Qudit.Label
                  (M.regionSubsystem (M.boundary region)).selectedDimensions) Complex
                ((M.regionSubsystem (M.boundary region)).splitLabel labels).1) ⊗ₜ[Complex]
            vector))) hAD).trans ?_
  have hBC := M.boundarySelectedToBCTransport_toLinearEquiv_apply_basis
    region ((M.regionSubsystem (M.boundary region)).splitLabel labels).1
  refine (congrArg
    (fun vector : Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region) =>
      (M.fourFactorMiddleReassociate region).symm.toLinearEquiv
        ((boundaryToMiddleReorder (M.fourFactorA region) (M.fourFactorB region)
            (M.fourFactorC region) (M.fourFactorD region)).toLinearEquiv
          (vector ⊗ₜ[Complex]
            M.boundaryComplementToADBasisVector region
              ((M.regionSubsystem (M.boundary region)).splitLabel labels).2))) hBC).trans ?_
  unfold boundaryComplementToADBasisVector
  rw [M.boundaryToFourFactorReorder_toLinearEquiv_apply_tmul]
  dsimp [fourFactorBCoordinateRelabel]
  erw [quditCoordinateRelabel_apply_basis]
  erw [quditCoordinateRelabel_apply_basis]
  erw [quditCoordinateRelabel_apply_basis]
  unfold fourFactorBasisVector
  congr 1 <;> funext site <;> rfl

/-- The boundary-based full transport is exactly the canonical four-factor transport. -/
theorem boundaryGlobalToFourFactorTransport_eq_fourFactorTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.boundaryGlobalToFourFactorTransport region = M.fourFactorTransport region := by
  apply unitaryTransport_ext
  apply LinearEquiv.toLinearMap_injective
  apply (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex).toBasis.ext
  intro labels
  exact M.boundaryGlobalToFourFactorTransport_apply_basis_eq_fourFactorTransport region labels

/--
The boundary-to-middle permutation carries an operator on `BC` to the middle
factor while leaving the source interior and exterior identities untouched.
-/
theorem boundaryToMiddleReorder_conj_middle
    (A B C D : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (P : Semantics.Operator (Semantics.CompositeSystem B C)) :
    (boundaryToMiddleReorder A B C D).conjOperator
        (TensorProduct.map P (1 : Semantics.Operator (Semantics.CompositeSystem A D))) =
      TensorProduct.map (1 : Semantics.Operator A)
        (TensorProduct.map P (1 : Semantics.Operator D)) := by
  have hidentity : (1 : Semantics.Operator (Semantics.CompositeSystem A D)) =
      TensorProduct.map (1 : Semantics.Operator A) (1 : Semantics.Operator D) := by
    symm
    exact TensorProduct.map_one
  rw [hidentity]
  dsimp [boundaryToMiddleReorder]
  rw [composeUnitaryTransport_conjOperator, composeUnitaryTransport_conjOperator]
  rw [tensorAssociatorUnitary_symm_conj_tensorMap]
  rw [unitaryRTensor_conj_tensorMap_left]
  rw [tensorSwapUnitary_conj_tensorMap]
  rw [tensorAssociatorUnitary_conj_tensorMap]

set_option maxHeartbeats 800000 in
/--
Conjugating an arbitrary concrete boundary-local extension through the
boundary-based global route produces an identity on `A`, the transported
operator on `BC`, and an identity on `D`.
-/
theorem boundaryGlobalToMiddleTransport_conj_extendLocalToRegister
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem (M.boundary region)).selectedSystem) :
    (M.boundaryGlobalToMiddleTransport region).conjOperator
        ((M.regionSubsystem (M.boundary region)).extendLocalToRegister P) =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map ((M.boundarySelectedToBCTransport region).conjOperator P)
          (1 : Semantics.Operator (M.fourFactorD region))) := by
  let BC := M.regionSubsystem (M.boundary region)
  let selectedTransport := M.boundarySelectedToBCTransport region
  let complementTransport := M.boundaryComplementToADTransport region
  dsimp [boundaryGlobalToMiddleTransport]
  rw [composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator]
  rw [registerFactorization_conj_extendLocalToRegister]
  rw [unitaryRTensor_conj_tensorMap_left,
    unitaryLTensor_conj_tensorMap_right]
  exact boundaryToMiddleReorder_conj_middle
    (M.fourFactorA region) (M.fourFactorB region) (M.fourFactorC region)
    (M.fourFactorD region) (selectedTransport.conjOperator P)

/--
The boundary-based full four-factor route has the exact `BC` support equation
for every boundary-local operator.  The later equality of coordinate routes
will transfer this statement to `fourFactorTransport` itself.
-/
theorem boundaryGlobalToFourFactorTransport_conj_extendLocalToRegister
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem (M.boundary region)).selectedSystem) :
    (M.boundaryGlobalToFourFactorTransport region).conjOperator
        ((M.regionSubsystem (M.boundary region)).extendLocalToRegister P) =
      M.fourFactorExtendBC region
        ((M.boundarySelectedToBCTransport region).conjOperator P) := by
  dsimp [boundaryGlobalToFourFactorTransport]
  rw [composeUnitaryTransport_conjOperator]
  rw [M.boundaryGlobalToMiddleTransport_conj_extendLocalToRegister]
  rfl

/-- Lift a physical boundary-selected unitary to a unitary on the full register. -/
noncomputable def boundaryLocalUnitaryToRegister
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (U : Semantics.UnitaryTransport
      (M.regionSubsystem (M.boundary region)).selectedSystem
      (M.regionSubsystem (M.boundary region)).selectedSystem) :
    Semantics.UnitaryTransport L.Register L.Register :=
  extendLocalUnitaryToRegister L.localDimension
    (M.regionSubsystem (M.boundary region)) U

/-- The lifted boundary unitary is physically supported on the boundary sites. -/
theorem boundaryLocalUnitaryToRegister_supported
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (U : Semantics.UnitaryTransport
      (M.regionSubsystem (M.boundary region)).selectedSystem
      (M.regionSubsystem (M.boundary region)).selectedSystem) :
    M.UnitarySupportedOn (M.boundary region)
      (M.boundaryLocalUnitaryToRegister region U) := by
  refine ⟨U.toLinearEquiv.toLinearMap, ?_⟩
  exact extendLocalUnitaryToRegister_toLinearMap_eq L.localDimension
    (M.regionSubsystem (M.boundary region)) U

/--
The physical boundary lift is exactly the corresponding `BC` action in the
boundary-based four-factor coordinates.
-/
theorem boundaryGlobalToFourFactorTransport_conj_boundaryLocalUnitaryToRegister
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (U : Semantics.UnitaryTransport
      (M.regionSubsystem (M.boundary region)).selectedSystem
      (M.regionSubsystem (M.boundary region)).selectedSystem) :
    (M.boundaryGlobalToFourFactorTransport region).conjOperator
        (M.boundaryLocalUnitaryToRegister region U).toLinearEquiv.toLinearMap =
      M.fourFactorExtendBC region
        ((M.boundarySelectedToBCTransport region).conjOperator U.toLinearEquiv.toLinearMap) := by
  change (M.boundaryGlobalToFourFactorTransport region).conjOperator
      (extendLocalUnitaryToRegister L.localDimension
        (M.regionSubsystem (M.boundary region)) U).toLinearEquiv.toLinearMap = _
  rw [extendLocalUnitaryToRegister_toLinearMap_eq]
  exact M.boundaryGlobalToFourFactorTransport_conj_extendLocalToRegister region _

/-- The canonical four-factor route has the same exact physical-boundary lift equation. -/
theorem fourFactorTransport_conj_boundaryLocalUnitaryToRegister
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (U : Semantics.UnitaryTransport
      (M.regionSubsystem (M.boundary region)).selectedSystem
      (M.regionSubsystem (M.boundary region)).selectedSystem) :
    (M.fourFactorTransport region).conjOperator
        (M.boundaryLocalUnitaryToRegister region U).toLinearEquiv.toLinearMap =
      M.fourFactorExtendBC region
        ((M.boundarySelectedToBCTransport region).conjOperator U.toLinearEquiv.toLinearMap) := by
  rw [← M.boundaryGlobalToFourFactorTransport_eq_fourFactorTransport region]
  exact M.boundaryGlobalToFourFactorTransport_conj_boundaryLocalUnitaryToRegister region U

/--
Pull the active physical `B tensor C` sector unitary back to the actual
boundary-selected subsystem.
-/
noncomputable def activeSectorBoundaryUnitary
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {WB NB WC NC : Type} [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC]
    (SB : Submodule Complex (M.fourFactorB region))
    (SC : Submodule Complex (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport SB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport SC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    Semantics.UnitaryTransport
      (M.regionSubsystem (M.boundary region)).selectedSystem
      (M.regionSubsystem (M.boundary region)).selectedSystem :=
  conjugateUnitaryTransport (M.boundarySelectedToBCTransport region)
    (activeSectorPhysicalUnitary SB SC UB UC U)

/--
Extend the active boundary operation to the full physical register.
-/
noncomputable def activeSectorBoundaryGlobalUnitary
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {WB NB WC NC : Type} [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC]
    (SB : Submodule Complex (M.fourFactorB region))
    (SC : Submodule Complex (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport SB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport SC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    Semantics.UnitaryTransport L.Register L.Register :=
  M.boundaryLocalUnitaryToRegister region
    (M.activeSectorBoundaryUnitary region SB SC UB UC U)

/-- The active-sector physical unitary is supported on the physical boundary. -/
theorem activeSectorBoundaryGlobalUnitary_supported
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {WB NB WC NC : Type} [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC]
    (SB : Submodule Complex (M.fourFactorB region))
    (SC : Submodule Complex (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport SB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport SC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    M.UnitarySupportedOn (M.boundary region)
      (M.activeSectorBoundaryGlobalUnitary region SB SC UB UC U) := by
  unfold activeSectorBoundaryGlobalUnitary
  exact M.boundaryLocalUnitaryToRegister_supported region
    (M.activeSectorBoundaryUnitary region SB SC UB UC U)

/--
In canonical four-factor coordinates, the physical global lift is exactly the
corresponding active `B tensor C` unitary with identities on `A` and `D`.
-/
theorem fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {WB NB WC NC : Type} [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC]
    (SB : Submodule Complex (M.fourFactorB region))
    (SC : Submodule Complex (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport SB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport SC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    (M.fourFactorTransport region).conjOperator
      (M.activeSectorBoundaryGlobalUnitary region SB SC UB UC U).toLinearEquiv.toLinearMap =
      M.fourFactorExtendBC region
        (activeSectorPhysicalUnitary SB SC UB UC U).toLinearEquiv.toLinearMap := by
  unfold activeSectorBoundaryGlobalUnitary
  rw [M.fourFactorTransport_conj_boundaryLocalUnitaryToRegister]
  unfold activeSectorBoundaryUnitary
  exact congrArg (M.fourFactorExtendBC region)
    (conj_conjugateUnitaryTransport_toLinearMap
      (M.boundarySelectedToBCTransport region)
      (activeSectorPhysicalUnitary SB SC UB UC U))

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 800000 in
/--
Under the `AB`-first four-factor transport, a complement-local operator is
the identity on `A B` tensored with its explicitly split `C D` action.
-/
theorem fourFactorTransportFromRegion_conj_extendComplementToRegister
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem region).complementSystem) :
    (M.fourFactorTransportFromRegion region).conjOperator
        (extendComplementToRegister (M.regionSubsystem region) P) =
      M.fourFactorExtendCD region
        (((M.regionSubsystem region).complementFactorization
          (M.regionSubsystem (region ∪ M.externalBoundary region))
          (by
            intro site hsite
            exact Finset.mem_union_left _ hsite)).conjOperator P) := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  let splitAB : Semantics.UnitaryTransport AB.selectedSystem
      (Semantics.CompositeSystem A.selectedSystem (A.additionalRetainedSystem AB)) := by
    let e := A.selectedFactorization AB hAAB
    exact
      { toLinearEquiv := e.toLinearEquiv
        map_inner := e.map_inner }
  let splitCD := AB.complementFactorization ABC hABABC
  dsimp [fourFactorTransportFromRegion, extendComplementToRegister]
  rw [composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator]
  rw [AB.registerFactorization.conjOperator_symm_conjOperator]
  rw [unitaryRTensor_conj_tensorMap_right,
    unitaryLTensor_conj_tensorMap_left]
  change (tensorAssociatorUnitary A.selectedSystem (A.additionalRetainedSystem AB)
      (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem)).conjOperator
      (TensorProduct.map (1 : Semantics.Operator
        (Semantics.CompositeSystem A.selectedSystem (A.additionalRetainedSystem AB)))
        (splitCD.conjOperator P)) =
    TensorProduct.map (1 : Semantics.Operator A.selectedSystem)
      (TensorProduct.map (1 : Semantics.Operator (A.additionalRetainedSystem AB))
        (splitCD.conjOperator P))
  rw [show (1 : Semantics.Operator
      (Semantics.CompositeSystem A.selectedSystem (A.additionalRetainedSystem AB))) =
        TensorProduct.map (1 : Semantics.Operator A.selectedSystem)
          (1 : Semantics.Operator (A.additionalRetainedSystem AB)) by
        symm
        exact TensorProduct.map_one]
  exact tensorAssociatorUnitary_conj_tensorMap
    (1 : Semantics.Operator A.selectedSystem)
    (1 : Semantics.Operator (A.additionalRetainedSystem AB))
    (splitCD.conjOperator P)

/-- A local projector touching the source interior cannot cross out of `M`. -/
theorem support_subset_region_of_mem_interior
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) (check : kappa)
    {site : L.Site} (hsupport : site ∈ M.support check) (hinterior : site ∈ M.interior region) :
    M.support check ⊆ region := by
  intro other hother
  by_contra hnotregion
  have hcouples : M.supportCouples check region := by
    constructor
    · exact ⟨site, Finset.mem_inter.mpr ⟨hsupport, (Finset.mem_sdiff.mp hinterior).1⟩⟩
    · exact ⟨other, Finset.mem_sdiff.mpr ⟨hother, hnotregion⟩⟩
  have hboundary : site ∈ M.boundary region :=
    M.support_subset_boundary_of_couples region check hcouples hsupport
  have hinterior' : site ∈ region \ M.boundary region := by
    rw [← M.interior_eq_region_sdiff_boundary region]
    exact hinterior
  exact (Finset.mem_sdiff.mp hinterior').2 hboundary

/-- A local projector touching the source exterior cannot cross into `M`. -/
theorem support_subset_complement_of_mem_exterior
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) (check : kappa)
    {site : L.Site} (hsupport : site ∈ M.support check) (hexterior : site ∈ M.exterior region) :
    M.support check ⊆ regionᶜ := by
  intro other hother
  apply Finset.mem_compl.mpr
  by_contra hregion
  have hcouples : M.supportCouples check region := by
    constructor
    · exact ⟨other, Finset.mem_inter.mpr ⟨hother, hregion⟩⟩
    · exact ⟨site, Finset.mem_sdiff.mpr ⟨hsupport,
        Finset.mem_compl.mp (Finset.mem_sdiff.mp hexterior).1⟩⟩
  have hexternal : site ∈ M.externalBoundary region :=
    (M.mem_externalBoundary_iff region site).mpr
      ⟨Finset.mem_compl.mp (Finset.mem_sdiff.mp hexterior).1, check, hcouples, hsupport⟩
  exact (Finset.mem_sdiff.mp hexterior).2 hexternal

/--
Any local projector touching neither source interior nor source exterior is
supported on the full source boundary.  This is the support classification used
to form the middle `BC` projector product in the BPT proof.
-/
theorem support_subset_boundary_of_not_mem_interior_not_mem_exterior
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) (check : kappa)
    (hinterior : ∀ site, site ∈ M.support check → site ∉ M.interior region)
    (hexterior : ∀ site, site ∈ M.support check → site ∉ M.exterior region) :
    M.support check ⊆ M.boundary region := by
  intro site hsupport
  by_cases hregion : site ∈ region
  · have hsplit : site ∈ M.interior region ∪ M.internalBoundary region := by
      rw [← M.region_eq_interior_union_internalBoundary region]
      exact hregion
    rcases Finset.mem_union.mp hsplit with hinside | hboundary
    · exact False.elim (hinterior site hsupport hinside)
    · exact (Finset.mem_inter.mp hboundary).1
  · have hcomplement : site ∈ regionᶜ := Finset.mem_compl.mpr hregion
    have hsplit : site ∈ M.externalBoundary region ∪ M.exterior region := by
      rw [← M.complement_eq_externalBoundary_union_exterior region]
      exact hcomplement
    rcases Finset.mem_union.mp hsplit with hboundary | houtside
    · exact (Finset.mem_sdiff.mp hboundary).1
    · exact False.elim (hexterior site hsupport houtside)

/-- Checks whose actual support meets the source interior `A`. -/
noncomputable def interiorChecks (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Finset kappa :=
  Finset.univ.filter fun check => (M.support check ∩ M.interior region).Nonempty

/-- Checks whose actual support meets the source exterior `D`. -/
noncomputable def exteriorChecks (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Finset kappa :=
  Finset.univ.filter fun check => (M.support check ∩ M.exterior region).Nonempty

/-- Remaining checks, which are supported on the source boundary `B union C`. -/
noncomputable def boundaryChecks (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Finset kappa :=
  Finset.univ \ (M.interiorChecks region ∪ M.exteriorChecks region)

/-- The `A`-touching and `D`-touching check families are disjoint. -/
theorem disjoint_interiorChecks_exteriorChecks
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Disjoint (M.interiorChecks region) (M.exteriorChecks region) := by
  rw [Finset.disjoint_left]
  intro check hinterior hexterior
  rcases (Finset.mem_filter.mp hinterior).2 with ⟨inside, hinside⟩
  rcases (Finset.mem_filter.mp hexterior).2 with ⟨outside, houtside⟩
  have hsuppInside : inside ∈ M.support check := (Finset.mem_inter.mp hinside).1
  have hinteriorInside : inside ∈ M.interior region := (Finset.mem_inter.mp hinside).2
  have hsuppOutside : outside ∈ M.support check := (Finset.mem_inter.mp houtside).1
  have hexteriorOutside : outside ∈ M.exterior region := (Finset.mem_inter.mp houtside).2
  have hsubset := M.support_subset_region_of_mem_interior region check hsuppInside hinteriorInside
  exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hexteriorOutside).1)
    (hsubset hsuppOutside)

/-- Every `A`-touching check acts only on the source `AB` side. -/
theorem support_subset_region_of_mem_interiorChecks
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {check : kappa} (hcheck : check ∈ M.interiorChecks region) :
    M.support check ⊆ region := by
  rcases (Finset.mem_filter.mp hcheck).2 with ⟨site, hsite⟩
  exact M.support_subset_region_of_mem_interior region check
    (Finset.mem_inter.mp hsite).1 (Finset.mem_inter.mp hsite).2

/-- Every `D`-touching check acts only on the source `CD` side. -/
theorem support_subset_complement_of_mem_exteriorChecks
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {check : kappa} (hcheck : check ∈ M.exteriorChecks region) :
    M.support check ⊆ regionᶜ := by
  rcases (Finset.mem_filter.mp hcheck).2 with ⟨site, hsite⟩
  exact M.support_subset_complement_of_mem_exterior region check
    (Finset.mem_inter.mp hsite).1 (Finset.mem_inter.mp hsite).2

/-- Every remaining check is genuinely supported on the source boundary `BC`. -/
theorem support_subset_boundary_of_mem_boundaryChecks
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {check : kappa} (hcheck : check ∈ M.boundaryChecks region) :
    M.support check ⊆ M.boundary region := by
  have hnotInterior : check ∉ M.interiorChecks region :=
    fun hmem => (Finset.mem_sdiff.mp hcheck).2 (Finset.mem_union_left _ hmem)
  have hnotExterior : check ∉ M.exteriorChecks region :=
    fun hmem => (Finset.mem_sdiff.mp hcheck).2 (Finset.mem_union_right _ hmem)
  apply M.support_subset_boundary_of_not_mem_interior_not_mem_exterior region check
  · intro site hsupport hinterior
    apply hnotInterior
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨site,
      Finset.mem_inter.mpr ⟨hsupport, hinterior⟩⟩⟩
  · intro site hsupport hexterior
    apply hnotExterior
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨site,
      Finset.mem_inter.mpr ⟨hsupport, hexterior⟩⟩⟩

/-- The three source check families partition the full finite projector family. -/
theorem union_interior_boundary_exteriorChecks_eq_univ
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.interiorChecks region ∪ M.boundaryChecks region) ∪ M.exteriorChecks region = Finset.univ := by
  ext check
  constructor
  · intro _
    exact Finset.mem_univ _
  · intro _
    by_cases hinterior : check ∈ M.interiorChecks region
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hinterior)
    · by_cases hexterior : check ∈ M.exteriorChecks region
      · exact Finset.mem_union_right _ hexterior
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
            simp [hinterior, hexterior]⟩))

/-- Pairwise commutation restricted to any finite subfamily of BPT checks. -/
theorem projectorPairwiseCommute (M : BPTCommutingProjectorModel L kappa)
    (checks : Finset kappa) :
    (checks : Set kappa).Pairwise (Function.onFun Commute M.projector) := by
  intro check _ other _ _
  exact M.projector_commute check other

/-- The finite product of an explicitly selected subfamily of actual projectors. -/
noncomputable def projectorProductOn (M : BPTCommutingProjectorModel L kappa)
    (checks : Finset kappa) : Semantics.Operator L.Register :=
  checks.noncommProd M.projector (M.projectorPairwiseCommute checks)

/-- A finite selected product of commuting self-adjoint BPT projectors is self-adjoint. -/
theorem projectorProductOn_adjoint_eq_self (M : BPTCommutingProjectorModel L kappa)
    (checks : Finset kappa) :
    LinearMap.adjoint (M.projectorProductOn checks) = M.projectorProductOn checks := by
  classical
  induction checks using Finset.induction_on with
  | empty =>
      simp [projectorProductOn, Finset.noncommProd_empty]
  | insert check checks hnotmem induction =>
      have hrest : (checks : Set kappa).Pairwise (Function.onFun Commute M.projector) :=
        (M.projectorPairwiseCommute (insert check checks)).mono
          (fun _ hmem => Finset.mem_insert_of_mem hmem)
      let productRest := checks.noncommProd M.projector hrest
      have hfactor : (insert check checks).noncommProd M.projector
          (M.projectorPairwiseCommute (insert check checks)) =
          M.projector check * productRest := by
        rw [Finset.noncommProd_insert_of_notMem checks check M.projector
          (M.projectorPairwiseCommute (insert check checks)) hnotmem]
      have hcommRest : Commute (M.projector check) productRest := by
        dsimp [productRest]
        exact Finset.noncommProd_commute checks M.projector hrest (M.projector check)
          (fun other _ => M.projector_commute check other)
      change LinearMap.adjoint
          ((insert check checks).noncommProd M.projector
            (M.projectorPairwiseCommute (insert check checks))) = _
      calc
        LinearMap.adjoint ((insert check checks).noncommProd M.projector
            (M.projectorPairwiseCommute (insert check checks))) =
            LinearMap.adjoint (M.projector check * productRest) := by rw [hfactor]
        _ = LinearMap.adjoint productRest * LinearMap.adjoint (M.projector check) := by
          rw [Module.End.mul_eq_comp, LinearMap.adjoint_comp, ← Module.End.mul_eq_comp]
        _ = productRest * M.projector check := by
          rw [show LinearMap.adjoint productRest = productRest by
            dsimp [productRest]
            simpa [projectorProductOn] using induction, M.projector_adjoint_eq_self]
        _ = M.projector check * productRest := hcommRest.eq.symm
        _ = (insert check checks).noncommProd M.projector
            (M.projectorPairwiseCommute (insert check checks)) := hfactor.symm

/-- A finite selected product of commuting idempotent BPT projectors is idempotent. -/
theorem projectorProductOn_idempotent (M : BPTCommutingProjectorModel L kappa)
    (checks : Finset kappa) :
    (M.projectorProductOn checks).comp (M.projectorProductOn checks) =
      M.projectorProductOn checks := by
  classical
  induction checks using Finset.induction_on with
  | empty =>
      change (1 : Semantics.Operator L.Register).comp 1 = 1
      ext x
      rfl
  | insert check checks hnotmem induction =>
      have hrest : (checks : Set kappa).Pairwise (Function.onFun Commute M.projector) :=
        (M.projectorPairwiseCommute (insert check checks)).mono
          (fun _ hmem => Finset.mem_insert_of_mem hmem)
      let productRest := checks.noncommProd M.projector hrest
      have hfactor : (insert check checks).noncommProd M.projector
          (M.projectorPairwiseCommute (insert check checks)) =
          M.projector check * productRest := by
        rw [Finset.noncommProd_insert_of_notMem checks check M.projector
          (M.projectorPairwiseCommute (insert check checks)) hnotmem]
      have hcommRest : Commute (M.projector check) productRest := by
        dsimp [productRest]
        exact Finset.noncommProd_commute checks M.projector hrest (M.projector check)
          (fun other _ => M.projector_commute check other)
      have hidempotentRest : productRest * productRest = productRest := by
        dsimp [productRest]
        simpa [projectorProductOn, Module.End.mul_eq_comp] using induction
      change ((insert check checks).noncommProd M.projector
          (M.projectorPairwiseCommute (insert check checks))) *
          ((insert check checks).noncommProd M.projector
            (M.projectorPairwiseCommute (insert check checks))) = _
      calc
        ((insert check checks).noncommProd M.projector
            (M.projectorPairwiseCommute (insert check checks))) *
            ((insert check checks).noncommProd M.projector
              (M.projectorPairwiseCommute (insert check checks))) =
            (M.projector check * productRest) * (M.projector check * productRest) := by
              rw [hfactor]
        _ = M.projector check * ((productRest * M.projector check) * productRest) := by
              simp only [mul_assoc]
        _ = M.projector check * ((M.projector check * productRest) * productRest) := by
              rw [hcommRest.eq]
        _ = (M.projector check * M.projector check) * (productRest * productRest) := by
              simp only [mul_assoc]
        _ = M.projector check * productRest := by
              rw [show M.projector check * M.projector check = M.projector check by
                simpa [Module.End.mul_eq_comp] using M.projector_is_idempotent check,
                hidempotentRest]
        _ = (insert check checks).noncommProd M.projector
            (M.projectorPairwiseCommute (insert check checks)) := hfactor.symm

/-- Grouped source products remain honest finite-dimensional orthogonal projectors. -/
theorem projectorProductOn_isSymmetricProjection (M : BPTCommutingProjectorModel L kappa)
    (checks : Finset kappa) :
    (M.projectorProductOn checks).IsSymmetricProjection := by
  refine ⟨?_, ?_⟩
  · change M.projectorProductOn checks * M.projectorProductOn checks =
      M.projectorProductOn checks
    simpa [Module.End.mul_eq_comp] using M.projectorProductOn_idempotent checks
  · exact (LinearMap.isSymmetric_iff_isSelfAdjoint (M.projectorProductOn checks)).mpr
      (M.projectorProductOn_adjoint_eq_self checks)

/-- Products of any two selected BPT check families commute. -/
theorem projectorProductOn_commute (M : BPTCommutingProjectorModel L kappa)
    (left right : Finset kappa) :
    Commute (M.projectorProductOn left) (M.projectorProductOn right) := by
  let rightProduct := M.projectorProductOn right
  have hright : ∀ check ∈ left, Commute rightProduct (M.projector check) := by
    intro check _
    dsimp [rightProduct, projectorProductOn]
    exact (Finset.noncommProd_commute right M.projector
      (M.projectorPairwiseCommute right) (M.projector check)
      (fun other _ => M.projector_commute check other)).symm
  dsimp [projectorProductOn]
  exact (Finset.noncommProd_commute left M.projector
    (M.projectorPairwiseCommute left) rightProduct hright).symm

/--
Selected-register support is closed under composition: after both operators are
written as identity extensions through the same coordinate factorization, their
product is the extension of the product of their local representatives.  This
turns a finite family of local check supports into locality of its grouped
projector product.
-/
theorem operatorSupportedOnRegister_comp
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {A B : Semantics.Operator L.Register}
    (hA : (M.regionSubsystem region).OperatorSupportedOnRegister A)
    (hB : (M.regionSubsystem region).OperatorSupportedOnRegister B) :
    (M.regionSubsystem region).OperatorSupportedOnRegister (A.comp B) := by
  rcases hA with ⟨localA, hlocalA⟩
  rcases hB with ⟨localB, hlocalB⟩
  refine ⟨localA.comp localB, ?_⟩
  rw [← localExtension_comp, hlocalA, hlocalB]

/--
An explicitly selected finite product remains supported on a region whenever
each factor is supported there.  This is the finite-product locality closure
used for the source `Pi_AB`, `Pi_BC`, and `Pi_CD` grouped products.
-/
theorem projectorProductOn_supportedOnRegister
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (checks : Finset kappa)
    (hsupported : ∀ check, check ∈ checks →
      (M.regionSubsystem region).OperatorSupportedOnRegister (M.projector check)) :
    (M.regionSubsystem region).OperatorSupportedOnRegister
      (M.projectorProductOn checks) := by
  classical
  induction checks using Finset.induction_on with
  | empty =>
      refine ⟨1, ?_⟩
      change (M.regionSubsystem region).registerFactorization.symm.conjOperator
        (TensorProduct.map (1 : Semantics.Operator (M.regionSubsystem region).selectedSystem)
          (1 : Semantics.Operator (M.regionSubsystem region).complementSystem)) = 1
      rw [TensorProduct.map_one]
      exact (M.regionSubsystem region).registerFactorization.symm.conjOperator_one
  | insert check checks hnotmem induction =>
      have hrest : (checks : Set kappa).Pairwise (Function.onFun Commute M.projector) :=
        (M.projectorPairwiseCommute (insert check checks)).mono
          (fun _ hmem => Finset.mem_insert_of_mem hmem)
      let productRest := checks.noncommProd M.projector hrest
      have hfactor : (insert check checks).noncommProd M.projector
          (M.projectorPairwiseCommute (insert check checks)) =
          M.projector check * productRest := by
        rw [Finset.noncommProd_insert_of_notMem checks check M.projector
          (M.projectorPairwiseCommute (insert check checks)) hnotmem]
      have hcheck :
          (M.regionSubsystem region).OperatorSupportedOnRegister (M.projector check) :=
        hsupported check (Finset.mem_insert_self check checks)
      have hproductRest :
          (M.regionSubsystem region).OperatorSupportedOnRegister productRest := by
        dsimp [productRest]
        simpa [projectorProductOn] using induction
          (fun other hother => hsupported other (Finset.mem_insert_of_mem hother))
      change (M.regionSubsystem region).OperatorSupportedOnRegister
        ((insert check checks).noncommProd M.projector
          (M.projectorPairwiseCommute (insert check checks)))
      rw [hfactor]
      exact M.operatorSupportedOnRegister_comp region hcheck hproductRest

/-- The `AB` source check family is disjoint from the middle `BC` family. -/
theorem disjoint_interiorChecks_boundaryChecks
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Disjoint (M.interiorChecks region) (M.boundaryChecks region) := by
  rw [Finset.disjoint_left]
  intro check hinterior hboundary
  exact (Finset.mem_sdiff.mp hboundary).2 (Finset.mem_union_left _ hinterior)

/-- The combined `AB` and `BC` families are disjoint from the `CD` family. -/
theorem disjoint_interiorBoundaryChecks_exteriorChecks
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Disjoint (M.interiorChecks region ∪ M.boundaryChecks region) (M.exteriorChecks region) := by
  rw [Finset.disjoint_left]
  intro check hleft hexterior
  rcases Finset.mem_union.mp hleft with hinterior | hboundary
  · exact (Finset.disjoint_left.mp (M.disjoint_interiorChecks_exteriorChecks region))
      hinterior hexterior
  · exact (Finset.mem_sdiff.mp hboundary).2 (Finset.mem_union_right _ hexterior)

/--
The full code projector is the source product `Pi_AB Pi_BC Pi_CD`.  The three
products are regrouped only after their check families have been proved
disjoint and after pairwise commutation has been retained explicitly.
-/
theorem projectorProduct_eq_source_three_products
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.projectorProduct =
      (M.projectorProductOn (M.interiorChecks region) *
        M.projectorProductOn (M.boundaryChecks region)) *
      M.projectorProductOn (M.exteriorChecks region) := by
  classical
  let interior := M.interiorChecks region
  let boundary := M.boundaryChecks region
  let exterior := M.exteriorChecks region
  have hwhole : (interior ∪ boundary) ∪ exterior = Finset.univ := by
    simpa only [interior, boundary, exterior] using
      M.union_interior_boundary_exteriorChecks_eq_univ region
  have hleft : Disjoint interior boundary := by
    simpa only [interior, boundary] using M.disjoint_interiorChecks_boundaryChecks region
  have hright : Disjoint (interior ∪ boundary) exterior := by
    simpa only [interior, boundary, exterior] using
      M.disjoint_interiorBoundaryChecks_exteriorChecks region
  change Finset.univ.noncommProd M.projector (M.projectorPairwiseCommute Finset.univ) = _
  rw [← hwhole]
  rw [Finset.noncommProd_union_of_disjoint hright M.projector
    (M.projectorPairwiseCommute ((interior ∪ boundary) ∪ exterior))]
  rw [Finset.noncommProd_union_of_disjoint hleft M.projector
    (M.projectorPairwiseCommute (interior ∪ boundary))]
  simp only [projectorProductOn, interior, boundary, exterior]

/-- The source `Pi_AB`: product of all projectors touching the interior `A`. -/
noncomputable def projectorAB (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Semantics.Operator L.Register :=
  M.projectorProductOn (M.interiorChecks region)

/-- The source `Pi_BC`: product of all remaining boundary-supported projectors. -/
noncomputable def projectorBC (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Semantics.Operator L.Register :=
  M.projectorProductOn (M.boundaryChecks region)

/-- The source `Pi_CD`: product of all projectors touching the exterior `D`. -/
noncomputable def projectorCD (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Semantics.Operator L.Register :=
  M.projectorProductOn (M.exteriorChecks region)

/-- The grouped `Pi_AB` product acts only on the source region `M = AB`. -/
theorem projectorAB_supportedOnRegister_region
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem region).OperatorSupportedOnRegister (M.projectorAB region) := by
  apply M.projectorProductOn_supportedOnRegister region (M.interiorChecks region)
  intro check hcheck
  exact M.projector_supportedOnRegister_of_support_subset check region
    (M.support_subset_region_of_mem_interiorChecks region hcheck)

/-- The grouped `Pi_BC` product acts only on the source boundary `B union C`. -/
theorem projectorBC_supportedOnRegister_boundary
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem (M.boundary region)).OperatorSupportedOnRegister (M.projectorBC region) := by
  apply M.projectorProductOn_supportedOnRegister (M.boundary region) (M.boundaryChecks region)
  intro check hcheck
  exact M.projector_supportedOnRegister_of_support_subset check (M.boundary region)
    (M.support_subset_boundary_of_mem_boundaryChecks region hcheck)

/-- The grouped `Pi_CD` product acts only on the complement `CD` of `M`. -/
theorem projectorCD_supportedOnRegister_complement
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem regionᶜ).OperatorSupportedOnRegister (M.projectorCD region) := by
  apply M.projectorProductOn_supportedOnRegister regionᶜ (M.exteriorChecks region)
  intro check hcheck
  exact M.projector_supportedOnRegister_of_support_subset check regionᶜ
    (M.support_subset_complement_of_mem_exteriorChecks region hcheck)

/-- The chosen concrete `AB`-local representative of the first source product. -/
noncomputable def projectorABLocal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.Operator (M.regionSubsystem region).selectedSystem :=
  Classical.choose (M.projectorAB_supportedOnRegister_region region)

/-- The chosen `AB` representative extends back to the actual source product. -/
theorem extendLocalToRegister_projectorABLocal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem region).extendLocalToRegister (M.projectorABLocal region) =
      M.projectorAB region :=
  Classical.choose_spec (M.projectorAB_supportedOnRegister_region region)

/-- The chosen concrete `BC`-local representative of the middle source product. -/
noncomputable def projectorBCLocal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.Operator (M.regionSubsystem (M.boundary region)).selectedSystem :=
  Classical.choose (M.projectorBC_supportedOnRegister_boundary region)

/-- The chosen `BC` representative extends back to the actual source product. -/
theorem extendLocalToRegister_projectorBCLocal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem (M.boundary region)).extendLocalToRegister (M.projectorBCLocal region) =
      M.projectorBC region :=
  Classical.choose_spec (M.projectorBC_supportedOnRegister_boundary region)

/-- The chosen concrete `CD`-local representative of the third source product. -/
noncomputable def projectorCDLocal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.Operator (M.regionSubsystem regionᶜ).selectedSystem :=
  Classical.choose (M.projectorCD_supportedOnRegister_complement region)

/-- The chosen `CD` representative extends back to the actual source product. -/
theorem extendLocalToRegister_projectorCDLocal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem regionᶜ).extendLocalToRegister (M.projectorCDLocal region) =
      M.projectorCD region :=
  Classical.choose_spec (M.projectorCD_supportedOnRegister_complement region)

/--
The third source product in the concrete `C tensor D` coordinates.  This is
obtained only from its complement-local representative and the fixed
coordinate transport, never by defining it as a conjugate of the full global
projector.
-/
noncomputable def fourFactorProjectorCDLocal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.Operator (Semantics.CompositeSystem
      ((M.regionSubsystem region).additionalRetainedSystem
        (M.regionSubsystem (region ∪ M.externalBoundary region)))
      (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem) :=
  (M.fourFactorCDCoordinateTransport region).conjOperator (M.projectorCDLocal region)

/--
The middle source product in the concrete `B tensor C` coordinates.  As for
the `CD` representative, this is transported only from its independently
chosen boundary-local representative through a fixed coordinate unitary.
-/
noncomputable def fourFactorProjectorBCLocal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.Operator (Semantics.CompositeSystem
      (M.fourFactorB region) (M.fourFactorC region)) :=
  (M.boundarySelectedToBCTransport region).conjOperator (M.projectorBCLocal region)

/-- The `AB` source product in the `A tensor B` coordinates of the common transport. -/
noncomputable def fourFactorProjectorABLocal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.Operator (Semantics.CompositeSystem
      (M.fourFactorA region) (M.fourFactorB region)) := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  exact (A.selectedFactorization AB hAAB).conjOperator (M.projectorABLocal region)

/--
The first source product has the exact `AB` support equation on the common
four-factor transport.  This realizes the `Pi_AB` side of both overlapping
commuting-projector cuts without replacing it by a global spectral sector.
-/
theorem fourFactorTransport_conj_projectorAB
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.fourFactorTransport region).conjOperator (M.projectorAB region) =
      M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  rw [← M.extendLocalToRegister_projectorABLocal region]
  dsimp [fourFactorTransport]
  rw [composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator]
  rw [nestedFactorizationLeft_conj_extendLocalToRegister AB ABC hABABC]
  rw [unitaryRTensor_conj_tensorMap_left]
  rfl

/--
The third source product has the exact `CD` support equation on the common
four-factor transport.  Together with the `AB` equation, this is the actual
overlapping-locality input to the BV03 interaction-algebra decomposition.
-/
theorem fourFactorTransport_conj_projectorCD
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.fourFactorTransport region).conjOperator (M.projectorCD region) =
      M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) := by
  rw [M.fourFactorTransport_eq_fourFactorTransportFromRegion]
  rw [← M.extendLocalToRegister_projectorCDLocal region]
  rw [M.extendLocalToRegister_complement_eq_extendComplementToRegister region]
  rw [M.fourFactorTransportFromRegion_conj_extendComplementToRegister]
  rw [fourFactorProjectorCDLocal, fourFactorCDCoordinateTransport,
    composeUnitaryTransport_conjOperator]

/--
The middle source product has the exact `BC` support equation on the common
four-factor transport.  This is the second overlapping-projector input for
the BV03 tensor-block theorem, not a substitute joint spectral decomposition.
-/
theorem fourFactorTransport_conj_projectorBC
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.fourFactorTransport region).conjOperator (M.projectorBC region) =
      M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) := by
  rw [← M.boundaryGlobalToFourFactorTransport_eq_fourFactorTransport region]
  rw [← M.extendLocalToRegister_projectorBCLocal region]
  rw [M.boundaryGlobalToFourFactorTransport_conj_extendLocalToRegister]
  rfl

/--
Products supported on two regions are supported on their union.  Each factor
is lifted through the proved selected-coordinate inclusion before the
same-region composition closure is applied.
-/
theorem operatorSupportedOnRegister_mul_union
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    {A B : Semantics.Operator L.Register}
    (hA : (M.regionSubsystem left).OperatorSupportedOnRegister A)
    (hB : (M.regionSubsystem right).OperatorSupportedOnRegister B) :
    (M.regionSubsystem (left ∪ right)).OperatorSupportedOnRegister (A * B) := by
  have hleft : (M.regionSubsystem (left ∪ right)).OperatorSupportedOnRegister A := by
    apply operatorSupportedOnRegister_of_subset (M.regionSubsystem left)
      (M.regionSubsystem (left ∪ right))
    · simp [BPTCommutingProjectorModel.regionSubsystem]
    · exact hA
  have hright : (M.regionSubsystem (left ∪ right)).OperatorSupportedOnRegister B := by
    apply operatorSupportedOnRegister_of_subset (M.regionSubsystem right)
      (M.regionSubsystem (left ∪ right))
    · simp [BPTCommutingProjectorModel.regionSubsystem]
    · exact hB
  exact M.operatorSupportedOnRegister_comp (left ∪ right) hleft hright

/--
The first source product `Pi_AB Pi_BC` acts only on `M union partial M`, the
`MC` side of the first commuting-projector decomposition in the BPT proof.
-/
theorem projectorAB_mul_BC_supportedOnRegister
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem (region ∪ M.boundary region)).OperatorSupportedOnRegister
      (M.projectorAB region * M.projectorBC region) :=
  M.operatorSupportedOnRegister_mul_union region (M.boundary region)
    (M.projectorAB_supportedOnRegister_region region)
    (M.projectorBC_supportedOnRegister_boundary region)

/--
The second source product `Pi_BC Pi_CD` acts only on `partial M union bar M`,
the `B bar(M)` side of the second BPT commuting-projector decomposition.
-/
theorem projectorBC_mul_CD_supportedOnRegister
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem (M.boundary region ∪ regionᶜ)).OperatorSupportedOnRegister
      (M.projectorBC region * M.projectorCD region) :=
  M.operatorSupportedOnRegister_mul_union (M.boundary region) regionᶜ
    (M.projectorBC_supportedOnRegister_boundary region)
    (M.projectorCD_supportedOnRegister_complement region)

/--
Composing units supported on two site regions is supported on their union.
This is the support calculation for the source choice
`W_{B''C'} U_B^dagger U_C^dagger`: every factor is confined to a piece of
the original boundary, hence so is their composition.
-/
theorem unitarySupportedOn_then_union
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    {U V : Semantics.UnitaryTransport L.Register L.Register}
    (hU : M.UnitarySupportedOn left U) (hV : M.UnitarySupportedOn right V) :
    M.UnitarySupportedOn (left ∪ right) (thenUnitary U V) := by
  have h := M.operatorSupportedOnRegister_mul_union right left hV hU
  rw [Finset.union_comm] at h
  exact h

/-- Each source grouped product is an actual orthogonal projector. -/
theorem projectorAB_isSymmetricProjection (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : (M.projectorAB region).IsSymmetricProjection :=
  M.projectorProductOn_isSymmetricProjection (M.interiorChecks region)

/-- Each source grouped product is an actual orthogonal projector. -/
theorem projectorBC_isSymmetricProjection (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : (M.projectorBC region).IsSymmetricProjection :=
  M.projectorProductOn_isSymmetricProjection (M.boundaryChecks region)

/-- Each source grouped product is an actual orthogonal projector. -/
theorem projectorCD_isSymmetricProjection (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : (M.projectorCD region).IsSymmetricProjection :=
  M.projectorProductOn_isSymmetricProjection (M.exteriorChecks region)

/-- The three source grouped projectors commute pairwise. -/
theorem projectorAB_commute_projectorBC (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Commute (M.projectorAB region) (M.projectorBC region) :=
  M.projectorProductOn_commute (M.interiorChecks region) (M.boundaryChecks region)

/-- The three source grouped projectors commute pairwise. -/
theorem projectorAB_commute_projectorCD (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Commute (M.projectorAB region) (M.projectorCD region) :=
  M.projectorProductOn_commute (M.interiorChecks region) (M.exteriorChecks region)

/-- The three source grouped projectors commute pairwise. -/
theorem projectorBC_commute_projectorCD (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Commute (M.projectorBC region) (M.projectorCD region) :=
  M.projectorProductOn_commute (M.boundaryChecks region) (M.exteriorChecks region)

/--
The product of two commuting finite-dimensional orthogonal projectors is again
an orthogonal projector.  This closes the elementary projector algebra needed
to apply the joint spectral theorem to BPT's two source cuts.
-/
theorem isSymmetricProjection_mul_of_commute {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] {P Q : Semantics.Operator H}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    (hcommute : Commute P Q) : (P * Q).IsSymmetricProjection := by
  constructor
  · calc
      (P * Q) * (P * Q) = P * ((Q * P) * Q) := by simp only [mul_assoc]
      _ = P * ((P * Q) * Q) := by rw [hcommute.eq]
      _ = (P * P) * (Q * Q) := by simp only [mul_assoc]
      _ = P * Q := by rw [hP.isIdempotentElem, hQ.isIdempotentElem]
  · have hadjointP := hP.isSymmetric.adjoint_eq
    have hadjointQ := hQ.isSymmetric.adjoint_eq
    apply (LinearMap.isSymmetric_iff_isSelfAdjoint (P * Q)).mpr
    apply LinearMap.isSelfAdjoint_iff'.mpr
    calc
      LinearMap.adjoint (P * Q) = LinearMap.adjoint Q * LinearMap.adjoint P := by
        rw [Module.End.mul_eq_comp, LinearMap.adjoint_comp, ← Module.End.mul_eq_comp]
      _ = Q * P := by rw [hadjointQ, hadjointP]
      _ = P * Q := hcommute.eq.symm

/--
If a local projector `Z` commutes with the code projector, then its code
sector `Pi Z` is either zero or the whole code whenever the local subsystem
has no information.  Unlike a naive local-sector statement, the hypothesis is
locality of `Z` itself: `Pi Z` is generally global.  This is precisely the
source step that collapses the central BV03 boundary sectors after the first
and second interaction-algebra decompositions.
-/
theorem local_commutingProjection_codeSector_eq_zero_or_codeProjector
    (S : Semantics.QuditSubsystem L.localDimension) (C : Semantics.QuantumCode L.Register)
    {Z : Semantics.Operator L.Register}
    (hInformation : Semantics.QuditSubsystem.NoInformationOn C S)
    (hLocal : S.OperatorSupportedOnRegister Z)
    (hProjection : Z.IsSymmetricProjection)
    (hCommute : Commute C.projector Z) :
    C.projector * Z = 0 ∨ C.projector * Z = C.projector := by
  rcases hLocal with ⟨localZ, hlocalZ⟩
  have hAll := (S.noInformationOn_iff_allLocalScalarCompression C).mp hInformation
  rcases hAll localZ with ⟨scalar, hscalar⟩
  have hProjector : C.projector.IsSymmetricProjection := by
    constructor
    · exact C.projector_idempotent
    · exact C.projector_isSymmetric
  have hsectorScalar : C.projector * Z = scalar • C.projector := by
    calc
      C.projector * Z = (C.projector * C.projector) * Z := by
        rw [show C.projector * C.projector = C.projector by
          simpa [Module.End.mul_eq_comp] using C.projector_idempotent]
      _ = C.projector * (C.projector * Z) := by rw [mul_assoc]
      _ = C.projector * (Z * C.projector) := by rw [hCommute.eq]
      _ = C.projector.comp (Z.comp C.projector) := rfl
      _ = C.projector.comp ((S.extendLocalToRegister localZ).comp C.projector) := by
        rw [hlocalZ]
      _ = scalar • C.projector := hscalar
  have hsectorProjection : (C.projector * Z).IsSymmetricProjection :=
    isSymmetricProjection_mul_of_commute hProjector hProjection hCommute
  by_cases hcode : C.projector = 0
  · left
    rw [hcode, zero_mul]
  · have hsectorIdem : (C.projector * Z) * (C.projector * Z) = C.projector * Z :=
      hsectorProjection.isIdempotentElem
    have hscalarIdem : scalar * scalar = scalar := by
      apply smul_left_injective Complex hcode
      calc
        (scalar * scalar) • C.projector =
            (scalar • C.projector) * (scalar • C.projector) := by
              rw [smul_mul_smul,
                show C.projector * C.projector = C.projector by
                  simpa [Module.End.mul_eq_comp] using C.projector_idempotent]
        _ = (C.projector * Z) * (C.projector * Z) := by rw [hsectorScalar]
        _ = C.projector * Z := hsectorIdem
        _ = scalar • C.projector := hsectorScalar
    have hfactor : scalar * (scalar - 1) = 0 := by
      calc
        scalar * (scalar - 1) = scalar * scalar - scalar := by ring
        _ = 0 := sub_eq_zero.mpr hscalarIdem
    rcases mul_eq_zero.mp hfactor with hzero | hone
    · left
      rw [hsectorScalar, hzero, zero_smul]
    · right
      rw [hsectorScalar, sub_eq_zero.mp hone, one_smul]

/-- The `MC` source grouped projector is an actual orthogonal projector. -/
theorem projectorAB_mul_BC_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.projectorAB region * M.projectorBC region).IsSymmetricProjection :=
  isSymmetricProjection_mul_of_commute
    (M.projectorAB_isSymmetricProjection region)
    (M.projectorBC_isSymmetricProjection region)
    (M.projectorAB_commute_projectorBC region)

/-- The `B bar(M)` source grouped projector is an actual orthogonal projector. -/
theorem projectorBC_mul_CD_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.projectorBC region * M.projectorCD region).IsSymmetricProjection :=
  isSymmetricProjection_mul_of_commute
    (M.projectorBC_isSymmetricProjection region)
    (M.projectorCD_isSymmetricProjection region)
    (M.projectorBC_commute_projectorCD region)

/-- The `MC` and `CD` source projectors commute across the first BV03 cut. -/
theorem projectorAB_mul_BC_commute_projectorCD
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Commute (M.projectorAB region * M.projectorBC region) (M.projectorCD region) := by
  change (M.projectorAB region * M.projectorBC region) * M.projectorCD region =
    M.projectorCD region * (M.projectorAB region * M.projectorBC region)
  calc
    (M.projectorAB region * M.projectorBC region) * M.projectorCD region =
        M.projectorAB region * (M.projectorBC region * M.projectorCD region) := by
          rw [mul_assoc]
    _ = M.projectorAB region * (M.projectorCD region * M.projectorBC region) := by
          rw [(M.projectorBC_commute_projectorCD region).eq]
    _ = (M.projectorAB region * M.projectorCD region) * M.projectorBC region := by
          rw [← mul_assoc]
    _ = (M.projectorCD region * M.projectorAB region) * M.projectorBC region := by
          rw [(M.projectorAB_commute_projectorCD region).eq]
    _ = M.projectorCD region * (M.projectorAB region * M.projectorBC region) := by
          rw [mul_assoc]

/-- The `AB` and `B bar(M)` source projectors commute across the second BV03 cut. -/
theorem projectorAB_commute_projectorBC_mul_CD
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Commute (M.projectorAB region) (M.projectorBC region * M.projectorCD region) := by
  change M.projectorAB region * (M.projectorBC region * M.projectorCD region) =
    (M.projectorBC region * M.projectorCD region) * M.projectorAB region
  calc
    M.projectorAB region * (M.projectorBC region * M.projectorCD region) =
        (M.projectorAB region * M.projectorBC region) * M.projectorCD region := by
          rw [← mul_assoc]
    _ = (M.projectorBC region * M.projectorAB region) * M.projectorCD region := by
          rw [(M.projectorAB_commute_projectorBC region).eq]
    _ = M.projectorBC region * (M.projectorAB region * M.projectorCD region) := by
          rw [mul_assoc]
    _ = M.projectorBC region * (M.projectorCD region * M.projectorAB region) := by
          rw [(M.projectorAB_commute_projectorCD region).eq]
    _ = (M.projectorBC region * M.projectorCD region) * M.projectorAB region := by
          rw [← mul_assoc]

/-- The actual code projector is exactly the source `Pi_AB Pi_BC Pi_CD` product. -/
theorem fullCodeProjector_eq_projectorAB_mul_BC_mul_CD
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.fullCodeProjector =
      (M.projectorAB region * M.projectorBC region) * M.projectorCD region := by
  rw [← M.projectorProduct_eq_fullCodeProjector]
  simpa only [projectorAB, projectorBC, projectorCD] using
    M.projectorProduct_eq_source_three_products region

/--
The canonical source-coordinate transport carries the full BPT code projector
to the literal product of its three source-local factors on `A B C D`.  This
is the single recombination point between the concrete geometry/support work
and the two BV03 overlapping-projector decompositions: the first cut groups
`AB` with `BC`, and the second groups `BC` with `CD`.
-/
theorem fourFactor_codeProjector_eq_source_products
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.fourFactorTransport region).conjOperator M.fullCodeProjector =
      (M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) *
        M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region)) *
        M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) := by
  rw [M.fullCodeProjector_eq_projectorAB_mul_BC_mul_CD]
  calc
    (M.fourFactorTransport region).conjOperator
        ((M.projectorAB region * M.projectorBC region) * M.projectorCD region) =
        (M.fourFactorTransport region).conjOperator
            (M.projectorAB region * M.projectorBC region) *
          (M.fourFactorTransport region).conjOperator (M.projectorCD region) := by
      exact Semantics.UnitaryTransport.conjOperator_mul
        (M.fourFactorTransport region)
        (M.projectorAB region * M.projectorBC region) (M.projectorCD region)
    _ = ((M.fourFactorTransport region).conjOperator (M.projectorAB region) *
          (M.fourFactorTransport region).conjOperator (M.projectorBC region)) *
          (M.fourFactorTransport region).conjOperator (M.projectorCD region) := by
      exact congrArg
        (fun product => product *
          (M.fourFactorTransport region).conjOperator (M.projectorCD region))
        (Semantics.UnitaryTransport.conjOperator_mul
          (M.fourFactorTransport region) (M.projectorAB region) (M.projectorBC region))
    _ = (M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) *
          M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region)) *
          M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) := by
      have hAB := M.fourFactorTransport_conj_projectorAB region
      have hBC := M.fourFactorTransport_conj_projectorBC region
      have hCD := M.fourFactorTransport_conj_projectorCD region
      exact congrArg₂ (fun left right => left * right)
        (congrArg₂ (fun left right => left * right) hAB hBC) hCD

/--
The first BPT overlap projector, written on the literal `MC = (AB) tensor C`
side of the source's first cut.  It is the actual product of the concrete
`AB` and `BC` source factors; `C` is the sole overlap on which the BV03
interaction algebra acts.
-/
noncomputable def firstCutProjectorMC
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
      (M.fourFactorC region)) :=
  TensorProduct.map (M.fourFactorProjectorABLocal region)
      (1 : Semantics.Operator (M.fourFactorC region)) *
    overlapLiftRight (A := M.fourFactorA region) (M.fourFactorProjectorBCLocal region)

/--
The explicit reassociation from the left-associated first BPT cut
`((AB)C)D` to the common source order `A(B(CD))`.  It is the coordinate bridge
used to turn the source products into the two local projectors consumed by
`overlap_projector_tensor_blocks_single_sector`.
-/
noncomputable def firstCutCoordinateTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (M.fourFactorC region))
        (M.fourFactorD region))
      (M.fourFactorSystem region) :=
  composeUnitaryTransport
    (tensorAssociatorUnitary
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
      (M.fourFactorC region) (M.fourFactorD region))
    (tensorAssociatorUnitary (M.fourFactorA region) (M.fourFactorB region)
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))

/-- The first-cut transport sends the literal `AB` lift to its common four-factor extension. -/
theorem firstCutCoordinateTransport_conj_AB_lift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) :
    (M.firstCutCoordinateTransport region).conjOperator
      (TensorProduct.map
        (TensorProduct.map P (1 : Semantics.Operator (M.fourFactorC region)))
        (1 : Semantics.Operator (M.fourFactorD region))) =
      M.fourFactorExtendAB region P := by
  unfold firstCutCoordinateTransport
  rw [composeUnitaryTransport_conjOperator]
  rw [tensorAssociatorUnitary_conj_tensorMap]
  rw [TensorProduct.map_one]
  rfl

/--
The associator coherence used by the `BC` support calculation.  This is the
finite-dimensional tensor identity which moves an arbitrary `BC` vector from
the first-cut parenthesization into the common four-factor parenthesization.
-/
theorem firstCut_associator_coherence
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (a : A) (x : Semantics.CompositeSystem B C) (d : D) :
    (TensorProduct.assoc Complex A B (Semantics.CompositeSystem C D))
        ((TensorProduct.assoc Complex (Semantics.CompositeSystem A B) C D)
          ((TensorProduct.assoc Complex A B C).symm (a ⊗ₜ[Complex] x) ⊗ₜ[Complex] d)) =
      a ⊗ₜ[Complex]
        (TensorProduct.assoc Complex B C D (x ⊗ₜ[Complex] d)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b c => rfl
  | add x y hx hy =>
      simpa only [TensorProduct.add_tmul, map_add, TensorProduct.tmul_add] using
        congrArg₂ (· + ·) hx hy

/-- The first-cut transport sends the literal `BC` lift to its common four-factor extension. -/
theorem firstCutCoordinateTransport_conj_BC_lift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region))) :
    (M.firstCutCoordinateTransport region).conjOperator
      (TensorProduct.map
        (overlapLiftRight (A := M.fourFactorA region) P)
        (1 : Semantics.Operator (M.fourFactorD region))) =
      M.fourFactorExtendBC region P := by
  let T : Semantics.Operator (M.fourFactorSystem region) :=
    (M.firstCutCoordinateTransport region).conjOperator
      (TensorProduct.map
        (overlapLiftRight (A := M.fourFactorA region) P)
        (1 : Semantics.Operator (M.fourFactorD region)))
  let R : Semantics.Operator (M.fourFactorSystem region) :=
    M.fourFactorExtendBC region P
  apply LinearMap.ext
  intro vector
  change T vector = R vector
  induction vector using TensorProduct.induction_on with
  | zero => exact T.map_zero.trans R.map_zero.symm
  | tmul a bcd =>
      induction bcd using TensorProduct.induction_on with
      | zero =>
          simpa only [TensorProduct.tmul_zero] using T.map_zero.trans R.map_zero.symm
      | tmul b cd =>
          induction cd using TensorProduct.induction_on with
          | zero =>
              simpa only [TensorProduct.zero_tmul, TensorProduct.tmul_zero] using
                T.map_zero.trans R.map_zero.symm
          | tmul c d =>
              simpa [T, R, firstCutCoordinateTransport, fourFactorExtendBC,
                fourFactorMiddleReassociate, overlapLiftRight,
                composeUnitaryTransport, tensorAssociatorUnitary,
                Semantics.UnitaryTransport.conjOperator] using
                firstCut_associator_coherence a (P (b ⊗ₜ[Complex] c)) d
          | add x y hx hy =>
              simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
      | add x y hx hy =>
          simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/--
The first source product has the literal first-cut overlap form.  This is the
`Pi_MC` support equation used to instantiate the BV03 block theorem; it is
derived from the independent `AB` and `BC` source-local representatives.
-/
theorem firstCutCoordinateTransport_conj_overlapLiftLeft_firstCutProjectorMC
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutCoordinateTransport region).conjOperator
      (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region)) =
      M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) *
        M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) := by
  let ABLift : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (M.fourFactorC region))
        (M.fourFactorD region)) :=
    TensorProduct.map
      (TensorProduct.map (M.fourFactorProjectorABLocal region)
        (1 : Semantics.Operator (M.fourFactorC region)))
      (1 : Semantics.Operator (M.fourFactorD region))
  let BCLift : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (M.fourFactorC region))
        (M.fourFactorD region)) :=
    TensorProduct.map
      (overlapLiftRight (A := M.fourFactorA region)
        (M.fourFactorProjectorBCLocal region))
      (1 : Semantics.Operator (M.fourFactorD region))
  have hfactor : overlapLiftLeft (C := M.fourFactorD region)
      (M.firstCutProjectorMC region) = ABLift * BCLift := by
    dsimp [ABLift, BCLift]
    unfold overlapLiftLeft firstCutProjectorMC
    rw [← one_mul (1 : Semantics.Operator (M.fourFactorD region))]
    exact TensorProduct.map_mul _ _ _ _
  have hAB : (M.firstCutCoordinateTransport region).conjOperator ABLift =
      M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) := by
    dsimp [ABLift]
    exact M.firstCutCoordinateTransport_conj_AB_lift region
      (M.fourFactorProjectorABLocal region)
  have hBC : (M.firstCutCoordinateTransport region).conjOperator BCLift =
      M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) := by
    dsimp [BCLift]
    exact M.firstCutCoordinateTransport_conj_BC_lift region
      (M.fourFactorProjectorBCLocal region)
  calc
    (M.firstCutCoordinateTransport region).conjOperator
        (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region)) =
        (M.firstCutCoordinateTransport region).conjOperator (ABLift * BCLift) :=
      congrArg (M.firstCutCoordinateTransport region).conjOperator hfactor
    _ = (M.firstCutCoordinateTransport region).conjOperator ABLift *
        (M.firstCutCoordinateTransport region).conjOperator BCLift :=
      Semantics.UnitaryTransport.conjOperator_mul
        (M.firstCutCoordinateTransport region) ABLift BCLift
    _ = M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) *
        M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) :=
      congrArg₂ (· * ·) hAB hBC

/-- The first-cut transport sends the literal `CD` overlap lift to the common source extension. -/
theorem firstCutCoordinateTransport_conj_overlapLiftRight_CD_lift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) :
    (M.firstCutCoordinateTransport region).conjOperator
      (overlapLiftRight
        (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) P) =
      M.fourFactorExtendCD region P := by
  unfold firstCutCoordinateTransport overlapLiftRight fourFactorExtendCD
  rw [composeUnitaryTransport_conjOperator]
  rw [Semantics.UnitaryTransport.conjOperator_symm_conjOperator]
  rw [show (1 : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) =
        TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
          (1 : Semantics.Operator (M.fourFactorB region)) by
        symm
        exact TensorProduct.map_one]
  exact tensorAssociatorUnitary_conj_tensorMap
    (1 : Semantics.Operator (M.fourFactorA region))
    (1 : Semantics.Operator (M.fourFactorB region)) P

/--
The first-cut overlap pair is exactly the full BPT code projector after its
explicit coordinate transport.  This is the source equation
`Pi = Pi_MC Pi_CD`, not a spectral replacement for it.
-/
theorem firstCutCoordinateTransport_conj_source_overlap_product
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutCoordinateTransport region).conjOperator
      (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region) *
        overlapLiftRight
          (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (M.fourFactorProjectorCDLocal region)) =
      (M.fourFactorTransport region).conjOperator M.fullCodeProjector := by
  calc
    (M.firstCutCoordinateTransport region).conjOperator
        (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region) *
          overlapLiftRight
            (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
            (M.fourFactorProjectorCDLocal region)) =
        (M.firstCutCoordinateTransport region).conjOperator
            (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region)) *
          (M.firstCutCoordinateTransport region).conjOperator
            (overlapLiftRight
              (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
              (M.fourFactorProjectorCDLocal region)) :=
      Semantics.UnitaryTransport.conjOperator_mul
        (M.firstCutCoordinateTransport region)
        (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region))
        (overlapLiftRight
          (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (M.fourFactorProjectorCDLocal region))
    _ = (M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) *
          M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region)) *
          M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) := by
      rw [M.firstCutCoordinateTransport_conj_overlapLiftLeft_firstCutProjectorMC,
        M.firstCutCoordinateTransport_conj_overlapLiftRight_CD_lift]
    _ = (M.fourFactorTransport region).conjOperator M.fullCodeProjector :=
      (M.fourFactor_codeProjector_eq_source_products region).symm

/-- The transported first-cut `MC` projector is the transported source `Pi_AB Pi_BC`. -/
theorem firstCutCoordinateTransport_conj_firstCutProjectorMC_eq_sourceMC
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutCoordinateTransport region).conjOperator
      (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region)) =
      (M.fourFactorTransport region).conjOperator
        (M.projectorAB region * M.projectorBC region) := by
  calc
    (M.firstCutCoordinateTransport region).conjOperator
        (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region)) =
        M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) *
          M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) :=
      M.firstCutCoordinateTransport_conj_overlapLiftLeft_firstCutProjectorMC region
    _ = (M.fourFactorTransport region).conjOperator (M.projectorAB region) *
          (M.fourFactorTransport region).conjOperator (M.projectorBC region) := by
      exact (congrArg₂ (· * ·)
        (M.fourFactorTransport_conj_projectorAB region)
        (M.fourFactorTransport_conj_projectorBC region)).symm
    _ = (M.fourFactorTransport region).conjOperator
          (M.projectorAB region * M.projectorBC region) :=
      (Semantics.UnitaryTransport.conjOperator_mul
        (M.fourFactorTransport region) (M.projectorAB region) (M.projectorBC region)).symm

/-- The transported first-cut `CD` projector is the transported source `Pi_CD`. -/
theorem firstCutCoordinateTransport_conj_CD_eq_sourceCD
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutCoordinateTransport region).conjOperator
      (overlapLiftRight
        (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (M.fourFactorProjectorCDLocal region)) =
      (M.fourFactorTransport region).conjOperator (M.projectorCD region) := by
  calc
    (M.firstCutCoordinateTransport region).conjOperator
        (overlapLiftRight
          (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (M.fourFactorProjectorCDLocal region)) =
        M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) :=
      M.firstCutCoordinateTransport_conj_overlapLiftRight_CD_lift region
        (M.fourFactorProjectorCDLocal region)
    _ = (M.fourFactorTransport region).conjOperator (M.projectorCD region) :=
      (M.fourFactorTransport_conj_projectorCD region).symm

/-- The concrete first-cut overlap pair commutes, inherited from the source products. -/
theorem firstCut_overlap_commute
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Commute
      (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region))
      (overlapLiftRight
        (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (M.fourFactorProjectorCDLocal region)) := by
  let U := M.firstCutCoordinateTransport region
  let P := overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region)
  let Q := overlapLiftRight
    (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
    (M.fourFactorProjectorCDLocal region)
  have hP : U.conjOperator P = (M.fourFactorTransport region).conjOperator
      (M.projectorAB region * M.projectorBC region) := by
    dsimp [U, P]
    exact M.firstCutCoordinateTransport_conj_firstCutProjectorMC_eq_sourceMC region
  have hQ : U.conjOperator Q =
      (M.fourFactorTransport region).conjOperator (M.projectorCD region) := by
    dsimp [U, Q]
    exact M.firstCutCoordinateTransport_conj_CD_eq_sourceCD region
  have hsource : Commute
      ((M.fourFactorTransport region).conjOperator (M.projectorAB region * M.projectorBC region))
      ((M.fourFactorTransport region).conjOperator (M.projectorCD region)) := by
    change (M.fourFactorTransport region).conjOperator
        (M.projectorAB region * M.projectorBC region) *
        (M.fourFactorTransport region).conjOperator (M.projectorCD region) =
      (M.fourFactorTransport region).conjOperator (M.projectorCD region) *
        (M.fourFactorTransport region).conjOperator
          (M.projectorAB region * M.projectorBC region)
    calc
      (M.fourFactorTransport region).conjOperator
          (M.projectorAB region * M.projectorBC region) *
          (M.fourFactorTransport region).conjOperator (M.projectorCD region) =
          (M.fourFactorTransport region).conjOperator
            ((M.projectorAB region * M.projectorBC region) * M.projectorCD region) :=
        (Semantics.UnitaryTransport.conjOperator_mul
          (M.fourFactorTransport region)
          (M.projectorAB region * M.projectorBC region) (M.projectorCD region)).symm
      _ = (M.fourFactorTransport region).conjOperator
            (M.projectorCD region * (M.projectorAB region * M.projectorBC region)) :=
        congrArg (M.fourFactorTransport region).conjOperator
          (M.projectorAB_mul_BC_commute_projectorCD region).eq
      _ = (M.fourFactorTransport region).conjOperator (M.projectorCD region) *
          (M.fourFactorTransport region).conjOperator
            (M.projectorAB region * M.projectorBC region) :=
        Semantics.UnitaryTransport.conjOperator_mul
          (M.fourFactorTransport region) (M.projectorCD region)
          (M.projectorAB region * M.projectorBC region)
  have htransport : U.conjOperator (P * Q) = U.conjOperator (Q * P) := by
    calc
      U.conjOperator (P * Q) = U.conjOperator P * U.conjOperator Q :=
        Semantics.UnitaryTransport.conjOperator_mul U P Q
      _ = U.conjOperator Q * U.conjOperator P := by
        rw [hP, hQ]
        exact hsource
      _ = U.conjOperator (Q * P) :=
        (Semantics.UnitaryTransport.conjOperator_mul U Q P).symm
  change P * Q = Q * P
  calc
    P * Q = U.symm.conjOperator (U.conjOperator (P * Q)) :=
      (Semantics.UnitaryTransport.symm_conjOperator_conjOperator U (P * Q)).symm
    _ = U.symm.conjOperator (U.conjOperator (Q * P)) := congrArg U.symm.conjOperator htransport
    _ = Q * P := Semantics.UnitaryTransport.symm_conjOperator_conjOperator U (Q * P)

/-- The finite source exterior factor has a concrete normalized vector for lift reflection. -/
theorem exists_normalized_fourFactorD_vector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    ∃ eta : M.fourFactorD region, ‖eta‖ = 1 := by
  refine ⟨EuclideanSpace.basisFun
    (Semantics.Qudit.Label
      (M.regionSubsystem (region ∪ M.externalBoundary region)).complementDimensions) Complex
    (Semantics.Qudit.zeroLabel
      (M.regionSubsystem (region ∪ M.externalBoundary region)).complementDimensions (by
        intro site
        exact L.localDimension_positive site)), ?_⟩
  simp

/-- Taking an adjoint commutes with the left overlap lift. -/
theorem adjoint_overlapLiftLeft
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B)) :
    LinearMap.adjoint (overlapLiftLeft (C := C) P) =
      overlapLiftLeft (C := C) (LinearMap.adjoint P) := by
  simp only [overlapLiftLeft, TensorProduct.adjoint_map, LinearMap.adjoint_one]

/-- Unitary conjugation preserves and reflects symmetry of finite-dimensional operators. -/
theorem isSymmetric_conjOperator_iff
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (P : Semantics.Operator H) :
    (U.conjOperator P).IsSymmetric ↔ P.IsSymmetric := by
  constructor
  · intro h
    apply (LinearMap.isSymmetric_iff_isSelfAdjoint P).mpr
    apply LinearMap.isSelfAdjoint_iff'.mpr
    have hTransportSelf : LinearMap.adjoint (U.conjOperator P) = U.conjOperator P :=
      LinearMap.isSelfAdjoint_iff'.mp
        ((LinearMap.isSymmetric_iff_isSelfAdjoint (U.conjOperator P)).mp h)
    calc
      LinearMap.adjoint P =
          U.symm.conjOperator (U.conjOperator (LinearMap.adjoint P)) :=
        (Semantics.UnitaryTransport.symm_conjOperator_conjOperator U
          (LinearMap.adjoint P)).symm
      _ = U.symm.conjOperator (LinearMap.adjoint (U.conjOperator P)) :=
        congrArg U.symm.conjOperator
          (Semantics.UnitaryTransport.conjOperator_adjoint U P).symm
      _ = U.symm.conjOperator (U.conjOperator P) :=
        congrArg U.symm.conjOperator hTransportSelf
      _ = P := Semantics.UnitaryTransport.symm_conjOperator_conjOperator U P
  · intro h
    apply (LinearMap.isSymmetric_iff_isSelfAdjoint (U.conjOperator P)).mpr
    apply LinearMap.isSelfAdjoint_iff'.mpr
    calc
      LinearMap.adjoint (U.conjOperator P) = U.conjOperator (LinearMap.adjoint P) :=
        Semantics.UnitaryTransport.conjOperator_adjoint U P
      _ = U.conjOperator P := congrArg U.conjOperator
        (LinearMap.isSelfAdjoint_iff'.mp
          ((LinearMap.isSymmetric_iff_isSelfAdjoint P).mp h))

/-- A normalized exterior vector reflects symmetry through the left overlap lift. -/
theorem isSymmetric_of_overlapLiftLeft
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (eta : C) (heta : ‖eta‖ = 1)
    (h : (overlapLiftLeft (C := C) P).IsSymmetric) : P.IsSymmetric := by
  intro x y
  have hxy := h (x ⊗ₜ[Complex] eta) (y ⊗ₜ[Complex] eta)
  simpa [overlapLiftLeft, TensorProduct.inner_tmul, inner_self_eq_norm_sq_to_K, heta]
    using hxy

/-- The literal first-cut `MC` source projector is symmetric. -/
theorem firstCutProjectorMC_isSymmetric
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutProjectorMC region).IsSymmetric := by
  let U := M.firstCutCoordinateTransport region
  let P := overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region)
  let sourceP := M.projectorAB region * M.projectorBC region
  have hP : U.conjOperator P = (M.fourFactorTransport region).conjOperator sourceP := by
    dsimp [U, P, sourceP]
    exact M.firstCutCoordinateTransport_conj_firstCutProjectorMC_eq_sourceMC region
  have hsource : sourceP.IsSymmetric := by
    dsimp [sourceP]
    exact (M.projectorAB_mul_BC_isSymmetricProjection region).isSymmetric
  have hTransport : (U.conjOperator P).IsSymmetric := by
    rw [hP]
    exact (isSymmetric_conjOperator_iff (M.fourFactorTransport region) sourceP).mpr hsource
  have hLift : P.IsSymmetric :=
    (isSymmetric_conjOperator_iff U P).mp hTransport
  rcases M.exists_normalized_fourFactorD_vector region with ⟨eta, heta⟩
  apply isSymmetric_of_overlapLiftLeft
    (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
    (B := M.fourFactorC region) (C := M.fourFactorD region)
    (M.firstCutProjectorMC region) eta heta
  simpa [P] using hLift

/--
The two overlapping source projectors admit a genuine finite-dimensional joint
spectral decomposition.  This is the spectral part of the source's boundary
decomposition step: the remaining BV03 work refines these joint sectors using
the two interaction algebras to obtain tensor factors on the boundary itself.
The present theorem is used to keep that refinement anchored in an actual
orthogonal direct-sum decomposition of the concrete finite register.
-/
theorem projectorAB_BC_jointEigenspaces_isInternal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    DirectSum.IsInternal (fun eigenvalue : Complex × Complex =>
      Module.End.eigenspace (M.projectorAB region) eigenvalue.2 ⊓
        Module.End.eigenspace (M.projectorBC region) eigenvalue.1) := by
  apply LinearMap.IsSymmetric.directSum_isInternal_of_commute
    (M.projectorAB_isSymmetricProjection region).isSymmetric
    (M.projectorBC_isSymmetricProjection region).isSymmetric
  exact M.projectorAB_commute_projectorBC region

/--
Finite-dimensional joint spectral decomposition for BPT's first `MC/CD`
commuting-projector cut.  The ensuing interaction-algebra refinement must
split the `C` factor inside these joint sectors, exactly as in source lines
594-607; this theorem supplies the concrete orthogonal sector decomposition
on which that refinement acts.
-/
theorem projectorMC_CD_jointEigenspaces_isInternal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    DirectSum.IsInternal (fun eigenvalue : Complex × Complex =>
      Module.End.eigenspace (M.projectorAB region * M.projectorBC region) eigenvalue.2 ⊓
        Module.End.eigenspace (M.projectorCD region) eigenvalue.1) := by
  apply LinearMap.IsSymmetric.directSum_isInternal_of_commute
    (M.projectorAB_mul_BC_isSymmetricProjection region).isSymmetric
    (M.projectorCD_isSymmetricProjection region).isSymmetric
  exact M.projectorAB_mul_BC_commute_projectorCD region

/--
Finite-dimensional joint spectral decomposition for BPT's second
`AB/B bar(M)` commuting-projector cut.  It is the second source decomposition
used before correctability makes the `AB'` factor one-dimensional.
-/
theorem projectorAB_BbarM_jointEigenspaces_isInternal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    DirectSum.IsInternal (fun eigenvalue : Complex × Complex =>
      Module.End.eigenspace (M.projectorAB region) eigenvalue.2 ⊓
        Module.End.eigenspace (M.projectorBC region * M.projectorCD region) eigenvalue.1) := by
  apply LinearMap.IsSymmetric.directSum_isInternal_of_commute
    (M.projectorAB_isSymmetricProjection region).isSymmetric
    (M.projectorBC_mul_CD_isSymmetricProjection region).isSymmetric
  exact M.projectorAB_commute_projectorBC_mul_CD region

/--
The coordinates retained after removing the external boundary from
`M union partialPlus M` are exactly the coordinates of `M`.  This is the
coordinate-level part of the external-boundary locality transport used in the
first BV03 sector collapse.
-/
def externalAdditionalToRegionCoordinateEquiv (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    (M.regionSubsystem (M.externalBoundary region)).AdditionalRetainedCoordinates
        (M.regionSubsystem (region ∪ M.externalBoundary region)) ≃
      (M.regionSubsystem region).SelectedCoordinates where
  toFun := fun site => ⟨site, by
    rcases Finset.mem_union.mp site.property.2 with hregion | hexternal
    · exact hregion
    · exact False.elim (site.property.1 hexternal)⟩
  invFun := fun site => ⟨site, by
    constructor
    · intro hexternal
      exact (Finset.disjoint_left.mp (M.externalBoundary_disjoint_region region))
        hexternal site.property
    · exact Finset.mem_union_left _ site.property⟩
  left_inv := by
    intro site
    exact Subtype.ext rfl
  right_inv := by
    intro site
    exact Subtype.ext rfl

/--
Relabel the residual selected coordinates after the external boundary has been
split off as the physical region `M`.  It is used immediately to compare the
two selected-factorization orders below.
-/
noncomputable def externalAdditionalToRegionCoordinateRelabel
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport
      ((M.regionSubsystem (M.externalBoundary region)).additionalRetainedSystem
        (M.regionSubsystem (region ∪ M.externalBoundary region)))
      (M.regionSubsystem region).selectedSystem :=
  quditCoordinateRelabel
    (q := (M.regionSubsystem (M.externalBoundary region)).additionalRetainedDimensions
      (M.regionSubsystem (region ∪ M.externalBoundary region)))
    (r := (M.regionSubsystem region).selectedDimensions)
    (M.externalAdditionalToRegionCoordinateEquiv region) (by
      intro site
      rfl)

/--
Reorder the `partialPlus M`-first selected factorization into the
`M`-first selected factorization.  The first tensor factor is relabeled as
the virtual first-cut `C` factor; the other factor is relabeled as `M` and
then swapped into source order.
-/
noncomputable def externalSelectedFactorizationReorder
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem
        (M.regionSubsystem (M.externalBoundary region)).selectedSystem
        ((M.regionSubsystem (M.externalBoundary region)).additionalRetainedSystem
          (M.regionSubsystem (region ∪ M.externalBoundary region))))
      (Semantics.CompositeSystem
        (M.regionSubsystem region).selectedSystem
        (M.fourFactorC region)) :=
  composeUnitaryTransport
    (composeUnitaryTransport
      (unitaryRTensor (M.fourFactorCCoordinateRelabel region)
        ((M.regionSubsystem (M.externalBoundary region)).additionalRetainedSystem
          (M.regionSubsystem (region ∪ M.externalBoundary region))))
      (unitaryLTensor (M.fourFactorC region)
        (M.externalAdditionalToRegionCoordinateRelabel region)))
    (tensorSwapUnitary (M.fourFactorC region)
      (M.regionSubsystem region).selectedSystem)

/--
Splitting `M union partialPlus M` first through `partialPlus M`, then
relabeling and swapping, is exactly the selected-coordinate factorization
through `M`.
-/
theorem externalSelectedFactorization_reorder_eq
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    composeUnitaryTransport
      ((M.regionSubsystem (M.externalBoundary region)).selectedFactorization
        (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
          intro site hsite
          exact Finset.mem_union_right _ hsite))
      (M.externalSelectedFactorizationReorder region) =
      (M.regionSubsystem region).selectedFactorization
        (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
          intro site hsite
          exact Finset.mem_union_left _ hsite) := by
  apply unitaryTransport_ext
  apply LinearEquiv.toLinearMap_injective
  apply (EuclideanSpace.basisFun
    (Semantics.Qudit.Label
      (M.regionSubsystem (region ∪ M.externalBoundary region)).selectedDimensions) Complex).toBasis.ext
  intro labels
  change composeUnitaryTransport
      ((M.regionSubsystem (M.externalBoundary region)).selectedFactorization
        (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
          intro site hsite
          exact Finset.mem_union_right _ hsite))
      (M.externalSelectedFactorizationReorder region)
      (EuclideanSpace.basisFun
        (Semantics.Qudit.Label
          (M.regionSubsystem (region ∪ M.externalBoundary region)).selectedDimensions) Complex labels) =
    (M.regionSubsystem region).selectedFactorization
      (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
        intro site hsite
        exact Finset.mem_union_left _ hsite)
      (EuclideanSpace.basisFun
        (Semantics.Qudit.Label
          (M.regionSubsystem (region ∪ M.externalBoundary region)).selectedDimensions) Complex labels)
  rw [composeUnitaryTransport_apply]
  erw [(M.regionSubsystem (M.externalBoundary region)).selectedFactorization_apply_basis
    (M.regionSubsystem (region ∪ M.externalBoundary region))]
  dsimp [externalSelectedFactorizationReorder,
    externalAdditionalToRegionCoordinateRelabel,
    fourFactorCCoordinateRelabel]
  erw [quditCoordinateRelabel_apply_basis, quditCoordinateRelabel_apply_basis]
  erw [(M.regionSubsystem region).selectedFactorization_apply_basis
    (M.regionSubsystem (region ∪ M.externalBoundary region))]
  congr 1

/--
An external-boundary local operator, pulled back along the physical-to-virtual
`C` relabeling, becomes `1_M tensor Z` when `M union partialPlus M` is split
through `M`.
-/
theorem selectedFactorization_conj_liftExternalBoundary
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorC region)) :
    ((M.regionSubsystem region).selectedFactorization
      (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
        intro site hsite
        exact Finset.mem_union_left _ hsite)).conjOperator
      (liftLocalToLarger (M.regionSubsystem (M.externalBoundary region))
        (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
          intro site hsite
          exact Finset.mem_union_right _ hsite)
        ((M.fourFactorCCoordinateRelabel region).symm.conjOperator Z)) =
      TensorProduct.map (1 : Semantics.Operator (M.regionSubsystem region).selectedSystem) Z := by
  rw [← M.externalSelectedFactorization_reorder_eq region,
    composeUnitaryTransport_conjOperator]
  dsimp [liftLocalToLarger]
  rw [((M.regionSubsystem (M.externalBoundary region)).selectedFactorization
    (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
      intro site hsite
      exact Finset.mem_union_right _ hsite)).conjOperator_symm_conjOperator]
  dsimp [externalSelectedFactorizationReorder]
  rw [composeUnitaryTransport_conjOperator, composeUnitaryTransport_conjOperator]
  rw [unitaryRTensor_conj_tensorMap_left]
  rw [(M.fourFactorCCoordinateRelabel region).conjOperator_symm_conjOperator]
  rw [unitaryLTensor_conj_tensorMap_right]
  exact tensorSwapUnitary_conj_tensorMap Z
    (1 : Semantics.Operator (M.regionSubsystem region).selectedSystem)

/--
The global nested `M, C, D` coordinates retain the physical support of an
external-boundary local operator while exposing it as `1_M tensor Z tensor
1_D`.  This is the locality bridge supplied to external-boundary
no-information in the first BV03 decomposition.
-/
theorem nestedFactorizationRight_conj_externalBoundaryLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorC region)) :
    (nestedFactorizationRight (M.regionSubsystem region)
      (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
        intro site hsite
        exact Finset.mem_union_left _ hsite)).conjOperator
      ((M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
        ((M.fourFactorCCoordinateRelabel region).symm.conjOperator Z)) =
      TensorProduct.map (1 : Semantics.Operator (M.regionSubsystem region).selectedSystem)
        (TensorProduct.map Z (1 : Semantics.Operator
          (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem)) := by
  rw [← extendLocalToRegister_liftLocalToLarger
    (M.regionSubsystem (M.externalBoundary region))
    (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
      intro site hsite
      exact Finset.mem_union_right _ hsite)]
  have hright : nestedFactorizationRight (M.regionSubsystem region)
      (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
        intro site hsite
        exact Finset.mem_union_left _ hsite) =
      composeUnitaryTransport
        (composeUnitaryTransport
          (M.regionSubsystem (region ∪ M.externalBoundary region)).registerFactorization
          (unitaryRTensor
            ((M.regionSubsystem region).selectedFactorization
              (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
                intro site hsite
                exact Finset.mem_union_left _ hsite))
            (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem))
        (tensorAssociatorUnitary
          (M.regionSubsystem region).selectedSystem
          (M.fourFactorC region)
          (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem) := by
    apply unitaryTransport_ext
    rfl
  rw [hright, composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator]
  rw [registerFactorization_conj_extendLocalToRegister]
  rw [unitaryRTensor_conj_tensorMap_left,
    M.selectedFactorization_conj_liftExternalBoundary region]
  exact tensorAssociatorUnitary_conj_tensorMap
    (1 : Semantics.Operator (M.regionSubsystem region).selectedSystem) Z
    (1 : Semantics.Operator
      (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem)

/--
An `AB`-first presentation of the four-factor transport built from the
right-nested `AB,C,D` factorization.  This form is used immediately to carry
the external-boundary support equation into the first BV03 cut.
-/
noncomputable def fourFactorTransportFromNestedRegion
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport L.Register (M.fourFactorSystem region) := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  let splitAB : Semantics.UnitaryTransport AB.selectedSystem
      (Semantics.CompositeSystem A.selectedSystem (A.additionalRetainedSystem AB)) := by
    let e := A.selectedFactorization AB hAAB
    exact
      { toLinearEquiv := e.toLinearEquiv
        map_inner := e.map_inner }
  exact composeUnitaryTransport
    (composeUnitaryTransport (nestedFactorizationRight AB ABC hABABC)
      (unitaryRTensor splitAB
        (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem)))
    (tensorAssociatorUnitary A.selectedSystem (A.additionalRetainedSystem AB)
      (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem))

set_option maxHeartbeats 800000 in
/--
The right-nested and original cumulative `A,B,C,D` factorizations coincide.
The proof is a basis calculation using the already-proved coherence of the
two nested coordinate splits.
-/
theorem fourFactorTransport_eq_fourFactorTransportFromNestedRegion
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.fourFactorTransport region = M.fourFactorTransportFromNestedRegion region := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  let splitAB : Semantics.UnitaryTransport AB.selectedSystem
      (Semantics.CompositeSystem A.selectedSystem (A.additionalRetainedSystem AB)) := by
    let e := A.selectedFactorization AB hAAB
    exact
      { toLinearEquiv := e.toLinearEquiv
        map_inner := e.map_inner }
  have hNested :
      nestedFactorizationLeft AB ABC hABABC =
        nestedFactorizationRight AB ABC hABABC := by
    apply unitaryTransport_ext
    exact nestedFactorization_toLinearEquiv_eq AB ABC hABABC
  change composeUnitaryTransport
      (composeUnitaryTransport (nestedFactorizationLeft AB ABC hABABC)
        (unitaryRTensor splitAB
          (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem)))
      (tensorAssociatorUnitary A.selectedSystem (A.additionalRetainedSystem AB)
        (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem)) =
    composeUnitaryTransport
      (composeUnitaryTransport (nestedFactorizationRight AB ABC hABABC)
        (unitaryRTensor splitAB
          (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem)))
      (tensorAssociatorUnitary A.selectedSystem (A.additionalRetainedSystem AB)
        (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem))
  exact congrArg (fun transport => composeUnitaryTransport
    (composeUnitaryTransport transport
      (unitaryRTensor splitAB
        (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem)))
    (tensorAssociatorUnitary A.selectedSystem (A.additionalRetainedSystem AB)
      (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem))) hNested

/--
In the canonical four-factor coordinates, a physical external-boundary lift
is exactly the virtual `C` lift with identities on `A`, `B`, and `D`.
-/
theorem fourFactorTransport_conj_externalBoundaryLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorC region)) :
    (M.fourFactorTransport region).conjOperator
      ((M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
        ((M.fourFactorCCoordinateRelabel region).symm.conjOperator Z)) =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorB region))
          (TensorProduct.map Z (1 : Semantics.Operator (M.fourFactorD region))) ) := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  let Zx : Semantics.Operator L.Register :=
    (M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
      ((M.fourFactorCCoordinateRelabel region).symm.conjOperator Z)
  change (M.fourFactorTransport region).conjOperator Zx =
    TensorProduct.map (1 : Semantics.Operator A.selectedSystem)
      (TensorProduct.map (1 : Semantics.Operator (A.additionalRetainedSystem AB))
        (TensorProduct.map Z (1 : Semantics.Operator ABC.complementSystem)))
  calc
    (M.fourFactorTransport region).conjOperator Zx =
        (M.fourFactorTransportFromNestedRegion region).conjOperator Zx :=
      congrArg (fun transport => transport.conjOperator Zx)
        (M.fourFactorTransport_eq_fourFactorTransportFromNestedRegion region)
    _ = TensorProduct.map (1 : Semantics.Operator A.selectedSystem)
        (TensorProduct.map (1 : Semantics.Operator (A.additionalRetainedSystem AB))
          (TensorProduct.map Z (1 : Semantics.Operator ABC.complementSystem))) := by
      dsimp [fourFactorTransportFromNestedRegion, Zx]
      rw [composeUnitaryTransport_conjOperator, composeUnitaryTransport_conjOperator]
      rw [M.nestedFactorizationRight_conj_externalBoundaryLift region Z]
      rw [unitaryRTensor_conj_tensorMap_right]
      rw [show (1 : Semantics.Operator
          (Semantics.CompositeSystem A.selectedSystem (A.additionalRetainedSystem AB))) =
          TensorProduct.map (1 : Semantics.Operator A.selectedSystem)
            (1 : Semantics.Operator (A.additionalRetainedSystem AB)) by
          symm
          exact TensorProduct.map_one]
      rw [tensorAssociatorUnitary_conj_tensorMap]

/--
Splitting the physical boundary into its internal and external pieces sends an
internal-boundary operator to the literal `B tensor 1_C` action.  This is the
locality bridge used by the second `AB / B bar(M)` cut.
-/
theorem boundarySelectedToBCTransport_conj_internalBoundaryLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorB region)) :
    (M.boundarySelectedToBCTransport region).conjOperator
      (liftLocalToLarger (M.regionSubsystem (M.internalBoundary region))
        (M.regionSubsystem (M.boundary region)) (by
          intro site hsite
          rw [M.boundary_eq_internal_union_external region]
          exact Finset.mem_union_left _ hsite)
        ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z)) =
      TensorProduct.map Z (1 : Semantics.Operator (M.fourFactorC region)) := by
  let B := M.regionSubsystem (M.internalBoundary region)
  let BC := M.regionSubsystem (M.boundary region)
  have hBBC : B.selected ⊆ BC.selected := by
    intro site hsite
    change site ∈ M.boundary region
    rw [M.boundary_eq_internal_union_external region]
    exact Finset.mem_union_left _ hsite
  change (M.boundarySelectedToBCTransport region).conjOperator
      (liftLocalToLarger B BC hBBC
        ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z)) =
      TensorProduct.map Z (1 : Semantics.Operator (M.fourFactorC region))
  unfold boundarySelectedToBCTransport
  rw [composeUnitaryTransport_conjOperator, composeUnitaryTransport_conjOperator]
  rw [liftLocalToLarger, Semantics.UnitaryTransport.conjOperator_symm_conjOperator]
  rw [unitaryRTensor_conj_tensorMap_left]
  rw [(M.fourFactorBCoordinateRelabel region).conjOperator_symm_conjOperator]
  rw [unitaryLTensor_conj_tensorMap_right]

/--
In canonical four-factor coordinates, a physical internal-boundary lift is
exactly the virtual `B` lift with identities on `A`, `C`, and `D`.  The proof
keeps the physical support visible through the boundary factorization.
-/
theorem fourFactorTransport_conj_internalBoundaryLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorB region)) :
    (M.fourFactorTransport region).conjOperator
      ((M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
        ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z)) =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map Z
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
            (1 : Semantics.Operator (M.fourFactorD region)))) := by
  let B := M.regionSubsystem (M.internalBoundary region)
  let BC := M.regionSubsystem (M.boundary region)
  have hBBC : B.selected ⊆ BC.selected := by
    intro site hsite
    change site ∈ M.boundary region
    rw [M.boundary_eq_internal_union_external region]
    exact Finset.mem_union_left _ hsite
  let Zx : Semantics.Operator L.Register :=
    B.extendLocalToRegister ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z)
  change (M.fourFactorTransport region).conjOperator Zx =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map Z
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
            (1 : Semantics.Operator (M.fourFactorD region))))
  calc
    (M.fourFactorTransport region).conjOperator Zx =
        (M.boundaryGlobalToFourFactorTransport region).conjOperator Zx := by
      exact congrArg (fun transport => transport.conjOperator Zx)
        (M.boundaryGlobalToFourFactorTransport_eq_fourFactorTransport region).symm
    _ = (M.boundaryGlobalToFourFactorTransport region).conjOperator
        (BC.extendLocalToRegister
          (liftLocalToLarger B BC hBBC
            ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z))) := by
      congr 1
      exact (extendLocalToRegister_liftLocalToLarger B BC hBBC
        ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z)).symm
    _ = M.fourFactorExtendBC region
        ((M.boundarySelectedToBCTransport region).conjOperator
          (liftLocalToLarger B BC hBBC
            ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z))) :=
      M.boundaryGlobalToFourFactorTransport_conj_extendLocalToRegister region _
    _ = M.fourFactorExtendBC region
        (TensorProduct.map Z (1 : Semantics.Operator (M.fourFactorC region))) := by
      rw [M.boundarySelectedToBCTransport_conj_internalBoundaryLift]
    _ = TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map Z
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
            (1 : Semantics.Operator (M.fourFactorD region)))) := by
      have hmiddle : (M.fourFactorMiddleReassociate region).symm =
          unitaryLTensor (M.fourFactorA region)
            (tensorAssociatorUnitary (M.fourFactorB region) (M.fourFactorC region)
              (M.fourFactorD region)) := by
        apply unitaryTransport_ext
        rfl
      unfold fourFactorExtendBC
      rw [hmiddle, unitaryLTensor_conj_tensorMap_left]
      exact congrArg (fun operator => TensorProduct.map
        (1 : Semantics.Operator (M.fourFactorA region)) operator)
        (tensorAssociatorUnitary_conj_tensorMap Z
          (1 : Semantics.Operator (M.fourFactorC region))
          (1 : Semantics.Operator (M.fourFactorD region)))

/--
The first-cut associators carry the virtual `C` sector lift to the same
`A,B,C,D` operator exposed by the external-boundary transport.
-/
theorem firstCutCoordinateTransport_conj_externalBoundarySectorLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorC region)) :
    (M.firstCutCoordinateTransport region).conjOperator
      (overlapLiftLeft (C := M.fourFactorD region)
        (TensorProduct.map
          (1 : Semantics.Operator
            (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) Z)) =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorB region))
          (TensorProduct.map Z (1 : Semantics.Operator (M.fourFactorD region))) ) := by
  unfold firstCutCoordinateTransport overlapLiftLeft
  rw [composeUnitaryTransport_conjOperator]
  rw [tensorAssociatorUnitary_conj_tensorMap]
  rw [show (1 : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) =
        TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
          (1 : Semantics.Operator (M.fourFactorB region)) by
        symm
        exact TensorProduct.map_one]
  exact tensorAssociatorUnitary_conj_tensorMap
    (1 : Semantics.Operator (M.fourFactorA region))
    (1 : Semantics.Operator (M.fourFactorB region))
    (TensorProduct.map Z (1 : Semantics.Operator (M.fourFactorD region)))

/--
Transporting a physical external-boundary local operator into first-cut
coordinates gives precisely the lift of its virtual `C` representative.
-/
theorem firstCutCoordinateTransport_symm_conj_externalBoundaryLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorC region)) :
    (M.firstCutCoordinateTransport region).symm.conjOperator
      ((M.fourFactorTransport region).conjOperator
        ((M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
          ((M.fourFactorCCoordinateRelabel region).symm.conjOperator Z))) =
      overlapLiftLeft (C := M.fourFactorD region)
        (TensorProduct.map
          (1 : Semantics.Operator
            (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) Z) := by
  let U := M.firstCutCoordinateTransport region
  let sectorLift := overlapLiftLeft (C := M.fourFactorD region)
    (TensorProduct.map
      (1 : Semantics.Operator
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) Z)
  have hfour := M.fourFactorTransport_conj_externalBoundaryLift region Z
  have hfirst := M.firstCutCoordinateTransport_conj_externalBoundarySectorLift region Z
  calc
    U.symm.conjOperator
        ((M.fourFactorTransport region).conjOperator
          ((M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
            ((M.fourFactorCCoordinateRelabel region).symm.conjOperator Z))) =
        U.symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
            (TensorProduct.map (1 : Semantics.Operator (M.fourFactorB region))
              (TensorProduct.map Z (1 : Semantics.Operator (M.fourFactorD region))))) :=
      congrArg U.symm.conjOperator hfour
    _ = U.symm.conjOperator (U.conjOperator sectorLift) := by
      exact congrArg U.symm.conjOperator hfirst.symm
    _ = sectorLift := U.symm_conjOperator_conjOperator sectorLift

/-- Unitary conjugation preserves and reflects orthogonal-projection structure. -/
theorem isSymmetricProjection_conjOperator_iff
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (P : Semantics.Operator H) :
    (U.conjOperator P).IsSymmetricProjection ↔ P.IsSymmetricProjection := by
  constructor
  · intro h
    constructor
    · calc
        P * P = U.symm.conjOperator (U.conjOperator (P * P)) :=
          (U.symm_conjOperator_conjOperator (P * P)).symm
        _ = U.symm.conjOperator (U.conjOperator P * U.conjOperator P) := by
          rw [Semantics.UnitaryTransport.conjOperator_mul]
        _ = U.symm.conjOperator (U.conjOperator P) :=
          congrArg U.symm.conjOperator h.isIdempotentElem
        _ = P := U.symm_conjOperator_conjOperator P
    · exact (isSymmetric_conjOperator_iff U P).mp h.isSymmetric
  · intro h
    constructor
    · calc
        U.conjOperator P * U.conjOperator P = U.conjOperator (P * P) :=
          (Semantics.UnitaryTransport.conjOperator_mul U P P).symm
        _ = U.conjOperator P := congrArg U.conjOperator h.isIdempotentElem
    · exact (isSymmetric_conjOperator_iff U P).mpr h.isSymmetric

/-- Orthogonal-projection structure transports across an equality of operators. -/
theorem isSymmetricProjection_congr
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] {P Q : Semantics.Operator H}
    (hP : P.IsSymmetricProjection) (hPQ : P = Q) : Q.IsSymmetricProjection := by
  cases hPQ
  exact hP

/-- A right-tensor extension is a projection only if its left tensor factor is one. -/
theorem isSymmetricProjection_of_rightTensorExtensionAfterLeft
    {A W N : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (P : Semantics.Operator (Semantics.CompositeSystem A W))
    (h : (rightTensorExtensionAfterLeft A W N P).IsSymmetricProjection) :
    (TensorProduct.map P (1 : Semantics.Operator N)).IsSymmetricProjection := by
  exact (isSymmetricProjection_conjOperator_iff
    (tensorAssociatorUnitary A W N)
    (TensorProduct.map P (1 : Semantics.Operator N))).mp
    (by simpa only [rightTensorExtensionAfterLeft] using h)

/--
Commutation can be reflected through a unitary coordinate transport.  This is
used by the two BPT cuts to return a virtual sector commutation relation to
the physical local operator supplied to no-information.
-/
theorem commute_of_conjOperator_commute
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K)
    {P Q : Semantics.Operator H}
    (h : Commute (U.conjOperator P) (U.conjOperator Q)) :
    Commute P Q := by
  calc
    P * Q = U.symm.conjOperator (U.conjOperator (P * Q)) :=
      (U.symm_conjOperator_conjOperator (P * Q)).symm
    _ = U.symm.conjOperator (U.conjOperator P * U.conjOperator Q) := by
      rw [Semantics.UnitaryTransport.conjOperator_mul]
    _ = U.symm.conjOperator (U.conjOperator Q * U.conjOperator P) :=
      congrArg U.symm.conjOperator h.eq
    _ = U.symm.conjOperator (U.conjOperator (Q * P)) := by
      exact congrArg U.symm.conjOperator
        (Semantics.UnitaryTransport.conjOperator_mul U Q P).symm
    _ = Q * P := U.symm_conjOperator_conjOperator (Q * P)

/-- Tensoring two orthogonal projections yields an orthogonal projection. -/
theorem tensorMap_isSymmetricProjection
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    {P : Semantics.Operator H} {Q : Semantics.Operator K}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    (TensorProduct.map P Q).IsSymmetricProjection := by
  constructor
  · apply LinearMap.ext
    intro vector
    induction vector using TensorProduct.induction_on with
    | zero => simp
    | tmul left right =>
        change (P * P) left ⊗ₜ[Complex] (Q * Q) right = P left ⊗ₜ[Complex] Q right
        rw [hP.isIdempotentElem, hQ.isIdempotentElem]
    | add left right hleft hright =>
        simpa only [map_add] using congrArg₂ (· + ·) hleft hright
  · apply (LinearMap.isSymmetric_iff_isSelfAdjoint (TensorProduct.map P Q)).mpr
    apply LinearMap.isSelfAdjoint_iff'.mpr
    rw [TensorProduct.adjoint_map, hP.isSymmetric.adjoint_eq,
      hQ.isSymmetric.adjoint_eq]

/-- The identity operator is an orthogonal projection. -/
theorem one_isSymmetricProjection
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] :
    (1 : Semantics.Operator H).IsSymmetricProjection := by
  constructor
  · exact mul_one _
  · intro left right
    simp

set_option maxHeartbeats 800000 in
/--
External-boundary correctability collapses every first-cut isotypic sector to
either the zero code sector or the entire code.  The measured sector is
presented to no-information as an actual operator supported on
`partialPlus M`, then transported back to the virtual first-cut `C` factor.
-/
theorem firstCut_externalBoundary_sector_dichotomy
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region))
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) :
    M.fullCodeProjector *
        (M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
          ((M.fourFactorCCoordinateRelabel region).symm.conjOperator
            (leftIsotypicSectorProjector (M.firstCutProjectorMC region) component)) = 0 ∨
    M.fullCodeProjector *
        (M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
          ((M.fourFactorCCoordinateRelabel region).symm.conjOperator
            (leftIsotypicSectorProjector (M.firstCutProjectorMC region) component)) =
      M.fullCodeProjector := by
  let A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)
  let C := M.fourFactorC region
  let D := M.fourFactorD region
  let P : Semantics.Operator (Semantics.CompositeSystem A C) := M.firstCutProjectorMC region
  let Q : Semantics.Operator (Semantics.CompositeSystem C D) :=
    M.fourFactorProjectorCDLocal region
  let sector : Semantics.Operator C := leftIsotypicSectorProjector P component
  let Zx : Semantics.Operator L.Register :=
    (M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
      ((M.fourFactorCCoordinateRelabel region).symm.conjOperator sector)
  let U := M.firstCutCoordinateTransport region
  let V := M.fourFactorTransport region
  let H := composeUnitaryTransport V U.symm
  let sectorLift : Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem A C) D) :=
    overlapLiftLeft (C := D) (TensorProduct.map (1 : Semantics.Operator A) sector)
  let codeLift : Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem A C) D) :=
    overlapLiftLeft (C := D) P * overlapLiftRight (A := A) Q
  have hself : LinearMap.adjoint P = P := by
    apply LinearMap.isSelfAdjoint_iff'.mp
    apply (LinearMap.isSymmetric_iff_isSelfAdjoint P).mp
    simpa [P] using M.firstCutProjectorMC_isSymmetric region
  have hover : Commute (overlapLiftLeft (C := D) P) (overlapLiftRight (A := A) Q) := by
    simpa [A, C, D, P, Q] using M.firstCut_overlap_commute region
  have hsectorCommutes := leftIsotypicSectorProjector_commutes_overlap
    P Q hself hover component
  have hPcommutes : Commute (overlapLiftLeft (C := D) P) sectorLift := by
    change TensorProduct.map P (1 : Semantics.Operator D) *
        TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) sector)
          (1 : Semantics.Operator D) =
      TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) sector)
          (1 : Semantics.Operator D) * TensorProduct.map P (1 : Semantics.Operator D)
    rw [← TensorProduct.map_mul, ← TensorProduct.map_mul]
    simpa using congrArg (fun operator =>
      TensorProduct.map operator (1 : Semantics.Operator D)) hsectorCommutes.1.eq
  have hsectorLiftRight : sectorLift =
      overlapLiftRight (A := A) (TensorProduct.map sector (1 : Semantics.Operator D)) := by
    dsimp [sectorLift, overlapLiftLeft, overlapLiftRight]
    symm
    exact tensorAssociatorUnitary_symm_conj_tensorMap
      (1 : Semantics.Operator A) sector (1 : Semantics.Operator D)
  have hQcommutes : Commute (overlapLiftRight (A := A) Q) sectorLift := by
    rw [hsectorLiftRight]
    change
      (tensorAssociatorUnitary A C D).symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator A) Q) *
        (tensorAssociatorUnitary A C D).symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator A)
            (TensorProduct.map sector (1 : Semantics.Operator D))) =
      (tensorAssociatorUnitary A C D).symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator A)
            (TensorProduct.map sector (1 : Semantics.Operator D))) *
        (tensorAssociatorUnitary A C D).symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator A) Q)
    calc
      (tensorAssociatorUnitary A C D).symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator A) Q) *
          (tensorAssociatorUnitary A C D).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A)
              (TensorProduct.map sector (1 : Semantics.Operator D))) =
          (tensorAssociatorUnitary A C D).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A) Q *
              TensorProduct.map (1 : Semantics.Operator A)
                (TensorProduct.map sector (1 : Semantics.Operator D))) :=
          (Semantics.UnitaryTransport.conjOperator_mul _ _ _).symm
      _ = (tensorAssociatorUnitary A C D).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A)
              (TensorProduct.map sector (1 : Semantics.Operator D)) *
              TensorProduct.map (1 : Semantics.Operator A) Q) := by
          congr 1
          rw [← TensorProduct.map_mul, ← TensorProduct.map_mul]
          simpa using congrArg (fun operator =>
            TensorProduct.map (1 : Semantics.Operator A) operator) hsectorCommutes.2.eq
      _ = (tensorAssociatorUnitary A C D).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A)
              (TensorProduct.map sector (1 : Semantics.Operator D))) *
          (tensorAssociatorUnitary A C D).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A) Q) :=
          Semantics.UnitaryTransport.conjOperator_mul _ _ _
  have hcodeLiftCommutes : Commute codeLift sectorLift := by
    exact (hPcommutes.symm.mul_right hQcommutes.symm).symm
  have hsectorProjection : sector.IsSymmetricProjection := by
    simpa [sector, P] using
      leftIsotypicSectorProjector_isSymmetricProjection P component
  have hsectorLiftProjection : sectorLift.IsSymmetricProjection := by
    dsimp [sectorLift, overlapLiftLeft]
    exact tensorMap_isSymmetricProjection
      (tensorMap_isSymmetricProjection (one_isSymmetricProjection A) hsectorProjection)
      (one_isSymmetricProjection D)
  have hHsector : H.conjOperator Zx = sectorLift := by
    change (composeUnitaryTransport (M.fourFactorTransport region)
      (M.firstCutCoordinateTransport region).symm).conjOperator
        ((M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
          ((M.fourFactorCCoordinateRelabel region).symm.conjOperator sector)) = sectorLift
    rw [composeUnitaryTransport_conjOperator]
    simpa [A, C, D, sectorLift] using
      M.firstCutCoordinateTransport_symm_conj_externalBoundaryLift region sector
  have hHcode : H.conjOperator M.fullCodeProjector = codeLift := by
    change (composeUnitaryTransport (M.fourFactorTransport region)
      (M.firstCutCoordinateTransport region).symm).conjOperator M.fullCodeProjector = codeLift
    rw [composeUnitaryTransport_conjOperator]
    calc
      (M.firstCutCoordinateTransport region).symm.conjOperator
          ((M.fourFactorTransport region).conjOperator M.fullCodeProjector) =
          (M.firstCutCoordinateTransport region).symm.conjOperator
            ((M.firstCutCoordinateTransport region).conjOperator codeLift) := by
        congr 1
        simpa [A, C, D, codeLift, P, Q] using
          (M.firstCutCoordinateTransport_conj_source_overlap_product region).symm
      _ = codeLift :=
        (M.firstCutCoordinateTransport region).symm_conjOperator_conjOperator codeLift
  have hZxProjection : Zx.IsSymmetricProjection := by
    apply (isSymmetricProjection_conjOperator_iff H Zx).mp
    rw [hHsector]
    exact hsectorLiftProjection
  have hcodeCommutes : Commute M.fullCodeProjector Zx := by
    apply commute_of_conjOperator_commute H
    rw [hHcode, hHsector]
    exact hcodeLiftCommutes
  have hlocal : (M.regionSubsystem (M.externalBoundary region)).OperatorSupportedOnRegister Zx := by
    refine ⟨(M.fourFactorCCoordinateRelabel region).symm.conjOperator sector, ?_⟩
    rfl
  have hInformation := M.regionErasureRecoverable_implies_noInformationOn
    (M.externalBoundary region) hC
  simpa [Zx, fullCodeProjector] using
    (local_commutingProjection_codeSector_eq_zero_or_codeProjector
      (M.regionSubsystem (M.externalBoundary region)) M.codeSpace hInformation hlocal
      hZxProjection hcodeCommutes)

/--
The product of a commuting overlap pair commutes with the lifted projector
onto every left-isotypic sector.  This is the coefficient-free commutation
input needed to instantiate finite sector collapse.
-/
theorem overlap_product_commutes_leftIsotypicSectorLift
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    Commute
      (overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q)
      (overlapLiftLeft (C := C)
        (TensorProduct.map (1 : Semantics.Operator A)
          (leftIsotypicSectorProjector P component))) := by
  let sector := leftIsotypicSectorProjector P component
  let sectorLift := overlapLiftLeft (C := C)
    (TensorProduct.map (1 : Semantics.Operator A) sector)
  have hsectorCommutes := leftIsotypicSectorProjector_commutes_overlap
    P Q hselfAdjoint hcommute component
  have hPcommutes : Commute (overlapLiftLeft (C := C) P) sectorLift := by
    change TensorProduct.map P (1 : Semantics.Operator C) *
        TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) sector)
          (1 : Semantics.Operator C) =
      TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) sector)
          (1 : Semantics.Operator C) * TensorProduct.map P (1 : Semantics.Operator C)
    rw [← TensorProduct.map_mul, ← TensorProduct.map_mul]
    simpa using congrArg (fun operator =>
      TensorProduct.map operator (1 : Semantics.Operator C)) hsectorCommutes.1.eq
  have hsectorLiftRight : sectorLift =
      overlapLiftRight (A := A) (TensorProduct.map sector (1 : Semantics.Operator C)) := by
    dsimp [sectorLift, overlapLiftLeft, overlapLiftRight]
    symm
    exact tensorAssociatorUnitary_symm_conj_tensorMap
      (1 : Semantics.Operator A) sector (1 : Semantics.Operator C)
  have hQcommutes : Commute (overlapLiftRight (A := A) Q) sectorLift := by
    rw [hsectorLiftRight]
    change Commute
      ((tensorAssociatorUnitary A B C).symm.conjOperator
        (TensorProduct.map (1 : Semantics.Operator A) Q))
      ((tensorAssociatorUnitary A B C).symm.conjOperator
        (TensorProduct.map (1 : Semantics.Operator A)
          (TensorProduct.map sector (1 : Semantics.Operator C))))
    calc
      (tensorAssociatorUnitary A B C).symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator A) Q) *
          (tensorAssociatorUnitary A B C).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A)
              (TensorProduct.map sector (1 : Semantics.Operator C))) =
          (tensorAssociatorUnitary A B C).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A) Q *
              TensorProduct.map (1 : Semantics.Operator A)
                (TensorProduct.map sector (1 : Semantics.Operator C))) :=
          (Semantics.UnitaryTransport.conjOperator_mul _ _ _).symm
      _ = (tensorAssociatorUnitary A B C).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A)
              (TensorProduct.map sector (1 : Semantics.Operator C)) *
              TensorProduct.map (1 : Semantics.Operator A) Q) := by
          congr 1
          rw [← TensorProduct.map_mul, ← TensorProduct.map_mul]
          simpa using congrArg (fun operator =>
            TensorProduct.map (1 : Semantics.Operator A) operator) hsectorCommutes.2.eq
      _ = (tensorAssociatorUnitary A B C).symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator A)
            (TensorProduct.map sector (1 : Semantics.Operator C))) *
          (tensorAssociatorUnitary A B C).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A) Q) :=
          Semantics.UnitaryTransport.conjOperator_mul _ _ _
  exact (hPcommutes.symm.mul_right hQcommutes.symm).symm

/--
The double matrix element of an actual overlapping product is the product of
its left and right interaction coefficients.  This is the coefficient-level
form of the BV03 overlap relation used to transfer sector commutation to the
nonzero coefficient that witnesses an active code sector.
-/
theorem doubleInteractionCoefficient_overlap_product_eq
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (a a' : A) (c c' : C) :
    leftInteractionCoefficient
        (rightInteractionCoefficient
          (overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q) c c') a a' =
      leftInteractionCoefficient P a a' * rightInteractionCoefficient Q c c' := by
  simpa [leftInteractionCoefficient, rightInteractionCoefficient,
    overlapTripleEmbedding, LinearMap.comp_assoc] using
    (overlapTripleCompression_left_then_right P Q a a' c c')

/--
Taking a right and then left interaction coefficient preserves commutation
with a lifted left-isotypic sector.
-/
theorem doubleInteractionCoefficient_commutes_leftIsotypicSector
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B)
    (c c' : C) (a a' : A) :
    Commute
      (leftInteractionCoefficient
        (rightInteractionCoefficient
          (overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q) c c') a a')
      (leftIsotypicSectorProjector P component) := by
  rw [doubleInteractionCoefficient_overlap_product_eq P Q a a' c c']
  let leftCoefficient := leftInteractionCoefficient P a a'
  let rightCoefficient := rightInteractionCoefficient Q c c'
  have hleft : Commute
      (leftIsotypicSectorProjector P component) leftCoefficient := by
    simpa [leftCoefficient] using
      leftIsotypicSectorProjector_commute_leftInteractionCoefficient P component a a'
  have hright : Commute
      (leftIsotypicSectorProjector P component) rightCoefficient := by
    simpa [rightCoefficient] using
      leftIsotypicSectorProjector_commute_rightInteractionCoefficient
        P Q hselfAdjoint hcommute component c c'
  change leftCoefficient * rightCoefficient *
      leftIsotypicSectorProjector P component =
    leftIsotypicSectorProjector P component * leftCoefficient * rightCoefficient
  calc
    leftCoefficient * rightCoefficient * leftIsotypicSectorProjector P component =
        leftCoefficient *
          (rightCoefficient * leftIsotypicSectorProjector P component) := by
            rw [mul_assoc]
    _ = leftCoefficient *
          (leftIsotypicSectorProjector P component * rightCoefficient) := by
            rw [hright.eq.symm]
    _ = (leftCoefficient * leftIsotypicSectorProjector P component) * rightCoefficient := by
            rw [← mul_assoc]
    _ = (leftIsotypicSectorProjector P component * leftCoefficient) * rightCoefficient := by
            rw [hleft.eq.symm]
    _ = leftIsotypicSectorProjector P component * leftCoefficient * rightCoefficient := by
            rw [mul_assoc]

/-- A nonzero triple-overlap operator has a nonzero double interaction coefficient. -/
theorem exists_nonzero_doubleInteractionCoefficient_of_ne_zero
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (T : Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem A B) C))
    (hT : T ≠ 0) :
    ∃ c c' : C, ∃ a a' : A,
      leftInteractionCoefficient (rightInteractionCoefficient T c c') a a' ≠ 0 := by
  by_contra h
  push_neg at h
  apply hT
  apply operator_eq_of_rightInteractionCoefficients_eq T 0
  intro c c'
  have hright : rightInteractionCoefficient T c c' = 0 := by
    apply operator_eq_of_leftInteractionCoefficients_eq
    intro a a'
    simpa [leftInteractionCoefficient] using h c c' a a'
  simpa [rightInteractionCoefficient] using hright

/-- The full first-cut overlap product in `((AB)C)D` coordinates. -/
noncomputable def firstCutCodeLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (M.fourFactorC region))
        (M.fourFactorD region)) :=
  overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region) *
    overlapLiftRight
      (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
      (M.fourFactorProjectorCDLocal region)

/-- The first-cut lift of one virtual `C` isotypic sector. -/
noncomputable def firstCutSectorLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) :
    Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (M.fourFactorC region))
        (M.fourFactorD region)) :=
  overlapLiftLeft (C := M.fourFactorD region)
    (TensorProduct.map
      (1 : Semantics.Operator
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)))
      (leftIsotypicSectorProjector (M.firstCutProjectorMC region) component))

/-- Global-to-first-cut coordinates, obtained by undoing the final associators. -/
noncomputable def firstCutGlobalCoordinateTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport L.Register
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (M.fourFactorC region))
        (M.fourFactorD region)) :=
  composeUnitaryTransport (M.fourFactorTransport region)
    (M.firstCutCoordinateTransport region).symm

/-- The global first-cut coordinates carry the full code projector to its overlap product. -/
theorem firstCutGlobalCoordinateTransport_conj_fullCodeProjector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutGlobalCoordinateTransport region).conjOperator M.fullCodeProjector =
      M.firstCutCodeLift region := by
  change (composeUnitaryTransport (M.fourFactorTransport region)
    (M.firstCutCoordinateTransport region).symm).conjOperator M.fullCodeProjector =
      M.firstCutCodeLift region
  rw [composeUnitaryTransport_conjOperator]
  calc
    (M.firstCutCoordinateTransport region).symm.conjOperator
        ((M.fourFactorTransport region).conjOperator M.fullCodeProjector) =
        (M.firstCutCoordinateTransport region).symm.conjOperator
          ((M.firstCutCoordinateTransport region).conjOperator
            (M.firstCutCodeLift region)) := by
      congr 1
      simpa [firstCutCodeLift] using
        (M.firstCutCoordinateTransport_conj_source_overlap_product region).symm
    _ = M.firstCutCodeLift region :=
      (M.firstCutCoordinateTransport region).symm_conjOperator_conjOperator _

/-- Physical external-boundary sector measurement in global first-cut coordinates. -/
theorem firstCutGlobalCoordinateTransport_conj_externalBoundarySector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) :
    (M.firstCutGlobalCoordinateTransport region).conjOperator
      ((M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
        ((M.fourFactorCCoordinateRelabel region).symm.conjOperator
          (leftIsotypicSectorProjector (M.firstCutProjectorMC region) component))) =
      M.firstCutSectorLift region component := by
  change (composeUnitaryTransport (M.fourFactorTransport region)
    (M.firstCutCoordinateTransport region).symm).conjOperator
      ((M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
        ((M.fourFactorCCoordinateRelabel region).symm.conjOperator
          (leftIsotypicSectorProjector (M.firstCutProjectorMC region) component))) =
      M.firstCutSectorLift region component
  rw [composeUnitaryTransport_conjOperator]
  simpa [firstCutSectorLift] using
    M.firstCutCoordinateTransport_symm_conj_externalBoundaryLift region
      (leftIsotypicSectorProjector (M.firstCutProjectorMC region) component)

set_option maxHeartbeats 800000 in
/--
The physical external-boundary dichotomy transported into first-cut
coordinates.  This is the exact `hsector` source for finite isotypic-sector
collapse.
-/
theorem firstCutCodeLift_sector_dichotomy
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region))
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) :
    M.firstCutCodeLift region * M.firstCutSectorLift region component = 0 ∨
      M.firstCutCodeLift region * M.firstCutSectorLift region component =
        M.firstCutCodeLift region := by
  let H := M.firstCutGlobalCoordinateTransport region
  let Zx : Semantics.Operator L.Register :=
    (M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
      ((M.fourFactorCCoordinateRelabel region).symm.conjOperator
        (leftIsotypicSectorProjector (M.firstCutProjectorMC region) component))
  have hHcode : H.conjOperator M.fullCodeProjector = M.firstCutCodeLift region := by
    simpa [H] using M.firstCutGlobalCoordinateTransport_conj_fullCodeProjector region
  have hHsector : H.conjOperator Zx = M.firstCutSectorLift region component := by
    simpa [H, Zx] using
      M.firstCutGlobalCoordinateTransport_conj_externalBoundarySector region component
  rcases M.firstCut_externalBoundary_sector_dichotomy region hC component with hzero | hfull
  · left
    calc
      M.firstCutCodeLift region * M.firstCutSectorLift region component =
          H.conjOperator M.fullCodeProjector * H.conjOperator Zx := by
        rw [hHcode, hHsector]
      _ = H.conjOperator (M.fullCodeProjector * Zx) :=
        (Semantics.UnitaryTransport.conjOperator_mul H _ _).symm
      _ = H.conjOperator 0 := congrArg H.conjOperator (by simpa [Zx] using hzero)
      _ = 0 := by simp [Semantics.UnitaryTransport.conjOperator]
  · right
    calc
      M.firstCutCodeLift region * M.firstCutSectorLift region component =
          H.conjOperator M.fullCodeProjector * H.conjOperator Zx := by
        rw [hHcode, hHsector]
      _ = H.conjOperator (M.fullCodeProjector * Zx) :=
        (Semantics.UnitaryTransport.conjOperator_mul H _ _).symm
      _ = H.conjOperator M.fullCodeProjector :=
        congrArg H.conjOperator (by simpa [Zx] using hfull)
      _ = M.firstCutCodeLift region := hHcode

set_option maxHeartbeats 2000000 in
/--
External-boundary recoverability makes every literal virtual `C` probe scalar
on the first-cut code lift.  The relation is obtained from the physical
external-boundary extension, then carried through the concrete first-cut
global coordinates.  It is the hC input for the residual `C'` no-cloning
factor, not merely the sector-measurement special case above.
-/
theorem firstCut_all_externalLocal_scalar_compression_of_externalBoundary_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region))
    (E : Semantics.Operator (M.fourFactorC region)) :
    ∃ scalar : Complex,
      M.firstCutCodeLift region *
          overlapLiftLeft (C := M.fourFactorD region)
            (TensorProduct.map
              (1 : Semantics.Operator
                (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) E) *
          M.firstCutCodeLift region = scalar • M.firstCutCodeLift region := by
  let S := M.regionSubsystem (M.externalBoundary region)
  let AB := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)
  let D := M.fourFactorD region
  let Elocal : Semantics.Operator S.selectedSystem :=
    (M.fourFactorCCoordinateRelabel region).symm.conjOperator E
  let Ephysical : Semantics.Operator L.Register := S.extendLocalToRegister Elocal
  let G := M.firstCutGlobalCoordinateTransport region
  let R := M.firstCutCodeLift region
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
    simpa [G, R] using M.firstCutGlobalCoordinateTransport_conj_fullCodeProjector region
  have hGlocal : G.conjOperator Ephysical =
      overlapLiftLeft (C := D) (TensorProduct.map (1 : Semantics.Operator AB) E) := by
    change (composeUnitaryTransport (M.fourFactorTransport region)
      (M.firstCutCoordinateTransport region).symm).conjOperator
        ((M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
          ((M.fourFactorCCoordinateRelabel region).symm.conjOperator E)) = _
    rw [composeUnitaryTransport_conjOperator]
    simpa [AB, D] using
      M.firstCutCoordinateTransport_symm_conj_externalBoundaryLift region E
  refine ⟨scalar, ?_⟩
  calc
    R * overlapLiftLeft (C := D) (TensorProduct.map (1 : Semantics.Operator AB) E) * R =
        G.conjOperator M.fullCodeProjector * G.conjOperator Ephysical *
          G.conjOperator M.fullCodeProjector := by
      rw [hGcode, hGlocal]
    _ = G.conjOperator (M.fullCodeProjector * Ephysical * M.fullCodeProjector) := by
      calc
        G.conjOperator M.fullCodeProjector * G.conjOperator Ephysical *
            G.conjOperator M.fullCodeProjector =
            G.conjOperator (M.fullCodeProjector * Ephysical) *
              G.conjOperator M.fullCodeProjector :=
          congrArg (fun operator => operator * G.conjOperator M.fullCodeProjector)
            (Semantics.UnitaryTransport.conjOperator_mul G M.fullCodeProjector Ephysical).symm
        _ = G.conjOperator ((M.fullCodeProjector * Ephysical) * M.fullCodeProjector) :=
          (Semantics.UnitaryTransport.conjOperator_mul G
            (M.fullCodeProjector * Ephysical) M.fullCodeProjector).symm
        _ = G.conjOperator (M.fullCodeProjector * Ephysical * M.fullCodeProjector) := rfl
    _ = G.conjOperator (scalar • M.fullCodeProjector) :=
      congrArg G.conjOperator hscalar'
    _ = scalar • G.conjOperator M.fullCodeProjector := by
      exact G.conjOperatorLinearMap.map_smul scalar M.fullCodeProjector
    _ = scalar • R := congrArg (fun operator => scalar • operator) hGcode
    _ = scalar • M.firstCutCodeLift region := rfl

/-- A double interaction coefficient of the first-cut full code overlap product. -/
noncomputable def firstCutDoubleInteractionCoefficient
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (d d' : M.fourFactorD region)
    (a a' : Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) :
    Semantics.Operator (M.fourFactorC region) :=
  leftInteractionCoefficient
    (rightInteractionCoefficient (M.firstCutCodeLift region) d d') a a'

/--
External-boundary correctability supplies the exact `hsector` premise for
every first-cut double coefficient.
-/
theorem firstCut_doubleInteractionCoefficient_sector_dichotomy
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region))
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (d d' : M.fourFactorD region)
    (a a' : Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) :
    M.firstCutDoubleInteractionCoefficient region d d' a a' *
        leftIsotypicSectorProjector (M.firstCutProjectorMC region) component = 0 ∨
      M.firstCutDoubleInteractionCoefficient region d d' a a' *
        leftIsotypicSectorProjector (M.firstCutProjectorMC region) component =
        M.firstCutDoubleInteractionCoefficient region d d' a a' := by
  rcases M.firstCutCodeLift_sector_dichotomy region hC component with hzero | hfull
  · left
    have hcoeff := congrArg (fun operator =>
      leftInteractionCoefficient (rightInteractionCoefficient operator d d') a a') hzero
    simp only [firstCutSectorLift, overlapLiftLeft] at hcoeff
    rw [rightInteractionCoefficient_mul_leftTensor,
      leftInteractionCoefficient_mul_rightTensor] at hcoeff
    rw [rightInteractionCoefficient_zero, leftInteractionCoefficient_zero] at hcoeff
    exact hcoeff
  · right
    have hcoeff := congrArg (fun operator =>
      leftInteractionCoefficient (rightInteractionCoefficient operator d d') a a') hfull
    simp only [firstCutSectorLift, overlapLiftLeft] at hcoeff
    rw [rightInteractionCoefficient_mul_leftTensor,
      leftInteractionCoefficient_mul_rightTensor] at hcoeff
    exact hcoeff

/-- A zero first-cut code sector forces every corresponding double coefficient to vanish. -/
theorem firstCutCodeLift_sector_eq_zero_implies_doubleInteractionCoefficient_zero
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (d d' : M.fourFactorD region)
    (a a' : Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
    (hzero : M.firstCutCodeLift region * M.firstCutSectorLift region component = 0) :
    M.firstCutDoubleInteractionCoefficient region d d' a a' *
        leftIsotypicSectorProjector (M.firstCutProjectorMC region) component = 0 := by
  have hcoeff := congrArg (fun operator =>
    leftInteractionCoefficient (rightInteractionCoefficient operator d d') a a') hzero
  simp only [firstCutSectorLift, overlapLiftLeft] at hcoeff
  rw [rightInteractionCoefficient_mul_leftTensor,
    leftInteractionCoefficient_mul_rightTensor] at hcoeff
  rw [rightInteractionCoefficient_zero, leftInteractionCoefficient_zero] at hcoeff
  exact hcoeff

/-- A full first-cut code sector fixes every corresponding double coefficient. -/
theorem firstCutCodeLift_sector_eq_codeLift_implies_doubleInteractionCoefficient_eq
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (d d' : M.fourFactorD region)
    (a a' : Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
    (hfull : M.firstCutCodeLift region * M.firstCutSectorLift region component =
      M.firstCutCodeLift region) :
    M.firstCutDoubleInteractionCoefficient region d d' a a' *
        leftIsotypicSectorProjector (M.firstCutProjectorMC region) component =
      M.firstCutDoubleInteractionCoefficient region d d' a a' := by
  have hcoeff := congrArg (fun operator =>
    leftInteractionCoefficient (rightInteractionCoefficient operator d d') a a') hfull
  simp only [firstCutSectorLift, overlapLiftLeft] at hcoeff
  rw [rightInteractionCoefficient_mul_leftTensor,
    leftInteractionCoefficient_mul_rightTensor] at hcoeff
  exact hcoeff

/--
For a nonzero double coefficient, an inactive coefficient sector cannot arise
from a full code sector.  Thus the physical first-cut sector is zero as well.
-/
theorem firstCut_doubleInteractionCoefficient_sector_eq_zero_implies_codeLift_sector_eq_zero
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region))
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (d d' : M.fourFactorD region)
    (a a' : Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
    (hnonzero : M.firstCutDoubleInteractionCoefficient region d d' a a' ≠ 0)
    (hzero : M.firstCutDoubleInteractionCoefficient region d d' a a' *
      leftIsotypicSectorProjector (M.firstCutProjectorMC region) component = 0) :
    M.firstCutCodeLift region * M.firstCutSectorLift region component = 0 := by
  rcases M.firstCutCodeLift_sector_dichotomy region hC component with hcodeZero | hcodeFull
  · exact hcodeZero
  · exfalso
    have hcoefficientFull :=
      M.firstCutCodeLift_sector_eq_codeLift_implies_doubleInteractionCoefficient_eq
        region component d d' a a' hcodeFull
    rw [hzero] at hcoefficientFull
    exact hnonzero hcoefficientFull.symm

set_option maxHeartbeats 800000 in
/--
For a nonempty code, external-boundary correctability leaves exactly one
first-cut left-isotypic sector active.  The proof calls the generic finite
sector-collapse theorem on a nonzero double coefficient of the actual full
first-cut code projector, then promotes that coefficient conclusion back to
the full projector using the physical-sector dichotomy above.
-/
theorem firstCut_exists_unique_active_leftIsotypicSector_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region)) :
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
  have hcodeLiftNonzero : M.firstCutCodeLift region ≠ 0 := by
    intro hzero
    apply hfullNonzero
    calc
      M.fullCodeProjector =
          (M.firstCutGlobalCoordinateTransport region).symm.conjOperator
            ((M.firstCutGlobalCoordinateTransport region).conjOperator
              M.fullCodeProjector) :=
        (M.firstCutGlobalCoordinateTransport region).symm_conjOperator_conjOperator _ |>.symm
      _ = (M.firstCutGlobalCoordinateTransport region).symm.conjOperator
            (M.firstCutCodeLift region) := by
        rw [M.firstCutGlobalCoordinateTransport_conj_fullCodeProjector]
      _ = (M.firstCutGlobalCoordinateTransport region).symm.conjOperator 0 :=
        congrArg (M.firstCutGlobalCoordinateTransport region).symm.conjOperator hzero
      _ = 0 := by simp [Semantics.UnitaryTransport.conjOperator]
  rcases exists_nonzero_doubleInteractionCoefficient_of_ne_zero
    (M.firstCutCodeLift region) hcodeLiftNonzero with ⟨d, d', a, a', hcoefficient⟩
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
  let coefficient := M.firstCutDoubleInteractionCoefficient region d d' a a'
  have hcoefficient' : coefficient ≠ 0 := by
    change leftInteractionCoefficient
      (rightInteractionCoefficient (M.firstCutCodeLift region) d d') a a' ≠ 0
    exact hcoefficient
  have hcommute : ∀ component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region),
      Commute coefficient
        (leftIsotypicSectorProjector (M.firstCutProjectorMC region) component) := by
    intro component
    simpa [coefficient, firstCutDoubleInteractionCoefficient, firstCutCodeLift] using
      (doubleInteractionCoefficient_commutes_leftIsotypicSector
        (M.firstCutProjectorMC region) (M.fourFactorProjectorCDLocal region)
        hself hover component d d' a a')
  have hsector : ∀ component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region),
      coefficient * leftIsotypicSectorProjector (M.firstCutProjectorMC region) component = 0 ∨
        coefficient * leftIsotypicSectorProjector (M.firstCutProjectorMC region) component =
          coefficient := by
    intro component
    simpa [coefficient] using
      M.firstCut_doubleInteractionCoefficient_sector_dichotomy
        region hC component d d' a a'
  rcases exists_unique_active_leftIsotypicSector
    (M.firstCutProjectorMC region) coefficient hcoefficient' hcommute hsector with
    ⟨component, hactive, hother⟩
  refine ⟨component, ?_, ?_⟩
  · rcases M.firstCutCodeLift_sector_dichotomy region hC component with hzero | hfull
    · exfalso
      have hvanish : coefficient *
          leftIsotypicSectorProjector (M.firstCutProjectorMC region) component = 0 := by
        change M.firstCutDoubleInteractionCoefficient region d d' a a' *
          leftIsotypicSectorProjector (M.firstCutProjectorMC region) component = 0
        exact M.firstCutCodeLift_sector_eq_zero_implies_doubleInteractionCoefficient_zero
          region component d d' a a' hzero
      rw [hactive] at hvanish
      exact hcoefficient' hvanish
    · exact hfull
  · intro other hne
    have hvanish : coefficient *
        leftIsotypicSectorProjector (M.firstCutProjectorMC region) other = 0 :=
      hother other hne
    change M.firstCutCodeLift region * M.firstCutSectorLift region other = 0
    apply M.firstCut_doubleInteractionCoefficient_sector_eq_zero_implies_codeLift_sector_eq_zero
      region hC other d d' a a' hcoefficient'
    change coefficient * leftIsotypicSectorProjector (M.firstCutProjectorMC region) other = 0
    exact hvanish


end BPTCommutingProjectorModel

end Bounds
end QEC
