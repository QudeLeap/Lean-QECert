import QEC.Bounds.BPTDisentangling.ScalarCompression.Core

/-!
# BPT joint-sector embeddings

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
The two literal BPT cut lifts are the same physical code operator, related by
the explicit associator from `((AB)C)D` to `(AB)(CD)`.  This is the concrete
first/second-cut equality from which the joint-sector `Theta tensor Pi_C''D`
block must be reconstructed; no tensor factorization is assumed here.
-/
theorem secondCutCodeLift_eq_reassociate_firstCutCodeLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (tensorAssociatorUnitary
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
      (M.fourFactorC region) (M.fourFactorD region)).conjOperator
        (M.firstCutCodeLift region) = M.secondCutCodeLift region := by
  let A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)
  let C := M.fourFactorC region
  let D := M.fourFactorD region
  let reassociate := tensorAssociatorUnitary A C D
  let second := M.secondCutCoordinateTransport region
  have hfirst : (composeUnitaryTransport reassociate second).conjOperator
      (M.firstCutCodeLift region) =
        (M.fourFactorTransport region).conjOperator M.fullCodeProjector := by
    exact M.firstCutCoordinateTransport_conj_source_overlap_product region
  have hsecond : second.conjOperator (M.secondCutCodeLift region) =
      (M.fourFactorTransport region).conjOperator M.fullCodeProjector := by
    simpa [second] using M.secondCutCoordinateTransport_conj_source_overlap_product region
  calc
    reassociate.conjOperator (M.firstCutCodeLift region) =
        second.symm.conjOperator
          (second.conjOperator (reassociate.conjOperator (M.firstCutCodeLift region))) :=
      (second.symm_conjOperator_conjOperator _).symm
    _ = second.symm.conjOperator
        ((composeUnitaryTransport reassociate second).conjOperator (M.firstCutCodeLift region)) := by
      rw [composeUnitaryTransport_conjOperator]
    _ = second.symm.conjOperator
        ((M.fourFactorTransport region).conjOperator M.fullCodeProjector) :=
      congrArg second.symm.conjOperator hfirst
    _ = second.symm.conjOperator (second.conjOperator (M.secondCutCodeLift region)) := by
      rw [hsecond]
    _ = M.secondCutCodeLift region := second.symm_conjOperator_conjOperator _

/--
Embed simultaneous `B`- and `C`-isotypic subspaces into the left-associated
four-factor source coordinates `((AB)C)D`.
-/
noncomputable def jointBCSectorEmbeddingLeft
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C) :
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (Semantics.CompositeSystem A pB) pC) D) →ₗ[Complex]
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (Semantics.CompositeSystem A B) C) D) :=
  TensorProduct.map
    (TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) pB.subtype) pC.subtype)
    (1 : Semantics.Operator D)

/-- The corresponding simultaneous-sector embedding in `(AB)(CD)` coordinates. -/
noncomputable def jointBCSectorEmbeddingRight
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C) :
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem A pB) (Semantics.CompositeSystem pC D)) →ₗ[Complex]
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem A B) (Semantics.CompositeSystem C D)) :=
  TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) pB.subtype)
    (TensorProduct.map pC.subtype (1 : Semantics.Operator D))

@[simp]
theorem jointBCSectorEmbeddingLeft_apply_tmul
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (a : A) (b : pB) (c : pC) (d : D) :
    jointBCSectorEmbeddingLeft pB pC (((a ⊗ₜ[Complex] b) ⊗ₜ[Complex] c) ⊗ₜ[Complex] d) =
      ((a ⊗ₜ[Complex] b.1) ⊗ₜ[Complex] c.1) ⊗ₜ[Complex] d := by
  rfl

@[simp]
theorem jointBCSectorEmbeddingRight_apply_tmul
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (a : A) (b : pB) (c : pC) (d : D) :
    jointBCSectorEmbeddingRight pB pC ((a ⊗ₜ[Complex] b) ⊗ₜ[Complex] (c ⊗ₜ[Complex] d)) =
      (a ⊗ₜ[Complex] b.1) ⊗ₜ[Complex] (c.1 ⊗ₜ[Complex] d) := by
  rfl

/--
The simultaneous `B,C` sector embedding in `(AB)(CD)` coordinates followed
by its adjoint is exactly the product of the two sector projectors.
-/
theorem jointBCSectorEmbeddingRight_comp_adjoint_eq_sectorProjectorProduct
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C) :
    (jointBCSectorEmbeddingRight pB pC).comp
      (LinearMap.adjoint (jointBCSectorEmbeddingRight pB pC)) =
      TensorProduct.map
        (TensorProduct.map (1 : Semantics.Operator A) pB.starProjection.toLinearMap)
        (TensorProduct.map pC.starProjection.toLinearMap (1 : Semantics.Operator D)) := by
  unfold jointBCSectorEmbeddingRight
  simp only [TensorProduct.adjoint_map, LinearMap.adjoint_one]
  rw [← TensorProduct.map_comp]
  rw [← TensorProduct.map_comp]
  rw [← TensorProduct.map_comp]
  rw [submoduleSubtype_comp_adjoint_eq_starProjection,
    submoduleSubtype_comp_adjoint_eq_starProjection]
  rfl

/--
Embed the simultaneous active `B,C` sector directly into canonical
`A tensor (B tensor (C tensor D))` four-factor coordinates.
-/
noncomputable def fourFactorJointBCSectorEmbedding
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C) :
    (Semantics.CompositeSystem (Semantics.CompositeSystem A pB)
      (Semantics.CompositeSystem pC D)) →ₗ[Complex]
      (Semantics.CompositeSystem A
        (Semantics.CompositeSystem B (Semantics.CompositeSystem C D))) :=
  (tensorAssociatorUnitary A B (Semantics.CompositeSystem C D)).toLinearEquiv.toLinearMap.comp
    (jointBCSectorEmbeddingRight pB pC)

/--
Conjugate a `B tensor C` unitary into canonical four-factor coordinates.  This
is the coordinate-side counterpart of the physical boundary lift used in D5.
-/
noncomputable def fourFactorBCUnitaryTransport
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (E : Semantics.UnitaryTransport (Semantics.CompositeSystem B C)
      (Semantics.CompositeSystem B C)) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem A (Semantics.CompositeSystem B (Semantics.CompositeSystem C D)))
      (Semantics.CompositeSystem A (Semantics.CompositeSystem B (Semantics.CompositeSystem C D))) :=
  conjugateUnitaryTransport
    (unitaryLTensor A (tensorAssociatorUnitary B C D).symm)
    (unitaryLTensor A (unitaryRTensor E D))

/--
Embed the joint active sector after reassociating the middle physical `B,C`
factors.  It is the bridge between the D4 joint embedding and D3's BC lift.
-/
noncomputable def jointBCSectorMiddleEmbedding
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C) :
    (Semantics.CompositeSystem A
      (Semantics.CompositeSystem (Semantics.CompositeSystem pB pC) D)) →ₗ[Complex]
      (Semantics.CompositeSystem A
        (Semantics.CompositeSystem (Semantics.CompositeSystem B C) D)) :=
  TensorProduct.map (1 : Semantics.Operator A)
    (TensorProduct.map (submoduleTensorEmbedding pB pC).toLinearMap
      (1 : Semantics.Operator D))

/--
Reassociate a joint active-sector state so that its `pB tensor pC` factor is
exposed between the outer `A,D` spectators.
-/
noncomputable def jointBCSectorMiddleTransport
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem (Semantics.CompositeSystem A pB)
        (Semantics.CompositeSystem pC D))
      (Semantics.CompositeSystem A
        (Semantics.CompositeSystem (Semantics.CompositeSystem pB pC) D)) :=
  composeUnitaryTransport
    (tensorAssociatorUnitary A pB (Semantics.CompositeSystem pC D))
    (unitaryLTensor A (tensorAssociatorUnitary pB pC D).symm)

/--
The active-sector unitary induced by a `pB tensor pC` operation after the
same reassociation as `jointBCSectorMiddleTransport`.
-/
noncomputable def jointBCSectorActiveUnitary
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (V : Semantics.UnitaryTransport (Semantics.CompositeSystem pB pC)
      (Semantics.CompositeSystem pB pC)) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem (Semantics.CompositeSystem A pB)
        (Semantics.CompositeSystem pC D))
      (Semantics.CompositeSystem (Semantics.CompositeSystem A pB)
        (Semantics.CompositeSystem pC D)) :=
  conjugateUnitaryTransport (jointBCSectorMiddleTransport pB pC)
    (unitaryLTensor A (unitaryRTensor V D))

/--
The canonical joint active embedding factors through the parenthesization
which exposes the physical `B tensor C` middle factor.
-/
theorem fourFactorJointBCSectorEmbedding_factor_through_middle
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C) :
    fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC =
      (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).symm.toLinearEquiv.toLinearMap.comp
        ((jointBCSectorMiddleEmbedding (A := A) (D := D) pB pC).comp
          (jointBCSectorMiddleTransport (A := A) pB pC).toLinearEquiv.toLinearMap) := by
  let L := fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC
  let R := (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).symm.toLinearEquiv.toLinearMap.comp
    ((jointBCSectorMiddleEmbedding (A := A) (D := D) pB pC).comp
      (jointBCSectorMiddleTransport (A := A) pB pC).toLinearEquiv.toLinearMap)
  apply LinearMap.ext
  intro vector
  change L vector = R vector
  induction vector using TensorProduct.induction_on with
  | zero => exact L.map_zero.trans R.map_zero.symm
  | tmul ab cd =>
      induction ab using TensorProduct.induction_on with
      | zero =>
          simpa only [TensorProduct.zero_tmul] using L.map_zero.trans R.map_zero.symm
      | tmul a b =>
          induction cd using TensorProduct.induction_on with
          | zero =>
              simpa only [TensorProduct.tmul_zero] using L.map_zero.trans R.map_zero.symm
          | tmul c d => rfl
          | add first second hfirst hsecond =>
              simpa only [TensorProduct.tmul_add, map_add] using
                congrArg₂ (· + ·) hfirst hsecond
      | add first second hfirst hsecond =>
          simpa only [TensorProduct.add_tmul, map_add] using
            congrArg₂ (· + ·) hfirst hsecond
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

/-- Pointwise form of the preceding joint-embedding factorization. -/
theorem fourFactorJointBCSectorEmbedding_apply_factor_through_middle
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (x : Semantics.CompositeSystem (Semantics.CompositeSystem A pB)
      (Semantics.CompositeSystem pC D)) :
    fourFactorJointBCSectorEmbedding pB pC x =
      (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).symm
        (jointBCSectorMiddleEmbedding pB pC (jointBCSectorMiddleTransport pB pC x)) := by
  exact congrArg (fun f => f x)
    (fourFactorJointBCSectorEmbedding_factor_through_middle
      (A := A) (B := B) (C := C) (D := D) pB pC)

/--
Tensoring an intertwining of the physical `B,C` sector embedding with the
outer spectators gives the corresponding middle-coordinate intertwining.
-/
theorem fourFactorBCUnitaryTransport_middle_intertwines_jointBCSectorMiddleEmbedding
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (E : Semantics.UnitaryTransport (Semantics.CompositeSystem B C)
      (Semantics.CompositeSystem B C))
    (V : Semantics.UnitaryTransport (Semantics.CompositeSystem pB pC)
      (Semantics.CompositeSystem pB pC))
    (hintertwines : E.toLinearEquiv.toLinearMap.comp (submoduleTensorEmbedding pB pC).toLinearMap =
      (submoduleTensorEmbedding pB pC).toLinearMap.comp V.toLinearEquiv.toLinearMap) :
    (unitaryLTensor A (unitaryRTensor E D)).toLinearEquiv.toLinearMap.comp
        (jointBCSectorMiddleEmbedding (A := A) (D := D) pB pC) =
      (jointBCSectorMiddleEmbedding (A := A) (D := D) pB pC).comp
        (unitaryLTensor A (unitaryRTensor V D)).toLinearEquiv.toLinearMap := by
  let L := (unitaryLTensor A (unitaryRTensor E D)).toLinearEquiv.toLinearMap.comp
    (jointBCSectorMiddleEmbedding (A := A) (D := D) pB pC)
  let R := (jointBCSectorMiddleEmbedding (A := A) (D := D) pB pC).comp
    (unitaryLTensor A (unitaryRTensor V D)).toLinearEquiv.toLinearMap
  apply LinearMap.ext
  intro vector
  change L vector = R vector
  induction vector using TensorProduct.induction_on with
  | zero => exact L.map_zero.trans R.map_zero.symm
  | tmul a bcd =>
      induction bcd using TensorProduct.induction_on with
      | zero =>
          simpa only [TensorProduct.tmul_zero] using L.map_zero.trans R.map_zero.symm
      | tmul bc d =>
          induction bc using TensorProduct.induction_on with
          | zero =>
              simpa only [TensorProduct.zero_tmul, TensorProduct.tmul_zero] using
                L.map_zero.trans R.map_zero.symm
          | tmul b c =>
              have hbc := congrArg (fun map => map (b ⊗ₜ[Complex] c)) hintertwines
              simpa [L, R, jointBCSectorMiddleEmbedding, unitaryLTensor, unitaryRTensor,
                unitaryTransportOfLinearIsometryEquiv, submoduleTensorEmbedding] using
                congrArg (fun x => a ⊗ₜ[Complex] (x ⊗ₜ[Complex] d)) hbc
          | add first second hfirst hsecond =>
              simpa only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add] using
                congrArg₂ (· + ·) hfirst hsecond
      | add first second hfirst hsecond =>
          simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hfirst hsecond
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

/--
The four-factor lift of a physical `B,C` unitary intertwines the joint active
embedding with its prescribed active-sector coordinate action.
-/
theorem fourFactorBCUnitaryTransport_intertwines_jointBCSectorEmbedding
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (E : Semantics.UnitaryTransport (Semantics.CompositeSystem B C)
      (Semantics.CompositeSystem B C))
    (V : Semantics.UnitaryTransport (Semantics.CompositeSystem pB pC)
      (Semantics.CompositeSystem pB pC))
    (hintertwines : E.toLinearEquiv.toLinearMap.comp (submoduleTensorEmbedding pB pC).toLinearMap =
      (submoduleTensorEmbedding pB pC).toLinearMap.comp V.toLinearEquiv.toLinearMap) :
    (fourFactorBCUnitaryTransport (A := A) (D := D) E).toLinearEquiv.toLinearMap.comp
        (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC) =
      (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC).comp
        (jointBCSectorActiveUnitary (A := A) pB pC V).toLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro vector
  change fourFactorBCUnitaryTransport E (fourFactorJointBCSectorEmbedding pB pC vector) =
    fourFactorJointBCSectorEmbedding pB pC (jointBCSectorActiveUnitary pB pC V vector)
  calc
    fourFactorBCUnitaryTransport E (fourFactorJointBCSectorEmbedding pB pC vector) =
        fourFactorBCUnitaryTransport E
          ((unitaryLTensor A (tensorAssociatorUnitary B C D).symm).symm
            (jointBCSectorMiddleEmbedding pB pC (jointBCSectorMiddleTransport pB pC vector))) := by
          rw [fourFactorJointBCSectorEmbedding_apply_factor_through_middle]
    _ = (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).symm
          (unitaryLTensor A (unitaryRTensor E D)
            (jointBCSectorMiddleEmbedding pB pC (jointBCSectorMiddleTransport pB pC vector))) := by
          rw [fourFactorBCUnitaryTransport, conjugateUnitaryTransport_apply]
          simp
    _ = (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).symm
          (jointBCSectorMiddleEmbedding pB pC
            (unitaryLTensor A (unitaryRTensor V D) (jointBCSectorMiddleTransport pB pC vector))) := by
          have hmiddle := congrArg
            (fun map => map (jointBCSectorMiddleTransport pB pC vector))
            (fourFactorBCUnitaryTransport_middle_intertwines_jointBCSectorMiddleEmbedding
              (A := A) (D := D) pB pC E V hintertwines)
          apply congrArg (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).symm
          exact hmiddle
    _ = (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).symm
          (jointBCSectorMiddleEmbedding pB pC
            (jointBCSectorMiddleTransport pB pC
              ((jointBCSectorMiddleTransport pB pC).symm
                (unitaryLTensor A (unitaryRTensor V D)
                  (jointBCSectorMiddleTransport pB pC vector))))) := by
          simp
    _ = fourFactorJointBCSectorEmbedding pB pC
          ((jointBCSectorMiddleTransport pB pC).symm
            (unitaryLTensor A (unitaryRTensor V D)
              (jointBCSectorMiddleTransport pB pC vector))) := by
          symm
          simpa using fourFactorJointBCSectorEmbedding_apply_factor_through_middle pB pC
            ((jointBCSectorMiddleTransport pB pC).symm
              (unitaryLTensor A (unitaryRTensor V D)
                (jointBCSectorMiddleTransport pB pC vector)))
    _ = fourFactorJointBCSectorEmbedding pB pC (jointBCSectorActiveUnitary pB pC V vector) := by
          rw [jointBCSectorActiveUnitary, conjugateUnitaryTransport_apply]

/--
Compression after ambient unitary conjugation is conjugation of the compressed
operator whenever the unitary intertwines the embedding.
-/
theorem conjOperator_compression_of_intertwining
    {S H : Type u} [NormedAddCommGroup S] [InnerProductSpace Complex S]
    [Semantics.FiniteQuantumSystem S] [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (J : S →ₗ[Complex] H)
    (F : Semantics.UnitaryTransport H H) (W : Semantics.UnitaryTransport S S)
    (hintertwines : F.toLinearEquiv.toLinearMap.comp J = J.comp W.toLinearEquiv.toLinearMap)
    (P : Semantics.Operator H) :
    (LinearMap.adjoint J).comp ((F.conjOperator P).comp J) =
      W.conjOperator ((LinearMap.adjoint J).comp (P.comp J)) := by
  have hintertwines_apply (x : S) : F (J x) = J (W x) := by
    exact congrArg (fun f => f x) hintertwines
  have hsymm : F.symm.toLinearEquiv.toLinearMap.comp J =
      J.comp W.symm.toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    intro x
    have h := congrArg (fun y => F.symm y) (hintertwines_apply (W.symm x))
    simpa using h.symm
  have hFsymmAdj : LinearMap.adjoint F.symm.toLinearEquiv.toLinearMap =
      F.toLinearEquiv.toLinearMap := by
    rw [Semantics.UnitaryTransport.symm_toLinearEquiv]
    exact F.adjoint_symm_toLinearMap
  have hWsymmAdj : LinearMap.adjoint W.symm.toLinearEquiv.toLinearMap =
      W.toLinearEquiv.toLinearMap := by
    rw [Semantics.UnitaryTransport.symm_toLinearEquiv]
    exact W.adjoint_symm_toLinearMap
  have hleft := congrArg LinearMap.adjoint hsymm
  rw [LinearMap.adjoint_comp, hFsymmAdj, LinearMap.adjoint_comp, hWsymmAdj] at hleft
  calc
    (LinearMap.adjoint J).comp ((F.conjOperator P).comp J) =
        ((LinearMap.adjoint J).comp F.toLinearEquiv.toLinearMap).comp
          (P.comp (F.symm.toLinearEquiv.toLinearMap.comp J)) := by
          simp only [Semantics.UnitaryTransport.conjOperator,
            Semantics.UnitaryTransport.symm_toLinearEquiv, LinearMap.comp_assoc]
    _ = (W.toLinearEquiv.toLinearMap.comp (LinearMap.adjoint J)).comp
          (P.comp (J.comp W.symm.toLinearEquiv.toLinearMap)) := by
          rw [hleft, hsymm]
    _ = W.conjOperator ((LinearMap.adjoint J).comp (P.comp J)) := by
          simp only [Semantics.UnitaryTransport.conjOperator,
            Semantics.UnitaryTransport.symm_toLinearEquiv, LinearMap.comp_assoc]

/--
The preceding two intertwining lemmas give the exact D3/D4 compressed-block
transport in canonical four-factor coordinates.
-/
theorem fourFactorBCUnitaryTransport_conjOperator_compression
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (E : Semantics.UnitaryTransport (Semantics.CompositeSystem B C)
      (Semantics.CompositeSystem B C))
    (V : Semantics.UnitaryTransport (Semantics.CompositeSystem pB pC)
      (Semantics.CompositeSystem pB pC))
    (hintertwines : E.toLinearEquiv.toLinearMap.comp (submoduleTensorEmbedding pB pC).toLinearMap =
      (submoduleTensorEmbedding pB pC).toLinearMap.comp V.toLinearEquiv.toLinearMap)
    (P : Semantics.Operator
      (Semantics.CompositeSystem A (Semantics.CompositeSystem B (Semantics.CompositeSystem C D)))) :
    (LinearMap.adjoint (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC)).comp
        (((fourFactorBCUnitaryTransport (A := A) (D := D) E).conjOperator P).comp
          (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC)) =
      (jointBCSectorActiveUnitary (A := A) pB pC V).conjOperator
        ((LinearMap.adjoint (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC)).comp
          (P.comp (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC))) := by
  exact conjOperator_compression_of_intertwining
    (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC)
    (fourFactorBCUnitaryTransport (A := A) (D := D) E)
    (jointBCSectorActiveUnitary (A := A) pB pC V)
    (fourFactorBCUnitaryTransport_intertwines_jointBCSectorEmbedding
      (A := A) (D := D) pB pC E V hintertwines) P


end BPTCommutingProjectorModel

end Bounds
end QEC
