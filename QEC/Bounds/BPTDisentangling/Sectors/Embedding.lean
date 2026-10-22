import QEC.Bounds.BPTDisentangling.Sectors.Selection

/-!
# BPT compressed sector blocks

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
The concrete inclusion of a middle subspace into a three-factor Hilbert
space.  The active BPT isotypic sector is substituted for `p` immediately in
the overlap-block reconstruction below.
-/
noncomputable def tensorTripleSubtypeEmbedding
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (p : Submodule Complex B) :
    (Semantics.CompositeSystem (Semantics.CompositeSystem A p) C) →ₗ[Complex]
      Semantics.CompositeSystem (Semantics.CompositeSystem A B) C :=
  TensorProduct.map
    (TensorProduct.map (1 : Semantics.Operator A) p.subtype)
    (1 : Semantics.Operator C)

/-- The adjoint of a finite-dimensional subspace inclusion is a left inverse. -/
theorem adjoint_submoduleSubtype_comp_subtype_eq_one
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (p : Submodule Complex H) :
    (LinearMap.adjoint p.subtype).comp p.subtype = (1 : Semantics.Operator p) := by
  apply LinearMap.ext
  intro vector
  change LinearMap.adjoint p.subtype (p.subtype vector) = vector
  exact adjoint_submoduleSubtype_apply_subtype p vector

/-- The inclusion followed by its adjoint is the orthogonal sector projector. -/
theorem submoduleSubtype_comp_adjoint_eq_starProjection
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (p : Submodule Complex H) :
    p.subtype.comp (LinearMap.adjoint p.subtype) = p.starProjection.toLinearMap := by
  apply LinearMap.ext
  intro vector
  change p.subtype (LinearMap.adjoint p.subtype vector) = p.starProjection vector
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact p.coe_mem _
  · intro test htest
    let testInSubmodule : p := ⟨test, htest⟩
    have hinner :
        inner Complex (p.subtype (LinearMap.adjoint p.subtype vector)) test =
          inner Complex vector test := by
      calc
        inner Complex (p.subtype (LinearMap.adjoint p.subtype vector)) test =
            inner Complex (LinearMap.adjoint p.subtype vector) testInSubmodule := rfl
        _ = inner Complex vector (p.subtype testInSubmodule) :=
          LinearMap.adjoint_inner_left p.subtype testInSubmodule vector
        _ = inner Complex vector test := rfl
    rw [inner_sub_left, hinner, sub_self]

/--
The finite triple embedding is an isometry.  This is the first half of the
active-block reconstruction: the compressed overlap projector can be returned
to the physical three-factor space without altering vectors in its sector.
-/
theorem adjoint_tensorTripleSubtypeEmbedding_comp_tensorTripleSubtypeEmbedding
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (p : Submodule Complex B) :
    (LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C) p)).comp
      (tensorTripleSubtypeEmbedding (A := A) (C := C) p) =
        (1 : Semantics.Operator
          (Semantics.CompositeSystem (Semantics.CompositeSystem A p) C)) := by
  unfold tensorTripleSubtypeEmbedding
  simp only [TensorProduct.adjoint_map, LinearMap.adjoint_one]
  rw [← TensorProduct.map_comp]
  rw [← TensorProduct.map_comp]
  rw [adjoint_submoduleSubtype_comp_subtype_eq_one p]
  change TensorProduct.map (TensorProduct.map (LinearMap.id.comp LinearMap.id) LinearMap.id)
      (LinearMap.id.comp LinearMap.id) = LinearMap.id
  rw [LinearMap.id_comp, LinearMap.id_comp]
  have hinner :
      TensorProduct.map
        (LinearMap.id : Semantics.Operator A)
        (LinearMap.id : Semantics.Operator p) =
          (1 : Semantics.Operator (Semantics.CompositeSystem A p)) :=
    TensorProduct.map_one
  rw [hinner]
  exact TensorProduct.map_one

/--
Returning from a subspace coordinate by its adjoint gives the literal tensor
extension of that subspace's orthogonal projector.  This is the second half
of the active-block reconstruction and is used to turn `Pi * sector = Pi`
into an equality with the compressed BV03 block product.
-/
theorem tensorTripleSubtypeEmbedding_comp_adjoint_eq_sectorLift
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (p : Submodule Complex B) :
    (tensorTripleSubtypeEmbedding (A := A) (C := C) p).comp
      (LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C) p)) =
        TensorProduct.map
          (TensorProduct.map (1 : Semantics.Operator A) p.starProjection.toLinearMap)
          (1 : Semantics.Operator C) := by
  unfold tensorTripleSubtypeEmbedding
  simp only [TensorProduct.adjoint_map, LinearMap.adjoint_one]
  rw [← TensorProduct.map_comp]
  rw [← TensorProduct.map_comp]
  rw [submoduleSubtype_comp_adjoint_eq_starProjection p]
  change TensorProduct.map
      (TensorProduct.map (LinearMap.id.comp LinearMap.id) p.starProjection.toLinearMap)
      (LinearMap.id.comp LinearMap.id) =
        TensorProduct.map (TensorProduct.map LinearMap.id p.starProjection.toLinearMap)
          LinearMap.id
  rw [LinearMap.id_comp, LinearMap.id_comp]

/--
For an isotypic component, the embedding followed by its adjoint is precisely
the physical lift of the local BV03 sector projector.  This connects the
subtype coordinate used by the block theorem to the sector selected by the
correctability argument.
-/
theorem tensorTripleSubtypeEmbedding_comp_adjoint_eq_leftIsotypicSectorLift
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    (tensorTripleSubtypeEmbedding (A := A) (C := C)
      (component.1.restrictScalars Complex)).comp
        (LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C)
          (component.1.restrictScalars Complex))) =
      overlapLiftLeft (C := C)
        (TensorProduct.map (1 : Semantics.Operator A)
          (leftIsotypicSectorProjector P component)) := by
  simpa [tensorTripleSubtypeEmbedding, overlapLiftLeft, leftIsotypicSectorProjector] using
    (tensorTripleSubtypeEmbedding_comp_adjoint_eq_sectorLift
      (A := A) (C := C) (component.1.restrictScalars Complex))

/--
An active isotypic sector reconstructs the full commuting-overlap product from
its compression to that sector.  The following tensor-block step applies the
BV03 unitary to this literal compressed operator, so this is the direct bridge
from correctability-selected support to the source projector factorization.
-/
theorem active_overlap_product_eq_isotypic_embedding_compression
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B)
    (hactive :
      (overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q) *
          overlapLiftLeft (C := C)
            (TensorProduct.map (1 : Semantics.Operator A)
              (leftIsotypicSectorProjector P component)) =
        overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q) :
    overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q =
      (tensorTripleSubtypeEmbedding (A := A) (C := C)
        (component.1.restrictScalars Complex)).comp
        (((LinearMap.adjoint
          (tensorTripleSubtypeEmbedding (A := A) (C := C)
            (component.1.restrictScalars Complex))).comp
          ((overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q).comp
            (tensorTripleSubtypeEmbedding (A := A) (C := C)
              (component.1.restrictScalars Complex)))).comp
          (LinearMap.adjoint
            (tensorTripleSubtypeEmbedding (A := A) (C := C)
              (component.1.restrictScalars Complex)))) := by
  let J := tensorTripleSubtypeEmbedding (A := A) (C := C)
    (component.1.restrictScalars Complex)
  let R := overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q
  let S := overlapLiftLeft (C := C)
    (TensorProduct.map (1 : Semantics.Operator A)
      (leftIsotypicSectorProjector P component))
  have hsector : J.comp (LinearMap.adjoint J) = S := by
    dsimp [J, S]
    exact tensorTripleSubtypeEmbedding_comp_adjoint_eq_leftIsotypicSectorLift P component
  have hcommuteSector : Commute R S := by
    dsimp [R, S]
    exact overlap_product_commutes_leftIsotypicSectorLift
      P Q hselfAdjoint hcommute component
  have hactive' : R * S = R := by
    simpa [R, S] using hactive
  have hleftActive : S * R = R := by
    calc
      S * R = R * S := hcommuteSector.eq.symm
      _ = R := hactive'
  have hdouble : R = S * R * S := by
    calc
      R = S * R := hleftActive.symm
      _ = S * (R * S) := by rw [hactive']
      _ = S * R * S := (mul_assoc S R S).symm
  change R = J.comp (((LinearMap.adjoint J).comp (R.comp J)).comp (LinearMap.adjoint J))
  calc
    R = S * R * S := hdouble
    _ = (J.comp (LinearMap.adjoint J)) * R * (J.comp (LinearMap.adjoint J)) := by
      rw [hsector]
    _ = J.comp (((LinearMap.adjoint J).comp (R.comp J)).comp (LinearMap.adjoint J)) := by
      simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]

/--
If `P tensor 1` is an orthogonal projection, so is `P`.  A normalized vector
of the inert factor reflects both idempotence and self-adjointness.  This is
used only for the actual BV03 blocks below.
-/
theorem isSymmetricProjection_of_tensorMap_left_one
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (P : Semantics.Operator H) (eta : K) (heta : ‖eta‖ = 1)
    (h : (TensorProduct.map P (1 : Semantics.Operator K)).IsSymmetricProjection) :
    P.IsSymmetricProjection := by
  have hmapMul : TensorProduct.map (P * P) (1 : Semantics.Operator K) =
      TensorProduct.map P (1 : Semantics.Operator K) *
        TensorProduct.map P (1 : Semantics.Operator K) := by
    rw [← TensorProduct.map_mul]
    simp
  have hPidem : P * P = P := by
    calc
      P * P = rightTensorCompression eta
          (TensorProduct.map (P * P) (1 : Semantics.Operator K)) :=
        (rightTensorCompression_tensorMap_left (P * P) eta heta).symm
      _ = rightTensorCompression eta
          (TensorProduct.map P (1 : Semantics.Operator K) *
            TensorProduct.map P (1 : Semantics.Operator K)) :=
        congrArg (rightTensorCompression eta) hmapMul
      _ = rightTensorCompression eta (TensorProduct.map P (1 : Semantics.Operator K)) :=
        congrArg (rightTensorCompression eta) h.isIdempotentElem
      _ = P := rightTensorCompression_tensorMap_left P eta heta
  have hPadjoint : LinearMap.adjoint P = P := by
    calc
      LinearMap.adjoint P = rightTensorCompression eta
          (TensorProduct.map (LinearMap.adjoint P) (1 : Semantics.Operator K)) :=
        (rightTensorCompression_tensorMap_left (LinearMap.adjoint P) eta heta).symm
      _ = rightTensorCompression eta
          (LinearMap.adjoint (TensorProduct.map P (1 : Semantics.Operator K))) := by
        congr 1
        rw [TensorProduct.adjoint_map, LinearMap.adjoint_one]
      _ = rightTensorCompression eta (TensorProduct.map P (1 : Semantics.Operator K)) :=
        congrArg (rightTensorCompression eta) h.isSymmetric.adjoint_eq
      _ = P := rightTensorCompression_tensorMap_left P eta heta
  constructor
  · exact hPidem
  · exact (LinearMap.isSymmetric_iff_isSelfAdjoint P).mpr
      (LinearMap.isSelfAdjoint_iff'.mpr hPadjoint)

/-- A unitary block equality with a right-tensor extension reflects projection structure. -/
theorem isSymmetricProjection_of_unitary_eq_rightTensorExtension
    {A H W N : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (P : Semantics.Operator (Semantics.CompositeSystem A H))
    (Pleft : Semantics.Operator (Semantics.CompositeSystem A W))
    (eta : N) (heta : ‖eta‖ = 1)
    (hP : P.IsSymmetricProjection)
    (hleft : (unitaryLTensor A U).conjOperator P =
      rightTensorExtensionAfterLeft A W N Pleft) :
    Pleft.IsSymmetricProjection := by
  have htransported : (rightTensorExtensionAfterLeft A W N Pleft).IsSymmetricProjection :=
    isSymmetricProjection_congr
      ((isSymmetricProjection_conjOperator_iff (unitaryLTensor A U) P).mpr hP) hleft
  have hmap : (TensorProduct.map Pleft (1 : Semantics.Operator N)).IsSymmetricProjection :=
    isSymmetricProjection_of_rightTensorExtensionAfterLeft Pleft htransported
  exact isSymmetricProjection_of_tensorMap_left_one Pleft eta heta hmap

/--
The literal `AB` projector of the second cut is an orthogonal projection.
This is reflected from the actual physical source projector through the
second-cut coordinate transport, not assumed as part of the BV03 package.
-/
theorem secondCutProjectorAB_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.fourFactorProjectorABLocal region).IsSymmetricProjection := by
  let P := M.fourFactorProjectorABLocal region
  let C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
  have hsource : (M.projectorAB region).IsSymmetricProjection :=
    M.projectorAB_isSymmetricProjection region
  have hfour : (M.fourFactorExtendAB region P).IsSymmetricProjection := by
    rw [← M.fourFactorTransport_conj_projectorAB region]
    exact (isSymmetricProjection_conjOperator_iff (M.fourFactorTransport region)
      (M.projectorAB region)).mpr hsource
  have hlift : (overlapLiftLeft (C := C) P).IsSymmetricProjection := by
    apply (isSymmetricProjection_conjOperator_iff
      (M.secondCutCoordinateTransport region)
      (overlapLiftLeft (C := C) P)).mp
    rw [M.secondCutCoordinateTransport_conj_overlapLiftLeft_AB]
    exact hfour
  rcases M.exists_normalized_fourFactorCD_vector region with ⟨eta, heta⟩
  simpa [P, C, overlapLiftLeft] using
    (isSymmetricProjection_of_tensorMap_left_one P eta heta hlift)

/-- The first-cut `MC` projector is an orthogonal projection in its literal coordinates. -/
theorem firstCutProjectorMC_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutProjectorMC region).IsSymmetricProjection := by
  let AB := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)
  let D := M.fourFactorD region
  let P := M.firstCutProjectorMC region
  have hsource : (M.projectorAB region * M.projectorBC region).IsSymmetricProjection :=
    M.projectorAB_mul_BC_isSymmetricProjection region
  have hfour : ((M.fourFactorTransport region).conjOperator
      (M.projectorAB region * M.projectorBC region)).IsSymmetricProjection :=
    (isSymmetricProjection_conjOperator_iff (M.fourFactorTransport region) _).mpr hsource
  have hlift : (overlapLiftLeft (C := D) P).IsSymmetricProjection := by
    apply (isSymmetricProjection_conjOperator_iff
      (M.firstCutCoordinateTransport region) (overlapLiftLeft (C := D) P)).mp
    rw [M.firstCutCoordinateTransport_conj_firstCutProjectorMC_eq_sourceMC]
    exact hfour
  rcases M.exists_normalized_fourFactorD_vector region with ⟨eta, heta⟩
  simpa [AB, D, P, overlapLiftLeft] using
    (isSymmetricProjection_of_tensorMap_left_one P eta heta hlift)

/--
The selected second-cut sector absorption reconstructs the literal second-cut
code lift from its two-sided isotypic-subspace compression.
-/
theorem secondCutCodeLift_eq_active_embedding_compression_of_absorption
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (hactive : M.secondCutCodeLift region * M.secondCutSectorLift region component =
      M.secondCutCodeLift region) :
    let A := M.fourFactorA region
    let H := component.1.restrictScalars Complex
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    let J := tensorTripleSubtypeEmbedding (A := A) (C := CD) H
    M.secondCutCodeLift region =
      J.comp (((LinearMap.adjoint J).comp ((M.secondCutCodeLift region).comp J)).comp
        (LinearMap.adjoint J)) := by
  dsimp only
  have hself : LinearMap.adjoint (M.fourFactorProjectorABLocal region) =
      M.fourFactorProjectorABLocal region :=
    (M.secondCutProjectorAB_isSymmetricProjection region).isSymmetric.adjoint_eq
  have hover : Commute
      (overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (M.fourFactorProjectorABLocal region))
      (overlapLiftRight (A := M.fourFactorA region)
        (M.secondCutProjectorBbarM region)) :=
    M.secondCut_overlap_commute region
  have hactive' :
      (overlapLiftLeft
          (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
          (M.fourFactorProjectorABLocal region) *
        overlapLiftRight (A := M.fourFactorA region)
          (M.secondCutProjectorBbarM region)) *
        overlapLiftLeft
          (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
            (leftIsotypicSectorProjector
              (M.fourFactorProjectorABLocal region) component)) =
      overlapLiftLeft
          (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
          (M.fourFactorProjectorABLocal region) *
        overlapLiftRight (A := M.fourFactorA region)
          (M.secondCutProjectorBbarM region) := by
    simpa only [secondCutCodeLift, secondCutSectorLift] using hactive
  simpa only [secondCutCodeLift] using
    (active_overlap_product_eq_isotypic_embedding_compression
      (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region)
      hself hover component hactive')

/--
Compressing the left member of an overlap pair to an isotypic sector is exactly
the previously defined left sector block, with the exterior factor untouched.
This is the first concrete factor in the active-block product equality.
-/
theorem adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftLeft_comp_tensorTripleSubtypeEmbedding
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    (LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C)
      (component.1.restrictScalars Complex))).comp
        ((overlapLiftLeft (C := C) P).comp
          (tensorTripleSubtypeEmbedding (A := A) (C := C)
            (component.1.restrictScalars Complex))) =
      overlapLiftLeft (C := C)
        (overlapProjectorOnIsotypicComponent P component) := by
  unfold tensorTripleSubtypeEmbedding overlapLiftLeft overlapProjectorOnIsotypicComponent
  simp only [TensorProduct.adjoint_map, LinearMap.adjoint_one]
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul middle exterior =>
      induction middle using TensorProduct.induction_on with
      | zero => simp
      | tmul interior sectorVector => rfl
      | add first second hfirst hsecond =>
          simpa only [TensorProduct.add_tmul, map_add] using
            congrArg₂ (· + ·) hfirst hsecond
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

/--
The adjoint sector embedding commutes with reassociation when the exterior
factor is fixed.  This is the concrete naturality needed to compress the
right member of an overlap pair even though that operator may produce an
arbitrary vector of the physical middle tensor factor.
-/
theorem adjoint_tensorTripleSubtypeEmbedding_apply_tensorAssociatorUnitary_symm_tmul
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (p : Submodule Complex B) (interior : A)
    (middle : Semantics.CompositeSystem B C) :
    LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C) p)
      ((tensorAssociatorUnitary A B C).symm (interior ⊗ₜ[Complex] middle)) =
      (tensorAssociatorUnitary A p C).symm
        (interior ⊗ₜ[Complex]
          (TensorProduct.map (LinearMap.adjoint p.subtype)
            (1 : Semantics.Operator C) middle)) := by
  unfold tensorTripleSubtypeEmbedding
  simp only [TensorProduct.adjoint_map, LinearMap.adjoint_one]
  induction middle using TensorProduct.induction_on with
  | zero => simp
  | tmul middleVector exterior => rfl
  | add first second hfirst hsecond =>
      simpa only [TensorProduct.tmul_add, map_add] using
        congrArg₂ (· + ·) hfirst hsecond

/--
Compressing the right member of an overlap pair to the same isotypic sector is
the literal right sector block.  The associator naturality above is used here
to retain the full `B tensor C` action of the right projector.
-/
theorem adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftRight_comp_tensorTripleSubtypeEmbedding
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    (LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C)
      (component.1.restrictScalars Complex))).comp
        ((overlapLiftRight (A := A) Q).comp
          (tensorTripleSubtypeEmbedding (A := A) (C := C)
            (component.1.restrictScalars Complex))) =
      overlapLiftRight (A := A)
        (overlapRightProjectorOnIsotypicComponent P Q component) := by
  let p : Submodule Complex B := component.1.restrictScalars Complex
  let J := tensorTripleSubtypeEmbedding (A := A) (C := C) p
  let Qp := overlapRightProjectorOnIsotypicComponent P Q component
  change (LinearMap.adjoint J).comp ((overlapLiftRight (A := A) Q).comp J) =
    overlapLiftRight (A := A) Qp
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul middle exterior =>
      induction middle using TensorProduct.induction_on with
      | zero => simp
      | tmul interior sectorVector =>
          change LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C) p)
            (overlapLiftRight Q
              ((interior ⊗ₜ[Complex] p.subtype sectorVector) ⊗ₜ[Complex] exterior)) =
            overlapLiftRight (A := A) Qp
              ((interior ⊗ₜ[Complex] sectorVector) ⊗ₜ[Complex] exterior)
          rw [overlapLiftRight_apply_tmul (A := A) Q interior
            (p.subtype sectorVector) exterior]
          calc
            LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C) p)
                ((tensorAssociatorUnitary A B C).symm
                  (interior ⊗ₜ[Complex]
                    Q (p.subtype sectorVector ⊗ₜ[Complex] exterior))) =
                (tensorAssociatorUnitary A p C).symm
                  (interior ⊗ₜ[Complex]
                    (TensorProduct.map (LinearMap.adjoint p.subtype)
                      (1 : Semantics.Operator C)
                      (Q (p.subtype sectorVector ⊗ₜ[Complex] exterior)))) := by
                exact
                  adjoint_tensorTripleSubtypeEmbedding_apply_tensorAssociatorUnitary_symm_tmul
                    (A := A) (B := B) (C := C) p interior
                      (Q (p.subtype sectorVector ⊗ₜ[Complex] exterior))
            _ = overlapLiftRight (A := A) Qp
                ((interior ⊗ₜ[Complex] sectorVector) ⊗ₜ[Complex] exterior) := by
                rw [overlapLiftRight_apply_tmul (A := A) Qp interior sectorVector exterior]
                dsimp [Qp, overlapRightProjectorOnIsotypicComponent, overlapRightCompression]
      | add first second hfirst hsecond =>
          simpa only [TensorProduct.add_tmul, map_add] using
            congrArg₂ (· + ·) hfirst hsecond
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

/--
The compression of a commuting overlap product to one left-isotypic sector is
the product of its two concrete sector blocks.  Sector invariance of the right
overlap factor supplies the inserted `J J†`; this is the operator equality
that turns the BV03 coefficient block theorem into a physical block product.
-/
theorem isotypic_compression_overlap_product_eq_sector_block_product
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    (LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C)
      (component.1.restrictScalars Complex))).comp
        (((overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q).comp
          (tensorTripleSubtypeEmbedding (A := A) (C := C)
            (component.1.restrictScalars Complex)))) =
      overlapLiftLeft (C := C) (overlapProjectorOnIsotypicComponent P component) *
        overlapLiftRight (A := A)
          (overlapRightProjectorOnIsotypicComponent P Q component) := by
  let p : Submodule Complex B := component.1.restrictScalars Complex
  let J := tensorTripleSubtypeEmbedding (A := A) (C := C) p
  let E := LinearMap.adjoint J
  let L := overlapLiftLeft (C := C) P
  let K := overlapLiftRight (A := A) Q
  let S := overlapLiftLeft (C := C)
    (TensorProduct.map (1 : Semantics.Operator A)
      (leftIsotypicSectorProjector P component))
  have hJE : J.comp E = S := by
    dsimp [J, E, S, p]
    exact tensorTripleSubtypeEmbedding_comp_adjoint_eq_leftIsotypicSectorLift P component
  have hEJ : E.comp J =
      (1 : Semantics.Operator (Semantics.CompositeSystem
        (Semantics.CompositeSystem A p) C)) := by
    dsimp [E, J]
    exact adjoint_tensorTripleSubtypeEmbedding_comp_tensorTripleSubtypeEmbedding
      (A := A) (C := C) p
  have hsectorLiftRight : S =
      overlapLiftRight (A := A)
        (TensorProduct.map (leftIsotypicSectorProjector P component)
          (1 : Semantics.Operator C)) := by
    dsimp [S, overlapLiftLeft, overlapLiftRight]
    symm
    exact tensorAssociatorUnitary_symm_conj_tensorMap
      (1 : Semantics.Operator A) (leftIsotypicSectorProjector P component)
      (1 : Semantics.Operator C)
  have hlocal : Commute Q
      (TensorProduct.map (leftIsotypicSectorProjector P component)
        (1 : Semantics.Operator C)) :=
    (leftIsotypicSectorProjector_commutes_overlap P Q hselfAdjoint hcommute component).2
  have hKS : Commute K S := by
    rw [hsectorLiftRight]
    change Commute
      ((tensorAssociatorUnitary A B C).symm.conjOperator
        (TensorProduct.map (1 : Semantics.Operator A) Q))
      ((tensorAssociatorUnitary A B C).symm.conjOperator
        (TensorProduct.map (1 : Semantics.Operator A)
          (TensorProduct.map (leftIsotypicSectorProjector P component)
            (1 : Semantics.Operator C))))
    calc
      (tensorAssociatorUnitary A B C).symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator A) Q) *
        (tensorAssociatorUnitary A B C).symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator A)
            (TensorProduct.map (leftIsotypicSectorProjector P component)
              (1 : Semantics.Operator C))) =
          (tensorAssociatorUnitary A B C).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A) Q *
              TensorProduct.map (1 : Semantics.Operator A)
                (TensorProduct.map (leftIsotypicSectorProjector P component)
                  (1 : Semantics.Operator C))) :=
        (Semantics.UnitaryTransport.conjOperator_mul _ _ _).symm
      _ = (tensorAssociatorUnitary A B C).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A)
              (TensorProduct.map (leftIsotypicSectorProjector P component)
                (1 : Semantics.Operator C)) *
              TensorProduct.map (1 : Semantics.Operator A) Q) := by
          congr 1
          rw [← TensorProduct.map_mul, ← TensorProduct.map_mul]
          simpa using congrArg (fun operator =>
            TensorProduct.map (1 : Semantics.Operator A) operator) hlocal.eq
      _ = (tensorAssociatorUnitary A B C).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A)
              (TensorProduct.map (leftIsotypicSectorProjector P component)
                (1 : Semantics.Operator C))) *
          (tensorAssociatorUnitary A B C).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A) Q) :=
        Semantics.UnitaryTransport.conjOperator_mul _ _ _
  have hScompK : S.comp K = K.comp S := by
    simpa only [Module.End.mul_eq_comp] using hKS.eq.symm
  have hSonJ : S.comp J = J := by
    calc
      S.comp J = (J.comp E).comp J := by rw [hJE]
      _ = J.comp (E.comp J) := by rw [LinearMap.comp_assoc]
      _ = J.comp (1 : Semantics.Operator
          (Semantics.CompositeSystem (Semantics.CompositeSystem A p) C)) := by rw [hEJ]
      _ = J := by
        apply LinearMap.ext
        intro vector
        rfl
  have hS_K_J : S.comp (K.comp J) = K.comp J := by
    calc
      S.comp (K.comp J) = (S.comp K).comp J := by rw [LinearMap.comp_assoc]
      _ = (K.comp S).comp J := congrArg (fun operator => operator.comp J) hScompK
      _ = K.comp (S.comp J) := by rw [LinearMap.comp_assoc]
      _ = K.comp J := by rw [hSonJ]
  have hleftCompression : E.comp (L.comp J) =
      overlapLiftLeft (C := C) (overlapProjectorOnIsotypicComponent P component) := by
    dsimp [E, L, J, p]
    exact
      adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftLeft_comp_tensorTripleSubtypeEmbedding
        P component
  have hrightCompression : E.comp (K.comp J) =
      overlapLiftRight (A := A)
        (overlapRightProjectorOnIsotypicComponent P Q component) := by
    dsimp [E, K, J, p]
    exact
      adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftRight_comp_tensorTripleSubtypeEmbedding
        P Q component
  have hraw : E.comp ((L * K).comp J) =
      (E.comp (L.comp J)) * (E.comp (K.comp J)) := by
    apply LinearMap.ext
    intro vector
    change E (L (K (J vector))) = E (L (J (E (K (J vector)))))
    have hcore : J (E (K (J vector))) = K (J vector) := by
      have happly := congrArg (fun operator => operator vector) hS_K_J
      calc
        J (E (K (J vector))) = S (K (J vector)) := by
          have hJEapply := congrArg (fun operator => operator (K (J vector))) hJE
          simpa only [LinearMap.comp_apply] using hJEapply
        _ = K (J vector) := by
          simpa only [LinearMap.comp_apply] using happly
    rw [hcore]
  change E.comp ((L * K).comp J) =
    overlapLiftLeft (C := C) (overlapProjectorOnIsotypicComponent P component) *
      overlapLiftRight (A := A)
        (overlapRightProjectorOnIsotypicComponent P Q component)
  calc
    E.comp ((L * K).comp J) = (E.comp (L.comp J)) * (E.comp (K.comp J)) := hraw
    _ = overlapLiftLeft (C := C) (overlapProjectorOnIsotypicComponent P component) *
        overlapLiftRight (A := A)
          (overlapRightProjectorOnIsotypicComponent P Q component) := by
        exact congrArg₂ (fun left right => left * right)
          hleftCompression hrightCompression


end BPTCommutingProjectorModel

end Bounds
end QEC
