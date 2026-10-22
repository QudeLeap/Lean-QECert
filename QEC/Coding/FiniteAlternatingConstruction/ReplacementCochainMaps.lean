import QEC.Coding.FiniteAlternatingConstruction.RZCoordinateBridge
import QEC.Coding.FiniteAlternatingConstruction.RXLocalReplacement

/-!
# Concrete cochain maps for the BDL26 local replacements

This file constructs the RX coordinate maps directly on the finite replacement
blocks.  The degree-one map is constant on each shifted Q-cylinder and zero on
the auxiliary X-local edges.  Its parent region is defined from those
constructors, independently of the support of a mapped word.
-/

namespace QEC.Coding.BDL26ReplacementCochainMaps

open scoped BigOperators Classical
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open QEC.Coding.BDL26TannerLocalRegularity
open QEC.Coding.BDL26RXLocalReplacement
open QEC.Coding.BDL26RZLocalReplacement
open QEC.Coding.BDL26RZMap1CoordinateBridge
open QEC.Coding.MultiscaleDecoder

abbrev Field := BDL26Field
abbrev Two := BDL26FiniteTannerSquare.Two

/-- Replicate an old Q coordinate on its shifted Q-cylinder vertices and
vanish on the auxiliary X-local edges. -/
def rxMap1Coord (P : TannerSquarePresentation) (S : OddScale) :
    Word Field P.Q →ₗ[Field] Word Field (RX1 P S) where
  toFun := fun word target => match target with
    | Sum.inl _ => 0
    | Sum.inr qVertex => word qVertex.1
  map_add' := by
    intro first second
    funext target
    rcases target with _ | _ <;> rfl
  map_smul' := by
    intro coefficient word
    funext target
    rcases target with _ | _ <;> rfl

/-- The concrete RX degree-zero coordinate map. -/
def rxMap0Coord (P : TannerSquarePresentation) (S : OddScale) :
    Word Field P.X →ₗ[Field] Word Field (RX0 P S) :=
  rxAggregateDegreeZero P S

/-- The concrete RX degree-two coordinate map. -/
def rxMap2Coord (P : TannerSquarePresentation) (S : OddScale) :
    Word Field P.Z →ₗ[Field] Word Field (RX2 P S) :=
  rxAggregateDegreeTwo P S

/-- Data-only finite-coordinate RX map.  Compatibility is proved below and
is deliberately not accepted as a field. -/
structure RXMapData (P : TannerSquarePresentation) (S : OddScale) where
  map0 : Word Field P.X →ₗ[Field] Word Field (RX0 P S)
  map1 : Word Field P.Q →ₗ[Field] Word Field (RX1 P S)
  map2 : Word Field P.Z →ₗ[Field] Word Field (RX2 P S)

/-- The concrete RX finite-coordinate map. -/
def rxMap (P : TannerSquarePresentation) (S : OddScale) : RXMapData P S where
  map0 := rxMap0Coord P S
  map1 := rxMap1Coord P S
  map2 := rxMap2Coord P S

@[simp] theorem rxMap1Coord_localEdge
    (P : TannerSquarePresentation) (S : OddScale) (word : Word Field P.Q)
    (edge : Σ x : P.X, DoubleCylinderEdge P x S) :
    rxMap1Coord P S word (Sum.inl edge) = 0 := rfl

@[simp] theorem rxMap1Coord_qVertex
    (P : TannerSquarePresentation) (S : OddScale) (word : Word Field P.Q)
    (vertex : Σ q : P.Q, QDoubleCylinderVertex P q S) :
    rxMap1Coord P S word (Sum.inr vertex) = word vertex.1 := rfl

/-- Constructor-defined image of one old-Q basis coordinate. -/
def rxMap1BasisImage (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) : Word Field (RX1 P S) := fun target => match target with
  | Sum.inl _ => 0
  | Sum.inr qVertex => if qVertex.1 = q then 1 else 0

@[simp] theorem rxMap1Coord_canonicalBasis
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    rxMap1Coord P S (canonicalBasisWord q) = rxMap1BasisImage P S q := by
  classical
  ext target
  rcases target with localEdge | qVertex
  · rfl
  · unfold rxMap1Coord rxMap1BasisImage canonicalBasisWord
    dsimp
    by_cases h : qVertex.1 = q
    · subst q
      simp
    · simp [h]

/-- The exact Q-cylinder parent region, independently of map support. -/
noncomputable def rxMap1ParentRegion
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    Finset (RX1 P S) := by
  classical
  exact Finset.univ.filter fun target => match target with
    | Sum.inl _ => False
    | Sum.inr qVertex => qVertex.1 = q

theorem rxMap1BasisImage_ne_zero_iff_mem_parentRegion
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (target : RX1 P S) :
    rxMap1BasisImage P S q target ≠ 0 ↔
      target ∈ rxMap1ParentRegion P S q := by
  classical
  rcases target with localEdge | qVertex
  · unfold rxMap1BasisImage rxMap1ParentRegion
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (0 : Field) ≠ 0 ↔ False
    simp
  · unfold rxMap1BasisImage rxMap1ParentRegion
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (if qVertex.1 = q then (1 : Field) else 0) ≠ 0 ↔
      qVertex.1 = q
    by_cases h : qVertex.1 = q <;> simp [h]

theorem rxMap1BasisImage_support_eq_parentRegion
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    hammingSupport (rxMap1BasisImage P S q) = rxMap1ParentRegion P S q := by
  classical
  ext target
  simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  exact rxMap1BasisImage_ne_zero_iff_mem_parentRegion P S q target

/-- Raw degree-one finite-basis table for the concrete RX map. -/
noncomputable def rxMap1FiniteBasisAction
    (P : TannerSquarePresentation) (S : OddScale) :
    TypedFiniteBasisAction (rxMap P S).map1 where
  basisImage := rxMap1BasisImage P S
  basis_action := rxMap1Coord_canonicalBasis P S

/-- Raw extension-by-zero/support/image witness for the concrete RX map1. -/
noncomputable def rxMap1ExtensionZeroLocalSupportImage
    (P : TannerSquarePresentation) (S : OddScale) :
    @ExtensionZeroLocalSupportImage P.Q P.Q (RX1 P S)
      inferInstance inferInstance inferInstance
      (Classical.decEq P.Q) (Classical.decEq (RX1 P S))
      (rxMap P S).map1 := by
  classical
  letI : DecidableEq P.Q := Classical.decEq _
  letI : DecidableEq (RX1 P S) := Classical.decEq _
  exact {
    sourceRegion := fun q => {q}
    targetRegion := rxMap1ParentRegion P S
    extensionByZero := fun q => zeroExtendWord ({q} : Finset P.Q)
    extension_zero := by
      intro q localWord source hsource
      change (if h : source ∈ ({q} : Finset P.Q) then
        localWord ⟨source, h⟩ else 0) = 0
      rw [dif_neg hsource]
    extension_on_region := by
      intro q localWord source
      change (if h : source.1 ∈ ({q} : Finset P.Q) then
        localWord ⟨source.1, h⟩ else 0) = localWord source
      simp
    selectedMapBasisImage := rxMap1BasisImage P S
    selectedMap_basis_action := rxMap1Coord_canonicalBasis P S
    selectedMap_basis_support := by
      intro owner source target hsource htarget
      have hsourceEq : source = owner := by simpa using hsource
      subst source
      by_contra hnonzero
      exact htarget ((rxMap1BasisImage_ne_zero_iff_mem_parentRegion
        P S owner target).1 hnonzero)
    selectedMap_basis_image := by
      intro owner source target hsource hnonzero
      have hsourceEq : source = owner := by simpa using hsource
      subst source
      exact (rxMap1BasisImage_ne_zero_iff_mem_parentRegion
        P S owner target).1 hnonzero }

/-- Constructor-defined image of one old-Z basis coordinate. -/
def rxMap2BasisImage (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) : Word Field (RX2 P S) := fun target => match target with
  | Sum.inl _ => 0
  | Sum.inr zPoint => if zPoint.1 = z then 1 else 0

@[simp] theorem rxMap2Coord_canonicalBasis
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) :
    rxMap2Coord P S (canonicalBasisWord z) = rxMap2BasisImage P S z := by
  classical
  ext target
  rcases target with auxiliary | zPoint
  · rcases auxiliary with xFace | qEdge <;> rfl
  · unfold rxMap2Coord rxAggregateDegreeTwo rxMap2BasisImage
    dsimp
    unfold canonicalBasisWord
    by_cases h : zPoint.1 = z
    · subst z
      simp
    · simp [h]

/-- The exact retained two-point Z block, independently of map support. -/
noncomputable def rxMap2ParentRegion
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) :
    Finset (RX2 P S) := by
  classical
  exact Finset.univ.filter fun target => match target with
    | Sum.inl _ => False
    | Sum.inr zPoint => zPoint.1 = z

theorem rxMap2BasisImage_ne_zero_iff_mem_parentRegion
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (target : RX2 P S) :
    rxMap2BasisImage P S z target ≠ 0 ↔
      target ∈ rxMap2ParentRegion P S z := by
  classical
  rcases target with auxiliary | zPoint
  · unfold rxMap2BasisImage rxMap2ParentRegion
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp
  · unfold rxMap2BasisImage rxMap2ParentRegion
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : zPoint.1 = z <;> simp [h]

theorem rxMap2BasisImage_support_eq_parentRegion
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) :
    hammingSupport (rxMap2BasisImage P S z) = rxMap2ParentRegion P S z := by
  classical
  ext target
  simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  exact rxMap2BasisImage_ne_zero_iff_mem_parentRegion P S z target

/-- Raw degree-two finite-basis table for the concrete RX map. -/
noncomputable def rxMap2FiniteBasisAction
    (P : TannerSquarePresentation) (S : OddScale) :
    TypedFiniteBasisAction (rxMap P S).map2 where
  basisImage := rxMap2BasisImage P S
  basis_action := rxMap2Coord_canonicalBasis P S

/-- Raw extension-by-zero/support/image witness for the concrete RX map2. -/
noncomputable def rxMap2ExtensionZeroLocalSupportImage
    (P : TannerSquarePresentation) (S : OddScale) :
    @ExtensionZeroLocalSupportImage P.Z P.Z (RX2 P S)
      inferInstance inferInstance inferInstance
      (Classical.decEq P.Z) (Classical.decEq (RX2 P S))
      (rxMap P S).map2 := by
  classical
  letI : DecidableEq P.Z := Classical.decEq _
  letI : DecidableEq (RX2 P S) := Classical.decEq _
  exact {
    sourceRegion := fun z => {z}
    targetRegion := rxMap2ParentRegion P S
    extensionByZero := fun z => zeroExtendWord ({z} : Finset P.Z)
    extension_zero := by
      intro z localWord source hsource
      change (if h : source ∈ ({z} : Finset P.Z) then
        localWord ⟨source, h⟩ else 0) = 0
      rw [dif_neg hsource]
    extension_on_region := by
      intro z localWord source
      change (if h : source.1 ∈ ({z} : Finset P.Z) then
        localWord ⟨source.1, h⟩ else 0) = localWord source
      simp
    selectedMapBasisImage := rxMap2BasisImage P S
    selectedMap_basis_action := rxMap2Coord_canonicalBasis P S
    selectedMap_basis_support := by
      intro owner source target hsource htarget
      have hsourceEq : source = owner := by simpa using hsource
      subst source
      by_contra hnonzero
      exact htarget ((rxMap2BasisImage_ne_zero_iff_mem_parentRegion
        P S owner target).1 hnonzero)
    selectedMap_basis_image := by
      intro owner source target hsource hnonzero
      have hsourceEq : source = owner := by simpa using hsource
      subst source
      exact (rxMap2BasisImage_ne_zero_iff_mem_parentRegion
        P S owner target).1 hnonzero }

/-! ## Structural incidence reductions -/

private noncomputable def vertexIndicator {Vertex : Type}
    (first second : Vertex) : Field := by
  classical
  exact if first = second then 1 else 0

private theorem sum_vertexIndicator_eq_one {Vertex : Type}
    [Fintype Vertex] [DecidableEq Vertex] (target : Vertex) :
    (∑ vertex : Vertex, vertexIndicator vertex target) = (1 : Field) := by
  classical
  rw [Finset.sum_eq_single target]
  · simp [vertexIndicator]
  · intro other _ hne
    simp [vertexIndicator, hne]
  · simp

/-- A shifted Q vertex has one structurally computed realization in every
adjacent X cylinder.  The realization comes from the supplied X-Q edge. -/
private theorem qVertexXIncidence_eq_indicator
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale)
    (x : P.X) (q : P.Q) (hxq : P.xq x q = true)
    (qVertex : QDoubleCylinderVertex P q S)
    (xVertex : DoubleCylinderVertex P x S) :
    qDoubleCylinderVertexXIncidence P q x S xVertex qVertex =
      vertexIndicator xVertex
        (qToXDoubleCylinderVertexAtRoot P q x hxq S
          (A.qzRoot q) qVertex) := by
  classical
  rcases xVertex with ⟨xCopy, xVertex⟩
  rcases qVertex with ⟨qCopy, qVertex⟩
  fin_cases xCopy <;> fin_cases qCopy
  all_goals rcases xVertex with oldVertex | edgeInterior | faceInterior
  all_goals rcases qVertex with oldVertex' | edgeInterior'
  all_goals
    first
    | (rcases oldVertex' with cone | endpoint <;>
        simp [qDoubleCylinderVertexXIncidence,
          qSubdivisionVertexXIncidence,
          qToXDoubleCylinderVertexAtRoot, qToXSubdivisionVertexAtRoot,
          qToXBoundaryVertexAtRoot, xStarBoundaryVertexToStar,
          xBoundaryEdgeStart, xBoundaryEdgeEnd, qToXBoundaryEdge,
          vertexIndicator, Subtype.ext_iff, Prod.ext_iff, hxq])
    | simp [qDoubleCylinderVertexXIncidence,
        qSubdivisionVertexXIncidence,
        qToXDoubleCylinderVertexAtRoot, qToXSubdivisionVertexAtRoot,
        qToXBoundaryVertexAtRoot, xStarBoundaryVertexToStar,
        xBoundaryEdgeStart, xBoundaryEdgeEnd, qToXBoundaryEdge,
        vertexIndicator, Subtype.ext_iff, Prod.ext_iff, hxq]
  all_goals
    rcases edgeInterior with ⟨⟨edge, hmem⟩, index⟩
    rcases edge with xqEdge | qzEdge
    · simp [xStarBoundaryEdgeToStar, vertexIndicator,
        Subtype.ext_iff] at hmem ⊢
    · simp [xStarBoundaryEdgeToStar, qToXBoundaryEdge,
        vertexIndicator, Subtype.ext_iff, Prod.ext_iff, and_assoc]

theorem sum_qVertexXIncidence
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale)
    (x : P.X) (q : P.Q) (qVertex : QDoubleCylinderVertex P q S) :
    (∑ xVertex : DoubleCylinderVertex P x S,
      qDoubleCylinderVertexXIncidence P q x S xVertex qVertex) =
        if P.xq x q = true then 1 else 0 := by
  classical
  by_cases hxq : P.xq x q = true
  · rw [if_pos hxq]
    simp_rw [qVertexXIncidence_eq_indicator P A S x q hxq qVertex]
    exact sum_vertexIndicator_eq_one _
  · rw [if_neg hxq]
    apply Finset.sum_eq_zero
    intro xVertex _
    simp [qDoubleCylinderVertexXIncidence,
      qSubdivisionVertexXIncidence, hxq]

theorem constant_doubleCylinder_coboundary
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    wordLinearMapTranspose (doubleCylinderBoundary1 P x S)
        (fun _ => (1 : Field)) = 0 := by
  classical
  rw [← doubleCylinderGraphBoundary_eq_boundary1]
  change wordLinearMapTranspose
      (graphBoundary (tannerDoubleCylinderEdgeStart P x S)
        (tannerDoubleCylinderEdgeEnd P x S)) (fun _ => (1 : Field)) = 0
  ext edge
  rw [wordLinearMapTranspose_graphBoundary_apply]
  exact ZModModule.add_self 1

private theorem qVertexZIncidence_eq_indicator
    (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (z : P.Z) (copy : Two) (hqz : P.qz q z = true)
    (vertex : QDoubleCylinderVertex P q S) :
    qDoubleCylinderVertexZIncidence P q S vertex (z, copy) =
      vertexIndicator vertex
        (copy, Sum.inl (Sum.inr (⟨z, hqz⟩ : QStarEdge P q))) := by
  classical
  rcases vertex with ⟨vertexCopy, vertex⟩
  fin_cases vertexCopy <;> fin_cases copy
  all_goals rcases vertex with (cone | endpoint) | interior
  all_goals
    simp [qDoubleCylinderVertexZIncidence, vertexIndicator, hqz,
      Subtype.ext_iff]

theorem sum_qVertexZIncidence
    (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (z : P.Z) (copy : Two) :
    (∑ vertex : QDoubleCylinderVertex P q S,
      qDoubleCylinderVertexZIncidence P q S vertex (z, copy)) =
        if P.qz q z = true then 1 else 0 := by
  classical
  by_cases hqz : P.qz q z = true
  · rw [if_pos hqz]
    simp_rw [qVertexZIncidence_eq_indicator P S q z copy hqz]
    exact sum_vertexIndicator_eq_one _
  · rw [if_neg hqz]
    apply Finset.sum_eq_zero
    intro vertex _
    simp [qDoubleCylinderVertexZIncidence, hqz]

theorem constant_qDoubleCylinder_coboundary
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
        (fun _ => (1 : Field)) = 0 := by
  classical
  ext edge
  unfold qDoubleCylinderBoundary1
  rw [wordLinearMapTranspose_graphBoundary_apply]
  exact ZModModule.add_self 1

/-! ## RX coboundaries and canonical-basis commutation -/

/-- Degree-zero coboundary of the concrete RX replacement. -/
noncomputable def rxCoboundary0
    (P : TannerSquarePresentation) (S : OddScale) :
    Word Field (RX0 P S) →ₗ[Field] Word Field (RX1 P S) :=
  wordLinearMapTranspose (rxBoundary1 P S)

/-- Degree-one coboundary of the concrete RX replacement. -/
noncomputable def rxCoboundary1
    (P : TannerSquarePresentation) (S : OddScale) :
    Word Field (RX1 P S) →ₗ[Field] Word Field (RX2 P S) :=
  wordLinearMapTranspose (rxBoundary2 P S)


/-- Canonical-basis degree-zero commutation for the concrete RX map. -/
theorem rxMap_delta0_canonicalBasis
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) :
    rxCoboundary0 P S (rxMap0Coord P S (canonicalBasisWord x)) =
      rxMap1Coord P S (tannerCoboundary0 P (canonicalBasisWord x)) := by
  classical
  ext target
  rcases target with localEdge | qVertex
  · rcases localEdge with ⟨targetX, edge⟩
    unfold rxCoboundary0 rxBoundary1
    rw [wordLinearMapTranspose_toLin'_apply]
    rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single x]
    · by_cases htx : x = targetX
      · subst targetX
        simp only [rxMap0Coord, rxAggregateDegreeZero, wordPullback_apply,
          rxBoundary1Matrix, dite_true, rxMap1Coord_localEdge]
        change (∑ vertex : DoubleCylinderVertex P x S,
          canonicalBasisWord (F := Field) x x *
            doubleCylinderEdgeVertexMatrix P x S vertex edge) = 0
        have hconstant := congrFun
          (constant_doubleCylinder_coboundary P S x) edge
        change wordLinearMapTranspose
            (Matrix.toLin' (doubleCylinderEdgeVertexMatrix P x S))
            (fun _ => (1 : Field)) edge = 0 at hconstant
        rw [wordLinearMapTranspose_toLin'_apply] at hconstant
        simpa [canonicalBasisWord] using hconstant
      · simp [rxMap0Coord, rxAggregateDegreeZero, rxBoundary1Matrix, htx]
    · intro other _ hne
      change (∑ xVertex : DoubleCylinderVertex P other S,
        canonicalBasisWord (F := Field) x other *
          rxBoundary1Matrix P S ⟨other, xVertex⟩
            (Sum.inl ⟨targetX, edge⟩)) = 0
      rw [show canonicalBasisWord (F := Field) x other = 0 by
        simp [canonicalBasisWord, hne]]
      simp
    · intro hnot
      exact (hnot (Finset.mem_univ x)).elim
  · rcases qVertex with ⟨q, vertex⟩
    unfold rxCoboundary0 rxBoundary1
    rw [wordLinearMapTranspose_toLin'_apply]
    rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single x]
    · change (∑ xVertex : DoubleCylinderVertex P x S,
          canonicalBasisWord (F := Field) x x *
            qDoubleCylinderVertexXIncidence P q x S xVertex vertex) =
          tannerCoboundary0 P (canonicalBasisWord x) q
      rw [show canonicalBasisWord (F := Field) x x = 1 by
        simp [canonicalBasisWord]]
      simp only [one_mul]
      rw [sum_qVertexXIncidence P A S x q vertex]
      exact (tannerCoboundary0_canonicalBasis_apply P x q).symm
    · intro other _ hne
      change (∑ xVertex : DoubleCylinderVertex P other S,
        canonicalBasisWord (F := Field) x other *
          qDoubleCylinderVertexXIncidence P q other S xVertex vertex) = 0
      rw [show canonicalBasisWord (F := Field) x other = 0 by
        simp [canonicalBasisWord, hne]]
      simp
    · intro hnot
      exact (hnot (Finset.mem_univ x)).elim



/-- Canonical-basis degree-one commutation for the concrete RX map. -/
theorem rxMap_delta1_canonicalBasis
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    rxCoboundary1 P S (rxMap1Coord P S (canonicalBasisWord q)) =
      rxMap2Coord P S (tannerCoboundary1 P (canonicalBasisWord q)) := by
  classical
  ext target
  rcases target with (xFace | qEdge) | zPoint
  · rcases xFace with ⟨x, face⟩
    unfold rxCoboundary1 rxBoundary2
    rw [wordLinearMapTranspose_toLin'_apply]
    rw [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sigma]
    simp [rxMap1Coord, rxBoundary2Matrix, rxMap2Coord,
      rxAggregateDegreeTwo]
  · rcases qEdge with ⟨targetQ, edge⟩
    unfold rxCoboundary1 rxBoundary2
    rw [wordLinearMapTranspose_toLin'_apply]
    rw [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sigma]
    simp only [rxMap1Coord_localEdge, zero_mul, Finset.sum_const_zero,
      zero_add, rxBoundary2Matrix, rxMap2Coord, rxAggregateDegreeTwo]
    rw [Finset.sum_eq_single q]
    · by_cases hqt : q = targetQ
      · subst targetQ
        simp only [rxMap1Coord_qVertex, dite_true]
        change (∑ vertex : QDoubleCylinderVertex P q S,
          canonicalBasisWord (F := Field) q q *
            qDoubleCylinderEdgeVertexIncidence P q S vertex edge) = 0
        simp only [canonicalBasisWord, Pi.single_eq_same, one_mul,
          qDoubleCylinderEdgeVertexIncidence, Finset.sum_add_distrib]
        rw [show (∑ vertex : QDoubleCylinderVertex P q S,
            if vertex = qDoubleCylinderEdgeStart P q S edge then
              (1 : Field) else 0) = 1 by simp]
        rw [show (∑ vertex : QDoubleCylinderVertex P q S,
            if vertex = qDoubleCylinderEdgeEnd P q S edge then
              (1 : Field) else 0) = 1 by simp]
        exact ZModModule.add_self 1
      · simp [canonicalBasisWord, hqt]
    · intro other _ hne
      simp only [rxMap1Coord_qVertex]
      rw [show canonicalBasisWord (F := Field) q other = 0 by
        simp [canonicalBasisWord, hne]]
      simp
    · intro hnot
      exact (hnot (Finset.mem_univ q)).elim
  · rcases zPoint with ⟨z, copy⟩
    unfold rxCoboundary1 rxBoundary2
    rw [wordLinearMapTranspose_toLin'_apply]
    rw [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sigma]
    simp only [rxMap1Coord_localEdge, zero_mul, Finset.sum_const_zero,
      zero_add, rxBoundary2Matrix]
    rw [Finset.sum_eq_single q]
    · change (∑ vertex : QDoubleCylinderVertex P q S,
          canonicalBasisWord (F := Field) q q *
            qDoubleCylinderVertexZIncidence P q S vertex (z, copy)) =
          tannerCoboundary1 P (canonicalBasisWord q) z
      rw [show canonicalBasisWord (F := Field) q q = 1 by
        simp [canonicalBasisWord]]
      simp only [one_mul]
      rw [sum_qVertexZIncidence P S q z copy]
      exact (tannerCoboundary1_canonicalBasis_apply P q z).symm
    · intro other _ hne
      simp only [rxMap1Coord_qVertex]
      rw [show canonicalBasisWord (F := Field) q other = 0 by
        simp [canonicalBasisWord, hne]]
      simp
    · intro hnot
      exact (hnot (Finset.mem_univ q)).elim

private theorem linearMap_ext_canonicalBasis
    {Source Target : Type} [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (first second : Word Field Source →ₗ[Field] Word Field Target)
    (hbasis : ∀ source,
      first (canonicalBasisWord source) = second (canonicalBasisWord source)) :
    first = second := by
  classical
  apply LinearMap.ext
  intro word
  have hdecompose : word =
      ∑ source : Source, word source • canonicalBasisWord source := by
    rw [← word_eq_sum_single word]
    apply Finset.sum_congr rfl
    intro source _
    ext target
    rw [Pi.single_apply, Pi.smul_apply]
    by_cases htarget : target = source
    · subst target
      simp [canonicalBasisWord]
    · simp [canonicalBasisWord, htarget]
  rw [hdecompose]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro source _
  rw [hbasis source]

/-- The concrete RX map commutes with degree-zero coboundaries.  The equality
is derived from the canonical-basis theorem above. -/
theorem rxMap_commutes_coboundary0
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) :
    (rxCoboundary0 P S).comp (rxMap P S).map0 =
      (rxMap P S).map1.comp (tannerCoboundary0 P) := by
  classical
  apply linearMap_ext_canonicalBasis
  intro x
  simpa [rxMap, LinearMap.comp_apply] using
    rxMap_delta0_canonicalBasis P A S x

/-- The concrete RX map commutes with degree-one coboundaries.  The equality
is derived from the canonical-basis theorem above. -/
theorem rxMap_commutes_coboundary1
    (P : TannerSquarePresentation) (S : OddScale) :
    (rxCoboundary1 P S).comp (rxMap P S).map1 =
      (rxMap P S).map2.comp (tannerCoboundary1 P) := by
  classical
  apply linearMap_ext_canonicalBasis
  intro q
  simpa [rxMap, LinearMap.comp_apply] using
    rxMap_delta1_canonicalBasis P S q

/-! ## Reused RZ degree-one/two coordinate surface -/

/-- The concrete successor RZ degree-zero coboundary. -/
noncomputable def rzCoboundary0
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) : Word Field (RZX P S) →ₗ[Field] Word Field (RZQ P S) :=
  tannerCoboundary0
    (rzReplacementPresentation P
      A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissible S)

/-- Constructor embedding of one transposed Q-cylinder edge word into the
degree-zero RZ successor carrier. -/
noncomputable def extendRZQEdgeWord
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    Word Field (QDoubleCylinderEdge (transposePresentation P) q S) →ₗ[Field]
      Word Field (RZX P S) := by
  classical
  exact wordPushforward (rzMap1QEdgeX P S q)

/-- Constructor embedding of one transposed Q-cylinder vertex word into the
degree-one RZ successor carrier. -/
noncomputable def extendRZQVertexWord
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    Word Field (QDoubleCylinderVertex (transposePresentation P) q S) →ₗ[Field]
      Word Field (RZQ P S) := by
  classical
  exact wordPushforward (fun vertex => Sum.inr ⟨q, vertex⟩)

/-- Constructor embedding of one Z-cylinder edge word into the degree-one RZ
successor carrier. -/
private noncomputable def extendRZLocalEdgeWord
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) :
    Word Field (ZDoubleCylinderEdge P z S) →ₗ[Field]
      Word Field (RZQ P S) := by
  classical
  exact wordPushforward (fun edge => Sum.inl ⟨z, edge⟩)

/-- The pushforward and constructor forms of the local-edge embedding agree. -/
theorem extendRZLocalEdgeWord_eq
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (word : Word Field (ZDoubleCylinderEdge P z S)) :
    extendRZLocalEdgeWord P S z word = extendZEdgeWord P S z word := by
  classical
  ext target
  unfold extendRZLocalEdgeWord
  rw [wordPushforward_apply]
  rcases target with ⟨other, edge⟩ | vertex
  · by_cases h : other = z
    · subst other
      simp [extendZEdgeWord, Sigma.mk.injEq]
    · simp [extendZEdgeWord, h, Ne.symm h, Sigma.mk.injEq]
  · simp [extendZEdgeWord]

/-- The explicit path from the retained copy-zero old-X endpoint to the fixed
#838 Q root.  Orientation is immaterial over the binary field. -/
noncomputable def rzMap0QPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (q : P.Q) (hxq : P.xq x q = true) :
    Word Field (QDoubleCylinderEdge (transposePresentation P) q S) :=
  pathChain
    (qDoubleCylinderPath (transposePresentation P)
      (transposeTannerSquareAdmissible P
        A4.toTannerSquareAdmissible) q S
      (rzXQVertex P q x hxq S 0))

/-- Degree-zero coboundary of an embedded Q-cylinder word: its two graph
endpoints together with the structurally pushed word in every adjacent
Z-cylinder. -/
theorem rzCoboundary0_extendRZQEdgeWord
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q)
    (word : Word Field
      (QDoubleCylinderEdge (transposePresentation P) q S)) :
    rzCoboundary0 P A4 S (extendRZQEdgeWord P S q word) =
      extendRZQVertexWord P S q
        (graphBoundary
          (qDoubleCylinderEdgeStart (transposePresentation P) q S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) q S) word) +
        ∑ z : P.Z, if hqz : P.qz q z = true then
          extendRZLocalEdgeWord P S z
            (rzQZDegreeZero P A4.toTannerSquareAdmissible q z hqz S word)
        else 0 := by
  classical
  let rhs : Word Field
        (QDoubleCylinderEdge (transposePresentation P) q S) →ₗ[Field]
        Word Field (RZQ P S) :=
    (extendRZQVertexWord P S q).comp
        (graphBoundary
          (qDoubleCylinderEdgeStart (transposePresentation P) q S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) q S)) +
      ∑ z : P.Z, if hqz : P.qz q z = true then
        (extendRZLocalEdgeWord P S z).comp
          (rzQZDegreeZero P A4.toTannerSquareAdmissible q z hqz S)
      else 0
  have hmaps : (rzCoboundary0 P A4 S).comp
        (extendRZQEdgeWord P S q) = rhs := by
    apply linearMap_ext_canonicalBasis
    intro edge
    have hbasis : canonicalBasisWord (F := Field) edge =
        Pi.single edge 1 := by
      ext target
      simp [canonicalBasisWord, Pi.single_apply]
    rw [hbasis]
    simp only [LinearMap.comp_apply]
    have hembed : (extendRZQEdgeWord P S q) (Pi.single edge 1) =
        canonicalBasisWord (rzMap1QEdgeX P S q edge) := by
      unfold extendRZQEdgeWord
      rw [wordPushforward_single]
      ext target
      simp [canonicalBasisWord, Pi.single_apply]
    rw [hembed]
    unfold rzCoboundary0
    change tannerCoboundary0
        (rzReplacementPresentation P
          A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissible S)
        (canonicalBasisWord (rzMap1QEdgeX P S q edge)) = _
    rw [rzMap1QEdge_delta0_canonicalBasis]
    unfold rzMap1QEdgeDelta0BasisImage rhs extendRZQVertexWord
      extendRZLocalEdgeWord
    simp only [LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.comp_apply]
    rw [graphBoundary_single, graphEdgeBoundary, map_add,
      wordPushforward_single, wordPushforward_single]
    apply congrArg₂ (· + ·)
    · simp [canonicalBasisWord]
    · apply Finset.sum_congr rfl
      intro z _
      by_cases hqz : P.qz q z = true
      · rw [dif_pos hqz, dif_pos hqz, LinearMap.comp_apply]
        unfold rzQZDegreeZero
        rw [wordPushforward_single, wordPushforward_single]
        simp [canonicalBasisWord]
      · rw [dif_neg hqz, dif_neg hqz, LinearMap.zero_apply]
  have happ := LinearMap.congr_fun hmaps word
  simp only [LinearMap.comp_apply] at happ
  rw [happ]
  simp only [rhs, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.comp_apply]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro z _
  by_cases hqz : P.qz q z = true <;> simp [hqz]

/-- The embedded copy-zero X-to-Q path has the fixed #838 Q root and the
retained old-X endpoint as its Q boundary, plus the pushed path in every
adjacent Z-cylinder. -/
theorem rzMap0QPath_delta0
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (q : P.Q) (hxq : P.xq x q = true) :
    rzCoboundary0 P A4 S
        (extendRZQEdgeWord P S q (rzMap0QPath P A4 S x q hxq)) =
      canonicalBasisWord
          (Sum.inr ⟨q, rzMap1QRoot P q S⟩ : RZQ P S) +
        canonicalBasisWord
          (Sum.inr ⟨q, rzXQVertex P q x hxq S 0⟩ : RZQ P S) +
        ∑ z : P.Z, if hqz : P.qz q z = true then
          extendRZLocalEdgeWord P S z
            (rzQZDegreeZero P A4.toTannerSquareAdmissible q z hqz S
              (rzMap0QPath P A4 S x q hxq))
        else 0 := by
  classical
  rw [rzCoboundary0_extendRZQEdgeWord]
  unfold rzMap0QPath
  rw [graphBoundary_pathChain, map_add]
  unfold extendRZQVertexWord
  rw [wordPushforward_single, wordPushforward_single]
  simp only [canonicalBasisWord]
  rfl

private def rzGridZero (S : OddScale) : Fin (S.half + 1) :=
  ⟨0, by omega⟩

private def rzGridLast (S : OddScale) : Fin (S.half + 1) :=
  ⟨S.half, by omega⟩

/-- Boundary of one canonical small square, exposed as its four structurally
enumerated grid edges. -/
private theorem subdivisionBoundary2_canonicalBasis
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (i j : Fin S.half) :
    subdivisionBoundary2 P x S
        (canonicalBasisWord (⟨face, i, j⟩ : SubdivisionFace P x S)) =
      canonicalBasisWord
          (subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 0)) +
        canonicalBasisWord
          (subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 1)) +
        canonicalBasisWord
          (subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 1)) +
      canonicalBasisWord
          (subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 0)) := by
  classical
  ext edge
  unfold subdivisionBoundary2
  rw [Matrix.toLin'_apply]
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_single (⟨face, i, j⟩ : SubdivisionFace P x S)]
  · rw [show canonicalBasisWord (F := Field)
          (⟨face, i, j⟩ : SubdivisionFace P x S) ⟨face, i, j⟩ = 1 by
        simp [canonicalBasisWord, Pi.single_apply]]
    simp only [mul_one, Pi.add_apply]
    have hslot := subdivisionFaceBoundaryEdge_injective
        P x S (⟨face, i, j⟩ : SubdivisionFace P x S)
    have h00_11 :
        subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 0) ≠
          subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 1) :=
      Function.Injective.ne hslot (by decide)
    have h00_01 :
        subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 0) ≠
          subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 1) :=
      Function.Injective.ne hslot (by decide)
    have h00_10 :
        subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 0) ≠
          subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 0) :=
      Function.Injective.ne hslot (by decide)
    have h11_01 :
        subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 1) ≠
          subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 1) :=
      Function.Injective.ne hslot (by decide)
    have h11_10 :
        subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 1) ≠
          subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 0) :=
      Function.Injective.ne hslot (by decide)
    have h01_10 :
        subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 1) ≠
          subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 0) :=
      Function.Injective.ne hslot (by decide)
    have hbasis_self (a : SubdivisionEdge P x S) :
        canonicalBasisWord (F := Field) a a = 1 := by
      simp [canonicalBasisWord, Pi.single_apply]
    have hbasis_ne {a b : SubdivisionEdge P x S} (h : a ≠ b) :
        canonicalBasisWord (F := Field) a b = 0 := by
      simp [canonicalBasisWord, Pi.single_apply, h]
    by_cases h00 : edge =
        subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 0)
    · have hmatrix : subdivisionFaceEdgeMatrix P x S edge ⟨face, i, j⟩ = 1 :=
        (subdivisionFaceEdgeMatrix_eq_one_iff P x S edge ⟨face, i, j⟩).2
          ⟨(0, 0), h00.symm⟩
      subst edge
      rw [hmatrix, hbasis_self, hbasis_ne h00_11.symm,
        hbasis_ne h00_01.symm, hbasis_ne h00_10.symm]
      simp
    · by_cases h11 : edge =
          subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 1)
      · have hmatrix : subdivisionFaceEdgeMatrix P x S edge ⟨face, i, j⟩ = 1 :=
          (subdivisionFaceEdgeMatrix_eq_one_iff P x S edge ⟨face, i, j⟩).2
            ⟨(1, 1), h11.symm⟩
        subst edge
        rw [hmatrix, hbasis_ne h00_11, hbasis_self,
          hbasis_ne h11_01.symm, hbasis_ne h11_10.symm]
        simp
      · by_cases h01 : edge =
            subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 1)
        · have hmatrix : subdivisionFaceEdgeMatrix P x S edge ⟨face, i, j⟩ = 1 :=
            (subdivisionFaceEdgeMatrix_eq_one_iff P x S edge ⟨face, i, j⟩).2
              ⟨(0, 1), h01.symm⟩
          subst edge
          rw [hmatrix, hbasis_ne h00_01, hbasis_ne h11_01,
            hbasis_self, hbasis_ne h01_10.symm]
          simp
        · by_cases h10 : edge =
              subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 0)
          · have hmatrix : subdivisionFaceEdgeMatrix P x S edge ⟨face, i, j⟩ = 1 :=
              (subdivisionFaceEdgeMatrix_eq_one_iff P x S edge ⟨face, i, j⟩).2
                ⟨(1, 0), h10.symm⟩
            subst edge
            rw [hmatrix, hbasis_ne h00_10, hbasis_ne h11_10,
              hbasis_ne h01_10, hbasis_self]
            simp
          · have hmatrix_ne :
                subdivisionFaceEdgeMatrix P x S edge ⟨face, i, j⟩ ≠ 1 := by
              intro hmatrix
              obtain ⟨slot, hslot_eq⟩ :=
                (subdivisionFaceEdgeMatrix_eq_one_iff
                  P x S edge ⟨face, i, j⟩).1 hmatrix
              rcases slot with ⟨first, second⟩
              fin_cases first <;> fin_cases second
              · exact h00 hslot_eq.symm
              · exact h01 hslot_eq.symm
              · exact h10 hslot_eq.symm
              · exact h11 hslot_eq.symm
            have hmatrix_zero :
                subdivisionFaceEdgeMatrix P x S edge ⟨face, i, j⟩ = 0 := by
              generalize hvalue_eq :
                subdivisionFaceEdgeMatrix P x S edge ⟨face, i, j⟩ = hvalue
              fin_cases hvalue
              · rfl
              · exfalso
                apply hmatrix_ne
                exact hvalue_eq
            have hb00 : canonicalBasisWord (F := Field)
                (subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 0)) edge = 0 :=
              hbasis_ne (Ne.symm h00)
            have hb11 : canonicalBasisWord (F := Field)
                (subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 1)) edge = 0 :=
              hbasis_ne (Ne.symm h11)
            have hb01 : canonicalBasisWord (F := Field)
                (subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 1)) edge = 0 :=
              hbasis_ne (Ne.symm h01)
            have hb10 : canonicalBasisWord (F := Field)
                (subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 0)) edge = 0 :=
              hbasis_ne (Ne.symm h10)
            rw [hmatrix_zero, hb00, hb11, hb01, hb10]
            simp
  · intro other hne
    rw [show canonicalBasisWord (F := Field)
        (⟨face, i, j⟩ : SubdivisionFace P x S) other = 0 by
      simp [canonicalBasisWord, Pi.single_apply, Ne.symm hne]]
    simp

private theorem fin_sum_adjacent_cancel
    (n : Nat) (values : Fin (n + 1) → Field) :
    (∑ i : Fin n, (values i.castSucc + values i.succ)) =
      values 0 + values (Fin.last n) := by
  rw [Finset.sum_add_distrib]
  have hcast := Fin.sum_univ_castSucc values
  have hsucc := Fin.sum_univ_succ values
  have hself (value : Field) : value + value = 0 := by
    fin_cases value <;> rfl
  have hcast' : (∑ i : Fin n, values i.castSucc) =
      (∑ i : Fin (n + 1), values i) + values (Fin.last n) := by
    calc
      _ = (∑ i : Fin n, values i.castSucc) +
          (values (Fin.last n) + values (Fin.last n)) := by rw [hself, add_zero]
      _ = ((∑ i : Fin n, values i.castSucc) + values (Fin.last n)) +
          values (Fin.last n) := by module
      _ = _ := by rw [← hcast]
  have hsucc' : (∑ i : Fin n, values i.succ) =
      values 0 + ∑ i : Fin (n + 1), values i := by
    calc
      _ = (values 0 + values 0) + (∑ i : Fin n, values i.succ) := by
        rw [hself, zero_add]
      _ = values 0 + (values 0 + ∑ i : Fin n, values i.succ) := by module
      _ = _ := by rw [← hsucc]
  rw [hcast', hsucc']
  calc
    _ = ((∑ i : Fin (n + 1), values i) +
          ∑ i : Fin (n + 1), values i) +
        (values (Fin.last n) + values 0) := by module
    _ = values (Fin.last n) + values 0 := by rw [hself, zero_add]
    _ = _ := add_comm _ _

private theorem fin_sum_adjacent_cancel_word
    {Index : Type} (n : Nat) (values : Fin (n + 1) → Word Field Index) :
    (∑ i : Fin n, (values i.castSucc + values i.succ)) =
      values 0 + values (Fin.last n) := by
  ext coordinate
  simp only [Finset.sum_apply, Pi.add_apply]
  exact fin_sum_adjacent_cancel n (fun i => values i coordinate)

/-- The vertices of an entire subdivided Q arm, including both endpoints. -/
def qArmChainVertex (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (edge : QStarEdge P q) (i : Fin (S.half + 1)) :
    QSubdivisionVertex P q S :=
  if hzero : i.1 = 0 then Sum.inl (Sum.inl ())
  else if hlast : i.1 = S.half then Sum.inl (Sum.inr edge)
  else Sum.inr (edge, ⟨i.1 - 1, by have := i.2; omega⟩)

private theorem qArmChainVertex_start
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (edge : QStarEdge P q) (i : Fin S.half) :
    qSubdivisionEdgeStart P q S (edge, i) =
      qArmChainVertex P q S edge i.castSucc := by
  have hi : i.1 ≠ S.half := Nat.ne_of_lt i.2
  simp [qSubdivisionEdgeStart, qArmChainVertex, hi, qStarEdgeStart]

private theorem qArmChainVertex_end
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (edge : QStarEdge P q) (i : Fin S.half) :
    qSubdivisionEdgeEnd P q S (edge, i) =
      qArmChainVertex P q S edge i.succ := by
  simp [qSubdivisionEdgeEnd, qArmChainVertex, qStarEdgeEnd]

/-- An explicit copy-zero arm, enumerating every segment once. -/
noncomputable def rzMap0QRay
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (q : P.Q) (hxq : P.xq x q = true) :
    Word Field (QDoubleCylinderEdge (transposePresentation P) q S) := by
  classical
  exact ∑ i : Fin S.half,
    canonicalBasisWord (Sum.inl (0, (⟨x, hxq⟩, i)))

/-- Cancellation of adjacent subdivision endpoints leaves the arm's root and
terminal vertex by finite enumeration. -/
theorem rzMap0QRay_boundary
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (q : P.Q) (hxq : P.xq x q = true) :
    graphBoundary
        (qDoubleCylinderEdgeStart (transposePresentation P) q S)
        (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
        (rzMap0QRay P S x q hxq) =
      canonicalBasisWord (rzMap1QRoot P q S) +
        canonicalBasisWord (rzXQVertex P q x hxq S 0) := by
  classical
  unfold rzMap0QRay
  rw [map_sum]
  have hbasis (edge : QDoubleCylinderEdge (transposePresentation P) q S) :
      canonicalBasisWord (F := Field) edge = Pi.single edge 1 := by
    ext other
    simp [canonicalBasisWord, Pi.single_apply]
  simp_rw [hbasis, graphBoundary_single, graphEdgeBoundary]
  change (∑ i : Fin S.half,
    (Pi.single (0, qSubdivisionEdgeStart (transposePresentation P) q S (⟨x, hxq⟩, i)) 1 +
      Pi.single (0, qSubdivisionEdgeEnd (transposePresentation P) q S (⟨x, hxq⟩, i)) 1)) = _
  have hsum : (∑ i : Fin S.half,
      ((Pi.single (0, qSubdivisionEdgeStart (transposePresentation P) q S (⟨x, hxq⟩, i)) (1 : Field) :
          Word Field (QDoubleCylinderVertex (transposePresentation P) q S)) +
        Pi.single (0, qSubdivisionEdgeEnd (transposePresentation P) q S (⟨x, hxq⟩, i)) 1)) =
      ∑ i : Fin S.half,
        ((Pi.single (0, qArmChainVertex (transposePresentation P) q S ⟨x, hxq⟩ i.castSucc) 1 :
          Word Field (QDoubleCylinderVertex (transposePresentation P) q S)) +
          Pi.single (0, qArmChainVertex (transposePresentation P) q S ⟨x, hxq⟩ i.succ) 1) := by
    apply Finset.sum_congr rfl
    intro i _
    erw [qArmChainVertex_start (transposePresentation P) q S ⟨x, hxq⟩ i,
      qArmChainVertex_end (transposePresentation P) q S ⟨x, hxq⟩ i]
  rw [hsum]
  rw [fin_sum_adjacent_cancel_word S.half
    (fun i => Pi.single (0, qArmChainVertex (transposePresentation P) q S
      ⟨x, hxq⟩ i) (1 : Field))]
  ext vertex
  simp [qArmChainVertex, S.half_pos.ne', rzMap1QRoot, rzXQVertex, canonicalBasisWord, Pi.single_apply] <;>
    first | rfl | (split_ifs <;> rfl)

/-- The total successor boundary of the explicit copied arm. -/
theorem rzMap0QRay_delta0
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (q : P.Q) (hxq : P.xq x q = true) :
    rzCoboundary0 P A4 S (extendRZQEdgeWord P S q (rzMap0QRay P S x q hxq)) =
      canonicalBasisWord
          (Sum.inr ⟨q, rzMap1QRoot P q S⟩ : RZQ P S) +
        canonicalBasisWord
          (Sum.inr ⟨q, rzXQVertex P q x hxq S 0⟩ : RZQ P S) +
        ∑ z : P.Z, if hqz : P.qz q z = true then
          extendRZLocalEdgeWord P S z
            (rzQZDegreeZero P A4.toTannerSquareAdmissible q z hqz S
              (rzMap0QRay P S x q hxq))
        else 0 := by
  classical
  rw [rzCoboundary0_extendRZQEdgeWord, rzMap0QRay_boundary, map_add]
  unfold extendRZQVertexWord
  simp only [wordPushforward_canonicalBasis]

/-- The copy-zero grid filling of one old face: every small square is used
once, independently of any boundary/support conclusion. -/
noncomputable def subdivisionWholeFaceChain
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) : Word Field (SubdivisionFace P x S) :=
  ∑ i : Fin S.half, ∑ j : Fin S.half,
    canonicalBasisWord (⟨face, i, j⟩ : SubdivisionFace P x S)

private theorem subdivisionHorizontalRows_cancel
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) :
    (∑ i : Fin S.half, ∑ j : Fin S.half,
        canonicalBasisWord (F := Field)
          (subdivisionHorizontalEdge P x S face i j.castSucc)) +
      (∑ i : Fin S.half, ∑ j : Fin S.half,
        canonicalBasisWord (F := Field)
          (subdivisionHorizontalEdge P x S face i j.succ)) =
      (∑ i : Fin S.half,
        canonicalBasisWord (F := Field)
          (subdivisionHorizontalEdge P x S face i 0)) +
      (∑ i : Fin S.half,
        canonicalBasisWord (F := Field)
          (subdivisionHorizontalEdge P x S face i (Fin.last S.half))) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  exact fin_sum_adjacent_cancel_word S.half
    (fun j => canonicalBasisWord (F := Field)
      (subdivisionHorizontalEdge P x S face i j))

private theorem subdivisionVerticalColumns_cancel
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) :
    (∑ i : Fin S.half, ∑ j : Fin S.half,
        canonicalBasisWord (F := Field)
          (subdivisionVerticalEdge P x S face i.succ j)) +
      (∑ i : Fin S.half, ∑ j : Fin S.half,
        canonicalBasisWord (F := Field)
          (subdivisionVerticalEdge P x S face i.castSucc j)) =
      (∑ j : Fin S.half,
        canonicalBasisWord (F := Field)
          (subdivisionVerticalEdge P x S face 0 j)) +
      (∑ j : Fin S.half,
        canonicalBasisWord (F := Field)
          (subdivisionVerticalEdge P x S face (Fin.last S.half) j)) := by
  calc
    _ = (∑ j : Fin S.half, ∑ i : Fin S.half,
          canonicalBasisWord (F := Field)
            (subdivisionVerticalEdge P x S face i.succ j)) +
        (∑ j : Fin S.half, ∑ i : Fin S.half,
          canonicalBasisWord (F := Field)
            (subdivisionVerticalEdge P x S face i.castSucc j)) := by
      congr 1 <;> exact Finset.sum_comm
    _ = ∑ j : Fin S.half,
        ((∑ i : Fin S.half, canonicalBasisWord (F := Field)
            (subdivisionVerticalEdge P x S face i.succ j)) +
          (∑ i : Fin S.half, canonicalBasisWord (F := Field)
            (subdivisionVerticalEdge P x S face i.castSucc j))) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ j : Fin S.half,
        (canonicalBasisWord (F := Field)
            (subdivisionVerticalEdge P x S face 0 j) +
          canonicalBasisWord (F := Field)
            (subdivisionVerticalEdge P x S face (Fin.last S.half) j)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_add_distrib]
      calc
        _ = ∑ i : Fin S.half,
            (canonicalBasisWord (F := Field)
                (subdivisionVerticalEdge P x S face i.castSucc j) +
              canonicalBasisWord (F := Field)
                (subdivisionVerticalEdge P x S face i.succ j)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact add_comm _ _
        _ = _ := fin_sum_adjacent_cancel_word S.half
          (fun i => canonicalBasisWord (F := Field)
            (subdivisionVerticalEdge P x S face i j))
    _ = _ := by rw [Finset.sum_add_distrib]

/-- Internal grid edges occur twice in the whole-face filling, leaving exactly
the four subdivided outer sides. -/
theorem subdivisionWholeFaceChain_boundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) :
    subdivisionBoundary2 P x S (subdivisionWholeFaceChain P x S face) =
      (∑ i : Fin S.half,
          canonicalBasisWord
            (subdivisionHorizontalEdge P x S face i (rzGridZero S))) +
        (∑ i : Fin S.half,
          canonicalBasisWord
            (subdivisionHorizontalEdge P x S face i (rzGridLast S))) +
        (∑ j : Fin S.half,
          canonicalBasisWord
            (subdivisionVerticalEdge P x S face (rzGridZero S) j)) +
      (∑ j : Fin S.half,
        canonicalBasisWord
          (subdivisionVerticalEdge P x S face (rzGridLast S) j)) := by
  classical
  unfold subdivisionWholeFaceChain
  simp_rw [map_sum, subdivisionBoundary2_canonicalBasis,
    subdivisionFaceBoundaryEdge_zero_zero,
    subdivisionFaceBoundaryEdge_zero_one,
    subdivisionFaceBoundaryEdge_one_zero,
    subdivisionFaceBoundaryEdge_one_one]
  simp_rw [Finset.sum_add_distrib]
  let horizontalLow : Word Field (SubdivisionEdge P x S) :=
    ∑ i : Fin S.half, ∑ j : Fin S.half,
      canonicalBasisWord
        (subdivisionHorizontalEdge P x S face i j.castSucc)
  let horizontalHigh : Word Field (SubdivisionEdge P x S) :=
    ∑ i : Fin S.half, ∑ j : Fin S.half,
      canonicalBasisWord
        (subdivisionHorizontalEdge P x S face i j.succ)
  let verticalHigh : Word Field (SubdivisionEdge P x S) :=
    ∑ i : Fin S.half, ∑ j : Fin S.half,
      canonicalBasisWord
        (subdivisionVerticalEdge P x S face i.succ j)
  let verticalLow : Word Field (SubdivisionEdge P x S) :=
    ∑ i : Fin S.half, ∑ j : Fin S.half,
      canonicalBasisWord
        (subdivisionVerticalEdge P x S face i.castSucc j)
  change horizontalLow + verticalHigh + horizontalHigh + verticalLow = _
  have hhorizontal : horizontalLow + horizontalHigh =
      (∑ i : Fin S.half, canonicalBasisWord
        (subdivisionHorizontalEdge P x S face i 0)) +
      (∑ i : Fin S.half, canonicalBasisWord
        (subdivisionHorizontalEdge P x S face i (Fin.last S.half))) := by
    simpa only [horizontalLow, horizontalHigh] using
      subdivisionHorizontalRows_cancel P x S face
  have hvertical : verticalHigh + verticalLow =
      (∑ j : Fin S.half, canonicalBasisWord
        (subdivisionVerticalEdge P x S face 0 j)) +
      (∑ j : Fin S.half, canonicalBasisWord
        (subdivisionVerticalEdge P x S face (Fin.last S.half) j)) := by
    simpa only [verticalHigh, verticalLow] using
      subdivisionVerticalColumns_cancel P x S face
  have hzero : (0 : Fin (S.half + 1)) = rzGridZero S := by
    apply Fin.ext
    rfl
  have hlast : Fin.last S.half = rzGridLast S := by
    apply Fin.ext
    rfl
  calc
    _ = (horizontalLow + horizontalHigh) + (verticalHigh + verticalLow) := by
      module
    _ =
        (((∑ i : Fin S.half, canonicalBasisWord
            (subdivisionHorizontalEdge P x S face i 0)) +
          (∑ i : Fin S.half, canonicalBasisWord
            (subdivisionHorizontalEdge P x S face i (Fin.last S.half)))) +
        ((∑ j : Fin S.half, canonicalBasisWord
            (subdivisionVerticalEdge P x S face 0 j)) +
          (∑ j : Fin S.half, canonicalBasisWord
            (subdivisionVerticalEdge P x S face (Fin.last S.half) j)))) := by
      rw [hhorizontal, hvertical]
    _ = _ := by
      rw [hzero, hlast]
      module

/-- Extend a subdivision face word into copy zero of the quotient-free
double cylinder. -/
noncomputable def extendCopyZeroSubdivisionFaceWord
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (SubdivisionFace P x S) →ₗ[Field]
      Word Field (DoubleCylinderFace P x S) where
  toFun word target := match target with
    | Sum.inl (copy, face) => if copy = 0 then word face else 0
    | Sum.inr _ => 0
  map_add' := by
    intro first second
    funext target
    rcases target with ⟨copy, face⟩ | rectangle
    · by_cases hcopy : copy = 0 <;> simp [hcopy]
    · rfl
  map_smul' := by
    intro coefficient word
    funext target
    rcases target with ⟨copy, face⟩ | rectangle
    · by_cases hcopy : copy = 0 <;> simp [hcopy]
    · rfl

/-- Extend a subdivision edge word into copy zero of the quotient-free
double cylinder. -/
noncomputable def extendCopyZeroSubdivisionEdgeWord
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (SubdivisionEdge P x S) →ₗ[Field]
      Word Field (DoubleCylinderEdge P x S) where
  toFun word target := match target with
    | Sum.inl (copy, edge) => if copy = 0 then word edge else 0
    | Sum.inr _ => 0
  map_add' := by
    intro first second
    funext target
    rcases target with ⟨copy, edge⟩ | boundary
    · by_cases hcopy : copy = 0 <;> simp [hcopy]
    · rfl
  map_smul' := by
    intro coefficient word
    funext target
    rcases target with ⟨copy, edge⟩ | boundary
    · by_cases hcopy : copy = 0 <;> simp [hcopy]
    · rfl

/-- Copy-zero extension intertwines the small-grid boundary with the
quotient-free double-cylinder boundary. -/
theorem doubleCylinderBoundary2_extendCopyZero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (word : Word Field (SubdivisionFace P x S)) :
    doubleCylinderBoundary2 P x S
        (extendCopyZeroSubdivisionFaceWord P x S word) =
      extendCopyZeroSubdivisionEdgeWord P x S
        (subdivisionBoundary2 P x S word) := by
  classical
  ext target
  rcases target with ⟨copy, edge⟩ | boundary
  · fin_cases copy
    · simp [doubleCylinderBoundary2, subdivisionBoundary2,
        extendCopyZeroSubdivisionFaceWord,
        extendCopyZeroSubdivisionEdgeWord, Matrix.toLin'_apply,
        Matrix.mulVec, dotProduct, doubleCylinderFaceEdgeMatrix,
        Fintype.sum_sum_type, Fintype.sum_prod_type]
    · simp [doubleCylinderBoundary2, subdivisionBoundary2,
        extendCopyZeroSubdivisionFaceWord,
        extendCopyZeroSubdivisionEdgeWord, Matrix.toLin'_apply,
        Matrix.mulVec, dotProduct, doubleCylinderFaceEdgeMatrix,
        Fintype.sum_sum_type, Fintype.sum_prod_type]
  · simp [doubleCylinderBoundary2, extendCopyZeroSubdivisionFaceWord,
      extendCopyZeroSubdivisionEdgeWord, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, doubleCylinderFaceEdgeMatrix,
      Fintype.sum_sum_type, Fintype.sum_prod_type]

/-- Constructor extension of one Z-local face word into the successor
degree-zero carrier. -/
noncomputable def extendRZFaceWord
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) :
    Word Field (ZDoubleCylinderFace P z S) →ₗ[Field]
      Word Field (RZX P S) := by
  classical
  exact wordPushforward (fun face => Sum.inl (Sum.inl ⟨z, face⟩))

private theorem doubleCylinderBoundary2_canonicalBasis_apply
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : DoubleCylinderFace P x S) (edge : DoubleCylinderEdge P x S) :
    doubleCylinderBoundary2 P x S (canonicalBasisWord face) edge =
      doubleCylinderFaceEdgeMatrix P x S edge face := by
  classical
  simp [doubleCylinderBoundary2, Matrix.toLin'_apply, Matrix.mulVec,
    canonicalBasisWord]

/-- The successor X-Q coboundary of an embedded local face word is exactly
the embedded quotient-free face boundary. -/
theorem rzCoboundary0_extendRZFaceWord
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z)
    (word : Word Field (ZDoubleCylinderFace P z S)) :
    rzCoboundary0 P A4 S (extendRZFaceWord P S z word) =
      extendRZLocalEdgeWord P S z
        (doubleCylinderBoundary2 (transposePresentation P) z S word) := by
  classical
  let lhs : Word Field (ZDoubleCylinderFace P z S) →ₗ[Field]
      Word Field (RZQ P S) :=
    (rzCoboundary0 P A4 S).comp (extendRZFaceWord P S z)
  let rhs : Word Field (ZDoubleCylinderFace P z S) →ₗ[Field]
      Word Field (RZQ P S) :=
    (extendRZLocalEdgeWord P S z).comp
      (doubleCylinderBoundary2 (transposePresentation P) z S)
  have hmaps : lhs = rhs := by
    apply linearMap_ext_canonicalBasis
    intro face
    ext target
    have hbasis : canonicalBasisWord (F := Field) face = Pi.single face 1 := by
      ext other
      simp [canonicalBasisWord, Pi.single_apply]
    have hembed : extendRZFaceWord P S z (canonicalBasisWord face) =
        canonicalBasisWord (Sum.inl (Sum.inl ⟨z, face⟩) : RZX P S) := by
      rw [hbasis]
      unfold extendRZFaceWord
      rw [wordPushforward_single]
      ext target
      simp [canonicalBasisWord, Pi.single_apply]
    simp only [lhs, rhs, LinearMap.comp_apply]
    rw [hembed]
    unfold rzCoboundary0
    have hcob := tannerCoboundary0_canonicalBasis_apply
      (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
      (Sum.inl (Sum.inl ⟨z, face⟩) : RZX P S) target
    apply hcob.trans
    rcases target with ⟨otherZ, edge⟩ | qVertex
    · by_cases hz : otherZ = z
      · subst otherZ
        change (if rzXQIncidence P A4.toTannerSquareAdmissible S
          (Sum.inl (Sum.inl ⟨z, face⟩)) (Sum.inl ⟨z, edge⟩) = true
          then 1 else 0) = _
        unfold extendRZLocalEdgeWord
        rw [wordPushforward_apply]
        simp only [Sum.inl.injEq, Sigma.mk.injEq, true_and]
        rw [Fintype.sum_eq_single edge]
        · erw [doubleCylinderBoundary2_canonicalBasis_apply]
          generalize hvalue : doubleCylinderFaceEdgeMatrix
            (transposePresentation P) z S edge face = value
          fin_cases value
          · have hinc : rzXQIncidence P A4.toTannerSquareAdmissible S
                (Sum.inl (Sum.inl ⟨z, face⟩)) (Sum.inl ⟨z, edge⟩) = false := by
              simp only [rzXQIncidence, decide_eq_false_iff_not]
              rintro ⟨h, hmatrix⟩
              have hmatrix' : doubleCylinderFaceEdgeMatrix
                  (transposePresentation P) z S edge face = 1 := by
                simpa using hmatrix
              rw [hvalue] at hmatrix'
              exact zero_ne_one hmatrix'
            rw [hinc]
            simp only [Bool.false_eq_true, if_false]
            erw [if_pos (HEq.rfl)]
            exact Fin.ext rfl
          · have hinc : rzXQIncidence P A4.toTannerSquareAdmissible S
                (Sum.inl (Sum.inl ⟨z, face⟩)) (Sum.inl ⟨z, edge⟩) = true := by
              simp only [rzXQIncidence, decide_eq_true_eq]
              exact ⟨by trivial, hvalue⟩
            rw [hinc]
            simp only [if_pos]
            erw [if_pos (HEq.rfl)]
            exact Fin.ext rfl
        · intro other hne
          rw [if_neg]
          intro heq
          exact hne (eq_of_heq heq).symm
      · have hinc : rzXQIncidence P A4.toTannerSquareAdmissible S
            (Sum.inl (Sum.inl ⟨z, face⟩)) (Sum.inl ⟨otherZ, edge⟩) = false := by
          simp only [rzXQIncidence, decide_eq_false_iff_not]
          intro hexists
          obtain ⟨hz', _⟩ := hexists
          exact hz hz'
        unfold extendRZLocalEdgeWord
        change (if rzXQIncidence P A4.toTannerSquareAdmissible S
          (Sum.inl (Sum.inl ⟨z, face⟩)) (Sum.inl ⟨otherZ, edge⟩) = true
          then 1 else 0) = _
        rw [hinc]
        simp only [Bool.false_eq_true, if_false]
        rw [wordPushforward_apply]
        symm
        apply Finset.sum_eq_zero
        intro source _
        rw [if_neg]
        intro heq
        have hsigma := Sum.inl.inj heq
        exact hz (congrArg Sigma.fst hsigma)
    · have hinc : rzXQIncidence P A4.toTannerSquareAdmissible S
          (Sum.inl (Sum.inl ⟨z, face⟩)) (Sum.inr qVertex) = false := rfl
      unfold extendRZLocalEdgeWord
      change (if rzXQIncidence P A4.toTannerSquareAdmissible S
        (Sum.inl (Sum.inl ⟨z, face⟩)) (Sum.inr qVertex) = true
        then 1 else 0) = _
      rw [hinc]
      simp only [Bool.false_eq_true, if_false]
      rw [wordPushforward_apply]
      symm
      apply Finset.sum_eq_zero
      intro source _
      rw [if_neg]
      exact Sum.inr_ne_inl
  have happ := LinearMap.congr_fun hmaps word
  simpa [lhs, rhs, LinearMap.comp_apply] using happ

private theorem rzXQVertex_heq
    (P : TannerSquarePresentation) (S : OddScale) (copy : Two)
    {q q' : P.Q} {x x' : P.X} (hq : q = q') (hx : x = x')
    (h : P.xq x q = true) (h' : P.xq x' q' = true) :
    HEq (rzXQVertex P q x h S copy) (rzXQVertex P q' x' h' S copy) := by
  cases hq
  cases hx
  rfl

/-- Exact incidence of a retained old-X copy: one terminal in each incident
Q-cylinder, and no Z-local edge. -/
theorem rzOldX_incidence_iff
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (copy : Two) (target : RZQ P S) :
    rzXQIncidence P A S (Sum.inr (x, copy)) target = true ↔
      ∃ q : P.Q, ∃ hxq : P.xq x q = true,
        target = Sum.inr ⟨q, rzXQVertex P q x hxq S copy⟩ := by
  classical
  rcases target with localEdge | qVertex
  · simp [rzXQIncidence]
  · simp only [rzXQIncidence, decide_eq_true_eq]
    constructor
    · rintro ⟨face, corner, rfl, htarget⟩
      exact ⟨P.faceQ face corner, P.data.faceQ_xq face corner, htarget.symm⟩
    · rintro ⟨q, hxq, htarget⟩
      have htarget' := Sum.inr.inj htarget
      subst qVertex
      let z := (A.qzRoot q).1
      let shared : SharedQ P.data x z :=
        ⟨q, by simp [z, hxq, (A.qzRoot q).2]⟩
      obtain ⟨⟨face, corner⟩, hshared⟩ := (P.perfectPairing x z).2 shared
      have hq : P.faceQ face.1 corner = q := congrArg Subtype.val hshared
      refine ⟨face.1, corner, face.2.1, ?_⟩
      simp only [oldXFaceQ, rzXQVertex, Sum.inr.injEq, Sigma.mk.injEq]
      refine ⟨hq, ?_⟩
      exact rzXQVertex_heq P S copy hq face.2.1
        (P.data.faceQ_xq face.1 corner) hxq

/-- Coboundary of the retained old-X copy, as the explicit sum of its local
terminal coordinates. -/
theorem rzOldX_delta0
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) :
    rzCoboundary0 P A4 S
        (canonicalBasisWord (Sum.inr (x, copy) : RZX P S)) =
      ∑ q : P.Q, if hxq : P.xq x q = true then
        canonicalBasisWord
          (Sum.inr ⟨q, rzXQVertex P q x hxq S copy⟩ : RZQ P S)
      else 0 := by
  classical
  ext target
  change tannerCoboundary0 (rzReplacementPresentation P
    A4.toTannerSquareAdmissible S) _ target = _
  erw [tannerCoboundary0_canonicalBasis_apply]
  change (if rzXQIncidence P A4.toTannerSquareAdmissible S
    (Sum.inr (x, copy)) target = true then (1 : Field) else 0) = _
  rcases target with localEdge | qVertex
  · simp only [rzXQIncidence, Bool.false_eq_true, if_false, Finset.sum_apply]
    symm
    apply Finset.sum_eq_zero
    intro q _
    by_cases h : P.xq x q = true <;> simp [h, canonicalBasisWord, Pi.single_apply]
  · simp only [rzOldX_incidence_iff]
    rw [Finset.sum_apply, Finset.sum_eq_single qVertex.1]
    · by_cases hxq : P.xq x qVertex.1 = true
      · rw [dif_pos hxq]
        have hindex :
            (∃ q : P.Q, ∃ h : P.xq x q = true,
              (Sum.inr qVertex : RZQ P S) =
                Sum.inr ⟨q, rzXQVertex P q x h S copy⟩) ↔
              (Sum.inr qVertex : RZQ P S) =
                Sum.inr ⟨qVertex.1, rzXQVertex P qVertex.1 x hxq S copy⟩ := by
          constructor
          · rintro ⟨q, h, heq⟩
            have hq : qVertex.1 = q := congrArg Sigma.fst (Sum.inr.inj heq)
            subst q
            exact heq
          · intro h
            exact ⟨qVertex.1, hxq, h⟩
        simp only [hindex]
        simp [canonicalBasisWord, Pi.single_apply]
      · rw [dif_neg hxq]
        have hnone : ¬ ∃ q : P.Q, ∃ h : P.xq x q = true,
            (Sum.inr qVertex : RZQ P S) =
              Sum.inr ⟨q, rzXQVertex P q x h S copy⟩ := by
          rintro ⟨q, h, heq⟩
          have hq := congrArg Sigma.fst (Sum.inr.inj heq)
          exact hxq (hq.symm ▸ h)
        simp only [if_neg hnone, Pi.zero_apply]
    · intro q _ hq
      by_cases hxq : P.xq x q = true
      · rw [dif_pos hxq]
        have hne : (Sum.inr qVertex : RZQ P S) ≠
            Sum.inr ⟨q, rzXQVertex P q x hxq S copy⟩ := by
          intro heq
          exact hq (congrArg Sigma.fst (Sum.inr.inj heq)).symm
        simp [canonicalBasisWord, hne]
      · rw [dif_neg hxq]
        rfl
    · simp

/-- An old face lying over the requested old X/Z coordinate pair. -/
abbrev RZOldFaceOver (P : TannerSquarePresentation) (x : P.X) (z : P.Z) :=
  { face : P.Face // P.faceX face = x ∧ P.faceZ face = z }

/-- The same old face, viewed structurally in the transposed Z-star. -/
def rzOldFaceOverZStarFace
    (P : TannerSquarePresentation) (x : P.X) (z : P.Z)
    (owner : RZOldFaceOver P x z) : XStarFace (transposePresentation P) z :=
  ⟨owner.1, by
    change decide (P.faceZ owner.1 = z) = true
    exact decide_eq_true owner.2.2⟩

/-- The copy-zero extension sends a single subdivision edge to its tagged copy. -/
@[simp] theorem extendCopyZeroSubdivisionEdgeWord_canonicalBasis
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : SubdivisionEdge P x S) :
    extendCopyZeroSubdivisionEdgeWord P x S (canonicalBasisWord edge) =
      canonicalBasisWord (Sum.inl (0, edge) : DoubleCylinderEdge P x S) := by
  classical
  ext target
  rcases target with ⟨copy, other⟩ | vertical
  · fin_cases copy <;> simp [extendCopyZeroSubdivisionEdgeWord, canonicalBasisWord, Pi.single_apply]
  · simp [extendCopyZeroSubdivisionEdgeWord, canonicalBasisWord, Pi.single_apply]

/-- The Q-cylinder arm embeds as the corresponding outer Q-Z side of an
incident transposed face.  All segments retain their original incidence tag. -/
theorem rzMap0QRay_image_face_side
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (z : P.Z)
    (owner : RZOldFaceOver P x z) (corner : Two)
    (hxq : P.xq x (P.faceQ owner.1 corner) = true)
    (hqz : P.qz (P.faceQ owner.1 corner) z = true) :
    rzQZDegreeZero P A (P.faceQ owner.1 corner) z hqz S
        (rzMap0QRay P S x (P.faceQ owner.1 corner) hxq) =
      ∑ i : Fin S.half, canonicalBasisWord
        (Sum.inl (0, Sum.inl
          (xStarFaceQZEdge (transposePresentation P) z
            (rzOldFaceOverZStarFace P x z owner) corner, i)) :
          ZDoubleCylinderEdge P z S) := by
  classical
  unfold rzQZDegreeZero rzMap0QRay
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [wordPushforward_canonicalBasis]
  congr 1
  apply congrArg Sum.inl
  change (0, Sum.inl _) = (0, Sum.inl _)
  congr 2
  change (_, i) = (_, i)
  congr 1
  apply Subtype.ext
  apply congrArg Sum.inr
  apply Subtype.ext
  change (P.faceQ owner.1 corner, x) = (P.faceQ owner.1 corner, P.faceX owner.1)
  exact Prod.ext rfl owner.2.1.symm

/-- A whole copied face contributes its two radial connector arms and its
two outer Q-cylinder arms, without any interior edge. -/
theorem rzWholeFace_four_sides
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (z : P.Z)
    (owner : RZOldFaceOver P x z) :
    extendCopyZeroSubdivisionEdgeWord (transposePresentation P) z S
      (subdivisionBoundary2 (transposePresentation P) z S
        (subdivisionWholeFaceChain (transposePresentation P) z S
          (rzOldFaceOverZStarFace P x z owner))) =
      ∑ corner : Two,
        ((∑ i : Fin S.half, canonicalBasisWord
          (Sum.inl (0, Sum.inl
            (xStarFaceXQEdge (transposePresentation P) z
              (rzOldFaceOverZStarFace P x z owner) corner, i)) :
            ZDoubleCylinderEdge P z S)) +
        (∑ i : Fin S.half, canonicalBasisWord
          (Sum.inl (0, Sum.inl
            (xStarFaceQZEdge (transposePresentation P) z
              (rzOldFaceOverZStarFace P x z owner) corner, i)) :
            ZDoubleCylinderEdge P z S))) := by
  classical
  erw [subdivisionWholeFaceChain_boundary]
  simp only [map_add, map_sum, Fin.sum_univ_two]
  ext target
  rcases target with ⟨copy, edge⟩ | vertex
  · fin_cases copy <;>
      simp [extendCopyZeroSubdivisionEdgeWord, canonicalBasisWord, Pi.single_apply,
        Finset.sum_apply, subdivisionHorizontalEdge, subdivisionVerticalEdge,
        rzGridZero, rzGridLast, S.half_pos.ne'] <;>
      simp only [Finset.card_filter, Nat.cast_sum, apply_ite, Nat.cast_one, Nat.cast_zero] <;>
      ring
  · simp [extendCopyZeroSubdivisionEdgeWord, canonicalBasisWord, Pi.single_apply,
      Finset.sum_apply]

/-- Perfect pairing reindexes any shared-Q sum by the two corners of each
old face.  This is the original presentation equivalence, not a selected face. -/
theorem rzSharedQ_sum_eq_face_corners
    (P : TannerSquarePresentation) (x : P.X) (z : P.Z)
    {Index : Type} (value : P.Q → Word Field Index) :
    (∑ q : P.Q, if P.xq x q && P.qz q z then value q else 0) =
      ∑ owner : RZOldFaceOver P x z, ∑ corner : Two,
        value (P.faceQ owner.1 corner) := by
  classical
  let shared : Finset P.Q := Finset.univ.filter fun q => P.xq x q && P.qz q z
  have hsubtype : (∑ q ∈ shared, value q) =
      ∑ q : SharedQ P.data x z, value q.1 :=
    Finset.sum_subtype shared (by simp [shared]) value
  have hpair : (∑ fc : FaceOver P.data x z × Two,
      value (P.faceQ fc.1.1 fc.2)) =
      ∑ q : SharedQ P.data x z, value q.1 := by
    exact Fintype.sum_equiv (P.faceCornerEquiv x z) _ _ (fun _ => rfl)
  calc
    _ = ∑ q ∈ shared, value q := by rw [Finset.sum_filter]
    _ = ∑ q : SharedQ P.data x z, value q.1 := hsubtype
    _ = ∑ fc : FaceOver P.data x z × Two,
          value (P.faceQ fc.1.1 fc.2) := hpair.symm
    _ = _ := Fintype.sum_prod_type _

/-- The boundary of the chosen face fillings is precisely the connector sum
plus the embedded Q-arm sum. -/
theorem rzMap0_face_boundary_local
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (z : P.Z) :
    (∑ owner : RZOldFaceOver P x z,
      extendCopyZeroSubdivisionEdgeWord (transposePresentation P) z S
        (subdivisionBoundary2 (transposePresentation P) z S
          (subdivisionWholeFaceChain (transposePresentation P) z S
            (rzOldFaceOverZStarFace P x z owner)))) =
      ∑ q : P.Q, if hxq : P.xq x q = true then
        if hqz : P.qz q z = true then
          rzMap1Connector P A4 q z hqz S +
            rzQZDegreeZero P A4.toTannerSquareAdmissible q z hqz S
              (rzMap0QRay P S x q hxq)
        else 0
      else 0 := by
  classical
  let value : P.Q → Word Field (ZDoubleCylinderEdge P z S) := fun q =>
    if hxq : P.xq x q = true then
      if hqz : P.qz q z = true then
        rzMap1Connector P A4 q z hqz S +
          rzQZDegreeZero P A4.toTannerSquareAdmissible q z hqz S
            (rzMap0QRay P S x q hxq)
      else 0
    else 0
  have hfilter : (∑ q : P.Q, if P.xq x q && P.qz q z then value q else 0) =
      ∑ q : P.Q, value q := by
    apply Finset.sum_congr rfl
    intro q _
    by_cases hxq : P.xq x q = true <;>
      by_cases hqz : P.qz q z = true <;> simp [value, hxq, hqz]
  change _ = ∑ q : P.Q, value q
  rw [← hfilter, rzSharedQ_sum_eq_face_corners]
  apply Finset.sum_congr rfl
  intro owner _
  rw [rzWholeFace_four_sides]
  apply Finset.sum_congr rfl
  intro corner _
  have hxq : P.xq x (P.faceQ owner.1 corner) = true := by
    simpa only [owner.2.1] using P.data.faceQ_xq owner.1 corner
  have hqz : P.qz (P.faceQ owner.1 corner) z = true := by
    simpa only [owner.2.2] using P.data.faceQ_qz owner.1 corner
  dsimp only [value]
  rw [dif_pos hxq, dif_pos hqz,
    rzMap0QRay_image_face_side P A4.toTannerSquareAdmissible S x z owner corner
      hxq hqz,
    rzMap1Connector_eq_face_radial P A4 (P.faceQ owner.1 corner) z hqz S
      (rzOldFaceOverZStarFace P x z owner) corner rfl]

/-- The exact explicit local face filling for one old X/Z pair: every old
face over the pair contributes all copy-zero subdivision squares. -/
noncomputable def rzMap0LocalFaceFill
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (z : P.Z) :
    Word Field (RZX P S) :=
  ∑ owner : RZOldFaceOver P x z,
    extendRZFaceWord P S z
      (extendCopyZeroSubdivisionFaceWord (transposePresentation P) z S
        (subdivisionWholeFaceChain (transposePresentation P) z S
          (rzOldFaceOverZStarFace P x z owner)))

/-- Coboundary of the explicit local filling is the sum of the four outer
subdivision sides of every old face over the requested X/Z pair. -/
theorem rzMap0LocalFaceFill_boundary
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (z : P.Z) :
    rzCoboundary0 P A4 S (rzMap0LocalFaceFill P S x z) =
      ∑ owner : RZOldFaceOver P x z,
        extendRZLocalEdgeWord P S z
          (extendCopyZeroSubdivisionEdgeWord (transposePresentation P) z S
            (subdivisionBoundary2 (transposePresentation P) z S
              (subdivisionWholeFaceChain (transposePresentation P) z S
                (rzOldFaceOverZStarFace P x z owner)))) := by
  classical
  unfold rzMap0LocalFaceFill
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro owner _
  erw [rzCoboundary0_extendRZFaceWord, doubleCylinderBoundary2_extendCopyZero]

/-- The fully specified degree-zero image: retained old-X bit, copied arms,
and every copy-zero small square of the old faces incident to that X. -/
noncomputable def rzMap0BasisImage
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    Word Field (RZX P S) :=
  canonicalBasisWord (Sum.inr (x, 0)) +
    (∑ q : P.Q, if hxq : P.xq x q = true then
      extendRZQEdgeWord P S q (rzMap0QRay P S x q hxq) else 0) +
    ∑ z : P.Z, rzMap0LocalFaceFill P S x z

/-- Linear extension of the explicit degree-zero basis table. -/
noncomputable def rzMap0Coord
    (P : TannerSquarePresentation) (S : OddScale) :
    Word Field P.X →ₗ[Field] Word Field (RZX P S) := by
  classical
  exact ClassicalWeightReduction.linearMapOfBasisImages
    (F := Field) (rzMap0BasisImage P S)

@[simp] theorem rzMap0Coord_canonicalBasis
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    rzMap0Coord P S (canonicalBasisWord x) = rzMap0BasisImage P S x := by
  classical
  have hbasis : canonicalBasisWord (F := Field) x = Pi.single x 1 := by
    ext coordinate
    simp [canonicalBasisWord, Pi.single_apply]
  rw [hbasis]
  exact ClassicalWeightReduction.linearMapOfBasisImages_single
    (F := Field) (rzMap0BasisImage P S) x

/-- Sum the exact face boundaries by their incident Q coordinates. -/
theorem rzMap0_all_face_boundaries
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) :
    (∑ z : P.Z, rzCoboundary0 P A4 S (rzMap0LocalFaceFill P S x z)) =
      ∑ q : P.Q, if hxq : P.xq x q = true then
        ∑ z : P.Z, if hqz : P.qz q z = true then
          extendRZLocalEdgeWord P S z
            (rzMap1Connector P A4 q z hqz S +
              rzQZDegreeZero P A4.toTannerSquareAdmissible q z hqz S
                (rzMap0QRay P S x q hxq))
        else 0
      else 0 := by
  classical
  have hlocal (z : P.Z) : rzCoboundary0 P A4 S (rzMap0LocalFaceFill P S x z) =
      ∑ q : P.Q, if hxq : P.xq x q = true then
        if hqz : P.qz q z = true then
          extendRZLocalEdgeWord P S z
            (rzMap1Connector P A4 q z hqz S +
              rzQZDegreeZero P A4.toTannerSquareAdmissible q z hqz S
                (rzMap0QRay P S x q hxq)) else 0 else 0 := by
    rw [rzMap0LocalFaceFill_boundary, ← map_sum]
    erw [rzMap0_face_boundary_local P A4 S x z, map_sum]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hxq : P.xq x q = true <;>
      by_cases hqz : P.qz q z = true <;> simp [hxq, hqz]
  simp_rw [hlocal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hxq : P.xq x q = true
  · simp only [dif_pos hxq]
  · simp [hxq]

/-- Explicit degree-zero construction commutes on every old-X basis vector.
The old terminal and outer-arm terms occur twice and cancel in the binary field. -/
theorem rzMap0BasisImage_delta0
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) :
    rzCoboundary0 P A4 S (rzMap0BasisImage P S x) =
      map1Coord P A4 S (tannerCoboundary0 P (canonicalBasisWord x)) := by
  classical
  have hdelta : tannerCoboundary0 P (canonicalBasisWord x) =
      ∑ q : P.Q, if P.xq x q = true then canonicalBasisWord q else 0 := by
    ext q
    rw [tannerCoboundary0_canonicalBasis_apply]
    rw [Finset.sum_apply, Finset.sum_eq_single q]
    · by_cases h : P.xq x q = true <;> simp [h, canonicalBasisWord, Pi.single_apply]
    · intro other _ hne
      by_cases h : P.xq x other = true <;> simp [h, canonicalBasisWord, Pi.single_apply, hne]
    · simp
  rw [rzMap0BasisImage, map_add, map_add, map_sum, map_sum,
    rzOldX_delta0, rzMap0_all_face_boundaries, hdelta, map_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hxq : P.xq x q = true
  · simp only [dif_pos hxq, if_pos hxq]
    rw [rzMap0QRay_delta0, map1Coord_canonicalBasis]
    unfold map1BasisImage
    have hconnect :
        (∑ z : P.Z, if hqz : P.qz q z = true then
          extendRZLocalEdgeWord P S z
            (rzMap1Connector P A4 q z hqz S +
              rzQZDegreeZero P A4.toTannerSquareAdmissible q z hqz S
                (rzMap0QRay P S x q hxq)) else 0) =
        (∑ z : P.Z, if hqz : P.qz q z = true then
          extendZEdgeWord P S z (rzMap1Connector P A4 q z hqz S) else 0) +
        (∑ z : P.Z, if hqz : P.qz q z = true then
          extendRZLocalEdgeWord P S z
            (rzQZDegreeZero P A4.toTannerSquareAdmissible q z hqz S
              (rzMap0QRay P S x q hxq)) else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hqz : P.qz q z = true
      · simp only [dif_pos hqz, map_add, extendRZLocalEdgeWord_eq]
      · simp [hqz]
    rw [hconnect]
    change canonicalBasisWord _ + (canonicalBasisWord _ + canonicalBasisWord _ + _) +
      (_ + _) = canonicalBasisWord _ + _
    abel_nf <;> simp [two_smul, ZModModule.add_self]
    change canonicalBasisWord (Sum.inr ⟨q, rzMap1QRoot P q S⟩ : RZQ P S) + _ =
      _ + canonicalBasisWord (Sum.inr ⟨q, rzMap1QRoot P q S⟩ : RZQ P S)
    exact add_comm _ _
  · simp [hxq]

/-- The explicit RZ degree-zero/one maps commute with the actual successor
coboundary on all finite words. -/
theorem rzMap_commutes_coboundary0
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) :
    (rzCoboundary0 P A4 S).comp (rzMap0Coord P S) =
      (map1Coord P A4 S).comp (tannerCoboundary0 P) := by
  classical
  apply linearMap_ext_canonicalBasis
  intro x
  simpa only [LinearMap.comp_apply, rzMap0Coord_canonicalBasis] using
    rzMap0BasisImage_delta0 P A4 S x

/-- Data-only assembly of the three concrete RZ coordinate maps. -/
structure RZCochainMapData (P : TannerSquarePresentation) (S : OddScale) where
  map0 : Word Field P.X →ₗ[Field] Word Field (RZX P S)
  map1 : Word Field P.Q →ₗ[Field] Word Field (RZQ P S)
  map2 : Word Field P.Z →ₗ[Field] Word Field (RZZ P S)

/-- The explicit RZ maps; their compatibility is a theorem obligation. -/
noncomputable def rzCochainMap
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) : RZCochainMapData P S where
  map0 := rzMap0Coord P S
  map1 := map1Coord P A4 S
  map2 := map2Coord P A4 S

/-- The concrete successor RZ degree-one coboundary. -/
noncomputable def rzCoboundary1
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) : Word Field (RZQ P S) →ₗ[Field] Word Field (RZZ P S) :=
  tannerCoboundary1
    (rzReplacementPresentation P A4.toTannerSquareAdmissible S)

/-- Existing #838 degree-one basis commutation, promoted to all finite words
by canonical-basis extensionality. -/
theorem rzMap_commutes_coboundary1
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) :
    (rzCoboundary1 P A4 S).comp (map1Coord P A4 S) =
      (map2Coord P A4 S).comp (tannerCoboundary1 P) := by
  classical
  apply linearMap_ext_canonicalBasis
  intro q
  change tannerCoboundary1
    (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
    (map1Coord P A4 S (canonicalBasisWord q)) = _
  exact map1Coord_delta1_canonicalBasis P A4 S q

/-- Constructor-defined singleton image of an old-Z basis coordinate. -/
noncomputable def rzMap2BasisImage
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) : Word Field (RZZ P S) :=
  canonicalBasisWord ⟨z, rzMap1ZRoot P A4 z S⟩

@[simp] theorem rzMap2BasisImage_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) :
    map2Coord P A4 S (canonicalBasisWord z) =
      rzMap2BasisImage P A4 S z :=
  map2Coord_canonicalBasis P A4 S z

/-- Exact constructor region of the selected RZ Z-root. -/
noncomputable def rzMap2ParentRegion
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) : Finset (RZZ P S) := by
  classical
  exact Finset.univ.filter fun target =>
    target = ⟨z, rzMap1ZRoot P A4 z S⟩

theorem rzMap2BasisImage_ne_zero_iff_mem_parentRegion
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (target : RZZ P S) :
    rzMap2BasisImage P A4 S z target ≠ 0 ↔
      target ∈ rzMap2ParentRegion P A4 S z := by
  classical
  unfold rzMap2BasisImage rzMap2ParentRegion canonicalBasisWord
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.single_apply]
  by_cases h : target = ⟨z, rzMap1ZRoot P A4 z S⟩ <;> simp [h]

theorem rzMap2BasisImage_support_eq_parentRegion
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) :
    hammingSupport (rzMap2BasisImage P A4 S z) =
      rzMap2ParentRegion P A4 S z := by
  classical
  ext target
  simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  exact rzMap2BasisImage_ne_zero_iff_mem_parentRegion P A4 S z target

/-- Raw #842 basis table for the existing #838 RZ degree-two map. -/
noncomputable def rzMap2FiniteBasisAction
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) : TypedFiniteBasisAction (map2Coord P A4 S) where
  basisImage := rzMap2BasisImage P A4 S
  basis_action := rzMap2BasisImage_eq P A4 S

/-- Raw extension-by-zero/support/image witness for the existing #838 RZ
degree-two coordinate map. -/
noncomputable def rzMap2ExtensionZeroLocalSupportImage
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) :
    @ExtensionZeroLocalSupportImage P.Z P.Z (RZZ P S)
      inferInstance inferInstance inferInstance
      (Classical.decEq P.Z) (Classical.decEq (RZZ P S))
      (map2Coord P A4 S) := by
  classical
  letI : DecidableEq P.Z := Classical.decEq _
  letI : DecidableEq (RZZ P S) := Classical.decEq _
  exact {
    sourceRegion := fun z => {z}
    targetRegion := rzMap2ParentRegion P A4 S
    extensionByZero := fun z => zeroExtendWord ({z} : Finset P.Z)
    extension_zero := by
      intro z localWord source hsource
      change (if h : source ∈ ({z} : Finset P.Z) then
        localWord ⟨source, h⟩ else 0) = 0
      rw [dif_neg hsource]
    extension_on_region := by
      intro z localWord source
      change (if h : source.1 ∈ ({z} : Finset P.Z) then
        localWord ⟨source.1, h⟩ else 0) = localWord source
      simp
    selectedMapBasisImage := rzMap2BasisImage P A4 S
    selectedMap_basis_action := rzMap2BasisImage_eq P A4 S
    selectedMap_basis_support := by
      intro owner source target hsource htarget
      have hsourceEq : source = owner := by simpa using hsource
      subst source
      by_contra hnonzero
      exact htarget ((rzMap2BasisImage_ne_zero_iff_mem_parentRegion
        P A4 S owner target).1 hnonzero)
    selectedMap_basis_image := by
      intro owner source target hsource hnonzero
      have hsourceEq : source = owner := by simpa using hsource
      subst source
      exact (rzMap2BasisImage_ne_zero_iff_mem_parentRegion
        P A4 S owner target).1 hnonzero }


/-! ## Finite composition of proved cochain identities -/

/-- Compose a finite sequence of linear coordinate maps in traversal order. -/
def finiteCoordinateComposite {Coordinate : Nat → Type}
    (step : ∀ n, Word Field (Coordinate n) →ₗ[Field] Word Field (Coordinate (n + 1))) :
    ∀ n, Word Field (Coordinate 0) →ₗ[Field] Word Field (Coordinate n)
  | 0 => LinearMap.id
  | n + 1 => (step n).comp (finiteCoordinateComposite step n)

/-- Finite composition preserves separately proved adjacent cochain identities.
This algebraic lemma does not identify a raw complex with a different presentation. -/
theorem finiteCoordinateComposite_commutes
    {Source Target : Nat → Type}
    (sourceStep : ∀ n, Word Field (Source n) →ₗ[Field] Word Field (Source (n + 1)))
    (targetStep : ∀ n, Word Field (Target n) →ₗ[Field] Word Field (Target (n + 1)))
    (boundary : ∀ n, Word Field (Source n) →ₗ[Field] Word Field (Target n))
    (commutes : ∀ n, (boundary (n + 1)).comp (sourceStep n) =
      (targetStep n).comp (boundary n)) (n : Nat) :
    (boundary n).comp (finiteCoordinateComposite sourceStep n) =
      (finiteCoordinateComposite targetStep n).comp (boundary 0) := by
  induction n with
  | zero => simp [finiteCoordinateComposite]
  | succ n ih =>
      simp only [finiteCoordinateComposite]
      rw [← LinearMap.comp_assoc, commutes, LinearMap.comp_assoc, ih,
        ← LinearMap.comp_assoc]

/-- The two concrete RX cochain identities target the assembled raw RX complex. -/
theorem rxCochainMap_identities
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (S : OddScale) :
    (rxCoboundary0 P S).comp (rxMap P S).map0 =
        (rxMap P S).map1.comp (tannerCoboundary0 P) ∧
      (rxCoboundary1 P S).comp (rxMap P S).map1 =
        (rxMap P S).map2.comp (tannerCoboundary1 P) := by
  exact ⟨rxMap_commutes_coboundary0 P A S, rxMap_commutes_coboundary1 P S⟩

/-- The two explicit RZ cochain identities use the materialized successor. -/
theorem rzCochainMap_identities
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) :
    (rzCoboundary0 P A4 S).comp (rzCochainMap P A4 S).map0 =
        (rzCochainMap P A4 S).map1.comp (tannerCoboundary0 P) ∧
      (rzCoboundary1 P A4 S).comp (rzCochainMap P A4 S).map1 =
        (rzCochainMap P A4 S).map2.comp (tannerCoboundary1 P) := by
  exact ⟨rzMap_commutes_coboundary0 P A4 S, rzMap_commutes_coboundary1 P A4 S⟩

end QEC.Coding.BDL26ReplacementCochainMaps
