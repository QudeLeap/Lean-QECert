import QEC.Coding.Core.Duality
import QEC.Coding.FiniteAlternatingConstruction.RXSeedSmallSupport
import QEC.Coding.FiniteAlternatingConstruction.ReplacementSupport
import QEC.Coding.FiniteAlternatingConstruction.LevelTwoCode
import QEC.Coding.FiniteAlternatingConstruction.AlternatingCochain

/-!
# Local proof closure for the concrete level-two code

This file constructs nontrivial logical representatives and attained finite
sector minima for the actual two-step incidence complex. The coordinate lemmas
also establish two-region separation by projecting cocycles through the
replacement blocks and constructing coboundary potentials.
-/

namespace QEC.Coding.BDL26LevelTwoDistance

open scoped BigOperators
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26LevelTwoCode

abbrev Field := BDL26FiniteTannerSquare.Field

noncomputable local instance rzQDecidableEq (P : TannerSquarePresentation) (S : OddScale) :
    DecidableEq (RZQ P S) := Classical.decEq _

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



/-- The explicit nontrivial seed cocycle uses the two endpoints of the first
Z-check, excluding the common fifth qubit. -/
def seedCocycle : Word Field BaseQubit := ![1, 0, 1, 0, 0]

/-- The explicit dual seed cycle intersects `seedCocycle` once. -/
def seedCycle : Word Field BaseQubit := ![1, 1, 0, 0, 0]

theorem seedCocycle_coboundary :
    tannerCoboundary1 baseTannerSquarePresentation seedCocycle = 0 := by
  decide

theorem seedCycle_boundary : baseBoundary1 seedCycle = 0 := by
  decide

theorem seedCocycle_not_coboundary :
    ∀ potential : Word Field BaseX,
      tannerCoboundary0 baseTannerSquarePresentation potential ≠ seedCocycle := by
  intro potential heq
  have hc : tannerCoboundary0 baseTannerSquarePresentation potential (0 : BaseQubit) =
      tannerCoboundary0 baseTannerSquarePresentation potential (1 : BaseQubit) := by rfl
  rw [heq] at hc
  norm_num [seedCocycle] at hc

/-- Equal actual syndromes make the error sum a cocycle, before any locality
argument is used. -/
theorem sameSyndrome_add_cocycle (S : OddScale)
    (first second : Word Field (levelTwoPresentation S).Q)
    (h : tannerCoboundary1 (levelTwoPresentation S) first =
      tannerCoboundary1 (levelTwoPresentation S) second) :
    tannerCoboundary1 (levelTwoPresentation S) (first + second) = 0 := by
  rw [map_add, h]
  exact ZModModule.add_self _

/-- Sum the concrete shifted Q-cylinder coordinates. Auxiliary Z-local edges
are discarded; this is a coordinate map, not a cohomology oracle. -/
noncomputable def rzQParity (P : TannerSquarePresentation) (S : OddScale) :
    Word Field (RZQ P S) →ₗ[Field] Word Field P.Q where
  toFun := fun word q => ∑ vertex : QDoubleCylinderVertex (transposePresentation P) q S,
    word (Sum.inr ⟨q, vertex⟩)
  map_add' := by intros; ext q; simp [Finset.sum_add_distrib]
  map_smul' := by intros; ext q; simp [Finset.mul_sum]

@[simp] theorem rzQParity_extendZEdgeWord (P : TannerSquarePresentation)
    (S : OddScale) (z : P.Z) (word : Word Field (ZDoubleCylinderEdge P z S)) :
    rzQParity P S (extendZEdgeWord P S z word) = 0 := by
  ext q
  simp [rzQParity, extendZEdgeWord]

@[simp] theorem rzQParity_single (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (vertex : QDoubleCylinderVertex (transposePresentation P) q S)
    (value : Field) :
    rzQParity P S (Pi.single (Sum.inr ⟨q, vertex⟩) value) = Pi.single q value := by
  classical
  ext other
  by_cases h : other = q
  · subst other
    simp [rzQParity, Pi.single_apply]
  · have hcoord : ∀ v : QDoubleCylinderVertex (transposePresentation P) other S,
        (Sum.inr ⟨other, v⟩ : RZQ P S) ≠ Sum.inr ⟨q, vertex⟩ := by
      intro v heq
      exact h (congrArg Sigma.fst (Sum.inr.inj heq))
    simp [rzQParity, Pi.single_apply, h, hcoord]

/-- The chosen RZ degree-one basis image has Q parity exactly its old basis
coordinate. Its connecting paths live in the discarded Z-edge summands. -/
theorem rzQParity_map1BasisImage (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (q : P.Q) :
    rzQParity P S (map1BasisImage P A4 S q) = Pi.single q 1 := by
  classical
  unfold map1BasisImage
  rw [map_add, map_sum]
  have hz : (∑ z : P.Z, rzQParity P S
      (if hqz : P.qz q z = true then
        extendZEdgeWord P S z (rzMap1Connector P A4 q z hqz S) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro z _
    split <;> simp
  rw [hz, add_zero]
  exact rzQParity_single P S q (rzMap1QRoot P q S) 1

/-- The RZ degree-one coordinate map has this explicit left inverse. -/
theorem rzQParity_map1Coord (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale)
    (word : Word Field P.Q) :
    rzQParity P S (map1Coord P A4 S word) = word := by
  classical
  have hmaps : (rzQParity P S).comp (map1Coord P A4 S) = LinearMap.id := by
    apply linearMap_ext_canonicalBasis
    intro q
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    erw [map1Coord_canonicalBasis]
    refine (rzQParity_map1BasisImage P A4 S q).trans ?_
    funext other
    by_cases h : other = q <;> simp [canonicalBasisWord, Pi.single_apply, h]
  exact LinearMap.congr_fun hmaps word


/-- A Z-local edge basis word has no shifted Q-cylinder parity. -/
@[simp] theorem rzQParity_localBasis (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (edge : ZDoubleCylinderEdge P z S) :
    rzQParity P S (canonicalBasisWord (Sum.inl ⟨z, edge⟩ : RZQ P S)) = 0 := by
  classical
  ext q
  simp [rzQParity, canonicalBasisWord]

@[simp] theorem rzQParity_qBasis (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (vertex : QDoubleCylinderVertex (transposePresentation P) q S) :
    rzQParity P S (canonicalBasisWord (Sum.inr ⟨q, vertex⟩ : RZQ P S)) =
      canonicalBasisWord q := by
  classical
  funext other
  by_cases h : other = q
  · subst other
    simp [rzQParity, canonicalBasisWord, Pi.single_apply, Sigma.mk.injEq]
  · have hcoord : ∀ v : QDoubleCylinderVertex (transposePresentation P) other S,
        (Sum.inr ⟨other, v⟩ : RZQ P S) ≠ Sum.inr ⟨q, vertex⟩ := by
      intro v heq
      exact h (congrArg Sigma.fst (Sum.inr.inj heq))
    simp [rzQParity, canonicalBasisWord, Pi.single_apply, h, hcoord]


/-- The only old degree-zero contribution is the sum of its two retained
copies. No potential or boundary conclusion is stored in this map. -/
def rzOldXParity (P : TannerSquarePresentation) (S : OddScale) :
    Word Field (RZX P S) →ₗ[Field] Word Field P.X where
  toFun := fun potential x => potential (Sum.inr (x, 0)) + potential (Sum.inr (x, 1))
  map_add' := by
    intro first second
    funext x
    exact add_add_add_comm _ _ _ _
  map_smul' := by
    intro coefficient potential
    funext x
    change coefficient * potential (Sum.inr (x, 0)) + coefficient * potential (Sum.inr (x, 1)) =
      coefficient * (potential (Sum.inr (x, 0)) + potential (Sum.inr (x, 1)))
    exact (mul_add _ _ _).symm

/-- The parity of an auxiliary local-face coboundary vanishes. -/
theorem rzQParity_localFace_coboundary (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale)
    (z : P.Z) (face : ZDoubleCylinderFace P z S) :
    rzQParity P S (rzCoboundary0 P A4 S
      (canonicalBasisWord (Sum.inl (Sum.inl ⟨z, face⟩) : RZX P S))) = 0 := by
  classical
  ext q
  change (∑ vertex : QDoubleCylinderVertex (transposePresentation P) q S,
    tannerCoboundary0 (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
      (canonicalBasisWord (Sum.inl (Sum.inl ⟨z, face⟩) : RZX P S))
      (Sum.inr ⟨q, vertex⟩)) = 0
  apply Finset.sum_eq_zero
  intro vertex _
  erw [tannerCoboundary0_canonicalBasis_apply]
  rfl

/-- Each Q-edge has exactly two endpoints in one shifted Q block. Their
parities cancel; all its adjacent Z-edge terms have zero Q parity. -/
theorem rzQParity_qEdge_coboundary (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale)
    (q : P.Q) (edge : QDoubleCylinderEdge (transposePresentation P) q S) :
    rzQParity P S (rzCoboundary0 P A4 S
      (canonicalBasisWord (rzMap1QEdgeX P S q edge))) = 0 := by
  classical
  unfold rzCoboundary0
  erw [rzMap1QEdge_delta0_canonicalBasis]
  unfold rzMap1QEdgeDelta0BasisImage
  rw [map_add, map_add, map_sum, rzQParity_qBasis, rzQParity_qBasis]
  have hz : (∑ z : P.Z, rzQParity P S
      (if hqz : P.qz q z = true then
        canonicalBasisWord (Sum.inl ⟨z, qToZDoubleCylinderEdge P
          A4.toTannerSquareAdmissible q z hqz S edge⟩ : RZQ P S)
      else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro z _
    split <;> simp
  rw [hz, add_zero]
  exact ZModModule.add_self _

/-- An old-X copy contributes exactly the old Tanner coboundary in Q parity. -/
theorem rzQParity_oldX_coboundary (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (x : P.X)
    (copy : BDL26FiniteTannerSquare.Two) :
    rzQParity P S (rzCoboundary0 P A4 S
      (canonicalBasisWord (Sum.inr (x, copy) : RZX P S))) =
      tannerCoboundary0 P (canonicalBasisWord x) := by
  classical
  rw [rzOldX_delta0, map_sum]
  ext target
  rw [Finset.sum_apply, Finset.sum_eq_single target]
  · rw [tannerCoboundary0_canonicalBasis_apply]
    by_cases hx : P.xq x target = true
    · rw [dif_pos hx, rzQParity_qBasis]
      simp [tannerCoboundary0_canonicalBasis_apply, hx, canonicalBasisWord]
    · simp [hx, tannerCoboundary0_canonicalBasis_apply]
  · intro q _ hq
    by_cases hx : P.xq x q = true
    · rw [dif_pos hx, rzQParity_qBasis]
      simp [canonicalBasisWord, hq, Ne.symm hq]
    · simp [hx]
  · simp

/-- Q-cylinder parity maps every actual RZ first coboundary to an actual old
first coboundary, by checking all three degree-zero coordinate families. -/
theorem rzQParity_coboundary (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale)
    (potential : Word Field (RZX P S)) :
    rzQParity P S (rzCoboundary0 P A4 S potential) =
      tannerCoboundary0 P (rzOldXParity P S potential) := by
  classical
  have hm : (rzQParity P S).comp (rzCoboundary0 P A4 S) =
      (tannerCoboundary0 P).comp (rzOldXParity P S) := by
    apply linearMap_ext_canonicalBasis
    intro coordinate
    simp only [LinearMap.comp_apply]
    rcases coordinate with (⟨z, face⟩ | ⟨q, edge⟩) | ⟨x, copy⟩
    · rw [rzQParity_localFace_coboundary]
      have hzero : rzOldXParity P S
          (canonicalBasisWord (Sum.inl (Sum.inl ⟨z, face⟩) : RZX P S)) = 0 := by
        ext x
        simp [rzOldXParity, canonicalBasisWord]
      rw [hzero, map_zero]
    · change rzQParity P S (rzCoboundary0 P A4 S
          (canonicalBasisWord (rzMap1QEdgeX P S q edge))) = _
      rw [rzQParity_qEdge_coboundary]
      have hzero : rzOldXParity P S
          (canonicalBasisWord (rzMap1QEdgeX P S q edge)) = 0 := by
        ext x
        simp [rzOldXParity, rzMap1QEdgeX, canonicalBasisWord]
      erw [hzero, map_zero]
    · rw [rzQParity_oldX_coboundary]
      have hcopy : rzOldXParity P S
          (canonicalBasisWord (Sum.inr (x, copy) : RZX P S)) = canonicalBasisWord x := by
        ext other
        fin_cases copy <;> simp [rzOldXParity, canonicalBasisWord, Pi.single_apply]
      rw [hcopy]
  exact LinearMap.congr_fun hm potential

/-- A genuine old nonboundary cannot become a first coboundary under the
constructed RZ map. The proof recovers an old potential explicitly. -/
theorem rzMap1_preserves_nonboundary (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (word : Word Field P.Q)
    (hword : ∀ potential, tannerCoboundary0 P potential ≠ word) :
    ∀ potential, rzCoboundary0 P A4 S potential ≠ map1Coord P A4 S word := by
  intro potential heq
  have hparity := congrArg (rzQParity P S) heq
  rw [rzQParity_coboundary, rzQParity_map1Coord] at hparity
  exact hword (rzOldXParity P S potential) hparity


/-- Restricting an actual RX coboundary to one X-local edge gives exactly the
local cylinder coboundary of the restricted potential. -/
theorem rxCoboundary0_localEdge (P : TannerSquarePresentation) (S : OddScale)
    (potential : Word Field (RX0 P S)) (x : P.X)
    (edge : DoubleCylinderEdge P x S) :
    rxCoboundary0 P S potential (Sum.inl ⟨x, edge⟩) =
      wordLinearMapTranspose (rxCx P x S).boundary1
        (fun vertex => potential ⟨x, vertex⟩) edge := by
  classical
  unfold rxCoboundary0 rxBoundary1
  rw [wordLinearMapTranspose_toLin'_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single x]
  · simp only [rxBoundary1Matrix, dite_true]
    change (∑ vertex : DoubleCylinderVertex P x S,
        potential ⟨x, vertex⟩ * doubleCylinderEdgeVertexMatrix P x S vertex edge) =
      wordLinearMapTranspose (Matrix.toLin' (doubleCylinderEdgeVertexMatrix P x S))
        (fun vertex => potential ⟨x, vertex⟩) edge
    exact (wordLinearMapTranspose_toLin'_apply _ _ _).symm
  · intro other _ hother
    simp [rxBoundary1Matrix, hother]
  · simp

/-- A putative potential for an RX image must be constant on every connected
X-cylinder, because the image vanishes on every auxiliary X-local edge. -/
theorem rxPotential_constant_of_boundary_eq_map1 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale)
    (potential : Word Field (RX0 P S)) (word : Word Field P.Q)
    (h : rxCoboundary0 P S potential = rxMap1Coord P S word)
    (x : P.X) (vertex : DoubleCylinderVertex P x S) :
    potential ⟨x, vertex⟩ = potential ⟨x,
      (0, (subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)).1)⟩ := by
  refine rxCxCocycle_eq_boundaryRoot_zeroCopy P A x S
    (fun vertex => potential ⟨x, vertex⟩) ?_ vertex
  ext edge
  have he := congrFun h (Sum.inl ⟨x, edge⟩)
  rw [rxCoboundary0_localEdge, rxMap1Coord_localEdge] at he
  exact he

/-- Recover the old potential by evaluating at the constructed X-block roots.
The Q-cylinder incidence sum then gives the old coboundary equation. -/
theorem rxBoundary_eq_map1_recovers_potential (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale)
    (potential : Word Field (RX0 P S)) (word : Word Field P.Q)
    (h : rxCoboundary0 P S potential = rxMap1Coord P S word) :
    tannerCoboundary0 P (fun x => potential ⟨x,
      (0, (subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)).1)⟩) = word := by
  classical
  ext q
  let root : QDoubleCylinderVertex P q S := (0, Sum.inl (Sum.inl ()))
  have he := congrFun h (Sum.inr ⟨q, root⟩)
  rw [rxMap1Coord_qVertex] at he
  unfold rxCoboundary0 rxBoundary1 at he
  rw [wordLinearMapTranspose_toLin'_apply, Fintype.sum_sigma] at he
  calc
    _ = ∑ x : P.X, ∑ vertex : DoubleCylinderVertex P x S,
        potential ⟨x, vertex⟩ * qDoubleCylinderVertexXIncidence P q x S vertex root := by
      apply Finset.sum_congr rfl
      intro x _
      simp_rw [rxPotential_constant_of_boundary_eq_map1 P A S potential word h]
      rw [← Finset.mul_sum, sum_qVertexXIncidence P A S x q root]
    _ = word q := he

/-- A genuine old nonboundary remains nonboundary under the concrete RX map;
connected local cylinders recover any allegedly existing old potential. -/
theorem rxMap1_preserves_nonboundary (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (word : Word Field P.Q)
    (hword : ∀ potential, tannerCoboundary0 P potential ≠ word) :
    ∀ potential, rxCoboundary0 P S potential ≠ rxMap1Coord P S word := by
  intro potential heq
  exact hword _ (rxBoundary_eq_map1_recovers_potential P A S potential word heq)


open BDL26DecodingGraph

/-- The seed cocycle transported through the actual ordered RX/RZ pair. -/
noncomputable def levelTwoXLogical (S : OddScale) :
    Word Field (levelTwoPresentation S).Q :=
  map1Coord (levelOnePresentation S) (rxState S baseState).admissible S
    (rxMap1Coord baseTannerSquarePresentation S seedCocycle)

/-- The transported word has zero actual level-two syndrome. -/
theorem levelTwoXLogical_cocycle (S : OddScale) :
    tannerCoboundary1 (levelTwoPresentation S) (levelTwoXLogical S) = 0 := by
  have hrx := LinearMap.congr_fun
    (rxMap_commutes_coboundary1 baseTannerSquarePresentation S) seedCocycle
  change rxCoboundary1 baseTannerSquarePresentation S
      (rxMap1Coord baseTannerSquarePresentation S seedCocycle) =
    rxMap2Coord baseTannerSquarePresentation S
      (tannerCoboundary1 baseTannerSquarePresentation seedCocycle) at hrx
  rw [seedCocycle_coboundary, map_zero] at hrx
  have hrx' : tannerCoboundary1 (levelOnePresentation S)
      (rxMap1Coord baseTannerSquarePresentation S seedCocycle) = 0 := by
    change tannerCoboundary1 (rxReplacementPresentation baseTannerSquarePresentation S)
      (rxMap1Coord baseTannerSquarePresentation S seedCocycle) = 0
    erw [rxPresentation_coboundary1_eq _ baseTannerSquareAdmissibleV4
      baseTannerSquareCellularRegular S]
    exact hrx
  have hrz := LinearMap.congr_fun
    (rzMap_commutes_coboundary1 (levelOnePresentation S)
      (rxState S baseState).admissible S)
    (rxMap1Coord baseTannerSquarePresentation S seedCocycle)
  change rzCoboundary1 (levelOnePresentation S) (rxState S baseState).admissible S
      (map1Coord (levelOnePresentation S) (rxState S baseState).admissible S
        (rxMap1Coord baseTannerSquarePresentation S seedCocycle)) =
    map2Coord (levelOnePresentation S) (rxState S baseState).admissible S
      (tannerCoboundary1 (levelOnePresentation S)
        (rxMap1Coord baseTannerSquarePresentation S seedCocycle)) at hrz
  rw [hrx', map_zero] at hrz
  exact hrz

/-- No actual level-two potential realizes the transported seed word. -/
theorem levelTwoXLogical_nonboundary (S : OddScale) :
    ∀ potential, tannerCoboundary0 (levelTwoPresentation S) potential ≠
      levelTwoXLogical S := by
  apply rzMap1_preserves_nonboundary (levelOnePresentation S)
    (rxState S baseState).admissible S
  intro potential heq
  have hx := rxMap1_preserves_nonboundary baseTannerSquarePresentation
    baseTannerSquareAdmissibleV4.toTannerSquareAdmissible S seedCocycle
    seedCocycle_not_coboundary potential
  change tannerCoboundary0 (rxReplacementPresentation baseTannerSquarePresentation S)
    potential = rxMap1Coord baseTannerSquarePresentation S seedCocycle at heq
  erw [rxPresentation_coboundary0_eq _ baseTannerSquareAdmissibleV4
    baseTannerSquareCellularRegular S] at heq
  exact hx heq

/-- Actual X checks of the incidence chain complex. -/
noncomputable def levelTwoXCode (S : OddScale) :
    LinearCode Field (levelTwoPresentation S).Q :=
  (levelTwoChainComplex S).firstCoboundaryCheckCode

/-- Actual Z checks of the incidence chain complex. -/
noncomputable def levelTwoZCode (S : OddScale) :
    LinearCode Field (levelTwoPresentation S).Q :=
  (levelTwoChainComplex S).middleBoundaryCode

theorem levelTwo_coboundary0_eq (S : OddScale) :
    wordLinearMapTranspose (levelTwoChainComplex S).boundary1 =
      tannerCoboundary0 (levelTwoPresentation S) := by
  apply LinearMap.ext
  intro word
  funext q
  exact wordLinearMapTranspose_toLin'_apply
    (xqIncidenceMatrix (levelTwoPresentation S)) word q

theorem levelTwo_coboundary1_eq (S : OddScale) :
    wordLinearMapTranspose (levelTwoChainComplex S).boundary2 =
      tannerCoboundary1 (levelTwoPresentation S) := by
  apply LinearMap.ext
  intro word
  funext z
  exact wordLinearMapTranspose_toLin'_apply
    (qzIncidenceMatrix (levelTwoPresentation S)) word z

/-- The named concrete X word lies in the logical sector, not only in the
kernel of an auxiliary map. -/
theorem levelTwoXLogical_sector (S : OddScale) :
    levelTwoXLogical S ∈ (levelTwoZCode S).dual.carrier ∧
      levelTwoXLogical S ∉ (levelTwoXCode S).carrier := by
  constructor
  · rw [levelTwoZCode,
      ChainComplexData.middleBoundaryCode_dual_carrier_eq_middleCocycleCode,
      ChainComplexData.mem_middleCocycleCode_iff, levelTwo_coboundary1_eq]
    exact levelTwoXLogical_cocycle S
  · intro hm
    obtain ⟨potential, hp⟩ :=
      ((levelTwoChainComplex S).mem_firstCoboundaryCheckCode_iff _).1 hm
    rw [levelTwo_coboundary0_eq] at hp
    exact levelTwoXLogical_nonboundary S potential hp

/-- Finite nondegenerate duality constructs a separating actual cycle from
the proved X nonboundary. No logical-sector nonemptiness is supplied. -/
theorem levelTwo_exists_separating_cycle (S : OddScale) :
    ∃ cycle : Word Field (levelTwoPresentation S).Q,
      cycle ∈ (levelTwoXCode S).dual.carrier ∧
        wordPairing (levelTwoXLogical S) cycle ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hm : levelTwoXLogical S ∈ (levelTwoXCode S).dual.dual.carrier :=
    ((levelTwoXCode S).dual.mem_dual _).2 h
  rw [LinearCode.dual_dual_carrier_eq] at hm
  exact (levelTwoXLogical_sector S).2 hm

/-- A named finite separating representative, selected only after existence
has been proved from the explicit transported seed cocycle. -/
noncomputable def levelTwoZLogical (S : OddScale) :
    Word Field (levelTwoPresentation S).Q :=
  Classical.choose (levelTwo_exists_separating_cycle S)

/-- The selected separating cycle is an actual nontrivial Z-sector word. -/
theorem levelTwoZLogical_sector (S : OddScale) :
    levelTwoZLogical S ∈ (levelTwoXCode S).dual.carrier ∧
      levelTwoZLogical S ∉ (levelTwoZCode S).carrier := by
  have hs := Classical.choose_spec (levelTwo_exists_separating_cycle S)
  refine ⟨hs.1, ?_⟩
  intro hz
  exact hs.2 ((levelTwoZCode S).orthogonal_of_mem_dual
    (levelTwoXLogical_sector S).1 hz)

/-- Actual X-sector nonemptiness gives a finite attained minimum. -/
theorem levelTwo_exists_pureXMinimum (S : OddScale) :
    ∃ d, PureXLogicalMinimumDistance (levelTwoXCode S) (levelTwoZCode S) d := by
  exact exists_relativeMinimumDistance_of_exists_mem_not_mem _ _
    (levelTwoChainComplex S).firstCoboundaryCheckCode_le_middleBoundaryCode_dual
    ⟨levelTwoXLogical S, levelTwoXLogical_sector S⟩

/-- Actual Z-sector nonemptiness independently gives its finite minimum. -/
theorem levelTwo_exists_pureZMinimum (S : OddScale) :
    ∃ d, PureZLogicalMinimumDistance (levelTwoXCode S) (levelTwoZCode S) d := by
  exact exists_relativeMinimumDistance_of_exists_mem_not_mem _ _
    (levelTwoChainComplex S).middleBoundaryCode_le_firstCoboundaryCheckCode_dual
    ⟨levelTwoZLogical S, levelTwoZLogical_sector S⟩

noncomputable def levelTwoXDistance (S : OddScale) : Nat :=
  Classical.choose (levelTwo_exists_pureXMinimum S)

noncomputable def levelTwoZDistance (S : OddScale) : Nat :=
  Classical.choose (levelTwo_exists_pureZMinimum S)

theorem levelTwo_pureXMinimum (S : OddScale) :
    PureXLogicalMinimumDistance (levelTwoXCode S) (levelTwoZCode S)
      (levelTwoXDistance S) := Classical.choose_spec (levelTwo_exists_pureXMinimum S)

theorem levelTwo_pureZMinimum (S : OddScale) :
    PureZLogicalMinimumDistance (levelTwoXCode S) (levelTwoZCode S)
      (levelTwoZDistance S) := Classical.choose_spec (levelTwo_exists_pureZMinimum S)

/-- The combined finite CSS minimum is the minimum of the two attained
logical-sector minima. This is not an asymptotic lower-bound claim. -/
theorem levelTwo_algebraicCSSMinimum (S : OddScale) :
    AlgebraicCSSMinimumDistance (levelTwoXCode S) (levelTwoZCode S)
      (min (levelTwoXDistance S) (levelTwoZDistance S)) :=
  algebraicCSSMinimumDistance_of_sector_minima
    (levelTwo_pureXMinimum S) (levelTwo_pureZMinimum S)


/-- Concrete physical C2 regions use the preceding presentation's constructor
owners. This differs from graph-node neighborhoods of the C2 Tanner graph. -/
noncomputable def levelTwoLocalComplex (S : OddScale) :
    MultiscaleDecoder.LocalComplexData (Vertex (levelOnePresentation S))
      (levelTwoPresentation S).Z (levelTwoPresentation S).Q := by
  classical
  exact
    { syndromeRegion := fun center => BDL26ReplacementSupport.fiberRegion
        (fun coordinate : RZZ (levelOnePresentation S) S => Vertex.z coordinate.1) center
      correctionRegion := BDL26ReplacementSupport.fiberRegion
        (BDL26ReplacementSupport.rzCorrectionOwner (levelOnePresentation S) S) }

/-- Actual-error locality in the concrete shifted-Q or local-Z block. -/
noncomputable def levelTwoLocalError (S : OddScale)
    (error : Word Field (levelTwoPresentation S).Q) : Prop :=
  ∃ center : Vertex (levelOnePresentation S),
    hammingSupport error ⊆ (levelTwoLocalComplex S).correctionRegion center

/-- The selected predicate is exactly the physical coordinate owner fibre,
with no identification of a graph radius with Hamming weight. -/
theorem levelTwoLocalError_iff_owner (S : OddScale)
    (error : Word Field (levelTwoPresentation S).Q) :
    levelTwoLocalError S error ↔
      ∃ center : Vertex (levelOnePresentation S), ∀ coordinate,
        error coordinate ≠ 0 →
          BDL26ReplacementSupport.rzCorrectionOwner (levelOnePresentation S) S coordinate = center := by
  classical
  simp [levelTwoLocalError, levelTwoLocalComplex,
    BDL26ReplacementSupport.fiberRegion, hammingSupport, Finset.subset_iff]


/-- The already proved zero local cohomology coordinate implies actual
coboundary/cocycle equality; a quotient class is zero exactly when its word
lies in the concrete coboundary submodule. -/
theorem xCylinder_coboundary_eq_cocycle (P : TannerSquarePresentation)
    (A3 : TannerSquareAdmissibleV3 P) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) :
    (rxCx P x S).firstCoboundaryCheckCode.carrier =
      (rxCx P x S).middleCocycleCode.carrier := by
  apply le_antisymm (rxCx P x S).firstCoboundaryCheckCode_le_middleCocycleCode
  intro word hword
  let cycle : (rxCx P x S).middleCocycleCode.carrier := ⟨word, hword⟩
  have hc : (Submodule.Quotient.mk cycle : RXH1 P x S) = 0 :=
    (rxCxH1Coordinate_bijective P A3 R x S).1 (by
      simp [rxCxH1Coordinate])
  exact (Submodule.Quotient.mk_eq_zero
    (rxCx P x S).middleCoboundaryInCocycles).1 hc

/-- Finite nondegenerate duality turns the actual X-cylinder cohomology
calculation into a cellular cycle-filling statement. -/
theorem xCylinder_boundary_eq_cycle (P : TannerSquarePresentation)
    (A3 : TannerSquareAdmissibleV3 P) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) :
    (rxCx P x S).middleBoundaryCode.carrier =
      (rxCx P x S).middleCycleCode.carrier := by
  have hcode : (rxCx P x S).firstCoboundaryCheckCode =
      (rxCx P x S).middleCocycleCode :=
    LinearCode.eq_of_carrier_eq (xCylinder_coboundary_eq_cocycle P A3 R x S)
  have hdual : (rxCx P x S).middleBoundaryCode.dual =
      (rxCx P x S).middleCocycleCode :=
    LinearCode.eq_of_carrier_eq
      (rxCx P x S).middleBoundaryCode_dual_carrier_eq_middleCocycleCode
  rw [← ChainComplexData.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode,
    hcode, ← hdual, LinearCode.dual_dual_carrier_eq]

/-- Every zero-boundary Z-cylinder edge chain has a genuine face filling.
This is the local exactness used after removing Q-block parities. -/
theorem zCylinder_cycle_has_filling (P : TannerSquarePresentation)
    (A3 : TannerSquareAdmissibleV3 P) (R : TannerSquareCellularRegular P)
    (z : P.Z) (S : OddScale) (word : Word Field (ZDoubleCylinderEdge P z S))
    (hword : doubleCylinderBoundary1 (transposePresentation P) z S word = 0) :
    ∃ faces : Word Field (ZDoubleCylinderFace P z S),
      doubleCylinderBoundary2 (transposePresentation P) z S faces = word := by
  have hm : word ∈ (rxCx (transposePresentation P) z S).middleCycleCode.carrier :=
    ((rxCx (transposePresentation P) z S).mem_middleCycleCode_iff word).2 hword
  rw [← xCylinder_boundary_eq_cycle (transposePresentation P)
    (transposeTannerSquareAdmissibleV3 P A3) (transposeTannerSquareCellularRegular P R)
    z S] at hm
  exact ((rxCx (transposePresentation P) z S).mem_middleBoundaryCode_iff word).1 hm

/-- The physical owner predicate is definitionally the approved abstract
F17 predicate for any decoder-data carrier assembled with these coordinates.
No decoder correctness or geometric conclusion is assumed or inferred. -/
theorem levelTwoLocalError_iff_f17 (S : OddScale) {depth : Nat}
    (hdepth : 2 ≤ depth)
    (D : MultiscaleDecoder.BDL26DecoderData depth
      (fun _ => (levelTwoPresentation S).X)
      (fun _ => (levelTwoPresentation S).Q)
      (fun _ => (levelTwoPresentation S).Z))
    (error : Word Field (levelTwoPresentation S).Q) :
    levelTwoLocalError S error ↔
      MultiscaleDecoder.LevelTwoLocalError
        (V := fun _ => Vertex (levelOnePresentation S)) D hdepth
        (levelTwoLocalComplex S) error := Iff.rfl

/-- The actual presentation incidence coboundaries square to zero. -/
theorem tannerCoboundary_squared (P : TannerSquarePresentation) :
    (tannerCoboundary1 P).comp (tannerCoboundary0 P) = 0 := by
  have h0 : tannerCoboundary0 P = wordLinearMapTranspose
      (Matrix.toLin' (xqIncidenceMatrix P)) := by
    apply LinearMap.ext
    intro word
    funext q
    exact (wordLinearMapTranspose_toLin'_apply (xqIncidenceMatrix P) word q).symm
  have h1 : tannerCoboundary1 P = wordLinearMapTranspose
      (Matrix.toLin' (qzIncidenceMatrix P)) := by
    apply LinearMap.ext
    intro word
    funext z
    exact (wordLinearMapTranspose_toLin'_apply (qzIncidenceMatrix P) word z).symm
  rw [h0, h1, ← wordLinearMapTranspose_comp, ← Matrix.toLin'_mul,
    xqIncidenceMatrix_mul_qzIncidenceMatrix]
  simp only [map_zero, wordLinearMapTranspose_zero]

/-- Evaluate an embedded Q-edge boundary on a physical Q-block coordinate. -/
theorem rzQEdge_coboundary_apply_q (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (q other : P.Q)
    (edges : Word Field (QDoubleCylinderEdge (transposePresentation P) q S))
    (vertex : QDoubleCylinderVertex (transposePresentation P) other S) :
    rzCoboundary0 P A4 S (extendRZQEdgeWord P S q edges) (Sum.inr ⟨other, vertex⟩) =
      extendRZQVertexWord P S q
        (qDoubleCylinderBoundary1 (transposePresentation P) q S edges)
        (Sum.inr ⟨other, vertex⟩) := by
  classical
  rw [rzCoboundary0_extendRZQEdgeWord]
  simp [extendRZLocalEdgeWord_eq, qDoubleCylinderBoundary1]
  apply Finset.sum_eq_zero
  intro z _
  split <;> rfl

/-- Each even physical Q block has a concrete Q-edge filling. -/
theorem rzQParity_zero_has_qFillings (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (word : Word Field (RZQ P S))
    (hparity : rzQParity P S word = 0) :
    ∀ q : P.Q, ∃ edges : Word Field (QDoubleCylinderEdge (transposePresentation P) q S),
      qDoubleCylinderBoundary1 (transposePresentation P) q S edges =
        fun vertex => word (Sum.inr ⟨q, vertex⟩) := by
  intro q
  have hker : (fun vertex : QDoubleCylinderVertex (transposePresentation P) q S =>
      word (Sum.inr ⟨q, vertex⟩)) ∈ LinearMap.ker totalParity := by
    apply LinearMap.mem_ker.mpr
    exact congrFun hparity q
  rw [← qTransposeDoubleCylinderBoundary_range_eq_totalParity_ker P A q S] at hker
  exact hker

/-- All embedded physical Q restrictions reassemble their Q coordinates. -/
theorem sum_extendRZQVertexWord_apply (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RZQ P S)) (q : P.Q)
    (vertex : QDoubleCylinderVertex (transposePresentation P) q S) :
    (∑ other : P.Q, extendRZQVertexWord P S other
      (fun v => word (Sum.inr ⟨other, v⟩))) (Sum.inr ⟨q, vertex⟩) =
        word (Sum.inr ⟨q, vertex⟩) := by
  classical
  rw [Finset.sum_apply, Finset.sum_eq_single q]
  · simp [extendRZQVertexWord, wordPushforward_apply, Sigma.mk.injEq]
  · intro other _ hother
    simp [extendRZQVertexWord, wordPushforward_apply, Sigma.mk.injEq, hother, Ne.symm hother]
  · simp

/-- A word with no physical Q coordinates is exactly its sum of local Z
restrictions, retaining all local edge coordinates. -/
theorem rzWord_eq_sum_local_of_q_zero (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RZQ P S))
    (hq : ∀ q vertex, word (Sum.inr ⟨q, vertex⟩) = 0) :
    word = ∑ z : P.Z, extendZEdgeWord P S z
      (fun edge => word (Sum.inl ⟨z, edge⟩)) := by
  classical
  funext coordinate
  rcases coordinate with ⟨z, edge⟩ | ⟨q, vertex⟩
  · simp [Finset.sum_apply, extendZEdgeWord]
  · simp [Finset.sum_apply, extendZEdgeWord, hq]

/-- A cocycle with no Q coordinates restricts to a cycle in every actual
Z cylinder. The proof uses the materialized global incidence map. -/
theorem rzLocal_cycle_of_cocycle_q_zero (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale)
    (word : Word Field (RZQ P S))
    (hc : rzCoboundary1 P A4 S word = 0)
    (hq : ∀ q vertex, word (Sum.inr ⟨q, vertex⟩) = 0) (z : P.Z) :
    doubleCylinderBoundary1 (transposePresentation P) z S
      (fun edge => word (Sum.inl ⟨z, edge⟩)) = 0 := by
  classical
  have hs := rzWord_eq_sum_local_of_q_zero P S word hq
  change tannerCoboundary1 (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
    word = 0 at hc
  rw [hs] at hc
  erw [map_sum] at hc
  simp only [rzCoboundary1_extendZEdgeWord, rzCzGraphBoundary_eq_boundary1] at hc
  funext vertex
  have hv := congrFun hc ⟨z, vertex⟩
  have heval : (∑ other : P.Z, extendZVertexWord P S other
      (doubleCylinderBoundary1 (transposePresentation P) other S
        (fun edge => word (Sum.inl ⟨other, edge⟩)))) ⟨z, vertex⟩ =
      doubleCylinderBoundary1 (transposePresentation P) z S
        (fun edge => word (Sum.inl ⟨z, edge⟩)) vertex := by
    rw [Finset.sum_apply, Finset.sum_eq_single z]
    · simp only [extendZVertexWord, dite_true]
    · intro other _ hother
      simp only [extendZVertexWord, Ne.symm hother, dite_false]
    · simp
  exact heval.symm.trans hv

/-- A cocycle entirely in Z-local edges has an actual global face potential. -/
theorem rzCocycle_q_zero_is_coboundary (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (word : Word Field (RZQ P S))
    (hc : rzCoboundary1 P A4 S word = 0)
    (hq : ∀ q vertex, word (Sum.inr ⟨q, vertex⟩) = 0) :
    ∃ potential : Word Field (RZX P S), rzCoboundary0 P A4 S potential = word := by
  classical
  have hf : ∀ z : P.Z, ∃ faces : Word Field (ZDoubleCylinderFace P z S),
      doubleCylinderBoundary2 (transposePresentation P) z S faces =
        fun edge => word (Sum.inl ⟨z, edge⟩) := by
    intro z
    exact zCylinder_cycle_has_filling P A4.toTannerSquareAdmissibleV3 R z S _
      (rzLocal_cycle_of_cocycle_q_zero P A4 S word hc hq z)
  choose faces hfaces using hf
  refine ⟨∑ z : P.Z, extendRZFaceWord P S z (faces z), ?_⟩
  rw [map_sum]
  simp only [rzCoboundary0_extendRZFaceWord, extendRZLocalEdgeWord_eq, hfaces]
  exact (rzWord_eq_sum_local_of_q_zero P S word hq).symm

/-- Vanishing physical Q parity is enough for an RZ cocycle to be a genuine
first coboundary. Q graph fillings remove all Q coordinates; Z face fillings
then remove the residual. No exactness field is assumed. -/
theorem rzCocycle_qParity_zero_is_coboundary (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (word : Word Field (RZQ P S))
    (hc : rzCoboundary1 P A4 S word = 0)
    (hp : rzQParity P S word = 0) :
    ∃ potential : Word Field (RZX P S), rzCoboundary0 P A4 S potential = word := by
  classical
  obtain ⟨edges, hedges⟩ := Classical.skolem.mp
    (rzQParity_zero_has_qFillings P A4.toTannerSquareAdmissible S word hp)
  let qPotential : Word Field (RZX P S) := ∑ q : P.Q, extendRZQEdgeWord P S q (edges q)
  have hqp : ∀ q vertex,
      rzCoboundary0 P A4 S qPotential (Sum.inr ⟨q, vertex⟩) =
        word (Sum.inr ⟨q, vertex⟩) := by
    intro q vertex
    dsimp only [qPotential]
    rw [map_sum, Finset.sum_apply]
    simp only [rzQEdge_coboundary_apply_q, hedges]
    simpa only [Finset.sum_apply] using sum_extendRZQVertexWord_apply P S word q vertex
  let residual := word + rzCoboundary0 P A4 S qPotential
  have hresq : ∀ q vertex, residual (Sum.inr ⟨q, vertex⟩) = 0 := by
    intro q vertex
    change word _ + rzCoboundary0 P A4 S qPotential _ = 0
    rw [hqp]
    exact ZModModule.add_self _
  have hresc : rzCoboundary1 P A4 S residual = 0 := by
    dsimp only [residual]
    rw [map_add, hc, zero_add]
    have h := LinearMap.congr_fun
      (tannerCoboundary_squared (rzReplacementPresentation P A4.toTannerSquareAdmissible S))
      qPotential
    exact h
  obtain ⟨zPotential, hz⟩ := rzCocycle_q_zero_is_coboundary P A4 R S residual hresc hresq
  refine ⟨zPotential + qPotential, ?_⟩
  rw [map_add, hz]
  change (word + rzCoboundary0 P A4 S qPotential) + rzCoboundary0 P A4 S qPotential = word
  rw [add_assoc, ZModModule.add_self, add_zero]

/-- A physical owner-local word has no Q parity outside its own Q label. -/
theorem rzQParity_zero_of_other_owner (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RZQ P S)) (owner : Vertex P)
    (howner : ∀ coordinate, word coordinate ≠ 0 →
      BDL26ReplacementSupport.rzCorrectionOwner P S coordinate = owner)
    (q : P.Q) (hne : Vertex.q q ≠ owner) : rzQParity P S word q = 0 := by
  classical
  change (∑ vertex : QDoubleCylinderVertex (transposePresentation P) q S,
    word (Sum.inr ⟨q, vertex⟩)) = 0
  apply Finset.sum_eq_zero
  intro vertex _
  by_contra hn
  exact hne (howner (Sum.inr ⟨q, vertex⟩) hn)

/-- Two independently local physical errors produce Q parity in at most
the two selected owner labels, even when the centers differ. -/
theorem rzQParity_add_owner_support (P : TannerSquarePresentation) (S : OddScale)
    (first second : Word Field (RZQ P S)) (a b : Vertex P)
    (ha : ∀ c, first c ≠ 0 → BDL26ReplacementSupport.rzCorrectionOwner P S c = a)
    (hb : ∀ c, second c ≠ 0 → BDL26ReplacementSupport.rzCorrectionOwner P S c = b)
    (q : P.Q) (hq : rzQParity P S (first + second) q ≠ 0) :
    Vertex.q q = a ∨ Vertex.q q = b := by
  by_contra hn
  push Not at hn
  have hf := rzQParity_zero_of_other_owner P S first a ha q hn.1
  have hs := rzQParity_zero_of_other_owner P S second b hb q hn.2
  have heq := congrFun ((rzQParity P S).map_add first second) q
  rw [Pi.add_apply, hf, hs, zero_add] at heq
  exact hq heq

theorem levelTwoLocalError_add_qParity_support (S : OddScale)
    (first second : Word Field (levelTwoPresentation S).Q)
    (hfirst : levelTwoLocalError S first) (hsecond : levelTwoLocalError S second) :
    ∃ firstOwner secondOwner : Vertex (levelOnePresentation S),
      ∀ q, rzQParity (levelOnePresentation S) S (first + second) q ≠ 0 →
        Vertex.q q = firstOwner ∨ Vertex.q q = secondOwner := by
  classical
  obtain ⟨a, ha⟩ := (levelTwoLocalError_iff_owner S first).1 hfirst
  obtain ⟨b, hb⟩ := (levelTwoLocalError_iff_owner S second).1 hsecond
  exact ⟨a, b, rzQParity_add_owner_support (levelOnePresentation S) S first second a b ha hb⟩

/-- Actual Z-block syndrome parity is the old syndrome of physical Q parity.
This is a coefficient calculation on the materialized RZ incidence. -/
theorem rzCoboundary1_blockParity (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale)
    (word : Word Field (RZQ P S)) (z : P.Z) :
    (∑ vertex : ZDoubleCylinderVertex P z S,
      rzCoboundary1 P A4 S word ⟨z, vertex⟩) =
        tannerCoboundary1 P (rzQParity P S word) z := by
  classical
  let parity : Word Field (RZZ P S) →ₗ[Field] Word Field P.Z :=
    { toFun := fun syndrome z => ∑ vertex : ZDoubleCylinderVertex P z S, syndrome ⟨z, vertex⟩
      map_add' := by intros; ext; simp [Finset.sum_add_distrib]
      map_smul' := by intros; ext; simp [Finset.mul_sum] }
  have hmaps : parity.comp (rzCoboundary1 P A4 S) =
      (tannerCoboundary1 P).comp (rzQParity P S) := by
    apply linearMap_ext_canonicalBasis
    intro coordinate
    simp only [LinearMap.comp_apply]
    funext target
    rcases coordinate with ⟨localZ, edge⟩ | ⟨q, vertex⟩
    · rw [rzQParity_localBasis, map_zero]
      have hb : (canonicalBasisWord (Sum.inl ⟨localZ, edge⟩ : RZQ P S)) =
          extendZEdgeWord P S localZ (canonicalBasisWord edge) := by
        funext c
        rcases c with ⟨other, e⟩ | v
        · by_cases h : other = localZ
          · subst other
            simp [extendZEdgeWord, canonicalBasisWord, Pi.single_apply, Sigma.mk.injEq]
          · simp [extendZEdgeWord, canonicalBasisWord, Pi.single_apply, h, Sigma.mk.injEq]
        · simp [extendZEdgeWord, canonicalBasisWord, Pi.single_apply]
      change (∑ v : ZDoubleCylinderVertex P target S,
        tannerCoboundary1 (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
          (canonicalBasisWord (Sum.inl ⟨localZ, edge⟩ : RZQ P S)) ⟨target, v⟩) = 0
      erw [hb, rzCoboundary1_extendZEdgeWord]
      by_cases ht : target = localZ
      · subst target
        simp only [extendZVertexWord, dite_true]
        change totalParity (rzCzGraphBoundary P localZ S (canonicalBasisWord edge)) = 0
        exact totalParity_graphBoundary _ _ _
      · simp only [extendZVertexWord, ht, dite_false, Finset.sum_const_zero]
    · rw [rzQParity_qBasis]
      change (∑ v : ZDoubleCylinderVertex P target S,
        tannerCoboundary1 (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
          (canonicalBasisWord (Sum.inr ⟨q, vertex⟩ : RZQ P S)) ⟨target, v⟩) =
            tannerCoboundary1 P (canonicalBasisWord q) target
      have hc : ∀ v : ZDoubleCylinderVertex P target S,
          tannerCoboundary1 (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
            (canonicalBasisWord (Sum.inr ⟨q, vertex⟩ : RZQ P S)) ⟨target, v⟩ =
          if hqz : P.qz q target = true then
            (if qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible
              q target hqz S vertex = v then 1 else 0) else 0 := by
        intro v
        erw [tannerCoboundary1_canonicalBasis_apply]
        change (if rzQZIncidence P A4.toTannerSquareAdmissible S
            (Sum.inr ⟨q, vertex⟩) ⟨target, v⟩ = true then (1 : Field) else 0) = _
        have hcoeff :=
          rzQZIncidence_q_coefficient P A4.toTannerSquareAdmissible S q target vertex v
        by_cases hqz : P.qz q target = true
        · by_cases hv : qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible
              q target hqz S vertex = v
          · simpa only [dif_pos hqz, vertexIndicator, if_pos hv] using hcoeff
          · simpa only [dif_pos hqz, vertexIndicator, if_neg hv] using hcoeff
        · simpa only [dif_neg hqz] using hcoeff
      simp_rw [hc]
      erw [tannerCoboundary1_canonicalBasis_apply]
      by_cases hqz : P.qz q target = true
      · simp only [dif_pos hqz, if_pos hqz]
        rw [Finset.sum_eq_single
          (qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible q target hqz S vertex)]
        · simp
        · intro other _ hother
          exact if_neg (Ne.symm hother)
        · simp
      · simp only [dif_neg hqz, if_neg hqz, Finset.sum_const_zero]
  exact congrFun (LinearMap.congr_fun hmaps word) z

/-- Every actual RZ cocycle projects to an old cocycle. -/
theorem rzQParity_cocycle (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale)
    (word : Word Field (RZQ P S)) (hc : rzCoboundary1 P A4 S word = 0) :
    tannerCoboundary1 P (rzQParity P S word) = 0 := by
  classical
  funext z
  rw [← rzCoboundary1_blockParity P A4 S word z, hc]
  simp

/-- Nonzero distinct binary syndrome columns separate all words supported on
at most two coordinates. This elementary incidence criterion has no distance
or radius hypothesis. -/
theorem binary_two_coordinate_kernel_eq_zero
    {Q Z : Type} [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
    (syndrome : Word Field Q →ₗ[Field] Word Field Z)
    (hnonzero : ∀ q, syndrome (canonicalBasisWord q) ≠ 0)
    (hdistinct : Function.Injective (fun q => syndrome (canonicalBasisWord q)))
    (word : Word Field Q) (hzero : syndrome word = 0) (a b : Q)
    (hsupport : ∀ q, word q ≠ 0 → q = a ∨ q = b) : word = 0 := by
  classical
  have hbinary : ∀ value : Field, value = 0 ∨ value = 1 := by decide
  by_cases hab : a = b
  · subst b
    by_cases ha : word a = 0
    · funext q
      by_contra hq
      have heq : q = a := (hsupport q hq).elim id id
      subst q
      exact hq ha
    · have haone : word a = 1 := (hbinary _).resolve_left ha
      have heq : word = canonicalBasisWord a := by
        funext q
        by_cases hq : q = a
        · subst q; simp [canonicalBasisWord, haone]
        · have hw : word q = 0 := by
            by_contra hn
            exact hq ((hsupport q hn).elim id id)
          simp [canonicalBasisWord, Pi.single_apply, hq, hw]
      rw [heq] at hzero
      exact False.elim (hnonzero a hzero)
  · have hdecompose : word =
        word a • canonicalBasisWord a + word b • canonicalBasisWord b := by
      funext q
      by_cases hqa : q = a
      · subst q
        simp [canonicalBasisWord, Pi.single_apply, hab]
      · by_cases hqb : q = b
        · subst q
          simp [canonicalBasisWord, Pi.single_apply, hab, Ne.symm hab]
        · have hw : word q = 0 := by
            by_contra hn
            exact (hsupport q hn).elim hqa hqb
          simp [canonicalBasisWord, Pi.single_apply, hqa, hqb, hw]
    rcases hbinary (word a) with ha | ha <;> rcases hbinary (word b) with hb | hb
    · simpa [ha, hb] using hdecompose
    · rw [hdecompose, ha, hb, zero_smul, one_smul, zero_add] at hzero
      exact False.elim (hnonzero b hzero)
    · rw [hdecompose, ha, hb, zero_smul, one_smul, add_zero] at hzero
      exact False.elim (hnonzero a hzero)
    · rw [hdecompose, ha, hb, one_smul, map_add] at hzero
      have heq : syndrome (canonicalBasisWord a) = syndrome (canonicalBasisWord b) := by
        have h := congrArg (fun value => value + syndrome (canonicalBasisWord b)) hzero
        simpa only [one_smul, add_assoc, ZModModule.add_self, add_zero, zero_add] using h
      exact False.elim (hab (hdistinct heq))

/-- Project a Q owner to its coordinate, using an arbitrary existing coordinate
for the X/Z owners whose physical Q parity is zero. -/
def qCoordinateOfOwner (P : TannerSquarePresentation) (defaultQ : P.Q) : Vertex P → P.Q
  | .q q => q
  | .x _ => defaultQ
  | .z _ => defaultQ

/-- An existing physical coordinate in the first RX replacement, used only
as the harmless fallback when a locality center is an X or Z vertex. -/
def levelOneQDefault (S : OddScale) : (levelOnePresentation S).Q :=
  Sum.inr ⟨(0 : BaseQubit), (0, Sum.inl (Sum.inl ()))⟩

theorem qCoordinateOfOwner_of_eq (P : TannerSquarePresentation) (defaultQ q : P.Q)
    (owner : Vertex P) (h : Vertex.q q = owner) :
    q = qCoordinateOfOwner P defaultQ owner := by
  subst owner
  rfl

/-- Convert the actual owner-label support conclusion to two coordinate
labels without assuming that either local center is a Q vertex. -/
theorem levelTwoLocalError_add_qParity_two_coordinates (S : OddScale)
    (defaultQ : (levelOnePresentation S).Q)
    (first second : Word Field (levelTwoPresentation S).Q)
    (hfirst : levelTwoLocalError S first) (hsecond : levelTwoLocalError S second) :
    ∃ a b : (levelOnePresentation S).Q,
      ∀ q, rzQParity (levelOnePresentation S) S (first + second) q ≠ 0 → q = a ∨ q = b := by
  obtain ⟨a, b, hab⟩ := levelTwoLocalError_add_qParity_support S first second hfirst hsecond
  refine ⟨qCoordinateOfOwner _ defaultQ a, qCoordinateOfOwner _ defaultQ b, ?_⟩
  intro q hq
  rcases hab q hq with ha | hb
  · exact Or.inl (qCoordinateOfOwner_of_eq _ defaultQ q a ha)
  · exact Or.inr (qCoordinateOfOwner_of_eq _ defaultQ q b hb)

private noncomputable def coordinatePreimageOr {Q I : Type} (embed : I → Q)
    (fallback : I) (q : Q) : I := by
  classical
  exact if h : ∃ i, embed i = q then Classical.choose h else fallback

private theorem coordinatePreimageOr_of_eq {Q I : Type} (embed : I → Q)
    (hinj : Function.Injective embed) (fallback i : I) (q : Q) (h : embed i = q) :
    i = coordinatePreimageOr embed fallback q := by
  classical
  have hex : ∃ j, embed j = q := ⟨i, h⟩
  rw [coordinatePreimageOr, dif_pos hex]
  exact hinj (h.trans (Classical.choose_spec hex).symm)

/-- Restricting a two-coordinate-supported word along an injective coordinate
embedding preserves the elementary two-column separation criterion. -/
theorem binary_two_coordinate_restriction_kernel_eq_zero
    {Q I Z : Type} [Fintype Q] [DecidableEq Q] [Fintype I] [DecidableEq I]
    [Fintype Z] [DecidableEq Z]
    (embed : I → Q) (hinj : Function.Injective embed)
    (syndrome : Word Field I →ₗ[Field] Word Field Z)
    (hnonzero : ∀ i, syndrome (canonicalBasisWord i) ≠ 0)
    (hdistinct : Function.Injective (fun i => syndrome (canonicalBasisWord i)))
    (word : Word Field Q)
    (hzero : syndrome (fun i => word (embed i)) = 0) (a b : Q)
    (hsupport : ∀ q, word q ≠ 0 → q = a ∨ q = b) :
    (fun i => word (embed i)) = 0 := by
  classical
  by_contra hlocal
  have hex : ∃ i, word (embed i) ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hlocal (funext hn)
  obtain ⟨fallback, _⟩ := hex
  apply hlocal
  apply binary_two_coordinate_kernel_eq_zero syndrome hnonzero hdistinct _ hzero
    (coordinatePreimageOr embed fallback a) (coordinatePreimageOr embed fallback b)
  intro i hi
  rcases hsupport (embed i) hi with ha | hb
  · exact Or.inl (coordinatePreimageOr_of_eq embed hinj fallback i a ha)
  · exact Or.inr (coordinatePreimageOr_of_eq embed hinj fallback i b hb)

/-- Actual RX syndrome restricted to an X-local face is exactly the local
face coboundary of the X-edge restriction. -/
theorem rxCoboundary1_localFace (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RX1 P S)) (x : P.X) (face : DoubleCylinderFace P x S) :
    rxCoboundary1 P S word (Sum.inl (Sum.inl ⟨x, face⟩)) =
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
        (fun edge => word (Sum.inl ⟨x, edge⟩)) face := by
  classical
  unfold rxCoboundary1 rxBoundary2
  rw [wordLinearMapTranspose_toLin'_apply, Fintype.sum_sum_type,
    Fintype.sum_sigma, Fintype.sum_sigma]
  have hq : (∑ q : P.Q, ∑ vertex : QDoubleCylinderVertex P q S,
      word (Sum.inr ⟨q, vertex⟩) *
        rxBoundary2Matrix P S (Sum.inr ⟨q, vertex⟩) (Sum.inl (Sum.inl ⟨x, face⟩))) = 0 := by
    simp [rxBoundary2Matrix]
  rw [hq, add_zero, Finset.sum_eq_single x]
  · simp only [rxBoundary2Matrix, dite_true]
    exact (wordLinearMapTranspose_toLin'_apply (doubleCylinderFaceEdgeMatrix P x S)
      (fun edge => word (Sum.inl ⟨x, edge⟩)) face).symm
  · intro other _ hother
    simp [rxBoundary2Matrix, hother]
  · simp

/-- After the actual X-edge coordinates vanish, a Q-edge syndrome is the
sum of its two physical Q endpoint values. -/
theorem rxCoboundary1_qEdge_of_local_zero (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RX1 P S))
    (hx : ∀ x edge, word (Sum.inl ⟨x, edge⟩) = 0)
    (q : P.Q) (edge : QDoubleCylinderEdge P q S) :
    rxCoboundary1 P S word (Sum.inl (Sum.inr ⟨q, edge⟩)) =
      word (Sum.inr ⟨q, qDoubleCylinderEdgeStart P q S edge⟩) +
        word (Sum.inr ⟨q, qDoubleCylinderEdgeEnd P q S edge⟩) := by
  classical
  unfold rxCoboundary1 rxBoundary2
  rw [wordLinearMapTranspose_toLin'_apply, Fintype.sum_sum_type,
    Fintype.sum_sigma, Fintype.sum_sigma]
  simp only [hx, zero_mul, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_eq_single q]
  · simp [rxBoundary2Matrix, qDoubleCylinderEdgeVertexIncidence, mul_add,
      Finset.sum_add_distrib]
  · intro other _ hother
    simp [rxBoundary2Matrix, hother]
  · simp

/-- An actual RX cocycle with zero X-edge coordinates is constant on every
connected Q cylinder. -/
theorem rxCocycle_q_constant_of_local_zero (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (word : Word Field (RX1 P S))
    (hc : rxCoboundary1 P S word = 0)
    (hx : ∀ x edge, word (Sum.inl ⟨x, edge⟩) = 0) (q : P.Q)
    (vertex : QDoubleCylinderVertex P q S) :
    word (Sum.inr ⟨q, vertex⟩) = word (Sum.inr ⟨q, (0, Sum.inl (Sum.inl ()))⟩) := by
  apply word_eq_root_of_graphCoboundary_eq_zero
    (qDoubleCylinderEdgeStart P q S) (qDoubleCylinderEdgeEnd P q S)
    (0, Sum.inl (Sum.inl ())) (qDoubleCylinderPath P A q S)
    (fun v => word (Sum.inr ⟨q, v⟩)) ?_ vertex
  funext edge
  rw [wordLinearMapTranspose_graphBoundary_apply]
  rw [← rxCoboundary1_qEdge_of_local_zero P S word hx q edge, hc]
  rfl

private theorem three_distinct_not_two {I : Type} (u v w a b : I)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu : u = a ∨ u = b) (hv : v = a ∨ v = b) (hw : w = a ∨ w = b) : False := by
  rcases hu with hu | hu <;> rcases hv with hv | hv <;> rcases hw with hw | hw
  all_goals aesop

/-- Three explicit distinct vertices in each Q cylinder rule out a nonzero
constant restriction of a word supported on at most two physical coordinates. -/
theorem rxCocycle_two_support_eq_zero_of_local_zero (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (word : Word Field (RX1 P S))
    (hc : rxCoboundary1 P S word = 0)
    (hx : ∀ x edge, word (Sum.inl ⟨x, edge⟩) = 0)
    (a b : RX1 P S) (hsupport : ∀ c, word c ≠ 0 → c = a ∨ c = b) : word = 0 := by
  classical
  funext coordinate
  rcases coordinate with ⟨x, edge⟩ | ⟨q, vertex⟩
  · exact hx x edge
  · rw [rxCocycle_q_constant_of_local_zero P A S word hc hx q vertex]
    by_contra hroot
    let first : RX1 P S := Sum.inr ⟨q, (0, Sum.inl (Sum.inl ()))⟩
    let second : RX1 P S := Sum.inr ⟨q, (1, Sum.inl (Sum.inl ()))⟩
    let third : RX1 P S := Sum.inr ⟨q, (0, Sum.inl (Sum.inr (A.qzRoot q)))⟩
    have hfirst : word first ≠ 0 := hroot
    have hsecond : word second ≠ 0 := by
      rw [rxCocycle_q_constant_of_local_zero P A S word hc hx q
        (1, Sum.inl (Sum.inl ()))]
      exact hroot
    have hthird : word third ≠ 0 := by
      rw [rxCocycle_q_constant_of_local_zero P A S word hc hx q
        (0, Sum.inl (Sum.inr (A.qzRoot q)))]
      exact hroot
    have h12 : first ≠ second := by simp [first, second]
    have h13 : first ≠ third := by simp [first, third]
    have h23 : second ≠ third := by simp [second, third]
    have hp1 := hsupport first hfirst
    have hp2 := hsupport second hsecond
    have hp3 := hsupport third hthird
    exact three_distinct_not_two first second third a b h12 h13 h23 hp1 hp2 hp3

private theorem transposeMatrix_basis_apply {I Z : Type}
    [Fintype I] [DecidableEq I] [Fintype Z] [DecidableEq Z]
    (matrix : Matrix I Z Field) (i : I) (z : Z) :
    wordLinearMapTranspose (Matrix.toLin' matrix) (canonicalBasisWord i) z = matrix i z := by
  classical
  rw [wordLinearMapTranspose_toLin'_apply]
  simp [canonicalBasisWord, Pi.single_apply]

/-- A matrix with nonzero distinct rows has no binary kernel vector on two
source coordinates under its transpose incidence map. -/
theorem binary_two_coordinate_matrix_restriction_eq_zero
    {Q I Z : Type} [Fintype Q] [DecidableEq Q] [Fintype I] [DecidableEq I]
    [Fintype Z] [DecidableEq Z]
    (embed : I → Q) (hinj : Function.Injective embed) (matrix : Matrix I Z Field)
    (hnonzero : ∀ i, ∃ z, matrix i z = 1)
    (hdistinct : Function.Injective (fun i => fun z => matrix i z))
    (word : Word Field Q)
    (hzero : wordLinearMapTranspose (Matrix.toLin' matrix) (fun i => word (embed i)) = 0)
    (a b : Q) (hsupport : ∀ q, word q ≠ 0 → q = a ∨ q = b) :
    (fun i => word (embed i)) = 0 := by
  apply binary_two_coordinate_restriction_kernel_eq_zero embed hinj
    (wordLinearMapTranspose (Matrix.toLin' matrix)) ?_ ?_ word hzero a b hsupport
  · intro i hi
    obtain ⟨z, hz⟩ := hnonzero i
    have h := congrFun hi z
    rw [transposeMatrix_basis_apply, hz] at h
    exact one_ne_zero h
  · intro i j hij
    apply hdistinct
    funext z
    have h := congrFun hij z
    simpa only [transposeMatrix_basis_apply] using h

/-- A two-coordinate-supported cocycle in the actual seed RX replacement
vanishes. Local face incidence kills X edges; connected Q cylinders then
have constant restrictions, which three distinct physical vertices kill. -/
theorem seedRX_two_support_cocycle_zero (S : OddScale)
    (word : Word Field (RX1 baseTannerSquarePresentation S))
    (hc : rxCoboundary1 baseTannerSquarePresentation S word = 0)
    (a b : RX1 baseTannerSquarePresentation S)
    (hsupport : ∀ c, word c ≠ 0 → c = a ∨ c = b) : word = 0 := by
  classical
  apply rxCocycle_two_support_eq_zero_of_local_zero baseTannerSquarePresentation
    baseTannerSquareAdmissible S word hc ?_ a b hsupport
  intro x edge
  have hlocal : wordLinearMapTranspose (doubleCylinderBoundary2 baseTannerSquarePresentation x S)
      (fun e => word (Sum.inl ⟨x, e⟩)) = 0 := by
    funext face
    rw [← rxCoboundary1_localFace baseTannerSquarePresentation S word x face, hc]
    rfl
  have hrestrict := binary_two_coordinate_matrix_restriction_eq_zero
    (fun e : DoubleCylinderEdge baseTannerSquarePresentation x S =>
      (Sum.inl ⟨x, e⟩ : RX1 baseTannerSquarePresentation S))
    (by
      intro e f h
      simpa [Sigma.mk.injEq] using h)
    (doubleCylinderFaceEdgeMatrix baseTannerSquarePresentation x S)
    (BDL26RXSeedSmallSupport.seed_local_column_nonzero S x)
    (BDL26RXSeedSmallSupport.seed_local_column_injective S x)
    word hlocal a b hsupport
  exact congrFun hrestrict edge

/-- The coordinate statement is transported to the actual first-level
presentation incidence, with no alternate chain complex. -/
theorem levelOne_two_support_cocycle_zero (S : OddScale)
    (word : Word Field (levelOnePresentation S).Q)
    (hc : tannerCoboundary1 (levelOnePresentation S) word = 0)
    (a b : (levelOnePresentation S).Q)
    (hsupport : ∀ c, word c ≠ 0 → c = a ∨ c = b) : word = 0 := by
  change tannerCoboundary1 (rxReplacementPresentation baseTannerSquarePresentation S) word = 0 at hc
  erw [rxPresentation_coboundary1_eq baseTannerSquarePresentation baseTannerSquareAdmissibleV4
    baseTannerSquareCellularRegular S] at hc
  exact seedRX_two_support_cocycle_zero S word hc a b hsupport

/-- Concrete F17 two-local-error separation. The centers are independent:
first take the actual cocycle sum, project its owner-fibre support to at most
two RX coordinates, and construct a genuine RZ coboundary potential. -/
theorem levelTwoLocalError_sameSyndrome (S : OddScale)
    (first second : Word Field (levelTwoPresentation S).Q)
    (hfirst : levelTwoLocalError S first) (hsecond : levelTwoLocalError S second)
    (hsyn : tannerCoboundary1 (levelTwoPresentation S) first =
      tannerCoboundary1 (levelTwoPresentation S) second) :
    first + second ∈ (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier := by
  have hc := sameSyndrome_add_cocycle S first second hsyn
  have hprojected := rzQParity_cocycle (levelOnePresentation S)
    (rxState S baseState).admissible S (first + second) hc
  obtain ⟨a, b, hab⟩ := levelTwoLocalError_add_qParity_two_coordinates S
    (levelOneQDefault S) first second hfirst hsecond
  have hparity := levelOne_two_support_cocycle_zero S
    (rzQParity (levelOnePresentation S) S (first + second)) hprojected a b hab
  obtain ⟨potential, hp⟩ := rzCocycle_qParity_zero_is_coboundary (levelOnePresentation S)
    (rxState S baseState).admissible (rxState S baseState).regular S (first + second) hc hparity
  apply ((levelTwoChainComplex S).mem_firstCoboundaryCheckCode_iff (first + second)).2
  refine ⟨potential, ?_⟩
  rw [levelTwo_coboundary0_eq]
  exact hp

/-- The same separation stated directly with the concrete chain complex's
syndrome map, for callers using the M3 code interface. -/
theorem levelTwoLocalError_sameChainSyndrome (S : OddScale)
    (first second : Word Field (levelTwoPresentation S).Q)
    (hfirst : levelTwoLocalError S first) (hsecond : levelTwoLocalError S second)
    (hsyn : wordLinearMapTranspose (levelTwoChainComplex S).boundary2 first =
      wordLinearMapTranspose (levelTwoChainComplex S).boundary2 second) :
    first + second ∈ (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier := by
  rw [levelTwo_coboundary1_eq] at hsyn
  exact levelTwoLocalError_sameSyndrome S first second hfirst hsecond hsyn

end QEC.Coding.BDL26LevelTwoDistance
