import QEC.Coding.Stabilizer.Parameters
import QEC.Locality.CorrectableRegions.SemanticDistanceErasure
import QEC.Semantics.ErrorCorrection.QuditNoInformation
/-!
# Two correctable regions and stabilizer logical dimension

This internal module realizes the finite stabilizer dimension argument behind
the two-correctable-regions lemma.  Its hypotheses are concrete finite-register
erasure recoveries; the conclusion is derived from the binary stabilizer
presentation and the finite symplectic form.
-/

noncomputable section

namespace QEC
namespace Locality

open QEC Semantics Coding
open PauliSymplectic

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- View a finite qubit subsystem as the definitional all-two qudit subsystem. -/
def quditSubsystemOfFinite (S : FiniteSubsystem ι) :
    QuditSubsystem (fun _ : ι => 2) :=
  ⟨S.selected⟩

/-- A concrete qubit erasure recovery makes the selected subsystem information-free. -/
theorem erasureCorrectableFromRegister_noInformation
    (S : FiniteSubsystem ι) (C : QuantumCode (Qubit.QubitRegister ι))
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι))
    (hRecovery : Correctable (Qubit.QubitRegister ι) S.complementSystem C
      S.erasureChannelFromRegister recovery) :
    (quditSubsystemOfFinite S).NoInformationOn C := by
  exact (quditSubsystemOfFinite S).erasureRecovery_implies_noInformationOn C
    ((quditSubsystemOfFinite S).maximallyMixedSelected (by
      intro i
      norm_num)) recovery hRecovery

/-- A local Pauli branch is detectable after concrete recovery from its erasure. -/
theorem detectableOn_embeddedLocalPauli_of_erasureCorrectableFromRegister
    (S : FiniteSubsystem ι) (C : QuantumCode (Qubit.QubitRegister ι))
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι))
    (hRecovery : Correctable (Qubit.QubitRegister ι) S.complementSystem C
      S.erasureChannelFromRegister recovery) (p : LocalPauliWordIndex S) :
    DetectableOn C (toQubitOperator (embeddedLocalPauli S p)) := by
  have hInformation :=
    erasureCorrectableFromRegister_noInformation S C recovery hRecovery
  have hAll :=
    ((quditSubsystemOfFinite S).noInformationOn_iff_allLocalScalarCompression C).mp
      hInformation
  have hScalar := hAll (toQubitOperator (wordBinaryPauli S p))
  apply (QuditSubsystem.scalarCompression_iff_detectableOn C _).mp
  rw [toQubitOperator_embeddedLocalPauli_eq_extendLocalToRegister]
  exact hScalar

/-- Extend a symplectic vector on a finite coordinate region by zero elsewhere. -/
def embedCoordinateVector (R : Finset ι) :
    SymplecticVector (ZMod 2) {i : ι // i ∈ R} →ₗ[ZMod 2]
      SymplecticVector (ZMod 2) ι where
  toFun v :=
    { xPart := fun i => if hi : i ∈ R then v.xPart ⟨i, hi⟩ else 0
      zPart := fun i => if hi : i ∈ R then v.zPart ⟨i, hi⟩ else 0 }
  map_add' := by
    intro a b
    apply (SymplecticVector.toProdLinearEquiv (F := ZMod 2) (ι := ι)).injective
    apply Prod.ext <;> funext i <;>
      by_cases hi : i ∈ R <;> simp [SymplecticVector.toProdLinearEquiv,
        SymplecticVector.toProdEquiv, SymplecticVector.xPart_add,
        SymplecticVector.zPart_add, hi]
  map_smul' := by
    intro c a
    apply (SymplecticVector.toProdLinearEquiv (F := ZMod 2) (ι := ι)).injective
    apply Prod.ext <;> funext i <;>
      by_cases hi : i ∈ R <;> simp [SymplecticVector.toProdLinearEquiv,
        SymplecticVector.toProdEquiv, SymplecticVector.xPart_smul,
        SymplecticVector.zPart_smul, hi]

/-- The finite binary subspace supported in a coordinate region. -/
def coordinateSubspace (R : Finset ι) :
    Submodule (ZMod 2) (SymplecticVector (ZMod 2) ι) :=
  LinearMap.range (embedCoordinateVector R)

theorem embedCoordinateVector_injective (R : Finset ι) :
    Function.Injective (embedCoordinateVector R) := by
  intro a b h
  apply (SymplecticVector.toProdLinearEquiv
    (F := ZMod 2) (ι := {i : ι // i ∈ R})).injective
  apply Prod.ext <;> funext i
  · have hx := congrArg (fun v : SymplecticVector (ZMod 2) ι => v.xPart i.1) h
    simpa [embedCoordinateVector, SymplecticVector.toProdLinearEquiv,
      SymplecticVector.toProdEquiv, i.2] using hx
  · have hz := congrArg (fun v : SymplecticVector (ZMod 2) ι => v.zPart i.1) h
    simpa [embedCoordinateVector, SymplecticVector.toProdLinearEquiv,
      SymplecticVector.toProdEquiv, i.2] using hz

/-- The coordinate subspace has two binary dimensions per selected qubit. -/
theorem finrank_coordinateSubspace (R : Finset ι) :
    Module.finrank (ZMod 2) (coordinateSubspace R) = 2 * R.card := by
  rw [coordinateSubspace,
    LinearMap.finrank_range_of_inj (embedCoordinateVector_injective R)]
  rw [(SymplecticVector.toProdLinearEquiv
    (F := ZMod 2) (ι := {i : ι // i ∈ R})).finrank_eq,
    Module.finrank_prod, Module.finrank_pi]
  simp [two_mul]

/-- Coordinates outside a region symplectically commute with every coordinate in it. -/
theorem coordinateSubspace_compl_le_orthogonal (R : Finset ι) :
    coordinateSubspace Rᶜ ≤
      FiniteSymplectic.form.orthogonal (coordinateSubspace R) := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  change FiniteSymplectic.form (embedCoordinateVector R b)
    (embedCoordinateVector Rᶜ a) = 0
  rw [FiniteSymplectic.form_apply, symplecticForm]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ R
  · simp [embedCoordinateVector, hi]
  · simp [embedCoordinateVector, hi]

omit [DecidableEq ι] in
private theorem finrank_globalSymplecticVector :
    Module.finrank (ZMod 2) (SymplecticVector (ZMod 2) ι) =
      2 * Fintype.card ι := by
  rw [(SymplecticVector.toProdLinearEquiv
    (F := ZMod 2) (ι := ι)).finrank_eq,
    Module.finrank_prod, Module.finrank_pi]
  simp [two_mul]

/-- The symplectic orthogonal of a coordinate region is its finite complement. -/
theorem orthogonal_coordinateSubspace (R : Finset ι) :
    FiniteSymplectic.form.orthogonal (coordinateSubspace R) = coordinateSubspace Rᶜ := by
  symm
  apply Submodule.eq_of_le_of_finrank_le (coordinateSubspace_compl_le_orthogonal R)
  rw [LinearMap.BilinForm.finrank_orthogonal FiniteSymplectic.form_nondegenerate,
    finrank_globalSymplecticVector, finrank_coordinateSubspace,
    finrank_coordinateSubspace, R.card_compl]
  omega

/-- A region disjoint from `R` lies in the coordinate complement of `R`. -/
theorem coordinateSubspace_le_coordinateSubspace_compl
    {R T : Finset ι} (hDisjoint : Disjoint R T) :
    coordinateSubspace T ≤ coordinateSubspace Rᶜ := by
  rintro _ ⟨v, rfl⟩
  let w : SymplecticVector (ZMod 2) {i : ι // i ∈ Rᶜ} :=
    { xPart := fun i => if hi : i.1 ∈ T then v.xPart ⟨i.1, hi⟩ else 0
      zPart := fun i => if hi : i.1 ∈ T then v.zPart ⟨i.1, hi⟩ else 0 }
  refine ⟨w, ?_⟩
  apply (SymplecticVector.toProdEquiv (F := ZMod 2) (ι := ι)).injective
  apply Prod.ext <;> funext i
  · by_cases hi : i ∈ T
    · have hiR : i ∉ R := by
        intro hiR
        exact (Finset.disjoint_left.mp hDisjoint hiR hi)
      have hiRcompl : i ∈ Rᶜ := Finset.mem_compl.mpr hiR
      change (if h : i ∈ Rᶜ then w.xPart ⟨i, h⟩ else 0) =
        if h : i ∈ T then v.xPart ⟨i, h⟩ else 0
      simp [w, hi, hiRcompl]
    · change (if h : i ∈ Rᶜ then w.xPart ⟨i, h⟩ else 0) =
        if h : i ∈ T then v.xPart ⟨i, h⟩ else 0
      simp [w, hi]
  · by_cases hi : i ∈ T
    · have hiR : i ∉ R := by
        intro hiR
        exact (Finset.disjoint_left.mp hDisjoint hiR hi)
      have hiRcompl : i ∈ Rᶜ := Finset.mem_compl.mpr hiR
      change (if h : i ∈ Rᶜ then w.zPart ⟨i, h⟩ else 0) =
        if h : i ∈ T then v.zPart ⟨i, h⟩ else 0
      simp [w, hi, hiRcompl]
    · change (if h : i ∈ Rᶜ then w.zPart ⟨i, h⟩ else 0) =
        if h : i ∈ T then v.zPart ⟨i, h⟩ else 0
      simp [w, hi]

omit [DecidableEq ι] in
private theorem orthogonal_sup (U V : Submodule (ZMod 2)
    (SymplecticVector (ZMod 2) ι)) :
    FiniteSymplectic.form.orthogonal (U ⊔ V) =
      FiniteSymplectic.form.orthogonal U ⊓ FiniteSymplectic.form.orthogonal V := by
  ext x
  constructor
  · intro hx
    exact ⟨fun u hu => hx u (Submodule.mem_sup_left hu),
      fun v hv => hx v (Submodule.mem_sup_right hv)⟩
  · rintro ⟨hU, hV⟩ y hy
    rcases Submodule.mem_sup.mp hy with ⟨u, hu, v, hv, rfl⟩
    change FiniteSymplectic.form (u + v) x = 0
    rw [map_add]
    change FiniteSymplectic.form u x + FiniteSymplectic.form v x = 0
    rw [hU u hu, hV v hv, add_zero]

omit [DecidableEq ι] in
private theorem stabilizer_rank_coordinate_identity
    (L W : Submodule (ZMod 2) (SymplecticVector (ZMod 2) ι))
    (hIsotropic : L ≤ FiniteSymplectic.form.orthogonal L)
    (hLocalNormalizer : FiniteSymplectic.form.orthogonal L ⊓ W ≤ L) :
    Module.finrank (ZMod 2) L + Module.finrank (ZMod 2) ↥(L ⊓ W) =
      Module.finrank (ZMod 2) W +
        Module.finrank (ZMod 2) ↥(L ⊓ FiniteSymplectic.form.orthogonal W) := by
  have hLocalEq : FiniteSymplectic.form.orthogonal L ⊓ W = L ⊓ W := by
    apply le_antisymm
    · intro x hx
      exact ⟨hLocalNormalizer hx, hx.2⟩
    · intro x hx
      exact ⟨hIsotropic hx.1, hx.2⟩
  have hOrthogonalSup :
      FiniteSymplectic.form.orthogonal
          (L ⊔ FiniteSymplectic.form.orthogonal W) =
        FiniteSymplectic.form.orthogonal L ⊓ W := by
    rw [orthogonal_sup,
      LinearMap.BilinForm.orthogonal_orthogonal FiniteSymplectic.form_nondegenerate
        FiniteSymplectic.form_isAlt.isRefl]
  have hSup := Submodule.finrank_sup_add_finrank_inf_eq L
    (FiniteSymplectic.form.orthogonal W)
  have hOuter := LinearMap.BilinForm.finrank_orthogonal
    FiniteSymplectic.form_nondegenerate
    (L ⊔ FiniteSymplectic.form.orthogonal W)
  have hInner := LinearMap.BilinForm.finrank_orthogonal
    FiniteSymplectic.form_nondegenerate W
  rw [hOrthogonalSup, hLocalEq] at hOuter
  have hOuterAdd :
      Module.finrank (ZMod 2) ↥(L ⊓ W) +
        Module.finrank (ZMod 2) ↥(L ⊔ FiniteSymplectic.form.orthogonal W) =
      Module.finrank (ZMod 2) (SymplecticVector (ZMod 2) ι) := by
    rw [hOuter, Nat.sub_add_cancel (Submodule.finrank_le _)]
  have hInnerAdd :
      Module.finrank (ZMod 2) ↥(FiniteSymplectic.form.orthogonal W) +
        Module.finrank (ZMod 2) W =
      Module.finrank (ZMod 2) (SymplecticVector (ZMod 2) ι) := by
    rw [hInner, Nat.sub_add_cancel (Submodule.finrank_le _)]
  omega

/--
Concrete erasure correctability excludes non-stabilizer normalizer vectors
supported in the erased coordinate region.
-/
theorem normalizer_inf_coordinateSubspace_le_stabilizer
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (S : FiniteSubsystem ι)
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι))
    (hRecovery : Correctable (Qubit.QubitRegister ι) S.complementSystem P.semanticCode
      S.erasureChannelFromRegister recovery) :
    FiniteSymplectic.form.orthogonal P.code.1.generatedVectorSubspace ⊓
      coordinateSubspace S.selected ≤ P.code.1.generatedVectorSubspace := by
  rintro v ⟨hNormalizer, ⟨localVector, rfl⟩⟩
  let p : LocalPauliWordIndex S := (localVector.xPart, localVector.zPart)
  have hVector : (embeddedLocalPauli S p).vector =
      embedCoordinateVector S.selected localVector := by
    rfl
  have hBinaryNormalizer : P.code.1.InBinaryNormalizer (embeddedLocalPauli S p) :=
    (StabilizerCode.vector_mem_orthogonal_iff_inBinaryNormalizer P.code.1
      (embeddedLocalPauli S p)).1 (by simpa [hVector] using hNormalizer)
  have hDetectable : DetectableOn P.semanticCode (toQubitOperator (embeddedLocalPauli S p)) :=
    detectableOn_embeddedLocalPauli_of_erasureCorrectableFromRegister
      S P.semanticCode recovery hRecovery p
  have hGenerated : P.code.1.InGeneratedGroupUpToSign (embeddedLocalPauli S p) :=
    StabilizerCode.inGeneratedGroupUpToSign_of_detectableOn_of_inBinaryNormalizer
      P.code (embeddedLocalPauli S p) hBinaryNormalizer hDetectable
  exact (StabilizerCode.vector_mem_generatedVectorSubspace_iff P.code.1
    (embeddedLocalPauli S p)).2 hGenerated

/-- Two disjoint recoverable regions force the actual stabilizer rank to cover both. -/
theorem generatorRank_ge_two_correctable_region_cards
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (A B : FiniteSubsystem ι)
    (hDisjoint : Disjoint A.selected B.selected)
    (recoveryA : QuantumChannel A.complementSystem (Qubit.QubitRegister ι))
    (hRecoveryA : Correctable (Qubit.QubitRegister ι) A.complementSystem P.semanticCode
      A.erasureChannelFromRegister recoveryA)
    (recoveryB : QuantumChannel B.complementSystem (Qubit.QubitRegister ι))
    (hRecoveryB : Correctable (Qubit.QubitRegister ι) B.complementSystem P.semanticCode
      B.erasureChannelFromRegister recoveryB) :
    A.selected.card + B.selected.card ≤ P.generatorRank := by
  have hRankA := stabilizer_rank_coordinate_identity
    P.code.1.generatedVectorSubspace (coordinateSubspace A.selected)
    P.code.1.generatedVectorSubspace_isotropic
    (normalizer_inf_coordinateSubspace_le_stabilizer P A recoveryA hRecoveryA)
  have hRankB := stabilizer_rank_coordinate_identity
    P.code.1.generatedVectorSubspace (coordinateSubspace B.selected)
    P.code.1.generatedVectorSubspace_isotropic
    (normalizer_inf_coordinateSubspace_le_stabilizer P B recoveryB hRecoveryB)
  have hBInAOrthogonal : coordinateSubspace B.selected ≤
      FiniteSymplectic.form.orthogonal (coordinateSubspace A.selected) := by
    rw [orthogonal_coordinateSubspace]
    exact coordinateSubspace_le_coordinateSubspace_compl hDisjoint
  have hAInBOrthogonal : coordinateSubspace A.selected ≤
      FiniteSymplectic.form.orthogonal (coordinateSubspace B.selected) := by
    rw [orthogonal_coordinateSubspace]
    exact coordinateSubspace_le_coordinateSubspace_compl hDisjoint.symm
  have hInfB : P.code.1.generatedVectorSubspace ⊓ coordinateSubspace B.selected ≤
      P.code.1.generatedVectorSubspace ⊓
        FiniteSymplectic.form.orthogonal (coordinateSubspace A.selected) := by
    intro x hx
    exact ⟨hx.1, hBInAOrthogonal hx.2⟩
  have hInfA : P.code.1.generatedVectorSubspace ⊓ coordinateSubspace A.selected ≤
      P.code.1.generatedVectorSubspace ⊓
        FiniteSymplectic.form.orthogonal (coordinateSubspace B.selected) := by
    intro x hx
    exact ⟨hx.1, hAInBOrthogonal hx.2⟩
  have hDimB := Submodule.finrank_mono hInfB
  have hDimA := Submodule.finrank_mono hInfA
  rw [finrank_coordinateSubspace] at hRankA hRankB
  change A.selected.card + B.selected.card ≤
    Module.finrank (ZMod 2) P.code.1.generatedVectorSubspace
  omega

/--
For a finite faithful stabilizer presentation, exact recovery from erasure of
two disjoint regions bounds the encoded logical dimension by the remaining
region's qubit count.
-/
theorem two_correctable_regions_encodedQubits_le_separator_card
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (A B C : FiniteSubsystem ι)
    (hAB : Disjoint A.selected B.selected)
    (hAC : Disjoint A.selected C.selected)
    (hBC : Disjoint B.selected C.selected)
    (hCover : A.selected ∪ B.selected ∪ C.selected = Finset.univ)
    (recoveryA : QuantumChannel A.complementSystem (Qubit.QubitRegister ι))
    (hRecoveryA : Correctable (Qubit.QubitRegister ι) A.complementSystem P.semanticCode
      A.erasureChannelFromRegister recoveryA)
    (recoveryB : QuantumChannel B.complementSystem (Qubit.QubitRegister ι))
    (hRecoveryB : Correctable (Qubit.QubitRegister ι) B.complementSystem P.semanticCode
      B.erasureChannelFromRegister recoveryB) :
    P.encodedQubits ≤ C.selected.card := by
  have hRank := generatorRank_ge_two_correctable_region_cards
    P A B hAB recoveryA hRecoveryA recoveryB hRecoveryB
  have hABDisjointC : Disjoint (A.selected ∪ B.selected) C.selected := by
    rw [Finset.disjoint_left]
    intro i hi hC
    rcases Finset.mem_union.mp hi with hA | hB
    · exact Finset.disjoint_left.mp hAC hA hC
    · exact Finset.disjoint_left.mp hBC hB hC
  have hPartitionCard : (A.selected ∪ B.selected ∪ C.selected).card =
      A.selected.card + B.selected.card + C.selected.card := by
    rw [Finset.card_union_of_disjoint hABDisjointC,
      Finset.card_union_of_disjoint hAB]
  have hBlockLength : Fintype.card ι =
      A.selected.card + B.selected.card + C.selected.card := by
    calc
      Fintype.card ι = (Finset.univ : Finset ι).card := by simp
      _ = (A.selected ∪ B.selected ∪ C.selected).card := by rw [hCover]
      _ = A.selected.card + B.selected.card + C.selected.card := hPartitionCard
  have hEncoded : P.encodedQubits = Fintype.card ι - P.generatorRank := by
    simpa [StabilizerCode.BinaryStabilizerPresentation.blockLength] using
      P.encodedQubits_eq_blockLength_sub_generatorRank
  rw [hEncoded, hBlockLength]
  omega

end Locality
end QEC
