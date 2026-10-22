import QEC.Locality.CorrectableRegions.TwoCorrectableRegionsDimension
import QEC.Coding.Stabilizer.FixedGeneratorInteraction

/-!
# Correctable finite-region closure

This internal module proves CPTP erasure-recovery closure for finite qudit
subsystems and for source-decoupled finite families in the fixed binary
stabilizer presentation model.
-/

noncomputable section

namespace QEC.Locality

open QEC Semantics Coding
open PauliSymplectic

universe u v w

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The phase-free restriction of a binary Pauli to a finite coordinate region. -/
def restrictBinaryTo (R : Finset ι) (E : Binary ι) : Binary ι :=
  { phase := 0
    vector :=
      { xPart := fun i => if i ∈ R then E.vector.xPart i else 0
        zPart := fun i => if i ∈ R then E.vector.zPart i else 0 } }

/-- The local Pauli word obtained by restricting both binary components. -/
def localIndexOfBinary (S : FiniteSubsystem ι) (E : Binary ι) :
    LocalPauliWordIndex S :=
  (fun i => E.vector.xPart i, fun i => E.vector.zPart i)

theorem restrictBinaryTo_eq_embeddedLocalPauli (S : FiniteSubsystem ι) (E : Binary ι) :
    restrictBinaryTo S.selected E = embeddedLocalPauli S (localIndexOfBinary S E) := by
  rfl

theorem support_restrictBinaryTo_subset (R : Finset ι) (E : Binary ι) :
    support (restrictBinaryTo R E) ⊆ R := by
  intro i hi
  by_contra hiR
  rw [mem_support] at hi
  rcases hi with hx | hz
  · have hzero : (restrictBinaryTo R E).vector.xPart i = 0 := by
      simp [restrictBinaryTo, hiR]
    exact ((mem_binarySupport _ i).1 (by simpa [xSupport] using hx)) hzero
  · have hzero : (restrictBinaryTo R E).vector.zPart i = 0 := by
      simp [restrictBinaryTo, hiR]
    exact ((mem_binarySupport _ i).1 (by simpa [zSupport] using hz)) hzero

/-- Restricting first to a smaller region and then to a larger one changes no vector data. -/
theorem restrictBinaryTo_restrictBinaryTo_vector_of_subset
    (R S : Finset ι) (hRS : R ⊆ S) (E : Binary ι) :
    (restrictBinaryTo S (restrictBinaryTo R E)).vector = (restrictBinaryTo R E).vector := by
  apply (SymplecticVector.toProdEquiv (F := ZMod 2) (ι := ι)).injective
  apply Prod.ext <;> funext i
  · by_cases hiR : i ∈ R
    · have hiS : i ∈ S := hRS hiR
      change (if i ∈ S then if i ∈ R then E.vector.xPart i else 0 else 0) =
        if i ∈ R then E.vector.xPart i else 0
      simp [hiR, hiS]
    · change (if i ∈ S then if i ∈ R then E.vector.xPart i else 0 else 0) =
        if i ∈ R then E.vector.xPart i else 0
      simp [hiR]
  · by_cases hiR : i ∈ R
    · have hiS : i ∈ S := hRS hiR
      change (if i ∈ S then if i ∈ R then E.vector.zPart i else 0 else 0) =
        if i ∈ R then E.vector.zPart i else 0
      simp [hiR, hiS]
    · change (if i ∈ S then if i ∈ R then E.vector.zPart i else 0 else 0) =
        if i ∈ R then E.vector.zPart i else 0
      simp [hiR]

/-- Coordinate-subspace membership is the vector form of finite support containment. -/
theorem support_subset_of_vector_mem_coordinateSubspace
    (R : Finset ι) (E : Binary ι) (hE : E.vector ∈ coordinateSubspace R) :
    support E ⊆ R := by
  rcases hE with ⟨v, hv⟩
  intro i hi
  by_contra hiR
  have hx : E.vector.xPart i = 0 := by
    rw [← hv]
    simp [embedCoordinateVector, hiR]
  have hz : E.vector.zPart i = 0 := by
    rw [← hv]
    simp [embedCoordinateVector, hiR]
  rcases (mem_support E i).1 hi with hxi | hzi
  · exact ((mem_binarySupport _ i).1 (by simpa [xSupport] using hxi)) hx
  · exact ((mem_binarySupport _ i).1 (by simpa [zSupport] using hzi)) hz

/-- Pauli representatives with disjoint physical supports commute. -/
theorem commutes_of_disjoint_support (E F : Binary ι)
    (hdisjoint : Disjoint (support E) (support F)) : Commutes E F := by
  change symplecticForm E.vector F.vector = 0
  rw [symplecticForm]
  apply Finset.sum_eq_zero
  intro i _
  have hxz : E.vector.xPart i * F.vector.zPart i = 0 := by
    by_cases hE : E.vector.xPart i = 0
    · simp [hE]
    by_cases hF : F.vector.zPart i = 0
    · simp [hF]
    exfalso
    apply (Finset.disjoint_left.mp hdisjoint)
    · exact (mem_support E i).2 (Or.inl ((mem_binarySupport _ i).2 hE))
    · exact (mem_support F i).2 (Or.inr ((mem_binarySupport _ i).2 hF))
  have hzx : E.vector.zPart i * F.vector.xPart i = 0 := by
    by_cases hE : E.vector.zPart i = 0
    · simp [hE]
    by_cases hF : F.vector.xPart i = 0
    · simp [hF]
    exfalso
    apply (Finset.disjoint_left.mp hdisjoint)
    · exact (mem_support E i).2 (Or.inr ((mem_binarySupport _ i).2 hE))
    · exact (mem_support F i).2 (Or.inl ((mem_binarySupport _ i).2 hF))
  rw [hxz, hzx]
  simp

/-- Restriction to two disjoint regions recombines every Pauli supported on their union. -/
theorem restrictBinaryTo_vector_add_of_support_subset_union
    (A B : Finset ι) (E : Binary ι)
    (hdisjoint : Disjoint A B) (hsupport : support E ⊆ A ∪ B) :
    E.vector = (restrictBinaryTo A E).vector + (restrictBinaryTo B E).vector := by
  apply (SymplecticVector.toProdEquiv (F := ZMod 2) (ι := ι)).injective
  apply Prod.ext <;> funext i
  · by_cases hiA : i ∈ A
    · have hiB : i ∉ B := by
        intro hiB
        exact (Finset.disjoint_left.mp hdisjoint hiA hiB)
      change E.vector.xPart i =
        (if i ∈ A then E.vector.xPart i else 0) +
          (if i ∈ B then E.vector.xPart i else 0)
      simp [hiA, hiB]
    · by_cases hiB : i ∈ B
      · change E.vector.xPart i =
          (if i ∈ A then E.vector.xPart i else 0) +
            (if i ∈ B then E.vector.xPart i else 0)
        simp [hiA, hiB]
      · have hinot : i ∉ support E := by
          intro hi
          rcases Finset.mem_union.mp (hsupport hi) with hiA' | hiB'
          · exact hiA hiA'
          · exact hiB hiB'
        have hzero : E.vector.xPart i = 0 := by
          by_contra hzero
          exact hinot ((mem_support E i).2
            (Or.inl ((mem_binarySupport _ i).2 hzero)))
        change E.vector.xPart i =
          (if i ∈ A then E.vector.xPart i else 0) +
            (if i ∈ B then E.vector.xPart i else 0)
        simp [hiA, hiB, hzero]
  · by_cases hiA : i ∈ A
    · have hiB : i ∉ B := by
        intro hiB
        exact (Finset.disjoint_left.mp hdisjoint hiA hiB)
      change E.vector.zPart i =
        (if i ∈ A then E.vector.zPart i else 0) +
          (if i ∈ B then E.vector.zPart i else 0)
      simp [hiA, hiB]
    · by_cases hiB : i ∈ B
      · change E.vector.zPart i =
          (if i ∈ A then E.vector.zPart i else 0) +
            (if i ∈ B then E.vector.zPart i else 0)
        simp [hiA, hiB]
      · have hinot : i ∉ support E := by
          intro hi
          rcases Finset.mem_union.mp (hsupport hi) with hiA' | hiB'
          · exact hiA hiA'
          · exact hiB hiB'
        have hzero : E.vector.zPart i = 0 := by
          by_contra hzero
          exact hinot ((mem_support E i).2
            (Or.inr ((mem_binarySupport _ i).2 hzero)))
        change E.vector.zPart i =
          (if i ∈ A then E.vector.zPart i else 0) +
            (if i ∈ B then E.vector.zPart i else 0)
        simp [hiA, hiB, hzero]

omit [DecidableEq ι] in
theorem symplecticForm_add_left (a b c : SymplecticVector (ZMod 2) ι) :
    symplecticForm (a + b) c = symplecticForm a c + symplecticForm b c := by
  simp only [symplecticForm, SymplecticVector.xPart_add, SymplecticVector.zPart_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply]
  ring

omit [DecidableEq ι] in
theorem symplecticForm_add_right (a b c : SymplecticVector (ZMod 2) ι) :
    symplecticForm a (b + c) = symplecticForm a b + symplecticForm a c := by
  change FiniteSymplectic.form a (b + c) =
    FiniteSymplectic.form a b + FiniteSymplectic.form a c
  exact map_add (FiniteSymplectic.form a) b c

omit [DecidableEq ι] in
theorem symplectic_orthogonal_sup_eq_inf
    (U V : Submodule (ZMod 2) (SymplecticVector (ZMod 2) ι)) :
    FiniteSymplectic.form.orthogonal (U ⊔ V) =
      FiniteSymplectic.form.orthogonal U ⊓ FiniteSymplectic.form.orthogonal V := by
  ext x
  constructor
  · intro hx
    exact ⟨fun u hu => hx u (Submodule.mem_sup_left hu),
      fun v hv => hx v (Submodule.mem_sup_right hv)⟩
  · rintro ⟨hU, hV⟩ y hy
    rcases Submodule.mem_sup.mp hy with ⟨u, hu, v, hv, rfl⟩
    have hu0 : symplecticForm u x = 0 := hU u hu
    have hv0 : symplecticForm v x = 0 := hV v hv
    change symplecticForm (u + v) x = 0
    rw [symplecticForm_add_left, hu0, hv0, add_zero]

/- In the finite nondegenerate symplectic space, orthogonal turns infimum into supremum. -/
omit [DecidableEq ι] in
theorem symplectic_orthogonal_inf_eq_sup
    (U V : Submodule (ZMod 2) (SymplecticVector (ZMod 2) ι)) :
    FiniteSymplectic.form.orthogonal (U ⊓ V) =
      FiniteSymplectic.form.orthogonal U ⊔ FiniteSymplectic.form.orthogonal V := by
  have hle : FiniteSymplectic.form.orthogonal U ⊔
      FiniteSymplectic.form.orthogonal V ≤
      FiniteSymplectic.form.orthogonal (U ⊓ V) := by
    apply sup_le
    · exact LinearMap.BilinForm.orthogonal_le inf_le_left
    · exact LinearMap.BilinForm.orthogonal_le inf_le_right
  apply (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  have hInf := Submodule.finrank_sup_add_finrank_inf_eq U V
  have hOrthSup := Submodule.finrank_sup_add_finrank_inf_eq
    (FiniteSymplectic.form.orthogonal U) (FiniteSymplectic.form.orthogonal V)
  rw [← symplectic_orthogonal_sup_eq_inf] at hOrthSup
  simp only [LinearMap.BilinForm.finrank_orthogonal FiniteSymplectic.form_nondegenerate]
    at hOrthSup ⊢
  have hU := Submodule.finrank_le U
  have hV := Submodule.finrank_le V
  have hUV := Submodule.finrank_le (U ⊓ V)
  have hSupUV := Submodule.finrank_le (U ⊔ V)
  omega

/--
Concrete erasure recovery gives the stabilizer cleaning decomposition: every
normalizer representative differs from one supported outside the recovered region
by an actual generated-stabilizer vector.
-/
theorem exists_cleanedOutside_of_erasure_correctable
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (S : FiniteSubsystem ι)
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι))
    (hRecovery : Correctable (Qubit.QubitRegister ι) S.complementSystem P.semanticCode
      S.erasureChannelFromRegister recovery)
    (E : Binary ι) (hNormalizer : P.code.1.InBinaryNormalizer E) :
    ∃ s, s ∈ P.code.1.generatedVectorSubspace ∧
      ∃ outside : Binary ι,
        P.code.1.InBinaryNormalizer outside ∧
        support outside ⊆ S.selectedᶜ ∧
        E.vector = s + outside.vector := by
  let L := P.code.1.generatedVectorSubspace
  let N := FiniteSymplectic.form.orthogonal L
  let W := coordinateSubspace S.selected
  have hLocal : N ⊓ W ≤ L := by
    simpa [L, N, W] using
      normalizer_inf_coordinateSubspace_le_stabilizer P S recovery hRecovery
  have hClean : N ≤ L ⊔ coordinateSubspace S.selectedᶜ := by
    have hOrth : FiniteSymplectic.form.orthogonal L ≤
        FiniteSymplectic.form.orthogonal (N ⊓ W) :=
      LinearMap.BilinForm.orthogonal_le hLocal
    rw [symplectic_orthogonal_inf_eq_sup,
      LinearMap.BilinForm.orthogonal_orthogonal FiniteSymplectic.form_nondegenerate
        FiniteSymplectic.form_isAlt.isRefl,
      orthogonal_coordinateSubspace] at hOrth
    simpa [N, W] using hOrth
  have hEVector : E.vector ∈ N := by
    simpa [N, L] using
      (StabilizerCode.vector_mem_orthogonal_iff_inBinaryNormalizer P.code.1 E).2 hNormalizer
  rcases Submodule.mem_sup.mp (hClean hEVector) with ⟨s, hs, outsideVector, hOutside, hsum⟩
  let outside : Binary ι := { phase := 0, vector := outsideVector }
  have hOutsideNormalizer : P.code.1.InBinaryNormalizer outside := by
    apply (StabilizerCode.vector_mem_orthogonal_iff_inBinaryNormalizer P.code.1 outside).1
    have hsNormalizer : s ∈ N := by
      exact P.code.1.generatedVectorSubspace_isotropic hs
    have hsumNormalizer : s + outsideVector ∈ N := by
      rw [hsum]
      exact hEVector
    have houtside : outsideVector ∈ N := by
      simpa only [add_sub_cancel_left] using N.sub_mem hsumNormalizer hsNormalizer
    exact houtside
  refine ⟨s, hs, outside, hOutsideNormalizer, ?_, ?_⟩
  · exact support_subset_of_vector_mem_coordinateSubspace S.selectedᶜ outside (by
      simpa [outside] using hOutside)
  · simpa [outside] using hsum.symm

theorem inBinaryNormalizer_of_commutes_generators
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (E : Binary ι) (hcommutes : ∀ j : κ, Commutes E (P.generators j)) :
    P.code.1.InBinaryNormalizer E := by
  intro G hG
  rw [← P.generated_eq] at hG
  induction hG with
  | one => exact commutes_binaryOne_right E
  | generator j => exact hcommutes j
  | mul _ _ ihP ihQ => exact commutes_binaryMul_right ihP ihQ
  | dagger _ ihP => exact commutes_binaryDagger_right ihP

theorem commutes_restrictBinaryTo_generator_of_no_cross_edge
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (A B : Finset ι) (E : Binary ι)
    (hdisjoint : Disjoint A B)
    (hnoCross : P.fixedGeneratorNoCrossEdge (A : Set ι) (B : Set ι))
    (hdecompose : E.vector =
      (restrictBinaryTo A E).vector + (restrictBinaryTo B E).vector)
    (j : κ) (hE : Commutes E (P.generators j)) :
    Commutes (restrictBinaryTo A E) (P.generators j) := by
  by_cases hAG : Disjoint A (support (P.generators j))
  · exact commutes_of_disjoint_support _ _
      (Finset.disjoint_of_subset_left (support_restrictBinaryTo_subset A E) hAG)
  · have hBG : Disjoint B (support (P.generators j)) := by
      apply Finset.disjoint_left.mpr
      intro b hbB hbG
      rcases Finset.not_disjoint_iff.mp hAG with ⟨a, haA, haG⟩
      have hab : a ≠ b := by
        intro hab
        subst b
        exact (Finset.disjoint_left.mp hdisjoint haA hbB)
      exact hnoCross (by simpa using haA) (by simpa using hbB)
        ((P.fixedGeneratorInteractionGraph_adj_iff_actual_support a b).2
          ⟨hab, j, haG, hbG⟩)
    have hRB : Commutes (restrictBinaryTo B E) (P.generators j) :=
      commutes_of_disjoint_support _ _
        (Finset.disjoint_of_subset_left (support_restrictBinaryTo_subset B E) hBG)
    change symplecticForm E.vector (P.generators j).vector = 0 at hE
    rw [hdecompose, symplecticForm_add_left] at hE
    change symplecticForm (restrictBinaryTo B E).vector (P.generators j).vector = 0 at hRB
    change symplecticForm (restrictBinaryTo A E).vector (P.generators j).vector = 0
    rw [hRB] at hE
    simpa using hE

theorem inBinaryNormalizer_restrictBinaryTo_of_no_cross_edge
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (A B : Finset ι) (E : Binary ι)
    (hdisjoint : Disjoint A B)
    (hnoCross : P.fixedGeneratorNoCrossEdge (A : Set ι) (B : Set ι))
    (hdecompose : E.vector =
      (restrictBinaryTo A E).vector + (restrictBinaryTo B E).vector)
    (hE : P.code.1.InBinaryNormalizer E) :
    P.code.1.InBinaryNormalizer (restrictBinaryTo A E) ∧
      P.code.1.InBinaryNormalizer (restrictBinaryTo B E) := by
  have hA := inBinaryNormalizer_of_commutes_generators P (restrictBinaryTo A E)
    (fun j => commutes_restrictBinaryTo_generator_of_no_cross_edge
      P A B E hdisjoint hnoCross hdecompose j
      (hE (P.generators j) (by
        rw [← P.generated_eq]
        exact GeneratedStabilizer.generator j)))
  refine ⟨hA, ?_⟩
  have hnoCrossBA : P.fixedGeneratorNoCrossEdge (B : Set ι) (A : Set ι) := by
    intro b hb a ha hba
    exact hnoCross ha hb (P.fixedGeneratorInteractionGraph_symmetric hba)
  apply inBinaryNormalizer_of_commutes_generators P (restrictBinaryTo B E)
  intro j
  apply commutes_restrictBinaryTo_generator_of_no_cross_edge
    P B A E hdisjoint.symm hnoCrossBA
    (hdecompose.trans (add_comm _ _)) j
  exact hE (P.generators j) (by
    rw [← P.generated_eq]
    exact GeneratedStabilizer.generator j)

theorem inGeneratedGroupUpToSign_restrictBinaryTo_of_erasure_correctable
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (S : FiniteSubsystem ι)
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι))
    (hRecovery : Correctable (Qubit.QubitRegister ι) S.complementSystem P.semanticCode
      S.erasureChannelFromRegister recovery)
    (E : Binary ι) (hNormalizer : P.code.1.InBinaryNormalizer (restrictBinaryTo S.selected E)) :
    P.code.1.InGeneratedGroupUpToSign (restrictBinaryTo S.selected E) := by
  apply StabilizerCode.inGeneratedGroupUpToSign_of_detectableOn_of_inBinaryNormalizer
    P.code (restrictBinaryTo S.selected E) hNormalizer
  rw [restrictBinaryTo_eq_embeddedLocalPauli]
  exact detectableOn_embeddedLocalPauli_of_erasureCorrectableFromRegister
    S P.semanticCode recovery hRecovery (localIndexOfBinary S E)

/-- Any normalizer restriction to a subset of a concretely recoverable region is generated. -/
theorem inGeneratedGroupUpToSign_restrictBinaryTo_of_subset_erasure_correctable
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (S : FiniteSubsystem ι) (R : Finset ι) (hRS : R ⊆ S.selected)
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι))
    (hRecovery : Correctable (Qubit.QubitRegister ι) S.complementSystem P.semanticCode
      S.erasureChannelFromRegister recovery)
    (E : Binary ι) (hNormalizer : P.code.1.InBinaryNormalizer (restrictBinaryTo R E)) :
    P.code.1.InGeneratedGroupUpToSign (restrictBinaryTo R E) := by
  have hNormalizerS :
      P.code.1.InBinaryNormalizer (restrictBinaryTo S.selected (restrictBinaryTo R E)) := by
    apply (StabilizerCode.vector_mem_orthogonal_iff_inBinaryNormalizer P.code.1 _).1
    rw [restrictBinaryTo_restrictBinaryTo_vector_of_subset R S.selected hRS E]
    exact (StabilizerCode.vector_mem_orthogonal_iff_inBinaryNormalizer P.code.1 _).2
      hNormalizer
  have hGeneratedS :=
    inGeneratedGroupUpToSign_restrictBinaryTo_of_erasure_correctable
      P S recovery hRecovery (restrictBinaryTo R E) hNormalizerS
  apply (StabilizerCode.vector_mem_generatedVectorSubspace_iff P.code.1 _).1
  rw [← restrictBinaryTo_restrictBinaryTo_vector_of_subset R S.selected hRS E]
  exact (StabilizerCode.vector_mem_generatedVectorSubspace_iff P.code.1 _).2 hGeneratedS

/--
If `T` contains the fixed-generator outer boundary of `U`, the part of `U`
outside `T` has no fixed-generator edge to the complement of their union.
-/
theorem fixedGeneratorNoCrossEdge_sdiff_compl_union_of_outerBoundary_subset
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (U T : Finset ι)
    (hBoundary : P.fixedGeneratorOuterBoundary (U : Set ι) ⊆ (T : Set ι)) :
    P.fixedGeneratorNoCrossEdge ((U \ T : Finset ι) : Set ι)
      (((U ∪ T)ᶜ : Finset ι) : Set ι) := by
  intro u hu w hw huw
  have huDiff : u ∈ U \ T := by simpa using hu
  have huU : u ∈ U := (Finset.mem_sdiff.mp huDiff).1
  have hwNotU : w ∉ U := by
    intro hwU
    have : w ∈ U ∪ T := Finset.mem_union_left T hwU
    exact (Finset.mem_compl.mp (by simpa using hw)) this
  have hwBoundary : w ∈ P.fixedGeneratorOuterBoundary (U : Set ι) :=
    (P.mem_fixedGeneratorOuterBoundary_iff (U : Set ι) w).2
      ⟨by simpa using hwNotU, u, by simpa using huU, huw⟩
  have hwT : w ∈ T := by simpa using hBoundary hwBoundary
  have hwUnion : w ∈ U ∪ T := Finset.mem_union_right U hwT
  exact (Finset.mem_compl.mp (by simpa using hw)) hwUnion

/-- The concrete finite subsystem selected by the union of two regions. -/
def unionSubsystem (A B : FiniteSubsystem ι) : FiniteSubsystem ι :=
  ⟨A.selected ∪ B.selected⟩

/--
Two source-decoupled regions with explicit CPTP erasure recoveries have an
explicit CPTP recovery after erasing their union.
-/
theorem exists_erasureRecovery_of_fixedGeneratorDecoupled
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (A B : FiniteSubsystem ι)
    (recoveryA : QuantumChannel A.complementSystem (Qubit.QubitRegister ι))
    (recoveryB : QuantumChannel B.complementSystem (Qubit.QubitRegister ι))
    (hRecoveryA : Correctable (Qubit.QubitRegister ι) A.complementSystem P.semanticCode
      A.erasureChannelFromRegister recoveryA)
    (hRecoveryB : Correctable (Qubit.QubitRegister ι) B.complementSystem P.semanticCode
      B.erasureChannelFromRegister recoveryB)
    (hDecoupled : P.fixedGeneratorDecoupled (A.selected : Set ι) (B.selected : Set ι)) :
    ∃ recovery : QuantumChannel (unionSubsystem A B).complementSystem (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) (unionSubsystem A B).complementSystem P.semanticCode
        (unionSubsystem A B).erasureChannelFromRegister recovery := by
  have hAB : Disjoint A.selected B.selected := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiB
    exact (Set.disjoint_left.mp hDecoupled.1) (by simpa using hiA) (by simpa using hiB)
  let U := unionSubsystem A B
  have hPairs : ∀ p q : LocalPauliWordIndex U,
      localPauliAmplitude U ≠ 0 → localPauliAmplitude U ≠ 0 →
        P.code.1.InGeneratedGroupUpToSign
            (binaryMul (binaryDagger (embeddedLocalPauli U p))
              (embeddedLocalPauli U q)) ∨
          ¬ P.code.1.InBinaryNormalizer
            (binaryMul (binaryDagger (embeddedLocalPauli U p))
              (embeddedLocalPauli U q)) := by
    intro p q _ _
    let E := binaryMul (binaryDagger (embeddedLocalPauli U p))
      (embeddedLocalPauli U q)
    by_cases hNormalizer : P.code.1.InBinaryNormalizer E
    · left
      have hSupport : support E ⊆ A.selected ∪ B.selected := by
        simpa [E, U, unionSubsystem] using support_relative_embeddedLocalPauli_subset U p q
      have hDecompose := restrictBinaryTo_vector_add_of_support_subset_union
        A.selected B.selected E hAB hSupport
      obtain ⟨hNormalizerA, hNormalizerB⟩ :=
        inBinaryNormalizer_restrictBinaryTo_of_no_cross_edge P A.selected B.selected E
          hAB hDecoupled.2 hDecompose hNormalizer
      have hGeneratedA :=
        inGeneratedGroupUpToSign_restrictBinaryTo_of_erasure_correctable
          P A recoveryA hRecoveryA E hNormalizerA
      have hGeneratedB :=
        inGeneratedGroupUpToSign_restrictBinaryTo_of_erasure_correctable
          P B recoveryB hRecoveryB E hNormalizerB
      apply (StabilizerCode.vector_mem_generatedVectorSubspace_iff P.code.1 E).1
      rw [hDecompose]
      exact P.code.1.generatedVectorSubspace.add_mem
        ((StabilizerCode.vector_mem_generatedVectorSubspace_iff P.code.1 _).2 hGeneratedA)
        ((StabilizerCode.vector_mem_generatedVectorSubspace_iff P.code.1 _).2 hGeneratedB)
    · exact Or.inr hNormalizer
  rcases
      (StabilizerCode.exists_finiteKrausCorrectable_iff_pairProductCriterion_on_support
        P.code (embeddedLocalPauli U) (fun _ => localPauliAmplitude U)
        (embeddedLocalPauliKrausFamily_complete U)).2 hPairs with
    ⟨twirlRecovery, hTwirlKrausRecovery⟩
  rcases
      (Semantics.exists_finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel
        P.semanticCode
        (binaryPauliKrausFamily (embeddedLocalPauli U)
          (fun _ => localPauliAmplitude U))).1
        ⟨twirlRecovery, hTwirlKrausRecovery⟩ with
    ⟨_hComplete, twirlRecovery, hTwirlRecovery⟩
  have hTwirlRecovery' : Correctable (Qubit.QubitRegister ι)
      (Qubit.QubitRegister ι) P.semanticCode
      ((binaryPauliKrausFamily (embeddedLocalPauli U)
        (fun _ => localPauliAmplitude U)).toQuantumChannel
          (embeddedLocalPauliKrausFamily_complete U)) twirlRecovery := by
    simpa using hTwirlRecovery
  have hLocalTwirlRecovery : Correctable (Qubit.QubitRegister ι)
      (Qubit.QubitRegister ι) P.semanticCode (localPauliTwirl U) twirlRecovery := by
    rw [← embeddedLocalPauliKrausFamily_toQuantumChannel_eq_localPauliTwirl]
    exact hTwirlRecovery'
  exact erasureRecoverableFromRegister_of_localPauliTwirl_correctable
    U P.semanticCode twirlRecovery hLocalTwirlRecovery

theorem exists_erasureRecovery_of_localPauli_pair_criterion
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (S : FiniteSubsystem ι)
    (hPairs : ∀ p q : LocalPauliWordIndex S,
      localPauliAmplitude S ≠ 0 → localPauliAmplitude S ≠ 0 →
        P.code.1.InGeneratedGroupUpToSign
            (binaryMul (binaryDagger (embeddedLocalPauli S p))
              (embeddedLocalPauli S q)) ∨
          ¬ P.code.1.InBinaryNormalizer
            (binaryMul (binaryDagger (embeddedLocalPauli S p))
              (embeddedLocalPauli S q))) :
    ∃ recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) S.complementSystem P.semanticCode
        S.erasureChannelFromRegister recovery := by
  rcases
      (StabilizerCode.exists_finiteKrausCorrectable_iff_pairProductCriterion_on_support
        P.code (embeddedLocalPauli S) (fun _ => localPauliAmplitude S)
        (embeddedLocalPauliKrausFamily_complete S)).2 hPairs with
    ⟨twirlRecovery, hTwirlKrausRecovery⟩
  rcases
      (Semantics.exists_finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel
        P.semanticCode
        (binaryPauliKrausFamily (embeddedLocalPauli S)
          (fun _ => localPauliAmplitude S))).1
        ⟨twirlRecovery, hTwirlKrausRecovery⟩ with
    ⟨_hComplete, twirlRecovery, hTwirlRecovery⟩
  have hTwirlRecovery' : Correctable (Qubit.QubitRegister ι)
      (Qubit.QubitRegister ι) P.semanticCode
      ((binaryPauliKrausFamily (embeddedLocalPauli S)
        (fun _ => localPauliAmplitude S)).toQuantumChannel
          (embeddedLocalPauliKrausFamily_complete S)) twirlRecovery := by
    simpa using hTwirlRecovery
  have hLocalTwirlRecovery : Correctable (Qubit.QubitRegister ι)
      (Qubit.QubitRegister ι) P.semanticCode (localPauliTwirl S) twirlRecovery := by
    rw [← embeddedLocalPauliKrausFamily_toQuantumChannel_eq_localPauliTwirl]
    exact hTwirlRecovery'
  exact erasureRecoverableFromRegister_of_localPauliTwirl_correctable
    S P.semanticCode twirlRecovery hLocalTwirlRecovery

/-
Source convention note: Baspin--Krishna's Expansion Lemma is stated as
`U_source ⊇ ∂₊ T_source`.  In the downstream orientation, `T` contains `∂₊ U`,
so `T = U_source` and `U = T_source`.
The boundary is exactly the #375 fixed-generator outer boundary.
-/
/--
Two concretely erasure-correctable regions remain concretely correctable after
union when the second contains the first region's fixed-generator outer boundary.
-/
theorem exists_erasureRecovery_of_fixedGeneratorOuterBoundary_subset
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (U T : FiniteSubsystem ι)
    (recoveryU : QuantumChannel U.complementSystem (Qubit.QubitRegister ι))
    (recoveryT : QuantumChannel T.complementSystem (Qubit.QubitRegister ι))
    (hRecoveryU : Correctable (Qubit.QubitRegister ι) U.complementSystem P.semanticCode
      U.erasureChannelFromRegister recoveryU)
    (hRecoveryT : Correctable (Qubit.QubitRegister ι) T.complementSystem P.semanticCode
      T.erasureChannelFromRegister recoveryT)
    (hBoundary : P.fixedGeneratorOuterBoundary (U.selected : Set ι) ⊆
      (T.selected : Set ι)) :
    ∃ recovery : QuantumChannel (unionSubsystem U T).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) (unionSubsystem U T).complementSystem
        P.semanticCode (unionSubsystem U T).erasureChannelFromRegister recovery := by
  apply exists_erasureRecovery_of_localPauli_pair_criterion P (unionSubsystem U T)
  intro p q _ _
  let E := binaryMul (binaryDagger (embeddedLocalPauli (unionSubsystem U T) p))
    (embeddedLocalPauli (unionSubsystem U T) q)
  by_cases hNormalizer : P.code.1.InBinaryNormalizer E
  · left
    by_contra hNotGenerated
    obtain ⟨F, hFNormalizer, hNotCommutes⟩ :=
      StabilizerCode.exists_inBinaryNormalizer_not_commutes P.code.1
        hNormalizer hNotGenerated
    obtain ⟨sT, hsT, outside, hOutsideNormalizer, hOutsideSupport, hCleanT⟩ :=
      exists_cleanedOutside_of_erasure_correctable
        P T recoveryT hRecoveryT F hFNormalizer
    have hSupportParts : support outside ⊆
        (U.selected \ T.selected) ∪ (U.selected ∪ T.selected)ᶜ := by
      intro i hi
      have hiTCompl := hOutsideSupport hi
      have hiNotT : i ∉ T.selected := Finset.mem_compl.mp hiTCompl
      by_cases hiU : i ∈ U.selected
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hiU, hiNotT⟩)
      · apply Finset.mem_union_right
        exact Finset.mem_compl.mpr (by
          intro hiUnion
          rcases Finset.mem_union.mp hiUnion with hiU' | hiT
          · exact hiU hiU'
          · exact hiNotT hiT)
    have hPartsDisjoint : Disjoint (U.selected \ T.selected)
        (U.selected ∪ T.selected)ᶜ := by
      apply Finset.disjoint_left.mpr
      intro i hiLeft hiRight
      exact (Finset.mem_compl.mp hiRight)
        (Finset.mem_union_left T.selected (Finset.mem_sdiff.mp hiLeft).1)
    have hNoCross :=
      fixedGeneratorNoCrossEdge_sdiff_compl_union_of_outerBoundary_subset
        P U.selected T.selected hBoundary
    have hDecompose : outside.vector =
        (restrictBinaryTo (U.selected \ T.selected) outside).vector +
          (restrictBinaryTo (U.selected ∪ T.selected)ᶜ outside).vector :=
      restrictBinaryTo_vector_add_of_support_subset_union
        (U.selected \ T.selected) (U.selected ∪ T.selected)ᶜ outside
          hPartsDisjoint hSupportParts
    obtain ⟨hNormalizerUOnly, _hNormalizerOutsideUnion⟩ :=
      inBinaryNormalizer_restrictBinaryTo_of_no_cross_edge P
        (U.selected \ T.selected) (U.selected ∪ T.selected)ᶜ outside
        hPartsDisjoint hNoCross hDecompose hOutsideNormalizer
    have hGeneratedUOnly :=
      inGeneratedGroupUpToSign_restrictBinaryTo_of_subset_erasure_correctable
        P U (U.selected \ T.selected) Finset.sdiff_subset
          recoveryU hRecoveryU outside hNormalizerUOnly
    have hEOrthogonal : E.vector ∈
        FiniteSymplectic.form.orthogonal P.code.1.generatedVectorSubspace :=
      (StabilizerCode.vector_mem_orthogonal_iff_inBinaryNormalizer P.code.1 E).2
        hNormalizer
    have hEsT : symplecticForm E.vector sT = 0 := by
      change FiniteSymplectic.form E.vector sT = 0
      exact FiniteSymplectic.form_isAlt.isRefl sT E.vector (hEOrthogonal sT hsT)
    have hUOnlyVector :
        (restrictBinaryTo (U.selected \ T.selected) outside).vector ∈
          P.code.1.generatedVectorSubspace :=
      (StabilizerCode.vector_mem_generatedVectorSubspace_iff P.code.1 _).2
        hGeneratedUOnly
    have hEUOnly : symplecticForm E.vector
        (restrictBinaryTo (U.selected \ T.selected) outside).vector = 0 := by
      change FiniteSymplectic.form E.vector
        (restrictBinaryTo (U.selected \ T.selected) outside).vector = 0
      exact FiniteSymplectic.form_isAlt.isRefl
        (restrictBinaryTo (U.selected \ T.selected) outside).vector E.vector
          (hEOrthogonal _ hUOnlyVector)
    have hESupport : support E ⊆ U.selected ∪ T.selected := by
      simpa [E, unionSubsystem] using
        support_relative_embeddedLocalPauli_subset (unionSubsystem U T) p q
    have hOutsideUnionSupport :
        support (restrictBinaryTo (U.selected ∪ T.selected)ᶜ outside) ⊆
          (U.selected ∪ T.selected)ᶜ :=
      support_restrictBinaryTo_subset _ _
    have hSupportDisjoint : Disjoint (support E)
        (support (restrictBinaryTo (U.selected ∪ T.selected)ᶜ outside)) := by
      apply Finset.disjoint_left.mpr
      intro i hiE hiOutside
      exact (Finset.mem_compl.mp (hOutsideUnionSupport hiOutside)) (hESupport hiE)
    have hEOutsideUnion : Commutes E
        (restrictBinaryTo (U.selected ∪ T.selected)ᶜ outside) :=
      commutes_of_disjoint_support E _ hSupportDisjoint
    have hCommutesF : Commutes E F := by
      change symplecticForm E.vector F.vector = 0
      rw [hCleanT, symplecticForm_add_right, hDecompose,
        symplecticForm_add_right, hEsT, hEUOnly]
      change 0 + (0 + symplecticForm E.vector
        (restrictBinaryTo (U.selected ∪ T.selected)ᶜ outside).vector) = 0
      simpa [Commutes] using hEOutsideUnion
    exact hNotCommutes hCommutesF
  · exact Or.inr hNormalizer

/-- The concrete selected subsystem formed by the union of a finite region family. -/
def familyUnionSubsystem {α : Type w} (regions : α → FiniteSubsystem ι)
    (s : Finset α) : FiniteSubsystem ι :=
  ⟨s.biUnion fun a => (regions a).selected⟩

theorem exists_erasureRecovery_of_pairwise_fixedGeneratorDecoupled
    {κ : Type v} [Fintype κ] {α : Type w} [DecidableEq α]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (regions : α → FiniteSubsystem ι) (s : Finset α)
    (hRecovery : ∀ a, a ∈ s →
      ∃ recovery : QuantumChannel (regions a).complementSystem (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι) (regions a).complementSystem P.semanticCode
          (regions a).erasureChannelFromRegister recovery)
    (hDecoupled : ∀ a, a ∈ s → ∀ b, b ∈ s → a ≠ b →
      P.fixedGeneratorDecoupled ((regions a).selected : Set ι) ((regions b).selected : Set ι)) :
    ∃ recovery : QuantumChannel (familyUnionSubsystem regions s).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) (familyUnionSubsystem regions s).complementSystem
        P.semanticCode (familyUnionSubsystem regions s).erasureChannelFromRegister recovery := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      apply exists_erasureRecovery_of_localPauli_pair_criterion P
        (familyUnionSubsystem regions ∅)
      intro p q _ _
      have hEmpty : IsEmpty (familyUnionSubsystem regions ∅).SelectedCoordinates := by
        constructor
        intro i
        rcases Finset.mem_biUnion.mp i.property with ⟨a, ha, _⟩
        simp at ha
      have hsubsingleton : Subsingleton (LocalPauliWordIndex (familyUnionSubsystem regions ∅)) := by
        constructor
        intro x y
        apply Prod.ext <;> funext i
        · exact (hEmpty.false i).elim
        · exact (hEmpty.false i).elim
      have hpq : p = q := hsubsingleton.elim _ _
      subst q
      left
      apply (StabilizerCode.vector_mem_generatedVectorSubspace_iff P.code.1 _).1
      change (0 : SymplecticVector (ZMod 2) ι) ∈ P.code.1.generatedVectorSubspace
      exact P.code.1.generatedVectorSubspace.zero_mem
  | @insert a s haNotMem ih =>
      have hRecoveryTail : ∀ b, b ∈ s →
          ∃ recovery : QuantumChannel (regions b).complementSystem (Qubit.QubitRegister ι),
            Correctable (Qubit.QubitRegister ι) (regions b).complementSystem P.semanticCode
              (regions b).erasureChannelFromRegister recovery := by
        intro b hb
        exact hRecovery b (Finset.mem_insert_of_mem hb)
      have hDecoupledTail : ∀ b, b ∈ s → ∀ c, c ∈ s → b ≠ c →
          P.fixedGeneratorDecoupled ((regions b).selected : Set ι) ((regions c).selected : Set ι) := by
        intro b hb c hc hbc
        exact hDecoupled b (Finset.mem_insert_of_mem hb)
          c (Finset.mem_insert_of_mem hc) hbc
      rcases hRecovery a (Finset.mem_insert_self a s) with ⟨recoveryA, hRecoveryA⟩
      rcases ih hRecoveryTail hDecoupledTail with ⟨recoveryB, hRecoveryB⟩
      have hHeadTail : P.fixedGeneratorDecoupled ((regions a).selected : Set ι)
          ((familyUnionSubsystem regions s).selected : Set ι) := by
        constructor
        · apply Set.disjoint_left.mpr
          intro x hxA hxTail
          rcases Finset.mem_biUnion.mp (by simpa [familyUnionSubsystem] using hxTail) with
            ⟨b, hb, hxb⟩
          have hab : a ≠ b := by
            intro hab
            subst b
            exact haNotMem hb
          exact (Set.disjoint_left.mp
            (hDecoupled a (Finset.mem_insert_self a s) b
              (Finset.mem_insert_of_mem hb) hab).1) hxA (by simpa using hxb)
        · intro x hxA y hxTail hxy
          rcases Finset.mem_biUnion.mp (by simpa [familyUnionSubsystem] using hxTail) with
            ⟨b, hb, hyb⟩
          have hab : a ≠ b := by
            intro hab
            subst b
            exact haNotMem hb
          exact (hDecoupled a (Finset.mem_insert_self a s) b
            (Finset.mem_insert_of_mem hb) hab).2 hxA (by simpa using hyb) hxy
      have hUnion : familyUnionSubsystem regions (insert a s) =
          unionSubsystem (regions a) (familyUnionSubsystem regions s) := by
        simp only [familyUnionSubsystem, unionSubsystem, Finset.biUnion_insert]
      rw [hUnion]
      exact exists_erasureRecovery_of_fixedGeneratorDecoupled P (regions a)
        (familyUnionSubsystem regions s) recoveryA recoveryB hRecoveryA hRecoveryB hHeadTail

/--
Erasing a larger finite qudit region with a concrete CPTP recovery implies
concrete recovery for every selected subset, by discarding the additionally
retained coordinates before applying the original recovery.
-/
theorem exists_qudit_erasureRecovery_of_subset
    {q : ι → Nat} (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected)
    (C : QuantumCode (Qudit.QuditRegister q))
    (hRecovery : ∃ recovery : QuantumChannel T.complementSystem (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) T.complementSystem C
        T.erasureChannelFromRegister recovery) :
    ∃ recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) S.complementSystem C
        S.erasureChannelFromRegister recovery := by
  exact QuditSubsystem.erasureRecoverableFromRegister_mono S T hST C hRecovery

end QEC.Locality
