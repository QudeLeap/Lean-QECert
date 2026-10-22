import QEC.Coding.Stabilizer.FiniteFieldPauli

/-!
# Finite local-check presentations for finite-field CSS complexes

This module packages the elementary boundary rows of a finite chain complex
as actual tensor-local qudit operators. The common fixed space is proved equal
to the transported finite-field CSS carrier, so blocklength, encoded dimension,
semantic distance, and locality all belong to one concrete presentation.
-/

noncomputable section

namespace QEC.Coding.FiniteFieldCSSPresentation

open QEC.Coding.FiniteFieldPauli

universe u

variable {F ι κ₀ κ₂ : Type u}
variable [Field F] [Fintype F]
variable [Fintype ι] [Fintype κ₀] [Fintype κ₂]

local instance : DecidableEq ι := Classical.decEq ι

/-- One scalar multiple of one X row, or one scalar multiple of one Z row. -/
abbrev CheckIndex (F κ₀ κ₂ : Type u) := Sum (κ₀ × F) (κ₂ × F)

/-- The elementary X-check word indexed by a degree-zero coordinate and scalar. -/
def xCheckWord
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (p : κ₀ × F) : Word F ι :=
  wordLinearMapTranspose K.boundary1 (p.2 • canonicalBasisWord p.1)

/-- The elementary Z-check word indexed by a degree-two coordinate and scalar. -/
def zCheckWord
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (p : κ₂ × F) : Word F ι :=
  K.boundary2 (p.2 • canonicalBasisWord p.1)

/-- The canonical qudit subsystem selected by a field word's Hamming support. -/
def wordRegion (x : Word F ι) :
    @Semantics.QuditSubsystem ι inferInstance (Classical.decEq ι)
      (fun _ : ι => Fintype.card F) where
  selected := hammingSupport x

/-- Outside its Hamming-support region a word vanishes. -/
theorem word_eq_zero_outside_wordRegion (x : Word F ι) :
    ∀ j, j ∉ (wordRegion x).selected → x j = 0 := by
  intro j hj
  simpa [wordRegion, hammingSupport] using hj

/-- The actual local qudit check associated with one elementary CSS row. -/
def check
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (c : CheckIndex F κ₀ κ₂) :
    @QLDPC.FiniteQuditCheck ι inferInstance (Classical.decEq ι)
      (Fintype.card F) :=
  match c with
  | Sum.inl p =>
      { region := wordRegion (xCheckWord K p)
        localOperator := selectedShift (wordRegion (xCheckWord K p)) (xCheckWord K p) }
  | Sum.inr p =>
      { region := wordRegion (zCheckWord K p)
        localOperator := selectedPhase (wordRegion (zCheckWord K p)) (zCheckWord K p) }

omit [Fintype κ₂] in
/-- An elementary X check extends to its transported global shift. -/
theorem check_inl_globalOperator
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (p : κ₀ × F) :
    (check K (Sum.inl p)).globalOperator =
      (registerUnitary (F := F) (ι' := ι)).conjOperator (shift (xCheckWord K p)) := by
  change (wordRegion (xCheckWord K p)).extendLocalToRegister
      (selectedShift (wordRegion (xCheckWord K p)) (xCheckWord K p)) = _
  exact extendLocalToRegister_selectedShift
    (wordRegion (xCheckWord K p)) (xCheckWord K p)
      (word_eq_zero_outside_wordRegion (xCheckWord K p))

omit [Fintype κ₂] in
/-- An elementary Z check extends to its transported global phase. -/
theorem check_inr_globalOperator
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (p : κ₂ × F) :
    (check K (Sum.inr p)).globalOperator =
      (registerUnitary (F := F) (ι' := ι)).conjOperator (phase (zCheckWord K p)) := by
  change (wordRegion (zCheckWord K p)).extendLocalToRegister
      (selectedPhase (wordRegion (zCheckWord K p)) (zCheckWord K p)) = _
  exact extendLocalToRegister_selectedPhase
    (wordRegion (zCheckWord K p)) (zCheckWord K p)
      (word_eq_zero_outside_wordRegion (zCheckWord K p))

/-- The transported CSS carrier is exactly the common fixed space of the
finite family of elementary local checks. -/
theorem mem_cssQuditCode_iff_elementaryChecks
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (ψ : Semantics.Qudit.QuditRegister (fun _ : ι => Fintype.card F)) :
    ψ ∈ (cssQuditCode K.firstCoboundaryCheckCode K.middleBoundaryCode).carrier ↔
      ∀ c : CheckIndex F κ₀ κ₂, (check K c).globalOperator ψ = ψ := by
  let U := registerUnitary (F := F) (ι' := ι)
  change ψ ∈ ((cssQuantumCode K.firstCoboundaryCheckCode
    K.middleBoundaryCode).transport U).carrier ↔ _
  rw [Semantics.QuantumCode.mem_transport_carrier_iff_symm]
  rw [mem_chainComplex_cssQuantumCode_iff_elementaryChecks]
  constructor
  · rintro ⟨hX, hZ⟩ c
    cases c with
    | inl p =>
        rw [check_inl_globalOperator]
        change U.toLinearEquiv
          (shift (xCheckWord K p) (U.toLinearEquiv.symm ψ)) = ψ
        simp only [xCheckWord]
        rw [hX p.1 p.2]
        exact U.toLinearEquiv.apply_symm_apply ψ
    | inr p =>
        rw [check_inr_globalOperator]
        change U.toLinearEquiv
          (phase (zCheckWord K p) (U.toLinearEquiv.symm ψ)) = ψ
        simp only [zCheckWord]
        rw [hZ p.1 p.2]
        exact U.toLinearEquiv.apply_symm_apply ψ
  · intro hfixed
    constructor
    · intro k a
      have h := hfixed (Sum.inl (k, a))
      rw [check_inl_globalOperator] at h
      have h' := congrArg U.toLinearEquiv.symm h
      simpa [xCheckWord, U] using h'
    · intro k a
      have h := hfixed (Sum.inr (k, a))
      rw [check_inr_globalOperator] at h
      have h' := congrArg U.toLinearEquiv.symm h
      simpa [zCheckWord, U] using h'

/-- Every finite chain complex over a finite field has a literal finite-qudit
local-check presentation with encoded dimension equal to its middle homology
rank. -/
def presentation
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂)) :
    @QLDPC.FiniteQuditCheckPresentation ι (CheckIndex F κ₀ κ₂)
      inferInstance (Classical.decEq ι) inferInstance where
  alphabetSize := Fintype.card F
  alphabetSize_ge_two := by
    exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  code := cssQuditCode K.firstCoboundaryCheckCode K.middleBoundaryCode
  checks := check K
  carrier_iff_fixed := by
    intro ψ
    exact mem_cssQuditCode_iff_elementaryChecks K ψ
  encodedQudits := Module.finrank F K.middleHomology
  dimension_eq := chainComplex_cssQuditCode_dimension_eq_pow_homology K

/-! ## Comparison with algebraic boundary incidence -/

/-- Forget the scalar multiple decorating a semantic elementary check. -/
def baseCheckIndex : CheckIndex F κ₀ κ₂ → Sum κ₀ κ₂
  | Sum.inl p => Sum.inl p.1
  | Sum.inr p => Sum.inr p.1

/-- Scalar-decorated checks are equivalently a base boundary row together
with one field scalar. -/
def checkIndexEquiv : CheckIndex F κ₀ κ₂ ≃ (Sum κ₀ κ₂) × F where
  toFun c := (baseCheckIndex c,
    match c with
    | Sum.inl p => p.2
    | Sum.inr p => p.2)
  invFun p :=
    match p.1 with
    | Sum.inl k => Sum.inl (k, p.2)
    | Sum.inr l => Sum.inr (l, p.2)
  left_inv := by rintro (⟨k, a⟩ | ⟨l, a⟩) <;> rfl
  right_inv := by rintro ⟨k | l, a⟩ <;> rfl

/-- A semantic scalar check can only touch coordinates touched by its
underlying algebraic boundary row. -/
theorem incident_baseCheckIndex_of_incident
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (c : CheckIndex F κ₀ κ₂) (q : ι)
    (hq : (presentation K).incidence.incident c q) :
    (QLDPC.chainComplexBoundaryIncidence K).incident (baseCheckIndex c) q := by
  cases c with
  | inl p =>
      rcases p with ⟨k, a⟩
      simp only [QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region,
        presentation, check, wordRegion, hammingSupport, Finset.mem_filter,
        Finset.mem_univ, true_and, xCheckWord, LinearMap.map_smul,
        Pi.smul_apply, smul_eq_mul] at hq
      simp only [baseCheckIndex,
        QLDPC.chainComplexBoundaryIncidence_incident_inl]
      intro hzero
      exact hq (by simp [hzero])
  | inr p =>
      rcases p with ⟨l, a⟩
      simp only [QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region,
        presentation, check, wordRegion, hammingSupport, Finset.mem_filter,
        Finset.mem_univ, true_and, zCheckWord, LinearMap.map_smul,
        Pi.smul_apply, smul_eq_mul] at hq
      simp only [baseCheckIndex,
        QLDPC.chainComplexBoundaryIncidence_incident_inr]
      intro hzero
      exact hq (by simp [hzero])

/-- Every semantic check region is contained in the support of its base
boundary row. In particular scalar decoration never increases row weight. -/
theorem checkRegion_subset_boundaryCheckSupport
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (c : CheckIndex F κ₀ κ₂) :
    ((presentation K).checks c).region.selected ⊆
      (QLDPC.chainComplexBoundaryIncidence K).checkSupport
        (baseCheckIndex c) := by
  intro q hq
  rw [QLDPC.CheckIncidence.mem_checkSupport]
  apply incident_baseCheckIndex_of_incident K c q
  exact hq

/-- The scalar-decorated semantic checks incident to a coordinate inject into
the product of its algebraic incident rows with all field scalars. -/
theorem variableSupport_map_subset_product
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (q : ι) :
    ((presentation K).incidence.variableSupport q).map
        checkIndexEquiv.toEmbedding ⊆
      (QLDPC.chainComplexBoundaryIncidence K).variableSupport q ×ˢ
        (Finset.univ : Finset F) := by
  intro p hp
  rw [Finset.mem_map] at hp
  obtain ⟨c, hc, rfl⟩ := hp
  rw [Finset.mem_product]
  constructor
  · rw [QLDPC.CheckIncidence.mem_variableSupport] at hc ⊢
    exact incident_baseCheckIndex_of_incident K c q hc
  · exact Finset.mem_univ _

/-- Decorating all base rows by finite-field scalars multiplies variable
degree by at most `|F|`. -/
theorem card_variableSupport_le_card_mul
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (q : ι) :
    ((presentation K).incidence.variableSupport q).card ≤
      ((QLDPC.chainComplexBoundaryIncidence K).variableSupport q).card *
        Fintype.card F := by
  calc
    ((presentation K).incidence.variableSupport q).card =
        (((presentation K).incidence.variableSupport q).map
          checkIndexEquiv.toEmbedding).card := by simp
    _ ≤ ((QLDPC.chainComplexBoundaryIncidence K).variableSupport q ×ˢ
          (Finset.univ : Finset F)).card :=
      Finset.card_le_card (variableSupport_map_subset_product K q)
    _ = ((QLDPC.chainComplexBoundaryIncidence K).variableSupport q).card *
        Fintype.card F := by simp

/-- Uniform row and column bounds for algebraic boundary incidence induce a
literal semantic qLDPC bound. The only overhead is one factor `|F|` in the
variable degree from listing every scalar multiple as a fixed-space check. -/
theorem presentation_boundedLocality_of_boundaryIncidence_bounds
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    {bound : Nat}
    (hcheck : ∀ c,
      ((QLDPC.chainComplexBoundaryIncidence K).checkSupport c).card ≤ bound)
    (hcoordinate : ∀ q,
      ((QLDPC.chainComplexBoundaryIncidence K).variableSupport q).card ≤ bound) :
    QEC.Coding.BoundedLocality (presentation K).localityProfile
      (bound * Fintype.card F) := by
  apply (presentation K).boundedLocality_of_region_bounds
  · intro c
    calc
      ((presentation K).checks c).region.selected.card ≤
          ((QLDPC.chainComplexBoundaryIncidence K).checkSupport
            (baseCheckIndex c)).card :=
        Finset.card_le_card (checkRegion_subset_boundaryCheckSupport K c)
      _ ≤ bound := hcheck (baseCheckIndex c)
      _ = bound * 1 := by simp
      _ ≤ bound * Fintype.card F :=
        Nat.mul_le_mul_left bound (by
          have := Fintype.card_pos (α := F)
          omega)
  · intro q
    exact (card_variableSupport_le_card_mul K q).trans
      (Nat.mul_le_mul_right (Fintype.card F) (hcoordinate q))

end QEC.Coding.FiniteFieldCSSPresentation
