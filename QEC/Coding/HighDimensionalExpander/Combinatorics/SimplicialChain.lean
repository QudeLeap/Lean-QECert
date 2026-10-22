import QEC.Coding.ChainComplex.HomotopyDistance
import QEC.Coding.QLDPC.SourceValidity
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Data.Finset.Interval

/-!
# Finite binary chains of an abstract simplicial complex

This file supplies the construction layer used by the EKZ20
high-dimensional-expander codes.  Face coordinates are derived from an
actual finite abstract simplicial complex, and the boundary matrices are its
binary face-incidence matrices.  No external matrix or homological,
distance, or locality conclusion is accepted as construction data.
-/

namespace QEC.Coding.HighDimensionalExpander.SimplicialChain

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Faces with exactly `p` vertices.  Thus `Face K (p + 1)` is the usual set
of `p`-dimensional simplices. -/
structure Face (K : AbstractSimplicialComplex V) (p : Nat) where
  vertices : Finset V
  mem_complex : vertices ∈ K
  card_vertices : vertices.card = p

namespace Face

variable {K : AbstractSimplicialComplex V} {p : Nat}

instance : DecidableEq (Face K p) := fun σ τ =>
  decidable_of_iff (σ.vertices = τ.vertices) ⟨by
    intro h
    cases σ
    cases τ
    cases h
    rfl, congrArg vertices⟩

noncomputable instance : Fintype (Face K p) :=
  Fintype.ofInjective vertices (by
    intro σ τ h
    cases σ
    cases τ
    cases h
    rfl)

end Face

variable (K : AbstractSimplicialComplex V)

/-- Binary incidence between a `p`-vertex face and a `(p+1)`-vertex face. -/
def boundaryMatrix (p : Nat) :
    Matrix (Face K p) (Face K (p + 1)) (ZMod 2) :=
  fun σ τ => if σ.vertices ⊂ τ.vertices then 1 else 0

/-- Intermediate faces appearing in one coefficient of two consecutive
boundary maps. -/
noncomputable def intermediateFaces
    (p : Nat) (σ : Face K p) (υ : Face K (p + 2)) :
    Finset (Face K (p + 1)) :=
  Finset.univ.filter fun τ =>
    σ.vertices ⊂ τ.vertices ∧ τ.vertices ⊂ υ.vertices

private def intermediateFaceEquiv
    (p : Nat) (σ : Face K p) (υ : Face K (p + 2)) :
    {τ : Face K (p + 1) //
      σ.vertices ⊂ τ.vertices ∧ τ.vertices ⊂ υ.vertices} ≃
      {s : Finset V // s ∈ Finset.Ioo σ.vertices υ.vertices} where
  toFun τ := ⟨τ.1.vertices, Finset.mem_Ioo.mpr τ.2⟩
  invFun s := by
    have hs := Finset.mem_Ioo.mp s.2
    have hσs : σ.vertices ⊂ s.1 := hs.1
    have hsυ : s.1 ⊂ υ.vertices := hs.2
    have hCardLower : σ.vertices.card < s.1.card :=
      Finset.card_lt_card hσs
    have hCardUpper : s.1.card < υ.vertices.card :=
      Finset.card_lt_card hsυ
    have hCard : s.1.card = p + 1 := by
      rw [σ.card_vertices] at hCardLower
      rw [υ.card_vertices] at hCardUpper
      omega
    have hNonempty : s.1.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hEmpty
      have : s.1.card = 0 := by simp [hEmpty]
      omega
    exact ⟨⟨s.1,
      (K.isRelLowerSet_faces υ.mem_complex).2 hsυ.1 hNonempty,
      hCard⟩, hσs, hsυ⟩
  left_inv τ := by
    apply Subtype.ext
    cases τ with
    | mk τ _ =>
        cases τ
        rfl
  right_inv s := by
    apply Subtype.ext
    rfl

theorem card_intermediateFaces_of_ssubset
    (p : Nat) (σ : Face K p) (υ : Face K (p + 2))
    (hσυ : σ.vertices ⊂ υ.vertices) :
    (intermediateFaces K p σ υ).card = 2 := by
  have hCardEquiv := Fintype.card_congr
    (intermediateFaceEquiv K p σ υ)
  have hDifference : υ.vertices.card - σ.vertices.card = 2 := by
    rw [σ.card_vertices, υ.card_vertices]
    omega
  rw [Fintype.card_subtype, Fintype.card_coe] at hCardEquiv
  rw [Finset.card_Ioo_finset hσυ.1, hDifference] at hCardEquiv
  norm_num at hCardEquiv ⊢
  simpa [intermediateFaces] using hCardEquiv

theorem boundaryMatrix_mul_boundaryMatrix (p : Nat) :
    boundaryMatrix K p * boundaryMatrix K (p + 1) = 0 := by
  ext σ υ
  rw [Matrix.mul_apply]
  change (∑ τ,
    boundaryMatrix K p σ τ * boundaryMatrix K (p + 1) τ υ) =
      (0 : ZMod 2)
  by_cases hσυ : σ.vertices ⊂ υ.vertices
  · have hSum :
        (∑ τ,
          boundaryMatrix K p σ τ * boundaryMatrix K (p + 1) τ υ) =
          ∑ _τ ∈ intermediateFaces K p σ υ, (1 : ZMod 2) := by
      unfold intermediateFaces
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro τ _
      by_cases hστ : σ.vertices ⊂ τ.vertices <;>
        by_cases hτυ : τ.vertices ⊂ υ.vertices <;>
        simp [boundaryMatrix, hστ, hτυ]
    rw [hSum]
    have hCard := card_intermediateFaces_of_ssubset K p σ υ hσυ
    simp only [Finset.sum_const, hCard]
    simpa only [two_nsmul] using (ZModModule.add_self (1 : ZMod 2))
  · apply Finset.sum_eq_zero
    intro τ hτ
    simp only [boundaryMatrix]
    by_cases hστ : σ.vertices ⊂ τ.vertices
    · have hNotτυ : ¬τ.vertices ⊂ υ.vertices := by
        intro hτυ
        exact hσυ (hστ.trans hτυ)
      simp [hστ, hNotτυ]
    · simp [hστ]

/-- Boundary linear map from `(p+1)`-vertex faces to `p`-vertex faces. -/
noncomputable def boundary (p : Nat) :
    Word (ZMod 2) (Face K (p + 1)) →ₗ[ZMod 2]
      Word (ZMod 2) (Face K p) :=
  Matrix.toLin' (boundaryMatrix K p)

theorem boundary_squared (p : Nat) :
    (boundary K p).comp (boundary K (p + 1)) = 0 := by
  change (Matrix.toLin' (boundaryMatrix K p)).comp
    (Matrix.toLin' (boundaryMatrix K (p + 1))) = 0
  rw [← Matrix.toLin'_mul]
  rw [boundaryMatrix_mul_boundaryMatrix]
  simp

/-- Honest three-term binary chain complex centered on the `(p+1)`-vertex
faces. -/
noncomputable def chainComplexAt (p : Nat) :
    ChainComplexData (ZMod 2)
      (Word (ZMod 2) (Face K p))
      (Word (ZMod 2) (Face K (p + 1)))
      (Word (ZMod 2) (Face K (p + 2))) where
  boundary1 := boundary K p
  boundary2 := boundary K (p + 1)
  boundary_squared := boundary_squared K p

/-- The CSS stabilizer extracted from the actual simplicial boundaries has
the repository's source-valid binary semantics. -/
theorem binaryCSSCode_stabilizer_isSourceValidBinary (p : Nat) :
    ((chainComplexAt K p).binaryCSSCode).stabilizer.IsSourceValidBinary :=
  ChainComplexData.binaryCSSCode_stabilizer_isSourceValidBinary
    (chainComplexAt K p)

/-! ## Simplicial systoles and the chain-complex distance predicates -/

/-- Every nontrivial binary `p`-cycle has weight at least `d`. -/
def SystoleAtLeast (p d : Nat) : Prop :=
  ∀ z : Word (ZMod 2) (Face K (p + 1)),
    boundary K p z = 0 →
    (¬ ∃ y : Word (ZMod 2) (Face K (p + 2)),
      boundary K (p + 1) y = z) →
    d ≤ HammingWeight z

/-- Every nontrivial binary `p`-cocycle has weight at least `d`. -/
def CosystoleAtLeast (p d : Nat) : Prop :=
  ∀ x : Word (ZMod 2) (Face K (p + 1)),
    wordLinearMapTranspose (boundary K (p + 1)) x = 0 →
    (¬ ∃ y : Word (ZMod 2) (Face K p),
      wordLinearMapTranspose (boundary K p) y = x) →
    d ≤ HammingWeight x

theorem systoleAtLeast_iff_middleHomologyDistanceAtLeast
    (p d : Nat) :
    SystoleAtLeast K p d ↔
      MiddleHomologyDistanceAtLeast (chainComplexAt K p) d := by
  rfl

theorem cosystoleAtLeast_iff_middleCohomologyDistanceAtLeast
    (p d : Nat) :
    CosystoleAtLeast K p d ↔
      MiddleCohomologyDistanceAtLeast (chainComplexAt K p) d := by
  rfl

/-! ## Exact incidence counts and locality -/

/-- Codimension-one faces of `τ`. -/
noncomputable def facets
    (p : Nat) (τ : Face K (p + 1)) : Finset (Face K p) :=
  Finset.univ.filter fun σ => σ.vertices ⊂ τ.vertices

/-- One-dimensional cofaces of `σ`. -/
noncomputable def cofaces
    (p : Nat) (σ : Face K p) : Finset (Face K (p + 1)) :=
  Finset.univ.filter fun τ => σ.vertices ⊂ τ.vertices

private def facetEquiv
    (p : Nat) (hp : 1 ≤ p) (τ : Face K (p + 1)) :
    {σ : Face K p // σ.vertices ⊂ τ.vertices} ≃
      {s : Finset V // s ∈ τ.vertices.powersetCard p} where
  toFun σ := ⟨σ.1.vertices,
    Finset.mem_powersetCard.mpr ⟨σ.2.1, σ.1.card_vertices⟩⟩
  invFun s := by
    have hs := Finset.mem_powersetCard.mp s.2
    have hNonempty : s.1.Nonempty := by
      apply Finset.card_pos.mp
      rw [hs.2]
      omega
    have hNe : s.1 ≠ τ.vertices := by
      intro hEq
      have hCardEq := congrArg Finset.card hEq
      rw [hs.2, τ.card_vertices] at hCardEq
      omega
    exact ⟨⟨s.1,
      (K.isRelLowerSet_faces τ.mem_complex).2 hs.1 hNonempty,
      hs.2⟩,
      Finset.ssubset_iff_subset_ne.mpr ⟨hs.1, hNe⟩⟩
  left_inv σ := by
    apply Subtype.ext
    cases σ with
    | mk σ _ =>
        cases σ
        rfl
  right_inv s := by
    apply Subtype.ext
    rfl

theorem card_facets
    (p : Nat) (hp : 1 ≤ p) (τ : Face K (p + 1)) :
    (facets K p τ).card = p + 1 := by
  have hCardEquiv := Fintype.card_congr (facetEquiv K p hp τ)
  rw [Fintype.card_subtype, Fintype.card_coe] at hCardEquiv
  rw [Finset.card_powersetCard, τ.card_vertices,
    Nat.choose_succ_self_right] at hCardEquiv
  simpa [facets] using hCardEquiv

private theorem canonicalBasisWord_eq_single
    {I : Type u} [DecidableEq I] (i : I) :
    canonicalBasisWord (F := ZMod 2) i = Pi.single i 1 := by
  classical
  ext i'
  by_cases hi : i = i'
  · subst i'
    simp [canonicalBasisWord]
  · simp [canonicalBasisWord, hi]

private theorem matrixToLin_canonicalBasis
    {Row Col : Type u} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (M : Matrix Row Col (ZMod 2)) (c : Col) :
    Matrix.toLin' M (canonicalBasisWord (F := ZMod 2) c) =
      fun r => M r c := by
  rw [canonicalBasisWord_eq_single]
  ext r
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single c]
  · simp
  · intro c' _ hc'
    simp [hc']
  · simp

private theorem wordLinearMapTranspose_matrixToLin_canonicalBasis
    {Row Col : Type u} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (M : Matrix Row Col (ZMod 2)) (r : Row) :
    wordLinearMapTranspose (Matrix.toLin' M)
        (canonicalBasisWord (F := ZMod 2) r) =
      fun c => M r c := by
  rw [canonicalBasisWord_eq_single]
  ext c
  unfold wordLinearMapTranspose
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Fintype.sum_eq_single r]
  · simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single c]
    · simp
    · intro c' _ hc'
      simp [hc']
    · simp
  · intro r' hr'
    simp [hr']

theorem HammingWeight_boundary_canonicalBasis_eq_card_facets
    (p : Nat) (τ : Face K (p + 1)) :
    HammingWeight
        (boundary K p (canonicalBasisWord (F := ZMod 2) τ)) =
      (facets K p τ).card := by
  rw [boundary, matrixToLin_canonicalBasis]
  simp [HammingWeight, hammingSupport, boundaryMatrix, facets]

theorem HammingWeight_transpose_boundary_canonicalBasis_eq_card_cofaces
    (p : Nat) (σ : Face K p) :
    HammingWeight
        (wordLinearMapTranspose (boundary K p)
          (canonicalBasisWord (F := ZMod 2) σ)) =
      (cofaces K p σ).card := by
  rw [boundary, wordLinearMapTranspose_matrixToLin_canonicalBasis]
  simp [HammingWeight, hammingSupport, boundaryMatrix, cofaces]

private theorem HammingWeight_sum_elim
    {F A B : Type*} [Zero F] [DecidableEq F]
    [Fintype A] [Fintype B]
    (x : Word F A) (y : Word F B) :
    HammingWeight (Sum.elim x y) =
      HammingWeight x + HammingWeight y := by
  classical
  let e :
      {s : Sum A B // Sum.elim x y s ≠ 0} ≃
        Sum {a : A // x a ≠ 0} {b : B // y b ≠ 0} :=
    { toFun := fun s =>
        match s with
        | ⟨Sum.inl a, ha⟩ => Sum.inl ⟨a, ha⟩
        | ⟨Sum.inr b, hb⟩ => Sum.inr ⟨b, hb⟩
      invFun := fun s =>
        match s with
        | Sum.inl a => ⟨Sum.inl a.1, a.2⟩
        | Sum.inr b => ⟨Sum.inr b.1, b.2⟩
      left_inv := by rintro ⟨a | b, h⟩ <;> rfl
      right_inv := by rintro (a | b) <;> rfl }
  calc
    HammingWeight (Sum.elim x y) =
        Fintype.card {s : Sum A B // Sum.elim x y s ≠ 0} := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
    _ = Fintype.card (Sum {a : A // x a ≠ 0} {b : B // y b ≠ 0}) :=
      Fintype.card_congr e
    _ = HammingWeight x + HammingWeight y := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]

private theorem variableSupport_card_eq_boundary_columns
    (p : Nat) (τ : Face K (p + 1)) :
    ((QEC.QLDPC.chainComplexBoundaryIncidence (chainComplexAt K p)).variableSupport τ).card =
      HammingWeight
          (boundary K p (canonicalBasisWord (F := ZMod 2) τ)) +
        HammingWeight
          (wordLinearMapTranspose (boundary K (p + 1))
            (canonicalBasisWord (F := ZMod 2) τ)) := by
  classical
  let x := boundary K p (canonicalBasisWord (F := ZMod 2) τ)
  let z := wordLinearMapTranspose (boundary K (p + 1))
    (canonicalBasisWord (F := ZMod 2) τ)
  have hSupport :
      (QEC.QLDPC.chainComplexBoundaryIncidence
          (chainComplexAt K p)).variableSupport τ =
        hammingSupport (Sum.elim x z) := by
    ext c
    rw [QEC.QLDPC.CheckIncidence.mem_variableSupport]
    simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    cases c with
    | inl σ =>
        dsimp [QEC.QLDPC.chainComplexBoundaryIncidence, chainComplexAt, x]
        simp only [boundary]
        rw [wordLinearMapTranspose_matrixToLin_canonicalBasis,
          matrixToLin_canonicalBasis]
    | inr υ =>
        dsimp [QEC.QLDPC.chainComplexBoundaryIncidence, chainComplexAt, z]
        simp only [boundary]
        rw [matrixToLin_canonicalBasis,
          wordLinearMapTranspose_matrixToLin_canonicalBasis]
  rw [hSupport]
  change HammingWeight (Sum.elim x z) =
    HammingWeight x + HammingWeight z
  exact HammingWeight_sum_elim x z

/-- A genuine uniform coface bound gives qLDPC locality for the extracted
simplicial chain complex.  Downward incidences are counted exactly from the
face cardinalities; only upward degrees are hypotheses. -/
theorem boundedLocality_of_coface_bounds
    (p B : Nat) (hp : 1 ≤ p)
    (hLower : ∀ σ : Face K p, (cofaces K p σ).card ≤ B)
    (hMiddle : ∀ τ : Face K (p + 1),
      (cofaces K (p + 1) τ).card ≤ B) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (chainComplexAt K p)).localityProfile
      (max (max B (p + 2)) (p + 1 + B)) := by
  apply QEC.QLDPC.chainComplexBoundaryIncidence_boundedLocality_of_boundary_bounds
    (chainComplexAt K p)
  · intro σ
    change HammingWeight
      (wordLinearMapTranspose (boundary K p)
        (canonicalBasisWord (F := ZMod 2) σ)) ≤ _
    rw [HammingWeight_transpose_boundary_canonicalBasis_eq_card_cofaces]
    exact (hLower σ).trans (Nat.le_max_left _ _)
  · intro υ
    change HammingWeight
      (boundary K (p + 1)
        (canonicalBasisWord (F := ZMod 2) υ)) ≤ _
    rw [HammingWeight_boundary_canonicalBasis_eq_card_facets,
      card_facets K (p + 1) (by omega)]
    exact Nat.le_max_right _ _
  · intro τ
    rw [variableSupport_card_eq_boundary_columns,
      HammingWeight_boundary_canonicalBasis_eq_card_facets,
      HammingWeight_transpose_boundary_canonicalBasis_eq_card_cofaces,
      card_facets K p hp]
    exact Nat.add_le_add_left (hMiddle τ) (p + 1)

end QEC.Coding.HighDimensionalExpander.SimplicialChain
