import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Regions

/-! # Coordinate transport for actual RX local complexes -/

namespace QEC.Coding.BDL26RXDecoderAdapter

open MultiscaleDecoder
open scoped Classical BigOperators

noncomputable def wordEquiv {A B : Type} (e : A ≃ B) :
    Word BDL26Field A ≃ₗ[BDL26Field] Word BDL26Field B where
  toFun w b := w (e.symm b)
  invFun w a := w (e a)
  left_inv w := by funext a; simp
  right_inv w := by funext b; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem wordEquiv_apply {A B : Type} (e : A ≃ B)
    (w : Word BDL26Field A) (b : B) : wordEquiv e w b = w (e.symm b) := rfl

@[simp] theorem wordEquiv_symm_apply {A B : Type} (e : A ≃ B)
    (w : Word BDL26Field B) (a : A) : (wordEquiv e).symm w a = w (e a) := rfl

@[simp] theorem transpose_wordEquiv {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) : wordLinearMapTranspose (wordEquiv e).toLinearMap =
      (wordEquiv e).symm.toLinearMap := by
  apply LinearMap.ext
  intro w
  funext a
  rw [wordLinearMapTranspose]
  change (∑ b : B, w b * (Pi.single a (1 : BDL26Field) : Word BDL26Field A) (e.symm b)) = w (e a)
  rw [Fintype.sum_eq_single (e a)]
  · simp
  · intro b hb
    have hne : e.symm b ≠ a := by
      intro h
      apply hb
      rw [← h]
      simp
    simp [Pi.single_apply, hne]

noncomputable def reindexComplex
    {A0 A1 A2 B0 B1 B2 : Type}
    [Fintype A0] [Fintype A1] [Fintype A2]
    [Fintype B0] [Fintype B1] [Fintype B2]
    (K : ChainComplexData BDL26Field (Word BDL26Field A0)
      (Word BDL26Field A1) (Word BDL26Field A2))
    (e0 : A0 ≃ B0) (e1 : A1 ≃ B1) (e2 : A2 ≃ B2) :
    ChainComplexData BDL26Field (Word BDL26Field B0)
      (Word BDL26Field B1) (Word BDL26Field B2) where
  boundary1 := (wordEquiv e0).toLinearMap.comp
    (K.boundary1.comp (wordEquiv e1).symm.toLinearMap)
  boundary2 := (wordEquiv e1).toLinearMap.comp
    (K.boundary2.comp (wordEquiv e2).symm.toLinearMap)
  boundary_squared := by
    apply LinearMap.ext
    intro w
    funext b
    change wordEquiv e0 (K.boundary1 ((wordEquiv e1).symm
      (wordEquiv e1 (K.boundary2 ((wordEquiv e2).symm w))))) b = 0
    rw [LinearEquiv.symm_apply_apply]
    have h := LinearMap.congr_fun K.boundary_squared ((wordEquiv e2).symm w)
    change K.boundary1 (K.boundary2 ((wordEquiv e2).symm w)) = 0 at h
    rw [h, map_zero]
    rfl

section Complex

variable {A0 A1 A2 B0 B1 B2 : Type}
variable [Fintype A0] [Fintype A1] [Fintype A2]
variable [Fintype B0] [Fintype B1] [Fintype B2]
variable (K : ChainComplexData BDL26Field (Word BDL26Field A0)
  (Word BDL26Field A1) (Word BDL26Field A2))
variable (e0 : A0 ≃ B0) (e1 : A1 ≃ B1) (e2 : A2 ≃ B2)

noncomputable def reindexForward : ThreeTermChainMap K (reindexComplex K e0 e1 e2) where
  map0 := (wordEquiv e0).toLinearMap
  map1 := (wordEquiv e1).toLinearMap
  map2 := (wordEquiv e2).toLinearMap
  commutes_boundary1 := by
    apply LinearMap.ext
    intro w
    funext b
    change wordEquiv e0 (K.boundary1 ((wordEquiv e1).symm (wordEquiv e1 w))) b = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  commutes_boundary2 := by
    apply LinearMap.ext
    intro w
    funext b
    change wordEquiv e1 (K.boundary2 ((wordEquiv e2).symm (wordEquiv e2 w))) b = _
    rw [LinearEquiv.symm_apply_apply]
    rfl

noncomputable def reindexInverse : ThreeTermChainMap (reindexComplex K e0 e1 e2) K where
  map0 := (wordEquiv e0).symm.toLinearMap
  map1 := (wordEquiv e1).symm.toLinearMap
  map2 := (wordEquiv e2).symm.toLinearMap
  commutes_boundary1 := by
    apply LinearMap.ext
    intro w
    funext a
    change K.boundary1 ((wordEquiv e1).symm w) a =
      (wordEquiv e0).symm (wordEquiv e0 (K.boundary1 ((wordEquiv e1).symm w))) a
    rw [LinearEquiv.symm_apply_apply]
  commutes_boundary2 := by
    apply LinearMap.ext
    intro w
    funext a
    change K.boundary2 ((wordEquiv e2).symm w) a =
      (wordEquiv e1).symm (wordEquiv e1 (K.boundary2 ((wordEquiv e2).symm w))) a
    rw [LinearEquiv.symm_apply_apply]

noncomputable def reindexHomotopyEquiv : ThreeTermChainHomotopyEquiv K
    (reindexComplex K e0 e1 e2) where
  forward := reindexForward K e0 e1 e2
  inverse := reindexInverse K e0 e1 e2
  inverse_forward :=
    { homotopy0 := 0
      homotopy1 := 0
      degree0 := by ext w a; simp [reindexInverse, reindexForward, ThreeTermChainMap.comp,
        ThreeTermChainMap.id]
      degree1 := by ext w a; simp [reindexInverse, reindexForward, ThreeTermChainMap.comp,
        ThreeTermChainMap.id]
      degree2 := by ext w a; simp [reindexInverse, reindexForward, ThreeTermChainMap.comp,
        ThreeTermChainMap.id] }
  forward_inverse :=
    { homotopy0 := 0
      homotopy1 := 0
      degree0 := by ext w b; simp [reindexInverse, reindexForward, ThreeTermChainMap.comp,
        ThreeTermChainMap.id]
      degree1 := by ext w b; simp [reindexInverse, reindexForward, ThreeTermChainMap.comp,
        ThreeTermChainMap.id]
      degree2 := by ext w b; simp [reindexInverse, reindexForward, ThreeTermChainMap.comp,
        ThreeTermChainMap.id] }

noncomputable def reindexCohomologyEquiv :
    (reindexComplex K e0 e1 e2).middleCohomology ≃ₗ[BDL26Field] K.middleCohomology :=
  (reindexHomotopyEquiv K e0 e1 e2).inducedMiddleCohomologyEquiv

end Complex

@[simp] theorem transpose_wordEquiv_symm {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) : wordLinearMapTranspose (wordEquiv e).symm.toLinearMap =
      (wordEquiv e).toLinearMap := by
  exact transpose_wordEquiv e.symm

section Differential
variable {A0 A1 A2 B0 B1 B2 : Type}
variable [Fintype A0] [Fintype A1] [Fintype A2]
variable [Fintype B0] [Fintype B1] [Fintype B2]
theorem reindex_delta0 (K : ChainComplexData BDL26Field (Word BDL26Field A0)
    (Word BDL26Field A1) (Word BDL26Field A2))
    (e0 : A0 ≃ B0) (e1 : A1 ≃ B1) (e2 : A2 ≃ B2) :
    wordLinearMapTranspose (reindexComplex K e0 e1 e2).boundary1 =
      (wordEquiv e1).toLinearMap.comp
        ((wordLinearMapTranspose K.boundary1).comp (wordEquiv e0).symm.toLinearMap) := by
  simp [reindexComplex, wordLinearMapTranspose_comp, LinearMap.comp_assoc]

theorem reindex_delta1 (K : ChainComplexData BDL26Field (Word BDL26Field A0)
    (Word BDL26Field A1) (Word BDL26Field A2))
    (e0 : A0 ≃ B0) (e1 : A1 ≃ B1) (e2 : A2 ≃ B2) :
    wordLinearMapTranspose (reindexComplex K e0 e1 e2).boundary2 =
      (wordEquiv e2).toLinearMap.comp
        ((wordLinearMapTranspose K.boundary2).comp (wordEquiv e1).symm.toLinearMap) := by
  simp [reindexComplex, wordLinearMapTranspose_comp, LinearMap.comp_assoc]

end Differential

-- Coordinate changes preserve the exact Hamming weight.
theorem wordEquiv_weight {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B)
    (w : Word BDL26Field A) : HammingWeight (wordEquiv e w) = HammingWeight w := by
  unfold HammingWeight
  apply Finset.card_equiv e.symm
  intro b
  constructor
  · intro hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
  · intro hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩

end QEC.Coding.BDL26RXDecoderAdapter
