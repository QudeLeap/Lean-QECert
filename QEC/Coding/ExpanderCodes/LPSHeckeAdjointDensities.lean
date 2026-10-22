import QEC.Coding.ExpanderCodes.LPSHeckeEffectiveCovers
import QEC.Coding.ExpanderCodes.LPSHeckePeterssonIntegrals

/-!
# Actual Hecke adjoint density identities

True original factors and weight-two scalar invariance identify both densities with the same inverse-matrix density. No determinant-p normalization is inserted.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

/-- Every nonzero real scalar matrix acts trivially on arbitrary weight-two slash functions. -/
lemma lpsScalarWeightTwo (f : ℍ → ℂ) (u : ℝˣ) :
    (f ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.scalar (Fin 2) u) = f := by
  ext τ
  have hu : (u.val : ℂ) ≠ 0 := by exact_mod_cast u.ne_zero
  simp [ModularForm.slash_apply,UpperHalfPlane.σ,
    Matrix.GeneralLinearGroup.det_scalar,zpow_neg,hu,sq_pos_iff]

/-- The first canonical inverse representative has its genuine original real Hecke factor. -/
lemma lpsHeckeIntersectionRepresentative_factor (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) :
    ∃δ : SL(2,ℤ), δ∈CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperGL ℝ p none * Matrix.SpecialLinearGroup.mapGL ℝ
        (lpsHeckeIntersectionRepresentative N p hNp i : SL(2,ℤ))⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ δ * lpsHeckeUpperGL ℝ p i := by
  obtain ⟨δ,hδ,he⟩ := lpsHeckeRightIndex_spec N p hNp
    (lpsHeckeIntersectionRepresentative N p hNp i : SL(2,ℤ))⁻¹
    ((CongruenceSubgroup.Gamma0 N).inv_mem
      (lpsHeckeIntersectionRepresentative N p hNp i).property) none
  rw [lpsHeckeIntersectionRepresentative_index] at he
  exact ⟨δ,hδ,lpsHeckeRightFactorGL ℝ p _ _ _ _ he⟩

/-- The second canonical inverse representative has its actual original real Hecke factor. -/
lemma lpsHeckeConjugateRepresentative_factor (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) :
    ∃δ : SL(2,ℤ), δ∈CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperGL ℝ p (some ⟨0,(Fact.out:p.Prime).pos⟩) * Matrix.SpecialLinearGroup.mapGL ℝ
        (lpsHeckeConjugateRepresentative N p hNp i : SL(2,ℤ))⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ δ * lpsHeckeUpperGL ℝ p i := by
  obtain ⟨δ,hδ,he⟩ := lpsHeckeRightIndex_spec N p hNp
    (lpsHeckeConjugateRepresentative N p hNp i : SL(2,ℤ))⁻¹
    ((CongruenceSubgroup.Gamma0 N).inv_mem
      (lpsHeckeConjugateRepresentative N p hNp i).property)
    (some ⟨0,(Fact.out:p.Prime).pos⟩)
  rw [lpsHeckeConjugateRepresentative_index] at he
  exact ⟨δ,hδ,lpsHeckeRightFactorGL ℝ p _ _ _ _ he⟩

/-- The original zero finite matrix is exactly scalar(p) times the original infinity inverse. -/
lemma lpsHeckeZero_scalarInverse (p : ℕ) [Fact p.Prime] :
    lpsHeckeUpperGL ℝ p (some ⟨0,(Fact.out:p.Prime).pos⟩) =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.mk0 (p:ℝ) (by exact_mod_cast (Fact.out:p.Prime).ne_zero)) *
          (lpsHeckeUpperGL ℝ p none)⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply Units.ext
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [lpsHeckeUpperGL_coe,lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.coe_scalar,Matrix.natCast_apply]

/-- Actual scalar invariance identifies the original zero slash with infinity inverse slash. -/
lemma lpsHeckeZero_slashInverse (p : ℕ) [Fact p.Prime] (g : ℍ→ℂ) :
    (g ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p (some ⟨0,(Fact.out:p.Prime).pos⟩)) =
      (g ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) := by
  rw [lpsHeckeZero_scalarInverse,SlashAction.slash_mul,lpsScalarWeightTwo]

/-- The genuine first factor identity transfers the original left Hecke density to the A-image cover. -/
lemma lpsHeckeLeft_density (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (i : Option (Fin p)) (τ : ℍ) :
    petersson 2 (f ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) g τ =
      petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹)
        (lpsHeckeUpperGL ℝ p none •
          ((lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • τ)) := by
  let γ : SL(2,ℤ) := (lpsHeckeIntersectionRepresentative N p hNp i : SL(2,ℤ))⁻¹
  have hγ : γ∈CongruenceSubgroup.Gamma0 N := (CongruenceSubgroup.Gamma0 N).inv_mem
    (lpsHeckeIntersectionRepresentative N p hNp i).property
  obtain ⟨δ,hδ,he⟩ := lpsHeckeIntersectionRepresentative_factor N p hNp i
  have hf : ((f:ℍ→ℂ) ∣[(2:ℤ)]
      (lpsHeckeUpperGL ℝ p none*Matrix.SpecialLinearGroup.mapGL ℝ γ)) =
        ((f:ℍ→ℂ) ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) := by
    rw [he,SlashAction.slash_mul]
    change (((f:ℍ→ℂ) ∣[(2:ℤ)] δ) ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i)=_
    rw [lpsWeightTwoCusp_slash_gamma0 N f δ hδ]
  have hp := petersson_slash_SL 2 ((f:ℍ→ℂ) ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p none) (g:ℍ→ℂ) γ τ
  rw [lpsWeightTwoCusp_slash_gamma0 N g γ hγ] at hp
  change petersson 2 (((f:ℍ→ℂ) ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p none) ∣[(2:ℤ)]
    Matrix.SpecialLinearGroup.mapGL ℝ γ) g τ = _ at hp
  rw [←SlashAction.slash_mul,hf] at hp
  rw [hp,lpsWeightTwoPetersson_transfer]
  · rfl
  · rw [lpsHeckeUpperGL_det]
    exact_mod_cast (Fact.out:p.Prime).pos

/-- The actual second factor identity transfers the original right Hecke density to the inverse cover. -/
lemma lpsHeckeRight_density (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (i : Option (Fin p)) (τ : ℍ) :
    petersson 2 f (g ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) τ =
      petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹)
        ((lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ • τ) := by
  let γ : SL(2,ℤ) := (lpsHeckeConjugateRepresentative N p hNp i : SL(2,ℤ))⁻¹
  have hγ : γ∈CongruenceSubgroup.Gamma0 N := (CongruenceSubgroup.Gamma0 N).inv_mem
    (lpsHeckeConjugateRepresentative N p hNp i).property
  obtain ⟨δ,hδ,he⟩ := lpsHeckeConjugateRepresentative_factor N p hNp i
  have hg : ((g:ℍ→ℂ) ∣[(2:ℤ)]
      (lpsHeckeUpperGL ℝ p (some ⟨0,(Fact.out:p.Prime).pos⟩)*Matrix.SpecialLinearGroup.mapGL ℝ γ)) =
        ((g:ℍ→ℂ) ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) := by
    rw [he,SlashAction.slash_mul]
    change (((g:ℍ→ℂ) ∣[(2:ℤ)] δ) ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i)=_
    rw [lpsWeightTwoCusp_slash_gamma0 N g δ hδ]
  have hp := petersson_slash_SL 2 (f:ℍ→ℂ)
    ((g:ℍ→ℂ) ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p (some ⟨0,(Fact.out:p.Prime).pos⟩)) γ τ
  rw [lpsWeightTwoCusp_slash_gamma0 N f γ hγ] at hp
  change petersson 2 f (((g:ℍ→ℂ) ∣[(2:ℤ)]
    lpsHeckeUpperGL ℝ p (some ⟨0,(Fact.out:p.Prime).pos⟩)) ∣[(2:ℤ)]
    Matrix.SpecialLinearGroup.mapGL ℝ γ) τ = _ at hp
  rw [←SlashAction.slash_mul,hg,lpsHeckeZero_slashInverse] at hp
  exact hp

end
end QEC.Coding.TannerLiftedProduct
