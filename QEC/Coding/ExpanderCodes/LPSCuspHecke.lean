import QEC.Coding.ExpanderCodes.LPSHeckeRepresentatives
import QEC.Coding.ExpanderCodes.LPSModularDilation

/-!
# Actual weight-two cusp Hecke action

The finite sum of true determinant-p slash operators is invariant under Gamma0(N)
by the actual right-index permutation. Holomorphicity and rational cusp transport
prove that it is a genuine CuspForm on the same group. No invariance, cusp vanishing,
coefficient action or spectral conclusion is assumed.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

/-- The genuine finite sum of weight-two slash actions. -/
noncomputable def lpsHeckeSlashSum (p : ℕ) [Fact p.Prime] (f : ℍ→ℂ) : ℍ→ℂ :=
  ∑ i : Option (Fin p),f ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i

/-- The proved right permutation and input Gamma0 invariance make the actual sum invariant. -/
lemma lpsHeckeSlashSum_invariant (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) :
    (lpsHeckeSlashSum p f ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ γ)=
      lpsHeckeSlashSum p f := by
  classical
  have he (i : Option (Fin p)) :
      (((f:ℍ→ℂ) ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ γ)=
        (f:ℍ→ℂ) ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p (lpsHeckeRightIndex N p hNp γ hγ i) := by
    obtain ⟨δ,hδ,h⟩ := lpsHeckeRightIndex_spec N p hNp γ hγ i
    rw [←SlashAction.slash_mul,lpsHeckeRightFactorGL ℝ p _ _ γ δ h,SlashAction.slash_mul]
    have hf := f.slash_action_eq' (Matrix.SpecialLinearGroup.mapGL ℝ δ) ⟨δ,hδ,rfl⟩
    change ((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ δ)=(f:ℍ→ℂ) at hf
    rw [hf]
  unfold lpsHeckeSlashSum
  rw [SlashAction.sum_slash]
  simp_rw [he]
  apply Fintype.sum_bijective (lpsHeckeRightIndex N p hNp γ hγ)
    (lpsHeckeRightIndex_bijective N p hNp γ hγ)
  intro i
  rfl

/-- Rational representative transport and finite summation preserve vanishing at every cusp. -/
lemma lpsHeckeSlashSum_zero_at_cusps (N p : ℕ) [NeZero N] [Fact p.Prime]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (c : OnePoint ℝ) (hc : IsCusp c (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    OnePoint.IsZeroAt c (lpsHeckeSlashSum p f) 2 := by
  classical
  have hz (i : Option (Fin p)) : OnePoint.IsZeroAt c
      ((f:ℍ→ℂ) ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) 2 := by
    have hs := lpsRationalGL_smul_cusp (lpsHeckeUpperGL ℚ p i) c
      (hc.mono (Subgroup.map_le_range (Matrix.SpecialLinearGroup.mapGL ℝ) _))
    rw [lpsHeckeUpperGL_rat_real] at hs
    have hsg : IsCusp (lpsHeckeUpperGL ℝ p i • c)
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) :=
      (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr hs
    exact OnePoint.IsZeroAt.smul_iff.mp (f.zero_at_cusps' hsg)
  intro g hg
  unfold lpsHeckeSlashSum
  rw [SlashAction.sum_slash,UpperHalfPlane.IsZeroAtImInfty,Filter.ZeroAtFilter]
  have ht := tendsto_finsetSum Finset.univ
    (fun (i : Option (Fin p)) _ => hz i g hg)
  simpa only [Finset.sum_fn,Finset.sum_const_zero] using ht

/-- The actual slash sum, with proved invariance, holomorphicity and all-cusp vanishing. -/
noncomputable def lpsCuspHecke (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 where
  toFun := lpsHeckeSlashSum p f
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ,hγ,rfl⟩ := hg
    exact lpsHeckeSlashSum_invariant N p hNp f γ hγ
  holo' := by
    change MDiff (lpsHeckeSlashSum p (f:ℍ→ℂ))
    unfold lpsHeckeSlashSum
    apply MDifferentiable.sum
    intro i _
    have hf : MDiff (f:ℍ→ℂ) := f.holo'
    exact hf.slash 2 (lpsHeckeUpperGL ℝ p i)
  zero_at_cusps' := lpsHeckeSlashSum_zero_at_cusps N p f _


end QEC.Coding.TannerLiftedProduct
