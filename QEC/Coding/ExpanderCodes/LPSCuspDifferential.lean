import QEC.Coding.ExpanderCodes.LPSHeckeCoefficients
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# LPSCuspDifferential

The original weight-two cusp function defines the actual pointwise complex differential. The genuine Mobius derivative proves Gamma0 tangent invariance and identifies the original determinant-p Hecke sum with p+1 differential pullbacks.
No differential law, regularity or Hecke pullback conclusion is assumed.
The algebraic modular curve, arithmetic magnitude bound and public PK22 theorem remain unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold
noncomputable section

/-- The true coefficient f(tau) dz acting on an actual complex tangent vector. -/
def lpsCuspDifferential (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) : ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ (f τ)

/-- The actual differential evaluated on a complex tangent vector. -/
lemma lpsCuspDifferential_apply (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (v : ℂ) : lpsCuspDifferential N f τ v = f τ*v := rfl

/-- Evaluation on the unit tangent proves that the original cusp form is recovered. -/
lemma lpsCuspDifferential_injective (N : ℕ) :
    Function.Injective (lpsCuspDifferential N) := by
  intro f g h
  apply DFunLike.ext
  intro τ
  have hv := congrArg (fun w => w τ (1 : ℂ)) h
  simpa only [lpsCuspDifferential_apply,mul_one] using hv

/-- Positive determinant weight-two slash is actual holomorphic differential pullback. -/
lemma lpsWeightTwo_slash_deriv (f : ℍ→ℂ) (g : GL (Fin 2) ℝ)
    (hg : 0<g.val.det) (τ : ℍ) :
    (f ∣[(2:ℤ)] g) τ = f (g • τ)*
      deriv (fun z : ℂ => (g • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ) τ := by
  rw [UpperHalfPlane.deriv_smul hg]
  have hd : UpperHalfPlane.denom g τ≠0 := UpperHalfPlane.denom_ne_zero g τ
  simp only [ModularForm.slash_apply,UpperHalfPlane.σ,
    Matrix.GeneralLinearGroup.val_det_apply]
  simp [hg,abs_of_pos hg,zpow_neg]
  field_simp

/-- The actual original differential is invariant under true Gamma0 tangent pullback. -/
lemma lpsCuspDifferential_Gamma0 (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (g : GL (Fin 2) ℝ)
    (hg : g∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) (τ : ℍ) (v : ℂ) :
    lpsCuspDifferential N f (g • τ)
      (deriv (fun z : ℂ => (g • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ) τ*v) =
    lpsCuspDifferential N f τ v := by
  have hdet : g.val.det=1 := by
    simpa only [Matrix.GeneralLinearGroup.val_det_apply,Units.val_one] using
      congrArg Units.val (Subgroup.HasDetOne.det_eq hg)
  have hs := congrFun (SlashInvariantForm.slash_action_eqn f g hg) τ
  rw [lpsWeightTwo_slash_deriv f g (by rw [hdet];norm_num)] at hs
  simpa only [lpsCuspDifferential_apply,mul_assoc] using congrArg (fun z : ℂ => z*v) hs

/-- The original Hecke differential is the actual sum of p+1 tangent pullbacks. -/
lemma lpsCuspHecke_differential_sum (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (v : ℂ) :
    lpsCuspDifferential N (lpsCuspHeckeLinearMap N p hNp f) τ v =
      ∑i : Option (Fin p),lpsCuspDifferential N f (lpsHeckeUpperGL ℝ p i • τ)
        (deriv (fun z : ℂ => (lpsHeckeUpperGL ℝ p i • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ) τ*v) := by
  change lpsHeckeSlashSum p f τ * v = _
  simp only [lpsHeckeSlashSum,Finset.sum_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hp : 0<(lpsHeckeUpperGL ℝ p i).val.det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply,lpsHeckeUpperGL_det]
    exact_mod_cast (Fact.out : p.Prime).pos
  rw [lpsWeightTwo_slash_deriv f _ hp,lpsCuspDifferential_apply,mul_assoc]

end
end QEC.Coding.TannerLiftedProduct
