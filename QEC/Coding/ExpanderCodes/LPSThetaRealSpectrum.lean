import QEC.Coding.ExpanderCodes.LPSCuspHeckeRealSpectrum
import QEC.Coding.ExpanderCodes.LPSThetaCuspidalRemainder

/-!
# Real spectral expansion of the original centered theta residual

The original theta cusp remainder has a derived real finite Hecke expansion. The original
PSL cardinality and signed correction term are retained. The arithmetic coefficient estimate
and the public PK22 theorem remain unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped UpperHalfPlane ModularForm MatrixGroups
noncomputable section

/-- The ORIGINAL centered theta residual has a derived finite real Hecke spectral expansion. -/
lemma lpsThetaResidual_exists_realSpectralExpansion (p : ℕ) (a : LPSResiduePrime p) :
    ∃eigenvalue : Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 ((4*a.q)^2) : Subgroup (GL (Fin 2) ℝ)) 2))→ℝ,
    ∃c : Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 ((4*a.q)^2) : Subgroup (GL (Fin 2) ℝ)) 2))→ℂ,
    ∀n : ℕ,lpsCenteredThetaResidual a (2*n)=
      (Fintype.card PSL(2,ZMod a.q):ℝ)*
        (∑i,c i*(lpsHeckePolynomial ℂ (p:ℂ) (2*n)).eval (eigenvalue i:ℂ)).re+2*(-(p:ℝ))^n := by
  classical
  let : Fact p.Prime := ⟨a.degreePrime⟩
  let : NeZero ((4*a.q)^2) := ⟨pow_ne_zero _ (mul_ne_zero (by norm_num) a.prime.ne_zero)⟩
  have hNp : p.Coprime ((4*a.q)^2) := by
    convert a.coprime_thetaLevel using 1
    ring
  obtain ⟨b,eigenvalue,_hb,hcoeff⟩ := lpsCuspHecke_exists_realCoefficientExpansion ((4*a.q)^2) p hNp
  let f := lpsThetaCuspidalRemainder a.q a.modFour
  refine ⟨eigenvalue,fun i => b.repr f i*PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (b i)),?_⟩
  intro n
  rw [lpsCenteredThetaResidual_even_eq_cuspidal_coefficient,hcoeff]
  congr 2
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end QEC.Coding.TannerLiftedProduct
