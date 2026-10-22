import QEC.Coding.ExpanderCodes.LPSHeckePeterssonAdjunction
import QEC.Coding.ExpanderCodes.LPSCongruenceFiniteDimension
import QEC.Coding.ExpanderCodes.LPSCuspPeterssonPositive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Real spectral expansion of the original cusp Hecke operator

The genuine positive Petersson pairing, actual adjunction and proved finite dimension give a
real eigenbasis of the original weight-two cusp space. The actual prime-power Hecke
recurrence then gives every original Fourier coefficient as a finite polynomial sum. Norm
and inner-product instances remain local to the spectral proof. No arithmetic eigenvalue
bound is proved.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped UpperHalfPlane ModularForm MatrixGroups
noncomputable section

/-- The true first Fourier coefficient on the original cusp space is complex linear. -/
def lpsCuspFirstCoefficient (N : ℕ) :
    CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 →ₗ[ℂ] ℂ where
  toFun f := PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 f)
  map_add' f g := by
    simp only [FunLike.coe_add, ModularForm.qExpansion_add (by norm_num : (0:ℝ)<1)
      (by simp) f g,map_add]
  map_smul' c f := by
    simp only [FunLike.coe_smul, ModularForm.qExpansion_smul (by norm_num : (0:ℝ)<1)
      (by simp) c f,PowerSeries.coeff_smul,smul_eq_mul,RingHom.id_apply]

/-- Positive genuine Petersson pairing, true adjunction and proved finite dimension give real eigenvalues. -/
lemma lpsCuspHecke_exists_realEigenBasis (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) :
    ∃b : Module.Basis (Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2))) ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
    ∃eigenvalue : Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2))→ℝ,
    ∀i,lpsCuspHeckeLinearMap N p hNp (b i)=(eigenvalue i:ℂ) • b i := by
  classical
  let : InnerProductSpace.Core ℂ
    (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) := lpsCuspPeterssonCore N
  let : NormedAddCommGroup
    (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : InnerProductSpace ℂ
    (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :=
    InnerProductSpace.ofCore (lpsCuspPeterssonCore N).toCore
  let := lpsGamma0CuspFiniteDimensional N 2
  have hT : (lpsCuspHeckeLinearMap N p hNp).IsSymmetric := by
    intro f g
    change lpsCuspPeterssonPairing N (lpsCuspHeckeLinearMap N p hNp f) g =
      lpsCuspPeterssonPairing N f (lpsCuspHeckeLinearMap N p hNp g)
    exact lpsCuspHecke_pairing_selfAdjoint N p hNp f g
  exact ⟨(hT.eigenvectorBasis rfl).toBasis,hT.eigenvalues rfl,hT.apply_eigenvectorBasis rfl⟩

/-- A genuine eigenbasis expands the actual prime-power operator, including zero dimension. -/
lemma lpsCuspHecke_primePower_eigenBasis (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) {I : Type*} [Fintype I]
    (b : Module.Basis I ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2))
    (eigenvalue : I→ℝ) (hb : ∀i,lpsCuspHeckeLinearMap N p hNp (b i)=(eigenvalue i:ℂ) • b i)
    (r : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsHeckePrimePowerLinearMap N p hNp r f =
      ∑i,(b.repr f i*(lpsHeckePolynomial ℂ (p:ℂ) r).eval (eigenvalue i:ℂ)) • b i := by
  classical
  have hi (i : I) : lpsHeckePrimePowerLinearMap N p hNp r (b i) =
      (lpsHeckePolynomial ℂ (p:ℂ) r).eval (eigenvalue i:ℂ) • b i := by
    rw [lpsHeckePrimePowerLinearMap_eq_polynomial]
    change (aeval (lpsCuspHeckeLinearMap N p hNp) (lpsHeckePolynomial ℂ (p:ℂ) r)) (b i)=_
    exact Module.End.aeval_apply_of_mem_apply_eq_smul (hb i)
  calc
    _ = lpsHeckePrimePowerLinearMap N p hNp r (∑i,b.repr f i • b i) := by rw [b.sum_repr]
    _ = ∑i,b.repr f i • lpsHeckePrimePowerLinearMap N p hNp r (b i) := by
      rw [map_sum]
      simp only [map_smul]
    _ = _ := by simp_rw [hi,smul_smul]

/-- The original prime-power Fourier coefficient is the real-eigenbasis polynomial sum. -/
lemma lpsCuspHecke_coefficient_eigenBasis (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) {I : Type*} [Fintype I]
    (b : Module.Basis I ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2))
    (eigenvalue : I→ℝ) (hb : ∀i,lpsCuspHeckeLinearMap N p hNp (b i)=(eigenvalue i:ℂ) • b i)
    (r : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    PowerSeries.coeff (p^r) (UpperHalfPlane.qExpansion 1 f) =
      ∑i,b.repr f i*(lpsHeckePolynomial ℂ (p:ℂ) r).eval (eigenvalue i:ℂ)*
        PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (b i)) := by
  classical
  rw [←coeff_one_lpsHeckePrimePowerLinearMap N p hNp r f]
  change lpsCuspFirstCoefficient N (lpsHeckePrimePowerLinearMap N p hNp r f)=_
  rw [lpsCuspHecke_primePower_eigenBasis N p hNp b eigenvalue hb,map_sum]
  simp only [map_smul,smul_eq_mul]
  rfl

/-- Real spectral expansion of the ORIGINAL cusp space is derived, not an eigenbasis supplied by a caller. -/
lemma lpsCuspHecke_exists_realCoefficientExpansion (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) :
    ∃b : Module.Basis (Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2))) ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
    ∃eigenvalue : Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2))→ℝ,
    (∀i,lpsCuspHeckeLinearMap N p hNp (b i)=(eigenvalue i:ℂ) • b i) ∧
    ∀r (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
      PowerSeries.coeff (p^r) (UpperHalfPlane.qExpansion 1 f)=
      ∑i,b.repr f i*(lpsHeckePolynomial ℂ (p:ℂ) r).eval (eigenvalue i:ℂ)*
        PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (b i)) := by
  classical
  obtain ⟨b,eigenvalue,hb⟩ := lpsCuspHecke_exists_realEigenBasis N p hNp
  exact ⟨b,eigenvalue,hb,lpsCuspHecke_coefficient_eigenBasis N p hNp b eigenvalue hb⟩

end
end QEC.Coding.TannerLiftedProduct
