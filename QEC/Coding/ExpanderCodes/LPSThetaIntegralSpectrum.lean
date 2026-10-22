import QEC.Coding.ExpanderCodes.LPSThetaIntegralLattice
import QEC.Coding.ExpanderCodes.LPSCuspHeckeRealSpectrum

/-!
# LPSThetaIntegralSpectrum

The actual original theta cusp form is annihilated by a derived monic integer polynomial. Its original real Hecke expansion has algebraic-integer eigenvalues on every nonzero term, retaining the exact PSL cardinality and signed correction.
No lattice, finite generation, stability, annihilator or integrality conclusion is assumed.
The arithmetic magnitude estimate and public PK22 theorem remain unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

/-- A derived integer polynomial annihilates the original nonzero theta cusp form. -/
lemma lpsTheta_exists_monic_originalHecke_annihilator
    (q p : ℕ) [Fact q.Prime] [Fact p.Prime] (hq4 : q%4=1)
    (hNp : p.Coprime ((4*q)^2)) :
    ∃ P : ℤ[X], P.Monic ∧
      (aeval (lpsCuspHeckeLinearMap ((4*q)^2) p hNp) (P.map (Int.castRingHom ℂ)))
        (lpsThetaCuspidalRemainder q hq4) = 0 := by
  have hq : q≠0 := (Fact.out : q.Prime).ne_zero
  let : NeZero ((4*q)^2) := ⟨by positivity⟩
  let f : lpsIntegralCuspLattice ((4*q)^2) :=
    ⟨lpsThetaIntegerDenominator q • lpsThetaCuspidalRemainder q hq4,
      lpsTheta_scaled_memIntegralLattice q hq4⟩
  obtain ⟨P, hP, hT⟩ := lpsIntegralCuspHecke_exists_monic_annihilator ((4*q)^2) p hNp
  refine ⟨P, hP, ?_⟩
  have hf : ((aeval (lpsIntegralCuspHecke ((4*q)^2) p hNp) P) f :
      CuspForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2) = 0 := by
    rw [hT]; rfl
  rw [lpsIntegralCuspHecke_polynomial_coe] at hf
  change (aeval (lpsCuspHeckeLinearMap ((4*q)^2) p hNp) (P.map (Int.castRingHom ℂ)))
    (lpsThetaIntegerDenominator q • lpsThetaCuspidalRemainder q hq4) = 0 at hf
  rw [← Int.cast_smul_eq_zsmul ℂ, map_smul] at hf
  have hd : (lpsThetaIntegerDenominator q : ℂ)≠0 := by
    exact_mod_cast lpsThetaIntegerDenominator_ne_zero q
  exact (smul_eq_zero.mp hf).resolve_left hd

/-- A genuine original Hecke eigenbasis diagonalizes every actual polynomial action. -/
lemma lpsCuspHecke_polynomial_repr (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) {I : Type*} [Fintype I]
    (b : Module.Basis I ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2))
    (eigenvalue : I→ℝ)
    (hb : ∀i,lpsCuspHeckeLinearMap N p hNp (b i)=(eigenvalue i:ℂ) • b i)
    (P : ℂ[X]) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (i : I) :
    b.repr ((aeval (lpsCuspHeckeLinearMap N p hNp) P) f) i =
      b.repr f i * P.eval (eigenvalue i:ℂ) := by
  classical
  have he (j : I) : (aeval (lpsCuspHeckeLinearMap N p hNp) P) (b j) =
      P.eval (eigenvalue j:ℂ) • b j :=
    Module.End.aeval_apply_of_mem_apply_eq_smul (hb j)
  have hf : (aeval (lpsCuspHeckeLinearMap N p hNp) P) f =
      ∑j,(b.repr f j*P.eval (eigenvalue j:ℂ)) • b j := by
    calc
      _ = (aeval (lpsCuspHeckeLinearMap N p hNp) P) (∑j,b.repr f j • b j) := by rw [b.sum_repr]
      _ = ∑j,b.repr f j • (aeval (lpsCuspHeckeLinearMap N p hNp) P) (b j) := by
        rw [map_sum]; simp only [map_smul]
      _ = _ := by simp_rw [he,smul_smul]
  rw [hf]
  simp [map_sum,map_smul,Finset.sum_apply,smul_eq_mul,Finsupp.single_apply]

/-- The actual derived real spectrum on the active original theta support is algebraically integral. -/
lemma lpsTheta_exists_realIntegralEigenBasis (q p : ℕ) [Fact q.Prime] [Fact p.Prime]
    (hq4 : q%4=1) (hNp : p.Coprime ((4*q)^2)) :
    ∃b : Module.Basis (Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2))) ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2),
    ∃eigenvalue : Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2))→ℝ,
    (∀i,lpsCuspHeckeLinearMap ((4*q)^2) p hNp (b i)=(eigenvalue i:ℂ) • b i) ∧
    ∀i,b.repr (lpsThetaCuspidalRemainder q hq4) i≠0 → IsIntegral ℤ (eigenvalue i:ℂ) := by
  have hq : q≠0 := (Fact.out : q.Prime).ne_zero
  let : NeZero ((4*q)^2) := ⟨by positivity⟩
  obtain ⟨b,eigenvalue,hb⟩ := lpsCuspHecke_exists_realEigenBasis ((4*q)^2) p hNp
  obtain ⟨P,hP,hann⟩ := lpsTheta_exists_monic_originalHecke_annihilator q p hq4 hNp
  refine ⟨b,eigenvalue,hb,?_⟩
  intro i hi
  have hroot : (P.map (Int.castRingHom ℂ)).eval (eigenvalue i:ℂ)=0 := by
    have h := lpsCuspHecke_polynomial_repr ((4*q)^2) p hNp b eigenvalue hb
      (P.map (Int.castRingHom ℂ)) (lpsThetaCuspidalRemainder q hq4) i
    rw [hann,map_zero,Finsupp.zero_apply] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hi
  exact ⟨P,hP,by simpa only [Polynomial.eval_map, algebraMap_int_eq] using hroot⟩

/-- The ORIGINAL centered theta expansion has algebraic-integer eigenvalues on every active term. -/
lemma lpsThetaResidual_exists_realIntegralSpectralExpansion (p : ℕ) (a : LPSResiduePrime p) :
    ∃eigenvalue : Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 ((4*a.q)^2) : Subgroup (GL (Fin 2) ℝ)) 2))→ℝ,
    ∃c : Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 ((4*a.q)^2) : Subgroup (GL (Fin 2) ℝ)) 2))→ℂ,
    (∀i,c i≠0 → IsIntegral ℤ (eigenvalue i:ℂ)) ∧
    ∀n : ℕ,lpsCenteredThetaResidual a (2*n)=
      (Fintype.card PSL(2,ZMod a.q):ℝ)*
        (∑i,c i*(lpsHeckePolynomial ℂ (p:ℂ) (2*n)).eval (eigenvalue i:ℂ)).re+2*(-(p:ℝ))^n := by
  classical
  let : Fact p.Prime := ⟨a.degreePrime⟩
  let : NeZero ((4*a.q)^2) := ⟨pow_ne_zero _ (mul_ne_zero (by norm_num) a.prime.ne_zero)⟩
  have hNp : p.Coprime ((4*a.q)^2) := by
    convert a.coprime_thetaLevel using 1
    ring
  obtain ⟨b,eigenvalue,hb,hint⟩ := lpsTheta_exists_realIntegralEigenBasis a.q p a.modFour hNp
  let f := lpsThetaCuspidalRemainder a.q a.modFour
  refine ⟨eigenvalue,fun i => b.repr f i*PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (b i)),?_,?_⟩
  · intro i hi
    exact hint i (mul_ne_zero_iff.mp hi).1
  · intro n
    rw [lpsCenteredThetaResidual_even_eq_cuspidal_coefficient,
      lpsCuspHecke_coefficient_eigenBasis ((4*a.q)^2) p hNp b eigenvalue hb]
    congr 2
    apply congrArg Complex.re
    apply Finset.sum_congr rfl
    intro i _
    ring

end
end QEC.Coding.TannerLiftedProduct
