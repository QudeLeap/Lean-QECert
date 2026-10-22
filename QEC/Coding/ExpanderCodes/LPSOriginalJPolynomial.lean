import QEC.Coding.ExpanderCodes.LPSOriginalDilatedModularFunction
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Separation.Connected

/-!
# LPSOriginalJPolynomial

Every genuine level-one weight12m modular form has a unique bounded-degree
polynomial representation Delta^m P(j) in the SAME original j=E4^3/Delta.
Actual qconstant subtraction and the discriminant cusp-form equivalence prove
existence by induction; connected continuity and nonconstancy give an infinite
j image, hence a faithful evaluation ring hom and uniqueness.

The genuine translated Delta on original Gamma0(N) has actual value
N^11 Delta(Ntau) under pinned Mathlib's determinant-to-weight-minus1 slash.
For every positive integer N its genuine finite-coset norm is a nonzero
level-one weight12r form, where r is the actual finite coset cardinal. Its
unique polynomial coefficient in original j is nonzero.

This is an internal coefficient bridge for the original modular-equation
route, motivated by PK22 main.tex ex:Xpq and th:qLDPC. It neither constructs
that equation nor proves its integral minimality, rational normalization,
every-away-level good reduction, geometric Hecke/Frobenius/Weil estimate or
the public PK22 theorem. A nonzero polynomial gives a nonzero evaluated
FUNCTION, not pointwise nonvanishing. No generation or norm law is assumed.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

/-- Actual E4^(3m), transported to weight12m; its qconstant1 supplies the genuine cusp subtraction in the polynomial induction. -/
def lpsOriginalE4CubePower (m : ℕ) : ModularForm 𝒮ℒ (12*(m:ℤ)) :=
  ModularForm.mcast (by push_cast; ring) (ModularForm.E₄.pow (3*m))

/-- Exact pointwise E4-cube power recovery; used in the polynomial induction. -/
lemma lpsOriginalE4CubePower_apply (m : ℕ) (τ : ℍ) :
    lpsOriginalE4CubePower m τ=(ModularForm.E₄ τ^3)^m := by
  simp only [lpsOriginalE4CubePower,ModularForm.mcast_apply,
    ModularForm.coe_pow,Pi.pow_apply,pow_mul]

/-- The actual constant q coefficient is1; used to subtract the genuine constant term and obtain a cusp form. -/
lemma lpsOriginalE4CubePower_qconstant (m : ℕ) :
    (qExpansion 1 (lpsOriginalE4CubePower m)).coeff 0=1 := by
  have he : (qExpansion 1 ModularForm.E₄).coeff 0=1 :=
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3≤4) ⟨2,rfl⟩
  simp only [PowerSeries.coeff_zero_eq_constantCoeff] at he
  simp only [lpsOriginalE4CubePower,ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff,map_pow,he,one_pow]

/-- Actual nowhere-zero Delta cancels in Delta^m*j^m=(E4^3)^m; used to reconstruct the induction polynomial. -/
lemma lpsOriginalDelta_j_power (m : ℕ) (τ : ℍ) :
    ModularForm.discriminant τ^m*lpsOriginalJInvariant τ^m=(ModularForm.E₄ τ^3)^m := by
  rw [←mul_pow]
  congr 1
  rw [lpsOriginalJInvariant,mul_div_cancel₀ _ (ModularForm.discriminant_ne_zero τ)]

/-- Every genuine level-one weight12m modular form has a degree-at-most-m polynomial representation in the SAME original j; used by uniqueness and norm coefficient recovery. -/
lemma lpsOriginalLevelOne_polynomial_j (m : ℕ)
    (f : ModularForm 𝒮ℒ (12*(m:ℤ))) :
    ∃ P : Polynomial ℂ, P.natDegree≤m ∧ ∀ τ : ℍ,
      f τ=ModularForm.discriminant τ^m*P.eval (lpsOriginalJInvariant τ) := by
  induction m with
  | zero =>
    let g : ModularForm 𝒮ℒ 0 := ModularForm.mcast (by norm_num) f
    obtain ⟨c,hc⟩ := ModularFormClass.levelOne_weight_zero_const g
    refine ⟨Polynomial.C c,by simp,?_⟩
    intro τ
    have h := congr_fun hc τ
    simpa only [g,ModularForm.mcast_apply,Function.const_apply,pow_zero,
      Polynomial.eval_C,one_mul] using h
  | succ m ih =>
    let g := lpsOriginalE4CubePower (m+1)
    let c := (qExpansion 1 f).coeff 0
    obtain ⟨h,hh⟩ := ModularForm.sub_smul_isCuspForm f g
      (lpsOriginalE4CubePower_qconstant (m+1))
    let d : ModularForm 𝒮ℒ (12*(m:ℤ)) :=
      ModularForm.mcast (by push_cast; ring) (CuspForm.discriminantEquiv h)
    obtain ⟨P,hP,hPeval⟩ := ih d
    refine ⟨P+Polynomial.C c*Polynomial.X^(m+1),
      Polynomial.natDegree_add_le_of_degree_le (hP.trans (Nat.le_succ m))
        (Polynomial.natDegree_C_mul_X_pow_le c (m+1)),?_⟩
    intro τ
    have hΔ : ModularForm.discriminant τ*d τ=h τ :=
      ModularForm.discriminant_mul_discriminantEquiv_apply h τ
    have hv : h τ=f τ-c*g τ := congrArg (fun u : ModularForm 𝒮ℒ (12*((m+1:ℕ):ℤ)) => u τ) hh
    rw [hPeval τ] at hΔ
    have hg : g τ=(ModularForm.E₄ τ^3)^(m+1) :=
      lpsOriginalE4CubePower_apply (m+1) τ
    rw [hg] at hv
    rw [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_pow,Polynomial.eval_X]
    have hp := lpsOriginalDelta_j_power (m+1) τ
    rw [pow_succ] at hp ⊢
    linear_combination -hΔ-hv-c*hp


/-- Actual connected upper-half-plane continuity and proved nonconstancy give an infinite original j image; used for polynomial evaluation injectivity. -/
lemma lpsOriginalJInvariant_range_infinite :
    (Set.range lpsOriginalJInvariant).Infinite := by
  apply (isPreconnected_range lpsOriginalJInvariant_holomorphic.continuous).infinite_of_nontrivial
  by_contra h
  have hs : (Set.range lpsOriginalJInvariant).Subsingleton := Set.not_nontrivial_iff.mp h
  apply lpsOriginalJInvariant_nonconstant
  exact ⟨lpsOriginalJInvariant UpperHalfPlane.I,fun τ => hs ⟨τ,rfl⟩ ⟨UpperHalfPlane.I,rfl⟩⟩

/-- Actual polynomial evaluation ring hom into original upper-half-plane functions; used for injection, nonzero-function control and uniqueness. -/
def lpsOriginalJPolynomialEvalHom : Polynomial ℂ →+* (ℍ→ℂ) :=
  RingHom.pi (fun τ => Polynomial.evalRingHom (lpsOriginalJInvariant τ))

/-- Literal actual ring-hom evaluation formula; used by the root fixture. -/
lemma lpsOriginalJPolynomialEvalHom_apply (P : Polynomial ℂ) (τ : ℍ) :
    lpsOriginalJPolynomialEvalHom P τ=P.eval (lpsOriginalJInvariant τ) := rfl

/-- Equality on the actual infinite original j image proves polynomial equality; used by nonzero-function control and uniqueness. -/
lemma lpsOriginalJPolynomialEvalHom_injective :
    Function.Injective lpsOriginalJPolynomialEvalHom := by
  intro P Q h
  apply Polynomial.eq_of_infinite_eval_eq
  apply lpsOriginalJInvariant_range_infinite.mono
  rintro z ⟨τ,rfl⟩
  exact congr_fun h τ

/-- Nonzero polynomial gives a nonzero evaluated FUNCTION, without claiming it is nowhere zero; used by the root fixture. -/
lemma lpsOriginalJPolynomialEvalHom_nonzero (P : Polynomial ℂ) (hP : P≠0) :
    lpsOriginalJPolynomialEvalHom P≠0 := by
  intro h
  apply hP
  apply lpsOriginalJPolynomialEvalHom_injective
  simpa only [map_zero] using h

/-- The bounded-degree polynomial representation of any genuine level-one weight12m form is unique; used by the actual dilated-Delta norm polynomial. -/
lemma lpsOriginalLevelOne_unique_polynomial_j (m : ℕ)
    (f : ModularForm 𝒮ℒ (12*(m:ℤ))) :
    ∃! P : Polynomial ℂ, P.natDegree≤m ∧ ∀ τ : ℍ,
      f τ=ModularForm.discriminant τ^m*P.eval (lpsOriginalJInvariant τ) := by
  obtain ⟨P,hP,hPeval⟩ := lpsOriginalLevelOne_polynomial_j m f
  refine ⟨P,⟨hP,hPeval⟩,?_⟩
  intro Q hQ
  apply lpsOriginalJPolynomialEvalHom_injective
  funext τ
  apply mul_left_cancel₀ (pow_ne_zero m (ModularForm.discriminant_ne_zero τ))
  exact (hQ.2 τ).symm.trans (hPeval τ)


/-- Actual translated Delta restricted to the original Gamma0(N) using proved subgroup inclusion and genuine cusp boundedness; used by its literal formula and norm. -/
def lpsOriginalDeltaDilatedForm (N : ℕ) (hN : 0<N) :
    ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 12 :=
  let f := CuspForm.translate CuspForm.discriminant (lpsE2AffineMatrix N hN 0)
  { toFun := f
    slash_action_eq' g hg := f.slash_action_eq' g
      (lpsOriginalJDilation_Gamma0_le_translated_SL N hN hg)
    holo' := f.holo'
    bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f
      (hc.mono (lpsOriginalJDilation_Gamma0_le_translated_SL N hN)) }

/-- Pinned Mathlib weight12 slash gives N^11*Delta(Ntau); used to prove the actual form nonzero. -/
lemma lpsOriginalDeltaDilatedForm_apply (N : ℕ) (hN : 0<N) (τ : ℍ) :
    lpsOriginalDeltaDilatedForm N hN τ=(N:ℂ)^11*
      ModularForm.discriminant (lpsE2AffineMatrix N hN 0•τ) := by
  change ((CuspForm.discriminant:ℍ→ℂ) ∣[(12:ℤ)] lpsE2AffineMatrix N hN 0) τ=_
  simp [ModularForm.slash_apply,UpperHalfPlane.σ,hN,UpperHalfPlane.denom,
    lpsE2AffineMatrix_coe,Matrix.of_apply,mul_comm]

/-- Positive N and actual nowhere-zero Delta prove the original dilated form is a nonzero FUNCTION; used by genuine norm nonvanishing. -/
lemma lpsOriginalDeltaDilatedForm_nonzero (N : ℕ) (hN : 0<N) :
    (lpsOriginalDeltaDilatedForm N hN:ℍ→ℂ)≠0 := by
  intro h
  have hv := congr_fun h UpperHalfPlane.I
  have hn : (N:ℂ)≠0 := by exact_mod_cast hN.ne'
  have hne : lpsOriginalDeltaDilatedForm N hN UpperHalfPlane.I≠0 := by
    rw [lpsOriginalDeltaDilatedForm_apply]
    exact mul_ne_zero (pow_ne_zero 11 hn) (ModularForm.discriminant_ne_zero _)
  exact hne (by simpa only [Pi.zero_apply] using hv)

/-- Genuine Mathlib finite-coset norm to levelSL, with weight12 times actual coset cardinal; used by norm nonvanishing and polynomial recovery. -/
def lpsOriginalDeltaDilatedNorm (N : ℕ) [NeZero N] (hN : 0<N) :
    ModularForm 𝒮ℒ (12*(Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ):ℤ)) :=
  ModularForm.norm 𝒮ℒ (lpsOriginalDeltaDilatedForm N hN)

/-- Actual norm_ne_zero proves the genuine norm is a nonzero form; used to exclude the zero recovered polynomial. -/
lemma lpsOriginalDeltaDilatedNorm_nonzero (N : ℕ) [NeZero N] (hN : 0<N) :
    lpsOriginalDeltaDilatedNorm N hN≠0 :=
  ModularForm.norm_ne_zero 𝒮ℒ (lpsOriginalDeltaDilatedForm_nonzero N hN)

/-- The genuine original dilated-Delta norm has a UNIQUE polynomial in SAME j of degree at most the actual coset cardinal; used to obtain a nonzero polynomial. -/
lemma lpsOriginalDeltaDilatedNorm_unique_polynomial (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃! P : Polynomial ℂ,
      P.natDegree≤Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      ∀ τ : ℍ, lpsOriginalDeltaDilatedNorm N hN τ=
        ModularForm.discriminant τ^(Nat.card (𝒮ℒ ⧸
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))*
          P.eval (lpsOriginalJInvariant τ) :=
  lpsOriginalLevelOne_unique_polynomial_j _ (lpsOriginalDeltaDilatedNorm N hN)

/-- Actual nonzero norm excludes a zero recovered polynomial; this supplies the genuine denominator coefficient bridge for the forthcoming original modular equation. -/
lemma lpsOriginalDeltaDilatedNorm_polynomial_nonzero (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃ P : Polynomial ℂ, P≠0 ∧
      P.natDegree≤Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      ∀ τ : ℍ, lpsOriginalDeltaDilatedNorm N hN τ=
        ModularForm.discriminant τ^(Nat.card (𝒮ℒ ⧸
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))*
          P.eval (lpsOriginalJInvariant τ) := by
  obtain ⟨P,⟨hP,hPeval⟩,_⟩ := lpsOriginalDeltaDilatedNorm_unique_polynomial N hN
  refine ⟨P,?_,hP,hPeval⟩
  intro hzero
  apply lpsOriginalDeltaDilatedNorm_nonzero N hN
  ext τ
  rw [hPeval τ,hzero,Polynomial.eval_zero,mul_zero]
  rfl

end
end QEC.Coding.TannerLiftedProduct
