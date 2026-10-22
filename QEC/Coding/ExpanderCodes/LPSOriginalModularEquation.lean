import QEC.Coding.ExpanderCodes.LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange

/-!
# LPSOriginalModularEquation

For every positive integer N the SAME original j and jN satisfy one fixed
nonzero polynomial in C[X][Y]. The construction uses genuine translated E4
and Delta on original Gamma0(N), the determinant-squared numerator correction,
and the actual finite-coset Mathlib norm. Every complex sample c gives a
proved unique norm coefficient P_c(j). The literal quotientFunc coset product
has degree at most its actual cardinal r and its genuine identity factor
vanishes at original jN. Interpolation at r+1 distinct integer complex nodes
constructs one fixed equation: Delta(tau)^r times its specialization is that
actual coset product for every tau. Genuine norm nonvanishing proves the fixed
equation nonzero. No polynomial relation, norm law or presentation is assumed.

This internal bridge is motivated by PK22 main.tex ex:Xpq and th:qLDPC. It
covers composite original theta levels and proves a complex relation. Monic
normalization, integral minimality, rational descent, every-away-level smooth
proper reduction, geometric Hecke/Frobenius/Weil and the public PK22 theorem
remain subsequent mathematical work. Nonzero input/norm semantics concern
functions; the input at c=jN(tau) does vanish at that actual tau.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

/-- Actual translated E4 on original Gamma0(N), restricted using proved subgroup inclusion. -/
def lpsOriginalE4DilatedForm (N : ℕ) (hN : 0<N) :
    ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 4 :=
  let f := ModularForm.translate ModularForm.E₄ (lpsE2AffineMatrix N hN 0)
  { toFun := f
    slash_action_eq' g hg := f.slash_action_eq' g
      (lpsOriginalJDilation_Gamma0_le_translated_SL N hN hg)
    holo' := f.holo'
    bdd_at_cusps' hc := f.bdd_at_cusps'
      (hc.mono (lpsOriginalJDilation_Gamma0_le_translated_SL N hN)) }

/-- Literal pinned weight4 slash evaluation of the genuine translated E4. -/
lemma lpsOriginalE4DilatedForm_apply (N : ℕ) (hN : 0<N) (τ : ℍ) :
    lpsOriginalE4DilatedForm N hN τ=
      ((ModularForm.E₄:ℍ→ℂ) ∣[(4:ℤ)] lpsE2AffineMatrix N hN 0) τ := rfl

/-- Actual weight12 original jN numerator with determinant-squared N^2 correction. -/
def lpsOriginalJNumeratorForm (N : ℕ) (hN : 0<N) :
    ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 12 :=
  (N:ℂ)^2 • ModularForm.mcast (by norm_num) ((lpsOriginalE4DilatedForm N hN).pow 3)

/-- Literal cubic slash formula for the determinant-corrected original numerator. -/
lemma lpsOriginalJNumeratorForm_apply (N : ℕ) (hN : 0<N) (τ : ℍ) :
    lpsOriginalJNumeratorForm N hN τ=(N:ℂ)^2*
      (((ModularForm.E₄:ℍ→ℂ) ∣[(4:ℤ)] lpsE2AffineMatrix N hN 0) τ)^3 := by
  simp only [lpsOriginalJNumeratorForm,FunLike.coe_smul,Pi.smul_apply,
    smul_eq_mul,ModularForm.mcast_apply,ModularForm.coe_pow,Pi.pow_apply,
    lpsOriginalE4DilatedForm_apply]

/-- Actual dilated Delta is nowhere zero on every upper-half-plane point. -/
lemma lpsOriginalDeltaDilatedForm_ne_zero_apply (N : ℕ) (hN : 0<N) (τ : ℍ) :
    lpsOriginalDeltaDilatedForm N hN τ≠0 := by
  rw [lpsOriginalDeltaDilatedForm_apply]
  exact mul_ne_zero (pow_ne_zero 11 (by exact_mod_cast hN.ne'))
    (ModularForm.discriminant_ne_zero _)

/-- The ratio of genuine original numerator and dilated Delta equals the same original jN. -/
lemma lpsOriginalJNumeratorForm_ratio (N : ℕ) (hN : 0<N) (τ : ℍ) :
    lpsOriginalJNumeratorForm N hN τ/lpsOriginalDeltaDilatedForm N hN τ=
      lpsOriginalJDilated N hN τ := by
  have hM : 0<(lpsE2AffineMatrix N hN 0).det.val := by
    rw [lpsE2AffineMatrix_det]
    exact_mod_cast hN
  have h := lpsOriginalJInvariant_slash_ratio (lpsE2AffineMatrix N hN 0) hM τ
  rw [lpsE2AffineMatrix_det] at h
  rw [lpsOriginalJNumeratorForm_apply]
  exact h

/-- Actual numerator equals original dilated Delta times the same original jN. -/
lemma lpsOriginalJNumeratorForm_eq_delta_mul_j (N : ℕ) (hN : 0<N) (τ : ℍ) :
    lpsOriginalJNumeratorForm N hN τ=
      lpsOriginalDeltaDilatedForm N hN τ*lpsOriginalJDilated N hN τ := by
  have h := (div_eq_iff (lpsOriginalDeltaDilatedForm_ne_zero_apply N hN τ)).mp
    (lpsOriginalJNumeratorForm_ratio N hN τ)
  simpa only [mul_comm] using h

/-- Genuine weight12 form a_N-c*b_N for an arbitrary complex c. -/
def lpsOriginalModularNormInput (N : ℕ) (hN : 0<N) (c : ℂ) :
    ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 12 :=
  lpsOriginalJNumeratorForm N hN-c • lpsOriginalDeltaDilatedForm N hN

/-- Pointwise original norm input equals b_N*(jN-c). -/
lemma lpsOriginalModularNormInput_apply (N : ℕ) (hN : 0<N) (c : ℂ) (τ : ℍ) :
    lpsOriginalModularNormInput N hN c τ=
      lpsOriginalDeltaDilatedForm N hN τ*(lpsOriginalJDilated N hN τ-c) := by
  simp only [lpsOriginalModularNormInput,FunLike.coe_sub,Pi.sub_apply,
    FunLike.coe_smul,Pi.smul_apply,smul_eq_mul,
    lpsOriginalJNumeratorForm_eq_delta_mul_j]
  ring

/-- Actual original norm input is a nonzero function by proved jN nonconstancy. -/
lemma lpsOriginalModularNormInput_nonzero (N : ℕ) (hN : 0<N) (c : ℂ) :
    (lpsOriginalModularNormInput N hN c:ℍ→ℂ)≠0 := by
  intro h
  apply lpsOriginalJDilated_nonconstant N hN
  refine ⟨c,fun τ => ?_⟩
  have hv := congr_fun h τ
  rw [lpsOriginalModularNormInput_apply] at hv
  have hz : lpsOriginalJDilated N hN τ-c=0 :=
    (mul_eq_zero.mp hv).resolve_left (lpsOriginalDeltaDilatedForm_ne_zero_apply N hN τ)
  exact sub_eq_zero.mp hz

/-- Genuine finite-coset Mathlib norm of the original input, at weight12r. -/
def lpsOriginalModularNorm (N : ℕ) [NeZero N] (hN : 0<N) (c : ℂ) :
    ModularForm 𝒮ℒ (12*(Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ):ℤ)) :=
  ModularForm.norm 𝒮ℒ (lpsOriginalModularNormInput N hN c)

/-- Genuine original input norm is a nonzero modular form. -/
lemma lpsOriginalModularNorm_nonzero (N : ℕ) [NeZero N] (hN : 0<N) (c : ℂ) :
    lpsOriginalModularNorm N hN c≠0 :=
  ModularForm.norm_ne_zero 𝒮ℒ (lpsOriginalModularNormInput_nonzero N hN c)

/-- Unique degree-at-most-r original j coefficient polynomial of the actual input norm. -/
lemma lpsOriginalModularNorm_unique_polynomial (N : ℕ) [NeZero N] (hN : 0<N) (c : ℂ) :
    ∃! P : Polynomial ℂ,
      P.natDegree≤Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      ∀ τ : ℍ, lpsOriginalModularNorm N hN c τ=
        ModularForm.discriminant τ^(Nat.card (𝒮ℒ ⧸
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))*
          P.eval (lpsOriginalJInvariant τ) :=
  lpsOriginalLevelOne_unique_polynomial_j _ (lpsOriginalModularNorm N hN c)

/-- Actual nonzero original input norm has a nonzero coefficient polynomial. -/
lemma lpsOriginalModularNorm_polynomial_nonzero (N : ℕ) [NeZero N] (hN : 0<N) (c : ℂ) :
    ∃ P : Polynomial ℂ, P≠0 ∧
      P.natDegree≤Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      ∀ τ : ℍ, lpsOriginalModularNorm N hN c τ=
        ModularForm.discriminant τ^(Nat.card (𝒮ℒ ⧸
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))*
          P.eval (lpsOriginalJInvariant τ) := by
  obtain ⟨P,⟨hP,hPeval⟩,_⟩ := lpsOriginalModularNorm_unique_polynomial N hN c
  refine ⟨P,?_,hP,hPeval⟩
  intro hzero
  apply lpsOriginalModularNorm_nonzero N hN c
  ext τ
  rw [hPeval τ,hzero,Polynomial.eval_zero,mul_zero]
  rfl


/-- Actual quotientFunc linearity for the genuine numerator-minus-c-Delta input. -/
lemma lpsOriginalModularNormInput_quotient_apply (N : ℕ) (hN : 0<N) (c : ℂ)
    (q : 𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
    (τ : ℍ) :
    SlashInvariantForm.quotientFunc (lpsOriginalModularNormInput N hN c) q τ=
      SlashInvariantForm.quotientFunc (lpsOriginalJNumeratorForm N hN) q τ-
        c*SlashInvariantForm.quotientFunc (lpsOriginalDeltaDilatedForm N hN) q τ := by
  induction q using Quotient.inductionOn with
  | h g =>
    have hd : (g.val⁻¹).det=1 := Subgroup.HasDetOne.det_eq (inv_mem g.property)
    have hp : 0<(g.val⁻¹).det.val := by rw [hd]; norm_num
    simp only [SlashInvariantForm.quotientFunc_mk,lpsOriginalModularNormInput,
      FunLike.coe_sub,FunLike.coe_smul,ModularForm.slash_apply,Pi.sub_apply,
      Pi.smul_apply,smul_eq_mul,UpperHalfPlane.σ,if_pos hp,
      ContinuousAlgEquiv.refl_apply]
    ring

/-- Literal finite product of original quotient numerator-minus-Y-Delta factors. -/
def lpsOriginalModularCosetPolynomial (N : ℕ) [NeZero N] (hN : 0<N) (τ : ℍ) :
    Polynomial ℂ := by
  classical
  letI := Fintype.ofFinite (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  exact ∏ q : (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ),
    (Polynomial.C (SlashInvariantForm.quotientFunc (lpsOriginalJNumeratorForm N hN) q τ)-
      Polynomial.X*Polynomial.C
        (SlashInvariantForm.quotientFunc (lpsOriginalDeltaDilatedForm N hN) q τ))

/-- Evaluation of the literal coset product at every c equals the actual input norm. -/
lemma lpsOriginalModularCosetPolynomial_eval (N : ℕ) [NeZero N] (hN : 0<N)
    (τ : ℍ) (c : ℂ) :
    (lpsOriginalModularCosetPolynomial N hN τ).eval c=
      lpsOriginalModularNorm N hN c τ := by
  classical
  simp only [lpsOriginalModularCosetPolynomial,Polynomial.eval_prod,
    Polynomial.eval_sub,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X,
    lpsOriginalModularNorm,ModularForm.coe_norm,Finset.prod_apply,
    lpsOriginalModularNormInput_quotient_apply]

/-- The genuine identity-coset factor makes same original jN a root of the coset product. -/
lemma lpsOriginalModularCosetPolynomial_original_root (N : ℕ) [NeZero N] (hN : 0<N)
    (τ : ℍ) :
    (lpsOriginalModularCosetPolynomial N hN τ).eval (lpsOriginalJDilated N hN τ)=0 := by
  classical
  let := Fintype.ofFinite (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  rw [lpsOriginalModularCosetPolynomial_eval]
  simp only [lpsOriginalModularNorm,ModularForm.coe_norm,Finset.prod_apply]
  change (∏ q : (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ),
    SlashInvariantForm.quotientFunc
      (lpsOriginalModularNormInput N hN (lpsOriginalJDilated N hN τ)) q τ)=0
  apply Finset.prod_eq_zero (Finset.mem_univ (⟦(1:𝒮ℒ)⟧))
  simp [SlashInvariantForm.quotientFunc_mk,lpsOriginalModularNormInput_apply]

/-- Actual coset-product polynomial degree is at most its genuine finite coset cardinal. -/
lemma lpsOriginalModularCosetPolynomial_degree (N : ℕ) [NeZero N] (hN : 0<N)
    (τ : ℍ) :
    (lpsOriginalModularCosetPolynomial N hN τ).natDegree≤
      Nat.card (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
  classical
  let := Fintype.ofFinite (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  unfold lpsOriginalModularCosetPolynomial
  refine (Polynomial.natDegree_prod_le Finset.univ _).trans ?_
  calc
    _ ≤ ∑ _q : (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ),
      (1:ℕ) := by
        apply Finset.sum_le_sum
        intro q hq
        apply (Polynomial.natDegree_sub_le _ _).trans
        apply max_le
        · simp
        · exact Polynomial.natDegree_mul_le.trans (by simp)
    _ = _ := by simp [Nat.card_eq_fintype_card]


/-- Coefficient polynomial chosen from the already proved unique original norm representation. -/
def lpsOriginalModularNormCoefficient (N : ℕ) [NeZero N] (hN : 0<N) (c : ℂ) :
    Polynomial ℂ :=
  Classical.choose (lpsOriginalModularNorm_unique_polynomial N hN c).exists

/-- Actual coefficient polynomial has bounded degree and recovers the genuine norm at every tau. -/
lemma lpsOriginalModularNormCoefficient_spec (N : ℕ) [NeZero N] (hN : 0<N) (c : ℂ) :
    (lpsOriginalModularNormCoefficient N hN c).natDegree≤
      Nat.card (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      ∀ τ : ℍ, lpsOriginalModularNorm N hN c τ=
        ModularForm.discriminant τ^(Nat.card (𝒮ℒ ⧸
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))*
          (lpsOriginalModularNormCoefficient N hN c).eval (lpsOriginalJInvariant τ) :=
  Classical.choose_spec (lpsOriginalModularNorm_unique_polynomial N hN c).exists

/-- The r+1 integer complex interpolation nodes are pairwise distinct. -/
lemma lpsOriginalModularInterpolationNodes_injective (r : ℕ) :
    Function.Injective (fun i : Fin (r+1) => (i.val:ℂ)) := by
  intro i j h
  apply Fin.ext
  change (i.val:ℂ)=(j.val:ℂ) at h
  exact_mod_cast h

/-- Fixed original nested complex polynomial constructed from genuine norm coefficients and Lagrange bases. -/
def lpsOriginalModularEquationComplex (N : ℕ) [NeZero N] (hN : 0<N) :
    Polynomial (Polynomial ℂ) := by
  classical
  let r := Nat.card (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  exact ∑ i : Fin (r+1),
    Polynomial.C (lpsOriginalModularNormCoefficient N hN (i.val:ℂ))*
      (Lagrange.basis (Finset.univ:Finset (Fin (r+1))) (fun j => (j.val:ℂ)) i).map Polynomial.C

/-- Specializing the coefficient variable gives the actual Lagrange interpolant. -/
lemma lpsOriginalModularEquationComplex_map (N : ℕ) [NeZero N] (hN : 0<N) (x : ℂ) :
    (lpsOriginalModularEquationComplex N hN).map (Polynomial.evalRingHom x)=
      Lagrange.interpolate (Finset.univ:Finset (Fin ((Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))+1)))
        (fun i => (i.val:ℂ))
        (fun i => (lpsOriginalModularNormCoefficient N hN (i.val:ℂ)).eval x) := by
  classical
  have hc : (Polynomial.evalRingHom x).comp (Polynomial.C:ℂ→+*Polynomial ℂ)=RingHom.id ℂ := by
    ext z
    exact Polynomial.eval_C
  simp only [lpsOriginalModularEquationComplex,Polynomial.map_sum,
    Polynomial.map_mul,Polynomial.map_C,Polynomial.map_map,hc,Polynomial.map_id,
    Lagrange.interpolate_apply,Polynomial.coe_evalRingHom]

/-- Actual Delta^r times the fixed original equation specializes to the literal coset product. -/
lemma lpsOriginalModularEquationComplex_recovery (N : ℕ) [NeZero N] (hN : 0<N)
    (τ : ℍ) :
    Polynomial.C (ModularForm.discriminant τ^(Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)))*
      (lpsOriginalModularEquationComplex N hN).map
        (Polynomial.evalRingHom (lpsOriginalJInvariant τ))=
      lpsOriginalModularCosetPolynomial N hN τ := by
  classical
  let r := Nat.card (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  let d := ModularForm.discriminant τ^r
  rw [lpsOriginalModularEquationComplex_map]
  have hm : Polynomial.C d*Lagrange.interpolate (Finset.univ:Finset (Fin (r+1)))
      (fun i => (i.val:ℂ))
      (fun i => (lpsOriginalModularNormCoefficient N hN (i.val:ℂ)).eval
        (lpsOriginalJInvariant τ))=
      Lagrange.interpolate (Finset.univ:Finset (Fin (r+1))) (fun i => (i.val:ℂ))
        (fun i => d*(lpsOriginalModularNormCoefficient N hN (i.val:ℂ)).eval
          (lpsOriginalJInvariant τ)) := by
    simp only [Lagrange.interpolate_apply,Finset.mul_sum,Polynomial.C_mul,mul_assoc]
  rw [hm]
  symm
  apply Lagrange.eq_interpolate_of_eval_eq _
    (lpsOriginalModularInterpolationNodes_injective r).injOn
  · apply Polynomial.degree_le_natDegree.trans_lt
    have hh := Nat.lt_succ_of_le (lpsOriginalModularCosetPolynomial_degree N hN τ)
    simp only [Finset.card_univ,Fintype.card_fin]
    exact_mod_cast hh
  · intro i hi
    rw [lpsOriginalModularCosetPolynomial_eval]
    exact (lpsOriginalModularNormCoefficient_spec N hN (i.val:ℂ)).2 τ

/-- The fixed original complex equation vanishes on the same actual j and jN at every tau. -/
lemma lpsOriginalModularEquationComplex_original_root (N : ℕ) [NeZero N] (hN : 0<N)
    (τ : ℍ) :
    (lpsOriginalModularEquationComplex N hN).eval₂
      (Polynomial.evalRingHom (lpsOriginalJInvariant τ)) (lpsOriginalJDilated N hN τ)=0 := by
  have h := congrArg (fun P : Polynomial ℂ => P.eval (lpsOriginalJDilated N hN τ))
    (lpsOriginalModularEquationComplex_recovery N hN τ)
  rw [Polynomial.eval_mul,Polynomial.eval_C,
    lpsOriginalModularCosetPolynomial_original_root] at h
  rw [Polynomial.eval₂_eq_eval_map]
  exact (mul_eq_zero.mp h).resolve_left
    (pow_ne_zero _ (ModularForm.discriminant_ne_zero τ))

/-- The fixed original complex equation is nonzero by genuine norm nonvanishing. -/
lemma lpsOriginalModularEquationComplex_nonzero (N : ℕ) [NeZero N] (hN : 0<N) :
    lpsOriginalModularEquationComplex N hN≠0 := by
  intro hz
  apply lpsOriginalModularNorm_nonzero N hN 0
  ext τ
  have h := congrArg (fun P : Polynomial ℂ => P.eval 0)
    (lpsOriginalModularEquationComplex_recovery N hN τ)
  change lpsOriginalModularNorm N hN 0 τ=0
  simpa only [hz,Polynomial.map_zero,mul_zero,Polynomial.eval_zero,
    lpsOriginalModularCosetPolynomial_eval] using h.symm

/-- The same original j and jN satisfy a fixed nonzero complex polynomial relation for every positive level. -/
lemma lpsOriginalJ_jN_algebraic_relation (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃ Φ : Polynomial (Polynomial ℂ), Φ≠0 ∧ ∀ τ : ℍ,
      Φ.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
        (lpsOriginalJDilated N hN τ)=0 :=
  ⟨lpsOriginalModularEquationComplex N hN,
    lpsOriginalModularEquationComplex_nonzero N hN,
    lpsOriginalModularEquationComplex_original_root N hN⟩

end
end QEC.Coding.TannerLiftedProduct
