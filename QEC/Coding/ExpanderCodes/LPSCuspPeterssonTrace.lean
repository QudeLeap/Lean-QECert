import QEC.Coding.ExpanderCodes.LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold

/-!
# LPSCuspPeterssonTrace

Actual quotient-indexed slash components, their induced permutation covariance,
and the invariant finite-coset Petersson trace. All-cusp bounds and true
exponential decay prove absolute convergence, including every complex height
power in the self-density. The integrated pairing is genuinely Hermitian and
sesquilinear. No coefficient-growth estimate, square-series continuation or
functional equation is asserted.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate

noncomputable section
/-- Gamma0 invariance of the actual weight-two Petersson integrand. -/
lemma lpsCuspPetersson_smul (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (j : SL(2,ℤ)) (hj : j∈CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    petersson 2 f g (j • τ)=petersson 2 f g τ := by
  have hj' : Matrix.SpecialLinearGroup.mapGL ℝ j ∈
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) hj
  have hcast : Matrix.SpecialLinearGroup.mapGL ℝ j=(j:GL (Fin 2) ℝ) := by
    ext i k
    rfl
  rw [hcast] at hj'
  simpa only [ModularGroup.sl_moeb] using
    (SlashInvariantFormClass.petersson_smul (f:=f) (f':=g) (τ:=τ) hj')

/-- The actual Petersson integrand indexed by a left coset, independent of its representative. -/
def lpsCuspCosetPetersson (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ :=
  Quotient.lift (fun h : SL(2,ℤ) => petersson 2 f g (h⁻¹ • τ)) fun h j hhj => by
    obtain ⟨l,hl,hl'⟩ : ∃l∈CongruenceSubgroup.Gamma0 N, j=h*l := by
      rw [← Quotient.eq_iff_equiv,Quotient.eq,QuotientGroup.leftRel_apply] at hhj
      exact ⟨h⁻¹*j,hhj,(mul_inv_cancel_left h j).symm⟩
    simp [-ModularGroup.sl_moeb,hl',mul_smul,lpsCuspPetersson_smul N f g l⁻¹ (inv_mem hl)]

/-- Every actual coset Petersson component is continuous. -/
lemma lpsCuspCosetPetersson_continuous (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    Continuous (fun τ => lpsCuspCosetPetersson N f g τ γ) := by
  refine QuotientGroup.induction_on γ (fun h => ?_)
  change Continuous (fun τ => petersson 2 f g (h⁻¹ • τ))
  apply (petersson_continuous 2 (by fun_prop) (by fun_prop)).comp
  change Continuous (fun τ : ℍ => h⁻¹ • τ)
  simpa only [ModularGroup.sl_moeb] using
    (show Continuous (fun τ : ℍ => ((h⁻¹ : SL(2,ℤ)) : GL (Fin 2) ℝ) • τ) from continuous_const_smul _)

/-- Simultaneous modular action on the point and coset preserves the actual integrand. -/
lemma lpsCuspCosetPetersson_covariant (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (h : SL(2,ℤ)) (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    lpsCuspCosetPetersson N f g (h • τ) (h • γ)=lpsCuspCosetPetersson N f g τ γ := by
  induction γ using QuotientGroup.induction_on
  simp [-ModularGroup.sl_moeb,lpsCuspCosetPetersson,mul_smul]

/-- The finite-coset trace of the actual Petersson integrand. -/
def lpsCuspPeterssonTrace (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) : ℂ :=
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  ∑ γ, lpsCuspCosetPetersson N f g τ γ

/-- The actual finite-coset Petersson trace is continuous. -/
lemma lpsCuspPeterssonTrace_continuous (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    Continuous (lpsCuspPeterssonTrace N f g) := by
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  exact continuous_finsetSum _ (fun γ _ => lpsCuspCosetPetersson_continuous N f g γ)

/-- The actual coset trace is invariant under the whole modular group. -/
lemma lpsCuspPeterssonTrace_invariant (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : SL(2,ℤ)) (τ : ℍ) :
    lpsCuspPeterssonTrace N f g (h • τ)=lpsCuspPeterssonTrace N f g τ := by
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  exact (Fintype.sum_equiv (MulAction.toPerm h) _ _
    (fun γ => (lpsCuspCosetPetersson_covariant N f g τ h γ).symm)).symm

/-- The actual coset trace is uniformly bounded by the genuine all-cusp bounds. -/
lemma lpsCuspPeterssonTrace_bounded (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ∃C,∀τ,‖lpsCuspPeterssonTrace N f g τ‖≤C := by
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  obtain ⟨C,hC⟩ := CuspFormClass.petersson_bounded_left 2 _ f g
  refine ⟨(Fintype.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ)*C,fun τ => ?_⟩
  calc
    ‖lpsCuspPeterssonTrace N f g τ‖ ≤ ∑γ,‖lpsCuspCosetPetersson N f g τ γ‖ := norm_sum_le _ _
    _ ≤ ∑_γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N, C := by
      apply Finset.sum_le_sum
      intro γ hγ
      induction γ using QuotientGroup.induction_on
      exact hC _
    _ = _ := by simp

/-- The actual finite-coset Petersson trace has an absolutely convergent integral. -/
lemma lpsCuspPeterssonTrace_integrable (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    IntegrableOn (lpsCuspPeterssonTrace N f g) ModularGroup.fd := by
  obtain ⟨C,hC⟩ := lpsCuspPeterssonTrace_bounded N f g
  have hi : IntegrableOn (fun _ : ℍ => C) ModularGroup.fd :=
    integrableOn_const (ne_of_lt lpsPetersson_fundamentalDomain_volume_finite)
  exact hi.mono' (lpsCuspPeterssonTrace_continuous N f g).aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

/-- The weight-two self-integrand is the actual squared norm times height squared. -/
lemma lpsWeightTwoPetersson_self (f : ℍ → ℂ) (τ : ℍ) :
    petersson 2 f f τ = ((‖f τ‖^2*τ.im^2:ℝ):ℂ) := by
  rw [petersson, ← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  simp

/-- Evaluation at a representative gives the actual transformed Petersson integrand. -/
lemma lpsCuspCosetPetersson_apply (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (h : SL(2,ℤ)) :
    lpsCuspCosetPetersson N f g τ ⟦h⟧=petersson 2 f g (h⁻¹ • τ) := rfl

/-- The actual self-component is height squared times the squared norm of the slash transform. -/
lemma lpsCuspCosetPetersson_slash_self (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (h : SL(2,ℤ)) :
    lpsCuspCosetPetersson N f f τ ⟦h⟧=
      ((‖((f:ℍ→ℂ) ∣[(2:ℤ)] h⁻¹) τ‖^2*τ.im^2:ℝ):ℂ) := by
  rw [lpsCuspCosetPetersson_apply, ← petersson_slash_SL,lpsWeightTwoPetersson_self]

/-- Every actual self-component has nonnegative real part. -/
lemma lpsCuspCosetPetersson_self_nonneg (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    0≤(lpsCuspCosetPetersson N f f τ γ).re := by
  refine QuotientGroup.induction_on γ (fun h => ?_)
  rw [lpsCuspCosetPetersson_slash_self]
  simp only [Complex.ofReal_re]
  positivity

/-- Every actual self-component is real. -/
lemma lpsCuspCosetPetersson_self_im_zero (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    (lpsCuspCosetPetersson N f f τ γ).im=0 := by
  refine QuotientGroup.induction_on γ (fun h => ?_)
  rw [lpsCuspCosetPetersson_slash_self]
  exact Complex.ofReal_im _

/-- The real finite-coset square density of the actual cusp form. -/
def lpsCuspPeterssonDensity (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) : ℝ := (lpsCuspPeterssonTrace N f f τ).re

/-- The actual finite-coset square density is nonnegative. -/
lemma lpsCuspPeterssonDensity_nonneg (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) : 0≤lpsCuspPeterssonDensity N f τ := by
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  simp only [lpsCuspPeterssonDensity,lpsCuspPeterssonTrace,Complex.re_sum]
  exact Finset.sum_nonneg (fun γ _ => lpsCuspCosetPetersson_self_nonneg N f τ γ)

/-- The actual self-trace equals the complex inclusion of its real square density. -/
lemma lpsCuspPeterssonDensity_ofReal (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) : (lpsCuspPeterssonDensity N f τ:ℂ)=lpsCuspPeterssonTrace N f f τ := by
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  apply Complex.ext
  · rfl
  · simp [lpsCuspPeterssonTrace,Complex.im_sum,lpsCuspCosetPetersson_self_im_zero]

/-- The actual untransformed cusp form contributes to the finite-coset square density. -/
lemma lpsCuspPeterssonDensity_individual_le (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) : ‖f τ‖^2*τ.im^2≤lpsCuspPeterssonDensity N f τ := by
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  have h := Finset.univ.single_le_sum
    (fun γ _ => lpsCuspCosetPetersson_self_nonneg N f τ γ)
    (Finset.mem_univ (⟦(1:SL(2,ℤ))⟧ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N))
  have ht : (lpsCuspCosetPetersson N f f τ ⟦(1:SL(2,ℤ))⟧).re=‖f τ‖^2*τ.im^2 := by
    rw [lpsCuspCosetPetersson_apply]
    simp only [inv_one,one_smul,lpsWeightTwoPetersson_self,Complex.ofReal_re]
  rw [ht] at h
  simpa only [lpsCuspPeterssonDensity,lpsCuspPeterssonTrace,Complex.re_sum] using h

/-- The actual finite-coset square density is continuous. -/
lemma lpsCuspPeterssonDensity_continuous (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    Continuous (lpsCuspPeterssonDensity N f) :=
  Complex.continuous_re.comp (lpsCuspPeterssonTrace_continuous N f f)

/-- The actual square density is invariant under the whole modular group. -/
lemma lpsCuspPeterssonDensity_invariant (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : SL(2,ℤ)) (τ : ℍ) :
    lpsCuspPeterssonDensity N f (h • τ)=lpsCuspPeterssonDensity N f τ := by
  exact congrArg Complex.re (lpsCuspPeterssonTrace_invariant N f f h τ)

/-- The actual square density is integrable with the genuine hyperbolic measure. -/
lemma lpsCuspPeterssonDensity_integrable (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    IntegrableOn (lpsCuspPeterssonDensity N f) ModularGroup.fd :=
  Complex.reCLM.integrable_comp (lpsCuspPeterssonTrace_integrable N f f)

/-- The convergent finite-coset Petersson integral on the standard fundamental domain. -/
def lpsCuspPeterssonPairing (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) : ℂ :=
  ∫τ in ModularGroup.fd, lpsCuspPeterssonTrace N f g τ

/-- The actual self-pairing is the integral of the nonnegative real square density. -/
lemma lpsCuspPeterssonPairing_self_eq (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N f f=(∫τ in ModularGroup.fd,lpsCuspPeterssonDensity N f τ : ℝ) := by
  unfold lpsCuspPeterssonPairing
  simp_rw [← lpsCuspPeterssonDensity_ofReal]
  exact integral_ofReal

/-- The actual convergent self-pairing is nonnegative. -/
lemma lpsCuspPeterssonPairing_self_nonneg (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    0≤(lpsCuspPeterssonPairing N f f).re := by
  rw [lpsCuspPeterssonPairing_self_eq,Complex.ofReal_re]
  exact integral_nonneg (lpsCuspPeterssonDensity_nonneg N f)

open ConjAct Pointwise in
/-- Every actual coset component decays exponentially, using the translated cusp form. -/
lemma lpsCuspCosetPetersson_exp_decay (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    ∃a>0,(fun τ => lpsCuspCosetPetersson N f g τ γ)=O[atImInfty]
      (fun τ => Real.exp (-a*τ.im)) := by
  refine QuotientGroup.induction_on γ (fun h => ?_)
  let Γ : Subgroup (GL (Fin 2) ℝ) := CongruenceSubgroup.Gamma0 N
  have hcast : Matrix.SpecialLinearGroup.mapGL ℝ h=(h:GL (Fin 2) ℝ) := by
    ext i k
    rfl
  have : ((toConjAct (((h⁻¹ : SL(2,ℤ)) : GL (Fin 2) ℝ)⁻¹)) • Γ).IsArithmetic := by
    simpa [Γ,(show Rat.castHom ℝ=algebraMap ℚ ℝ by rfl),map_inv,Matrix.SpecialLinearGroup.map_mapGL,hcast]
      using Subgroup.IsArithmetic.conj Γ (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)⁻¹
  obtain ⟨a,ha,hb⟩ := (CuspFormClass.zero_at_infty (CuspForm.translate f (((h⁻¹ : SL(2,ℤ)) : GL (Fin 2) ℝ)))).petersson_exp_decay_left
    2 _ (CuspForm.translate g (((h⁻¹ : SL(2,ℤ)) : GL (Fin 2) ℝ)))
  refine ⟨a,ha,?_⟩
  change (petersson 2 ((f:ℍ→ℂ) ∣[(2:ℤ)] h⁻¹) ((g:ℍ→ℂ) ∣[(2:ℤ)] h⁻¹))=O[atImInfty]
    (fun τ => Real.exp (-a*τ.im)) at hb
  have he : petersson 2 ((f:ℍ→ℂ) ∣[(2:ℤ)] h⁻¹) ((g:ℍ→ℂ) ∣[(2:ℤ)] h⁻¹)=
      (fun τ => lpsCuspCosetPetersson N f g τ ⟦h⟧) := by
    funext τ
    exact petersson_slash_SL 2 f g h⁻¹ τ
  rw [he] at hb
  exact hb

/-- The finite actual coset trace decays exponentially with a common positive exponent. -/
lemma lpsCuspPeterssonTrace_exp_decay (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ∃a>0,lpsCuspPeterssonTrace N f g=O[atImInfty] (fun τ => Real.exp (-a*τ.im)) := by
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  choose a ha hb using lpsCuspCosetPetersson_exp_decay N f g
  have hne : (Finset.univ : Finset (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)).Nonempty :=
    ⟨⟦(1:SL(2,ℤ))⟧,Finset.mem_univ _⟩
  let b : ℝ := Finset.univ.inf' hne a
  have hpos : 0<b := by
    obtain ⟨γ,hγ,hmin⟩ := Finset.exists_mem_eq_inf' hne a
    change 0<Finset.univ.inf' hne a
    rw [hmin]
    exact ha γ
  have hba (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : b≤a γ :=
    Finset.inf'_le _ (Finset.mem_univ γ)
  refine ⟨b,hpos,?_⟩
  have hγ (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
      (fun τ => lpsCuspCosetPetersson N f g τ γ)=O[atImInfty] (fun τ => Real.exp (-b*τ.im)) := by
    apply (hb γ).trans
    apply isBigO_of_le
    intro τ
    rw [Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    nlinarith [hba γ,τ.im_pos]
  exact IsBigO.fun_sum (fun γ _ => hγ γ)

/-- The actual invariant square density decays exponentially at infinity. -/
lemma lpsCuspPeterssonDensity_exp_decay (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ∃a>0,lpsCuspPeterssonDensity N f=O[atImInfty] (fun τ => Real.exp (-a*τ.im)) := by
  obtain ⟨a,ha,hb⟩ := lpsCuspPeterssonTrace_exp_decay N f f
  refine ⟨a,ha,?_⟩
  have h : lpsCuspPeterssonDensity N f=O[atImInfty] lpsCuspPeterssonTrace N f f :=
    isBigO_of_le atImInfty (fun τ => by
      exact Complex.abs_re_le_norm _)
  exact h.trans hb

/-- The actual coset Petersson component is Hermitian. -/
lemma lpsCuspCosetPetersson_conj (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    lpsCuspCosetPetersson N g f τ γ=conj (lpsCuspCosetPetersson N f g τ γ) := by
  refine QuotientGroup.induction_on γ (fun h => ?_)
  exact petersson_symm 2 f g (h⁻¹ • τ)

/-- The actual finite-coset trace is Hermitian. -/
lemma lpsCuspPeterssonTrace_conj (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) : lpsCuspPeterssonTrace N g f τ=conj (lpsCuspPeterssonTrace N f g τ) := by
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  change (∑γ,lpsCuspCosetPetersson N g f τ γ)=conj (∑γ,lpsCuspCosetPetersson N f g τ γ)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  exact lpsCuspCosetPetersson_conj N f g τ γ

/-- The genuine convergent finite-coset integral is Hermitian. -/
lemma lpsCuspPeterssonPairing_conj (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N g f=conj (lpsCuspPeterssonPairing N f g) := by
  unfold lpsCuspPeterssonPairing
  calc
    _ = ∫τ in ModularGroup.fd,conj (lpsCuspPeterssonTrace N f g τ) :=
      integral_congr_ae (Filter.Eventually.of_forall (lpsCuspPeterssonTrace_conj N f g))
    _ = _ := integral_conj

/-- The actual coset integrand is additive in its second cusp form. -/
lemma lpsCuspCosetPetersson_add_right (N : ℕ)
    (f g h : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    lpsCuspCosetPetersson N f (g+h) τ γ=
      lpsCuspCosetPetersson N f g τ γ+lpsCuspCosetPetersson N f h τ γ := by
  refine QuotientGroup.induction_on γ (fun j => ?_)
  simp [lpsCuspCosetPetersson_apply,petersson,mul_add,add_mul]

/-- The actual finite-coset trace is additive in its second cusp form. -/
lemma lpsCuspPeterssonTrace_add_right (N : ℕ) [NeZero N]
    (f g h : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) : lpsCuspPeterssonTrace N f (g+h) τ=
      lpsCuspPeterssonTrace N f g τ+lpsCuspPeterssonTrace N f h τ := by
  simp [lpsCuspPeterssonTrace,lpsCuspCosetPetersson_add_right,Finset.sum_add_distrib]

/-- Absolute convergence gives additivity of the actual integral in its second argument. -/
lemma lpsCuspPeterssonPairing_add_right (N : ℕ) [NeZero N]
    (f g h : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N f (g+h)=
      lpsCuspPeterssonPairing N f g+lpsCuspPeterssonPairing N f h := by
  simp only [lpsCuspPeterssonPairing,lpsCuspPeterssonTrace_add_right]
  exact integral_add (lpsCuspPeterssonTrace_integrable N f g) (lpsCuspPeterssonTrace_integrable N f h)

/-- The actual coset integrand is complex linear in its second cusp form. -/
lemma lpsCuspCosetPetersson_smul_right (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (c : ℂ) (τ : ℍ) (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    lpsCuspCosetPetersson N f (c • g) τ γ=c*lpsCuspCosetPetersson N f g τ γ := by
  refine QuotientGroup.induction_on γ (fun j => ?_)
  simp only [lpsCuspCosetPetersson_apply,petersson,smul_apply,smul_eq_mul]
  ring

/-- The actual finite-coset trace is complex linear in its second cusp form. -/
lemma lpsCuspPeterssonTrace_smul_right (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (c : ℂ) (τ : ℍ) : lpsCuspPeterssonTrace N f (c • g) τ=c*lpsCuspPeterssonTrace N f g τ := by
  simp [lpsCuspPeterssonTrace,lpsCuspCosetPetersson_smul_right,Finset.mul_sum]

/-- The actual convergent integral is complex linear in its second argument. -/
lemma lpsCuspPeterssonPairing_smul_right (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (c : ℂ) : lpsCuspPeterssonPairing N f (c • g)=c*lpsCuspPeterssonPairing N f g := by
  simp only [lpsCuspPeterssonPairing,lpsCuspPeterssonTrace_smul_right]
  exact integral_const_mul _ _

/-- Every real height power times the actual square density is bounded at infinity. -/
lemma lpsCuspPeterssonDensity_rpow_isBigO (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (s : ℝ) : (fun τ => lpsCuspPeterssonDensity N f τ*τ.im^s)=O[atImInfty]
      (fun _ => (1:ℝ)) := by
  obtain ⟨a,ha,hb⟩ := lpsCuspPeterssonDensity_exp_decay N f
  have hexp : (fun τ : ℍ => Real.exp (-a*τ.im)*τ.im^s)=O[atImInfty]
      (fun _ => (1:ℝ)) := by
    have h := (isLittleO_exp_mul_rpow_of_lt s (show -a<(0:ℝ) by linarith)).isBigO
    simpa only [zero_mul,Real.exp_zero,Function.comp_def,atImInfty] using h.comp_tendsto (tendsto_comap :
      Tendsto UpperHalfPlane.im atImInfty atTop)
  exact (hb.mul (isBigO_refl (fun τ : ℍ => τ.im^s) atImInfty)).trans hexp

/-- Every real height power times the actual square density is integrable on the fundamental domain. -/
lemma lpsCuspPeterssonDensity_rpow_integrable (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (s : ℝ) : IntegrableOn (fun τ => lpsCuspPeterssonDensity N f τ*τ.im^s) ModularGroup.fd := by
  have hc : Continuous (fun τ : ℍ => lpsCuspPeterssonDensity N f τ*τ.im^s) :=
    (lpsCuspPeterssonDensity_continuous N f).mul
      (continuous_im.rpow_const (fun τ => Or.inl τ.im_ne_zero))
  have hO : (fun τ : ℍ => lpsCuspPeterssonDensity N f τ*τ.im^s)=O[atImInfty]
      (fun τ => τ.im^(0:ℝ)) := by
    simpa using lpsCuspPeterssonDensity_rpow_isBigO N f s
  obtain ⟨C,hC⟩ := ModularGroup.exists_bound_fundamental_domain_of_isBigO hc hO
  have hi : IntegrableOn (fun _ : ℍ => C) ModularGroup.fd :=
    integrableOn_const (ne_of_lt lpsPetersson_fundamentalDomain_volume_finite)
  refine hi.mono' hc.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with τ hτ
  simpa only [Real.rpow_zero,mul_one] using hC τ hτ

/-- Every complex height power times the actual square density is integrable on the fundamental domain. -/
lemma lpsCuspPeterssonDensity_cpow_integrable (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (s : ℂ) : IntegrableOn (fun τ : ℍ => (lpsCuspPeterssonDensity N f τ:ℂ)*(τ.im:ℂ)^s)
      ModularGroup.fd := by
  have hi := lpsCuspPeterssonDensity_rpow_integrable N f s.re
  refine hi.mono' ?_ ?_
  · have hc : Continuous (fun τ : ℍ => (lpsCuspPeterssonDensity N f τ:ℂ)*(τ.im:ℂ)^s) := by
      apply Continuous.mul
      · exact Complex.continuous_ofReal.comp (lpsCuspPeterssonDensity_continuous N f)
      · apply continuous_iff_continuousAt.mpr
        intro τ
        exact (Complex.continuousAt_ofReal_cpow_const τ.im s (Or.inr τ.im_ne_zero)).comp
          continuous_im.continuousAt
    exact hc.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun τ => by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (lpsCuspPeterssonDensity_nonneg N f τ),
        Complex.norm_cpow_eq_rpow_re_of_pos τ.im_pos])

/-- The genuine cusp form is fixed by slash transforms in Gamma0. -/
lemma lpsWeightTwoCusp_slash_gamma0 (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : SL(2,ℤ)) (hh : h∈CongruenceSubgroup.Gamma0 N) :
    (f:ℍ→ℂ) ∣[(2:ℤ)] h=f := by
  change (f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ h=f
  exact SlashInvariantFormClass.slash_action_eq f _
    (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) hh)

/-- The actual finite-index induced slash component, independent of representatives. -/
def lpsCuspCosetComponent (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N → (ℍ→ℂ) :=
  Quotient.lift (fun h : SL(2,ℤ) => (f:ℍ→ℂ) ∣[(2:ℤ)] h⁻¹) fun h j hhj => by
    obtain ⟨l,hl,hl'⟩ : ∃l∈CongruenceSubgroup.Gamma0 N, j=h*l := by
      rw [← Quotient.eq_iff_equiv,Quotient.eq,QuotientGroup.leftRel_apply] at hhj
      exact ⟨h⁻¹*j,hhj,(mul_inv_cancel_left h j).symm⟩
    rw [hl',mul_inv_rev,SlashAction.slash_mul,lpsWeightTwoCusp_slash_gamma0 N f l⁻¹ (inv_mem hl)]

/-- An actual induced component evaluates to the slash transform of its representative. -/
lemma lpsCuspCosetComponent_apply (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : SL(2,ℤ)) : lpsCuspCosetComponent N f ⟦h⟧=(f:ℍ→ℂ) ∣[(2:ℤ)] h⁻¹ := rfl

/-- Slash transformation permutes the actual induced cusp components. -/
lemma lpsCuspCosetComponent_slash_covariant (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : SL(2,ℤ)) (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    (lpsCuspCosetComponent N f (h • γ)) ∣[(2:ℤ)] h=lpsCuspCosetComponent N f γ := by
  refine QuotientGroup.induction_on γ (fun j => ?_)
  change ((f:ℍ→ℂ) ∣[(2:ℤ)] (h*j)⁻¹) ∣[(2:ℤ)] h=(f:ℍ→ℂ) ∣[(2:ℤ)] j⁻¹
  rw [← SlashAction.slash_mul]
  simp [mul_inv_rev,mul_assoc]

/-- The actual coset integrand is the Petersson product of the two induced components. -/
lemma lpsCuspCosetComponent_petersson (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    lpsCuspCosetPetersson N f g τ γ=
      petersson 2 (lpsCuspCosetComponent N f γ) (lpsCuspCosetComponent N g γ) τ := by
  refine QuotientGroup.induction_on γ (fun h => ?_)
  exact (petersson_slash_SL 2 f g h⁻¹ τ).symm

/-- The finite sum of squared norms of the actual induced cusp components. -/
def lpsCuspComponentSquareSum (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) : ℝ :=
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  ∑γ,‖lpsCuspCosetComponent N f γ τ‖^2

/-- The genuine invariant density is height squared times the actual component-square sum. -/
lemma lpsCuspPeterssonDensity_eq_component_squares (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) :
    lpsCuspPeterssonDensity N f τ=
      τ.im^2*lpsCuspComponentSquareSum N f τ := by
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  simp only [lpsCuspPeterssonDensity,lpsCuspPeterssonTrace,Complex.re_sum,lpsCuspComponentSquareSum]
  calc
    _ = ∑γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N, τ.im^2*‖lpsCuspCosetComponent N f γ τ‖^2 := by
      apply Finset.sum_congr rfl
      intro γ hγ
      rw [lpsCuspCosetComponent_petersson,lpsWeightTwoPetersson_self,Complex.ofReal_re,mul_comm]
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The actual convergent pairing is additive in its first argument. -/
lemma lpsCuspPeterssonPairing_add_left (N : ℕ) [NeZero N]
    (f g h : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N (f+g) h=
      lpsCuspPeterssonPairing N f h+lpsCuspPeterssonPairing N g h := by
  calc
    _ = conj (lpsCuspPeterssonPairing N h (f+g)) := lpsCuspPeterssonPairing_conj N h (f+g)
    _ = conj (lpsCuspPeterssonPairing N h f+lpsCuspPeterssonPairing N h g) := by
      rw [lpsCuspPeterssonPairing_add_right]
    _ = _ := by rw [map_add,← lpsCuspPeterssonPairing_conj,← lpsCuspPeterssonPairing_conj]

/-- The actual convergent pairing is conjugate linear in its first argument. -/
lemma lpsCuspPeterssonPairing_smul_left (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (c : ℂ) : lpsCuspPeterssonPairing N (c • f) g=conj c*lpsCuspPeterssonPairing N f g := by
  calc
    _ = conj (lpsCuspPeterssonPairing N g (c • f)) := lpsCuspPeterssonPairing_conj N g (c • f)
    _ = conj (c*lpsCuspPeterssonPairing N g f) := by rw [lpsCuspPeterssonPairing_smul_right]
    _ = _ := by rw [map_mul,← lpsCuspPeterssonPairing_conj]

end
end QEC.Coding.TannerLiftedProduct
