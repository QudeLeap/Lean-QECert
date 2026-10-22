import QEC.Coding.ExpanderCodes.LPSFourierPeriodChange
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Congruence Sturm and genuine finite-dimensional Hecke spaces

Internal proof closure for the original PK22 theta route. Fourier width, actual
coset norm and level-one Sturm give a finite coefficient injection at Gamma0(N).
The finite basis and matrices describe the already proved weight-two operators.
The arithmetic spectral bound and public theorem pk-good-qldpc remain unproved;
parent #449 remains open. No spectral or finite-dimensional conclusion is assumed.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

/-- Every integral coset translate at Gamma0(N) has the common strict period N. -/
lemma lpsGamma0Translate_integerPeriod (N : ℕ) (ρ : SL(2,ℤ)) :
    (N:ℝ)∈(ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ ρ)⁻¹ •
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff,ConjAct.toConjAct_inv,
    Subgroup.mem_inv_pointwise_smul_iff,ConjAct.toConjAct_smul]
  have ht : ModularGroup.T^(N:ℤ)∈CongruenceSubgroup.Gamma N := by
    simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N:ℤ) (N:ℤ) (dvd_refl _)
  have hc := (CongruenceSubgroup.Gamma_normal N).conj_mem _ ht ρ
  have hg : ρ*(ModularGroup.T^(N:ℤ))*ρ⁻¹∈CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma_mem] at hc
    rw [CongruenceSubgroup.Gamma0_mem]
    exact hc.2.2.1
  have he : Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T^(N:ℤ))=
      Matrix.GeneralLinearGroup.upperRightHom (N:ℝ) := by
    apply Units.ext
    change ((ModularGroup.T^(N:ℤ):SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.castRingHom ℝ)=_
    rw [ModularGroup.coe_T_zpow]
    ext r c
    fin_cases r <;> fin_cases c <;> simp
  have hmap := Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) hg
  simpa only [map_mul,map_inv,he] using hmap

/-- The actual cusp function of the constant one function is constant one. -/
lemma lpsCuspFunction_one (h : ℝ) : UpperHalfPlane.cuspFunction h (1:ℍ→ℂ)=1 := by
  ext q
  rcases eq_or_ne q 0 with rfl | hq
  · simpa [UpperHalfPlane.cuspFunction,Function.Periodic.cuspFunction] using!
      (tendsto_const_nhds : Tendsto (fun _ : ℂ => (1:ℂ)) (nhdsWithin 0 {0}ᶜ) (𝓝 1)).limUnder_eq
  · simp [UpperHalfPlane.cuspFunction,Function.Periodic.cuspFunction_eq_of_nonzero h _ hq]

/-- A finite product of actual cusp functions is analytic at zero when each factor is analytic. -/
lemma lpsCuspFunction_prod_analytic {ι : Type*} (h : ℝ) (s : Finset ι) (F : ι→ℍ→ℂ)
    (ha : ∀i∈s,AnalyticAt ℂ (UpperHalfPlane.cuspFunction h (F i)) 0) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction h (∏i∈s,F i)) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,lpsCuspFunction_one];exact analyticAt_const
  | @insert i s hi ih =>
    have hai := ha i (Finset.mem_insert_self _ _)
    have has : ∀j∈s,AnalyticAt ℂ (UpperHalfPlane.cuspFunction h (F j)) 0 :=
      fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hp := ih has
    rw [Finset.prod_insert hi,UpperHalfPlane.cuspFunction_mul hai.continuousAt hp.continuousAt]
    exact hai.mul hp

/-- The actual Fourier expansion of an analytic finite product is the product of the expansions. -/
lemma lpsQExpansion_prod {ι : Type*} (h : ℝ) (s : Finset ι) (F : ι→ℍ→ℂ)
    (ha : ∀i∈s,AnalyticAt ℂ (UpperHalfPlane.cuspFunction h (F i)) 0) :
    UpperHalfPlane.qExpansion h (∏i∈s,F i)=∏i∈s,UpperHalfPlane.qExpansion h (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,UpperHalfPlane.qExpansion_one]
  | @insert i s hi ih =>
    have hai := ha i (Finset.mem_insert_self _ _)
    have has : ∀j∈s,AnalyticAt ℂ (UpperHalfPlane.cuspFunction h (F j)) 0 :=
      fun j hj => ha j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi,Finset.prod_insert hi,
      UpperHalfPlane.qExpansion_mul hai (lpsCuspFunction_prod_analytic h s F has),ih has]

/-- Every actual Gamma0(N) quotient slash component is analytic at the common N-width cusp. -/
lemma lpsGamma0QuotientFunc_analytic (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (q : 𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction (N:ℝ) (SlashInvariantForm.quotientFunc f q)) 0 := by
  induction q using Quotient.inductionOn with
  | h r =>
    obtain ⟨ρ,hρ⟩ := r.property
    have hm : (0:ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have ha := ModularFormClass.analyticAt_cuspFunction_zero
      (ModularForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ ρ⁻¹)) hm
      (lpsGamma0Translate_integerPeriod N ρ⁻¹)
    simpa only [SlashInvariantForm.quotientFunc_mk,ModularForm.coe_translate,map_inv,hρ] using ha

/-- The actual modular-form norm expansion is the finite product of the quotient expansions. -/
lemma lpsGamma0Norm_qExpansion_product (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    UpperHalfPlane.qExpansion (N:ℝ) (ModularForm.norm 𝒮ℒ f)=
      let : Fintype (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :=
        Fintype.ofFinite _
      ∏ q : 𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ,
        UpperHalfPlane.qExpansion (N:ℝ) (SlashInvariantForm.quotientFunc f q) := by
  classical
  let : Fintype (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :=
    Fintype.ofFinite _
  rw [ModularForm.coe_norm 𝒮ℒ f]
  exact lpsQExpansion_prod (N:ℝ) Finset.univ _
    (fun q _ => lpsGamma0QuotientFunc_analytic N k f q)

/-- The identity coset gives a lower bound for the norm Fourier order at common width N. -/
lemma lpsGamma0Norm_order_commonWidth (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    (UpperHalfPlane.qExpansion (N:ℝ) f).order≤
      (UpperHalfPlane.qExpansion (N:ℝ) (ModularForm.norm 𝒮ℒ f)).order := by
  classical
  let : Fintype (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :=
    Fintype.ofFinite _
  let q0 : 𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ :=
    QuotientGroup.mk (1:𝒮ℒ)
  have h0 : SlashInvariantForm.quotientFunc f q0=(f:ℍ→ℂ) := by
    simp [q0,SlashInvariantForm.quotientFunc_mk]
  rw [lpsGamma0Norm_qExpansion_product,PowerSeries.order_prod]
  rw [←h0]
  exact Finset.single_le_sum (fun _ _ => (show (0 : ℕ∞) ≤ _ from bot_le)) (Finset.mem_univ q0)

/-- Cancel the positive integer width to compare the actual unit-width Fourier orders. -/
lemma lpsGamma0Norm_order (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    (UpperHalfPlane.qExpansion 1 f).order≤
      (UpperHalfPlane.qExpansion 1 (ModularForm.norm 𝒮ℒ f)).order := by
  have h := lpsGamma0Norm_order_commonWidth N k f
  have hN : 0<N := Nat.pos_of_ne_zero (NeZero.ne N)
  rw [lpsQExpansion_integerWidth_order _ k (by simp) N hN f,
    lpsQExpansion_integerWidth_order 𝒮ℒ _ (by simp) N hN (ModularForm.norm 𝒮ℒ f)] at h
  simp only [nsmul_eq_mul] at h
  exact (ENat.mul_le_mul_left_iff (by exact_mod_cast (NeZero.ne N)) (ENat.natCast_ne_top N)).mp h

/-- A genuine Gamma0(N) form with Fourier order above weight times index divided by twelve is zero. -/
lemma lpsGamma0_sturm (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (h : (((k * Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)).toNat/12 : ℕ):ℕ∞)<
        (UpperHalfPlane.qExpansion 1 f).order) : f=0 := by
  have hn : ModularForm.norm 𝒮ℒ f=0 :=
    ModularForm.sturm_bound_levelOne (lt_of_lt_of_le h (lpsGamma0Norm_order N k f))
  have hf := (ModularForm.norm_eq_zero_iff 𝒮ℒ f).mp hn
  exact DFunLike.coe_injective (by simpa using hf)

end QEC.Coding.TannerLiftedProduct
