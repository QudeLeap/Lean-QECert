import QEC.Coding.ExpanderCodes.LPSOriginalQExpansionArithmetic
import QEC.Coding.ExpanderCodes.LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# LPSOriginalRationalModularEquation

Descend an actual monic annihilator of the SAME original j/jN to rational
coefficients for every positive level, including composite theta levels.
A genuine rational-linear retraction is applied only to finite coefficient
sums. Actual convergent Taylor series under q-power composition and genuine
nome pullbacks clear all supported negative powers. The complex zero cusp
germ descends coefficientwise to a rational zero series; actual analytic
uniqueness and the upper-half-plane identity theorem prove the global
original relation. The final theorem obtains the complex relation from its
proved predecessor and takes only the actual positive level assumptions.

The constructed monic annihilator retains the genuine finite coset-degree.
This is not irreducibility or a minimal-degree claim. Integer coefficients,
ALL compact meromorphic-field identification, a canonical smooth proper
arithmetic normalization, uniform good reduction, geometric Hecke/Frobenius/
Weil and public PK22 remain subsequent mathematics. This internal original-
family bridge is motivated by pinned PK22 main.tex ex:Xpq/th:qLDPC and the
audited Milne modular-curve route; no new public source claim is introduced.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

/-- Existence of a genuine rational-linear retraction of complex scalars fixing one, via basis extension. -/
lemma lpsOriginalRationalRetraction_exists :
    ∃ L : ℂ →ₗ[ℚ] ℚ, L 1=1 := by
  obtain ⟨L, _, hL⟩ := LinearMap.exists_extend_of_notMem
    (0 : (⊥ : Submodule ℚ ℂ) →ₗ[ℚ] ℚ) (v := (1:ℂ))
    (by simp) (1:ℚ)
  exact ⟨L,hL⟩

/-- A chosen genuine Q-linear retraction fixing one; no multiplicativity or continuity is asserted. -/
def lpsOriginalRationalRetraction : ℂ →ₗ[ℚ] ℚ :=
  Classical.choose lpsOriginalRationalRetraction_exists

/-- The chosen retraction sends actual complex one to rational one. -/
lemma lpsOriginalRationalRetraction_one :
    lpsOriginalRationalRetraction 1=1 :=
  Classical.choose_spec lpsOriginalRationalRetraction_exists

/-- The actual retraction fixes every rational cast. -/
lemma lpsOriginalRationalRetraction_rat (a : ℚ) :
    lpsOriginalRationalRetraction (a:ℂ)=a := by
  have h := lpsOriginalRationalRetraction.map_smul a (1:ℂ)
  simpa [Algebra.smul_def,eq_ratCast,lpsOriginalRationalRetraction_one] using h

/-- Genuine rational linearity for a rational scalar times an arbitrary complex scalar. -/
lemma lpsOriginalRationalRetraction_rat_mul (a : ℚ) (c : ℂ) :
    lpsOriginalRationalRetraction ((a:ℂ)*c)=
      a*lpsOriginalRationalRetraction c := by
  simpa [Algebra.smul_def,eq_ratCast] using lpsOriginalRationalRetraction.map_smul a c

/-- Coefficientwise rational linear transfer of an actual complex formal series. -/
def lpsOriginalRationalSeriesRetraction (S : PowerSeries ℂ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => lpsOriginalRationalRetraction (S.coeff n)

/-- The coefficientwise transfer respects addition by actual coefficient additivity. -/
lemma lpsOriginalRationalSeriesRetraction_add (S T : PowerSeries ℂ) :
    lpsOriginalRationalSeriesRetraction (S+T)=
      lpsOriginalRationalSeriesRetraction S+lpsOriginalRationalSeriesRetraction T := by
  ext n
  simp only [lpsOriginalRationalSeriesRetraction,PowerSeries.coeff_mk,map_add]

/-- The coefficientwise transfer sends the actual zero series to zero. -/
lemma lpsOriginalRationalSeriesRetraction_zero :
    lpsOriginalRationalSeriesRetraction 0=0 := by
  ext n
  simp only [lpsOriginalRationalSeriesRetraction,PowerSeries.coeff_mk,map_zero]

/-- Finite coefficient-convolution transfer of a complex constant times a mapped rational series. -/
lemma lpsOriginalRationalSeriesRetraction_C_mul_map (c : ℂ) (S : PowerSeries ℚ) :
    lpsOriginalRationalSeriesRetraction
      (PowerSeries.C c*PowerSeries.map (algebraMap ℚ ℂ) S)=
        PowerSeries.C (lpsOriginalRationalRetraction c)*S := by
  ext n
  simp only [lpsOriginalRationalSeriesRetraction,PowerSeries.coeff_mk,
    PowerSeries.coeff_C_mul,PowerSeries.coeff_map,eq_ratCast]
  rw [mul_comm c,lpsOriginalRationalRetraction_rat_mul,mul_comm]

/-- Actual analytic Taylor series under q-to-q-power composition from convergent sums and uniqueness. -/
lemma lpsOriginalTaylorSeries_comp_pow {f : ℂ→ℂ} (hf : AnalyticAt ℂ f 0)
    (N : ℕ) (hN : N≠0) :
    lpsOriginalTaylorSeries (fun q => f (q^N))=
      PowerSeries.expand N hN (lpsOriginalTaylorSeries f) := by
  let S := PowerSeries.expand N hN (lpsOriginalTaylorSeries f)
  have ht : Filter.Tendsto (fun q : ℂ => q^N) (𝓝 0) (𝓝 0) := by
    have he : (id : ℂ→ℂ)^N=(fun q : ℂ=>q^N) := by
      ext q
      simp only [Pi.pow_apply,id_eq]
    have h := ((continuousAt_id : ContinuousAt (id : ℂ→ℂ) 0).pow N).tendsto
    rw [he] at h
    simpa only [zero_pow hN] using h
  have he := hasFPowerSeriesAt_iff.mp hf.hasFPowerSeriesAt
  have hex : HasFPowerSeriesAt (fun q : ℂ=>f (q^N))
      (FormalMultilinearSeries.ofScalars ℂ (fun n=>S.coeff n)) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [ht.eventually he] with q hq
    simp only [zero_add,FormalMultilinearSeries.coeff_ofScalars] at hq ⊢
    have hinj : Function.Injective (fun n : ℕ => N*n) := by
      intro a b h
      exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hN) h
    apply (hinj.hasSum_iff (fun n hn=> ?_)).mp
    · simpa only [Function.comp_def,S,PowerSeries.coeff_expand_mul,
        lpsOriginalTaylorSeries_coeff,pow_mul,smul_eq_mul,div_eq_mul_inv,mul_comm] using hq
    · have hn' : ¬N∣n := by
        intro hd
        obtain ⟨m,hm⟩ := hd
        exact hn ⟨m,hm.symm⟩
      simp only [S,PowerSeries.coeff_expand_of_not_dvd N hN _ hn',smul_zero]
  have h := hex.eq_formalMultilinearSeries hex.analyticAt.hasFPowerSeriesAt
  ext n
  have heq := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ=>p.coeff n) h
  simpa only [FormalMultilinearSeries.coeff_ofScalars,lpsOriginalTaylorSeries_coeff,
    div_eq_mul_inv,mul_comm] using heq.symm

/-- Actual Taylor series under complex constant multiplication from derivative linearity. -/
lemma lpsOriginalTaylorSeries_const_mul (c : ℂ) (f : ℂ→ℂ) :
    lpsOriginalTaylorSeries (fun q=>c*f q)=PowerSeries.C c*lpsOriginalTaylorSeries f := by
  ext n
  simp only [lpsOriginalTaylorSeries_coeff,iteratedDeriv_const_mul_field,PowerSeries.coeff_C_mul]
  ring

/-- The actual zero function has zero Taylor series. -/
lemma lpsOriginalTaylorSeries_zero :
    lpsOriginalTaylorSeries (0 : ℂ→ℂ)=0 := by
  have h := lpsOriginalTaylorSeries_const_mul 0 (1:ℂ→ℂ)
  have he : (fun _ : ℂ=>0)=(0 : ℂ→ℂ) := by
    ext q
    rfl
  simpa only [zero_mul,map_zero,he] using h

/-- Actual Taylor addition for genuinely analytic functions. -/
lemma lpsOriginalTaylorSeries_add {f g : ℂ→ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    lpsOriginalTaylorSeries (f+g)=lpsOriginalTaylorSeries f+lpsOriginalTaylorSeries g := by
  ext n
  simp only [lpsOriginalTaylorSeries_coeff,map_add,
    iteratedDeriv_add hf.contDiffAt hg.contDiffAt,mul_add]

/-- The actual identity function has Taylor series X. -/
lemma lpsOriginalTaylorSeries_id :
    lpsOriginalTaylorSeries (fun q : ℂ=>q)=PowerSeries.X := by
  ext n
  simp only [lpsOriginalTaylorSeries_coeff,iteratedDeriv_fun_id_zero,PowerSeries.coeff_X]
  by_cases hn : n=1
  · subst n;norm_num
  · simp only [hn,ite_false,mul_zero]

/-- The actual q-to-q-power function has Taylor series X to the same natural power. -/
lemma lpsOriginalTaylorSeries_qpow (n : ℕ) :
    lpsOriginalTaylorSeries (fun q : ℂ=>q^n)=PowerSeries.X^n := by
  have he : (fun q : ℂ=>q^n)=((fun q : ℂ=>q)^n) := by
    funext q
    simp only [Pi.pow_apply]
  rw [he,lpsOriginalTaylorSeries_pow (f := fun q : ℂ=>q) analyticAt_id n,lpsOriginalTaylorSeries_id]

/-- Actual Taylor series of a finite sum of genuinely analytic functions. -/
lemma lpsOriginalTaylorSeries_sum {α : Type*} (S : Finset α) (f : α→ℂ→ℂ)
    (hf : ∀ a∈S, AnalyticAt ℂ (f a) 0) :
    lpsOriginalTaylorSeries (∑ a∈S, f a)=∑ a∈S, lpsOriginalTaylorSeries (f a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,lpsOriginalTaylorSeries_zero]
  | @insert a S ha ih =>
      simp only [Finset.mem_insert] at hf
      rw [Finset.sum_insert ha,Finset.sum_insert ha,lpsOriginalTaylorSeries_add
        (hf a (Or.inl rfl)) (S.analyticAt_sum fun b hb=>hf b (Or.inr hb))]
      rw [ih fun b hb=>hf b (Or.inr hb)]

/-- Genuine equivalence between zero Taylor series and ordinary analytic zero neighborhood germ. -/
lemma lpsOriginalTaylorSeries_zero_iff_germ {f : ℂ→ℂ} (hf : AnalyticAt ℂ f 0) :
    lpsOriginalTaylorSeries f=0 ↔ f=ᶠ[𝓝 0]0 := by
  constructor
  · intro h
    have h0 : FormalMultilinearSeries.ofScalars ℂ
        (fun n=>iteratedDeriv n f 0/(n.factorial:ℂ))=0 := by
      funext n
      apply FormalMultilinearSeries.coeff_eq_zero.mp
      have he := congrArg (fun S : PowerSeries ℂ=>S.coeff n) h
      simpa only [FormalMultilinearSeries.coeff_ofScalars,lpsOriginalTaylorSeries_coeff,
        div_eq_mul_inv,mul_comm,map_zero] using he
    have hp := hf.hasFPowerSeriesAt
    rw [h0] at hp
    exact hp.eventually_eq_zero
  · intro h
    have hp := hf.hasFPowerSeriesAt.eq_zero_of_eventually h
    ext n
    have he := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ=>p.coeff n) hp
    have hz : (0 : FormalMultilinearSeries ℂ ℂ ℂ).coeff n=0 := rfl
    rw [hz] at he
    simpa only [FormalMultilinearSeries.coeff_ofScalars,lpsOriginalTaylorSeries_coeff,
      div_eq_mul_inv,mul_comm,map_zero] using he

/-- The SAME rational K series expanded by every positive level maps to actual Taylor K(q^N). -/
lemma lpsOriginalJQSeries_dilated_map (N : ℕ) (hN : N≠0) :
    PowerSeries.map (algebraMap ℚ ℂ) (PowerSeries.expand N hN lpsOriginalJQSeries)=
      lpsOriginalTaylorSeries (fun q=>lpsOriginalJQCoefficient (q^N)) := by
  rw [PowerSeries.map_expand,lpsOriginalJQSeries_map]
  exact (lpsOriginalTaylorSeries_comp_pow lpsOriginalJQCoefficient_analytic_zero N hN).symm

/-- Finite monomial coefficientwise rational transfer of an actual complex polynomial. -/
def lpsOriginalRationalPolynomialRetraction (P : Polynomial ℂ) : Polynomial ℚ :=
  P.sum fun n c=>Polynomial.monomial n (lpsOriginalRationalRetraction c)

/-- Literal coefficient identity for the actual polynomial transfer. -/
lemma lpsOriginalRationalPolynomialRetraction_coeff (P : Polynomial ℂ) (n : ℕ) :
    (lpsOriginalRationalPolynomialRetraction P).coeff n=
      lpsOriginalRationalRetraction (P.coeff n) := by
  classical
  rw [lpsOriginalRationalPolynomialRetraction,Polynomial.coeff_sum,Polynomial.sum_def]
  simp only [Polynomial.coeff_monomial]
  by_cases hn : n∈P.support
  · simp [hn]
  · simp [hn,Polynomial.notMem_support_iff.mp hn]

/-- The actual polynomial transfer sends zero to zero. -/
lemma lpsOriginalRationalPolynomialRetraction_zero :
    lpsOriginalRationalPolynomialRetraction 0=0 := by
  ext n
  simp only [lpsOriginalRationalPolynomialRetraction_coeff,Polynomial.coeff_zero,map_zero]

/-- The actual polynomial transfer preserves one by the proved scalar retraction law. -/
lemma lpsOriginalRationalPolynomialRetraction_one :
    lpsOriginalRationalPolynomialRetraction 1=1 := by
  ext n
  rw [lpsOriginalRationalPolynomialRetraction_coeff]
  by_cases hn : n=0
  · subst n;simp only [Polynomial.coeff_one_zero,lpsOriginalRationalRetraction_one]
  · simp [Polynomial.coeff_one,hn]

/-- Finite bivariate coefficient transfer using the actual rational polynomial transfer. -/
def lpsOriginalRationalBivariateRetraction (P : Polynomial (Polynomial ℂ)) :
    Polynomial (Polynomial ℚ) :=
  P.sum fun n c=>Polynomial.monomial n (lpsOriginalRationalPolynomialRetraction c)

/-- Literal outer coefficient identity for the actual bivariate transfer. -/
lemma lpsOriginalRationalBivariateRetraction_coeff (P : Polynomial (Polynomial ℂ)) (n : ℕ) :
    (lpsOriginalRationalBivariateRetraction P).coeff n=
      lpsOriginalRationalPolynomialRetraction (P.coeff n) := by
  classical
  rw [lpsOriginalRationalBivariateRetraction,Polynomial.coeff_sum,Polynomial.sum_def]
  simp only [Polynomial.coeff_monomial]
  by_cases hn : n∈P.support
  · simp [hn]
  · simp [hn,Polynomial.notMem_support_iff.mp hn,lpsOriginalRationalPolynomialRetraction_zero]

/-- Actual bivariate monicity and constructed degree preservation, without minimal-degree claim. -/
lemma lpsOriginalRationalBivariateRetraction_monic_degree
    (P : Polynomial (Polynomial ℂ)) (hP : P.Monic) :
    (lpsOriginalRationalBivariateRetraction P).Monic ∧
      (lpsOriginalRationalBivariateRetraction P).natDegree=P.natDegree := by
  have hle : (lpsOriginalRationalBivariateRetraction P).natDegree≤P.natDegree := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [lpsOriginalRationalBivariateRetraction_coeff,
      Polynomial.coeff_eq_zero_of_natDegree_lt hn,lpsOriginalRationalPolynomialRetraction_zero]
  have hc : (lpsOriginalRationalBivariateRetraction P).coeff P.natDegree=1 := by
    rw [lpsOriginalRationalBivariateRetraction_coeff,hP.coeff_natDegree,
      lpsOriginalRationalPolynomialRetraction_one]
  have hd := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hc];exact one_ne_zero)
  refine ⟨?_,hd⟩
  change (lpsOriginalRationalBivariateRetraction P).coeff
    (lpsOriginalRationalBivariateRetraction P).natDegree=1
  rw [hd,hc]


/-- The actual formal coefficient retraction respects arbitrary finite sums. -/
lemma lpsOriginalRationalSeriesRetraction_sum {α : Type*}
    (s : Finset α) (f : α→PowerSeries ℂ) :
    lpsOriginalRationalSeriesRetraction (∑ a∈s,f a)=
      ∑ a∈s,lpsOriginalRationalSeriesRetraction (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,lpsOriginalRationalSeriesRetraction_zero]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha,Finset.sum_insert ha,
        lpsOriginalRationalSeriesRetraction_add,ih]

/-- Actual finite supremum of the literal weighted exponents in a complex bivariate support. -/
def lpsOriginalClearingBound (N : ℕ) (P : Polynomial (Polynomial ℂ)) : ℕ :=
  P.support.sup fun k=>(P.coeff k).support.sup fun i=>i+N*k

/-- Every genuinely supported weighted exponent is bounded by that finite supremum. -/
lemma lpsOriginalClearingBound_le (N : ℕ) (P : Polynomial (Polynomial ℂ))
    {k i : ℕ} (hk : k∈P.support) (hi : i∈(P.coeff k).support) :
    i+N*k≤lpsOriginalClearingBound N P :=
by
  change i+N*k≤P.support.sup (fun k=>(P.coeff k).support.sup (fun i=>i+N*k))
  have h : i+N*k≤(P.coeff k).support.sup (fun i=>i+N*k) := Finset.le_sup (f := fun i=>i+N*k) hi
  exact h.trans (Finset.le_sup (f := fun k=>(P.coeff k).support.sup (fun i=>i+N*k)) hk)

/-- Actual analytic cusp monomial after nonnegative weighted-exponent clearing. -/
def lpsOriginalClearedMonomial (N B i k : ℕ) (q : ℂ) : ℂ :=
  q^(B-(i+N*k))*lpsOriginalJQCoefficient q^i*lpsOriginalJQCoefficient (q^N)^k

/-- Concrete rational formal monomial of the SAME K series and its true power expansion. -/
def lpsOriginalClearedFormalMonomial (N : ℕ) (hN : N≠0)
    (B i k : ℕ) : PowerSeries ℚ :=
  PowerSeries.X^(B-(i+N*k))*lpsOriginalJQSeries^i*
    (PowerSeries.expand N hN lpsOriginalJQSeries)^k

/-- Actual analyticity at zero of every nonnegative q power. -/
lemma lpsOriginalPower_analytic (n : ℕ) :
    AnalyticAt ℂ (fun q : ℂ=>q^n) 0 := by
  have h := (analyticAt_id : AnalyticAt ℂ (id : ℂ→ℂ) 0).pow n
  have he : (id : ℂ→ℂ)^n=(fun q : ℂ=>q^n) := by
    ext q
    simp only [Pi.pow_apply,id_eq]
  rw [he] at h
  exact h

/-- Actual cleared cusp monomial analyticity for every positive level. -/
lemma lpsOriginalClearedMonomial_analytic (N : ℕ) (hN : N≠0) (B i k : ℕ) :
    AnalyticAt ℂ (lpsOriginalClearedMonomial N B i k) 0 := by
  have hKN : AnalyticAt ℂ (fun q : ℂ=>lpsOriginalJQCoefficient (q^N)) 0 := by
    exact lpsOriginalJQCoefficient_analytic_zero.comp_of_eq
      (lpsOriginalPower_analytic N) (zero_pow hN)
  exact ((lpsOriginalPower_analytic _).mul (lpsOriginalJQCoefficient_analytic_zero.pow i)).mul (hKN.pow k)

/-- Actual cleared cusp monomial Taylor identity with its concrete rational formal counterpart. -/
lemma lpsOriginalClearedMonomial_taylor (N : ℕ) (hN : N≠0) (B i k : ℕ) :
    lpsOriginalTaylorSeries (lpsOriginalClearedMonomial N B i k)=
      PowerSeries.map (algebraMap ℚ ℂ) (lpsOriginalClearedFormalMonomial N hN B i k) := by
  have hKN : AnalyticAt ℂ (fun q : ℂ=>lpsOriginalJQCoefficient (q^N)) 0 := by
    exact lpsOriginalJQCoefficient_analytic_zero.comp_of_eq
      (lpsOriginalPower_analytic N) (zero_pow hN)
  change lpsOriginalTaylorSeries
    (((fun q : ℂ=>q^(B-(i+N*k)))*(lpsOriginalJQCoefficient^i))*
      ((fun q : ℂ=>lpsOriginalJQCoefficient (q^N))^k))=_
  rw [lpsOriginalTaylorSeries_mul
    ((lpsOriginalPower_analytic _).mul (lpsOriginalJQCoefficient_analytic_zero.pow i)) (hKN.pow k),
    lpsOriginalTaylorSeries_mul (lpsOriginalPower_analytic _) (lpsOriginalJQCoefficient_analytic_zero.pow i),
    lpsOriginalTaylorSeries_qpow,
    lpsOriginalTaylorSeries_pow lpsOriginalJQCoefficient_analytic_zero,
    lpsOriginalTaylorSeries_pow hKN]
  simp only [lpsOriginalClearedFormalMonomial,map_mul,map_pow,PowerSeries.map_X,
    lpsOriginalJQSeries_map,lpsOriginalJQSeries_dilated_map]

/-- Actual nome pullback of every supported cleared monomial to the SAME original j and jN. -/
lemma lpsOriginalClearedMonomial_pullback (N : ℕ) (hN : 0<N)
    (B i k : ℕ) (hB : i+N*k≤B) (τ : ℍ) :
    lpsOriginalClearedMonomial N B i k (Function.Periodic.qParam 1 (τ:ℂ))=
      (Function.Periodic.qParam 1 (τ:ℂ))^B*lpsOriginalJInvariant τ^i*
        lpsOriginalJDilated N hN τ^k := by
  unfold lpsOriginalClearedMonomial
  rw [←lpsOriginalJInvariant_qParam_pullback τ,←lpsOriginalJDilated_qParam_pullback N hN τ,
    mul_pow,mul_pow,←pow_mul]
  calc
    _=(Function.Periodic.qParam 1 (τ:ℂ))^(B-(i+N*k)+i+N*k)*
      lpsOriginalJInvariant τ^i*lpsOriginalJDilated N hN τ^k := by
        simp only [pow_add]
        ring
    _=_ := by rw [show B-(i+N*k)+i+N*k=B by omega]

/-- Actual finite cleared complex cusp function built from the original polynomial support. -/
def lpsOriginalClearedCusp (N B : ℕ) (P : Polynomial (Polynomial ℂ)) : ℂ→ℂ :=
  ∑ k∈P.support,∑ i∈(P.coeff k).support,
    fun q=> (P.coeff k).coeff i*lpsOriginalClearedMonomial N B i k q

/-- Actual finite rational-coefficient cleared cusp function on the SAME K, using only finite retraction. -/
def lpsOriginalClearedRationalCusp (N B : ℕ)
    (P : Polynomial (Polynomial ℂ)) : ℂ→ℂ :=
  ∑ k∈P.support,∑ i∈(P.coeff k).support,
    fun q=> (lpsOriginalRationalRetraction ((P.coeff k).coeff i):ℂ)*
      lpsOriginalClearedMonomial N B i k q

/-- Actual finite rational formal cleared series with true original K monomials. -/
def lpsOriginalClearedFormal (N : ℕ) (hN : N≠0) (B : ℕ)
    (P : Polynomial (Polynomial ℂ)) : PowerSeries ℚ :=
  ∑ k∈P.support,∑ i∈(P.coeff k).support,
    PowerSeries.C (lpsOriginalRationalRetraction ((P.coeff k).coeff i))*
      lpsOriginalClearedFormalMonomial N hN B i k

/-- Actual complex cleared cusp analyticity at zero. -/
lemma lpsOriginalClearedCusp_analytic (N : ℕ) (hN : N≠0) (B : ℕ)
    (P : Polynomial (Polynomial ℂ)) : AnalyticAt ℂ (lpsOriginalClearedCusp N B P) 0 := by
  classical
  exact P.support.analyticAt_sum fun k _=> (P.coeff k).support.analyticAt_sum fun i _=>
    analyticAt_const.mul (lpsOriginalClearedMonomial_analytic N hN B i k)

/-- Actual rational cleared cusp analyticity at zero. -/
lemma lpsOriginalClearedRationalCusp_analytic (N : ℕ) (hN : N≠0) (B : ℕ)
    (P : Polynomial (Polynomial ℂ)) :
    AnalyticAt ℂ (lpsOriginalClearedRationalCusp N B P) 0 := by
  classical
  exact P.support.analyticAt_sum fun k _=> (P.coeff k).support.analyticAt_sum fun i _=>
    analyticAt_const.mul (lpsOriginalClearedMonomial_analytic N hN B i k)

/-- Genuine Taylor series of the finite complex cleared cusp function. -/
lemma lpsOriginalClearedCusp_taylor (N : ℕ) (hN : N≠0) (B : ℕ)
    (P : Polynomial (Polynomial ℂ)) :
    lpsOriginalTaylorSeries (lpsOriginalClearedCusp N B P)=
      ∑ k∈P.support,∑ i∈(P.coeff k).support,
        PowerSeries.C ((P.coeff k).coeff i)*
          PowerSeries.map (algebraMap ℚ ℂ) (lpsOriginalClearedFormalMonomial N hN B i k) := by
  classical
  unfold lpsOriginalClearedCusp
  rw [lpsOriginalTaylorSeries_sum P.support (fun k=>∑ i∈(P.coeff k).support,fun q=>(P.coeff k).coeff i*lpsOriginalClearedMonomial N B i k q) (fun k _=>
    (P.coeff k).support.analyticAt_sum fun i _=>analyticAt_const.mul
      (lpsOriginalClearedMonomial_analytic N hN B i k))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [lpsOriginalTaylorSeries_sum (P.coeff k).support (fun i=>fun q=>(P.coeff k).coeff i*lpsOriginalClearedMonomial N B i k q) (fun i _=>analyticAt_const.mul
    (lpsOriginalClearedMonomial_analytic N hN B i k))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lpsOriginalTaylorSeries_const_mul,lpsOriginalClearedMonomial_taylor N hN]

/-- Genuine Taylor series of the finite rational cleared cusp function. -/
lemma lpsOriginalClearedRationalCusp_taylor (N : ℕ) (hN : N≠0) (B : ℕ)
    (P : Polynomial (Polynomial ℂ)) :
    lpsOriginalTaylorSeries (lpsOriginalClearedRationalCusp N B P)=
      PowerSeries.map (algebraMap ℚ ℂ) (lpsOriginalClearedFormal N hN B P) := by
  classical
  unfold lpsOriginalClearedRationalCusp lpsOriginalClearedFormal
  simp only [map_sum,map_mul,PowerSeries.map_C]
  rw [lpsOriginalTaylorSeries_sum P.support (fun k=>∑ i∈(P.coeff k).support,fun q=>(lpsOriginalRationalRetraction ((P.coeff k).coeff i):ℂ)*lpsOriginalClearedMonomial N B i k q) (fun k _=>
    (P.coeff k).support.analyticAt_sum fun i _=>analyticAt_const.mul
      (lpsOriginalClearedMonomial_analytic N hN B i k))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [lpsOriginalTaylorSeries_sum (P.coeff k).support (fun i=>fun q=>(lpsOriginalRationalRetraction ((P.coeff k).coeff i):ℂ)*lpsOriginalClearedMonomial N B i k q) (fun i _=>analyticAt_const.mul
    (lpsOriginalClearedMonomial_analytic N hN B i k))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lpsOriginalTaylorSeries_const_mul,lpsOriginalClearedMonomial_taylor N hN]
  rfl

/-- Actual original polynomial nome pullback after the genuine common clearing bound. -/
lemma lpsOriginalClearedCusp_pullback (N : ℕ) (hN : 0<N)
    (P : Polynomial (Polynomial ℂ)) (τ : ℍ) :
    lpsOriginalClearedCusp N (lpsOriginalClearingBound N P) P
      (Function.Periodic.qParam 1 (τ:ℂ))=
      (Function.Periodic.qParam 1 (τ:ℂ))^(lpsOriginalClearingBound N P)*
        P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ)) (lpsOriginalJDilated N hN τ) := by
  classical
  simp only [lpsOriginalClearedCusp,Finset.sum_apply,Polynomial.eval₂_eq_sum,
    Polynomial.coe_evalRingHom,Polynomial.eval_eq_sum,Polynomial.sum_def,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  rw [lpsOriginalClearedMonomial_pullback N hN _ i k
    (lpsOriginalClearingBound_le N P hk hi)]
  ring

/-- Original global complex relation implies zero on the punctured unit disk via a true upper-half-plane lift. -/
lemma lpsOriginalClearedCusp_disk_zero (N : ℕ) (hN : 0<N)
    (P : Polynomial (Polynomial ℂ))
    (hroot : ∀ τ : ℍ,P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
      (lpsOriginalJDilated N hN τ)=0) {q : ℂ} (hq : ‖q‖<1) (hq0 : q≠0) :
    lpsOriginalClearedCusp N (lpsOriginalClearingBound N P) P q=0 := by
  let τ : ℍ := ⟨Function.Periodic.invQParam 1 q,
    Function.Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num) hq hq0⟩
  have hqτ : Function.Periodic.qParam 1 (τ:ℂ)=q :=
    Function.Periodic.qParam_right_inv (by norm_num) hq0
  rw [←hqτ,lpsOriginalClearedCusp_pullback N hN P τ,hroot,mul_zero]


/-- Ordinary cleared cusp zero germ from the actual punctured-disk relation and continuity at zero. -/
lemma lpsOriginalClearedCusp_zero_germ (N : ℕ) (hN : 0<N)
    (P : Polynomial (Polynomial ℂ))
    (hroot : ∀ τ : ℍ,P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
      (lpsOriginalJDilated N hN τ)=0) :
    lpsOriginalClearedCusp N (lpsOriginalClearingBound N P) P=ᶠ[𝓝 0]0 := by
  let G := lpsOriginalClearedCusp N (lpsOriginalClearingBound N P) P
  have hsmall : ∀ᶠ q : ℂ in 𝓝 0, ‖q‖<1 := by
    exact (isOpen_lt (continuous_norm : Continuous (fun q : ℂ=>‖q‖)) continuous_const).mem_nhds (by norm_num : ‖(0:ℂ)‖<1)
  have hp : G=ᶠ[𝓝[≠] (0:ℂ)]0 := by
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with q hq hq0
    exact lpsOriginalClearedCusp_disk_zero N hN P hroot hq hq0
  have h0 : G 0=0 := tendsto_nhds_unique_of_eventuallyEq
    ((lpsOriginalClearedCusp_analytic N (Nat.ne_of_gt hN) _ P).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds) tendsto_const_nhds hp
  filter_upwards [hsmall] with q hq
  by_cases hq0 : q=0
  · subst q;exact h0
  · exact lpsOriginalClearedCusp_disk_zero N hN P hroot hq hq0

/-- The actual rational cleared formal series is zero by finite coefficientwise descent of the complex zero Taylor series. -/
lemma lpsOriginalClearedFormal_zero (N : ℕ) (hN : 0<N)
    (P : Polynomial (Polynomial ℂ))
    (hroot : ∀ τ : ℍ,P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
      (lpsOriginalJDilated N hN τ)=0) :
    lpsOriginalClearedFormal N (Nat.ne_of_gt hN) (lpsOriginalClearingBound N P) P=0 := by
  have hz := (lpsOriginalTaylorSeries_zero_iff_germ
    (lpsOriginalClearedCusp_analytic N (Nat.ne_of_gt hN) _ P)).mpr
      (lpsOriginalClearedCusp_zero_germ N hN P hroot)
  rw [lpsOriginalClearedCusp_taylor] at hz
  have h := congrArg lpsOriginalRationalSeriesRetraction hz
  simpa only [lpsOriginalRationalSeriesRetraction_sum,
    lpsOriginalRationalSeriesRetraction_C_mul_map,lpsOriginalRationalSeriesRetraction_zero,
    lpsOriginalClearedFormal] using h

/-- The actual rational cleared cusp function has ordinary zero germ by genuine Taylor uniqueness. -/
lemma lpsOriginalClearedRationalCusp_zero_germ (N : ℕ) (hN : 0<N)
    (P : Polynomial (Polynomial ℂ))
    (hroot : ∀ τ : ℍ,P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
      (lpsOriginalJDilated N hN τ)=0) :
    lpsOriginalClearedRationalCusp N (lpsOriginalClearingBound N P) P=ᶠ[𝓝 0]0 := by
  apply (lpsOriginalTaylorSeries_zero_iff_germ
    (lpsOriginalClearedRationalCusp_analytic N (Nat.ne_of_gt hN) _ P)).mp
  rw [lpsOriginalClearedRationalCusp_taylor N (Nat.ne_of_gt hN),lpsOriginalClearedFormal_zero N hN P hroot,
    map_zero]

/-- Literal evaluation of the transferred rational bivariate polynomial as finite original-support scalar sums. -/
lemma lpsOriginalRationalBivariateRetraction_eval
    (P : Polynomial (Polynomial ℂ)) (x y : ℂ) :
    (lpsOriginalRationalBivariateRetraction P).eval₂
      ((Polynomial.evalRingHom x).comp (Polynomial.mapRingHom (algebraMap ℚ ℂ))) y=
      ∑ k∈P.support,∑ i∈(P.coeff k).support,
        (lpsOriginalRationalRetraction ((P.coeff k).coeff i):ℂ)*x^i*y^k := by
  classical
  unfold lpsOriginalRationalBivariateRetraction
  rw [Polynomial.eval₂_sum]
  simp only [Polynomial.eval₂_monomial,Polynomial.sum_def,RingHom.comp_apply,
    Polynomial.coe_evalRingHom,lpsOriginalRationalPolynomialRetraction,
    Polynomial.coe_mapRingHom,Polynomial.map_sum,Polynomial.map_monomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial,
    Finset.sum_mul,eq_ratCast]

/-- Actual rational cleared cusp nome pullback to the transferred original j/jN equation. -/
lemma lpsOriginalClearedRationalCusp_pullback (N : ℕ) (hN : 0<N)
    (P : Polynomial (Polynomial ℂ)) (τ : ℍ) :
    lpsOriginalClearedRationalCusp N (lpsOriginalClearingBound N P) P
      (Function.Periodic.qParam 1 (τ:ℂ))=
      (Function.Periodic.qParam 1 (τ:ℂ))^(lpsOriginalClearingBound N P)*
        (lpsOriginalRationalBivariateRetraction P).eval₂
          ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
            (Polynomial.mapRingHom (algebraMap ℚ ℂ))) (lpsOriginalJDilated N hN τ) := by
  classical
  rw [lpsOriginalRationalBivariateRetraction_eval]
  simp only [lpsOriginalClearedRationalCusp,Finset.sum_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  rw [lpsOriginalClearedMonomial_pullback N hN _ i k
    (lpsOriginalClearingBound_le N P hk hi)]
  ring


/-- The rational transferred polynomial vanishes globally on SAME original j and jN by the true analytic identity theorem. -/
lemma lpsOriginalRationalBivariateRetraction_original_root
    (N : ℕ) (hN : 0<N) (P : Polynomial (Polynomial ℂ))
    (hroot : ∀ τ : ℍ,P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
      (lpsOriginalJDilated N hN τ)=0) : ∀ τ : ℍ,
      (lpsOriginalRationalBivariateRetraction P).eval₂
        ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
          (Polynomial.mapRingHom (algebraMap ℚ ℂ))) (lpsOriginalJDilated N hN τ)=0 := by
  classical
  let F : ℍ→ℂ := ∑ k∈P.support,∑ i∈(P.coeff k).support,
    fun τ=> (lpsOriginalRationalRetraction ((P.coeff k).coeff i):ℂ)*
      lpsOriginalJInvariant τ^i*lpsOriginalJDilated N hN τ^k
  have hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := by
    exact MDifferentiable.sum fun k _=>MDifferentiable.sum fun i _=>
      (mdifferentiable_const.mul (lpsOriginalJInvariant_holomorphic.pow i)).mul
        ((lpsOriginalJDilated_holomorphic N hN).pow k)
  have heval (τ : ℍ) :
      (lpsOriginalRationalBivariateRetraction P).eval₂
        ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
          (Polynomial.mapRingHom (algebraMap ℚ ℂ))) (lpsOriginalJDilated N hN τ)=F τ := by
    rw [lpsOriginalRationalBivariateRetraction_eval]
    simp only [F,Finset.sum_apply]
  let G := lpsOriginalClearedRationalCusp N (lpsOriginalClearingBound N P) P
  have hg : G=ᶠ[𝓝 (0:ℂ)]0 := lpsOriginalClearedRationalCusp_zero_germ N hN P hroot
  obtain ⟨s,hs,hopen,h0⟩ := eventually_nhds_iff.mp hg
  obtain ⟨τ,hτ⟩ : ∃ τ : ℍ,Function.Periodic.qParam 1 (τ:ℂ)∈s :=
    ((UpperHalfPlane.qParam_tendsto_atImInfty (by norm_num : (0:ℝ)<1)).eventually
      (hopen.mem_nhds h0)).exists
  have hnear : ∀ᶠ z : ℍ in 𝓝 τ,Function.Periodic.qParam 1 (z:ℂ)∈s :=
    ((Function.Periodic.continuous_qParam.comp UpperHalfPlane.continuous_coe).continuousAt.tendsto).eventually
      (hopen.mem_nhds hτ)
  have hzero : ∀ᶠ z : ℍ in 𝓝 τ,F z=0 := by
    filter_upwards [hnear] with z hz
    have h := hs _ hz
    change lpsOriginalClearedRationalCusp N (lpsOriginalClearingBound N P) P (Function.Periodic.qParam 1 (z:ℂ))=0 at h
    rw [lpsOriginalClearedRationalCusp_pullback N hN P z,heval] at h
    exact (mul_eq_zero.mp h).resolve_left
      (pow_ne_zero _ (Function.Periodic.qParam_ne_zero _))
  have hfzero : F=0 := UpperHalfPlane.eq_zero_of_frequently hF
    ((hzero.filter_mono nhdsWithin_le_nhds).frequently)
  intro z
  rw [heval,hfzero]
  rfl


/-- Owned rational MONIC annihilator for SAME original j/jN at every positive level, with genuine finite coset-degree and no supplied relation/model. -/
lemma lpsOriginalJ_jN_rational_monic_relation (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃ Φ : Polynomial (Polynomial ℚ), Φ.Monic ∧
      Φ.natDegree=Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧ ∀ τ : ℍ,
      Φ.eval₂ ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ))) (lpsOriginalJDilated N hN τ)=0 := by
  obtain ⟨P,hP,hdeg,hroot⟩ := lpsOriginalJ_jN_monic_relation N hN
  obtain ⟨hm,hd⟩ := lpsOriginalRationalBivariateRetraction_monic_degree P hP
  exact ⟨lpsOriginalRationalBivariateRetraction P,hm,hd.trans hdeg,
    lpsOriginalRationalBivariateRetraction_original_root N hN P hroot⟩


end
end QEC.Coding.TannerLiftedProduct
