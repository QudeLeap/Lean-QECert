import QEC.Coding.ExpanderCodes.LPSOriginalMeromorphicRestriction
import Mathlib.Analysis.Analytic.Polynomial

/-!
# Finite actual poles and original j-polynomial clearing

This module belongs to the source-grounded original LPS analytic proof closure.
Milne, *Modular Functions and Modular Forms*, Theorem 6.1 (PDF85 / printed82)
and Propositions 1.16–1.18 motivate the genuine function-field degree argument.
The filled original Gamma0(N) manifold statements retain their proved scope
4 divides N, including the actual theta levels 16*q_graph^2.

The all-meromorphic objects use actual chartwise-meromorphic representatives
and genuine germ equality. They are never defined as the generated C(j,j_N).
The public arbitrary-field/all-rate PK22 theorem, arithmetic normalization,
uniform good reduction and geometric Weil estimate remain further proof work.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

/-- Actual local meromorphy implies analyticity away from the chart center. -/
lemma lpsOriginalFilledChartMeromorphic_eventually_analytic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (x : LPSOriginalFilledCurve N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    ∀ᶠ y in 𝓝[≠] x, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F y := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let e := chartAt ℂ x
  have hx : x ∈ e.source := mem_chart_source ℂ x
  have hm := hF x (e x) (e.map_source hx)
  have ht : Tendsto e (𝓝[≠] x) (𝓝[≠] (e x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(e.continuousAt hx).tendsto.mono_left
      nhdsWithin_le_nhds,e.eventually_ne_nhdsWithin hx⟩
  have ha := ht.eventually hm.eventually_analyticAt
  have hs : ∀ᶠ y in 𝓝[≠] x, y ∈ e.source :=
    nhdsWithin_le_nhds (e.open_source.mem_nhds hx)
  filter_upwards [ha,hs] with y hy hys
  apply (contMDiffAt_iff_source_of_mem_source
    (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (n := ω) (x := x) hys).mpr
  rw [contMDiffWithinAt_iff_contDiffWithinAt]
  simpa only [extChartAt_coe_symm,extChartAt_coe,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Set.range_id,Function.comp_def,id_eq]
    using hy.contDiffAt.contDiffWithinAt

/-- Compactness makes the actual nonanalytic set of any meromorphic function finite. -/
lemma lpsOriginalFilledChartMeromorphic_finite_nonanalytic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    {x : LPSOriginalFilledCurve N |
      ¬ ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x}.Finite := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilledTopology_compactSpace N
  have hc : {x : LPSOriginalFilledCurve N |
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x} ∈
      Filter.codiscreteWithin (Set.univ : Set (LPSOriginalFilledCurve N)) := by
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
    intro x hx
    simp only [Set.compl_univ,Set.union_empty]
    change ∀ᶠ y in 𝓝[≠] x, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F y
    exact lpsOriginalFilledChartMeromorphic_eventually_analytic N hN F hF x
  convert isCompact_univ.finite_sdiff_of_mem_codiscreteWithin hc using 1
  ext x
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A genuine analytic zero clears a local meromorphic pole after a sufficiently large power. -/
lemma lpsOriginalMeromorphic_clear_by_analytic_zero
    (f g : ℂ → ℂ) (x : ℂ) (hf : MeromorphicAt f x) (hg : AnalyticAt ℂ g x) :
    ∃ n : ℕ, AnalyticAt ℂ (fun z => (g z-g x)^n * f z) x := by
  obtain ⟨n,hn⟩ := hf
  obtain ⟨p,hp⟩ := hg
  have hs : AnalyticAt ℂ (dslope g x) x :=
    ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩
  refine ⟨n,?_⟩
  simp only [smul_eq_mul] at hn
  apply ((hs.pow n).mul hn).congr
  apply Filter.Eventually.of_forall
  intro z
  have hd : (z-x) * dslope g x z = g z-g x :=
    sub_smul_dslope g x z
  simp only [Pi.mul_apply,Pi.pow_apply]
  rw [← hd,mul_pow]
  ring

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A monic finite product of actual j-zero factors clears every actual interior pole. -/
lemma lpsOriginalFilledMeromorphic_exists_interior_pole_polynomial
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    ∃ P : Polynomial ℂ, P.Monic ∧
      ∀ y : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ,
      AnalyticAt ℂ (fun z => P.eval (lpsOriginalFilledJ N
        ((lpsOriginalFilledInteriorChart N hN y).symm z)) *
        F ((lpsOriginalFilledInteriorChart N hN y).symm z))
        (lpsOriginalFilledInteriorChart N hN y (Sum.inl y)) := by
  classical
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let Q := MulAction.orbitRel.Quotient
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
  have hbad := lpsOriginalFilledChartMeromorphic_finite_nonanalytic N hN F hF
  have hbi : {y : Q | ¬ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F (Sum.inl y)}.Finite :=
    Set.Finite.preimage Sum.inl_injective.injOn hbad
  let B : Finset Q := hbi.toFinset
  have hc (y : Q) : ∃ n : ℕ,
      AnalyticAt ℂ (fun z => (lpsOriginalFilledJ N
        ((lpsOriginalFilledInteriorChart N hN y).symm z) -
        lpsOriginalFilledJ N (Sum.inl y))^n *
        F ((lpsOriginalFilledInteriorChart N hN y).symm z))
        (lpsOriginalFilledInteriorChart N hN y (Sum.inl y)) := by
    let e := lpsOriginalFilledInteriorChart N hN y
    have hy : Sum.inl y ∈ e.source := lpsOriginalFilledInteriorChart_mem N hN y
    have hm := hF (Sum.inl y) (e (Sum.inl y)) (e.map_source hy)
    have hj := lpsOriginalFilledJ_interior_analytic N hN y
      (e (Sum.inl y)) (e.map_source hy)
    have h := lpsOriginalMeromorphic_clear_by_analytic_zero
      (F ∘ e.symm) (lpsOriginalFilledJ N ∘ e.symm) (e (Sum.inl y)) hm hj
    simpa only [Function.comp_apply,e.left_inv hy] using h
  let n : Q → ℕ := fun y => (hc y).choose
  let A : Q → Polynomial ℂ := fun y =>
    (Polynomial.X-Polynomial.C (lpsOriginalFilledJ N (Sum.inl y)))^(n y)
  let P := ∏ y ∈ B, A y
  have hA (y : Q) : (A y).Monic :=
    (Polynomial.monic_X_sub_C _).pow _
  refine ⟨P,Polynomial.monic_prod_of_monic _ _ (fun y hy => hA y),?_⟩
  intro y
  let e := lpsOriginalFilledInteriorChart N hN y
  let j : ℂ → ℂ := lpsOriginalFilledJ N ∘ e.symm
  let f : ℂ → ℂ := F ∘ e.symm
  let a := e (Sum.inl y)
  have hy : Sum.inl y ∈ e.source := lpsOriginalFilledInteriorChart_mem N hN y
  have hj : AnalyticAt ℂ j a :=
    lpsOriginalFilledJ_interior_analytic N hN y a (e.map_source hy)
  have heval (R : Polynomial ℂ) : AnalyticAt ℂ (fun z => R.eval (j z)) a := by
    simpa only [Polynomial.coe_aeval_eq_eval] using hj.aeval_polynomial R
  by_cases hmem : y ∈ B
  · have hclear : AnalyticAt ℂ (fun z => (A y).eval (j z) * f z) a := by
      simpa only [A,n,j,f,a,Polynomial.eval_pow,Polynomial.eval_sub,
        Polynomial.eval_X,Polynomial.eval_C,Function.comp_apply] using (hc y).choose_spec
    have hrest := heval (∏ b ∈ B.erase y, A b)
    have hprod : P = (∏ b ∈ B.erase y, A b) * A y :=
      (Finset.prod_erase_mul B A hmem).symm
    change AnalyticAt ℂ (fun z => P.eval (j z) * f z) a
    rw [hprod]
    convert! hrest.mul hclear using 1
    first
    | rfl
    | (funext z; simp only [Pi.mul_apply,Polynomial.eval_mul]; ring)
  · have hreg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F (Sum.inl y) := by
      by_contra hn
      apply hmem
      exact (Set.Finite.mem_toFinset hbi).mpr hn
    have hf : AnalyticAt ℂ f a := by
      have hd := (contMDiffAt_iff_source.mp hreg)
      rw [contMDiffWithinAt_iff_contDiffWithinAt] at hd
      have hchart : chartAt ℂ (Sum.inl y : LPSOriginalFilledCurve N) = e := rfl
      have hdu : ContDiffAt ℂ ω f a := by
        simpa only [extChartAt_coe_symm,extChartAt_coe,
          modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
          Set.range_id,Function.comp_def,id_eq,contDiffWithinAt_univ,hchart,f,a]
          using hd
      exact hdu.analyticAt
    exact (heval P).mul hf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual monic pole-clearing polynomial makes P(j)F holomorphic upstairs. -/
lemma lpsOriginalFilledMeromorphic_exists_holomorphic_pole_clearing
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    ∃ P : Polynomial ℂ, P.Monic ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ =>
        P.eval (lpsOriginalJInvariant τ) * F (Sum.inl (Quotient.mk
          (MulAction.orbitRel
            (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ))) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  obtain ⟨P,hP,hclear⟩ :=
    lpsOriginalFilledMeromorphic_exists_interior_pole_polynomial N hN F hF
  refine ⟨P,hP,?_⟩
  intro τ
  let π : ℍ → LPSOriginalFilledCurve N := fun σ => Sum.inl (Quotient.mk
    (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) σ)
  let G : LPSOriginalFilledCurve N → ℂ := fun x => P.eval (lpsOriginalFilledJ N x) * F x
  have hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω G (π τ) := by
    apply contMDiffAt_iff_source.mpr
    rw [contMDiffWithinAt_iff_contDiffWithinAt]
    have hchart : chartAt ℂ (π τ) =
        lpsOriginalFilledInteriorChart N hN (Quotient.mk _ τ) := rfl
    simpa only [extChartAt_coe_symm,extChartAt_coe,hchart,
      modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
      Set.range_id,Function.comp_def,id_eq,π,G]
      using (hclear (Quotient.mk _ τ)).contDiffAt.contDiffWithinAt
  have hproj : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω π τ :=
    lpsOriginalFilled_projection_contMDiff N hN τ
  have h := (hg.comp τ hproj).mdifferentiableAt (by decide)
  simpa only [Function.comp_def,G,π,lpsOriginalFilledJ_projection] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual chartwise meromorphy is closed under natural powers. -/
lemma lpsOriginalFilledChartMeromorphic_pow
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    {F : LPSOriginalFilledCurve N → ℂ}
    (hF : lpsOriginalFilledChartMeromorphic N hN F) (m : ℕ) :
    lpsOriginalFilledChartMeromorphic N hN (F^m) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  intro x z hz
  exact (hF x z hz).pow m

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual chartwise meromorphy is preserved by any complex polynomial. -/
lemma lpsOriginalFilledChartMeromorphic_polynomial
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    {F : LPSOriginalFilledCurve N → ℂ}
    (hF : lpsOriginalFilledChartMeromorphic N hN F) (P : Polynomial ℂ) :
    lpsOriginalFilledChartMeromorphic N hN (fun x => P.eval (F x)) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have he : (fun x => (P+Q).eval (F x)) =
        ((fun x => P.eval (F x)) + (fun x => Q.eval (F x))) := by
      funext x
      exact Polynomial.eval_add
    rw [he]
    exact lpsOriginalFilledChartMeromorphic_add N hN hP hQ
  | monomial m c =>
    have he : (fun x => (Polynomial.monomial m c).eval (F x)) =
        ((fun _ => c) * F^m) := by
      funext x
      exact Polynomial.eval_monomial
    rw [he]
    exact lpsOriginalFilledChartMeromorphic_mul N hN
      (lpsOriginalFilledChartMeromorphic_const N hN c)
      (lpsOriginalFilledChartMeromorphic_pow N hN hF m)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- One actual natural power clears the poles at all finitely many original cusps. -/
lemma lpsOriginalFilledMeromorphic_uniform_cusp_pole_clearing
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    letI := lpsOriginalFilledTopology N
    ∃ k : ℕ, ∀ c : CuspOrbits
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
      AnalyticAt ℂ (fun q : ℂ => q^k *
        F ((lpsOriginalFilledCuspChart N c).symm q)) 0 := by
  classical
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let C := CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
  let := Fintype.ofFinite C
  have hc (c : C) : ∃ n : ℕ, AnalyticAt ℂ
      (fun q : ℂ => q^n * F ((lpsOriginalFilledCuspChart N c).symm q)) 0 := by
    have hz : (0 : ℂ) ∈ (lpsOriginalFilledCuspChart N c).target := by
      rw [← lpsOriginalFilledCuspChart_cusp N c]
      exact (lpsOriginalFilledCuspChart N c).map_source
        (lpsOriginalFilledCuspChart_mem_cusp N c)
    have h := hF (Sum.inr c) 0 hz
    obtain ⟨n,hn⟩ := h
    refine ⟨n,?_⟩
    have hchart : chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N) =
        lpsOriginalFilledCuspChart N c := rfl
    simp only [sub_zero,smul_eq_mul,hchart,Function.comp_apply] at hn
    convert! hn using 1
  let n : C → ℕ := fun c => (hc c).choose
  let k := ∑ c : C, n c
  refine ⟨k,?_⟩
  intro c
  have hnk : n c ≤ k := Finset.single_le_sum (fun d hd => Nat.zero_le (n d))
    (Finset.mem_univ c)
  have ha := (hc c).choose_spec
  have hh := (analyticAt_id.pow (k-n c)).mul ha
  convert! hh using 1
  funext q
  simp only [Pi.mul_apply,Pi.pow_apply,id_eq]
  rw [←mul_assoc,←pow_add,Nat.sub_add_cancel hnk]

end
end QEC.Coding.TannerLiftedProduct
