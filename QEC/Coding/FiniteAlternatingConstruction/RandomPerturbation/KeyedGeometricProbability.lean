import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.KeyedGeometricEvents
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.ProbabilityDecay
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.ConcreteParameters

/-!
Project-derived internal/API primitive-key event closure, pinned BDL26 paper.tex
1409–1424. Speculative stacked source over audited PR1608 H7aec; no kernel,
recursive embedding, execution-law or expected-time completion is claimed.
-/
namespace QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory
/-- Joint address injectivity follows from the proved incidence-rank coloring. -/
theorem key_addresses_injective (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key)
    {A : Type*} (labels : A → Triangle P) (hinj : Function.Injective labels)
    (hcolor : ∀ a b, BDL26NativeTriangleColors.policyColor P key (labels a) = BDL26NativeTriangleColors.policyColor P key (labels b)) :
    Function.Injective (fun s : (a : A) × Fin 3 => triangleVertex P (labels s.1) s.2) := by
  intro s t h
  have hab := hinj (BDL26NativeTriangleColors.policy_same_vertex P key hk (hcolor s.1 t.1) h)
  rcases s with ⟨a,i⟩
  rcases t with ⟨b,j⟩
  dsimp at hab
  subst b
  have hij := triangleVertex_injective P (labels a) h
  change i = j at hij
  subst j
  rfl

/-- Reindexing the actual vertex product derives a joint product of triangle laws. -/
theorem key_triangle_family_law (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) {A : Type*} [Fintype A]
    (labels : A → Triangle P) (hinj : Function.Injective labels)
    (hcolor : ∀ a b, BDL26NativeTriangleColors.policyColor P key (labels a) = BDL26NativeTriangleColors.policyColor P key (labels b))
    (ν : Vertex P → Measure Space) [∀ v, IsProbabilityMeasure (ν v)] :
    (Measure.pi ν).map (fun p a i => p (triangleVertex P (labels a) i)) =
      Measure.pi (fun a => Measure.pi (fun i => ν (triangleVertex P (labels a) i))) := by
  let address : ((a : A) × Fin 3) → Vertex P := fun s => triangleVertex P (labels s.1) s.2
  have hflat := Measure.map_infinitePi_infinitePi_of_inj
    (P := ν) (f := address) (key_addresses_injective P key hk labels hinj hcolor)
  have hcur := congrArg
    (fun m => m.map (MeasurableEquiv.piCurry (fun (_a : A) (_i : Fin 3) => Space))) hflat
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hcur
  change _ = (Measure.infinitePi (fun s : (a : A) × Fin 3 => ν (address s))).map
    (MeasurableEquiv.piCurry (fun (_a : A) (_i : Fin 3) => Space)) at hcur
  rw [Measure.infinitePi_map_piCurry (fun (a : A) (i : Fin 3) => ν (address ⟨a,i⟩))] at hcur
  simp only [Function.comp_def,MeasurableEquiv.coe_piCurry,Measure.infinitePi_eq_pi] at hcur
  have he : (fun (p : Vertex P → Space) => Sigma.curry (fun s : (a : A) × Fin 3 => p (address s))) =
      (fun (p : Vertex P → Space) a i => p (triangleVertex P (labels a) i)) := by
    funext p a i
    rfl
  rw [he] at hcur
  exact hcur

/-- A fixed ball is tested against every selected triangle; no pairwise-only shortcut. -/
theorem key_triangle_hit_probability (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key)
    {A : Type*} [Fintype A] (labels : A → Triangle P) (hinj : Function.Injective labels)
    (hcolor : ∀ a b, BDL26NativeTriangleColors.policyColor P key (labels a) = BDL26NativeTriangleColors.policyColor P key (labels b))
    {R c ρ : ℝ} (hR : 0 < R) (hc0 : -1 < c) (hc1 : c < 1) (hρ : 0 ≤ ρ)
    (J : Vertex P → Space) (z : Space) :
    Measure.pi (vertexLaw P R c)
      {p | ∀ a, (fun i => p (triangleVertex P (labels a) i)) ∈
        triangleHit (fun i => J (triangleVertex P (labels a) i)) z ρ} ≤
      ENNReal.ofReal (18*ρ/(R*(1-c))) ^ Fintype.card A := by
  letI (v : Vertex P) := vertexLaw_probability P R hc1 v
  let read := fun (p : Vertex P → Space) a i => p (triangleVertex P (labels a) i)
  let test := fun a => triangleHit (fun i => J (triangleVertex P (labels a) i)) z ρ
  have hm : Measurable read := by fun_prop
  have ht : ∀ a, MeasurableSet (test a) := fun a => measurableSet_triangleHit _ _ _
  have he : {p | ∀ a, read p a ∈ test a} = read ⁻¹' Set.univ.pi test := by ext p; simp
  change Measure.pi (vertexLaw P R c) {p | ∀ a, read p a ∈ test a} ≤ _
  rw [he,← Measure.map_apply hm (MeasurableSet.univ_pi ht)]
  change ((Measure.pi (vertexLaw P R c)).map
    (fun p a i => p (triangleVertex P (labels a) i))) (Set.univ.pi test) ≤ _
  rw [key_triangle_family_law P key hk labels hinj hcolor,Measure.pi_pi]
  calc
    _ ≤ ∏ _a : A, ENNReal.ofReal (18*ρ/(R*(1-c))) := by
      apply Finset.prod_le_prod'
      intro a _
      exact capProduct_triangleHit_le_same_cutoff hR hρ
        (fun i => vertexAxis P (triangleVertex P (labels a) i)) hc0 hc1 _ _
    _ = _ := by simp

/-- Joint triangle independence is derived before taking the finite union of grid centers. -/
theorem key_event_probability_le (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : KeyEvent P key hk J radius)
    {R c : ℝ} (hR : 0 < R) (hc0 : -1 < c) (hc1 : c < 1) :
    Measure.pi (vertexLaw P R c)
      (localEvent (keySupport P key hk J radius) (keyBad P key hk J radius lambda K) e) ≤
      (Fintype.card (Grid K) : ENNReal)*ENNReal.ofReal (18*2/(R*(1-c)))^4 := by
  let test (g : Grid K) : Set (Vertex P → Space) :=
    {p | ∀ a : e.val, (fun i => p (triangleVertex P a.val i)) ∈
      triangleHit (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i)))
        (keyCenter P key hk J radius lambda K e g) 2}
  have he : localEvent (keySupport P key hk J radius) (keyBad P key hk J radius lambda K) e =
      ⋃ g : Grid K, test g := by
    ext p
    simpa only [test,Set.mem_iUnion,Set.mem_setOf_eq] using mem_keyEvent P key hk J radius lambda K e p
  have hb (g : Grid K) : Measure.pi (vertexLaw P R c) (test g) ≤
      ENNReal.ofReal (18*2/(R*(1-c)))^4 := by
    have h := key_triangle_hit_probability P key hk (fun a : e.val => a.val)
      Subtype.val_injective (fun a b => e.property.2.1 a.val a.property b.val b.property)
      hR hc0 hc1 (by norm_num : (0 : ℝ) ≤ 2)
      (fun v => lambda • ((1/2 : ℝ) • J v)) (keyCenter P key hk J radius lambda K e g)
    simpa only [Fintype.card_coe,e.property.1] using h
  rw [he]
  calc
    _ ≤ ∑ g : Grid K, Measure.pi (vertexLaw P R c) (test g) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _g : Grid K, ENNReal.ofReal (18*2/(R*(1-c)))^4 :=
      Finset.sum_le_sum (fun g _ => hb g)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem key_event_probability_real_le (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : KeyEvent P key hk J radius)
    {R c : ℝ} (hR : 0 < R) (hc0 : -1 < c) (hc1 : c < 1) :
    (Measure.pi (vertexLaw P R c)).real
      (localEvent (keySupport P key hk J radius) (keyBad P key hk J radius lambda K) e) ≤
      (Fintype.card (Grid K) : ℝ)*(18*2/(R*(1-c)))^4 := by
  have hb := key_event_probability_le P key hk J radius lambda K e hR hc0 hc1
  have htop : (Fintype.card (Grid K) : ENNReal)*ENNReal.ofReal (18*2/(R*(1-c)))^4 ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have h := ENNReal.toReal_mono htop hb
  have hden : 0 < 1-c := sub_pos.mpr hc1
  have hn : 0 ≤ (18*2 : ℝ)/(R*(1-c)) := by positivity
  simpa only [measureReal_def,ENNReal.toReal_mul,ENNReal.toReal_natCast,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal hn] using h

theorem key_event_probability_real_decay (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius : ℝ) (a lambda : ℕ) (ha : 0 < a) (hl : 1 ≤ lambda)
    (e : KeyEvent P key hk J radius) {c : ℝ} (hc0 : -1 < c) (hc1 : c < 1) :
    (Measure.pi (vertexLaw P ((a : ℝ)*lambda) c)).real
      (localEvent (keySupport P key hk J radius)
        (keyBad P key hk J radius lambda ((a+2)*lambda)) e) ≤
      probabilityCoefficient a c/(lambda : ℝ) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hlR : (0 : ℝ) < lambda := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hl)
  have hden : 0 < 1-c := sub_pos.mpr hc1
  let B : ℝ := 125*18/((a : ℝ)*(1-c))
  have hhit0 : 0 ≤ (18*2 : ℝ)/((a : ℝ)*lambda*(1-c)) := by positivity
  have hhit : (18*2 : ℝ)/((a : ℝ)*lambda*(1-c)) ≤ B/(lambda : ℝ) := by
    calc
      _ ≤ (125*18 : ℝ)/((a : ℝ)*lambda*(1-c)) :=
        div_le_div_of_nonneg_right (by norm_num) (by positivity)
      _ = B/(lambda : ℝ) := by
        dsimp [B]
        field_simp [haR.ne',hlR.ne',hden.ne']
        <;> ring
  have hgrid : (Fintype.card (Grid ((a+2)*lambda)) : ℝ) ≤
      ((2*(a+2)+1 : ℕ)^3 : ℝ)*(lambda : ℝ)^3 := by
    exact_mod_cast scaled_grid_card_le (a+2) lambda hl
  have hb := key_event_probability_real_le P key hk J radius lambda ((a+2)*lambda) e
    (mul_pos haR hlR) hc0 hc1
  calc
    _ ≤ (Fintype.card (Grid ((a+2)*lambda)) : ℝ)*
        (18*2/((a : ℝ)*lambda*(1-c)))^4 := hb
    _ ≤ (((2*(a+2)+1 : ℕ)^3 : ℝ)*(lambda : ℝ)^3)*(B/(lambda : ℝ))^4 :=
      mul_le_mul hgrid (pow_le_pow_left₀ hhit0 hhit 4) (by positivity) (by positivity)
    _ = probabilityCoefficient a c/(lambda : ℝ) := by
      rw [cubic_times_four_hits hlR]
      rfl


/-- Four complete triangles expose twelve distinct ORIGINAL vertex addresses. -/
theorem keyEvent_addresses_injective (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ)
    (e : KeyEvent P key hk J radius) :
    Function.Injective (fun s : (a : e.val) × Fin 3 => triangleVertex P s.1.val s.2) :=
  key_addresses_injective P key hk (fun a : e.val => a.val) Subtype.val_injective
    (fun a b => e.property.2.1 a.val a.property b.val b.property)

/-- The union support has exactly twelve domain variables, including collapsed images. -/
theorem keySupport_card_eq_twelve (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ)
    (e : KeyEvent P key hk J radius) : (keySupport P key hk J radius e).card = 12 := by
  classical
  let address : ((a : e.val) × Fin 3) → keySupport P key hk J radius e :=
    fun s => keyVertex P key hk J radius e s.1 s.2
  have hinj : Function.Injective address := by
    intro a b h
    exact keyEvent_addresses_injective P key hk J radius e (congrArg Subtype.val h)
  have hsurj : Function.Surjective address := by
    intro v
    obtain ⟨a,ha,hva⟩ := Finset.mem_biUnion.mp v.property
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hva
    exact ⟨⟨⟨a,ha⟩,i⟩,Subtype.ext hi⟩
  have hcard := Fintype.card_congr (Equiv.ofBijective address ⟨hinj,hsurj⟩)
  have hdomain : Fintype.card ((a : e.val) × Fin 3) = 12 := by
    rw [Fintype.card_sigma]
    norm_num [Fintype.card_coe,e.property.1]
  calc
    _ = Fintype.card ((a : e.val) × Fin 3) := by
      simpa only [Fintype.card_coe] using hcard.symm
    _ = 12 := hdomain

/-- No caller supplies an event joint-law certificate: all twelve addresses are derived. -/
theorem keyEvent_joint_law (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ)
    (e : KeyEvent P key hk J radius) (ν : Vertex P → Measure Space)
    [∀ v, IsProbabilityMeasure (ν v)] :
    (Measure.pi ν).map (fun w (a : e.val) i => w (triangleVertex P a.val i)) =
      Measure.pi (fun a : e.val => Measure.pi (fun i => ν (triangleVertex P a.val i))) :=
  key_triangle_family_law P key hk (fun a : e.val => a.val) Subtype.val_injective
    (fun a b => e.property.2.1 a.val a.property b.val b.property) ν

/-- The complete numerical parameters give the actual keyed event's required bound. -/
theorem key_probability_real_bound (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) (e : KeyEvent P key hk J (anchorRadius p.m)) :
    (Measure.pi (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))).real
      (localEvent (keySupport P key hk J (anchorRadius p.m))
        (keyBad P key hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e) ≤
      probabilityCoefficient (6*p.m) (capCutoff p.m)/(p.lambda : ℝ) := by
  have ha : 0 < 6*p.m := by have hm := p.m_two; omega
  exact key_event_probability_real_decay P key hk J (anchorRadius p.m) (6*p.m)
    p.lambda ha p.lambda_one e (capCutoff_bounds p.m_two).1 (capCutoff_bounds p.m_two).2

end QEC.Coding.BDL26KeyedGeometric
