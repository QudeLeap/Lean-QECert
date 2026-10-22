import QEC.Locality.Graph.ConnectedSetCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite weighted induced connected-set masses

Project-derived internal algebra for BDL26 `bdl26-witness-counting`, paper.tex
3658–3673 and 3763–3818. Complete vertex SETS are counted. Numerical local
factors in this generic layer are discharged from actual fibers in the Coding
adapter. Finite polynomial bounds are unconditional; structural exponent
lowering and geometric envelopes explicitly retain q<1. No witness, energy,
minimum size, sparse-active occupancy or physical Gibbs assertion is made.
-/
noncomputable section
namespace QEC.Locality.WeightedConnectedSetMass
open Classical ConnectedSetCounting
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Real walk-count alphabet, including genuine degree zero. -/
def alpha (Delta : ℕ) : ℝ := (Delta+1 : ℝ)^2

theorem alpha_one_le (Delta : ℕ) : 1 ≤ alpha Delta := by
  have h : (0 : ℝ) ≤ (Delta : ℝ) := Nat.cast_nonneg Delta
  unfold alpha
  nlinarith [sq_nonneg (Delta : ℝ)]

/-- Full product over every vertex of a connected induced SET. -/
def rootedMass (G : SimpleGraph V) (r : V) (m : ℕ) (a : V → ℝ) : ℝ :=
  ∑ K ∈ rooted G r m, ∏ v ∈ K, a v

def anchoredMass (G : SimpleGraph V) (R : Finset V) (m : ℕ) (a : V → ℝ) : ℝ :=
  ∑ K ∈ anchored G R m, ∏ v ∈ K, a v

/-- Structural vertices have a neutral contribution, not a fictitious factor. -/
def occupiedMass (G : SimpleGraph V) (R B : Finset V) (m : ℕ) (a : V → ℝ) : ℝ :=
  ∑ K ∈ anchored G R m, ∏ v ∈ K \ B, a v

/-- Positive-cardinality finite interval; the absent empty set contributes zero. -/
def interval (f : ℕ → ℝ) (L U : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (U+1-max 1 L), f (max 1 L+j)

theorem interval_reversed (f : ℕ → ℝ) (L U : ℕ) (h : U < max 1 L) :
    interval f L U = 0 := by
  have hz : U+1-max 1 L = 0 := by omega
  simp [interval,hz]

theorem interval_mono (f g : ℕ → ℝ) (L U : ℕ)
    (h : ∀ m, 1 ≤ m → f m ≤ g m) : interval f L U ≤ interval g L U := by
  apply Finset.sum_le_sum
  intro j hj
  apply h
  omega

/-- The range-indexed interval is exactly the positive natural closed interval. -/
theorem interval_eq_positive_Icc (f : ℕ → ℝ) (L U : ℕ) :
    interval f L U=∑ m ∈ Finset.Icc (max 1 L) U, f m := by
  have he : Finset.Icc (max 1 L) U =
      (Finset.range (U+1-max 1 L)).image (fun j => max 1 L+j) := by
    ext m
    simp only [Finset.mem_Icc,Finset.mem_image,Finset.mem_range]
    constructor
    · rintro ⟨hl,hu⟩
      exact ⟨m-max 1 L,by omega,by omega⟩
    · rintro ⟨j,hj,rfl⟩; omega
  rw [he,Finset.sum_image]
  · rfl
  · intro i hi j hj h
    change max 1 L+i = max 1 L+j at h
    exact Nat.add_left_cancel h

/-- Including m0 changes no mass when the rooted/anchored zero family is empty. -/
theorem interval_eq_Icc (f : ℕ → ℝ) (hf : f 0=0) (L U : ℕ) :
    interval f L U=∑ m ∈ Finset.Icc L U, f m := by
  rw [interval_eq_positive_Icc]
  apply Finset.sum_subset
  · intro m hm
    have h := Finset.mem_Icc.mp hm
    exact Finset.mem_Icc.mpr ⟨by omega,h.2⟩
  · intro m hm hn
    have h := Finset.mem_Icc.mp hm
    have he : m=0 := by
      simp only [Finset.mem_Icc,not_and_or,not_le] at hn
      omega
    simpa only [he] using hf

omit [Fintype V] [DecidableEq V] in
private theorem product_bound (K : Finset V) (a : V → ℝ) (b : ℝ)
    (ha : ∀ v, 0 ≤ a v) (hb : ∀ v, a v ≤ b) :
    0 ≤ ∏ v ∈ K, a v ∧ (∏ v ∈ K, a v) ≤ b^K.card := by
  refine ⟨Finset.prod_nonneg (fun v _ => ha v), ?_⟩
  calc
    _ ≤ ∏ _v ∈ K, b := Finset.prod_le_prod (fun v _ => ha v) (fun v _ => hb v)
    _ = _ := by simp

omit [Fintype V] [DecidableEq V] in
private theorem weighted_count_bound (F : Finset (Finset V)) (m : ℕ)
    (hF : ∀ K ∈ F, K.card = m) (a : V → ℝ) (b : ℝ)
    (ha : ∀ v, 0 ≤ a v) (hb : ∀ v, a v ≤ b) :
    0 ≤ ∑ K ∈ F, ∏ v ∈ K, a v ∧
      (∑ K ∈ F, ∏ v ∈ K, a v) ≤ (F.card : ℝ)*b^m := by
  refine ⟨Finset.sum_nonneg (fun K _ => (product_bound K a b ha hb).1), ?_⟩
  calc
    _ ≤ ∑ _K ∈ F, b^m := by
      apply Finset.sum_le_sum
      intro K hK
      simpa only [hF K hK] using (product_bound K a b ha hb).2
    _ = _ := by simp

/-- No smallness or temperature sign is needed for a full-factor finite bound. -/
theorem rooted_bounds (G : SimpleGraph V) (Delta : ℕ)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} ≤ Delta)
    (r : V) (m : ℕ) (a : V → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (ha : ∀ v, 0 ≤ a v) (hab : ∀ v, a v ≤ b) :
    0 ≤ rootedMass G r m a ∧ rootedMass G r m a ≤ (alpha Delta*b)^m := by
  have hh := weighted_count_bound (rooted G r m) m
    (fun K hK => ((mem_rooted G r m K).mp hK).2.1) a b ha hab
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hc : ((rooted G r m).card : ℝ) ≤ alpha Delta^m := by
    have hn := rooted_card_le G Delta hd r m
    unfold alpha
    exact_mod_cast (show (rooted G r m).card ≤ ((Delta+1)^2)^m by
      rw [← pow_mul]
      exact hn)
  calc
    _ ≤ alpha Delta^m*b^m := mul_le_mul_of_nonneg_right hc (pow_nonneg hb _)
    _ = _ := (mul_pow _ _ _).symm

theorem anchored_bounds (G : SimpleGraph V) (Delta : ℕ)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} ≤ Delta)
    (R : Finset V) (m : ℕ) (a : V → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (ha : ∀ v, 0 ≤ a v) (hab : ∀ v, a v ≤ b) :
    0 ≤ anchoredMass G R m a ∧
      anchoredMass G R m a ≤ (R.card : ℝ)*(alpha Delta*b)^m := by
  have hh := weighted_count_bound (anchored G R m) m
    (fun K hK => ((mem_anchored G R m K).mp hK).1) a b ha hab
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hc : ((anchored G R m).card : ℝ) ≤ (R.card : ℝ)*alpha Delta^m := by
    have hn := anchored_card_le G Delta hd R m
    unfold alpha
    exact_mod_cast (show (anchored G R m).card ≤ R.card*((Delta+1)^2)^m by
      rw [← pow_mul]
      exact hn)
  calc
    _ ≤ ((R.card : ℝ)*alpha Delta^m)*b^m :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg hb _)
    _ = _ := by rw [mul_pow]; ring

theorem rooted_zero_mass (G : SimpleGraph V) (r : V) (a : V → ℝ) :
    rootedMass G r 0 a = 0 := by simp [rootedMass,rooted_zero]

theorem anchored_zero_mass (G : SimpleGraph V) (R : Finset V) (a : V → ℝ) :
    anchoredMass G R 0 a = 0 := by simp [anchoredMass,anchored_zero]

theorem rooted_one_mass (G : SimpleGraph V) (r : V) (a : V → ℝ) :
    rootedMass G r 1 a = a r := by simp [rootedMass,rooted_one]

private theorem anchored_one_family (G : SimpleGraph V) (R : Finset V) :
    anchored G R 1 = R.image (fun v => ({v} : Finset V)) := by
  rw [anchored_eq_biUnion]
  ext K
  simp only [Finset.mem_biUnion,rooted_one,Finset.mem_singleton,Finset.mem_image]
  constructor
  · rintro ⟨r,hr,hK⟩
    exact ⟨r,hr,hK.symm⟩
  · rintro ⟨r,hr,hK⟩
    exact ⟨r,hr,hK.symm⟩

theorem anchored_one_mass (G : SimpleGraph V) (R : Finset V) (a : V → ℝ) :
    anchoredMass G R 1 a = ∑ r ∈ R, a r := by
  unfold anchoredMass
  rw [anchored_one_family,Finset.sum_image]
  · simp
  · intro r _ s _ h
    exact Finset.singleton_injective h

theorem anchored_empty_mass (G : SimpleGraph V) (m : ℕ) (a : V → ℝ) :
    anchoredMass G ∅ m a = 0 := by simp [anchoredMass,anchored_empty]

/-- A degree-zero connected induced carrier is a singleton, not merely <=1 set. -/
private theorem rooted_degree_zero_empty (G : SimpleGraph V)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} = 0) (r : V) (m : ℕ) (hm : m ≠ 1) :
    rooted G r m = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro K hK
  obtain ⟨hr,hcard,hc⟩ := (mem_rooted G r m K).mp hK
  have hno : ∀ v w, ¬ G.Adj v w := by
    intro v w hvw
    have hcard0 : Fintype.card {w : V // G.Adj v w}=0 := by
      simpa only [Nat.card_eq_fintype_card] using hd v
    have hEmpty : IsEmpty {w : V // G.Adj v w} := Fintype.card_eq_zero_iff.mp hcard0
    exact hEmpty.false (⟨w,hvw⟩ : {w : V // G.Adj v w})
  have heq : G.induce (K : Set V) = ⊥ := by
    ext v w
    exact iff_false_intro (hno v.val w.val)
  have hsub : Subsingleton (K : Set V) :=
    SimpleGraph.preconnected_bot_iff_subsingleton.mp (heq ▸ hc.preconnected)
  have hsingle : K = {r} := by
    ext v
    constructor
    · intro hv
      have he := @Subsingleton.elim _ hsub (⟨v,hv⟩ : K) ⟨r,hr⟩
      exact Finset.mem_singleton.mpr (congrArg Subtype.val he)
    · intro hv
      simpa only [Finset.mem_singleton.mp hv] using hr
  apply hm
  simpa only [hsingle,Finset.card_singleton] using hcard.symm

theorem rooted_degree_zero_mass (G : SimpleGraph V)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} = 0) (r : V) (m : ℕ) (a : V → ℝ) :
    rootedMass G r m a = if m=1 then a r else 0 := by
  by_cases h : m=1
  · subst m; simp [rooted_one_mass]
  · simp [rootedMass,rooted_degree_zero_empty G hd r m h,h]

theorem anchored_degree_zero_mass (G : SimpleGraph V)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} = 0) (R : Finset V) (m : ℕ) (a : V → ℝ) :
    anchoredMass G R m a = if m=1 then ∑ r ∈ R, a r else 0 := by
  by_cases h : m=1
  · subst m; simp [anchored_one_mass]
  · have he : anchored G R m = ∅ := by
      rw [anchored_eq_biUnion]
      apply Finset.eq_empty_of_forall_notMem
      intro K hK
      obtain ⟨r,hr,hKr⟩ := Finset.mem_biUnion.mp hK
      rw [rooted_degree_zero_empty G hd r m h] at hKr
      exact Finset.notMem_empty K hKr
    simp [anchoredMass,he,h]

/-- A degree-zero interval contains exactly its singleton mass when size1 is present. -/
theorem singleton_interval (x : ℝ) (L U : ℕ) :
    interval (fun m => if m=1 then x else 0) L U =
      if L≤1 ∧ 1≤U then x else 0 := by
  by_cases hL : L≤1
  · cases U with
    | zero => simp [interval]
    | succ U => simp [interval,hL]
  · have hl : 2 ≤ max 1 L := by omega
    have he : ∀ j : ℕ, max 1 L+j≠1 := by intro j; omega
    simp [interval,he,hL]

theorem rooted_degree_zero_interval (G : SimpleGraph V)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w}=0) (r : V) (a : V → ℝ) (L U : ℕ) :
    interval (fun m => rootedMass G r m a) L U = if L≤1 ∧ 1≤U then a r else 0 := by
  simp_rw [rooted_degree_zero_mass G hd]
  exact singleton_interval _ L U

theorem anchored_degree_zero_interval (G : SimpleGraph V)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w}=0) (R : Finset V) (a : V → ℝ) (L U : ℕ) :
    interval (fun m => anchoredMass G R m a) L U =
      if L≤1 ∧ 1≤U then ∑ r ∈ R, a r else 0 := by
  simp_rw [anchored_degree_zero_mass G hd]
  exact singleton_interval _ L U

/-- Finite geometric identity proved algebraically, valid even at q=0. -/
theorem geometric_identity (q : ℝ) (n : ℕ) :
    (1-q)*(∑ j ∈ Finset.range n, q^j) = 1-q^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,pow_succ]; nlinarith

def geometric (q : ℝ) (l n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, q^(l+j)

theorem geometric_formula (q : ℝ) (l n : ℕ) (hq : q<1) :
    geometric q l n = q^l*(1-q^n)/(1-q) := by
  have he := geometric_identity q n
  have hn : 1-q ≠ 0 := by linarith
  unfold geometric
  simp_rw [pow_add]
  rw [← Finset.mul_sum]
  apply (eq_div_iff hn).mpr
  calc
    (q^l*(∑ j ∈ Finset.range n, q^j))*(1-q) =
        q^l*((1-q)*(∑ j ∈ Finset.range n, q^j)) := by ring
    _ = q^l*(1-q^n) := by rw [he]

theorem geometric_le (q : ℝ) (l n : ℕ) (h0 : 0≤q) (hq : q<1) :
    geometric q l n ≤ q^l/(1-q) := by
  rw [geometric_formula q l n hq]
  apply div_le_div_of_nonneg_right _ (by linarith)
  nlinarith [mul_nonneg (pow_nonneg h0 l) (pow_nonneg h0 n)]

theorem geometric_half (q : ℝ) (l n : ℕ) (h0 : 0≤q) (hq : q≤1/2) :
    geometric q l n ≤ 2*q^l := by
  have ht := geometric_le q l n h0 (by linarith)
  have hden : 0<1-q := by linarith
  have he : q^l/(1-q) ≤ 2*q^l := (div_le_iff₀ hden).mpr (by
    nlinarith [mul_nonneg (pow_nonneg h0 l) (show 0≤1-2*q by linarith)])
  exact ht.trans he

/-- Unconditional finite interval polynomial from complete full-factor masses. -/
theorem anchored_interval_polynomial (G : SimpleGraph V) (Delta : ℕ)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} ≤ Delta) (R : Finset V)
    (a : V → ℝ) (b : ℝ) (hb : 0≤b) (ha : ∀ v, 0≤a v) (hab : ∀ v, a v≤b)
    (L U : ℕ) :
    interval (fun m => anchoredMass G R m a) L U ≤
      (R.card : ℝ)*geometric (alpha Delta*b) (max 1 L) (U+1-max 1 L) := by
  calc
    _ ≤ interval (fun m => (R.card : ℝ)*(alpha Delta*b)^m) L U :=
      interval_mono _ _ L U (fun m _ => (anchored_bounds G Delta hd R m a b hb ha hab).2)
    _ = _ := by simp only [interval,geometric,Finset.mul_sum]

theorem anchored_interval_tail (G : SimpleGraph V) (Delta : ℕ)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} ≤ Delta) (R : Finset V)
    (a : V → ℝ) (b : ℝ) (hb : 0≤b) (ha : ∀ v, 0≤a v) (hab : ∀ v, a v≤b)
    (hq : alpha Delta*b<1) (L U : ℕ) :
    interval (fun m => anchoredMass G R m a) L U ≤
      (R.card : ℝ)*(alpha Delta*b)^(max 1 L)/(1-alpha Delta*b) := by
  have h0 : 0≤alpha Delta*b := mul_nonneg (le_trans (by norm_num) (alpha_one_le Delta)) hb
  have hR : (0 : ℝ) ≤ (R.card : ℝ) := Nat.cast_nonneg R.card
  have hgeo :
      (R.card : ℝ)*geometric (alpha Delta*b) (max 1 L) (U+1-max 1 L) ≤
        (R.card : ℝ)*((alpha Delta*b)^(max 1 L)/(1-alpha Delta*b)) :=
    mul_le_mul_of_nonneg_left
      (geometric_le (alpha Delta*b) (max 1 L) (U+1-max 1 L) h0 hq) hR
  exact (anchored_interval_polynomial G Delta hd R a b hb ha hab L U).trans
    (by simpa only [mul_div_assoc] using hgeo)

/-- The rooted finite geometric consequence, with the same complete quantifiers. -/
theorem rooted_interval_tail (G : SimpleGraph V) (Delta : ℕ)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w}≤Delta) (r : V)
    (a : V → ℝ) (b : ℝ) (hb : 0≤b) (ha : ∀ v, 0≤a v) (hab : ∀ v, a v≤b)
    (hq : alpha Delta*b<1) (L U : ℕ) :
    interval (fun m => rootedMass G r m a) L U ≤
      (alpha Delta*b)^(max 1 L)/(1-alpha Delta*b) := by
  have h := interval_mono _ _ L U
    (fun m _ => (rooted_bounds G Delta hd r m a b hb ha hab).2)
  have hα : (0 : ℝ) ≤ alpha Delta := le_trans (by norm_num) (alpha_one_le Delta)
  have hq0 : (0 : ℝ) ≤ alpha Delta*b := mul_nonneg hα hb
  exact h.trans (geometric_le _ _ _ hq0 hq)

/-- Smallness derives the decreasing-power domain; it is never assumed silently. -/
theorem smallness (Delta : ℕ) (b : ℝ) (hb : 0≤b) (hq : alpha Delta*b<1) :
    0≤b ∧ b≤alpha Delta*b ∧ b<1 := by
  have he : b≤alpha Delta*b := by
    calc
      b = 1*b := by ring
      _ ≤ alpha Delta*b := mul_le_mul_of_nonneg_right (alpha_one_le Delta) hb
  exact ⟨hb,he,lt_of_le_of_lt he hq⟩

theorem occupied_zero (G : SimpleGraph V) (R B : Finset V) (a : V → ℝ) :
    occupiedMass G R B 0 a = 0 := by simp [occupiedMass,anchored_zero]

theorem occupied_empty (G : SimpleGraph V) (B : Finset V) (m : ℕ) (a : V → ℝ) :
    occupiedMass G ∅ B m a = 0 := by simp [occupiedMass,anchored_empty]

/-- Exact singleton occupied mass, because anchors are disjoint from structural nodes. -/
theorem occupied_one (G : SimpleGraph V) (R B : Finset V) (hRB : Disjoint R B)
    (a : V → ℝ) : occupiedMass G R B 1 a=∑ r ∈ R, a r := by
  unfold occupiedMass
  rw [anchored_one_family,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro r hr
    have hn : r∉B := fun h => Finset.disjoint_left.mp hRB hr h
    have hs : ({r} : Finset V) \ B = {r} := by
      ext v
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · exact fun h => h.1
      · intro hv
        exact ⟨hv,by simpa only [hv] using hn⟩
    rw [hs,Finset.prod_singleton]
  · intro r _ t _ h
    exact Finset.singleton_injective h

/-- Every actual occupied factor can be bounded without any smallness condition. -/
theorem occupied_polynomial (G : SimpleGraph V) (Delta : ℕ)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} ≤ Delta) (R B : Finset V)
    (m : ℕ) (a : V → ℝ) (b : ℝ) (hb : 0≤b)
    (ha : ∀ v, 0≤a v) (hab : ∀ v, a v≤b) :
    0≤occupiedMass G R B m a ∧
      occupiedMass G R B m a ≤ (R.card : ℝ)*(alpha Delta*(1+b))^m := by
  have hp : ∀ K ∈ anchored G R m, (∏ v ∈ K \ B, a v)≤(1+b)^m := by
    intro K hK
    have hm := ((mem_anchored G R m K).mp hK).1
    calc
      _ ≤ (1+b)^(K \ B).card :=
        (product_bound (K \ B) a (1+b) ha (fun v => by linarith [hab v])).2
      _ ≤ (1+b)^m := pow_le_pow_right₀ (by linarith)
        (hm ▸ Finset.card_le_card Finset.sdiff_subset)
  have hn : 0≤occupiedMass G R B m a :=
    Finset.sum_nonneg (fun K _ => Finset.prod_nonneg (fun v _ => ha v))
  refine ⟨hn,?_⟩
  calc
    _ ≤ ∑ _K ∈ anchored G R m, (1+b)^m := Finset.sum_le_sum hp
    _ = ((anchored G R m).card : ℝ)*(1+b)^m := by simp
    _ ≤ ((R.card : ℝ)*alpha Delta^m)*(1+b)^m := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) m)
      unfold alpha
      exact_mod_cast (show (anchored G R m).card ≤ R.card*((Delta+1)^2)^m by
        rw [← pow_mul]
        exact anchored_card_le G Delta hd R m)
    _ = _ := by rw [mul_pow]; ring

omit [Fintype V] in
private theorem remaining_card (K R B : Finset V) (m : ℕ) (hm : K.card=m)
    (hKR : (K∩R).Nonempty) (hRB : Disjoint R B) :
    max 1 (m-B.card) ≤ (K \ B).card := by
  have hpos : 1≤(K \ B).card := by
    apply Finset.one_le_card.mpr
    obtain ⟨v,hv⟩ := hKR
    have hvR := (Finset.mem_inter.mp hv).2
    have hvB : v∉B := fun hvB => (Finset.disjoint_left.mp hRB) hvR hvB
    exact ⟨v,Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hv).1,hvB⟩⟩
  have he := Finset.card_sdiff_add_card_inter K B
  have hi : (K∩B).card≤B.card := Finset.card_le_card Finset.inter_subset_right
  omega

/-- Explicit q<1 is needed to lower the actual number of occupied factors. -/
theorem occupied_strong (G : SimpleGraph V) (Delta : ℕ)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} ≤ Delta) (R B : Finset V)
    (hRB : Disjoint R B) (m : ℕ) (a : V → ℝ) (b : ℝ) (hb : 0≤b)
    (ha : ∀ v, 0≤a v) (hab : ∀ v, a v≤b) (hq : alpha Delta*b<1) :
    occupiedMass G R B m a ≤ (R.card : ℝ)*alpha Delta^m*b^(max 1 (m-B.card)) := by
  have hb1 : b≤1 := (smallness Delta b hb hq).2.2.le
  calc
    _ ≤ ∑ _K ∈ anchored G R m, b^(max 1 (m-B.card)) := by
      apply Finset.sum_le_sum
      intro K hK
      obtain ⟨hm,hc,hKR⟩ := (mem_anchored G R m K).mp hK
      exact (product_bound (K \ B) a b ha hab).2.trans
        (pow_le_pow_of_le_one hb hb1 (remaining_card K R B m hm hKR hRB))
    _ = ((anchored G R m).card : ℝ)*b^(max 1 (m-B.card)) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hb _)
      unfold alpha
      exact_mod_cast (show (anchored G R m).card ≤ R.card*((Delta+1)^2)^m by
        rw [← pow_mul]
        exact anchored_card_le G Delta hd R m)

/-- Exact finite low-prefix/shifted-tail split; the cutoff is the derived B.card. -/
def structuralEnvelope (A b : ℝ) (c L U : ℕ) : ℝ :=
  (∑ m ∈ (Finset.range (U+1-max 1 L)).filter (fun j => max 1 L+j≤c),
      b*A^(max 1 L+m)) +
    (∑ m ∈ (Finset.range (U+1-max 1 L)).filter (fun j => c < max 1 L+j),
      A^c*(A*b)^(max 1 L+m-c))

theorem occupied_interval_strong (G : SimpleGraph V) (Delta : ℕ)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} ≤ Delta) (R B : Finset V)
    (hRB : Disjoint R B) (a : V → ℝ) (b : ℝ) (hb : 0≤b)
    (ha : ∀ v, 0≤a v) (hab : ∀ v, a v≤b) (hq : alpha Delta*b<1) (L U : ℕ) :
    interval (fun m => occupiedMass G R B m a) L U ≤
      (R.card : ℝ)*structuralEnvelope (alpha Delta) b B.card L U := by
  have h := interval_mono _ _ L U
    (fun m _ => occupied_strong G Delta hd R B hRB m a b hb ha hab hq)
  apply h.trans_eq
  let l := max 1 L
  let F := Finset.range (U+1-l)
  let f := fun j => alpha Delta^(l+j)*b^(max 1 (l+j-B.card))
  have he : QEC.Locality.WeightedConnectedSetMass.interval
      (fun m => (R.card : ℝ)*alpha Delta^m*b^(max 1 (m-B.card))) L U =
      (R.card : ℝ)*∑ j ∈ F, f j := by
    simp only [interval,F,f,l,Finset.mul_sum,mul_assoc]
  rw [he]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not F (fun j => l+j≤B.card) f]
  unfold structuralEnvelope
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hc := (Finset.mem_filter.mp hj).2
    have hpow : max 1 (l+j-B.card)=1 := by omega
    simp only [f,hpow,pow_one]
    ring
  · have heq : F.filter (fun j => ¬l+j≤B.card) =
        F.filter (fun j => B.card<l+j) := by ext j; simp
    rw [heq]
    apply Finset.sum_congr rfl
    intro j hj
    have hc := (Finset.mem_filter.mp hj).2
    have hsum : B.card+(l+j-B.card)=l+j := by omega
    have hpow : max 1 (l+j-B.card)=l+j-B.card := by omega
    simp only [f,hpow,mul_pow]
    rw [← mul_assoc,← pow_add,hsum]

/-- Above the structural prefix, the finite envelope has a closed geometric form. -/
theorem structuralEnvelope_above (A b : ℝ) (c L U : ℕ) (hL : c<L) (hpos : 1≤L) :
    structuralEnvelope A b c L U = A^c*geometric (A*b) (L-c) (U+1-L) := by
  have hl : max 1 L=L := max_eq_right hpos
  unfold structuralEnvelope geometric
  simp only [hl]
  have hf : (Finset.range (U+1-L)).filter (fun j => L+j≤c) = ∅ := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range,Finset.notMem_empty,iff_false]
    omega
  have ht : (Finset.range (U+1-L)).filter (fun j => c<L+j) = Finset.range (U+1-L) := by
    ext j; simp; omega
  rw [hf,ht,Finset.sum_empty,zero_add,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hexp : L+j-c=(L-c)+j := by omega
  rw [hexp]

/-- The complete split is a finite prefix plus a geometric shifted tail at every cutoff. -/
theorem structuralEnvelope_formula (A b : ℝ) (c L U : ℕ) :
    structuralEnvelope A b c L U =
      b*geometric A (max 1 L) (min (U+1-max 1 L) (c+1-max 1 L)) +
      A^c*geometric (A*b) (max (max 1 L) (c+1)-c)
        (U+1-max (max 1 L) (c+1)) := by
  let l := max 1 L
  let h := max l (c+1)
  have hp : (Finset.range (U+1-l)).filter (fun j => l+j≤c) =
      Finset.range (min (U+1-l) (c+1-l)) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  have ht : (Finset.range (U+1-l)).filter (fun j => c<l+j) =
      (Finset.range (U+1-h)).image (fun j => h-l+j) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_image]
    constructor
    · rintro ⟨hj,hc⟩
      exact ⟨j-(h-l),by dsimp [h] at *; omega,by dsimp [h] at *; omega⟩
    · rintro ⟨k,hk,rfl⟩; dsimp [h] at *; omega
  unfold structuralEnvelope
  change (∑ j ∈ (Finset.range (U+1-l)).filter (fun j => l+j≤c), b*A^(l+j)) +
    (∑ j ∈ (Finset.range (U+1-l)).filter (fun j => c<l+j), A^c*(A*b)^(l+j-c)) = _
  rw [hp,ht,Finset.sum_image]
  · have hexps : ∀ j : ℕ, l+(h-l+j)-c=(h-c)+j := by
      intro j
      dsimp [h]
      omega
    simp_rw [hexps]
    simp only [geometric,Finset.mul_sum]
    rfl
  · intro i hi j hj he
    change h-l+i = h-l+j at he
    exact Nat.add_left_cancel he

/-- Closed low prefix handles A=1 without dividing by zero. -/
theorem prefix_formula (A b : ℝ) (l n : ℕ) (hA : A≠1) :
    b*(∑ j ∈ Finset.range n, A^(l+j)) = b*A^l*(A^n-1)/(A-1) := by
  have he := geometric_identity A n
  have he' : (A-1)*(∑ j ∈ Finset.range n, A^j)=A^n-1 := by linarith
  have hn : A-1≠0 := sub_ne_zero.mpr hA
  simp_rw [pow_add]
  rw [← Finset.mul_sum]
  apply (eq_div_iff hn).mpr
  calc
    (b*(A^l*(∑ j ∈ Finset.range n, A^j)))*(A-1) =
        b*A^l*((A-1)*(∑ j ∈ Finset.range n, A^j)) := by ring
    _ = b*A^l*(A^n-1) := by rw [he']

theorem prefix_one (b : ℝ) (l n : ℕ) :
    b*(∑ j ∈ Finset.range n, (1 : ℝ)^(l+j)) = b*n := by simp

/-- A complete above-prefix tail; no division by b or q. -/
theorem occupied_shifted_tail (G : SimpleGraph V) (Delta : ℕ)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} ≤ Delta) (R B : Finset V)
    (hRB : Disjoint R B) (a : V → ℝ) (b : ℝ) (hb : 0≤b)
    (ha : ∀ v, 0≤a v) (hab : ∀ v, a v≤b) (hq : alpha Delta*b<1)
    (L U : ℕ) (hL : B.card<L) (hp : 1≤L) :
    interval (fun m => occupiedMass G R B m a) L U ≤
      (R.card : ℝ)*alpha Delta^B.card*(alpha Delta*b)^(L-B.card)/(1-alpha Delta*b) := by
  have h := occupied_interval_strong G Delta hd R B hRB a b hb ha hab hq L U
  rw [structuralEnvelope_above _ _ _ L U hL hp] at h
  have h0 : 0≤alpha Delta*b := mul_nonneg (by linarith [alpha_one_le Delta]) hb
  have hn : 0 ≤ (R.card : ℝ)*alpha Delta^B.card :=
    mul_nonneg (Nat.cast_nonneg R.card)
      (pow_nonneg (le_trans (by norm_num) (alpha_one_le Delta)) _)
  exact h.trans (by simpa only [mul_assoc,mul_div_assoc] using
    mul_le_mul_of_nonneg_left (geometric_le _ _ _ h0 hq) hn)

end QEC.Locality.WeightedConnectedSetMass
