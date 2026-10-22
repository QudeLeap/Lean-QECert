import QEC.Locality.Graph.WeightedConnectedSetMass
import QEC.Coding.FiniteAlternatingConstruction.ConnectedSetCounting
import QEC.Coding.FiniteAlternatingConstruction.LocalSyndromeWeights

/-!
# Actual finite occupied-owner syndrome masses

Internal, project-derived finite algebra motivated by BDL26 paper.tex3763–3818.
The product contains every nonstructural vertex in K. It is not the sparse
source tildeV_K product, a physical Gibbs bad mass, or a witness assignment.
All real t are permitted for finite polynomial bounds. Strong structural and
geometric bounds explicitly assume q<1 and derive b<=1 from it.
-/
noncomputable section
namespace QEC.Coding.BDL26ConnectedSyndromeMass
open Classical BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26DecodingGraph BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26BoundedValence
open BDL26LocalSyndromeWeights BDL26ReplacementSupport MultiscaleDecoder
open scoped BigOperators Classical

universe u

/-- The original FULL replacement syndrome carrier; shallow graph levels are structural. -/
def OwnerCarrier (S : OddScale) : ℕ → Type
  | 0 => PEmpty.{1}
  | 1 => PEmpty.{1}
  | n+2 => if (n+2)%2=1 then RX2 (state S (n+1)).presentation S
      else RZZ (state S (n+1)).presentation S

noncomputable instance ownerCarrierFintype (S : OddScale) (i : ℕ) : Fintype (OwnerCarrier S i) := by
  cases i with
  | zero => exact inferInstanceAs (Fintype PEmpty.{1})
  | succ i => cases i with
    | zero => exact inferInstanceAs (Fintype PEmpty.{1})
    | succ n =>
      change Fintype (if (n+2)%2=1 then RX2 (state S (n+1)).presentation S
        else RZZ (state S (n+1)).presentation S)
      by_cases h : (n+2)%2=1
      · rw [if_pos h]
        infer_instance
      · rw [if_neg h]
        infer_instance

/-- Literal original owner, with the RZ owner included as its Z vertex. -/
def owner (S : OddScale) : (i : ℕ) → OwnerCarrier S i → GraphVertex S i
  | 0, c => PEmpty.elim c
  | 1, c => PEmpty.elim c
  | n+2, c =>
      if h : (n+2)%2=1 then
        rxSyndromeOwner (state S (n+1)).presentation S
          (cast (show OwnerCarrier S (n+2)=RX2 (state S (n+1)).presentation S from
            if_pos h) c)
      else Vertex.z (rzSyndromeOwner (state S (n+1)).presentation S
        (cast (show OwnerCarrier S (n+2)=RZZ (state S (n+1)).presentation S from
          if_neg h) c))

abbrev OwnerFiber (S : OddScale) (i : ℕ) (u : GraphVertex S i) :=
  {c : OwnerCarrier S i // owner S i c=u}

/-- Full original-carrier extension, no supplied fiber equivalence. -/
def extend (S : OddScale) (i : ℕ) (u : GraphVertex S i)
    (x : Word Bit (OwnerFiber S i u)) : Word Bit (OwnerCarrier S i) :=
  fiberExtend (owner S i) u x

theorem extend_weight (S : OddScale) (i : ℕ) (u : GraphVertex S i)
    (x : Word Bit (OwnerFiber S i u)) : HammingWeight (extend S i u x)=HammingWeight x := by
  convert fiberExtend_weight (owner S i) u x using 1 <;> congr 1
  exact Subsingleton.elim _ _

theorem extend_injective (S : OddScale) (i : ℕ) (u : GraphVertex S i) :
    Function.Injective (extend S i u) := fiberExtend_injective (owner S i) u

/-- All nonzero words, as a SET; zero is deleted exactly once. -/
def localWords (S : OddScale) (i : ℕ) (u : GraphVertex S i) :
    Finset (Word Bit (OwnerFiber S i u)) := Finset.univ.filter (fun x => x≠0)

theorem mem_localWords (S : OddScale) (i : ℕ) (u : GraphVertex S i)
    (x : Word Bit (OwnerFiber S i u)) : x∈localWords S i u ↔ x≠0 := by
  simp [localWords]

/-- Literal finite word factor on the actual original carrier. -/
def factor (S : OddScale) (i : ℕ) (u : GraphVertex S i) (t : ℝ) : ℝ :=
  fiberFactor (owner S i) u (localWords S i u) t

theorem factor_eq_original_set (S : OddScale) (i : ℕ) (u : GraphVertex S i) (t : ℝ) :
    factor S i u t = weightedFamily ((localWords S i u).image (extend S i u)) t :=
  fiberFactor_eq_image (owner S i) u _ t

/-- This finite-coordinate identity is proved before specializing any recursive carrier. -/
private theorem full_fiber_factor_nonzero {C Label : Type*} [Fintype C]
    (f : C → Label) (u : Label) (t : ℝ) :
    fiberFactor f u (Finset.univ.filter (fun x : Word Bit {c : C // f c=u} => x≠0)) t =
      nonzeroFactor {c : C // f c=u} t := by
  rw [fiberFactor_eq_weightedFamily]
  unfold weightedFamily nonzeroFactor
  exact Finset.sum_subtype _ (fun x => by simp) _

private theorem full_fiber_factor_empty {C Label : Type*} [Fintype C]
    (f : C → Label) (u : Label) (empty : IsEmpty {c : C // f c=u}) (t : ℝ) :
    fiberFactor f u (Finset.univ.filter (fun x : Word Bit {c : C // f c=u} => x≠0)) t=0 := by
  rw [full_fiber_factor_nonzero]
  let : IsEmpty {c : C // f c=u} := empty
  exact nonzeroFactor_empty_coordinates _ t

/-- Transport enumeration dictionaries while the coordinate type is still abstract.
The same original-carrier factor and full nonzero SET are retained. -/
private theorem full_fiber_factor_nonzero_explicit {C Label : Type*}
    (FC : Fintype C) (f : C → Label) (u : Label)
    (F : Fintype {c : C // f c=u}) (t : ℝ) :
    letI := FC
    letI := F
    fiberFactor f u (Finset.univ.filter (fun x : Word Bit {c : C // f c=u} => x≠0)) t =
      nonzeroFactor {c : C // f c=u} t := by
  let : Fintype C := FC
  have hF : F = @Subtype.fintype C (fun c => f c=u)
      (inferInstance : DecidablePred (fun c : C => f c=u)) FC := Subsingleton.elim _ _
  cases hF
  exact full_fiber_factor_nonzero f u t

/-- The empty-coordinate identity is independent of the finite enumeration too. -/
private theorem full_fiber_factor_empty_explicit {C Label : Type*}
    (FC : Fintype C) (f : C → Label) (u : Label)
    (F : Fintype {c : C // f c=u}) (empty : IsEmpty {c : C // f c=u}) (t : ℝ) :
    letI := FC
    letI := F
    fiberFactor f u (Finset.univ.filter (fun x : Word Bit {c : C // f c=u} => x≠0)) t=0 := by
  let : Fintype C := FC
  have hF : F = @Subtype.fintype C (fun c => f c=u)
      (inferInstance : DecidablePred (fun c : C => f c=u)) FC := Subsingleton.elim _ _
  cases hF
  exact full_fiber_factor_empty f u empty t

theorem factor_eq_nonzero (S : OddScale) (i : ℕ) (u : GraphVertex S i) (t : ℝ) :
    factor S i u t = nonzeroFactor (OwnerFiber S i u) t := by
  exact full_fiber_factor_nonzero_explicit
    (inferInstance : Fintype (OwnerCarrier S i)) (owner S i) u
    (inferInstance : Fintype (OwnerFiber S i u)) t

/-- Compose the full empty-fiber factor while the level is symbolic.  The finite
carrier/fiber dictionaries are fixed here before any recursive level is supplied. -/
private theorem factor_empty (S : OddScale) (i : ℕ) (u : GraphVertex S i)
    (empty : IsEmpty (OwnerFiber S i u)) (t : ℝ) : factor S i u t=0 := by
  exact full_fiber_factor_empty_explicit
    (C := OwnerCarrier S i) (Label := GraphVertex S i)
    (ownerCarrierFintype S i) (owner S i) u
    (inferInstance : Fintype (OwnerFiber S i u)) empty t

/-- Transport a complete fiber TYPE across the proved carrier equality and the
same pointwise owner; no supplied fiber equivalence or conclusion is assumed. -/
private theorem subtype_transport {A B : Type u} {Label : Type*} (e : A=B)
    (f : A → Label) (g : B → Label) (hfg : ∀ a,f a=g (cast e a)) (u : Label) :
    {a : A // f a=u}={b : B // g b=u} := by
  cases e
  have hf : f=g := funext hfg
  cases hf
  rfl

private theorem owner_rx_apply (S : OddScale) (n : ℕ) (h : (n+2)%2=1)
    (c : OwnerCarrier S (n+2)) :
    owner S (n+2) c = rxSyndromeOwner (state S (n+1)).presentation S
      (cast (show OwnerCarrier S (n+2)=RX2 (state S (n+1)).presentation S from
        if_pos h) c) := by
  change @Eq (Vertex (state S (n+1)).presentation)
    (if h' : (n+2)%2=1 then
      rxSyndromeOwner (state S (n+1)).presentation S
        (cast (show OwnerCarrier S (n+2)=RX2 (state S (n+1)).presentation S from
          if_pos h') c)
     else Vertex.z (rzSyndromeOwner (state S (n+1)).presentation S
        (cast (show OwnerCarrier S (n+2)=RZZ (state S (n+1)).presentation S from
          if_neg h') c)))
    (rxSyndromeOwner (state S (n+1)).presentation S
      (cast (show OwnerCarrier S (n+2)=RX2 (state S (n+1)).presentation S from
        if_pos h) c))
  exact dif_pos h

private theorem owner_rz_apply (S : OddScale) (n : ℕ) (h : (n+2)%2≠1)
    (c : OwnerCarrier S (n+2)) :
    owner S (n+2) c = Vertex.z (rzSyndromeOwner (state S (n+1)).presentation S
      (cast (show OwnerCarrier S (n+2)=RZZ (state S (n+1)).presentation S from
        if_neg h) c)) := by
  change @Eq (Vertex (state S (n+1)).presentation)
    (if h' : (n+2)%2=1 then
      rxSyndromeOwner (state S (n+1)).presentation S
        (cast (show OwnerCarrier S (n+2)=RX2 (state S (n+1)).presentation S from
          if_pos h') c)
     else Vertex.z (rzSyndromeOwner (state S (n+1)).presentation S
        (cast (show OwnerCarrier S (n+2)=RZZ (state S (n+1)).presentation S from
          if_neg h') c)))
    (Vertex.z (rzSyndromeOwner (state S (n+1)).presentation S
      (cast (show OwnerCarrier S (n+2)=RZZ (state S (n+1)).presentation S from
        if_neg h) c)))
  exact dif_neg h

/-- RX is the entire literal RX2 fiber, including all sum/copy constructors. -/
theorem ownerFiber_rx (S : OddScale) (n : ℕ) (h : (n+2)%2=1)
    (u : Vertex (state S (n+1)).presentation) :
    OwnerFiber S (n+2) u = RXFiber (state S (n+1)).presentation S u :=
  subtype_transport
    (show OwnerCarrier S (n+2)=RX2 (state S (n+1)).presentation S from if_pos h)
    (owner S (n+2)) (rxSyndromeOwner (state S (n+1)).presentation S)
    (owner_rx_apply S n h) u

/-- On the RZ branch X and Q owner fibers are empty, not invented syndromes. -/
theorem ownerFiber_rz_x_empty (S : OddScale) (n : ℕ) (h : (n+2)%2≠1)
    (x : (state S (n+1)).presentation.X) : IsEmpty (OwnerFiber S (n+2) (Vertex.x x)) := by
  refine ⟨?_⟩
  rintro ⟨c,hc⟩
  rw [owner_rz_apply S n h c] at hc
  cases hc

theorem ownerFiber_rz_q_empty (S : OddScale) (n : ℕ) (h : (n+2)%2≠1)
    (q : (state S (n+1)).presentation.Q) : IsEmpty (OwnerFiber S (n+2) (Vertex.q q)) := by
  refine ⟨?_⟩
  rintro ⟨c,hc⟩
  rw [owner_rz_apply S n h c] at hc
  cases hc

/-- The Z branch equivalence is constructed on the unchanged original RZZ carrier. -/
def rzFiberEquiv (S : OddScale) (n : ℕ) (h : (n+2)%2≠1)
    (z : (state S (n+1)).presentation.Z) :
    OwnerFiber S (n+2) (Vertex.z z) ≃ RZFiber (state S (n+1)).presentation S z := by
  let e : OwnerCarrier S (n+2) ≃ RZZ (state S (n+1)).presentation S :=
    Equiv.cast (show OwnerCarrier S (n+2)=RZZ (state S (n+1)).presentation S from if_neg h)
  have he (c : OwnerCarrier S (n+2)) :
      owner S (n+2) c=Vertex.z (rzSyndromeOwner (state S (n+1)).presentation S (e c)) :=
    owner_rz_apply S n h c
  refine {
    toFun := fun c => ⟨e c.val,Vertex.z.inj ((he c.val).symm.trans c.property)⟩
    invFun := fun c => ⟨e.symm c.val,?_⟩
    left_inv := fun c => Subtype.ext (e.symm_apply_apply c.val)
    right_inv := fun c => Subtype.ext (e.apply_symm_apply c.val) }
  rw [he,e.apply_symm_apply]
  exact congrArg Vertex.z c.property

/-- Cardinality depends on the coordinate TYPE, not its finite enumeration.
This equality is used before composing the native RX/RZ fiber bounds. -/
private theorem finite_card_independent {I : Type*} (F G : Fintype I) :
    @Fintype.card I F = @Fintype.card I G :=
  congrArg (fun e : Fintype I => @Fintype.card I e) (Subsingleton.elim F G)

/-- All finite enumerations of the SAME coordinate type have the same card.
The explicit instance argument avoids changing dependent dictionaries in a goal. -/
private theorem ownerFiber_card_all (S : OddScale) (i : ℕ) (u : GraphVertex S i)
    (F : Fintype (OwnerFiber S i u)) : @Fintype.card (OwnerFiber S i u) F ≤ 14*S.ell^2 := by
  let : Fintype (OwnerFiber S i u) := F
  cases i with
  | zero =>
    have hEmpty : IsEmpty (OwnerFiber S 0 u) := ⟨fun c => PEmpty.elim c.val⟩
    exact le_trans (Fintype.card_eq_zero_iff.mpr hEmpty).le (Nat.zero_le _)
  | succ i => cases i with
    | zero =>
      have hEmpty : IsEmpty (OwnerFiber S 1 u) := ⟨fun c => PEmpty.elim c.val⟩
      exact le_trans (Fintype.card_eq_zero_iff.mpr hEmpty).le (Nat.zero_le _)
    | succ n =>
      by_cases h : (n+2)%2=1
      · exact (@Fintype.card_congr _ _ F _ (Equiv.cast (ownerFiber_rx S n h u))).le.trans
          ((finite_card_independent _ _).le.trans
            (rxSyndromeFiber_card_le _ (state_boundedValence S (n+1)) S u))
      · cases u with
        | x x =>
          exact le_trans
            (Fintype.card_eq_zero_iff.mpr (ownerFiber_rz_x_empty S n h x)).le (Nat.zero_le _)
        | q q =>
          exact le_trans
            (Fintype.card_eq_zero_iff.mpr (ownerFiber_rz_q_empty S n h q)).le (Nat.zero_le _)
        | z z =>
          exact (@Fintype.card_congr _ _ F _ (rzFiberEquiv S n h z)).le.trans
            ((finite_card_independent _ _).le.trans
              (rzSyndromeFiber_card_le _ (state S (n+1)).admissible.toTannerSquareAdmissible
                (state_boundedValence S (n+1)) S z))

theorem ownerFiber_card (S : OddScale) (i : ℕ) (u : GraphVertex S i) :
    Fintype.card (OwnerFiber S i u) ≤ 14*S.ell^2 :=
  ownerFiber_card_all S i u _

def envelope (S : OddScale) (t : ℝ) : ℝ := (1+Real.exp (-t))^(14*S.ell^2)-1

def alphabet (S : OddScale) : ℝ := QEC.Locality.WeightedConnectedSetMass.alpha (14*S.ell^2+8)
def ratio (S : OddScale) (t : ℝ) : ℝ := alphabet S*envelope S t

theorem envelope_nonneg (S : OddScale) (t : ℝ) : 0≤envelope S t := by
  have hp : (1 : ℝ)≤1+Real.exp (-t) := by linarith [Real.exp_pos (-t)]
  have h : (1 : ℝ) ≤ (1+Real.exp (-t))^(14*S.ell^2) := one_le_pow₀ hp
  unfold envelope
  linarith

theorem factor_bounds (S : OddScale) (i : ℕ) (u : GraphVertex S i) (t : ℝ) :
    0≤factor S i u t ∧ factor S i u t≤envelope S t := by
  have heq : factor S i u t=weightedFamily (localWords S i u) t := by
    unfold factor fiberFactor weightedFamily
    apply Finset.sum_congr rfl
    intro x _
    rw [show HammingWeight (fiberExtend (owner S i) u x)=HammingWeight x from
      extend_weight S i u x]
  rw [heq]
  change 0≤weightedFamily (localWords S i u) t ∧
    weightedFamily (localWords S i u) t≤(1+Real.exp (-t))^(14*S.ell^2)-1
  exact weightedFamily_bounds _ t (fun x hx => (mem_localWords S i u x).mp hx)
    (14*S.ell^2) (ownerFiber_card S i u)

theorem rz_x_factor_zero (S : OddScale) (n : ℕ) (h : (n+2)%2≠1)
    (x : (state S (n+1)).presentation.X) (t : ℝ) :
    factor S (n+2) (Vertex.x x) t=0 := by
  exact factor_empty S (n+2) (Vertex.x x)
    (ownerFiber_rz_x_empty S n h x) t

theorem rz_q_factor_zero (S : OddScale) (n : ℕ) (h : (n+2)%2≠1)
    (q : (state S (n+1)).presentation.Q) (t : ℝ) :
    factor S (n+2) (Vertex.q q) t=0 := by
  exact factor_empty S (n+2) (Vertex.q q)
    (ownerFiber_rz_q_empty S n h q) t

/-- Finite Cartesian distributivity on dependent full original-carrier words. -/
theorem product_cartesian (S : OddScale) (depth : ℕ)
    (T : Finset (decodingGraph S depth).Node) (t : ℝ) :
    (∏ v ∈ T, factor S v.1.val v.2 t) =
      ∑ x : (∀ v : T, {w : Word Bit (OwnerFiber S v.val.1.val v.val.2) // w≠0}),
        Real.exp (-t*(∑ v : T,
          (HammingWeight (extend S v.val.1.val v.val.2 (x v).val) : ℝ))) := by
  have hprod : (∏ v ∈ T, factor S v.1.val v.2 t) =
      ∏ v : T, ∑ w : {w : Word Bit (OwnerFiber S v.val.1.val v.val.2) // w≠0},
        Real.exp (-t*(HammingWeight (extend S v.val.1.val v.val.2 w.val) : ℝ)) := by
    rw [← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro v hv
    unfold factor fiberFactor
    exact Finset.sum_subtype _ (fun x => mem_localWords S _ _ x) _
  rw [hprod,Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

abbrev Node (S : OddScale) (depth : ℕ) := (decodingGraph S depth).Node

def structural (S : OddScale) (depth : ℕ) : Finset (Node S depth) :=
  Finset.univ.filter (fun v => v.1.val<2)

def slice (S : OddScale) (depth : ℕ) (i : LevelIndex depth) : Finset (Node S depth) :=
  Finset.univ.filter (fun v => v.1=i)

private def sliceEquiv (S : OddScale) (depth : ℕ) (i : LevelIndex depth) :
    {v : Node S depth // v.1=i} ≃ GraphVertex S i.val where
  toFun := fun v => v.property ▸ v.val.2
  invFun := fun w => ⟨⟨i,w⟩,rfl⟩
  left_inv := by rintro ⟨⟨j,w⟩,h⟩; cases h; rfl
  right_inv := by intro w; rfl

theorem slice_card (S : OddScale) (depth : ℕ) (i : LevelIndex depth) :
    (slice S depth i).card = Fintype.card (GraphVertex S i.val) := by
  simpa only [slice,Fintype.card_subtype] using Fintype.card_congr (sliceEquiv S depth i)

theorem structural_zero_card (S : OddScale) : (structural S 0).card=1 := by
  have he : structural S 0=slice S 0 ⟨0,by omega⟩ := by
    ext v
    simp only [structural,slice,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro h; apply Fin.ext; have hi := v.1.isLt; omega
    · intro h; have hi := congrArg Fin.val h; simp at hi; omega
  rw [he,slice_card]
  change Fintype.card Unit=1
  simp

private def vertexTags (P : TannerSquarePresentation) : Vertex P ≃ P.X ⊕ (P.Q ⊕ P.Z) where
  toFun := fun v => match v with
    | .x x => Sum.inl x
    | .q q => Sum.inr (Sum.inl q)
    | .z z => Sum.inr (Sum.inr z)
  invFun := fun v => match v with
    | .inl x => Vertex.x x
    | .inr (.inl q) => Vertex.q q
    | .inr (.inr z) => Vertex.z z
  left_inv := by intro v; cases v <;> rfl
  right_inv := by rintro (x | (q | z)) <;> rfl

theorem structural_positive_card (S : OddScale) (depth : ℕ) (hd : 0<depth) :
    (structural S depth).card=10 := by
  let i0 : LevelIndex depth := ⟨0,by omega⟩
  let i1 : LevelIndex depth := ⟨1,by omega⟩
  have he : structural S depth=slice S depth i0 ∪ slice S depth i1 := by
    ext v
    simp only [structural,slice,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
    constructor
    · intro h
      have hv := v.1.isLt
      by_cases hz : v.1.val=0
      · exact Or.inl (Fin.ext hz)
      · exact Or.inr (Fin.ext (by dsimp [i1]; omega))
    · rintro (h|h)
      all_goals have hi := congrArg Fin.val h; dsimp [i0,i1] at hi; omega
  have hdis : Disjoint (slice S depth i0) (slice S depth i1) := by
    apply Finset.disjoint_left.mpr
    intro v h0 h1
    have e0 := (Finset.mem_filter.mp h0).2
    have e1 := (Finset.mem_filter.mp h1).2
    have h := congrArg Fin.val (e0.symm.trans e1)
    norm_num [i0,i1] at h
  rw [he,Finset.card_union_of_disjoint hdis,slice_card,slice_card]
  change Fintype.card Unit+Fintype.card (Vertex baseState.presentation)=10
  rw [Fintype.card_congr (vertexTags baseState.presentation)]
  have hx : Fintype.card baseState.presentation.X=2 := by
    change Fintype.card (Fin 2)=2
    exact Fintype.card_fin 2
  have hq : Fintype.card baseState.presentation.Q=5 := by
    change Fintype.card (Fin 5)=5
    exact Fintype.card_fin 5
  have hz : Fintype.card baseState.presentation.Z=2 := by
    change Fintype.card (Fin 2)=2
    exact Fintype.card_fin 2
  norm_num only [Fintype.card_unit,Fintype.card_sum,hx,hq,hz]

theorem anchors_disjoint (S : OddScale) (depth : ℕ) :
    Disjoint (BDL26ConnectedSetCounting.levelTwoAnchors S depth) (structural S depth) := by
  apply Finset.disjoint_left.mpr
  intro v ha hb
  have he := (BDL26ConnectedSetCounting.mem_levelTwoAnchors S depth v).mp ha
  have hl := (Finset.mem_filter.mp hb).2
  omega

/-- The complete actual graph remains unchanged. -/
def actualMass (S : OddScale) (depth m : ℕ) (t : ℝ) : ℝ :=
  QEC.Locality.WeightedConnectedSetMass.occupiedMass (BDL26ConnectedSetCounting.graph S depth)
    (BDL26ConnectedSetCounting.levelTwoAnchors S depth) (structural S depth) m
    (fun v => factor S v.1.val v.2 t)

theorem actual_zero (S : OddScale) (depth : ℕ) (t : ℝ) : actualMass S depth 0 t=0 :=
  QEC.Locality.WeightedConnectedSetMass.occupied_zero _ _ _ _

theorem actual_shallow (S : OddScale) (depth m : ℕ) (hd : depth<2) (t : ℝ) :
    actualMass S depth m t=0 := by
  unfold actualMass
  rw [BDL26ConnectedSetCounting.levelTwoAnchors_empty S depth hd]
  exact QEC.Locality.WeightedConnectedSetMass.occupied_empty _ _ _ _

theorem actual_one (S : OddScale) (depth : ℕ) (t : ℝ) :
    actualMass S depth 1 t=∑ v ∈ BDL26ConnectedSetCounting.levelTwoAnchors S depth,
      factor S v.1.val v.2 t :=
  QEC.Locality.WeightedConnectedSetMass.occupied_one _ _ _ (anchors_disjoint S depth) _

/-- Complete occupied-owner Cartesian mass, without global syndrome coherence. -/
theorem actual_cartesian (S : OddScale) (depth m : ℕ) (t : ℝ) :
    actualMass S depth m t=
      ∑ K ∈ BDL26ConnectedSetCounting.levelTwoSets S depth m,
        ∑ x : (∀ v : (show Finset (Node S depth) from K \ structural S depth),
          {w : Word Bit (OwnerFiber S v.val.1.val v.val.2) // w≠0}),
          Real.exp (-t*(∑ v : (show Finset (Node S depth) from K \ structural S depth),
            (HammingWeight (extend S v.val.1.val v.val.2 (x v).val) : ℝ))) := by
  unfold actualMass QEC.Locality.WeightedConnectedSetMass.occupiedMass
  apply Finset.sum_congr rfl
  intro K hK
  exact product_cartesian S depth (K \ structural S depth) t

/-- All-real-t actual polynomial envelope, without smallness. -/
theorem actual_polynomial (S : OddScale) (depth m : ℕ) (t : ℝ) :
    0≤actualMass S depth m t ∧ actualMass S depth m t≤
      ((BDL26ConnectedSetCounting.levelTwoAnchors S depth).card : ℝ)*
        (alphabet S*(1+envelope S t))^m :=
  QEC.Locality.WeightedConnectedSetMass.occupied_polynomial _ _ (BDL26ConnectedSetCounting.graph_degree_bound S depth)
    _ _ m _ _ (envelope_nonneg S t)
    (fun v => (factor_bounds S v.1.val v.2 t).1)
    (fun v => (factor_bounds S v.1.val v.2 t).2)

theorem actual_interval_polynomial (S : OddScale) (depth L U : ℕ) (t : ℝ) :
    QEC.Locality.WeightedConnectedSetMass.interval (fun m => actualMass S depth m t) L U ≤
      ((BDL26ConnectedSetCounting.levelTwoAnchors S depth).card : ℝ)*
        QEC.Locality.WeightedConnectedSetMass.geometric (alphabet S*(1+envelope S t)) (max 1 L) (U+1-max 1 L) := by
  calc
    _ ≤ QEC.Locality.WeightedConnectedSetMass.interval (fun m =>
      ((BDL26ConnectedSetCounting.levelTwoAnchors S depth).card : ℝ)*
        (alphabet S*(1+envelope S t))^m) L U :=
      QEC.Locality.WeightedConnectedSetMass.interval_mono _ _ L U (fun m _ => (actual_polynomial S depth m t).2)
    _ = _ := by simp only [QEC.Locality.WeightedConnectedSetMass.interval,QEC.Locality.WeightedConnectedSetMass.geometric,Finset.mul_sum]

theorem actual_strong (S : OddScale) (depth m : ℕ) (t : ℝ) (hq : ratio S t<1) :
    actualMass S depth m t≤
      ((BDL26ConnectedSetCounting.levelTwoAnchors S depth).card : ℝ)*alphabet S^m*
        envelope S t^(max 1 (m-(structural S depth).card)) :=
  QEC.Locality.WeightedConnectedSetMass.occupied_strong _ _ (BDL26ConnectedSetCounting.graph_degree_bound S depth)
    _ _ (anchors_disjoint S depth) m _ _ (envelope_nonneg S t)
    (fun v => (factor_bounds S v.1.val v.2 t).1)
    (fun v => (factor_bounds S v.1.val v.2 t).2) hq

theorem actual_prefix_tail (S : OddScale) (depth L U : ℕ) (t : ℝ) (hq : ratio S t<1) :
    QEC.Locality.WeightedConnectedSetMass.interval (fun m => actualMass S depth m t) L U≤
      ((BDL26ConnectedSetCounting.levelTwoAnchors S depth).card : ℝ)*
        QEC.Locality.WeightedConnectedSetMass.structuralEnvelope (alphabet S) (envelope S t) (structural S depth).card L U :=
  QEC.Locality.WeightedConnectedSetMass.occupied_interval_strong _ _ (BDL26ConnectedSetCounting.graph_degree_bound S depth)
    _ _ (anchors_disjoint S depth) _ _ (envelope_nonneg S t)
    (fun v => (factor_bounds S v.1.val v.2 t).1)
    (fun v => (factor_bounds S v.1.val v.2 t).2) hq L U

theorem actual_shifted_tail (S : OddScale) (depth L U : ℕ) (hd : 2≤depth)
    (t : ℝ) (hq : ratio S t<1) (hL : 11≤L) :
    QEC.Locality.WeightedConnectedSetMass.interval (fun m => actualMass S depth m t) L U≤
      ((BDL26ConnectedSetCounting.levelTwoAnchors S depth).card : ℝ)*
        alphabet S^10*ratio S t^(L-10)/(1-ratio S t) := by
  have hc := structural_positive_card S depth (by omega)
  have h := QEC.Locality.WeightedConnectedSetMass.occupied_shifted_tail _ _ (BDL26ConnectedSetCounting.graph_degree_bound S depth)
    (BDL26ConnectedSetCounting.levelTwoAnchors S depth) (structural S depth)
    (anchors_disjoint S depth) _ _ (envelope_nonneg S t)
    (fun v => (factor_bounds S v.1.val v.2 t).1)
    (fun v => (factor_bounds S v.1.val v.2 t).2) hq L U (by omega) (by omega)
  simpa only [hc,actualMass,alphabet,ratio] using h

theorem actual_half_tail (S : OddScale) (depth L U : ℕ) (hd : 2≤depth)
    (t : ℝ) (hq : ratio S t≤1/2) (hL : 11≤L) :
    QEC.Locality.WeightedConnectedSetMass.interval (fun m => actualMass S depth m t) L U≤
      2*((BDL26ConnectedSetCounting.levelTwoAnchors S depth).card : ℝ)*
        alphabet S^10*ratio S t^(L-10) := by
  have ht := actual_shifted_tail S depth L U hd t (by linarith) hL
  have h0 : 0≤ratio S t := mul_nonneg
    (by unfold alphabet; linarith [QEC.Locality.WeightedConnectedSetMass.alpha_one_le (14*S.ell^2+8)]) (envelope_nonneg S t)
  have hα : (0 : ℝ) ≤ alphabet S := by
    unfold alphabet
    exact le_trans (by norm_num) (QEC.Locality.WeightedConnectedSetMass.alpha_one_le _)
  have hp : 0≤((BDL26ConnectedSetCounting.levelTwoAnchors S depth).card : ℝ)*
      alphabet S^10*ratio S t^(L-10) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hα _)) (pow_nonneg h0 _)
  have hden : 0<1-ratio S t := by linarith
  exact ht.trans ((div_le_iff₀ hden).mpr (by
    nlinarith [mul_nonneg hp (show 0≤1-2*ratio S t by linarith)]))

/-- The original beta/4 substitution retains precisely the same smallness domain. -/
theorem source_shifted_tail (S : OddScale) (depth L U : ℕ) (hd : 2≤depth)
    (beta : ℝ) (hq : ratio S (beta/4)<1) (hL : 11≤L) :
    QEC.Locality.WeightedConnectedSetMass.interval (fun m => actualMass S depth m (beta/4)) L U≤
      ((BDL26ConnectedSetCounting.levelTwoAnchors S depth).card : ℝ)*
        alphabet S^10*ratio S (beta/4)^(L-10)/(1-ratio S (beta/4)) :=
  actual_shifted_tail S depth L U hd (beta/4) hq hL

end QEC.Coding.BDL26ConnectedSyndromeMass
