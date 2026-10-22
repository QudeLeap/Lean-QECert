import QEC.Coding.FiniteAlternatingConstruction.LevelTwoDecoder
import QEC.Coding.FiniteAlternatingConstruction.RZPhysicalXStarTransport
import Mathlib.Tactic

/-!
# Old-X-star endpoints on both original local-search branches

Internal, project-derived refinement of BDL26 v1 paper.tex:3404–3484
(SHA256 66d1927b20efccb757da40af3d291e4738c60054799812393e0a739abcc73e5b).
The full preceding X cylinder and its neighboring Q cylinders have relative
H1 zero with two stray coordinates. Both literal original first searches
supply the two actual corrections. The final potential retains the old-X
copy-zero lift, every Q-edge filling and every remaining Z-face filling.
No fallback, history reachability, stability or lifetime theorem is asserted.
-/
noncomputable section
namespace QEC.Coding.BDL26LevelTwoOldXStarEndpoint

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder BDL26DecodingGraph
open scoped Classical BigOperators

abbrev F := BDL26FiniteTannerSquare.Field
abbrev Seed := baseTannerSquarePresentation
abbrev P (S : OddScale) := levelOnePresentation S
abbrev C (S : OddScale) := levelTwoPresentation S
abbrev W1 (S : OddScale) := Word F (RX1 Seed S)
abbrev V1 (S : OddScale) := Word F (RX0 Seed S)

/-- The entire distinguished X cylinder and all adjacent entire Q cylinders. -/
def Neighborhood (S : OddScale) (x : BaseX) : Finset (RX1 Seed S) :=
  Finset.univ.filter fun q => match q with
    | .inl e => e.1 = x
    | .inr v => Seed.xq x v.1 = true

@[simp] theorem mem_neighborhood_edge (S : OddScale) (x y : BaseX)
    (e : DoubleCylinderEdge Seed y S) :
    Sum.inl ⟨y,e⟩ ∈ Neighborhood S x ↔ y=x := by
  simp [Neighborhood]
  rfl

@[simp] theorem mem_neighborhood_q (S : OddScale) (x : BaseX) (q : BaseQubit)
    (v : QDoubleCylinderVertex Seed q S) :
    Sum.inr ⟨q,v⟩ ∈ Neighborhood S x ↔ Seed.xq x q=true := by simp [Neighborhood]

/-- Every actual first-level physical X star lies in the declared neighborhood. -/
theorem physical_star_subset (S : OddScale) (x : (P S).X) :
    BDL26RXPhysicalStarTransport.physicalXStar (P S) x ⊆ Neighborhood S x.1 := by
  intro r hr
  have hi := (BDL26RXPhysicalStarTransport.mem_physicalXStar (P S) x r).mp hr
  change rxXQIncidence Seed S x r=true at hi
  rcases r with e | ⟨q,v⟩
  · exact (mem_neighborhood_edge S x.1 e.1 e.2).mpr
      (BDL26RXPhysicalStarTransport.raw_local_edge_owner Seed S x e hi).symm
  · exact (mem_neighborhood_q S x.1 q v).mpr
      (BDL26RXPhysicalStarTransport.raw_q_vertex_owner Seed S x q v hi)

/-- Full global mask; no global cocycle assertion about this mask is made. -/
def outsideMask (S : OddScale) (y : BaseX) (w : W1 S) : W1 S := fun r =>
  match r with
  | .inl e => if e.1=y then w r else 0
  | .inr _ => 0

@[simp] theorem outsideMask_read (S : OddScale) (y : BaseX) (w : W1 S)
    (e : DoubleCylinderEdge Seed y S) :
    outsideMask S y w (Sum.inl ⟨y,e⟩)=w (Sum.inl ⟨y,e⟩) := by
  simp [outsideMask]
  intro h
  exact (h rfl).elim

/-- The masked word, not the original neighborhood-supported word, has global
support in the two extra coordinates. Duplicates and missing labels are allowed. -/
theorem outsideMask_support (S : OddScale) (x y : BaseX) (hy : y≠x)
    (w : W1 S) (a b : RX1 Seed S)
    (hw : ∀ r, w r≠0 → r∈Neighborhood S x ∨ r=a ∨ r=b) :
    ∀ r, outsideMask S y w r≠0 → r=a ∨ r=b := by
  intro r hr
  rcases r with ⟨z,e⟩ | v
  · by_cases hzy : z=y
    · subst z
      have hn : w (Sum.inl ⟨y,e⟩)≠0 := by simpa using hr
      rcases hw _ hn with hN | ha | hb
      · exact False.elim (hy ((mem_neighborhood_edge S x y e).mp hN))
      · exact Or.inl ha
      · exact Or.inr hb
    · exact False.elim (hr (by simp [outsideMask,hzy]))
  · exact False.elim (hr rfl)

/-- The original cocycle supplies LOCAL face closedness of the mask. -/
theorem outsideMask_local_closed (S : OddScale) (y : BaseX) (w : W1 S)
    (hc : rxCoboundary1 Seed S w=0) :
    wordLinearMapTranspose (doubleCylinderBoundary2 Seed y S)
      (fun e => outsideMask S y w (Sum.inl ⟨y,e⟩))=0 := by
  funext face
  simp only [outsideMask_read]
  rw [← rxCoboundary1_localFace Seed S w y face,hc]
  rfl

/-- Nonzero distinct actual seed columns kill each outside cylinder. -/
theorem outside_edges_zero (S : OddScale) (x y : BaseX) (hy : y≠x)
    (w : W1 S) (hc : rxCoboundary1 Seed S w=0) (a b : RX1 Seed S)
    (hw : ∀ r, w r≠0 → r∈Neighborhood S x ∨ r=a ∨ r=b)
    (e : DoubleCylinderEdge Seed y S) : w (Sum.inl ⟨y,e⟩)=0 := by
  have hm := binary_two_coordinate_matrix_restriction_eq_zero
    (fun f : DoubleCylinderEdge Seed y S => (Sum.inl ⟨y,f⟩ : RX1 Seed S))
    (by
      intro f g h
      exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inl.inj h)).2)
    (doubleCylinderFaceEdgeMatrix Seed y S)
    (BDL26RXSeedSmallSupport.seed_local_column_nonzero S y)
    (BDL26RXSeedSmallSupport.seed_local_column_injective S y)
    (outsideMask S y w) (outsideMask_local_closed S y w hc) a b
    (outsideMask_support S x y hy w a b hw)
  simpa using congrFun hm e

/-- Extend one genuine local vertex potential by zero to ALL actual X vertices. -/
def localLift (S : OddScale) (x : BaseX)
    (f : Word F (DoubleCylinderVertex Seed x S)) : V1 S := fun u =>
  if h : u.1=x then f (h ▸ u.2) else 0

@[simp] theorem localLift_same (S : OddScale) (x : BaseX)
    (f : Word F (DoubleCylinderVertex Seed x S)) (v : DoubleCylinderVertex Seed x S) :
    localLift S x f ⟨x,v⟩=f v := by
  simp [localLift]
  intro h
  exact (h rfl).elim

@[simp] theorem localLift_other (S : OddScale) (x y : BaseX) (hy : y≠x)
    (f : Word F (DoubleCylinderVertex Seed x S)) (v : DoubleCylinderVertex Seed y S) :
    localLift S x f ⟨y,v⟩=0 := by
  simp [localLift]
  intro h
  exact (hy h).elim

theorem localLift_edge_same (S : OddScale) (x : BaseX)
    (f : Word F (DoubleCylinderVertex Seed x S)) (e : DoubleCylinderEdge Seed x S) :
    rxCoboundary0 Seed S (localLift S x f) (Sum.inl ⟨x,e⟩)=
      wordLinearMapTranspose (rxCx Seed x S).boundary1 f e := by
  exact (rxCoboundary0_localEdge Seed S (localLift S x f) x e).trans
    (congrArg (fun g : Word F (DoubleCylinderVertex Seed x S) =>
      wordLinearMapTranspose (rxCx Seed x S).boundary1 g e)
      (funext (localLift_same S x f)))

theorem localLift_edge_other (S : OddScale) (x y : BaseX) (hy : y≠x)
    (f : Word F (DoubleCylinderVertex Seed x S)) (e : DoubleCylinderEdge Seed y S) :
    rxCoboundary0 Seed S (localLift S x f) (Sum.inl ⟨y,e⟩)=0 := by
  have hz : (fun v : DoubleCylinderVertex Seed y S => localLift S x f ⟨y,v⟩)=0 :=
    funext (localLift_other S x y hy f)
  calc
    rxCoboundary0 Seed S (localLift S x f) (Sum.inl ⟨y,e⟩) =
        wordLinearMapTranspose (rxCx Seed y S).boundary1
          (fun v => localLift S x f ⟨y,v⟩) e :=
      rxCoboundary0_localEdge Seed S (localLift S x f) y e
    _ = wordLinearMapTranspose (rxCx Seed y S).boundary1 0 e :=
      congrArg (fun g : Word F (DoubleCylinderVertex Seed y S) =>
        wordLinearMapTranspose (rxCx Seed y S).boundary1 g e) hz
    _ = 0 := congrFun (map_zero (wordLinearMapTranspose (rxCx Seed y S).boundary1)) e

/-- Connecting terms are retained; they vanish outside the actual neighbor set. -/
theorem localLift_q_outside (S : OddScale) (x : BaseX)
    (f : Word F (DoubleCylinderVertex Seed x S)) (q : BaseQubit)
    (hq : Seed.xq x q≠true) (v : QDoubleCylinderVertex Seed q S) :
    rxCoboundary0 Seed S (localLift S x f) (Sum.inr ⟨q,v⟩)=0 := by
  classical
  unfold rxCoboundary0 rxBoundary1
  rw [wordLinearMapTranspose_toLin'_apply,Fintype.sum_sigma]
  apply Finset.sum_eq_zero
  intro y _
  apply Finset.sum_eq_zero
  intro u _
  by_cases hy : y=x
  · subst y
    simp [rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,
      qSubdivisionVertexXIncidence,hq]
  · simp [localLift,hy]

/-- Raw coboundaries square to zero by the ACTUAL Tanner presentation. -/
theorem rx_squared (S : OddScale) (u : V1 S) :
    rxCoboundary1 Seed S (rxCoboundary0 Seed S u)=0 := by
  have h := LinearMap.congr_fun (tannerCoboundary_squared (P S)) u
  change tannerCoboundary1 (rxReplacementPresentation Seed S)
    (tannerCoboundary0 (rxReplacementPresentation Seed S) u)=0 at h
  rw [rxPresentation_coboundary0_eq Seed baseTannerSquareAdmissibleV4
    baseTannerSquareCellularRegular S,
    rxPresentation_coboundary1_eq Seed baseTannerSquareAdmissibleV4
    baseTannerSquareCellularRegular S] at h
  exact h

/-- Extract the distinguished cylinder potential from proved local H1=0. -/
theorem local_potential (S : OddScale) (x : BaseX) (w : W1 S)
    (hc : rxCoboundary1 Seed S w=0) :
    ∃ f : Word F (DoubleCylinderVertex Seed x S),
      wordLinearMapTranspose (rxCx Seed x S).boundary1 f=
        fun e => w (Sum.inl ⟨x,e⟩) := by
  have hc' : wordLinearMapTranspose (rxCx Seed x S).boundary2
      (fun e => w (Sum.inl ⟨x,e⟩))=0 := by
    funext face
    exact (rxCoboundary1_localFace Seed S w x face).symm.trans
      (congrFun hc (Sum.inl (Sum.inl ⟨x,face⟩)))
  have hm := ((rxCx Seed x S).mem_middleCocycleCode_iff _).mpr hc'
  rw [← xCylinder_coboundary_eq_cocycle Seed baseTannerSquareAdmissibleV4.toTannerSquareAdmissibleV3
    baseTannerSquareCellularRegular x S] at hm
  exact ((rxCx Seed x S).mem_firstCoboundaryCheckCode_iff _).mp hm

private theorem three_not_two {I : Type} (u v w a b : I)
    (huv : u≠v) (huw : u≠w) (hvw : v≠w)
    (hu : u=a ∨ u=b) (hv : v=a ∨ v=b) (hw : w=a ∨ w=b) : False := by
  rcases hu with hu | hu <;> rcases hv with hv | hv <;> rcases hw with hw | hw
  all_goals aesop

/-- Three literal vertices kill the remaining two-coordinate spill at half1 too. -/
theorem outside_q_zero (S : OddScale) (x : BaseX) (w : W1 S)
    (hc : rxCoboundary1 Seed S w=0)
    (hx : ∀ y e, w (Sum.inl ⟨y,e⟩)=0) (a b : RX1 Seed S)
    (hw : ∀ r, w r≠0 → r∈Neighborhood S x ∨ r=a ∨ r=b)
    (q : BaseQubit) (hq : Seed.xq x q≠true)
    (v : QDoubleCylinderVertex Seed q S) : w (Sum.inr ⟨q,v⟩)=0 := by
  rw [rxCocycle_q_constant_of_local_zero Seed baseTannerSquareAdmissible S w hc hx q v]
  by_contra hn
  let v1 : RX1 Seed S := Sum.inr ⟨q,(0,Sum.inl (Sum.inl ()))⟩
  let v2 : RX1 Seed S := Sum.inr ⟨q,(1,Sum.inl (Sum.inl ()))⟩
  let v3 : RX1 Seed S := Sum.inr ⟨q,(0,Sum.inl (Sum.inr (baseTannerSquareAdmissible.qzRoot q)))⟩
  have hnon : ∀ z : QDoubleCylinderVertex Seed q S, w (Sum.inr ⟨q,z⟩)≠0 := by
    intro z
    rw [rxCocycle_q_constant_of_local_zero Seed baseTannerSquareAdmissible S w hc hx q z]
    exact hn
  have hs : ∀ z : QDoubleCylinderVertex Seed q S,
      (Sum.inr ⟨q,z⟩ : RX1 Seed S)=a ∨ Sum.inr ⟨q,z⟩=b := by
    intro z
    rcases hw _ (hnon z) with hN | ha | hb
    · exact False.elim (hq ((mem_neighborhood_q S x q z).mp hN))
    · exact Or.inl ha
    · exact Or.inr hb
  have h12 : v1≠v2 := by
    intro h
    have h' := eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h)).2
    exact (by decide : (0 : BDL26FiniteTannerSquare.Two)≠1) (congrArg Prod.fst h')
  have h13 : v1≠v3 := by
    intro h
    have h' := eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h)).2
    have h'' := Sum.inl.inj (congrArg Prod.snd h')
    cases h''
  have h23 : v2≠v3 := by
    intro h
    have h' := eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h)).2
    exact (by decide : (1 : BDL26FiniteTannerSquare.Two)≠0) (congrArg Prod.fst h')
  exact three_not_two v1 v2 v3 a b h12 h13 h23 (hs _) (hs _) (hs _)

/-- Both complete seed cases; the remaining fifth coefficient is retained. -/
theorem seed_relative_potential (x : BaseX) (k : Word F BaseQubit)
    (hc : tannerCoboundary1 Seed k=0)
    (hk : ∀ q, Seed.xq x q≠true → k q=0) :
    tannerCoboundary0 Seed (k 4 • canonicalBasisWord x)=k := by
  have h0 := congrFun hc (0 : BaseZ)
  have h1 := congrFun hc (1 : BaseZ)
  change (∑ q : BaseQubit, k q * (if Seed.qz q (0 : BaseZ)=true then 1 else 0))=0 at h0
  change (∑ q : BaseQubit, k q * (if Seed.qz q (1 : BaseZ)=true then 1 else 0))=0 at h1
  simp [Seed,TannerSquarePresentation.qz,baseTannerSquarePresentation,baseTannerSquareData,
    baseBoundary2Matrix,Fin.sum_univ_succ] at h0 h1
  have heval : ∀ (x : BaseX) (q : BaseQubit),
      tannerCoboundary0 Seed (k 4 • canonicalBasisWord x) q=
        k 4 * (if Seed.xq x q=true then 1 else 0) := by
    intro x q
    calc
      tannerCoboundary0 Seed (k 4 • canonicalBasisWord x) q =
          (k 4 • tannerCoboundary0 Seed (canonicalBasisWord x)) q :=
        congrFun ((tannerCoboundary0 Seed).map_smul (k 4) (canonicalBasisWord x)) q
      _ = k 4 * (if Seed.xq x q=true then 1 else 0) :=
        congrArg (fun z : F => k 4 * z) (tannerCoboundary0_canonicalBasis_apply Seed x q)
  fin_cases x
  · have h2 := hk (2 : BaseQubit) (by decide)
    have h3 := hk (3 : BaseQubit) (by decide)
    have h02 : k 0=k 4 := by
      have he := congrArg (fun z : F => z+k 4) h0
      simpa [h2,add_assoc,ZModModule.add_self] using he
    have h14 : k 1=k 4 := by
      have he := congrArg (fun z : F => z+k 4) h1
      simpa [h3,add_assoc,ZModModule.add_self] using he
    funext q
    fin_cases q <;> rw [heval] <;>
      simp [Seed,TannerSquarePresentation.xq,baseTannerSquarePresentation,baseTannerSquareData,baseBoundary1Matrix,
        h02,h14,h2,h3]
  · have h0' := hk (0 : BaseQubit) (by decide)
    have h1' := hk (1 : BaseQubit) (by decide)
    have h24 : k 2=k 4 := by
      have he := congrArg (fun z : F => z+k 4) h0
      simpa [h0',add_assoc,ZModModule.add_self] using he
    have h34 : k 3=k 4 := by
      have he := congrArg (fun z : F => z+k 4) h1
      simpa [h1',add_assoc,ZModModule.add_self] using he
    funext q
    fin_cases q <;> rw [heval] <;>
      simp [Seed,TannerSquarePresentation.xq,baseTannerSquarePresentation,baseTannerSquareData,baseBoundary1Matrix,
        h0',h1',h24,h34]

/-- Construct relative exactness on the full neighborhood plus two coordinates. -/
theorem neighborhood_relative_exact (S : OddScale) (x : BaseX) (w : W1 S)
    (hc : rxCoboundary1 Seed S w=0) (a b : RX1 Seed S)
    (hw : ∀ r, w r≠0 → r∈Neighborhood S x ∨ r=a ∨ r=b) :
    ∃ g : V1 S, rxCoboundary0 Seed S g=w := by
  obtain ⟨f,hf⟩ := local_potential S x w hc
  let u := localLift S x f
  let w' : W1 S := w+rxCoboundary0 Seed S u
  have hc' : rxCoboundary1 Seed S w'=0 := by
    dsimp only [w']
    rw [map_add,hc,rx_squared,zero_add]
  have hx : ∀ y e, w' (Sum.inl ⟨y,e⟩)=0 := by
    intro y e
    by_cases hy : y=x
    · subst y
      change w _+rxCoboundary0 Seed S (localLift S x f) _=0
      rw [localLift_edge_same,congrFun hf e]
      exact ZModModule.add_self _
    · change w _+rxCoboundary0 Seed S (localLift S x f) _=0
      rw [outside_edges_zero S x y hy w hc a b hw e,localLift_edge_other S x y hy,zero_add]
  have hs : ∀ r, w' r≠0 → r∈Neighborhood S x ∨ r=a ∨ r=b := by
    intro r hr
    by_cases hN : r∈Neighborhood S x
    · exact Or.inl hN
    · have hz : rxCoboundary0 Seed S u r=0 := by
        rcases r with ⟨y,e⟩ | ⟨q,v⟩
        · exact localLift_edge_other S x y (fun h => hN ((mem_neighborhood_edge S x y e).mpr h)) f e
        · exact localLift_q_outside S x f q (fun h => hN ((mem_neighborhood_q S x q v).mpr h)) v
      have hn : w r≠0 := by simpa only [w',Pi.add_apply,hz,add_zero] using hr
      exact hw r hn
  let k : Word F BaseQubit := fun q => w' (Sum.inr ⟨q,(0,Sum.inl (Sum.inl ()))⟩)
  have heq : w'=rxMap1Coord Seed S k := by
    funext r
    rcases r with ⟨y,e⟩ | ⟨q,v⟩
    · exact hx y e
    · exact rxCocycle_q_constant_of_local_zero Seed baseTannerSquareAdmissible S w' hc' hx q v
  have hk : ∀ q, Seed.xq x q≠true → k q=0 := by
    intro q hq
    exact outside_q_zero S x w' hc' hx a b hs q hq _
  have hkc : tannerCoboundary1 Seed k=0 := by
    have hm := LinearMap.congr_fun (rxMap_commutes_coboundary1 Seed S) k
    change rxCoboundary1 Seed S (rxMap1Coord Seed S k)=
      rxMap2Coord Seed S (tannerCoboundary1 Seed k) at hm
    rw [← heq,hc'] at hm
    funext z
    have hz := congrFun hm (Sum.inr (z,0))
    exact hz.symm
  let v := rxMap0Coord Seed S (k 4 • canonicalBasisWord x)
  have hv : rxCoboundary0 Seed S v=w' := by
    have hm := LinearMap.congr_fun
      (rxMap_commutes_coboundary0 Seed baseTannerSquareAdmissible S)
      (k 4 • canonicalBasisWord x)
    change rxCoboundary0 Seed S v=
      rxMap1Coord Seed S (tannerCoboundary0 Seed (k 4 • canonicalBasisWord x)) at hm
    rw [seed_relative_potential x k hkc hk,← heq] at hm
    exact hm
  refine ⟨u+v,?_⟩
  rw [map_add,hv]
  change rxCoboundary0 Seed S u+(w+rxCoboundary0 Seed S u)=w
  rw [add_left_comm,ZModModule.add_self,add_zero]

/-- The same relative exactness in the literal first-level Tanner presentation. -/
theorem actual_neighborhood_relative_exact (S : OddScale) (x : BaseX)
    (w : Word F (P S).Q) (hc : tannerCoboundary1 (P S) w=0)
    (a b : (P S).Q)
    (hw : ∀ r, w r≠0 → r∈Neighborhood S x ∨ r=a ∨ r=b) :
    ∃ g : Word F (P S).X, tannerCoboundary0 (P S) g=w := by
  change tannerCoboundary1 (rxReplacementPresentation Seed S) w=0 at hc
  rw [rxPresentation_coboundary1_eq Seed baseTannerSquareAdmissibleV4
    baseTannerSquareCellularRegular S] at hc
  obtain ⟨g,hg⟩ := neighborhood_relative_exact S x w hc a b hw
  refine ⟨g,?_⟩
  change tannerCoboundary0 (rxReplacementPresentation Seed S) g=w
  rw [rxPresentation_coboundary0_eq Seed baseTannerSquareAdmissibleV4
    baseTannerSquareCellularRegular S]
  exact hg

/-- Literal original first search; all executable instance/order arguments are Main's. -/
def firstSearch (S : OddScale) (s : Word F (C S).Z) :=
  search (fun w => executableLocal S w &&
    decide (executableSyndrome S w=toExecutableSyndrome S s)) (allWords (ExecutableQ S))

/-- Both locality and syndrome of the unchanged decoder follow from the actual branch. -/
theorem firstSearch_sound (S : OddScale) (s : Word F (C S).Z)
    (w : Word F (ExecutableQ S)) (hs : firstSearch S s=some w) :
    decode S s=toActualError S w ∧ levelTwoLocalError S (decode S s) ∧
      tannerCoboundary1 (C S) (decode S s)=s := by
  have ha := (search_sound _ _ w hs).2
  have hl : executableLocal S w=true := ((Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp ha).1
  have hsyn : executableSyndrome S w=toExecutableSyndrome S s := by
    simpa using ((Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp ha).2
  have hd : decode S s=toActualError S w := by
    unfold decode executableDecode lookup
    have hs' : search (fun e => executableLocal S e &&
        decide (executableSyndrome S e=toExecutableSyndrome S s))
        (allWords (ExecutableQ S))=some w := hs
    rw [hs']
  refine ⟨hd,?_,?_⟩
  · apply (executableLocal_iff S _).mp
    rw [hd,toExecutableError_toActualError]
    exact hl
  · apply toExecutableSyndrome_injective S
    rw [← executableSyndrome_eq,hd,toExecutableError_toActualError,hsyn]

private theorem support_star_iff (B : TannerSquarePresentation)
    (qF : Fintype B.Q) (x : B.X) (h : Word F B.Q) :
    letI : Fintype B.Q := qF
    hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar B x ↔
      ∀ r, h r ≠ 0 → B.xq x r = true := by
  letI : Fintype B.Q := qF
  constructor
  · intro hs r hn
    have hm : r ∈ hammingSupport h :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
    exact (BDL26RXPhysicalStarTransport.mem_physicalXStar B x r).mp (hs hm)
  · intro hs r hr
    exact (BDL26RXPhysicalStarTransport.mem_physicalXStar B x r).mpr
      (hs r (Finset.mem_filter.mp hr).2)

/-- Capture the original raw RZ carrier instance before the actual C2 instance. -/
private def nativeRZQFintype (B : TannerSquarePresentation) (S : OddScale) :
    Fintype (RZQ B S) := inferInstance

private theorem raw_oldX_qParity_support (B : TannerSquarePresentation)
    (A : TannerSquareAdmissible B) (S : OddScale) (x : B.X)
    (c : BDL26FiniteTannerSquare.Two) (h : Word F (RZQ B S))
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar
      (rzReplacementPresentation B A S) (Sum.inr (x,c))) :
    ∀ q, rzQParity B S h q≠0 →
      q∈BDL26RXPhysicalStarTransport.physicalXStar B x := by
  intro q hq
  by_contra hN
  have hz : ∀ v : QDoubleCylinderVertex (transposePresentation B) q S,
      h (Sum.inr ⟨q,v⟩)=0 := by
    intro v
    by_contra hn
    have hi := (support_star_iff (rzReplacementPresentation B A S)
      (nativeRZQFintype B S) (Sum.inr (x,c)) h).mp hh (Sum.inr ⟨q,v⟩) hn
    change rzXQIncidence B A S
      (Sum.inr (x,c)) (Sum.inr ⟨q,v⟩)=true at hi
    have hcover := BDL26RZPhysicalXStarTransport.raw_star_cover B A S
      (Sum.inr (x,c)) (Sum.inr ⟨q,v⟩) hi
    have hqmem : q∈BDL26RXPhysicalStarTransport.physicalXStar B x :=
      (BDL26RZFiniteBlockTransport.Coordinates.mem_input_q B S _ _ q v).mp hcover
    exact hN hqmem
  apply hq
  change (∑ v : QDoubleCylinderVertex (transposePresentation B) q S,
    h (Sum.inr ⟨q,v⟩))=0
  exact Finset.sum_eq_zero (fun v _ => hz v)

/-- Compose the raw parity support with the original full seed neighborhood
before specializing the recursive second-level presentation. -/
private theorem levelOne_oldX_qParity_neighborhood (S : OddScale) (x : (P S).X)
    (c : BDL26FiniteTannerSquare.Two) (h : Word F (RZQ (P S) S))
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar
      (rzReplacementPresentation (P S)
        (rxState S baseState).admissible.toTannerSquareAdmissible S) (Sum.inr (x,c))) :
    ∀ q, rzQParity (P S) S h q≠0 → q∈Neighborhood S x.1 := by
  intro q hq
  exact physical_star_subset S x
    (raw_oldX_qParity_support (P S)
      (rxState S baseState).admissible.toTannerSquareAdmissible S x c h hh q hq)

/-- Keep the original actual carrier instance explicit during specialization. -/
local instance oldXActualQFintype (S : OddScale) : Fintype (C S).Q :=
  (C S).data.qFintype

/-- Old-X support has no auxiliary Z edges and projects to the full preceding star. -/
theorem oldX_parity_support (S : OddScale) (x : (P S).X)
    (c : BDL26FiniteTannerSquare.Two) (h : Word F (C S).Q)
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar
      (C S) (Sum.inr (x,c))) :
    ∀ q, rzQParity (P S) S h q≠0 → q∈Neighborhood S x.1 := by
  apply levelOne_oldX_qParity_neighborhood S x c h
  apply (support_star_iff
    (rzReplacementPresentation (P S)
      (rxState S baseState).admissible.toTannerSquareAdmissible S)
    (nativeRZQFintype (P S) S) (Sum.inr (x,c)) h).mpr
  intro r hr
  have hi := (support_star_iff (C S) (oldXActualQFintype S)
    (Sum.inr (x,c)) h).mp hh r hr
  change rzXQIncidence (P S)
    (rxState S baseState).admissible.toTannerSquareAdmissible S
    (Sum.inr (x,c)) r=true at hi
  exact hi

/-- The explicit section uses old-X copy0, independently of the input star copy. -/
def oldXLift (S : OddScale) (g : Word F (P S).X) : Word F (C S).X := fun u =>
  match u with
  | .inl _ => 0
  | .inr (x,c) => if c=0 then g x else 0

@[simp] theorem oldXLift_parity (S : OddScale) (g : Word F (P S).X) :
    rzOldXParity (P S) S (oldXLift S g)=g := by
  funext x
  simp [rzOldXParity,oldXLift]

/-- Rigid-carrier construction before specialization to the recursive presentation. -/
private theorem raw_zeroParity_full_filling (B : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 B) (R : TannerSquareCellularRegular B)
    (S : OddScale) (r : Word F (RZQ B S))
    (hc : rzCoboundary1 B A4 S r=0) (hp : rzQParity B S r=0) :
    ∃ (edges : ∀ q : B.Q, Word F (QDoubleCylinderEdge (transposePresentation B) q S))
      (faces : ∀ z : B.Z, Word F (ZDoubleCylinderFace B z S)),
      rzCoboundary0 B A4 S
        ((∑ q,extendRZQEdgeWord B S q (edges q))+
         (∑ z,extendRZFaceWord B S z (faces z)))=r := by
  obtain ⟨edges,he⟩ := Classical.skolem.mp
    (rzQParity_zero_has_qFillings B A4.toTannerSquareAdmissible S r hp)
  let qPot : Word F (RZX B S) := ∑ q,extendRZQEdgeWord B S q (edges q)
  have hq : ∀ q v, rzCoboundary0 B A4 S qPot
      (Sum.inr ⟨q,v⟩)=r (Sum.inr ⟨q,v⟩) := by
    intro q v
    dsimp only [qPot]
    rw [map_sum,Finset.sum_apply]
    simp only [rzQEdge_coboundary_apply_q,he]
    simpa only [Finset.sum_apply] using sum_extendRZQVertexWord_apply B S r q v
  let v : Word F (RZQ B S) := r+rzCoboundary0 B A4 S qPot
  have hvq : ∀ q u, v (Sum.inr ⟨q,u⟩)=0 := by
    intro q u
    change r _+rzCoboundary0 B A4 S qPot _=0
    rw [hq]
    exact ZModModule.add_self _
  have hvc : rzCoboundary1 B A4 S v=0 := by
    dsimp only [v]
    rw [map_add,hc,zero_add]
    exact LinearMap.congr_fun
      (tannerCoboundary_squared (rzReplacementPresentation B A4.toTannerSquareAdmissible S)) qPot
  have hf : ∀ z : B.Z, ∃ f : Word F (ZDoubleCylinderFace B z S),
      doubleCylinderBoundary2 (transposePresentation B) z S f=
        fun e => v (Sum.inl ⟨z,e⟩) := by
    intro z
    exact zCylinder_cycle_has_filling B A4.toTannerSquareAdmissibleV3 R z S _
      (rzLocal_cycle_of_cocycle_q_zero B A4 S v hvc hvq z)
  choose faces hfaces using hf
  have hzp : rzCoboundary0 B A4 S
      (∑ z,extendRZFaceWord B S z (faces z))=v := by
    rw [map_sum]
    simp only [rzCoboundary0_extendRZFaceWord,extendRZLocalEdgeWord_eq,hfaces]
    exact (rzWord_eq_sum_local_of_q_zero B S v hvq).symm
  refine ⟨edges,faces,?_⟩
  rw [map_add,hzp]
  change rzCoboundary0 B A4 S qPot+(r+rzCoboundary0 B A4 S qPot)=r
  rw [add_left_comm,ZModModule.add_self,add_zero]

/-- ALL Q-edge and ALL Z-face components of a zero-parity physical filling. -/
theorem zeroParity_full_filling (S : OddScale) (r : Word F (C S).Q)
    (hc : rzCoboundary1 (P S) (rxState S baseState).admissible S r=0)
    (hp : rzQParity (P S) S r=0) :
    ∃ (edges : ∀ q : (P S).Q, Word F (QDoubleCylinderEdge (transposePresentation (P S)) q S))
      (faces : ∀ z : (P S).Z, Word F (ZDoubleCylinderFace (P S) z S)),
      rzCoboundary0 (P S) (rxState S baseState).admissible S
        ((∑ q,extendRZQEdgeWord (P S) S q (edges q))+
         (∑ z,extendRZFaceWord (P S) S z (faces z)))=r := by
  exact raw_zeroParity_full_filling (P S)
    (show TannerSquareAdmissibleV4 (P S) from (rxState S baseState).admissible)
    (show TannerSquareCellularRegular (P S) from (rxState S baseState).regular) S r hc hp

/-- Actual-word addition is transported as a value equality, not by unfolding
recursive presentation instances inside a rewrite motive. -/
private theorem actual_parity_add (S : OddScale) (u v : Word F (C S).Q) :
    rzQParity (P S) S (u+v)=rzQParity (P S) S u+rzQParity (P S) S v := by
  exact (rzQParity (P S) S).map_add u v

private theorem actual_oldLift_boundary_parity (S : OddScale) (g : Word F (P S).X) :
    rzQParity (P S) S (tannerCoboundary0 (C S) (oldXLift S g))=
      tannerCoboundary0 (P S) g := by
  exact (rzQParity_coboundary (P S)
    (show TannerSquareAdmissibleV4 (P S) from (rxState S baseState).admissible)
    S (oldXLift S g)).trans
      (congrArg (tannerCoboundary0 (P S)) (oldXLift_parity S g))

/-- A full old-X-star word and two independently local original corrections
have a complete physical boundary potential. -/
theorem oldX_two_local_full_potential (S : OddScale) (x : (P S).X)
    (c : BDL26FiniteTannerSquare.Two) (h d e : Word F (C S).Q)
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar (C S) (Sum.inr (x,c)))
    (hd : levelTwoLocalError S d) (he : levelTwoLocalError S e)
    (hc : tannerCoboundary1 (C S) (h+d+e)=0) :
    ∃ (g : Word F (P S).X)
      (edges : ∀ q : (P S).Q, Word F (QDoubleCylinderEdge (transposePresentation (P S)) q S))
      (faces : ∀ z : (P S).Z, Word F (ZDoubleCylinderFace (P S) z S)),
      tannerCoboundary0 (C S)
        (oldXLift S g+
          (∑ q,(show Word F (C S).X from extendRZQEdgeWord (P S) S q (edges q)))+
          (∑ z,(show Word F (C S).X from extendRZFaceWord (P S) S z (faces z))))=h+d+e := by
  let r : Word F (C S).Q := h+d+e
  obtain ⟨a,b,hab⟩ := levelTwoLocalError_add_qParity_two_coordinates S (levelOneQDefault S) d e hd he
  have hpclosed := rzQParity_cocycle (P S) (rxState S baseState).admissible S r hc
  have hsupport : ∀ q, rzQParity (P S) S r q≠0 → q∈Neighborhood S x.1 ∨ q=a ∨ q=b := by
    intro q hq
    by_cases hN : q∈Neighborhood S x.1
    · exact Or.inl hN
    · have hz : rzQParity (P S) S h q=0 := by
        by_contra hn
        exact hN (oldX_parity_support S x c h hh q hn)
      have hsum : r=h+(d+e) := by dsimp only [r]; abel
      have hn : rzQParity (P S) S (d+e) q≠0 := by
        have hvalue : rzQParity (P S) S r q=rzQParity (P S) S (d+e) q := by
          calc
            rzQParity (P S) S r q = rzQParity (P S) S (h+(d+e)) q :=
              congrArg (fun w : Word F (C S).Q => rzQParity (P S) S w q) hsum
            _ = rzQParity (P S) S h q+rzQParity (P S) S (d+e) q :=
              congrFun (actual_parity_add S h (d+e)) q
            _ = 0+rzQParity (P S) S (d+e) q :=
              congrArg (fun z : F => z+rzQParity (P S) S (d+e) q) hz
            _ = rzQParity (P S) S (d+e) q := zero_add _
        exact fun hzero => hq (hvalue.trans hzero)
      exact Or.inr (hab q hn)
  obtain ⟨g,hg⟩ := actual_neighborhood_relative_exact S x.1 _ hpclosed a b hsupport
  let G := oldXLift S g
  let v := r+tannerCoboundary0 (C S) G
  have hvc : rzCoboundary1 (P S) (rxState S baseState).admissible S v=0 := by
    have hactual : tannerCoboundary1 (C S) v=0 := by
      dsimp only [v]
      rw [map_add,hc,zero_add]
      exact LinearMap.congr_fun (tannerCoboundary_squared (C S)) G
    exact hactual
  have hG : rzQParity (P S) S (tannerCoboundary0 (C S) G)=
      tannerCoboundary0 (P S) g := by
    exact actual_oldLift_boundary_parity S g
  have hvp : rzQParity (P S) S v=0 := by
    calc
      rzQParity (P S) S v =
          rzQParity (P S) S r+rzQParity (P S) S (tannerCoboundary0 (C S) G) :=
        actual_parity_add S r (tannerCoboundary0 (C S) G)
      _ = rzQParity (P S) S r+tannerCoboundary0 (P S) g :=
        congrArg (fun w : Word F (P S).Q => rzQParity (P S) S r+w) hG
      _ = rzQParity (P S) S r+rzQParity (P S) S r :=
        congrArg (fun w : Word F (P S).Q => rzQParity (P S) S r+w) hg
      _ = 0 := ZModModule.add_self _
  obtain ⟨edges,faces,hf⟩ := zeroParity_full_filling S v hvc hvp
  have hf' : tannerCoboundary0 (C S)
      ((∑ q,(show Word F (C S).X from extendRZQEdgeWord (P S) S q (edges q)))+
       (∑ z,(show Word F (C S).X from extendRZFaceWord (P S) S z (faces z))))=v := hf
  refine ⟨g,edges,faces,?_⟩
  let Q : Word F (C S).X :=
    ∑ q,(show Word F (C S).X from extendRZQEdgeWord (P S) S q (edges q))
  let Z : Word F (C S).X :=
    ∑ z,(show Word F (C S).X from extendRZFaceWord (P S) S z (faces z))
  calc
    tannerCoboundary0 (C S) (G+Q+Z) = tannerCoboundary0 (C S) (G+(Q+Z)) :=
      congrArg (tannerCoboundary0 (C S)) (add_assoc G Q Z)
    _ = tannerCoboundary0 (C S) G+tannerCoboundary0 (C S) (Q+Z) :=
      (tannerCoboundary0 (C S)).map_add G (Q+Z)
    _ = tannerCoboundary0 (C S) G+v :=
      congrArg (fun w : Word F (C S).Q => tannerCoboundary0 (C S) G+w) hf'
    _ = r := by
      change tannerCoboundary0 (C S) G+(r+tannerCoboundary0 (C S) G)=r
      rw [add_left_comm,ZModModule.add_self,add_zero]

/-- Exact original two-search endpoint for arbitrary raw, possibly nonzero,
syndromes. No range certificate, earlier-zero convention or linearity is used. -/
theorem oldX_two_search_endpoint (S : OddScale) (x : (P S).X)
    (c : BDL26FiniteTannerSquare.Two) (h : Word F (C S).Q)
    (s t : Word F (C S).Z) (ws wt : Word F (ExecutableQ S))
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar (C S) (Sum.inr (x,c)))
    (hsyn : tannerCoboundary1 (C S) h=s+t)
    (hs : firstSearch S s=some ws) (ht : firstSearch S t=some wt) :
    ∃ p : Word F (C S).X, tannerCoboundary0 (C S) p=h+decode S s+decode S t := by
  have hds := firstSearch_sound S s ws hs
  have hdt := firstSearch_sound S t wt ht
  have hc : tannerCoboundary1 (C S) (h+decode S s+decode S t)=0 := by
    rw [map_add,map_add,hsyn,hds.2.2,hdt.2.2]
    calc
      s+t+s+t=(s+s)+(t+t) := by abel
      _=0 := by rw [ZModModule.add_self,ZModModule.add_self,add_zero]
  obtain ⟨g,edges,faces,hp⟩ := oldX_two_local_full_potential S x c h _ _ hh hds.2.1 hdt.2.1 hc
  exact ⟨_,hp⟩

/-- The original arbitrary background is preserved in BOTH actual decoder calls. -/
theorem oldX_background_endpoint (S : OddScale) (x : (P S).X)
    (c : BDL26FiniteTannerSquare.Two) (a h : Word F (C S).Q)
    (ws wt : Word F (ExecutableQ S))
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar (C S) (Sum.inr (x,c)))
    (hs : firstSearch S (tannerCoboundary1 (C S) a)=some ws)
    (ht : firstSearch S (tannerCoboundary1 (C S) (a+h))=some wt) :
    ∃ p : Word F (C S).X, tannerCoboundary0 (C S) p=
      h+decode S (tannerCoboundary1 (C S) a)+decode S (tannerCoboundary1 (C S) (a+h)) := by
  apply oldX_two_search_endpoint S x c h _ _ ws wt hh _ hs ht
  rw [map_add,← add_assoc,ZModModule.add_self,zero_add]

/-- Repeated nonzero input cancellation uses only determinism, not D-linearity. -/
theorem repeated_correction_cancel (S : OddScale) (s : Word F (C S).Z) :
    decode S s+decode S s=0 := ZModModule.add_self _

end QEC.Coding.BDL26LevelTwoOldXStarEndpoint
