import QEC.Coding.FiniteAlternatingConstruction.LevelTwoDecoderZero
import QEC.Coding.FiniteAlternatingConstruction.RXCohomology.Equivalence
import QEC.Coding.FiniteAlternatingConstruction.SeedCohomology

/-!
# Explicit sparse-cocycle exactness in the actual first replacement

An explicit finite sparse-cocycle theorem for the original first replacement.
All geometry and instance data are the original finite construction.

The fifteen slices use only interior horizontal edges of seed faces 0 and 1,
and interior shifted-Q vertices over seed qubits 0 and 1. Their shared left
end is on the X0--Q4 edge. The right ends are the actual Q0--Z0 and Q1--Z1
embeddings. The original full gauge decomposition identifies every slice
with the seed coefficient. The threshold is half >= 16, not a distance
hypothesis. No canonical decoder, graph, mark or family is changed.
-/
noncomputable section
namespace QEC.Coding.BDL26FirstReplacementSparseExactness

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators

abbrev Bit := BDL26FiniteTannerSquare.Field
abbrev Seed := baseTannerSquarePresentation
/-- The existing seed X0, typed before coercing to the presentation carrier. -/
abbrev center : Seed.X := (0 : BDL26FiniteAlternatingCore.BaseX)
abbrev RawQ (S : OddScale) := RX1 Seed S
abbrev W (S : OddScale) := Word Bit (RawQ S)
abbrev V (S : OddScale) := Word Bit (RX0 Seed S)

/-- Both selected old Q labels are incident only with X0. -/
def oldQ (b : Fin 2) : Seed.Q := Fin.castLE (by decide : 2 ≤ 5) b

def oldFace (b : Fin 2) : XStarFace Seed center :=
  ⟨Fin.castLE (by decide : 2 ≤ 4) b, by fin_cases b <;> decide⟩

def armEdge (b : Fin 2) : QStarEdge Seed (oldQ b) :=
  ⟨b, by fin_cases b <;> decide⟩

 theorem oldQ_unique_x (b : Fin 2) (x : Seed.X) :
    Seed.xq x (oldQ b)=true ↔ x=center := by
  have column : BDL26FiniteAlternatingCore.baseBoundary1Matrix x (oldQ b) =
      if x=center then (1 : Bit) else 0 := by
    have same : (0 : BDL26FiniteAlternatingCore.BaseX)=center := rfl
    have different : (1 : BDL26FiniteAlternatingCore.BaseX)≠center := by
      intro h
      have bad : (1 : Nat)=0 := congrArg Fin.val h
      cases bad
    fin_cases b <;> fin_cases x
    · calc
        _ = (1 : Bit) := rfl
        _ = _ := (if_pos same).symm
    · calc
        _ = (0 : Bit) := rfl
        _ = _ := (if_neg different).symm
    · calc
        _ = (1 : Bit) := rfl
        _ = _ := (if_pos same).symm
    · calc
        _ = (0 : Bit) := rfl
        _ = _ := (if_neg different).symm
  have matrix : (if Seed.xq x (oldQ b)=true then (1 : Bit) else 0) =
      BDL26FiniteAlternatingCore.baseBoundary1Matrix x (oldQ b) :=
    congrFun (congrFun base_xqIncidenceMatrix_eq x) (oldQ b)
  have indicator := matrix.trans column
  constructor
  · intro h
    by_contra hn
    have bad : (1 : Bit)=0 := by
      simpa only [if_pos h,if_neg hn] using indicator
    exact one_ne_zero bad
  · intro h
    by_contra hn
    have bad : (0 : Bit)=1 := by
      simpa only [if_neg hn,if_pos h] using indicator
    exact zero_ne_one bad

 theorem shared_edge (b : Fin 2) :
    xStarFaceXQEdge Seed center (oldFace b) 1 =
      xStarFaceXQEdge Seed center (oldFace 0) 1 := by
  fin_cases b <;> rfl

 theorem face_arm (b : Fin 2) :
    (xStarFaceQZEdge Seed center (oldFace b) 0).val =
      Sum.inr ⟨(oldQ b,b), (armEdge b).property⟩ := by
  fin_cases b <;> rfl

/-- Explicit legal interior index for each of the fifteen slices. -/
def sliceIndex (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) : Fin (S.half-1) :=
  ⟨k.val, by have := k.isLt; omega⟩

def height (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) : Fin (S.half+1) :=
  ⟨k.val+1, by have := k.isLt; omega⟩

 theorem height_pos (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) :
    0 < (height S large k).val := by simp [height]

 theorem height_lt (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) :
    (height S large k).val < S.half := by
  have := k.isLt; dsimp [height]; omega

/-- An actual shifted Q-cylinder vertex, not an artificial new coordinate. -/
def arm (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) (b : Fin 2) : RawQ S :=
  .inr ⟨oldQ b, (0,.inr (armEdge b,sliceIndex S large k))⟩

/-- An actual copy-zero horizontal edge of one of the two actual seed faces. -/
def horizontal (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15)
    (b : Fin 2) (i : Fin S.half) : RawQ S :=
  .inl ⟨center,.inl (0,subdivisionHorizontalEdge Seed center S (oldFace b) i (height S large k))⟩

 theorem horizontal_tag (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15)
    (b : Fin 2) (i : Fin S.half) :
    horizontal S large k b i =
      .inl ⟨center,.inl (0,.inr (.inl (oldFace b,i,sliceIndex S large k)))⟩ := by
  have hp := height_pos S large k
  have hl := height_lt S large k
  simp only [horizontal, subdivisionHorizontalEdge, dif_neg (by omega :
    (height S large k).val ≠ 0), dif_neg (by omega :
    (height S large k).val ≠ S.half)]
  apply congrArg (fun j : Fin (S.half-1) =>
    (Sum.inl ⟨center,Sum.inl (0,Sum.inr (Sum.inl (oldFace b,i,j)))⟩ : RawQ S))
  apply Fin.ext
  change (k.val+1)-1=k.val
  omega

abbrev Atom (S : OddScale) := Fin 2 ⊕ (Fin 2 × Fin S.half)

def atom (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) : Atom S → RawQ S
  | .inl b => arm S large k b
  | .inr (b,i) => horizontal S large k b i

/-- A total tag inspector; it does not redefine ownership or graph incidence. -/
def interiorLayer (S : OddScale) : RawQ S → Nat
  | .inl ⟨_,.inl (_, .inr (.inl (_,_,j)))⟩ => j.val
  | .inr ⟨_,(_, .inr (_,j))⟩ => j.val
  | _ => S.half

 theorem atom_layer (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) (a : Atom S) :
    interiorLayer S (atom S large k a) = k.val := by
  rcases a with b | ⟨b,i⟩
  · rfl
  · rw [atom,horizontal_tag]
    rfl

 theorem different_slices (S : OddScale) (large : 16 ≤ S.half)
    (k l : Fin 15) (a b : Atom S)
    (same : atom S large k a=atom S large l b) : k=l := by
  apply Fin.ext
  simpa only [atom_layer] using congrArg (interiorLayer S) same

/-- Direct finite pigeonhole argument on the whole original word support. -/
 theorem exists_zero_slice (S : OddScale) (large : 16 ≤ S.half) (w : W S)
    (small : HammingWeight w ≤ 14) :
    ∃ k : Fin 15, ∀ a : Atom S, w (atom S large k a)=0 := by
  by_contra nozero
  have hit : ∀ k : Fin 15, ∃ a : Atom S, w (atom S large k a)≠0 := by
    intro k
    by_contra h
    apply nozero
    refine ⟨k,?_⟩
    intro a
    by_contra ha
    exact h ⟨a,ha⟩
  choose a ha using hit
  let f : Fin 15 → {q : RawQ S // q ∈ hammingSupport w} := fun k =>
    ⟨atom S large k (a k), by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha k⟩⟩
  have inj : Function.Injective f := by
    intro k l h
    exact different_slices S large k l (a k) (a l) (congrArg Subtype.val h)
  have card := Fintype.card_le_of_injective f inj
  have lower : 15 ≤ (hammingSupport w).card := by simpa using card
  rw [HammingWeight_eq_card_hammingSupport] at small
  omega

def evaluate (S : OddScale) (q : RawQ S) : W S →ₗ[Bit] Bit where
  toFun w := w q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def sliceReadout (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) : W S →ₗ[Bit] Bit :=
  ∑ b : Fin 2, (evaluate S (arm S large k b)+
    ∑ i : Fin S.half, evaluate S (horizontal S large k b i))

 theorem sliceReadout_apply (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) (w : W S) :
    sliceReadout S large k w =
      ∑ b : Fin 2, (w (arm S large k b)+∑ i : Fin S.half, w (horizontal S large k b i)) := by
  simp only [sliceReadout,LinearMap.sum_apply,LinearMap.add_apply]
  rfl

 theorem zero_slice_readout (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) (w : W S)
    (zero : ∀ a : Atom S, w (atom S large k a)=0) : sliceReadout S large k w=0 := by
  rw [sliceReadout_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [show w (arm S large k b)=0 from zero (.inl b),zero_add]
  apply Finset.sum_eq_zero
  intro i _
  exact zero (.inr (b,i))

/-- The full endpoint telescoping identity in characteristic two. -/
 theorem sum_adjacent (n : Nat) (f : Fin (n+1) → Bit) :
    (∑ i : Fin n, (f i.castSucc+f i.succ))=f 0+f (Fin.last n) := by
  induction n with
  | zero => simpa using (ZModModule.add_self (f (0 : Fin 1))).symm
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have tail := ih (fun i => f i.succ)
    change (f 0+f (0 : Fin (n+1)).succ)+
      (∑ i : Fin n, (f i.castSucc.succ+f i.succ.succ))=f 0+f (Fin.last (n+1))
    rw [tail]
    have ends : (Fin.last n).succ=Fin.last (n+1) := rfl
    rw [ends]
    calc
      _ = f 0+((f (0 : Fin (n+1)).succ+f (0 : Fin (n+1)).succ)+f (Fin.last (n+1))) := by abel
      _ = _ := by rw [ZModModule.add_self,zero_add]

 def grid (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15)
    (b : Fin 2) (i : Fin (S.half+1)) : RX0 Seed S :=
  ⟨center,(0,subdivisionGridVertex Seed center S (oldFace b) i (height S large k))⟩

 theorem horizontal_gradient (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15)
    (b : Fin 2) (i : Fin S.half) (p : V S) :
    rxCoboundary0 Seed S p (horizontal S large k b i)=
      p (grid S large k b i.castSucc)+p (grid S large k b i.succ) := by
  rw [horizontal,BDL26RXDecoderAdapter.raw_delta0_x,
    ← doubleCylinderGraphBoundary_eq_boundary1]
  change wordLinearMapTranspose
    (graphBoundary (tannerDoubleCylinderEdgeStart Seed center S)
      (tannerDoubleCylinderEdgeEnd Seed center S)) (fun v => p ⟨center,v⟩)
      (.inl (0,subdivisionHorizontalEdge Seed center S (oldFace b) i (height S large k)))=_
  rw [wordLinearMapTranspose_graphBoundary_apply]
  simp only [tannerDoubleCylinderEdgeStart,tannerDoubleCylinderEdgeEnd,
    subdivisionHorizontalEdge_start,subdivisionHorizontalEdge_end]
  rfl

 theorem row_gradient (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15)
    (b : Fin 2) (p : V S) :
    (∑ i : Fin S.half, rxCoboundary0 Seed S p (horizontal S large k b i))=
      p (grid S large k b 0)+p (grid S large k b (Fin.last S.half)) := by
  simp_rw [horizontal_gradient]
  exact sum_adjacent S.half (fun i => p (grid S large k b i))

 def armVertex (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) (b : Fin 2) : RX0 Seed S :=
  ⟨center,(0,.inr (.inl (xStarFaceQZEdge Seed center (oldFace b) 0,sliceIndex S large k)))⟩

 theorem grid_right (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) (b : Fin 2) :
    grid S large k b (Fin.last S.half)=armVertex S large k b := by
  have last_eq : Fin.last S.half = (⟨S.half, by omega⟩ : Fin (S.half+1)) := by
    apply Fin.ext
    rfl
  have height_eq : height S large k =
      (⟨(sliceIndex S large k).val+1, by
        have := (sliceIndex S large k).isLt; omega⟩ : Fin (S.half+1)) := by
    apply Fin.ext
    rfl
  unfold grid armVertex
  apply congrArg (fun v : SubdivisionVertex Seed center S =>
    (⟨center,(0,v)⟩ : RX0 Seed S))
  rw [last_eq,height_eq]
  exact subdivisionGridVertex_edgeInterior_qz0 Seed center S (oldFace b)
    (sliceIndex S large k)

 theorem grid_left (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) (b : Fin 2) :
    grid S large k b 0=grid S large k 0 0 := by
  have height_eq : height S large k =
      (⟨(sliceIndex S large k).val+1, by
        have := (sliceIndex S large k).isLt; omega⟩ : Fin (S.half+1)) := by
    apply Fin.ext
    rfl
  unfold grid
  apply congrArg (fun v : SubdivisionVertex Seed center S =>
    (⟨center,(0,v)⟩ : RX0 Seed S))
  rw [height_eq]
  exact (subdivisionGridVertex_edgeInterior_xq1 Seed center S (oldFace b)
    (sliceIndex S large k)).trans
      ((congrArg (fun e : XStarEdge Seed center =>
        (Sum.inr (Sum.inl (e,sliceIndex S large k)) : SubdivisionVertex Seed center S))
        (shared_edge b)).trans
          (subdivisionGridVertex_edgeInterior_xq1 Seed center S (oldFace 0)
            (sliceIndex S large k)).symm)

/-- All original subdivision-vertex tags, including both kinds of old edge. -/
 theorem arm_subdivision_incidence (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15)
    (b : Fin 2) (v : SubdivisionVertex Seed center S) :
    qSubdivisionVertexXIncidence Seed (oldQ b) center S v
      (.inr (armEdge b,sliceIndex S large k)) =
      if v = .inr (.inl
        (xStarFaceQZEdge Seed center (oldFace b) 0,sliceIndex S large k)) then 1 else 0 := by
  have hinc := (oldQ_unique_x b center).mpr rfl
  have arm_value : (armEdge b).val=b := rfl
  rcases v with vertex | ⟨edge,i⟩ | face
  · simp [qSubdivisionVertexXIncidence,hinc]
  · rcases edge with ⟨edge,hmem⟩
    rcases edge with xq | qz
    · simp [qSubdivisionVertexXIncidence,hinc,Subtype.ext_iff,face_arm]
    · simp [qSubdivisionVertexXIncidence,hinc,Subtype.ext_iff,face_arm,
        Prod.ext_iff,and_assoc,arm_value]
  · simp [qSubdivisionVertexXIncidence,hinc]

/-- Whole original degree-one matrix column for each shifted interior vertex. -/
 theorem arm_incidence (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15)
    (b : Fin 2) (v : RX0 Seed S) :
    rxBoundary1Matrix Seed S v (arm S large k b)=
      if v=armVertex S large k b then 1 else 0 := by
  classical
  rcases v with ⟨x,c,v⟩
  by_cases hx : x=center
  · subst x
    by_cases hc : c=0
    · subst c
      simpa [arm,armVertex,rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,
        Sigma.mk.injEq] using arm_subdivision_incidence S large k b v
    · simp [arm,armVertex,rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,
        hc,Sigma.mk.injEq]
  · have hn : Seed.xq x (oldQ b)≠true := by
      intro ht; exact hx ((oldQ_unique_x b x).mp ht)
    have hv : (⟨x,(c,v)⟩ : RX0 Seed S) ≠ armVertex S large k b := by
      intro he
      exact hx (congrArg Sigma.fst he)
    rw [if_neg hv]
    simp [arm,rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,
      qSubdivisionVertexXIncidence,hn]

 theorem arm_gradient (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15)
    (b : Fin 2) (p : V S) :
    rxCoboundary0 Seed S p (arm S large k b)=p (armVertex S large k b) := by
  unfold rxCoboundary0 rxBoundary1
  rw [wordLinearMapTranspose_toLin'_apply]
  simp_rw [arm_incidence]
  simp

/-- Every slice annihilates every full raw boundary, with both row endpoints. -/
 theorem slice_boundary (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) (p : V S) :
    sliceReadout S large k (rxCoboundary0 Seed S p)=0 := by
  rw [sliceReadout_apply]
  simp_rw [arm_gradient,row_gradient,grid_right,grid_left S large k]
  rw [Fin.sum_univ_two]
  calc
    _ = (p (armVertex S large k 0)+p (armVertex S large k 0))+
      (p (armVertex S large k 1)+p (armVertex S large k 1))+
      (p (grid S large k 0 0)+p (grid S large k 0 0)) := by abel
    _ = 0 := by simp only [ZModModule.add_self]

/-- The auxiliary X-edge values are zero; each actual Q vertex reads its old Q. -/
 theorem slice_map1 (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15)
    (v : Word Bit Seed.Q) :
    sliceReadout S large k (rxMap1Coord Seed S v)=BDL26SeedCohomology.coefficient v := by
  rw [sliceReadout_apply]
  change (∑ b : Fin 2, (v (oldQ b)+∑ _i : Fin S.half, (0 : Bit))) =
    BDL26SeedCohomology.coefficient v
  simp only [Finset.sum_const_zero,add_zero,Fin.sum_univ_two]
  rfl

/-- A zero slice of a complete actual cocycle constructs its full potential. -/
 theorem exact_of_zero_slice (S : OddScale) (large : 16 ≤ S.half)
    (w : W S) (closed : tannerCoboundary1 (rxReplacementPresentation Seed S) w=0)
    (k : Fin 15) (zero : sliceReadout S large k w=0) :
    ∃ p : V S, tannerCoboundary0 (rxReplacementPresentation Seed S) p=w := by
  let wc : BDL26RXCohomology.Cocycle (rxReplacementPresentation Seed S) :=
    ⟨w,(BDL26RZCohomology.mem_cocycle_iff _ _).mpr closed⟩
  obtain ⟨v,f,full⟩ := BDL26RXCohomology.full_gauge_residual Seed
    baseTannerSquareAdmissibleV4 baseTannerSquareCellularRegular S wc
  have original_word : BDL26RXCohomology.coordinateWord Seed S wc.val = w := rfl
  have full_raw : rxMap1Coord Seed S v.val = w-rxCoboundary0 Seed S f :=
    full.trans (congrArg (fun u : W S => u-rxCoboundary0 Seed S f) original_word)
  have read := congrArg (sliceReadout S large k) full_raw
  rw [slice_map1,map_sub,slice_boundary,sub_zero,zero] at read
  have coefficient : BDL26SeedCohomology.coefficient v.val=0 := read
  have oldclosed : tannerCoboundary1 Seed v.val=0 :=
    (BDL26RZCohomology.mem_cocycle_iff _ _).mp v.property
  have form := BDL26SeedCohomology.cocycle_decomposition v.val oldclosed
  have oldboundary : tannerCoboundary0 Seed
      (BDL26SeedCohomology.normalPotential v.val)=v.val := by
    funext q
    have hq := congrFun form q
    simpa only [coefficient,zero_mul,add_zero] using hq.symm
  obtain ⟨g,hg⟩ := (BDL26RXCohomology.raw_boundary_iff Seed
    baseTannerSquareAdmissible S v.val).mpr
      ⟨BDL26SeedCohomology.normalPotential v.val,oldboundary⟩
  have raw : rxCoboundary0 Seed S (g+f)=w := by
    calc
      rxCoboundary0 Seed S (g+f) =
          rxCoboundary0 Seed S g+rxCoboundary0 Seed S f :=
        (rxCoboundary0 Seed S).map_add g f
      _ = rxMap1Coord Seed S v.val+rxCoboundary0 Seed S f :=
        congrArg (fun u : W S => u+rxCoboundary0 Seed S f) hg
      _ = w := eq_sub_iff_add_eq.mp full_raw
  refine ⟨g+f,?_⟩
  exact (BDL26RXCohomology.semanticWord_delta0 Seed baseTannerSquareAdmissibleV4
    baseTannerSquareCellularRegular S (g+f)).trans
      (congrArg (BDL26RXCohomology.semanticWord Seed S) raw)

/-- Explicit H=16: no bound on a selected representative or a distance oracle. -/
 theorem actual_first_replacement_sparse_cocycle_exact (S : OddScale)
    (large : 16 ≤ S.half) (w : Word Bit (BDL26DecodingGraph.state S 1).presentation.Q)
    (closed : tannerCoboundary1 (BDL26DecodingGraph.state S 1).presentation w=0)
    (small : HammingWeight w≤14) :
    w ∈ LinearMap.range (tannerCoboundary0 (BDL26DecodingGraph.state S 1).presentation) := by
  change w ∈ LinearMap.range (tannerCoboundary0 (rxReplacementPresentation Seed S))
  change tannerCoboundary1 (rxReplacementPresentation Seed S) w=0 at closed
  obtain ⟨k,hk⟩ := exists_zero_slice S large w small
  exact exact_of_zero_slice S large w closed k (zero_slice_readout S large k w hk)

 theorem explicit_uniform_threshold :
    ∃ H : Nat, ∀ S : OddScale, H≤S.half →
      ∀ w : Word Bit (BDL26DecodingGraph.state S 1).presentation.Q,
        tannerCoboundary1 (BDL26DecodingGraph.state S 1).presentation w=0 →
        HammingWeight w≤14 →
        w ∈ LinearMap.range (tannerCoboundary0 (BDL26DecodingGraph.state S 1).presentation) := by
  exact ⟨16,actual_first_replacement_sparse_cocycle_exact⟩

end QEC.Coding.BDL26FirstReplacementSparseExactness

/-!
# Separately named LOCAL-FIRST/minimum-full-weight fallback comparison

A separately named finite comparison decoder with the original LOCAL-FIRST
branch and a minimum-full-weight fallback. Its full-word correction theorem
uses the explicit first-replacement threshold and original RZ parity maps.
This namespace does not replace any canonical decoder, family, graph or mark.
-/
namespace QEC.Coding.BDL26BottomLocalFirstMinWeightComparison

open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators

abbrev F := BDL26FiniteTannerSquare.Field
abbrev P1 (S : OddScale) := levelOnePresentation S
abbrev P2 (S : OddScale) := levelTwoPresentation S
abbrev Error (S : OddScale) := Word F (P2 S).Q
abbrev Syndrome (S : OddScale) := Word F (P2 S).Z
abbrev OldWord (S : OddScale) := Word F (P1 S).Q

/-- Exhaustive same-syndrome minimum; <= retains the earlier table entry on ties. -/
def minimumSame {E Z : Type} [DecidableEq Z]
    (syndrome : E → Z) (weight : E → Nat) (sigma : Z) : List E → Option E
  | [] => none
  | a :: rest =>
      if syndrome a = sigma then
        match minimumSame syndrome weight sigma rest with
        | none => some a
        | some b => if weight a ≤ weight b then some a else some b
      else minimumSame syndrome weight sigma rest

/-- The complete recursion invariant proves membership, syndrome and minimum weight. -/
theorem minimumSame_spec {E Z : Type} [DecidableEq Z]
    (syndrome : E → Z) (weight : E → Nat) (sigma : Z) (entries : List E) :
    match minimumSame syndrome weight sigma entries with
    | none => ∀ b ∈ entries, syndrome b ≠ sigma
    | some a => a ∈ entries ∧ syndrome a = sigma ∧
        ∀ b ∈ entries, syndrome b = sigma → weight a ≤ weight b := by
  induction entries with
  | nil => simp [minimumSame]
  | cons a rest ih =>
      cases ht : minimumSame syndrome weight sigma rest with
      | none =>
          have hn : ∀ b ∈ rest, syndrome b ≠ sigma := by
            simpa only [ht] using ih
          by_cases ha : syndrome a = sigma
          · simp only [minimumSame,if_pos ha,ht]
            refine ⟨List.mem_cons_self,ha,?_⟩
            intro b hb hs
            rcases List.mem_cons.mp hb with h | h
            · subst b; exact le_rfl
            · exact False.elim (hn b h hs)
          · simp only [minimumSame,if_neg ha,ht]
            intro b hb hs
            rcases List.mem_cons.mp hb with h | h
            · subst b; exact ha hs
            · exact hn b h hs
      | some c =>
          have hs : c ∈ rest ∧ syndrome c = sigma ∧
              ∀ b ∈ rest, syndrome b = sigma → weight c ≤ weight b := by
            simpa only [ht] using ih
          obtain ⟨hc,hsc,hmin⟩ := hs
          by_cases ha : syndrome a = sigma
          · by_cases hw : weight a ≤ weight c
            · simp only [minimumSame,if_pos ha,ht,if_pos hw]
              refine ⟨List.mem_cons_self,ha,?_⟩
              intro b hb hs
              rcases List.mem_cons.mp hb with h | h
              · subst b; exact le_rfl
              · exact hw.trans (hmin b h hs)
            · simp only [minimumSame,if_pos ha,ht,if_neg hw]
              refine ⟨List.mem_cons_of_mem a hc,hsc,?_⟩
              intro b hb hs
              rcases List.mem_cons.mp hb with h | h
              · subst b; exact le_of_lt (Nat.lt_of_not_ge hw)
              · exact hmin b h hs
          · simp only [minimumSame,if_neg ha,ht]
            refine ⟨List.mem_cons_of_mem a hc,hsc,?_⟩
            intro b hb hs
            rcases List.mem_cons.mp hb with h | h
            · subst b; exact False.elim (ha hs)
            · exact hmin b h hs

/-- A represented syndrome excludes the default and gives a real minimum. -/
theorem minimumSame_exists {E Z : Type} [DecidableEq Z]
    (syndrome : E → Z) (weight : E → Nat) (sigma : Z) (entries : List E)
    (hex : ∃ b ∈ entries, syndrome b = sigma) :
    ∃ a, minimumSame syndrome weight sigma entries = some a := by
  have h := minimumSame_spec syndrome weight sigma entries
  cases hr : minimumSame syndrome weight sigma entries with
  | none =>
      have hn : ∀ b ∈ entries, syndrome b ≠ sigma := by
        simpa only [hr] using h
      obtain ⟨b,hb,hs⟩ := hex
      exact False.elim (hn b hb hs)
  | some a => exact ⟨a,rfl⟩

/-- Only the fallback changes; the first search is the literal original predicate. -/
def ownerFirstLookup {E Z : Type} [DecidableEq Z]
    (entries : List E) (syndrome : E → Z) (isLocal : E → Bool)
    (weight : E → Nat) (fallback : E) (sigma : Z) : E :=
  match search (fun e => isLocal e && decide (syndrome e = sigma)) entries with
  | some e => e
  | none => (minimumSame syndrome weight sigma entries).getD fallback

theorem ownerFirstLookup_syndrome {E Z : Type} [DecidableEq Z]
    (entries : List E) (syndrome : E → Z) (isLocal : E → Bool)
    (weight : E → Nat) (fallback : E) (sigma : Z)
    (hex : ∃ b ∈ entries, syndrome b = sigma) :
    syndrome (ownerFirstLookup entries syndrome isLocal weight fallback sigma) = sigma := by
  unfold ownerFirstLookup
  cases hl : search (fun e => isLocal e && decide (syndrome e = sigma)) entries with
  | some a =>
      have ha := (search_sound _ _ _ hl).2
      simpa using ((Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp ha).2
  | none =>
      obtain ⟨a,ha⟩ := minimumSame_exists syndrome weight sigma entries hex
      have hs := minimumSame_spec syndrome weight sigma entries
      rw [ha] at hs
      simpa only [ha,Option.getD_some] using hs.2.1

theorem ownerFirstLookup_agrees_local {E Z : Type} [DecidableEq Z]
    (entries : List E) (syndrome : E → Z) (isLocal : E → Bool)
    (weight : E → Nat) (fallback : E) (sigma : Z)
    (hex : ∃ b ∈ entries, isLocal b = true ∧ syndrome b = sigma) :
    ownerFirstLookup entries syndrome isLocal weight fallback sigma =
      lookup entries syndrome isLocal fallback sigma := by
  obtain ⟨b,hb,hl,hs⟩ := hex
  obtain ⟨a,ha⟩ := search_complete
    (fun e => isLocal e && decide (syndrome e = sigma)) entries
      ⟨b,hb,by simp [hl,hs]⟩
  simp only [ownerFirstLookup,lookup,ha]

theorem ownerFirstLookup_fallback_weight {E Z : Type} [DecidableEq Z]
    (entries : List E) (syndrome : E → Z) (isLocal : E → Bool)
    (weight : E → Nat) (fallback : E) (sigma : Z) (b : E)
    (hb : b ∈ entries) (hs : syndrome b = sigma)
    (hl : search (fun e => isLocal e && decide (syndrome e = sigma)) entries = none) :
    weight (ownerFirstLookup entries syndrome isLocal weight fallback sigma) ≤ weight b := by
  obtain ⟨a,ha⟩ := minimumSame_exists syndrome weight sigma entries ⟨b,hb,hs⟩
  have h := minimumSame_spec syndrome weight sigma entries
  rw [ha] at h
  simpa only [ownerFirstLookup,hl,ha,Option.getD_some] using h.2.2 b hb hs

/-- Weight is the FULL actual physical word count, not a selector proxy. -/
def actualWeight (S : OddScale) (e : Word F (ExecutableQ S)) : Nat :=
  HammingWeight (toActualError S e)

/-- A separate comparison decoder; canonical executableDecode/decode are untouched. -/
def executableComparison (S : OddScale) (sigma : Word F (ExecutableZ S)) :
    Word F (ExecutableQ S) :=
  ownerFirstLookup (allWords (ExecutableQ S)) (executableSyndrome S)
    (executableLocal S) (actualWeight S) 0 sigma

def ownerFirstMinWeightFallback (S : OddScale) (sigma : Syndrome S) : Error S :=
  toActualError S (executableComparison S (toExecutableSyndrome S sigma))

/-- Right inverse on the actual full represented syndrome domain. -/
theorem comparison_rightInverse (S : OddScale) (sigma : Syndrome S)
    (hsigma : sigma ∈ LinearMap.range (tannerCoboundary1 (P2 S))) :
    tannerCoboundary1 (P2 S) (ownerFirstMinWeightFallback S sigma) = sigma := by
  apply toExecutableSyndrome_injective S
  rw [← executableSyndrome_eq]
  unfold ownerFirstMinWeightFallback
  rw [toExecutableError_toActualError]
  unfold executableComparison
  apply ownerFirstLookup_syndrome
  obtain ⟨e,he⟩ := hsigma
  exact ⟨toExecutableError S e,mem_allWords _ _,by rw [executableSyndrome_eq,he]⟩

/-- Every admissible local preimage forces EXACT agreement with original LOCAL-FIRST. -/
theorem comparison_agrees_of_local_preimage (S : OddScale) (sigma : Syndrome S)
    (e : Error S) (he : levelTwoLocalError S e)
    (hs : tannerCoboundary1 (P2 S) e = sigma) :
    ownerFirstMinWeightFallback S sigma = decode S sigma := by
  unfold ownerFirstMinWeightFallback decode executableComparison executableDecode
  congr 1
  apply ownerFirstLookup_agrees_local
  refine ⟨toExecutableError S e,mem_allWords _ _,(executableLocal_iff S e).2 he,?_⟩
  rw [executableSyndrome_eq,hs]

/-- Literal first-branch locality OR full actual minimum-weight bound. -/
theorem comparison_local_or_weight (S : OddScale) (e : Error S) :
    levelTwoLocalError S
      (ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e)) ∨
    HammingWeight (ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e)) ≤
      HammingWeight e := by
  let sigma := toExecutableSyndrome S (tannerCoboundary1 (P2 S) e)
  cases hl : search (fun a => executableLocal S a &&
      decide (executableSyndrome S a = sigma)) (allWords (ExecutableQ S)) with
  | some a =>
      left
      have ha := ((Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp
        (search_sound _ _ _ hl).2).1
      have localActual : levelTwoLocalError S (toActualError S a) := by
        apply (executableLocal_iff S _).1
        simpa only [toExecutableError_toActualError] using ha
      change levelTwoLocalError S (toActualError S
        (ownerFirstLookup (allWords (ExecutableQ S)) (executableSyndrome S)
          (executableLocal S) (actualWeight S) 0 sigma))
      rw [ownerFirstLookup,hl]
      exact localActual
  | none =>
      right
      have h := ownerFirstLookup_fallback_weight
        (allWords (ExecutableQ S)) (executableSyndrome S) (executableLocal S)
        (actualWeight S) 0 sigma (toExecutableError S e)
        (mem_allWords _ _) (executableSyndrome_eq S e) hl
      simpa only [ownerFirstMinWeightFallback,executableComparison,actualWeight,
        sigma,toActualError_toExecutableError] using h

/-- Zero is still the original first local head, independently of scale size. -/
theorem comparison_zero (S : OddScale) : ownerFirstMinWeightFallback S 0 = 0 := by
  have hlocal : levelTwoLocalError S (0 : Error S) := by
    apply (executableLocal_iff S _).1
    have transport_zero : toExecutableError S (0 : Error S) = 0 := by
      funext q
      rfl
    rw [transport_zero]
    exact executableLocal_zero S
  have h := comparison_agrees_of_local_preimage S 0 0 hlocal (map_zero _)
  exact h.trans (decode_zero S)

/-- Original code membership and the full original Tanner range are the same object. -/
theorem chain_boundary_iff (S : OddScale) (w : Error S) :
    w ∈ (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier ↔
      w ∈ LinearMap.range (tannerCoboundary0 (P2 S)) := by
  constructor
  · intro hw
    obtain ⟨p,hp⟩ := ((levelTwoChainComplex S).mem_firstCoboundaryCheckCode_iff w).1 hw
    refine ⟨p,?_⟩
    rw [levelTwo_coboundary0_eq] at hp
    exact hp
  · rintro ⟨p,hp⟩
    apply ((levelTwoChainComplex S).mem_firstCoboundaryCheckCode_iff w).2
    refine ⟨p,?_⟩
    rw [levelTwo_coboundary0_eq]
    exact hp

/-- Current F17 owner-local correctness is preserved for every original scale. -/
theorem comparison_corrects_local (S : OddScale) (e : Error S)
    (he : levelTwoLocalError S e) :
    e + ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e) ∈
      LinearMap.range (tannerCoboundary0 (P2 S)) := by
  rw [comparison_agrees_of_local_preimage S _ e he rfl]
  exact (chain_boundary_iff S _).1 (decode_corrects_local S e he)

/-- The actual finite Q-cylinder parity, on the entire physical C2 word. -/
abbrev rho (S : OddScale) : Error S →ₗ[F] OldWord S := rzQParity (P1 S) S

/-- Every nonzero parity label injects into a different original nonzero Q fibre. -/
theorem rho_weight_le (S : OddScale) (w : Error S) :
    HammingWeight (rho S w) ≤ HammingWeight w := by
  classical
  have hit : ∀ q : {q : (P1 S).Q // q ∈ hammingSupport (rho S w)},
      ∃ v : QDoubleCylinderVertex (transposePresentation (P1 S)) q.val S,
        w (Sum.inr ⟨q.val,v⟩) ≠ 0 := by
    intro q
    by_contra hn
    have hz : ∀ v : QDoubleCylinderVertex (transposePresentation (P1 S)) q.val S,
        w (Sum.inr ⟨q.val,v⟩) = 0 := by
      intro v
      by_contra hv
      exact hn ⟨v,hv⟩
    have hp : rho S w q.val = 0 := by
      change (∑ v : QDoubleCylinderVertex (transposePresentation (P1 S)) q.val S,
        w (Sum.inr ⟨q.val,v⟩)) = 0
      exact Finset.sum_eq_zero (fun v _ => hz v)
    exact (Finset.mem_filter.mp q.property).2 hp
  choose vertex hv using hit
  let f : {q : (P1 S).Q // q ∈ hammingSupport (rho S w)} →
      {c : (P2 S).Q // c ∈ hammingSupport w} := fun q =>
    ⟨Sum.inr ⟨q.val,vertex q⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv q⟩⟩
  have inj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    have he := Sum.inr.inj (congrArg Subtype.val h)
    exact congrArg Sigma.fst he
  have hc := Fintype.card_le_of_injective f inj
  simp only [HammingWeight_eq_card_hammingSupport]
  simpa using hc

/-- All actual owner kinds are retained: X/Z owners give zero parity everywhere. -/
theorem rho_local_support (S : OddScale) (w : Error S)
    (hw : levelTwoLocalError S w) :
    ∃ a : (P1 S).Q, ∀ q, q ≠ a → rho S w q = 0 := by
  obtain ⟨owner,ho⟩ := (levelTwoLocalError_iff_owner S w).1 hw
  let a := qCoordinateOfOwner (P1 S) (levelOneQDefault S) owner
  refine ⟨a,?_⟩
  intro q hq
  apply rzQParity_zero_of_other_owner (P1 S) S w owner ho q
  intro h
  exact hq (qCoordinateOfOwner_of_eq (P1 S) (levelOneQDefault S) q owner h)

/-- Large owner-local corrections still cost at most one OLD parity coordinate. -/
theorem rho_local_weight_le_one (S : OddScale) (w : Error S)
    (hw : levelTwoLocalError S w) : HammingWeight (rho S w) ≤ 1 := by
  classical
  obtain ⟨a,ha⟩ := rho_local_support S w hw
  have hs : hammingSupport (rho S w) ⊆ {a} := by
    intro q hq
    apply Finset.mem_singleton.mpr
    by_contra hn
    exact (Finset.mem_filter.mp hq).2 (ha q hn)
  rw [HammingWeight_eq_card_hammingSupport]
  exact (Finset.card_le_card hs).trans (by simp)

/-- Actual full differentials square to zero; no caller exactness certificate. -/
theorem tanner_d1_d0 (P : TannerSquarePresentation) (p : Word F P.X) :
    tannerCoboundary1 P (tannerCoboundary0 P p) = 0 :=
  LinearMap.congr_fun (tannerCoboundary_squared P) p

/-- Genuine parity cochain transport on all actual closed physical words. -/
theorem rho_closed (S : OddScale) (w : Error S)
    (hw : tannerCoboundary1 (P2 S) w = 0) :
    tannerCoboundary1 (P1 S) (rho S w) = 0 :=
  rzQParity_cocycle (P1 S) (rxState S baseState).admissible S w hw

/-- Compatibility with the actual entire C2 potential, including all X families. -/
theorem rho_boundary (S : OddScale) (p : Word F (P2 S).X) :
    rho S (tannerCoboundary0 (P2 S) p) =
      tannerCoboundary0 (P1 S) (rzOldXParity (P1 S) S p) := by
  have h := rzQParity_coboundary (P1 S) (rxState S baseState).admissible S p
  funext q
  exact congrFun h q

/-- Old full boundaries lift through the actual selected RZ map. -/
theorem lifted_boundary (S : OddScale) (p : Word F (P1 S).X) :
    tannerCoboundary0 (P2 S) (rzMap0Coord (P1 S) S p) =
      map1Coord (P1 S) (rxState S baseState).admissible S
        (tannerCoboundary0 (P1 S) p) := by
  have h := LinearMap.congr_fun
    (rzMap_commutes_coboundary0 (P1 S) (rxState S baseState).admissible S) p
  change rzCoboundary0 (P1 S) (rxState S baseState).admissible S
      (rzMap0Coord (P1 S) S p) =
    map1Coord (P1 S) (rxState S baseState).admissible S
      (tannerCoboundary0 (P1 S) p) at h
  funext q
  exact congrFun h q

/-- Full cohomology detection, by constructing the whole residual potential. -/
theorem rho_boundary_iff (S : OddScale) (w : Error S)
    (hw : tannerCoboundary1 (P2 S) w = 0) :
    w ∈ LinearMap.range (tannerCoboundary0 (P2 S)) ↔
      rho S w ∈ LinearMap.range (tannerCoboundary0 (P1 S)) := by
  constructor
  · rintro ⟨p,hp⟩
    refine ⟨rzOldXParity (P1 S) S p,?_⟩
    exact (rho_boundary S p).symm.trans (congrArg (rho S) hp)
  · rintro ⟨p,hp⟩
    let liftedPotential : Word F (P2 S).X := rzMap0Coord (P1 S) S p
    have square : tannerCoboundary1 (P2 S)
        (tannerCoboundary0 (P2 S) liftedPotential) = 0 :=
      tanner_d1_d0 (P2 S) liftedPotential
    let residual : Error S := w-tannerCoboundary0 (P2 S) liftedPotential
    have hc : tannerCoboundary1 (P2 S) residual = 0 := by
      calc
        tannerCoboundary1 (P2 S) residual =
            tannerCoboundary1 (P2 S) w-
              tannerCoboundary1 (P2 S) (tannerCoboundary0 (P2 S) liftedPotential) :=
          map_sub (tannerCoboundary1 (P2 S)) _ _
        _ = 0 := by rw [hw,square,sub_self]
    have liftedParity : rho S (tannerCoboundary0 (P2 S) liftedPotential) =
        tannerCoboundary0 (P1 S) p :=
      (congrArg (rho S) (lifted_boundary S p)).trans
        (rzQParity_map1Coord (P1 S) (rxState S baseState).admissible S
          (tannerCoboundary0 (P1 S) p))
    have hrho : rho S residual = 0 := by
      calc
        rho S residual = rho S w-rho S (tannerCoboundary0 (P2 S) liftedPotential) :=
          map_sub (rho S) _ _
        _ = 0 := by rw [liftedParity,hp,sub_self]
    have actualFilling : ∃ fillingPotential : Word F (P2 S).X,
        tannerCoboundary0 (P2 S) fillingPotential = residual := by
      obtain ⟨rawPotential,rawBoundary⟩ := rzCocycle_qParity_zero_is_coboundary (P1 S)
        (rxState S baseState).admissible (rxState S baseState).regular S residual hc hrho
      let fillingPotential : Word F (P2 S).X := rawPotential
      refine ⟨fillingPotential,?_⟩
      funext coordinate
      exact congrFun rawBoundary coordinate
    obtain ⟨fillingPotential,actualBoundary⟩ := actualFilling
    refine ⟨fillingPotential+liftedPotential,?_⟩
    calc
      tannerCoboundary0 (P2 S) (fillingPotential+liftedPotential) =
          tannerCoboundary0 (P2 S) fillingPotential+
            tannerCoboundary0 (P2 S) liftedPotential :=
        (tannerCoboundary0 (P2 S)).map_add fillingPotential liftedPotential
      _ = residual+tannerCoboundary0 (P2 S) liftedPotential :=
        congrArg (fun a : Error S => a+tannerCoboundary0 (P2 S) liftedPotential)
          actualBoundary
      _ = w := sub_add_cancel _ _

/-- The accepted explicit original H16 theorem is consumed on the entire parity word. -/
theorem boundary_of_closed_small_rho (S : OddScale) (large : 16 ≤ S.half)
    (w : Error S) (hw : tannerCoboundary1 (P2 S) w = 0)
    (small : HammingWeight (rho S w) ≤ 14) :
    w ∈ LinearMap.range (tannerCoboundary0 (P2 S)) := by
  apply (rho_boundary_iff S w hw).2
  exact BDL26FirstReplacementSparseExactness.actual_first_replacement_sparse_cocycle_exact
    S large (rho S w) (rho_closed S w hw) small

/-- ANY same-syndrome owner-local preimage, even of large physical weight, works. -/
theorem small_error_local_preimage (S : OddScale) (large : 16 ≤ S.half)
    (e c : Error S) (small : HammingWeight e ≤ 7) (hlocal : levelTwoLocalError S c)
    (same : tannerCoboundary1 (P2 S) c = tannerCoboundary1 (P2 S) e) :
    e+c ∈ LinearMap.range (tannerCoboundary0 (P2 S)) := by
  apply boundary_of_closed_small_rho S large (e+c)
    (sameSyndrome_add_cocycle S e c same.symm)
  have he := rho_weight_le S e
  have hc := rho_local_weight_le_one S c hlocal
  have ha := HammingWeight_add_le (rho S e) (rho S c)
  have sum : rho S (e+c)=rho S e+rho S c := (rho S).map_add e c
  have residualWeight : HammingWeight (rho S (e+c)) ≤ 8 := by
    rw [sum]
    omega
  omega

/-- ANY same-syndrome full preimage no heavier than e has parity residual weight≤14. -/
theorem small_error_light_preimage (S : OddScale) (large : 16 ≤ S.half)
    (e c : Error S) (small : HammingWeight e ≤ 7) (light : HammingWeight c ≤ HammingWeight e)
    (same : tannerCoboundary1 (P2 S) c = tannerCoboundary1 (P2 S) e) :
    e+c ∈ LinearMap.range (tannerCoboundary0 (P2 S)) := by
  apply boundary_of_closed_small_rho S large (e+c)
    (sameSyndrome_add_cocycle S e c same.symm)
  have he := rho_weight_le S e
  have hc := rho_weight_le S c
  have ha := HammingWeight_add_le (rho S e) (rho S c)
  have sum : rho S (e+c)=rho S e+rho S c := (rho S).map_add e c
  rw [sum]
  omega

/-- The coherent positive bottom theorem: every arbitrary full actual error of weight≤7. -/
theorem comparison_corrects_weight_seven (S : OddScale) (large : 16 ≤ S.half)
    (e : Error S) (small : HammingWeight e ≤ 7) :
    e+ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e) ∈
      LinearMap.range (tannerCoboundary0 (P2 S)) := by
  have same := comparison_rightInverse S (tannerCoboundary1 (P2 S) e) ⟨e,rfl⟩
  rcases comparison_local_or_weight S e with hlocal | light
  · exact small_error_local_preimage S large e _ small hlocal same
  · exact small_error_light_preimage S large e _ small light same

/-- The same full result in the original physical C2 check-code interface. -/
theorem comparison_corrects_weight_seven_code (S : OddScale) (large : 16 ≤ S.half)
    (e : Error S) (small : HammingWeight e ≤ 7) :
    e+ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e) ∈
      (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier :=
  (chain_boundary_iff S _).2 (comparison_corrects_weight_seven S large e small)

/-- Separately named comparison data only; canonical baseAdapter is unchanged. -/
def comparisonBaseAdapter (S : OddScale) :
    MultiscaleDecoder.F17LevelTwoBaseAdapterV2 (decoderData S)
      (decodingGraph S 2) (show 2 ≤ 2 from le_rfl) where
  decode := fun sigma => ownerFirstMinWeightFallback S sigma.val

theorem comparisonBaseAdapter_rightInverse (S : OddScale) :
    (comparisonBaseAdapter S).IsRightInverse := by
  intro sigma
  change (decoderFamily S).coboundary1
    (MultiscaleDecoder.levelTwoIndex (show 2 ≤ 2 from le_rfl))
    (ownerFirstMinWeightFallback S sigma.val) = sigma.val
  rw [decoderFamily_coboundary1]
  apply comparison_rightInverse
  have hsigma : sigma.val ∈ LinearMap.range
      ((decoderFamily S).coboundary1
        (MultiscaleDecoder.levelTwoIndex (show 2 ≤ 2 from le_rfl))) := sigma.property
  rw [decoderFamily_coboundary1] at hsigma
  exact hsigma

theorem comparisonBaseAdapter_correctsLocalErrors (S : OddScale) :
    (comparisonBaseAdapter S).CorrectsLocalErrors (levelTwoLocalComplex S) := by
  intro input hlocal
  have he : levelTwoLocalError S input.error := hlocal
  let e : Error S := input.error
  change e+ownerFirstMinWeightFallback S ((decoderFamily S).coboundary1
      (MultiscaleDecoder.levelTwoIndex (show 2 ≤ 2 from le_rfl)) e) ∈
    (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier
  rw [decoderFamily_coboundary1]
  exact (chain_boundary_iff S _).2 (comparison_corrects_local S e he)

/-- One complete separately named comparison contract; no canonical adoption. -/
theorem ownerFirstMinWeightFallback_contract (S : OddScale) (large : 16 ≤ S.half) :
    ownerFirstMinWeightFallback S 0 = 0 ∧
    (comparisonBaseAdapter S).IsRightInverse ∧
    (comparisonBaseAdapter S).CorrectsLocalErrors (levelTwoLocalComplex S) ∧
    ∀ e : Error S, HammingWeight e ≤ 7 →
      e+ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e) ∈
        (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier := by
  exact ⟨comparison_zero S,comparisonBaseAdapter_rightInverse S,
    comparisonBaseAdapter_correctsLocalErrors S,comparison_corrects_weight_seven_code S large⟩

end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison

/-!
# Scale-dependent full-word exactness and comparison radius

This is a stacked Source extension of the original finite model. The n+1
interior slices are disjoint actual coordinates; no distance or correctness
certificate is assumed. The separately named comparison decoder is unchanged.
-/
namespace QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators

/-- There are n+1 disjoint legal interior slices when n+2 ≤ half. -/
def sliceIndex (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) : Fin (S.half-1) :=
  ⟨k.val, by have := k.isLt; omega⟩

def height (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) : Fin (S.half+1) :=
  ⟨k.val+1, by have := k.isLt; omega⟩

 theorem height_pos (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) :
    0 < (height S n large k).val := by simp [height]

 theorem height_lt (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) :
    (height S n large k).val < S.half := by
  have := k.isLt; dsimp [height]; omega

/-- An actual shifted Q-cylinder vertex, not an artificial new coordinate. -/
def arm (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) (b : Fin 2) : RawQ S :=
  .inr ⟨oldQ b, (0,.inr (armEdge b,sliceIndex S n large k))⟩

/-- An actual copy-zero horizontal edge of one of the two actual seed faces. -/
def horizontal (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1))
    (b : Fin 2) (i : Fin S.half) : RawQ S :=
  .inl ⟨center,.inl (0,subdivisionHorizontalEdge Seed center S (oldFace b) i (height S n large k))⟩

 theorem horizontal_tag (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1))
    (b : Fin 2) (i : Fin S.half) :
    horizontal S n large k b i =
      .inl ⟨center,.inl (0,.inr (.inl (oldFace b,i,sliceIndex S n large k)))⟩ := by
  have hp := height_pos S n large k
  have hl := height_lt S n large k
  simp only [horizontal, subdivisionHorizontalEdge, dif_neg (by omega :
    (height S n large k).val ≠ 0), dif_neg (by omega :
    (height S n large k).val ≠ S.half)]
  apply congrArg (fun j : Fin (S.half-1) =>
    (Sum.inl ⟨center,Sum.inl (0,Sum.inr (Sum.inl (oldFace b,i,j)))⟩ : RawQ S))
  apply Fin.ext
  change (k.val+1)-1=k.val
  omega


def atom (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) : Atom S → RawQ S
  | .inl b => arm S n large k b
  | .inr (b,i) => horizontal S n large k b i

 theorem atom_layer (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) (a : Atom S) :
    interiorLayer S (atom S n large k a) = k.val := by
  rcases a with b | ⟨b,i⟩
  · rfl
  · rw [atom,horizontal_tag]
    rfl

 theorem different_slices (S : OddScale) (n : Nat) (large : n+2 ≤ S.half)
    (k l : Fin (n+1)) (a b : Atom S)
    (same : atom S n large k a=atom S n large l b) : k=l := by
  apply Fin.ext
  simpa only [atom_layer] using congrArg (interiorLayer S) same

/-- Direct finite pigeonhole argument on the whole original word support. -/
 theorem exists_zero_slice (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (w : W S)
    (small : HammingWeight w ≤ n) :
    ∃ k : Fin (n+1), ∀ a : Atom S, w (atom S n large k a)=0 := by
  by_contra nozero
  have hit : ∀ k : Fin (n+1), ∃ a : Atom S, w (atom S n large k a)≠0 := by
    intro k
    by_contra h
    apply nozero
    refine ⟨k,?_⟩
    intro a
    by_contra ha
    exact h ⟨a,ha⟩
  choose a ha using hit
  let f : Fin (n+1) → {q : RawQ S // q ∈ hammingSupport w} := fun k =>
    ⟨atom S n large k (a k), by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha k⟩⟩
  have inj : Function.Injective f := by
    intro k l h
    exact different_slices S n large k l (a k) (a l) (congrArg Subtype.val h)
  have card := Fintype.card_le_of_injective f inj
  have lower : n+1 ≤ (hammingSupport w).card := by simpa using card
  rw [HammingWeight_eq_card_hammingSupport] at small
  omega

def sliceReadout (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) : W S →ₗ[Bit] Bit :=
  ∑ b : Fin 2, (evaluate S (arm S n large k b)+
    ∑ i : Fin S.half, evaluate S (horizontal S n large k b i))

 theorem sliceReadout_apply (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) (w : W S) :
    sliceReadout S n large k w =
      ∑ b : Fin 2, (w (arm S n large k b)+∑ i : Fin S.half, w (horizontal S n large k b i)) := by
  simp only [sliceReadout,LinearMap.sum_apply,LinearMap.add_apply]
  rfl

 theorem zero_slice_readout (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) (w : W S)
    (zero : ∀ a : Atom S, w (atom S n large k a)=0) : sliceReadout S n large k w=0 := by
  rw [sliceReadout_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [show w (arm S n large k b)=0 from zero (.inl b),zero_add]
  apply Finset.sum_eq_zero
  intro i _
  exact zero (.inr (b,i))

 def grid (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1))
    (b : Fin 2) (i : Fin (S.half+1)) : RX0 Seed S :=
  ⟨center,(0,subdivisionGridVertex Seed center S (oldFace b) i (height S n large k))⟩

 theorem horizontal_gradient (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1))
    (b : Fin 2) (i : Fin S.half) (p : V S) :
    rxCoboundary0 Seed S p (horizontal S n large k b i)=
      p (grid S n large k b i.castSucc)+p (grid S n large k b i.succ) := by
  rw [horizontal,BDL26RXDecoderAdapter.raw_delta0_x,
    ← doubleCylinderGraphBoundary_eq_boundary1]
  change wordLinearMapTranspose
    (graphBoundary (tannerDoubleCylinderEdgeStart Seed center S)
      (tannerDoubleCylinderEdgeEnd Seed center S)) (fun v => p ⟨center,v⟩)
      (.inl (0,subdivisionHorizontalEdge Seed center S (oldFace b) i (height S n large k)))=_
  rw [wordLinearMapTranspose_graphBoundary_apply]
  simp only [tannerDoubleCylinderEdgeStart,tannerDoubleCylinderEdgeEnd,
    subdivisionHorizontalEdge_start,subdivisionHorizontalEdge_end]
  rfl

 theorem row_gradient (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1))
    (b : Fin 2) (p : V S) :
    (∑ i : Fin S.half, rxCoboundary0 Seed S p (horizontal S n large k b i))=
      p (grid S n large k b 0)+p (grid S n large k b (Fin.last S.half)) := by
  simp_rw [horizontal_gradient]
  exact sum_adjacent S.half (fun i => p (grid S n large k b i))

 def armVertex (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) (b : Fin 2) : RX0 Seed S :=
  ⟨center,(0,.inr (.inl (xStarFaceQZEdge Seed center (oldFace b) 0,sliceIndex S n large k)))⟩

 theorem grid_right (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) (b : Fin 2) :
    grid S n large k b (Fin.last S.half)=armVertex S n large k b := by
  have last_eq : Fin.last S.half = (⟨S.half, by omega⟩ : Fin (S.half+1)) := by
    apply Fin.ext
    rfl
  have height_eq : height S n large k =
      (⟨(sliceIndex S n large k).val+1, by
        have := (sliceIndex S n large k).isLt; omega⟩ : Fin (S.half+1)) := by
    apply Fin.ext
    rfl
  unfold grid armVertex
  apply congrArg (fun v : SubdivisionVertex Seed center S =>
    (⟨center,(0,v)⟩ : RX0 Seed S))
  rw [last_eq,height_eq]
  exact subdivisionGridVertex_edgeInterior_qz0 Seed center S (oldFace b)
    (sliceIndex S n large k)

 theorem grid_left (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) (b : Fin 2) :
    grid S n large k b 0=grid S n large k 0 0 := by
  have height_eq : height S n large k =
      (⟨(sliceIndex S n large k).val+1, by
        have := (sliceIndex S n large k).isLt; omega⟩ : Fin (S.half+1)) := by
    apply Fin.ext
    rfl
  unfold grid
  apply congrArg (fun v : SubdivisionVertex Seed center S =>
    (⟨center,(0,v)⟩ : RX0 Seed S))
  rw [height_eq]
  exact (subdivisionGridVertex_edgeInterior_xq1 Seed center S (oldFace b)
    (sliceIndex S n large k)).trans
      ((congrArg (fun e : XStarEdge Seed center =>
        (Sum.inr (Sum.inl (e,sliceIndex S n large k)) : SubdivisionVertex Seed center S))
        (shared_edge b)).trans
          (subdivisionGridVertex_edgeInterior_xq1 Seed center S (oldFace 0)
            (sliceIndex S n large k)).symm)

/-- All original subdivision-vertex tags, including both kinds of old edge. -/
 theorem arm_subdivision_incidence (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1))
    (b : Fin 2) (v : SubdivisionVertex Seed center S) :
    qSubdivisionVertexXIncidence Seed (oldQ b) center S v
      (.inr (armEdge b,sliceIndex S n large k)) =
      if v = .inr (.inl
        (xStarFaceQZEdge Seed center (oldFace b) 0,sliceIndex S n large k)) then 1 else 0 := by
  have hinc := (oldQ_unique_x b center).mpr rfl
  have arm_value : (armEdge b).val=b := rfl
  rcases v with vertex | ⟨edge,i⟩ | face
  · simp [qSubdivisionVertexXIncidence,hinc]
  · rcases edge with ⟨edge,hmem⟩
    rcases edge with xq | qz
    · simp [qSubdivisionVertexXIncidence,hinc,Subtype.ext_iff,face_arm]
    · simp [qSubdivisionVertexXIncidence,hinc,Subtype.ext_iff,face_arm,
        Prod.ext_iff,and_assoc,arm_value]
  · simp [qSubdivisionVertexXIncidence,hinc]

/-- Whole original degree-one matrix column for each shifted interior vertex. -/
 theorem arm_incidence (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1))
    (b : Fin 2) (v : RX0 Seed S) :
    rxBoundary1Matrix Seed S v (arm S n large k b)=
      if v=armVertex S n large k b then 1 else 0 := by
  classical
  rcases v with ⟨x,c,v⟩
  by_cases hx : x=center
  · subst x
    by_cases hc : c=0
    · subst c
      simpa [arm,armVertex,rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,
        Sigma.mk.injEq] using arm_subdivision_incidence S n large k b v
    · simp [arm,armVertex,rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,
        hc,Sigma.mk.injEq]
  · have hn : Seed.xq x (oldQ b)≠true := by
      intro ht; exact hx ((oldQ_unique_x b x).mp ht)
    have hv : (⟨x,(c,v)⟩ : RX0 Seed S) ≠ armVertex S n large k b := by
      intro he
      exact hx (congrArg Sigma.fst he)
    rw [if_neg hv]
    simp [arm,rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,
      qSubdivisionVertexXIncidence,hn]

 theorem arm_gradient (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1))
    (b : Fin 2) (p : V S) :
    rxCoboundary0 Seed S p (arm S n large k b)=p (armVertex S n large k b) := by
  unfold rxCoboundary0 rxBoundary1
  rw [wordLinearMapTranspose_toLin'_apply]
  simp_rw [arm_incidence]
  simp

/-- Every slice annihilates every full raw boundary, with both row endpoints. -/
 theorem slice_boundary (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) (p : V S) :
    sliceReadout S n large k (rxCoboundary0 Seed S p)=0 := by
  rw [sliceReadout_apply]
  simp_rw [arm_gradient,row_gradient,grid_right,grid_left S n large k]
  rw [Fin.sum_univ_two]
  calc
    _ = (p (armVertex S n large k 0)+p (armVertex S n large k 0))+
      (p (armVertex S n large k 1)+p (armVertex S n large k 1))+
      (p (grid S n large k 0 0)+p (grid S n large k 0 0)) := by abel
    _ = 0 := by simp only [ZModModule.add_self]

/-- The auxiliary X-edge values are zero; each actual Q vertex reads its old Q. -/
 theorem slice_map1 (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1))
    (v : Word Bit Seed.Q) :
    sliceReadout S n large k (rxMap1Coord Seed S v)=BDL26SeedCohomology.coefficient v := by
  rw [sliceReadout_apply]
  change (∑ b : Fin 2, (v (oldQ b)+∑ _i : Fin S.half, (0 : Bit))) =
    BDL26SeedCohomology.coefficient v
  simp only [Finset.sum_const_zero,add_zero,Fin.sum_univ_two]
  rfl

/-- A zero slice of a complete actual cocycle constructs its full potential. -/
 theorem exact_of_zero_slice (S : OddScale) (n : Nat) (large : n+2 ≤ S.half)
    (w : W S) (closed : tannerCoboundary1 (rxReplacementPresentation Seed S) w=0)
    (k : Fin (n+1)) (zero : sliceReadout S n large k w=0) :
    ∃ p : V S, tannerCoboundary0 (rxReplacementPresentation Seed S) p=w := by
  let wc : BDL26RXCohomology.Cocycle (rxReplacementPresentation Seed S) :=
    ⟨w,(BDL26RZCohomology.mem_cocycle_iff _ _).mpr closed⟩
  obtain ⟨v,f,full⟩ := BDL26RXCohomology.full_gauge_residual Seed
    baseTannerSquareAdmissibleV4 baseTannerSquareCellularRegular S wc
  have original_word : BDL26RXCohomology.coordinateWord Seed S wc.val = w := rfl
  have full_raw : rxMap1Coord Seed S v.val = w-rxCoboundary0 Seed S f :=
    full.trans (congrArg (fun u : W S => u-rxCoboundary0 Seed S f) original_word)
  have read := congrArg (sliceReadout S n large k) full_raw
  rw [slice_map1,map_sub,slice_boundary,sub_zero,zero] at read
  have coefficient : BDL26SeedCohomology.coefficient v.val=0 := read
  have oldclosed : tannerCoboundary1 Seed v.val=0 :=
    (BDL26RZCohomology.mem_cocycle_iff _ _).mp v.property
  have form := BDL26SeedCohomology.cocycle_decomposition v.val oldclosed
  have oldboundary : tannerCoboundary0 Seed
      (BDL26SeedCohomology.normalPotential v.val)=v.val := by
    funext q
    have hq := congrFun form q
    simpa only [coefficient,zero_mul,add_zero] using hq.symm
  obtain ⟨g,hg⟩ := (BDL26RXCohomology.raw_boundary_iff Seed
    baseTannerSquareAdmissible S v.val).mpr
      ⟨BDL26SeedCohomology.normalPotential v.val,oldboundary⟩
  have raw : rxCoboundary0 Seed S (g+f)=w := by
    calc
      rxCoboundary0 Seed S (g+f) =
          rxCoboundary0 Seed S g+rxCoboundary0 Seed S f :=
        (rxCoboundary0 Seed S).map_add g f
      _ = rxMap1Coord Seed S v.val+rxCoboundary0 Seed S f :=
        congrArg (fun u : W S => u+rxCoboundary0 Seed S f) hg
      _ = w := eq_sub_iff_add_eq.mp full_raw
  refine ⟨g+f,?_⟩
  exact (BDL26RXCohomology.semanticWord_delta0 Seed baseTannerSquareAdmissibleV4
    baseTannerSquareCellularRegular S (g+f)).trans
      (congrArg (BDL26RXCohomology.semanticWord Seed S) raw)


/-- Every complete first-replacement cocycle of weight at most k is exact. -/
theorem actual_first_replacement_sparse_cocycle_exact (S : OddScale) (k : Nat)
    (large : k+2 ≤ S.half)
    (w : Word Bit (BDL26DecodingGraph.state S 1).presentation.Q)
    (closed : tannerCoboundary1 (BDL26DecodingGraph.state S 1).presentation w=0)
    (small : HammingWeight w≤k) :
    w ∈ LinearMap.range (tannerCoboundary0 (BDL26DecodingGraph.state S 1).presentation) := by
  change w ∈ LinearMap.range (tannerCoboundary0 (rxReplacementPresentation Seed S))
  change tannerCoboundary1 (rxReplacementPresentation Seed S) w=0 at closed
  obtain ⟨j,hj⟩ := exists_zero_slice S k large w small
  exact exact_of_zero_slice S k large w closed j (zero_slice_readout S k large j w hj)

end QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent

namespace QEC.Coding.BDL26BottomLocalFirstMinWeightComparison

open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators

/-- Full-word weight zero is zero at every actual C2 coordinate. -/
private theorem radius_error_eq_zero (S : OddScale) (e : Error S)
    (small : HammingWeight e ≤ 0) : e=0 := by
  classical
  rw [HammingWeight_eq_card_hammingSupport] at small
  have empty : hammingSupport e = ∅ := Finset.card_eq_zero.mp (by omega)
  funext q
  change e q = 0
  by_contra hq
  have member : q ∈ hammingSupport e :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq⟩
  rw [empty] at member
  simpa using member

/-- Scale-dependent exactness is applied to the entire actual RZ parity word. -/
theorem boundary_of_closed_rho_weight (S : OddScale) (k : Nat)
    (large : k+2 ≤ S.half) (w : Error S)
    (closed : tannerCoboundary1 (P2 S) w=0)
    (small : HammingWeight (rho S w) ≤ k) :
    w ∈ LinearMap.range (tannerCoboundary0 (P2 S)) := by
  apply (rho_boundary_iff S w closed).2
  exact BDL26FirstReplacementSparseExactness.ScaleDependent.actual_first_replacement_sparse_cocycle_exact
    S k large (rho S w) (rho_closed S w closed) small

/-- ANY same-syndrome owner-local preimage, with no physical-weight bound on it. -/
theorem radius_error_local_preimage (S : OddScale) (r : Nat)
    (large : 2*r+2 ≤ S.half) (e c : Error S)
    (small : HammingWeight e ≤ r) (hlocal : levelTwoLocalError S c)
    (same : tannerCoboundary1 (P2 S) c = tannerCoboundary1 (P2 S) e) :
    e+c ∈ LinearMap.range (tannerCoboundary0 (P2 S)) := by
  by_cases zero : r=0
  · subst r
    have he : e=0 := radius_error_eq_zero S e small
    subst e
    have hc : tannerCoboundary1 (P2 S) c=0 := same.trans (map_zero _)
    have correct := comparison_corrects_local S c hlocal
    simpa only [hc,comparison_zero,add_zero,zero_add] using correct
  · apply boundary_of_closed_rho_weight S (2*r) large (e+c)
      (sameSyndrome_add_cocycle S e c same.symm)
    have he := rho_weight_le S e
    have hc := rho_local_weight_le_one S c hlocal
    have ha := HammingWeight_add_le (rho S e) (rho S c)
    have sum : rho S (e+c)=rho S e+rho S c := (rho S).map_add e c
    rw [sum]
    omega

/-- ANY full same-syndrome preimage no heavier than e has parity weight at most 2r. -/
theorem radius_error_light_preimage (S : OddScale) (r : Nat)
    (large : 2*r+2 ≤ S.half) (e c : Error S)
    (small : HammingWeight e ≤ r) (light : HammingWeight c ≤ HammingWeight e)
    (same : tannerCoboundary1 (P2 S) c = tannerCoboundary1 (P2 S) e) :
    e+c ∈ LinearMap.range (tannerCoboundary0 (P2 S)) := by
  apply boundary_of_closed_rho_weight S (2*r) large (e+c)
    (sameSyndrome_add_cocycle S e c same.symm)
  have he := rho_weight_le S e
  have hc := rho_weight_le S c
  have ha := HammingWeight_add_le (rho S e) (rho S c)
  have sum : rho S (e+c)=rho S e+rho S c := (rho S).map_add e c
  rw [sum]
  omega

/-- The unchanged comparison decoder corrects every full physical error of weight≤r. -/
theorem comparison_corrects_radius (S : OddScale) (r : Nat)
    (large : 2*r+2 ≤ S.half) (e : Error S) (small : HammingWeight e ≤ r) :
    e+ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e) ∈
      LinearMap.range (tannerCoboundary0 (P2 S)) := by
  have same := comparison_rightInverse S (tannerCoboundary1 (P2 S) e) ⟨e,rfl⟩
  rcases comparison_local_or_weight S e with hlocal | light
  · exact radius_error_local_preimage S r large e _ small hlocal same
  · exact radius_error_light_preimage S r large e _ small light same

/-- The same full-word radius theorem in the original C2 check-code carrier. -/
theorem comparison_corrects_radius_code (S : OddScale) (r : Nat)
    (large : 2*r+2 ≤ S.half) (e : Error S) (small : HammingWeight e ≤ r) :
    e+ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e) ∈
      (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier :=
  (chain_boundary_iff S _).2 (comparison_corrects_radius S r large e small)

/-- All original F17 properties together with scale-dependent full-word correction. -/
theorem ownerFirstMinWeightFallback_radius_contract (S : OddScale) (r : Nat)
    (large : 2*r+2 ≤ S.half) :
    ownerFirstMinWeightFallback S 0 = 0 ∧
    (comparisonBaseAdapter S).IsRightInverse ∧
    (comparisonBaseAdapter S).CorrectsLocalErrors (levelTwoLocalComplex S) ∧
    ∀ e : Error S, HammingWeight e ≤ r →
      e+ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e) ∈
        (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier := by
  exact ⟨comparison_zero S,comparisonBaseAdapter_rightInverse S,
    comparisonBaseAdapter_correctsLocalErrors S,comparison_corrects_radius_code S r large⟩

end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
