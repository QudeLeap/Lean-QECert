import QEC.Coding.FiniteAlternatingConstruction.RZPhysicalStarTransport
import QEC.Coding.FiniteAlternatingConstruction.RXPhysicalStarTransport
import QEC.Coding.FiniteAlternatingConstruction.HistorySyndromeSensitivity.Snapshots
import Mathlib.Tactic

/-!
# Actual RZ physical-X-star transport and the adjacent original RX step

Project-derived internal refinement of BDL26 v1 paper.tex:3455–3481
(SHA256 66d1927b20efccb757da40af3d291e4738c60054799812393e0a739abcc73e5b).
All three materialized X constructors use their literal incidences. The fixed
RZ Q parity and full eleven-clause pullback retain both original runs and all
neighbour Z terms. The adjacent RX step uses representatives of those SAME
coarse inputs and keeps the full composed potential. This proves one adjacent
pair, not an all-interval induction, stability, mask or lifetime theorem.
-/
noncomputable section
namespace QEC.Coding.BDL26RZPhysicalXStarTransport

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26LevelTwoDistance
open BDL26ReplacementCochainMaps BDL26RZDecoderAdapter BDL26RZErrorPullback
open BDL26RZFiniteBlockTransport MultiscaleDecoder
open scoped Classical BigOperators

private theorem twice {I : Type} (w : Word BDL26FiniteTannerSquare.Field I) : w+w=0 := by
  funext q
  exact CharTwo.add_self_eq_zero _

private theorem shift {I : Type} (a e : Word BDL26FiniteTannerSquare.Field I) : a+(a+e)=e := by
  rw [← add_assoc,twice,zero_add]

/-- Empty raw Q blocks, proved before instantiating any recursive presentation. -/
private theorem raw_qBlocks_empty (P : TannerSquarePresentation) (S : OddScale) :
    Coordinates.qBlocks P S ∅=∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro r hr
  have h := (Finset.mem_filter.mp hr).2
  rcases r with ze | ⟨q,v⟩
  · exact h
  · exact Finset.notMem_empty q h

/-- Composition algebra in one fixed pair of word carriers. -/
private theorem full_linear_composition {I J : Type}
    (F : Word BDL26FiniteTannerSquare.Field I →ₗ[BDL26FiniteTannerSquare.Field]
      Word BDL26FiniteTannerSquare.Field J)
    (x c d q : Word BDL26FiniteTannerSquare.Field I)
    (e p r : Word BDL26FiniteTannerSquare.Field J)
    (hx : F x=e+p) (hr : r=p+F q) :
    F (x+c+d+q)=e+F (c+d)+r := by
  rw [map_add,map_add,map_add,map_add,hx,hr]
  abel

private theorem cast_xq (U V : TannerSquarePresentation) (hp : U=V)
    (x : U.X) (q : U.Q) : U.xq x q=
      V.xq ((Equiv.cast (congrArg TannerSquarePresentation.X hp)) x)
        ((Equiv.cast (congrArg TannerSquarePresentation.Q hp)) q) := by
  cases hp
  rfl

private theorem cast_vertex_x (U V : TannerSquarePresentation) (hp : U=V)
    (hv : Vertex U=Vertex V) (hx : U.X=V.X) (x : V.X) :
    cast hv (Vertex.x ((Equiv.cast hx).symm x))=Vertex.x x := by
  cases hp
  rfl

private theorem basis_support {I : Type} [Fintype I] (q : I) :
    hammingSupport (canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q) ⊆ {q} := by
  intro r hr
  by_contra hn
  have hnq : r≠q := by simpa using hn
  have hz : canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q r=0 := by
    simp [canonicalBasisWord,hnq]
  exact (by simpa [hammingSupport] using hr :
    canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q r≠0) hz

private theorem read_basis {I J : Type} (e : I ≃ J)
    (R : Word BDL26FiniteTannerSquare.Field I ≃ₗ[BDL26FiniteTannerSquare.Field]
      Word BDL26FiniteTannerSquare.Field J)
    (hr : ∀ w x, R w x=w (e.symm x)) (q : J) :
    R (canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) (e.symm q))=
      canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q := by
  funext r
  rw [hr]
  by_cases h : r=q
  · subst r
    simp [canonicalBasisWord]
  · have hn : e.symm r≠e.symm q := fun he => h (e.symm.injective he)
    simp [canonicalBasisWord,h,hn]

/-- Computed Q support for all three original raw X constructors. -/
def rawQ0 (P : TannerSquarePresentation) (S : OddScale) : RZX P S → Finset P.Q
  | .inl (.inl _) => ∅
  | .inl (.inr ⟨q,_⟩) => {q}
  | .inr (x,_) => BDL26RXPhysicalStarTransport.physicalXStar P x

/-- Every old qz neighbour is retained in the Q-edge case. -/
def rawZ0 (P : TannerSquarePresentation) (S : OddScale) : RZX P S → Finset P.Z
  | .inl (.inl ⟨z,_⟩) => {z}
  | .inl (.inr ⟨q,_⟩) => Coordinates.neighborZ P {q}
  | .inr _ => ∅

/-- The first case merely names an inhabited centre, never a raw parent. -/
def rawDown (C : ConstructionState) (S : OddScale) : RZX C.presentation S → C.presentation.X
  | .inl (.inl _) => C.selectedX
  | .inl (.inr ⟨q,_⟩) => (C.admissible.toTannerSquareAdmissible.xqRoot q).1
  | .inr (x,_) => x

/-- The original partial parent, including both intrinsically unparented cases. -/
def rawParent (P : TannerSquarePresentation) (S : OddScale) : RZX P S → Option (Vertex P)
  | .inl _ => none
  | .inr (x,_) => some (Vertex.x x)

/-- This is a calculation of incidence, not a supplied covering certificate. -/
theorem raw_star_cover (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (u : RZX P S) (r : RZQ P S)
    (hi : rzXQIncidence P A S u r=true) :
    r ∈ Coordinates.inputBlocks P S (rawQ0 P S u) (rawZ0 P S u) := by
  rcases u with (⟨z,f⟩ | ⟨q,e⟩) | ⟨x,c⟩
  · rcases r with ⟨z',edge⟩ | ⟨q,v⟩
    · change decide (∃ h : z'=z,
        doubleCylinderFaceEdgeMatrix (transposePresentation P) z S (h ▸ edge) f=1)=true at hi
      obtain ⟨h,_⟩ := of_decide_eq_true hi
      rw [Coordinates.mem_input_z]
      simp [rawZ0,h]
    · cases hi
  · rcases r with ⟨z,edge⟩ | ⟨q',v⟩
    · change decide (∃ h : P.qz q z=true,
        qToZDoubleCylinderEdge P A q z h S e=edge)=true at hi
      obtain ⟨hz,_⟩ := of_decide_eq_true hi
      rw [Coordinates.mem_input_z]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,q,by simp,hz⟩
    · change decide (∃ h : q'=q,
        h ▸ v=qDoubleCylinderEdgeStart (transposePresentation P) q S e ∨
        h ▸ v=qDoubleCylinderEdgeEnd (transposePresentation P) q S e)=true at hi
      obtain ⟨hq,_⟩ := of_decide_eq_true hi
      rw [Coordinates.mem_input_q]
      simp [rawQ0,hq]
  · rcases r with ⟨z,edge⟩ | ⟨q,v⟩
    · cases hi
    · change decide (∃ f : P.Face, ∃ k : BDL26FiniteTannerSquare.Two,
        P.faceX f=x ∧ oldXFaceQ P S k (f,c)=Sum.inr ⟨q,v⟩)=true at hi
      obtain ⟨f,k,hx,hq⟩ := of_decide_eq_true hi
      have hq' : P.faceQ f k=q := congrArg Sigma.fst (Sum.inr.inj hq)
      rw [Coordinates.mem_input_q]
      apply (BDL26RXPhysicalStarTransport.mem_physicalXStar P x q).mpr
      simpa only [hx,hq'] using P.data.faceQ_xq f k

/-- The singleton Q-edge root comes from original admissibility. -/
theorem raw_Q0_subset (C : ConstructionState) (S : OddScale) (u : RZX C.presentation S) :
    rawQ0 C.presentation S u ⊆ BDL26RXPhysicalStarTransport.physicalXStar
      C.presentation (rawDown C S u) := by
  rcases u with (⟨z,f⟩ | ⟨q,e⟩) | ⟨x,c⟩
  · exact Finset.empty_subset _
  · intro r hr
    have h : r=q := by simpa [rawQ0] using hr
    subst r
    exact (BDL26RXPhysicalStarTransport.mem_physicalXStar _ _ _).mpr
      (C.admissible.toTannerSquareAdmissible.xqRoot q).2
  · exact fun _ h => h

variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)

def upperXChart : RZX (Old S depth i) S ≃ FamilyX S depth i.succ := (coord0 S depth i odd).symm
def upperQChart : RZQ (Old S depth i) S ≃ FamilyQ S depth i.succ := (coord1 S depth i odd).symm

def upperStar (u : FamilyX S depth i.succ) : Finset (FamilyQ S depth i.succ) :=
  BDL26RXPhysicalStarTransport.physicalXStar (state S (i.val+1)).presentation u

def Q0 (u : FamilyX S depth i.succ) := rawQ0 (Old S depth i) S (coord0 S depth i odd u)
def Z0 (u : FamilyX S depth i.succ) := rawZ0 (Old S depth i) S (coord0 S depth i odd u)
def downX (u : FamilyX S depth i.succ) := rawDown (state S i.val) S (coord0 S depth i odd u)
def Zplus (u : FamilyX S depth i.succ) := Coordinates.zplus (Old S depth i)
  (Q0 S depth i odd u) (Z0 S depth i odd u)
def Localized (u : FamilyX S depth i.succ) (a b : Upper S depth i) : Prop :=
  hammingSupport (a+b) ⊆ upperStar S depth i u

@[simp] theorem coord0_chart (x : RZX (Old S depth i) S) :
    coord0 S depth i odd (upperXChart S depth i odd x)=x := (coord0 S depth i odd).apply_symm_apply x
@[simp] theorem coord1_chart (r : RZQ (Old S depth i) S) :
    coord1 S depth i odd (upperQChart S depth i odd r)=r := (coord1 S depth i odd).apply_symm_apply r

/-- Literal xq transport along the actual RZ successor equality. -/
theorem actual_incidence (u : FamilyX S depth i.succ) (r : FamilyQ S depth i.succ) :
    (state S (i.val+1)).presentation.xq u r=
      rzXQIncidence (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S
        (coord0 S depth i odd u) (coord1 S depth i odd r) :=
  cast_xq _ _ (upper_eq S depth i odd) u r

theorem chart_incidence (x : RZX (Old S depth i) S) (r : RZQ (Old S depth i) S) :
    (state S (i.val+1)).presentation.xq
      (upperXChart S depth i odd x) (upperQChart S depth i odd r)=
      rzXQIncidence (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S x r := by
  rw [actual_incidence S depth i odd,coord0_chart,coord1_chart]

/-- Exact whole-Vertex cast computes none/none/some, rather than an X owner guess. -/
theorem parent_chart (x : RZX (Old S depth i) S) :
    parent S (i.val+1) (Vertex.x (upperXChart S depth i odd x))=
      rawParent (Old S depth i) S x := by
  simp only [parent,nextParent,dif_neg odd,nextRZVertex,upperXChart,coord0]
  erw [cast_vertex_x _ _ (upper_eq S depth i odd)]
  rcases x with x | x <;> rfl

/-- Exact constructor table: the local face computes no Q block and no raw parent. -/
theorem local_face_data (z : (Old S depth i).Z) (f : ZDoubleCylinderFace (Old S depth i) z S) :
    Q0 S depth i odd (upperXChart S depth i odd (.inl (.inl ⟨z,f⟩)))=∅ ∧
    Z0 S depth i odd (upperXChart S depth i odd (.inl (.inl ⟨z,f⟩)))={z} ∧
    downX S depth i odd (upperXChart S depth i odd (.inl (.inl ⟨z,f⟩)))=(state S i.val).selectedX ∧
    parent S (i.val+1) (Vertex.x (upperXChart S depth i odd (.inl (.inl ⟨z,f⟩))))=none := by
  refine ⟨?_,?_,?_,?_⟩
  · simp [Q0,rawQ0]
  · simp [Z0,rawZ0]
  · simp [downX,rawDown]
  · rw [parent_chart S depth i odd]
    rfl

/-- Exact Q-edge table, including all old Z neighbours and an incident computed centre. -/
theorem q_edge_data (q : (Old S depth i).Q)
    (e : QDoubleCylinderEdge (transposePresentation (Old S depth i)) q S) :
    Q0 S depth i odd (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩)))={q} ∧
    Z0 S depth i odd (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩)))=Coordinates.neighborZ (Old S depth i) {q} ∧
    downX S depth i odd (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩)))=
      ((state S i.val).admissible.toTannerSquareAdmissible.xqRoot q).1 ∧
    parent S (i.val+1) (Vertex.x (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))))=none := by
  refine ⟨?_,?_,?_,?_⟩
  · simp [Q0,rawQ0]
  · simp [Z0,rawZ0]
  · simp [downX,rawDown]
  · rw [parent_chart S depth i odd]
    rfl

/-- The old X and its actual copy tag determine its original nonzero-cell parent. -/
theorem old_x_data (x : (Old S depth i).X) (c : BDL26FiniteTannerSquare.Two) :
    Q0 S depth i odd (upperXChart S depth i odd (.inr (x,c)))=
      BDL26RXPhysicalStarTransport.physicalXStar (Old S depth i) x ∧
    Z0 S depth i odd (upperXChart S depth i odd (.inr (x,c)))=∅ ∧
    downX S depth i odd (upperXChart S depth i odd (.inr (x,c)))=x ∧
    parent S (i.val+1) (Vertex.x (upperXChart S depth i odd (.inr (x,c))))=some (Vertex.x x) := by
  refine ⟨?_,?_,?_,?_⟩
  · simp [Q0,rawQ0]
  · simp [Z0,rawZ0]
  · simp [downX,rawDown]
  · rw [parent_chart S depth i odd]
    rfl

/-- Every actual physical star is covered by its computed finite input blocks. -/
theorem upperStar_subset_inputBlocks (u : FamilyX S depth i.succ) :
    upperStar S depth i u ⊆ inputBlocks S depth i odd (Q0 S depth i odd u) (Z0 S depth i odd u) := by
  intro r hr
  have hi := (actual_incidence S depth i odd u r).symm.trans
    ((BDL26RXPhysicalStarTransport.mem_physicalXStar _ _ _).mp hr)
  apply Finset.mem_union.mpr
  have h := raw_star_cover (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S
    (coord0 S depth i odd u) (coord1 S depth i odd r) hi
  rcases Finset.mem_union.mp h with hq | hz
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq⟩)
  · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩)

theorem Q0_subset_lowerStar (u : FamilyX S depth i.succ) :
    Q0 S depth i odd u ⊆ BDL26RXPhysicalStarTransport.physicalXStar (Old S depth i) (downX S depth i odd u) :=
  raw_Q0_subset (state S i.val) S (coord0 S depth i odd u)

theorem Q0_card_le_seven (u : FamilyX S depth i.succ) : (Q0 S depth i odd u).card ≤ 7 := by
  obtain ⟨x,rfl⟩ := (upperXChart S depth i odd).surjective u
  rcases x with (⟨z,f⟩ | ⟨q,e⟩) | ⟨x,c⟩
  · simp [Q0,rawQ0]
  · simp [Q0,rawQ0]
  · simpa [Q0,rawQ0] using BDL26RXPhysicalStarTransport.incident_card_le_seven S depth i x

theorem localized_blocks (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    hammingSupport (a+b) ⊆ inputBlocks S depth i odd (Q0 S depth i odd u) (Z0 S depth i odd u) :=
  he.trans (upperStar_subset_inputBlocks S depth i odd u)

theorem lower_supported (above : 3 ≤ i.val) (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) : hammingSupport (lowerError S depth i odd a b) ⊆ Q0 S depth i odd u := by
  obtain ⟨p,hp⟩ := BDL26RZFiniteBlockTransport.two_run S depth i odd (by omega) _ _ a b
    (localized_blocks S depth i odd u a b he)
  exact hp.2.2.2.2.1

theorem lower_physical_supported (above : 3 ≤ i.val) (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) : hammingSupport (lowerError S depth i odd a b) ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (Old S depth i) (downX S depth i odd u) :=
  (lower_supported S depth i odd above u a b he).trans (Q0_subset_lowerStar S depth i odd u)

theorem lower_weight (above : 3 ≤ i.val) (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    HammingWeight (lowerError S depth i odd a b) ≤ (Q0 S depth i odd u).card ∧ (Q0 S depth i odd u).card ≤ 7 := by
  rw [HammingWeight_eq_card_hammingSupport]
  exact ⟨Finset.card_le_card (lower_supported S depth i odd above u a b he),Q0_card_le_seven S depth i odd u⟩

theorem correction_difference_supported (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    hammingSupport ((run S depth i odd a).correction+(run S depth i odd b).correction) ⊆
      zBlocks S depth i odd (Zplus S depth i odd u) :=
  correction_difference_support S depth i odd _ _ a b (localized_blocks S depth i odd u a b he)

theorem input_syndrome_supported (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    hammingSupport ((errorSyndrome S depth i a).val+(errorSyndrome S depth i b).val) ⊆
      syndromeBlocks S depth i odd (Zplus S depth i odd u) :=
  input_syndrome_support S depth i odd _ _ a b (localized_blocks S depth i odd u a b he)

/-- Full eleven clauses, lower physical support and weight; no upper word is truncated. -/
theorem two_run (above : 3 ≤ i.val) (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    ∃ p : Potential S depth i,
      Pullback S depth i odd (Q0 S depth i odd u) (Z0 S depth i odd u) a b p ∧
      hammingSupport (lowerError S depth i odd a b) ⊆
        BDL26RXPhysicalStarTransport.physicalXStar (Old S depth i) (downX S depth i odd u) ∧
      HammingWeight (lowerError S depth i odd a b) ≤ (Q0 S depth i odd u).card ∧
      (Q0 S depth i odd u).card ≤ 7 ∧
      (∀ x : (Old S depth i).X, ∀ c : BDL26FiniteTannerSquare.Two, read0 S depth i odd p (.inr (x,c))=0) := by
  obtain ⟨p,hp⟩ := BDL26RZFiniteBlockTransport.two_run S depth i odd (by omega) _ _ a b
    (localized_blocks S depth i odd u a b he)
  exact ⟨p,hp,lower_physical_supported S depth i odd above u a b he,
    (lower_weight S depth i odd above u a b he).1,(lower_weight S depth i odd above u a b he).2,
    potential_oldX_zero S depth i odd _ _ p hp.2.2.2.2.2.2.2.2.1⟩

/-- Same-p both-copy zero, independently usable with the literal full Pullback. -/
theorem oldX_zero (u : FamilyX S depth i.succ) (a b : Upper S depth i) (p : Potential S depth i)
    (hp : Pullback S depth i odd (Q0 S depth i odd u) (Z0 S depth i odd u) a b p)
    (x : (Old S depth i).X) (c : BDL26FiniteTannerSquare.Two) : read0 S depth i odd p (.inr (x,c))=0 :=
  potential_oldX_zero S depth i odd _ _ p hp.2.2.2.2.2.2.2.2.1 x c

/-- The local-face constructor has sharp zero lower error but retains full E as a boundary. -/
theorem local_face_transport (above : 3 ≤ i.val) (z : (Old S depth i).Z)
    (f : ZDoubleCylinderFace (Old S depth i) z S) (a b : Upper S depth i)
    (he : Localized S depth i (upperXChart S depth i odd (.inl (.inl ⟨z,f⟩))) a b) :
    ∃ p : Potential S depth i, Pullback S depth i odd ∅ {z} a b p ∧
      lowerError S depth i odd a b=0 ∧ HammingWeight (lowerError S depth i odd a b)=0 ∧
      (run S depth i odd a).coarse.val=(run S depth i odd b).coarse.val ∧
      updated S depth i odd a b=(indexedFamily S depth).coboundary0 i.succ p := by
  have hb := localized_blocks S depth i odd _ a b he
  have hz : hammingSupport (a+b) ⊆ zBlocks S depth i odd {z} := by
    have hd := local_face_data S depth i odd z f
    have hb' : hammingSupport (a+b) ⊆ inputBlocks S depth i odd ∅ {z} := by
      rw [hd.1,hd.2.1] at hb
      exact hb
    intro r hr
    rcases Finset.mem_union.mp (hb' hr) with hq | hz
    · have hc : coord1 S depth i odd r ∈ Coordinates.qBlocks (Old S depth i) S ∅ :=
        (Finset.mem_filter.mp hq).2
      rw [raw_qBlocks_empty] at hc
      exact False.elim (Finset.notMem_empty _ hc)
    · exact hz
  obtain ⟨p,hp,hl,hc,hu⟩ := one_z_block S depth i odd (by omega) z a b hz
  exact ⟨p,hp,hl,by simp [hl],hc,hu⟩

theorem q_edge_weight (above : 3 ≤ i.val) (q : (Old S depth i).Q)
    (e : QDoubleCylinderEdge (transposePresentation (Old S depth i)) q S) (a b : Upper S depth i)
    (he : Localized S depth i (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))) a b) :
    HammingWeight (lowerError S depth i odd a b) ≤ 1 := by
  simpa [Q0,rawQ0] using (lower_weight S depth i odd above _ a b he).1

theorem old_x_weight (above : 3 ≤ i.val) (x : (Old S depth i).X) (c : BDL26FiniteTannerSquare.Two)
    (a b : Upper S depth i) (he : Localized S depth i (upperXChart S depth i odd (.inr (x,c))) a b) :
    HammingWeight (lowerError S depth i odd a b) ≤
      (BDL26RXPhysicalStarTransport.physicalXStar (Old S depth i) x).card ∧
      (BDL26RXPhysicalStarTransport.physicalXStar (Old S depth i) x).card ≤ 7 := by
  simpa [Q0,rawQ0] using lower_weight S depth i odd above _ a b he

/-- A physical basis perturbation is localized for arbitrary original background. -/
theorem basis_localized (u : FamilyX S depth i.succ) (r : FamilyQ S depth i.succ)
    (hr : (state S (i.val+1)).presentation.xq u r=true) (a : Upper S depth i) :
    Localized S depth i u a (a+canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) r) := by
  change hammingSupport (a+(a+canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) r)) ⊆ _
  rw [shift]
  apply (basis_support r).trans
  intro t ht
  have htr : t=r := by simpa using ht
  subst t
  exact (BDL26RXPhysicalStarTransport.mem_physicalXStar _ _ _).mpr hr

/-- The literal two endpoints, with their actual copy/subdivision tags. -/
def edgeEndpointQ (q : (Old S depth i).Q)
    (e : QDoubleCylinderEdge (transposePresentation (Old S depth i)) q S)
    (c : BDL26FiniteTannerSquare.Two) : FamilyQ S depth i.succ :=
  upperQChart S depth i odd (.inr ⟨q,twoSelect
    (qDoubleCylinderEdgeStart (transposePresentation (Old S depth i)) q S e)
    (qDoubleCylinderEdgeEnd (transposePresentation (Old S depth i)) q S e) c⟩)

theorem edgeEndpoint_incident (q : (Old S depth i).Q)
    (e : QDoubleCylinderEdge (transposePresentation (Old S depth i)) q S)
    (c : BDL26FiniteTannerSquare.Two) :
    (state S (i.val+1)).presentation.xq
      (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))) (edgeEndpointQ S depth i odd q e c)=true := by
  rw [edgeEndpointQ,chart_incidence]
  change decide (∃ h : q=q,
    h ▸ twoSelect _ _ c=qDoubleCylinderEdgeStart (transposePresentation (Old S depth i)) q S e ∨
    h ▸ twoSelect _ _ c=qDoubleCylinderEdgeEnd (transposePresentation (Old S depth i)) q S e)=true
  apply decide_eq_true
  refine ⟨rfl,?_⟩
  by_cases hc : c=0
  · exact Or.inl (by simp [twoSelect,hc])
  · exact Or.inr (by simp [twoSelect,hc])

/-- Either endpoint yields the nonzero old q basis, although the X centre has no raw parent. -/
theorem endpoint_transport (above : 3 ≤ i.val) (q : (Old S depth i).Q)
    (e : QDoubleCylinderEdge (transposePresentation (Old S depth i)) q S)
    (c : BDL26FiniteTannerSquare.Two) (a : Upper S depth i) :
    let u := upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))
    let b := a+canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) (edgeEndpointQ S depth i odd q e c)
    ∃ p : Potential S depth i, Pullback S depth i odd {q} (Coordinates.neighborZ (Old S depth i) {q}) a b p ∧
      parent S (i.val+1) (Vertex.x u)=none ∧
      lowerError S depth i odd a b=canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q ∧
      lowerError S depth i odd a b≠0 ∧ HammingWeight (lowerError S depth i odd a b) ≤ 1 := by
  dsimp only
  have he := basis_localized S depth i _ _ (edgeEndpoint_incident S depth i odd q e c) a
  obtain ⟨p,hp,_,_,_,_⟩ := two_run S depth i odd above _ _ _ he
  have hl : lowerError S depth i odd a
      (a+canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) (edgeEndpointQ S depth i odd q e c))=
        canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q :=
    BDL26RZPhysicalStarTransport.lower_physicalQ_basis S depth i odd a q _
  refine ⟨p,by simpa [Q0,Z0,rawQ0,rawZ0] using hp,parent_chart S depth i odd _,hl,?_,
    q_edge_weight S depth i odd above q e _ _ he⟩
  intro hz
  exact BDL26RZPhysicalStarTransport.basis_nonzero q (hl.symm.trans hz)

/-- The retained original face constructs q and a genuine vertical edge without caller witnesses. -/
def retainedFace : (Old S depth i).Face := BDL26UniformHistoryObstruction.retainedFace S i.val

def retainedQ : (Old S depth i).Q := (Old S depth i).faceQ (retainedFace S depth i) 0

def retainedX : (Old S depth i).X := (Old S depth i).faceX (retainedFace S depth i)

def retainedEdge : QDoubleCylinderEdge (transposePresentation (Old S depth i)) (retainedQ S depth i) S :=
  .inr ⟨retainedX S depth i,(Old S depth i).data.faceQ_xq (retainedFace S depth i) 0⟩

theorem retained_endpoints (above : 3 ≤ i.val) (c : BDL26FiniteTannerSquare.Two) (a : Upper S depth i) :
    let q := retainedQ S depth i
    let e := retainedEdge S depth i
    let u := upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))
    let b := a+canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) (edgeEndpointQ S depth i odd q e c)
    ∃ p : Potential S depth i, Pullback S depth i odd {q} (Coordinates.neighborZ (Old S depth i) {q}) a b p ∧
      parent S (i.val+1) (Vertex.x u)=none ∧
      lowerError S depth i odd a b=canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q ∧
      lowerError S depth i odd a b≠0 ∧ HammingWeight (lowerError S depth i odd a b) ≤ 1 :=
  endpoint_transport S depth i odd above _ _ c a

/-- Full original upper gradient, not a truncated local boundary. -/
def gradient (u : FamilyX S depth i.succ) : Upper S depth i :=
  (indexedFamily S depth).coboundary0 i.succ (canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) u)

theorem gradient_support (u : FamilyX S depth i.succ) :
    hammingSupport (gradient S depth i u)=upperStar S depth i u := by
  rw [gradient,indexedFamily_coboundary0,BDL26RXPhysicalStarTransport.basis_boundary_support]
  rfl

theorem gradient_localized (u : FamilyX S depth i.succ) (a : Upper S depth i) :
    Localized S depth i u a (a+gradient S depth i u) := by
  change hammingSupport (a+(a+gradient S depth i u)) ⊆ _
  rw [shift,gradient_support]

theorem gradient_cocycle (u : FamilyX S depth i.succ) :
    (indexedFamily S depth).coboundary1 i.succ (gradient S depth i u)=0 :=
  potential_cocycle S depth i (canonicalBasisWord u)

theorem gradient_run_eq (u : FamilyX S depth i.succ) (a : Upper S depth i) :
    run S depth i odd (a+gradient S depth i u)=run S depth i odd a := by
  have hs : errorSyndrome S depth i (a+gradient S depth i u)=errorSyndrome S depth i a := by
    apply Subtype.ext
    simp only [errorSyndrome,map_add,gradient_cocycle,add_zero]
  unfold run
  rw [hs]

theorem gradient_updated (u : FamilyX S depth i.succ) (a : Upper S depth i) :
    updated S depth i odd a (a+gradient S depth i u)=gradient S depth i u := by
  unfold updated
  rw [gradient_run_eq,shift,add_assoc,twice,add_zero]

theorem gradient_coarse_zero (u : FamilyX S depth i.succ) (a : Upper S depth i) :
    (run S depth i odd a).coarse.val+(run S depth i odd (a+gradient S depth i u)).coarse.val=0 := by
  rw [gradient_run_eq,twice]

theorem read0_basis (x : RZX (Old S depth i) S) :
    read0 S depth i odd (canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) (upperXChart S depth i odd x))=
      canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) x :=
  read_basis (coord0 S depth i odd) (read0 S depth i odd) (read0_apply S depth i odd) x

/-- The full global gradient is exactly the literal raw gradient under the actual charts. -/
theorem gradient_coordinates (x : RZX (Old S depth i) S) :
    read1 S depth i odd (gradient S depth i (upperXChart S depth i odd x))=
      rzCoboundary0 (Old S depth i) (state S i.val).admissible S
        (canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) x) := by
  rw [gradient,delta0_coordinates,read0_basis]

/-- All three raw gradient cases are evaluated through the original fixed parity. -/
theorem lower_gradient_coordinates (x : RZX (Old S depth i) S) (a : Upper S depth i) :
    lowerError S depth i odd a (a+gradient S depth i (upperXChart S depth i odd x))=
      rzQParity (Old S depth i) S (rzCoboundary0 (Old S depth i) (state S i.val).admissible S
        (canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) x)) := by
  rw [lowerError_coordinates,shift,gradient,delta0_coordinates,read0_basis]

/-- Both endpoints cancel under lower parity, while the complete upper expansion remains. -/
theorem q_edge_gradient (q : (Old S depth i).Q)
    (e : QDoubleCylinderEdge (transposePresentation (Old S depth i)) q S) (a : Upper S depth i) :
    read1 S depth i odd (gradient S depth i (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))))=
      rzMap1QEdgeDelta0BasisImage (Old S depth i) (state S i.val).admissible S q e ∧
    lowerError S depth i odd a (a+gradient S depth i (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))))=0 := by
  constructor
  · rw [gradient,delta0_coordinates,read0_basis]
    exact rzMap1QEdge_delta0_canonicalBasis (Old S depth i) (state S i.val).admissible S q e
  · rw [lower_gradient_coordinates]
    exact rzQParity_qEdge_coboundary (Old S depth i) (state S i.val).admissible S q e

/-- Exact coefficients at both original endpoints, not just an equality after lower parity. -/
theorem q_edge_gradient_endpoints (q : (Old S depth i).Q)
    (e : QDoubleCylinderEdge (transposePresentation (Old S depth i)) q S) :
    read1 S depth i odd (gradient S depth i (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))))
      (.inr ⟨q,qDoubleCylinderEdgeStart (transposePresentation (Old S depth i)) q S e⟩)=1 ∧
    read1 S depth i odd (gradient S depth i (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))))
      (.inr ⟨q,qDoubleCylinderEdgeEnd (transposePresentation (Old S depth i)) q S e⟩)=1 := by
  constructor
  · rw [gradient_coordinates]
    exact rzMap1QEdge_delta0_start _ _ _ _ _
  · rw [gradient_coordinates]
    exact rzMap1QEdge_delta0_end _ _ _ _ _

/-- A local-face gradient has zero lower error, keeping its full upper boundary. -/
theorem local_face_gradient (z : (Old S depth i).Z) (f : ZDoubleCylinderFace (Old S depth i) z S)
    (a : Upper S depth i) :
    lowerError S depth i odd a (a+gradient S depth i (upperXChart S depth i odd (.inl (.inl ⟨z,f⟩))))=0 := by
  rw [lower_gradient_coordinates]
  exact rzQParity_localFace_coboundary _ _ _ _ _

/-- A closed old-X gradient survives as its nontruncated lower old-X gradient, for either copy. -/
theorem old_x_gradient (x : (Old S depth i).X) (c : BDL26FiniteTannerSquare.Two) (a : Upper S depth i) :
    lowerError S depth i odd a (a+gradient S depth i (upperXChart S depth i odd (.inr (x,c))))=
      tannerCoboundary0 (Old S depth i) (canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) x) := by
  rw [lower_gradient_coordinates]
  exact rzQParity_oldX_coboundary _ _ _ _ _

/-- Internally retained-face incidence proves the lower closed word is actually nonzero. -/
theorem retained_old_x_nonzero (c : BDL26FiniteTannerSquare.Two) (a : Upper S depth i) :
    lowerError S depth i odd a
      (a+gradient S depth i (upperXChart S depth i odd (.inr (retainedX S depth i,c))))≠0 := by
  rw [old_x_gradient]
  intro hz
  have h := congrFun hz (retainedQ S depth i)
  rw [tannerCoboundary0_canonicalBasis_apply] at h
  have hi : (Old S depth i).xq (retainedX S depth i) (retainedQ S depth i)=true :=
    (Old S depth i).data.faceQ_xq (retainedFace S depth i) 0
  have hone : (1 : BDL26FiniteTannerSquare.Field)=0 := by
    simpa only [hi,if_true,Pi.zero_apply] using h
  exact one_ne_zero hone

/-- Full control: equal original syndromes/corrections and zero coarse difference coexist with nonzero lower l. -/
theorem retained_closed_transport (above : 3 ≤ i.val) (c : BDL26FiniteTannerSquare.Two) (a : Upper S depth i) :
    let u := upperXChart S depth i odd (.inr (retainedX S depth i,c))
    let b := a+gradient S depth i u
    ∃ p : Potential S depth i,
      Pullback S depth i odd (BDL26RXPhysicalStarTransport.physicalXStar (Old S depth i) (retainedX S depth i)) ∅ a b p ∧
      parent S (i.val+1) (Vertex.x u)=some (Vertex.x (retainedX S depth i)) ∧
      lowerError S depth i odd a b≠0 ∧
      (run S depth i odd b).correction=(run S depth i odd a).correction ∧
      (run S depth i odd a).coarse.val+(run S depth i odd b).coarse.val=0 ∧
      (indexedFamily S depth).coboundary1 i.castSucc (lowerError S depth i odd a b)=0 ∧
      updated S depth i odd a b=gradient S depth i u := by
  dsimp only
  have he := gradient_localized S depth i
    (upperXChart S depth i odd (.inr (retainedX S depth i,c))) a
  obtain ⟨p,hp,_,_,_,_⟩ := two_run S depth i odd above
    (upperXChart S depth i odd (.inr (retainedX S depth i,c))) _ _ he
  refine ⟨p,by simpa [Q0,Z0,rawQ0,rawZ0] using hp,parent_chart S depth i odd _,
    retained_old_x_nonzero S depth i odd c a,
    congrArg AssemblyStepOutput.correction (gradient_run_eq S depth i odd _ a),
    gradient_coarse_zero S depth i odd _ a,?_,gradient_updated S depth i odd _ a⟩
  rw [lowerError_delta,gradient_coarse_zero]

theorem self_localized (u : FamilyX S depth i.succ) (a : Upper S depth i) : Localized S depth i u a a := by
  change hammingSupport (a+a) ⊆ _
  rw [twice]
  simp [hammingSupport]

theorem self_zero_potential (u : FamilyX S depth i.succ) (a : Upper S depth i) :
    Pullback S depth i odd (Q0 S depth i odd u) (Z0 S depth i odd u) a a 0 := by
  have hz {I : Type} [Fintype I] : hammingSupport (0 : Word BDL26FiniteTannerSquare.Field I)=∅ := by
    ext r
    simp [hammingSupport]
  have hu : updated S depth i odd a a=0 := by unfold updated; rw [twice,zero_add,twice]
  simp only [Pullback,lowerError,twice,map_zero,hu,add_zero,hz,Finset.empty_subset,and_self]

theorem mixed_localized (u : FamilyX S depth i.succ) (a e f : Upper S depth i)
    (he : hammingSupport e ⊆ upperStar S depth i u) (hf : hammingSupport f ⊆ upperStar S depth i u) :
    Localized S depth i u a (a+(e+f)) := by
  change hammingSupport (a+(a+(e+f))) ⊆ _
  rw [shift]
  intro r hr
  by_contra hn
  have he0 : e r=0 := by by_contra h; exact hn (he (by simpa [hammingSupport] using h))
  have hf0 : f r=0 := by by_contra h; exact hn (hf (by simpa [hammingSupport] using h))
  exact (by simpa [hammingSupport] using hr : (e+f) r≠0) (by simp [he0,hf0])

theorem repeated_perturbation (a e : Upper S depth i) : a+(e+e)=a := by rw [twice,add_zero]

theorem no_small_depth (small : depth ≤ 2) : ¬3 ≤ i.val := by omega

section HistoryBridge
open BDL26HistorySyndromeSensitivity

/-- Each proof-prefix input is an actual entry of the unchanged original recursion. -/
private theorem prefix_entry {d : Nat} {C0 C1 C2 : LevelIndex d → Type}
    [∀ k, Fintype (C0 k)] [∀ k, Fintype (C1 k)] [∀ k, Fintype (C2 k)]
    (D : BDL26DecoderData d C0 C1 C2) (st : AlternatingStepData D) (base : AuditedBaseDecoder D)
    (n : Nat) (hn : n ≤ d) (s : D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩)
    (a : LevelIndex d) (ha : a.val ≤ n) :
    ∃ e ∈ prefixHistory D st base n hn s, e.inputSyndrome.1=a ∧
      HEq e.inputSyndrome.2 (prefixInput D st n hn s a ha) := by
  induction n generalizing a with
  | zero =>
    have hz : a=⟨0,Nat.lt_succ_of_le hn⟩ := Fin.ext (by change a.val=0; omega)
    subst a
    let b : RecursiveBaseLevelCorrection D :=
      {input := s,correction := base.decode s,relation := (base.rightInverse s).symm}
    refine ⟨.base b,?_,rfl,?_⟩
    · rw [prefixHistory]
      exact List.mem_singleton_self _
    · rw [prefixInput_self]
      rfl
  | succ n ih =>
    by_cases h : a.val=n+1
    · have ha' : a=⟨n+1,Nat.lt_succ_of_le hn⟩ := Fin.ext h
      subst a
      let k : StepIndex d := ⟨n,by omega⟩
      let out := st.step k s
      refine ⟨.step k out,?_,rfl,?_⟩
      · rw [prefixHistory]
        exact List.mem_cons_self
      · rw [prefixInput_self]
        exact heq_of_eq ((st.relation k).input_eq s)
    · have hal : a.val ≤ n := by omega
      obtain ⟨e,he,hae,his⟩ := ih (by omega) (st.step ⟨n,by omega⟩ s).coarse a hal
      refine ⟨e,?_,hae,?_⟩
      · rw [prefixHistory]
        exact List.mem_cons_of_mem _ he
      · rw [prefixInput_succ D st n hn s a hal]
        exact his

/-- The original unique stored input equals the proved traversal of that SAME history. -/
theorem original_input_eq (S : OddScale) (n : Nat) (s : TopInput S n) (a : LevelIndex n) :
    BDL26CanonicalHistoryMarks.inputAt S n s a=actualInputs S n s a := by
  obtain ⟨e,he,ha,hi⟩ := prefix_entry (SuffixData S n)
    (LevelTwoHistory.suffixSteps _ (BDL26OwnerIncidenceMasks.actualAboveTwoSteps S n))
    (BDL26OwnerIncidenceMasks.actualBase S n) n (Nat.le_refl _) s a (Nat.le_of_lt_succ a.isLt)
  have hm : e ∈ BDL26OwnerIncidenceMasks.actualHistory S n s := by
    change e ∈ buildCorrectionHistory (SuffixData S n)
      (LevelTwoHistory.suffixSteps _ (BDL26OwnerIncidenceMasks.actualAboveTwoSteps S n))
      (BDL26OwnerIncidenceMasks.actualBase S n) s
    rw [← prefixHistory_top_eq (SuffixData S n)
      (LevelTwoHistory.suffixSteps _ (BDL26OwnerIncidenceMasks.actualAboveTwoSteps S n))
      (BDL26OwnerIncidenceMasks.actualBase S n) s]
    exact he
  have hh : HEq (BDL26CanonicalHistoryMarks.entryAt S n s a).inputSyndrome.2
      (actualInputs S n s a) := by
    rw [BDL26CanonicalHistoryMarks.entryAt_eq S n s a e hm ha]
    exact hi
  exact eq_of_heq (rec_heq_of_heq (BDL26CanonicalHistoryMarks.entryAt_spec S n s a).2 hh)

/-- Adjacent stored inputs use precisely the previous selected coarse output. -/
theorem original_input_step (S : OddScale) (n : Nat) (s : TopInput S n) (k : StepIndex n) :
    BDL26CanonicalHistoryMarks.inputAt S n s k.castSucc=
      (BDL26CanonicalHistoryMarks.outputAt S n s k).coarse := by
  rw [original_input_eq,BDL26CanonicalHistoryMarks.outputAt,original_input_eq]
  exact actualInputs_step S n s k
end HistoryBridge

section Adjacent

/-- The immediately lower actual RX step; its successor is the RZ lower level. -/
def rxStep (j : Nat) : StepIndex (2*j+4) := ⟨2*j+2,by omega⟩
theorem rxStep_even (j : Nat) : (rxStep j).val%2=0 := by simp [rxStep]

theorem adjacent_levels (j : Nat) : (rxStep j).succ=(topStep j).castSucc := Fin.ext rfl

/-- The lower word is the FIXED RZ parity, never a chosen gauge representative. -/
def firstLower (S : OddScale) (j : Nat) (a b : Upper S (2*j+4) (topStep j)) :
    BDL26RXErrorPullback.Upper S (2*j+4) (rxStep j) :=
  lowerError S (2*j+4) (topStep j) (topStep_odd j) a b

/-- One representative obtained internally from the actual first coarse syndrome's validity. -/
def firstRepresentative (S : OddScale) (j : Nat) (a : Upper S (2*j+4) (topStep j)) :
    BDL26RXErrorPullback.Upper S (2*j+4) (rxStep j) :=
  Classical.choose ((run S (2*j+4) (topStep j) (topStep_odd j) a).coarse.property)

theorem firstRepresentative_spec (S : OddScale) (j : Nat) (a : Upper S (2*j+4) (topStep j)) :
    (indexedFamily S (2*j+4)).coboundary1 (rxStep j).succ (firstRepresentative S j a)=
      (run S (2*j+4) (topStep j) (topStep_odd j) a).coarse.val :=
  Classical.choose_spec ((run S (2*j+4) (topStep j) (topStep_odd j) a).coarse.property)

/-- Correlate the second representative by the fixed difference; never independently choose it. -/
def secondRepresentative (S : OddScale) (j : Nat) (a b : Upper S (2*j+4) (topStep j)) :
    BDL26RXErrorPullback.Upper S (2*j+4) (rxStep j) := firstRepresentative S j a+firstLower S j a b

/-- Both original coarse inputs and the full fixed difference are retained. -/
theorem representatives_spec (S : OddScale) (j : Nat) (a b : Upper S (2*j+4) (topStep j)) :
    (indexedFamily S (2*j+4)).coboundary1 (rxStep j).succ (firstRepresentative S j a)=
      (run S (2*j+4) (topStep j) (topStep_odd j) a).coarse.val ∧
    (indexedFamily S (2*j+4)).coboundary1 (rxStep j).succ (secondRepresentative S j a b)=
      (run S (2*j+4) (topStep j) (topStep_odd j) b).coarse.val ∧
    firstRepresentative S j a+secondRepresentative S j a b=firstLower S j a b := by
  refine ⟨firstRepresentative_spec S j a,?_,?_⟩
  · rw [secondRepresentative,map_add,firstRepresentative_spec]
    have hl := lowerError_delta S (2*j+4) (topStep j) (topStep_odd j) a b
    change (indexedFamily S (2*j+4)).coboundary1 (rxStep j).succ (firstLower S j a b)=_ at hl
    rw [hl]
    let zA : Word BDL26FiniteTannerSquare.Field (state S (2*j+3)).presentation.Z :=
      (run S (2*j+4) (topStep j) (topStep_odd j) a).coarse.val
    let zB : Word BDL26FiniteTannerSquare.Field (state S (2*j+3)).presentation.Z :=
      (run S (2*j+4) (topStep j) (topStep_odd j) b).coarse.val
    change zA+(zA+zB)=zB
    exact shift zA zB
  · change firstRepresentative S j a+(firstRepresentative S j a+firstLower S j a b)=_
    exact shift _ _

/-- The literal next canonical output on the original coarse input. -/
def nextOutput (S : OddScale) (j : Nat) (a : Upper S (2*j+4) (topStep j)) :
    AssemblyStepOutput (indexedDecoderData S (2*j+4)) (rxStep j) :=
  BDL26OwnerIncidenceMasks.actualStep S (2*j+4) (rxStep j) (run S (2*j+4) (topStep j) (topStep_odd j) a).coarse

/-- The next stored run's input is exactly the original first coarse input. -/
theorem nextOutput_input (S : OddScale) (j : Nat) (a : Upper S (2*j+4) (topStep j)) :
    (nextOutput S j a).input=(topOutput S j a).coarse := by
  rw [topOutput_eq]
  exact (BDL26OwnerIncidenceMasks.actualStep_relation S (2*j+4) (rxStep j)).input_eq _

/-- The reconstructed representatives give the SAME full canonical outputs, not only the same corrections. -/
theorem nextOutput_run (S : OddScale) (j : Nat) (a b : Upper S (2*j+4) (topStep j)) :
    BDL26RXErrorPullback.run S (2*j+4) (rxStep j) (rxStep_even j) (firstRepresentative S j a)=nextOutput S j a ∧
    BDL26RXErrorPullback.run S (2*j+4) (rxStep j) (rxStep_even j) (secondRepresentative S j a b)=nextOutput S j b := by
  have hA : BDL26RXErrorPullback.errorSyndrome S (2*j+4) (rxStep j) (firstRepresentative S j a)=
      (run S (2*j+4) (topStep j) (topStep_odd j) a).coarse :=
    Subtype.ext (representatives_spec S j a b).1
  have hB : BDL26RXErrorPullback.errorSyndrome S (2*j+4) (rxStep j) (secondRepresentative S j a b)=
      (run S (2*j+4) (topStep j) (topStep_odd j) b).coarse :=
    Subtype.ext (representatives_spec S j a b).2.1
  constructor
  · rw [BDL26RXErrorPullback.run,hA,nextOutput,BDL26OwnerIncidenceMasks.actualStep_rx S (2*j+4) (rxStep j) (rxStep_even j)]
  · rw [BDL26RXErrorPullback.run,hB,nextOutput,BDL26OwnerIncidenceMasks.actualStep_rx S (2*j+4) (rxStep j) (rxStep_even j)]

def nextSnapshotIndex (j : Nat) : StepIndex (2*j+2) := ⟨2*j,by omega⟩

/-- The next full output really is the unique next snapshot of the original stopped history. -/
theorem nextOutput_snapshot (S : OddScale) (j : Nat) (a : Upper S (2*j+4) (topStep j)) :
    nextOutput S j a=BDL26CanonicalHistoryMarks.outputAt S (2*j+2)
      (errorSyndrome S (2*j+4) (topStep j) a) (nextSnapshotIndex j) := by
  let s := errorSyndrome S (2*j+4) (topStep j) a
  let t : StepIndex (2*j+2) := Fin.last (2*j+1)
  have hc := original_input_step S (2*j+2) s t
  have ht : BDL26CanonicalHistoryMarks.outputAt S (2*j+2) s t=
      run S (2*j+4) (topStep j) (topStep_odd j) a := topOutput_eq S j a
  have hinput : BDL26CanonicalHistoryMarks.inputAt S (2*j+2) s
      (nextSnapshotIndex j).succ=
      (run S (2*j+4) (topStep j) (topStep_odd j) a).coarse := by
    change BDL26CanonicalHistoryMarks.inputAt S (2*j+2) s t.castSucc=_
    exact hc.trans (congrArg (fun O : AssemblyStepOutput
      (indexedDecoderData S (2*j+4)) (topStep j) => O.coarse) ht)
  change BDL26OwnerIncidenceMasks.actualStep S (2*j+4) (rxStep j)
      (run S (2*j+4) (topStep j) (topStep_odd j) a).coarse=
    BDL26OwnerIncidenceMasks.actualStep S (2*j+4) (rxStep j)
      (BDL26CanonicalHistoryMarks.inputAt S (2*j+2) s (nextSnapshotIndex j).succ)
  exact congrArg (BDL26OwnerIncidenceMasks.actualStep S (2*j+4) (rxStep j)) hinput.symm

/-- Fixed physical centre of the first lower star. -/
def middleX (S : OddScale) (j : Nat) (u : FamilyX S (2*j+4) (topStep j).succ) :=
  downX S (2*j+4) (topStep j) (topStep_odd j) u

def secondLower (S : OddScale) (j : Nat) (u : FamilyX S (2*j+4) (topStep j).succ)
    (a b : Upper S (2*j+4) (topStep j)) :=
  BDL26RXPhysicalStarTransport.L S (2*j+4) (rxStep j) (rxStep_even j) (middleX S j u)
    (firstRepresentative S j a) (secondRepresentative S j a b)

def secondPotential (S : OddScale) (j : Nat) (u : FamilyX S (2*j+4) (topStep j).succ)
    (a b : Upper S (2*j+4) (topStep j)) :=
  BDL26RXPhysicalStarTransport.Phi S (2*j+4) (rxStep j) (rxStep_even j) (middleX S j u)
    (firstRepresentative S j a) (secondRepresentative S j a b)

def composedPotential (S : OddScale) (j : Nat) (u : FamilyX S (2*j+4) (topStep j).succ)
    (a b : Upper S (2*j+4) (topStep j)) (p : Potential S (2*j+4) (topStep j)) :=
  p+((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map0 (secondPotential S j u a b)

/-- The RX locality premise is derived, with both actual original coarse inputs. -/
theorem adjacent_localized (S : OddScale) (j : Nat) (u : FamilyX S (2*j+4) (topStep j).succ)
    (a b : Upper S (2*j+4) (topStep j))
    (he : Localized S (2*j+4) (topStep j) u a b) :
    BDL26RXPhysicalStarTransport.Localized S (2*j+4) (rxStep j) (middleX S j u)
      (firstRepresentative S j a) (secondRepresentative S j a b) := by
  change hammingSupport (firstRepresentative S j a+secondRepresentative S j a b) ⊆ _
  rw [(representatives_spec S j a b).2.2]
  exact lower_physical_supported S (2*j+4) (topStep j) (topStep_odd j) (by simp [topStep]) u a b he

/-- The complete RX result, including its raw parent, same-run corrections, full q and seven bound. -/
theorem adjacent_RX (S : OddScale) (j : Nat) (u : FamilyX S (2*j+4) (topStep j).succ)
    (a b : Upper S (2*j+4) (topStep j))
    (he : Localized S (2*j+4) (topStep j) u a b) :
    parent S ((rxStep j).val+1) (Vertex.x (middleX S j u))=
      some (Vertex.x (BDL26RXPhysicalStarTransport.parentX S (2*j+4) (rxStep j) (rxStep_even j) (middleX S j u))) ∧
    ((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).map1 (secondLower S j u a b)=
      firstLower S j a b+(nextOutput S j a).correction+(nextOutput S j b).correction+
        (indexedFamily S (2*j+4)).coboundary0 (rxStep j).succ (secondPotential S j u a b) ∧
    (indexedFamily S (2*j+4)).coboundary1 (rxStep j).castSucc (secondLower S j u a b)=
      (nextOutput S j a).coarse.val+(nextOutput S j b).coarse.val ∧
    hammingSupport ((nextOutput S j a).correction+(nextOutput S j b).correction) ⊆
      BDL26RXXStarTransport.star1 S (2*j+4) (rxStep j) (rxStep_even j)
        (BDL26RXPhysicalStarTransport.parentX S (2*j+4) (rxStep j) (rxStep_even j) (middleX S j u)) ∧
    hammingSupport (secondPotential S j u a b) ⊆
      BDL26RXXStarTransport.degreeZeroBlock S (2*j+4) (rxStep j) (rxStep_even j)
        (BDL26RXPhysicalStarTransport.parentX S (2*j+4) (rxStep j) (rxStep_even j) (middleX S j u)) ∧
    hammingSupport (secondLower S j u a b) ⊆ BDL26RXPhysicalStarTransport.physicalXStar
      (state S (rxStep j).val).presentation
        (BDL26RXPhysicalStarTransport.parentX S (2*j+4) (rxStep j) (rxStep_even j) (middleX S j u)) ∧
    HammingWeight (secondLower S j u a b) ≤ 7 := by
  have h := BDL26RXPhysicalStarTransport.two_run S (2*j+4) (rxStep j) (rxStep_even j)
    (middleX S j u) (firstRepresentative S j a) (secondRepresentative S j a b)
    (adjacent_localized S j u a b he)
  simpa only [secondLower,secondPotential,BDL26RXErrorPullback.updated,
    (nextOutput_run S j a b).1,(nextOutput_run S j a b).2,(representatives_spec S j a b).2.2,
    BDL26RXErrorPullback.coarseSum] using h

/-- Actual cochain compatibility transports the FULL q, not just its boundary support. -/
theorem composed_boundary (S : OddScale) (j : Nat) (u : FamilyX S (2*j+4) (topStep j).succ)
    (a b : Upper S (2*j+4) (topStep j)) (p : Potential S (2*j+4) (topStep j)) :
    (indexedFamily S (2*j+4)).coboundary0 (topStep j).succ (composedPotential S j u a b p)=
      (indexedFamily S (2*j+4)).coboundary0 (topStep j).succ p+
      ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map1
        ((indexedFamily S (2*j+4)).coboundary0 (rxStep j).succ (secondPotential S j u a b)) := by
  rw [composedPotential,map_add]
  have h := LinearMap.congr_fun
    (((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).commutes_coboundary0)
    (secondPotential S j u a b)
  exact congrArg (fun w => (indexedFamily S (2*j+4)).coboundary0 (topStep j).succ p+w) h

/-- The composite image keeps full E, both next original corrections and p+FZ.map0(q). -/
theorem composed_equation (S : OddScale) (j : Nat) (u : FamilyX S (2*j+4) (topStep j).succ)
    (a b : Upper S (2*j+4) (topStep j))
    (he : Localized S (2*j+4) (topStep j) u a b)
    (p : Potential S (2*j+4) (topStep j))
    (hp : Pullback S (2*j+4) (topStep j) (topStep_odd j)
      (Q0 S (2*j+4) (topStep j) (topStep_odd j) u)
      (Z0 S (2*j+4) (topStep j) (topStep_odd j) u) a b p) :
    ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map1
      (((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).map1 (secondLower S j u a b))=
      a+b+(topOutput S j a).correction+(topOutput S j b).correction+
      ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map1
        ((nextOutput S j a).correction+(nextOutput S j b).correction)+
      (indexedFamily S (2*j+4)).coboundary0 (topStep j).succ (composedPotential S j u a b p) := by
  let F : Word BDL26FiniteTannerSquare.Field (state S (2*j+3)).presentation.Q →ₗ[
      BDL26FiniteTannerSquare.Field]
      Word BDL26FiniteTannerSquare.Field (state S (2*j+4)).presentation.Q :=
    ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map1
  let x : Word BDL26FiniteTannerSquare.Field (state S (2*j+3)).presentation.Q :=
    firstLower S j a b
  let cA : Word BDL26FiniteTannerSquare.Field (state S (2*j+3)).presentation.Q :=
    (nextOutput S j a).correction
  let cB : Word BDL26FiniteTannerSquare.Field (state S (2*j+3)).presentation.Q :=
    (nextOutput S j b).correction
  let q : Word BDL26FiniteTannerSquare.Field (state S (2*j+3)).presentation.Q :=
    (indexedFamily S (2*j+4)).coboundary0 (rxStep j).succ (secondPotential S j u a b)
  let y : Word BDL26FiniteTannerSquare.Field (state S (2*j+3)).presentation.Q :=
    ((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).map1 (secondLower S j u a b)
  let e : Word BDL26FiniteTannerSquare.Field (state S (2*j+4)).presentation.Q :=
    updated S (2*j+4) (topStep j) (topStep_odd j) a b
  let dp : Word BDL26FiniteTannerSquare.Field (state S (2*j+4)).presentation.Q :=
    (indexedFamily S (2*j+4)).coboundary0 (topStep j).succ p
  let r : Word BDL26FiniteTannerSquare.Field (state S (2*j+4)).presentation.Q :=
    (indexedFamily S (2*j+4)).coboundary0 (topStep j).succ (composedPotential S j u a b p)
  have hX : y=x+cA+cB+q := (adjacent_RX S j u a b he).2.1
  have hF : F y=F (x+cA+cB+q) := congrArg F hX
  have hz : F x=e+dp := hp.1
  have hd : r=dp+F q := composed_boundary S j u a b p
  have ha : F (x+cA+cB+q)=e+F (cA+cB)+r :=
    full_linear_composition F x cA cB q e dp r hz hd
  rw [topOutput_eq,topOutput_eq]
  change F y=e+F (cA+cB)+r
  exact hF.trans ha

/-- The composed full potential is a cocycle boundary under the same upper complex. -/
theorem composed_cocycle (S : OddScale) (j : Nat) (u : FamilyX S (2*j+4) (topStep j).succ)
    (a b : Upper S (2*j+4) (topStep j)) (p : Potential S (2*j+4) (topStep j)) :
    (indexedFamily S (2*j+4)).coboundary1 (topStep j).succ
      ((indexedFamily S (2*j+4)).coboundary0 (topStep j).succ (composedPotential S j u a b p))=0 :=
  potential_cocycle S (2*j+4) (topStep j) (composedPotential S j u a b p)

/-- Both original selected map2 images retain the actual twice-coarsened difference. -/
theorem composed_syndrome (S : OddScale) (j : Nat) (u : FamilyX S (2*j+4) (topStep j).succ)
    (a b : Upper S (2*j+4) (topStep j))
    (he : Localized S (2*j+4) (topStep j) u a b) :
    (indexedFamily S (2*j+4)).coboundary1 (topStep j).succ
      (((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map1
        (((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).map1 (secondLower S j u a b)))=
      ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map2
        (((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).map2
          ((nextOutput S j a).coarse.val+(nextOutput S j b).coarse.val)) := by
  have hZ := LinearMap.congr_fun
    (((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).commutes_coboundary1)
    (((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).map1 (secondLower S j u a b))
  have hX := LinearMap.congr_fun
    (((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).commutes_coboundary1)
    (secondLower S j u a b)
  calc
    _ = ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map2
        ((indexedFamily S (2*j+4)).coboundary1 (rxStep j).succ
          (((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).map1 (secondLower S j u a b))) := hZ
    _ = ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map2
        (((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).map2
          ((indexedFamily S (2*j+4)).coboundary1 (rxStep j).castSucc (secondLower S j u a b))) :=
      congrArg (((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map2) hX
    _ = _ := by rw [(adjacent_RX S j u a b he).2.2.1]

/-- Mandatory adjacent endpoint: p is internally constructed, and both snapshots are the actual histories. -/
theorem top_adjacent_two_run (S : OddScale) (j : Nat) (u : FamilyX S (2*j+4) (topStep j).succ)
    (a b : Upper S (2*j+4) (topStep j))
    (he : Localized S (2*j+4) (topStep j) u a b) :
    ∃ p : Potential S (2*j+4) (topStep j),
      Pullback S (2*j+4) (topStep j) (topStep_odd j)
        (Q0 S (2*j+4) (topStep j) (topStep_odd j) u)
        (Z0 S (2*j+4) (topStep j) (topStep_odd j) u) a b p ∧
      (∀ x : (Old S (2*j+4) (topStep j)).X, ∀ c : BDL26FiniteTannerSquare.Two,
        read0 S (2*j+4) (topStep j) (topStep_odd j) p (.inr (x,c))=0) ∧
      ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map1
        (((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).map1 (secondLower S j u a b))=
        a+b+(topOutput S j a).correction+(topOutput S j b).correction+
        ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map1
          ((nextOutput S j a).correction+(nextOutput S j b).correction)+
        (indexedFamily S (2*j+4)).coboundary0 (topStep j).succ (composedPotential S j u a b p) ∧
      (indexedFamily S (2*j+4)).coboundary1 (rxStep j).castSucc (secondLower S j u a b)=
        (nextOutput S j a).coarse.val+(nextOutput S j b).coarse.val ∧
      HammingWeight (secondLower S j u a b) ≤ 7 ∧
      nextOutput S j a=BDL26CanonicalHistoryMarks.outputAt S (2*j+2)
        (errorSyndrome S (2*j+4) (topStep j) a) (nextSnapshotIndex j) ∧
      nextOutput S j b=BDL26CanonicalHistoryMarks.outputAt S (2*j+2)
        (errorSyndrome S (2*j+4) (topStep j) b) (nextSnapshotIndex j) := by
  obtain ⟨p,hp,_,_,_,hx⟩ := two_run S (2*j+4) (topStep j) (topStep_odd j)
    (by simp [topStep]) u a b he
  have hr := adjacent_RX S j u a b he
  exact ⟨p,hp,hx,composed_equation S j u a b he p hp,hr.2.2.1,hr.2.2.2.2.2.2,
    nextOutput_snapshot S j a,nextOutput_snapshot S j b⟩

/-- Literal arithmetic C4→C3→C2; no decoder below the stopped boundary is introduced. -/
theorem depth_four_indices : (topStep 0).val=3 ∧ (rxStep 0).val=2 ∧
    (topStep 0).succ.val=4 ∧ (rxStep 0).castSucc.val=2 := by decide

end Adjacent
end QEC.Coding.BDL26RZPhysicalXStarTransport
