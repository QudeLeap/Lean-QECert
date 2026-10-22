import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.FirstZeroQVertexTower
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.BoundaryTailInvariance

/-!
# Higher RX face-edge seeds in the original two histories

Project-derived internal restriction of BDL26 paper.tex3136–3185,3453–3480
(SHA256 66d1927b20efccb757da40af3d291e4738c60054799812393e0a739abcc73e5b).
At C_(2j+5), the RX local-edge owner is a literal RZ local-Z face.
The SAME fixed-total histories first reach the whole physical face star,
then a zero word at suffix2j+1. The intermediate word need not vanish.
Both actual potentials and all accumulated terms are retained. This proves
all-u chiX and X/SAME-Y dressed-Z protection on this generated family,
not arbitrary RX owners, general-coordinate stability, chiZ/full XYZ,
ALL-component locality, Peierls, Gibbs or lifetime.
-/
noncomputable section
namespace QEC.Coding.BDL26HigherRXFaceTower
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26TransposedStoppedDecoder
open PauliSymplectic
open scoped Classical BigOperators

private theorem pOdd (j : Nat) : ¬(2*j+3)%2=0 := by omega
private theorem mEven (j : Nat) : (2*j+4)%2=0 := by omega

/-- Actual local-Z face owner in C_(2j+4), with parity derived from j. -/
def faceOwner (S : OddScale) (j : Nat) (z : (state S (2*j+3)).presentation.Z)
    (f : ZDoubleCylinderFace (state S (2*j+3)).presentation z S) :
    (state S (2*j+4)).presentation.X :=
  BDL26RZPhysicalXStarTransport.upperXChart S (2*j+4) ⟨2*j+3,by omega⟩ (pOdd j)
    (.inl (.inl ⟨z,f⟩))

/-- Only original z, local face, and local X-edge coordinate data. -/
abbrev SeedData (S : OddScale) (j : Nat) :=
  Σ z : (state S (2*j+3)).presentation.Z,
    Σ f : ZDoubleCylinderFace (state S (2*j+3)).presentation z S,
      DoubleCylinderEdge (state S (2*j+4)).presentation (faceOwner S j z f) S

def seedPhysical (S : OddScale) (j : Nat) (a : SeedData S j) : Physical S (2*j+5) :=
  BDL26RXDecoderAdapter.rxPhysicalQEquiv S (2*j+5) ⟨2*j+4,by omega⟩ (mEven j)
    (.inl ⟨faceOwner S j a.1 a.2.1,a.2.2⟩)

inductive Family (S : OddScale) : (n : Nat) → Physical S (n+2) → Type
  | seed (j : Nat) (a : SeedData S j) : Family S (2*j+3) (seedPhysical S j a)
  | rx {n : Nat} {q : Physical S (n+2)} (t : Family S n q) (he : (n+2)%2=0)
      (v : QDoubleCylinderVertex (state S (n+2)).presentation q S) :
      Family S (n+1) (BDL26FirstZeroQVertexTower.rxVertex S (n+2) he q v)
  | rz {n : Nat} {q : Physical S (n+2)} (t : Family S n q) (ho : ¬(n+2)%2=0)
      (v : QDoubleCylinderVertex (transposePresentation (state S (n+2)).presentation) q S) :
      Family S (n+1) (BDL26FirstZeroQVertexTower.rzVertex S (n+2) ho q v)

def stopDepth {S : OddScale} {n : Nat} {q : Physical S (n+2)} : Family S n q → Nat
  | .seed j _ => 2*j+1
  | .rx t _ _ => stopDepth t
  | .rz t _ _ => stopDepth t

theorem stopDepth_pos {S : OddScale} {n : Nat} {q : Physical S (n+2)}
    (t : Family S n q) : 1 ≤ stopDepth t := by
  induction t with
  | seed j a => dsimp only [stopDepth]; omega
  | rx t he v ih => exact ih
  | rz t ho v ih => exact ih

theorem stopDepth_gap {S : OddScale} {n : Nat} {q : Physical S (n+2)}
    (t : Family S n q) : stopDepth t+2 ≤ n := by
  induction t with
  | seed j a => exact Nat.le_refl _
  | rx t he v ih => dsimp only [stopDepth]; omega
  | rz t ho v ih => dsimp only [stopDepth]; omega

theorem no_low_seed (S : OddScale) (n : Nat) (hn : n ≤ 2) (q : Physical S (n+2)) :
    Family S n q → False := by
  intro t
  have hp := stopDepth_pos t
  have hg := stopDepth_gap t
  omega

def stopIndex {S : OddScale} {n : Nat} {q : Physical S (n+2)} (t : Family S n q) :
    LevelIndex n := ⟨stopDepth t,by have h:=stopDepth_gap t; omega⟩

def rxIndex (N j : Nat) (hN : 2*j+3 ≤ N) : StepIndex N := ⟨2*j+2,by omega⟩
def rzIndex (N j : Nat) (hN : 2*j+3 ≤ N) : StepIndex N := ⟨2*j+1,by omega⟩

theorem seed_indices (N j : Nat) (hN : 2*j+3 ≤ N) :
    (rxIndex N j hN).val+2=2*j+4 ∧ (rzIndex N j hN).val+2=2*j+3 ∧
      (rzIndex N j hN).succ=(rxIndex N j hN).castSucc :=
  ⟨rfl,rfl,Fin.ext rfl⟩

theorem rx_index_even (N j : Nat) (hN : 2*j+3 ≤ N) :
    (BDL26LocalizedHistoryErrorDescent.Edge N (rxIndex N j hN)).val%2=0 := mEven j
theorem rz_index_odd (N j : Nat) (hN : 2*j+3 ≤ N) :
    ¬(BDL26LocalizedHistoryErrorDescent.Edge N (rzIndex N j hN)).val%2=0 := pOdd j

/-- Ambient TOTAL changes only proof indices, never the original physical chart. -/
theorem seed_physical_ambient (S : OddScale) (N j : Nat) (hN : 2*j+3 ≤ N)
    (a : SeedData S j) :
    seedPhysical S j a=BDL26RXDecoderAdapter.rxPhysicalQEquiv S (N+2)
      (BDL26LocalizedHistoryErrorDescent.Edge N (rxIndex N j hN)) (rx_index_even N j hN)
      (.inl ⟨faceOwner S j a.1 a.2.1,a.2.2⟩) := rfl

theorem face_owner_ambient (S : OddScale) (N j : Nat) (hN : 2*j+3 ≤ N)
    (z : (state S (2*j+3)).presentation.Z)
    (f : ZDoubleCylinderFace (state S (2*j+3)).presentation z S) :
    faceOwner S j z f=BDL26RZPhysicalXStarTransport.upperXChart S (N+2)
      (BDL26LocalizedHistoryErrorDescent.Edge N (rzIndex N j hN)) (rz_index_odd N j hN)
      (.inl (.inl ⟨z,f⟩)) := rfl

/-- General-index actual RX owner, proved from materialized incidence. -/
theorem rx_local_edge_parent (S : OddScale) (d : Nat) (i : StepIndex d) (he : i.val%2=0)
    (u : FamilyX S d i.succ) (x : (state S i.val).presentation.X)
    (e : DoubleCylinderEdge (state S i.val).presentation x S)
    (hu : BDL26RXDecoderAdapter.rxPhysicalQEquiv S d i he (.inl ⟨x,e⟩) ∈
      BDL26RXPhysicalStarTransport.physicalXStar (state S (i.val+1)).presentation u) :
    BDL26RXPhysicalStarTransport.parentX S d i he u=x := by
  obtain ⟨r,rfl⟩ := (BDL26RXDecoderAdapter.rxDegreeZeroEquiv S d i he).surjective u
  have hi := (BDL26RXPhysicalStarTransport.mem_physicalXStar _ _ _).mp hu
  rw [BDL26RXDecoderAdapter.rxPhysical_incidence] at hi
  have hr := BDL26RXPhysicalStarTransport.raw_local_edge_owner (state S i.val).presentation S
    r ⟨x,e⟩ hi
  change ((BDL26RXDecoderAdapter.rxDegreeZeroEquiv S d i he).symm
    (BDL26RXDecoderAdapter.rxDegreeZeroEquiv S d i he r)).1=x
  rw [Equiv.symm_apply_apply]
  exact hr

private theorem word_smul_zero {I : Type} (w : Word F I) : (0 : F) • w=0 := by
  funext r
  exact zero_mul _

private theorem word_smul_one {I : Type} (w : Word F I) : (1 : F) • w=w := by
  funext r
  exact one_mul _

private theorem bit_cases (c : F) : c=0 ∨ c=1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem scalar_singleton {I : Type} [Fintype I] [DecidableEq I]
    (w : Word F I) (q : I) (hw : hammingSupport w ⊆ {q}) :
    ∃ c : F, w=c • canonicalBasisWord q := by
  refine ⟨w q,?_⟩
  funext r
  by_cases hr : r=q
  · subst r
    simp [canonicalBasisWord]
  · have hz : w r=0 := by
      by_contra hn
      exact hr (Finset.mem_singleton.mp
        (hw (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)))
    simp [canonicalBasisWord,hr,hz]

private theorem basis_singleton {I : Type} [Fintype I] [DecidableEq I] (q : I) :
    hammingSupport (canonicalBasisWord (F:=F) q) ⊆ {q} := by
  intro r hr
  by_contra hn
  have hne : r≠q := by simpa only [Finset.mem_singleton] using hn
  have hz : canonicalBasisWord (F:=F) q r=0 := by simp [canonicalBasisWord,hne]
  exact (Finset.mem_filter.mp hr).2 hz

section FixedTotal
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)

private theorem step_rx_singleton (i : StepIndex n) (h : (i.val+2)%2=0)
    (u : BDL26LocalizedHistoryErrorDescent.LocalizedWord S n sigma tau i.succ)
    (q : Physical S (i.val+2))
    (v : QDoubleCylinderVertex (state S (i.val+2)).presentation q S)
    (hu : hammingSupport u.word ⊆ {BDL26FirstZeroQVertexTower.rxVertex S (i.val+2) h q v}) :
    (BDL26LocalizedHistoryErrorDescent.step S n sigma tau i u).potential=0 ∧
    hammingSupport (BDL26LocalizedHistoryErrorDescent.step S n sigma tau i u).lower.word ⊆ {q} := by
  have hh : (BDL26LocalizedHistoryErrorDescent.Edge n i).val%2=0 := by
    simpa only [BDL26LocalizedHistoryErrorDescent.Edge,LevelTwoHistory.physicalStep_val] using h
  have he : hammingSupport
      (BDL26LocalizedHistoryErrorDescent.first S n sigma i+
        BDL26LocalizedHistoryErrorDescent.second S n sigma tau i u) ⊆
      (BDL26RXDecoderAdapter.rxLq S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i) hh).correctionRegion q := by
    rw [BDL26LocalizedHistoryErrorDescent.representatives_difference]
    intro r hr
    have heq : r=BDL26FirstZeroQVertexTower.rxVertex S (i.val+2) h q v := Finset.mem_singleton.mp (hu hr)
    subst r
    exact (BDL26RXDecoderAdapter.rxQVertexEquiv S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i) hh q v).property
  have hz := BDL26FirstZeroQVertexTower.rx_computed_parent S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i) hh q _ _ he u.center
  rw [BDL26LocalizedHistoryErrorDescent.step_rx S n sigma tau i hh u]
  constructor
  · exact hz.1
  · change hammingSupport (BDL26RXPhysicalStarTransport.L S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i) hh
      u.center _ _) ⊆ {q}
    rw [hz.2]
    exact BDL26RXQBlockTransport.lower_supported S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i) hh q _ _

private theorem step_rz_singleton (i : StepIndex n) (h : ¬(i.val+2)%2=0)
    (u : BDL26LocalizedHistoryErrorDescent.LocalizedWord S n sigma tau i.succ)
    (q : Physical S (i.val+2))
    (v : QDoubleCylinderVertex (transposePresentation (state S (i.val+2)).presentation) q S)
    (hu : hammingSupport u.word ⊆ {BDL26FirstZeroQVertexTower.rzVertex S (i.val+2) h q v}) :
    hammingSupport (BDL26LocalizedHistoryErrorDescent.step S n sigma tau i u).lower.word ⊆ {q} := by
  have hh : ¬(BDL26LocalizedHistoryErrorDescent.Edge n i).val%2=0 := by
    simpa only [BDL26LocalizedHistoryErrorDescent.Edge,LevelTwoHistory.physicalStep_val] using h
  obtain ⟨c,hc⟩ := scalar_singleton u.word _ hu
  have hcases : c=0 ∨ c=1 := bit_cases c
  rw [BDL26LocalizedHistoryErrorDescent.step_rz S n sigma tau i hh u]
  change hammingSupport (BDL26RZFiniteBlockTransport.lowerError S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i) hh
    (BDL26LocalizedHistoryErrorDescent.first S n sigma i)
    (BDL26LocalizedHistoryErrorDescent.second S n sigma tau i u)) ⊆ {q}
  rcases hcases with rfl | rfl
  · have hw : u.word=0 := hc.trans (word_smul_zero _)
    rw [BDL26RZFiniteBlockTransport.lowerError_coordinates,
      BDL26LocalizedHistoryErrorDescent.representatives_difference,hw,map_zero,map_zero]
    simp [hammingSupport]
  · have hw : u.word=canonicalBasisWord (BDL26FirstZeroQVertexTower.rzVertex S (i.val+2) h q v) :=
      hc.trans (word_smul_one _)
    have hw' : u.word=(canonicalBasisWord
        (BDL26RZPhysicalStarTransport.physicalQ S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i) hh q v) :
        BDL26RZErrorPullback.Upper S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i)) := hw
    change hammingSupport (BDL26RZFiniteBlockTransport.lowerError S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i) hh
      (BDL26LocalizedHistoryErrorDescent.first S n sigma i)
      (BDL26LocalizedHistoryErrorDescent.first S n sigma i+u.word)) ⊆ {q}
    rw [hw']
    have hl := BDL26RZPhysicalStarTransport.lower_physicalQ_basis S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i) hh
      (BDL26LocalizedHistoryErrorDescent.first S n sigma i) q v
    rw [hl]
    exact basis_singleton q

end FixedTotal

private theorem step_zero (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (i : StepIndex N) (w : LocalizedWord S N sigma tau i.succ) (hw : w.word=0) :
    (step S N sigma tau i w).lower.word=0 := by
  by_cases he : (BDL26LocalizedHistoryErrorDescent.Edge N i).val%2=0
  · have hs : second S N sigma tau i w=first S N sigma i := by
      change first S N sigma i+w.word=first S N sigma i
      rw [hw,add_zero]
    rw [step_rx S N sigma tau i he w]
    change BDL26RXPhysicalStarTransport.L S (N+2)
      (BDL26LocalizedHistoryErrorDescent.Edge N i) he w.center
      (first S N sigma i) (second S N sigma tau i w)=0
    rw [hs]
    exact BDL26RXPhysicalStarTransport.lower_self S (N+2)
      (BDL26LocalizedHistoryErrorDescent.Edge N i) he w.center _
  · rw [step_rz S N sigma tau i he w]
    change BDL26RZFiniteBlockTransport.lowerError S (N+2)
      (BDL26LocalizedHistoryErrorDescent.Edge N i) he
      (first S N sigma i) (second S N sigma tau i w)=0
    rw [BDL26RZFiniteBlockTransport.lowerError_coordinates,representatives_difference,hw,map_zero,map_zero]

/-- Nonzero seed branch: the ENTIRE intermediate word lies in the literal face star. -/
theorem seed_intermediate_supported (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (j : Nat) (hN : 2*j+3 ≤ N) (a : SeedData S j)
    (w : LocalizedWord S N sigma tau (rxIndex N j hN).succ)
    (hw : w.word=canonicalBasisWord (F:=F) (seedPhysical S j a)) :
    hammingSupport (step S N sigma tau (rxIndex N j hN) w).lower.word ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (state S (2*j+4)).presentation
        (faceOwner S j a.1 a.2.1) := by
  let i := rxIndex N j hN
  have hm : seedPhysical S j a ∈ hammingSupport w.word := by
    rw [hw]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hself : canonicalBasisWord (F:=F) (seedPhysical S j a) (seedPhysical S j a)=(1 : F) := by
      simp [canonicalBasisWord,Pi.single_apply]
    exact fun hz => one_ne_zero (hself.symm.trans hz)
  have hi := w.supported hm
  change seedPhysical S j a ∈
    BDL26RXPhysicalStarTransport.physicalXStar (state S (2*j+5)).presentation w.center at hi
  rw [seed_physical_ambient S N j hN a] at hi
  have hp := rx_local_edge_parent S (N+2) (BDL26LocalizedHistoryErrorDescent.Edge N i)
    (rx_index_even N j hN) w.center (faceOwner S j a.1 a.2.1) a.2.2 hi
  have hs := (step S N sigma tau i w).lower.supported
  rw [step_rx S N sigma tau i (rx_index_even N j hN) w] at hs
  change hammingSupport (BDL26RXPhysicalStarTransport.L S (N+2)
    (BDL26LocalizedHistoryErrorDescent.Edge N i) (rx_index_even N j hN) w.center _ _) ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (state S (2*j+4)).presentation
        (BDL26RXPhysicalStarTransport.parentX S (N+2)
          (BDL26LocalizedHistoryErrorDescent.Edge N i) (rx_index_even N j hN) w.center) at hs
  rw [hp] at hs
  rw [step_rx S N sigma tau i (rx_index_even N j hN) w]
  exact hs

/-- Equality elimination transports the whole support operation with its original
finite instances; no original history or representative is chosen again. -/
private theorem localized_support_cast (S : OddScale) (N : Nat)
    (sigma tau : TopInput S N) {a b : LevelIndex N} (hab : a=b)
    (u : LocalizedWord S N sigma tau a) :
    HEq (hammingSupport (cast (congrArg (LocalizedWord S N sigma tau) hab) u).word)
      (hammingSupport u.word) := by
  cases hab
  rfl

/-- Both original seed steps at one TOTAL; the first lower word need not be zero. -/
theorem seed_two_step_zero (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (j : Nat) (hN : 2*j+3 ≤ N) (a : SeedData S j)
    (w : LocalizedWord S N sigma tau (rxIndex N j hN).succ)
    (hw : hammingSupport w.word ⊆ {seedPhysical S j a}) :
    (step S N sigma tau (rzIndex N j hN)
      (step S N sigma tau (rxIndex N j hN) w).lower).lower.word=0 := by
  obtain ⟨c,hc⟩ := scalar_singleton w.word _ hw
  rcases bit_cases c with rfl | rfl
  · have hzero : w.word=0 := hc.trans (word_smul_zero _)
    exact step_zero S N sigma tau (rzIndex N j hN) _
      (step_zero S N sigma tau (rxIndex N j hN) w hzero)
  · have hone : w.word=canonicalBasisWord (F:=F) (seedPhysical S j a) :=
      hc.trans (word_smul_one _)
    let v0 := (step S N sigma tau (rxIndex N j hN) w).lower
    let hlevel : (rxIndex N j hN).castSucc=(rzIndex N j hN).succ :=
      (seed_indices N j hN).2.2.symm
    let v : LocalizedWord S N sigma tau (rzIndex N j hN).succ :=
      cast (congrArg (LocalizedWord S N sigma tau) hlevel) v0
    have hv : HEq v v0 := cast_heq _ _
    have hs0 := seed_intermediate_supported S N sigma tau j hN a w hone
    have hsupport : hammingSupport v.word=hammingSupport v0.word :=
      eq_of_heq (localized_support_cast S N sigma tau hlevel v0)
    have hs : hammingSupport v.word ⊆
        BDL26RXPhysicalStarTransport.physicalXStar (state S (2*j+4)).presentation
          (faceOwner S j a.1 a.2.1) := by
      intro r hr
      have hr0 := Eq.mp (congrArg (fun a : Finset (Physical S (2*j+4)) => r ∈ a) hsupport) hr
      exact hs0 hr0
    have he : BDL26RZPhysicalXStarTransport.Localized S (N+2)
        (BDL26LocalizedHistoryErrorDescent.Edge N (rzIndex N j hN))
        (BDL26RZPhysicalXStarTransport.upperXChart S (N+2)
          (BDL26LocalizedHistoryErrorDescent.Edge N (rzIndex N j hN)) (rz_index_odd N j hN)
          (.inl (.inl ⟨a.1,a.2.1⟩)))
        (first S N sigma (rzIndex N j hN))
        (second S N sigma tau (rzIndex N j hN) v) := by
      change hammingSupport (first S N sigma (rzIndex N j hN)+
        second S N sigma tau (rzIndex N j hN) v) ⊆ _
      rw [representatives_difference S N sigma tau (rzIndex N j hN) v]
      change hammingSupport v.word ⊆
        BDL26RXPhysicalStarTransport.physicalXStar (state S (2*j+4)).presentation _
      rw [← face_owner_ambient S N j hN a.1 a.2.1]
      exact hs
    obtain ⟨p,hp,hl,_,_,_⟩ := BDL26RZPhysicalXStarTransport.local_face_transport S (N+2)
      (BDL26LocalizedHistoryErrorDescent.Edge N (rzIndex N j hN)) (rz_index_odd N j hN)
      (by change 3 ≤ 2*j+3; omega) a.1 a.2.1 _ _ he
    have hz : (step S N sigma tau (rzIndex N j hN) v).lower.word=0 := by
      rw [step_rz S N sigma tau (rzIndex N j hN) (rz_index_odd N j hN) v]
      exact hl
    have hv' : v=(show LocalizedWord S N sigma tau (rzIndex N j hN).succ from v0) :=
      eq_of_heq hv
    have hstep := congrArg
      (fun z : LocalizedWord S N sigma tau (rzIndex N j hN).succ =>
        (step S N sigma tau (rzIndex N j hN) z).lower.word) hv'
    exact hstep.symm.trans hz

/-- The original adjacent potential is literally RX.Phi + RX.map0(RZ.Phi). -/
theorem seed_window_potential (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (top : LocalizedWord S N sigma tau (TopIndex N)) (j : Nat) (hN : 2*j+3 ≤ N) :
    intervalPotential S N sigma tau top (rzIndex N j hN).castSucc (rxIndex N j hN).succ=
      edgePotential S N sigma tau top (rxIndex N j hN)+
        ((SuffixData S N).selectedMap (rxIndex N j hN)).map0
          ((seed_indices N j hN).2.2 ▸ edgePotential S N sigma tau top (rzIndex N j hN)) :=
  adjacent_potential_pair S N sigma tau top _ _ (seed_indices N j hN).2.2

/-- Both complete original corrections and BOTH actual chosen potentials in the seed window. -/
theorem seed_window_equation (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (top : LocalizedWord S N sigma tau (TopIndex N)) (j : Nat) (hN : 2*j+3 ≤ N) :
    intervalMap1 (SuffixData S N) (rzIndex N j hN).castSucc (rxIndex N j hN).succ
      (by change 2*j+1 ≤ 2*j+3; omega)
      (path S N sigma tau top (rzIndex N j hN).castSucc).word=
      (path S N sigma tau top (rxIndex N j hN).succ).word+
        correctionIntervalSum S N sigma (rzIndex N j hN).castSucc (rxIndex N j hN).succ+
        correctionIntervalSum S N tau (rzIndex N j hN).castSucc (rxIndex N j hN).succ+
        (SuffixData S N).family.coboundary0 (rxIndex N j hN).succ
          (edgePotential S N sigma tau top (rxIndex N j hN)+
            ((SuffixData S N).selectedMap (rxIndex N j hN)).map0
              ((seed_indices N j hN).2.2 ▸ edgePotential S N sigma tau top (rzIndex N j hN))) :=
  interior_pair_equation S N sigma tau top _ _ (seed_indices N j hN).2.2

private theorem family_down {S : OddScale} {b : Nat} {q : Physical S (b+2)}
    (t : Family S b q) :
    ∀ (N : Nat) (sigma tau : TopInput S N) (hb : b ≤ N)
      (w : LocalizedWord S N sigma tau ⟨b,Nat.lt_succ_of_le hb⟩),
      hammingSupport w.word ⊆ {q} →
      (down S N sigma tau b hb w
        ⟨stopDepth t,by have h:=stopDepth_gap t; omega⟩
        (by change stopDepth t ≤ b; have h:=stopDepth_gap t; omega)).word=0 := by
  induction t with
  | seed j a =>
      intro N sigma tau hb w hw
      have hz := seed_two_step_zero S N sigma tau j hb a w hw
      change (down S N sigma tau (2*j+3) hb w
        ⟨2*j+1,by omega⟩ (by change 2*j+1 ≤ 2*j+3; omega)).word=0
      rw [down_succ S N sigma tau (2*j+2) hb w ⟨2*j+1,by omega⟩
        (by change 2*j+1 ≤ 2*j+2; omega)]
      rw [down_succ S N sigma tau (2*j+1) (by omega) _
        ⟨2*j+1,by omega⟩ (Nat.le_refl _),down_self]
      exact hz
  | @rx b q t he v ih =>
      intro N sigma tau hb w hw
      let i : StepIndex N := ⟨b,by omega⟩
      have hl := (step_rx_singleton S N sigma tau i he w q v hw).2
      change (down S N sigma tau (b+1) hb w ⟨stopDepth t,by have h:=stopDepth_gap t; omega⟩
        (by change stopDepth t ≤ b+1; have h:=stopDepth_gap t; omega)).word=0
      rw [down_succ S N sigma tau b hb w ⟨stopDepth t,by have h:=stopDepth_gap t; omega⟩
        (by change stopDepth t ≤ b; have h:=stopDepth_gap t; omega)]
      exact ih N sigma tau (by omega) _ hl
  | @rz b q t ho v ih =>
      intro N sigma tau hb w hw
      let i : StepIndex N := ⟨b,by omega⟩
      have hl := step_rz_singleton S N sigma tau i ho w q v hw
      change (down S N sigma tau (b+1) hb w ⟨stopDepth t,by have h:=stopDepth_gap t; omega⟩
        (by change stopDepth t ≤ b+1; have h:=stopDepth_gap t; omega)).word=0
      rw [down_succ S N sigma tau b hb w ⟨stopDepth t,by have h:=stopDepth_gap t; omega⟩
        (by change stopDepth t ≤ b; have h:=stopDepth_gap t; omega)]
      exact ih N sigma tau (by omega) _ hl

/-- All-u actual lower snapshot zero, with its stop and support constructed internally. -/
theorem snapshot_zero (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Family S n q) :
    (BDL26BoundaryTailInvariance.snapshot S n u q (stopIndex t)).word=0 := by
  have hi : hammingSupport (BDL26BoundaryTailInvariance.physicalTop S n u q).word ⊆ {q} := by
    change hammingSupport (BDL26ActualFailureReadout.flip S n q) ⊆ {q}
    rw [flip_eq_basis]
    exact basis_singleton q
  exact family_down t n (input S n u)
    (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) (Nat.le_refl _) _ hi

theorem stop_boundary (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Family S n q) :
    (SuffixData S n).family.coboundary0 (stopIndex t) 0=
      (BDL26BoundaryTailInvariance.snapshot S n u q (stopIndex t)).word :=
  (map_zero _).trans (snapshot_zero S n u q t).symm


private theorem state_face_nonempty (S : OddScale) (m : Nat) :
    Nonempty (state S m).presentation.Face := by
  let x := (state S m).selectedX
  obtain ⟨v,hv⟩ := (state S m).admissible.toTannerSquareAdmissible.xBoundaryRoot x
  cases v with
  | x y => simp [xStarBoundaryVertexMember] at hv
  | q q =>
      simp only [xStarBoundaryVertexMember,decide_eq_true_eq] at hv
      obtain ⟨f,_,_⟩ := hv
      exact ⟨f⟩
  | z z =>
      simp only [xStarBoundaryVertexMember,decide_eq_true_eq] at hv
      obtain ⟨f,_,_⟩ := hv
      exact ⟨f⟩

/-- A genuine actual seed for every S/j, built from original admissible incidence. -/
def canonicalSeed (S : OddScale) (j : Nat) : SeedData S j := by
  let P := (state S (2*j+3)).presentation
  let F0 : P.Face := Classical.choice (state_face_nonempty S (2*j+3))
  let z : P.Z := P.faceZ F0
  let sf : XStarFace (transposePresentation P) z := ⟨F0,by
    change decide (P.faceZ F0=z)=true
    exact decide_eq_true rfl⟩
  let k : Fin S.half := ⟨0,S.half_pos⟩
  let f : ZDoubleCylinderFace P z S := .inl (0,(sf,k,k))
  let x := faceOwner S j z f
  let bv := subdivisionOriginalBoundaryVertex (state S (2*j+4)).presentation x S
    ((state S (2*j+4)).admissible.toTannerSquareAdmissible.xBoundaryRoot x)
  exact ⟨z,f,Sum.inr bv⟩

theorem family_seed_nonempty (S : OddScale) (j : Nat) :
    ∃ q : Physical S (2*j+5), Nonempty (Family S (2*j+3) q) :=
  ⟨seedPhysical S j (canonicalSeed S j),⟨Family.seed j (canonicalSeed S j)⟩⟩

/-- Both stored original base calls and both unchanged original D applications. -/
theorem base_calls (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Family S n q) :
    firstReadout S n u=secondReadout S n u q ∧
      (actualBase S n).decode (actualInputs S n (input S n u) 0)=
        (actualBase S n).decode (actualInputs S n
          (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) 0) ∧
      BDL26LevelTwoDecoder.decode S (firstReadout S n u)=
        BDL26LevelTwoDecoder.decode S (secondReadout S n u q) :=
  BDL26BoundaryTailInvariance.physical_base_calls S n u q (stopIndex t) 0
    (stop_boundary S n u q t)

theorem second_zero (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Family S n q) (hs : firstReadout S n u=0) :
    secondReadout S n u q=0 :=
  (base_calls S n u q t).1.symm.trans hs

theorem inputs_eq (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Family S n q) (b : LevelIndex n) (hb : b.val ≤ stopDepth t) :
    actualInputs S n (input S n u) b=
      actualInputs S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) b :=
  BDL26BoundaryTailInvariance.physical_readouts_eq S n u q (stopIndex t) 0
    (stop_boundary S n u q t) b hb

theorem outputs_eq (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Family S n q) (i : StepIndex n) (hi : i.succ.val ≤ stopDepth t) :
    actualOutput S n (input S n u) i=
      actualOutput S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) i :=
  BDL26BoundaryTailInvariance.tail_outputs_eq S n _ _
    (BDL26BoundaryTailInvariance.physicalTop S n u q) (stopIndex t) 0
    (stop_boundary S n u q t) i hi

/-- Preserve the actual chosen bottom filling, including possible kernel terms. -/
def bottomPotential (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Family S n q) : (SuffixData S n).family.Cochain0 0 :=
  BDL26BoundaryTailInvariance.tailPotential S n _ _
    (BDL26BoundaryTailInvariance.physicalTop S n u q) (stopIndex t) 0
    (stop_boundary S n u q t) 0 (Nat.zero_le _)

def fullPotential (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Family S n q) :
    (SuffixData S n).family.Cochain0 (TopIndex n) :=
  BDL26BoundaryTailInvariance.physicalPotential S n u q (stopIndex t) 0
    (stop_boundary S n u q t)

theorem full_potential_formula (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Family S n q) :
    fullPotential S n u q t=
      intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
        (bottomPotential S n u q t)+BDL26ActualFailureReadout.accumulated S n u q := rfl

theorem full_potential_spec (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Family S n q) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (fullPotential S n u q t)=
      BDL26LogicalDefectProtection.deltaX S n u q :=
  BDL26BoundaryTailInvariance.physical_potential_spec S n u q (stopIndex t) 0
    (stop_boundary S n u q t)

theorem chiX_zero (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Family S n q) :
    BDL26LogicalDefectProtection.chiX S n u q=0 :=
  BDL26BoundaryTailInvariance.physical_chiX_zero S n u q (stopIndex t) 0
    (stop_boundary S n u q t)

theorem source_even (S : OddScale) (k : Nat) (hk : 1 ≤ k)
    (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S (2*(k-1)))
    (q : Physical S (2*(k-1)+2)) (t : Family S (2*(k-1)) q) :
    2*(k-1)+2=2*k ∧ BDL26LogicalDefectProtection.chiX S (2*(k-1)) u q=0 :=
  ⟨by omega,chiX_zero S _ u q t⟩

open QEC.Semantics BDL26PairedDecoderPhase

theorem paired_X_zero (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (t : Family S n q) :
    BDL26LogicalDefectProtection.dX S n s (CSSDaviesLocality.singlePauli q .x)=0 :=
  BDL26BoundaryTailInvariance.paired_X_zero S n s q (stopIndex t) 0
    (stop_boundary S n s.1 q t)

theorem paired_Y_zero (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (t : Family S n q) :
    BDL26LogicalDefectProtection.dX S n s (CSSDaviesLocality.singlePauli q .y)=0 :=
  BDL26BoundaryTailInvariance.paired_Y_zero S n s q (stopIndex t) 0
    (stop_boundary S n s.1 q t)

theorem physical_X_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (t : Family S n q) :
    (PauliSymplectic.toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x)*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*PauliSymplectic.toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x))*
      atom S n s=0 :=
  BDL26BoundaryTailInvariance.physical_X_dressed_Z S n s q (stopIndex t) 0
    (stop_boundary S n s.1 q t)

theorem physical_Y_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (t : Family S n q) :
    (PauliSymplectic.toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y)*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*PauliSymplectic.toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y))*
      atom S n s=0 :=
  BDL26BoundaryTailInvariance.physical_Y_dressed_Z S n s q (stopIndex t) 0
    (stop_boundary S n s.1 q t)

theorem actual_X_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (t : Family S n q) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q .x*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .x)*atom S n s=0 :=
  BDL26BoundaryTailInvariance.actual_X_dressed_Z S n s q (stopIndex t) 0
    (stop_boundary S n s.1 q t)

theorem actual_Y_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (t : Family S n q) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q .y*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .y)*atom S n s=0 :=
  BDL26BoundaryTailInvariance.actual_Y_dressed_Z S n s q (stopIndex t) 0
    (stop_boundary S n s.1 q t)

theorem actual_Y_package (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (t : Family S n q) :
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) ∧
      (BDL26CSSDaviesLocality.coupling S (n+2) q .y*BDL26PairedDecoderChannel.dressedZ S n-
        BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .y)*atom S n s=0 :=
  BDL26BoundaryTailInvariance.actual_Y_package S n s q (stopIndex t) 0
    (stop_boundary S n s.1 q t)

end QEC.Coding.BDL26HigherRXFaceTower
