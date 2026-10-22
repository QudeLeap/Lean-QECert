import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.FirstZeroQVertexTower
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.BoundaryTailInvariance

/-!
# FIRST-only RX local-edge towers over literal C2 RZ faces

Project-derived restricted internal/API calculation for BDL26 paper.tex3398–3418,
3423–3484 (SHA256 66d1927b20efccb757da40af3d291e4738c60054799812393e0a739abcc73e5b).
Only actual C3 local-X edges over literal C2 local-Z-face X coordinates seed
this family. Subsequent lifts use every actual Q vertex and both copies.
The original parent, local correction owner, SECOND search and exact v2
correctness are derived internally. FIRST alone is assumed zero. Both base
calls and all original accumulated potentials remain. No general-coordinate,
chiZ/full XYZ, ALL-component, Peierls, Gibbs or lifetime claim is made.
-/
noncomputable section
namespace QEC.Coding.BDL26RXFaceEdgeTower
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators

abbrev Error (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.Error S
abbrev Potential (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.Potential S
abbrev delta (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.delta S
abbrev boundary (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.boundary S
abbrev D (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.D S
abbrev Edge (n : Nat) (i : StepIndex n) := BDL26LocalizedHistoryErrorDescent.Edge n i

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

/-- Literal RZ local-face X constructor at actual C2; not an arbitrary X owner. -/
def faceOwner (S : OddScale) (z : (RawOne S).Z)
    (f : ZDoubleCylinderFace (RawOne S) z S) : (state S 2).presentation.X :=
  .inl (.inl ⟨z,f⟩)

/-- All seed data are physical constructors, with no correctness certificate. -/
abbrev Seed (S : OddScale) := Σ z : (RawOne S).Z,
  Σ f : ZDoubleCylinderFace (RawOne S) z S,
    DoubleCylinderEdge (state S 2).presentation (faceOwner S z f) S

def seedPhysical (S : OddScale) (a : Seed S) : Physical S 3 :=
  BDL26RXDecoderAdapter.rxPhysicalQEquiv S 3 ⟨2,by omega⟩ (by decide)
    (.inl ⟨faceOwner S a.1 a.2.1,a.2.2⟩)

/-- C3 edge seed followed only by actual Q-vertex lifts. -/
inductive Tower (S : OddScale) : (n : Nat) → Physical S (n+2) → Type
  | seed (a : Seed S) : Tower S 1 (seedPhysical S a)
  | rx {n : Nat} {q : Physical S (n+2)} (t : Tower S n q)
      (he : (n+2)%2=0)
      (v : QDoubleCylinderVertex (state S (n+2)).presentation q S) :
      Tower S (n+1) (BDL26FirstZeroQVertexTower.rxVertex S (n+2) he q v)
  | rz {n : Nat} {q : Physical S (n+2)} (t : Tower S n q)
      (ho : ¬(n+2)%2=0)
      (v : QDoubleCylinderVertex (transposePresentation (state S (n+2)).presentation) q S) :
      Tower S (n+1) (BDL26FirstZeroQVertexTower.rzVertex S (n+2) ho q v)

def bottomSeed {S : OddScale} {n : Nat} {q : Physical S (n+2)} : Tower S n q → Seed S
  | .seed a => a
  | .rx t _ _ => bottomSeed t
  | .rz t _ _ => bottomSeed t

theorem positive_depth {S : OddScale} {n : Nat} {q : Physical S (n+2)}
    (t : Tower S n q) : 1≤n := by
  induction t with
  | seed a => omega
  | rx t he v ih => omega
  | rz t ho v ih => omega

theorem no_C2_seed (S : OddScale) (q : Physical S 2) : Tower S 0 q → False := by
  intro t
  have h := positive_depth t
  omega

/-- The seed is genuinely outside the Q-vertex parent fibre. -/
theorem seed_parent_none (S : OddScale) (a : Seed S) :
    parent S 3 (Vertex.q (seedPhysical S a))=none :=
  BDL26RXDecoderAdapter.rxPhysical_localEdge_parent_none S 3 ⟨2,by omega⟩
    (by decide) (faceOwner S a.1 a.2.1) a.2.2

/-- Literal face constructor table, retaining both the empty Q0 and singleton Z0. -/
theorem face_blocks (S : OddScale) (z : (RawOne S).Z)
    (f : ZDoubleCylinderFace (RawOne S) z S) :
    BDL26RZPhysicalXStarTransport.Q0 S 2 ⟨1,by omega⟩ (by decide) (faceOwner S z f)=∅ ∧
    BDL26RZPhysicalXStarTransport.Z0 S 2 ⟨1,by omega⟩ (by decide) (faceOwner S z f)={z} := by
  have h := BDL26RZPhysicalXStarTransport.local_face_data S 2 ⟨1,by omega⟩ (by decide) z f
  exact ⟨h.1,h.2.1⟩

section FixedTotal
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)

private theorem step_rx_singleton (i : StepIndex n) (h : (i.val+2)%2=0)
    (u : BDL26LocalizedHistoryErrorDescent.LocalizedWord S n sigma tau i.succ)
    (q : Physical S (i.val+2))
    (v : QDoubleCylinderVertex (state S (i.val+2)).presentation q S)
    (hu : hammingSupport u.word ⊆ {BDL26FirstZeroQVertexTower.rxVertex S (i.val+2) h q v}) :
    (BDL26LocalizedHistoryErrorDescent.step S n sigma tau i u).potential=0 ∧
    hammingSupport (BDL26LocalizedHistoryErrorDescent.step S n sigma tau i u).lower.word ⊆ {q} := by
  have hh : (Edge n i).val%2=0 := by
    simpa only [Edge,LevelTwoHistory.physicalStep_val] using h
  have he : hammingSupport
      (BDL26LocalizedHistoryErrorDescent.first S n sigma i+
        BDL26LocalizedHistoryErrorDescent.second S n sigma tau i u) ⊆
      (BDL26RXDecoderAdapter.rxLq S (n+2) (Edge n i) hh).correctionRegion q := by
    rw [BDL26LocalizedHistoryErrorDescent.representatives_difference]
    intro r hr
    have heq : r=BDL26FirstZeroQVertexTower.rxVertex S (i.val+2) h q v := Finset.mem_singleton.mp (hu hr)
    subst r
    exact (BDL26RXDecoderAdapter.rxQVertexEquiv S (n+2) (Edge n i) hh q v).property
  have hz := BDL26FirstZeroQVertexTower.rx_computed_parent S (n+2) (Edge n i) hh q _ _ he u.center
  rw [BDL26LocalizedHistoryErrorDescent.step_rx S n sigma tau i hh u]
  constructor
  · exact hz.1
  · change hammingSupport (BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) hh
      u.center _ _) ⊆ {q}
    rw [hz.2]
    exact BDL26RXQBlockTransport.lower_supported S (n+2) (Edge n i) hh q _ _

private theorem step_rz_singleton (i : StepIndex n) (h : ¬(i.val+2)%2=0)
    (u : BDL26LocalizedHistoryErrorDescent.LocalizedWord S n sigma tau i.succ)
    (q : Physical S (i.val+2))
    (v : QDoubleCylinderVertex (transposePresentation (state S (i.val+2)).presentation) q S)
    (hu : hammingSupport u.word ⊆ {BDL26FirstZeroQVertexTower.rzVertex S (i.val+2) h q v}) :
    hammingSupport (BDL26LocalizedHistoryErrorDescent.step S n sigma tau i u).lower.word ⊆ {q} := by
  have hh : ¬(Edge n i).val%2=0 := by
    simpa only [Edge,LevelTwoHistory.physicalStep_val] using h
  obtain ⟨c,hc⟩ := scalar_singleton u.word _ hu
  have hcases : c=0 ∨ c=1 := bit_cases c
  rw [BDL26LocalizedHistoryErrorDescent.step_rz S n sigma tau i hh u]
  change hammingSupport (BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) hh
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
        (BDL26RZPhysicalStarTransport.physicalQ S (n+2) (Edge n i) hh q v) :
        BDL26RZErrorPullback.Upper S (n+2) (Edge n i)) := hw
    change hammingSupport (BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) hh
      (BDL26LocalizedHistoryErrorDescent.first S n sigma i)
      (BDL26LocalizedHistoryErrorDescent.first S n sigma i+u.word)) ⊆ {q}
    rw [hw']
    have hl := BDL26RZPhysicalStarTransport.lower_physicalQ_basis S (n+2) (Edge n i) hh
      (BDL26LocalizedHistoryErrorDescent.first S n sigma i) q v
    rw [hl]
    exact basis_singleton q

/- Transport the complete seed word along the actual suffix/physical index
equality. Support is transported as an operation, including its finite carrier
instance; it is not assumed to be definitionally the same filtered finset. -/
private abbrev seedCarrier (S : OddScale) (n : Nat) (hn : 1≤n) :=
  LevelTwoHistory.Suffix (BDL26IndexedDecoder.FamilyQ S (n+2))
    (⟨1,by omega⟩ : LevelIndex n)

private theorem seedCarrier_eq (S : OddScale) (n : Nat) (hn : 1≤n) :
    seedCarrier S n hn=Physical S 3 := by
  have hlevel : (LevelTwoHistory.physicalLevel
      (⟨1,by omega⟩ : LevelIndex n)).val=3 := by
    simp only [LevelTwoHistory.physicalLevel_val,Fin.val_mk]
  simpa only [seedCarrier,LevelTwoHistory.Suffix,BDL26IndexedDecoder.FamilyQ,
    BDL26CSSHamiltonian.Physical,BDL26CSSHamiltonian.presentation] using
      congrArg (fun k => (state S k).presentation.Q) hlevel

private theorem cast_word_zero {I J : Type} (h : I=J) (u : Word F I) :
    cast (congrArg (Word F) h) u=0 ↔ u=0 := by
  cases h
  rfl

private def seedWord (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (hn : 1≤n)
    (w : BDL26LocalizedHistoryErrorDescent.LocalizedWord S n sigma tau ⟨1,by omega⟩) :
    Word F (Physical S 3) :=
  cast (congrArg (Word F) (seedCarrier_eq S n hn)) w.word

private theorem seedWord_heq (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (hn : 1≤n)
    (w : BDL26LocalizedHistoryErrorDescent.LocalizedWord S n sigma tau ⟨1,by omega⟩) :
    HEq (seedWord S n sigma tau hn w) w.word := cast_heq _ _

/- The actual fixed-depth seed chart and its ambient-history chart differ only
in proof indices. Unfold both actual equivalences before comparing their casts. -/
private theorem seed_physical_ambient (S : OddScale) (n : Nat) (hn : 1≤n)
    (a : Seed S) :
    seedPhysical S a=BDL26RXDecoderAdapter.rxPhysicalQEquiv S (n+2)
      (Edge n ⟨0,by omega⟩) (by change 2%2=0; decide)
      (.inl ⟨faceOwner S a.1 a.2.1,a.2.2⟩) := by
  unfold seedPhysical BDL26RXDecoderAdapter.rxPhysicalQEquiv
  simp only [Edge,LevelTwoHistory.physicalStep,Fin.val_mk]

/-- Nonzero seed support determines the original computed parent from incidence. -/
theorem seed_computed_parent (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (hn : 1≤n) (a : Seed S)
    (w : BDL26LocalizedHistoryErrorDescent.LocalizedWord S n sigma tau ⟨1,by omega⟩)
    (hw : w.word=canonicalBasisWord (seedPhysical S a)) :
    BDL26RXPhysicalStarTransport.parentX S (n+2) (Edge n ⟨0,by omega⟩) (by change 2%2=0; decide)
      w.center=faceOwner S a.1 a.2.1 := by
  let i : StepIndex n := ⟨0,by omega⟩
  have heven : (Edge n i).val%2=0 := by change 2%2=0; decide
  let originalWord := w.word
  dsimp only [BDL26CochainFamily.Cochain1,LevelTwoHistory.Suffix,
    BDL26IndexedDecoder.FamilyQ,LevelTwoHistory.physicalLevel] at originalWord
  let originalSupport := hammingSupport w.word
  dsimp only [BDL26CochainFamily.Cochain1,LevelTwoHistory.Suffix,
    BDL26IndexedDecoder.FamilyQ,LevelTwoHistory.physicalLevel] at originalSupport
  have hraw := seedWord_heq S n sigma tau hn w
  dsimp only [BDL26CochainFamily.Cochain1,LevelTwoHistory.Suffix,
    BDL26IndexedDecoder.FamilyQ,LevelTwoHistory.physicalLevel] at hraw
  have hword : HEq (seedWord S n sigma tau hn w) originalWord :=
    hraw
  have hw0 : originalWord=canonicalBasisWord (seedPhysical S a) := by
    simpa only [BDL26CochainFamily.Cochain1,LevelTwoHistory.Suffix,
      BDL26IndexedDecoder.FamilyQ,LevelTwoHistory.physicalLevel] using hw
  have hw3 : seedWord S n sigma tau hn w=canonicalBasisWord (seedPhysical S a) := by
    exact (eq_of_heq hword).trans hw0
  have hq3 : seedPhysical S a∈hammingSupport (seedWord S n sigma tau hn w) := by
    rw [hw3]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hself : canonicalBasisWord (F:=F) (seedPhysical S a) (seedPhysical S a)=(1 : F) := by
      simp [canonicalBasisWord,Pi.single_apply]
    exact fun hz => one_ne_zero (hself.symm.trans hz)
  have hsupport : hammingSupport (seedWord S n sigma tau hn w)=originalSupport := by
    ext r
    have hvalue := congrFun (eq_of_heq hword) r
    have hnonzero : (seedWord S n sigma tau hn w) r≠0 ↔ originalWord r≠0 := by
      constructor
      · exact Eq.mp (congrArg (fun x : F => x≠0) hvalue)
      · exact Eq.mpr (congrArg (fun x : F => x≠0) hvalue)
    simpa only [originalSupport,originalWord,hammingSupport,Finset.mem_filter,
      Finset.mem_univ,true_and] using hnonzero
  have hq := Eq.mp (congrArg (fun b => seedPhysical S a ∈ b) hsupport) hq3
  have hi := (BDL26RXPhysicalStarTransport.mem_physicalXStar _ _ _).mp (w.supported (by
    simpa only [BDL26CochainFamily.Cochain1,LevelTwoHistory.Suffix,
      BDL26IndexedDecoder.FamilyQ,LevelTwoHistory.physicalLevel] using hq))
  obtain ⟨r,hr⟩ := (BDL26RXDecoderAdapter.rxDegreeZeroEquiv S (n+2) (Edge n i) heven).surjective w.center
  have hic : rxXQIncidence (state S 2).presentation S r
      (.inl ⟨faceOwner S a.1 a.2.1,a.2.2⟩)=true := by
    rw [← BDL26RXDecoderAdapter.rxPhysical_incidence S (n+2) (Edge n i) heven r]
    rw [seed_physical_ambient S n hn a] at hi
    simpa only [hr,i,Edge,LevelTwoHistory.physicalStep_val,Fin.val_mk] using hi
  have ho := BDL26RXPhysicalStarTransport.raw_local_edge_owner
    (state S 2).presentation S r ⟨faceOwner S a.1 a.2.1,a.2.2⟩ hic
  change ((BDL26RXDecoderAdapter.rxDegreeZeroEquiv S (n+2) (Edge n i) heven).symm w.center).1=_
  rw [←hr,Equiv.symm_apply_apply]
  exact ho

/-- Zero input uses the actual self branch; no centre is inferred from empty support. -/
theorem seed_step_supported (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (hn : 1≤n) (a : Seed S)
    (w : BDL26LocalizedHistoryErrorDescent.LocalizedWord S n sigma tau ⟨1,by omega⟩)
    (hw : hammingSupport w.word ⊆ {seedPhysical S a}) :
    hammingSupport (BDL26LocalizedHistoryErrorDescent.step S n sigma tau ⟨0,by omega⟩ w).lower.word ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation (faceOwner S a.1 a.2.1) := by
  let i : StepIndex n := ⟨0,by omega⟩
  have heven : (Edge n i).val%2=0 := by change 2%2=0; decide
  let originalWord := w.word
  dsimp only [BDL26CochainFamily.Cochain1,LevelTwoHistory.Suffix,
    BDL26IndexedDecoder.FamilyQ,LevelTwoHistory.physicalLevel] at originalWord
  let originalSupport := hammingSupport w.word
  dsimp only [BDL26CochainFamily.Cochain1,LevelTwoHistory.Suffix,
    BDL26IndexedDecoder.FamilyQ,LevelTwoHistory.physicalLevel] at originalSupport
  have hraw := seedWord_heq S n sigma tau hn w
  dsimp only [BDL26CochainFamily.Cochain1,LevelTwoHistory.Suffix,
    BDL26IndexedDecoder.FamilyQ,LevelTwoHistory.physicalLevel] at hraw
  have hword : HEq (seedWord S n sigma tau hn w) originalWord := hraw
  have hw0 : originalSupport ⊆ {seedPhysical S a} := by
    simpa only [BDL26CochainFamily.Cochain1,LevelTwoHistory.Suffix,
      BDL26IndexedDecoder.FamilyQ,LevelTwoHistory.physicalLevel] using hw
  have hw3 : hammingSupport (seedWord S n sigma tau hn w) ⊆ {seedPhysical S a} := by
    have hsupport : hammingSupport (seedWord S n sigma tau hn w)=originalSupport := by
      ext r
      have hvalue := congrFun (eq_of_heq hword) r
      have hnonzero : (seedWord S n sigma tau hn w) r≠0 ↔ originalWord r≠0 := by
        constructor
        · exact Eq.mp (congrArg (fun x : F => x≠0) hvalue)
        · exact Eq.mpr (congrArg (fun x : F => x≠0) hvalue)
      simpa only [originalSupport,originalWord,hammingSupport,Finset.mem_filter,
        Finset.mem_univ,true_and] using hnonzero
    intro r hr
    have hr0 := Eq.mp (congrArg (fun b => r ∈ b) hsupport) hr
    exact Finset.mem_singleton.mpr (Finset.mem_singleton.mp (hw0 hr0))
  obtain ⟨c,hc⟩ := scalar_singleton (seedWord S n sigma tau hn w) (seedPhysical S a) hw3
  rcases bit_cases c with rfl | rfl
  · have hz3 : seedWord S n sigma tau hn w=0 := hc.trans (word_smul_zero _)
    have hz : w.word=0 := (cast_word_zero (seedCarrier_eq S n hn) w.word).mp hz3
    have hs : BDL26LocalizedHistoryErrorDescent.second S n sigma tau i w=
        BDL26LocalizedHistoryErrorDescent.first S n sigma i := by
      dsimp only [BDL26LocalizedHistoryErrorDescent.second]
      rw [hz,add_zero]
    rw [BDL26LocalizedHistoryErrorDescent.step_rx S n sigma tau i heven w]
    change hammingSupport (BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) heven
      w.center (BDL26LocalizedHistoryErrorDescent.first S n sigma i)
        (BDL26LocalizedHistoryErrorDescent.second S n sigma tau i w)) ⊆ _
    rw [hs,BDL26RXPhysicalStarTransport.lower_self]
    simp [hammingSupport]
  · have hb3 : seedWord S n sigma tau hn w=canonicalBasisWord (seedPhysical S a) :=
      hc.trans (word_smul_one _)
    have hb0 : originalWord=canonicalBasisWord (seedPhysical S a) :=
      (eq_of_heq hword).symm.trans hb3
    have hp := seed_computed_parent S n sigma tau hn a w
      (by simpa only [BDL26CochainFamily.Cochain1,LevelTwoHistory.Suffix,
        BDL26IndexedDecoder.FamilyQ,LevelTwoHistory.physicalLevel] using hb0)
    have hs := (BDL26LocalizedHistoryErrorDescent.step S n sigma tau i w).lower.supported
    rw [BDL26LocalizedHistoryErrorDescent.step_rx S n sigma tau i heven w] at hs
    change hammingSupport (BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) heven
      w.center _ _) ⊆ BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation
        (BDL26RXPhysicalStarTransport.parentX S (n+2) (Edge n i) heven w.center) at hs
    rw [hp] at hs
    rw [BDL26LocalizedHistoryErrorDescent.step_rx S n sigma tau i heven w]
    exact hs

private theorem tower_down {b : Nat} {q : Physical S (b+2)} (t : Tower S b q) :
    ∀ (total : Nat) (sigma tau : TopInput S total) (hb : b≤total)
      (w : BDL26LocalizedHistoryErrorDescent.LocalizedWord S total sigma tau ⟨b,Nat.lt_succ_of_le hb⟩),
      hammingSupport w.word ⊆ {q} →
      hammingSupport (BDL26LocalizedHistoryErrorDescent.down S total sigma tau b hb w 0 (Nat.zero_le b)).word ⊆
        BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation
          (faceOwner S (bottomSeed t).1 (bottomSeed t).2.1) := by
  induction t with
  | seed a =>
      intro total sigma tau hb w hw
      change hammingSupport
        (BDL26LocalizedHistoryErrorDescent.down S total sigma tau 1 hb w
          ⟨0,by omega⟩ (by change 0 ≤ 1; omega)).word ⊆
        BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation (faceOwner S a.1 a.2.1)
      rw [BDL26LocalizedHistoryErrorDescent.down_succ S total sigma tau 0 hb w
        ⟨0,by omega⟩ (Nat.le_refl 0),BDL26LocalizedHistoryErrorDescent.down_self]
      exact seed_step_supported S total sigma tau hb a w hw
  | @rx b q t he v ih =>
      intro total sigma tau hb w hw
      let i : StepIndex total := ⟨b,by omega⟩
      have hl := (step_rx_singleton S total sigma tau i he w q v hw).2
      rw [BDL26LocalizedHistoryErrorDescent.down_succ S total sigma tau b hb w 0 (Nat.zero_le b)]
      exact ih total sigma tau (by omega) _ hl
  | @rz b q t ho v ih =>
      intro total sigma tau hb w hw
      let i : StepIndex total := ⟨b,by omega⟩
      have hl := step_rz_singleton S total sigma tau i ho w q v hw
      rw [BDL26LocalizedHistoryErrorDescent.down_succ S total sigma tau b hb w 0 (Nat.zero_le b)]
      exact ih total sigma tau (by omega) _ hl
end FixedTotal

private theorem actual_star_heq {U V : TannerSquarePresentation} (h : U=V) :
    HEq (BDL26RXPhysicalStarTransport.physicalXStar U)
      (BDL26RXPhysicalStarTransport.physicalXStar V) ∧
    HEq (fun w : Word F U.Q => hammingSupport w)
      (fun w : Word F V.Q => hammingSupport w) := by
  cases h
  exact ⟨HEq.rfl,HEq.rfl⟩

/-- Actual terminal support, derived from seed incidence and fixed-total descent. -/
theorem terminal_supported (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) :
    BDL26FirstZeroFaceEndpoint.faceSupported S (bottomSeed t).1 (bottomSeed t).2.1 (descent S n u q).word := by
  have hi : hammingSupport (BDL26BoundaryTailInvariance.physicalTop S n u q).word ⊆ {q} := by
    change hammingSupport (flip S n q) ⊆ {q}
    rw [flip_eq_basis]
    exact basis_singleton q
  have hs := tower_down S t n (input S n u) (perturbTop S n (input S n u) (flip S n q))
    (Nat.le_refl _) _ hi
  have hop : (BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation :
      (RawTwo S).X → Finset (RawTwo S).Q)=BDL26RXPhysicalStarTransport.physicalXStar (RawTwo S) :=
    eq_of_heq (actual_star_heq (congrArg ConstructionState.presentation (levelTwoState_eq_pair S))).1
  have hsupport : ((fun w : Word F (state S 2).presentation.Q => hammingSupport w) :
      Error S → Finset (RawTwo S).Q)=(fun w : Error S => hammingSupport w) :=
    eq_of_heq (actual_star_heq (congrArg ConstructionState.presentation (levelTwoState_eq_pair S))).2
  change (fun w : Word F (state S 2).presentation.Q => hammingSupport w)
    (descent S n u q).word ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation
        (faceOwner S (bottomSeed t).1 (bottomSeed t).2.1) at hs
  let h : Error S := (descent S n u q).word
  have hhs := congrArg (fun support : Error S → Finset (RawTwo S).Q => support h) hsupport
  have hxs := congrArg (fun star : (RawTwo S).X → Finset (RawTwo S).Q =>
    star (faceOwner S (bottomSeed t).1 (bottomSeed t).2.1)) hop
  change hammingSupport h ⊆
    BDL26RXPhysicalStarTransport.physicalXStar (RawTwo S) (faceOwner S (bottomSeed t).1 (bottomSeed t).2.1)
  intro r hr
  have hri := Eq.mpr (congrArg (fun a : Finset (RawTwo S).Q => r ∈ a) hhs) hr
  exact Eq.mp (congrArg (fun a : Finset (RawTwo S).Q => r ∈ a) hxs) (hs hri)

/-- Every nonzero terminal coordinate has the actual preceding Z owner. -/
theorem terminal_owner (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (r : RZQ (RawOne S) S)
    (hr : (descent S n u q).word r≠0) :
    BDL26ReplacementSupport.rzCorrectionOwner (RawOne S) S r=Vertex.z (bottomSeed t).1 :=
  BDL26FirstZeroFaceEndpoint.face_owner S _ _ _ (terminal_supported S n u q t) r hr

def terminalWord (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) : Error S := (descent S n u q).word

theorem terminal_local (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) : levelTwoLocalError S (terminalWord S n u q) :=
  BDL26FirstZeroFaceEndpoint.face_local S _ _ _ (terminal_supported S n u q t)

/-- Exact merged v2 local decoder correctness, rather than a supplied certificate. -/
theorem terminal_decode_corrects (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) :
    terminalWord S n u q+D S (delta S (terminalWord S n u q)) ∈
      (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier :=
  BDL26LevelTwoDecoder.decode_corrects_local S _ (terminal_local S n u q t)

/-- The unchanged original first table search succeeds on the actual SECOND input. -/
theorem second_search (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n u=0) :
    BDL26LevelTwoLocalBranchEndpoint.localSuccess S (secondReadout S n u q) := by
  rw [← BDL26FirstZeroFaceEndpoint.terminal_syndrome S n u q hs]
  exact (BDL26LevelTwoLocalBranchEndpoint.localSuccess_iff S _).mpr
    ⟨terminalWord S n u q,terminal_local S n u q t,rfl⟩

/-- Keep the actual independently returned word and its derived properties. -/
theorem second_returned (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n u=0) :
    ∃ w : Word F (BDL26LevelTwoDecoder.ExecutableQ S),
      BDL26LevelTwoLocalBranchEndpoint.localSearch S (secondReadout S n u q)=some w ∧
      D S (secondReadout S n u q)=BDL26LevelTwoDecoder.toActualError S w ∧
      levelTwoLocalError S (D S (secondReadout S n u q)) ∧
      delta S (D S (secondReadout S n u q))=secondReadout S n u q := by
  obtain ⟨w,hw⟩ := second_search S n u q t hs
  exact ⟨w,hw,BDL26LevelTwoLocalBranchEndpoint.returned_word S _ w hw,
    BDL26LevelTwoLocalBranchEndpoint.returned_local_and_syndrome S _ w hw⟩

private theorem coboundary0_heq {U V : TannerSquarePresentation} (e : U=V) :
    HEq (tannerCoboundary0 U) (tannerCoboundary0 V) := by
  cases e
  rfl

private theorem actual_delta0 (S : OddScale) :
    (tannerCoboundary0 (state S 2).presentation : Potential S →ₗ[F] Error S)=boundary S :=
  eq_of_heq (coboundary0_heq
    (congrArg ConstructionState.presentation (levelTwoState_eq_pair S)))

private theorem terminal_endpoint (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) :
    ∃ p : Potential S, boundary S p=
      terminalWord S n u q+D S 0+D S (delta S (terminalWord S n u q)) := by
  obtain ⟨p,hp⟩ := ((levelTwoChainComplex S).mem_firstCoboundaryCheckCode_iff _).mp
    (terminal_decode_corrects S n u q t)
  rw [levelTwo_coboundary0_eq] at hp
  let pRaw : Potential S := p
  have hboundary : boundary S pRaw=
      terminalWord S n u q+D S (delta S (terminalWord S n u q)) :=
    (LinearMap.congr_fun (actual_delta0 S) pRaw).symm.trans hp
  have hz : D S 0=(0 : Error S) := BDL26LevelTwoLocalBranchEndpoint.decode_zero S
  have hzero : terminalWord S n u q+D S 0=terminalWord S n u q :=
    (congrArg (fun d : Error S => terminalWord S n u q+d) hz).trans (add_zero _)
  have hrestore := congrArg
    (fun h : Error S => h+D S (delta S (terminalWord S n u q))) hzero
  exact ⟨pRaw,hboundary.trans hrestore.symm⟩

/-- Chosen only from the proved endpoint of the actual terminal word. -/
def basePotential (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) : (SuffixData S n).family.Cochain0 0 :=
  Classical.choose (terminal_endpoint S n u q t)

/-- Both stored original base calls, on their literal original input histories. -/
theorem base_history_spec (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n u=0) :
    (SuffixData S n).family.coboundary0 0 (basePotential S n u q t)=
      (descent S n u q).word+
        (actualBase S n).decode (actualInputs S n (input S n u) 0)+
        (actualBase S n).decode
          (actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0) := by
  have hp : boundary S (basePotential S n u q t)=
      terminalWord S n u q+D S 0+D S (delta S (terminalWord S n u q)) :=
    Classical.choose_spec (terminal_endpoint S n u q t)
  have hd : delta S (terminalWord S n u q)=secondReadout S n u q :=
    BDL26FirstZeroFaceEndpoint.terminal_syndrome S n u q hs
  have hdecode := congrArg (D S) hd
  have hnormalized := congrArg
    (fun d : Error S => terminalWord S n u q+D S 0+d) hdecode
  have hp' := hp.trans hnormalized
  have hfirst : (actualBase S n).decode (actualInputs S n (input S n u) 0)=D S 0 :=
    (first_base_original_D S n u).trans (congrArg (D S) hs)
  have hsecond : (actualBase S n).decode
      (actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0)=
        D S (secondReadout S n u q) := second_base_original_D S n u q
  let h : Error S := terminalWord S n u q
  have hcalls := congrArg₂ (fun a b : Error S => h+a+b) hfirst.symm hsecond.symm
  have hbase : (SuffixData S n).family.coboundary0 0 (basePotential S n u q t)=
      boundary S (basePotential S n u q t) := by
    rw [suffix_delta0]
    exact LinearMap.congr_fun (actual_delta0 S) (basePotential S n u q t)
  exact hbase.trans (hp'.trans hcalls)

/-- All original accumulated potentials remain, including nonzero RZ choices. -/
def fullPotential (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) : (SuffixData S n).family.Cochain0 (TopIndex n) :=
  intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _) (basePotential S n u q t)+
    accumulated S n u q

theorem full_potential_formula (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) :
    fullPotential S n u q t=
      intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _) (basePotential S n u q t)+
        accumulated S n u q := rfl

theorem full_potential_spec (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n u=0) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (fullPotential S n u q t)=
      BDL26LogicalDefectProtection.deltaX S n u q := by
  unfold fullPotential
  rw [map_add,intervalMap_commutes0 _ n (Nat.le_refl _) 0 (Nat.zero_le _),
    base_history_spec S n u q t hs]
  exact (full_history S n u q).symm

theorem original_correction_equation (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n u=0) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (fullPotential S n u q t)=
      flip S n q+xCorrection S n u+xCorrection S n (translateX S n u (flip S n q)) := by
  rw [full_potential_spec S n u q t hs]
  unfold BDL26LogicalDefectProtection.deltaX BDL26ActualFailureReadout.flip
  ac_rfl

theorem first_zero_chiX (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n u=0) :
    BDL26LogicalDefectProtection.chiX S n u q=0 := by
  rw [chiX_top_coefficient]
  apply (top_zero_iff_boundary S n (input S n u) (flip S n q)).mpr
  refine ⟨fullPotential S n u q t,?_⟩
  rw [full_residual]
  exact full_potential_spec S n u q t hs

/-- Source-even depths retain the generated C3 seed, so k starts at two. -/
theorem source_even (S : OddScale) (k : Nat) (hk : 2≤k)
    (u : XSyndromeDomain S (2*(k-1))) (q : Physical S (2*(k-1)+2))
    (t : Tower S (2*(k-1)) q) (hs : firstReadout S (2*(k-1)) u=0) :
    2*(k-1)+2=2*k ∧ BDL26LogicalDefectProtection.chiX S (2*(k-1)) u q=0 :=
  ⟨by omega,first_zero_chiX S _ u q t hs⟩

open QEC.Semantics BDL26PairedDecoderPhase

theorem physical_Y_iXZ (S : OddScale) (n : Nat) (q : Physical S (n+2)) :
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) :=
  BDL26ActualFailureReadout.physical_Y_iXZ S n q

theorem physical_X_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n s.1=0) :
    (toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x)*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x))*
      atom S n s=0 := by
  apply (BDL26LogicalDefectProtection.protected_Z_iff S n s _).mpr
  rw [paired_X_bit]
  exact first_zero_chiX S n s.1 q t hs

theorem physical_Y_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n s.1=0) :
    (toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y)*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y))*
      atom S n s=0 := by
  apply (BDL26LogicalDefectProtection.protected_Z_iff S n s _).mpr
  rw [paired_Y_bit]
  exact first_zero_chiX S n s.1 q t hs

theorem actual_X_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n s.1=0) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q .x*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .x)*atom S n s=0 :=
  physical_X_dressed_Z S n s q t hs

theorem actual_Y_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n s.1=0) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q .y*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .y)*atom S n s=0 :=
  physical_Y_dressed_Z S n s q t hs

theorem actual_Y_package (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n s.1=0) :
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) ∧
    (BDL26CSSDaviesLocality.coupling S (n+2) q .y*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .y)*atom S n s=0 :=
  ⟨physical_Y_iXZ S n q,actual_Y_dressed_Z S n s q t hs⟩

end QEC.Coding.BDL26RXFaceEdgeTower
