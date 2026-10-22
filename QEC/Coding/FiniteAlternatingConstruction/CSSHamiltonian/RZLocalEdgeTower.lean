import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.FirstZeroQVertexTower
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.BoundaryTailInvariance

/-!
# Actual RZ local-edge seeds and Q-vertex lifts

Project-derived internal/API restriction of BDL26 paper.tex3383–3484.
An odd physical RZ local-Z-edge seed is killed by the original parity map.
Arbitrary actual Q-vertex lifts preserve singleton confinement above that
seed at the SAME total depth and in the SAME two histories. The original
full seed potential is retained. BoundaryTailInvariance then gives all-u
chiX and actual X/SAME-Y dressed-Z consumers, including nonzero common
base outputs. This is not general-coordinate stability, chiZ/full XYZ,
ALL-component locality, Peierls, Gibbs or lifetime.
-/
noncomputable section
namespace QEC.Coding.BDL26RZLocalEdgeTower
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26TransposedStoppedDecoder
open PauliSymplectic
open scoped Classical BigOperators

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

/-- Literal original local-Z-edge summand of the actual odd successor. -/
def rzLocalEdge (S : OddScale) (m : Nat) (ho : ¬m%2=0)
    (z : (state S m).presentation.Z)
    (e : ZDoubleCylinderEdge (state S m).presentation z S) : Physical S (m+1) :=
  BDL26RZPhysicalStarTransport.upperQChart S (m+1) ⟨m,Nat.lt_succ_self m⟩ ho (.inl ⟨z,e⟩)

/-- Only actual coordinate constructors: one odd RZ seed and arbitrary Q vertices. -/
inductive Killed (S : OddScale) : (n : Nat) → Physical S (n+2) → Type
  | seed (j : Nat) (ho : ¬(j+2)%2=0) (z : (state S (j+2)).presentation.Z)
      (e : ZDoubleCylinderEdge (state S (j+2)).presentation z S) :
      Killed S (j+1) (rzLocalEdge S (j+2) ho z e)
  | rx {n : Nat} {q : Physical S (n+2)} (t : Killed S n q)
      (he : (n+2)%2=0)
      (v : QDoubleCylinderVertex (state S (n+2)).presentation q S) :
      Killed S (n+1) (BDL26FirstZeroQVertexTower.rxVertex S (n+2) he q v)
  | rz {n : Nat} {q : Physical S (n+2)} (t : Killed S n q)
      (ho : ¬(n+2)%2=0)
      (v : QDoubleCylinderVertex (transposePresentation (state S (n+2)).presentation) q S) :
      Killed S (n+1) (BDL26FirstZeroQVertexTower.rzVertex S (n+2) ho q v)

/-- Computed seed location, not a supplied stopping/zero certificate. -/
def seedDepth {S : OddScale} {n : Nat} {q : Physical S (n+2)} : Killed S n q → Nat
  | .seed j _ _ _ => j
  | .rx t _ _ => seedDepth t
  | .rz t _ _ => seedDepth t

theorem seedDepth_pos {S : OddScale} {n : Nat} {q : Physical S (n+2)}
    (t : Killed S n q) : 1 ≤ seedDepth t := by
  induction t with
  | seed j ho z e => dsimp only [seedDepth]; omega
  | rx t he v ih => exact ih
  | rz t ho v ih => exact ih

theorem seedDepth_lt {S : OddScale} {n : Nat} {q : Physical S (n+2)}
    (t : Killed S n q) : seedDepth t+1 ≤ n := by
  induction t with
  | seed j ho z e => exact Nat.le_refl _
  | rx t he v ih => dsimp only [seedDepth]; omega
  | rz t ho v ih => dsimp only [seedDepth]; omega

theorem no_small_seed (S : OddScale) (n : Nat) (hn : n ≤ 1) (q : Physical S (n+2)) :
    Killed S n q → False := by
  intro t
  have hp := seedDepth_pos t
  have hl := seedDepth_lt t
  omega

def seedIndex {S : OddScale} {n : Nat} {q : Physical S (n+2)} (t : Killed S n q) :
    LevelIndex n := ⟨seedDepth t,by have h:=seedDepth_lt t; omega⟩

private theorem basis_read {I J : Type} (e : I ≃ J)
    (R : Word F I ≃ₗ[F] Word F J)
    (hr : ∀ w x, R w x=w (e.symm x)) (q : J) :
    R.symm (canonicalBasisWord (F:=F) q)=canonicalBasisWord (F:=F) (e.symm q) := by
  apply R.injective
  rw [LinearEquiv.apply_symm_apply]
  funext r
  rw [hr]
  by_cases h : r=q
  · subst r; simp [canonicalBasisWord]
  · have hn : e.symm r≠e.symm q := fun he => h (e.symm.injective he)
    simp [canonicalBasisWord,h,hn]

private theorem cancel_pair {I : Type} (a b : Word F I) : a+(a+b)=b := by
  rw [← add_assoc,word_add_self,zero_add]

/-- Actual physical basis transport followed by the literal original parity projection. -/
theorem lower_local_edge_basis (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (ho : ¬i.val%2=0) (a : BDL26RZErrorPullback.Upper S depth i)
    (z : (state S i.val).presentation.Z)
    (e : ZDoubleCylinderEdge (state S i.val).presentation z S) :
    BDL26RZFiniteBlockTransport.lowerError S depth i ho a
      (a+canonicalBasisWord (F:=F)
        (BDL26RZPhysicalStarTransport.upperQChart S depth i ho (.inl ⟨z,e⟩)))=0 := by
  let R := BDL26RZFiniteBlockTransport.read1 S depth i ho
  let r : RZQ (BDL26RZFiniteBlockTransport.Old S depth i) S := Sum.inl ⟨z,e⟩
  have hb : R.symm (canonicalBasisWord (F:=F) r)=
      canonicalBasisWord (F:=F) (BDL26RZPhysicalStarTransport.upperQChart S depth i ho r) := by
    exact basis_read (BDL26RZFiniteBlockTransport.coord1 S depth i ho)
      R (BDL26RZFiniteBlockTransport.read1_apply S depth i ho) r
  have hread : R (canonicalBasisWord (F:=F)
      (BDL26RZPhysicalStarTransport.upperQChart S depth i ho r))=canonicalBasisWord (F:=F) r :=
    (congrArg (fun w : BDL26RZErrorPullback.Upper S depth i => R w) hb.symm).trans
      (R.apply_symm_apply _)
  have hc : a+(a+canonicalBasisWord (F:=F)
      (BDL26RZPhysicalStarTransport.upperQChart S depth i ho r))=
      canonicalBasisWord (F:=F) (BDL26RZPhysicalStarTransport.upperQChart S depth i ho r) :=
    cancel_pair _ _
  have hp := congrArg (fun w : BDL26RZErrorPullback.Upper S depth i =>
    rzQParity (BDL26RZFiniteBlockTransport.Old S depth i) S (R w)) hc
  have hq := congrArg (rzQParity (BDL26RZFiniteBlockTransport.Old S depth i) S) hread
  exact (BDL26RZFiniteBlockTransport.lowerError_coordinates S depth i ho _ _).trans
    (hp.trans (hq.trans (rzQParity_localBasis
      (BDL26RZFiniteBlockTransport.Old S depth i) S z e)))

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

/-- Internally derived scalar0/1, in the actual unchanged RZ step. -/
theorem seed_step_zero (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (i : StepIndex n) (ho : ¬(i.val+2)%2=0)
    (w : LocalizedWord S n sigma tau i.succ)
    (z : (state S (i.val+2)).presentation.Z)
    (e : ZDoubleCylinderEdge (state S (i.val+2)).presentation z S)
    (hw : hammingSupport w.word ⊆ {rzLocalEdge S (i.val+2) ho z e}) :
    (step S n sigma tau i w).lower.word=0 := by
  have hh : ¬(BDL26LocalizedHistoryErrorDescent.Edge n i).val%2=0 := by
    simpa only [BDL26LocalizedHistoryErrorDescent.Edge,LevelTwoHistory.physicalStep_val] using ho
  obtain ⟨c,hc⟩ := scalar_singleton w.word _ hw
  rcases bit_cases c with rfl | rfl
  · have hz : w.word=0 := hc.trans (word_smul_zero _)
    rw [step_rz S n sigma tau i hh w]
    change BDL26RZFiniteBlockTransport.lowerError S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i) hh
      (first S n sigma i) (second S n sigma tau i w)=0
    rw [BDL26RZFiniteBlockTransport.lowerError_coordinates,representatives_difference,hz,map_zero,map_zero]
  · have hz : w.word=canonicalBasisWord (rzLocalEdge S (i.val+2) ho z e) :=
      hc.trans (word_smul_one _)
    have hz' : w.word=(canonicalBasisWord (F:=F)
        (BDL26RZPhysicalStarTransport.upperQChart S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i) hh (.inl ⟨z,e⟩)) :
        BDL26RZErrorPullback.Upper S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i)) := hz
    rw [step_rz S n sigma tau i hh w]
    change BDL26RZFiniteBlockTransport.lowerError S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i) hh
      (first S n sigma i) (first S n sigma i+w.word)=0
    rw [hz']
    exact lower_local_edge_basis S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i) hh _ z e

private theorem eq_of_add_zero {I : Type} (a b : Word F I) (h : a+b=0) : a=b := by
  funext r
  exact (binary_add_eq_zero_iff _ _).mp (congrFun h r)

/-- Full actual seed Phi stays present; no claim that its chosen value is zero. -/
theorem seed_full_equation (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (i : StepIndex n) (ho : ¬(i.val+2)%2=0)
    (w : LocalizedWord S n sigma tau i.succ)
    (z : (state S (i.val+2)).presentation.Z)
    (e : ZDoubleCylinderEdge (state S (i.val+2)).presentation z S)
    (hw : hammingSupport w.word ⊆ {rzLocalEdge S (i.val+2) ho z e}) :
    (step S n sigma tau i w).lower.word=0 ∧
      w.word+(actualOutput S n sigma i).correction+(actualOutput S n tau i).correction=
        (SuffixData S n).family.coboundary0 i.succ (step S n sigma tau i w).potential := by
  have hz := seed_step_zero S n sigma tau i ho w z e hw
  refine ⟨hz,?_⟩
  have he := (step S n sigma tau i w).equation
  rw [hz,map_zero] at he
  exact eq_of_add_zero _ _ he.symm

private theorem killed_down {S : OddScale} {b : Nat} {q : Physical S (b+2)}
    (t : Killed S b q) :
    ∀ (total : Nat) (sigma tau : TopInput S total) (hb : b ≤ total)
      (w : LocalizedWord S total sigma tau ⟨b,Nat.lt_succ_of_le hb⟩),
      hammingSupport w.word ⊆ {q} →
      (down S total sigma tau b hb w
        ⟨seedDepth t,by have h:=seedDepth_lt t; omega⟩
        (by change seedDepth t ≤ b; have h:=seedDepth_lt t; omega)).word=0 := by
  induction t with
  | seed j ho z e =>
      intro total sigma tau hb w hw
      let i : StepIndex total := ⟨j,by omega⟩
      have hz := seed_step_zero S total sigma tau i ho w z e hw
      change (down S total sigma tau (j+1) hb w
        ⟨j,by omega⟩ (by change j ≤ j+1; omega)).word=0
      rw [down_succ S total sigma tau j hb w ⟨j,by omega⟩ (Nat.le_refl j)]
      rw [down_self]
      exact hz
  | @rx b q t he v ih =>
      intro total sigma tau hb w hw
      let i : StepIndex total := ⟨b,by omega⟩
      have hl := (step_rx_singleton S total sigma tau i he w q v hw).2
      change (down S total sigma tau (b+1) hb w
        ⟨seedDepth t,by have h:=seedDepth_lt t; omega⟩
        (by change seedDepth t ≤ b+1; have h:=seedDepth_lt t; omega)).word=0
      rw [down_succ S total sigma tau b hb w
        ⟨seedDepth t,by have h:=seedDepth_lt t; omega⟩
        (by change seedDepth t ≤ b; have h:=seedDepth_lt t; omega)]
      exact ih total sigma tau (by omega) _ hl
  | @rz b q t ho v ih =>
      intro total sigma tau hb w hw
      let i : StepIndex total := ⟨b,by omega⟩
      have hl := step_rz_singleton S total sigma tau i ho w q v hw
      change (down S total sigma tau (b+1) hb w
        ⟨seedDepth t,by have h:=seedDepth_lt t; omega⟩
        (by change seedDepth t ≤ b+1; have h:=seedDepth_lt t; omega)).word=0
      rw [down_succ S total sigma tau b hb w
        ⟨seedDepth t,by have h:=seedDepth_lt t; omega⟩
        (by change seedDepth t ≤ b; have h:=seedDepth_lt t; omega)]
      exact ih total sigma tau (by omega) _ hl
end FixedTotal

/-- Literal intermediate snapshot zero, derived from generated coordinate data. -/
theorem seed_snapshot_zero (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) :
    (BDL26BoundaryTailInvariance.snapshot S n u q (seedIndex t)).word=0 := by
  have hi : hammingSupport (BDL26BoundaryTailInvariance.physicalTop S n u q).word ⊆ {q} := by
    change hammingSupport (BDL26ActualFailureReadout.flip S n q) ⊆ {q}
    rw [flip_eq_basis]
    exact basis_singleton q
  exact killed_down t n (input S n u)
    (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) (Nat.le_refl _) _ hi

/-- The boundary-tail witness is constructed internally, not accepted from callers. -/
theorem seed_boundary (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) :
    (SuffixData S n).family.coboundary0 (seedIndex t) 0=
      (BDL26BoundaryTailInvariance.snapshot S n u q (seedIndex t)).word :=
  (map_zero _).trans (seed_snapshot_zero S n u q t).symm

/-- Original zero absorption; RZ Phi is retained and need not be zero. -/
theorem step_zero (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (i : StepIndex n) (w : LocalizedWord S n sigma tau i.succ) (hw : w.word=0) :
    (step S n sigma tau i w).lower.word=0 := by
  by_cases he : (BDL26LocalizedHistoryErrorDescent.Edge n i).val%2=0
  · have hs : second S n sigma tau i w=first S n sigma i := by
      change first S n sigma i+w.word=first S n sigma i
      rw [hw,add_zero]
    rw [step_rx S n sigma tau i he w]
    change BDL26RXPhysicalStarTransport.L S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i) he w.center
      (first S n sigma i) (second S n sigma tau i w)=0
    rw [hs]
    exact BDL26RXPhysicalStarTransport.lower_self S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i) he w.center _
  · rw [step_rz S n sigma tau i he w]
    change BDL26RZFiniteBlockTransport.lowerError S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i) he
      (first S n sigma i) (second S n sigma tau i w)=0
    rw [BDL26RZFiniteBlockTransport.lowerError_coordinates,representatives_difference,hw,map_zero,map_zero]

private theorem path_zero_below_nat (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (top : LocalizedWord S n sigma tau (TopIndex n)) (a : Nat) (ha : a ≤ n)
    (hz : (path S n sigma tau top ⟨a,Nat.lt_succ_of_le ha⟩).word=0)
    (b : LevelIndex n) (hb : b.val ≤ a) : (path S n sigma tau top b).word=0 := by
  cases a with
  | zero =>
      have h : b=⟨0,Nat.lt_succ_of_le ha⟩ := Fin.ext (by change b.val=0; omega)
      subst b
      exact hz
  | succ a =>
      by_cases h : b.val=a+1
      · have h' : b=⟨a+1,Nat.lt_succ_of_le ha⟩ := Fin.ext h
        subst b
        exact hz
      · let i : StepIndex n := ⟨a,by omega⟩
        have hl : (path S n sigma tau top i.castSucc).word=0 := by
          rw [path_step S n sigma tau top i]
          exact step_zero S n sigma tau i _ hz
        exact path_zero_below_nat S n sigma tau top a (by omega) hl b (by omega)
termination_by a

/-- Below the computed seed the SAME original descent word remains literally zero. -/
theorem snapshot_zero_below (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) (b : LevelIndex n)
    (hb : b.val ≤ seedDepth t) :
    (BDL26BoundaryTailInvariance.snapshot S n u q b).word=0 :=
  path_zero_below_nat S n (input S n u)
    (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q))
    (BDL26BoundaryTailInvariance.physicalTop S n u q) (seedDepth t)
    (by have h:=seedDepth_lt t; omega) (seed_snapshot_zero S n u q t) b hb

theorem terminal_zero (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) : (descent S n u q).word=0 := by
  have h := snapshot_zero_below S n u q t 0 (Nat.zero_le _)
  rw [BDL26BoundaryTailInvariance.snapshot_bottom] at h
  exact h


/-- All original input records below the internally computed seed agree. -/
theorem inputs_eq (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) (b : LevelIndex n)
    (hb : b.val ≤ seedDepth t) :
    actualInputs S n (input S n u) b=
      actualInputs S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) b :=
  BDL26BoundaryTailInvariance.physical_readouts_eq S n u q (seedIndex t) 0
    (seed_boundary S n u q t) b hb

theorem readouts_eq (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) (b : LevelIndex n)
    (hb : b.val ≤ seedDepth t) :
    actualReadout S n (input S n u) b=
      actualReadout S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) b :=
  BDL26BoundaryTailInvariance.tail_readouts_eq S n _ _
    (BDL26BoundaryTailInvariance.physicalTop S n u q) (seedIndex t) 0
    (seed_boundary S n u q t) b hb

theorem outputs_eq (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) (i : StepIndex n)
    (hi : i.succ.val ≤ seedDepth t) :
    actualOutput S n (input S n u) i=
      actualOutput S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) i :=
  BDL26BoundaryTailInvariance.tail_outputs_eq S n _ _
    (BDL26BoundaryTailInvariance.physicalTop S n u q) (seedIndex t) 0
    (seed_boundary S n u q t) i hi

theorem corrections_eq (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) (i : StepIndex n)
    (hi : i.succ.val ≤ seedDepth t) :
    (actualOutput S n (input S n u) i).correction=
      (actualOutput S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) i).correction :=
  BDL26BoundaryTailInvariance.tail_corrections_eq S n _ _
    (BDL26BoundaryTailInvariance.physicalTop S n u q) (seedIndex t) 0
    (seed_boundary S n u q t) i hi

/-- BOTH original calls cancel even when their common input or output is nonzero. -/
theorem base_calls (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) :
    firstReadout S n u=secondReadout S n u q ∧
      (actualBase S n).decode (actualInputs S n (input S n u) 0)=
        (actualBase S n).decode (actualInputs S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) 0) ∧
      BDL26LevelTwoDecoder.decode S (firstReadout S n u)=
        BDL26LevelTwoDecoder.decode S (secondReadout S n u q) :=
  BDL26BoundaryTailInvariance.physical_base_calls S n u q (seedIndex t) 0
    (seed_boundary S n u q t)

/-- FIRST-zero is optional; SECOND-zero is a conclusion, never a premise. -/
theorem second_zero (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) (hs : firstReadout S n u=0) :
    secondReadout S n u q=0 :=
  (base_calls S n u q t).1.symm.trans hs

/-- This chosen tail filling is retained verbatim, including possible kernel terms. -/
def bottomPotential (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) :
    (SuffixData S n).family.Cochain0 0 :=
  BDL26BoundaryTailInvariance.tailPotential S n _ _
    (BDL26BoundaryTailInvariance.physicalTop S n u q) (seedIndex t) 0
    (seed_boundary S n u q t) 0 (Nat.zero_le _)

/-- The literal #1595 full potential; no chosen value is replaced by zero. -/
def fullPotential (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) :
    (SuffixData S n).family.Cochain0 (TopIndex n) :=
  BDL26BoundaryTailInvariance.physicalPotential S n u q (seedIndex t) 0
    (seed_boundary S n u q t)

theorem full_potential_formula (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) :
    fullPotential S n u q t=
      intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
        (bottomPotential S n u q t)+BDL26ActualFailureReadout.accumulated S n u q := rfl

theorem full_potential_spec (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (fullPotential S n u q t)=
      BDL26LogicalDefectProtection.deltaX S n u q :=
  BDL26BoundaryTailInvariance.physical_potential_spec S n u q (seedIndex t) 0
    (seed_boundary S n u q t)

/-- Terminal zero follows from absorption, not from a chosen-potential value. -/
theorem accumulated_spec (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) :
    (SuffixData S n).family.coboundary0 (TopIndex n)
      (BDL26ActualFailureReadout.accumulated S n u q)=
      BDL26LogicalDefectProtection.deltaX S n u q := by
  let b : (SuffixData S n).family.Cochain1 0 :=
    (actualBase S n).decode
      (actualInputs S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) 0)
  have hc : (actualBase S n).decode (actualInputs S n (input S n u) 0)=b :=
    (base_calls S n u q t).2.1
  have hz : (descent S n u q).word=0 := terminal_zero S n u q t
  have he := congrArg₂ (fun x y : (SuffixData S n).family.Cochain1 0 => x+y) hz hc
  have hs := congrArg (fun x : (SuffixData S n).family.Cochain1 0 => x+b) he
  have hb : b+b=(0 : (SuffixData S n).family.Cochain1 0) := word_add_self b
  have hbase : (descent S n u q).word+
      (actualBase S n).decode (actualInputs S n (input S n u) 0)+
      (actualBase S n).decode
        (actualInputs S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) 0)=0 :=
    hs.trans ((congrArg (fun x : (SuffixData S n).family.Cochain1 0 => x+b)
      (zero_add b)).trans hb)
  have h := BDL26ActualFailureReadout.full_history S n u q
  rw [hbase,map_zero,zero_add] at h
  exact h.symm

theorem chiX_zero (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) :
    BDL26LogicalDefectProtection.chiX S n u q=0 :=
  BDL26BoundaryTailInvariance.physical_chiX_zero S n u q (seedIndex t) 0
    (seed_boundary S n u q t)

theorem source_even (S : OddScale) (k : Nat) (hk : 2 ≤ k)
    (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S (2*(k-1))) (q : Physical S (2*(k-1)+2))
    (t : Killed S (2*(k-1)) q) :
    2*(k-1)+2=2*k ∧ BDL26LogicalDefectProtection.chiX S (2*(k-1)) u q=0 :=
  ⟨by omega,chiX_zero S _ u q t⟩

open QEC.Semantics BDL26PairedDecoderPhase

theorem paired_X_zero (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (t : Killed S n q) :
    BDL26LogicalDefectProtection.dX S n s (CSSDaviesLocality.singlePauli q .x)=0 :=
  BDL26BoundaryTailInvariance.paired_X_zero S n s q (seedIndex t) 0
    (seed_boundary S n s.1 q t)

theorem paired_Y_zero (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (t : Killed S n q) :
    BDL26LogicalDefectProtection.dX S n s (CSSDaviesLocality.singlePauli q .y)=0 :=
  BDL26BoundaryTailInvariance.paired_Y_zero S n s q (seedIndex t) 0
    (seed_boundary S n s.1 q t)

theorem physical_X_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (t : Killed S n q) :
    (PauliSymplectic.toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x)*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*PauliSymplectic.toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x))*
      atom S n s=0 :=
  BDL26BoundaryTailInvariance.physical_X_dressed_Z S n s q (seedIndex t) 0
    (seed_boundary S n s.1 q t)

theorem physical_Y_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (t : Killed S n q) :
    (PauliSymplectic.toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y)*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*PauliSymplectic.toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y))*
      atom S n s=0 :=
  BDL26BoundaryTailInvariance.physical_Y_dressed_Z S n s q (seedIndex t) 0
    (seed_boundary S n s.1 q t)

theorem actual_X_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (t : Killed S n q) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q .x*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .x)*atom S n s=0 :=
  BDL26BoundaryTailInvariance.actual_X_dressed_Z S n s q (seedIndex t) 0
    (seed_boundary S n s.1 q t)

theorem actual_Y_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (t : Killed S n q) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q .y*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .y)*atom S n s=0 :=
  BDL26BoundaryTailInvariance.actual_Y_dressed_Z S n s q (seedIndex t) 0
    (seed_boundary S n s.1 q t)

theorem actual_Y_package (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (t : Killed S n q) :
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) ∧
      (BDL26CSSDaviesLocality.coupling S (n+2) q .y*BDL26PairedDecoderChannel.dressedZ S n-
        BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .y)*atom S n s=0 :=
  BDL26BoundaryTailInvariance.actual_Y_package S n s q (seedIndex t) 0
    (seed_boundary S n s.1 q t)

end QEC.Coding.BDL26RZLocalEdgeTower
