import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.ActualFailureReadout
import QEC.Coding.FiniteAlternatingConstruction.RXCohomology

/-!
# Boundary tails in the original fixed-depth stopped histories

Project-derived internal/API propagation for BDL26 paper.tex3434–3484.
An intermediate boundary in the existing localized path remains a boundary
below that snapshot. Both original histories, their possibly nonzero common
base output, and every original accumulated potential are retained. This
does not prove that a physical flip reaches such a snapshot, FIRST-zero
stability, ALL-component locality, chiZ, full XYZ or a lifetime bound.
-/
noncomputable section
namespace QEC.Coding.BDL26BoundaryTailInvariance
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26TannerLocalRegularity
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26TransposedStoppedDecoder PauliSymplectic
open scoped Classical

abbrev W (S : OddScale) (n : Nat) (a : LevelIndex n) :=
  (SuffixData S n).family.Cochain1 a
abbrev V (S : OddScale) (n : Nat) (a : LevelIndex n) :=
  (SuffixData S n).family.Cochain0 a

private theorem word_eq_of_add_zero {I : Type} (u v : Word BDL26Field I)
    (h : u+v=0) : u=v := by
  funext i
  exact (binary_add_eq_zero_iff _ _).mp (congrFun h i)

/-- Boundary data at this literal snapshot forces the original inputs to agree. -/
theorem inputs_eq (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (a : LevelIndex n) (u : LocalizedWord S n sigma tau a) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=u.word) :
    actualInputs S n sigma a=actualInputs S n tau a := by
  have hz : (SuffixData S n).family.coboundary1 a u.word=0 := by
    rw [← hp]
    exact LinearMap.congr_fun ((SuffixData S n).family.coboundary1_comp_coboundary0 a) p
  exact Subtype.ext (word_eq_of_add_zero _ _ (u.syndrome.symm.trans hz))

/-- These are complete original outputs, not just their coarse values. -/
theorem output_eq (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (i : StepIndex n) (u : LocalizedWord S n sigma tau i.succ) (p : V S n i.succ)
    (hp : (SuffixData S n).family.coboundary0 i.succ p=u.word) :
    actualOutput S n sigma i=actualOutput S n tau i := by
  unfold actualOutput
  rw [inputs_eq S n sigma tau i.succ u p hp]

/-- The actual step potential stays in the full equation after cancellation. -/
theorem step_boundary_equation (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (i : StepIndex n) (u : LocalizedWord S n sigma tau i.succ) (p : V S n i.succ)
    (hp : (SuffixData S n).family.coboundary0 i.succ p=u.word) :
    ((SuffixData S n).selectedMap i).map1 (step S n sigma tau i u).lower.word=
      (SuffixData S n).family.coboundary0 i.succ
        (p+(step S n sigma tau i u).potential) := by
  have hc := congrArg (fun out : AssemblyStepOutput (SuffixData S n) i => out.correction)
    (output_eq S n sigma tau i u p hp)
  rw [(step S n sigma tau i u).equation,← hp,hc,map_add]
  calc
    _ = (SuffixData S n).family.coboundary0 i.succ p+
        ((actualOutput S n tau i).correction+(actualOutput S n tau i).correction)+
        (SuffixData S n).family.coboundary0 i.succ (step S n sigma tau i u).potential := by abel
    _ = _ := by rw [word_add_self,add_zero]

private theorem rx_reflection_transport (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (U : TannerSquarePresentation) (e : U=BDL26RXLocalReplacement.rxReplacementPresentation P S)
    (f : Word BDL26Field P.Q →ₗ[BDL26Field] Word BDL26Field U.Q)
    (hf : HEq f (BDL26ReplacementCochainMaps.rxMap1Coord P S))
    (v : Word BDL26Field P.Q) (p : Word BDL26Field U.X)
    (hp : tannerCoboundary0 U p=f v) :
    ∃ q : Word BDL26Field P.X, tannerCoboundary0 P q=v := by
  cases e
  have hm : f=BDL26ReplacementCochainMaps.rxMap1Coord P S := eq_of_heq hf
  rw [hm,BDL26RXCohomology.differential0_eq P A R S] at hp
  exact (BDL26RXCohomology.raw_boundary_iff P A.toTannerSquareAdmissible S v).mp ⟨p,hp⟩

private theorem rx_indexed_reflection (S : OddScale) (d : Nat) (i : StepIndex d)
    (he : i.val%2=0) (v : (indexedFamily S d).Cochain1 i.castSucc)
    (p : (indexedFamily S d).Cochain0 i.succ)
    (hp : (indexedFamily S d).coboundary0 i.succ p=
      ((indexedDecoderData S d).selectedMap i).map1 v) :
    ∃ q : (indexedFamily S d).Cochain0 i.castSucc,
      (indexedFamily S d).coboundary0 i.castSucc q=v := by
  have e : (state S (i.val+1)).presentation=
      BDL26RXLocalReplacement.rxReplacementPresentation (state S i.val).presentation S := by
    change (nextState S i.val (state S i.val)).presentation=(rxState S (state S i.val)).presentation
    exact congrArg ConstructionState.presentation (if_pos he)
  have hp0 : tannerCoboundary0 (state S (i.val+1)).presentation p=
      ((indexedDecoderData S d).selectedMap i).map1 v := by
    funext r
    exact (congrFun (LinearMap.congr_fun (indexedFamily_coboundary0 S d i.succ) p) r).symm.trans
      (congrFun hp r)
  obtain ⟨q,hq⟩ := rx_reflection_transport (state S i.val).presentation
    (state S i.val).admissible (state S i.val).regular S _ e
    ((indexedDecoderData S d).selectedMap i).map1
    (indexedDecoderData_selected_rx S d i he).2.1 v p hp0
  refine ⟨q,?_⟩
  funext r
  exact (congrFun (LinearMap.congr_fun (indexedFamily_coboundary0 S d i.castSucc) q) r).trans
    (congrFun hq r)

/-- Concrete RX raw boundary reflection constructs the actual lower filling. -/
theorem rx_lower_exists (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (i : StepIndex n) (he : (Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) (p : V S n i.succ)
    (hp : (SuffixData S n).family.coboundary0 i.succ p=u.word) :
    ∃ q : V S n i.castSucc, (SuffixData S n).family.coboundary0 i.castSucc q=
      (step S n sigma tau i u).lower.word := by
  have hs := step_boundary_equation S n sigma tau i u p hp
  rw [LevelTwoHistory.suffix_selected_map1,LevelTwoHistory.suffix_coboundary0] at hs
  obtain ⟨q,hq⟩ := rx_indexed_reflection S (n+2) (Edge n i) he _ _ hs.symm
  refine ⟨q,?_⟩
  change (SuffixData S n).family.coboundary0 i.castSucc q=
    (step S n sigma tau i u).lower.word at hq
  exact hq

/-- The RZ filling is the parity of ALL actual degree-zero coordinates. -/
def rzLowerPotential (S : OddScale) (n : Nat) (i : StepIndex n)
    (ho : ¬(Edge n i).val%2=0) (p : V S n i.succ) : V S n i.castSucc :=
  BDL26LevelTwoDistance.rzOldXParity
    (BDL26RZFiniteBlockTransport.Old S (n+2) (Edge n i)) S
    (BDL26RZFiniteBlockTransport.read0 S (n+2) (Edge n i) ho p)

/-- No RZ filling is set to zero: the lower word remains the original parity. -/
theorem rz_lower_spec (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (i : StepIndex n) (ho : ¬(Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) (p : V S n i.succ)
    (hp : (SuffixData S n).family.coboundary0 i.succ p=u.word) :
    (SuffixData S n).family.coboundary0 i.castSucc (rzLowerPotential S n i ho p)=
      (step S n sigma tau i u).lower.word := by
  have hl : (step S n sigma tau i u).lower.word=
      BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) ho
        (first S n sigma i) (second S n sigma tau i u) := by
    rw [step_rz S n sigma tau i ho u]
    rfl
  have hp' : (indexedFamily S (n+2)).coboundary0 (Edge n i).succ p=u.word := by
    change (SuffixData S n).family.coboundary0 i.succ p=u.word
    exact hp
  have hd := BDL26RZFiniteBlockTransport.delta0_coordinates S (n+2) (Edge n i) ho p
  have hq := BDL26LevelTwoDistance.rzQParity_coboundary
    (BDL26RZFiniteBlockTransport.Old S (n+2) (Edge n i))
    (state S (Edge n i).val).admissible S
    (BDL26RZFiniteBlockTransport.read0 S (n+2) (Edge n i) ho p)
  rw [← hd,hp'] at hq
  rw [hl,BDL26RZFiniteBlockTransport.lowerError_coordinates,
    representatives_difference S n sigma tau i u]
  rw [suffix_delta0]
  exact hq.symm

/-- RX uses its proved reflection; RZ uses the literal parity formula. -/
def lowerPotential (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (i : StepIndex n) (u : LocalizedWord S n sigma tau i.succ) (p : V S n i.succ)
    (hp : (SuffixData S n).family.coboundary0 i.succ p=u.word) : V S n i.castSucc :=
  if he : (Edge n i).val%2=0 then Classical.choose (rx_lower_exists S n sigma tau i he u p hp)
  else rzLowerPotential S n i he p

theorem lower_potential_spec (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (i : StepIndex n) (u : LocalizedWord S n sigma tau i.succ) (p : V S n i.succ)
    (hp : (SuffixData S n).family.coboundary0 i.succ p=u.word) :
    (SuffixData S n).family.coboundary0 i.castSucc (lowerPotential S n sigma tau i u p hp)=
      (step S n sigma tau i u).lower.word := by
  unfold lowerPotential
  split
  · rename_i he
    exact Classical.choose_spec (rx_lower_exists S n sigma tau i he u p hp)
  · rename_i ho
    exact rz_lower_spec S n sigma tau i ho u p hp

private theorem tail_exists_nat (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (top : LocalizedWord S n sigma tau (TopIndex n)) (a : Nat) (ha : a≤n)
    (p : V S n ⟨a,Nat.lt_succ_of_le ha⟩)
    (hp : (SuffixData S n).family.coboundary0 ⟨a,Nat.lt_succ_of_le ha⟩ p=
      (path S n sigma tau top ⟨a,Nat.lt_succ_of_le ha⟩).word)
    (b : LevelIndex n) (hb : b.val≤a) :
    ∃ q : V S n b, (SuffixData S n).family.coboundary0 b q=(path S n sigma tau top b).word := by
  cases a with
  | zero =>
      have h : b=⟨0,Nat.lt_succ_of_le ha⟩ := Fin.ext (by change b.val=0; omega)
      subst b
      exact ⟨p,hp⟩
  | succ a =>
      by_cases h : b.val=a+1
      · have h' : b=⟨a+1,Nat.lt_succ_of_le ha⟩ := Fin.ext h
        subst b
        exact ⟨p,hp⟩
      · let j : StepIndex n := ⟨a,by omega⟩
        let v := path S n sigma tau top j.succ
        let q := lowerPotential S n sigma tau j v p hp
        have hq : (SuffixData S n).family.coboundary0 j.castSucc q=
            (path S n sigma tau top j.castSucc).word := by
          rw [path_step S n sigma tau top j]
          exact lower_potential_spec S n sigma tau j v p hp
        exact tail_exists_nat S n sigma tau top a (by omega) q hq b (by omega)
termination_by a

/-- A filling constructed through the existing path at the SAME total depth. -/
def tailPotential (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (top : LocalizedWord S n sigma tau (TopIndex n)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(path S n sigma tau top a).word)
    (b : LevelIndex n) (hb : b.val≤a.val) : V S n b :=
  Classical.choose (tail_exists_nat S n sigma tau top a.val (Nat.le_of_lt_succ a.isLt) p hp b hb)

theorem tail_potential_spec (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (top : LocalizedWord S n sigma tau (TopIndex n)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(path S n sigma tau top a).word)
    (b : LevelIndex n) (hb : b.val≤a.val) :
    (SuffixData S n).family.coboundary0 b (tailPotential S n sigma tau top a p hp b hb)=
      (path S n sigma tau top b).word :=
  Classical.choose_spec (tail_exists_nat S n sigma tau top a.val (Nat.le_of_lt_succ a.isLt) p hp b hb)

theorem tail_inputs_eq (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (top : LocalizedWord S n sigma tau (TopIndex n)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(path S n sigma tau top a).word)
    (b : LevelIndex n) (hb : b.val≤a.val) : actualInputs S n sigma b=actualInputs S n tau b :=
  inputs_eq S n sigma tau b _ _ (tail_potential_spec S n sigma tau top a p hp b hb)

theorem tail_readouts_eq (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (top : LocalizedWord S n sigma tau (TopIndex n)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(path S n sigma tau top a).word)
    (b : LevelIndex n) (hb : b.val≤a.val) : actualReadout S n sigma b=actualReadout S n tau b := by
  rw [actualInputs_readout S n sigma b,actualInputs_readout S n tau b]
  exact congrArg Subtype.val (tail_inputs_eq S n sigma tau top a p hp b hb)

theorem tail_outputs_eq (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (top : LocalizedWord S n sigma tau (TopIndex n)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(path S n sigma tau top a).word)
    (i : StepIndex n) (hi : i.succ.val≤a.val) : actualOutput S n sigma i=actualOutput S n tau i := by
  unfold actualOutput
  rw [tail_inputs_eq S n sigma tau top a p hp i.succ hi]

theorem tail_corrections_eq (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (top : LocalizedWord S n sigma tau (TopIndex n)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(path S n sigma tau top a).word)
    (i : StepIndex n) (hi : i.succ.val≤a.val) :
    (actualOutput S n sigma i).correction=(actualOutput S n tau i).correction :=
  congrArg (fun out : AssemblyStepOutput (SuffixData S n) i => out.correction)
    (tail_outputs_eq S n sigma tau top a p hp i hi)

/-- Equal nonzero original base outputs are allowed and cancel literally. -/
theorem base_calls_eq (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (top : LocalizedWord S n sigma tau (TopIndex n)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(path S n sigma tau top a).word) :
    (actualBase S n).decode (actualInputs S n sigma 0)=
      (actualBase S n).decode (actualInputs S n tau 0) := by
  rw [tail_inputs_eq S n sigma tau top a p hp 0 (Nat.zero_le _)]

theorem base_residual_boundary (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (top : LocalizedWord S n sigma tau (TopIndex n)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(path S n sigma tau top a).word) :
    (SuffixData S n).family.coboundary0 0 (tailPotential S n sigma tau top a p hp 0 (Nat.zero_le _))=
      (path S n sigma tau top 0).word+(actualBase S n).decode (actualInputs S n sigma 0)+
        (actualBase S n).decode (actualInputs S n tau 0) := by
  have hc : (path S n sigma tau top 0).word+
      (actualBase S n).decode (actualInputs S n sigma 0)+
      (actualBase S n).decode (actualInputs S n tau 0)=(path S n sigma tau top 0).word := by
    let w : W S n 0 := (path S n sigma tau top 0).word
    let b : W S n 0 := (actualBase S n).decode (actualInputs S n tau 0)
    have he : (actualBase S n).decode (actualInputs S n sigma 0)=b :=
      base_calls_eq S n sigma tau top a p hp
    have hb : b+b=(0 : W S n 0) := word_add_self b
    change (w+(actualBase S n).decode (actualInputs S n sigma 0))+b=w
    exact (congrArg (fun c : W S n 0 => (w+c)+b) he).trans
      ((add_assoc w b b).trans ((congrArg (fun c : W S n 0 => w+c) hb).trans (add_zero w)))
  exact (tail_potential_spec S n sigma tau top a p hp 0 (Nat.zero_le _)).trans hc.symm

/-- The ORIGINAL total accumulation includes all levels ABOVE the stop a. -/
def fullPotential (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (top : LocalizedWord S n sigma tau (TopIndex n)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(path S n sigma tau top a).word) : V S n (TopIndex n) :=
  intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
    (tailPotential S n sigma tau top a p hp 0 (Nat.zero_le _))+
      intervalPotential S n sigma tau top 0 (TopIndex n)

theorem full_potential_spec (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (top : LocalizedWord S n sigma tau (TopIndex n)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(path S n sigma tau top a).word) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (fullPotential S n sigma tau top a p hp)=
      top.word+historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma)+
        historyLiftedCorrection (SuffixData S n) (actualHistory S n tau) := by
  unfold fullPotential
  rw [map_add,intervalMap_commutes0 _ n (Nat.le_refl _) 0 (Nat.zero_le _),
    base_residual_boundary S n sigma tau top a p hp]
  exact (history_equation S n sigma tau top).symm

/-- Physical localization is constructed internally from the actual flip. -/
theorem physical_supported (S : OddScale) (n : Nat) (q : Physical S (n+2)) :
    hammingSupport (BDL26ActualFailureReadout.flip S n q) ⊆ star S n (TopIndex n) (elementaryCenter S n q) := by
  rw [flip_eq_basis]
  exact elementary_support S n q

/-- This is the pre-existing initial state of the actual physical flip. -/
def physicalTop (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n) (q : Physical S (n+2)) :=
  BDL26LocalizedHistoryErrorDescent.initial S n (input S n u) (BDL26ActualFailureReadout.flip S n q)
    (elementaryCenter S n q) (physical_supported S n q)

def snapshot (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n) (q : Physical S (n+2)) (a : LevelIndex n) :=
  path S n (input S n u) (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) (physicalTop S n u q) a

theorem snapshot_original (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (a : LevelIndex n) : snapshot S n u q a=
      actualDescent S n (input S n u) (BDL26ActualFailureReadout.flip S n q) (elementaryCenter S n q)
        (physical_supported S n q) a := rfl

theorem snapshot_bottom (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) : snapshot S n u q 0=BDL26ActualFailureReadout.descent S n u q := rfl

theorem physical_readouts_eq (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n u q a).word)
    (b : LevelIndex n) (hb : b.val≤a.val) :
    actualInputs S n (input S n u) b=
      actualInputs S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) b :=
  tail_inputs_eq S n _ _ (physicalTop S n u q) a p hp b hb

theorem physical_base_calls (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n u q a).word) :
    firstReadout S n u=secondReadout S n u q ∧
      (actualBase S n).decode (actualInputs S n (input S n u) 0)=
        (actualBase S n).decode (actualInputs S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) 0) ∧
      BDL26LevelTwoDecoder.decode S (firstReadout S n u)=
        BDL26LevelTwoDecoder.decode S (secondReadout S n u q) := by
  have hi := physical_readouts_eq S n u q a p hp 0 (Nat.zero_le _)
  have hv : firstReadout S n u=secondReadout S n u q := congrArg Subtype.val hi
  exact ⟨hv,base_calls_eq S n _ _ (physicalTop S n u q) a p hp,
    congrArg (BDL26LevelTwoDecoder.decode S) hv⟩

def physicalPotential (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n u q a).word) : V S n (TopIndex n) :=
  fullPotential S n _ _ (physicalTop S n u q) a p hp

/-- The full accumulation is literally the original physical accumulation. -/
theorem physical_potential_formula (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n u q a).word) :
    physicalPotential S n u q a p hp=
      intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
        (tailPotential S n _ _ (physicalTop S n u q) a p hp 0 (Nat.zero_le _))+
        BDL26ActualFailureReadout.accumulated S n u q := rfl

theorem physical_potential_spec (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n u q a).word) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (physicalPotential S n u q a p hp)=
      BDL26LogicalDefectProtection.deltaX S n u q := by
  have h := full_potential_spec S n _ _ (physicalTop S n u q) a p hp
  change (SuffixData S n).family.coboundary0 (TopIndex n) (physicalPotential S n u q a p hp)=
    topWord S n (input S n u) (BDL26ActualFailureReadout.flip S n q) at h
  exact h.trans (BDL26ActualFailureReadout.full_residual S n u q)

theorem physical_chiX_zero (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n u q a).word) :
    BDL26LogicalDefectProtection.chiX S n u q=0 := by
  rw [chiX_top_coefficient]
  apply (top_zero_iff_boundary S n (input S n u) (BDL26ActualFailureReadout.flip S n q)).mpr
  refine ⟨physicalPotential S n u q a p hp,?_⟩
  rw [BDL26ActualFailureReadout.full_residual]
  exact physical_potential_spec S n u q a p hp

theorem source_even (S : OddScale) (k : Nat) (hk : 1≤k)
    (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S (2*(k-1))) (q : Physical S (2*(k-1)+2))
    (a : LevelIndex (2*(k-1))) (p : V S (2*(k-1)) a)
    (hp : (SuffixData S (2*(k-1))).family.coboundary0 a p=(snapshot S (2*(k-1)) u q a).word) :
    2*(k-1)+2=2*k ∧ BDL26LogicalDefectProtection.chiX S (2*(k-1)) u q=0 :=
  ⟨by omega,physical_chiX_zero S _ u q a p hp⟩

open QEC.Semantics BDL26PairedDecoderPhase

theorem paired_X_zero (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n s.1 q a).word) :
    BDL26LogicalDefectProtection.dX S n s (CSSDaviesLocality.singlePauli q .x)=0 := by
  rw [paired_X_bit]
  exact physical_chiX_zero S n s.1 q a p hp

theorem paired_Y_zero (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n s.1 q a).word) :
    BDL26LogicalDefectProtection.dX S n s (CSSDaviesLocality.singlePauli q .y)=0 := by
  rw [paired_Y_bit]
  exact physical_chiX_zero S n s.1 q a p hp

theorem physical_X_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n s.1 q a).word) :
    (PauliSymplectic.toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x)*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*PauliSymplectic.toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x))*
      atom S n s=0 := by
  apply (BDL26LogicalDefectProtection.protected_Z_iff S n s _).mpr
  exact paired_X_zero S n s q a p hp

theorem physical_Y_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n s.1 q a).word) :
    (PauliSymplectic.toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y)*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*PauliSymplectic.toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y))*
      atom S n s=0 := by
  apply (BDL26LogicalDefectProtection.protected_Z_iff S n s _).mpr
  exact paired_Y_zero S n s q a p hp

theorem actual_X_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n s.1 q a).word) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q .x*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .x)*atom S n s=0 :=
  physical_X_dressed_Z S n s q a p hp

theorem actual_Y_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n s.1 q a).word) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q .y*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .y)*atom S n s=0 :=
  physical_Y_dressed_Z S n s q a p hp

theorem actual_Y_package (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n s.1 q a).word) :
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) ∧
      (BDL26CSSDaviesLocality.coupling S (n+2) q .y*BDL26PairedDecoderChannel.dressedZ S n-
        BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .y)*atom S n s=0 :=
  ⟨BDL26ActualFailureReadout.physical_Y_iXZ S n q,actual_Y_dressed_Z S n s q a p hp⟩

end QEC.Coding.BDL26BoundaryTailInvariance
