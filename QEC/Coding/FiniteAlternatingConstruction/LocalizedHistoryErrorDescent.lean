import QEC.Coding.FiniteAlternatingConstruction.RZPhysicalXStarTransport
import QEC.Coding.FiniteAlternatingConstruction.HistoryErrorTelescoping

/-!
# Correlated localized descent in the original stopped histories

Internal finite refinement of BDL26 paper.tex2325–2384,3136–3185,3455–3477.
Every representative is constructed from an original input; the second is
correlated by the fixed error difference. No canonical selector is assumed
linear. All full potentials and original correction positions are retained.
Physical-star support is not an owner-local F17 correctness assertion.
-/
noncomputable section
namespace QEC.Coding.BDL26LocalizedHistoryErrorDescent

open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators

private theorem twice {I : Type} (w : Word BDL26Field I) : w+w=0 := by
  funext q
  exact ZModModule.add_self (w q)

private theorem cancel_pair {I : Type} (a b : Word BDL26Field I) : a+(a+b)=b := by
  rw [← add_assoc,twice,zero_add]

abbrev Data (S : OddScale) (n : Nat) := SuffixData S n
abbrev Edge (n : Nat) (i : StepIndex n) := LevelTwoHistory.physicalStep i

def star (S : OddScale) (n : Nat) (a : LevelIndex n)
    (x : (state S (a.val+2)).presentation.X) :
    Finset (state S (a.val+2)).presentation.Q :=
  BDL26RXPhysicalStarTransport.physicalXStar (state S (a.val+2)).presentation x

/-- This is a proved incidence bound on the actual state, not a caller radius. -/
theorem star_card (S : OddScale) (n : Nat) (a : LevelIndex n)
    (x : (state S (a.val+2)).presentation.X) : (star S n a x).card ≤ 7 := by
  have h := BDL26GraphQuantitativeBounds.state_tannerDegree_le S (a.val+2) (Vertex.x x)
  rw [BDL26GraphQuantitativeBounds.tannerDegree,
    Fintype.card_congr (BDL26GraphQuantitativeBounds.xNeighborEquiv _ x)] at h
  simpa [star,BDL26RXPhysicalStarTransport.physicalXStar,Fintype.card_subtype] using h

variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)

/-- A state of the constructed recursion. No endpoint accepts this as a
certificate: the initial state and every successor are proved below. -/
structure LocalizedWord (a : LevelIndex n) where
  word : (Data S n).family.Cochain1 a
  center : (state S (a.val+2)).presentation.X
  supported : hammingSupport word ⊆ star S n a center
  syndrome : (Data S n).family.coboundary1 a word =
    (actualInputs S n sigma a).val+(actualInputs S n tau a).val

/-- Literal complete physical output on the original stored input. -/
def originalOutput (i : StepIndex n) :
    AssemblyStepOutput (indexedDecoderData S (n+2)) (Edge n i) :=
  actualStep S (n+2) (Edge n i) (actualInputs S n sigma i.succ)

theorem originalOutput_snapshot (i : StepIndex n) : originalOutput S n sigma i =
    BDL26CanonicalHistoryMarks.outputAt S n sigma i := by
  change actualStep S (n+2) (Edge n i) (actualInputs S n sigma i.succ)=
    actualStep S (n+2) (Edge n i) (BDL26CanonicalHistoryMarks.inputAt S n sigma i.succ)
  rw [BDL26RZPhysicalXStarTransport.original_input_eq]

theorem originalOutput_correction (i : StepIndex n) :
    (originalOutput S n sigma i).correction=(actualOutput S n sigma i).correction := rfl

theorem originalOutput_coarse (i : StepIndex n) :
    (originalOutput S n sigma i).coarse=actualInputs S n sigma i.castSucc :=
  (actualInputs_step S n sigma i).symm

/-- Only the first original input is used to choose a preimage. -/
def first (i : StepIndex n) : (Data S n).family.Cochain1 i.succ :=
  Classical.choose (actualInputs S n sigma i.succ).property

theorem first_spec (i : StepIndex n) :
    (Data S n).family.coboundary1 i.succ (first S n sigma i)=
      (actualInputs S n sigma i.succ).val :=
  Classical.choose_spec (actualInputs S n sigma i.succ).property

/-- The second representative is correlated, never chosen independently. -/
def second (i : StepIndex n) (u : LocalizedWord S n sigma tau i.succ) :
    (Data S n).family.Cochain1 i.succ := first S n sigma i+u.word

theorem second_spec (i : StepIndex n) (u : LocalizedWord S n sigma tau i.succ) :
    (Data S n).family.coboundary1 i.succ (second S n sigma tau i u)=
      (actualInputs S n tau i.succ).val := by
  rw [second,map_add,first_spec,u.syndrome]
  exact cancel_pair _ _

theorem representatives_difference (i : StepIndex n)
    (u : LocalizedWord S n sigma tau i.succ) :
    first S n sigma i+second S n sigma tau i u=u.word := cancel_pair _ _

private theorem rx_first (i : StepIndex n) (h : (Edge n i).val%2=0) :
    BDL26RXErrorPullback.run S (n+2) (Edge n i) h (first S n sigma i)=
      originalOutput S n sigma i := by
  have hi : BDL26RXErrorPullback.errorSyndrome S (n+2) (Edge n i) (first S n sigma i)=
      actualInputs S n sigma i.succ := Subtype.ext (first_spec S n sigma i)
  rw [BDL26RXErrorPullback.run,hi,originalOutput,actualStep_rx S (n+2) (Edge n i) h]

private theorem rx_second (i : StepIndex n) (h : (Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    BDL26RXErrorPullback.run S (n+2) (Edge n i) h (second S n sigma tau i u)=
      originalOutput S n tau i := by
  have hi : BDL26RXErrorPullback.errorSyndrome S (n+2) (Edge n i) (second S n sigma tau i u)=
      actualInputs S n tau i.succ := Subtype.ext (second_spec S n sigma tau i u)
  rw [BDL26RXErrorPullback.run,hi,originalOutput,actualStep_rx S (n+2) (Edge n i) h]

private theorem rz_first (i : StepIndex n) (h : ¬(Edge n i).val%2=0) :
    BDL26RZErrorPullback.run S (n+2) (Edge n i) h (first S n sigma i)=
      originalOutput S n sigma i := by
  have hi : BDL26RZErrorPullback.errorSyndrome S (n+2) (Edge n i) (first S n sigma i)=
      actualInputs S n sigma i.succ := Subtype.ext (first_spec S n sigma i)
  rw [BDL26RZErrorPullback.run,hi,originalOutput,actualStep_rz S (n+2) (Edge n i) h]

private theorem rz_second (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    BDL26RZErrorPullback.run S (n+2) (Edge n i) h (second S n sigma tau i u)=
      originalOutput S n tau i := by
  have hi : BDL26RZErrorPullback.errorSyndrome S (n+2) (Edge n i) (second S n sigma tau i u)=
      actualInputs S n tau i.succ := Subtype.ext (second_spec S n sigma tau i u)
  rw [BDL26RZErrorPullback.run,hi,originalOutput,actualStep_rz S (n+2) (Edge n i) h]

/-- Constructed one-step data; the equation uses the full original corrections. -/
structure StepResult (i : StepIndex n) (u : LocalizedWord S n sigma tau i.succ) where
  lower : LocalizedWord S n sigma tau i.castSucc
  potential : (Data S n).family.Cochain0 i.succ
  equation : ((Data S n).selectedMap i).map1 lower.word=
    u.word+(actualOutput S n sigma i).correction+(actualOutput S n tau i).correction+
      (Data S n).family.coboundary0 i.succ potential

private theorem rx_localized (i : StepIndex n) (h : (Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    BDL26RXPhysicalStarTransport.Localized S (n+2) (Edge n i) u.center
      (first S n sigma i) (second S n sigma tau i u) := by
  change hammingSupport (first S n sigma i+second S n sigma tau i u) ⊆ _
  rw [representatives_difference]
  exact u.supported

private theorem rz_localized (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    BDL26RZPhysicalXStarTransport.Localized S (n+2) (Edge n i) u.center
      (first S n sigma i) (second S n sigma tau i u) := by
  change hammingSupport (first S n sigma i+second S n sigma tau i u) ⊆ _
  rw [representatives_difference]
  exact u.supported

def rxResult (i : StepIndex n) (h : (Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) : StepResult S n sigma tau i u := by
  let A := first S n sigma i
  let B := second S n sigma tau i u
  have hr := BDL26RXPhysicalStarTransport.two_run S (n+2) (Edge n i) h u.center A B
    (rx_localized S n sigma tau i h u)
  dsimp only [A,B] at hr
  refine {
    lower := {
      word := BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) h u.center A B
      center := BDL26RXPhysicalStarTransport.parentX S (n+2) (Edge n i) h u.center
      supported := hr.2.2.2.2.2.1
      syndrome := ?_ }
    potential := BDL26RXPhysicalStarTransport.Phi S (n+2) (Edge n i) h u.center A B
    equation := ?_ }
  · dsimp only [A,B]
    have hs := hr.2.2.1
    change (indexedFamily S (n+2)).coboundary1 (Edge n i).castSucc
      (BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) h u.center
        (first S n sigma i) (second S n sigma tau i u))=
      (BDL26RXErrorPullback.run S (n+2) (Edge n i) h (first S n sigma i)).coarse.val+
        (BDL26RXErrorPullback.run S (n+2) (Edge n i) h
          (second S n sigma tau i u)).coarse.val at hs
    rw [rx_first S n sigma i h,rx_second S n sigma tau i h u,
      originalOutput_coarse S n sigma i,originalOutput_coarse S n tau i] at hs
    rw [indexedFamily_coboundary1] at hs
    rw [LevelTwoHistory.suffix_coboundary1]
    change (indexedFamily S (n+2)).coboundary1
      (LevelTwoHistory.physicalLevel i.castSucc)
      (BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) h u.center
        (first S n sigma i) (second S n sigma tau i u))=_
    rw [indexedFamily_coboundary1]
    funext z
    have hz := congrFun hs z
    change (BDL26RZMap1CoordinateBridge.tannerCoboundary1 (state S (i.val+2)).presentation
      (BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) h u.center
        (first S n sigma i) (second S n sigma tau i u))) z=
      (actualInputs S n sigma i.castSucc).val z+(actualInputs S n tau i.castSucc).val z at hz ⊢
    exact hz
  · dsimp only [A,B]
    rw [LevelTwoHistory.suffix_selected_map1,LevelTwoHistory.suffix_coboundary0]
    change ((indexedDecoderData S (n+2)).selectedMap (Edge n i)).map1
      (BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) h u.center
        (first S n sigma i) (second S n sigma tau i u))=
      u.word+(actualOutput S n sigma i).correction+(actualOutput S n tau i).correction+
        (indexedFamily S (n+2)).coboundary0 (LevelTwoHistory.physicalLevel i.succ)
          (BDL26RXPhysicalStarTransport.Phi S (n+2) (Edge n i) h u.center
            (first S n sigma i) (second S n sigma tau i u))
    rw [indexedFamily_coboundary0]
    have he := hr.2.1
    rw [BDL26RXErrorPullback.updated,rx_first,rx_second,originalOutput_correction S n sigma i,
      originalOutput_correction S n tau i,indexedFamily_coboundary0] at he
    funext q
    have hq := congrFun he q
    change (((indexedDecoderData S (n+2)).selectedMap (Edge n i)).map1
      (BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) h u.center
        (first S n sigma i) (second S n sigma tau i u))) q=
      ((first S n sigma i) q+(second S n sigma tau i u) q)+
        (actualOutput S n sigma i).correction q+(actualOutput S n tau i).correction q+
        (BDL26RZMap1CoordinateBridge.tannerCoboundary0 (state S (i.val+3)).presentation
          (BDL26RXPhysicalStarTransport.Phi S (n+2) (Edge n i) h u.center
            (first S n sigma i) (second S n sigma tau i u))) q at hq
    have hab := congrFun (representatives_difference S n sigma tau i u) q
    change (first S n sigma i) q+(second S n sigma tau i u) q=u.word q at hab
    rw [hab] at hq
    change (((indexedDecoderData S (n+2)).selectedMap (Edge n i)).map1
      (BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) h u.center
        (first S n sigma i) (second S n sigma tau i u))) q=
      u.word q+(actualOutput S n sigma i).correction q+(actualOutput S n tau i).correction q+
        (BDL26RZMap1CoordinateBridge.tannerCoboundary0 (state S (i.val+3)).presentation
          (BDL26RXPhysicalStarTransport.Phi S (n+2) (Edge n i) h u.center
            (first S n sigma i) (second S n sigma tau i u))) q
    exact hq

/-- The RZ potential is chosen from the complete eleven-clause theorem;
the lower word remains literally its fixed parity projection. -/
def rzPotential (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) : (Data S n).family.Cochain0 i.succ :=
  Classical.choose (BDL26RZPhysicalXStarTransport.two_run S (n+2) (Edge n i) h
    (by change 3 ≤ i.val+2; simp only [Edge,LevelTwoHistory.physicalStep_val] at h; omega)
    u.center (first S n sigma i) (second S n sigma tau i u)
    (rz_localized S n sigma tau i h u))

theorem rzPotential_full (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    BDL26RZFiniteBlockTransport.Pullback S (n+2) (Edge n i) h
      (BDL26RZPhysicalXStarTransport.Q0 S (n+2) (Edge n i) h u.center)
      (BDL26RZPhysicalXStarTransport.Z0 S (n+2) (Edge n i) h u.center)
      (first S n sigma i) (second S n sigma tau i u) (rzPotential S n sigma tau i h u) :=
  (Classical.choose_spec (BDL26RZPhysicalXStarTransport.two_run S (n+2) (Edge n i) h
    (by change 3 ≤ i.val+2; simp only [Edge,LevelTwoHistory.physicalStep_val] at h; omega)
    u.center (first S n sigma i) (second S n sigma tau i u)
    (rz_localized S n sigma tau i h u))).1

def rzResult (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) : StepResult S n sigma tau i u := by
  have hp := rzPotential_full S n sigma tau i h u
  have above : 3 ≤ (Edge n i).val := by
    change 3 ≤ i.val+2
    simp only [Edge,LevelTwoHistory.physicalStep_val] at h
    omega
  refine {
    lower := {
      word := BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) h
        (first S n sigma i) (second S n sigma tau i u)
      center := BDL26RZPhysicalXStarTransport.downX S (n+2) (Edge n i) h u.center
      supported := BDL26RZPhysicalXStarTransport.lower_physical_supported S (n+2) (Edge n i) h
        above u.center _ _ (rz_localized S n sigma tau i h u)
      syndrome := ?_ }
    potential := rzPotential S n sigma tau i h u
    equation := ?_ }
  · have hs := hp.2.1
    rw [rz_first,rz_second,originalOutput_coarse S n sigma i,
      originalOutput_coarse S n tau i,indexedFamily_coboundary1] at hs
    rw [LevelTwoHistory.suffix_coboundary1]
    change (indexedFamily S (n+2)).coboundary1
      (LevelTwoHistory.physicalLevel i.castSucc)
      (BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) h
        (first S n sigma i) (second S n sigma tau i u))=_
    rw [indexedFamily_coboundary1]
    funext z
    have hz := congrFun hs z
    change (BDL26RZMap1CoordinateBridge.tannerCoboundary1 (state S (i.val+2)).presentation
      (BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) h
        (first S n sigma i) (second S n sigma tau i u))) z=
      (actualInputs S n sigma i.castSucc).val z+(actualInputs S n tau i.castSucc).val z at hz ⊢
    exact hz
  · rw [LevelTwoHistory.suffix_selected_map1,LevelTwoHistory.suffix_coboundary0]
    change ((indexedDecoderData S (n+2)).selectedMap (Edge n i)).map1
      (BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) h
        (first S n sigma i) (second S n sigma tau i u))=
      u.word+(actualOutput S n sigma i).correction+(actualOutput S n tau i).correction+
        (indexedFamily S (n+2)).coboundary0 (LevelTwoHistory.physicalLevel i.succ)
          (rzPotential S n sigma tau i h u)
    rw [indexedFamily_coboundary0]
    have he := hp.1
    rw [BDL26RZErrorPullback.updated,rz_first,rz_second,originalOutput_correction S n sigma i,
      originalOutput_correction S n tau i,indexedFamily_coboundary0] at he
    funext q
    have hq := congrFun he q
    change (((indexedDecoderData S (n+2)).selectedMap (Edge n i)).map1
      (BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) h
        (first S n sigma i) (second S n sigma tau i u))) q=
      ((first S n sigma i) q+(second S n sigma tau i u) q)+
        (actualOutput S n sigma i).correction q+(actualOutput S n tau i).correction q+
        (BDL26RZMap1CoordinateBridge.tannerCoboundary0 (state S (i.val+3)).presentation (rzPotential S n sigma tau i h u)) q at hq
    have hab := congrFun (representatives_difference S n sigma tau i u) q
    change (first S n sigma i) q+(second S n sigma tau i u) q=u.word q at hab
    rw [hab] at hq
    change (((indexedDecoderData S (n+2)).selectedMap (Edge n i)).map1
      (BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) h
        (first S n sigma i) (second S n sigma tau i u))) q=
      u.word q+(actualOutput S n sigma i).correction q+(actualOutput S n tau i).correction q+
        (BDL26RZMap1CoordinateBridge.tannerCoboundary0 (state S (i.val+3)).presentation (rzPotential S n sigma tau i h u)) q
    exact hq

def step (i : StepIndex n) (u : LocalizedWord S n sigma tau i.succ) : StepResult S n sigma tau i u :=
  if h : (Edge n i).val%2=0 then rxResult S n sigma tau i h u
  else rzResult S n sigma tau i h u

theorem step_rx (i : StepIndex n) (h : (Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) : step S n sigma tau i u=rxResult S n sigma tau i h u := dif_pos h

theorem step_rz (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) : step S n sigma tau i u=rzResult S n sigma tau i h u := dif_neg h

/-- A descending traversal at FIXED total depth and fixed original histories. -/
def down (b : Nat) (hb : b ≤ n)
    (u : LocalizedWord S n sigma tau ⟨b,Nat.lt_succ_of_le hb⟩)
    (a : LevelIndex n) (ha : a.val ≤ b) : LocalizedWord S n sigma tau a := by
  cases b with
  | zero =>
      have he : (⟨0,Nat.lt_succ_of_le hb⟩ : LevelIndex n)=a := Fin.ext (by change 0 = a.val; omega)
      exact he ▸ u
  | succ b =>
      if h : a.val=b+1 then
        exact (show (⟨b+1,Nat.lt_succ_of_le hb⟩ : LevelIndex n)=a from Fin.ext h.symm) ▸ u
      else
        exact down b (by omega) (step S n sigma tau ⟨b,by omega⟩ u).lower a (by omega)
termination_by b

theorem down_self (b : Nat) (hb : b ≤ n)
    (u : LocalizedWord S n sigma tau ⟨b,Nat.lt_succ_of_le hb⟩) :
    down S n sigma tau b hb u ⟨b,Nat.lt_succ_of_le hb⟩ (Nat.le_refl _)=u := by
  cases b with
  | zero => rw [down]; rfl
  | succ b => rw [down]; exact dif_pos rfl

theorem down_succ (b : Nat) (hb : b+1 ≤ n)
    (u : LocalizedWord S n sigma tau ⟨b+1,Nat.lt_succ_of_le hb⟩)
    (a : LevelIndex n) (ha : a.val ≤ b) :
    down S n sigma tau (b+1) hb u a (by omega)=
      down S n sigma tau b (by omega) (step S n sigma tau ⟨b,by omega⟩ u).lower a ha := by
  rw [down]
  exact dif_neg (by omega)

theorem down_step (b : Nat) (hb : b ≤ n)
    (u : LocalizedWord S n sigma tau ⟨b,Nat.lt_succ_of_le hb⟩)
    (i : StepIndex n) (hi : i.val < b) :
    down S n sigma tau b hb u i.castSucc (by change i.val ≤ b; omega)=
      (step S n sigma tau i (down S n sigma tau b hb u i.succ (by change i.val+1 ≤ b; omega))).lower := by
  induction b generalizing i with
  | zero => omega
  | succ b ih =>
      by_cases he : i.val=b
      · have hb_lt : b < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hb
        let j : StepIndex n := ⟨b,hb_lt⟩
        have hei : i=j := Fin.ext he
        subst i
        have hlow : b ≤ n := Nat.le_trans (Nat.le_succ b) hb
        have hu : down S n sigma tau (b+1) hb u j.succ
            (by change b+1 ≤ b+1; exact Nat.le_refl _)=u := by
          change down S n sigma tau (b+1) hb u
            ⟨b+1,Nat.lt_succ_of_le hb⟩ (Nat.le_refl _)=u
          exact down_self S n sigma tau (b+1) hb u
        rw [hu]
        rw [down_succ S n sigma tau b hb u j.castSucc
          (by change b ≤ b; exact Nat.le_refl _)]
        change down S n sigma tau b hlow (step S n sigma tau j u).lower
          ⟨b,Nat.lt_succ_of_le hlow⟩ (Nat.le_refl _)=(step S n sigma tau j u).lower
        exact down_self S n sigma tau b hlow (step S n sigma tau j u).lower
      · have hil : i.val+1 ≤ b := by omega
        rw [down_succ S n sigma tau b hb u i.castSucc (by change i.val ≤ b; omega),
          down_succ S n sigma tau b hb u i.succ hil]
        exact ih (by omega) _ i (by omega)

variable (top : LocalizedWord S n sigma tau (TopIndex n))

/-- Full fixed-depth descent, initialized by the supplied top state. -/
def path (a : LevelIndex n) : LocalizedWord S n sigma tau a :=
  down S n sigma tau n (Nat.le_refl _) top a (Nat.le_of_lt_succ a.isLt)

theorem path_top : path S n sigma tau top (TopIndex n)=top :=
  down_self S n sigma tau n (Nat.le_refl _) top

theorem path_step (i : StepIndex n) :
    path S n sigma tau top i.castSucc=
      (step S n sigma tau i (path S n sigma tau top i.succ)).lower :=
  down_step S n sigma tau n (Nat.le_refl _) top i i.isLt

def edgePotential (i : StepIndex n) : (Data S n).family.Cochain0 i.succ :=
  (step S n sigma tau i (path S n sigma tau top i.succ)).potential

theorem path_local_equation (i : StepIndex n) :
    ((Data S n).selectedMap i).map1 (path S n sigma tau top i.castSucc).word=
      (path S n sigma tau top i.succ).word+
        (actualOutput S n sigma i).correction+(actualOutput S n tau i).correction+
        (Data S n).family.coboundary0 i.succ (edgePotential S n sigma tau top i) := by
  rw [path_step]
  exact (step S n sigma tau i (path S n sigma tau top i.succ)).equation

theorem path_syndrome (a : LevelIndex n) :
    (Data S n).family.coboundary1 a (path S n sigma tau top a).word=
      (actualInputs S n sigma a).val+(actualInputs S n tau a).val :=
  (path S n sigma tau top a).syndrome

theorem path_localized (a : LevelIndex n) :
    hammingSupport (path S n sigma tau top a).word ⊆
      star S n a (path S n sigma tau top a).center :=
  (path S n sigma tau top a).supported

/-- These are bounds on the constructed LOWER word, never on full corrections. -/
theorem path_lower_weight (a : LevelIndex n) (_below : a.val<n) :
    HammingWeight (path S n sigma tau top a).word ≤
        (star S n a (path S n sigma tau top a).center).card ∧
      (star S n a (path S n sigma tau top a).center).card ≤ 7 := by
  rw [HammingWeight_eq_card_hammingSupport]
  exact ⟨Finset.card_le_card (path_localized S n sigma tau top a),star_card S n a _⟩

/-- One full lifted term, with eligibility determined only by original levels. -/
def potentialTerm (a b : LevelIndex n) (i : StepIndex n) : (Data S n).family.Cochain0 b :=
  if h : a.val< (i.succ).val ∧ (i.succ).val≤b.val then
    intervalMap0 (Data S n) i.succ b h.2 (edgePotential S n sigma tau top i)
  else 0

/-- The literal finite sum of all entire transported degree-zero potentials. -/
def intervalPotential (a b : LevelIndex n) : (Data S n).family.Cochain0 b :=
  ∑ i : StepIndex n, potentialTerm S n sigma tau top a b i

/-- Explicit full-sum interface, including every original interior level. -/
theorem intervalPotential_sum (a b : LevelIndex n) :
    intervalPotential S n sigma tau top a b=
      ∑ i : StepIndex n, (if h : a.val< (i.succ).val ∧ (i.succ).val≤b.val then
        intervalMap0 (Data S n) i.succ b h.2 (edgePotential S n sigma tau top i) else 0) := rfl

theorem intervalPotential_self (a : LevelIndex n) : intervalPotential S n sigma tau top a a=0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact dif_neg (by omega)

private theorem potentialTerm_split (a b c : LevelIndex n)
    (hab : a.val≤b.val) (hbc : b.val≤c.val) (i : StepIndex n) :
    potentialTerm S n sigma tau top a c i=
      potentialTerm S n sigma tau top b c i+
        intervalMap0 (Data S n) b c hbc (potentialTerm S n sigma tau top a b i) := by
  by_cases hib : (i.succ).val≤b.val
  · by_cases hai : a.val< (i.succ).val
    · have hac : a.val< (i.succ).val ∧ (i.succ).val≤c.val := ⟨hai,hib.trans hbc⟩
      have hno : ¬(b.val< (i.succ).val ∧ (i.succ).val≤c.val) := by omega
      simp only [potentialTerm,dif_pos hac,dif_neg hno,dif_pos (And.intro hai hib),zero_add]
      exact congrArg (fun f => f (edgePotential S n sigma tau top i))
        (intervalMap0_comp (Data S n) i.succ b c hib hbc)
    · have hnoa : ¬(a.val< (i.succ).val ∧ (i.succ).val≤c.val) := by omega
      have hnob : ¬(b.val< (i.succ).val ∧ (i.succ).val≤c.val) := by omega
      have hnol : ¬(a.val< (i.succ).val ∧ (i.succ).val≤b.val) := by omega
      simp only [potentialTerm,dif_neg hnoa,dif_neg hnob,dif_neg hnol,map_zero,add_zero]
  · by_cases hic : (i.succ).val≤c.val
    · have hai : a.val< (i.succ).val := by omega
      have hbi : b.val< (i.succ).val := by omega
      have hnol : ¬(a.val< (i.succ).val ∧ (i.succ).val≤b.val) := by omega
      simp only [potentialTerm,dif_pos (And.intro hai hic),dif_pos (And.intro hbi hic),
        dif_neg hnol,map_zero,add_zero]
    · have hnoa : ¬(a.val< (i.succ).val ∧ (i.succ).val≤c.val) := by omega
      have hnob : ¬(b.val< (i.succ).val ∧ (i.succ).val≤c.val) := by omega
      have hnol : ¬(a.val< (i.succ).val ∧ (i.succ).val≤b.val) := by omega
      simp only [potentialTerm,dif_neg hnoa,dif_neg hnob,dif_neg hnol,map_zero,add_zero]

/-- Exact concatenation, as full words rather than boundary equivalence. -/
theorem intervalPotential_comp (a b c : LevelIndex n)
    (hab : a.val≤b.val) (hbc : b.val≤c.val) :
    intervalPotential S n sigma tau top a c=
      intervalPotential S n sigma tau top b c+
        intervalMap0 (Data S n) b c hbc (intervalPotential S n sigma tau top a b) := by
  simp only [intervalPotential,map_sum,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => potentialTerm_split S n sigma tau top a b c hab hbc i)

theorem intervalPotential_adjacent (i : StepIndex n) :
    intervalPotential S n sigma tau top i.castSucc i.succ=edgePotential S n sigma tau top i := by
  unfold intervalPotential
  rw [Finset.sum_eq_single i]
  · simp only [potentialTerm,dif_pos (by simp : (i.castSucc).val< (i.succ).val ∧ (i.succ).val≤ (i.succ).val),
      intervalMap0_self,LinearMap.id_apply]
  · intro j _ hji
    apply dif_neg
    intro h
    apply hji
    exact Fin.ext (by simp only [Fin.val_succ,Fin.val_castSucc] at h; omega)
  · simp

theorem intervalPotential_succ (a : LevelIndex n) (i : StepIndex n) (hai : a.val≤ i.val) :
    intervalPotential S n sigma tau top a i.succ=
      edgePotential S n sigma tau top i+
        ((Data S n).selectedMap i).map0 (intervalPotential S n sigma tau top a i.castSucc) := by
  rw [intervalPotential_comp S n sigma tau top a i.castSucc i.succ hai (by simp),
    intervalPotential_adjacent,intervalMap0_adjacent]

/-- The full same-history equation on EVERY finite original interval. -/
theorem interval_equation_nat (b : Nat) (hb : b≤n) (a : LevelIndex n) (ha : a.val≤b) :
    intervalMap1 (Data S n) a ⟨b,Nat.lt_succ_of_le hb⟩ ha (path S n sigma tau top a).word=
      (path S n sigma tau top ⟨b,Nat.lt_succ_of_le hb⟩).word+
        correctionIntervalSum S n sigma a ⟨b,Nat.lt_succ_of_le hb⟩+
        correctionIntervalSum S n tau a ⟨b,Nat.lt_succ_of_le hb⟩+
        (Data S n).family.coboundary0 ⟨b,Nat.lt_succ_of_le hb⟩
          (intervalPotential S n sigma tau top a ⟨b,Nat.lt_succ_of_le hb⟩) := by
  induction b generalizing a with
  | zero =>
      have he : a=⟨0,Nat.lt_succ_of_le hb⟩ := Fin.ext (by change a.val = 0; omega)
      subst a
      simp only [intervalMap1_self,LinearMap.id_apply,correctionIntervalSum_self,
        intervalPotential_self,map_zero,add_zero]
  | succ b ih =>
      by_cases he : a.val=b+1
      · have he' : a=⟨b+1,Nat.lt_succ_of_le hb⟩ := Fin.ext he
        subst a
        simp only [intervalMap1_self,LinearMap.id_apply,correctionIntervalSum_self,
          intervalPotential_self,map_zero,add_zero]
      · have hal : a.val≤b := by omega
        let i : StepIndex n := ⟨b,by omega⟩
        change intervalMap1 (Data S n) a i.succ ha (path S n sigma tau top a).word=
          (path S n sigma tau top i.succ).word+
            correctionIntervalSum S n sigma a i.succ+correctionIntervalSum S n tau a i.succ+
            (Data S n).family.coboundary0 i.succ
              (intervalPotential S n sigma tau top a i.succ)
        rw [intervalMap1_succ (Data S n) a i hal]
        change ((Data S n).selectedMap i).map1
          (intervalMap1 (Data S n) a i.castSucc hal (path S n sigma tau top a).word)=_
        have hi := ih (by omega) a hal
        change intervalMap1 (Data S n) a i.castSucc hal (path S n sigma tau top a).word=
          (path S n sigma tau top i.castSucc).word+
            correctionIntervalSum S n sigma a i.castSucc+correctionIntervalSum S n tau a i.castSucc+
            (Data S n).family.coboundary0 i.castSucc
              (intervalPotential S n sigma tau top a i.castSucc) at hi
        rw [hi]
        simp only [map_add]
        rw [path_local_equation]
        have hc := LinearMap.congr_fun ((Data S n).selectedMap i).commutes_coboundary0
          (intervalPotential S n sigma tau top a i.castSucc)
        simp only [LinearMap.comp_apply] at hc
        rw [← hc,correctionIntervalSum_succ S n sigma a i hal,
          correctionIntervalSum_succ S n tau a i hal,intervalPotential_succ S n sigma tau top a i hal,map_add]
        abel

theorem interval_equation (a b : LevelIndex n) (hab : a.val≤b.val) :
    intervalMap1 (Data S n) a b hab (path S n sigma tau top a).word=
      (path S n sigma tau top b).word+correctionIntervalSum S n sigma a b+
        correctionIntervalSum S n tau a b+(Data S n).family.coboundary0 b
          (intervalPotential S n sigma tau top a b) :=
  interval_equation_nat S n sigma tau top b.val (Nat.le_of_lt_succ b.isLt) a hab

theorem potential_boundary_cocycle (a b : LevelIndex n) :
    (Data S n).family.coboundary1 b
      ((Data S n).family.coboundary0 b (intervalPotential S n sigma tau top a b))=0 :=
  LinearMap.congr_fun ((Data S n).family.coboundary1_comp_coboundary0 b) _

/-- Every adjacent pair retains exactly p+FZ.map0(q), with no gauge substitution. -/
theorem adjacent_potential_pair (i j : StepIndex n) (hij : j.succ=i.castSucc) :
    intervalPotential S n sigma tau top j.castSucc i.succ=
      edgePotential S n sigma tau top i+
        ((Data S n).selectedMap i).map0 (hij ▸ edgePotential S n sigma tau top j) := by
  have hai : (j.castSucc).val≤ i.val := by have h:=congrArg Fin.val hij; simp only [Fin.val_succ,Fin.val_castSucc] at h ⊢; omega
  rw [intervalPotential_succ S n sigma tau top j.castSucc i hai]
  have he : intervalPotential S n sigma tau top j.castSucc i.castSucc=
      (hij ▸ edgePotential S n sigma tau top j) := by
    have transport : ∀ (b : LevelIndex n) (hb : j.succ=b),
        intervalPotential S n sigma tau top j.castSucc b=
          (hb ▸ edgePotential S n sigma tau top j) := by
      intro b hb
      cases hb
      exact intervalPotential_adjacent S n sigma tau top j
    exact transport i.castSucc hij
  rw [he]

/-- The full composed equation on any adjacent original window. In the
RZ/RX case the outer selected map is FZ and the potential is literally p+FZ(q). -/
theorem interior_pair_equation (i j : StepIndex n) (hij : j.succ=i.castSucc) :
    intervalMap1 (Data S n) j.castSucc i.succ
      (by have h:=congrArg Fin.val hij; simp only [Fin.val_succ,Fin.val_castSucc] at h ⊢; omega)
      (path S n sigma tau top j.castSucc).word=
      (path S n sigma tau top i.succ).word+
        correctionIntervalSum S n sigma j.castSucc i.succ+
        correctionIntervalSum S n tau j.castSucc i.succ+
        (Data S n).family.coboundary0 i.succ
          (edgePotential S n sigma tau top i+
            ((Data S n).selectedMap i).map0 (hij ▸ edgePotential S n sigma tau top j)) := by
  have hle : (j.castSucc).val≤ (i.succ).val := by
    have h:=congrArg Fin.val hij
    simp only [Fin.val_succ,Fin.val_castSucc] at h ⊢
    omega
  have he := interval_equation S n sigma tau top j.castSucc i.succ hle
  rw [adjacent_potential_pair S n sigma tau top i j hij] at he
  exact he

/-- Full original assembled prefixes, including their physical-C2 base words. -/
theorem history_equation :
    top.word+historyLiftedCorrection (Data S n) (actualHistory S n sigma)+
        historyLiftedCorrection (Data S n) (actualHistory S n tau)=
      intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
        ((path S n sigma tau top 0).word+(actualBase S n).decode (actualInputs S n sigma 0)+
          (actualBase S n).decode (actualInputs S n tau 0))+
      (Data S n).family.coboundary0 (TopIndex n)
        (intervalPotential S n sigma tau top 0 (TopIndex n)) := by
  have hi := interval_equation S n sigma tau top 0 (TopIndex n) (Nat.zero_le _)
  rw [path_top] at hi
  have hs := assembledPrefix_split S n sigma 0 (TopIndex n) (Nat.zero_le _)
  have ht := assembledPrefix_split S n tau 0 (TopIndex n) (Nat.zero_le _)
  rw [assembledPrefix_top,assembledPrefix_zero] at hs ht
  have hm : top.word+correctionIntervalSum S n sigma 0 (TopIndex n)+
      correctionIntervalSum S n tau 0 (TopIndex n)=
      intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _) (path S n sigma tau top 0).word+
        (Data S n).family.coboundary0 (TopIndex n)
          (intervalPotential S n sigma tau top 0 (TopIndex n)) :=
    BDL26HistoryErrorTelescoping.word_toggle _ _ _ hi
  rw [hs,ht,map_add,map_add]
  calc
    _ = (top.word+correctionIntervalSum S n sigma 0 (TopIndex n)+
        correctionIntervalSum S n tau 0 (TopIndex n))+
      intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
        ((actualBase S n).decode (actualInputs S n sigma 0))+
      intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
        ((actualBase S n).decode (actualInputs S n tau 0)) := by ac_rfl
    _ = _ := by rw [hm]; ac_rfl

theorem base_residual_cocycle :
    (Data S n).family.coboundary1 0
      ((path S n sigma tau top 0).word+(actualBase S n).decode (actualInputs S n sigma 0)+
        (actualBase S n).decode (actualInputs S n tau 0))=0 := by
  rw [map_add,map_add,path_syndrome,(actualBase S n).rightInverse,(actualBase S n).rightInverse]
  have hs := twice (actualInputs S n sigma 0).val
  have ht := twice (actualInputs S n tau 0).val
  change ((actualInputs S n sigma 0).val+(actualInputs S n tau 0).val)+
    (actualInputs S n sigma 0).val+(actualInputs S n tau 0).val=0
  calc
    _ = ((actualInputs S n sigma 0).val+(actualInputs S n sigma 0).val)+
        ((actualInputs S n tau 0).val+(actualInputs S n tau 0).val) := by abel
    _ = 0 := by rw [hs,ht,add_zero]


/-- Both complete represented RX records are the original snapshots. -/
theorem represented_RX_records (i : StepIndex n) (h : (Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    BDL26RXErrorPullback.run S (n+2) (Edge n i) h (first S n sigma i)=
        BDL26CanonicalHistoryMarks.outputAt S n sigma i ∧
      BDL26RXErrorPullback.run S (n+2) (Edge n i) h (second S n sigma tau i u)=
        BDL26CanonicalHistoryMarks.outputAt S n tau i :=
  ⟨(rx_first S n sigma i h).trans (originalOutput_snapshot S n sigma i),
    (rx_second S n sigma tau i h u).trans (originalOutput_snapshot S n tau i)⟩

/-- Both complete represented RZ records are the original snapshots. -/
theorem represented_RZ_records (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    BDL26RZErrorPullback.run S (n+2) (Edge n i) h (first S n sigma i)=
        BDL26CanonicalHistoryMarks.outputAt S n sigma i ∧
      BDL26RZErrorPullback.run S (n+2) (Edge n i) h (second S n sigma tau i u)=
        BDL26CanonicalHistoryMarks.outputAt S n tau i :=
  ⟨(rz_first S n sigma i h).trans (originalOutput_snapshot S n sigma i),
    (rz_second S n sigma tau i h u).trans (originalOutput_snapshot S n tau i)⟩

/-- Interior RZ steps retain the entire literal eleven-clause pullback and
BOTH old-X zero copies for the SAME whole potential used by the recursion. -/
theorem step_RZ_full (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    BDL26RZFiniteBlockTransport.Pullback S (n+2) (Edge n i) h
      (BDL26RZPhysicalXStarTransport.Q0 S (n+2) (Edge n i) h u.center)
      (BDL26RZPhysicalXStarTransport.Z0 S (n+2) (Edge n i) h u.center)
      (first S n sigma i) (second S n sigma tau i u) (step S n sigma tau i u).potential ∧
    (step S n sigma tau i u).lower.word=
      BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) h
        (first S n sigma i) (second S n sigma tau i u) ∧
    (step S n sigma tau i u).lower.center=
      BDL26RZPhysicalXStarTransport.downX S (n+2) (Edge n i) h u.center ∧
    (∀ x : (state S (Edge n i).val).presentation.X, ∀ c : BDL26FiniteTannerSquare.Two,
      BDL26RZFiniteBlockTransport.read0 S (n+2) (Edge n i) h
        (step S n sigma tau i u).potential (.inr (x,c))=0) := by
  rw [step_rz S n sigma tau i h u]
  have hp := rzPotential_full S n sigma tau i h u
  exact ⟨hp,rfl,rfl,BDL26RZPhysicalXStarTransport.oldX_zero S (n+2) (Edge n i) h
    u.center _ _ _ hp⟩

/-- Sharp RZ input-block bound: the constructor cases compute 0,1,or an
old physical incidence star, never a bound on the full corrected upper word. -/
theorem step_RZ_weight (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    HammingWeight (step S n sigma tau i u).lower.word ≤
        (BDL26RZPhysicalXStarTransport.Q0 S (n+2) (Edge n i) h u.center).card ∧
      (BDL26RZPhysicalXStarTransport.Q0 S (n+2) (Edge n i) h u.center).card≤7 := by
  rw [step_rz S n sigma tau i h u]
  exact BDL26RZPhysicalXStarTransport.lower_weight S (n+2) (Edge n i) h
    (by change 3≤ i.val+2; simp only [Edge,LevelTwoHistory.physicalStep_val] at h; omega)
    u.center _ _ (rz_localized S n sigma tau i h u)

/-- Exact raw parent table, including none for both positive-dimensional
constructors. A computed star centre is not relabelled as a graph parent. -/
theorem RZ_constructor_parent (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (v : BDL26RZLocalReplacement.RZX (state S (Edge n i).val).presentation S) :
    parent S ((Edge n i).val+1)
      (Vertex.x (BDL26RZPhysicalXStarTransport.upperXChart S (n+2) (Edge n i) h v))=
      BDL26RZPhysicalXStarTransport.rawParent (state S (Edge n i).val).presentation S v :=
  BDL26RZPhysicalXStarTransport.parent_chart S (n+2) (Edge n i) h v

/-- All three actual constructors retain the exact 0/1/incidence-card table. -/
theorem RZ_constructor_card (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (v : BDL26RZLocalReplacement.RZX (state S (Edge n i).val).presentation S) :
    (BDL26RZPhysicalXStarTransport.Q0 S (n+2) (Edge n i) h
      (BDL26RZPhysicalXStarTransport.upperXChart S (n+2) (Edge n i) h v)).card=
      match v with
      | .inl (.inl _) => 0
      | .inl (.inr _) => 1
      | .inr (x,_) => (BDL26RXPhysicalStarTransport.physicalXStar
          (state S (Edge n i).val).presentation x).card := by
  simp only [BDL26RZPhysicalXStarTransport.Q0,
    BDL26RZPhysicalXStarTransport.coord0_chart]
  rcases v with (⟨z,f⟩ | ⟨q,e⟩) | ⟨x,c⟩ <;>
    simp [BDL26RZPhysicalXStarTransport.rawQ0]

/-- RX interior windows retain the actual some-parent and fixed normalized
root and full potential; the seven-clause theorem remains directly usable. -/
theorem step_RX_fixed (i : StepIndex n) (h : (Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    (step S n sigma tau i u).lower.word=
      BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) h u.center
        (first S n sigma i) (second S n sigma tau i u) ∧
    (step S n sigma tau i u).potential=
      BDL26RXPhysicalStarTransport.Phi S (n+2) (Edge n i) h u.center
        (first S n sigma i) (second S n sigma tau i u) ∧
    parent S ((Edge n i).val+1) (Vertex.x u.center)=
      some (Vertex.x (step S n sigma tau i u).lower.center) := by
  rw [step_rx S n sigma tau i h u]
  exact ⟨rfl,rfl,BDL26RXPhysicalStarTransport.parent_computed S (n+2) (Edge n i) h u.center⟩

/-- The complete seven-clause RX theorem at any interior original window. -/
theorem step_RX_full (i : StepIndex n) (h : (Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    parent S ((Edge n i).val+1) (Vertex.x u.center)=some (Vertex.x
      (BDL26RXPhysicalStarTransport.parentX S (n+2) (Edge n i) h u.center)) ∧
    ((Data S n).selectedMap i).map1 (step S n sigma tau i u).lower.word=
      u.word+(show (Data S n).family.Cochain1 i.succ from (originalOutput S n sigma i).correction)+
        (show (Data S n).family.Cochain1 i.succ from (originalOutput S n tau i).correction)+
        (Data S n).family.coboundary0 i.succ (step S n sigma tau i u).potential ∧
    (Data S n).family.coboundary1 i.castSucc (step S n sigma tau i u).lower.word=
      (originalOutput S n sigma i).coarse.val+(originalOutput S n tau i).coarse.val ∧
    hammingSupport ((originalOutput S n sigma i).correction+(originalOutput S n tau i).correction) ⊆
      BDL26RXXStarTransport.star1 S (n+2) (Edge n i) h
        (BDL26RXPhysicalStarTransport.parentX S (n+2) (Edge n i) h u.center) ∧
    hammingSupport (step S n sigma tau i u).potential ⊆
      BDL26RXXStarTransport.degreeZeroBlock S (n+2) (Edge n i) h
        (BDL26RXPhysicalStarTransport.parentX S (n+2) (Edge n i) h u.center) ∧
    hammingSupport (step S n sigma tau i u).lower.word ⊆ star S n i.castSucc
      (step S n sigma tau i u).lower.center ∧
    HammingWeight (step S n sigma tau i u).lower.word≤7 := by
  have hr := BDL26RXPhysicalStarTransport.two_run S (n+2) (Edge n i) h u.center
    (first S n sigma i) (second S n sigma tau i u) (rx_localized S n sigma tau i h u)
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact hr.1
  · simpa only [originalOutput_correction] using (step S n sigma tau i u).equation
  · rw [originalOutput_coarse,originalOutput_coarse]
    exact (step S n sigma tau i u).lower.syndrome
  · simpa only [rx_first,rx_second] using hr.2.2.2.1
  · rw [step_rx S n sigma tau i h u]
    exact hr.2.2.2.2.1
  · exact (step S n sigma tau i u).lower.supported
  · rw [step_rx S n sigma tau i h u]
    exact hr.2.2.2.2.2.2

section PhysicalEndpoint
variable (e : (Data S n).family.Cochain1 (TopIndex n))
variable (x : (state S (n+2)).presentation.X) (he : hammingSupport e ⊆ star S n (TopIndex n) x)

/-- Initial correlation follows from the actual physical perturbation, not
from a caller-supplied lower representative or equality of outputs. -/
def initial : LocalizedWord S n sigma (perturbTop S n sigma e) (TopIndex n) where
  word := e
  center := x
  supported := he
  syndrome := by
    rw [actualInputs_top,actualInputs_top]
    exact (perturbTop_difference S n sigma e).symm

def actualDescent (a : LevelIndex n) : LocalizedWord S n sigma (perturbTop S n sigma e) a :=
  path S n sigma (perturbTop S n sigma e) (initial S n sigma e x he) a

def actualPotential (a b : LevelIndex n) : (Data S n).family.Cochain0 b :=
  intervalPotential S n sigma (perturbTop S n sigma e) (initial S n sigma e x he) a b

theorem actualDescent_top : (actualDescent S n sigma e x he (TopIndex n)).word=e :=
  congrArg LocalizedWord.word (path_top S n sigma (perturbTop S n sigma e) (initial S n sigma e x he))

theorem actualDescent_supported (a : LevelIndex n) :
    hammingSupport (actualDescent S n sigma e x he a).word ⊆
      star S n a (actualDescent S n sigma e x he a).center :=
  path_localized S n sigma (perturbTop S n sigma e) (initial S n sigma e x he) a

theorem actualDescent_syndrome (a : LevelIndex n) :
    (Data S n).family.coboundary1 a (actualDescent S n sigma e x he a).word=
      (actualInputs S n sigma a).val+(actualInputs S n (perturbTop S n sigma e) a).val :=
  path_syndrome S n sigma (perturbTop S n sigma e) (initial S n sigma e x he) a

theorem actualDescent_weight (a : LevelIndex n) (ha : a.val<n) :
    HammingWeight (actualDescent S n sigma e x he a).word≤
        (star S n a (actualDescent S n sigma e x he a).center).card ∧
      (star S n a (actualDescent S n sigma e x he a).center).card≤7 :=
  path_lower_weight S n sigma (perturbTop S n sigma e) (initial S n sigma e x he) a ha

theorem actual_interval (a b : LevelIndex n) (hab : a.val≤b.val) :
    intervalMap1 (Data S n) a b hab (actualDescent S n sigma e x he a).word=
      (actualDescent S n sigma e x he b).word+correctionIntervalSum S n sigma a b+
        correctionIntervalSum S n (perturbTop S n sigma e) a b+
        (Data S n).family.coboundary0 b (actualPotential S n sigma e x he a b) :=
  interval_equation S n sigma (perturbTop S n sigma e) (initial S n sigma e x he) a b hab

theorem actual_potential_comp (a b c : LevelIndex n) (hab : a.val≤b.val) (hbc : b.val≤c.val) :
    actualPotential S n sigma e x he a c=actualPotential S n sigma e x he b c+
      intervalMap0 (Data S n) b c hbc (actualPotential S n sigma e x he a b) :=
  intervalPotential_comp S n sigma (perturbTop S n sigma e) (initial S n sigma e x he) a b c hab hbc

/-- The actual two histories, both base words, and the literal accumulated P. -/
theorem actual_history :
    e+historyLiftedCorrection (Data S n) (actualHistory S n sigma)+
      historyLiftedCorrection (Data S n) (actualHistory S n (perturbTop S n sigma e))=
      intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
        ((actualDescent S n sigma e x he 0).word+
          (actualBase S n).decode (actualInputs S n sigma 0)+
          (actualBase S n).decode (actualInputs S n (perturbTop S n sigma e) 0))+
      (Data S n).family.coboundary0 (TopIndex n) (actualPotential S n sigma e x he 0 (TopIndex n)) :=
  history_equation S n sigma (perturbTop S n sigma e) (initial S n sigma e x he)

theorem actual_base_cocycle :
    (Data S n).family.coboundary1 0
      ((actualDescent S n sigma e x he 0).word+
        (actualBase S n).decode (actualInputs S n sigma 0)+
        (actualBase S n).decode (actualInputs S n (perturbTop S n sigma e) 0))=0 :=
  base_residual_cocycle S n sigma (perturbTop S n sigma e) (initial S n sigma e x he)

theorem actual_top_cocycle :
    (Data S n).family.coboundary1 (TopIndex n)
      (e+historyLiftedCorrection (Data S n) (actualHistory S n sigma)+
        historyLiftedCorrection (Data S n) (actualHistory S n (perturbTop S n sigma e)))=0 := by
  rw [map_add,map_add]
  have hs : (Data S n).family.coboundary1 (TopIndex n)
      (historyLiftedCorrection (Data S n) (actualHistory S n sigma))=sigma.val :=
    actualHistory_syndrome S n sigma
  have ht : (Data S n).family.coboundary1 (TopIndex n)
      (historyLiftedCorrection (Data S n) (actualHistory S n (perturbTop S n sigma e)))=
        (perturbTop S n sigma e).val := actualHistory_syndrome S n (perturbTop S n sigma e)
  rw [hs,ht]
  change (Data S n).family.coboundary1 (TopIndex n) e+sigma.val+
    (sigma.val+(Data S n).family.coboundary1 (TopIndex n) e)=0
  calc
    _ = ((Data S n).family.coboundary1 (TopIndex n) e+
        (Data S n).family.coboundary1 (TopIndex n) e)+(sigma.val+sigma.val) := by ac_rfl
    _ = 0 := by rw [twice,twice,add_zero]

/-- The empty interval retains both base words and creates no below-C2 step. -/
theorem actual_empty_interval (a : LevelIndex n) :
    actualPotential S n sigma e x he a a=0 ∧
      intervalMap1 (Data S n) a a (Nat.le_refl _)=LinearMap.id :=
  ⟨intervalPotential_self S n sigma (perturbTop S n sigma e) (initial S n sigma e x he) a,
    intervalMap1_self (Data S n) a⟩

end PhysicalEndpoint

/-- Every actual physical qubit has an internally computed incident X centre. -/
def elementaryCenter (S : OddScale) (n : Nat)
    (q : (state S (n+2)).presentation.Q) : (state S (n+2)).presentation.X :=
  ((state S (n+2)).admissible.toTannerSquareAdmissible.xqRoot q).1

theorem elementary_support (S : OddScale) (n : Nat) (q : (state S (n+2)).presentation.Q) :
    hammingSupport (canonicalBasisWord (F := BDL26Field) q) ⊆ star S n (TopIndex n) (elementaryCenter S n q) := by
  intro r hr
  have hrq : r=q := by
    by_contra hn
    have hz : canonicalBasisWord (F := BDL26Field) q r=0 := by simp [canonicalBasisWord,hn]
    exact (Finset.mem_filter.mp hr).2 hz
  subst r
  exact (BDL26RXPhysicalStarTransport.mem_physicalXStar _ _ _).mpr
    ((state S (n+2)).admissible.toTannerSquareAdmissible.xqRoot q).2

/-- No caller incidence or lower-locality certificate enters an elementary flip. -/
theorem elementary_history (S : OddScale) (n : Nat) (sigma : TopInput S n)
    (q : (state S (n+2)).presentation.Q) :
    let e := canonicalBasisWord (F := BDL26Field) q
    let x := elementaryCenter S n q
    let he := elementary_support S n q
    e+historyLiftedCorrection (Data S n) (actualHistory S n sigma)+
      historyLiftedCorrection (Data S n) (actualHistory S n (perturbTop S n sigma e))=
      intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
        ((actualDescent S n sigma e x he 0).word+
          (actualBase S n).decode (actualInputs S n sigma 0)+
          (actualBase S n).decode (actualInputs S n (perturbTop S n sigma e) 0))+
      (Data S n).family.coboundary0 (TopIndex n) (actualPotential S n sigma e x he 0 (TopIndex n)) :=
  actual_history S n sigma (canonicalBasisWord (F := BDL26Field) q) (elementaryCenter S n q) (elementary_support S n q)

/-- Source-even depth2k, k>=1, includes the empty suffix k=1 exactly. -/
theorem source_even_history (S : OddScale) (k : Nat) (hk : 1≤k)
    (sigma : TopInput S (2*(k-1))) (q : (state S (2*(k-1)+2)).presentation.Q) :
    2*(k-1)+2=2*k ∧
    (let n := 2*(k-1)
     let e := canonicalBasisWord (F := BDL26Field) q
     let x := elementaryCenter S n q
     let he := elementary_support S n q
     e+historyLiftedCorrection (Data S n) (actualHistory S n sigma)+
       historyLiftedCorrection (Data S n) (actualHistory S n (perturbTop S n sigma e))=
       intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
         ((actualDescent S n sigma e x he 0).word+
           (actualBase S n).decode (actualInputs S n sigma 0)+
           (actualBase S n).decode (actualInputs S n (perturbTop S n sigma e) 0))+
       (Data S n).family.coboundary0 (TopIndex n) (actualPotential S n sigma e x he 0 (TopIndex n))) :=
  ⟨by omega,elementary_history S (2*(k-1)) sigma q⟩

/-- Physical C2 is literally unchanged; h=e and P=0 at suffix depth zero. -/
theorem depth_two (S : OddScale) (sigma : TopInput S 0)
    (e : (Data S 0).family.Cochain1 (TopIndex 0))
    (x : (state S 2).presentation.X) (he : hammingSupport e⊆star S 0 (TopIndex 0) x) :
    (actualDescent S 0 sigma e x he 0).word=e ∧ actualPotential S 0 sigma e x he 0 0=0 := by
  constructor
  · exact actualDescent_top S 0 sigma e x he
  · exact (actual_empty_interval S 0 sigma e x he 0).1

end QEC.Coding.BDL26LocalizedHistoryErrorDescent
