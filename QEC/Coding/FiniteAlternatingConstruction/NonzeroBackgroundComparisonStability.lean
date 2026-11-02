import QEC.Coding.FiniteAlternatingConstruction.AllDepthBottomComparisonStability

/-!
# All-depth comparison stability under a finite physical background budget

The correction function is precisely the separately named merged comparison;
no original decoder, history, graph, mark, selected map or zero-baseline theorem
is changed. A full top background word g is decomposed internally into its
actual supported coordinates. The correlated histories for consecutive partial
words construct a C2 preimage of the readout difference, with weight at most
7 * HammingWeight g, independently of depth. No linearity of the nonlinear
stored readout is asserted. The full top potential retains the entire original
accumulated history potential. This is internal comparison mathematics, not a
canonical-decoder or public stability/lifetime assertion.
-/
noncomputable section
namespace QEC.Coding.BDL26NonzeroBackgroundComparisonStability

open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual (suffix_delta0 suffix_delta1)
open BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators


abbrev F := BDL26Field
abbrev Data (S : OddScale) (n : Nat) := SuffixData S n
abbrev TopWord (S : OddScale) (n : Nat) := (Data S n).family.Cochain1 (TopIndex n)
abbrev BaseWord (S : OddScale) (n : Nat) := (Data S n).family.Cochain1 0
abbrev TopQ (S : OddScale) (n : Nat) := (state S (n+2)).presentation.Q

/-- One actual coordinate with its original coefficient; no binary normal form is assumed. -/
def coordinateTerm (S : OddScale) (n : Nat) (g : TopWord S n) (q : TopQ S n) : TopWord S n :=
  fun r => if r=q then g q else 0

/-- A finite prefix of the actual full physical background word. -/
def partialWord (S : OddScale) (n : Nat) (g : TopWord S n) (A : Finset (TopQ S n)) : TopWord S n :=
  fun q => if q ∈ A then g q else 0

private theorem partial_empty (S : OddScale) (n : Nat) (g : TopWord S n) :
    partialWord S n g ∅=0 := by
  funext q
  simp [partialWord]

private theorem partial_insert (S : OddScale) (n : Nat) (g : TopWord S n)
    (A : Finset (TopQ S n)) (q : TopQ S n) (hq : q ∉ A) :
    partialWord S n g (insert q A)=partialWord S n g A+coordinateTerm S n g q := by
  funext r
  by_cases hr : r=q
  · subst r
    simp [partialWord,coordinateTerm,hq]
  · simp [partialWord,coordinateTerm,hr]

/-- The complete supported-coordinate decomposition is proved from the word itself. -/
theorem partial_support_eq (S : OddScale) (n : Nat) (g : TopWord S n) :
    partialWord S n g (hammingSupport g)=g := by
  funext q
  by_cases hm : q ∈ hammingSupport g
  · simp only [partialWord,if_pos hm]
  · have hq : g q=0 := by
      by_contra hq
      exact hm (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq⟩)
    simp only [partialWord,if_neg hm,hq]

private theorem coordinate_supported (S : OddScale) (n : Nat) (g : TopWord S n) (q : TopQ S n) :
    hammingSupport (coordinateTerm S n g q) ⊆
      BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) (BDL26LocalizedHistoryErrorDescent.elementaryCenter S n q) := by
  intro r hr
  have hrq : r=q := by
    by_contra hn
    exact (Finset.mem_filter.mp hr).2 (by simp [coordinateTerm,hn])
  subst r
  apply BDL26LocalizedHistoryErrorDescent.elementary_support S n q
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [canonicalBasisWord]⟩

/-- Addition of top words composes actual physical perturbations, not decoder outputs. -/
theorem perturb_add (S : OddScale) (n : Nat) (sigma : TopInput S n) (g e : TopWord S n) :
    perturbTop S n (perturbTop S n sigma g) e=perturbTop S n sigma (g+e) := by
  apply Subtype.ext
  change (sigma.val+((indexedFamily S (n+2)).coboundary1 (TopIndex (n+2))) g)+
      ((indexedFamily S (n+2)).coboundary1 (TopIndex (n+2))) e =
    sigma.val+((indexedFamily S (n+2)).coboundary1 (TopIndex (n+2))) (g+e)
  rw [map_add,add_assoc]

private theorem perturb_zero (S : OddScale) (n : Nat) (sigma : TopInput S n) :
    perturbTop S n sigma (0 : TopWord S n)=sigma := by
  apply Subtype.ext
  change sigma.val+((indexedFamily S (n+2)).coboundary1 (TopIndex (n+2))) 0=sigma.val
  rw [map_zero,add_zero]

private theorem pair_cancel {I : Type} (a b c : Word F I) : (a+b)+(b+c)=a+c := by
  calc
    _ = (a+c)+(b+b) := by abel
    _ = _ := by rw [word_add_self,add_zero]

/-- Finite induction constructs a real C2 representative of each readout difference. -/
private theorem partial_difference_preimage (S : OddScale) (n : Nat) (sigma : TopInput S n)
    (g : TopWord S n) (A : Finset (TopQ S n)) :
    ∃ b : BaseWord S n,
      (Data S n).family.coboundary1 0 b=
        BDL26AllDepthBottomComparisonStability.baseReadout S n sigma+
          BDL26AllDepthBottomComparisonStability.baseReadout S n (perturbTop S n sigma (partialWord S n g A)) ∧
      HammingWeight b ≤ 7*A.card := by
  induction A using Finset.induction_on with
  | empty =>
      refine ⟨0,?_,?_⟩
      · rw [partial_empty,perturb_zero,map_zero]
        exact (word_add_self _).symm
      · rw [HammingWeight_eq_card_hammingSupport]
        simp [hammingSupport]
  | @insert q A hq ih =>
      obtain ⟨b,hb,wb⟩ := ih
      let tau : TopInput S n := perturbTop S n sigma (partialWord S n g A)
      let a : TopWord S n := coordinateTerm S n g q
      let x := BDL26LocalizedHistoryErrorDescent.elementaryCenter S n q
      have ha : hammingSupport a ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x :=
        coordinate_supported S n g q
      let h : BaseWord S n := (BDL26LocalizedHistoryErrorDescent.actualDescent S n tau a x ha 0).word
      have wh : HammingWeight h ≤ 7 := BDL26AllDepthBottomComparisonStability.terminal_weight S n tau a x ha
      have next : perturbTop S n tau a=
          perturbTop S n sigma (partialWord S n g (insert q A)) := by
        dsimp only [tau,a]
        rw [partial_insert S n g A q hq]
        exact perturb_add S n sigma _ _
      have hd : (Data S n).family.coboundary1 0 h=
          BDL26AllDepthBottomComparisonStability.baseReadout S n tau+BDL26AllDepthBottomComparisonStability.baseReadout S n (perturbTop S n tau a) :=
        BDL26LocalizedHistoryErrorDescent.actualDescent_syndrome S n tau a x ha 0
      have hd' : (Data S n).family.coboundary1 0 h=
          BDL26AllDepthBottomComparisonStability.baseReadout S n tau+
            BDL26AllDepthBottomComparisonStability.baseReadout S n (perturbTop S n sigma (partialWord S n g (insert q A))) :=
        hd.trans (congrArg (fun s : TopInput S n =>
          BDL26AllDepthBottomComparisonStability.baseReadout S n tau+BDL26AllDepthBottomComparisonStability.baseReadout S n s) next)
      refine ⟨b+h,?_,?_⟩
      · rw [map_add,hb,hd']
        exact pair_cancel
          (BDL26AllDepthBottomComparisonStability.baseReadout S n sigma)
          (BDL26AllDepthBottomComparisonStability.baseReadout S n tau)
          (BDL26AllDepthBottomComparisonStability.baseReadout S n
            (perturbTop S n sigma (partialWord S n g (insert q A))))
      · have hw := HammingWeight_add_le b h
        rw [Finset.card_insert_of_notMem hq]
        omega

/-- Depth-independent whole-word readout-preimage bound for arbitrary correlated backgrounds. -/
theorem readout_difference_preimage (S : OddScale) (n : Nat) (sigma : TopInput S n)
    (g : TopWord S n) :
    ∃ b : BaseWord S n,
      (Data S n).family.coboundary1 0 b=
        BDL26AllDepthBottomComparisonStability.baseReadout S n sigma+BDL26AllDepthBottomComparisonStability.baseReadout S n (perturbTop S n sigma g) ∧
      HammingWeight b ≤ 7*HammingWeight g := by
  obtain ⟨b,hb,hw⟩ := partial_difference_preimage S n sigma g (hammingSupport g)
  refine ⟨b,?_,?_⟩
  · simpa only [partial_support_eq] using hb
  · simpa only [HammingWeight_eq_card_hammingSupport] using hw

/-- Chosen from the preceding finite construction, never supplied as an input certificate. -/
def differenceWord (S : OddScale) (n : Nat) (sigma : TopInput S n) (g : TopWord S n) : BaseWord S n :=
  Classical.choose (readout_difference_preimage S n sigma g)

theorem differenceWord_syndrome (S : OddScale) (n : Nat) (sigma : TopInput S n) (g : TopWord S n) :
    (Data S n).family.coboundary1 0 (differenceWord S n sigma g)=
      BDL26AllDepthBottomComparisonStability.baseReadout S n sigma+BDL26AllDepthBottomComparisonStability.baseReadout S n (perturbTop S n sigma g) :=
  (Classical.choose_spec (readout_difference_preimage S n sigma g)).1

theorem differenceWord_weight (S : OddScale) (n : Nat) (sigma : TopInput S n) (g : TopWord S n) :
    HammingWeight (differenceWord S n sigma g) ≤ 7*HammingWeight g :=
  (Classical.choose_spec (readout_difference_preimage S n sigma g)).2

/-- The complete C2 readout of the new, possibly nonzero background has a constructed preimage. -/
theorem background_preimage (S : OddScale) (n : Nat) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0) (g : TopWord S n) :
    (Data S n).family.coboundary1 0 (differenceWord S n sigma0 g)=
      BDL26AllDepthBottomComparisonStability.baseReadout S n (perturbTop S n sigma0 g) := by
  have h := differenceWord_syndrome S n sigma0 g
  rw [zero,zero_add] at h
  exact h

/-- Quantitative bottom step with a real preimage budget; no output-weight premise. -/
theorem terminal_boundary_of_preimage (S : OddScale) (n : Nat) (B : Nat)
    (large : 2*B+16 ≤ S.half) (sigma : TopInput S n) (b : BaseWord S n)
    (hb : (Data S n).family.coboundary1 0 b=BDL26AllDepthBottomComparisonStability.baseReadout S n sigma)
    (small : HammingWeight b ≤ B) (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x) :
    ∃ p : (Data S n).family.Cochain0 0,
      (Data S n).family.coboundary0 0 p=
        (BDL26LocalizedHistoryErrorDescent.actualDescent S n sigma e x support 0).word+
          BDL26AllDepthBottomComparisonStability.baseComparison S n sigma+BDL26AllDepthBottomComparisonStability.baseComparison S n (perturbTop S n sigma e) := by
  let h : BaseWord S n := (BDL26LocalizedHistoryErrorDescent.actualDescent S n sigma e x support 0).word
  let bNative : BDL26BottomLocalFirstMinWeightComparison.Error S := fun q => b q
  let hNative : BDL26BottomLocalFirstMinWeightComparison.Error S := fun q => h q
  let first : BDL26BottomLocalFirstMinWeightComparison.Syndrome S := BDL26AllDepthBottomComparisonStability.baseReadout S n sigma
  let second : BDL26BottomLocalFirstMinWeightComparison.Syndrome S := BDL26AllDepthBottomComparisonStability.baseReadout S n (perturbTop S n sigma e)
  have hd : (Data S n).family.coboundary1 0 h=
      BDL26AllDepthBottomComparisonStability.baseReadout S n sigma+BDL26AllDepthBottomComparisonStability.baseReadout S n (perturbTop S n sigma e) :=
    BDL26LocalizedHistoryErrorDescent.actualDescent_syndrome S n sigma e x support 0
  have db : tannerCoboundary1 (BDL26BottomLocalFirstMinWeightComparison.P2 S) bNative=first := by
    funext z
    have hz := congrFun ((LinearMap.congr_fun
      (suffix_delta1 S n (0 : LevelIndex n)) b).symm.trans hb) z
    exact hz
  have dh : tannerCoboundary1 (BDL26BottomLocalFirstMinWeightComparison.P2 S) hNative=first+second := by
    funext z
    have hz := congrFun ((LinearMap.congr_fun
      (suffix_delta1 S n (0 : LevelIndex n)) h).symm.trans hd) z
    exact hz
  have dbh : tannerCoboundary1 (BDL26BottomLocalFirstMinWeightComparison.P2 S) (bNative+hNative)=second := by
    rw [map_add,db,dh]
    rw [← add_assoc,word_add_self,zero_add]
  have wb : HammingWeight bNative ≤ B := small
  have wh : HammingWeight hNative ≤ 7 := BDL26AllDepthBottomComparisonStability.terminal_weight S n sigma e x support
  have wbh : HammingWeight (bNative+hNative) ≤ B+7 :=
    (HammingWeight_add_le bNative hNative).trans (Nat.add_le_add wb wh)
  have radius : 2*(B+7)+2 ≤ S.half := by omega
  obtain ⟨p0,hp0⟩ := BDL26BottomLocalFirstMinWeightComparison.comparison_corrects_radius S (B+7) radius bNative (by omega)
  obtain ⟨p1,hp1⟩ := BDL26BottomLocalFirstMinWeightComparison.comparison_corrects_radius S (B+7) radius (bNative+hNative) wbh
  have hp0' : tannerCoboundary0 (BDL26BottomLocalFirstMinWeightComparison.P2 S) p0=
      bNative+BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback S first :=
    hp0.trans (congrArg (fun s : BDL26BottomLocalFirstMinWeightComparison.Syndrome S =>
      bNative+BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback S s) db)
  have hp1' : tannerCoboundary0 (BDL26BottomLocalFirstMinWeightComparison.P2 S) p1=
      (bNative+hNative)+BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback S second :=
    hp1.trans (congrArg (fun s : BDL26BottomLocalFirstMinWeightComparison.Syndrome S =>
      (bNative+hNative)+BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback S s) dbh)
  have nativeBoundary : tannerCoboundary0 (BDL26BottomLocalFirstMinWeightComparison.P2 S) (p0+p1)=
      hNative+BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback S first+
        BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback S second := by
    rw [map_add,hp0',hp1']
    calc
      _ = (hNative+BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback S first+
        BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback S second)+(bNative+bNative) := by abel
      _ = _ := by rw [word_add_self,add_zero]
  let pFamily : (Data S n).family.Cochain0 0 := fun x => (p0+p1) x
  have familyBoundary : (Data S n).family.coboundary0 0 pFamily=
      (fun q => (hNative+BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback S first+
        BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback S second) q) :=
    (LinearMap.congr_fun (suffix_delta0 S n (0 : LevelIndex n)) pFamily).trans nativeBoundary
  refine ⟨pFamily,?_⟩
  funext q
  exact congrFun familyBoundary q

/-- Main bottom exactness: the small representative is constructed from FULL top background g. -/
theorem terminal_boundary_exists (S : OddScale) (n : Nat) (B : Nat)
    (large : 14*B+16 ≤ S.half) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0) (g : TopWord S n)
    (budget : HammingWeight g ≤ B) (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x) :
    ∃ p : (Data S n).family.Cochain0 0,
      (Data S n).family.coboundary0 0 p=
        (BDL26LocalizedHistoryErrorDescent.actualDescent S n (perturbTop S n sigma0 g) e x support 0).word+
          BDL26AllDepthBottomComparisonStability.baseComparison S n (perturbTop S n sigma0 g)+
          BDL26AllDepthBottomComparisonStability.baseComparison S n (perturbTop S n (perturbTop S n sigma0 g) e) := by
  exact terminal_boundary_of_preimage S n (7*B) (by omega) (perturbTop S n sigma0 g)
    (differenceWord S n sigma0 g) (background_preimage S n sigma0 zero g)
    ((differenceWord_weight S n sigma0 g).trans (Nat.mul_le_mul_left 7 budget)) e x support

/-- Defined only after the full actual bottom boundary has been proved. -/
def terminalPotential (S : OddScale) (n : Nat) (B : Nat)
    (large : 14*B+16 ≤ S.half) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0) (g : TopWord S n)
    (budget : HammingWeight g ≤ B) (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x) : (Data S n).family.Cochain0 0 :=
  Classical.choose (terminal_boundary_exists S n B large sigma0 zero g budget e x support)

theorem terminalPotential_spec (S : OddScale) (n : Nat) (B : Nat)
    (large : 14*B+16 ≤ S.half) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0) (g : TopWord S n)
    (budget : HammingWeight g ≤ B) (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x) :
    (Data S n).family.coboundary0 0
      (terminalPotential S n B large sigma0 zero g budget e x support)=
      (BDL26LocalizedHistoryErrorDescent.actualDescent S n (perturbTop S n sigma0 g) e x support 0).word+
        BDL26AllDepthBottomComparisonStability.baseComparison S n (perturbTop S n sigma0 g)+
        BDL26AllDepthBottomComparisonStability.baseComparison S n (perturbTop S n (perturbTop S n sigma0 g) e) :=
  Classical.choose_spec (terminal_boundary_exists S n B large sigma0 zero g budget e x support)

/-- The complete original top potential: lifted bottom filling PLUS entire accumulated P. -/
def topPotential (S : OddScale) (n : Nat) (B : Nat)
    (large : 14*B+16 ≤ S.half) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0) (g : TopWord S n)
    (budget : HammingWeight g ≤ B) (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x) :
    (Data S n).family.Cochain0 (TopIndex n) :=
  intervalMap0 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
    (terminalPotential S n B large sigma0 zero g budget e x support)+
  BDL26LocalizedHistoryErrorDescent.actualPotential S n (perturbTop S n sigma0 g) e x support 0 (TopIndex n)

/-- All depths, arbitrary genuine seed, FULL background budget and FULL physical star perturbation. -/
theorem topPotential_spec (S : OddScale) (n : Nat) (B : Nat)
    (large : 14*B+16 ≤ S.half) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0) (g : TopWord S n)
    (budget : HammingWeight g ≤ B) (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x) :
    (Data S n).family.coboundary0 (TopIndex n)
      (topPotential S n B large sigma0 zero g budget e x support)=
        BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 g) e := by
  unfold topPotential
  rw [map_add,intervalMap_commutes0 _ n (Nat.le_refl _) 0 (Nat.zero_le _),terminalPotential_spec]
  exact (BDL26AllDepthBottomComparisonStability.localized_residual S n (perturbTop S n sigma0 g) e x support).symm

theorem full_boundary (S : OddScale) (n : Nat) (B : Nat)
    (large : 14*B+16 ≤ S.half) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0) (g : TopWord S n)
    (budget : HammingWeight g ≤ B) (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x) :
    BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 g) e ∈
      LinearMap.range ((Data S n).family.coboundary0 (TopIndex n)) :=
  ⟨topPotential S n B large sigma0 zero g budget e x support,
    topPotential_spec S n B large sigma0 zero g budget e x support⟩

/-- Actual single-coordinate perturbations need no supplied star centre or support certificate. -/
theorem single_flip_stable (S : OddScale) (n : Nat) (B : Nat)
    (large : 14*B+16 ≤ S.half) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0) (g : TopWord S n)
    (budget : HammingWeight g ≤ B) :
    BDL26AllDepthBottomComparisonStability.SingleFlipStable S n (perturbTop S n sigma0 g) := by
  intro q
  exact full_boundary S n B large sigma0 zero g budget (canonicalBasisWord (F:=F) q)
    (BDL26LocalizedHistoryErrorDescent.elementaryCenter S n q) (BDL26LocalizedHistoryErrorDescent.elementary_support S n q)

/-- The scale-dependent source convention, still with the genuine top-word budget. -/
theorem threshold_iff (S : OddScale) (B : Nat) :
    14*B+16 ≤ S.half ↔ 28*B+33 ≤ S.ell := by
  have h := S.two_half_add_one
  omega

theorem source_scale_single_flip_stable (S : OddScale) (n : Nat) (B : Nat)
    (large : 28*B+33 ≤ S.ell) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0) (g : TopWord S n)
    (budget : HammingWeight g ≤ B) :
    BDL26AllDepthBottomComparisonStability.SingleFlipStable S n (perturbTop S n sigma0 g) :=
  single_flip_stable S n B ((threshold_iff S B).2 large) sigma0 zero g budget

/-- Full valid zero syndrome; used below only at actual depth two, without a history oracle. -/
def zeroInput (S : OddScale) (n : Nat) : TopInput S n := ⟨0,⟨0,map_zero _⟩⟩

theorem depth_two_readout (S : OddScale) (sigma : TopInput S 0) :
    BDL26AllDepthBottomComparisonStability.baseReadout S 0 sigma=sigma.val := by
  change (actualInputs S 0 sigma (TopIndex 0)).val=sigma.val
  exact congrArg Subtype.val (actualInputs_top S 0 sigma)

theorem zeroInput_depth_two (S : OddScale) :
    BDL26AllDepthBottomComparisonStability.baseReadout S 0 (zeroInput S 0)=0 :=
  depth_two_readout S (zeroInput S 0)

theorem basis_weight (S : OddScale) (n : Nat) (q : TopQ S n) :
    HammingWeight (canonicalBasisWord (F:=F) q) ≤ 1 := by
  have hs : hammingSupport (canonicalBasisWord (F:=F) q) ⊆ {q} := by
    intro r hr
    apply Finset.mem_singleton.mpr
    by_contra hn
    exact (Finset.mem_filter.mp hr).2 (by simp [canonicalBasisWord,hn])
  rw [HammingWeight_eq_card_hammingSupport]
  exact (Finset.card_le_card hs).trans (by simp)

/-- The new first bottom readout can be genuinely nonzero, not merely permitted syntactically. -/
theorem depth_two_basis_readout_nonzero (S : OddScale) (q : TopQ S 0) :
    BDL26AllDepthBottomComparisonStability.baseReadout S 0
      (perturbTop S 0 (zeroInput S 0) (canonicalBasisWord (F:=F) q))≠0 := by
  let e : TopWord S 0 := canonicalBasisWord (F:=F) q
  let z := ((state S 2).admissible.toTannerSquareAdmissible.qzRoot q).val
  have incident : (state S 2).presentation.qz q z=true :=
    ((state S 2).admissible.toTannerSquareAdmissible.qzRoot q).property
  have value : tannerCoboundary1 (state S 2).presentation e z=1 := by
    rw [tannerCoboundary1_canonicalBasis_apply,if_pos incident]
  have readout : BDL26AllDepthBottomComparisonStability.baseReadout S 0 (perturbTop S 0 (zeroInput S 0) e)=
      tannerCoboundary1 (state S 2).presentation e := by
    rw [depth_two_readout]
    change 0+(Data S 0).family.coboundary1 (TopIndex 0) e=_
    exact (zero_add ((Data S 0).family.coboundary1 (TopIndex 0) e)).trans
      (LinearMap.congr_fun (suffix_delta1 S 0 (TopIndex 0)) e)
  intro hz
  have scalar := congrFun (readout.symm.trans hz) z
  exact one_ne_zero (value.symm.trans scalar)

/-- First explicit scale for one top-coordinate background under the general uniform bound. -/
def scaleSixtyOne : OddScale := ⟨61,by decide,by decide⟩

theorem scaleSixtyOne_half : scaleSixtyOne.half=30 := by decide

/-- A literal actual C2 physical coordinate, with no nonempty-carrier assumption. -/
def finiteCoordinate : TopQ scaleSixtyOne 0 :=
  Sum.inr ⟨BDL26LevelTwoDistance.levelOneQDefault scaleSixtyOne,
    rzMap1QRoot (BDL26BottomLocalFirstMinWeightComparison.P1 scaleSixtyOne)
      (BDL26LevelTwoDistance.levelOneQDefault scaleSixtyOne) scaleSixtyOne⟩

/-- The actual nonzero one-coordinate full physical background at the first explicit scale. -/
def finiteBackground : TopWord scaleSixtyOne 0 :=
  canonicalBasisWord (F:=F) finiteCoordinate

/-- The genuine valid input obtained by perturbing the full zero input by the named background. -/
def finiteBackgroundInput : TopInput scaleSixtyOne 0 :=
  perturbTop scaleSixtyOne 0 (zeroInput scaleSixtyOne 0) finiteBackground

/-- The complete actual top potential for that physical background and the same nonzero flip. -/
def finiteTopPotential : (Data scaleSixtyOne 0).family.Cochain0 (TopIndex 0) :=
  topPotential scaleSixtyOne 0 1 (by decide) (zeroInput scaleSixtyOne 0)
    (zeroInput_depth_two scaleSixtyOne) finiteBackground (basis_weight scaleSixtyOne 0 finiteCoordinate)
    finiteBackground (BDL26LocalizedHistoryErrorDescent.elementaryCenter scaleSixtyOne 0 finiteCoordinate)
    (BDL26LocalizedHistoryErrorDescent.elementary_support scaleSixtyOne 0 finiteCoordinate)

/-- Genuine finite consumer: nonzero complete baseline readout AND nonzero perturbation. -/
theorem finite_nonzero_background_and_perturbation :
    BDL26AllDepthBottomComparisonStability.baseReadout scaleSixtyOne 0 finiteBackgroundInput≠0 ∧
      finiteBackground≠0 ∧
      BDL26AllDepthBottomComparisonStability.SingleFlipStable scaleSixtyOne 0 finiteBackgroundInput ∧
      (Data scaleSixtyOne 0).family.coboundary0 (TopIndex 0) finiteTopPotential=
        BDL26AllDepthBottomComparisonStability.residual scaleSixtyOne 0 finiteBackgroundInput finiteBackground := by
  dsimp only [finiteBackgroundInput,finiteTopPotential,finiteBackground]
  refine ⟨depth_two_basis_readout_nonzero scaleSixtyOne finiteCoordinate,?_,?_,?_⟩
  · intro hg
    have hv := congrFun hg finiteCoordinate
    exact (one_ne_zero : (1 : F) ≠ 0) (by simpa [canonicalBasisWord] using hv)
  · exact single_flip_stable scaleSixtyOne 0 1 (by decide) (zeroInput scaleSixtyOne 0)
      (zeroInput_depth_two scaleSixtyOne) _ (basis_weight scaleSixtyOne 0 finiteCoordinate)
  · exact topPotential_spec scaleSixtyOne 0 1 (by decide) (zeroInput scaleSixtyOne 0)
      (zeroInput_depth_two scaleSixtyOne) _ (basis_weight scaleSixtyOne 0 finiteCoordinate) _
      (BDL26LocalizedHistoryErrorDescent.elementaryCenter scaleSixtyOne 0 finiteCoordinate)
      (BDL26LocalizedHistoryErrorDescent.elementary_support scaleSixtyOne 0 finiteCoordinate)

end QEC.Coding.BDL26NonzeroBackgroundComparisonStability
end
