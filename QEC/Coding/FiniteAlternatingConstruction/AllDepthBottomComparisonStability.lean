import QEC.Coding.FiniteAlternatingConstruction.BottomLocalFirstMinWeightComparison
import QEC.Coding.FiniteAlternatingConstruction.LocalizedHistoryErrorDescent
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.ActualFailureReadout
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.EvenC4OldXEndpoint

/-!
# All-depth stability for a separately named bottom comparison decoder

The original above-C2 histories, selected maps, graph,
marks and canonical decoder are unchanged. Only this new correction function
uses the already proved finite Dstar at the physical C2 endpoint. Its theorem
has arbitrary valid backgrounds and full physical words, not caller-supplied
lower errors, support certificates, logical classes or potential witnesses.

BDL26 v1 paper.tex3435 permits a suitable finite bottom decoder; 3445 and
3465--3481 give the zero-readout stability route. The uniform canonical
counterexample at the end concerns the existing implementation, not that
choice-dependent paper assertion. No canonical adoption or public claim.
-/
noncomputable section
namespace QEC.Coding.BDL26AllDepthBottomComparisonStability

open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators

abbrev F := BDL26Field
abbrev Data (S : OddScale) (n : Nat) := SuffixData S n
abbrev TopWord (S : OddScale) (n : Nat) := (Data S n).family.Cochain1 (TopIndex n)
abbrev BaseWord (S : OddScale) (n : Nat) := (Data S n).family.Cochain1 0

/-- The entire literal stored input at physical C2. -/
def baseReadout (S : OddScale) (n : Nat) (sigma : TopInput S n) :
    Word F (state S 2).presentation.Z :=
  (actualInputs S n sigma 0).val

/-- Separately named full C2 comparison call; no change to actualBase. -/
def baseComparison (S : OddScale) (n : Nat) (sigma : TopInput S n) : BaseWord S n :=
  fun q => BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback S
    (baseReadout S n sigma) q

/-- Exact bottom replacement, retaining the original complete correction. -/
def correction (S : OddScale) (n : Nat) (sigma : TopInput S n) : TopWord S n :=
  historyLiftedCorrection (Data S n) (actualHistory S n sigma) +
    intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
      ((actualBase S n).decode (actualInputs S n sigma 0) + baseComparison S n sigma)

/-- Every base input is valid in the original full physical C2 complex. -/
theorem baseReadout_valid (S : OddScale) (n : Nat) (sigma : TopInput S n) :
    baseReadout S n sigma ∈ LinearMap.range
      (tannerCoboundary1 (state S 2).presentation) := by
  obtain ⟨e,he⟩ := (actualInputs S n sigma 0).property
  refine ⟨e,?_⟩
  have heq := LinearMap.congr_fun (suffix_delta1 S n (0 : LevelIndex n)) e
  exact heq.symm.trans he

/-- The new endpoint call is a right inverse, for all original scales. -/
theorem baseComparison_syndrome (S : OddScale) (n : Nat) (sigma : TopInput S n) :
    (Data S n).family.coboundary1 0 (baseComparison S n sigma) =
      (actualInputs S n sigma 0).val := by
  rw [suffix_delta1]
  exact BDL26BottomLocalFirstMinWeightComparison.comparison_rightInverse
    S (baseReadout S n sigma) (baseReadout_valid S n sigma)

theorem baseComparison_zero (S : OddScale) (n : Nat) (sigma : TopInput S n)
    (zero : baseReadout S n sigma=0) : baseComparison S n sigma=0 := by
  have hs : (baseReadout S n sigma :
      BDL26BottomLocalFirstMinWeightComparison.Syndrome S) =
      (0 : BDL26BottomLocalFirstMinWeightComparison.Syndrome S) := zero
  have hnative : BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback S
      (baseReadout S n sigma) =
      (0 : BDL26BottomLocalFirstMinWeightComparison.Error S) :=
    (congrArg (BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback S) hs).trans
      (BDL26BottomLocalFirstMinWeightComparison.comparison_zero S)
  funext q
  exact congrFun hnative q

/-- Exact operational meaning: same above-C2 sums and one new bottom call. -/
theorem correction_above (S : OddScale) (n : Nat) (sigma : TopInput S n) :
    correction S n sigma = correctionIntervalSum S n sigma 0 (TopIndex n) +
      intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
        (baseComparison S n sigma) := by
  unfold correction
  rw [actualCorrection_split,map_add]
  let old := intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
    ((actualBase S n).decode (actualInputs S n sigma 0))
  have twice : old+old=0 := word_add_self old
  calc
    _ = correctionIntervalSum S n sigma 0 (TopIndex n) + (old+old) +
      intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _) (baseComparison S n sigma) := by
        dsimp only [old]
        abel
    _ = _ := by rw [twice,add_zero]

/-- A full cocycle is preserved by the actual selected interval map1. -/
private theorem interval_closed (S : OddScale) (n : Nat) (w : BaseWord S n)
    (closed : (Data S n).family.coboundary1 0 w=0) :
    (Data S n).family.coboundary1 (TopIndex n)
      (intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _) w)=0 := by
  let wNative : Word F (state S 2).presentation.Q := fun q => w q
  have closedNative : tannerCoboundary1 (state S 2).presentation wNative = 0 :=
    (LinearMap.congr_fun (suffix_delta1 S n (0 : LevelIndex n)) w).symm.trans closed
  let c : BDL26FiniteCohomology.Cocycle S 2 :=
    ⟨wNative,(BDL26RZCohomology.mem_cocycle_iff
      (state S 2).presentation wNative).mpr closedNative⟩
  let upper : BDL26FiniteCohomology.Cocycle S ((TopIndex n).val+2) :=
    intervalCocycle S n 0 (TopIndex n) (Nat.zero_le _) c
  have upperClosed : tannerCoboundary1
      (state S ((TopIndex n).val+2)).presentation upper.val = 0 :=
    (BDL26RZCohomology.mem_cocycle_iff
      (state S ((TopIndex n).val+2)).presentation upper.val).mp upper.property
  have wordNative : upper.val =
      (fun q => intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _) w q) :=
    intervalCocycle_word S n 0 (TopIndex n) (Nat.zero_le _) c
  have liftedClosed : tannerCoboundary1 (state S ((TopIndex n).val+2)).presentation
      (fun q => intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _) w q) = 0 :=
    (congrArg (tannerCoboundary1 (state S ((TopIndex n).val+2)).presentation)
      wordNative).symm.trans upperClosed
  exact (LinearMap.congr_fun (suffix_delta1 S n (TopIndex n))
    (intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _) w)).trans liftedClosed

/-- The separately named all-depth comparison is itself a genuine decoder. -/
theorem correction_syndrome (S : OddScale) (n : Nat) (sigma : TopInput S n) :
    (Data S n).family.coboundary1 (TopIndex n) (correction S n sigma)=sigma.val := by
  have hb := (actualBase S n).rightInverse (actualInputs S n sigma 0)
  have hc := baseComparison_syndrome S n sigma
  have hclosed : (Data S n).family.coboundary1 0
      ((actualBase S n).decode (actualInputs S n sigma 0)+baseComparison S n sigma)=0 := by
    rw [map_add,hb,hc]
    exact word_add_self _
  unfold correction
  rw [map_add,interval_closed S n _ hclosed,add_zero]
  exact actualHistory_syndrome S n sigma

/-- The full response of two correlated original histories to one upper error. -/
def residual (S : OddScale) (n : Nat) (sigma : TopInput S n) (e : TopWord S n) : TopWord S n :=
  e+correction S n sigma+correction S n (perturbTop S n sigma e)

/-- Elementary F2 algebra of replacing BOTH original endpoint calls. -/
private theorem swap_two_bases {I J K : Type}
    (L : Word F I →ₗ[F] Word F J) (d : Word F K →ₗ[F] Word F J)
    (e A B : Word F J) (h b c u v : Word F I) (P : Word F K)
    (equation : e+A+B=L (h+b+c)+d P) :
    e+(A+L (b+u))+(B+L (c+v))=L (h+u+v)+d P := by
  have cancel : L (h+b+c)+L (b+u)+L (c+v)=L (h+u+v) := by
    rw [← map_add,← map_add]
    apply congrArg L
    calc
      _ = (h+u+v)+(b+b)+(c+c) := by abel
      _ = _ := by rw [word_add_self,word_add_self,add_zero,add_zero]
  calc
    _ = (e+A+B)+L (b+u)+L (c+v) := by abel
    _ = (L (h+b+c)+d P)+L (b+u)+L (c+v) := by rw [equation]
    _ = (L (h+b+c)+L (b+u)+L (c+v))+d P := by abel
    _ = _ := by rw [cancel]

/-- Actual whole-word telescoping, without any bottom-readout assumption. -/
theorem localized_residual (S : OddScale) (n : Nat) (sigma : TopInput S n)
    (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x) :
    residual S n sigma e =
      intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
        ((BDL26LocalizedHistoryErrorDescent.actualDescent S n sigma e x support 0).word+
          baseComparison S n sigma+baseComparison S n (perturbTop S n sigma e))+
      (Data S n).family.coboundary0 (TopIndex n)
        (BDL26LocalizedHistoryErrorDescent.actualPotential S n sigma e x support 0 (TopIndex n)) := by
  exact swap_two_bases
    (intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _))
    ((Data S n).family.coboundary0 (TopIndex n)) _ _ _ _ _ _ _ _ _
    (BDL26LocalizedHistoryErrorDescent.actual_history S n sigma e x support)

/-- Direct support/card counting includes the empty suffix n=0. -/
theorem terminal_weight (S : OddScale) (n : Nat) (sigma : TopInput S n)
    (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x) :
    HammingWeight (BDL26LocalizedHistoryErrorDescent.actualDescent S n sigma e x support 0).word ≤ 7 := by
  rw [HammingWeight_eq_card_hammingSupport]
  exact (Finset.card_le_card
    (BDL26LocalizedHistoryErrorDescent.actualDescent_supported S n sigma e x support 0)).trans
      (BDL26LocalizedHistoryErrorDescent.star_card S n 0 _)

/-- The terminal degree-zero potential is proved, not supplied by the caller. -/
theorem terminal_boundary_exists (S : OddScale) (n : Nat) (large : 16 ≤ S.half)
    (sigma : TopInput S n) (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x)
    (zero : baseReadout S n sigma=0) :
    ∃ p : (Data S n).family.Cochain0 0,
      (Data S n).family.coboundary0 0 p =
        (BDL26LocalizedHistoryErrorDescent.actualDescent S n sigma e x support 0).word+
          baseComparison S n sigma+baseComparison S n (perturbTop S n sigma e) := by
  let h : BaseWord S n :=
    (BDL26LocalizedHistoryErrorDescent.actualDescent S n sigma e x support 0).word
  have small : HammingWeight h ≤ 7 := terminal_weight S n sigma e x support
  let hNative : BDL26BottomLocalFirstMinWeightComparison.Error S := fun q => h q
  have smallNative : HammingWeight hNative ≤ 7 := small
  have hd := BDL26LocalizedHistoryErrorDescent.actualDescent_syndrome S n sigma e x support 0
  have hdelta : (Data S n).family.coboundary1 0 h =
      tannerCoboundary1 (BDL26BottomLocalFirstMinWeightComparison.P2 S) hNative :=
    LinearMap.congr_fun (suffix_delta1 S n (0 : LevelIndex n)) h
  have sameNative : tannerCoboundary1 (BDL26BottomLocalFirstMinWeightComparison.P2 S) hNative =
      (baseReadout S n (perturbTop S n sigma e) :
        BDL26BottomLocalFirstMinWeightComparison.Syndrome S) := by
    funext z
    have hz : tannerCoboundary1 (BDL26BottomLocalFirstMinWeightComparison.P2 S) hNative z =
        baseReadout S n sigma z+baseReadout S n (perturbTop S n sigma e) z :=
      congrFun (hdelta.symm.trans hd) z
    have zeroScalar : baseReadout S n sigma z = (0 : F) := congrFun zero z
    simpa only [zeroScalar,zero_add] using hz
  obtain ⟨p,hp⟩ :=
    BDL26BottomLocalFirstMinWeightComparison.comparison_corrects_weight_seven
      S large hNative smallNative
  have nativeBoundary : tannerCoboundary0 (BDL26BottomLocalFirstMinWeightComparison.P2 S) p =
      hNative+BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback S
        (baseReadout S n (perturbTop S n sigma e)) :=
    hp.trans (congrArg (fun s : BDL26BottomLocalFirstMinWeightComparison.Syndrome S =>
      hNative+BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback S s) sameNative)
  let pFamily : (Data S n).family.Cochain0 0 := fun x => p x
  have familyBoundary : (Data S n).family.coboundary0 0 pFamily =
      (fun q => (hNative+
        BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback S
          (baseReadout S n (perturbTop S n sigma e))) q) :=
    (LinearMap.congr_fun (suffix_delta0 S n (0 : LevelIndex n)) pFamily).trans nativeBoundary
  refine ⟨pFamily,?_⟩
  rw [baseComparison_zero S n sigma zero,add_zero]
  funext q
  exact congrFun familyBoundary q

/-- Chosen only from the preceding genuine complete boundary theorem. -/
def terminalPotential (S : OddScale) (n : Nat) (large : 16 ≤ S.half)
    (sigma : TopInput S n) (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x)
    (zero : baseReadout S n sigma=0) : (Data S n).family.Cochain0 0 :=
  Classical.choose (terminal_boundary_exists S n large sigma e x support zero)

theorem terminalPotential_spec (S : OddScale) (n : Nat) (large : 16 ≤ S.half)
    (sigma : TopInput S n) (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x)
    (zero : baseReadout S n sigma=0) :
    (Data S n).family.coboundary0 0 (terminalPotential S n large sigma e x support zero)=
      (BDL26LocalizedHistoryErrorDescent.actualDescent S n sigma e x support 0).word+
        baseComparison S n sigma+baseComparison S n (perturbTop S n sigma e) :=
  Classical.choose_spec (terminal_boundary_exists S n large sigma e x support zero)

/-- Entire lifted bottom potential plus the entire actual accumulated potential. -/
def topPotential (S : OddScale) (n : Nat) (large : 16 ≤ S.half)
    (sigma : TopInput S n) (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x)
    (zero : baseReadout S n sigma=0) : (Data S n).family.Cochain0 (TopIndex n) :=
  intervalMap0 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
    (terminalPotential S n large sigma e x support zero)+
      BDL26LocalizedHistoryErrorDescent.actualPotential S n sigma e x support 0 (TopIndex n)

/-- Main all-depth full-error theorem, with its explicit original top potential. -/
theorem topPotential_spec (S : OddScale) (n : Nat) (large : 16 ≤ S.half)
    (sigma : TopInput S n) (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x)
    (zero : baseReadout S n sigma=0) :
    (Data S n).family.coboundary0 (TopIndex n) (topPotential S n large sigma e x support zero)=
      residual S n sigma e := by
  unfold topPotential
  rw [map_add,intervalMap_commutes0 _ n (Nat.le_refl _) 0 (Nat.zero_le _),terminalPotential_spec]
  exact (localized_residual S n sigma e x support).symm

theorem zero_base_full_boundary (S : OddScale) (n : Nat) (large : 16 ≤ S.half)
    (sigma : TopInput S n) (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x)
    (zero : baseReadout S n sigma=0) :
    residual S n sigma e ∈ LinearMap.range ((Data S n).family.coboundary0 (TopIndex n)) :=
  ⟨topPotential S n large sigma e x support zero,topPotential_spec S n large sigma e x support zero⟩

/-- Decoder-dependent X stability; the comparison decoder is named explicitly. -/
def SingleFlipStable (S : OddScale) (n : Nat) (sigma : TopInput S n) : Prop :=
  ∀ q : (state S (n+2)).presentation.Q,
    residual S n sigma (canonicalBasisWord (F:=F) q) ∈
      LinearMap.range ((Data S n).family.coboundary0 (TopIndex n))

theorem zero_base_single_flip_stable (S : OddScale) (n : Nat) (large : 16 ≤ S.half)
    (sigma : TopInput S n) (zero : baseReadout S n sigma=0) :
    SingleFlipStable S n sigma := by
  intro q
  exact zero_base_full_boundary S n large sigma (canonicalBasisWord (F:=F) q)
    (BDL26LocalizedHistoryErrorDescent.elementaryCenter S n q)
    (BDL26LocalizedHistoryErrorDescent.elementary_support S n q) zero

/-- The exact source-even physical depths include k=1, the empty suffix. -/
theorem source_even_single_flip_stable (S : OddScale) (k : Nat) (hk : 1≤k)
    (large : 16 ≤ S.half) (sigma : TopInput S (2*(k-1)))
    (zero : baseReadout S (2*(k-1)) sigma=0) :
    2*(k-1)+2=2*k ∧ SingleFlipStable S (2*(k-1)) sigma :=
  ⟨by omega,zero_base_single_flip_stable S _ large sigma zero⟩

/-- The full stored base word equals the existing public FIRST word. -/
theorem baseReadout_original_FIRST (S : OddScale) (n : Nat)
    (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n) :
    baseReadout S n (BDL26ActualFailureReadout.input S n u)=
      BDL26ActualFailureReadout.firstReadout S n u := rfl

/-- In the original odd-scale convention, the fixed threshold is ell>=33. -/
theorem threshold_iff (S : OddScale) : 16≤S.half ↔ 33≤S.ell := by
  have h := S.two_half_add_one
  omega

/-- The source-scale formulation retains the complete all-depth hypothesis. -/
theorem source_scale_single_flip_stable (S : OddScale) (n : Nat) (large : 33≤S.ell)
    (sigma : TopInput S n) (zero : baseReadout S n sigma=0) :
    SingleFlipStable S n sigma :=
  zero_base_single_flip_stable S n ((threshold_iff S).2 large) sigma zero

/-- Actual physical-input consumer of the existing complete FIRST word. -/
theorem original_input_single_flip_stable (S : OddScale) (n : Nat) (large : 16≤S.half)
    (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (zero : BDL26ActualFailureReadout.firstReadout S n u=0) :
    SingleFlipStable S n (BDL26ActualFailureReadout.input S n u) :=
  zero_base_single_flip_stable S n large _
    ((baseReadout_original_FIRST S n u).trans zero)

/-- Explicit first admissible odd scale for the stated uniform comparison bound. -/
def scaleThirtyThree : OddScale := ⟨33,by decide,by decide⟩

theorem scaleThirtyThree_half : scaleThirtyThree.half=16 := by decide

theorem scaleThirtyThree_stable (n : Nat) (sigma : TopInput scaleThirtyThree n)
    (zero : baseReadout scaleThirtyThree n sigma=0) :
    SingleFlipStable scaleThirtyThree n sigma :=
  source_scale_single_flip_stable scaleThirtyThree n (by decide) sigma zero

/-- Canonical obstruction in the ORIGINAL sigma2=0 domain, uniform in scale.
It retains a genuine legal C4 input, one physical flip and the full residual.
The second bottom input is nonzero; replacing its decoder call can matter. -/
theorem canonical_zero_base_instability (S : OddScale) :
    ∃ (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S 2)
      (q : BDL26CSSHamiltonian.Physical S 4),
      BDL26CanonicalHistoryMarks.baseInput S 2 (BDL26ActualFailureReadout.input S 2 u)=0 ∧
      BDL26ActualFailureReadout.secondReadout S 2 u q≠0 ∧
      BDL26LogicalDefectProtection.chiX S 2 u q=1 ∧
      BDL26CSSHamiltonian.zSyndrome S 4 (BDL26LogicalDefectProtection.deltaX S 2 u q)=0 ∧
      BDL26LogicalDefectProtection.deltaX S 2 u q ∉ LinearMap.range
        (tannerCoboundary0 (state S 4).presentation) := by
  obtain ⟨u,q,hfirst,hchi,hclosed,hnb⟩ :=
    BDL26EvenC4OldXEndpoint.exists_original_even_C4_single_physical_first_zero_chi_one S
  have hsecond : BDL26ActualFailureReadout.secondReadout S 2 u q≠0 := by
    intro hz
    exact one_ne_zero (hchi.symm.trans (BDL26ActualFailureReadout.chiX_zero S 2 u q hfirst hz))
  refine ⟨u,q,?_,hsecond,hchi,hclosed,hnb⟩
  apply Subtype.ext
  exact (BDL26ActualFailureReadout.firstReadout_marks_base S 2 u).symm.trans hfirst

end QEC.Coding.BDL26AllDepthBottomComparisonStability
end
