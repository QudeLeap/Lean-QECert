import QEC.Coding.FiniteAlternatingConstruction.NonzeroBackgroundComparisonStability
import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.UniformRXTail.StoppedReadout

/-!
# A quantitative obstruction to uniformly bounded background responses

The same comparison decoder and both complete correction calls are retained.
A finite path through the actual canonical logical word contains a bad physical
single-flip step. At sufficiently large scale no background restriction with
weight at most B can preserve that step's logical class. This excludes a fixed
response-weight budget; it does not exclude spatial footprints or witnesses
whose weight grows with scale.
-/
noncomputable section
namespace QEC.Coding.BDL26LocalBackgroundComparisonResponse

open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26RZMap1CoordinateBridge
open BDL26HistoryLogicalResidual
open scoped Classical BigOperators

abbrev W (S : OddScale) (n : Nat) := (SuffixData S n).family.Cochain1 (TopIndex n)
abbrev Q (S : OddScale) (n : Nat) := (state S (n+2)).presentation.Q
abbrev boundaries (S : OddScale) (n : Nat) :=
  LinearMap.range ((SuffixData S n).family.coboundary0 (TopIndex n))

def backgroundRestriction (S : OddScale) (n : Nat) (w : W S n) (A : Finset (Q S n)) : W S n :=
  BDL26NonzeroBackgroundComparisonStability.partialWord S n w A

private theorem prefix_empty (S : OddScale) (n : Nat) (w : W S n) :
    backgroundRestriction S n w ∅=0 := by
  funext q
  simp [backgroundRestriction,BDL26NonzeroBackgroundComparisonStability.partialWord]

private theorem prefix_insert (S : OddScale) (n : Nat) (w : W S n)
    (A : Finset (Q S n)) (q : Q S n) (hq : q ∉ A)
    (hw : q ∈ hammingSupport w) :
    backgroundRestriction S n w (insert q A)=backgroundRestriction S n w A+canonicalBasisWord (F:=BDL26Field) q := by
  have one : w q=1 := PauliSymplectic.zmod_two_eq_one_of_ne_zero (Finset.mem_filter.mp hw).2
  funext r
  by_cases hr : r=q
  · subst r
    simp [backgroundRestriction,BDL26NonzeroBackgroundComparisonStability.partialWord,canonicalBasisWord,hq,one]
  · simp [backgroundRestriction,BDL26NonzeroBackgroundComparisonStability.partialWord,canonicalBasisWord,hr]

private theorem perturb_zero (S : OddScale) (n : Nat) (sigma : TopInput S n) :
    perturbTop S n sigma (0 : W S n)=sigma := by
  apply Subtype.ext
  change sigma.val+((SuffixData S n).family.coboundary1 (TopIndex n)) 0=sigma.val
  rw [map_zero,add_zero]

/-- Exact telescoping retains both complete correction calls at all three inputs. -/
theorem residual_add (S : OddScale) (n : Nat) (sigma : TopInput S n) (a b : W S n) :
    BDL26AllDepthBottomComparisonStability.residual S n sigma (a+b)=
      BDL26AllDepthBottomComparisonStability.residual S n sigma a+BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma a) b := by
  unfold BDL26AllDepthBottomComparisonStability.residual
  rw [BDL26NonzeroBackgroundComparisonStability.perturb_add]
  have h := word_add_self (BDL26AllDepthBottomComparisonStability.correction S n (perturbTop S n sigma a))
  symm
  calc
    _ = ((a+b)+BDL26AllDepthBottomComparisonStability.correction S n sigma+
        BDL26AllDepthBottomComparisonStability.correction S n (perturbTop S n sigma (a+b)))+
        (BDL26AllDepthBottomComparisonStability.correction S n (perturbTop S n sigma a)+
          BDL26AllDepthBottomComparisonStability.correction S n (perturbTop S n sigma a)) := by abel
    _ = _ := by rw [h,add_zero]

private theorem residual_zero (S : OddScale) (n : Nat) (sigma : TopInput S n) :
    BDL26AllDepthBottomComparisonStability.residual S n sigma (0 : W S n)=0 := by
  rw [BDL26AllDepthBottomComparisonStability.residual,perturb_zero,zero_add,word_add_self]

/-- A closed full word returns to exactly the same input, without a selector law. -/
theorem residual_of_closed (S : OddScale) (n : Nat) (sigma : TopInput S n)
    (w : W S n) (closed : (SuffixData S n).family.coboundary1 (TopIndex n) w=0) :
    BDL26AllDepthBottomComparisonStability.residual S n sigma w=w := by
  have same : perturbTop S n sigma w=sigma := by
    apply Subtype.ext
    change sigma.val+((SuffixData S n).family.coboundary1 (TopIndex n)) w=sigma.val
    rw [closed,add_zero]
  rw [BDL26AllDepthBottomComparisonStability.residual,same,add_assoc,word_add_self,add_zero]

/-- The literal finite-backgroundRestriction generator is a nonboundary in the full top carrier. -/
theorem logical_word_nonboundary (S : OddScale) (n : Nat) (sigma : TopInput S n) :
    logicalError S n ∉ boundaries S n := by
  intro h
  apply logicalError_not_boundary S n sigma
  obtain ⟨p,hp⟩ := h
  exact ⟨p,hp.trans (topWord_of_closed S n sigma _ (logicalError_closed S n)).symm⟩

/-- A genuine supported-coordinate backgroundRestriction of the actual logical word has a bad
next physical flip. No hypothetical terminal residual is supplied. -/
theorem exists_bad_prefix (S : OddScale) (n : Nat) (sigma0 : TopInput S n) :
    ∃ (A : Finset (Q S n)) (q : Q S n),
      A ⊆ hammingSupport (logicalError S n) ∧
      q ∈ hammingSupport (logicalError S n) ∧ q ∉ A ∧
      BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 (backgroundRestriction S n (logicalError S n) A))
        (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n := by
  by_contra none
  have every : ∀ (A : Finset (Q S n)) (q : Q S n),
      A ⊆ hammingSupport (logicalError S n) →
      q ∈ hammingSupport (logicalError S n) → q ∉ A →
      BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 (backgroundRestriction S n (logicalError S n) A))
        (canonicalBasisWord (F:=BDL26Field) q) ∈ boundaries S n := by
    intro A q hA hq hn
    by_contra bad
    exact none ⟨A,q,hA,hq,hn,bad⟩
  have allprefix : ∀ A : Finset (Q S n), A ⊆ hammingSupport (logicalError S n) →
      BDL26AllDepthBottomComparisonStability.residual S n sigma0 (backgroundRestriction S n (logicalError S n) A) ∈ boundaries S n := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
        intro _
        rw [prefix_empty,residual_zero]
        exact (boundaries S n).zero_mem
    | @insert q A hn ih =>
        intro sub
        have hq := sub (Finset.mem_insert_self q A)
        have hA : A ⊆ hammingSupport (logicalError S n) := fun r hr => sub (Finset.mem_insert_of_mem hr)
        rw [prefix_insert S n _ A q hn hq,residual_add]
        exact (boundaries S n).add_mem (ih hA) (every A q hA hq hn)
  have full := allprefix (hammingSupport (logicalError S n)) (fun _ h => h)
  have hp : backgroundRestriction S n (logicalError S n) (hammingSupport (logicalError S n))=logicalError S n :=
    BDL26NonzeroBackgroundComparisonStability.partial_support_eq S n _
  rw [hp,residual_of_closed S n sigma0 _ (logicalError_closed S n)] at full
  exact logical_word_nonboundary S n sigma0 full

/-- Every restricted background within the existing budget has a trivial defect. -/
theorem restricted_background_stable (S : OddScale) (n B : Nat)
    (large : 28*B+33 ≤ S.ell) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0) (g : W S n) (A : Finset (Q S n))
    (small : HammingWeight (backgroundRestriction S n g A) ≤ B) (q : Q S n) :
    BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 (backgroundRestriction S n g A))
      (canonicalBasisWord (F:=BDL26Field) q) ∈ boundaries S n :=
  BDL26NonzeroBackgroundComparisonStability.source_scale_single_flip_stable S n B large sigma0 zero _ small q

/-- Quantitative no-go: a constructed bad backgroundRestriction admits no boundary-equivalent
restriction of its same background having weight at most B. -/
theorem exists_no_bounded_response (S : OddScale) (n B : Nat)
    (large : 28*B+33 ≤ S.ell) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0) :
    ∃ (P : Finset (Q S n)) (q : Q S n),
      P ⊆ hammingSupport (logicalError S n) ∧ q ∈ hammingSupport (logicalError S n) ∧ q ∉ P ∧
      let g := backgroundRestriction S n (logicalError S n) P
      BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 g) (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n ∧
      ∀ A : Finset (Q S n), HammingWeight (backgroundRestriction S n g A) ≤ B →
        BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 g) (canonicalBasisWord (F:=BDL26Field) q)-
          BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 (backgroundRestriction S n g A))
            (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n := by
  obtain ⟨P,q,hP,hq,hn,bad⟩ := exists_bad_prefix S n sigma0
  refine ⟨P,q,hP,hq,hn,bad,?_⟩
  intro A small equalclass
  have safe := restricted_background_stable S n B large sigma0 zero
    (backgroundRestriction S n (logicalError S n) P) A small q
  apply bad
  have sum := (boundaries S n).add_mem equalclass safe
  simpa only [sub_add_cancel] using sum


/-- The literal zero valid input has zero FIRST at every depth, by its actual history. -/
theorem zero_seed_readout (S : OddScale) (n : Nat) :
    BDL26AllDepthBottomComparisonStability.baseReadout S n
      (BDL26NonzeroBackgroundComparisonStability.zeroInput S n)=0 := by
  unfold BDL26AllDepthBottomComparisonStability.baseReadout
  rw [← actualInputs_readout]
  exact BDL26UniformRXTail.actualHistory_zero_readout S n
    (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) rfl
    (LevelTwoHistory.physicalLevel (0 : LevelIndex n))

/-- Every actual bad background exceeds the proved stability budget. -/
theorem bad_background_weight_gt (S : OddScale) (n B : Nat)
    (large : 28*B+33 ≤ S.ell) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0)
    (g : W S n) (q : Q S n)
    (bad : BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 g)
      (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n) : B < HammingWeight g := by
  by_contra small
  apply bad
  exact BDL26NonzeroBackgroundComparisonStability.source_scale_single_flip_stable
    S n B large sigma0 zero g (by omega) q

/-- Fully inhabited actual-family obstruction: zero seed, a nonzero physical
background and a nonzero supported single flip, including all positive depths. -/
theorem exists_large_bad_prefix (S : OddScale) (n B : Nat)
    (large : 28*B+33 ≤ S.ell) :
    ∃ (P : Finset (Q S n)) (q : Q S n),
      P ⊆ hammingSupport (logicalError S n) ∧ q ∈ hammingSupport (logicalError S n) ∧ q ∉ P ∧
      let g := backgroundRestriction S n (logicalError S n) P
      B < HammingWeight g ∧ g ≠ 0 ∧
      canonicalBasisWord (F:=BDL26Field) q ≠ (0 : W S n) ∧
      BDL26AllDepthBottomComparisonStability.residual S n
        (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g)
        (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n := by
  obtain ⟨P,q,hP,hq,hn,bad⟩ := exists_bad_prefix S n
    (BDL26NonzeroBackgroundComparisonStability.zeroInput S n)
  have weight := bad_background_weight_gt S n B large
    (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) (zero_seed_readout S n) _ q bad
  refine ⟨P,q,hP,hq,hn,weight,?_,?_,bad⟩
  · intro hz
    rw [hz,HammingWeight_zero] at weight
    omega
  · intro hz
    have hv := congrFun hz q
    have onezero : (1 : BDL26Field)=0 := by simpa [canonicalBasisWord] using hv
    exact one_ne_zero onezero

end QEC.Coding.BDL26LocalBackgroundComparisonResponse
