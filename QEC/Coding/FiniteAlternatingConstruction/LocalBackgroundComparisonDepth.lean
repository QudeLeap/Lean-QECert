import QEC.Coding.FiniteAlternatingConstruction.LocalBackgroundComparisonResponse
import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.UniformReadoutWeight

/-!
# Fixed-scale obstruction to depth-uniform response weight

The actual global alternating history contracts syndrome weight by a factor
of two at each RX step. A sufficiently deep history therefore has zero FIRST
on every bounded-weight background above the genuine zero seed. A bad prefix
of the actual logical generator cannot have a boundary-equivalent response
whose weight is bounded independently of depth, even at one fixed scale.

This concerns response weight. Spatial-radius bounds and variable-size
probabilistic witnesses are separate questions.
-/
noncomputable section
namespace QEC.Coding.BDL26LocalBackgroundComparisonDepth

open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open BDL26LocalBackgroundComparisonResponse
open scoped Classical BigOperators

/-- Every comparison residual is a genuine full top cocycle. Thus the
nonboundary conclusions below concern logical classes, not nonclosed words. -/
theorem comparison_residual_closed (S : OddScale) (n : Nat)
    (sigma : TopInput S n) (e : W S n) :
    (SuffixData S n).family.coboundary1 (TopIndex n)
      (BDL26AllDepthBottomComparisonStability.residual S n sigma e)=0 := by
  have first := BDL26AllDepthBottomComparisonStability.correction_syndrome S n sigma
  have second := BDL26AllDepthBottomComparisonStability.correction_syndrome S n (perturbTop S n sigma e)
  unfold BDL26AllDepthBottomComparisonStability.residual
  rw [map_add,map_add,first,second]
  change (SuffixData S n).family.coboundary1 (TopIndex n) e+sigma.val+
    (sigma.val+(SuffixData S n).family.coboundary1 (TopIndex n) e)=0
  calc
    _ = ((SuffixData S n).family.coboundary1 (TopIndex n) e+
        (SuffixData S n).family.coboundary1 (TopIndex n) e)+(sigma.val+sigma.val) := by abel
    _ = 0 := by rw [word_add_self,word_add_self,add_zero]

/-- The actual full global C2 readout obeys the global alternating contraction.
No marked-component restriction theorem is used. -/
theorem zero_seed_c2_weight (S : OddScale) (n : Nat) (g : W S n) :
    2 ^ ((n+1)/2) * HammingWeight
      (BDL26AllDepthBottomComparisonStability.baseReadout S n
        (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g)) ≤
      4 * HammingWeight g := by
  let tau : TopInput S n :=
    perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g
  have history := BDL26UniformHistoryObstruction.actualHistory_c2_weight S n tau
  change 2 ^ ((n+1)/2) * HammingWeight (actualReadout S n tau 0) ≤ HammingWeight tau.val at history
  rw [actualInputs_readout] at history
  have top : tau.val = (indexedFamily S (n+2)).coboundary1 (TopIndex (n+2)) g := by
    change (0 : (indexedFamily S (n+2)).Cochain2 (TopIndex (n+2)))+_=_
    exact zero_add _
  rw [top] at history
  have degree := differential_weight S (n+2) (Fin.last (n+1)) g
  exact history.trans degree

/-- A bounded physical background at sufficient depth has literally zero FIRST. -/
theorem small_background_first_zero (S : OddScale) (n B : Nat)
    (deep : 4*B < 2 ^ ((n+1)/2)) (g : W S n)
    (small : HammingWeight g ≤ B) :
    BDL26AllDepthBottomComparisonStability.baseReadout S n
      (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g)=0 := by
  apply (HammingWeight_eq_zero_iff _).mp
  have upper := (zero_seed_c2_weight S n g).trans (Nat.mul_le_mul_left 4 small)
  by_contra nonzero
  have one : 1 ≤ HammingWeight
      (BDL26AllDepthBottomComparisonStability.baseReadout S n
        (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g)) := by omega
  have lower := Nat.mul_le_mul_left (2 ^ ((n+1)/2)) one
  simp only [Nat.mul_one] at lower
  omega

/-- Stability at a fixed scale, with the budget controlled by depth rather than scale. -/
theorem fixed_scale_small_background_stable (S : OddScale) (n B : Nat)
    (large : 33 ≤ S.ell) (deep : 4*B < 2 ^ ((n+1)/2))
    (g : W S n) (small : HammingWeight g ≤ B) :
    BDL26AllDepthBottomComparisonStability.SingleFlipStable S n
      (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g) :=
  BDL26AllDepthBottomComparisonStability.source_scale_single_flip_stable S n large _
    (small_background_first_zero S n B deep g small)

/-- An explicit even suffix depth works for every finite response budget. -/
def budgetDepth (B : Nat) : Nat := 2*(4*B+1)

theorem budgetDepth_rx_count (B : Nat) : (budgetDepth B+1)/2=4*B+1 := by
  unfold budgetDepth
  omega

theorem budgetDepth_source_even (B : Nat) :
    budgetDepth B+2=2*(4*B+2) ∧ 0 < budgetDepth B := by
  unfold budgetDepth
  omega

private theorem nat_lt_two_pow (k : Nat) : k < 2^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      have positive : 0 < 2^k := pow_pos (by decide) _
      omega

theorem budgetDepth_deep (B : Nat) : 4*B < 2 ^ ((budgetDepth B+1)/2) := by
  rw [budgetDepth_rx_count]
  have h := nat_lt_two_pow (4*B+1)
  omega

/-- At a fixed scale, a real canonical-generator prefix forces response weight
larger than ANY proposed depth-independent finite budget. Both full comparison
correction calls remain in the residual and in the restriction comparator. -/
theorem fixed_scale_no_bounded_response (S : OddScale) (large : 33 ≤ S.ell) (B : Nat) :
    ∃ (P : Finset (Q S (budgetDepth B))) (q : Q S (budgetDepth B)),
      P ⊆ hammingSupport (logicalError S (budgetDepth B)) ∧
      q ∈ hammingSupport (logicalError S (budgetDepth B)) ∧ q ∉ P ∧
      let g := backgroundRestriction S (budgetDepth B) (logicalError S (budgetDepth B)) P
      B < HammingWeight g ∧ g ≠ 0 ∧
      canonicalBasisWord (F:=BDL26Field) q ≠ (0 : W S (budgetDepth B)) ∧
      BDL26AllDepthBottomComparisonStability.residual S (budgetDepth B)
        (perturbTop S (budgetDepth B)
          (BDL26NonzeroBackgroundComparisonStability.zeroInput S (budgetDepth B)) g)
        (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S (budgetDepth B) ∧
      ∀ A : Finset (Q S (budgetDepth B)),
        HammingWeight (backgroundRestriction S (budgetDepth B) g A) ≤ B →
        BDL26AllDepthBottomComparisonStability.residual S (budgetDepth B)
          (perturbTop S (budgetDepth B)
            (BDL26NonzeroBackgroundComparisonStability.zeroInput S (budgetDepth B)) g)
          (canonicalBasisWord (F:=BDL26Field) q)-
        BDL26AllDepthBottomComparisonStability.residual S (budgetDepth B)
          (perturbTop S (budgetDepth B)
            (BDL26NonzeroBackgroundComparisonStability.zeroInput S (budgetDepth B))
            (backgroundRestriction S (budgetDepth B) g A))
          (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S (budgetDepth B) := by
  let n := budgetDepth B
  let sigma := BDL26NonzeroBackgroundComparisonStability.zeroInput S n
  obtain ⟨P,q,hP,hq,hn,bad⟩ := exists_bad_prefix S n sigma
  let g := backgroundRestriction S n (logicalError S n) P
  have deep : 4*B < 2^((n+1)/2) := budgetDepth_deep B
  have heavy : B < HammingWeight g := by
    by_contra small
    exact bad (fixed_scale_small_background_stable S n B large deep g (by omega) q)
  have nonzero : g ≠ 0 := by
    intro zero
    rw [zero,HammingWeight_zero] at heavy
    omega
  have flip : canonicalBasisWord (F:=BDL26Field) q ≠ (0 : W S n) := by
    intro zero
    have impossible : (1 : BDL26Field)=0 := by
      simpa [canonicalBasisWord] using congrFun zero q
    exact one_ne_zero impossible
  refine ⟨P,q,hP,hq,hn,heavy,nonzero,flip,bad,?_⟩
  intro A small sameclass
  have safe := fixed_scale_small_background_stable S n B large deep
    (backgroundRestriction S n g A) small q
  apply bad
  have sum := (boundaries S n).add_mem sameclass safe
  simpa only [n,g,sigma,sub_add_cancel] using sum


/-- Literal restriction cannot have more nonzero coordinates than its mask. -/
theorem restriction_weight_le_card (S : OddScale) (n : Nat)
    (g : W S n) (A : Finset (Q S n)) :
    HammingWeight (backgroundRestriction S n g A) ≤ A.card := by
  rw [HammingWeight_eq_card_hammingSupport]
  apply Finset.card_le_card
  intro q hq
  by_contra outside
  have zero : backgroundRestriction S n g A q=0 := by
    simp [backgroundRestriction,BDL26NonzeroBackgroundComparisonStability.partialWord,outside]
  exact (Finset.mem_filter.mp hq).2 zero

/-- Every adaptive selector of uniformly bounded coordinate sets fails, including
selectors depending on the whole background and on the actual flipped coordinate.
No graph or geometric radius assumption supplies the conclusion. -/
theorem bounded_selector_fails (S : OddScale) (large : 33 ≤ S.ell) (B : Nat)
    (response : ∀ n : Nat, W S n → Q S n → Finset (Q S n))
    (bounded : ∀ (n : Nat) (g : W S n) (q : Q S n), (response n g q).card ≤ B) :
    ∃ (g : W S (budgetDepth B)) (q : Q S (budgetDepth B)),
      B < HammingWeight g ∧ g ≠ 0 ∧
      canonicalBasisWord (F:=BDL26Field) q ≠ (0 : W S (budgetDepth B)) ∧
      BDL26AllDepthBottomComparisonStability.residual S (budgetDepth B)
        (perturbTop S (budgetDepth B)
          (BDL26NonzeroBackgroundComparisonStability.zeroInput S (budgetDepth B)) g)
        (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S (budgetDepth B) ∧
      BDL26AllDepthBottomComparisonStability.residual S (budgetDepth B)
        (perturbTop S (budgetDepth B)
          (BDL26NonzeroBackgroundComparisonStability.zeroInput S (budgetDepth B)) g)
        (canonicalBasisWord (F:=BDL26Field) q)-
      BDL26AllDepthBottomComparisonStability.residual S (budgetDepth B)
        (perturbTop S (budgetDepth B)
          (BDL26NonzeroBackgroundComparisonStability.zeroInput S (budgetDepth B))
          (backgroundRestriction S (budgetDepth B) g (response (budgetDepth B) g q)))
        (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S (budgetDepth B) := by
  obtain ⟨P,q,hP,hq,hn,heavy,nonzero,flip,bad,exclude⟩ :=
    fixed_scale_no_bounded_response S large B
  let g := backgroundRestriction S (budgetDepth B) (logicalError S (budgetDepth B)) P
  refine ⟨g,q,heavy,nonzero,flip,bad,?_⟩
  exact exclude (response (budgetDepth B) g q)
    ((restriction_weight_le_card S (budgetDepth B) g _).trans (bounded (budgetDepth B) g q))

end QEC.Coding.BDL26LocalBackgroundComparisonDepth
