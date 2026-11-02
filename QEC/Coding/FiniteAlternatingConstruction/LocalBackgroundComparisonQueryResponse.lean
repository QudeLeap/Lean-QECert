import QEC.Coding.FiniteAlternatingConstruction.PairedHistoryQueryCone
import QEC.Coding.FiniteAlternatingConstruction.LocalBackgroundComparisonDepth

/-!
# Literal physical query footprints preserve complete comparison responses

The footprint is the nonzero-column pullback of the constructed paired
history queries. It is allowed to grow with the depth and the selected
history. No graph-radius conclusion, witness-count estimate or probabilistic
bound is asserted here.
-/
noncomputable section
namespace QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26RZMap1CoordinateBridge
open BDL26HistoryLogicalResidual (suffix_delta1)
open BDL26LocalBackgroundComparisonResponse BDL26PairedHistoryQueryCone
open MultiscaleDecoder
open scoped Classical BigOperators

variable (S : OddScale) (n : Nat)

/-- The actual nonzero entries of one row of the physical differential. -/
def physicalRow (z : Coordinates S n (TopIndex n)) : Finset (Q S n) :=
  Finset.univ.filter fun q =>
    (SuffixData S n).family.coboundary1 (TopIndex n)
      (canonicalBasisWord (F:=BDL26Field) q) z ≠ 0

/-- Query pullback is by the real differential, not a graph enlargement. -/
def physicalPullback (A : Finset (Coordinates S n (TopIndex n))) : Finset (Q S n) :=
  A.biUnion (physicalRow S n)

theorem physicalRow_eq_incidence (z : Coordinates S n (TopIndex n)) :
    physicalRow S n z = Finset.univ.filter (fun q : Q S n =>
      (state S (n+2)).presentation.qz q z = true) := by
  ext q
  simp only [physicalRow,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [suffix_delta1,tannerCoboundary1_canonicalBasis_apply]
  by_cases h : (state S (n+2)).presentation.qz q z = true
  · simp [h]
  · simp [h]

theorem physicalRow_card (z : Coordinates S n (TopIndex n)) :
    (physicalRow S n z).card ≤ 7 := by
  rw [physicalRow_eq_incidence]
  have h := (BDL26BoundedValence.state_boundedValence S (n+2)).2.1 z
  have hcard : BDL26BoundedValence.zDegree (state S (n+2)).presentation z =
      (Finset.univ.filter (fun q : Q S n => (state S (n+2)).presentation.qz q z = true)).card := by
    unfold BDL26BoundedValence.zDegree
    apply Fintype.card_of_subtype
    intro q
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact hcard.symm.trans_le h

theorem physicalPullback_card (A : Finset (Coordinates S n (TopIndex n))) :
    (physicalPullback S n A).card ≤ 7*A.card := by
  exact (Finset.card_biUnion_le_card_mul A _ 7
    (fun z _ => physicalRow_card S n z)).trans_eq (Nat.mul_comm _ _)

private theorem basis_expansion (g : W S n) :
    g = ∑ q, g q • canonicalBasisWord (F:=BDL26Field) q := by
  funext p
  simp [canonicalBasisWord,Pi.single_apply,Finset.sum_apply,eq_comm]

/-- Literal restriction preserves every requested syndrome coordinate. -/
theorem pullback_agreement (g : W S n) (A : Finset (Coordinates S n (TopIndex n))) :
    AgreeOn A ((SuffixData S n).family.coboundary1 (TopIndex n) g)
      ((SuffixData S n).family.coboundary1 (TopIndex n)
        (backgroundRestriction S n g (physicalPullback S n A))) := by
  intro z hz
  conv_lhs => rw [basis_expansion S n g]
  conv_rhs => rw [basis_expansion S n (backgroundRestriction S n g (physicalPullback S n A))]
  rw [map_sum,map_sum,Finset.sum_apply,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_smul,map_smul]
  by_cases hq : q ∈ physicalPullback S n A
  · simp only [backgroundRestriction,BDL26NonzeroBackgroundComparisonStability.partialWord,if_pos hq]
  · have hc : (SuffixData S n).family.coboundary1 (TopIndex n)
        (canonicalBasisWord (F:=BDL26Field) q) z = 0 := by
      by_contra hn
      exact hq (Finset.mem_biUnion.mpr ⟨z,hz,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩⟩)
    change g q * _ = backgroundRestriction S n g (physicalPullback S n A) q * _
    rw [hc,mul_zero,mul_zero]

theorem background_top_agreement (sigma0 : TopInput S n) (g : W S n)
    (A : Finset (Coordinates S n (TopIndex n))) :
    AgreeOn A (perturbTop S n sigma0 g).val
      (perturbTop S n sigma0 (backgroundRestriction S n g (physicalPullback S n A))).val := by
  intro z hz
  exact congrArg (fun t => sigma0.val z+t) (pullback_agreement S n g A z hz)

theorem flip_preserves_agreement (A : Finset (Coordinates S n (TopIndex n)))
    (s t : TopInput S n) (e : W S n) (ha : AgreeOn A s.val t.val) :
    AgreeOn A (perturbTop S n s e).val (perturbTop S n t e).val := by
  intro z hz
  exact congrArg (fun u => u+(SuffixData S n).family.coboundary1 (TopIndex n) e z) (ha z hz)

/-- A stopping-level choice is made solely from the original paired run. -/
def queryStop (sigma0 : TopInput S n) (g e : W S n) : LevelIndex n :=
  stoppingLevel S n (perturbTop S n sigma0 g) e

def topQueries (sigma0 : TopInput S n) (g e : W S n) :
    Finset (Coordinates S n (TopIndex n)) :=
  queries S n e (queryStop S n sigma0 g e) (TopIndex n)

/-- The actual variable-size physical mask constructed from both histories. -/
def queryMask (sigma0 : TopInput S n) (g e : W S n) : Finset (Q S n) :=
  physicalPullback S n (topQueries S n sigma0 g e)

/-- Full paired correction equality; both genuine C2 calls are retained. -/
theorem full_pair_replay (s t : TopInput S n) (e : W S n)
    (a : LevelIndex n)
    (hstop : a.val = 0 ∨ actualInputs S n s a = actualInputs S n (perturbTop S n s e) a)
    (ha : AgreeOn (queries S n e a (TopIndex n)) s.val t.val) :
    BDL26AllDepthBottomComparisonStability.correction S n s +
        BDL26AllDepthBottomComparisonStability.correction S n (perturbTop S n s e) =
      BDL26AllDepthBottomComparisonStability.correction S n t +
        BDL26AllDepthBottomComparisonStability.correction S n (perturbTop S n t e) := by
  have hb := flip_preserves_agreement S n _ s t e ha
  have hsuffix : 0 < a.val →
      (actualInputs S n s a = actualInputs S n (perturbTop S n s e) a ∧
        actualInputs S n t a = actualInputs S n (perturbTop S n t e) a) := by
    intro hp
    have hs := hstop.resolve_left (by omega)
    exact ⟨hs,stopping_replay S n e a hp s t hs ha hb⟩
  have hstep : ∀ i : StepIndex n, (actualOutput S n s i).correction +
        (actualOutput S n (perturbTop S n s e) i).correction =
      (actualOutput S n t i).correction +
        (actualOutput S n (perturbTop S n t e) i).correction := by
    intro i
    by_cases hi : a.val ≤ i.val
    · exact paired_step_replay S n e a s t ha hb i hi
    · have hp : 0 < a.val := by omega
      rw [coalesced_output_pair_zero S n s e a (hsuffix hp).1 i (by omega),
        coalesced_output_pair_zero S n t e a (hsuffix hp).2 i (by omega)]
  have hsum := interval_pair_replay S n s (perturbTop S n s e)
    t (perturbTop S n t e) 0 (TopIndex n) (Nat.zero_le _)
      (fun i _ _ => hstep i)
  have hbase : BDL26AllDepthBottomComparisonStability.baseComparison S n s +
        BDL26AllDepthBottomComparisonStability.baseComparison S n (perturbTop S n s e) =
      BDL26AllDepthBottomComparisonStability.baseComparison S n t +
        BDL26AllDepthBottomComparisonStability.baseComparison S n (perturbTop S n t e) := by
    by_cases hz : a.val = 0
    · have haz : a = 0 := Fin.ext hz
      subst a
      have hq : queries S n e (0 : LevelIndex n) 0 = Finset.univ := by
        rw [queries_self,querySeed]
        exact if_pos hz
      have hleft : actualInputs S n s 0 = actualInputs S n t 0 := by
        apply Subtype.ext
        funext p
        exact query_agreement S n e 0 s t ha 0 (Nat.le_refl _) p (by rw [hq]; simp)
      have hright : actualInputs S n (perturbTop S n s e) 0 =
          actualInputs S n (perturbTop S n t e) 0 := by
        apply Subtype.ext
        funext p
        exact query_agreement S n e 0 _ _ hb 0 (Nat.le_refl _) p (by rw [hq]; simp)
      unfold BDL26AllDepthBottomComparisonStability.baseComparison
        BDL26AllDepthBottomComparisonStability.baseReadout
      rw [hleft,hright]
    · have hp : 0 < a.val := by omega
      have hleft := inputs_eq_below S n s (perturbTop S n s e) a 0 (Nat.zero_le _) (hsuffix hp).1
      have hright := inputs_eq_below S n t (perturbTop S n t e) a 0 (Nat.zero_le _) (hsuffix hp).2
      unfold BDL26AllDepthBottomComparisonStability.baseComparison
        BDL26AllDepthBottomComparisonStability.baseReadout
      rw [hleft,hright,binary_word_add_self,binary_word_add_self]
  simp_rw [BDL26AllDepthBottomComparisonStability.correction_above]
  calc
    _ = (correctionIntervalSum S n s 0 (TopIndex n) +
        correctionIntervalSum S n (perturbTop S n s e) 0 (TopIndex n)) +
        intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
          (BDL26AllDepthBottomComparisonStability.baseComparison S n s +
            BDL26AllDepthBottomComparisonStability.baseComparison S n (perturbTop S n s e)) := by
          rw [map_add]; abel
    _ = (correctionIntervalSum S n t 0 (TopIndex n) +
        correctionIntervalSum S n (perturbTop S n t e) 0 (TopIndex n)) +
        intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
          (BDL26AllDepthBottomComparisonStability.baseComparison S n t +
            BDL26AllDepthBottomComparisonStability.baseComparison S n (perturbTop S n t e)) := by
          rw [hsum,hbase]
    _ = _ := by rw [map_add]; abel

/-- Literal full-word replay for every valid seed and physical background. -/
theorem residual_restriction (sigma0 : TopInput S n) (g e : W S n) :
    BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 g) e =
      BDL26AllDepthBottomComparisonStability.residual S n
        (perturbTop S n sigma0 (backgroundRestriction S n g (queryMask S n sigma0 g e))) e := by
  let s := perturbTop S n sigma0 g
  let a := queryStop S n sigma0 g e
  let t := perturbTop S n sigma0 (backgroundRestriction S n g (queryMask S n sigma0 g e))
  have hstop : a.val = 0 ∨ actualInputs S n s a = actualInputs S n (perturbTop S n s e) a := by
    by_cases hz : a.val = 0
    · exact Or.inl hz
    · exact Or.inr (stoppingLevel_coalesces S n s e (by change 0 < a.val; omega))
  have ha : AgreeOn (queries S n e a (TopIndex n)) s.val t.val :=
    background_top_agreement S n sigma0 g (topQueries S n sigma0 g e)
  have hc := full_pair_replay S n s t e a hstop ha
  unfold BDL26AllDepthBottomComparisonStability.residual
  calc
    _ = e+(BDL26AllDepthBottomComparisonStability.correction S n s+
      BDL26AllDepthBottomComparisonStability.correction S n (perturbTop S n s e)) := by abel
    _ = e+(BDL26AllDepthBottomComparisonStability.correction S n t+
      BDL26AllDepthBottomComparisonStability.correction S n (perturbTop S n t e)) := by rw [hc]
    _ = _ := by abel

theorem nonboundary_restriction (sigma0 : TopInput S n) (g : W S n) (q : Q S n)
    (bad : BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 g)
      (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n) :
    BDL26AllDepthBottomComparisonStability.residual S n
      (perturbTop S n sigma0 (backgroundRestriction S n g
        (queryMask S n sigma0 g (canonicalBasisWord (F:=BDL26Field) q))))
      (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n := by
  rwa [← residual_restriction S n sigma0 g (canonicalBasisWord (F:=BDL26Field) q)]

def occupiedQueries (sigma0 : TopInput S n) (g e : W S n) : Finset (Q S n) :=
  hammingSupport g ∩ queryMask S n sigma0 g e

theorem restriction_support (sigma0 : TopInput S n) (g e : W S n) :
    hammingSupport (backgroundRestriction S n g (queryMask S n sigma0 g e)) =
      occupiedQueries S n sigma0 g e := by
  ext q
  by_cases hq : q ∈ queryMask S n sigma0 g e
  · simp [occupiedQueries,hammingSupport,backgroundRestriction,
      BDL26NonzeroBackgroundComparisonStability.partialWord,hq]
  · simp [occupiedQueries,hammingSupport,backgroundRestriction,
      BDL26NonzeroBackgroundComparisonStability.partialWord,hq]

theorem failure_occupied_weight (B : Nat) (large : 33 ≤ S.ell)
    (deep : 4*B < 2^((n+1)/2)) (g : W S n) (q : Q S n)
    (bad : BDL26AllDepthBottomComparisonStability.residual S n
      (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g)
      (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n) :
    B < HammingWeight (backgroundRestriction S n g
      (queryMask S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g
        (canonicalBasisWord (F:=BDL26Field) q))) := by
  by_contra hn
  have hsmall : HammingWeight (backgroundRestriction S n g
      (queryMask S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g
        (canonicalBasisWord (F:=BDL26Field) q))) ≤ B := by omega
  exact nonboundary_restriction S n _ g q bad
    (BDL26LocalBackgroundComparisonDepth.fixed_scale_small_background_stable S n B large deep
      _ hsmall q)

theorem failure_occupied_card (B : Nat) (large : 33 ≤ S.ell)
    (deep : 4*B < 2^((n+1)/2)) (g : W S n) (q : Q S n)
    (bad : BDL26AllDepthBottomComparisonStability.residual S n
      (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g)
      (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n) :
    B < (occupiedQueries S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n)
      g (canonicalBasisWord (F:=BDL26Field) q)).card := by
  have h := failure_occupied_weight S n B large deep g q bad
  rwa [HammingWeight_eq_card_hammingSupport,restriction_support] at h

theorem failure_occupied_nonempty (large : 33 ≤ S.ell) (g : W S n) (q : Q S n)
    (bad : BDL26AllDepthBottomComparisonStability.residual S n
      (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g)
      (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n) :
    (occupiedQueries S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n)
      g (canonicalBasisWord (F:=BDL26Field) q)).Nonempty := by
  apply Finset.card_pos.mp
  exact failure_occupied_card S n 0 large (by positivity) g q bad

theorem queryMask_recursive_card (sigma0 : TopInput S n) (g e : W S n) :
    (queryMask S n sigma0 g e).card ≤ 7 * budgetPrefix S n e
      (queryStop S n sigma0 g e) n (Nat.le_refl _) := by
  exact (physicalPullback_card S n (topQueries S n sigma0 g e)).trans
    (Nat.mul_le_mul_left 7 (queries_card_budget S n e _ (TopIndex n)))

theorem queryMask_window_card (sigma0 : TopInput S n) (g e : W S n)
    (L w : Nat) (hstop : 0 < (queryStop S n sigma0 g e).val)
    (hlen : n-(queryStop S n sigma0 g e).val ≤ L)
    (hw : HammingWeight ((SuffixData S n).family.coboundary1 (TopIndex n) e) ≤ w) :
    (queryMask S n sigma0 g e).card ≤ 7*windowBudget S L w := by
  exact (physicalPullback_card S n (topQueries S n sigma0 g e)).trans
    (Nat.mul_le_mul_left 7 (queries_window_card S n e _ hstop L w hw hlen))

theorem basis_syndrome_weight (q : Q S n) :
    HammingWeight ((SuffixData S n).family.coboundary1 (TopIndex n)
      (canonicalBasisWord (F:=BDL26Field) q)) ≤ 4 := by
  rw [suffix_delta1,BDL26UniformHistoryObstruction.basis_coboundary_weight]
  exact ((BDL26BoundedValence.state_boundedValence S (n+2)).2.2 q).2.1

theorem basis_syndrome_nonzero (q : Q S n) :
    (SuffixData S n).family.coboundary1 (TopIndex n)
      (canonicalBasisWord (F:=BDL26Field) q) ≠ 0 := by
  let z := ((state S (n+2)).admissible.toTannerSquareAdmissible.qzRoot q).val
  have hi : (state S (n+2)).presentation.qz q z = true :=
    ((state S (n+2)).admissible.toTannerSquareAdmissible.qzRoot q).property
  intro hz
  have hv := congrFun hz z
  rw [suffix_delta1,tannerCoboundary1_canonicalBasis_apply,if_pos hi] at hv
  exact one_ne_zero hv

theorem basis_nonzero (q : Q S n) :
    canonicalBasisWord (F:=BDL26Field) q ≠ (0 : W S n) := by
  intro he
  have hq := congrFun he q
  simpa [canonicalBasisWord] using hq

theorem zero_input_below (s : TopInput S n) (hs : s.val = 0) (a : LevelIndex n) :
    (actualInputs S n s a).val = 0 := by
  have hc := actual_interval_contraction S n s a (TopIndex n) (Nat.le_of_lt_succ a.isLt)
  rw [actualInputs_top,hs,HammingWeight_zero] at hc
  apply (HammingWeight_eq_zero_iff _).mp
  have hp : 0 < 2 ^ rxCount a.val n := by positivity
  nlinarith

/-- The upper five-step window of an odd-depth actual history contains
three RX contractions. A genuine basis background and the same flip therefore
coalesce strictly above C2; the initial syndrome is separately proved nonzero. -/
theorem five_step_coalescence (hn : 7 ≤ n) (odd : n % 2 = 1) (q : Q S n) :
    actualInputs S n
      (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n)
        (canonicalBasisWord (F:=BDL26Field) q)) ⟨n-5,by omega⟩ =
    actualInputs S n
      (perturbTop S n
        (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n)
          (canonicalBasisWord (F:=BDL26Field) q))
        (canonicalBasisWord (F:=BDL26Field) q)) ⟨n-5,by omega⟩ := by
  let e : W S n := canonicalBasisWord (F:=BDL26Field) q
  let s := perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) e
  let a : LevelIndex n := ⟨n-5,by omega⟩
  have hc := actual_interval_contraction S n s a (TopIndex n) (by dsimp [a]; omega)
  have hr : rxCount a.val n = 3 := by
    rw [rxCount_formula _ _ (by dsimp [a]; omega)]
    dsimp [a]
    omega
  have ht : s.val = (SuffixData S n).family.coboundary1 (TopIndex n) e := by
    change 0+_=_
    exact zero_add _
  rw [actualInputs_top,ht,hr] at hc
  change 8 * HammingWeight (actualInputs S n s a).val ≤
    HammingWeight ((SuffixData S n).family.coboundary1 (TopIndex n) e) at hc
  have hw : 8 * HammingWeight (actualInputs S n s a).val ≤ 4 :=
    hc.trans (basis_syndrome_weight S n q)
  have hweight : HammingWeight (actualInputs S n s a).val = 0 := by omega
  have hz : (actualInputs S n s a).val = 0 := by
    exact (HammingWeight_eq_zero_iff _).mp hweight
  have hflip : (perturbTop S n s e).val = 0 := by
    change s.val+(SuffixData S n).family.coboundary1 (TopIndex n) e=0
    rw [ht,binary_word_add_self]
  apply Subtype.ext
  exact hz.trans (zero_input_below S n (perturbTop S n s e) hflip a).symm

def fiveStepPhysicalBudget (S : OddScale) : Nat := 7 * windowBudget S 5 4

theorem basis_query_five_window (hn : 7 ≤ n) (odd : n % 2 = 1) (q : Q S n) :
    let zero := BDL26NonzeroBackgroundComparisonStability.zeroInput S n
    let e : W S n := canonicalBasisWord (F:=BDL26Field) q
    0 < (queryStop S n zero e e).val ∧
      n-(queryStop S n zero e e).val ≤ 5 ∧
      (queryMask S n zero e e).card ≤ fiveStepPhysicalBudget S := by
  let zero := BDL26NonzeroBackgroundComparisonStability.zeroInput S n
  let e : W S n := canonicalBasisWord (F:=BDL26Field) q
  have hc := le_stoppingLevel S n (perturbTop S n zero e) e ⟨n-5,by omega⟩
    (five_step_coalescence S n hn odd q)
  have hl : n-5 ≤ (queryStop S n zero e e).val := hc
  have hp : 0 < (queryStop S n zero e e).val := by omega
  have hw : n-(queryStop S n zero e e).val ≤ 5 := by omega
  exact ⟨hp,hw,queryMask_window_card S n zero e e 5 4 hp hw (basis_syndrome_weight S n q)⟩

theorem basis_query_proper (hn : 7 ≤ n) (odd : n % 2 = 1)
    (large : fiveStepPhysicalBudget S < 5*2^(n+2)) (q : Q S n) :
    queryMask S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n)
      (canonicalBasisWord (F:=BDL26Field) q) (canonicalBasisWord (F:=BDL26Field) q) ≠ Finset.univ := by
  intro hall
  have hb := (basis_query_five_window S n hn odd q).2.2
  rw [hall,Finset.card_univ] at hb
  have lower : 5*2^(n+2) ≤ Fintype.card (Q S n) :=
    BDL26QuantitativeBounds.state_qubit_card_lower S (n+2)
  omega

private theorem nat_lt_two_pow (k : Nat) : k < 2^k := by
  induction k with
  | zero => norm_num
  | succ k ih => rw [pow_succ]; omega

/-- The numerical witness is chosen before it becomes a recursive code index.
Its elimination leaves n abstract when constructing the physical coordinate. -/
private theorem exists_large_odd_depth (C lowerDepth : Nat) :
    ∃ n : Nat, lowerDepth ≤ n ∧ 7 ≤ n ∧ n%2=1 ∧ C < 5*2^(n+2) := by
  let n := 2*(C+lowerDepth+1)+7
  have hpow : C < 2^(n+2) :=
    (nat_lt_two_pow C).trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [n]; omega))
  refine ⟨n,?_,?_,?_,?_⟩
  · dsimp [n]
    omega
  · dsimp [n]
    omega
  · dsimp [n]
    omega
  · omega

/-- At every scale, arbitrarily deep actual nonzero basis pairs have a proper
physical footprint whose budget depends only on the five-step window and S.
This is an existence theorem about the constructed queryMask, not a supplied
coalescence or properness certificate. -/
theorem arbitrarily_deep_proper_queries (lowerDepth : Nat) :
    ∃ n : Nat, lowerDepth ≤ n ∧ 7 ≤ n ∧ n % 2 = 1 ∧
      ∃ q : Q S n,
        let zero := BDL26NonzeroBackgroundComparisonStability.zeroInput S n
        let e : W S n := canonicalBasisWord (F:=BDL26Field) q
        e ≠ 0 ∧ (SuffixData S n).family.coboundary1 (TopIndex n) e ≠ 0 ∧
        0 < (queryStop S n zero e e).val ∧
        n-(queryStop S n zero e e).val ≤ 5 ∧
        (queryMask S n zero e e).card ≤ fiveStepPhysicalBudget S ∧
        queryMask S n zero e e ≠ Finset.univ ∧
        BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n zero e) e =
          BDL26AllDepthBottomComparisonStability.residual S n
            (perturbTop S n zero (backgroundRestriction S n e (queryMask S n zero e e))) e := by
  obtain ⟨n,hdepth,hn,hodd,hlarge⟩ := exists_large_odd_depth (fiveStepPhysicalBudget S) lowerDepth
  have hcard : 0 < Fintype.card (Q S n) := by
    have lower := BDL26QuantitativeBounds.state_qubit_card_lower S (n+2)
    have hp : 0 < 5*2^(n+2) := by positivity
    exact hp.trans_le lower
  let q : Q S n := Classical.choice (Fintype.card_pos_iff.mp hcard)
  have hw := basis_query_five_window S n hn hodd q
  exact ⟨n,hdepth,hn,hodd,q,basis_nonzero S n q,
    basis_syndrome_nonzero S n q,hw.1,hw.2.1,hw.2.2,
    basis_query_proper S n hn hodd hlarge q,residual_restriction S n _ _ _⟩

end QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
