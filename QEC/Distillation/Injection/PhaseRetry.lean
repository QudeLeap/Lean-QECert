import Mathlib.Probability.Distributions.Uniform

/-!
# Finite cyclic phase retry

The phase-injection retry argument from BK05 is a finite symmetric walk on the
cyclic exponent groups of orders eight and twelve.  This module deliberately
contains only that classical finite mathematics: it neither assumes nor
implements a quantum circuit.
-/

namespace QEC
namespace Distillation
namespace PhaseRetry

noncomputable section

/-- The exponent increment selected by one known fair retry outcome. -/
def signedIncrement (coin : Bool) {q : Nat} : ZMod q :=
  if coin then 1 else -1

/-- The successive cyclic exponents, including the initial exponent. -/
def positions {q : Nat} (start : ZMod q) : List Bool → List (ZMod q)
  | [] => [start]
  | coin :: coins => start :: positions (start + signedIncrement coin) coins

/-- The cyclic exponent after every outcome in a finite retry history. -/
def endpoint {q : Nat} (start : ZMod q) : List Bool → ZMod q
  | [] => start
  | coin :: coins => endpoint (start + signedIncrement coin) coins

/-- A finite retry trace has reached the required cyclic exponent. -/
def visitsTarget {q : Nat} (start target : ZMod q) (coins : List Bool) : Prop :=
  target ∈ positions start coins

/-- A target reached in a prefix remains reached after further retry outcomes. -/
theorem visitsTarget_append_left {q : Nat} {start target : ZMod q}
    (history suffix : List Bool)
    (h : visitsTarget start target history) :
    visitsTarget start target (history ++ suffix) := by
  induction history generalizing start with
  | nil =>
      unfold visitsTarget at h ⊢
      change target ∈ [start] at h
      change target ∈ positions start suffix
      rw [List.mem_singleton] at h
      subst target
      induction suffix with
      | nil => simp [positions]
      | cons coin tail ih => simp [positions]
  | cons coin tail ih =>
      unfold visitsTarget at h ⊢
      change target ∈ start :: positions (start + signedIncrement coin) tail at h
      change target ∈ start :: positions (start + signedIncrement coin) (tail ++ suffix)
      simp only [List.mem_cons] at h ⊢
      exact h.elim Or.inl (fun h' => Or.inr (ih h'))

/-- A target reached after a retry suffix is reached in the whole trace. -/
theorem visitsTarget_append_right {q : Nat} {start target : ZMod q}
    (history suffix : List Bool)
    (h : visitsTarget (endpoint start history) target suffix) :
    visitsTarget start target (history ++ suffix) := by
  induction history generalizing start with
  | nil => simpa [endpoint] using h
  | cons coin tail ih =>
      unfold visitsTarget at h ⊢
      change target ∈ start :: positions (start + signedIncrement coin) (tail ++ suffix)
      simp only [List.mem_cons]
      apply Or.inr
      exact ih (by simpa only [visitsTarget, endpoint] using h)

/-- The length-`q` outcome block in which every step increments the exponent. -/
def positiveBlock (q : Nat) : List Bool :=
  List.replicate q true

/-- The `2 ^ q` possible fair outcome strings in one `q`-step retry block. -/
abbrev CoinBlock (q : Nat) := Fin q → Bool

/-- The unique all-positive outcome block. -/
def allPositiveBlock (q : Nat) : CoinBlock q := fun _ => true

/-- The ordered coin list represented by a finite outcome block. -/
def blockCoins {q : Nat} (block : CoinBlock q) : List Bool :=
  List.ofFn block

theorem blockCoins_allPositive (q : Nat) :
    blockCoins (allPositiveBlock q) = positiveBlock q := by
  exact List.ofFn_const q true

/-- A block is the deterministic all-positive certificate for target reachability. -/
def isPositiveBlock {q : Nat} (block : CoinBlock q) : Bool :=
  decide (block = allPositiveBlock q)

/-- One block which is not the all-positive target-reachability certificate. -/
abbrev NonpositiveBlock (q : Nat) := { block : CoinBlock q // isPositiveBlock block = false }

/-- Independent `q`-step blocks and their certificate-failure subspace. -/
abbrev BlockTrace (q blocks : Nat) := Fin blocks → CoinBlock q
abbrev NoPositiveTrace (q blocks : Nat) := Fin blocks → NonpositiveBlock q

/-- The exponent at the end of one finite outcome block. -/
def blockEndpoint {q : Nat} (start : ZMod q) (block : CoinBlock q) : ZMod q :=
  endpoint start (blockCoins block)

/--
The actual sequential target-visit event of a finite block trace.  It records
the target visit in the current block or recursively in the remaining blocks,
started from the concrete endpoint of the current block.
-/
def traceVisitsTarget {q : Nat} (start target : ZMod q) :
    (blocks : Nat) → BlockTrace q blocks → Prop
  | 0, _ => start = target
  | blocks + 1, trace =>
      visitsTarget start target (blockCoins (trace 0)) ∨
        traceVisitsTarget (blockEndpoint start (trace 0)) target blocks
          (fun index => trace index.succ)

/-- A uniformly sampled finite trace that has not actually visited its target. -/
abbrev TargetMissTrace (q blocks : Nat) (start target : ZMod q) :=
  { trace : BlockTrace q blocks // ¬ traceVisitsTarget start target blocks trace }

/-- The canonical finite enumeration of actual target-miss traces. -/
@[reducible] noncomputable def targetMissTraceFintype (q blocks : Nat) (start target : ZMod q) :
    Fintype (TargetMissTrace q blocks start target) :=
  Fintype.ofFinite _

/-- The exact finite-sample probability of an actual target miss. -/
noncomputable def targetMissProbability (q blocks : Nat) (start target : ZMod q) : Real :=
  @Fintype.card (TargetMissTrace q blocks start target)
    (targetMissTraceFintype q blocks start target) /
    Fintype.card (BlockTrace q blocks)

/-- On the order-eight (`-pi/4`) phase cycle, an all-positive block visits every target. -/
theorem positiveBlock_visits_target_eight (start target : ZMod 8) :
    visitsTarget start target (positiveBlock 8) := by
  change target ∈ positions start (positiveBlock 8)
  native_decide +revert

/-- On the order-twelve (`-pi/6`) phase cycle, an all-positive block visits every target. -/
theorem positiveBlock_visits_target_twelve (start target : ZMod 12) :
    visitsTarget start target (positiveBlock 12) := by
  change target ∈ positions start (positiveBlock 12)
  native_decide +revert

/-- A positive order-eight block reaches its target after every retry prefix. -/
theorem positiveBlock_suffix_visits_target_eight
    (start target : ZMod 8) (history : List Bool) :
    visitsTarget start target (history ++ positiveBlock 8) := by
  apply visitsTarget_append_right history (positiveBlock 8)
  exact positiveBlock_visits_target_eight (endpoint start history) target

/-- A positive order-twelve block reaches its target after every retry prefix. -/
theorem positiveBlock_suffix_visits_target_twelve
    (start target : ZMod 12) (history : List Bool) :
    visitsTarget start target (history ++ positiveBlock 12) := by
  apply visitsTarget_append_right history (positiveBlock 12)
  exact positiveBlock_visits_target_twelve (endpoint start history) target

/-- A positive block anywhere in an order-eight trace forces an actual target visit. -/
theorem traceVisitsTarget_of_positiveBlock_eight (start target : ZMod 8) :
    ∀ {blocks : Nat} (trace : BlockTrace 8 blocks) (index : Fin blocks),
      trace index = allPositiveBlock 8 → traceVisitsTarget start target blocks trace := by
  intro blocks
  induction blocks generalizing start with
  | zero =>
      intro trace index
      exact Fin.elim0 index
  | succ blocks ih =>
      intro trace index h
      simp only [traceVisitsTarget]
      revert h
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · intro h
        apply Or.inl
        rw [h, blockCoins_allPositive]
        exact positiveBlock_visits_target_eight start target
      · intro h
        apply Or.inr
        apply ih (start := blockEndpoint start (trace 0))
          (trace := fun inner => trace inner.succ) (index := tailIndex)
        simpa using h

/-- A positive block anywhere in an order-twelve trace forces an actual target visit. -/
theorem traceVisitsTarget_of_positiveBlock_twelve (start target : ZMod 12) :
    ∀ {blocks : Nat} (trace : BlockTrace 12 blocks) (index : Fin blocks),
      trace index = allPositiveBlock 12 → traceVisitsTarget start target blocks trace := by
  intro blocks
  induction blocks generalizing start with
  | zero =>
      intro trace index
      exact Fin.elim0 index
  | succ blocks ih =>
      intro trace index h
      simp only [traceVisitsTarget]
      revert h
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · intro h
        apply Or.inl
        rw [h, blockCoins_allPositive]
        exact positiveBlock_visits_target_twelve start target
      · intro h
        apply Or.inr
        apply ih (start := blockEndpoint start (trace 0))
          (trace := fun inner => trace inner.succ) (index := tailIndex)
        simpa using h

/-- A retry certificate reaches its target after every finite preceding history. -/
def FiniteCyclicRetryHitsTarget (q : Nat) (start target : ZMod q) : Prop :=
  ∀ history : List Bool, visitsTarget start target (history ++ positiveBlock q)

/-- Every order-eight cyclic retry certificate reaches its requested target. -/
theorem finiteCyclicRetry_eight_hits_target (start target : ZMod 8) :
    FiniteCyclicRetryHitsTarget 8 start target := by
  intro history
  exact positiveBlock_suffix_visits_target_eight start target history

/-- Every order-twelve cyclic retry certificate reaches its requested target. -/
theorem finiteCyclicRetry_twelve_hits_target (start target : ZMod 12) :
    FiniteCyclicRetryHitsTarget 12 start target := by
  intro history
  exact positiveBlock_suffix_visits_target_twelve start target history

/--
The probability that no length-`q` block is the all-positive certificate after
`blocks` independent blocks.  It is an explicit exponential upper bound on
the failure probability of a retry protocol: a certified all-positive block
already forces a target visit by the two finite theorems above.
-/
def certificateFailureTail (q blocks : Nat) : Real :=
  (1 - ((2 : Real)⁻¹) ^ q) ^ blocks

/--
The exact uniform finite-sample probability that every block misses the
all-positive certificate.  A target miss is bounded by this number, since a
positive block visits every target from every cyclic start state.
-/
def certificateFailureProbability (q blocks : Nat) : Real :=
  Fintype.card (NoPositiveTrace q blocks) /
    Fintype.card (BlockTrace q blocks)

/-- The exact finite-sample target-hit probability, complementing the actual miss event. -/
noncomputable def targetHitProbability (q blocks : Nat) (start target : ZMod q) : Real :=
  1 - targetMissProbability q blocks start target

theorem card_nonpositiveBlock_eight :
    Fintype.card (NonpositiveBlock 8) = 255 := by
  native_decide

theorem card_nonpositiveBlock_twelve :
    Fintype.card (NonpositiveBlock 12) = 4095 := by
  native_decide

theorem certificateFailureProbability_eight (blocks : Nat) :
    certificateFailureProbability 8 blocks = (255 / 256 : Real) ^ blocks := by
  have hBool : Fintype.card Bool = 2 := by native_decide
  simp only [certificateFailureProbability, Fintype.card_fun,
    Fintype.card_fin, card_nonpositiveBlock_eight]
  rw [div_pow]
  norm_num [hBool, Nat.cast_pow]

theorem certificateFailureProbability_twelve (blocks : Nat) :
    certificateFailureProbability 12 blocks = (4095 / 4096 : Real) ^ blocks := by
  have hBool : Fintype.card Bool = 2 := by native_decide
  simp only [certificateFailureProbability, Fintype.card_fun,
    Fintype.card_fin, card_nonpositiveBlock_twelve]
  rw [div_pow]
  norm_num [hBool, Nat.cast_pow]

/-- An actual order-eight target miss has no all-positive block, hence injects into it. -/
theorem targetMissCard_le_certificate_eight (start target : ZMod 8) (blocks : Nat) :
    @Fintype.card (TargetMissTrace 8 blocks start target)
      (targetMissTraceFintype 8 blocks start target) ≤
      Fintype.card (NoPositiveTrace 8 blocks) := by
  classical
  letI : Fintype (TargetMissTrace 8 blocks start target) :=
    targetMissTraceFintype 8 blocks start target
  let embed : TargetMissTrace 8 blocks start target → NoPositiveTrace 8 blocks :=
    fun missed index =>
      ⟨missed.val index, by
        apply Bool.eq_false_of_not_eq_true
        intro hPositive
        apply missed.property
        apply traceVisitsTarget_of_positiveBlock_eight start target missed.val index
        simpa [isPositiveBlock] using hPositive⟩
  apply Fintype.card_le_of_injective embed
  intro left right h
  apply Subtype.ext
  have hValues : (fun index => (embed left index).val) =
      (fun index => (embed right index).val) :=
    congrArg (fun certificate : NoPositiveTrace 8 blocks =>
      fun index => (certificate index).val) h
  simpa [embed] using hValues

/-- An actual order-twelve target miss has no all-positive block, hence injects into it. -/
theorem targetMissCard_le_certificate_twelve (start target : ZMod 12) (blocks : Nat) :
    @Fintype.card (TargetMissTrace 12 blocks start target)
      (targetMissTraceFintype 12 blocks start target) ≤
      Fintype.card (NoPositiveTrace 12 blocks) := by
  classical
  letI : Fintype (TargetMissTrace 12 blocks start target) :=
    targetMissTraceFintype 12 blocks start target
  let embed : TargetMissTrace 12 blocks start target → NoPositiveTrace 12 blocks :=
    fun missed index =>
      ⟨missed.val index, by
        apply Bool.eq_false_of_not_eq_true
        intro hPositive
        apply missed.property
        apply traceVisitsTarget_of_positiveBlock_twelve start target missed.val index
        simpa [isPositiveBlock] using hPositive⟩
  apply Fintype.card_le_of_injective embed
  intro left right h
  apply Subtype.ext
  have hValues : (fun index => (embed left index).val) =
      (fun index => (embed right index).val) :=
    congrArg (fun certificate : NoPositiveTrace 12 blocks =>
      fun index => (certificate index).val) h
  simpa [embed] using hValues

/-- The actual order-eight miss probability is bounded by the exact certificate tail. -/
theorem targetMissProbability_le_certificate_eight (start target : ZMod 8) (blocks : Nat) :
    targetMissProbability 8 blocks start target ≤ certificateFailureProbability 8 blocks := by
  unfold targetMissProbability certificateFailureProbability
  apply div_le_div_of_nonneg_right
  · exact_mod_cast targetMissCard_le_certificate_eight start target blocks
  · exact_mod_cast Nat.zero_le (Fintype.card (BlockTrace 8 blocks))

/-- The actual order-twelve miss probability is bounded by the exact certificate tail. -/
theorem targetMissProbability_le_certificate_twelve (start target : ZMod 12) (blocks : Nat) :
    targetMissProbability 12 blocks start target ≤ certificateFailureProbability 12 blocks := by
  unfold targetMissProbability certificateFailureProbability
  apply div_le_div_of_nonneg_right
  · exact_mod_cast targetMissCard_le_certificate_twelve start target blocks
  · exact_mod_cast Nat.zero_le (Fintype.card (BlockTrace 12 blocks))

/-- The actual order-eight target-miss probability has the explicit exponential bound. -/
theorem targetMissProbability_eight_exponential_bound
    (start target : ZMod 8) (blocks : Nat) :
    targetMissProbability 8 blocks start target ≤ (255 / 256 : Real) ^ blocks := by
  calc
    targetMissProbability 8 blocks start target ≤ certificateFailureProbability 8 blocks :=
      targetMissProbability_le_certificate_eight start target blocks
    _ = (255 / 256 : Real) ^ blocks := certificateFailureProbability_eight blocks

/-- The actual order-twelve target-miss probability has the explicit exponential bound. -/
theorem targetMissProbability_twelve_exponential_bound
    (start target : ZMod 12) (blocks : Nat) :
    targetMissProbability 12 blocks start target ≤ (4095 / 4096 : Real) ^ blocks := by
  calc
    targetMissProbability 12 blocks start target ≤ certificateFailureProbability 12 blocks :=
      targetMissProbability_le_certificate_twelve start target blocks
    _ = (4095 / 4096 : Real) ^ blocks := certificateFailureProbability_twelve blocks

/-- A failure tail tending to zero expresses probability-one eventual success. -/
def AlmostSureTargetHit (failure : Nat → Real) : Prop :=
  Filter.Tendsto failure Filter.atTop (nhds 0)

/-- Any nonnegative tail below a vanishing certificate tail also vanishes. -/
theorem almostSureTargetHit_of_le_certificateTail
    {q : Nat} {failure : Nat → Real}
    (hNonnegative : ∀ blocks, 0 ≤ failure blocks)
    (hBound : ∀ blocks, failure blocks ≤ certificateFailureTail q blocks)
    (hTail : AlmostSureTargetHit (certificateFailureTail q)) :
    AlmostSureTargetHit failure := by
  unfold AlmostSureTargetHit at hTail ⊢
  exact squeeze_zero hNonnegative hBound hTail

/-- The order-eight retry certificate has an exponential failure tail. -/
theorem certificateFailureTail_eight_tends_zero :
    AlmostSureTargetHit (certificateFailureTail 8) := by
  change Filter.Tendsto
    (fun blocks : Nat => (1 - ((2 : Real)⁻¹) ^ 8) ^ blocks)
    Filter.atTop (nhds 0)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The order-twelve retry certificate has an exponential failure tail. -/
theorem certificateFailureTail_twelve_tends_zero :
    AlmostSureTargetHit (certificateFailureTail 12) := by
  change Filter.Tendsto
    (fun blocks : Nat => (1 - ((2 : Real)⁻¹) ^ 12) ^ blocks)
    Filter.atTop (nhds 0)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The exact order-eight finite-sample certificate failure probability vanishes. -/
theorem certificateFailureProbability_eight_tends_zero :
    AlmostSureTargetHit (certificateFailureProbability 8) := by
  unfold AlmostSureTargetHit
  have h : certificateFailureProbability 8 = fun blocks => (255 / 256 : Real) ^ blocks := by
    funext blocks
    exact certificateFailureProbability_eight blocks
  rw [h]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : Real) ≤ 255 / 256)
    (by norm_num : (255 / 256 : Real) < 1)

/-- The exact order-twelve finite-sample certificate failure probability vanishes. -/
theorem certificateFailureProbability_twelve_tends_zero :
    AlmostSureTargetHit (certificateFailureProbability 12) := by
  unfold AlmostSureTargetHit
  have h : certificateFailureProbability 12 = fun blocks => (4095 / 4096 : Real) ^ blocks := by
    funext blocks
    exact certificateFailureProbability_twelve blocks
  rw [h]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : Real) ≤ 4095 / 4096)
    (by norm_num : (4095 / 4096 : Real) < 1)

/-- The actual order-eight target-miss probability tends to zero. -/
theorem targetMissProbability_eight_tends_zero (start target : ZMod 8) :
    AlmostSureTargetHit (fun blocks => targetMissProbability 8 blocks start target) := by
  apply almostSureTargetHit_of_le_certificateTail
  · intro blocks
    unfold targetMissProbability
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro blocks
    calc
      targetMissProbability 8 blocks start target ≤ certificateFailureProbability 8 blocks :=
        targetMissProbability_le_certificate_eight start target blocks
      _ = certificateFailureTail 8 blocks := by
        simp only [certificateFailureProbability_eight, certificateFailureTail]
        norm_num
  · exact certificateFailureTail_eight_tends_zero

/-- The actual order-twelve target-miss probability tends to zero. -/
theorem targetMissProbability_twelve_tends_zero (start target : ZMod 12) :
    AlmostSureTargetHit (fun blocks => targetMissProbability 12 blocks start target) := by
  apply almostSureTargetHit_of_le_certificateTail
  · intro blocks
    unfold targetMissProbability
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro blocks
    calc
      targetMissProbability 12 blocks start target ≤ certificateFailureProbability 12 blocks :=
        targetMissProbability_le_certificate_twelve start target blocks
      _ = certificateFailureTail 12 blocks := by
        simp only [certificateFailureProbability_twelve, certificateFailureTail]
        norm_num
  · exact certificateFailureTail_twelve_tends_zero

/-- The actual order-eight finite retry walk hits every target with probability one. -/
theorem finiteCyclicRetry_eight_target_hit_probability_one (start target : ZMod 8) :
    Filter.Tendsto (fun blocks => targetHitProbability 8 blocks start target)
      Filter.atTop (nhds 1) := by
  unfold targetHitProbability
  have h := targetMissProbability_eight_tends_zero start target
  unfold AlmostSureTargetHit at h
  simpa using
    ((tendsto_const_nhds : Filter.Tendsto (fun _ : Nat => (1 : Real)) Filter.atTop (nhds 1)).sub h)

/-- The actual order-twelve finite retry walk hits every target with probability one. -/
theorem finiteCyclicRetry_twelve_target_hit_probability_one (start target : ZMod 12) :
    Filter.Tendsto (fun blocks => targetHitProbability 12 blocks start target)
      Filter.atTop (nhds 1) := by
  unfold targetHitProbability
  have h := targetMissProbability_twelve_tends_zero start target
  unfold AlmostSureTargetHit at h
  simpa using
    ((tendsto_const_nhds : Filter.Tendsto (fun _ : Nat => (1 : Real)) Filter.atTop (nhds 1)).sub h)

end
end PhaseRetry
end Distillation
end QEC
