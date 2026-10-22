import QEC.Distillation.Core.DependentBatch
import QEC.Distillation.LowOverheadProtocol.Parameterized.PathEnvelope

/-!
# Parameterized HH18 finite-path yield accounting

This internal layer accounts for a selected finite logical path by multiplying
the success probabilities of the actual fresh stage runs.  It is not a joint
success event for every block in an exponentially branching construction.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit

attribute [local instance 100] Fintype.ofFinite

/-- The literal prefix of a selected output path at a finite stage. -/
def routedDepthOutputPathPrefix (m w depth : Nat)
    (path : routedDepthOutputSlots m w depth) (stage : Fin (depth + 1)) :
    routedDepthOutputSlots m w stage.1 :=
  fun index => path ⟨index.1,
    Nat.lt_of_lt_of_le index.2 (Nat.le_of_lt_succ stage.2)⟩

/-- The selected prefix at a stage belonging to a finite path. -/
def routedDepthPathStagePath (m w depth : Nat)
    (path : routedDepthOutputSlots m w depth) (stage : Fin depth) :
    routedDepthOutputSlots m w stage.1 :=
  routedDepthOutputPathPrefix m w depth path stage.castSucc

/-- The actual decoded run at one finite stage of a literal selected path. -/
noncomputable def routedDepthPathStageRun {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) (stage : Fin depth) :
    DistillationRun QubitSpace (PhysicalRegister m w) (LogicalRegister m w) :=
  routedDepthPathActualRun h hdegree epsilon hsmall stage.1
    (routedDepthPathStagePath m w depth path stage)

/-- The accounting yield of one stage, defined from its actual path-indexed
run rather than from a separately supplied success parameter. -/
noncomputable def routedDepthPathStageYield {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) (stage : Fin depth) :
    NNReal :=
  ⟨(routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).successProbability,
    (routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).success_nonneg⟩

/-- Each finite stage yield is exactly the success probability of its actual
parameterized routed-depth run. -/
theorem routedDepthPathStageYield_eq_actualRunSuccess {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) (stage : Fin depth) :
    (routedDepthPathStageYield h hdegree epsilon hsmall depth path stage : ℝ) =
      (routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).successProbability :=
  rfl

/-- The finite fresh-layer accounting factor for one selected logical path.
This product ranges only over the actual stage runs on that path. -/
noncomputable def routedDepthPathYieldFactor {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) : NNReal :=
  ∏ stage : Fin depth, routedDepthPathStageYield h hdegree epsilon hsmall depth path stage

/-- The finite accounting product is literally the product of success
probabilities of the actual path-indexed stage runs. -/
theorem routedDepthPathYieldFactor_eq_actualStageSuccessProduct {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    (routedDepthPathYieldFactor h hdegree epsilon hsmall depth path : ℝ) =
      ∏ stage : Fin depth,
        (routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).successProbability := by
  classical
  rw [routedDepthPathYieldFactor, NNReal.coe_prod]
  apply Finset.prod_congr rfl
  intro stage _
  exact routedDepthPathStageYield_eq_actualRunSuccess
    h hdegree epsilon hsmall depth path stage

/-- The all-zero accepted physical-error branch and Bernoulli's inequality
give a literal one-stage success lower bound at every reached path rate. -/
theorem routedDepthPathStageRun_success_one_sub_physicalInputCount_rate_le
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) (stage : Fin depth) :
    1 - (physicalInputCount m w : ℝ) *
        (routedDepthPathRate h hdegree epsilon hsmall stage.1
          (routedDepthPathStagePath m w depth path stage)).1 ≤
      (routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).successProbability := by
  let rate := routedDepthPathRate h hdegree epsilon hsmall stage.1
    (routedDepthPathStagePath m w depth path stage)
  change 1 - (physicalInputCount m w : ℝ) * rate.1 ≤
    endpointWeight h hdegree (noisyResources m w rate) .accepted
  have hrate : 0 ≤ rate.1 := rate.property.1
  calc
    1 - (physicalInputCount m w : ℝ) * rate.1 ≤
        (1 - rate.1) ^ physicalInputCount m w := by
      have hbernoulli := one_add_mul_sub_le_pow
        (a := 1 - rate.1) (by linarith [rate.property.2]) (physicalInputCount m w)
      calc
        1 - (physicalInputCount m w : ℝ) * rate.1 =
            1 + (physicalInputCount m w : ℝ) * ((1 - rate.1) - 1) := by ring
        _ ≤ (1 - rate.1) ^ physicalInputCount m w := hbernoulli
    _ ≤ acceptedBernoulliMass w r m rate :=
      acceptedBernoulliMass_allZeroWord_le h rate
    _ = endpointWeight h hdegree (noisyResources m w rate) .accepted :=
      (endpointWeight_accepted_eq_acceptedBernoulliMass h hdegree rate).symm

/-- A finite product of factors in the unit interval is bounded below by one
minus the sum of their losses. -/
theorem routedDepthFiniteOneSubSum_le_product {ι : Type*} (s : Finset ι)
    (loss : ι → ℝ) (hlossNonneg : ∀ item ∈ s, 0 ≤ loss item)
    (hlossLeOne : ∀ item ∈ s, loss item ≤ 1) :
    1 - ∑ item ∈ s, loss item ≤ ∏ item ∈ s, (1 - loss item) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert item s hitem ih =>
      rw [Finset.sum_insert hitem, Finset.prod_insert hitem]
      have hsumNonneg : 0 ≤ ∑ other ∈ s, loss other :=
        Finset.sum_nonneg fun other hother =>
          hlossNonneg other (Finset.mem_insert_of_mem hother)
      have hrest :
          1 - ∑ item ∈ s, loss item ≤ ∏ item ∈ s, (1 - loss item) :=
        ih (fun other hother => hlossNonneg other (Finset.mem_insert_of_mem hother))
          (fun other hother => hlossLeOne other (Finset.mem_insert_of_mem hother))
      calc
        1 - (loss item + ∑ other ∈ s, loss other) ≤
            (1 - loss item) * (1 - ∑ other ∈ s, loss other) := by
          nlinarith [hlossNonneg item (Finset.mem_insert_self item s), hsumNonneg]
        _ ≤ (1 - loss item) * ∏ other ∈ s, (1 - loss other) :=
          mul_le_mul_of_nonneg_left hrest
            (by linarith [hlossLeOne item (Finset.mem_insert_self item s)])

/-- Every finite stage rate is bounded by the uniform envelope at that same
stage, while retaining its literal selected prefix. -/
theorem routedDepthPathStageRate_le_errorEnvelope {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) (stage : Fin depth) :
    (routedDepthPathRate h hdegree epsilon hsmall stage.1
      (routedDepthPathStagePath m w depth path stage)).1 ≤
        routedDepthErrorEnvelope w r m epsilon stage.1 :=
  routedDepthPathRate_le_errorEnvelope h hdegree epsilon hsmall stage.1
    (routedDepthPathStagePath m w depth path stage)

/-- The physical-input-weighted losses along every literal finite path are
summable by the same global envelope budget. -/
theorem routedDepthPathLoss_sum_le_one_sixth {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    ∑ stage : Fin depth, (physicalInputCount m w : ℝ) *
      (routedDepthPathRate h hdegree epsilon hsmall stage.1
        (routedDepthPathStagePath m w depth path stage)).1 ≤ 1 / 6 := by
  rw [← Finset.mul_sum]
  calc
    (physicalInputCount m w : ℝ) *
        ∑ stage : Fin depth,
          (routedDepthPathRate h hdegree epsilon hsmall stage.1
            (routedDepthPathStagePath m w depth path stage)).1 ≤
        (physicalInputCount m w : ℝ) *
          ∑ stage : Fin depth, routedDepthErrorEnvelope w r m epsilon stage.1 :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun stage _ =>
          routedDepthPathStageRate_le_errorEnvelope h hdegree epsilon hsmall depth path stage)
        (Nat.cast_nonneg _)
    _ ≤ 1 / 6 :=
      routedDepthPhysicalInputCount_mul_envelope_sum_le_one_sixth
        h epsilon hsmall depth

/-- The actual finite fresh-stage accounting product is uniformly bounded
below by five sixths; this is a pathwise accounting result rather than a
joint-event construction. -/
theorem routedDepthPathYieldFactor_five_sixths_le {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    (5 / 6 : ℝ) ≤ (routedDepthPathYieldFactor h hdegree epsilon hsmall depth path : ℝ) := by
  classical
  let loss : Fin depth → ℝ := fun stage =>
    (physicalInputCount m w : ℝ) *
      (routedDepthPathRate h hdegree epsilon hsmall stage.1
        (routedDepthPathStagePath m w depth path stage)).1
  have hlossNonneg (stage : Fin depth) : 0 ≤ loss stage := by
    dsimp [loss]
    exact mul_nonneg (Nat.cast_nonneg _)
      (routedDepthPathRate h hdegree epsilon hsmall stage.1
        (routedDepthPathStagePath m w depth path stage)).property.1
  have hsumLoss : ∑ stage : Fin depth, loss stage ≤ 1 / 6 := by
    simpa only [loss] using
      routedDepthPathLoss_sum_le_one_sixth h hdegree epsilon hsmall depth path
  have hlossLeOne (stage : Fin depth) : loss stage ≤ 1 := by
    calc
      loss stage ≤ ∑ other : Fin depth, loss other :=
        Finset.single_le_sum (fun other _ => hlossNonneg other) (Finset.mem_univ stage)
      _ ≤ 1 / 6 := hsumLoss
      _ ≤ 1 := by norm_num
  have hproductLower :
      1 - ∑ stage : Fin depth, loss stage ≤
        ∏ stage : Fin depth,
          (routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).successProbability := by
    calc
      1 - ∑ stage : Fin depth, loss stage ≤ ∏ stage : Fin depth, (1 - loss stage) := by
        simpa using (routedDepthFiniteOneSubSum_le_product Finset.univ loss
          (fun stage _ => hlossNonneg stage)
          (fun stage _ => hlossLeOne stage))
      _ ≤ ∏ stage : Fin depth,
          (routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).successProbability := by
        refine Finset.prod_le_prod ?_ ?_
        · intro stage _
          linarith [hlossLeOne stage]
        · intro stage _
          dsimp [loss]
          exact routedDepthPathStageRun_success_one_sub_physicalInputCount_rate_le
            h hdegree epsilon hsmall depth path stage
  rw [routedDepthPathYieldFactor_eq_actualStageSuccessProduct]
  linarith

/-- The routed physical input-slot carrier has the exact `n^z` cardinality
used by pathwise successful-output accounting. -/
theorem routedDepthPathTypedInputSlots_card (m w depth : Nat) :
    Fintype.card (routedDepthInputSlots m w depth) =
      physicalInputCount m w ^ depth :=
  routedDepthInputSlots_card m w depth

/-- The routed logical output-slot carrier has the exact `k^z` cardinality
used by pathwise successful-output accounting. -/
theorem routedDepthPathTypedOutputSlots_card (m w depth : Nat) :
    Fintype.card (routedDepthOutputSlots m w depth) =
      logicalOutputCount m w ^ depth :=
  routedDepthOutputSlots_card m w depth

/-- The expected accepted-output count obtained by summing the literal
path-survival factors over all routed output slots.  This is a finite output
accounting sum, not a simultaneous success event. -/
noncomputable def routedDepthPooledAcceptedOutput {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) : NNReal :=
  ∑ path : routedDepthOutputSlots m w depth,
    routedDepthPathYieldFactor h hdegree epsilon hsmall depth path

/-- Coercing the pooled expected accepted-output count exposes its literal
finite sum of path-survival factors. -/
theorem routedDepthPooledAcceptedOutput_eq_sum {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    (routedDepthPooledAcceptedOutput h hdegree epsilon hsmall depth : ℝ) =
      ∑ path : routedDepthOutputSlots m w depth,
        (routedDepthPathYieldFactor h hdegree epsilon hsmall depth path : ℝ) := by
  classical
  rw [routedDepthPooledAcceptedOutput, NNReal.coe_sum]

/-- The routed output-slot carrier is inhabited by the all-zero logical
address at every finite depth. -/
theorem routedDepthOutputSlots_nonempty (m w depth : Nat) :
    Nonempty (routedDepthOutputSlots m w depth) := by
  refine ⟨fun _ => ⟨(fun _ : Fin m => 0), ?_⟩⟩
  simp [Coding.ReedMuller.pointWeight, HammingWeight, hammingSupport]

/-- The finite routed output-slot carrier therefore has positive cardinality. -/
theorem routedDepthOutputSlots_card_pos (m w depth : Nat) :
    0 < Fintype.card (routedDepthOutputSlots m w depth) :=
  Fintype.card_pos_iff.mpr (routedDepthOutputSlots_nonempty m w depth)

/-- The normalized pooled yield is the expected accepted-output count per
actual routed output slot. -/
noncomputable def routedDepthPooledYield {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) : NNReal :=
  routedDepthPooledAcceptedOutput h hdegree epsilon hsmall depth /
    Fintype.card (routedDepthOutputSlots m w depth)

/-- The pooled yield is the literal finite path sum divided by the exact
output-slot cardinality. -/
theorem routedDepthPooledYield_eq_sum_div_card {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    (routedDepthPooledYield h hdegree epsilon hsmall depth : ℝ) =
      (∑ path : routedDepthOutputSlots m w depth,
        (routedDepthPathYieldFactor h hdegree epsilon hsmall depth path : ℝ)) /
        Fintype.card (routedDepthOutputSlots m w depth) := by
  rw [routedDepthPooledYield, NNReal.coe_div,
    routedDepthPooledAcceptedOutput_eq_sum]
  rfl

/-- The pooled yield normalizes the literal finite path sum by the exact
`k^z` routed output-slot cardinality. -/
theorem routedDepthPooledYield_eq_normalized_path_sum {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    (routedDepthPooledYield h hdegree epsilon hsmall depth : ℝ) =
      (∑ path : routedDepthOutputSlots m w depth,
        (routedDepthPathYieldFactor h hdegree epsilon hsmall depth path : ℝ)) /
        (logicalOutputCount m w : ℝ) ^ depth := by
  rw [routedDepthPooledYield_eq_sum_div_card,
    routedDepthPathTypedOutputSlots_card]
  norm_cast

/-- Averaging the literal finite path-survival products preserves their
uniform five-sixths lower bound. -/
theorem routedDepthPooledYield_five_sixths_le {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    (5 / 6 : ℝ) ≤ (routedDepthPooledYield h hdegree epsilon hsmall depth : ℝ) := by
  classical
  have hcard : 0 < (Fintype.card (routedDepthOutputSlots m w depth) : ℝ) := by
    exact_mod_cast routedDepthOutputSlots_card_pos m w depth
  rw [routedDepthPooledYield_eq_sum_div_card]
  apply (le_div_iff₀ hcard).mpr
  calc
    (5 / 6 : ℝ) * Fintype.card (routedDepthOutputSlots m w depth) =
        ∑ path : routedDepthOutputSlots m w depth, (5 / 6 : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ ∑ path : routedDepthOutputSlots m w depth,
        (routedDepthPathYieldFactor h hdegree epsilon hsmall depth path : ℝ) :=
      Finset.sum_le_sum fun path _ =>
        routedDepthPathYieldFactor_five_sixths_le h hdegree epsilon hsmall depth path

/-- The normalized pooled yield is strictly positive. -/
theorem routedDepthPooledYield_pos {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    0 < (routedDepthPooledYield h hdegree epsilon hsmall depth : ℝ) :=
  lt_of_lt_of_le (by norm_num)
    (routedDepthPooledYield_five_sixths_le h hdegree epsilon hsmall depth)

/-- Typed successful-output cost uses the actual routed input/output slot
types and the pooled normalized yield over every output path. -/
noncomputable def routedDepthTypedSuccessfulOutputCost {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) : ℝ :=
  DependentBatch.typedSuccessfulOutputCost (routedDepthInputSlots m w depth)
    (routedDepthOutputSlots m w depth)
    (routedDepthPooledYield h hdegree epsilon hsmall depth)

/-- The typed successful-output cost has its exact finite routed
input/output ratio and pooled-yield form. -/
theorem routedDepthTypedSuccessfulOutputCost_eq {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    routedDepthTypedSuccessfulOutputCost h hdegree epsilon hsmall depth =
      ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth /
        (routedDepthPooledYield h hdegree epsilon hsmall depth : ℝ) := by
  unfold routedDepthTypedSuccessfulOutputCost
  unfold DependentBatch.typedSuccessfulOutputCost
  unfold DependentBatch.typedInputOutputRatio
  rw [routedDepthPathTypedInputSlots_card, routedDepthPathTypedOutputSlots_card]
  simp only [Nat.cast_pow]
  rw [div_pow]

/-- The parameterized logical output count is positive, as follows from the
all-zero logical address and the exact depth-one output-slot cardinality. -/
theorem routedDepthLogicalOutputCount_pos (m w : Nat) :
    0 < logicalOutputCount m w := by
  have hcard := routedDepthOutputSlots_card_pos m w 1
  rw [routedDepthPathTypedOutputSlots_card] at hcard
  simpa using hcard

/-- The pooled typed successful-output accounting cost is strictly positive. -/
theorem routedDepthTypedSuccessfulOutputCost_pos {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    0 < routedDepthTypedSuccessfulOutputCost h hdegree epsilon hsmall depth := by
  rw [routedDepthTypedSuccessfulOutputCost_eq]
  have hinput : 0 < (physicalInputCount m w : ℝ) := by
    exact_mod_cast routedDepthPhysicalInputCount_pos h
  have houtput : 0 < (logicalOutputCount m w : ℝ) := by
    exact_mod_cast routedDepthLogicalOutputCount_pos m w
  exact div_pos (pow_pos (div_pos hinput houtput) _)
    (routedDepthPooledYield_pos h hdegree epsilon hsmall depth)

/-- The uniformly positive pooled yield gives a constant-factor bound on the
typed routed input-per-successful-output cost. -/
theorem routedDepthTypedSuccessfulOutputCost_le_six_fifths {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    routedDepthTypedSuccessfulOutputCost h hdegree epsilon hsmall depth ≤
      (6 / 5 : ℝ) * ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth := by
  rw [routedDepthTypedSuccessfulOutputCost_eq]
  have hratioNonneg :
      0 ≤ ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth :=
    pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _
  have hyield : (5 / 6 : ℝ) ≤
      (routedDepthPooledYield h hdegree epsilon hsmall depth : ℝ) :=
    routedDepthPooledYield_five_sixths_le h hdegree epsilon hsmall depth
  calc
    ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth /
        (routedDepthPooledYield h hdegree epsilon hsmall depth : ℝ) ≤
        ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth / ((5 : ℝ) / 6) :=
      div_le_div_of_nonneg_left hratioNonneg (by norm_num) hyield
    _ = (6 / 5 : ℝ) * ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth := by
      ring

/-- At depth one, the sole stage of every output path is the genuine initial
parameterized HH18 run at the original physical input rate. -/
theorem routedDepthPathYieldFactor_one_eq_actualRootRunSuccess {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (path : routedDepthOutputSlots m w 1) :
    (routedDepthPathYieldFactor h hdegree epsilon hsmall 1 path : ℝ) =
      (resourceDecodedRun h hdegree (noisyResources m w epsilon)).successProbability := by
  rw [routedDepthPathYieldFactor_eq_actualStageSuccessProduct, Fin.prod_univ_one]
  change (routedDepthPathActualRun h hdegree epsilon hsmall 0
    (routedDepthPathStagePath m w 1 path 0)).successProbability = _
  rw [routedDepthPathActualRun_eq_resourceDecodedRun]
  simp

/-- At depth one, averaging the identical genuine initial path factors gives
exactly that one-level run's success probability. -/
theorem routedDepthPooledYield_one_eq_actualRootRunSuccess {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    (routedDepthPooledYield h hdegree epsilon hsmall 1 : ℝ) =
      (resourceDecodedRun h hdegree (noisyResources m w epsilon)).successProbability := by
  classical
  rw [routedDepthPooledYield_eq_sum_div_card]
  simp_rw [routedDepthPathYieldFactor_one_eq_actualRootRunSuccess h hdegree epsilon hsmall]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (routedDepthOutputSlots m w 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (routedDepthOutputSlots_card_pos m w 1)
  field_simp [hcard]

/-- The depth-one pooled typed cost is expressed by the genuine initial
parameterized HH18 run's literal success probability. -/
theorem routedDepthTypedSuccessfulOutputCost_one_eq_actualRootRunSuccess
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    routedDepthTypedSuccessfulOutputCost h hdegree epsilon hsmall 1 =
      ((physicalInputCount m w : ℝ) / logicalOutputCount m w) /
        (resourceDecodedRun h hdegree (noisyResources m w epsilon)).successProbability := by
  rw [routedDepthTypedSuccessfulOutputCost_eq,
    routedDepthPooledYield_one_eq_actualRootRunSuccess]
  simp

end HH18Parameterized
end Distillation
end QEC
