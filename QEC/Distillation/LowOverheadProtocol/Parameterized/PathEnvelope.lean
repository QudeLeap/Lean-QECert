import QEC.Distillation.LowOverheadProtocol.Parameterized.FreshDepth

/-!
# Parameterized HH18 path-dependent error envelope

This internal layer derives a uniform finite-depth error envelope for actual
selected-port paths.  The envelope bounds each path separately; it does not
identify rates at different logical ports.  Its initial domain is chosen from
the finite residual coefficient, physical block size, and code distance so
that all successor input-domain witnesses are constructed internally.

This module stops before finite yield products, successful-output cost, and
terminal-family packaging.
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

/-- The literal coefficient in the source-scaled selected-port recurrence. -/
noncomputable def routedDepthRawErrorCoefficient (w r m : Nat) : ℝ :=
  2 * residualCoefficient w r m *
    (physicalInputCount m w : ℝ) ^ codeDistance r w

/-- A finite scale dominating the literal source-scaled selected-port
coefficient. -/
noncomputable def routedDepthIterationScale (w r m : Nat) : ℝ :=
  routedDepthRawErrorCoefficient w r m +
    2 * (physicalInputCount m w : ℝ) + 1

/-- The actual physical block has at least one resource coordinate under the
admissible HH18 parameter inequalities. -/
theorem routedDepthPhysicalInputCount_pos {w r m : Nat}
    (h : Admissible w r m) : 0 < physicalInputCount m w := by
  unfold physicalInputCount
  apply Fintype.card_pos_iff.mpr
  refine ⟨⟨(fun _ : Fin m => (1 : ZMod 2)), ?_⟩⟩
  rcases h with ⟨_, hwr, hrm⟩
  have hwm : w < m := by
    omega
  simpa [Coding.ReedMuller.pointWeight, HammingWeight, hammingSupport] using hwm

/-- The literal source-scaled coefficient is nonnegative. -/
theorem routedDepthRawErrorCoefficient_nonneg (w r m : Nat) :
    0 ≤ routedDepthRawErrorCoefficient w r m := by
  unfold routedDepthRawErrorCoefficient
  exact mul_nonneg
    (mul_nonneg (by norm_num) (residualCoefficient_nonneg w r m))
    (pow_nonneg (Nat.cast_nonneg _) _)

/-- The derived iteration scale is at least one. -/
theorem routedDepthIterationScale_one_le (w r m : Nat) :
    1 ≤ routedDepthIterationScale w r m := by
  unfold routedDepthIterationScale
  linarith [routedDepthRawErrorCoefficient_nonneg w r m]

/-- The scale retains a visible multiple of the actual block input count for
later uniform pooled-resource accounting. -/
theorem two_mul_routedDepthPhysicalInputCount_le_iterationScale (w r m : Nat) :
    2 * (physicalInputCount m w : ℝ) ≤ routedDepthIterationScale w r m := by
  have hcount : 0 ≤ (physicalInputCount m w : ℝ) := Nat.cast_nonneg _
  unfold routedDepthIterationScale
  nlinarith [routedDepthRawErrorCoefficient_nonneg w r m, hcount]

/-- The derived iteration scale is positive. -/
theorem routedDepthIterationScale_pos (w r m : Nat) :
    0 < routedDepthIterationScale w r m :=
  lt_of_lt_of_le zero_lt_one (routedDepthIterationScale_one_le w r m)

/-- The actual HH18 binomial-tail distance is at least two; this follows from
the admissible parameter inequalities and does not need a caller hypothesis. -/
theorem codeDistance_two_le {w r m : Nat} (h : Admissible w r m) :
    2 ≤ codeDistance r w := by
  rcases h with ⟨_, hwr, _⟩
  rw [codeDistance_eq_binomialTail]
  change 2 ≤ ∑ i ∈ Finset.Icc (w + 1) (r + 1), Nat.choose (r + 1) i
  have hrpos : 0 < r := by
    omega
  have hsub : ({r, r + 1} : Finset Nat) ⊆ Finset.Icc (w + 1) (r + 1) := by
    intro index hindex
    simp only [Finset.mem_insert, Finset.mem_singleton] at hindex
    rcases hindex with hindex | hindex
    · subst index
      simp
      omega
    · subst index
      simp
      omega
  have hsum := Finset.sum_le_sum_of_subset
    (f := fun i => Nat.choose (r + 1) i) hsub
  calc
    2 ≤ (r + 1) + 1 := by omega
    _ = Nat.choose (r + 1) r + Nat.choose (r + 1) (r + 1) := by
      rw [Nat.choose_succ_self_right, Nat.choose_self]
    _ = ∑ i ∈ ({r, r + 1} : Finset Nat), Nat.choose (r + 1) i := by
      rw [Finset.sum_pair (Nat.ne_of_lt (Nat.lt_succ_self r))]
    _ ≤ ∑ i ∈ Finset.Icc (w + 1) (r + 1), Nat.choose (r + 1) i := hsum

/-- The literal selected-port raw error satisfies the source-scaled finite
recurrence coefficient at every physical input rate. -/
theorem selectedLogicalPortRawError_le_routedDepthRawErrorCoefficient_mul_pow
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (rate : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    selectedLogicalPortRawError h hdegree rate port ≤
      routedDepthRawErrorCoefficient w r m * rate.1 ^ codeDistance r w := by
  calc
    selectedLogicalPortRawError h hdegree rate port ≤
        2 * acceptedResidualError h hdegree rate :=
      selectedLogicalPortRawError_le_two_mul_acceptedResidual h hdegree rate port
    _ ≤ 2 * (residualCoefficient w r m *
        ((physicalInputCount m w : ℝ) * rate.1) ^ codeDistance r w) := by
      exact mul_le_mul_of_nonneg_left
        (acceptedResidualError_le_sourceScaled h hdegree rate) (by norm_num)
    _ = routedDepthRawErrorCoefficient w r m * rate.1 ^ codeDistance r w := by
      unfold routedDepthRawErrorCoefficient
      rw [mul_pow]
      ring

/-- The derived scale dominates the literal coefficient at every admissible
HH18 distance. -/
theorem routedDepthRawErrorCoefficient_le_scale_pow_pred {w r m : Nat}
    (h : Admissible w r m) :
    routedDepthRawErrorCoefficient w r m ≤
      routedDepthIterationScale w r m ^ (codeDistance r w - 1) := by
  have hdistance : 2 ≤ codeDistance r w := codeDistance_two_le h
  have hone : 1 ≤ codeDistance r w - 1 := by
    omega
  calc
    routedDepthRawErrorCoefficient w r m ≤ routedDepthIterationScale w r m := by
      unfold routedDepthIterationScale
      linarith [routedDepthRawErrorCoefficient_nonneg w r m]
    _ = routedDepthIterationScale w r m ^ 1 := by simp
    _ ≤ routedDepthIterationScale w r m ^ (codeDistance r w - 1) :=
      pow_le_pow_right₀ (routedDepthIterationScale_one_le w r m) hone

/-- The explicit small initial domain from which all actual successor
half-domain witnesses are derived. -/
def routedDepthInitialSmallDomain (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : Prop :=
  routedDepthIterationScale w r m * epsilon.1 ≤ 1 / 4

/-- The separate uniform finite-depth envelope for literal path-dependent
physical rates. -/
noncomputable def routedDepthErrorEnvelope (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : Nat → ℝ
  | 0 => epsilon.1
  | depth + 1 =>
      routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
        (routedDepthErrorEnvelope w r m epsilon depth) ^ codeDistance r w

/-- The derived envelope has the exact distance-power closed form. -/
theorem routedDepthErrorEnvelope_closed_form {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (depth : Nat) :
    routedDepthIterationScale w r m * routedDepthErrorEnvelope w r m epsilon depth =
      (routedDepthIterationScale w r m * epsilon.1) ^ (codeDistance r w ^ depth) := by
  have hdistance : 1 ≤ codeDistance r w := (codeDistance_two_le h).trans' (by omega)
  induction depth with
  | zero =>
      simp [routedDepthErrorEnvelope]
  | succ depth ih =>
      calc
        routedDepthIterationScale w r m *
            routedDepthErrorEnvelope w r m epsilon (depth + 1) =
            (routedDepthIterationScale w r m *
              routedDepthErrorEnvelope w r m epsilon depth) ^ codeDistance r w := by
          simp only [routedDepthErrorEnvelope]
          rw [mul_pow]
          have hsub : codeDistance r w - 1 + 1 = codeDistance r w :=
            Nat.sub_add_cancel hdistance
          calc
            routedDepthIterationScale w r m *
                (routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
                  routedDepthErrorEnvelope w r m epsilon depth ^ codeDistance r w) =
                (routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
                  routedDepthIterationScale w r m) *
                  routedDepthErrorEnvelope w r m epsilon depth ^ codeDistance r w := by ring
            _ = routedDepthIterationScale w r m ^ codeDistance r w *
                  routedDepthErrorEnvelope w r m epsilon depth ^ codeDistance r w := by
              rw [← pow_succ, hsub]
        _ = ((routedDepthIterationScale w r m * epsilon.1) ^
            (codeDistance r w ^ depth)) ^ codeDistance r w := by rw [ih]
        _ = (routedDepthIterationScale w r m * epsilon.1) ^
            (codeDistance r w ^ (depth + 1)) := by
          rw [← pow_mul, pow_succ]

private theorem routedDepthErrorEnvelope_nonneg (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat) :
    0 ≤ routedDepthErrorEnvelope w r m epsilon depth := by
  induction depth with
  | zero =>
      exact epsilon.property.1
  | succ depth ih =>
      simp only [routedDepthErrorEnvelope]
      exact mul_nonneg
        (pow_nonneg (routedDepthIterationScale_pos w r m).le _)
        (pow_nonneg ih _)

/-- The prefix of a nonempty finite logical-port path. -/
def routedDepthOutputPathInit (m w depth : Nat)
    (path : routedDepthOutputSlots m w (depth + 1)) :
    routedDepthOutputSlots m w depth :=
  fun index => path index.castSucc

/-- The final selected logical port of a nonempty finite path. -/
def routedDepthOutputPathLast (m w depth : Nat)
    (path : routedDepthOutputSlots m w (depth + 1)) : LogicalSite m w :=
  path (Fin.last depth)

/-- Every nonempty finite selected-port path decomposes into its literal
prefix and final port. -/
theorem routedDepthOutputPath_append_init_last (m w depth : Nat)
    (path : routedDepthOutputSlots m w (depth + 1)) :
    routedDepthOutputPathAppend m w depth
      (routedDepthOutputPathInit m w depth path)
      (routedDepthOutputPathLast m w depth path) = path := by
  funext index
  refine Fin.lastCases ?_ ?_ index
  · simp [routedDepthOutputPathAppend, routedDepthOutputPathLast]
  · intro prefixIndex
    simp [routedDepthOutputPathAppend, routedDepthOutputPathInit]

@[simp] theorem routedDepthOutputPathInit_append (m w depth : Nat)
    (path : routedDepthOutputSlots m w depth) (port : LogicalSite m w) :
    routedDepthOutputPathInit m w depth
      (routedDepthOutputPathAppend m w depth path port) = path := by
  funext index
  simp [routedDepthOutputPathInit, routedDepthOutputPathAppend]

@[simp] theorem routedDepthOutputPathLast_append (m w depth : Nat)
    (path : routedDepthOutputSlots m w depth) (port : LogicalSite m w) :
    routedDepthOutputPathLast m w depth
      (routedDepthOutputPathAppend m w depth path port) = port :=
  by
    simp [routedDepthOutputPathLast, routedDepthOutputPathAppend]

/-- The internal recursively constructed path state retains only facts proved
from the literal selected-port recurrence and the uniform envelope. -/
private structure RoutedDepthPathIteration {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) where
  rate : HH18NoisyInput.DiagonalErrorRate
  state : RoutedDepthState h hdegree epsilon depth path rate
  scaled_small : routedDepthIterationScale w r m * rate.1 ≤ 1 / 4
  rate_le_envelope : rate.1 ≤ routedDepthErrorEnvelope w r m epsilon depth

private theorem routedDepthIteration_scale_mul_rawError_le_quarter
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} {path : routedDepthOutputSlots m w depth}
    (current : RoutedDepthPathIteration h hdegree epsilon hsmall depth path)
    (port : LogicalSite m w) :
    routedDepthIterationScale w r m *
        selectedLogicalPortRawError h hdegree current.rate port ≤ 1 / 4 := by
  have hdistance : 1 ≤ codeDistance r w :=
    (codeDistance_two_le h).trans' (by omega)
  have hraw := selectedLogicalPortRawError_le_routedDepthRawErrorCoefficient_mul_pow
    h hdegree current.rate port
  have hdomination := routedDepthRawErrorCoefficient_le_scale_pow_pred h
  have hrateNonneg : 0 ≤ current.rate.1 := current.rate.property.1
  have hscaleNonneg : 0 ≤ routedDepthIterationScale w r m :=
    (routedDepthIterationScale_pos w r m).le
  have hscaledPower :
      (routedDepthIterationScale w r m * current.rate.1) ^ codeDistance r w ≤
        (1 / 4 : ℝ) ^ codeDistance r w :=
    pow_le_pow_left₀ (mul_nonneg hscaleNonneg hrateNonneg)
      current.scaled_small _
  calc
    routedDepthIterationScale w r m *
        selectedLogicalPortRawError h hdegree current.rate port ≤
        routedDepthIterationScale w r m *
          (routedDepthRawErrorCoefficient w r m *
            current.rate.1 ^ codeDistance r w) :=
      mul_le_mul_of_nonneg_left hraw hscaleNonneg
    _ ≤ routedDepthIterationScale w r m *
          (routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
            current.rate.1 ^ codeDistance r w) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hdomination
          (pow_nonneg hrateNonneg _)) hscaleNonneg
    _ = (routedDepthIterationScale w r m * current.rate.1) ^ codeDistance r w := by
      rw [mul_pow]
      have hsub : codeDistance r w - 1 + 1 = codeDistance r w :=
        Nat.sub_add_cancel hdistance
      calc
        routedDepthIterationScale w r m *
            (routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
              current.rate.1 ^ codeDistance r w) =
            (routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
              routedDepthIterationScale w r m) *
              current.rate.1 ^ codeDistance r w := by ring
        _ = routedDepthIterationScale w r m ^ codeDistance r w *
              current.rate.1 ^ codeDistance r w := by
          rw [← pow_succ, hsub]
    _ ≤ (1 / 4 : ℝ) ^ codeDistance r w := hscaledPower
    _ ≤ (1 / 4 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hdistance
    _ = 1 / 4 := by norm_num

private theorem routedDepthIteration_next_half
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} {path : routedDepthOutputSlots m w depth}
    (current : RoutedDepthPathIteration h hdegree epsilon hsmall depth path)
    (port : LogicalSite m w) :
    selectedLogicalPortRawError h hdegree current.rate port ≤ 1 / 2 := by
  have hrawNonneg : 0 ≤ selectedLogicalPortRawError h hdegree current.rate port :=
    selectedLogicalPortRawError_nonneg h hdegree current.rate port
  have hscaled := routedDepthIteration_scale_mul_rawError_le_quarter
    h hdegree epsilon hsmall current port
  have hscaleOne : 1 ≤ routedDepthIterationScale w r m :=
    routedDepthIterationScale_one_le w r m
  calc
    selectedLogicalPortRawError h hdegree current.rate port ≤
        routedDepthIterationScale w r m *
          selectedLogicalPortRawError h hdegree current.rate port := by
      nlinarith
    _ ≤ 1 / 4 := hscaled
    _ ≤ 1 / 2 := by norm_num

private theorem routedDepthIteration_next_scaled_small
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} {path : routedDepthOutputSlots m w depth}
    (current : RoutedDepthPathIteration h hdegree epsilon hsmall depth path)
    (port : LogicalSite m w) :
    routedDepthIterationScale w r m *
        (selectedLogicalPortNextInputRate h hdegree current.rate port
          (routedDepthIteration_next_half h hdegree epsilon hsmall current port)).1 ≤ 1 / 4 := by
  change routedDepthIterationScale w r m *
      selectedLogicalPortRawError h hdegree current.rate port ≤ 1 / 4
  exact routedDepthIteration_scale_mul_rawError_le_quarter
    h hdegree epsilon hsmall current port

private theorem routedDepthIteration_next_le_envelope
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} {path : routedDepthOutputSlots m w depth}
    (current : RoutedDepthPathIteration h hdegree epsilon hsmall depth path)
    (port : LogicalSite m w) :
    (selectedLogicalPortNextInputRate h hdegree current.rate port
      (routedDepthIteration_next_half h hdegree epsilon hsmall current port)).1 ≤
        routedDepthErrorEnvelope w r m epsilon (depth + 1) := by
  change selectedLogicalPortRawError h hdegree current.rate port ≤ _
  calc
    selectedLogicalPortRawError h hdegree current.rate port ≤
        routedDepthRawErrorCoefficient w r m * current.rate.1 ^ codeDistance r w :=
      selectedLogicalPortRawError_le_routedDepthRawErrorCoefficient_mul_pow
        h hdegree current.rate port
    _ ≤ routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
          current.rate.1 ^ codeDistance r w :=
      mul_le_mul_of_nonneg_right
        (routedDepthRawErrorCoefficient_le_scale_pow_pred h)
        (pow_nonneg current.rate.property.1 _)
    _ ≤ routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
          (routedDepthErrorEnvelope w r m epsilon depth) ^ codeDistance r w :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ current.rate.property.1 current.rate_le_envelope _)
        (pow_nonneg (routedDepthIterationScale_pos w r m).le _)
    _ = routedDepthErrorEnvelope w r m epsilon (depth + 1) := rfl

private noncomputable def routedDepthPathIteration {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    (depth : Nat) → (path : routedDepthOutputSlots m w depth) →
      RoutedDepthPathIteration h hdegree epsilon hsmall depth path
  | 0, path => by
      have hpath : path = routedDepthOutputPathEmpty m w := Subsingleton.elim _ _
      subst path
      exact ⟨epsilon, RoutedDepthState.root, hsmall, by rfl⟩
  | depth + 1, path => by
      let previous := routedDepthPathIteration h hdegree epsilon hsmall depth
        (routedDepthOutputPathInit m w depth path)
      let port := routedDepthOutputPathLast m w depth path
      let hhalf := routedDepthIteration_next_half h hdegree epsilon hsmall previous port
      refine ⟨selectedLogicalPortNextInputRate h hdegree previous.rate port hhalf, ?_,
        routedDepthIteration_next_scaled_small h hdegree epsilon hsmall previous port,
        routedDepthIteration_next_le_envelope h hdegree epsilon hsmall previous port⟩
      have hstate := RoutedDepthState.succ previous.state port hhalf
      simpa only [port, routedDepthOutputPath_append_init_last] using hstate

private theorem routedDepthPathIteration_succ_rate {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w (depth + 1)) :
    (routedDepthPathIteration h hdegree epsilon hsmall (depth + 1) path).rate =
      selectedLogicalPortNextInputRate h hdegree
        (routedDepthPathIteration h hdegree epsilon hsmall depth
          (routedDepthOutputPathInit m w depth path)).rate
        (routedDepthOutputPathLast m w depth path)
        (routedDepthIteration_next_half h hdegree epsilon hsmall
          (routedDepthPathIteration h hdegree epsilon hsmall depth
            (routedDepthOutputPathInit m w depth path))
          (routedDepthOutputPathLast m w depth path)) :=
  rfl

/-- The actual physical diagonal rate reached along one finite logical-port
path, with every successor-domain witness derived internally. -/
private noncomputable def routedDepthStateProjectionRate {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    HH18NoisyInput.DiagonalErrorRate :=
  (routedDepthPathIteration h hdegree epsilon hsmall depth path).rate

/-- The actual routed-depth run state carried by one finite logical-port
path. -/
private noncomputable def routedDepthStateProjection {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    RoutedDepthState h hdegree epsilon depth path
      (routedDepthStateProjectionRate h hdegree epsilon hsmall depth path) :=
  (routedDepthPathIteration h hdegree epsilon hsmall depth path).state

/-- The selected-port successor half-domain witness is derived from the
uniform path envelope, never supplied by the caller. -/
private theorem routedDepthStateProjectionNextHalf {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} (path : routedDepthOutputSlots m w depth)
    (port : LogicalSite m w) :
    selectedLogicalPortRawError h hdegree
      (routedDepthStateProjectionRate h hdegree epsilon hsmall depth path) port ≤ 1 / 2 :=
  routedDepthIteration_next_half h hdegree epsilon hsmall
    (routedDepthPathIteration h hdegree epsilon hsmall depth path) port

/-- The root path reaches the literal initial physical error rate. -/
private theorem routedDepthStateProjectionRate_root {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    routedDepthStateProjectionRate h hdegree epsilon hsmall 0
      (routedDepthOutputPathEmpty m w) = epsilon :=
  rfl

/-- Every actual finite path rate is bounded by the same separately proved
envelope while retaining its own path-dependent value. -/
private theorem routedDepthStateProjectionRate_le_errorEnvelope {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    (routedDepthStateProjectionRate h hdegree epsilon hsmall depth path).1 ≤
      routedDepthErrorEnvelope w r m epsilon depth :=
  (routedDepthPathIteration h hdegree epsilon hsmall depth path).rate_le_envelope

private theorem routedDepthScale_mul_selectedRawError_le_quarter
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (rate : HH18NoisyInput.DiagonalErrorRate)
    (hscaled : routedDepthIterationScale w r m * rate.1 ≤ 1 / 4)
    (port : LogicalSite m w) :
    routedDepthIterationScale w r m *
        selectedLogicalPortRawError h hdegree rate port ≤ 1 / 4 := by
  have hdistance : 1 ≤ codeDistance r w :=
    (codeDistance_two_le h).trans' (by omega)
  have hraw := selectedLogicalPortRawError_le_routedDepthRawErrorCoefficient_mul_pow
    h hdegree rate port
  have hdomination := routedDepthRawErrorCoefficient_le_scale_pow_pred h
  have hrateNonneg : 0 ≤ rate.1 := rate.property.1
  have hscaleNonneg : 0 ≤ routedDepthIterationScale w r m :=
    (routedDepthIterationScale_pos w r m).le
  have hscaledPower :
      (routedDepthIterationScale w r m * rate.1) ^ codeDistance r w ≤
        (1 / 4 : ℝ) ^ codeDistance r w :=
    pow_le_pow_left₀ (mul_nonneg hscaleNonneg hrateNonneg) hscaled _
  calc
    routedDepthIterationScale w r m *
        selectedLogicalPortRawError h hdegree rate port ≤
        routedDepthIterationScale w r m *
          (routedDepthRawErrorCoefficient w r m *
            rate.1 ^ codeDistance r w) :=
      mul_le_mul_of_nonneg_left hraw hscaleNonneg
    _ ≤ routedDepthIterationScale w r m *
          (routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
            rate.1 ^ codeDistance r w) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hdomination
          (pow_nonneg hrateNonneg _)) hscaleNonneg
    _ = (routedDepthIterationScale w r m * rate.1) ^ codeDistance r w := by
      rw [mul_pow]
      have hsub : codeDistance r w - 1 + 1 = codeDistance r w :=
        Nat.sub_add_cancel hdistance
      calc
        routedDepthIterationScale w r m *
            (routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
              rate.1 ^ codeDistance r w) =
            (routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
              routedDepthIterationScale w r m) *
              rate.1 ^ codeDistance r w := by ring
        _ = routedDepthIterationScale w r m ^ codeDistance r w *
              rate.1 ^ codeDistance r w := by
          rw [← pow_succ, hsub]
    _ ≤ (1 / 4 : ℝ) ^ codeDistance r w := hscaledPower
    _ ≤ (1 / 4 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hdistance
    _ = 1 / 4 := by norm_num

private theorem routedDepthSelectedRawError_half_of_scaled
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (rate : HH18NoisyInput.DiagonalErrorRate)
    (hscaled : routedDepthIterationScale w r m * rate.1 ≤ 1 / 4)
    (port : LogicalSite m w) :
    selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2 := by
  have hrawNonneg : 0 ≤ selectedLogicalPortRawError h hdegree rate port :=
    selectedLogicalPortRawError_nonneg h hdegree rate port
  have hscaleOne : 1 ≤ routedDepthIterationScale w r m :=
    routedDepthIterationScale_one_le w r m
  calc
    selectedLogicalPortRawError h hdegree rate port ≤
        routedDepthIterationScale w r m *
          selectedLogicalPortRawError h hdegree rate port := by
      nlinarith
    _ ≤ 1 / 4 :=
      routedDepthScale_mul_selectedRawError_le_quarter h hdegree rate hscaled port
    _ ≤ 1 / 2 := by norm_num

/-- A total selector used only to keep path-rate reduction transparent.  The
fallback is unreachable for every physical path satisfying the derived
initial domain. -/
private noncomputable def routedDepthTotalNextInputRate {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (rate : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    HH18NoisyInput.DiagonalErrorRate :=
  dite (selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2)
    (fun hhalf => selectedLogicalPortNextInputRate h hdegree rate port hhalf)
    (fun _ => rate)

private theorem routedDepthTotalNextInputRate_of_half {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (rate : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    routedDepthTotalNextInputRate h hdegree rate port =
      selectedLogicalPortNextInputRate h hdegree rate port hhalf := by
  have hhalf' : selectedLogicalPortRawError h hdegree rate port ≤ (2 : ℝ)⁻¹ := by
    simpa using hhalf
  simp [routedDepthTotalNextInputRate, hhalf']

/-- The transparent path selector follows literal selected ports; its total
fallback is eliminated by the proved small-domain invariant below. -/
noncomputable def routedDepthPathRate {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (_hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    (depth : Nat) → routedDepthOutputSlots m w depth →
      HH18NoisyInput.DiagonalErrorRate
  | 0, _ => epsilon
  | depth + 1, path =>
      routedDepthTotalNextInputRate h hdegree
        (routedDepthPathRate h hdegree epsilon _hsmall depth
          (routedDepthOutputPathInit m w depth path))
        (routedDepthOutputPathLast m w depth path)

@[simp] theorem routedDepthPathRate_root {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (path : routedDepthOutputSlots m w 0) :
    routedDepthPathRate h hdegree epsilon hsmall 0 path = epsilon :=
  rfl

@[simp] theorem routedDepthPathRate_succ {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w (depth + 1)) :
    routedDepthPathRate h hdegree epsilon hsmall (depth + 1) path =
      routedDepthTotalNextInputRate h hdegree
        (routedDepthPathRate h hdegree epsilon hsmall depth
          (routedDepthOutputPathInit m w depth path))
        (routedDepthOutputPathLast m w depth path) :=
  rfl

private theorem routedDepthPathRate_scaled_small {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    ∀ (depth : Nat) (path : routedDepthOutputSlots m w depth),
      routedDepthIterationScale w r m *
        (routedDepthPathRate h hdegree epsilon hsmall depth path).1 ≤ 1 / 4 := by
  intro depth
  induction depth with
  | zero =>
      intro path
      simpa [routedDepthInitialSmallDomain] using hsmall
  | succ depth ih =>
      intro path
      let previous := routedDepthPathRate h hdegree epsilon hsmall depth
        (routedDepthOutputPathInit m w depth path)
      let port := routedDepthOutputPathLast m w depth path
      have hprevious : routedDepthIterationScale w r m * previous.1 ≤ 1 / 4 :=
        ih (routedDepthOutputPathInit m w depth path)
      have hhalf : selectedLogicalPortRawError h hdegree previous port ≤ 1 / 2 :=
        routedDepthSelectedRawError_half_of_scaled h hdegree previous hprevious port
      rw [routedDepthPathRate_succ,
        routedDepthTotalNextInputRate_of_half h hdegree previous port hhalf]
      change routedDepthIterationScale w r m *
        selectedLogicalPortRawError h hdegree previous port ≤ 1 / 4
      exact routedDepthScale_mul_selectedRawError_le_quarter
        h hdegree previous hprevious port

/-- On every finite physical path, the selector's fallback branch is ruled
out by the internally derived scaled-smallness invariant. -/
theorem routedDepthPathNextHalf {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} (path : routedDepthOutputSlots m w depth)
    (port : LogicalSite m w) :
    selectedLogicalPortRawError h hdegree
      (routedDepthPathRate h hdegree epsilon hsmall depth path) port ≤ 1 / 2 :=
  routedDepthSelectedRawError_half_of_scaled h hdegree
    (routedDepthPathRate h hdegree epsilon hsmall depth path)
    (routedDepthPathRate_scaled_small h hdegree epsilon hsmall depth path) port

/-- Appending a selected port uses the literal selected-port Born error, with
the total selector's fallback branch proved unreachable. -/
theorem routedDepthPathRate_append_eq_rawError {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} (path : routedDepthOutputSlots m w depth)
    (port : LogicalSite m w) :
    (routedDepthPathRate h hdegree epsilon hsmall (depth + 1)
      (routedDepthOutputPathAppend m w depth path port)).1 =
        selectedLogicalPortRawError h hdegree
          (routedDepthPathRate h hdegree epsilon hsmall depth path) port := by
  rw [routedDepthPathRate_succ]
  simp only [routedDepthOutputPathInit_append, routedDepthOutputPathLast_append]
  have hhalf := routedDepthPathNextHalf h hdegree epsilon hsmall path port
  rw [routedDepthTotalNextInputRate_of_half h hdegree
    (routedDepthPathRate h hdegree epsilon hsmall depth path) port hhalf]
  rfl

/-- The actual selector rate on every finite path is bounded by the separate
uniform distance-power envelope. -/
theorem routedDepthPathRate_le_errorEnvelope {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    ∀ (depth : Nat) (path : routedDepthOutputSlots m w depth),
      (routedDepthPathRate h hdegree epsilon hsmall depth path).1 ≤
        routedDepthErrorEnvelope w r m epsilon depth := by
  intro depth
  induction depth with
  | zero =>
      intro path
      simp [routedDepthErrorEnvelope]
  | succ depth ih =>
      intro path
      let previous := routedDepthPathRate h hdegree epsilon hsmall depth
        (routedDepthOutputPathInit m w depth path)
      let port := routedDepthOutputPathLast m w depth path
      have hprevious : previous.1 ≤ routedDepthErrorEnvelope w r m epsilon depth :=
        ih (routedDepthOutputPathInit m w depth path)
      have hhalf : selectedLogicalPortRawError h hdegree previous port ≤ 1 / 2 :=
        routedDepthSelectedRawError_half_of_scaled h hdegree previous
          (routedDepthPathRate_scaled_small h hdegree epsilon hsmall depth
            (routedDepthOutputPathInit m w depth path)) port
      rw [routedDepthPathRate_succ,
        routedDepthTotalNextInputRate_of_half h hdegree previous port hhalf]
      change selectedLogicalPortRawError h hdegree previous port ≤ _
      calc
        selectedLogicalPortRawError h hdegree previous port ≤
            routedDepthRawErrorCoefficient w r m * previous.1 ^ codeDistance r w :=
          selectedLogicalPortRawError_le_routedDepthRawErrorCoefficient_mul_pow
            h hdegree previous port
        _ ≤ routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
              previous.1 ^ codeDistance r w :=
          mul_le_mul_of_nonneg_right
            (routedDepthRawErrorCoefficient_le_scale_pow_pred h)
            (pow_nonneg previous.property.1 _)
        _ ≤ routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
              (routedDepthErrorEnvelope w r m epsilon depth) ^ codeDistance r w :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ previous.property.1 hprevious _)
            (pow_nonneg (routedDepthIterationScale_pos w r m).le _)
        _ = routedDepthErrorEnvelope w r m epsilon (depth + 1) := rfl


/-- The actual `RoutedDepthState` constructed at the transparent selector
rate.  Its successor uses only the internally derived half-domain witness. -/
noncomputable def routedDepthPathState {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    (depth : Nat) → (path : routedDepthOutputSlots m w depth) →
      RoutedDepthState h hdegree epsilon depth path
        (routedDepthPathRate h hdegree epsilon hsmall depth path)
  | 0, path => by
      have hpath : path = routedDepthOutputPathEmpty m w := Subsingleton.elim _ _
      subst path
      exact RoutedDepthState.root
  | depth + 1, path => by
      let priorPath := routedDepthOutputPathInit m w depth path
      let port := routedDepthOutputPathLast m w depth path
      let hhalf := routedDepthPathNextHalf h hdegree epsilon hsmall priorPath port
      have hrate : routedDepthPathRate h hdegree epsilon hsmall (depth + 1) path =
          selectedLogicalPortNextInputRate h hdegree
            (routedDepthPathRate h hdegree epsilon hsmall depth priorPath) port hhalf := by
        rw [routedDepthPathRate_succ,
          routedDepthTotalNextInputRate_of_half h hdegree
            (routedDepthPathRate h hdegree epsilon hsmall depth priorPath) port hhalf]
      rw [hrate]
      have hstate := RoutedDepthState.succ
        (routedDepthPathState h hdegree epsilon hsmall depth priorPath) port hhalf
      simpa only [priorPath, port, routedDepthOutputPath_append_init_last] using hstate

/-- An actual routed-depth state packaged at the transparent selector rate. -/
structure RoutedDepthPathStatePackage {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) where
  rate : HH18NoisyInput.DiagonalErrorRate
  state : RoutedDepthState h hdegree epsilon depth path rate

/-- The selector rate packages an actual internally constructed routed state,
not a caller-supplied recurrence value. -/
noncomputable def routedDepthPathStatePackage {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
  (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    RoutedDepthPathStatePackage h hdegree epsilon hsmall depth path := by
  exact ⟨routedDepthPathRate h hdegree epsilon hsmall depth path,
    routedDepthPathState h hdegree epsilon hsmall depth path⟩

/-- The transparent selector is exactly the rate index of its packaged actual
routed-depth state. -/
theorem routedDepthPathRate_eq_statePackage_rate {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    routedDepthPathRate h hdegree epsilon hsmall depth path =
      (routedDepthPathStatePackage h hdegree epsilon hsmall depth path).rate :=
  rfl

/-- The actual decoded run indexed by one finite selected-port path. -/
noncomputable def routedDepthPathActualRun {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    DistillationRun QubitSpace (PhysicalRegister m w) (LogicalRegister m w) :=
  resourceDecodedRun h hdegree (noisyResources m w
    (routedDepthPathRate h hdegree epsilon hsmall depth path))

/-- A path-indexed actual run is the literal one-level decoded run at that
path's independently selected physical rate. -/
theorem routedDepthPathActualRun_eq_resourceDecodedRun {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    routedDepthPathActualRun h hdegree epsilon hsmall depth path =
      resourceDecodedRun h hdegree (noisyResources m w
        (routedDepthPathRate h hdegree epsilon hsmall depth path)) :=
  rfl

/-- The direct path run is exactly the run indexed by its packaged actual
routed-depth state. -/
theorem routedDepthPathActualRun_eq_routedDepthActualRun {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    routedDepthPathActualRun h hdegree epsilon hsmall depth path =
      routedDepthActualRun h hdegree
        (routedDepthPathStatePackage h hdegree epsilon hsmall depth path).state :=
  rfl

/-- The selector successor is the actual domain-certified next input rate. -/
theorem routedDepthPathRate_append_eq_nextInputRate {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} (path : routedDepthOutputSlots m w depth)
    (port : LogicalSite m w) :
    routedDepthPathRate h hdegree epsilon hsmall (depth + 1)
      (routedDepthOutputPathAppend m w depth path port) =
        selectedLogicalPortNextInputRate h hdegree
          (routedDepthPathRate h hdegree epsilon hsmall depth path) port
          (routedDepthPathNextHalf h hdegree epsilon hsmall path port) := by
  rw [routedDepthPathRate_succ]
  simp only [routedDepthOutputPathInit_append, routedDepthOutputPathLast_append]
  exact routedDepthTotalNextInputRate_of_half h hdegree _ _
    (routedDepthPathNextHalf h hdegree epsilon hsmall path port)

/-- Appending a selected port constructs the literal routed child run of the
actual preceding path state. -/
theorem routedDepthPathActualRun_append_eq_childRun {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} (path : routedDepthOutputSlots m w depth)
    (port : LogicalSite m w) :
    routedDepthPathActualRun h hdegree epsilon hsmall (depth + 1)
      (routedDepthOutputPathAppend m w depth path port) =
      routedDepthChildRun h hdegree
        (routedDepthPathState h hdegree epsilon hsmall depth path) port
        (routedDepthPathNextHalf h hdegree epsilon hsmall path port) := by
  rw [routedDepthPathActualRun_eq_resourceDecodedRun,
    routedDepthChildRun_eq_resourceDecodedRun,
    routedDepthPathRate_append_eq_nextInputRate]

private theorem routedDepthSelectedRawError_le_rate_div_four_of_scaled
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (rate : HH18NoisyInput.DiagonalErrorRate)
    (hscaled : routedDepthIterationScale w r m * rate.1 ≤ 1 / 4)
    (port : LogicalSite m w) :
    selectedLogicalPortRawError h hdegree rate port ≤ rate.1 / 4 := by
  have hdistance : 2 ≤ codeDistance r w := codeDistance_two_le h
  have hpred : 1 ≤ codeDistance r w - 1 := by
    omega
  have hraw := selectedLogicalPortRawError_le_routedDepthRawErrorCoefficient_mul_pow
    h hdegree rate port
  have hdomination := routedDepthRawErrorCoefficient_le_scale_pow_pred h
  have hrateNonneg : 0 ≤ rate.1 := rate.property.1
  have hscaleNonneg : 0 ≤ routedDepthIterationScale w r m :=
    (routedDepthIterationScale_pos w r m).le
  have hpower :
      (routedDepthIterationScale w r m * rate.1) ^ (codeDistance r w - 1) ≤
        1 / 4 := by
    calc
      (routedDepthIterationScale w r m * rate.1) ^ (codeDistance r w - 1) ≤
          (1 / 4 : ℝ) ^ (codeDistance r w - 1) :=
        pow_le_pow_left₀ (mul_nonneg hscaleNonneg hrateNonneg) hscaled _
      _ ≤ (1 / 4 : ℝ) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hpred
      _ = 1 / 4 := by norm_num
  have hfactor :
      routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
          rate.1 ^ codeDistance r w =
        rate.1 * (routedDepthIterationScale w r m * rate.1) ^
          (codeDistance r w - 1) := by
    rw [mul_pow]
    have hsub : codeDistance r w - 1 + 1 = codeDistance r w :=
      Nat.sub_add_cancel (by omega)
    calc
      routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
          rate.1 ^ codeDistance r w =
          routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
            rate.1 ^ (codeDistance r w - 1 + 1) := by rw [hsub]
      _ = routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
            (rate.1 ^ (codeDistance r w - 1) * rate.1) := by rw [pow_succ]
      _ = rate.1 * (routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
            rate.1 ^ (codeDistance r w - 1)) := by ring
  calc
    selectedLogicalPortRawError h hdegree rate port ≤
        routedDepthRawErrorCoefficient w r m * rate.1 ^ codeDistance r w :=
      hraw
    _ ≤ routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
          rate.1 ^ codeDistance r w :=
      mul_le_mul_of_nonneg_right hdomination (pow_nonneg hrateNonneg _)
    _ = rate.1 * (routedDepthIterationScale w r m * rate.1) ^
          (codeDistance r w - 1) := hfactor
    _ ≤ rate.1 * (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hpower hrateNonneg
    _ = rate.1 / 4 := by ring

/-- Every actual selected-port path contracts by a factor of four at each
successor, although different ports retain different literal rates. -/
theorem routedDepthPathRate_append_le_quarter {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} (path : routedDepthOutputSlots m w depth)
    (port : LogicalSite m w) :
    (routedDepthPathRate h hdegree epsilon hsmall (depth + 1)
      (routedDepthOutputPathAppend m w depth path port)).1 ≤
        (routedDepthPathRate h hdegree epsilon hsmall depth path).1 / 4 := by
  rw [routedDepthPathRate_append_eq_rawError]
  exact routedDepthSelectedRawError_le_rate_div_four_of_scaled h hdegree
    (routedDepthPathRate h hdegree epsilon hsmall depth path)
    (routedDepthPathRate_scaled_small h hdegree epsilon hsmall depth path) port

/-- The uniform envelope itself remains in the scaled quarter-domain at every
finite depth. -/
theorem routedDepthErrorEnvelope_scaled_small {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) (depth : Nat) :
    routedDepthIterationScale w r m *
      routedDepthErrorEnvelope w r m epsilon depth ≤ 1 / 4 := by
  rw [routedDepthErrorEnvelope_closed_form h epsilon]
  have hbase : 0 ≤ routedDepthIterationScale w r m * epsilon.1 :=
    mul_nonneg (routedDepthIterationScale_pos w r m).le epsilon.property.1
  have hdistance : 2 ≤ codeDistance r w := codeDistance_two_le h
  have hpower : 1 ≤ codeDistance r w ^ depth :=
    one_le_pow₀ (by omega)
  calc
    (routedDepthIterationScale w r m * epsilon.1) ^ (codeDistance r w ^ depth) ≤
        (1 / 4 : ℝ) ^ (codeDistance r w ^ depth) :=
      pow_le_pow_left₀ hbase hsmall _
    _ ≤ (1 / 4 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hpower
    _ = 1 / 4 := by norm_num

/-- The global envelope contracts by a factor of four, uniformly over all
finite logical-port paths it bounds. -/
theorem routedDepthErrorEnvelope_succ_le_quarter {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) (depth : Nat) :
    routedDepthErrorEnvelope w r m epsilon (depth + 1) ≤
      routedDepthErrorEnvelope w r m epsilon depth / 4 := by
  have hdistance : 2 ≤ codeDistance r w := codeDistance_two_le h
  have hpred : 1 ≤ codeDistance r w - 1 := by omega
  have henvelopeNonneg : 0 ≤ routedDepthErrorEnvelope w r m epsilon depth :=
    routedDepthErrorEnvelope_nonneg w r m epsilon depth
  have hpower :
      (routedDepthIterationScale w r m *
        routedDepthErrorEnvelope w r m epsilon depth) ^ (codeDistance r w - 1) ≤
        1 / 4 := by
    calc
      (routedDepthIterationScale w r m *
        routedDepthErrorEnvelope w r m epsilon depth) ^ (codeDistance r w - 1) ≤
          (1 / 4 : ℝ) ^ (codeDistance r w - 1) :=
        pow_le_pow_left₀
          (mul_nonneg (routedDepthIterationScale_pos w r m).le henvelopeNonneg)
          (routedDepthErrorEnvelope_scaled_small h epsilon hsmall depth) _
      _ ≤ (1 / 4 : ℝ) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hpred
      _ = 1 / 4 := by norm_num
  have hfactor :
      routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
          routedDepthErrorEnvelope w r m epsilon depth ^ codeDistance r w =
        routedDepthErrorEnvelope w r m epsilon depth *
          (routedDepthIterationScale w r m *
            routedDepthErrorEnvelope w r m epsilon depth) ^
            (codeDistance r w - 1) := by
    rw [mul_pow]
    have hsub : codeDistance r w - 1 + 1 = codeDistance r w :=
      Nat.sub_add_cancel (by omega)
    calc
      routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
          routedDepthErrorEnvelope w r m epsilon depth ^ codeDistance r w =
          routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
            routedDepthErrorEnvelope w r m epsilon depth ^
              (codeDistance r w - 1 + 1) := by rw [hsub]
      _ = routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
            (routedDepthErrorEnvelope w r m epsilon depth ^
              (codeDistance r w - 1) * routedDepthErrorEnvelope w r m epsilon depth) := by
            rw [pow_succ]
      _ = routedDepthErrorEnvelope w r m epsilon depth *
            (routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
              routedDepthErrorEnvelope w r m epsilon depth ^
                (codeDistance r w - 1)) := by ring
  calc
    routedDepthErrorEnvelope w r m epsilon (depth + 1) =
        routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
          routedDepthErrorEnvelope w r m epsilon depth ^ codeDistance r w := rfl
    _ = routedDepthErrorEnvelope w r m epsilon depth *
          (routedDepthIterationScale w r m *
            routedDepthErrorEnvelope w r m epsilon depth) ^
            (codeDistance r w - 1) := hfactor
    _ ≤ routedDepthErrorEnvelope w r m epsilon depth * (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hpower henvelopeNonneg
    _ = routedDepthErrorEnvelope w r m epsilon depth / 4 := by ring

/-- The finite envelope sum plus its geometric tail is bounded uniformly by
the literal initial rate. -/
theorem routedDepthErrorEnvelope_sum_with_tail_le {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) (depth : Nat) :
    (∑ stage : Fin depth, routedDepthErrorEnvelope w r m epsilon stage.1) +
      (4 / 3 : ℝ) * routedDepthErrorEnvelope w r m epsilon depth ≤
        (4 / 3 : ℝ) * epsilon.1 := by
  induction depth with
  | zero =>
      change 0 + (4 / 3 : ℝ) * epsilon.1 ≤ (4 / 3 : ℝ) * epsilon.1
      linarith
  | succ depth ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hnext := routedDepthErrorEnvelope_succ_le_quarter h epsilon hsmall depth
      nlinarith

/-- Summing only the finite uniform envelope is no larger than its geometric
tail budget. -/
theorem routedDepthErrorEnvelope_sum_le {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) (depth : Nat) :
    ∑ stage : Fin depth, routedDepthErrorEnvelope w r m epsilon stage.1 ≤
      (4 / 3 : ℝ) * epsilon.1 := by
  calc
    ∑ stage : Fin depth, routedDepthErrorEnvelope w r m epsilon stage.1 ≤
        (∑ stage : Fin depth, routedDepthErrorEnvelope w r m epsilon stage.1) +
          (4 / 3 : ℝ) * routedDepthErrorEnvelope w r m epsilon depth := by
      exact le_add_of_nonneg_right
        (mul_nonneg (by norm_num)
          (routedDepthErrorEnvelope_nonneg w r m epsilon depth))
    _ ≤ (4 / 3 : ℝ) * epsilon.1 :=
      routedDepthErrorEnvelope_sum_with_tail_le h epsilon hsmall depth

/-- The scale's visible block-size term turns the uniform envelope tail into
a finite physical-input budget required by later pooled-resource accounting. -/
theorem routedDepthPhysicalInputCount_mul_envelope_sum_le_one_sixth
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) (depth : Nat) :
    (physicalInputCount m w : ℝ) *
      (∑ stage : Fin depth, routedDepthErrorEnvelope w r m epsilon stage.1) ≤
        1 / 6 := by
  have hcountNonneg : 0 ≤ (physicalInputCount m w : ℝ) := Nat.cast_nonneg _
  have hcountScale := two_mul_routedDepthPhysicalInputCount_le_iterationScale w r m
  have hscaledProduct :
      (2 * (physicalInputCount m w : ℝ)) * epsilon.1 ≤
        routedDepthIterationScale w r m * epsilon.1 := by
    exact mul_le_mul_of_nonneg_right hcountScale epsilon.property.1
  change routedDepthIterationScale w r m * epsilon.1 ≤ 1 / 4 at hsmall
  have hcountEpsilon : (physicalInputCount m w : ℝ) * epsilon.1 ≤ 1 / 8 := by
    nlinarith [hscaledProduct, hsmall]
  calc
    (physicalInputCount m w : ℝ) *
        (∑ stage : Fin depth, routedDepthErrorEnvelope w r m epsilon stage.1) ≤
        (physicalInputCount m w : ℝ) * ((4 / 3 : ℝ) * epsilon.1) :=
      mul_le_mul_of_nonneg_left
        (routedDepthErrorEnvelope_sum_le h epsilon hsmall depth) hcountNonneg
    _ = (4 / 3 : ℝ) * ((physicalInputCount m w : ℝ) * epsilon.1) := by ring
    _ ≤ (4 / 3 : ℝ) * (1 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left hcountEpsilon (by norm_num)
    _ = 1 / 6 := by norm_num

end HH18Parameterized
end Distillation
end QEC
