import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Schedule.DyadicSlack

/-!
# Parameterized HH18 decoded retry-pool backward schedule

This internal counting layer turns a terminal accepted-block request into a
finite backward schedule.  Its forward-stage equations expose the exact
dyadic retry attempt at each stage and the physical parent demand of every
nonterminal stage.
-/

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller

attribute [local instance 100] Fintype.ofFinite

/-- The terminal-to-root recursion for a fixed finite depth.  Distance zero
is the terminal request; each predecessor requests one physical block for
every retry attempt of the next stage. -/
def decodedRetryPoolBackwardRequiredAtDistance (m w z q : Nat) : Nat → Nat
  | 0 => q
  | distance + 1 =>
      physicalInputCount m w *
        decodedRetryPoolDyadicAttempts (z - (distance + 1))
          (decodedRetryPoolBackwardRequiredAtDistance m w z q distance)

/-- The required accepted blocks at a forward stage of a finite backward
schedule. -/
def decodedRetryPoolBackwardSchedule (m w z q : Nat) (stage : Fin z) : Nat :=
  decodedRetryPoolBackwardRequiredAtDistance m w z q (z - 1 - stage.1)

/-- The derived retry attempts at a forward stage. -/
def decodedRetryPoolBackwardAttempts (m w z q : Nat) (stage : Fin z) : Nat :=
  decodedRetryPoolDyadicAttempts stage.1
    (decodedRetryPoolBackwardSchedule m w z q stage)

/-- The terminal stage carries precisely the requested number of accepted
blocks. -/
theorem decodedRetryPoolBackwardSchedule_terminal (m w z q : Nat) (hz : 0 < z) :
    decodedRetryPoolBackwardSchedule m w z q ⟨z - 1, by omega⟩ = q := by
  change decodedRetryPoolBackwardRequiredAtDistance m w z q (z - 1 - (z - 1)) = q
  rw [Nat.sub_self]
  rfl

/-- Every nonterminal forward stage requests one physical block for each
retry attempt at its immediate successor. -/
theorem decodedRetryPoolBackwardSchedule_required_eq_physicalInputCount_mul_attempt_succ
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    decodedRetryPoolBackwardSchedule m w z q stage =
      physicalInputCount m w *
        decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩ := by
  let distance := z - 2 - stage.1
  have hcurrent : z - 1 - stage.1 = distance + 1 := by
    dsimp [distance]
    omega
  have hnext : z - 1 - (stage.1 + 1) = distance := by
    dsimp [distance]
    omega
  have hdyadicStage : z - (distance + 1) = stage.1 + 1 := by
    dsimp [distance]
    omega
  change decodedRetryPoolBackwardRequiredAtDistance m w z q (z - 1 - stage.1) =
    physicalInputCount m w *
      decodedRetryPoolDyadicAttempts (stage.1 + 1)
        (decodedRetryPoolBackwardRequiredAtDistance m w z q
          (z - 1 - (stage.1 + 1)))
  rw [hcurrent, decodedRetryPoolBackwardRequiredAtDistance, hdyadicStage, hnext]

/-- At depth two, the root demand is the physical input count times the
derived retry attempts of the terminal request. -/
theorem decodedRetryPoolBackwardSchedule_preterminal (m w z q : Nat) (hdepth : z = 2) :
    decodedRetryPoolBackwardSchedule m w z q ⟨0, by omega⟩ =
      physicalInputCount m w * decodedRetryPoolDyadicAttempts 1 q := by
  subst z
  change decodedRetryPoolBackwardRequiredAtDistance m w 2 q 1 =
    physicalInputCount m w * decodedRetryPoolDyadicAttempts 1 q
  rfl

/-- The forward-stage retry attempt is exactly the compiled dyadic attempt
count for that stage's required accepted blocks. -/
theorem decodedRetryPoolBackwardAttempts_eq_dyadicAttempts
    (m w z q : Nat) (stage : Fin z) :
    decodedRetryPoolBackwardAttempts m w z q stage =
      decodedRetryPoolDyadicAttempts stage.1
        (decodedRetryPoolBackwardSchedule m w z q stage) := rfl

/-- Every stage-local accepted-block request fits into its derived retry
attempt count. -/
theorem decodedRetryPoolBackwardSchedule_required_le_attempt
    (m w z q : Nat) (stage : Fin z) :
    decodedRetryPoolBackwardSchedule m w z q stage ≤
      decodedRetryPoolBackwardAttempts m w z q stage := by
  simpa [decodedRetryPoolBackwardAttempts] using
    decodedRetryPoolRequired_le_dyadicAttempts stage.1
      (decodedRetryPoolBackwardSchedule m w z q stage)

/-- Every stage-local retry count obeys the compiled dyadic shortage relation. -/
theorem decodedRetryPoolBackwardSchedule_attempt_le_dyadic_shortageSlack
    (m w z q : Nat) (stage : Fin z) :
    decodedRetryPoolBackwardAttempts m w z q stage ≤
      decodedRetryPoolDyadicDenominator stage.1 *
        (decodedRetryPoolBackwardAttempts m w z q stage -
          decodedRetryPoolBackwardSchedule m w z q stage + 1) := by
  simpa [decodedRetryPoolBackwardAttempts] using
    decodedRetryPoolDyadicAttempts_le_denominator_mul_shortageSlack stage.1
      (decodedRetryPoolBackwardSchedule m w z q stage)

/-- The actual root physical carrier has one physical-site coordinate for
every root retry attempt. -/
abbrev decodedRetryPoolBackwardRootRawCarrier (m w z q : Nat) (hz : 0 < z) :=
  Fin (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) × PhysicalSite m w

/-- The actual terminal good carrier retains one logical-site coordinate at
each of the exactly `z` finite stages. -/
abbrev decodedRetryPoolBackwardTerminalGoodCarrier (m w z q : Nat) :=
  Fin q × (Fin z → LogicalSite m w)

/-- The root raw carrier has the physical input count times the root retry
attempt count. -/
theorem decodedRetryPoolBackwardRootRawCarrier_card (m w z q : Nat) (hz : 0 < z) :
    Fintype.card (decodedRetryPoolBackwardRootRawCarrier m w z q hz) =
      physicalInputCount m w * decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩ := by
  calc
    Fintype.card (decodedRetryPoolBackwardRootRawCarrier m w z q hz) =
        decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩ * physicalInputCount m w := by
      simp [physicalInputCount]
    _ = physicalInputCount m w * decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩ :=
      Nat.mul_comm _ _

/-- The terminal good carrier has the requested number of outputs times the
logical output count raised to the exact finite depth. -/
theorem decodedRetryPoolBackwardTerminalGoodCarrier_card (m w z q : Nat) :
    Fintype.card (decodedRetryPoolBackwardTerminalGoodCarrier m w z q) =
      q * logicalOutputCount m w ^ z := by
  simp [logicalOutputCount]

end HH18Parameterized
end Distillation
end QEC
