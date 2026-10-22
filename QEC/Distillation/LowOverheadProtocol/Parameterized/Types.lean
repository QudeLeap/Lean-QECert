import QEC.Distillation.LowOverheadProtocol.Core.NoisyInput

/-!
# Parameterized HH18 code carriers

This module exposes the actual finite carriers and transversal target for an
admissible HH18 punctured Reed--Muller block.  It deliberately keeps the
parameters symbolic: the physical input count, logical output count, and
distance are derived from the finite coordinate types and the constructed
code, rather than specializing the fixed `[[15,1,3]]` block.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit

attribute [local instance 100] Fintype.ofFinite

/-- The retained coordinates of a parameterized HH18 physical block. -/
abbrev PhysicalSite (m w : Nat) :=
  HH18PuncturedReedMuller.PhysicalSite m w

/-- The removed coordinates indexing the decoded logical register. -/
abbrev LogicalSite (m w : Nat) :=
  HH18PuncturedReedMuller.LogicalSite m w

/-- The actual physical register consumed by one parameterized block. -/
abbrev PhysicalRegister (m w : Nat) := QubitRegister (PhysicalSite m w)

/-- The actual logical register produced by decoding one parameterized block. -/
abbrev LogicalRegister (m w : Nat) := QubitRegister (LogicalSite m w)

/-- A complete binary Pauli-`Z` error history on a parameterized physical block. -/
abbrev PhysicalErrorWord (m w : Nat) :=
  HH18NoisyInput.PhysicalErrorWord m w

/-- The number of physical `T†` resources consumed by one block. -/
def physicalInputCount (m w : Nat) : Nat := Fintype.card (PhysicalSite m w)

/-- The number of logical output ports provided by one decoded block. -/
def logicalOutputCount (m w : Nat) : Nat := Fintype.card (LogicalSite m w)

/-- The common CSS distance derived for the parameterized HH18 code. -/
def codeDistance (r w : Nat) : Nat := binomialTail (r + 1) w

/-- The physical resource count is the retained-coordinate binomial tail. -/
theorem physicalInputCount_eq_binomialTail (m w : Nat) :
    physicalInputCount m w = binomialTail m w := by
  simpa [physicalInputCount] using keptPoint_card_eq_binomialTail m w

/-- The logical output count is the removed-coordinate cumulative binomial sum. -/
theorem logicalOutputCount_eq_binomialUpTo (m w : Nat) :
    logicalOutputCount m w = binomialUpTo m w := by
  simpa [logicalOutputCount, binomialUpTo] using lowPoint_card_eq_sum_choose m w

/-- The named distance is the exact punctured Reed--Muller distance formula. -/
theorem codeDistance_eq_binomialTail (r w : Nat) :
    codeDistance r w = binomialTail (r + 1) w :=
  rfl

/-- The named distance is attained by the actual source-valid parameterized
HH18 CSS stabilizer, rather than carried as detached protocol metadata. -/
theorem codeDistance_semanticDistance {w r m : Nat} (h : Admissible w r m) :
    StabilizerCode.SemanticStabilizerDistance
      (HH18PuncturedReedMuller.sourceValidStabilizer h) (codeDistance r w) := by
  simpa only [codeDistance] using HH18PuncturedReedMuller.semanticDistance h

/-- The normalized logical-plus seed on the actual decoded register. -/
noncomputable def logicalPlus (m w : Nat) : LogicalRegister m w :=
  Triorthogonal.BinaryRowFamily.logicalPlusState (LogicalSite m w)

/-- The logical-plus seed is normalized for every finite parameterized register. -/
theorem logicalPlus_norm (m w : Nat) : ‖logicalPlus m w‖ = 1 := by
  have hinner := Triorthogonal.BinaryRowFamily.logicalPlusState_inner_self
    (LogicalSite m w)
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hsquare : ‖logicalPlus m w‖ ^ 2 = 1 := by
    change ‖Triorthogonal.BinaryRowFamily.logicalPlusState (LogicalSite m w)‖ ^ 2 = 1
    apply Complex.ofReal_injective
    rw [Complex.ofReal_pow]
    exact hinner
  nlinarith [norm_nonneg (logicalPlus m w)]

/-- The #759 encoded realization of the parameterized logical-plus seed. -/
noncomputable def encodedLogicalPlus {w r m : Nat} (h : Admissible w r m) :
    PhysicalRegister m w :=
  (HH18PuncturedReedMuller.encodedCode h).encode (logicalPlus m w)

/-- The actual transversal inverse-`T` transport implements logical `T`. -/
theorem physicalTInv_implements_logicalT {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    (HH18PuncturedReedMuller.encodedCode h).ImplementsLogicalGate
      (HH18PuncturedReedMuller.physicalTInv w m)
      (HH18PuncturedReedMuller.logicalT w m) :=
  HH18PuncturedReedMuller.physicalTInv_implements_logicalT h hdegree

/-- The concrete error-free physical target branch for a parameterized block. -/
noncomputable def physicalTInvBranch {w r m : Nat}
    (h : Admissible w r m) (_hdegree : 3 * r < m) : PhysicalRegister m w :=
  HH18PuncturedReedMuller.physicalTInv w m (encodedLogicalPlus h)

/-- The parameterized physical target is exactly the encoded logical-`T` target. -/
theorem physicalTInvBranch_eq_logicalT {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    physicalTInvBranch h hdegree =
      (HH18PuncturedReedMuller.encodedCode h).encode
        (HH18PuncturedReedMuller.logicalT w m (logicalPlus m w)) := by
  simpa only [physicalTInvBranch, encodedLogicalPlus] using
    (physicalTInv_implements_logicalT h hdegree (logicalPlus m w))

end HH18Parameterized
end Distillation
end QEC
