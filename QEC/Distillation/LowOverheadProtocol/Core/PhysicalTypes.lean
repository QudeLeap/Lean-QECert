import QEC.Distillation.LowOverheadProtocol.Core.NoisyInput

/-!
# HH18 physical carrier types

The fixed `[[15,1,3]]` carrier aliases and its logical-plus normalization are
shared by the resource consumer and the total decoder without importing either
implementation layer.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Protocol

open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit

universe u

attribute [local instance 100] Fintype.ofFinite

/-- The physical input sites of the fixed HH18 `[[15,1,3]]` block. -/
abbrev PhysicalSite := HH18PuncturedReedMuller.PhysicalSite 4 0

/-- The actual physical register measured and postselected by this route. -/
abbrev PhysicalRegister := QubitRegister PhysicalSite

/-- The logical register decoded after successful HH18 postselection. -/
abbrev LogicalRegister := QubitRegister (HH18PuncturedReedMuller.LogicalSite 4 0)

/-- A full independent binary resource-error history. -/
abbrev PhysicalErrorWord := HH18NoisyInput.PhysicalErrorWord 4 0

/-- The registered HH18 logical-plus input is normalized.  This public carrier
fact is shared by the physical branch and ideal-decoder layers. -/
theorem hh18LogicalPlusInput_norm : ‖HH18NoisyInput.hh18LogicalPlusInput‖ = 1 := by
  have hinner := Triorthogonal.BinaryRowFamily.logicalPlusState_inner_self
    (HH18PuncturedReedMuller.LogicalSite 4 0)
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hsquare : ‖HH18NoisyInput.hh18LogicalPlusInput‖ ^ 2 = 1 := by
    change ‖Triorthogonal.BinaryRowFamily.logicalPlusState
      (HH18PuncturedReedMuller.LogicalSite 4 0)‖ ^ 2 = 1
    apply Complex.ofReal_injective
    rw [Complex.ofReal_pow]
    exact hinner
  nlinarith [norm_nonneg HH18NoisyInput.hh18LogicalPlusInput]

end HH18Protocol
end Distillation
end QEC
