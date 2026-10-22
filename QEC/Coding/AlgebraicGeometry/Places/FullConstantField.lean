import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.RatFunc.IntermediateField

/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li, Lean-QEC contributors
-/

/-!
# Full constant fields

The source-facing Riemann--Roch formula with constant term `1` requires that
the supplied field of constants be relatively algebraically closed in the
function field.  This module records that standard function-field hypothesis
and identifies it with Mathlib's relative algebraic closure.

The interface is adapted from Guanghao Li's Apache-2.0 formalization
`vaca22/riemann-roch-function-fields`.  It contains no genus, divisor-degree,
duality, or Riemann--Roch conclusion.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped RatFunc

/-- Every element of `F` algebraic over the supplied constant field `k` is
already a constant.  This is the standard full-constant-field hypothesis for
an algebraic function field. -/
class IsFullConstantField (k F : Type*) [Field k] [Field F] [Algebra k F] : Prop where
  /-- Algebraic elements of the function field come from the constant field. -/
  algebraic_mem : ∀ x : F, IsAlgebraic k x → ∃ c : k, x = algebraMap k F c

namespace IsFullConstantField

variable (k F : Type*) [Field k] [Field F] [Algebra k F] [IsFullConstantField k F]

/-- An algebraic function-field element belongs to the range of the constant
embedding. -/
theorem mem_range {x : F} (hx : IsAlgebraic k x) :
    x ∈ Set.range (algebraMap k F) := by
  obtain ⟨c, hc⟩ := IsFullConstantField.algebraic_mem (k := k) (F := F) x hx
  exact ⟨c, hc.symm⟩

end IsFullConstantField

/-- Full constants are equivalent to the relative algebraic closure of `k`
inside `F` being the bottom intermediate field. -/
theorem isFullConstantField_iff_algebraicClosure_eq_bot
    (k F : Type*) [Field k] [Field F] [Algebra k F] :
    IsFullConstantField k F ↔ algebraicClosure k F = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨c, rfl⟩ := h.algebraic_mem x (mem_algebraicClosure_iff.mp hx)
    exact (⊥ : IntermediateField k F).algebraMap_mem c
  · intro h
    refine ⟨fun x hx => ?_⟩
    have hxb : x ∈ (⊥ : IntermediateField k F) :=
      h ▸ mem_algebraicClosure_iff.mpr hx
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hxb
    exact ⟨c, hc.symm⟩

/-- The rational function field has exactly its coefficient field as its
relative algebraic closure. -/
instance ratFuncIsFullConstantField (k : Type*) [Field k] :
    IsFullConstantField k (RatFunc k) where
  algebraic_mem x hx := by
    by_contra h
    exact RatFunc.transcendental_of_ne_C x h hx

end QEC.Coding.AlgebraicGeometry
