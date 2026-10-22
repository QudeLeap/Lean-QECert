/-
Valuation-bound construction.

This module is intentionally parametric in a carrier and a family of actual
`Valuation`s.  It is a reusable local theorem: it does not claim that the
carrier is a complete global place space, that its divisors have a global
degree theory, or that the resulting submodule is finite-dimensional.  The
future all-place construction will instantiate this API only after it has
constructed the missing places above infinity.

The scalar-closure proof is derived from the finite-field valuation theorem;
no "constants are trivial" assumption is stored in the API.

-/

import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.FieldTheory.Finite.Valuation
import QEC.Coding.AlgebraicGeometry.Divisors.Divisor

namespace QEC.Coding.AlgebraicGeometry

open scoped WithZero

namespace ValuationBound

variable {k F P : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

/-- Functions whose valuation at every supplied place satisfies the divisor
bound.  This is an actual `Submodule`, constructed from valuation inequalities.

It is not named `L` because a global `L(G)` space must quantify over a proved
complete global place space, which has not yet been constructed. -/
def space (valuations : P → Valuation F ℤᵐ⁰) (G : Divisor P) : Submodule k F where
  carrier := { f | ∀ place, valuations place f ≤ WithZero.exp (G place) }
  zero_mem' := by
    intro place
    simp
  add_mem' hf hg := by
    intro place
    exact (valuations place).map_add_le (hf place) (hg place)
  smul_mem' c f hf := by
    intro place
    by_cases hc : c = 0
    · subst c
      simp
    · rw [Algebra.smul_def, (valuations place).map_mul,
        FiniteField.valuation_algebraMap_eq_one (valuations place) c hc, one_mul]
      exact hf place

/-- Increasing a divisor bound enlarges the associated valuation-bound space. -/
theorem space_mono (valuations : P → Valuation F ℤᵐ⁰) {G H : Divisor P}
    (hGH : G ≤ H) : space (k := k) valuations G ≤ space (k := k) valuations H := by
  intro f hf place
  exact (hf place).trans (WithZero.exp_le_exp.mpr (hGH place))

/-- Product closure follows directly from valuation multiplicativity and
additivity of the divisor bound; it does not use Riemann--Roch. -/
theorem mul_mem_space_add (valuations : P → Valuation F ℤᵐ⁰) {G H : Divisor P}
    {f g : F} (hf : f ∈ space (k := k) valuations G)
    (hg : g ∈ space (k := k) valuations H) :
    f * g ∈ space (k := k) valuations (G + H) := by
  intro place
  calc
    valuations place (f * g) = valuations place f * valuations place g :=
      (valuations place).map_mul f g
    _ ≤ WithZero.exp (G place) * WithZero.exp (H place) :=
      mul_le_mul' (hf place) (hg place)
    _ = WithZero.exp (G place + H place) :=
      (WithZero.exp_add _ _).symm
    _ = WithZero.exp ((G + H) place) := by rw [Finsupp.add_apply]

end ValuationBound

end QEC.Coding.AlgebraicGeometry
