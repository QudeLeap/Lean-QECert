/-
Global-place carrier.

`GlobalPlace k F` is the all-place carrier representation: a normalized, surjective
integer-valued valuation of `F`, over the supplied finite constant field `k`.
It is not an affine height-one spectrum, so it can represent both finite
places and places lying above the rational-function place at infinity.  The valuation
subring and residue field below are the actual Mathlib constructions.

The finite-constant condition is a theorem, not a stored conclusion: every
valuation on an algebra over a finite field is trivial on nonzero constants.
No divisor degree, finite residue degree, Riemann--Roch space, finiteness, or
evaluation-code law is a field of this structure.

This module constructs the rational-function infinity place itself.  Extending
that valuation through a general finite function-field extension remains a
separate construction: Mathlib's valuation-extension API records an existing
extension but does not supply its existence.  Consequently this file never
claims a witness above infinity for an arbitrary `FunctionField k F`.

-/

import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.FieldTheory.Finite.Valuation
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

namespace QEC.Coding.AlgebraicGeometry

open scoped WithZero

/-- A global function-field place is a normalized rank-one discrete valuation,
encoded directly as a surjection onto `ℤᵐ⁰`.  Keeping the normalized valuation,
rather than quotienting equivalent valuations, makes its integer order usable
for divisor coefficients and local bounds. -/
structure GlobalPlace (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F] where
  valuation : Valuation F ℤᵐ⁰
  normalized : Function.Surjective valuation

namespace GlobalPlace

variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

/-- A global place is trivial on the supplied finite constant field. -/
theorem trivialOnConstants (P : GlobalPlace k F) : P.valuation.IsTrivialOn k := by
  infer_instance

/-- A uniformizer obtained from the normalized integer value group. -/
noncomputable def uniformizer (P : GlobalPlace k F) : F :=
  Classical.choose (P.normalized (WithZero.exp (-1 : ℤ)))

/-- The chosen uniformizer has valuation `exp (-1)`, exhibiting the discrete
integer normalization without storing any divisor or Riemann--Roch law. -/
theorem valuation_uniformizer (P : GlobalPlace k F) :
    P.valuation P.uniformizer = WithZero.exp (-1 : ℤ) :=
  Classical.choose_spec (P.normalized (WithZero.exp (-1 : ℤ)))

/-- The normalized integer order of a function at a place.  Its intended use
is for nonzero functions; `WithZero.log 0 = 0` is only a totalization device.
The sign is chosen so that the uniformizer has order `1`. -/
def order (P : GlobalPlace k F) (f : F) : ℤ :=
  -WithZero.log (P.valuation f)

/-- The normalized uniformizer has order one. -/
theorem order_uniformizer (P : GlobalPlace k F) : order P P.uniformizer = 1 := by
  rw [order, valuation_uniformizer]
  simp

/-- Orders add on nonzero products, by valuation multiplicativity. -/
theorem order_mul (P : GlobalPlace k F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    order P (f * g) = order P f + order P g := by
  unfold order
  rw [(P.valuation).map_mul f g,
    WithZero.log_mul ((P.valuation).ne_zero_iff.mpr hf)
      ((P.valuation).ne_zero_iff.mpr hg)]
  ring

/-- Inversion negates order. -/
theorem order_inv (P : GlobalPlace k F) (f : F) :
    order P f⁻¹ = -order P f := by
  unfold order
  rw [(P.valuation).map_inv, WithZero.log_inv]

/-- Every nonzero element of the finite constant field has order zero. -/
theorem order_algebraMap (P : GlobalPlace k F) (a : k) (ha : a ≠ 0) :
    order P (algebraMap k F a) = 0 := by
  simp [order, (trivialOnConstants P).eq_one a ha]

/-- The valuation ring attached to a global place. -/
abbrev valuationRing (P : GlobalPlace k F) : ValuationSubring F :=
  P.valuation.valuationSubring

/-- The residue field of a global place. -/
abbrev residueField (P : GlobalPlace k F) : Type _ :=
  IsLocalRing.ResidueField (valuationRing P)

/-- Reduction from the valuation ring to the residue field at a global place. -/
def residue (P : GlobalPlace k F) : valuationRing P →+* residueField P :=
  IsLocalRing.residue _

/-- Integral elements reduce to zero exactly when they lie in the maximal ideal. -/
theorem residue_eq_zero_iff (P : GlobalPlace k F) (f : valuationRing P) :
    residue P f = 0 ↔ f ∈ IsLocalRing.maximalIdeal (valuationRing P) :=
  IsLocalRing.residue_eq_zero_iff f

/-- Membership in the valuation ring is precisely the non-pole bound. -/
theorem mem_valuationRing_iff (P : GlobalPlace k F) (f : F) :
    f ∈ valuationRing P ↔ P.valuation f ≤ 1 :=
  P.valuation.mem_valuationSubring_iff f

/-- A function is regular at a place exactly when it lies in its valuation
ring. -/
def RegularAt (P : GlobalPlace k F) (f : F) : Prop := P.valuation f ≤ 1

theorem regularAt_iff_mem_valuationRing (P : GlobalPlace k F) (f : F) :
    RegularAt P f ↔ f ∈ valuationRing P :=
  (mem_valuationRing_iff P f).symm

/-- For a nonzero function, regularity is the nonnegative order condition.
This is the sign convention used later in the valuation-bound RR submodule. -/
theorem regularAt_iff_order_nonnegative (P : GlobalPlace k F) {f : F} (hf : f ≠ 0) :
    RegularAt P f ↔ 0 ≤ order P f := by
  change P.valuation f ≤ 1 ↔ 0 ≤ -WithZero.log (P.valuation f)
  rw [neg_nonneg]
  symm
  simpa using WithZero.log_le_iff_le_exp ((P.valuation).ne_zero_iff.mpr hf) (a := 0)

/-- Evaluate a function already proved regular at the place.  This is not a
total map `F → residueField P`: functions with a pole are intentionally
outside its domain. -/
def evaluate (P : GlobalPlace k F) : valuationRing P →+* residueField P :=
  residue P

/-- Residue evaluation of a function together with a proof that it is regular
at the place.  No total rational-function evaluation is introduced. -/
noncomputable def evaluateRegular (P : GlobalPlace k F) (f : F) (hf : RegularAt P f) :
    residueField P :=
  evaluate P ⟨f, (mem_valuationRing_iff P f).mpr hf⟩

/-- The rational-function infinity valuation is surjective onto the normalized
integer value group. -/
theorem rationalInfinity_surjective (k : Type*) [Field k] [DecidableEq (RatFunc k)] :
    Function.Surjective (RatFunc.inftyValuation k) := by
  classical
  intro x
  rcases GroupWithZero.eq_zero_or_unit x with (rfl | ⟨x, rfl⟩)
  · exact ⟨0, by simp⟩
  · refine ⟨RatFunc.X ^ WithZero.log x.val, ?_⟩
    rw [RatFunc.inftyValuation.X_zpow]
    exact WithZero.exp_log (Units.ne_zero x)

/-- The genuine place at infinity of the rational function field. -/
noncomputable def rationalInfinity (k : Type*) [Field k] [Finite k] : GlobalPlace k (RatFunc k) := by
  letI : DecidableEq (RatFunc k) := Classical.decEq _
  exact
    { valuation := RatFunc.inftyValuation k
      normalized := rationalInfinity_surjective k }

end GlobalPlace

end QEC.Coding.AlgebraicGeometry
