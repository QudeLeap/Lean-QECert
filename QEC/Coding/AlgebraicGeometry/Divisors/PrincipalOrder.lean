/-
Principal-order family.

For a nonzero function, represented here by a unit of the function field, the
existing all-place order gives a total integer-valued family on `GlobalPlace`.
It is intentionally a function, not a `Finsupp`: proving that only finitely
many places have nonzero order requires a global place-completeness and
finite-support construction.

Accordingly this file proves only pointwise identities forced by the valuation.
It does not define a principal divisor, its degree, a product formula, or a
negative-degree theorem.

-/

import QEC.Coding.AlgebraicGeometry.Places.GlobalPlace

namespace QEC.Coding.AlgebraicGeometry

namespace GlobalPlace

variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

/-- The pointwise order family of a nonzero function.  Its codomain is the
ordinary function type on all global places; no finite-support assertion is
made at this layer. -/
def principalOrder (f : Fˣ) : GlobalPlace k F → ℤ := fun P => order P f

/-- Principal-order families add under multiplication of nonzero functions. -/
theorem principalOrder_mul (f g : Fˣ) :
    principalOrder (k := k) (F := F) (f * g) =
      principalOrder (k := k) (F := F) f + principalOrder (k := k) (F := F) g := by
  funext P
  simpa [principalOrder] using
    order_mul P (f := (f : F)) (g := (g : F)) f.ne_zero g.ne_zero

/-- Principal-order families negate under inversion. -/
theorem principalOrder_inv (f : Fˣ) :
    principalOrder (k := k) (F := F) f⁻¹ = -principalOrder (k := k) (F := F) f := by
  funext P
  simpa [principalOrder] using order_inv P (f : F)

/-- A nonzero constant has pointwise principal order zero at every global
place.  This is derived from finite-field valuation triviality, not stored in
the place data. -/
theorem principalOrder_constants (a : kˣ) :
    principalOrder (k := k) (F := F) (Units.map (algebraMap k F) a : Fˣ) = 0 := by
  funext P
  simpa [principalOrder] using order_algebraMap P (a : k) a.ne_zero

end GlobalPlace

end QEC.Coding.AlgebraicGeometry
