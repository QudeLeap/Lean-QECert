import Mathlib.FieldTheory.RatFunc.Degree
import QEC.Coding.AlgebraicGeometry.Places.GlobalPlace

namespace QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation

open scoped RatFunc WithZero

variable (k : Type*) [Field k] [Finite k]

/-- The actual infinity-place order is the negative normalized rational
function degree. -/
theorem rationalInfinity_order_eq_neg_intDegree (f : RatFunc k) (hf : f ≠ 0) :
    GlobalPlace.order (GlobalPlace.rationalInfinity k) f = -f.intDegree := by
  classical
  change -WithZero.log (RatFunc.inftyValuation k f) = -f.intDegree
  rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero (F := k) hf,
    WithZero.log_exp]

/-- The same actual order, expanded through the normalized numerator and
denominator chosen by `RatFunc`. -/
theorem rationalInfinity_order_eq_denomDegree_sub_numDegree
    (f : RatFunc k) (hf : f ≠ 0) :
    GlobalPlace.order (GlobalPlace.rationalInfinity k) f =
      (f.denom.natDegree : ℤ) - f.num.natDegree := by
  rw [rationalInfinity_order_eq_neg_intDegree k f hf, RatFunc.intDegree]
  ring

/-- The infinity contribution cancels the numerator-minus-denominator degree
term exactly.  This is the terminal cancellation used by the finite-place
factorization construction in the next dependency step. -/
theorem rationalInfinity_order_add_normalizedDegree
    (f : RatFunc k) (hf : f ≠ 0) :
    GlobalPlace.order (GlobalPlace.rationalInfinity k) f +
        ((f.num.natDegree : ℤ) - f.denom.natDegree) = 0 := by
  rw [rationalInfinity_order_eq_neg_intDegree k f hf, RatFunc.intDegree]
  ring

end QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation
