import QEC.Coding.AlgebraicGeometry.Differentials.ParameterDifferentialOrder
import QEC.Coding.AlgebraicGeometry.Differentials.RatFuncDifferentialOrder

/-!
# Differential orders through a rational field equivalence

The target keeps its existing rational-base presentation. A constant-field
equivalence with k(t) need not identify t with that presentation's generator.
The chain rule explicitly records the derivative of the image of t.
-/

namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [Algebra.IsSeparable (RatFunc k) K] [FiniteDimensional (RatFunc k) K]

/-- The chain rule, without changing the target's chosen rational-base algebra. -/
theorem functionFieldDerivation_rationalEquiv (e : RatFunc k ≃ₐ[k] K) (f : RatFunc k) :
    functionFieldDerivation (k := k) (e f) =
      e (functionFieldDerivation (k := k) f) *
        functionFieldDerivation (k := k) (e RatFunc.X) := by
  let D := functionFieldDerivation (k := k) (F := K)
  let Dr := functionFieldDerivation (k := k) (F := RatFunc k)
  let Dt : Derivation k (RatFunc k) (RatFunc k) :=
    { toLinearMap := e.symm.toLinearMap.comp (D.toLinearMap.comp e.toLinearMap)
      map_one_eq_zero' := by simp
      leibniz' := by
        intro a b
        change e.symm (D (e (a * b))) =
          a * e.symm (D (e b)) + b * e.symm (D (e a))
        simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add,
          e.symm_apply_apply] }
  have h : Dt = e.symm (D (e RatFunc.X)) • Dr := by
    apply (RatFuncDerivation.rationalDerivationEquiv (k := k)
      (M := RatFunc k)).injective
    change e.symm (D (e RatFunc.X)) = e.symm (D (e RatFunc.X)) * Dr RatFunc.X
    rw [show Dr RatFunc.X = 1 from functionFieldDerivation_apply_X, mul_one]
  have hf := congrArg e (Derivation.congr_fun h f)
  change e (e.symm (D (e f))) = e (e.symm (D (e RatFunc.X)) * Dr f) at hf
  simpa only [e.apply_symm_apply, map_mul, mul_comm] using hf

variable [Finite k]

/-- Intrinsic differential order under a rational field equivalence. The
order identity is the defining equality of the transported place. -/
theorem differentialGenerator_order_rationalEquiv
    (e : RatFunc k ≃ₐ[k] K) (P : GlobalPlace k K)
    (R : GlobalPlace k (RatFunc k)) (horder : ∀ f, P.order (e f) = R.order f) :
    ∃ _hd : functionFieldDerivation (k := k) (e RatFunc.X) ≠ 0,
      differentialOrder P (functionFieldDifferentialGenerator (k := k) (F := K))
        functionFieldDifferentialGenerator_ne_zero =
      differentialOrder R (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        functionFieldDifferentialGenerator_ne_zero -
      P.order (functionFieldDerivation (k := k) (e RatFunc.X)) := by
  let t := R.uniformizer
  have ht : t ≠ 0 := by
    intro hz
    have h := R.order_uniformizer
    change R.order t = 1 at h
    rw [hz] at h
    simp [GlobalPlace.order] at h
  have het : e t ≠ 0 := (map_ne_zero e).mpr ht
  have hRt : R.order t = 1 := R.order_uniformizer
  have hPt : P.order (e t) = 1 := (horder t).trans hRt
  obtain ⟨hdr, hr⟩ := differentialGenerator_order_of_order_one_or_neg_one R t ht (.inl hRt)
  obtain ⟨hdp, hp⟩ := differentialGenerator_order_of_order_one_or_neg_one P (e t) het (.inl hPt)
  have hdx : functionFieldDerivation (k := k) (e RatFunc.X) ≠ 0 := by
    intro hz
    exact hdp (by rw [functionFieldDerivation_rationalEquiv e t, hz, mul_zero])
  refine ⟨hdx, ?_⟩
  rw [functionFieldDerivation_rationalEquiv e t,
    P.order_mul ((map_ne_zero e).mpr hdr) hdx, horder, horder] at hp
  rw [hp, hr]
  ring

/-- At any rational-base place where the variable is a unit, dt has order
zero. Classification includes all finite-degree places, not just rational points. -/
theorem rational_differentialGenerator_order_of_order_X_zero
    (R : GlobalPlace k (RatFunc k)) (hX : R.order RatFunc.X = 0) :
    differentialOrder R (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
      functionFieldDifferentialGenerator_ne_zero = 0 := by
  obtain ⟨p, rfl⟩ := (GlobalPlace.rationalPlaceEquiv (k := k)).surjective R
  cases p with
  | none =>
    change (GlobalPlace.rationalInfinity k).order RatFunc.X = 0 at hX
    rw [RationalBaseInfinityCancellation.rationalInfinity_order_eq_neg_intDegree
      k RatFunc.X RatFunc.X_ne_zero, RatFunc.intDegree_X] at hX
    norm_num at hX
  | some p => exact Differential.differentialOrder_generator_rationalAdic p

end

end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
