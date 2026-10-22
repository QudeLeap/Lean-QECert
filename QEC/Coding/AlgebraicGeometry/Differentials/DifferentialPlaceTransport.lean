import QEC.Coding.AlgebraicGeometry.Differentials.ParameterDifferentialOrder
import QEC.Coding.AlgebraicGeometry.Places.IntegralModelCentre

/-!
# Reading intrinsic differential orders on actual place centres

Equal normalized orders identify the local differential-generator order.
The height-one prime of a place's own DVR recovers that original order.
-/

namespace QEC.Coding.AlgebraicGeometry

noncomputable section

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]

local instance placeTransportDVR (P : GlobalPlace k K) :
    IsDiscreteValuationRing P.valuationRing := P.valuationRing_isDiscreteValuationRing

theorem GlobalPlace.heightOne_valuationRing_order (P : GlobalPlace k K)
    (H : IsDedekindDomain.HeightOneSpectrum P.valuationRing) :
    (heightOnePlace (k := k) (K := K) H).order = P.order := by
  have hlt : P.valuation P.uniformizer < 1 := by
    rw [P.valuation_uniformizer, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  let t : P.valuationRing := ⟨P.uniformizer, hlt.le⟩
  have ht : t ≠ 0 := by
    intro hz
    have h := P.order_uniformizer
    have htzero : P.uniformizer = 0 := congrArg (fun x : P.valuationRing => (x : K)) hz
    rw [htzero] at h
    simp [GlobalPlace.order] at h
  obtain ⟨J, _, hJ⟩ := P.exists_heightOne_order_eq P.valuationRing
    (fun r => r.property) ⟨t, ht, hlt⟩
  have heq : H = J := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    exact (IsLocalRing.eq_maximalIdeal H.isMaximal).trans
      (IsLocalRing.eq_maximalIdeal J.isMaximal).symm
  simpa only [heq] using hJ

namespace FunctionFieldDifferential

variable [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [Algebra.IsSeparable (RatFunc k) K] [FiniteDimensional (RatFunc k) K]

theorem differentialGenerator_order_eq_of_order_eq (P Q : GlobalPlace k K)
    (horder : P.order = Q.order) :
    differentialOrder P (functionFieldDifferentialGenerator (k := k) (F := K))
      functionFieldDifferentialGenerator_ne_zero =
    differentialOrder Q (functionFieldDifferentialGenerator (k := k) (F := K))
      functionFieldDifferentialGenerator_ne_zero := by
  have ht : P.uniformizer ≠ 0 := by
    intro hz
    have h := P.order_uniformizer
    rw [hz] at h
    simp [GlobalPlace.order] at h
  have hQ : Q.order P.uniformizer = 1 := by rw [← horder, P.order_uniformizer]
  obtain ⟨_, hP⟩ := differentialGenerator_order_of_order_one_or_neg_one
    P P.uniformizer ht (.inl P.order_uniformizer)
  obtain ⟨_, hQ⟩ := differentialGenerator_order_of_order_one_or_neg_one
    Q P.uniformizer ht (.inl hQ)
  rw [hP, hQ, horder]

end FunctionFieldDifferential

end

end QEC.Coding.AlgebraicGeometry
