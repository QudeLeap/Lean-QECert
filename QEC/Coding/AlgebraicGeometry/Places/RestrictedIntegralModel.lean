import QEC.Coding.AlgebraicGeometry.Places.NormalizedRestriction
import QEC.Coding.AlgebraicGeometry.Places.IntegralModelCentre
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Integral models under one fixed ambient place

Restrict the given ambient place to the chosen finite subfield, take its
actual valuation ring, and form the integral closure in the ambient field.
The centre constructed below recovers the given ambient normalized order.
Thus different coordinate-window bases can use the same ambient place.
-/

namespace QEC.Coding.AlgebraicGeometry.GlobalPlace

noncomputable section

variable {k F E : Type*} [Field k] [Finite k] [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E] [Algebra.IsAlgebraic F E]
    (Q : GlobalPlace k E)

local notation "P" => Q.restrict (F := F)
local notation "A" => GlobalPlace.valuationRing (GlobalPlace.restrict (F := F) Q)
local notation "C" => integralClosure A E

variable [Algebra (Q.restrict (F := F)).valuationRing E]
    [IsScalarTower (Q.restrict (F := F)).valuationRing F E]

/-- The literal integral closure of the restricted valuation ring lies in
the original ambient valuation ring. -/
theorem restrictedIntegralClosure_le_valuationRing :
    (C).toSubring ≤ Q.valuationRing.toSubring := by
  letI : IsIntegrallyClosedIn Q.valuationRing E :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn E).mp inferInstance
  change (integralClosure A E).toSubring ≤ Q.valuation.integer
  rw [Subring.integralClosure_le_iff]
  intro a
  have ha : (a : F) ∈ (Q.valuation.comap (algebraMap F E)).valuationSubring :=
    (show (P).valuationRing ≤ (Q.valuation.comap (algebraMap F E)).valuationSubring from
      le_of_eq Q.restrict_valuationRing) a.property
  change Q.valuation (algebraMap F E (a : F)) ≤ 1 at ha
  change Q.valuation (algebraMap A E a) ≤ 1
  rwa [IsScalarTower.algebraMap_apply A F E]

/-- At every finite coordinate-window base, the actual integral closure
contains a height-one prime with precisely the originally supplied ambient
order. This constructs the prime, rather than assuming order compatibility. -/
theorem exists_restrictedIntegralClosure_prime
    [IsDedekindDomain C] [IsFractionRing C E] :
    ∃ H : IsDedekindDomain.HeightOneSpectrum C,
      H.valuationSubringAtPrime E = Q.valuationRing ∧
        (heightOnePlace (k := k) (K := E) H).order = Q.order := by
  apply Q.exists_heightOne_order_eq C
  · intro r
    exact Q.restrictedIntegralClosure_le_valuationRing r.property
  · have hu0 : (P).uniformizer ≠ 0 := by
      apply (P).valuation.ne_zero_iff.mp
      rw [(P).valuation_uniformizer]
      exact WithZero.exp_ne_zero
    have hult : (P).valuation (P).uniformizer < 1 := by
      rw [(P).valuation_uniformizer, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
    let u : A := ⟨(P).uniformizer, hult.le⟩
    refine ⟨algebraMap A C u, ?_, ?_⟩
    · intro hzero
      have hzero' := congrArg (algebraMap C E) hzero
      rw [map_zero, ← IsScalarTower.algebraMap_apply A C E,
        IsScalarTower.algebraMap_apply A F E] at hzero'
      apply hu0
      apply (algebraMap F E).injective
      rw [map_zero]
      exact hzero'
    · rw [← IsScalarTower.algebraMap_apply A C E, IsScalarTower.algebraMap_apply A F E]
      exact (Q.restrict_valuation_lt_one_iff (P).uniformizer).mp hult

end

end QEC.Coding.AlgebraicGeometry.GlobalPlace
