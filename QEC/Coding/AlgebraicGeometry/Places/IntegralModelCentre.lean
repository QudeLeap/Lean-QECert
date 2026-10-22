import QEC.Coding.AlgebraicGeometry.Places.HeightOneOrder
import QEC.Coding.AlgebraicGeometry.Places.TwoChartGlobalPlace

/-!
# The actual centre of a place on a Dedekind integral model

A model contained in the valuation ring, with a nonzero element vanishing
at the place, has a height-one centre. Its normalized order is exactly the
supplied place's order. This is not a choice of an unrelated prime above a
base place.
-/

namespace QEC.Coding.AlgebraicGeometry

noncomputable section

/-- Construct the height-one centre of the supplied actual place on any
Dedekind fraction model contained in its valuation ring. -/
theorem GlobalPlace.exists_heightOne_order_eq
    {k E : Type*} [Field k] [Finite k] [Field E] [Algebra k E]
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Algebra R E] [IsFractionRing R E] (Q : GlobalPlace k E)
    (hR : ∀ r : R, Q.valuation (algebraMap R E r) ≤ 1)
    (hn : ∃ r : R, r ≠ 0 ∧ Q.valuation (algebraMap R E r) < 1) :
    ∃ H : IsDedekindDomain.HeightOneSpectrum R,
      H.valuationSubringAtPrime E = Q.valuationRing ∧
        (heightOnePlace (k := k) (K := E) H).order = Q.order := by
  let f : R →+* Q.valuationRing :=
    (algebraMap R E).codRestrict Q.valuationRing hR
  let I : Ideal R := Ideal.comap f (IsLocalRing.maximalIdeal Q.valuationRing)
  letI : I.IsPrime := Ideal.comap_isPrime _ _
  have hIne : I ≠ ⊥ := by
    obtain ⟨r, hr, hrv⟩ := hn
    intro heq
    have hrI : r ∈ I := (Q.valuation.mem_maximalIdeal_iff).mpr hrv
    rw [heq, Ideal.mem_bot] at hrI
    exact hr hrI
  let H : IsDedekindDomain.HeightOneSpectrum R := ⟨I, inferInstance, hIne⟩
  have hle : H.valuationSubringAtPrime E ≤ Q.valuationRing := by
    rintro x ⟨a, s, hs, rfl⟩
    have hsnot : ¬ Q.valuation (algebraMap R E s) < 1 := by
      intro hlt
      exact hs ((Q.valuation.mem_maximalIdeal_iff).mpr hlt)
    have hsone : Q.valuation (algebraMap R E s) = 1 :=
      le_antisymm (hR s) (le_of_not_gt hsnot)
    change Q.valuation (algebraMap R E a * (algebraMap R E s)⁻¹) ≤ 1
    rw [map_mul, map_inv₀, hsone, inv_one, mul_one]
    exact hR a
  have hQnontrivial : Q.valuation.IsNontrivial := by
    obtain ⟨r, hr, hv⟩ := hn
    refine ⟨algebraMap R E r, ?_, ne_of_lt hv⟩
    apply Q.valuation.ne_zero_iff.mpr
    simpa only [map_zero] using (IsFractionRing.injective R E).ne hr
  have hnotop : Q.valuationRing ≠ ⊤ := by
    intro htop
    exact ((Valuation.valuationSubring_eq_top_iff (v := Q.valuation)).mp htop) hQnontrivial
  have hring : H.valuationSubringAtPrime E = Q.valuationRing :=
    ValuationSubring.eq_of_le_of_ne_top _ hle hnotop
  refine ⟨H, hring, ?_⟩
  have hval : H.valuation E = Q.valuation :=
    normalizedValuation_eq_of_isEquiv _ _ (H.valuation_surjective E) Q.normalized
      ((Valuation.isEquiv_iff_valuationSubring _ _).mpr
        (H.valuationSubringAtPrime_eq_valuationSubring.symm.trans hring))
  funext x
  change -WithZero.log (H.valuation E x) = -WithZero.log (Q.valuation x)
  rw [hval]

end

end QEC.Coding.AlgebraicGeometry
