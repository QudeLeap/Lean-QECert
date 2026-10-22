import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The residue field of a height-one localization

This small certificate identifies the quotient at a height-one prime with the
residue field of its associated valuation subring.  Keeping this generic
localization argument separate prevents concrete function-field towers from
being unfolded while the equivalence is constructed.
-/

namespace Valuation

/-- Equal normalized integer valuations have canonically equivalent residue
fields, without requiring their valuation subring types to reduce
definitionally. -/
noncomputable def residueFieldEquivOfEq {F : Type*} [Field F]
    (v w : Valuation F (WithZero (Multiplicative ℤ))) (h : v = w) :
    IsLocalRing.ResidueField v.valuationSubring ≃+*
      IsLocalRing.ResidueField w.valuationSubring := by
  cases h
  exact RingEquiv.refl _

end Valuation

namespace IsDedekindDomain.HeightOneSpectrum

noncomputable section

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The prime quotient of a Dedekind domain is the residue field of the
valuation attached to that height-one prime. -/
noncomputable def quotientResidueEquivValuation
    (H : IsDedekindDomain.HeightOneSpectrum R) :
    (R ⧸ H.asIdeal) ≃+*
      IsLocalRing.ResidueField ((H.valuation K).valuationSubring) := by
  let e₁ : (R ⧸ H.asIdeal) ≃+*
      IsLocalRing.ResidueField (H.valuationSubringAtPrime K) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal H.asIdeal
      (H.valuationSubringAtPrime K)
  let e₂ : H.valuationSubringAtPrime K ≃+*
      (H.valuation K).valuationSubring := by
    rw [H.valuationSubringAtPrime_eq_valuationSubring]
  exact e₁.trans (IsLocalRing.ResidueField.mapEquiv e₂)

end

end IsDedekindDomain.HeightOneSpectrum
