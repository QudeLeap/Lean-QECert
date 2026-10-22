import QEC.Coding.ExpanderCodes.LPSCuspPeterssonTrace
import QEC.Coding.ExpanderCodes.LPSThetaCuspidalRemainder

/-!
# LPSThetaRankinDensity

The genuine LPS theta-minus-complete-Eisenstein-correction remainder supplies
the invariant finite-coset square density and its convergent hyperbolic integral.
This supplies the actual integrand for subsequent Rankin analysis; the stronger
pointwise coefficient growth and the PK22 main theorem remain to be proved.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate

noncomputable section
/-- The actual invariant finite-coset square density of the LPS theta remainder. -/
def lpsThetaRankinDensity (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) (τ : ℍ) : ℝ :=
  let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
  lpsCuspPeterssonDensity ((4*q)^2) (lpsThetaCuspidalRemainder q hq4) τ

/-- The actual LPS theta square density is continuous. -/
lemma lpsThetaRankinDensity_continuous (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    Continuous (lpsThetaRankinDensity q hq4) := by
  let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
  exact lpsCuspPeterssonDensity_continuous ((4*q)^2) (lpsThetaCuspidalRemainder q hq4)

/-- The actual LPS theta square density is nonnegative. -/
lemma lpsThetaRankinDensity_nonneg (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) (τ : ℍ) :
    0≤lpsThetaRankinDensity q hq4 τ := by
  let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
  exact lpsCuspPeterssonDensity_nonneg ((4*q)^2) (lpsThetaCuspidalRemainder q hq4) _

/-- The actual LPS theta square density is invariant under the whole modular group. -/
lemma lpsThetaRankinDensity_invariant (q : ℕ) [Fact q.Prime] (hq4 : q%4=1)
    (h : SL(2,ℤ)) (τ : ℍ) :
    lpsThetaRankinDensity q hq4 (h • τ)=lpsThetaRankinDensity q hq4 τ := by
  let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
  exact lpsCuspPeterssonDensity_invariant ((4*q)^2) (lpsThetaCuspidalRemainder q hq4) h τ

/-- The true theta-minus-complete-correction function contributes to the actual square density. -/
lemma lpsThetaRankinDensity_remainder_le (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) (τ : ℍ) :
    ‖lpsStandardTheta q τ-lpsThetaEisensteinCorrection q
      (by intro h;subst q;norm_num at hq4) τ‖^2*τ.im^2≤lpsThetaRankinDensity q hq4 τ := by
  let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
  exact lpsCuspPeterssonDensity_individual_le ((4*q)^2) (lpsThetaCuspidalRemainder q hq4) _

/-- The actual LPS theta square density decays exponentially at infinity. -/
lemma lpsThetaRankinDensity_exp_decay (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    ∃a>0,lpsThetaRankinDensity q hq4=O[atImInfty] (fun τ => Real.exp (-a*τ.im)) := by
  let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
  exact lpsCuspPeterssonDensity_exp_decay ((4*q)^2) (lpsThetaCuspidalRemainder q hq4)

/-- The actual LPS theta square density has a convergent hyperbolic integral. -/
lemma lpsThetaRankinDensity_integrable (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    IntegrableOn (lpsThetaRankinDensity q hq4) ModularGroup.fd := by
  let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
  exact lpsCuspPeterssonDensity_integrable ((4*q)^2) (lpsThetaCuspidalRemainder q hq4)

/-- The actual LPS theta square density is integrable against every real height power. -/
lemma lpsThetaRankinDensity_rpow_integrable (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) (s : ℝ) :
    IntegrableOn (fun τ : ℍ => lpsThetaRankinDensity q hq4 τ*τ.im^s) ModularGroup.fd := by
  let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
  exact lpsCuspPeterssonDensity_rpow_integrable ((4*q)^2) (lpsThetaCuspidalRemainder q hq4) _

/-- The actual LPS theta square density is integrable against every complex height power. -/
lemma lpsThetaRankinDensity_cpow_integrable (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) (s : ℂ) :
    IntegrableOn (fun τ : ℍ => (lpsThetaRankinDensity q hq4 τ:ℂ)*(τ.im:ℂ)^s) ModularGroup.fd := by
  let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
  exact lpsCuspPeterssonDensity_cpow_integrable ((4*q)^2) (lpsThetaCuspidalRemainder q hq4) _

/-- The genuine finite hyperbolic integral of the actual LPS theta square density. -/
def lpsThetaRankinMass (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) : ℝ :=
  ∫τ in ModularGroup.fd,lpsThetaRankinDensity q hq4 τ

/-- The actual convergent LPS theta square integral is nonnegative. -/
lemma lpsThetaRankinMass_nonneg (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    0≤lpsThetaRankinMass q hq4 :=
  integral_nonneg (lpsThetaRankinDensity_nonneg q hq4)

end
end QEC.Coding.TannerLiftedProduct
