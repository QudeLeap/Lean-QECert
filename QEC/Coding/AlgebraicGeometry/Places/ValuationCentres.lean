import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.AlgebraicGeometry.StructureSheaf

/-!
# Valuation centres and model stalks

A dominating nontrivial valuation of a Dedekind function-field model agrees
with the actual height-one localization at its centre. Integral polynomial
models have nonzero evaluation kernels, and their scheme stalks are those
localizations. The original normalization's local-ring comparison consumes
these constructions with all hypotheses discharged.
-/

namespace QEC.Coding.AlgebraicGeometry.ValuationCentres
noncomputable section

/-- Evaluating an integral model containing a genuine polynomial coordinate
over its scalar field has a nonzero kernel: the coordinate minus its evaluated constant. -/
lemma polynomialIntegralModel_evaluation_kernel_ne_bot
    {k K : Type*} [Field k] [Field K] [Algebra (Polynomial k) K]
    (hi : Function.Injective (algebraMap (Polynomial k) K))
    (e : integralClosure (Polynomial k) K →+* k)
    (hc : ∀ c : k, e ⟨algebraMap (Polynomial k) K (Polynomial.C c),
      isIntegral_algebraMap⟩ = c) : RingHom.ker e ≠ ⊥ := by
  let z : integralClosure (Polynomial k) K :=
    ⟨algebraMap (Polynomial k) K Polynomial.X,isIntegral_algebraMap⟩
  let c : k := e z
  let a : integralClosure (Polynomial k) K :=
    ⟨algebraMap (Polynomial k) K (Polynomial.C c),isIntegral_algebraMap⟩
  have hza : z-a ≠ 0 := by
    intro h
    have hv := congrArg Subtype.val h
    change algebraMap (Polynomial k) K Polynomial.X -
      algebraMap (Polynomial k) K (Polynomial.C c) = 0 at hv
    exact Polynomial.X_ne_C c (hi (sub_eq_zero.mp hv))
  have hm : z-a ∈ RingHom.ker e := by
    change e (z-a) = 0
    rw [map_sub,hc]
    exact sub_self _
  intro hbot
  rw [hbot,Ideal.mem_bot] at hm
  exact hza hm

/-- A genuine nontrivial valuation dominating a Dedekind model has the same
valuation ring as the model's height-one localization at its actual centre. -/
lemma valuationRing_eq_actual_heightOneCentre
    {K : Type*} [Field K] (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Algebra R K] [IsFractionRing R K]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (hR : ∀ r : R, v (algebraMap R K r) ≤ 1)
    (hn : ∃ r : R, r ≠ 0 ∧ v (algebraMap R K r) < 1) :
    ∃ H : IsDedekindDomain.HeightOneSpectrum R,
      H.asIdeal = Ideal.comap ((algebraMap R K).codRestrict v.valuationSubring hR)
        (IsLocalRing.maximalIdeal v.valuationSubring) ∧
      H.valuationSubringAtPrime K = v.valuationSubring := by
  let f : R →+* v.valuationSubring := (algebraMap R K).codRestrict v.valuationSubring hR
  let I : Ideal R := Ideal.comap f (IsLocalRing.maximalIdeal v.valuationSubring)
  let : I.IsPrime := Ideal.comap_isPrime _ _
  have hIne : I ≠ ⊥ := by
    obtain ⟨r,hr,hv⟩ := hn
    intro heq
    have hrI : r ∈ I := (v.mem_maximalIdeal_iff).mpr hv
    rw [heq,Ideal.mem_bot] at hrI
    exact hr hrI
  let H : IsDedekindDomain.HeightOneSpectrum R := ⟨I,inferInstance,hIne⟩
  have hle : H.valuationSubringAtPrime K ≤ v.valuationSubring := by
    rintro z ⟨a,s,hs,rfl⟩
    have hsnot : ¬ v (algebraMap R K s) < 1 := by
      intro hv
      exact hs ((v.mem_maximalIdeal_iff).mpr hv)
    have hsone : v (algebraMap R K s) = 1 :=
      le_antisymm (hR s) (le_of_not_gt hsnot)
    change v (algebraMap R K a * (algebraMap R K s)⁻¹) ≤ 1
    rw [map_mul,map_inv₀,hsone,inv_one,mul_one]
    exact hR a
  have hnontrivial : v.IsNontrivial := by
    obtain ⟨r,hr,hv⟩ := hn
    refine ⟨algebraMap R K r,?_,ne_of_lt hv⟩
    apply v.ne_zero_iff.mpr
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hr
  have hnotop : v.valuationSubring ≠ ⊤ := by
    intro ht
    exact ((Valuation.valuationSubring_eq_top_iff (v := v)).mp ht) hnontrivial
  exact ⟨H,rfl,ValuationSubring.eq_of_le_of_ne_top _ hle hnotop⟩


def heightOneStalkValuationRingEquiv
    {K : Type*} [Field K] (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Algebra R K] [IsFractionRing R K] (H : IsDedekindDomain.HeightOneSpectrum R) :
    (_root_.AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk
      (⟨H.asIdeal,H.isPrime⟩ : PrimeSpectrum R) ≃+* H.valuationSubringAtPrime K :=
by
  let p : PrimeSpectrum R := ⟨H.asIdeal,H.isPrime⟩
  letI : IsLocalization H.asIdeal.primeCompl
      ((_root_.AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk p) :=
    _root_.AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk R p
  exact (IsLocalization.algEquiv H.asIdeal.primeCompl _ _).toRingEquiv

lemma heightOneStalkValuationRingEquiv_algebraMap
    {K : Type*} [Field K] (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Algebra R K] [IsFractionRing R K] (H : IsDedekindDomain.HeightOneSpectrum R) (a : R) :
    ((heightOneStalkValuationRingEquiv R H)
      (algebraMap R ((_root_.AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk
        (⟨H.asIdeal,H.isPrime⟩ : PrimeSpectrum R)) a)).val = algebraMap R K a := by
  let : IsLocalization H.asIdeal.primeCompl
      ((_root_.AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk
        (⟨H.asIdeal,H.isPrime⟩ : PrimeSpectrum R)) :=
    _root_.AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk R
      (⟨H.asIdeal,H.isPrime⟩ : PrimeSpectrum R)
  unfold heightOneStalkValuationRingEquiv
  change ((IsLocalization.algEquiv H.asIdeal.primeCompl
    ((_root_.AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk
      (⟨H.asIdeal,H.isPrime⟩ : PrimeSpectrum R)) (H.valuationSubringAtPrime K))
    (algebraMap R _ a)).val = algebraMap R K a
  rw [AlgEquiv.commutes]
  rfl

lemma heightOneValuationRing_isDiscreteValuationRing
    {K : Type*} [Field K] (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Algebra R K] [IsFractionRing R K] (H : IsDedekindDomain.HeightOneSpectrum R) :
    IsDiscreteValuationRing (H.valuationSubringAtPrime K) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R H.ne_bot _

end
end QEC.Coding.AlgebraicGeometry.ValuationCentres
