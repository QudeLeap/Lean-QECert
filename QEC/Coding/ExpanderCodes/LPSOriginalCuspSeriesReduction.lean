import QEC.Coding.ExpanderCodes.LPSOriginalIntegerQExpansion
import QEC.Coding.ExpanderCodes.LPSOriginalCyclotomicCoefficients
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Original cusp-series reduction and faithful pole evaluation

Only the formal cusp parameter is inverted. Integer coefficient Frobenius,
cyclotomic reduction and the constant-one original j numerator give the formal
prime-product factorization. Clearing the pole proves polynomial evaluation
injective; reduction never inverts the characteristic prime.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

lemma lpsOriginalIntegerSeriesFrobenius
    (R : Type*) [CommRing R] (p : ℕ) [ExpChar R p] (hp : p≠0)
    (F : PowerSeries ℤ) :
    (PowerSeries.map (Int.castRingHom R) F)^p=
      PowerSeries.expand p hp (PowerSeries.map (Int.castRingHom R) F) := by
  have hc : (frobenius R p).comp (Int.castRingHom R)=Int.castRingHom R := by
    ext z
    simp
  have hf : PowerSeries.map (frobenius R p)
      (PowerSeries.map (Int.castRingHom R) F)=
      PowerSeries.map (Int.castRingHom R) F := by
    rw [← RingHom.comp_apply,← PowerSeries.map_comp,hc]
  have h := MvPowerSeries.map_frobenius_expand (R:=R) (σ:=Unit) p hp
    (f:=PowerSeries.map (Int.castRingHom R) F)
  change PowerSeries.map (frobenius R p)
    (PowerSeries.expand p hp (PowerSeries.map (Int.castRingHom R) F))=
      (PowerSeries.map (Int.castRingHom R) F)^p at h
  rw [PowerSeries.map_expand,hf] at h
  exact h.symm

lemma lpsOriginalJZSeries_constant : PowerSeries.constantCoeff lpsOriginalJZSeries=1 := by
  have h := congrArg PowerSeries.constantCoeff lpsOriginalJZSeries_mapC
  have hc : PowerSeries.constantCoeff (lpsOriginalTaylorSeries lpsOriginalJQCoefficient)=1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,lpsOriginalTaylorSeries_coeff]
    simp [lpsOriginalJQCoefficient_zero]
  simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map] at h
  simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply,hc] at h
  change ((PowerSeries.constantCoeff lpsOriginalJZSeries : ℤ) : ℂ)=1 at h
  exact_mod_cast h

lemma lpsOriginalJZSeries_mod_constant (p : ℕ) :
    PowerSeries.constantCoeff
      (PowerSeries.map (Int.castRingHom (ZMod p)) lpsOriginalJZSeries)=1 := by
  simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,PowerSeries.coeff_map]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,lpsOriginalJZSeries_constant,map_one]

abbrev lpsOriginalCuspSeriesRing (R : Type*) [CommRing R] : Type _ :=
  Localization.Away (PowerSeries.X : PowerSeries R)

def lpsOriginalCuspCoefficientMap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : lpsOriginalCuspSeriesRing R →+* lpsOriginalCuspSeriesRing S :=
  IsLocalization.Away.lift (PowerSeries.X : PowerSeries R)
    (g:=(algebraMap (PowerSeries S) (lpsOriginalCuspSeriesRing S)).comp (PowerSeries.map f))
    (by
      change IsUnit (algebraMap (PowerSeries S) (lpsOriginalCuspSeriesRing S)
        (PowerSeries.map f PowerSeries.X))
      rw [PowerSeries.map_X]
      exact IsLocalization.Away.algebraMap_isUnit PowerSeries.X)

lemma lpsOriginalCuspCoefficientMap_series {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F : PowerSeries R) :
    lpsOriginalCuspCoefficientMap f
      (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) F)=
      algebraMap (PowerSeries S) (lpsOriginalCuspSeriesRing S) (PowerSeries.map f F) :=
  IsLocalization.Away.lift_eq _ _ _

lemma lpsOriginalCuspCoefficientMap_invParameter {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) :
    lpsOriginalCuspCoefficientMap f
      (IsLocalization.Away.invSelf (S:=lpsOriginalCuspSeriesRing R)
        (PowerSeries.X : PowerSeries R))=
      IsLocalization.Away.invSelf (S:=lpsOriginalCuspSeriesRing S)
        (PowerSeries.X : PowerSeries S) := by
  have h:=congrArg (lpsOriginalCuspCoefficientMap f)
    (IsLocalization.Away.mul_invSelf (S:=lpsOriginalCuspSeriesRing R)
      (PowerSeries.X : PowerSeries R))
  rw [map_mul,map_one,lpsOriginalCuspCoefficientMap_series,PowerSeries.map_X] at h
  exact (IsLocalization.Away.algebraMap_isUnit (S:=lpsOriginalCuspSeriesRing S)
    (PowerSeries.X : PowerSeries S)).mul_left_cancel
      (h.trans (IsLocalization.Away.mul_invSelf (S:=lpsOriginalCuspSeriesRing S)
        (PowerSeries.X : PowerSeries S)).symm)

def lpsOriginalCyclotomicCuspReduction (p : ℕ) [Fact p.Prime] :
    lpsOriginalCuspSeriesRing (lpsOriginalCyclotomicCoefficientRing p) →+*
      lpsOriginalCuspSeriesRing (ZMod p) :=
  lpsOriginalCuspCoefficientMap (lpsOriginalCyclotomicReduction p)

lemma lpsOriginalCyclotomicSeries_rescaleReduction (p : ℕ) [Fact p.Prime]
    (m : ℕ) :
    PowerSeries.map (lpsOriginalCyclotomicReduction p)
      (PowerSeries.rescale ((AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^m)
        (PowerSeries.map (algebraMap ℤ (lpsOriginalCyclotomicCoefficientRing p))
          lpsOriginalJZSeries))=
      PowerSeries.map (Int.castRingHom (ZMod p)) lpsOriginalJZSeries := by
  rw [←PowerSeries.rescale_map,lpsOriginalCyclotomicReduction_root_pow,
    PowerSeries.rescale_one]
  ext n
  simp [PowerSeries.coeff_map]

def lpsOriginalCuspJNumerator (R : Type*) [CommRing R] : PowerSeries R :=
  PowerSeries.map (Int.castRingHom R) lpsOriginalJZSeries

def lpsOriginalCuspJWidth (R : Type*) [CommRing R] (m : ℕ) (hm : m≠0) :
    lpsOriginalCuspSeriesRing R :=
  (IsLocalization.Away.invSelf (S:=lpsOriginalCuspSeriesRing R)
    (PowerSeries.X : PowerSeries R))^m *
    algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)
      (PowerSeries.expand m hm (lpsOriginalCuspJNumerator R))

lemma lpsOriginalCuspCoefficientMap_integerNumerator {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) :
    PowerSeries.map f (lpsOriginalCuspJNumerator R)=lpsOriginalCuspJNumerator S := by
  ext n
  simp [lpsOriginalCuspJNumerator,PowerSeries.coeff_map]

lemma lpsOriginalCuspCoefficientMap_jWidth {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) (m : ℕ) (hm : m≠0) :
    lpsOriginalCuspCoefficientMap f (lpsOriginalCuspJWidth R m hm)=
      lpsOriginalCuspJWidth S m hm := by
  rw [lpsOriginalCuspJWidth,map_mul,map_pow,
    lpsOriginalCuspCoefficientMap_invParameter,lpsOriginalCuspCoefficientMap_series,
    PowerSeries.map_expand,lpsOriginalCuspCoefficientMap_integerNumerator]
  rfl

def lpsOriginalCyclotomicFiniteCuspBranch (p : ℕ) [Fact p.Prime] (m : ℕ) :
    lpsOriginalCuspSeriesRing (lpsOriginalCyclotomicCoefficientRing p) :=
  IsLocalization.Away.invSelf
    (S:=lpsOriginalCuspSeriesRing (lpsOriginalCyclotomicCoefficientRing p))
    (PowerSeries.X : PowerSeries (lpsOriginalCyclotomicCoefficientRing p)) *
    algebraMap (PowerSeries (lpsOriginalCyclotomicCoefficientRing p))
      (lpsOriginalCuspSeriesRing (lpsOriginalCyclotomicCoefficientRing p))
      (PowerSeries.C ((AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^((p-1)*m)) *
        PowerSeries.rescale ((AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^m)
          (lpsOriginalCuspJNumerator (lpsOriginalCyclotomicCoefficientRing p)))

lemma lpsOriginalCyclotomicFiniteCuspBranch_reduction (p : ℕ) [Fact p.Prime] (m : ℕ) :
    lpsOriginalCyclotomicCuspReduction p (lpsOriginalCyclotomicFiniteCuspBranch p m)=
      lpsOriginalCuspJWidth (ZMod p) 1 (by decide) := by
  change lpsOriginalCuspCoefficientMap (lpsOriginalCyclotomicReduction p) _=_
  rw [lpsOriginalCyclotomicFiniteCuspBranch,map_mul,
    lpsOriginalCuspCoefficientMap_invParameter,lpsOriginalCuspCoefficientMap_series,
    map_mul,PowerSeries.map_C,lpsOriginalCyclotomicReduction_root_pow]
  have hr := lpsOriginalCyclotomicSeries_rescaleReduction p m
  change PowerSeries.map (lpsOriginalCyclotomicReduction p)
    (PowerSeries.rescale ((AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^m)
      (lpsOriginalCuspJNumerator (lpsOriginalCyclotomicCoefficientRing p)))=
      lpsOriginalCuspJNumerator (ZMod p) at hr
  rw [hr]
  simp [lpsOriginalCuspJWidth,PowerSeries.expand_one]

lemma lpsOriginalCuspJWidth_frobenius (R : Type*) [CommRing R]
    (p : ℕ) [ExpChar R p] (hp : p≠0) (m : ℕ) (hm : m≠0) :
    (lpsOriginalCuspJWidth R m hm)^p=
      lpsOriginalCuspJWidth R (m*p) (Nat.mul_ne_zero hm hp) := by
  have hf : (lpsOriginalCuspJNumerator R)^p=
      PowerSeries.expand p hp (lpsOriginalCuspJNumerator R) :=
    lpsOriginalIntegerSeriesFrobenius R p hp lpsOriginalJZSeries
  rw [lpsOriginalCuspJWidth,mul_pow,←map_pow,←map_pow,hf,
    ←PowerSeries.expand_mul]
  rw [lpsOriginalCuspJWidth,←pow_mul]

lemma lpsOriginalCuspSeriesAlgebraMap_injective (R : Type*) [CommRing R] [IsDomain R] :
    Function.Injective (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)) := by
  apply IsLocalization.injective (M:=Submonoid.powers (PowerSeries.X : PowerSeries R))
  intro x hx
  obtain ⟨n,rfl⟩:=hx
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n PowerSeries.X_ne_zero)

lemma lpsOriginalCuspSeries_charP (p : ℕ) [Fact p.Prime] :
    CharP (lpsOriginalCuspSeriesRing (ZMod p)) p := by
  let : CharP (PowerSeries (ZMod p)) p :=
    charP_of_injective_ringHom PowerSeries.C_injective p
  exact charP_of_injective_algebraMap (lpsOriginalCuspSeriesAlgebraMap_injective (ZMod p)) p

def lpsOriginalCyclotomicFormalPrimeProduct (p : ℕ) [Fact p.Prime] :
    Polynomial (lpsOriginalCuspSeriesRing (lpsOriginalCyclotomicCoefficientRing p)) :=
  (Polynomial.X-Polynomial.C
      (lpsOriginalCuspJWidth (lpsOriginalCyclotomicCoefficientRing p) (p*p)
        (Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (Fact.out : p.Prime).ne_zero))) *
    ∏ m : Fin p,
      (Polynomial.X-Polynomial.C (lpsOriginalCyclotomicFiniteCuspBranch p m.val))

lemma lpsOriginalCyclotomicFormalPrimeProduct_reduction (p : ℕ) [Fact p.Prime] :
    (lpsOriginalCyclotomicFormalPrimeProduct p).map (lpsOriginalCyclotomicCuspReduction p)=
      (Polynomial.X-Polynomial.C
          ((lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero)^p)) *
        (Polynomial.X^p-Polynomial.C
          (lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero)) := by
  classical
  let : CharP (lpsOriginalCuspSeriesRing (ZMod p)) p := lpsOriginalCuspSeries_charP p
  have hfinite :
      (∏ m : Fin p, (Polynomial.X-Polynomial.C (lpsOriginalCyclotomicFiniteCuspBranch p m.val))).map
        (lpsOriginalCyclotomicCuspReduction p)=
      (Polynomial.X-Polynomial.C (lpsOriginalCuspJWidth (ZMod p) 1 (by decide)))^p := by
    rw [Polynomial.map_prod]
    simp only [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
      lpsOriginalCyclotomicFiniteCuspBranch_reduction]
    simp
  have hinfty : lpsOriginalCyclotomicCuspReduction p
      (lpsOriginalCuspJWidth (lpsOriginalCyclotomicCoefficientRing p) (p*p)
        (Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (Fact.out : p.Prime).ne_zero))=
      (lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero)^p := by
    change lpsOriginalCuspCoefficientMap (lpsOriginalCyclotomicReduction p) _=_
    rw [lpsOriginalCuspCoefficientMap_jWidth]
    exact (lpsOriginalCuspJWidth_frobenius (ZMod p) p (Fact.out : p.Prime).ne_zero
      p (Fact.out : p.Prime).ne_zero).symm
  have hfinitepow :
      (lpsOriginalCuspJWidth (ZMod p) 1 (by decide))^p=
      lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero := by
    simpa only [one_mul] using lpsOriginalCuspJWidth_frobenius (ZMod p) p
      (Fact.out : p.Prime).ne_zero 1 one_ne_zero
  rw [lpsOriginalCyclotomicFormalPrimeProduct,Polynomial.map_mul,hfinite,
    Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,hinfty,
    sub_pow_expChar,←Polynomial.C_pow,hfinitepow]

lemma lpsOriginalCuspCoefficientMap_injective {R S : Type*}
    [CommRing R] [CommRing S] [IsDomain S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (lpsOriginalCuspCoefficientMap f) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (PowerSeries.X : PowerSeries R)) _).mpr
  intro A B
  constructor
  · exact congrArg (lpsOriginalCuspCoefficientMap f)
  · intro h
    rw [lpsOriginalCuspCoefficientMap_series,lpsOriginalCuspCoefficientMap_series] at h
    have he:=lpsOriginalCuspSeriesAlgebraMap_injective S h
    have hab:=PowerSeries.map_injective f hf he
    exact congrArg (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)) hab

def lpsOriginalClearedPolePolynomialSeries {R : Type*} [CommRing R]
    (F : PowerSeries R) (m D : ℕ) (P : Polynomial R) : PowerSeries R :=
  ∑ i ∈ Finset.range (D+1),
    PowerSeries.C (P.coeff i) * PowerSeries.X^(m*(D-i)) * F^i

lemma lpsOriginalClearedPolePolynomialSeries_constant {R : Type*} [CommRing R]
    (F : PowerSeries R) (hF : PowerSeries.constantCoeff F=1)
    (m : ℕ) (hm : 0<m) (P : Polynomial R) :
    PowerSeries.constantCoeff (lpsOriginalClearedPolePolynomialSeries F m P.natDegree P)=
      P.leadingCoeff := by
  classical
  rw [lpsOriginalClearedPolePolynomialSeries,map_sum]
  rw [Finset.sum_eq_single P.natDegree]
  · simp [map_mul,map_pow,hF]
  · intro i hi hne
    have hiD : i<P.natDegree := by
      have hi':i<P.natDegree+1 := Finset.mem_range.mp hi
      omega
    have hpow : 0<m*(P.natDegree-i) := Nat.mul_pos hm (Nat.sub_pos_of_lt hiD)
    simp [map_mul,map_pow,zero_pow (Nat.ne_of_gt hpow)]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (Nat.lt_succ_self _)))

lemma lpsOriginalCuspParameter_cancelPowers {R : Type*} [CommRing R]
    (m D i : ℕ) (hi : i≤D) :
    (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) PowerSeries.X)^(m*D) *
      (IsLocalization.Away.invSelf (S:=lpsOriginalCuspSeriesRing R)
        (PowerSeries.X : PowerSeries R))^(m*i)=
      (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) PowerSeries.X)^(m*(D-i)) := by
  have he : m*D=m*(D-i)+m*i := by
    rw [←Nat.mul_add,Nat.sub_add_cancel hi]
  rw [he,pow_add,mul_assoc,←mul_pow,IsLocalization.Away.mul_invSelf,one_pow,mul_one]

lemma lpsOriginalClearedPolePolynomialSeries_localization {R : Type*} [CommRing R]
    (F : PowerSeries R) (m : ℕ) (P : Polynomial R) :
    algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)
      (lpsOriginalClearedPolePolynomialSeries F m P.natDegree P)=
      (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) PowerSeries.X)^(m*P.natDegree) *
        P.eval₂ ((algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)).comp PowerSeries.C)
          ((IsLocalization.Away.invSelf (S:=lpsOriginalCuspSeriesRing R)
              (PowerSeries.X : PowerSeries R))^m *
            algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) F) := by
  classical
  rw [lpsOriginalClearedPolePolynomialSeries,map_sum,Polynomial.eval₂_eq_sum_range,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hiD : i≤P.natDegree := by
    have hi':i<P.natDegree+1 := Finset.mem_range.mp hi
    omega
  simp only [map_mul,map_pow,RingHom.comp_apply]
  symm
  calc
    _ = (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) (PowerSeries.C (P.coeff i))) *
        ((algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) PowerSeries.X)^(m*P.natDegree) *
          (IsLocalization.Away.invSelf (S:=lpsOriginalCuspSeriesRing R)
            (PowerSeries.X : PowerSeries R))^(m*i)) *
        (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) F)^i := by
      rw [mul_pow,←pow_mul]
      ring
    _ = _ := by rw [lpsOriginalCuspParameter_cancelPowers m P.natDegree i hiD]

lemma lpsOriginalPoleSeriesPolynomial_eval_eq_zero_iff {R : Type*}
    [CommRing R] [IsDomain R] (F : PowerSeries R)
    (hF : PowerSeries.constantCoeff F=1) (m : ℕ) (hm : 0<m) (P : Polynomial R) :
    P.eval₂ ((algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)).comp PowerSeries.C)
      ((IsLocalization.Away.invSelf (S:=lpsOriginalCuspSeriesRing R)
        (PowerSeries.X : PowerSeries R))^m *
          algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) F)=0 ↔ P=0 := by
  constructor
  · intro h
    have hc:=lpsOriginalClearedPolePolynomialSeries_localization F m P
    rw [h,mul_zero] at hc
    have hz : lpsOriginalClearedPolePolynomialSeries F m P.natDegree P=0 :=
      (lpsOriginalCuspSeriesAlgebraMap_injective R)
        (hc.trans ((algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)).map_zero).symm)
    have hcoeff:=congrArg PowerSeries.constantCoeff hz
    rw [lpsOriginalClearedPolePolynomialSeries_constant F hF m hm P,map_zero] at hcoeff
    exact Polynomial.leadingCoeff_eq_zero.mp hcoeff
  · rintro rfl
    simp

end
end QEC.Coding.TannerLiftedProduct
