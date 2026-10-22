import QEC.Coding.AlgebraicGeometry.Places.ArtinSchreierOrder
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Tactic.Ring

/-!
# Restriction of normalized orders along a specified prime chain

Orders are computed directly from prime multiplicities of numerator and
denominator ideals. Thus the lower and upper places come from the supplied
global primes, with no need to select a place in a local polynomial model.
-/

namespace QEC.Coding.AlgebraicGeometry

noncomputable section

variable {k : Type*} [Field k] [Finite k]

/-- The normalized place of a specified height-one prime in its given
fraction field. -/
noncomputable def heightOnePlace
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra k K] [Algebra R K] [IsFractionRing R K]
    (H : IsDedekindDomain.HeightOneSpectrum R) : GlobalPlace k K where
  valuation := H.valuation K
  normalized := H.valuation_surjective K

/-- The prime's normalized place has precisely its canonical localization
as valuation ring. -/
theorem heightOnePlace_valuationRing
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra k K] [Algebra R K] [IsFractionRing R K]
    (H : IsDedekindDomain.HeightOneSpectrum R) :
    H.valuationSubringAtPrime K = (heightOnePlace (k := k) (K := K) H).valuationRing :=
  H.valuationSubringAtPrime_eq_valuationSubring

theorem heightOnePlace_order_integral
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra k K] [Algebra R K] [IsFractionRing R K]
    (H : IsDedekindDomain.HeightOneSpectrum R) {r : R} (hr : r ≠ 0) :
    (heightOnePlace (k := k) (K := K) H).order (algebraMap R K r) =
      (multiplicity H.asIdeal (Ideal.span {r}) : ℤ) := by
  unfold heightOnePlace GlobalPlace.order
  rw [H.valuation_of_algebraMap, H.intValuation_eq_exp_neg_multiplicity hr,
    WithZero.log_exp]
  ring

private theorem heightOne_multiplicity_map
    {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra R S] [FaithfulSMul R S]
    (H : IsDedekindDomain.HeightOneSpectrum R)
    (J : IsDedekindDomain.HeightOneSpectrum S) [J.asIdeal.LiesOver H.asIdeal]
    (I : Ideal R) (hI : I ≠ ⊥) :
    multiplicity J.asIdeal (Ideal.map (algebraMap R S) I) =
      H.asIdeal.ramificationIdx' J.asIdeal * multiplicity H.asIdeal I := by
  have hH : Prime H.asIdeal := Ideal.prime_of_isPrime H.ne_bot H.isPrime
  have hJ : Prime J.asIdeal := Ideal.prime_of_isPrime J.ne_bot J.isPrime
  have hmap : Ideal.map (algebraMap R S) I ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hI
  have hIfin : FiniteMultiplicity H.asIdeal I := FiniteMultiplicity.of_prime_left hH hI
  have hJfin : FiniteMultiplicity J.asIdeal (Ideal.map (algebraMap R S) I) :=
    FiniteMultiplicity.of_prime_left hJ hmap
  have h := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul
    hI hH.irreducible hJ.irreducible J.ne_bot
  rw [hIfin.emultiplicity_eq_multiplicity, hJfin.emultiplicity_eq_multiplicity] at h
  exact_mod_cast h

private theorem place_order_div
    {K : Type*} [Field K] [Algebra k K] (P : GlobalPlace k K)
    {r s : K} (hr : r ≠ 0) (hs : s ≠ 0) :
    P.order (r / s) = P.order r - P.order s := by
  rw [div_eq_mul_inv, P.order_mul hr (inv_ne_zero hs), P.order_inv, sub_eq_add_neg]

/-- At a fixed chain of global primes, restriction scales normalized orders
by the actual ramification index. No order compatibility is assumed. -/
theorem heightOnePlace_order_algebraMap
    {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra k K] [Algebra k L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra R S] [FaithfulSMul R S] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    (H : IsDedekindDomain.HeightOneSpectrum R)
    (J : IsDedekindDomain.HeightOneSpectrum S) [J.asIdeal.LiesOver H.asIdeal]
    (x : K) (hx : x ≠ 0) :
    (heightOnePlace (k := k) (K := L) J).order (algebraMap K L x) =
      (H.asIdeal.ramificationIdx' J.asIdeal : ℤ) *
        (heightOnePlace (k := k) (K := K) H).order x := by
  let P := heightOnePlace (k := k) (K := K) H
  let Q := heightOnePlace (k := k) (K := L) J
  have hi (r : R) (hr : r ≠ 0) :
      Q.order (algebraMap K L (algebraMap R K r)) =
        (H.asIdeal.ramificationIdx' J.asIdeal : ℤ) * P.order (algebraMap R K r) := by
    have hmapr : algebraMap R S r ≠ 0 := by
      simpa only [map_zero] using (FaithfulSMul.algebraMap_injective R S).ne hr
    have hspan : Ideal.span ({r} : Set R) ≠ ⊥ := by
      simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hr
    have hm := heightOne_multiplicity_map H J (Ideal.span {r}) hspan
    rw [Ideal.map_span, Set.image_singleton] at hm
    rw [← IsScalarTower.algebraMap_apply R K L,
      IsScalarTower.algebraMap_apply R S L]
    change (heightOnePlace (k := k) (K := L) J).order
        (algebraMap S L (algebraMap R S r)) =
      (H.asIdeal.ramificationIdx' J.asIdeal : ℤ) *
        (heightOnePlace (k := k) (K := K) H).order (algebraMap R K r)
    rw [heightOnePlace_order_integral J hmapr, heightOnePlace_order_integral H hr, hm]
    exact Nat.cast_mul _ _
  obtain ⟨r, s, hs, hfrac⟩ := IsFractionRing.div_surjective R x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    intro h
    apply hx
    rw [← hfrac, h, map_zero, zero_div]
  have hrK : algebraMap R K r ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hr0
  have hsK : algebraMap R K s ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hs0
  have hrL : algebraMap K L (algebraMap R K r) ≠ 0 := by
    simpa only [map_zero] using (algebraMap K L).injective.ne hrK
  have hsL : algebraMap K L (algebraMap R K s) ≠ 0 := by
    simpa only [map_zero] using (algebraMap K L).injective.ne hsK
  change Q.order (algebraMap K L x) = (H.asIdeal.ramificationIdx' J.asIdeal : ℤ) * P.order x
  rw [← hfrac, map_div₀, place_order_div Q hrL hsL, place_order_div P hrK hsK,
    hi r hr0, hi s hs0]
  ring

/-- A normalized quadratic parameter propagates its order alternative along
a fixed chain of global primes. All order compatibility and ramification
bounds are derived from the rings and the field degree. -/
theorem heightOnePlace_artinSchreier_order_dichotomy_of_finrank_le_two
    {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra k K] [Algebra k L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra R S] [FaithfulSMul R S] [Module.Finite R S]
    [Algebra K L] [Algebra R L] [FiniteDimensional K L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    (H : IsDedekindDomain.HeightOneSpectrum R)
    (J : IsDedekindDomain.HeightOneSpectrum S) [J.asIdeal.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L ≤ 2)
    (ha : (heightOnePlace (k := k) (K := K) H).order a = -1 ∨
      0 ≤ (heightOnePlace (k := k) (K := K) H).order a) :
    (heightOnePlace (k := k) (K := L) J).order y = -1 ∨
      0 ≤ (heightOnePlace (k := k) (K := L) J).order y := by
  letI : Module.IsTorsionFree R S := Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  letI : NoZeroSMulDivisors R S := ⟨fun {_ _} h => smul_eq_zero.mp h⟩
  letI : H.asIdeal.IsMaximal := H.isPrime.isMaximal H.ne_bot
  have he0 : 0 < H.asIdeal.ramificationIdx' J.asIdeal :=
    Nat.pos_iff_ne_zero.mpr
      (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver J.asIdeal H.ne_bot)
  have he2 : H.asIdeal.ramificationIdx' J.asIdeal ≤ 2 :=
    (Ideal.ramificationIdx_le_finrank S K L J.asIdeal).trans hdegree
  apply (heightOnePlace (k := k) (K := K) H).artinSchreier_root_order_dichotomy
    (heightOnePlace (k := k) (K := L) J) a y
    (H.asIdeal.ramificationIdx' J.asIdeal) he0 he2 hy
  · by_cases ha0 : a = 0
    · simp [ha0, GlobalPlace.order]
    · exact heightOnePlace_order_algebraMap H J a ha0
  · exact ha

/-- The degree-two specialization of normalized root-order propagation. -/
theorem heightOnePlace_artinSchreier_order_dichotomy
    {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra k K] [Algebra k L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra R S] [FaithfulSMul R S] [Module.Finite R S]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    (H : IsDedekindDomain.HeightOneSpectrum R)
    (J : IsDedekindDomain.HeightOneSpectrum S) [J.asIdeal.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2)
    (ha : (heightOnePlace (k := k) (K := K) H).order a = -1 ∨
      0 ≤ (heightOnePlace (k := k) (K := K) H).order a) :
    (heightOnePlace (k := k) (K := L) J).order y = -1 ∨
      0 ≤ (heightOnePlace (k := k) (K := L) J).order y := by
  letI : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (by rw [hdegree]; norm_num)
  exact heightOnePlace_artinSchreier_order_dichotomy_of_finrank_le_two
    H J a y hy hdegree.le ha

end

end QEC.Coding.AlgebraicGeometry
