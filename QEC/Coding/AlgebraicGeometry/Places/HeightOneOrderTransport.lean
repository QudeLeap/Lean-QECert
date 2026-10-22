import QEC.Coding.AlgebraicGeometry.Places.HeightOneOrder

/-!
# Preserving normalized orders when a prime maps to a prime

Integral models in the same fraction field have identical normalized orders
at a prime and its prime image. This covers both lower-prime localization
and an equivalent integral-closure carrier inside the fixed final field.
-/

namespace QEC.Coding.AlgebraicGeometry

noncomputable section

/-- A normalized order cannot be rescaled by a different positive integer
while preserving the same values on a field. Evaluating at both actual
uniformizers determines the scaling factor and hence the order itself. -/
theorem GlobalPlace.order_eq_of_common_positive_scaling
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P Q : GlobalPlace k K) (e f : ℕ) (he : 0 < e) (hf : 0 < f)
    (h : ∀ x : K, (e : ℤ) * P.order x = (f : ℤ) * Q.order x) :
    P.order = Q.order := by
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  have hf' : (0 : ℤ) < f := by exact_mod_cast hf
  have hP := h P.uniformizer
  have hQ := h Q.uniformizer
  rw [P.order_uniformizer, mul_one] at hP
  rw [Q.order_uniformizer, mul_one] at hQ
  have hQu : 0 < Q.order P.uniformizer :=
    (mul_pos_iff_of_pos_left hf').mp (by rwa [← hP])
  have hPu : 0 < P.order Q.uniformizer :=
    (mul_pos_iff_of_pos_left he').mp (by rwa [hQ])
  have hfe : (f : ℤ) ≤ e := by
    calc
      (f : ℤ) = f * 1 := (mul_one _).symm
      _ ≤ f * Q.order P.uniformizer :=
        mul_le_mul_of_nonneg_left (by omega) hf'.le
      _ = e := hP.symm
  have hef : (e : ℤ) ≤ f := by
    calc
      (e : ℤ) = e * 1 := (mul_one _).symm
      _ ≤ e * P.order Q.uniformizer :=
        mul_le_mul_of_nonneg_left (by omega) he'.le
      _ = f := hQ
  have heq : (e : ℤ) = f := le_antisymm hef hfe
  funext x
  have hx := h x
  rw [heq] at hx
  exact mul_left_cancel₀ (ne_of_gt hf') hx

/-- Equality of the actual upper orders determines both normalized lower
orders. Their compatibility with restriction is computed from prime
multiplicities, not assumed for the lower places. -/
theorem heightOnePlace_order_eq_of_common_extension
    {k R R' S S' K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [IsDedekindDomain R] [IsDedekindDomain R']
    [IsDedekindDomain S] [IsDedekindDomain S']
    [Algebra k K] [Algebra k L] [Algebra K L]
    [Algebra R K] [IsFractionRing R K] [Algebra R' K] [IsFractionRing R' K]
    [Algebra S L] [IsFractionRing S L] [Algebra S' L] [IsFractionRing S' L]
    [Algebra R S] [FaithfulSMul R S] [Module.Finite R S]
    [Algebra R' S'] [FaithfulSMul R' S'] [Module.Finite R' S']
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
    [Algebra R' L] [IsScalarTower R' K L] [IsScalarTower R' S' L]
    (P : IsDedekindDomain.HeightOneSpectrum R)
    (P' : IsDedekindDomain.HeightOneSpectrum R')
    (Q : IsDedekindDomain.HeightOneSpectrum S)
    (Q' : IsDedekindDomain.HeightOneSpectrum S')
    [Q.asIdeal.LiesOver P.asIdeal] [Q'.asIdeal.LiesOver P'.asIdeal]
    (hupper : (heightOnePlace (k := k) (K := L) Q).order =
      (heightOnePlace (k := k) (K := L) Q').order) :
    (heightOnePlace (k := k) (K := K) P).order =
      (heightOnePlace (k := k) (K := K) P').order := by
  letI : Module.IsTorsionFree R S := Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  letI : Module.IsTorsionFree R' S' := Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  letI : NoZeroSMulDivisors R S := ⟨fun {_ _} h => smul_eq_zero.mp h⟩
  letI : NoZeroSMulDivisors R' S' := ⟨fun {_ _} h => smul_eq_zero.mp h⟩
  letI : P.asIdeal.IsMaximal := P.isPrime.isMaximal P.ne_bot
  letI : P'.asIdeal.IsMaximal := P'.isPrime.isMaximal P'.ne_bot
  have he : 0 < P.asIdeal.ramificationIdx' Q.asIdeal :=
    Nat.pos_iff_ne_zero.mpr
      (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver Q.asIdeal P.ne_bot)
  have hf : 0 < P'.asIdeal.ramificationIdx' Q'.asIdeal :=
    Nat.pos_iff_ne_zero.mpr
      (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver Q'.asIdeal P'.ne_bot)
  apply GlobalPlace.order_eq_of_common_positive_scaling _ _ _ _ he hf
  intro x
  by_cases hx : x = 0
  · simp [hx, GlobalPlace.order]
  · rw [← heightOnePlace_order_algebraMap (k := k) (K := K) (L := L) P Q x hx,
      ← heightOnePlace_order_algebraMap (k := k) (K := K) (L := L) P' Q' x hx, hupper]

/-- If a height-one prime maps to the supplied height-one prime of an
overring in the same fraction field, the normalized orders agree exactly.
The ramification index is derived to be one from the prime image. -/
theorem heightOnePlace_order_eq_of_map_eq
    {k R S L : Type*} [Field k] [Finite k]
    [CommRing R] [CommRing S] [Field L]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra k L] [Algebra R L] [Algebra S L]
    [IsFractionRing R L] [IsFractionRing S L]
    [Algebra R S] [FaithfulSMul R S] [IsScalarTower R S L]
    (H : IsDedekindDomain.HeightOneSpectrum R)
    (J : IsDedekindDomain.HeightOneSpectrum S) [J.asIdeal.LiesOver H.asIdeal]
    (hmap : Ideal.map (algebraMap R S) H.asIdeal = J.asIdeal) (x : L) :
    (heightOnePlace (k := k) (K := L) H).order x =
      (heightOnePlace (k := k) (K := L) J).order x := by
  have he : H.asIdeal.ramificationIdx' J.asIdeal = 1 := by
    have htop : Ideal.map (algebraMap R S) H.asIdeal ≠ ⊤ := by
      rw [hmap]
      exact J.isPrime.ne_top
    have hbot : Ideal.map (algebraMap R S) H.asIdeal ≠ ⊥ := by
      rw [hmap]
      exact J.ne_bot
    have h := H.asIdeal.ramificationIdx_map_self_eq_one htop hbot
    rwa [hmap] at h
  by_cases hx : x = 0
  · simp [hx, GlobalPlace.order]
  · have h := heightOnePlace_order_algebraMap (k := k) (K := L) (L := L) H J x hx
    simpa only [Algebra.algebraMap_self, RingHom.id_apply, he, Nat.cast_one, one_mul] using h.symm

end

end QEC.Coding.AlgebraicGeometry
