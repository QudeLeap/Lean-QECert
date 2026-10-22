import QEC.Coding.AlgebraicGeometry.Towers.Galois
import QEC.Coding.AlgebraicGeometry.Towers.SplitIntegralClosure

import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Splitting of rational places in one Garcia--Stichtenoth step

The sixteen concrete constant translations act on the upper primes above a
rational base place.  The residual-root calculation makes this orbit free,
so these translations enumerate every upper prime and force ramification and
inertia degrees one.  Rational upper places and tower-level counts are formed
later; no divisor, genus, or asymptotic statement is packaged here.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {K : Type*} [Field K] [Algebra F256 K]

private theorem exists_splitBaseUpperIdeal
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    ∃ R : Ideal (SplitIntegralClosure Q P x hx),
      R.IsMaximal ∧
        R.LiesOver (IsLocalRing.maximalIdeal Q.place.valuationRing) := by
  letI : IsDiscreteValuationRing Q.place.valuationRing :=
    Q.place.valuationRing_isDiscreteValuationRing
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := SplitIntegralClosure Q P x hx)
    (IsLocalRing.maximalIdeal Q.place.valuationRing)

/-- A fixed upper maximal ideal above the supplied rational base place. -/
noncomputable def splitBaseUpperIdeal
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    Ideal (SplitIntegralClosure Q P x hx) :=
  Classical.choose (exists_splitBaseUpperIdeal Q P x hx)

theorem splitBaseUpperIdeal_isMaximal
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    (splitBaseUpperIdeal Q P x hx).IsMaximal :=
  (Classical.choose_spec (exists_splitBaseUpperIdeal Q P x hx)).1

theorem splitBaseUpperIdeal_liesOver
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    (splitBaseUpperIdeal Q P x hx).LiesOver
      (IsLocalRing.maximalIdeal Q.place.valuationRing) :=
  (Classical.choose_spec (exists_splitBaseUpperIdeal Q P x hx)).2

private noncomputable def splitBaseUpperPrime
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).primesOver
      (SplitIntegralClosure Q P x hx) := by
  letI : (splitBaseUpperIdeal Q P x hx).IsPrime :=
    (splitBaseUpperIdeal_isMaximal Q P x hx).isPrime
  letI : (splitBaseUpperIdeal Q P x hx).LiesOver
      (IsLocalRing.maximalIdeal Q.place.valuationRing) :=
    splitBaseUpperIdeal_liesOver Q P x hx
  exact Ideal.primesOver.mk _ (splitBaseUpperIdeal Q P x hx)

/-- The upper prime obtained by applying one concrete constant translation to
the fixed upper prime. -/
noncomputable def splitUpperPrime
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).primesOver
      (SplitIntegralClosure Q P x hx) :=
  (stepTranslation P x hx c) • splitBaseUpperPrime Q P x hx

private theorem galRestrict_stepTranslation_apply_auxiliaryCoordinate
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier) :
    galRestrict Q.place.valuationRing K (StepField P x hx)
        (SplitIntegralClosure Q P x hx) (stepTranslation P x hx c)
        (splitIntegralAuxiliaryCoordinate Q P x hx hregular) =
      splitIntegralAuxiliaryCoordinate Q P x hx hregular +
        algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
          (GlobalPlace.constantsToValuationRing Q.place (c : F256)) := by
  apply IsIntegralClosure.algebraMap_injective
    (SplitIntegralClosure Q P x hx) Q.place.valuationRing
      (StepField P x hx)
  rw [algebraMap_galRestrict_apply]
  change stepTranslation P x hx c (stepAuxiliaryCoordinate P x hx) =
    stepAuxiliaryCoordinate P x hx +
      algebraMap F256 (StepField P x hx) (c : F256)
  exact stepTranslation_apply_auxiliaryCoordinate P x hx c

private theorem translated_auxiliary_residue_mem_splitUpperPrime
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (b : F256)
    (hb : splitIntegralAuxiliaryCoordinate Q P x hx hregular -
        algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
          (GlobalPlace.constantsToValuationRing Q.place b) ∈
        splitBaseUpperIdeal Q P x hx)
    (c : LinearMap.ker f256ArtinSchreier) :
    splitIntegralAuxiliaryCoordinate Q P x hx hregular +
          algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
            (GlobalPlace.constantsToValuationRing Q.place (c : F256)) -
        algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
          (GlobalPlace.constantsToValuationRing Q.place b) ∈
      (splitUpperPrime Q P x hx c).1 := by
  let σ := stepTranslation P x hx c
  let φ := galRestrict Q.place.valuationRing K (StepField P x hx)
    (SplitIntegralClosure Q P x hx) σ
  have hmap := Ideal.mem_map_of_mem φ hb
  change _ ∈ Ideal.map φ (splitBaseUpperIdeal Q P x hx)
  rw [← galRestrict_stepTranslation_apply_auxiliaryCoordinate
    Q P x hx hregular c]
  rw [← φ.commutes]
  rw [← map_sub]
  exact hmap

/-- If the base coordinate reduces to zero, one of the concrete split upper
primes contains the actual auxiliary coordinate.  This selects the unique
zero branch used by the common-zero path; it does not store a ramification or
divisor conclusion. -/
theorem exists_splitUpperPrime_auxiliary_mem_of_evaluate_eq_zero
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hzero : Q.evaluateRegular x hregular = 0) :
    ∃ c : LinearMap.ker f256ArtinSchreier,
      splitIntegralAuxiliaryCoordinate Q P x hx hregular ∈
        (splitUpperPrime Q P x hx c).1 := by
  letI : (splitBaseUpperIdeal Q P x hx).IsMaximal :=
    splitBaseUpperIdeal_isMaximal Q P x hx
  letI : (splitBaseUpperIdeal Q P x hx).LiesOver
      (IsLocalRing.maximalIdeal Q.place.valuationRing) :=
    splitBaseUpperIdeal_liesOver Q P x hx
  obtain ⟨b, hb, hroot⟩ :=
    exists_splitUpperIdeal_auxiliary_residue_root
      Q P x hx hregular (splitBaseUpperIdeal Q P x hx)
  have hbKernel : f256ArtinSchreier b = 0 := by
    rw [f256ArtinSchreier_apply]
    have hbEquation := (mem_f256ArtinSchreierRoots
      (Q.evaluateRegular x hregular) b).mp hb
    rw [hzero] at hbEquation
    simpa only [zero_pow (by norm_num : (17 : ℕ) ≠ 0)] using hbEquation
  let c : LinearMap.ker f256ArtinSchreier := ⟨b, hbKernel⟩
  have htranslated := translated_auxiliary_residue_mem_splitUpperPrime
    Q P x hx hregular b hroot c
  refine ⟨c, ?_⟩
  simpa only [c, Subtype.coe_mk, add_sub_cancel_right] using htranslated

/-- Distinct constant translations give distinct upper primes above every
rational place where the preceding coordinate is regular. -/
theorem splitUpperPrime_injective
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Function.Injective (splitUpperPrime Q P x hx) := by
  intro c d hcd
  let R := splitBaseUpperIdeal Q P x hx
  letI : R.IsMaximal := splitBaseUpperIdeal_isMaximal Q P x hx
  letI : R.LiesOver (IsLocalRing.maximalIdeal Q.place.valuationRing) :=
    splitBaseUpperIdeal_liesOver Q P x hx
  obtain ⟨b, hb, hroot⟩ :=
    exists_splitUpperIdeal_auxiliary_residue_root
      Q P x hx hregular R
  have hc := translated_auxiliary_residue_mem_splitUpperPrime
    Q P x hx hregular b hroot c
  have hd := translated_auxiliary_residue_mem_splitUpperPrime
    Q P x hx hregular b hroot d
  rw [hcd] at hc
  let I : Ideal (SplitIntegralClosure Q P x hx) :=
    (splitUpperPrime Q P x hx d).1
  have hconstants :
      algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
            (GlobalPlace.constantsToValuationRing Q.place (c : F256)) -
          algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
            (GlobalPlace.constantsToValuationRing Q.place (d : F256)) ∈ I := by
    have hidentity :
        algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
              (GlobalPlace.constantsToValuationRing Q.place (c : F256)) -
            algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
              (GlobalPlace.constantsToValuationRing Q.place (d : F256)) =
          (splitIntegralAuxiliaryCoordinate Q P x hx hregular +
                algebraMap Q.place.valuationRing
                  (SplitIntegralClosure Q P x hx)
                  (GlobalPlace.constantsToValuationRing Q.place (c : F256)) -
              algebraMap Q.place.valuationRing
                (SplitIntegralClosure Q P x hx)
                (GlobalPlace.constantsToValuationRing Q.place b)) -
            (splitIntegralAuxiliaryCoordinate Q P x hx hregular +
                algebraMap Q.place.valuationRing
                  (SplitIntegralClosure Q P x hx)
                  (GlobalPlace.constantsToValuationRing Q.place (d : F256)) -
              algebraMap Q.place.valuationRing
                (SplitIntegralClosure Q P x hx)
                (GlobalPlace.constantsToValuationRing Q.place b)) := by
      ring
    rw [hidentity]
    exact I.sub_mem hc hd
  have hbase :
      GlobalPlace.constantsToValuationRing Q.place (c : F256) -
          GlobalPlace.constantsToValuationRing Q.place (d : F256) ∈
        IsLocalRing.maximalIdeal Q.place.valuationRing := by
    rw [Ideal.over_def I (IsLocalRing.maximalIdeal Q.place.valuationRing)]
    change algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
        (GlobalPlace.constantsToValuationRing Q.place (c : F256) -
          GlobalPlace.constantsToValuationRing Q.place (d : F256)) ∈ I
    simpa only [map_sub] using hconstants
  have heval :
      Q.evaluate
          (GlobalPlace.constantsToValuationRing Q.place (c : F256) -
            GlobalPlace.constantsToValuationRing Q.place (d : F256)) = 0 :=
    (Q.evaluate_eq_zero_iff _).2 hbase
  have hvalue : (c : F256) - (d : F256) = 0 := by
    simpa only [map_sub, Q.evaluate_constants] using heval
  apply Subtype.ext
  exact sub_eq_zero.mp hvalue

/-- Exactly sixteen upper primes lie above the supplied rational place. -/
theorem split_primesOver_ncard
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    ((IsLocalRing.maximalIdeal Q.place.valuationRing).primesOver
      (SplitIntegralClosure Q P x hx)).ncard = 16 := by
  let O := Q.place.valuationRing
  let S := SplitIntegralClosure Q P x hx
  let L := StepField P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let G := L ≃ₐ[K] L
  letI : IsDiscreteValuationRing O :=
    Q.place.valuationRing_isDiscreteValuationRing
  letI : MulSemiringAction G S :=
    IsIntegralClosure.MulSemiringAction O K L S
  letI : IsGaloisGroup G O S :=
    IsGaloisGroup.of_isFractionRing G O S K L
  have hlower : 16 ≤ (m.primesOver S).ncard := by
    calc
      16 = Nat.card (LinearMap.ker f256ArtinSchreier) := by
        rw [Nat.card_eq_fintype_card, f256ArtinSchreier_ker_card]
      _ ≤ Nat.card (m.primesOver S) :=
        Nat.card_le_card_of_injective (splitUpperPrime Q P x hx)
          (splitUpperPrime_injective Q P x hx hregular)
      _ = (m.primesOver S).ncard := Nat.card_coe_set_eq _
  have he : m.ramificationIdxIn S ≠ 0 :=
    Ideal.ramificationIdxIn_ne_zero G
  have hf : m.inertiaDegIn S ≠ 0 :=
    Ideal.inertiaDegIn_ne_zero G
  have hfundamental :
      (m.primesOver S).ncard *
          (m.ramificationIdxIn S * m.inertiaDegIn S) = 16 := by
    calc
      (m.primesOver S).ncard *
            (m.ramificationIdxIn S * m.inertiaDegIn S) = Nat.card G :=
        Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
          m S G
      _ = 16 := stepField_algEquiv_card P x hx
  apply le_antisymm
  · calc
      (m.primesOver S).ncard ≤
          (m.primesOver S).ncard *
            (m.ramificationIdxIn S * m.inertiaDegIn S) :=
        Nat.le_mul_of_pos_right _
          (Nat.mul_pos (Nat.pos_of_ne_zero he) (Nat.pos_of_ne_zero hf))
      _ = 16 := hfundamental
  · exact hlower

/-- The concrete constant translations enumerate all upper primes. -/
noncomputable def splitUpperPrimeEquiv
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    LinearMap.ker f256ArtinSchreier ≃
      (IsLocalRing.maximalIdeal Q.place.valuationRing).primesOver
        (SplitIntegralClosure Q P x hx) := by
  apply Equiv.ofBijective (splitUpperPrime Q P x hx)
  apply (Nat.bijective_iff_injective_and_card _).2
  refine ⟨splitUpperPrime_injective Q P x hx hregular, ?_⟩
  calc
    Nat.card (LinearMap.ker f256ArtinSchreier) = 16 := by
      rw [Nat.card_eq_fintype_card, f256ArtinSchreier_ker_card]
    _ = ((IsLocalRing.maximalIdeal Q.place.valuationRing).primesOver
        (SplitIntegralClosure Q P x hx)).ncard :=
      (split_primesOver_ncard Q P x hx hregular).symm
    _ = Nat.card
        ((IsLocalRing.maximalIdeal Q.place.valuationRing).primesOver
          (SplitIntegralClosure Q P x hx)) :=
      (Nat.card_coe_set_eq _).symm

private theorem split_ramificationIdxIn_mul_inertiaDegIn_eq_one
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).ramificationIdxIn
          (SplitIntegralClosure Q P x hx) *
        (IsLocalRing.maximalIdeal Q.place.valuationRing).inertiaDegIn
          (SplitIntegralClosure Q P x hx) = 1 := by
  let O := Q.place.valuationRing
  let S := SplitIntegralClosure Q P x hx
  let L := StepField P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let G := L ≃ₐ[K] L
  letI : IsDiscreteValuationRing O :=
    Q.place.valuationRing_isDiscreteValuationRing
  letI : MulSemiringAction G S :=
    IsIntegralClosure.MulSemiringAction O K L S
  letI : IsGaloisGroup G O S :=
    IsGaloisGroup.of_isFractionRing G O S K L
  have hfundamental :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      m S G
  rw [split_primesOver_ncard Q P x hx hregular,
    stepField_algEquiv_card P x hx] at hfundamental
  have hcancel :
      16 * (m.ramificationIdxIn S * m.inertiaDegIn S) = 16 * 1 := by
    simpa only [Nat.mul_one] using hfundamental
  exact Nat.mul_left_cancel (by norm_num : 0 < 16) hcancel

/-- Every upper prime in this split rational fibre has ramification index
one. -/
theorem split_ramificationIdxIn_eq_one
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).ramificationIdxIn
      (SplitIntegralClosure Q P x hx) = 1 := by
  apply Nat.eq_one_of_dvd_one
  exact ⟨(IsLocalRing.maximalIdeal Q.place.valuationRing).inertiaDegIn
      (SplitIntegralClosure Q P x hx),
    (split_ramificationIdxIn_mul_inertiaDegIn_eq_one
      Q P x hx hregular).symm⟩

/-- Every upper prime in this split rational fibre has inertia degree one. -/
theorem split_inertiaDegIn_eq_one
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).inertiaDegIn
      (SplitIntegralClosure Q P x hx) = 1 := by
  apply Nat.eq_one_of_dvd_one
  refine ⟨(IsLocalRing.maximalIdeal Q.place.valuationRing).ramificationIdxIn
      (SplitIntegralClosure Q P x hx), ?_⟩
  simpa only [Nat.mul_comm] using
    (split_ramificationIdxIn_mul_inertiaDegIn_eq_one
      Q P x hx hregular).symm

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
