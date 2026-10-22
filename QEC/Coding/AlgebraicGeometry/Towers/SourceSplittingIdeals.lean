import QEC.Coding.AlgebraicGeometry.Towers.SourceSplitIntegralClosure

import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Splitting ideals in one selected source recursion step

The sixteen proved constant translations act on upper primes above a selected
rational base place.  Residue-root classification makes this orbit free, and
the Galois fundamental identity then proves that these are all upper primes,
with ramification and inertia degree one.  Rational upper places and recursive
families are constructed later.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {K : Type*} [Field K] [Algebra F256 K]

private theorem exists_sourceSplitBaseUpperIdeal
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    ∃ R : Ideal (SourceSplitIntegralClosure Q P x hx),
      R.IsMaximal ∧
        R.LiesOver (IsLocalRing.maximalIdeal Q.place.valuationRing) := by
  letI : IsDiscreteValuationRing Q.place.valuationRing :=
    Q.place.valuationRing_isDiscreteValuationRing
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := SourceSplitIntegralClosure Q P x hx)
    (IsLocalRing.maximalIdeal Q.place.valuationRing)

/-- A fixed upper maximal ideal above the selected rational base place. -/
noncomputable def sourceSplitBaseUpperIdeal
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    Ideal (SourceSplitIntegralClosure Q P x hx) :=
  Classical.choose (exists_sourceSplitBaseUpperIdeal Q P x hx)

theorem sourceSplitBaseUpperIdeal_isMaximal
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    (sourceSplitBaseUpperIdeal Q P x hx).IsMaximal :=
  (Classical.choose_spec (exists_sourceSplitBaseUpperIdeal Q P x hx)).1

theorem sourceSplitBaseUpperIdeal_liesOver
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    (sourceSplitBaseUpperIdeal Q P x hx).LiesOver
      (IsLocalRing.maximalIdeal Q.place.valuationRing) :=
  (Classical.choose_spec (exists_sourceSplitBaseUpperIdeal Q P x hx)).2

private noncomputable def sourceSplitBaseUpperPrime
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).primesOver
      (SourceSplitIntegralClosure Q P x hx) := by
  letI : (sourceSplitBaseUpperIdeal Q P x hx).IsPrime :=
    (sourceSplitBaseUpperIdeal_isMaximal Q P x hx).isPrime
  letI : (sourceSplitBaseUpperIdeal Q P x hx).LiesOver
      (IsLocalRing.maximalIdeal Q.place.valuationRing) :=
    sourceSplitBaseUpperIdeal_liesOver Q P x hx
  exact Ideal.primesOver.mk _ (sourceSplitBaseUpperIdeal Q P x hx)

/-- The upper prime obtained by applying one source-step translation to the
fixed upper prime. -/
noncomputable def sourceSplitUpperPrime
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).primesOver
      (SourceSplitIntegralClosure Q P x hx) :=
  (sourceStepTranslation P x hx c) •
    sourceSplitBaseUpperPrime Q P x hx

private theorem galRestrict_sourceStepTranslation_apply_coordinate
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    galRestrict Q.place.valuationRing K (SourceStepField P x hx)
        (SourceSplitIntegralClosure Q P x hx)
        (sourceStepTranslation P x hx c)
        (sourceSplitIntegralCoordinate Q P x hx hregular hsplit) =
      sourceSplitIntegralCoordinate Q P x hx hregular hsplit +
        algebraMap Q.place.valuationRing
          (SourceSplitIntegralClosure Q P x hx)
          (GlobalPlace.constantsToValuationRing Q.place (c : F256)) := by
  apply IsIntegralClosure.algebraMap_injective
    (SourceSplitIntegralClosure Q P x hx) Q.place.valuationRing
      (SourceStepField P x hx)
  rw [algebraMap_galRestrict_apply]
  change sourceStepTranslation P x hx c (sourceStepCoordinate P x hx) =
    sourceStepCoordinate P x hx +
      algebraMap F256 (SourceStepField P x hx) (c : F256)
  exact sourceStepTranslation_apply_coordinate P x hx c

private theorem translated_sourceCoordinate_residue_mem_sourceSplitUpperPrime
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (b : F256)
    (hb : sourceSplitIntegralCoordinate Q P x hx hregular hsplit -
        algebraMap Q.place.valuationRing
          (SourceSplitIntegralClosure Q P x hx)
          (GlobalPlace.constantsToValuationRing Q.place b) ∈
        sourceSplitBaseUpperIdeal Q P x hx)
    (c : LinearMap.ker f256ArtinSchreier) :
    sourceSplitIntegralCoordinate Q P x hx hregular hsplit +
          algebraMap Q.place.valuationRing
            (SourceSplitIntegralClosure Q P x hx)
            (GlobalPlace.constantsToValuationRing Q.place (c : F256)) -
        algebraMap Q.place.valuationRing
          (SourceSplitIntegralClosure Q P x hx)
          (GlobalPlace.constantsToValuationRing Q.place b) ∈
      (sourceSplitUpperPrime Q P x hx c).1 := by
  let σ := sourceStepTranslation P x hx c
  let φ := galRestrict Q.place.valuationRing K (SourceStepField P x hx)
    (SourceSplitIntegralClosure Q P x hx) σ
  have hmap := Ideal.mem_map_of_mem φ hb
  change _ ∈ Ideal.map φ (sourceSplitBaseUpperIdeal Q P x hx)
  rw [← galRestrict_sourceStepTranslation_apply_coordinate
    Q P x hx hregular hsplit c]
  rw [← φ.commutes]
  rw [← map_sub]
  exact hmap

/-- Distinct source-step translations give distinct upper primes above every
selected rational base place. -/
theorem sourceSplitUpperPrime_injective
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    Function.Injective (sourceSplitUpperPrime Q P x hx) := by
  intro c d hcd
  let R := sourceSplitBaseUpperIdeal Q P x hx
  letI : R.IsMaximal := sourceSplitBaseUpperIdeal_isMaximal Q P x hx
  letI : R.LiesOver (IsLocalRing.maximalIdeal Q.place.valuationRing) :=
    sourceSplitBaseUpperIdeal_liesOver Q P x hx
  obtain ⟨b, hb, hroot⟩ :=
    exists_sourceSplitUpperIdeal_coordinate_residue_root
      Q P x hx hregular hsplit R
  have hc := translated_sourceCoordinate_residue_mem_sourceSplitUpperPrime
    Q P x hx hregular hsplit b hroot c
  have hd := translated_sourceCoordinate_residue_mem_sourceSplitUpperPrime
    Q P x hx hregular hsplit b hroot d
  rw [hcd] at hc
  let I : Ideal (SourceSplitIntegralClosure Q P x hx) :=
    (sourceSplitUpperPrime Q P x hx d).1
  have hconstants :
      algebraMap Q.place.valuationRing
            (SourceSplitIntegralClosure Q P x hx)
            (GlobalPlace.constantsToValuationRing Q.place (c : F256)) -
          algebraMap Q.place.valuationRing
            (SourceSplitIntegralClosure Q P x hx)
            (GlobalPlace.constantsToValuationRing Q.place (d : F256)) ∈ I := by
    have hidentity :
        algebraMap Q.place.valuationRing
              (SourceSplitIntegralClosure Q P x hx)
              (GlobalPlace.constantsToValuationRing Q.place (c : F256)) -
            algebraMap Q.place.valuationRing
              (SourceSplitIntegralClosure Q P x hx)
              (GlobalPlace.constantsToValuationRing Q.place (d : F256)) =
          (sourceSplitIntegralCoordinate Q P x hx hregular hsplit +
                algebraMap Q.place.valuationRing
                  (SourceSplitIntegralClosure Q P x hx)
                  (GlobalPlace.constantsToValuationRing Q.place (c : F256)) -
              algebraMap Q.place.valuationRing
                (SourceSplitIntegralClosure Q P x hx)
                (GlobalPlace.constantsToValuationRing Q.place b)) -
            (sourceSplitIntegralCoordinate Q P x hx hregular hsplit +
                algebraMap Q.place.valuationRing
                  (SourceSplitIntegralClosure Q P x hx)
                  (GlobalPlace.constantsToValuationRing Q.place (d : F256)) -
              algebraMap Q.place.valuationRing
                (SourceSplitIntegralClosure Q P x hx)
                (GlobalPlace.constantsToValuationRing Q.place b)) := by
      ring
    rw [hidentity]
    exact I.sub_mem hc hd
  have hbase :
      GlobalPlace.constantsToValuationRing Q.place (c : F256) -
          GlobalPlace.constantsToValuationRing Q.place (d : F256) ∈
        IsLocalRing.maximalIdeal Q.place.valuationRing := by
    rw [Ideal.over_def I (IsLocalRing.maximalIdeal Q.place.valuationRing)]
    change algebraMap Q.place.valuationRing
        (SourceSplitIntegralClosure Q P x hx)
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

/-- Exactly sixteen upper primes lie above a selected rational source place.
-/
theorem sourceSplit_primesOver_ncard
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    ((IsLocalRing.maximalIdeal Q.place.valuationRing).primesOver
      (SourceSplitIntegralClosure Q P x hx)).ncard = 16 := by
  let O := Q.place.valuationRing
  let S := SourceSplitIntegralClosure Q P x hx
  let L := SourceStepField P x hx
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
        Nat.card_le_card_of_injective (sourceSplitUpperPrime Q P x hx)
          (sourceSplitUpperPrime_injective Q P x hx hregular hsplit)
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
      _ = 16 := sourceStepField_algEquiv_card P x hx
  apply le_antisymm
  · calc
      (m.primesOver S).ncard ≤
          (m.primesOver S).ncard *
            (m.ramificationIdxIn S * m.inertiaDegIn S) :=
        Nat.le_mul_of_pos_right _
          (Nat.mul_pos (Nat.pos_of_ne_zero he) (Nat.pos_of_ne_zero hf))
      _ = 16 := hfundamental
  · exact hlower

/-- The constant translations enumerate all upper primes in a selected
source-step fibre. -/
noncomputable def sourceSplitUpperPrimeEquiv
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    LinearMap.ker f256ArtinSchreier ≃
      (IsLocalRing.maximalIdeal Q.place.valuationRing).primesOver
        (SourceSplitIntegralClosure Q P x hx) := by
  apply Equiv.ofBijective (sourceSplitUpperPrime Q P x hx)
  apply (Nat.bijective_iff_injective_and_card _).2
  refine ⟨sourceSplitUpperPrime_injective Q P x hx hregular hsplit, ?_⟩
  calc
    Nat.card (LinearMap.ker f256ArtinSchreier) = 16 := by
      rw [Nat.card_eq_fintype_card, f256ArtinSchreier_ker_card]
    _ = ((IsLocalRing.maximalIdeal Q.place.valuationRing).primesOver
        (SourceSplitIntegralClosure Q P x hx)).ncard :=
      (sourceSplit_primesOver_ncard Q P x hx hregular hsplit).symm
    _ = Nat.card
        ((IsLocalRing.maximalIdeal Q.place.valuationRing).primesOver
          (SourceSplitIntegralClosure Q P x hx)) :=
      (Nat.card_coe_set_eq _).symm

private theorem sourceSplit_ramificationIdxIn_mul_inertiaDegIn_eq_one
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).ramificationIdxIn
          (SourceSplitIntegralClosure Q P x hx) *
        (IsLocalRing.maximalIdeal Q.place.valuationRing).inertiaDegIn
          (SourceSplitIntegralClosure Q P x hx) = 1 := by
  let O := Q.place.valuationRing
  let S := SourceSplitIntegralClosure Q P x hx
  let L := SourceStepField P x hx
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
  rw [sourceSplit_primesOver_ncard Q P x hx hregular hsplit,
    sourceStepField_algEquiv_card P x hx] at hfundamental
  have hcancel :
      16 * (m.ramificationIdxIn S * m.inertiaDegIn S) = 16 * 1 := by
    simpa only [Nat.mul_one] using hfundamental
  exact Nat.mul_left_cancel (by norm_num : 0 < 16) hcancel

/-- Every selected upper prime has ramification index one. -/
theorem sourceSplit_ramificationIdxIn_eq_one
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).ramificationIdxIn
      (SourceSplitIntegralClosure Q P x hx) = 1 := by
  apply Nat.eq_one_of_dvd_one
  exact ⟨(IsLocalRing.maximalIdeal Q.place.valuationRing).inertiaDegIn
      (SourceSplitIntegralClosure Q P x hx),
    (sourceSplit_ramificationIdxIn_mul_inertiaDegIn_eq_one
      Q P x hx hregular hsplit).symm⟩

/-- Every selected upper prime has inertia degree one. -/
theorem sourceSplit_inertiaDegIn_eq_one
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).inertiaDegIn
      (SourceSplitIntegralClosure Q P x hx) = 1 := by
  apply Nat.eq_one_of_dvd_one
  refine ⟨(IsLocalRing.maximalIdeal Q.place.valuationRing).ramificationIdxIn
      (SourceSplitIntegralClosure Q P x hx), ?_⟩
  simpa only [Nat.mul_comm] using
    (sourceSplit_ramificationIdxIn_mul_inertiaDegIn_eq_one
      Q P x hx hregular hsplit).symm

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
