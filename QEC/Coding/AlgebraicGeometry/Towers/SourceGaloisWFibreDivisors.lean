import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisWResidueDegrees
import QEC.Coding.AlgebraicGeometry.Divisors.FinitePlaceDivisor

/-!
# Fibre divisors above zero and infinity in the source normal closure

This module forms the actual reduced divisors on the zero and infinity prime
fibres over `F256(w)` inside the source-recursion normal closure. Their weighted
degrees are computed from the proved residue-degree and Galois fundamental
identities. No ramification value, different, canonical differential, or genus
formula is asserted here.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

open scoped BigOperators

noncomputable section

private abbrev E (m : ℕ) := SourceGaloisClosureField m

private noncomputable local instance closurePolynomialAlgebra (m : ℕ) :
    Algebra (Polynomial F256) (E m) :=
  ((algebraMap (RatFunc F256) (E m)).comp
    (algebraMap (Polynomial F256) (RatFunc F256))).toAlgebra

private noncomputable local instance closurePolynomialRatFuncScalarTower (m : ℕ) :
    IsScalarTower (Polynomial F256) (RatFunc F256) (E m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable local instance closureRatFuncIsSeparable (m : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (E m) :=
  IsGalois.to_isSeparable

private noncomputable local instance sourceGaloisWZeroPrimeFintype (m : ℕ) :
    Fintype (SourceGaloisWZeroPrime m) :=
  Set.Finite.fintype (sourceGaloisWZeroPrime_finite m)

private noncomputable local instance sourceGaloisWInfinityPrimeFintype (m : ℕ) :
    Fintype (SourceGaloisWInfinityPrime m) :=
  Set.Finite.fintype (sourceGaloisWInfinityPrime_finite m)

private local instance sourceGaloisWZeroPrimeNonempty (m : ℕ) :
    Nonempty (SourceGaloisWZeroPrime m) :=
  sourceGaloisWZeroPrime_nonempty m

private local instance sourceGaloisWInfinityPrimeNonempty (m : ℕ) :
    Nonempty (SourceGaloisWInfinityPrime m) :=
  sourceGaloisWInfinityPrime_nonempty m

/-- The actual reduced divisor on the zero-place prime fibre over `F256(w)`. -/
noncomputable def sourceGaloisWZeroFibreDivisor (m : ℕ) :
    Divisor (GlobalPlace F256 (SourceGaloisClosureField m)) :=
  GlobalPlace.finitePlaceDivisor (sourceGaloisWZeroPlaceOfPrime m)

/-- The actual reduced divisor on the infinity-place prime fibre over
`F256(w)`. -/
noncomputable def sourceGaloisWInfinityFibreDivisor (m : ℕ) :
    Divisor (GlobalPlace F256 (SourceGaloisClosureField m)) :=
  GlobalPlace.finitePlaceDivisor (sourceGaloisWInfinityPlaceOfPrime m)

/-- Each genuine zero-fibre place has coefficient one. -/
@[simp]
theorem sourceGaloisWZeroFibreDivisor_apply (m : ℕ) (P : SourceGaloisWZeroPrime m) :
    sourceGaloisWZeroFibreDivisor m (sourceGaloisWZeroPlaceOfPrime m P) = 1 := by
  exact GlobalPlace.finitePlaceDivisor_apply _
    (sourceGaloisWZeroPlaceOfPrime_injective m) P

/-- Each genuine infinity-fibre place has coefficient one. -/
@[simp]
theorem sourceGaloisWInfinityFibreDivisor_apply (m : ℕ)
    (P : SourceGaloisWInfinityPrime m) :
    sourceGaloisWInfinityFibreDivisor m
        (sourceGaloisWInfinityPlaceOfPrime m P) = 1 := by
  exact GlobalPlace.finitePlaceDivisor_apply _
    (sourceGaloisWInfinityPlaceOfPrime_injective m) P

/-- The zero-fibre divisor has exactly the genuine zero-fibre places as its
support. -/
theorem sourceGaloisWZeroFibreDivisor_support (m : ℕ) :
    ↑(sourceGaloisWZeroFibreDivisor m).support =
      Set.range (sourceGaloisWZeroPlaceOfPrime m) := by
  exact GlobalPlace.finitePlaceDivisor_support _
    (sourceGaloisWZeroPlaceOfPrime_injective m)

/-- The infinity-fibre divisor has exactly the genuine infinity-fibre places
as its support. -/
theorem sourceGaloisWInfinityFibreDivisor_support (m : ℕ) :
    ↑(sourceGaloisWInfinityFibreDivisor m).support =
      Set.range (sourceGaloisWInfinityPlaceOfPrime m) := by
  exact GlobalPlace.finitePlaceDivisor_support _
    (sourceGaloisWInfinityPlaceOfPrime_injective m)

/-- The zero-fibre divisor is coefficientwise nonnegative. -/
theorem sourceGaloisWZeroFibreDivisor_nonnegative (m : ℕ) :
    0 ≤ sourceGaloisWZeroFibreDivisor m := by
  change 0 ≤ GlobalPlace.finitePlaceDivisor (sourceGaloisWZeroPlaceOfPrime m)
  exact GlobalPlace.finitePlaceDivisor_nonnegative _

/-- The infinity-fibre divisor is coefficientwise nonnegative. -/
theorem sourceGaloisWInfinityFibreDivisor_nonnegative (m : ℕ) :
    0 ≤ sourceGaloisWInfinityFibreDivisor m := by
  change 0 ≤ GlobalPlace.finitePlaceDivisor (sourceGaloisWInfinityPlaceOfPrime m)
  exact GlobalPlace.finitePlaceDivisor_nonnegative _

/-- The weighted degree of the zero-fibre divisor is the fibre cardinality
times its common inertia degree. -/
theorem sourceGaloisWZeroFibreDivisor_degree (m : ℕ) :
    Divisor.degree GlobalPlace.residueDegree (sourceGaloisWZeroFibreDivisor m) =
      (Set.ncard (SourceGaloisWZeroPrime m) : ℤ) *
        (sourceGaloisWZeroInertiaDegree m : ℤ) := by
  rw [sourceGaloisWZeroFibreDivisor, GlobalPlace.finitePlaceDivisor_degree]
  simp_rw [sourceGaloisWZeroPlace_residueDegree_eq_inertia]
  simp [Set.fintypeCard_eq_ncard]

/-- The weighted degree of the infinity-fibre divisor is the fibre cardinality
times its common inertia degree. -/
theorem sourceGaloisWInfinityFibreDivisor_degree (m : ℕ) :
    Divisor.degree GlobalPlace.residueDegree
        (sourceGaloisWInfinityFibreDivisor m) =
      (Set.ncard (SourceGaloisWInfinityPrime m) : ℤ) *
        (sourceGaloisWInfinityInertiaDegree m : ℤ) := by
  rw [sourceGaloisWInfinityFibreDivisor, GlobalPlace.finitePlaceDivisor_degree]
  simp_rw [sourceGaloisWInfinityPlace_residueDegree_eq_inertia]
  simp [Set.fintypeCard_eq_ncard]

/-- The zero-fibre ramification index times its divisor degree is the actual
relative source-normal-closure degree over `F256(w)`. -/
theorem sourceGaloisWZeroRamificationIndex_mul_fibreDivisor_degree (m : ℕ) :
    (sourceGaloisWZeroRamificationIndex m : ℤ) *
        Divisor.degree GlobalPlace.residueDegree
          (sourceGaloisWZeroFibreDivisor m) =
      (sourceGaloisWRelativeDegree m : ℤ) := by
  rw [sourceGaloisWZeroFibreDivisor_degree]
  have h := congrArg (fun n : ℕ => (n : ℤ))
    (sourceGaloisWZero_fundamental_identity_relativeDegree m)
  norm_num only [Nat.cast_mul] at h
  calc
    (sourceGaloisWZeroRamificationIndex m : ℤ) *
          ((Set.ncard (SourceGaloisWZeroPrime m) : ℤ) *
            (sourceGaloisWZeroInertiaDegree m : ℤ)) =
        (Set.ncard (SourceGaloisWZeroPrime m) : ℤ) *
          ((sourceGaloisWZeroRamificationIndex m : ℤ) *
            (sourceGaloisWZeroInertiaDegree m : ℤ)) := by ring
    _ = (sourceGaloisWRelativeDegree m : ℤ) := h

/-- The infinity-fibre ramification index times its divisor degree is the
actual relative source-normal-closure degree over `F256(w)`. -/
theorem sourceGaloisWInfinityRamificationIndex_mul_fibreDivisor_degree (m : ℕ) :
    (sourceGaloisWInfinityRamificationIndex m : ℤ) *
        Divisor.degree GlobalPlace.residueDegree
          (sourceGaloisWInfinityFibreDivisor m) =
      (sourceGaloisWRelativeDegree m : ℤ) := by
  rw [sourceGaloisWInfinityFibreDivisor_degree]
  have h := congrArg (fun n : ℕ => (n : ℤ))
    (sourceGaloisWInfinity_fundamental_identity_relativeDegree m)
  norm_num only [Nat.cast_mul] at h
  calc
    (sourceGaloisWInfinityRamificationIndex m : ℤ) *
          ((Set.ncard (SourceGaloisWInfinityPrime m) : ℤ) *
            (sourceGaloisWInfinityInertiaDegree m : ℤ)) =
        (Set.ncard (SourceGaloisWInfinityPrime m) : ℤ) *
          ((sourceGaloisWInfinityRamificationIndex m : ℤ) *
            (sourceGaloisWInfinityInertiaDegree m : ℤ)) := by ring
    _ = (sourceGaloisWRelativeDegree m : ℤ) := h

/-- The source normalization `e₀ deg(A) = n / 15` for the actual zero-fibre
divisor. -/
theorem sourceGaloisWZeroRamificationIndex_mul_fibreDivisor_degree_eq_length_div
    (m : ℕ) :
    (sourceGaloisWZeroRamificationIndex m : ℤ) *
        Divisor.degree GlobalPlace.residueDegree
          (sourceGaloisWZeroFibreDivisor m) =
      (sourceGaloisClosureSelectedLength m / 15 : ℕ) := by
  rw [sourceGaloisWZeroRamificationIndex_mul_fibreDivisor_degree]
  norm_cast
  rw [← sourceGaloisWRelativeDegree_mul_fifteen m]
  simp

/-- The source normalization `e∞ deg(B) = n / 15` for the actual infinity-fibre
divisor. -/
theorem sourceGaloisWInfinityRamificationIndex_mul_fibreDivisor_degree_eq_length_div
    (m : ℕ) :
    (sourceGaloisWInfinityRamificationIndex m : ℤ) *
        Divisor.degree GlobalPlace.residueDegree
          (sourceGaloisWInfinityFibreDivisor m) =
      (sourceGaloisClosureSelectedLength m / 15 : ℕ) := by
  rw [sourceGaloisWInfinityRamificationIndex_mul_fibreDivisor_degree]
  norm_cast
  rw [← sourceGaloisWRelativeDegree_mul_fifteen m]
  simp

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
