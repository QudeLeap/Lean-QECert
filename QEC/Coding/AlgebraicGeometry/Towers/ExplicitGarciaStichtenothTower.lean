import QEC.Coding.AlgebraicGeometry.Towers.ClosureGenus
import QEC.Coding.AlgebraicGeometry.Towers.SelectedFibreSeparation
import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisWZeroRamification
import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisWRamification

/-!
# The explicit F256 source normal-closure family

Public level i is `SourceGaloisClosureField (i+2)`, the normal closure of
`SourceField (i+2)`. In [Sti06, proof of Theorem 1.7], E_n closes F_(n-1),
so this tail corresponds to E_(i+3), not E_(i+2). Its finite
selected coordinates, reduced fibre divisors, canonical differential and
intrinsic genus all come from the checked construction. The two ramification
parameters are the actual common indices, not the GS95 parity expressions
for a different, non-normalized family.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

open Filter FunctionFieldDifferential

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

/-- Actual normal-closure level, shifted past the initial ramification boundary. -/
abbrev f256GarciaStichtenothField (i : ℕ) : Type := SourceGaloisClosureField (i + 2)

scoped instance f256GarciaStichtenothBaseAlgebra (i : ℕ) :
    Algebra GaloisBaseField (f256GarciaStichtenothField i) := sourceGaloisClosureFieldAlgebra (i + 2)

scoped instance f256GarciaStichtenothConstantAlgebra (i : ℕ) :
    Algebra F256 (f256GarciaStichtenothField i) := sourceGaloisClosureConstantAlgebra (i + 2)

scoped instance f256GarciaStichtenothRatFuncAlgebra (i : ℕ) :
    Algebra (RatFunc F256) (f256GarciaStichtenothField i) := sourceGaloisClosureRatFuncAlgebra (i + 2)

scoped instance f256GarciaStichtenothPolynomialAlgebra (i : ℕ) :
    Algebra (Polynomial F256) (f256GarciaStichtenothField i) := sourceClosurePolynomialAlgebra (i + 2)

scoped instance f256GarciaStichtenothRatFuncTower (i : ℕ) :
    IsScalarTower F256 (RatFunc F256) (f256GarciaStichtenothField i) :=
  sourceGaloisClosureRatFuncScalarTower (i + 2)

scoped instance f256GarciaStichtenothPolynomialTower (i : ℕ) :
    IsScalarTower (Polynomial F256) (RatFunc F256) (f256GarciaStichtenothField i) :=
  sourceClosurePolynomialTower (i + 2)

scoped instance f256GarciaStichtenothFunctionField (i : ℕ) :
    _root_.FunctionField F256 (f256GarciaStichtenothField i) := sourceGaloisClosureFunctionField (i + 2)

scoped instance f256GarciaStichtenothSeparable (i : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (f256GarciaStichtenothField i) :=
  (sourceGaloisClosureRatFuncIsGalois (i + 2)).to_isSeparable

scoped instance f256GarciaStichtenothFullConstants (i : ℕ) :
    IsFullConstantField F256 (f256GarciaStichtenothField i) := sourceClosureFullConstants (i + 2)

scoped instance f256GarciaStichtenothDirectFullConstants (i : ℕ) :
    @IsFullConstantField F256 (f256GarciaStichtenothField i) _ _
      (@AffinePlace.constantAlgebra F256 (f256GarciaStichtenothField i) _ _
        (f256GarciaStichtenothPolynomialAlgebra i)) := sourceClosureDirectFullConstants (i + 2)

def f256GarciaStichtenothSeedEmbedding (i : ℕ) :
    SourceField (i + 2) →ₐ[GaloisBaseField] f256GarciaStichtenothField i :=
  sourceGaloisSeedToClosure (i + 2)

theorem f256GarciaStichtenothSeedRecursionEquation (i : ℕ) :
    f256GarciaStichtenothSeedEmbedding i (sourceDistinguishedCoordinate (i + 2)) ^ 16 +
      f256GarciaStichtenothSeedEmbedding i (sourceDistinguishedCoordinate (i + 2)) =
    f256GarciaStichtenothSeedEmbedding i (sourceRecursionEmbedding (i + 1)
      (sourceStepRhs (sourceDistinguishedCoordinate (i + 1)))) := by
  simpa only [map_add, map_pow] using
    congrArg (f256GarciaStichtenothSeedEmbedding i) (sourceRecursion_equation (i + 1))

def f256GarciaStichtenothLength (i : ℕ) : ℕ := sourceGaloisClosureSelectedLength (i + 2)

theorem f256GarciaStichtenothLength_lower_bound (i : ℕ) :
    240 * 16 ^ (i + 2) ≤ f256GarciaStichtenothLength i :=
  sourceGaloisClosureSelectedLength_lower_bound (i + 2)

theorem f256GarciaStichtenothLength_two_hundred_forty_le (i : ℕ) :
    240 ≤ f256GarciaStichtenothLength i := by
  have h := f256GarciaStichtenothLength_lower_bound i
  have hp : 0 < 16 ^ (i + 2) := pow_pos (by norm_num) _
  omega

theorem f256GarciaStichtenothLength_div_fifteen_pos (i : ℕ) :
    0 < f256GarciaStichtenothLength i / 15 := by
  apply Nat.div_pos
  · have h := f256GarciaStichtenothLength_two_hundred_forty_le i
    omega
  · norm_num

theorem f256GarciaStichtenothLength_fifteen_dvd (i : ℕ) :
    15 ∣ f256GarciaStichtenothLength i :=
  ⟨sourceGaloisWRelativeDegree (i + 2), (sourceGaloisWRelativeDegree_mul_fifteen (i + 2)).symm⟩

def f256GarciaStichtenothSelectedRationalPlace (i : ℕ)
    (j : Fin (f256GarciaStichtenothLength i)) : RationalPlace F256 (f256GarciaStichtenothField i) :=
  sourceGaloisClosureSelectedRationalPlace (i + 2) j

def f256GarciaStichtenothSelectedPlace (i : ℕ) (j : Fin (f256GarciaStichtenothLength i)) :
    GlobalPlace F256 (f256GarciaStichtenothField i) :=
  (f256GarciaStichtenothSelectedRationalPlace i j).place

def f256GarciaStichtenothSelectedPlaces (i : ℕ) :
    Finset (GlobalPlace F256 (f256GarciaStichtenothField i)) :=
  sourceGaloisClosureSelectedPlaces (i + 2)

theorem f256GarciaStichtenothSelectedPlaces_card (i : ℕ) :
    (f256GarciaStichtenothSelectedPlaces i).card = f256GarciaStichtenothLength i :=
  sourceGaloisClosureSelectedPlaces_card (i + 2)

theorem f256GarciaStichtenothSelectedPlace_injective (i : ℕ) :
    Function.Injective (f256GarciaStichtenothSelectedPlace i) := by
  classical
  have hcard : (Finset.univ.image (f256GarciaStichtenothSelectedPlace i)).card =
      (Finset.univ : Finset (Fin (f256GarciaStichtenothLength i))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact sourceGaloisClosureSelectedPlaces_card (i + 2)
  exact fun a b h => Finset.card_image_iff.mp hcard (Finset.mem_univ a) (Finset.mem_univ b) h

theorem f256GarciaStichtenothSelectedPlaces_coe (i : ℕ) :
    (f256GarciaStichtenothSelectedPlaces i : Set (GlobalPlace F256 (f256GarciaStichtenothField i))) =
      Set.range (f256GarciaStichtenothSelectedPlace i) := by
  classical
  change (sourceGaloisClosureSelectedPlaces (i + 2) :
      Set (GlobalPlace F256 (SourceGaloisClosureField (i + 2)))) =
    Set.range (fun j : Fin (sourceGaloisClosureSelectedLength (i + 2)) =>
      (sourceGaloisClosureSelectedRationalPlace (i + 2) j).place)
  simp only [sourceGaloisClosureSelectedPlaces, Finset.coe_image, Finset.coe_univ, Set.image_univ]

/-- Exact finite coordinates for the actual selected place set. -/
def f256GarciaStichtenothSelectedPlaceEquiv (i : ℕ) :
    Fin (f256GarciaStichtenothLength i) ≃ ↑(f256GarciaStichtenothSelectedPlaces i) :=
  (Equiv.ofInjective (f256GarciaStichtenothSelectedPlace i)
    (f256GarciaStichtenothSelectedPlace_injective i)).trans
      (Equiv.setCongr (f256GarciaStichtenothSelectedPlaces_coe i).symm)

def f256GarciaStichtenothDivisorA (i : ℕ) : Divisor (GlobalPlace F256 (f256GarciaStichtenothField i)) :=
  sourceGaloisWZeroFibreDivisor (i + 2)

def f256GarciaStichtenothDivisorB (i : ℕ) : Divisor (GlobalPlace F256 (f256GarciaStichtenothField i)) :=
  sourceGaloisWInfinityFibreDivisor (i + 2)

def f256GarciaStichtenothDivisorD (i : ℕ) : Divisor (GlobalPlace F256 (f256GarciaStichtenothField i)) :=
  sourceGaloisClosureSelectedDivisor (i + 2)

theorem f256GarciaStichtenothDivisorA_nonnegative (i : ℕ) : 0 ≤ f256GarciaStichtenothDivisorA i :=
  sourceGaloisWZeroFibreDivisor_nonnegative (i + 2)

theorem f256GarciaStichtenothDivisorB_nonnegative (i : ℕ) : 0 ≤ f256GarciaStichtenothDivisorB i :=
  sourceGaloisWInfinityFibreDivisor_nonnegative (i + 2)

theorem f256GarciaStichtenothDivisorD_nonnegative (i : ℕ) : 0 ≤ f256GarciaStichtenothDivisorD i :=
  sourceGaloisClosureSelectedDivisor_nonnegative (i + 2)

theorem f256GarciaStichtenothDivisorA_support_disjoint_D (i : ℕ) :
    Disjoint (f256GarciaStichtenothDivisorA i).support (f256GarciaStichtenothDivisorD i).support :=
  sourceClosureWZeroFibre_disjoint_selected (i + 2)

theorem f256GarciaStichtenothDivisorB_support_disjoint_D (i : ℕ) :
    Disjoint (f256GarciaStichtenothDivisorB i).support (f256GarciaStichtenothDivisorD i).support :=
  sourceClosureWInfinityFibre_disjoint_selected (i + 2)

/-- Actual common ramification indices at the two named fibres. -/
def f256GarciaStichtenothAlpha (i : ℕ) : ℕ := sourceGaloisWZeroRamificationIndex (i + 2)
def f256GarciaStichtenothBeta (i : ℕ) : ℕ := sourceGaloisWInfinityRamificationIndex (i + 2)

theorem f256GarciaStichtenothAlpha_even (i : ℕ) : Even (f256GarciaStichtenothAlpha i) :=
  sourceGaloisWZeroRamificationIndex_even (i + 1)

theorem f256GarciaStichtenothBeta_even (i : ℕ) : Even (f256GarciaStichtenothBeta i) :=
  sourceGaloisWInfinityRamificationIndex_even (i + 2)

theorem f256GarciaStichtenothAlpha_two_le (i : ℕ) : 2 ≤ f256GarciaStichtenothAlpha i :=
  sourceGaloisWZeroRamificationIndex_two_le (i + 1)

theorem f256GarciaStichtenothBeta_two_le (i : ℕ) : 2 ≤ f256GarciaStichtenothBeta i :=
  sourceGaloisWInfinityRamificationIndex_two_le (i + 2)

theorem f256GarciaStichtenothAlpha_mul_degree_divisorA (i : ℕ) :
    (f256GarciaStichtenothAlpha i : ℤ) *
      Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorA i) =
        (f256GarciaStichtenothLength i / 15 : ℕ) :=
  sourceGaloisWZeroRamificationIndex_mul_fibreDivisor_degree_eq_length_div (i + 2)

theorem f256GarciaStichtenothBeta_mul_degree_divisorB (i : ℕ) :
    (f256GarciaStichtenothBeta i : ℤ) *
      Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorB i) =
        (f256GarciaStichtenothLength i / 15 : ℕ) :=
  sourceGaloisWInfinityRamificationIndex_mul_fibreDivisor_degree_eq_length_div (i + 2)

theorem f256GarciaStichtenothDivisorD_degree (i : ℕ) :
    Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorD i) =
      f256GarciaStichtenothLength i := sourceGaloisClosureSelectedDivisor_degree (i + 2)

theorem f256GarciaStichtenothDivisorA_degree_pos (i : ℕ) :
    0 < Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorA i) := by
  have hp : (0 : ℤ) < (f256GarciaStichtenothLength i / 15 : ℕ) := by
    exact_mod_cast f256GarciaStichtenothLength_div_fifteen_pos i
  by_contra hn
  have h := mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg (f256GarciaStichtenothAlpha i))
    (le_of_not_gt hn)
  rw [f256GarciaStichtenothAlpha_mul_degree_divisorA] at h
  omega

theorem f256GarciaStichtenothDivisorB_degree_pos (i : ℕ) :
    0 < Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorB i) := by
  have hp : (0 : ℤ) < (f256GarciaStichtenothLength i / 15 : ℕ) := by
    exact_mod_cast f256GarciaStichtenothLength_div_fifteen_pos i
  by_contra hn
  have h := mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg (f256GarciaStichtenothBeta i))
    (le_of_not_gt hn)
  rw [f256GarciaStichtenothBeta_mul_degree_divisorB] at h
  omega

def f256GarciaStichtenothCanonicalDifferential (i : ℕ) : Differential F256 (f256GarciaStichtenothField i) :=
  sourceClosureCanonicalDifferential (i + 2)

theorem f256GarciaStichtenothCanonicalDifferential_ne_zero (i : ℕ) :
    f256GarciaStichtenothCanonicalDifferential i ≠ 0 := sourceClosureCanonicalDifferential_ne_zero (i + 2)

def f256GarciaStichtenothCanonicalDifferentialAtPlace (i : ℕ)
    (P : GlobalPlace F256 (f256GarciaStichtenothField i)) : Differential.simplePoleDifferentialLattice P :=
  sourceClosureCanonicalDifferentialAtPlace (i + 2) P

theorem f256GarciaStichtenothCanonicalDifferentialAtPlace_coe (i : ℕ)
    (P : GlobalPlace F256 (f256GarciaStichtenothField i)) :
    (f256GarciaStichtenothCanonicalDifferentialAtPlace i P : Differential F256 (f256GarciaStichtenothField i)) =
      f256GarciaStichtenothCanonicalDifferential i := rfl

theorem f256GarciaStichtenothCanonicalDifferential_selected_residue (i : ℕ)
    (j : Fin (f256GarciaStichtenothLength i)) :
    Differential.simplePoleResidue (f256GarciaStichtenothSelectedPlace i j)
      (f256GarciaStichtenothCanonicalDifferentialAtPlace i (f256GarciaStichtenothSelectedPlace i j)) = 1 :=
  sourceClosureCanonicalDifferential_selected_residue (i + 2) j

def f256GarciaStichtenothCanonicalDivisor (i : ℕ) : Divisor (GlobalPlace F256 (f256GarciaStichtenothField i)) :=
  sourceClosureCanonicalDivisor (i + 2)

theorem f256GarciaStichtenothCanonicalDivisor_eq (i : ℕ) :
    f256GarciaStichtenothCanonicalDivisor i =
      (16 * (f256GarciaStichtenothAlpha i : ℤ) - 2) • f256GarciaStichtenothDivisorA i +
        ((f256GarciaStichtenothBeta i : ℤ) - 2) • f256GarciaStichtenothDivisorB i -
          f256GarciaStichtenothDivisorD i := sourceClosureCanonicalDivisor_eq (i + 2)

theorem f256GarciaStichtenothCanonicalDivisor_isCanonical (i : ℕ) :
    IsCanonicalDivisor (k := F256) (F := f256GarciaStichtenothField i)
      (f256GarciaStichtenothCanonicalDivisor i) := sourceClosureCanonicalDivisor_isCanonical (i + 2)

def f256GarciaStichtenothGenus (i : ℕ) : ℕ := sourceClosureGenus (i + 2)

theorem f256GarciaStichtenothFunctionFieldGenus_eq (i : ℕ) :
    GlobalPlace.functionFieldGenus F256 (f256GarciaStichtenothField i) =
      f256GarciaStichtenothGenus i := rfl

theorem f256GarciaStichtenothGenus_source_formula (i : ℕ) :
    (f256GarciaStichtenothGenus i : ℚ) = 1 + (f256GarciaStichtenothLength i : ℚ) / 15 *
      (1 - 1 / (f256GarciaStichtenothAlpha i : ℚ) - 1 / (f256GarciaStichtenothBeta i : ℚ)) :=
  sourceClosureGenus_eq_source_formula (i + 2)

theorem f256GarciaStichtenothGenus_ngu24_identity (i : ℕ) :
    15 * (f256GarciaStichtenothAlpha i : ℤ) * f256GarciaStichtenothBeta i *
      ((f256GarciaStichtenothGenus i : ℤ) - 1) =
      f256GarciaStichtenothLength i * ((f256GarciaStichtenothAlpha i : ℤ) *
        f256GarciaStichtenothBeta i - f256GarciaStichtenothAlpha i - f256GarciaStichtenothBeta i) := by
  have ha : (f256GarciaStichtenothAlpha i : ℚ) ≠ 0 := by
    exact_mod_cast (by have h := f256GarciaStichtenothAlpha_two_le i; omega : f256GarciaStichtenothAlpha i ≠ 0)
  have hb : (f256GarciaStichtenothBeta i : ℚ) ≠ 0 := by
    exact_mod_cast (by have h := f256GarciaStichtenothBeta_two_le i; omega : f256GarciaStichtenothBeta i ≠ 0)
  have h : (15 : ℚ) * f256GarciaStichtenothAlpha i * f256GarciaStichtenothBeta i *
      ((f256GarciaStichtenothGenus i : ℚ) - 1) =
      f256GarciaStichtenothLength i * ((f256GarciaStichtenothAlpha i : ℚ) *
        f256GarciaStichtenothBeta i - f256GarciaStichtenothAlpha i - f256GarciaStichtenothBeta i) := by
    rw [f256GarciaStichtenothGenus_source_formula]
    field_simp
    ring
  exact_mod_cast h

theorem f256GarciaStichtenothLength_tendsto_atTop :
    Tendsto f256GarciaStichtenothLength atTop atTop := by
  exact sourceGaloisClosureSelectedLength_tendsto_atTop.comp (tendsto_add_atTop_nat 2)

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
