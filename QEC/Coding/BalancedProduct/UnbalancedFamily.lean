import QEC.Coding.BalancedProduct.LPSFamily

/-!
# Exact finite certificates for the unbalanced BE20 family

The source exponents are encoded by natural-number power inequalities.  Both
sides of the dimension `Theta` claim and both sides of the linear dressed-Z
scale are retained; the dressed-X claim is one-sided, exactly as in BE20.
-/

namespace QEC.Coding.BalancedProduct.BE20Unbalanced

open QEC.Coding
open LPSFamily LPSGraph LPSQuotientTanner

/-- A fixed prefix after which all integral floors in the PK distance bounds
carry their advertised family-independent scales. -/
def familyThreshold : Nat := 100000000

def dimensionLowerCoefficient : Nat := 8 * 401 ^ 2
def dimensionUpperCoefficient : Nat := 4 * 201 ^ 3
def dressedXCoefficient : Nat := 401 * (4 * 804 * 37273) ^ 3
def dressedZCoefficient : Nat := 12 * 10000000 * 3739

/-- A quotient loses at most a factor two once its denominator fits in its
numerator. -/
theorem le_two_mul_mul_div
    (a d : Nat) (hd : 0 < d) (hda : d ≤ a) :
    a ≤ 2 * d * (a / d) := by
  have hq : 1 ≤ a / d :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.div_pos hda hd))
  have hmod : a % d ≤ d := (Nat.mod_lt a hd).le
  calc
    a = d * (a / d) + a % d := (Nat.div_add_mod a d).symm
    _ ≤ d * (a / d) + d := Nat.add_le_add_left hmod _
    _ ≤ d * (a / d) + d * (a / d) := by
      exact Nat.add_le_add_left (by
        simpa only [mul_one] using Nat.mul_le_mul_left d hq) _
    _ = 2 * d * (a / d) := by ring

/-- Exact finite meaning of the unbalanced BE20 parameter claim.  The
construction, graph, local code, Tanner maps, logical sector, and locality
witness are all fixed by `q`; none is a field supplied by the caller. -/
def UnbalancedFamilyCertificate
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) : Prop :=
  let hOdd : Odd q :=
    (Fact.out : q.Prime).odd_of_ne_two (by omega)
  let D := HorizontalSubsystem.horizontalSubsystem
    (lpsTannerGroupAlgebraMatrix q hq40 hq)
    (Cyclic.cyclicGenerator q)
    (by simpa [Cyclic.CyclicGroup, ZMod.card] using hOdd)
  let N := Fintype.card
    (LiftedProduct.QubitIndex
      (CheckOrbit401 q) (EdgeOrbit401 q hq) Unit Unit
      (Cyclic.CyclicGroup q))
  let K := D.logicalQubits
  let dX := lpsDressedXLowerBound q
  let dZ := lpsDressedZLowerBound q hq
  (D.complex.binaryCSSCode).stabilizer.IsSourceValidBinary ∧
    D.DressedXDistanceAtLeast dX ∧
    D.DressedZDistanceAtLeast dZ ∧
    BoundedLocality
      (LiftedProduct.boundaryIncidence
        (Cyclic.liftedProductData
          (lpsTannerGroupAlgebraMatrix q hq40 hq)
          (Cyclic.cyclicGenerator q))).localityProfile 404 ∧
    N = 401 * q * (q ^ 2 - 1) ∧
    q ^ 2 - 1 ≤ K ∧
    K ≤ 201 * (q ^ 2 - 1) ∧
    N ^ 2 ≤ dimensionLowerCoefficient * K ^ 3 ∧
    K ^ 3 ≤ dimensionUpperCoefficient * N ^ 2 ∧
    N ≤ dressedXCoefficient * dX ^ 3 ∧
    N ≤ dressedZCoefficient * dZ ∧
    dZ ≤ N

theorem quotientScales_large
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q)
    (hqLarge : familyThreshold ≤ q)
    (hq : legendreSym q 401 = -1) :
    10000000 ≤ Fintype.card (EdgeOrbit401 q hq) ∧
      10000000 ≤ Fintype.card (CheckOrbit401 q) := by
  rw [LPSFamily.card_edgeOrbit401 q hq40 hq,
    LPSFamily.card_checkOrbit401 q hq40]
  dsimp [familyThreshold] at hqLarge
  have hqSub : q ≤ q ^ 2 - 1 := by
    apply Nat.le_sub_of_add_le
    nlinarith
  constructor
  · calc
      10000000 ≤ 201 * q := by omega
      _ ≤ 201 * (q ^ 2 - 1) := Nat.mul_le_mul_left 201 hqSub
  · calc
      10000000 ≤ 200 * q := by omega
      _ ≤ 200 * (q ^ 2 - 1) := Nat.mul_le_mul_left 200 hqSub

theorem dressedXLowerBound_eq
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q)
    (hqLarge : familyThreshold ≤ q) :
    lpsDressedXLowerBound q = (q / 804) / 37273 := by
  have hCheckLarge : 10000000 ≤ Fintype.card (CheckOrbit401 q) :=
    by
      rw [LPSFamily.card_checkOrbit401 q hq40]
      dsimp [familyThreshold] at hqLarge
      have hqSub : q ≤ q ^ 2 - 1 := by
        apply Nat.le_sub_of_add_le
        nlinarith
      calc
        10000000 ≤ 200 * q := by omega
        _ ≤ 200 * (q ^ 2 - 1) := Nat.mul_le_mul_left 200 hqSub
  have hScalePositive : 0 < lpsDualQuotientDistanceScale q := by
    exact Nat.div_pos hCheckLarge (by norm_num)
  unfold lpsDressedXLowerBound
  rw [min_eq_right]
  have hOne : 1 ≤ lpsDualQuotientDistanceScale q := by omega
  calc
    q / 804 ≤ q := Nat.div_le_self _ _
    _ = q * 1 := by omega
    _ ≤ q * lpsDualQuotientDistanceScale q :=
      Nat.mul_le_mul_left q hOne

theorem dimension_power_bounds
    (q N K : Nat)
    (hqLarge : familyThreshold ≤ q)
    (hN : N = 401 * q * (q ^ 2 - 1))
    (hKLower : q ^ 2 - 1 ≤ K)
    (hKUpper : K ≤ 201 * (q ^ 2 - 1)) :
    N ^ 2 ≤ dimensionLowerCoefficient * K ^ 3 ∧
      K ^ 3 ≤ dimensionUpperCoefficient * N ^ 2 := by
  dsimp [familyThreshold] at hqLarge
  have hqSqGe : 2 ≤ q ^ 2 := by nlinarith
  have hqSqPos : 1 ≤ q ^ 2 - 1 := by
    omega
  have hKPos : 1 ≤ K := hqSqPos.trans hKLower
  have hqSqLe : q ^ 2 ≤ 2 * K := by
    calc
      q ^ 2 = (q ^ 2 - 1) + 1 := by omega
      _ ≤ K + K := Nat.add_le_add hKLower hKPos
      _ = 2 * K := by ring
  have hNUpper : N ≤ 401 * q ^ 3 := by
    rw [hN]
    have hsub : q ^ 2 - 1 ≤ q ^ 2 := Nat.sub_le _ _
    calc
      401 * q * (q ^ 2 - 1) ≤ 401 * q * q ^ 2 :=
        Nat.mul_le_mul_left (401 * q) hsub
      _ = 401 * q ^ 3 := by ring
  constructor
  · calc
      N ^ 2 ≤ (401 * q ^ 3) ^ 2 := pow_le_pow_left' hNUpper 2
      _ = 401 ^ 2 * (q ^ 2) ^ 3 := by ring
      _ ≤ 401 ^ 2 * (2 * K) ^ 3 := by gcongr
      _ = dimensionLowerCoefficient * K ^ 3 := by
        simp only [dimensionLowerCoefficient]
        ring
  · have hSubLe : q ^ 2 ≤ 2 * (q ^ 2 - 1) := by
      calc
        q ^ 2 = (q ^ 2 - 1) + 1 := by omega
        _ ≤ (q ^ 2 - 1) + (q ^ 2 - 1) :=
          Nat.add_le_add_left hqSqPos _
        _ = 2 * (q ^ 2 - 1) := by ring
    have hCube : (q ^ 2) ^ 3 ≤
        4 * (q ^ 2 * (q ^ 2 - 1) ^ 2) := by
      calc
        (q ^ 2) ^ 3 = q ^ 2 * (q ^ 2) ^ 2 := by ring
        _ ≤ q ^ 2 * (2 * (q ^ 2 - 1)) ^ 2 := by gcongr
        _ = 4 * (q ^ 2 * (q ^ 2 - 1) ^ 2) := by ring
    have hBaseToN : q ^ 2 * (q ^ 2 - 1) ^ 2 ≤ N ^ 2 := by
      rw [hN]
      calc
        q ^ 2 * (q ^ 2 - 1) ^ 2 ≤
            401 ^ 2 * (q ^ 2 * (q ^ 2 - 1) ^ 2) := by
          simpa only [one_mul] using Nat.mul_le_mul_right
            (q ^ 2 * (q ^ 2 - 1) ^ 2) (by norm_num : 1 ≤ 401 ^ 2)
        _ = (401 * q * (q ^ 2 - 1)) ^ 2 := by ring
    calc
      K ^ 3 ≤ (201 * (q ^ 2 - 1)) ^ 3 :=
        pow_le_pow_left' hKUpper 3
      _ ≤ 201 ^ 3 * (q ^ 2) ^ 3 := by
        rw [mul_pow]
        exact Nat.mul_le_mul_left _
          (pow_le_pow_left' (Nat.sub_le (q ^ 2) 1) 3)
      _ ≤ 201 ^ 3 *
          (4 * (q ^ 2 * (q ^ 2 - 1) ^ 2)) :=
        Nat.mul_le_mul_left _ hCube
      _ ≤ 4 * 201 ^ 3 * N ^ 2 := by
        nlinarith [Nat.mul_le_mul_left (4 * 201 ^ 3) hBaseToN]
      _ = dimensionUpperCoefficient * N ^ 2 := by
        simp [dimensionUpperCoefficient]

theorem dressedX_power_bound
    (q N : Nat) [Fact q.Prime]
    (hq40 : 40 < q)
    (hqLarge : familyThreshold ≤ q)
    (hq : legendreSym q 401 = -1)
    (hN : N = 401 * q * (q ^ 2 - 1)) :
    N ≤ dressedXCoefficient * lpsDressedXLowerBound q ^ 3 := by
  have h804 : 804 ≤ q := by
    dsimp [familyThreshold] at hqLarge
    omega
  have hDivLarge : 37273 ≤ q / 804 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 804)).2
    dsimp [familyThreshold] at hqLarge
    omega
  have hFloorOne := le_two_mul_mul_div q 804 (by norm_num) h804
  have hFloorTwo := le_two_mul_mul_div (q / 804) 37273
    (by norm_num) hDivLarge
  have hDX : q ≤
      4 * 804 * 37273 * lpsDressedXLowerBound q := by
    rw [dressedXLowerBound_eq q hq40 hqLarge]
    calc
      q ≤ 2 * 804 * (q / 804) := hFloorOne
      _ ≤ 2 * 804 * (2 * 37273 * ((q / 804) / 37273)) := by
        exact Nat.mul_le_mul_left (2 * 804) hFloorTwo
      _ = 4 * 804 * 37273 * ((q / 804) / 37273) := by ring
  have hNUpper : N ≤ 401 * q ^ 3 := by
    rw [hN]
    calc
      401 * q * (q ^ 2 - 1) ≤ 401 * q * q ^ 2 :=
        Nat.mul_le_mul_left (401 * q) (Nat.sub_le _ _)
      _ = 401 * q ^ 3 := by ring
  calc
    N ≤ 401 * q ^ 3 := hNUpper
    _ ≤ 401 *
        (4 * 804 * 37273 * lpsDressedXLowerBound q) ^ 3 := by gcongr
    _ = dressedXCoefficient * lpsDressedXLowerBound q ^ 3 := by
      simp [dressedXCoefficient]
      ring

theorem dressedZ_linear_bounds
    (q N : Nat) [Fact q.Prime]
    (hq40 : 40 < q)
    (hqLarge : familyThreshold ≤ q)
    (hq : legendreSym q 401 = -1)
    (hN : N = 401 * q * (q ^ 2 - 1)) :
    N ≤ dressedZCoefficient * lpsDressedZLowerBound q hq ∧
      lpsDressedZLowerBound q hq ≤ N := by
  let e := Fintype.card (EdgeOrbit401 q hq)
  let s := e / 10000000
  let d := (q * s) / 3739
  have he : e = 201 * (q ^ 2 - 1) :=
    LPSFamily.card_edgeOrbit401 q hq40 hq
  have heLarge : 10000000 ≤ e := by
    simpa only [e] using (quotientScales_large q hq40 hqLarge hq).1
  have hsPos : 1 ≤ s := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (Nat.div_pos heLarge (by norm_num)))
  have hqsLarge : 3739 ≤ q * s := by
    have hqLarge' : 3739 ≤ q := by
      dsimp [familyThreshold] at hqLarge
      omega
    calc
      3739 ≤ q := hqLarge'
      _ = q * 1 := by omega
      _ ≤ q * s := Nat.mul_le_mul_left q hsPos
  have hFloorE := le_two_mul_mul_div e 10000000
    (by norm_num) heLarge
  have hFloorD := le_two_mul_mul_div (q * s) 3739
    (by norm_num) hqsLarge
  have hNToQE : N ≤ 3 * (q * e) := by
    rw [hN, he]
    nlinarith
  have hQEToD : q * e ≤
      4 * 10000000 * 3739 * d := by
    calc
      q * e ≤ q * (2 * 10000000 * s) :=
        Nat.mul_le_mul_left q hFloorE
      _ = 2 * 10000000 * (q * s) := by ring
      _ ≤ 2 * 10000000 * (2 * 3739 * d) :=
        Nat.mul_le_mul_left (2 * 10000000) hFloorD
      _ = 4 * 10000000 * 3739 * d := by ring
  have hdDef : d = lpsDressedZLowerBound q hq := by rfl
  constructor
  · calc
      N ≤ 3 * (q * e) := hNToQE
      _ ≤ 3 * (4 * 10000000 * 3739 * d) :=
        Nat.mul_le_mul_left 3 hQEToD
      _ = dressedZCoefficient * lpsDressedZLowerBound q hq := by
        rw [← hdDef]
        simp [dressedZCoefficient]
        ring
  · rw [← hdDef]
    calc
      d ≤ q * s := Nat.div_le_self _ _
      _ ≤ q * e := Nat.mul_le_mul_left q (Nat.div_le_self _ _)
      _ ≤ N := by
        rw [hN, he]
        nlinarith

/-- Every sufficiently large admissible prime produces the full finite
unbalanced BE20 certificate.  The only non-elementary argument is the direct
graph-only Rayleigh premise for that prime. -/
theorem unbalancedFamilyCertificate_of_rayleigh
    (q : Nat) [Fact q.Prime]
    (hqLarge : familyThreshold ≤ q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq) :
    UnbalancedFamilyCertificate q (by
      dsimp [familyThreshold] at hqLarge
      omega) hq := by
  classical
  have hq40 : 40 < q := by
    dsimp [familyThreshold] at hqLarge
    omega
  have hq804 : 804 ≤ q := by
    dsimp [familyThreshold] at hqLarge
    omega
  have hScales := quotientScales_large q hq40 hqLarge hq
  let hOdd : Odd q :=
    (Fact.out : q.Prime).odd_of_ne_two (by omega)
  let D := HorizontalSubsystem.horizontalSubsystem
    (lpsTannerGroupAlgebraMatrix q hq40 hq)
    (Cyclic.cyclicGenerator q)
    (by simpa [Cyclic.CyclicGroup, ZMod.card] using hOdd)
  let N := Fintype.card
    (LiftedProduct.QubitIndex
      (CheckOrbit401 q) (EdgeOrbit401 q hq) Unit Unit
      (Cyclic.CyclicGroup q))
  let K := D.logicalQubits
  let dX := lpsDressedXLowerBound q
  let dZ := lpsDressedZLowerBound q hq
  have hDistances := lpsHorizontalSubsystem_dressedDistanceBounds
    q hq40 hq804 hq hLPS hScales.1 hScales.2
  have hN : N = 401 * q * (q ^ 2 - 1) :=
    LPSFamily.lpsHorizontalSubsystem_blocklength_eq_polynomial q hq40 hq
  have hKLower : q ^ 2 - 1 ≤ K :=
    LPSFamily.lpsHorizontalSubsystem_logicalQubits_lowerBound_polynomial
      q hq40 hq
  have hKUpper : K ≤ 201 * (q ^ 2 - 1) :=
    LPSFamily.lpsHorizontalSubsystem_logicalQubits_upperBound_polynomial
      q hq40 hq
  have hDimension := dimension_power_bounds q N K hqLarge hN hKLower hKUpper
  have hXPower := dressedX_power_bound q N hq40 hqLarge hq hN
  have hZLinear := dressedZ_linear_bounds q N hq40 hqLarge hq hN
  unfold UnbalancedFamilyCertificate
  dsimp only
  exact ⟨ChainComplexData.binaryCSSCode_stabilizer_isSourceValidBinary D.complex,
    hDistances.2, hDistances.1,
    lpsHorizontalSubsystem_boundedLocality q hq40 hq,
    hN, hKLower, hKUpper, hDimension.1, hDimension.2,
    hXPower, hZLinear.1, hZLinear.2⟩

/-- Construction-indexed unbounded unbalanced family.  The public spectral
input is uniform over all admissible primes, while the prime and every code
witness are selected internally. -/
theorem exists_be20_unbalanced_family_at
    (hLPS : LPS401FamilyRayleighBound) (B : Nat) :
    ∃ a : AdmissiblePrime401,
      max B familyThreshold < a.q ∧
      UnbalancedFamilyCertificate a.q a.gt40 a.legendre := by
  obtain ⟨a, ha⟩ := LPSFamily.exists_admissiblePrime401_gt
    (max B familyThreshold)
  have hLarge : familyThreshold ≤ a.q :=
    (Nat.le_max_right B familyThreshold).trans ha.le
  refine ⟨a, ha, ?_⟩
  exact unbalancedFamilyCertificate_of_rayleigh a.q hLarge a.legendre
    (hLPS a.q a.prime a.gt40 a.legendre)

end QEC.Coding.BalancedProduct.BE20Unbalanced
