import QEC.Coding.BalancedProduct.UnbalancedFamily
import QEC.Coding.CodeReduction.DistanceBalancing.SubsystemKernel
import QEC.Coding.CSS.SubsystemDual

/-!
# The distance-balanced BE20 subsystem family

This file applies the EKZ20 distance-balancing product to the finite
unbalanced BE20 subsystem.  The classical factor is the construction-owned
LPS quotient Tanner boundary.  It is not assumed surjective: its cokernel is
explicitly discarded as gauge by `balancedKernelSubsystemData`.
-/

namespace QEC.Coding.BalancedProduct.BE20Balanced

open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner

def blocklengthCoefficient : Nat := 120601
def dimensionLowerCoefficient : Nat := 4 * blocklengthCoefficient ^ 4
def dimensionUpperCoefficient : Nat := 201 ^ 10
def dressedXPowerCoefficient : Nat :=
  blocklengthCoefficient ^ 3 * BE20Unbalanced.dressedZCoefficient ^ 5
def dressedZLinearCoefficient : Nat :=
  2 * 10000000 * (4 * 804 * 37273)
def dressedZPowerCoefficient : Nat :=
  blocklengthCoefficient ^ 3 * dressedZLinearCoefficient ^ 5

@[reducible] noncomputable def edgeOrbit401Nonempty
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1) :
    Nonempty (EdgeOrbit401 q hq) := by
  rw [← Fintype.card_pos_iff, LPSFamily.card_edgeOrbit401 q hq40 hq]
  exact Nat.mul_pos (by norm_num) (Nat.sub_pos_of_lt (by nlinarith))

noncomputable def sourceSubsystem
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1) :=
  HorizontalSubsystem.horizontalSubsystem
    (lpsTannerGroupAlgebraMatrix q hq40 hq)
    (Cyclic.cyclicGenerator q)
    (by
      simpa [Cyclic.CyclicGroup, ZMod.card] using
        (Fact.out : q.Prime).odd_of_ne_two (by omega))

noncomputable def balancingBoundary
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1) :=
  HorizontalSubsystem.quotientBoundary
    (lpsTannerGroupAlgebraMatrix q hq40 hq)

noncomputable def balancedSubsystem
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1) := by
  letI : Nonempty (EdgeOrbit401 q hq) :=
    edgeOrbit401Nonempty q hq40 hq
  exact balancedKernelSubsystemData
    (sourceSubsystem q hq40 hq).dual
    (balancingBoundary q hq40 hq)

/-- Physical coordinates of the balanced code, displayed without unfolding
the selected logical quotient spaces. -/
abbrev BalancedQubitIndex
    (q : Nat) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :=
  DistanceBalancing.QubitIndex
    (LiftedProduct.QubitIndex
      (CheckOrbit401 q) (EdgeOrbit401 q hq) Unit Unit
      (Cyclic.CyclicGroup q))
    (LiftedProduct.C0Index
      (CheckOrbit401 q) Unit (Cyclic.CyclicGroup q))
    (EdgeOrbit401 q hq) (CheckOrbit401 q)

noncomputable instance balancedQubitIndexDecidableEq
    (q : Nat) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :
    DecidableEq (BalancedQubitIndex q hq) := Classical.decEq _

theorem card_balancedQubitIndex
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1) :
    Fintype.card (BalancedQubitIndex q hq) =
      blocklengthCoefficient * q * (q ^ 2 - 1) ^ 2 := by
  rw [DistanceBalancing.card_qubitIndex]
  simp [LiftedProduct.QubitIndex, LiftedProduct.C0Index,
    Fintype.card_sum, Fintype.card_prod,
    Cyclic.CyclicGroup, ZMod.card]
  rw [LPSFamily.card_edgeOrbit401 q hq40 hq,
    LPSFamily.card_checkOrbit401 q hq40]
  simp [blocklengthCoefficient]
  ring

/-- A reusable integral form of the exponent conversion
`N = C q(q²-1)²` and `q(q²-1) = O(d)` imply `N³ = O(d⁵)`. -/
theorem distance_power_bound_of_linear_q_scale
    (q N d coefficient : Nat)
    (hN : N = blocklengthCoefficient * q * (q ^ 2 - 1) ^ 2)
    (hqd : q * (q ^ 2 - 1) ≤ coefficient * d) :
    N ^ 3 ≤ blocklengthCoefficient ^ 3 * coefficient ^ 5 * d ^ 5 := by
  let s := q ^ 2 - 1
  have hs : s ≤ q ^ 2 := Nat.sub_le _ _
  have hsCube : s ^ 3 ≤ (q * s) ^ 2 := by
    calc
      s ^ 3 = s * s ^ 2 := by ring
      _ ≤ q ^ 2 * s ^ 2 := Nat.mul_le_mul_right (s ^ 2) hs
      _ = (q * s) ^ 2 := by ring
  rw [hN]
  change (blocklengthCoefficient * q * s ^ 2) ^ 3 ≤ _
  calc
    (blocklengthCoefficient * q * s ^ 2) ^ 3 =
        blocklengthCoefficient ^ 3 * (q * s) ^ 3 * s ^ 3 := by ring
    _ ≤ blocklengthCoefficient ^ 3 * (q * s) ^ 3 * (q * s) ^ 2 :=
      Nat.mul_le_mul_left _ hsCube
    _ = blocklengthCoefficient ^ 3 * (q * s) ^ 5 := by ring
    _ ≤ blocklengthCoefficient ^ 3 * (coefficient * d) ^ 5 :=
      Nat.mul_le_mul_left _ (pow_le_pow_left' hqd 5)
    _ = blocklengthCoefficient ^ 3 * coefficient ^ 5 * d ^ 5 := by ring

theorem dimension_power_bounds
    (q N K : Nat) (hq40 : 40 < q)
    (hN : N = blocklengthCoefficient * q * (q ^ 2 - 1) ^ 2)
    (hKLower : (q ^ 2 - 1) ^ 2 ≤ K)
    (hKUpper : K ≤ (201 * (q ^ 2 - 1)) ^ 2) :
    N ^ 4 ≤ dimensionLowerCoefficient * K ^ 5 ∧
      K ^ 5 ≤ dimensionUpperCoefficient * N ^ 4 := by
  let s := q ^ 2 - 1
  have hqSqTwo : 2 ≤ q ^ 2 := by nlinarith
  have hsPos : 1 ≤ s := by
    dsimp [s]
    omega
  have hqSq : q ^ 2 ≤ 2 * s := by
    dsimp [s]
    omega
  have hqFourth : q ^ 4 ≤ 4 * s ^ 2 := by
    calc
      q ^ 4 = (q ^ 2) ^ 2 := by ring
      _ ≤ (2 * s) ^ 2 := pow_le_pow_left' hqSq 2
      _ = 4 * s ^ 2 := by ring
  have hsSq : s ^ 2 ≤ q ^ 4 := by
    calc
      s ^ 2 ≤ (q ^ 2) ^ 2 := pow_le_pow_left' (Nat.sub_le _ _) 2
      _ = q ^ 4 := by ring
  constructor
  · rw [hN]
    change (blocklengthCoefficient * q * s ^ 2) ^ 4 ≤ _
    calc
      (blocklengthCoefficient * q * s ^ 2) ^ 4 =
          blocklengthCoefficient ^ 4 * q ^ 4 * s ^ 8 := by ring
      _ ≤ blocklengthCoefficient ^ 4 * (4 * s ^ 2) * s ^ 8 :=
        Nat.mul_le_mul_right (s ^ 8)
          (Nat.mul_le_mul_left _ hqFourth)
      _ = dimensionLowerCoefficient * (s ^ 2) ^ 5 := by
        simp [dimensionLowerCoefficient]
        ring
      _ ≤ dimensionLowerCoefficient * K ^ 5 :=
        Nat.mul_le_mul_left _ (pow_le_pow_left' hKLower 5)
  · calc
      K ^ 5 ≤ ((201 * s) ^ 2) ^ 5 := pow_le_pow_left' hKUpper 5
      _ = 201 ^ 10 * s ^ 8 * s ^ 2 := by ring
      _ ≤ 201 ^ 10 * s ^ 8 * q ^ 4 :=
        Nat.mul_le_mul_left _ hsSq
      _ ≤ 201 ^ 10 *
          (blocklengthCoefficient ^ 4 * q ^ 4 * s ^ 8) := by
        have hCoefficient : 1 ≤ blocklengthCoefficient ^ 4 := by
          simp [blocklengthCoefficient]
        nlinarith [Nat.mul_le_mul_right (q ^ 4 * s ^ 8) hCoefficient]
      _ = dimensionUpperCoefficient *
          (blocklengthCoefficient * q * s ^ 2) ^ 4 := by
        simp [dimensionUpperCoefficient]
        ring
      _ = dimensionUpperCoefficient * N ^ 4 := by rw [hN]

theorem balancedSubsystem_logicalQubits
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1) :
    (balancedSubsystem q hq40 hq).logicalQubits =
      (sourceSubsystem q hq40 hq).logicalQubits *
        Module.finrank (ZMod 2)
          (LinearMap.ker (balancingBoundary q hq40 hq)) := by
  letI : Nonempty (EdgeOrbit401 q hq) :=
    edgeOrbit401Nonempty q hq40 hq
  rw [balancedSubsystem, balancedKernelSubsystemData_logicalQubits,
    SubsystemCSSData.dual_logicalQubits]
  change (sourceSubsystem q hq40 hq).logicalQubits *
      Module.finrank (ZMod 2)
        (LinearMap.ker (Matrix.toLin'
          (LinearMap.toMatrix' (balancingBoundary q hq40 hq)))) = _
  rw [Matrix.toLin'_toMatrix']

theorem balancedSubsystem_logicalQubits_bounds
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1) :
    (q ^ 2 - 1) ^ 2 ≤ (balancedSubsystem q hq40 hq).logicalQubits ∧
      (balancedSubsystem q hq40 hq).logicalQubits ≤
        (201 * (q ^ 2 - 1)) ^ 2 := by
  letI : Nonempty (EdgeOrbit401 q hq) :=
    edgeOrbit401Nonempty q hq40 hq
  have hSourceLower : q ^ 2 - 1 ≤
      (sourceSubsystem q hq40 hq).logicalQubits := by
    simpa only [sourceSubsystem] using
      LPSFamily.lpsHorizontalSubsystem_logicalQubits_lowerBound_polynomial
        q hq40 hq
  have hSourceUpper : (sourceSubsystem q hq40 hq).logicalQubits ≤
      201 * (q ^ 2 - 1) := by
    simpa only [sourceSubsystem] using
      LPSFamily.lpsHorizontalSubsystem_logicalQubits_upperBound_polynomial
        q hq40 hq
  have hKernelLower : q ^ 2 - 1 ≤ Module.finrank (ZMod 2)
      (LinearMap.ker (balancingBoundary q hq40 hq)) := by
    rw [← LPSFamily.card_edgeOrbit401_sub_checkOrbit401 q hq40 hq]
    have h := quotientTanner_middleHomology_finrank_lowerBound q hq40 hq
    rw [HorizontalSubsystem.finrank_quotientTannerComplex_middleHomology_eq_ker] at h
    exact h
  have hKernelUpper : Module.finrank (ZMod 2)
      (LinearMap.ker (balancingBoundary q hq40 hq)) ≤
        201 * (q ^ 2 - 1) := by
    calc
      Module.finrank (ZMod 2)
          (LinearMap.ker (balancingBoundary q hq40 hq)) ≤
          Module.finrank (ZMod 2)
            (Word (ZMod 2) (EdgeOrbit401 q hq)) := Submodule.finrank_le _
      _ = Fintype.card (EdgeOrbit401 q hq) := by simp
      _ = 201 * (q ^ 2 - 1) :=
        LPSFamily.card_edgeOrbit401 q hq40 hq
  rw [balancedSubsystem_logicalQubits q hq40 hq]
  constructor <;> nlinarith

/-- The construction-owned quotient Tanner boundary has the classical
distance required by EKZ balancing.  The proof extracts the actual attained
minimum; no distance parameter is supplied by the caller. -/
theorem balancingBoundary_classicalDistanceAtLeast
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq) :
    ClassicalDistanceAtLeast
      (productData (sourceSubsystem q hq40 hq).dual
        (balancingBoundary q hq40 hq)).classicalBoundary
      (Fintype.card (EdgeOrbit401 q hq) / 10000000) := by
  obtain ⟨actualDistance, hMinimum⟩ :=
    exists_quotientTanner_minimumDistance q hq40 hq
  have hLower : Fintype.card (EdgeOrbit401 q hq) / 10000000 ≤
      actualDistance :=
    quotientTanner_minimumDistance_lowerBound
      q hq40 hq hLPS hMinimum
  rcases hMinimum with ⟨minimumWord, hMinimumMem, hMinimumNe,
    hMinimumWeight, hLeast⟩
  intro w hw hne
  apply hLower.trans
  apply hLeast w
  · rw [(HorizontalSubsystem.quotientTannerComplex
      (lpsTannerGroupAlgebraMatrix q hq40 hq)).mem_middleCycleCode_iff]
    simpa [productData, balancingBoundary,
      DistanceBalancing.Data.ofComplexes, Matrix.toLin'_toMatrix'] using hw
  · exact hne

/-- Both balanced dressed distances follow from the already-certified
unbalanced distances.  Dualization is essential: the classical distance
multiplies the formerly short dressed-X side. -/
theorem balancedSubsystem_dressedDistanceBounds
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq804 : 804 ≤ q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq)
    (hEdgeOrbitLarge : 10000000 ≤ Fintype.card (EdgeOrbit401 q hq))
    (hCheckOrbitLarge : 10000000 ≤ Fintype.card (CheckOrbit401 q)) :
    (balancedSubsystem q hq40 hq).DressedXDistanceAtLeast
        (lpsDressedZLowerBound q hq) ∧
      (balancedSubsystem q hq40 hq).DressedZDistanceAtLeast
        ((Fintype.card (EdgeOrbit401 q hq) / 10000000) *
          lpsDressedXLowerBound q) := by
  letI : Nonempty (EdgeOrbit401 q hq) :=
    edgeOrbit401Nonempty q hq40 hq
  have hSource := lpsHorizontalSubsystem_dressedDistanceBounds
    q hq40 hq804 hq hLPS hEdgeOrbitLarge hCheckOrbitLarge
  have hDualZ : (sourceSubsystem q hq40 hq).dual.DressedZDistanceAtLeast
      (lpsDressedXLowerBound q) :=
    ((sourceSubsystem q hq40 hq).dual_dressedZDistanceAtLeast_iff _).2 hSource.2
  have hDualX : (sourceSubsystem q hq40 hq).dual.DressedXDistanceAtLeast
      (lpsDressedZLowerBound q hq) :=
    ((sourceSubsystem q hq40 hq).dual_dressedXDistanceAtLeast_iff _).2 hSource.1
  constructor
  · exact balancedKernelSubsystemData_dressedXDistanceAtLeast
      (sourceSubsystem q hq40 hq).dual (balancingBoundary q hq40 hq) hDualX
  · exact balancedKernelSubsystemData_dressedZDistanceAtLeast_mul
      (sourceSubsystem q hq40 hq).dual (balancingBoundary q hq40 hq)
      hDualZ (balancingBoundary_classicalDistanceAtLeast q hq40 hq hLPS)

theorem q_scale_le_dressedXLowerBound
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hqLarge : BE20Unbalanced.familyThreshold ≤ q)
    (hq : legendreSym q 401 = -1) :
    q * (q ^ 2 - 1) ≤
      BE20Unbalanced.dressedZCoefficient * lpsDressedZLowerBound q hq := by
  have h := (BE20Unbalanced.dressedZ_linear_bounds q
    (401 * q * (q ^ 2 - 1)) hq40 hqLarge hq rfl).1
  calc
    q * (q ^ 2 - 1) ≤ 401 * (q * (q ^ 2 - 1)) := by
      simpa only [one_mul] using
        Nat.mul_le_mul_right (q * (q ^ 2 - 1)) (by norm_num : 1 ≤ 401)
    _ = 401 * q * (q ^ 2 - 1) := by ring
    _ ≤ BE20Unbalanced.dressedZCoefficient *
        lpsDressedZLowerBound q hq := h

theorem q_scale_le_dressedZLowerBound
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hqLarge : BE20Unbalanced.familyThreshold ≤ q)
    (hq : legendreSym q 401 = -1)
    (hEdgeOrbitLarge : 10000000 ≤ Fintype.card (EdgeOrbit401 q hq)) :
    q * (q ^ 2 - 1) ≤ dressedZLinearCoefficient *
      ((Fintype.card (EdgeOrbit401 q hq) / 10000000) *
        lpsDressedXLowerBound q) := by
  let e := Fintype.card (EdgeOrbit401 q hq)
  let dClassical := e / 10000000
  let dSource := lpsDressedXLowerBound q
  have h804 : 804 ≤ q := by
    dsimp [BE20Unbalanced.familyThreshold] at hqLarge
    omega
  have hDivLarge : 37273 ≤ q / 804 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 804)).2
    dsimp [BE20Unbalanced.familyThreshold] at hqLarge
    omega
  have hFloorOne := BE20Unbalanced.le_two_mul_mul_div
    q 804 (by norm_num) h804
  have hFloorTwo := BE20Unbalanced.le_two_mul_mul_div
    (q / 804) 37273 (by norm_num) hDivLarge
  have hqToSource : q ≤ 4 * 804 * 37273 * dSource := by
    rw [show dSource = (q / 804) / 37273 by
      exact BE20Unbalanced.dressedXLowerBound_eq q hq40 hqLarge]
    calc
      q ≤ 2 * 804 * (q / 804) := hFloorOne
      _ ≤ 2 * 804 * (2 * 37273 * ((q / 804) / 37273)) :=
        Nat.mul_le_mul_left (2 * 804) hFloorTwo
      _ = 4 * 804 * 37273 * ((q / 804) / 37273) := by ring
  have hFloorClassical : e ≤ 2 * 10000000 * dClassical :=
    BE20Unbalanced.le_two_mul_mul_div e 10000000
      (by norm_num) (by simpa only [e] using hEdgeOrbitLarge)
  have hsToClassical : q ^ 2 - 1 ≤ 2 * 10000000 * dClassical := by
    calc
      q ^ 2 - 1 ≤ 201 * (q ^ 2 - 1) := by
        simpa only [one_mul] using
          Nat.mul_le_mul_right (q ^ 2 - 1) (by norm_num : 1 ≤ 201)
      _ = e := by
        simpa only [e] using
          (LPSFamily.card_edgeOrbit401 q hq40 hq).symm
      _ ≤ 2 * 10000000 * dClassical := hFloorClassical
  calc
    q * (q ^ 2 - 1) ≤
        (4 * 804 * 37273 * dSource) *
          (2 * 10000000 * dClassical) :=
      Nat.mul_le_mul hqToSource hsToClassical
    _ = dressedZLinearCoefficient * (dClassical * dSource) := by
      simp [dressedZLinearCoefficient]
      ring

theorem balanced_distance_power_bounds
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hqLarge : BE20Unbalanced.familyThreshold ≤ q)
    (hq : legendreSym q 401 = -1)
    (hEdgeOrbitLarge : 10000000 ≤ Fintype.card (EdgeOrbit401 q hq)) :
    let N := Fintype.card (BalancedQubitIndex q hq)
    N ^ 3 ≤ dressedXPowerCoefficient *
        (lpsDressedZLowerBound q hq) ^ 5 ∧
      N ^ 3 ≤ dressedZPowerCoefficient *
        ((Fintype.card (EdgeOrbit401 q hq) / 10000000) *
          lpsDressedXLowerBound q) ^ 5 := by
  dsimp only
  have hN := card_balancedQubitIndex q hq40 hq
  constructor
  · simpa only [dressedXPowerCoefficient] using
      distance_power_bound_of_linear_q_scale q
        (Fintype.card (BalancedQubitIndex q hq))
        (lpsDressedZLowerBound q hq)
        BE20Unbalanced.dressedZCoefficient hN
        (q_scale_le_dressedXLowerBound q hq40 hqLarge hq)
  · simpa only [dressedZPowerCoefficient] using
      distance_power_bound_of_linear_q_scale q
        (Fintype.card (BalancedQubitIndex q hq))
        ((Fintype.card (EdgeOrbit401 q hq) / 10000000) *
          lpsDressedXLowerBound q)
        dressedZLinearCoefficient hN
        (q_scale_le_dressedZLowerBound q hq40 hqLarge hq hEdgeOrbitLarge)

end QEC.Coding.BalancedProduct.BE20Balanced
