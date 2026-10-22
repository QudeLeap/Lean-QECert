import QEC.Coding.BalancedProduct.BalancedFamily
import QEC.Coding.CodeReduction.DistanceBalancing.Locality

/-!
# Locality of the distance-balanced BE20 family

The quotient Tanner matrix inherits its row and column bounds from the lifted
Tanner action.  This is proved through constant-orbit words, so matrix sparsity
is not accepted as external data.
-/

namespace QEC.Coding.BalancedProduct.BE20Balanced

open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner

theorem augmentation_groupConj
    {G : Type*} [Group G] [Fintype G]
    (a : MonoidAlgebra (ZMod 2) G) :
    HorizontalSubsystem.augmentation (LiftedProduct.groupConj a) =
      HorizontalSubsystem.augmentation a := by
  rw [HorizontalSubsystem.augmentation_apply,
    HorizontalSubsystem.augmentation_apply]
  change (∑ g : G, a.coeff g⁻¹) = ∑ g : G, a.coeff g
  exact Equiv.sum_comp (Equiv.inv G) a.coeff

/-- A basis bound for a lifted Tanner action descends to the augmented
quotient boundary. -/
theorem quotientBoundary_basis_weight_le
    {G aRow aCol : Type}
    [Group G] [Fintype G] [DecidableEq G] [Nonempty G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (L : Nat)
    (hBasis : ∀ i : aCol × G,
      HammingWeight (PKDistance.tannerAction A (Pi.single i 1)) ≤ L)
    (c : aCol) :
    HammingWeight
      (HorizontalSubsystem.quotientBoundary A (Pi.single c 1)) ≤ L := by
  let z : Word (ZMod 2) aCol := Pi.single c 1
  have hLift := HammingWeight_linearMap_le_of_basis
    (PKDistance.tannerAction A) L hBasis
      (PKDistance.constantOrbitWord (G := G) z)
  rw [PKDistance.tannerAction_constantOrbitWord,
    PKDistance.HammingWeight_constantOrbitWord,
    PKDistance.HammingWeight_constantOrbitWord] at hLift
  have hz : HammingWeight z ≤ 1 := by
    exact ClassicalWeightReduction.HammingWeight_single_le_one (F := ZMod 2) c
  have hCard : 0 < Fintype.card G := Fintype.card_pos
  have hMul : Fintype.card G *
      HammingWeight (HorizontalSubsystem.quotientBoundary A z) ≤
      Fintype.card G * L := by
    calc
    Fintype.card G *
        HammingWeight (HorizontalSubsystem.quotientBoundary A z) ≤
        L * (Fintype.card G * HammingWeight z) := hLift
    _ ≤ L * (Fintype.card G * 1) :=
      Nat.mul_le_mul_left L (Nat.mul_le_mul_left _ hz)
    _ = Fintype.card G * L := by ring
  exact Nat.le_of_mul_le_mul_left hMul hCard

theorem quotientBoundary_starTranspose_single
    {G aRow aCol : Type}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (r : aRow) :
    HorizontalSubsystem.quotientBoundary (LiftedProduct.starTranspose A)
        (Pi.single r 1) =
      wordLinearMapTranspose (HorizontalSubsystem.quotientBoundary A)
        (Pi.single r 1) := by
  rw [HorizontalSubsystem.quotientBoundary,
    DistanceBalancing.matrixToLin_single]
  rw [HorizontalSubsystem.quotientBoundary,
    FiberBundle.wordLinearMapTranspose_matrixToLin_single]
  funext c
  simp only [HorizontalSubsystem.quotientBoundaryMatrix,
    LiftedProduct.starTranspose_apply]
  exact augmentation_groupConj (A r c)

theorem lpsQuotientBoundary_column_weight_le
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1)
    (c : EdgeOrbit401 q hq) :
    HammingWeight (balancingBoundary q hq40 hq (Pi.single c 1)) ≤ 400 := by
  letI : Nonempty (Cyclic.CyclicGroup q) :=
    ⟨Multiplicative.ofAdd 0⟩
  apply quotientBoundary_basis_weight_le
    (lpsTannerGroupAlgebraMatrix q hq40 hq) 400
  exact lpsTannerAction_basis_weight_le q hq40 hq

theorem lpsQuotientBoundary_row_weight_le
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1)
    (r : CheckOrbit401 q) :
    HammingWeight
      (wordLinearMapTranspose (balancingBoundary q hq40 hq)
        (Pi.single r 1)) ≤ 402 := by
  letI : Nonempty (Cyclic.CyclicGroup q) :=
    ⟨Multiplicative.ofAdd 0⟩
  unfold balancingBoundary
  rw [← quotientBoundary_starTranspose_single
    (lpsTannerGroupAlgebraMatrix q hq40 hq) r]
  apply quotientBoundary_basis_weight_le
    (LiftedProduct.starTranspose
      (lpsTannerGroupAlgebraMatrix q hq40 hq)) 402
  exact lpsTannerAction_starTranspose_basis_weight_le q hq40 hq

/-- The final distance-balanced family remains qLDPC.  The bound is the
construction-level sum `404 + 402 = 806`; it is independent of `q`. -/
theorem balancedSubsystem_boundedLocality
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (balancedSubsystem q hq40 hq).complex).localityProfile 806 := by
  letI : Nonempty (EdgeOrbit401 q hq) :=
    edgeOrbit401Nonempty q hq40 hq
  have hSource : BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (sourceSubsystem q hq40 hq).complex).localityProfile 404 := by
    exact lpsHorizontalSubsystem_boundedLocality q hq40 hq
  have hDual : BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (sourceSubsystem q hq40 hq).dual.complex).localityProfile 404 :=
    boundedLocality_dual (sourceSubsystem q hq40 hq).complex hSource
  have hProduct := boundedLocality_add_ofComplexes_of_source_bounded
    (sourceSubsystem q hq40 hq).dual.complex
    (balancingBoundary q hq40 hq) hDual
    (lpsQuotientBoundary_row_weight_le q hq40 hq)
    (fun c => (lpsQuotientBoundary_column_weight_le q hq40 hq c).trans
      (by norm_num))
  exact hProduct

theorem balancedSubsystem_sourceValid
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1) :
    ((balancedSubsystem q hq40 hq).complex.binaryCSSCode).stabilizer.IsSourceValidBinary :=
  ChainComplexData.binaryCSSCode_stabilizer_isSourceValidBinary
    (balancedSubsystem q hq40 hq).complex

/-- Exact finite meaning of the distance-balanced BE20 parameter theorem.
The sole non-construction premise in the proving theorem below is the
graph-only LPS Rayleigh bound. -/
def BalancedFamilyCertificate
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1) : Prop :=
  let D := balancedSubsystem q hq40 hq
  let N := Fintype.card (BalancedQubitIndex q hq)
  let K := D.logicalQubits
  let dX := lpsDressedZLowerBound q hq
  let dZ := (Fintype.card (EdgeOrbit401 q hq) / 10000000) *
    lpsDressedXLowerBound q
  (D.complex.binaryCSSCode).stabilizer.IsSourceValidBinary ∧
    D.DressedXDistanceAtLeast dX ∧
    D.DressedZDistanceAtLeast dZ ∧
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence D.complex).localityProfile 806 ∧
    N = blocklengthCoefficient * q * (q ^ 2 - 1) ^ 2 ∧
    (q ^ 2 - 1) ^ 2 ≤ K ∧
    K ≤ (201 * (q ^ 2 - 1)) ^ 2 ∧
    N ^ 4 ≤ dimensionLowerCoefficient * K ^ 5 ∧
    K ^ 5 ≤ dimensionUpperCoefficient * N ^ 4 ∧
    N ^ 3 ≤ dressedXPowerCoefficient * dX ^ 5 ∧
    N ^ 3 ≤ dressedZPowerCoefficient * dZ ^ 5

/-- Every sufficiently large admissible prime produces a distance-balanced
BE20 qLDPC subsystem code with `K = Θ(N^(4/5))` and both dressed distances
`Ω(N^(3/5))`. -/
theorem balancedFamilyCertificate_of_rayleigh
    (q : Nat) [Fact q.Prime]
    (hqLarge : BE20Unbalanced.familyThreshold ≤ q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq) :
    BalancedFamilyCertificate q (by
      dsimp [BE20Unbalanced.familyThreshold] at hqLarge
      omega) hq := by
  classical
  have hq40 : 40 < q := by
    dsimp [BE20Unbalanced.familyThreshold] at hqLarge
    omega
  have hq804 : 804 ≤ q := by
    dsimp [BE20Unbalanced.familyThreshold] at hqLarge
    omega
  have hScales := BE20Unbalanced.quotientScales_large
    q hq40 hqLarge hq
  let D := balancedSubsystem q hq40 hq
  let N := Fintype.card (BalancedQubitIndex q hq)
  let K := D.logicalQubits
  let dX := lpsDressedZLowerBound q hq
  let dZ := (Fintype.card (EdgeOrbit401 q hq) / 10000000) *
    lpsDressedXLowerBound q
  have hN : N = blocklengthCoefficient * q * (q ^ 2 - 1) ^ 2 :=
    card_balancedQubitIndex q hq40 hq
  have hK := balancedSubsystem_logicalQubits_bounds q hq40 hq
  have hDimension := dimension_power_bounds q N K hq40 hN hK.1 hK.2
  have hDistancePower := balanced_distance_power_bounds
    q hq40 hqLarge hq hScales.1
  have hDistances := balancedSubsystem_dressedDistanceBounds
    q hq40 hq804 hq hLPS hScales.1 hScales.2
  unfold BalancedFamilyCertificate
  dsimp only
  exact ⟨balancedSubsystem_sourceValid q hq40 hq,
    hDistances.1, hDistances.2,
    balancedSubsystem_boundedLocality q hq40 hq,
    hN, hK.1, hK.2, hDimension.1, hDimension.2,
    hDistancePower.1, hDistancePower.2⟩

/-- Construction-indexed unbounded balanced family.  The LPS premise is
uniform and graph-only; the prime, code, quotient Tanner factor, and all
finite witnesses are selected internally. -/
theorem exists_be20_balanced_family_at
    (hLPS : LPS401FamilyRayleighBound) (B : Nat) :
    ∃ a : AdmissiblePrime401,
      max B BE20Unbalanced.familyThreshold < a.q ∧
      BalancedFamilyCertificate a.q a.gt40 a.legendre := by
  obtain ⟨a, ha⟩ := LPSFamily.exists_admissiblePrime401_gt
    (max B BE20Unbalanced.familyThreshold)
  have hLarge : BE20Unbalanced.familyThreshold ≤ a.q :=
    (Nat.le_max_right B BE20Unbalanced.familyThreshold).trans ha.le
  refine ⟨a, ha, ?_⟩
  exact balancedFamilyCertificate_of_rayleigh a.q hLarge a.legendre
    (hLPS a.q a.prime a.gt40 a.legendre)

/-- Public conditional endpoint for the registered BE20 family result. -/
theorem breuckmannEberhardtBalancedProductQLDPCFamilies
    (hLPS : LPS401FamilyRayleighBound) :
    (∀ B : Nat, ∃ a : AdmissiblePrime401,
      max B BE20Unbalanced.familyThreshold < a.q ∧
      BE20Unbalanced.UnbalancedFamilyCertificate
        a.q a.gt40 a.legendre) ∧
    (∀ B : Nat, ∃ a : AdmissiblePrime401,
      max B BE20Unbalanced.familyThreshold < a.q ∧
      BalancedFamilyCertificate a.q a.gt40 a.legendre) :=
  ⟨BE20Unbalanced.exists_be20_unbalanced_family_at hLPS,
    exists_be20_balanced_family_at hLPS⟩

end QEC.Coding.BalancedProduct.BE20Balanced
