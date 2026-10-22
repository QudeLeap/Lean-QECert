import QEC.Coding.ExpanderCodes.ClassicalFactor
import QEC.Coding.ExpanderCodes.TwoStepBalancing

/-!
# PK20 two-product tradeoff family

This file joins one almost-linear lifted-product member with one classical
factor extracted from another output of PK20 Proposition 1.  The same
classical boundary is used in both EKZ products.  Thus the only external
input to the complete PK20 Theorems 1--2 closure remains Proposition 1.
-/

namespace QEC.Coding.ExpanderCodes.PK20

open QEC.Coding
open QEC.Coding.BalancedProduct

abbrev InitialC0 (q n m w : Nat) :=
  LiftedProduct.C0Index (Fin m) Unit (Cyclic.CyclicGroup q)

abbrev InitialQubit (q n m w : Nat) :=
  LiftedProduct.QubitIndex (Fin m) (Fin (w * n)) Unit Unit
    (Cyclic.CyclicGroup q)

abbrev InitialC2 (q n m w : Nat) :=
  LiftedProduct.C2Index (Fin (w * n)) Unit (Cyclic.CyclicGroup q)

abbrev FactorBit (r nc w : Nat) :=
  Fin (w * nc) × Cyclic.CyclicGroup r

abbrev FactorRawCheck (r mc : Nat) :=
  Fin mc × Cyclic.CyclicGroup r

abbrev FactorCheck
    (r nc mc w : Nat) [NeZero r]
    (C : Matrix (Fin mc) (Fin (w * nc))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup r))) :=
  ClassicalRowReduction.ReducedCheck (PKDistance.tannerAction C)

noncomputable def tradeoffComplex
    (q n m r nc mc w : Nat) [NeZero q] [NeZero r]
    (A : Matrix (Fin m) (Fin (w * n))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (C : Matrix (Fin mc) (Fin (w * nc))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup r))) :=
  twiceBalancedComplex
    (LiftedProduct.chainComplex (Cyclic.data q A))
    (ClassicalRowReduction.reducedBoundary (PKDistance.tannerAction C))
    (ClassicalRowReduction.reducedBoundary (PKDistance.tannerAction C))

/-- The exact finite two-product conclusion.  The blocklength identity is
that of the actual truncated homological products; `K` and both CSS distance
sectors are stated for the final complex itself. -/
def TradeoffMember
    (q n m r nc mc w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat)
    [NeZero q] [NeZero r]
    (A : Matrix (Fin m) (Fin (w * n))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (C : Matrix (Fin mc) (Fin (w * nc))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup r))) : Prop :=
  let X := LiftedProduct.chainComplex (Cyclic.data q A)
  let Y := ClassicalRowReduction.reducedBoundary (PKDistance.tannerAction C)
  let sourceK := w * n - m
  let classicalK :=
    Fintype.card (FactorBit r nc w) - Fintype.card (FactorRawCheck r mc)
  let sourceD := certifiedDistanceLowerBound q w radiusDenominator
    expansionNumerator expansionDenominator
  let classicalD := classicalDistanceLowerBound
    (Fintype.card (FactorBit r nc w))
    radiusNumerator radiusDenominator
  let Q := tradeoffComplex q n m r nc mc w A C
  ((Q.binaryCSSCode).stabilizer.IsSourceValidBinary) ∧
    Fintype.card
      (SecondQubit
          (xZero := InitialC0 q n m w)
          (xOne := InitialQubit q n m w)
          (xTwo := InitialC2 q n m w)
          (bitOne := FactorBit r nc w)
          (checkOne := FactorCheck r nc mc w C)
          (bitTwo := FactorBit r nc w)
          (checkTwo := FactorCheck r nc mc w C)) =
      (Fintype.card (InitialQubit q n m w) *
          Fintype.card (FactorBit r nc w) +
        Fintype.card (InitialC2 q n m w) *
          Fintype.card (FactorCheck r nc mc w C)) *
          Fintype.card (FactorBit r nc w) +
      (Fintype.card (InitialC0 q n m w) *
          Fintype.card (FactorBit r nc w) +
        Fintype.card (InitialQubit q n m w) *
          Fintype.card (FactorCheck r nc mc w C)) *
          Fintype.card (FactorCheck r nc mc w C) ∧
    sourceK * classicalK * classicalK ≤
      Module.finrank (ZMod 2) Q.middleHomology ∧
    MiddleHomologyDistanceAtLeast Q (classicalD * sourceD) ∧
    MiddleCohomologyDistanceAtLeast Q (classicalD * sourceD) ∧
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence Q).localityProfile (3 * w + 2)

/-- The actual final blocklength is at most four times the initial blocklength
times the square of the number of classical bits.  This is the finite
inequality used in PK20's exponent calculation. -/
theorem tradeoff_blockLength_le
    (q n m r nc mc w : Nat) [NeZero q] [NeZero r]
    (A : Matrix (Fin m) (Fin (w * n))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (C : Matrix (Fin mc) (Fin (w * nc))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup r)))
    (hChecks : mc ≤ w * nc) :
    Fintype.card
        (SecondQubit
          (xZero := InitialC0 q n m w)
          (xOne := InitialQubit q n m w)
          (xTwo := InitialC2 q n m w)
          (bitOne := FactorBit r nc w)
          (checkOne := FactorCheck r nc mc w C)
          (bitTwo := FactorBit r nc w)
          (checkTwo := FactorCheck r nc mc w C)) ≤
      4 * blockLength q A * Fintype.card (FactorBit r nc w) ^ 2 := by
  have hReduced : Fintype.card (FactorCheck r nc mc w C) ≤
      Fintype.card (FactorRawCheck r mc) :=
    ClassicalRowReduction.card_reducedCheck_le (PKDistance.tannerAction C)
  have hRaw : Fintype.card (FactorRawCheck r mc) ≤
      Fintype.card (FactorBit r nc w) := by
    simp only [FactorRawCheck, FactorBit, Fintype.card_prod,
      Fintype.card_fin]
    exact Nat.mul_le_mul_right
      (Fintype.card (Cyclic.CyclicGroup r)) hChecks
  have hCheckBit : Fintype.card (FactorCheck r nc mc w C) ≤
      Fintype.card (FactorBit r nc w) := hReduced.trans hRaw
  have hC0 : Fintype.card (InitialC0 q n m w) ≤ blockLength q A := by
    simp [InitialC0, blockLength, LiftedProduct.C0Index,
      LiftedProduct.QubitIndex, Cyclic.CyclicGroup, ZMod.card]
  have hC1 : Fintype.card (InitialQubit q n m w) = blockLength q A := rfl
  have hC2 : Fintype.card (InitialC2 q n m w) ≤ blockLength q A := by
    simp [InitialC2, blockLength, LiftedProduct.C2Index,
      LiftedProduct.QubitIndex, Cyclic.CyclicGroup, ZMod.card]
  rw [card_twiceBalanced_qubits
    (LiftedProduct.chainComplex (Cyclic.data q A))
    (ClassicalRowReduction.reducedBoundary (PKDistance.tannerAction C))
    (ClassicalRowReduction.reducedBoundary (PKDistance.tannerAction C))]
  rw [hC1]
  calc
    (blockLength q A * Fintype.card (FactorBit r nc w) +
        Fintype.card (InitialC2 q n m w) *
          Fintype.card (FactorCheck r nc mc w C)) *
          Fintype.card (FactorBit r nc w) +
      (Fintype.card (InitialC0 q n m w) * Fintype.card (FactorBit r nc w) +
        blockLength q A * Fintype.card (FactorCheck r nc mc w C)) *
          Fintype.card (FactorCheck r nc mc w C) ≤
      (blockLength q A * Fintype.card (FactorBit r nc w) +
        blockLength q A * Fintype.card (FactorBit r nc w)) *
          Fintype.card (FactorBit r nc w) +
      (blockLength q A * Fintype.card (FactorBit r nc w) +
        blockLength q A * Fintype.card (FactorBit r nc w)) *
          Fintype.card (FactorBit r nc w) := by gcongr
    _ = 4 * blockLength q A * Fintype.card (FactorBit r nc w) ^ 2 := by ring

/-- Finite PK20 Theorem 2 construction from two literal outputs of the sole
Proposition 1 premise. -/
theorem tradeoffMember_of_propositionOne_outputs
    (q n m r nc mc w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat)
    [NeZero q] [NeZero r]
    (A : Matrix (Fin m) (Fin (w * n))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (C : Matrix (Fin mc) (Fin (w * nc))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup r)))
    (hInitial : FirstFamilyMember w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator q n m A)
    (hExpansionNumerator : 0 < expansionNumerator)
    (hFactorForwardWeight : ∀ i : FactorBit r nc w,
      HammingWeight (PKDistance.tannerAction C (Pi.single i 1)) ≤ w)
    (hFactorTransposeWeight : ∀ i : FactorRawCheck r mc,
      HammingWeight
        (PKDistance.tannerAction (LiftedProduct.starTranspose C)
          (Pi.single i 1)) ≤ w)
    (hFactorExpansion :
      (PKDistance.tannerAction C).SmallSetExpandingAtRelativeRadius
        radiusNumerator radiusDenominator
        expansionNumerator expansionDenominator) :
    TradeoffMember q n m r nc mc w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator A C := by
  let X := LiftedProduct.chainComplex (Cyclic.data q A)
  let Y := ClassicalRowReduction.reducedBoundary (PKDistance.tannerAction C)
  let sourceK := w * n - m
  let classicalK :=
    Fintype.card (FactorBit r nc w) - Fintype.card (FactorRawCheck r mc)
  let sourceD := certifiedDistanceLowerBound q w radiusDenominator
    expansionNumerator expansionDenominator
  let classicalD := classicalDistanceLowerBound
    (Fintype.card (FactorBit r nc w))
    radiusNumerator radiusDenominator
  have hClassical := classicalFactorCertificate_of_propositionOne_output
    r C w radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator hExpansionNumerator
      hFactorForwardWeight hFactorTransposeWeight hFactorExpansion
  have hFinite := twiceBalancedMemberCertificate X Y Y
    (sourceDimension := sourceK)
    (classicalDimensionOne := classicalK)
    (classicalDimensionTwo := classicalK)
    (sourceDistance := sourceD)
    (classicalDistanceOne := classicalD)
    (classicalDistanceTwo := classicalD)
    (sourceLocality := w + 2)
    (classicalLocalityOne := w)
    (classicalLocalityTwo := w)
    hInitial.2.2.2.2.2.1 hClassical.2.2.1 hClassical.2.2.1
    hClassical.1 hClassical.1
    hInitial.2.2.2.2.2.2.2.2.2.1
    hInitial.2.2.2.2.2.2.2.2.2.2.1
    hClassical.2.1 hClassical.2.1
    hInitial.2.2.2.2.2.2.2.2.1
    hClassical.2.2.2.1 hClassical.2.2.2.2
    hClassical.2.2.2.1 hClassical.2.2.2.2
  rcases hFinite with
    ⟨hValid, hCard, hDimension, hHomology, hCohomology, hLocality⟩
  dsimp only [TradeoffMember]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [tradeoffComplex, X, Y] using hValid
  · exact hCard
  · change (w * n - m) *
        (Fintype.card (FactorBit r nc w) - Fintype.card (FactorRawCheck r mc)) *
        (Fintype.card (FactorBit r nc w) - Fintype.card (FactorRawCheck r mc)) ≤
      Module.finrank (ZMod 2) (twiceBalancedComplex X Y Y).middleHomology
    simpa [sourceK, classicalK, Nat.mul_assoc] using hDimension
  · simpa [tradeoffComplex, X, Y, sourceD, classicalD] using hHomology
  · simpa [tradeoffComplex, X, Y, sourceD, classicalD] using hCohomology
  · have hLocality' : BoundedLocality
        (QEC.QLDPC.chainComplexBoundaryIncidence
          (tradeoffComplex q n m r nc mc w A C)).localityProfile
        (w + 2 + w + w) := by
      simpa [tradeoffComplex, X, Y] using hLocality
    convert hLocality' using 1 <;> omega

/-! ## Source-exact selection of the balancing scale -/

/-- PK20's exponent for the length of either classical balancing factor. -/
noncomputable def balancingExponent (alpha : ℝ) : ℝ :=
  alpha / (2 * (1 - alpha))

/-- An integral lift at the required real-power scale.  The maximum with two
only removes the finite prefix where Proposition 1 has no matrix output. -/
noncomputable def balancingLift (alpha : ℝ) (q : Nat) : Nat :=
  max 2 (Nat.ceil ((q : ℝ) ^ balancingExponent alpha))

theorem balancingLift_gt_one (alpha : ℝ) (q : Nat) :
    1 < balancingLift alpha q := by
  unfold balancingLift
  omega

theorem rpow_le_balancingLift (alpha : ℝ) (q : Nat) :
    (q : ℝ) ^ balancingExponent alpha ≤ balancingLift alpha q := by
  calc
    (q : ℝ) ^ balancingExponent alpha ≤
        (Nat.ceil ((q : ℝ) ^ balancingExponent alpha) : Nat) :=
      Nat.le_ceil _
    _ ≤ balancingLift alpha q := by
      exact_mod_cast Nat.le_max_right 2
        (Nat.ceil ((q : ℝ) ^ balancingExponent alpha))

/-- The exact construction-scale family underlying PK20 Theorem 2.  It
records the real exponent used to choose each classical factor and retains
all actual finite code conclusions through `TradeoffMember`. -/
def TwoProductConstructionFamily : Prop :=
  ∃ (w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat),
    4 ≤ w ∧
    0 < gamma ∧
    0 < radiusNumerator ∧
    0 < radiusDenominator ∧
    0 < expansionNumerator ∧
    0 < expansionDenominator ∧
    ∀ alpha : ℝ, 0 ≤ alpha → alpha < 1 → ∀ B : Nat,
      ∃ (q n m r nc mc : Nat) (_hq : NeZero q) (_hr : NeZero r)
        (A : Matrix (Fin m) (Fin (w * n))
          (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
        (C : Matrix (Fin mc) (Fin (w * nc))
          (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup r))),
        B < q ∧
        r = balancingLift alpha q ∧
        (q : ℝ) ^ balancingExponent alpha ≤ r ∧
        gamma * Nat.log 2 r ≤ nc ∧
        nc ≤ gamma * (Nat.log 2 r + 1) ∧
        TradeoffMember q n m r nc mc w gamma radiusNumerator
          radiusDenominator expansionNumerator expansionDenominator A C ∧
        Fintype.card
            (SecondQubit
              (xZero := InitialC0 q n m w)
              (xOne := InitialQubit q n m w)
              (xTwo := InitialC2 q n m w)
              (bitOne := FactorBit r nc w)
              (checkOne := FactorCheck r nc mc w C)
              (bitTwo := FactorBit r nc w)
              (checkTwo := FactorCheck r nc mc w C)) ≤
          4 * blockLength q A * Fintype.card (FactorBit r nc w) ^ 2

/-- Proposition 1 constructs every finite member in the two-product family;
there is no independent assumption of asymptotically good classical codes. -/
theorem twoProductConstructionFamily_of_propositionOne
    (hPropositionOne : PropositionOneExpandingMatrixFamily) :
    TwoProductConstructionFamily := by
  rcases hPropositionOne with
    ⟨w, gamma, radiusNumerator, radiusDenominator,
      expansionNumerator, expansionDenominator,
      hw4, hgamma, hRadiusNumerator, hRadiusDenominator,
      hExpansionNumerator, hExpansionDenominator, hMatrices⟩
  refine ⟨w, gamma, radiusNumerator, radiusDenominator,
    expansionNumerator, expansionDenominator,
    hw4, hgamma, hRadiusNumerator, hRadiusDenominator,
    hExpansionNumerator, hExpansionDenominator, ?_⟩
  intro alpha hAlphaNonnegative hAlphaOne B
  let q := familyLift w radiusDenominator B
  have hqOdd : Odd q := familyLift_odd w radiusDenominator B
  have hqTwo : 1 < q := by
    unfold q familyLift
    have hPowPositive : 0 < 2 ^ radiusDenominator := pow_pos (by norm_num) _
    omega
  letI : NeZero q := ⟨by omega⟩
  obtain ⟨n, m, A, hm, hnLower, hnUpper,
      hForwardWeight, hTransposeWeight,
      hForwardRelative, hTransposeRelative⟩ := hMatrices q hqTwo
  have hDenominatorLog : radiusDenominator ≤ Nat.log 2 q := by
    apply Nat.le_log_of_pow_le (by norm_num)
    exact two_pow_radiusDenominator_le_familyLift w radiusDenominator B
  have hDenominatorLeN : radiusDenominator ≤ n := by
    calc
      radiusDenominator ≤ Nat.log 2 q := hDenominatorLog
      _ ≤ gamma * Nat.log 2 q := Nat.le_mul_of_pos_left _ hgamma
      _ ≤ n := hnLower
  have hLiftLarge : 2 * w * radiusDenominator ≤ q :=
    liftScale_le_familyLift w radiusDenominator B
  have hInitial := firstFamilyMember_of_propositionOne_output
    w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator q n m A
    hw4 hgamma hRadiusNumerator hRadiusDenominator
      hExpansionNumerator hExpansionDenominator hqOdd hm hnLower hnUpper
      hDenominatorLeN hLiftLarge hForwardWeight hTransposeWeight
      hForwardRelative hTransposeRelative
  let r := balancingLift alpha q
  have hrTwo : 1 < r := balancingLift_gt_one alpha q
  letI : NeZero r := ⟨by omega⟩
  obtain ⟨nc, mc, C, hmc, hncLower, hncUpper,
      hFactorForwardWeight, hFactorTransposeWeight,
      hFactorForwardRelative, _hFactorTransposeRelative⟩ := hMatrices r hrTwo
  have hTradeoff := tradeoffMember_of_propositionOne_outputs
    q n m r nc mc w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator A C hInitial
      hExpansionNumerator hFactorForwardWeight hFactorTransposeWeight
      hFactorForwardRelative
  have hChecks : mc ≤ w * nc := by
    rw [hmc]
    have : 2 * (w / 4) ≤ w := by omega
    nlinarith
  have hBlocklength := tradeoff_blockLength_le q n m r nc mc w A C hChecks
  exact ⟨q, n, m, r, nc, mc, inferInstance, inferInstance, A, C,
    familyLift_gt w radiusDenominator B, rfl,
    rpow_le_balancingLift alpha q,
    hncLower, hncUpper, hTradeoff, hBlocklength⟩

end QEC.Coding.ExpanderCodes.PK20
