import QEC.Coding.CodeReduction.DistanceBalancing.Core
import QEC.Coding.FiberBundle.WeightReductionParameters

/-!
# Construction-owned classical LDPC codes for HHO20 distance balancing

The EKZ20 product needs a surjective classical boundary with linear distance
and bounded row and column weight.  This module obtains that boundary from the
same assumption-free HHO20 random-base witnesses, followed by the already
verified classical weight-reduction construction.  In particular, callers do
not supply a matrix, a rank certificate, or a distance assumption.
-/

namespace QEC.Coding.FiberBundle.RandomBase

open QEC.Coding

universe u v w

/-- The relation-defined original Tanner boundary is exactly the sampled
binary boundary matrix, not an externally supplied representation. -/
theorem originalBoundary_incidenceRelation_eq
    {r : Nat} (sample : Sample r) :
    ClassicalWeightReduction.originalBoundary (F := ZMod 2)
        (incidenceRelation sample) =
      Matrix.toLin' (boundary sample) := by
  apply LinearMap.ext
  intro x
  ext a
  simp [ClassicalWeightReduction.originalBoundary,
    ClassicalWeightReduction.linearMapOfBasisImages,
    ClassicalWeightReduction.originalBasisBoundary,
    incidenceRelation, boundary, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct]
  apply Finset.sum_congr rfl
  intro c _hc
  by_cases hentry : sample (a, c) = true
  · erw [if_pos hentry, if_pos hentry] <;> simp only [mul_one]
  · erw [if_neg hentry, if_neg hentry] <;> simp only [mul_zero]

/-- Surjectivity of the degree-one boundary is invariant in the direction
needed here under a three-term chain-homotopy equivalence. -/
theorem boundary1_surjective_of_homotopyEquiv
    {F : Type u} {AZero AOne ATwo : Type v}
    {BZero BOne BTwo : Type w}
    [Field F]
    [AddCommGroup AZero] [Module F AZero]
    [AddCommGroup AOne] [Module F AOne]
    [AddCommGroup ATwo] [Module F ATwo]
    [AddCommGroup BZero] [Module F BZero]
    [AddCommGroup BOne] [Module F BOne]
    [AddCommGroup BTwo] [Module F BTwo]
    {A : ChainComplexData F AZero AOne ATwo}
    {B : ChainComplexData F BZero BOne BTwo}
    (e : ThreeTermChainHomotopyEquiv A B)
    (hB : Function.Surjective B.boundary1) :
    Function.Surjective A.boundary1 := by
  intro y
  obtain ⟨x, hx⟩ := hB (e.forward.map0 y)
  refine ⟨e.inverse.map1 x - e.inverse_forward.homotopy0 y, ?_⟩
  have hComm := LinearMap.congr_fun e.inverse.commutes_boundary1 x
  have hHomotopy := LinearMap.congr_fun e.inverse_forward.degree0 y
  simp only [LinearMap.comp_apply] at hComm
  simp only [ThreeTermChainMap.comp_map0, ThreeTermChainMap.id_map0,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply] at hHomotopy
  rw [map_sub, hComm, hx, ← hHomotopy]
  abel

/-- Full row rank of the sampled Tanner matrix therefore implies
surjectivity of its internally weight-reduced boundary. -/
theorem weightReducedBoundary_surjective
    {r Delta : Nat} (sample : Sample r)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    Function.Surjective
      (ClassicalWeightReduction.boundary (F := ZMod 2)
        (incidenceRelation sample)) := by
  let hNoIsolated :=
    hasNoIsolatedVertices_of_isFullyGood sample hDelta hGood
  let e :=
    ClassicalWeightReduction.classicalWeightReductionHomotopyEquiv
      (F₀ := ZMod 2) (incidenceRelation sample) hNoIsolated
  apply boundary1_surjective_of_homotopyEquiv e
  change Function.Surjective
    (ClassicalWeightReduction.originalBoundary (F := ZMod 2)
      (incidenceRelation sample))
  rw [originalBoundary_incidenceRelation_eq]
  exact hGood.1.2.1

/-- The original Tanner complex inherits the explicit `4r/5` distance from
the fully-good random-base event. -/
theorem originalComplex_middleHomologyDistanceAtLeast
    {r Delta : Nat} (sample : Sample r)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    MiddleHomologyDistanceAtLeast
      (ClassicalWeightReduction.originalComplex (F₀ := ZMod 2)
        (incidenceRelation sample))
      ((4 * r) / 5) := by
  intro x hxCycle hxNontrivial
  have hxKernel : Matrix.toLin' (boundary sample) x = 0 := by
    rw [← originalBoundary_incidenceRelation_eq]
    exact ((ClassicalWeightReduction.originalComplex
      (F₀ := ZMod 2) (incidenceRelation sample)).mem_middleCycleCode_iff x).mp
        hxCycle
  have hxCode : x ∈ (code sample).carrier := by
    rw [code, mem_parityCheckKernelCode]
    exact hxKernel
  have hxNe : x ≠ 0 := by
    intro hxZero
    subst x
    exact hxNontrivial (by simp)
  have hDistance := hGood.1.2.2 x hxCode hxNe
  exact Nat.div_le_of_le_mul (by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hDistance)

/-- The original sampled Tanner complex has exactly the advertised `r`
logical dimensions. -/
theorem finrank_originalComplex_middleHomology_eq
    {r Delta : Nat} (sample : Sample r)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    Module.finrank (ZMod 2)
        (ClassicalWeightReduction.originalComplex (F₀ := ZMod 2)
          (incidenceRelation sample)).middleHomology = r := by
  let K := ClassicalWeightReduction.originalComplex (F₀ := ZMod 2)
    (incidenceRelation sample)
  change Module.finrank (ZMod 2) K.middleHomology = r
  rw [K.finrank_middleHomology_eq]
  have hCycle : Dimension K.middleCycleCode = Dimension (code sample) := by
    rw [Dimension_eq_finrank_carrier, Dimension_eq_finrank_carrier]
    have hCarrier : K.middleCycleCode.carrier = (code sample).carrier := by
      ext x
      rw [K.mem_middleCycleCode_iff]
      change K.boundary1 x = 0 ↔ Matrix.toLin' (boundary sample) x = 0
      simp [K, ClassicalWeightReduction.originalComplex,
        originalBoundary_incidenceRelation_eq sample]
    rw [hCarrier]
  have hBoundary : Dimension K.middleBoundaryCode = 0 := by
    rw [Dimension_eq_finrank_carrier]
    have hCarrier : K.middleBoundaryCode.carrier = ⊥ := by
      ext x
      rw [K.mem_middleBoundaryCode_iff]
      simp [K, ClassicalWeightReduction.originalComplex, eq_comm]
    rw [hCarrier, finrank_bot]
  rw [hCycle, hBoundary, Nat.sub_zero]
  exact dimension_code_eq sample hGood.1.2.1

/-- Classical weight reduction preserves the exact logical dimension. -/
theorem finrank_weightReducedComplex_middleHomology_eq
    {r Delta : Nat} (sample : Sample r)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    Module.finrank (ZMod 2)
        (ClassicalWeightReduction.weightReducedComplex (F₀ := ZMod 2)
          (incidenceRelation sample)).middleHomology = r := by
  let hNoIsolated :=
    hasNoIsolatedVertices_of_isFullyGood sample hDelta hGood
  let e :=
    ClassicalWeightReduction.classicalWeightReductionHomotopyEquiv
      (F₀ := ZMod 2) (incidenceRelation sample) hNoIsolated
  calc
    Module.finrank (ZMod 2)
        (ClassicalWeightReduction.weightReducedComplex (F₀ := ZMod 2)
          (incidenceRelation sample)).middleHomology =
      Module.finrank (ZMod 2)
        (ClassicalWeightReduction.originalComplex (F₀ := ZMod 2)
          (incidenceRelation sample)).middleHomology :=
      e.finrank_middleHomology_eq
    _ = r := finrank_originalComplex_middleHomology_eq sample hGood

/-- The internally extracted classical parity-check matrix has kernel
dimension exactly `r`; no rank certificate is supplied by a caller. -/
theorem finrank_weightReducedClassicalKernel_eq
    {r Delta : Nat} (sample : Sample r)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    Module.finrank (ZMod 2)
        (LinearMap.ker (Matrix.toLin'
          (LinearMap.toMatrix'
            (ClassicalWeightReduction.boundary (F := ZMod 2)
              (incidenceRelation sample))))) = r := by
  rw [Matrix.toLin'_toMatrix']
  let K := ClassicalWeightReduction.weightReducedComplex (F₀ := ZMod 2)
    (incidenceRelation sample)
  have hHomology :=
    finrank_weightReducedComplex_middleHomology_eq sample hDelta hGood
  change Module.finrank (ZMod 2) (LinearMap.ker K.boundary1) = r
  rw [K.finrank_middleHomology_eq] at hHomology
  have hCycle :
      Dimension K.middleCycleCode =
        Module.finrank (ZMod 2) (LinearMap.ker K.boundary1) := by
    rw [Dimension_eq_finrank_carrier]
    rfl
  have hBoundary : Dimension K.middleBoundaryCode = 0 := by
    rw [Dimension_eq_finrank_carrier]
    have hCarrier : K.middleBoundaryCode.carrier = ⊥ := by
      ext x
      rw [K.mem_middleBoundaryCode_iff]
      simp [K, ClassicalWeightReduction.weightReducedComplex, eq_comm]
    rw [hCarrier, finrank_bot]
  rw [hCycle, hBoundary, Nat.sub_zero] at hHomology
  exact hHomology

/-- Classical weight reduction preserves the random-base homological
distance because its forward middle map is one-Lipschitz. -/
theorem weightReducedComplex_middleHomologyDistanceAtLeast
    {r Delta : Nat} (sample : Sample r)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    MiddleHomologyDistanceAtLeast
      (ClassicalWeightReduction.weightReducedComplex (F₀ := ZMod 2)
        (incidenceRelation sample))
      ((4 * r) / 5) := by
  let hNoIsolated :=
    hasNoIsolatedVertices_of_isFullyGood sample hDelta hGood
  let e :=
    ClassicalWeightReduction.classicalWeightReductionHomotopyEquiv
      (F₀ := ZMod 2) (incidenceRelation sample) hNoIsolated
  simpa using
    e.middleHomologyDistanceAtLeast_of_forward_lipschitz (L := 1)
      (originalComplex_middleHomologyDistanceAtLeast sample hGood)
      (by
        intro x
        rw [Nat.one_mul]
        exact ClassicalWeightReduction.classicalWeightReductionForward_map1_lipschitz
          (F := ZMod 2) (incidenceRelation sample) hNoIsolated x)

/-- The matrix extracted from the weight-reduced boundary has the classical
distance required by the EKZ product. -/
theorem weightReducedClassicalDistanceAtLeast
    {r Delta : Nat} (sample : Sample r)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    DistanceBalancing.ClassicalDistanceAtLeast
      (LinearMap.toMatrix'
        (ClassicalWeightReduction.boundary (F := ZMod 2)
          (incidenceRelation sample)))
      ((4 * r) / 5) := by
  intro w hw hne
  apply weightReducedComplex_middleHomologyDistanceAtLeast
    sample hDelta hGood w
  · rw [(ClassicalWeightReduction.weightReducedComplex
      (F₀ := ZMod 2) (incidenceRelation sample)).mem_middleCycleCode_iff]
    rw [Matrix.toLin'_toMatrix'] at hw
    exact hw
  · intro hBoundary
    rcases ((ClassicalWeightReduction.weightReducedComplex
      (F₀ := ZMod 2) (incidenceRelation sample)).mem_middleBoundaryCode_iff
        w).mp hBoundary with ⟨z, hz⟩
    have hzZero : z = 0 := by
      ext i
      exact Fin.elim0 i
    subst z
    simp only [ClassicalWeightReduction.weightReducedComplex,
      LinearMap.zero_apply] at hz
    exact hne hz.symm

/-- Every row of the extracted balancing matrix has weight at most three. -/
theorem weightReducedClassical_rowWeight_le_three
    {r : Nat} (sample : Sample r)
    (q : ClassicalWeightReduction.WeightReducedCheck
      (incidenceRelation sample)) :
    HammingWeight
      (wordLinearMapTranspose
        (ClassicalWeightReduction.boundary (F := ZMod 2)
          (incidenceRelation sample))
        (Pi.single q 1)) ≤ 3 :=
  ClassicalWeightReduction.HammingWeight_transpose_boundary_single_le_three
    (F := ZMod 2) (incidenceRelation sample) q

/-- Every column of the extracted balancing matrix has weight at most three. -/
theorem weightReducedClassical_columnWeight_le_three
    {r : Nat} (sample : Sample r)
    (b : ClassicalWeightReduction.WeightReducedBit
      (incidenceRelation sample)) :
    HammingWeight
      (ClassicalWeightReduction.boundary (F := ZMod 2)
        (incidenceRelation sample) (Pi.single b 1)) ≤ 3 :=
  ClassicalWeightReduction.HammingWeight_boundary_single_le_three
    (F := ZMod 2) (incidenceRelation sample) b

/-- Direct incidence count for an arbitrary Tanner relation. -/
theorem card_incidence_eq_sum_bitNeighbor
    {Check Bit : Type*} [Fintype Check] [DecidableEq Check]
    [Fintype Bit] [DecidableEq Bit]
    (R : Check → Bit → Prop) [DecidableRel R] :
    Fintype.card (ClassicalWeightReduction.Incidence R) =
      ∑ b : Bit,
        Fintype.card (ClassicalWeightReduction.BitNeighbor R b) := by
  let e : ClassicalWeightReduction.Incidence R ≃
      ClassicalWeightReduction.BitPositionSigma R :=
    { toFun := ClassicalWeightReduction.incidenceBitPosition R
      invFun := ClassicalWeightReduction.incidenceAtBitPosition R
      left_inv :=
        ClassicalWeightReduction.incidenceAtBitPosition_incidenceBitPosition R
      right_inv := by
        rintro ⟨b, i⟩
        change ClassicalWeightReduction.incidenceBitPosition R
            (ClassicalWeightReduction.bitIncidenceAt R b i) = ⟨b, i⟩
        unfold ClassicalWeightReduction.incidenceBitPosition
        apply Sigma.ext (show
          (ClassicalWeightReduction.bitIncidenceAt R b i).1.2 = b by rfl)
        simp
        exact HEq.rfl }
  rw [Fintype.card_congr e]
  simp [ClassicalWeightReduction.BitPositionSigma]

/-- Both sides of classical weight reduction contain at most two copies of
the original incidence set. -/
theorem card_weightReducedClassicalSides_le_two_mul_incidence
    {Check Bit : Type*} [Fintype Check] [DecidableEq Check]
    [Fintype Bit] [DecidableEq Bit]
    (R : Check → Bit → Prop) [DecidableRel R] :
    Fintype.card (ClassicalWeightReduction.WeightReducedBit R) ≤
        2 * Fintype.card (ClassicalWeightReduction.Incidence R) ∧
      Fintype.card (ClassicalWeightReduction.WeightReducedCheck R) ≤
        2 * Fintype.card (ClassicalWeightReduction.Incidence R) := by
  have hAuxCheck :
      Fintype.card (ClassicalWeightReduction.AuxiliaryCheck R) ≤
        Fintype.card (ClassicalWeightReduction.Incidence R) := by
    rw [card_incidence_eq_sum_bitNeighbor R]
    simp only [ClassicalWeightReduction.AuxiliaryCheck,
      Fintype.card_sigma, Fintype.card_fin]
    apply Finset.sum_le_sum
    intro b _
    omega
  have hAuxBit :
      Fintype.card (ClassicalWeightReduction.AuxiliaryBit R) ≤
        Fintype.card (ClassicalWeightReduction.Incidence R) := by
    classical
    let e : ClassicalWeightReduction.Incidence R ≃
        (Σ c : Check,
          Fin (Fintype.card
            (ClassicalWeightReduction.CheckNeighbor R c))) :=
      { toFun := fun edge =>
          ⟨edge.1.1, ClassicalWeightReduction.checkPosition R edge⟩
        invFun := fun s =>
          ClassicalWeightReduction.checkIncidenceAt R s.1 s.2
        left_inv :=
          ClassicalWeightReduction.checkIncidenceAt_checkPosition R
        right_inv := by
          rintro ⟨c, i⟩
          apply Sigma.ext (show c = c by rfl)
          simp
          exact HEq.rfl }
    rw [Fintype.card_congr e]
    simp only [ClassicalWeightReduction.AuxiliaryBit,
      Fintype.card_sigma, Fintype.card_fin]
    apply Finset.sum_le_sum
    intro c _
    omega
  constructor
  · rw [show Fintype.card
        (ClassicalWeightReduction.WeightReducedBit R) =
          Fintype.card (ClassicalWeightReduction.Incidence R) +
            Fintype.card (ClassicalWeightReduction.AuxiliaryBit R) by simp]
    omega
  · rw [show Fintype.card
        (ClassicalWeightReduction.WeightReducedCheck R) =
          Fintype.card (ClassicalWeightReduction.Incidence R) +
            Fintype.card (ClassicalWeightReduction.AuxiliaryCheck R) by simp]
    omega

/-- The number of reduced classical bits is controlled explicitly by the
sample degree window. -/
theorem card_weightReducedClassicalBit_le
    {r Delta : Nat} (sample : Sample r)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    Fintype.card
        (ClassicalWeightReduction.WeightReducedBit
          (incidenceRelation sample)) ≤
      808 * r * Delta := by
  have hCard :=
    (card_weightReducedClassicalSides_le_two_mul_incidence
      (incidenceRelation sample)).1
  rw [card_incidence_eq_sum_bitNeighbor (incidenceRelation sample)] at hCard
  have hIncidence :
      (∑ b : Fin (4 * r),
        Fintype.card (ClassicalWeightReduction.BitNeighbor
          (incidenceRelation sample) b)) ≤
        (4 * r) * (101 * Delta) := by
    calc
      _ ≤ ∑ _b : Fin (4 * r), 101 * Delta := by
        apply Finset.sum_le_sum
        intro b _
        exact bitNeighbor_card_le_of_degreeWindows sample hGood.1.1 b
      _ = (4 * r) * (101 * Delta) := by simp
  calc
    _ ≤ 2 *
        (∑ b : Fin (4 * r),
          Fintype.card (ClassicalWeightReduction.BitNeighbor
            (incidenceRelation sample) b)) := hCard
    _ ≤ 2 * ((4 * r) * (101 * Delta)) :=
      Nat.mul_le_mul_left 2 hIncidence
    _ = 808 * r * Delta := by ring

/-- The number of reduced classical checks obeys the analogous explicit
degree-window bound. -/
theorem card_weightReducedClassicalCheck_le
    {r Delta : Nat} (sample : Sample r)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    Fintype.card
        (ClassicalWeightReduction.WeightReducedCheck
          (incidenceRelation sample)) ≤
      808 * r * Delta := by
  have hCard :=
    (card_weightReducedClassicalSides_le_two_mul_incidence
      (incidenceRelation sample)).2
  rw [card_incidence_eq_sum_bitNeighbor (incidenceRelation sample)] at hCard
  have hIncidence :
      (∑ b : Fin (4 * r),
        Fintype.card (ClassicalWeightReduction.BitNeighbor
          (incidenceRelation sample) b)) ≤
        (4 * r) * (101 * Delta) := by
    calc
      _ ≤ ∑ _b : Fin (4 * r), 101 * Delta := by
        apply Finset.sum_le_sum
        intro b _
        exact bitNeighbor_card_le_of_degreeWindows sample hGood.1.1 b
      _ = (4 * r) * (101 * Delta) := by simp
  calc
    _ ≤ 2 *
        (∑ b : Fin (4 * r),
          Fintype.card (ClassicalWeightReduction.BitNeighbor
            (incidenceRelation sample) b)) := hCard
    _ ≤ 2 * ((4 * r) * (101 * Delta)) :=
      Nat.mul_le_mul_left 2 hIncidence
    _ = 808 * r * Delta := by ring

/-- At every HHO20 hierarchy index, an actual construction-owned classical
LDPC balancing code exists with all EKZ premises and size/locality bounds
proved together. -/
theorem exists_classicalLDPCBalance_at
    (s : Nat) (hs : 200 ≤ s) :
    ∃ sample : Sample (RandomPartition.hho20BaseScale s),
      IsFullyGood
          (Delta := RandomPartition.hho20DegreeScale s) sample ∧
      Function.Surjective
        (ClassicalWeightReduction.boundary (F := ZMod 2)
          (incidenceRelation sample)) ∧
      DistanceBalancing.ClassicalDistanceAtLeast
        (LinearMap.toMatrix'
          (ClassicalWeightReduction.boundary (F := ZMod 2)
            (incidenceRelation sample)))
        ((4 * RandomPartition.hho20BaseScale s) / 5) ∧
      (∀ q : ClassicalWeightReduction.WeightReducedCheck
          (incidenceRelation sample),
        HammingWeight
          (wordLinearMapTranspose
            (ClassicalWeightReduction.boundary (F := ZMod 2)
              (incidenceRelation sample))
            (Pi.single q 1)) ≤ 3) ∧
      (∀ b : ClassicalWeightReduction.WeightReducedBit
          (incidenceRelation sample),
        HammingWeight
          (ClassicalWeightReduction.boundary (F := ZMod 2)
            (incidenceRelation sample) (Pi.single b 1)) ≤ 3) ∧
      Fintype.card
          (ClassicalWeightReduction.WeightReducedBit
            (incidenceRelation sample)) ≤
        808 * RandomPartition.hho20BaseScale s *
          RandomPartition.hho20DegreeScale s ∧
      Fintype.card
          (ClassicalWeightReduction.WeightReducedCheck
            (incidenceRelation sample)) ≤
        808 * RandomPartition.hho20BaseScale s *
          RandomPartition.hho20DegreeScale s := by
  letI : NeZero (RandomPartition.hho20BaseScale s) :=
    ⟨by
      have := RandomPartition.hho20_baseScale_ge_five_hundred s hs
      omega⟩
  letI : NeZero (RandomPartition.hho20TypeCount s) :=
    ⟨RandomPartition.hho20TypeCount_ne_zero s (by omega)⟩
  letI : NeZero (RandomPartition.hho20FiberLength s) :=
    ⟨by
      have := RandomPartition.hho20_fiberLength_ge s (by omega)
      omega⟩
  letI : NeZero (RandomPartition.hho20FiberLength s - 1) :=
    ⟨by
      have := RandomPartition.hho20_fiberLength_ge s (by omega)
      omega⟩
  obtain ⟨sample, _twistSample, hGood, _hChecks, _hSpectrum, _hLTC⟩ :=
    RandomPartition.exists_hho20_base_and_twist_at s hs
  have hDelta : 1 ≤ RandomPartition.hho20DegreeScale s := by
    exact Nat.one_le_iff_ne_zero.mpr (by
      simp only [RandomPartition.hho20DegreeScale,
        RandomPartition.hho20TypeCount]
      positivity)
  refine ⟨sample, hGood,
    weightReducedBoundary_surjective sample hDelta hGood,
    weightReducedClassicalDistanceAtLeast sample hDelta hGood,
    weightReducedClassical_rowWeight_le_three sample,
    weightReducedClassical_columnWeight_le_three sample,
    card_weightReducedClassicalBit_le sample hGood,
    card_weightReducedClassicalCheck_le sample hGood⟩

end QEC.Coding.FiberBundle.RandomBase
