import QEC.Coding.CSS.Distance
import QEC.Coding.Stabilizer.JointMeasurement
import QEC.Coding.ReedMuller.Punctured
import QEC.Distillation.Universality.OneQubitPhase
import QEC.Distillation.Core.TransversalGate
import QEC.Distillation.Triorthogonal.CSS
import QEC.Distillation.Triorthogonal.Transversal
/-!
# HH18 punctured Reed--Muller CSS codes

This module builds the finite code in HH18 Theorem 1 from the actual punctured
and shortened Reed--Muller codes in `QEC.Coding.PuncturedReedMuller`.  The
present layers construct its checks, semantic carrier, joint projector, and
normalized encoding.  Exact parameters and transversal phase results are
added in later layers.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18PuncturedReedMuller

open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Coding.PauliSymplectic
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

/-- The retained HH18 coordinates are the physical qubit sites. -/
abbrev PhysicalSite (m w : Nat) := KeptPoint m w

/-- The removed HH18 coordinates index the selected logical qubits. -/
abbrev LogicalSite (m w : Nat) := LowPoint m w

private abbrev CodeBasisIndex {ι : Type} [Fintype ι]
    (C : LinearCode (ZMod 2) ι) :=
  Fin (Dimension C)

private noncomputable def codeBasis {ι : Type} [Fintype ι]
    (C : LinearCode (ZMod 2) ι) :
    Module.Basis (CodeBasisIndex C) (ZMod 2) C.carrier :=
  Module.finBasis (ZMod 2) C.carrier

private def codeBasisWord {ι : Type} [Fintype ι]
    (C : LinearCode (ZMod 2) ι) (i : CodeBasisIndex C) :
    Word (ZMod 2) ι :=
  codeBasis C i

private noncomputable def codeParityCheck {ι : Type} [Fintype ι]
    (C : LinearCode (ZMod 2) ι) :
    Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) (CodeBasisIndex C) where
  toFun word i := wordPairing (codeBasisWord C i) word
  map_add' := by
    intro left right
    funext i
    exact (wordPairing (F := ZMod 2) (codeBasisWord C i)).map_add left right
  map_smul' := by
    intro scalar word
    funext i
    exact (wordPairing (F := ZMod 2) (codeBasisWord C i)).map_smul scalar word

private theorem codeParityCheck_row {ι : Type} [Fintype ι]
    (C : LinearCode (ZMod 2) ι) (i : CodeBasisIndex C) :
    parityCheckRow (codeParityCheck C) i = codeBasisWord C i := by
  classical
  ext j
  simp [parityCheckRow, wordLinearMapTranspose, codeParityCheck,
    codeBasisWord, wordPairing_apply, dotProduct]
  rw [Fintype.sum_eq_single i]
  · rw [Fintype.sum_eq_single j]
    · simp
    · intro other hne
      simp [hne]
  · intro other hne
    simp [hne]

private theorem codeParityCheck_rowCode {ι : Type} [Fintype ι]
    (C : LinearCode (ZMod 2) ι) :
    parityCheckRowCode (codeParityCheck C) = C := by
  have hcarrier :
      (parityCheckRowCode (codeParityCheck C)).carrier = C.carrier := by
    ext word
    constructor
    · rintro ⟨coefficients, rfl⟩
      rw [wordLinearMapTranspose_eq_sum_parityCheckRows]
      simp_rw [codeParityCheck_row]
      exact Submodule.sum_mem C.carrier fun i _ =>
        C.carrier.smul_mem _ (codeBasis C i).property
    · intro hword
      let wordInCode : C.carrier := ⟨word, hword⟩
      refine ⟨fun i => (codeBasis C).repr wordInCode i, ?_⟩
      rw [wordLinearMapTranspose_eq_sum_parityCheckRows]
      simp_rw [codeParityCheck_row]
      change
        (∑ x, (codeBasis C).repr wordInCode x •
          ((codeBasis C x : C.carrier) : Word (ZMod 2) ι)) = word
      simpa only [Submodule.coe_sum, Submodule.coe_smul, wordInCode] using
        congrArg Subtype.val ((codeBasis C).sum_repr wordInCode)
  cases hleft : parityCheckRowCode (codeParityCheck C) with
  | mk leftCarrier =>
      cases hright : C with
      | mk rightCarrier =>
          rw [hleft, hright] at hcarrier
          change leftCarrier = rightCarrier at hcarrier
          cases hcarrier
          rfl

/-- Canonical finite index type for the chosen X-check basis. -/
abbrev XCheckIndex (w r m : Nat) :=
  CodeBasisIndex (shortenedReedMullerCode r m w)

/-- Canonical finite index type for the chosen Z-check basis. -/
abbrev ZCheckIndex (w r m : Nat) :=
  CodeBasisIndex (shortenedReedMullerCode (m - r - 1) m w)

/-- A chosen basis of the actual X-shortened Reed--Muller code. -/
noncomputable def xCheckBasis (w r m : Nat) :
    Module.Basis (XCheckIndex w r m) (ZMod 2)
      (shortenedReedMullerCode r m w).carrier :=
  codeBasis (shortenedReedMullerCode r m w)

/-- A chosen basis of the actual Z-shortened Reed--Muller code. -/
noncomputable def zCheckBasis (w r m : Nat) :
    Module.Basis (ZCheckIndex w r m) (ZMod 2)
      (shortenedReedMullerCode (m - r - 1) m w).carrier :=
  codeBasis (shortenedReedMullerCode (m - r - 1) m w)

/-- The physical word selected by one X-check basis index. -/
def xCheckWord (w r m : Nat) (i : XCheckIndex w r m) :
    Word (ZMod 2) (PhysicalSite m w) :=
  xCheckBasis w r m i

/-- The physical word selected by one Z-check basis index. -/
def zCheckWord (w r m : Nat) (i : ZCheckIndex w r m) :
    Word (ZMod 2) (PhysicalSite m w) :=
  zCheckBasis w r m i

/-- The basis-indexed parity-check map whose transpose rows are the X checks. -/
noncomputable def xParityCheck (w r m : Nat) :
    Word (ZMod 2) (PhysicalSite m w) →ₗ[ZMod 2]
      Word (ZMod 2) (XCheckIndex w r m) :=
  codeParityCheck (shortenedReedMullerCode r m w)

/-- The basis-indexed parity-check map whose transpose rows are the Z checks. -/
noncomputable def zParityCheck (w r m : Nat) :
    Word (ZMod 2) (PhysicalSite m w) →ₗ[ZMod 2]
      Word (ZMod 2) (ZCheckIndex w r m) :=
  codeParityCheck (shortenedReedMullerCode (m - r - 1) m w)

@[simp]
theorem parityCheckRow_xParityCheck (w r m : Nat) (i : XCheckIndex w r m) :
    parityCheckRow (xParityCheck w r m) i = xCheckWord w r m i :=
  codeParityCheck_row (shortenedReedMullerCode r m w) i

@[simp]
theorem parityCheckRow_zParityCheck (w r m : Nat) (i : ZCheckIndex w r m) :
    parityCheckRow (zParityCheck w r m) i = zCheckWord w r m i :=
  codeParityCheck_row (shortenedReedMullerCode (m - r - 1) m w) i

/-- The presented X row code is exactly the constructed X-shortened code. -/
theorem xParityCheck_rowCode (w r m : Nat) :
    parityCheckRowCode (xParityCheck w r m) =
      shortenedReedMullerCode r m w :=
  codeParityCheck_rowCode (shortenedReedMullerCode r m w)

/-- The presented Z row code is exactly the constructed Z-shortened code. -/
theorem zParityCheck_rowCode (w r m : Nat) :
    parityCheckRowCode (zParityCheck w r m) =
      shortenedReedMullerCode (m - r - 1) m w :=
  codeParityCheck_rowCode (shortenedReedMullerCode (m - r - 1) m w)

/-- The actual X-stabilizer code used by the semantic CSS constructor. -/
noncomputable def xCode (w r m : Nat) :
    LinearCode (ZMod 2) (PhysicalSite m w) :=
  parityCheckRowCode (xParityCheck w r m)

/-- The actual Z-stabilizer code used by the semantic CSS constructor. -/
noncomputable def zCode (w r m : Nat) :
    LinearCode (ZMod 2) (PhysicalSite m w) :=
  parityCheckRowCode (zParityCheck w r m)

@[simp]
theorem xCode_eq_shortened (w r m : Nat) :
    xCode w r m = shortenedReedMullerCode r m w :=
  xParityCheck_rowCode w r m

@[simp]
theorem zCode_eq_shortened (w r m : Nat) :
    zCode w r m = shortenedReedMullerCode (m - r - 1) m w :=
  zParityCheck_rowCode w r m

/-- HH18 admissibility derives the required X/Z dual containment. -/
theorem cssDualContainment {w r m : Nat} (h : Admissible w r m) :
    (zCode w r m).carrier ≤ (xCode w r m).dual.carrier := by
  rw [xCode_eq_shortened, zCode_eq_shortened]
  exact shortenedReedMullerCode_dualContainment h

/-- Every chosen Z basis row is orthogonal to every chosen X basis row. -/
theorem parityCheckRows_orthogonal {w r m : Nat} (h : Admissible w r m) :
    ∀ z x,
      wordPairing
        (parityCheckRow (zParityCheck w r m) z)
        (parityCheckRow (xParityCheck w r m) x) = 0 :=
  (parityCheckRows_orthogonal_iff_rowCode_le_dual
    (zParityCheck w r m) (xParityCheck w r m)).2 (cssDualContainment h)

/-- The finite oriented family: left indices are Z checks and right indices are X checks. -/
noncomputable def checkGenerator (w r m : Nat) :
    Sum (ZCheckIndex w r m) (XCheckIndex w r m) →
      PauliSymplectic.Binary (PhysicalSite m w) :=
  binaryCSSParityCheckGenerators (zParityCheck w r m) (xParityCheck w r m)

/-- The selected finite HH18 checks commute pairwise. -/
theorem checkGenerator_commutes {w r m : Nat} (h : Admissible w r m) :
    ∀ left right,
      PauliSymplectic.Commutes
        (checkGenerator w r m left) (checkGenerator w r m right) := by
  intro left right
  exact
    (binaryCSSStabilizerCodeOfParityChecks
      (zParityCheck w r m) (xParityCheck w r m)
      (parityCheckRows_orthogonal h)).isotropic
      (checkGenerator w r m left)
      (binaryCSSParityCheckGenerator_mem_checkSet
        (zParityCheck w r m) (xParityCheck w r m) left)
      (checkGenerator w r m right)
      (binaryCSSParityCheckGenerator_mem_checkSet
        (zParityCheck w r m) (xParityCheck w r m) right)

/-- The actual parity-check stabilizer generated by the chosen finite bases. -/
noncomputable def stabilizer {w r m : Nat} (h : Admissible w r m) :
    StabilizerCode (ZMod 2) (PhysicalSite m w)
      (Qubit.QubitRegister (PhysicalSite m w)) :=
  binaryCSSStabilizerCodeOfParityChecks
    (zParityCheck w r m) (xParityCheck w r m)
    (parityCheckRows_orthogonal h)

/-- The chosen finite family generates the stabilizer's actual generated group. -/
theorem checkGenerator_generates_stabilizer {w r m : Nat}
    (h : Admissible w r m) :
    generatedStabilizerSet (checkGenerator w r m) =
      (stabilizer h).generatedGroup :=
  binaryCSSParityCheckGenerators_generate_generatedGroup
    (zParityCheck w r m) (xParityCheck w r m)
    (parityCheckRows_orthogonal h)

/-- The HH18 stabilizer satisfies the repository's source-valid binary convention. -/
noncomputable def sourceValidStabilizer {w r m : Nat}
    (h : Admissible w r m) :
    StabilizerCode.SourceValidBinary (PhysicalSite m w) :=
  binaryCSSSourceValidStabilizerOfParityChecks
    (zParityCheck w r m) (xParityCheck w r m)
    (parityCheckRows_orthogonal h)

/-- The attained X-logical distance is the punctured Reed--Muller coset
distance for the actual HH18 parity-check presentation. -/
theorem xLogicalMinimumDistance {w r m : Nat} (h : Admissible w r m) :
    CSSXLogicalMinimumDistance (zParityCheck w r m) (xParityCheck w r m)
      (binomialTail (m - r) w) := by
  have hnoKernel : w < m - r := by
    have hwindow := h.2
    omega
  unfold CSSXLogicalMinimumDistance
  rw [← parityCheckRowCode_dual_eq_kernelCode (zParityCheck w r m),
    zParityCheck_rowCode, xParityCheck_rowCode]
  simpa only [RelativeMinimumDistance,
    shortenedReedMullerCode_dual_eq_punctured h] using
    (puncturedReedMullerCode_relativeMinimumDistance_shortened hnoKernel)

/-- The attained Z-logical distance is the complementary punctured
Reed--Muller coset distance for the actual HH18 parity-check presentation. -/
theorem zLogicalMinimumDistance {w r m : Nat} (h : Admissible w r m) :
    CSSZLogicalMinimumDistance (zParityCheck w r m) (xParityCheck w r m)
      (binomialTail (r + 1) w) := by
  have hcomplementDegree : m - (m - r - 1) - 1 = r := by
    have hdegree := h.2.2
    omega
  have hcomplementTail : m - (m - r - 1) = r + 1 := by
    have hdegree := h.2.2
    omega
  have hcomplementLt : m - r - 1 < m := by
    have hdegree := h.2.2
    omega
  have hcut : w ≤ m - (m - r - 1) - 1 := by
    have hwindow := h.2
    omega
  have hnoKernel : w < m - (m - r - 1) := by
    have hwindow := h.2
    omega
  have hdual :
      (shortenedReedMullerCode r m w).dual.carrier =
        (puncturedReedMullerCode (m - r - 1) m w).carrier := by
    simpa only [hcomplementDegree] using
      (shortenedReedMullerCode_dual_eq_punctured_of_lt_of_le
        (r := m - r - 1) (m := m) (w := w) hcomplementLt hcut)
  unfold CSSZLogicalMinimumDistance
  rw [← parityCheckRowCode_dual_eq_kernelCode (xParityCheck w r m),
    xParityCheck_rowCode, zParityCheck_rowCode]
  simpa only [RelativeMinimumDistance, hdual, hcomplementTail] using
    (puncturedReedMullerCode_relativeMinimumDistance_shortened
      (r := m - r - 1) hnoKernel)

/-- The semantic distance of the actual source-valid HH18 CSS stabilizer is
the smaller complementary logical-sector binomial tail. -/
theorem semanticDistance {w r m : Nat} (h : Admissible w r m) :
    StabilizerCode.SemanticStabilizerDistance (sourceValidStabilizer h)
      (binomialTail (r + 1) w) := by
  have hindex : r + 1 ≤ m - r := by
    have hdegree := h.2.2
    omega
  have htail : binomialTail (r + 1) w ≤ binomialTail (m - r) w :=
    binomialTail_mono_left hindex
  simpa only [sourceValidStabilizer, Nat.min_eq_right htail] using
    (StabilizerCode.binaryCSSStabilizerDistance_eq_min_logicalDistances
      (zParityCheck w r m) (xParityCheck w r m)
      (parityCheckRows_orthogonal h)
      (xLogicalMinimumDistance h) (zLogicalMinimumDistance h))

/-- The actual semantic HH18 CSS code. -/
noncomputable def cssCode {w r m : Nat} (h : Admissible w r m) :
    CSSCode (ZMod 2) (PhysicalSite m w)
      (Qubit.QubitRegister (PhysicalSite m w)) where
  xCode := xCode w r m
  zCode := zCode w r m
  stabilizer := stabilizer h
  orthogonal := by
    intro x hx z hz
    exact (xCode w r m).symplecticForm_x_zero_zero_z_eq_zero_of_mem_dual
      hx (cssDualContainment h hz)

@[simp]
theorem cssCode_xCode {w r m : Nat} (h : Admissible w r m) :
    (cssCode h).xCode = shortenedReedMullerCode r m w :=
  xCode_eq_shortened w r m

@[simp]
theorem cssCode_zCode {w r m : Nat} (h : Admissible w r m) :
    (cssCode h).zCode = shortenedReedMullerCode (m - r - 1) m w :=
  zCode_eq_shortened w r m

/-- The all-positive visible joint syndrome. -/
def allPositiveSyndrome (w r m : Nat) :
    JointSyndrome (Sum (ZCheckIndex w r m) (XCheckIndex w r m)) :=
  fun _ => StabilizerOutcome.positive

/-- The literal all-positive joint projector for the chosen HH18 check bases. -/
noncomputable def jointProjector {w r m : Nat} (h : Admissible w r m) :
    Operator (Qubit.QubitRegister (PhysicalSite m w)) :=
  jointStabilizerProjector (checkGenerator w r m)
    (checkGenerator_commutes h) (allPositiveSyndrome w r m)

private theorem checkGenerator_toHermitian_eq {w r m : Nat}
    (check : Sum (ZCheckIndex w r m) (XCheckIndex w r m)) :
    toHermitianQubitOperator (checkGenerator w r m check) =
      toQubitOperator (checkGenerator w r m check) := by
  cases check <;>
    simp [checkGenerator, binaryCSSParityCheckGenerators,
      toHermitianQubitOperator, hermitianPhaseScalar,
      binaryOverlapCount, binaryOverlapSupport, cssXCheck, cssZCheck,
      xSupport, zSupport]

/-- Membership in the actual CSS carrier is finite basis-check fixedness. -/
theorem mem_cssCarrier_iff_checkGenerator_fixed {w r m : Nat}
    (h : Admissible w r m)
    (psi : Qubit.QubitRegister (PhysicalSite m w)) :
    psi ∈ (cssCode h).stabilizer.code.carrier ↔
      ∀ check, toQubitOperator (checkGenerator w r m check) psi = psi := by
  rcases binaryCSSStabilizerCodeOfParityChecks_spec
      (zParityCheck w r m) (xParityCheck w r m)
      (parityCheckRows_orthogonal h) with
    ⟨_hchecks, hgenerated, _hsign, _hcommutes, hfixed⟩
  calc
    psi ∈ (cssCode h).stabilizer.code.carrier ↔
        ∀ S, S ∈ (stabilizer h).generatedGroup →
          toQubitOperator S psi = psi := hfixed psi
    _ ↔ ∀ S, GeneratedStabilizer (checkGenerator w r m) S →
          toQubitOperator S psi = psi := by
      change
        (∀ S, S ∈
            (binaryCSSStabilizerCodeOfParityChecks
              (zParityCheck w r m) (xParityCheck w r m)
              (parityCheckRows_orthogonal h)).generatedGroup →
            toQubitOperator S psi = psi) ↔
          ∀ S, GeneratedStabilizer (checkGenerator w r m) S →
            toQubitOperator S psi = psi
      rw [← hgenerated]
      rfl
    _ ↔ ∀ check, toQubitOperator (checkGenerator w r m check) psi = psi :=
      fixed_generatedStabilizer_iff_fixed_generators (checkGenerator w r m) psi

/-- The all-positive joint projector fixes exactly the actual HH18 CSS carrier. -/
theorem jointProjector_fixed_iff_mem_cssCarrier {w r m : Nat}
    (h : Admissible w r m)
    (psi : Qubit.QubitRegister (PhysicalSite m w)) :
    jointProjector h psi = psi ↔
      psi ∈ (cssCode h).stabilizer.code.carrier := by
  rw [mem_cssCarrier_iff_checkGenerator_fixed h]
  rw [jointProjector, jointStabilizerProjector_fixed_iff]
  constructor
  · intro hfixed check
    have := hfixed check
    rw [checkGenerator_toHermitian_eq] at this
    simpa [allPositiveSyndrome, StabilizerOutcome.sign] using this
  · intro hfixed check
    rw [checkGenerator_toHermitian_eq]
    simpa [allPositiveSyndrome, StabilizerOutcome.sign] using hfixed check

/-- The retained block of the systematic Reed--Muller lift. -/
noncomputable def keptSystematicLift {w r m : Nat} (h : Admissible w r m) :
    Word (ZMod 2) (LogicalSite m w) →ₗ[ZMod 2]
      Word (ZMod 2) (PhysicalSite m w) :=
  PuncturedReedMuller.systematicKeptLift h

/-- Every retained systematic lift belongs to the actual punctured code. -/
theorem keptSystematicLift_mem_punctured {w r m : Nat}
    (h : Admissible w r m)
    (logical : Word (ZMod 2) (LogicalSite m w)) :
    keptSystematicLift h logical ∈
      (puncturedReedMullerCode r m w).carrier :=
  systematicKeptLift_mem_puncturedReedMullerCode h logical

/-- The CSS logical quotient is the actual quotient of the Z normalizer by X checks. -/
noncomputable abbrev LogicalQuotient (w r m : Nat) :=
  binaryCSSLogicalBasisQuotient (xCode w r m) (zCode w r m)

private def keptSystematicLiftInZDual {w r m : Nat}
    (h : Admissible w r m) :
    Word (ZMod 2) (LogicalSite m w) →ₗ[ZMod 2]
      (zCode w r m).dual.carrier :=
  (keptSystematicLift h).codRestrict (zCode w r m).dual.carrier fun logical => by
    rw [zCode_eq_shortened, shortenedReedMullerCode_dual_eq_punctured h]
    exact keptSystematicLift_mem_punctured h logical

/-- Map a low-coordinate logical word to its systematic CSS quotient class. -/
noncomputable def logicalWordToQuotient {w r m : Nat}
    (h : Admissible w r m) :
    Word (ZMod 2) (LogicalSite m w) →ₗ[ZMod 2]
      LogicalQuotient w r m :=
  (binaryCSSXCodeInZDual (xCode w r m) (zCode w r m)).mkQ.comp
    (keptSystematicLiftInZDual h)

@[simp]
theorem logicalWordToQuotient_apply {w r m : Nat}
    (h : Admissible w r m)
    (logical : Word (ZMod 2) (LogicalSite m w)) :
    logicalWordToQuotient h logical =
      Submodule.Quotient.mk (keptSystematicLiftInZDual h logical) :=
  rfl

/-- A systematic lift is shortened exactly when its logical low block is zero. -/
theorem keptSystematicLift_mem_xCode_iff {w r m : Nat}
    (h : Admissible w r m)
    (logical : Word (ZMod 2) (LogicalSite m w)) :
    keptSystematicLift h logical ∈ (xCode w r m).carrier ↔ logical = 0 := by
  rw [xCode_eq_shortened]
  exact systematicKeptLift_mem_shortenedReedMullerCode_iff h logical

/-- Distinct low-coordinate words determine distinct CSS quotient classes. -/
theorem logicalWordToQuotient_injective {w r m : Nat}
    (h : Admissible w r m) :
    Function.Injective (logicalWordToQuotient h) := by
  rw [injective_iff_map_eq_zero]
  intro logical hlogical
  have hmem :
      keptSystematicLift h logical ∈ (xCode w r m).carrier := by
    exact
      (Submodule.Quotient.mk_eq_zero
        (binaryCSSXCodeInZDual (xCode w r m) (zCode w r m))).mp hlogical
  exact (keptSystematicLift_mem_xCode_iff h logical).1 hmem

/-- Every CSS quotient class has a systematic low-coordinate representative. -/
theorem logicalWordToQuotient_surjective {w r m : Nat}
    (h : Admissible w r m) :
    Function.Surjective (logicalWordToQuotient h) := by
  intro quotient
  refine Submodule.Quotient.induction_on
    (p := binaryCSSXCodeInZDual (xCode w r m) (zCode w r m))
    quotient ?_
  intro word
  have hpunctured :
      (word : Word (ZMod 2) (PhysicalSite m w)) ∈
        (puncturedReedMullerCode r m w).carrier := by
    have hshortened :
        (word : Word (ZMod 2) (PhysicalSite m w)) ∈
          (shortenedReedMullerCode (m - r - 1) m w).dual.carrier := by
      rw [← zCode_eq_shortened]
      exact word.2
    rw [shortenedReedMullerCode_dual_eq_punctured h] at hshortened
    exact hshortened
  obtain ⟨logical, shortened, hshortened, hdecompose⟩ :=
    exists_systematicKeptLift_add_shortened h hpunctured
  refine ⟨logical, ?_⟩
  apply (Submodule.Quotient.eq
    (binaryCSSXCodeInZDual (xCode w r m) (zCode w r m))).2
  change
    keptSystematicLift h logical -
        (word : Word (ZMod 2) (PhysicalSite m w)) ∈
      (xCode w r m).carrier
  rw [xCode_eq_shortened]
  have hneg :
      -shortened ∈ (shortenedReedMullerCode r m w).carrier :=
    (shortenedReedMullerCode r m w).carrier.neg_mem hshortened
  convert hneg using 1
  change systematicKeptLift h logical -
      (word : Word (ZMod 2) (PhysicalSite m w)) = -shortened
  rw [← hdecompose]
  module

/-- Low-coordinate words are linearly equivalent to the actual CSS quotient. -/
noncomputable def logicalWordEquivQuotient {w r m : Nat}
    (h : Admissible w r m) :
    Word (ZMod 2) (LogicalSite m w) ≃ₗ[ZMod 2]
      LogicalQuotient w r m :=
  LinearEquiv.ofBijective (logicalWordToQuotient h)
    ⟨logicalWordToQuotient_injective h, logicalWordToQuotient_surjective h⟩

@[simp]
theorem logicalWordEquivQuotient_apply {w r m : Nat}
    (h : Admissible w r m)
    (logical : Word (ZMod 2) (LogicalSite m w)) :
    logicalWordEquivQuotient h logical = logicalWordToQuotient h logical :=
  rfl

/-- Computational labels on low sites are the systematic CSS quotient labels. -/
noncomputable def logicalBasisEquivQuotient {w r m : Nat}
    (h : Admissible w r m) :
    Qubit.Bitstring (LogicalSite m w) ≃ LogicalQuotient w r m :=
  (bitstringWordEquiv (LogicalSite m w)).trans
    (logicalWordEquivQuotient h).toEquiv

/-- Reindex logical amplitudes by their actual CSS quotient classes. -/
noncomputable def logicalBasisReindex {w r m : Nat}
    (h : Admissible w r m) :
    Qubit.QubitRegister (LogicalSite m w) ≃ₗᵢ[Complex]
      EuclideanSpace Complex (LogicalQuotient w r m) :=
  LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex
    (logicalBasisEquivQuotient h)

private theorem quotientToCarrier_inner {w r m : Nat}
    (h : Admissible w r m)
    (phi chi : EuclideanSpace Complex (LogicalQuotient w r m)) :
    inner Complex
        (binaryCSSLogicalBasisQuotientToCarrier
          (xCode w r m) (zCode w r m) (cssDualContainment h) phi)
        (binaryCSSLogicalBasisQuotientToCarrier
          (xCode w r m) (zCode w r m) (cssDualContainment h) chi) =
      (Nat.card (xCode w r m).carrier : Complex) *
        inner Complex phi chi := by
  exact Triorthogonal.binaryCSSLogicalBasisQuotientToCarrier_inner
    (xCode w r m) (zCode w r m) (cssDualContainment h) phi chi

/-- The inverse square-root normalization of one X-stabilizer coset. -/
noncomputable def cssNormalizationScalar {w r m : Nat}
    (_h : Admissible w r m) : Complex :=
  (Real.sqrt (Nat.card (xCode w r m).carrier : Real) : Complex)⁻¹

private theorem cssNormalizationScalar_identity {w r m : Nat}
    (h : Admissible w r m) :
    starRingEnd Complex (cssNormalizationScalar h) *
        cssNormalizationScalar h *
        (Nat.card (xCode w r m).carrier : Complex) = 1 := by
  have hcard : 0 < Nat.card (xCode w r m).carrier := Nat.card_pos
  have hsqrtPos :
      0 < Real.sqrt (Nat.card (xCode w r m).carrier : Real) :=
    Real.sqrt_pos.2 (by exact_mod_cast hcard)
  have hsqrtNe :
      (Real.sqrt (Nat.card (xCode w r m).carrier : Real) : Complex) ≠ 0 := by
    exact_mod_cast hsqrtPos.ne'
  have hsquare :
      (Real.sqrt (Nat.card (xCode w r m).carrier : Real) : Complex) *
          (Real.sqrt (Nat.card (xCode w r m).carrier : Real) : Complex) =
        (Nat.card (xCode w r m).carrier : Complex) := by
    exact_mod_cast Real.mul_self_sqrt
      (by positivity : (0 : Real) ≤ Nat.card (xCode w r m).carrier)
  simp only [cssNormalizationScalar, map_inv₀]
  rw [show starRingEnd Complex
      (Real.sqrt (Nat.card (xCode w r m).carrier : Real) : Complex) =
        (Real.sqrt (Nat.card (xCode w r m).carrier : Real) : Complex) by simp]
  rw [← hsquare]
  field_simp [hsqrtNe]

/-- The explicitly normalized quotient-amplitude reconstruction map. -/
noncomputable def normalizedQuotientToCarrierLinearMap {w r m : Nat}
    (h : Admissible w r m) :
    EuclideanSpace Complex (LogicalQuotient w r m) →ₗ[Complex]
      (cssCode h).stabilizer.code.carrier :=
  cssNormalizationScalar h •
    binaryCSSLogicalBasisQuotientToCarrier
      (xCode w r m) (zCode w r m) (cssDualContainment h)

@[simp]
theorem normalizedQuotientToCarrierLinearMap_apply {w r m : Nat}
    (h : Admissible w r m)
    (phi : EuclideanSpace Complex (LogicalQuotient w r m)) :
    normalizedQuotientToCarrierLinearMap h phi =
      cssNormalizationScalar h •
        binaryCSSLogicalBasisQuotientToCarrier
          (xCode w r m) (zCode w r m) (cssDualContainment h) phi :=
  rfl

/-- The normalized quotient reconstruction preserves the exact inner product. -/
theorem normalizedQuotientToCarrierLinearMap_inner {w r m : Nat}
    (h : Admissible w r m)
    (phi chi : EuclideanSpace Complex (LogicalQuotient w r m)) :
    inner Complex (normalizedQuotientToCarrierLinearMap h phi)
        (normalizedQuotientToCarrierLinearMap h chi) =
      inner Complex phi chi := by
  rw [normalizedQuotientToCarrierLinearMap_apply,
    normalizedQuotientToCarrierLinearMap_apply]
  calc
    inner Complex
          (cssNormalizationScalar h •
            binaryCSSLogicalBasisQuotientToCarrier
              (xCode w r m) (zCode w r m) (cssDualContainment h) phi)
          (cssNormalizationScalar h •
            binaryCSSLogicalBasisQuotientToCarrier
              (xCode w r m) (zCode w r m) (cssDualContainment h) chi) =
        starRingEnd Complex (cssNormalizationScalar h) *
          inner Complex
            (binaryCSSLogicalBasisQuotientToCarrier
              (xCode w r m) (zCode w r m) (cssDualContainment h) phi)
            (cssNormalizationScalar h •
              binaryCSSLogicalBasisQuotientToCarrier
                (xCode w r m) (zCode w r m) (cssDualContainment h) chi) :=
      inner_smul_left _ _ _
    _ = starRingEnd Complex (cssNormalizationScalar h) *
          (cssNormalizationScalar h *
            inner Complex
              (binaryCSSLogicalBasisQuotientToCarrier
                (xCode w r m) (zCode w r m) (cssDualContainment h) phi)
              (binaryCSSLogicalBasisQuotientToCarrier
                (xCode w r m) (zCode w r m) (cssDualContainment h) chi)) := by
      rw [inner_smul_right]
    _ = starRingEnd Complex (cssNormalizationScalar h) *
          (cssNormalizationScalar h *
            ((Nat.card (xCode w r m).carrier : Complex) *
              inner Complex phi chi)) := by
      rw [quotientToCarrier_inner h]
    _ = (starRingEnd Complex (cssNormalizationScalar h) *
          cssNormalizationScalar h *
          (Nat.card (xCode w r m).carrier : Complex)) *
        inner Complex phi chi := by ring
    _ = inner Complex phi chi := by
      rw [cssNormalizationScalar_identity h, one_mul]

/-- The normalized quotient reconstruction as a linear isometry. -/
noncomputable def normalizedQuotientToCarrierLinearIsometry {w r m : Nat}
    (h : Admissible w r m) :
    EuclideanSpace Complex (LogicalQuotient w r m) →ₗᵢ[Complex]
      (cssCode h).stabilizer.code.carrier :=
  (normalizedQuotientToCarrierLinearMap h).isometryOfInner
    (normalizedQuotientToCarrierLinearMap_inner h)

/-- The normalized quotient reconstruction is onto the actual CSS carrier. -/
noncomputable def normalizedQuotientToCarrier {w r m : Nat}
    (h : Admissible w r m) :
    EuclideanSpace Complex (LogicalQuotient w r m) ≃ₗᵢ[Complex]
      (cssCode h).stabilizer.code.carrier := by
  let reconstruction := normalizedQuotientToCarrierLinearIsometry h
  have hdim :
      Module.finrank Complex (EuclideanSpace Complex (LogicalQuotient w r m)) =
        Module.finrank Complex (cssCode h).stabilizer.code.carrier := by
    have hraw :=
      (binaryCSSQuantumCodeOfDualLeCarrierEquivLogicalBasisQuotient
        (xCode w r m) (zCode w r m) (cssDualContainment h)).finrank_eq.symm
    rw [finrank_euclideanSpace] at hraw
    rw [finrank_euclideanSpace]
    exact hraw
  have hsurjective : Function.Surjective reconstruction :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      reconstruction.injective
  exact LinearIsometryEquiv.ofSurjective reconstruction hsurjective

@[simp]
theorem normalizedQuotientToCarrier_apply {w r m : Nat}
    (h : Admissible w r m)
    (phi : EuclideanSpace Complex (LogicalQuotient w r m)) :
    normalizedQuotientToCarrier h phi =
      normalizedQuotientToCarrierLinearMap h phi :=
  rfl

/-- The actual normalized logical-register encoding. -/
noncomputable def encoding {w r m : Nat} (h : Admissible w r m) :
    Qubit.QubitRegister (LogicalSite m w) ≃ₗᵢ[Complex]
      (cssCode h).stabilizer.code.carrier :=
  (logicalBasisReindex h).trans (normalizedQuotientToCarrier h)

/-- Exact normalized amplitudes on computational words in the actual
Z-normalizer carrier. -/
theorem encoding_apply_of_mem {w r m : Nat}
    (h : Admissible w r m)
    (psi : Qubit.QubitRegister (LogicalSite m w))
    {bits : Qubit.Bitstring (PhysicalSite m w)}
    (hbits :
      bitstringWordEquiv (PhysicalSite m w) bits ∈
        (zCode w r m).dual.carrier) :
    (encoding h psi : Qubit.QubitRegister (PhysicalSite m w)) bits =
      cssNormalizationScalar h *
        psi ((logicalBasisEquivQuotient h).symm
          (Submodule.Quotient.mk
            ⟨bitstringWordEquiv (PhysicalSite m w) bits, hbits⟩)) := by
  change cssNormalizationScalar h *
      binaryCSSLogicalBasisQuotientToQubitRegister
        (xCode w r m) (zCode w r m) (logicalBasisReindex h psi) bits = _
  rw [binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_mem
    (xCode w r m) (zCode w r m) (logicalBasisReindex h psi) hbits]
  rfl

/-- Exact normalized amplitudes vanish outside the actual Z-normalizer
carrier. -/
theorem encoding_apply_of_not_mem {w r m : Nat}
    (h : Admissible w r m)
    (psi : Qubit.QubitRegister (LogicalSite m w))
    {bits : Qubit.Bitstring (PhysicalSite m w)}
    (hbits :
      bitstringWordEquiv (PhysicalSite m w) bits ∉
        (zCode w r m).dual.carrier) :
    (encoding h psi : Qubit.QubitRegister (PhysicalSite m w)) bits = 0 := by
  change cssNormalizationScalar h *
      binaryCSSLogicalBasisQuotientToQubitRegister
        (xCode w r m) (zCode w r m) (logicalBasisReindex h psi) bits = 0
  rw [binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_not_mem
    (xCode w r m) (zCode w r m) (logicalBasisReindex h psi) hbits]
  simp

/-- Splitting a full Reed--Muller word into low and retained coordinates. -/
private theorem wordPairing_restrict_split {m w : Nat}
    (left right : Word (ZMod 2) (BooleanPoint m)) :
    wordPairing left right =
      wordPairing (restrictLow m w left) (restrictLow m w right) +
        wordPairing (restrictKept m w left) (restrictKept m w right) := by
  classical
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype
      (fun point : BooleanPoint m => pointWeight point ≤ w)
      (fun point => left point * right point)
  let complementKept :
      {point : BooleanPoint m // ¬ pointWeight point ≤ w} ≃ KeptPoint m w :=
    { toFun := fun point => ⟨point.1, by omega⟩
      invFun := fun point => ⟨point.1, by omega⟩
      left_inv := fun point => Subtype.ext rfl
      right_inv := fun point => Subtype.ext rfl }
  have hequiv :
      (∑ point : {point : BooleanPoint m // ¬ pointWeight point ≤ w},
        left point.1 * right point.1) =
        ∑ point : KeptPoint m w, left point.1 * right point.1 := by
    exact Fintype.sum_equiv complementKept _ _ (fun _ => rfl)
  change
    (∑ point : BooleanPoint m, left point * right point) =
      (∑ point : LowPoint m w, left point.1 * right point.1) +
        ∑ point : KeptPoint m w, left point.1 * right point.1
  calc
    (∑ point : BooleanPoint m, left point * right point) =
        (∑ point : LowPoint m w, left point.1 * right point.1) +
          ∑ point : {point : BooleanPoint m // ¬ pointWeight point ≤ w},
            left point.1 * right point.1 := by
      simpa only [LowPoint] using hsplit.symm
    _ = (∑ point : LowPoint m w, left point.1 * right point.1) +
          ∑ point : KeptPoint m w, left point.1 * right point.1 := by
      rw [hequiv]

/-- The retained systematic lifts preserve the binary pairing of their low
coordinate labels. -/
private theorem wordPairing_systematicKeptLift {w r m : Nat}
    (h : Admissible w r m)
    (left right : Word (ZMod 2) (LogicalSite m w)) :
    wordPairing (keptSystematicLift h left) (keptSystematicLift h right) =
      wordPairing left right := by
  classical
  have hwr : w ≤ r := by
    have hwindow := h.2
    omega
  have hdegree : r + r < m := by
    have hwindow := h.2.2
    omega
  let fullLeft := lowCoordinateExtension hwr left
  let fullRight := lowCoordinateExtension hwr right
  have hfullLeft : fullLeft ∈ (reedMullerCode r m).carrier := by
    simpa [fullLeft] using lowCoordinateExtension_mem_reedMullerCode hwr left
  have hfullRight : fullRight ∈ (reedMullerCode r m).carrier := by
    simpa [fullRight] using lowCoordinateExtension_mem_reedMullerCode hwr right
  have hfullLeftDual : fullLeft ∈ (reedMullerCode r m).dual.carrier :=
    reedMullerCode_le_dual_of_add_lt hdegree hfullLeft
  have hfullPair : wordPairing fullLeft fullRight = 0 :=
    (reedMullerCode r m).orthogonal_of_mem_dual hfullLeftDual hfullRight
  have hlowLeft : restrictLow m w fullLeft = left := by
    simpa [fullLeft] using restrictLow_lowCoordinateExtension hwr left
  have hlowRight : restrictLow m w fullRight = right := by
    simpa [fullRight] using restrictLow_lowCoordinateExtension hwr right
  have hkeptLeft : restrictKept m w fullLeft = keptSystematicLift h left := by
    change restrictKept m w (lowCoordinateExtension hwr left) =
      restrictKept m w (lowCoordinateExtension hwr left)
    rfl
  have hkeptRight : restrictKept m w fullRight = keptSystematicLift h right := by
    change restrictKept m w (lowCoordinateExtension hwr right) =
      restrictKept m w (lowCoordinateExtension hwr right)
    rfl
  have hsplit := wordPairing_restrict_split (w := w) fullLeft fullRight
  rw [hfullPair, hlowLeft, hlowRight, hkeptLeft, hkeptRight] at hsplit
  have hneg := (eq_neg_of_add_eq_zero_left hsplit.symm).symm
  simpa only [ZMod.neg_eq_self_mod_two] using hneg

/-- The retained systematic representative of one computational logical
basis label. -/
noncomputable def logicalBasisWord {w r m : Nat}
    (h : Admissible w r m) (logical : LogicalSite m w) :
    Word (ZMod 2) (PhysicalSite m w) :=
  keptSystematicLift h (canonicalBasisWord logical)

/-- Each systematic logical basis word is in the actual Z normalizer. -/
theorem logicalBasisWord_mem_zDual {w r m : Nat}
    (h : Admissible w r m) (logical : LogicalSite m w) :
    logicalBasisWord h logical ∈ (zCode w r m).dual.carrier := by
  change keptSystematicLift h (canonicalBasisWord logical) ∈
    (zCode w r m).dual.carrier
  rw [zCode_eq_shortened, shortenedReedMullerCode_dual_eq_punctured h]
  exact keptSystematicLift_mem_punctured h (canonicalBasisWord logical)

/-- Each systematic logical basis word is dual to the actual X checks. -/
theorem logicalBasisWord_mem_xDual {w r m : Nat}
    (h : Admissible w r m) (logical : LogicalSite m w) :
    logicalBasisWord h logical ∈ (xCode w r m).dual.carrier := by
  classical
  have hwr : w ≤ r := by
    have hwindow := h.2
    omega
  have hdegree : r + r < m := by
    have hwindow := h.2.2
    omega
  change keptSystematicLift h (canonicalBasisWord logical) ∈
    (xCode w r m).dual.carrier
  rw [xCode_eq_shortened]
  refine ((shortenedReedMullerCode r m w).mem_dual _).2 ?_
  intro x hx
  rcases (mem_shortenedReedMullerCode x).1 hx with
    ⟨fullX, hfullX, hlowX, hkeptX⟩
  let fullLogical := lowCoordinateExtension hwr (canonicalBasisWord logical)
  have hfullLogical : fullLogical ∈ (reedMullerCode r m).carrier := by
    simpa [fullLogical] using
      lowCoordinateExtension_mem_reedMullerCode hwr (canonicalBasisWord logical)
  have hfullXDual : fullX ∈ (reedMullerCode r m).dual.carrier :=
    reedMullerCode_le_dual_of_add_lt hdegree hfullX
  have hkeptLogical : restrictKept m w fullLogical =
      keptSystematicLift h (canonicalBasisWord logical) := by
    change restrictKept m w
        (lowCoordinateExtension hwr (canonicalBasisWord logical)) =
      restrictKept m w (lowCoordinateExtension hwr (canonicalBasisWord logical))
    rfl
  calc
    wordPairing (keptSystematicLift h (canonicalBasisWord logical)) x =
        wordPairing (restrictKept m w fullLogical)
          (restrictKept m w fullX) := by
      rw [hkeptLogical, hkeptX]
    _ = wordPairing (restrictKept m w fullX)
          (restrictKept m w fullLogical) := by
      simp only [wordPairing_apply]
      exact dotProduct_comm _ _
    _ = wordPairing fullX fullLogical :=
      wordPairing_restrictKept_eq_of_restrictLow_eq_zero
        fullX fullLogical hlowX
    _ = 0 :=
      (reedMullerCode r m).orthogonal_of_mem_dual hfullXDual hfullLogical

/-- Systematic logical basis representatives have the source-stated delta
pairing. -/
theorem logicalBasisWord_pairing {w r m : Nat}
    (h : Admissible w r m) (left right : LogicalSite m w) :
    wordPairing (logicalBasisWord h left) (logicalBasisWord h right) =
      if left = right then 1 else 0 := by
  classical
  rw [logicalBasisWord, logicalBasisWord,
    wordPairing_systematicKeptLift h]
  by_cases hsites : left = right
  · subst right
    simp [canonicalBasisWord, wordPairing_apply]
  · simp [canonicalBasisWord, wordPairing_apply, hsites]

/-- The physical `X` representative for a systematic logical basis label. -/
noncomputable def logicalXPauli {w r m : Nat}
    (h : Admissible w r m) (logical : LogicalSite m w) :
    PauliSymplectic.Binary (PhysicalSite m w) :=
  cssXCheck (logicalBasisWord h logical)

/-- The physical `Z` representative for a systematic logical basis label. -/
noncomputable def logicalZPauli {w r m : Nat}
    (h : Admissible w r m) (logical : LogicalSite m w) :
    PauliSymplectic.Binary (PhysicalSite m w) :=
  cssZCheck (logicalBasisWord h logical)

/-- A logical `X` representative commutes with every X-type stabilizer. -/
theorem logicalXPauli_commutes_xCheck {w r m : Nat}
    (h : Admissible w r m) (logical : LogicalSite m w)
    {x : Word (ZMod 2) (PhysicalSite m w)}
    (_hx : x ∈ (xCode w r m).carrier) :
    PauliSymplectic.Commutes (logicalXPauli h logical) (cssXCheck x) :=
  cssXCheck_commutes_cssXCheck _ _

/-- A logical `X` representative commutes with every Z-type stabilizer. -/
theorem logicalXPauli_commutes_zCheck {w r m : Nat}
    (h : Admissible w r m) (logical : LogicalSite m w)
    {z : Word (ZMod 2) (PhysicalSite m w)}
    (hz : z ∈ (zCode w r m).carrier) :
    PauliSymplectic.Commutes (logicalXPauli h logical) (cssZCheck z) := by
  have hpair := (zCode w r m).orthogonal_of_mem_dual
    (logicalBasisWord_mem_zDual h logical) hz
  simpa [logicalXPauli, cssXCheck, cssZCheck, PauliSymplectic.Commutes,
    symplecticForm_x_zero_zero_z_eq_wordPairing] using hpair

/-- A logical `Z` representative commutes with every Z-type stabilizer. -/
theorem logicalZPauli_commutes_zCheck {w r m : Nat}
    (h : Admissible w r m) (logical : LogicalSite m w)
    {z : Word (ZMod 2) (PhysicalSite m w)}
    (_hz : z ∈ (zCode w r m).carrier) :
    PauliSymplectic.Commutes (logicalZPauli h logical) (cssZCheck z) :=
  cssZCheck_commutes_cssZCheck _ _

/-- A logical `Z` representative commutes with every X-type stabilizer. -/
theorem logicalZPauli_commutes_xCheck {w r m : Nat}
    (h : Admissible w r m) (logical : LogicalSite m w)
    {x : Word (ZMod 2) (PhysicalSite m w)}
    (hx : x ∈ (xCode w r m).carrier) :
    PauliSymplectic.Commutes (logicalZPauli h logical) (cssXCheck x) :=
  cssZCheck_commutes_cssXCheck_of_mem_dual (xCode w r m)
    hx (logicalBasisWord_mem_xDual h logical)

/-- The chosen logical Pauli representatives commute precisely off the
logical-basis diagonal. -/
theorem logicalXPauli_commutes_logicalZPauli_iff {w r m : Nat}
    (h : Admissible w r m) (left right : LogicalSite m w) :
    PauliSymplectic.Commutes (logicalXPauli h left) (logicalZPauli h right) ↔
      left ≠ right := by
  classical
  simp only [logicalXPauli, logicalZPauli, PauliSymplectic.Commutes,
    symplecticForm_x_zero_zero_z_eq_wordPairing,
    logicalBasisWord_pairing h]
  by_cases hsites : left = right <;> simp [hsites]

/-- The exact number of retained HH18 physical coordinates. -/
theorem cssLength {w r m : Nat} (_h : Admissible w r m) :
    Length (ZMod 2) (PhysicalSite m w) = binomialTail m w := by
  simpa [Length] using keptPoint_card_eq_binomialTail m w

/-- The exact binary-CSS logical exponent of the HH18 construction. -/
theorem cssLogicalExponent {w r m : Nat} (h : Admissible w r m) :
    Length (ZMod 2) (PhysicalSite m w) - Dimension (xCode w r m) -
        Dimension (zCode w r m) = binomialUpTo m w := by
  have hfinrank := (logicalWordEquivQuotient h).finrank_eq
  rw [finrank_word_eq_length,
    finrank_binaryCSSLogicalBasisQuotient_eq
      (xCode w r m) (zCode w r m) (cssDualContainment h)] at hfinrank
  calc
    Length (ZMod 2) (PhysicalSite m w) - Dimension (xCode w r m) -
        Dimension (zCode w r m) = Length (ZMod 2) (LogicalSite m w) :=
      hfinrank.symm
    _ = Fintype.card (LogicalSite m w) := rfl
    _ = binomialUpTo m w := by
      simpa [binomialUpTo] using lowPoint_card_eq_sum_choose m w

/-- The actual CSS carrier has the expected finite logical dimension. -/
theorem cssCarrierFinrank {w r m : Nat} (h : Admissible w r m) :
    Module.finrank Complex (cssCode h).stabilizer.code.carrier =
      2 ^ binomialUpTo m w := by
  rw [show (cssCode h).stabilizer.code =
      binaryCSSQuantumCodeOfDualLe (xCode w r m) (zCode w r m)
        (cssDualContainment h) by rfl]
  rw [binaryCSSQuantumCodeOfDualLe_finrank_carrier,
    cssLogicalExponent h]

/-- Finite CSS parameters and the already-proved common semantic distance,
all packaged for the actual HH18 code. -/
theorem cssParameters {w r m : Nat} (h : Admissible w r m) :
    Length (ZMod 2) (PhysicalSite m w) = binomialTail m w ∧
      Length (ZMod 2) (PhysicalSite m w) - Dimension (xCode w r m) -
          Dimension (zCode w r m) = binomialUpTo m w ∧
        Module.finrank Complex (cssCode h).stabilizer.code.carrier =
          2 ^ binomialUpTo m w ∧
        StabilizerCode.SemanticStabilizerDistance (sourceValidStabilizer h)
          (binomialTail (r + 1) w) :=
  ⟨cssLength h, cssLogicalExponent h, cssCarrierFinrank h, semanticDistance h⟩

/-- The HH18 code as a genuine logical-to-physical encoded code. -/
noncomputable def encodedCode {w r m : Nat} (h : Admissible w r m) :
    EncodedCode (Qubit.QubitRegister (LogicalSite m w))
      (Qubit.QubitRegister (PhysicalSite m w)) where
  code := (cssCode h).stabilizer.code
  encoding := encoding h

@[simp]
theorem encodedCode_code {w r m : Nat} (h : Admissible w r m) :
    (encodedCode h).code = (cssCode h).stabilizer.code :=
  rfl

@[simp]
theorem encodedCode_encoding {w r m : Nat} (h : Admissible w r m) :
    (encodedCode h).encoding = encoding h :=
  rfl

/-- The HH18 physical phase angle with denominator `2^nu`. -/
def phaseAngle (nu : Nat) : Real :=
  (2 * Real.pi) / ((2 ^ nu : Nat) : Real)

/-- A Ward-divisible physical/logical weight sum identifies the positive
physical phase with the negative logical phase. -/
theorem phaseAmplitude_eq_neg_of_weight_add_dvd {w m nu : Nat}
    (physical : Word (ZMod 2) (PhysicalSite m w))
    (logical : Word (ZMod 2) (LogicalSite m w))
    (hdiv : 2 ^ nu ∣ HammingWeight physical + HammingWeight logical) :
    OneQubitMagic.phaseAmplitude
        (phaseAngle nu * (HammingWeight physical : Real)) =
      OneQubitMagic.phaseAmplitude
        (-phaseAngle nu * (HammingWeight logical : Real)) := by
  rcases hdiv with ⟨k, hk⟩
  have hangle :
      phaseAngle nu * (HammingWeight physical : Real) =
        -phaseAngle nu * (HammingWeight logical : Real) +
          (2 * Real.pi) * (k : Real) := by
    calc
      phaseAngle nu * (HammingWeight physical : Real) =
          phaseAngle nu *
              ((HammingWeight physical + HammingWeight logical : Nat) : Real) -
            phaseAngle nu * (HammingWeight logical : Real) := by
              push_cast
              ring
      _ = phaseAngle nu * ((2 ^ nu * k : Nat) : Real) -
            phaseAngle nu * (HammingWeight logical : Real) := by rw [hk]
      _ = -phaseAngle nu * (HammingWeight logical : Real) +
            (2 * Real.pi) * (k : Real) := by
              unfold phaseAngle
              push_cast
              have hdenominator : ((2 ^ nu : Nat) : Real) ≠ 0 := by positivity
              field_simp [hdenominator]
              ring
  have hperiod :
      OneQubitMagic.phaseAmplitude ((2 * Real.pi) * (k : Real)) = 1 := by
    simpa using OneQubitMagic.phaseAmplitude_two_pi_mul_int (k : Int)
  rw [hangle, OneQubitMagic.phaseAmplitude_add, hperiod, mul_one]

/-- Every actual representative of a systematic HH18 quotient class has the
Ward-divisible physical-plus-logical Hamming weight. -/
theorem cosetWeightDivisible {w r m nu : Nat}
    (h : Admissible w r m) (hdegree : nu * r < m)
    (logical : Word (ZMod 2) (LogicalSite m w))
    (physical : (zCode w r m).dual.carrier)
    (hcoset : (Submodule.Quotient.mk physical : LogicalQuotient w r m) =
      logicalWordToQuotient h logical) :
    2 ^ nu ∣ HammingWeight (physical : Word (ZMod 2) (PhysicalSite m w)) +
      HammingWeight logical := by
  rw [logicalWordToQuotient_apply] at hcoset
  have hresidual := (Submodule.Quotient.eq
    (binaryCSSXCodeInZDual (xCode w r m) (zCode w r m))).mp hcoset
  change (physical : Word (ZMod 2) (PhysicalSite m w)) -
      keptSystematicLift h logical ∈ (xCode w r m).carrier at hresidual
  rw [xCode_eq_shortened] at hresidual
  exact systematicCoset_weight_add_logical_dvd h hdegree logical hresidual

/-- The actual all-site phase action on an HH18 quotient representative is
the negative phase of its logical low-coordinate word. -/
theorem cosetPhase {w r m nu : Nat}
    (h : Admissible w r m) (hdegree : nu * r < m)
    (logical : Word (ZMod 2) (LogicalSite m w))
    (physical : (zCode w r m).dual.carrier)
    (hcoset : (Submodule.Quotient.mk physical : LogicalQuotient w r m) =
      logicalWordToQuotient h logical)
    (psi : Qubit.QubitRegister (PhysicalSite m w))
    (bits : Qubit.Bitstring (PhysicalSite m w))
    (hbits : bitstringWordEquiv (PhysicalSite m w) bits = physical) :
    Triorthogonal.allSitePhase (Index := PhysicalSite m w) (phaseAngle nu) psi bits =
      OneQubitMagic.phaseAmplitude
        (-phaseAngle nu * (HammingWeight logical : Real)) * psi bits := by
  rw [Triorthogonal.allSitePhase_apply]
  have hphase := phaseAmplitude_eq_neg_of_weight_add_dvd
    (physical := (physical : Word (ZMod 2) (PhysicalSite m w)))
    (logical := logical)
    (cosetWeightDivisible h hdegree logical physical hcoset)
  rw [hbits]
  rw [hphase]

/-- The positive physical all-site phase at the HH18 denominator `2^nu`. -/
noncomputable def physicalAllSitePhase (w m nu : Nat) :
    UnitaryTransport (Qubit.QubitRegister (PhysicalSite m w))
      (Qubit.QubitRegister (PhysicalSite m w)) :=
  Triorthogonal.allSitePhase (Index := PhysicalSite m w) (phaseAngle nu)

/-- The simultaneous negative all-site phase on the HH18 logical register. -/
noncomputable def logicalAllSitePhase (w m nu : Nat) :
    UnitaryTransport (Qubit.QubitRegister (LogicalSite m w))
      (Qubit.QubitRegister (LogicalSite m w)) :=
  Triorthogonal.allSitePhase (Index := LogicalSite m w) (-phaseAngle nu)

/-- The actual HH18 encoding intertwines the positive physical all-site phase
with the simultaneous negative logical all-site phase. -/
theorem phaseIntertwinesEncoding {w r m nu : Nat}
    (h : Admissible w r m) (hdegree : nu * r < m)
    (psi : Qubit.QubitRegister (LogicalSite m w)) :
    physicalAllSitePhase w m nu
        (encoding h psi : Qubit.QubitRegister (PhysicalSite m w)) =
      (encoding h (logicalAllSitePhase w m nu psi) :
        Qubit.QubitRegister (PhysicalSite m w)) := by
  ext bits
  by_cases hbits : bitstringWordEquiv (PhysicalSite m w) bits ∈
      (zCode w r m).dual.carrier
  · let physical : (zCode w r m).dual.carrier :=
      ⟨bitstringWordEquiv (PhysicalSite m w) bits, hbits⟩
    let logicalBits : Qubit.Bitstring (LogicalSite m w) :=
      (logicalBasisEquivQuotient h).symm (Submodule.Quotient.mk physical)
    let logical : Word (ZMod 2) (LogicalSite m w) :=
      bitstringWordEquiv (LogicalSite m w) logicalBits
    have hcoset :
        (Submodule.Quotient.mk physical : LogicalQuotient w r m) =
          logicalWordToQuotient h logical := by
      rw [← logicalWordEquivQuotient_apply h logical]
      change (Submodule.Quotient.mk physical : LogicalQuotient w r m) =
        logicalBasisEquivQuotient h logicalBits
      exact ((logicalBasisEquivQuotient h).apply_symm_apply
        (Submodule.Quotient.mk physical)).symm
    have hphysical : bitstringWordEquiv (PhysicalSite m w) bits = physical :=
      rfl
    calc
      physicalAllSitePhase w m nu
          (encoding h psi : Qubit.QubitRegister (PhysicalSite m w)) bits =
          OneQubitMagic.phaseAmplitude
              (-phaseAngle nu * (HammingWeight logical : Real)) *
            (encoding h psi : Qubit.QubitRegister (PhysicalSite m w)) bits := by
              exact cosetPhase h hdegree logical physical hcoset
                (encoding h psi : Qubit.QubitRegister (PhysicalSite m w)) bits hphysical
      _ = OneQubitMagic.phaseAmplitude
              (-phaseAngle nu * (HammingWeight logical : Real)) *
            (cssNormalizationScalar h * psi logicalBits) := by
              rw [encoding_apply_of_mem h psi hbits]
      _ = cssNormalizationScalar h *
            (logicalAllSitePhase w m nu psi) logicalBits := by
              rw [logicalAllSitePhase, Triorthogonal.allSitePhase_apply]
              change OneQubitMagic.phaseAmplitude
                  (-phaseAngle nu * (HammingWeight logical : Real)) *
                    (cssNormalizationScalar h * psi logicalBits) =
                cssNormalizationScalar h *
                  (OneQubitMagic.phaseAmplitude
                    (-phaseAngle nu * (HammingWeight logical : Real)) *
                    psi logicalBits)
              ring
      _ = (encoding h (logicalAllSitePhase w m nu psi) :
            Qubit.QubitRegister (PhysicalSite m w)) bits := by
              rw [encoding_apply_of_mem h
                (logicalAllSitePhase w m nu psi) hbits]
  · rw [physicalAllSitePhase, Triorthogonal.allSitePhase_apply,
      encoding_apply_of_not_mem h psi hbits,
      encoding_apply_of_not_mem h (logicalAllSitePhase w m nu psi) hbits]
    simp

/-- The positive physical phase implements the negative logical phase on the
actual HH18 encoded code. -/
theorem physicalAllSitePhase_implements_logicalAllSitePhase {w r m nu : Nat}
    (h : Admissible w r m) (hdegree : nu * r < m) :
    (encodedCode h).ImplementsLogicalGate
      (physicalAllSitePhase w m nu) (logicalAllSitePhase w m nu) := by
  intro psi
  change physicalAllSitePhase w m nu
      (encoding h psi : Qubit.QubitRegister (PhysicalSite m w)) =
    (encoding h (logicalAllSitePhase w m nu psi) :
      Qubit.QubitRegister (PhysicalSite m w))
  exact phaseIntertwinesEncoding h hdegree psi

/-- The HH18 phase implementation together with its literal singleton-site
factorization. -/
noncomputable def sitewisePhaseTransversalLogicalGate {w r m nu : Nat}
    (h : Admissible w r m) (hdegree : nu * r < m) :
    SitewiseTransversalLogicalGate (encodedCode h)
      (logicalAllSitePhase w m nu)
      (Triorthogonal.diagonalPhaseGateModel (Index := PhysicalSite m w)) where
  physicalGate := physicalAllSitePhase w m nu
  implements := physicalAllSitePhase_implements_logicalAllSitePhase h hdegree
  transversality := by
    simpa only [physicalAllSitePhase] using
      (Triorthogonal.allSitePhaseTransversality
        (Index := PhysicalSite m w) (phaseAngle nu))

/-- The HH18 denominator-three angle is exactly the standard `T` angle. -/
theorem phaseAngle_three : phaseAngle 3 = Real.pi / 4 := by
  norm_num [phaseAngle]
  ring

/-- The positive physical HH18 phase at `nu = 3`, namely simultaneous `T`. -/
noncomputable def physicalT (w m : Nat) :
    UnitaryTransport (Qubit.QubitRegister (PhysicalSite m w))
      (Qubit.QubitRegister (PhysicalSite m w)) :=
  physicalAllSitePhase w m 3

/-- The negative logical HH18 phase at `nu = 3`, namely simultaneous `T†`. -/
noncomputable def logicalTInv (w m : Nat) :
    UnitaryTransport (Qubit.QubitRegister (LogicalSite m w))
      (Qubit.QubitRegister (LogicalSite m w)) :=
  logicalAllSitePhase w m 3

/-- The named HH18 physical `T` is the generic raw all-site `T` transport. -/
theorem physicalT_eq_allSiteT (w m : Nat) :
    physicalT w m = Triorthogonal.allSiteT (Index := PhysicalSite m w) := by
  simp only [physicalT, physicalAllSitePhase, phaseAngle_three,
    Triorthogonal.allSiteT]

/-- The named HH18 logical inverse-`T` is the negative `π/4` all-site phase. -/
theorem logicalTInv_eq_allSitePhase_neg_pi_div_four (w m : Nat) :
    logicalTInv w m =
      Triorthogonal.allSitePhase (Index := LogicalSite m w) (-Real.pi / 4) := by
  simp only [logicalTInv, logicalAllSitePhase, phaseAngle_three]
  congr 1
  ring

/-- Simultaneous physical `T` implements simultaneous logical `T†` on HH18. -/
theorem physicalT_implements_logicalTInv {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    (encodedCode h).ImplementsLogicalGate (physicalT w m) (logicalTInv w m) := by
  simpa only [physicalT, logicalTInv] using
    (physicalAllSitePhase_implements_logicalAllSitePhase
      (nu := 3) h hdegree)

/-- The physical HH18 `T` implementation with its singleton-site factors. -/
noncomputable def physicalT_sitewise_transversal {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    SitewiseTransversalLogicalGate (encodedCode h) (logicalTInv w m)
      (Triorthogonal.diagonalPhaseGateModel (Index := PhysicalSite m w)) := by
  simpa only [physicalT, logicalTInv] using
    (sitewisePhaseTransversalLogicalGate (nu := 3) h hdegree)

/-- The inverse named physical transport is defined by the unitary inverse. -/
noncomputable def physicalTInv (w m : Nat) :
    UnitaryTransport (Qubit.QubitRegister (PhysicalSite m w))
      (Qubit.QubitRegister (PhysicalSite m w)) :=
  (physicalT w m).symm

/-- The inverse named logical transport is defined by the unitary inverse. -/
noncomputable def logicalT (w m : Nat) :
    UnitaryTransport (Qubit.QubitRegister (LogicalSite m w))
      (Qubit.QubitRegister (LogicalSite m w)) :=
  (logicalTInv w m).symm

/-- Simultaneous physical `T†` implements simultaneous logical `T` on HH18. -/
theorem physicalTInv_implements_logicalT {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    (encodedCode h).ImplementsLogicalGate (physicalTInv w m) (logicalT w m) := by
  simpa only [physicalTInv, logicalT] using
    (EncodedCode.ImplementsLogicalGate.symm (encodedCode h)
      (physicalT_implements_logicalTInv h hdegree))


end HH18PuncturedReedMuller
end Distillation
end QEC
