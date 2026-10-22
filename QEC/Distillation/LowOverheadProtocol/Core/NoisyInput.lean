import QEC.Coding.Stabilizer.PauliSemantics
import QEC.Distillation.LowOverheadProtocol.Core.PuncturedReedMuller
import QEC.Distillation.Core.MagicStateProtocol
import QEC.Distillation.Universality.OneQubitPhase
import QEC.Semantics.Entropy.Convexity
/-!
# HH18 independent diagonal noisy inputs

This module constructs the first physical-input layer for the HH18
distillation route. A single resource is the equatorial `T†` injection state
`phaseState (-pi / 4)` and its Pauli-`Z` error. A finite register is the
literal mixture over binary error words, with product Bernoulli weights and
actual Pauli-`Z` word operators acting on the product phase-resource state.

No syndrome measurement, postselection, decoder, error bound, or
concatenation conclusion is introduced here.  In particular, the subsequent
protocol layer must use the #759 inverse orientation: physical `T†` implements
logical `T`.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18NoisyInput

open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open OneQubitMagic
open scoped BigOperators

universe u

/-- The diagonal error-rate domain used by HH18: `0 <= epsilon <= 1/2`. -/
abbrev DiagonalErrorRate := Set.Icc (0 : Real) (1 / 2)

/-- A binary Pauli-`Z` error word on the physical sites of an HH18 block. -/
abbrev PhysicalErrorWord (m w : Nat) :=
  Word (ZMod 2) (HH18PuncturedReedMuller.PhysicalSite m w)

/-- One Bernoulli factor: no error has weight `1-epsilon`, and `Z` has weight
`epsilon`. -/
def bitErrorWeight (epsilon : DiagonalErrorRate) (error : ZMod 2) : Real :=
  if error = 0 then 1 - epsilon.1 else epsilon.1

theorem bitErrorWeight_nonneg (epsilon : DiagonalErrorRate) (error : ZMod 2) :
    0 <= bitErrorWeight epsilon error := by
  unfold bitErrorWeight
  split_ifs
  · linarith [epsilon.property.2]
  · exact epsilon.property.1

private theorem sum_binary (f : ZMod 2 -> Real) :
    (∑ bit, f bit) = f 0 + f 1 := by
  calc
    (∑ bit : ZMod 2, f bit) =
        ∑ index : Fin 2, f (ZMod.finEquiv 2 index) := by
      exact Fintype.sum_equiv (ZMod.finEquiv 2).toEquiv.symm _ _ (fun _ => rfl)
    _ = f 0 + f 1 := by
      rw [Fin.sum_univ_two]
      norm_num

theorem bitErrorWeight_sum (epsilon : DiagonalErrorRate) :
    ∑ error : ZMod 2, bitErrorWeight epsilon error = 1 := by
  rw [sum_binary]
  simp [bitErrorWeight]

/-- The equatorial resource that injects physical `T†` in the #759 inverse route. -/
def idealTInvResourceState : QubitSpace :=
  OneQubitMagic.phaseState (-Real.pi / 4)

theorem idealTInvResourceState_ne_zero : idealTInvResourceState ≠ 0 := by
  simpa [idealTInvResourceState] using
    OneQubitMagic.phaseState_ne_zero (-Real.pi / 4)

/-- The `Z`-flipped equatorial resource is exactly orthogonal to the ideal one. -/
theorem idealTInvResourceState_pauliZ_orthogonal :
    inner Complex idealTInvResourceState (pauliZ idealTInvResourceState) = 0 := by
  rw [PiLp.inner_apply]
  simp only [idealTInvResourceState, Fin.sum_univ_two,
    OneQubitMagic.phaseState_apply_zero, OneQubitMagic.phaseState_apply_one,
    RCLike.inner_apply, pauliZ_apply, zPhase_zero, zPhase_one, one_mul,
    neg_one_mul, map_neg, map_mul, map_inv₀, Complex.conj_ofReal]
  calc
    (Real.sqrt 2 : Complex)⁻¹ * (Real.sqrt 2 : Complex)⁻¹ +
        -((Real.sqrt 2 : Complex)⁻¹ * phaseAmplitude (-Real.pi / 4)) *
          ((Real.sqrt 2 : Complex)⁻¹ * star (phaseAmplitude (-Real.pi / 4))) =
        (Real.sqrt 2 : Complex)⁻¹ * (Real.sqrt 2 : Complex)⁻¹ -
          ((Real.sqrt 2 : Complex)⁻¹ * (Real.sqrt 2 : Complex)⁻¹) *
            (phaseAmplitude (-Real.pi / 4) * star (phaseAmplitude (-Real.pi / 4))) := by
          ring
    _ = 0 := by
      rw [OneQubitMagic.phaseAmplitude_mul_conj]
      ring

/-- The actual one-qubit phase resource after the selected diagonal error. -/
def tInvResourceErrorState (error : ZMod 2) : QubitSpace :=
  if error = 0 then idealTInvResourceState else pauliZ idealTInvResourceState

theorem tInvResourceErrorState_ne_zero (error : ZMod 2) :
    tInvResourceErrorState error ≠ 0 := by
  by_cases herror : error = 0
  · simpa [tInvResourceErrorState, herror] using idealTInvResourceState_ne_zero
  · intro hzero
    have hflipped : pauliZ idealTInvResourceState = 0 := by
      simpa [tInvResourceErrorState, herror] using hzero
    have hrecover : pauliZ (pauliZ idealTInvResourceState) =
        idealTInvResourceState := by
      simpa only [Module.End.mul_apply, Module.End.one_apply] using
        LinearMap.congr_fun pauliZ_square idealTInvResourceState
    rw [hflipped] at hrecover
    simp only [map_zero] at hrecover
    exact idealTInvResourceState_ne_zero hrecover.symm

/-- The normalized one-qubit density after the selected diagonal error. -/
noncomputable def tInvResourceErrorDensity (error : ZMod 2) :
    DensityOperator QubitSpace :=
  DensityOperator.pureOfNonzero
    (tInvResourceErrorState error) (tInvResourceErrorState_ne_zero error)

@[simp]
theorem tInvResourceErrorDensity_zero :
    tInvResourceErrorDensity 0 = OneQubitMagic.phaseStateDensity (-Real.pi / 4) := by
  rfl

/-- The zero-error resource is the exact `T†` phase-injection density. -/
theorem tInvResourceErrorDensity_zero_eq_phaseStateDensity :
    tInvResourceErrorDensity 0 = OneQubitMagic.phaseStateDensity (-Real.pi / 4) :=
  tInvResourceErrorDensity_zero

/-- One actual noisy diagonal `T†` injection resource. -/
noncomputable def noisyTInvResource (epsilon : DiagonalErrorRate) :
    DensityOperator QubitSpace :=
  DensityOperator.convexCombination Finset.univ
    (bitErrorWeight epsilon) tInvResourceErrorDensity
    (by
      intro error _herror
      exact bitErrorWeight_nonneg epsilon error)
    (by simpa using bitErrorWeight_sum epsilon)

/-- The homogeneous resource family consumed by the shared protocol API. -/
noncomputable def noisyTInvResources (count : Nat) (epsilon : DiagonalErrorRate) :
    ResourceInput count QubitSpace :=
  fun _ => noisyTInvResource epsilon

/-- The normalized product-vector representative of ideal `T†` injection
resources on a finite register. -/
def idealTInvResourceRegister {ι : Type u} [Fintype ι] : QubitRegister ι :=
  WithLp.toLp 2 fun bits => ∏ i, idealTInvResourceState (bits i)

theorem idealTInvResourceRegister_ne_zero {ι : Type u} [Fintype ι] :
    idealTInvResourceRegister (ι := ι) ≠ 0 := by
  classical
  have hzero : idealTInvResourceState 0 ≠ 0 := by
    rw [idealTInvResourceState, OneQubitMagic.phaseState_apply_zero]
    have hsqrt_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
      exact_mod_cast sqrt_two_pos.ne'
    exact inv_ne_zero hsqrt_ne
  have hproduct : (∏ _i : ι, idealTInvResourceState 0) ≠ 0 := by
    simp [hzero]
  intro hzero
  have hcoordinate :=
    congrArg (fun psi : QubitRegister ι => psi (fun _ => 0)) hzero
  apply hproduct
  simpa [idealTInvResourceRegister] using hcoordinate

/-- The concrete register Pauli represented by a binary `Z` error word. -/
def zErrorOperator {ι : Type u} [Fintype ι] [DecidableEq ι]
    (error : Word (ZMod 2) ι) : Operator (QubitRegister ι) :=
  PauliSymplectic.toQubitOperator (PauliSymplectic.cssZCheck error)

/-- The actual error-word branch obtained by applying its Pauli operator to
the ideal product phase-resource vector. -/
def errorWordState {ι : Type u} [Fintype ι] [DecidableEq ι]
    (error : Word (ZMod 2) ι) : QubitRegister ι :=
  zErrorOperator error (idealTInvResourceRegister (ι := ι))

theorem errorWordState_ne_zero {ι : Type u} [Fintype ι] [DecidableEq ι]
    (error : Word (ZMod 2) ι) : errorWordState error ≠ 0 := by
  intro hzero
  have hrecover := LinearMap.congr_fun
    (PauliSymplectic.toQubitOperator_adjoint_comp_self
      (PauliSymplectic.cssZCheck error))
    (idealTInvResourceRegister (ι := ι))
  simp only [LinearMap.comp_apply, Module.End.one_apply] at hrecover
  have happlied :
      PauliSymplectic.toQubitOperator (PauliSymplectic.cssZCheck error)
          (idealTInvResourceRegister (ι := ι)) = 0 := by
    simpa [errorWordState, zErrorOperator] using hzero
  rw [happlied] at hrecover
  simp only [map_zero] at hrecover
  exact idealTInvResourceRegister_ne_zero hrecover.symm

/-- The normalized density of one concrete physical error-word branch. -/
noncomputable def errorWordDensity {ι : Type u} [Fintype ι] [DecidableEq ι]
    (error : Word (ZMod 2) ι) : DensityOperator (QubitRegister ι) :=
  DensityOperator.pureOfNonzero
    (errorWordState error) (errorWordState_ne_zero error)

/-- The independent Bernoulli mass of a complete physical error word. -/
def errorWordWeight {ι : Type u} [Fintype ι]
    (epsilon : DiagonalErrorRate) (error : Word (ZMod 2) ι) : Real :=
  ∏ i, bitErrorWeight epsilon (error i)

/-- The literal product law separates the error support from its complement.
This is an identity for the actual diagonal resource distribution, not an
enumerator supplied to a later protocol layer. -/
theorem errorWordWeight_eq_hammingWeight {ι : Type u} [Fintype ι] [DecidableEq ι]
    (epsilon : DiagonalErrorRate) (error : Word (ZMod 2) ι) :
    errorWordWeight epsilon error =
      epsilon.1 ^ HammingWeight error *
        (1 - epsilon.1) ^ (Fintype.card ι - HammingWeight error) := by
  classical
  let support := hammingSupport error
  have hdisjoint : Disjoint support (Finset.univ \ support) := by
    exact Finset.disjoint_sdiff
  have hunion : support ∪ (Finset.univ \ support) = Finset.univ := by
    simp
  have hsupp_card : support.card = HammingWeight error := by
    rfl
  have hcompl_card : (Finset.univ \ support).card =
      Fintype.card ι - HammingWeight error := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ support),
      Finset.card_univ, hsupp_card]
  calc
    errorWordWeight epsilon error =
        (∏ site ∈ support, bitErrorWeight epsilon (error site)) *
          (∏ site ∈ Finset.univ \ support,
            bitErrorWeight epsilon (error site)) := by
      rw [errorWordWeight, ← Finset.prod_union hdisjoint, hunion]
    _ = (∏ _site ∈ support, epsilon.1) *
          ∏ _site ∈ Finset.univ \ support, (1 - epsilon.1) := by
      have hsupp :
          (∏ site ∈ support, bitErrorWeight epsilon (error site)) =
            ∏ _site ∈ support, epsilon.1 := by
        apply Finset.prod_congr rfl
        intro site hsite
        have hnonzero : error site ≠ 0 := by
          simpa [support, hammingSupport] using hsite
        simp [bitErrorWeight, hnonzero]
      have hcompl :
          (∏ site ∈ Finset.univ \ support,
            bitErrorWeight epsilon (error site)) =
            ∏ _site ∈ Finset.univ \ support, (1 - epsilon.1) := by
        apply Finset.prod_congr rfl
        intro site hsite
        have hzero : error site = 0 := by
          by_contra hnonzero
          exact (Finset.mem_sdiff.mp hsite).2
            (by simp [support, hammingSupport, hnonzero])
        simp [bitErrorWeight, hzero]
      rw [hsupp, hcompl]
    _ = epsilon.1 ^ HammingWeight error *
          (1 - epsilon.1) ^ (Fintype.card ι - HammingWeight error) := by
      simp [hsupp_card, hcompl_card]

theorem errorWordWeight_nonneg {ι : Type u} [Fintype ι]
    (epsilon : DiagonalErrorRate) (error : Word (ZMod 2) ι) :
    0 <= errorWordWeight epsilon error := by
  classical
  unfold errorWordWeight
  apply Finset.prod_nonneg
  intro i _hi
  exact bitErrorWeight_nonneg epsilon (error i)

theorem errorWordWeight_sum {ι : Type u} [Fintype ι] [DecidableEq ι]
    (epsilon : DiagonalErrorRate) :
    ∑ error : Word (ZMod 2) ι, errorWordWeight epsilon error = 1 := by
  classical
  unfold errorWordWeight
  rw [← Fintype.prod_sum]
  simp [bitErrorWeight_sum]

/-- The independent diagonal noisy input on a finite qubit register, expanded
as an actual convex mixture over all binary physical error words. -/
noncomputable def independentNoisyTRegister {ι : Type u}
    [Fintype ι] [DecidableEq ι] (epsilon : DiagonalErrorRate) :
    DensityOperator (QubitRegister ι) :=
  DensityOperator.convexCombination Finset.univ
    (errorWordWeight epsilon) errorWordDensity
    (by
      intro error _herror
      exact errorWordWeight_nonneg epsilon error)
    (by simpa using errorWordWeight_sum (ι := ι) epsilon)

@[simp]
theorem independentNoisyTRegister_toOperator {ι : Type u}
    [Fintype ι] [DecidableEq ι] (epsilon : DiagonalErrorRate) :
    (independentNoisyTRegister (ι := ι) epsilon).toOperator =
      ∑ error : Word (ZMod 2) ι,
        (errorWordWeight epsilon error : Complex) •
          (errorWordDensity error).toOperator := by
  simp [independentNoisyTRegister,
    DensityOperator.convexCombinationOperator]

/-- The route-local independent noisy input on the physical sites of an HH18
punctured Reed--Muller block. -/
noncomputable def hh18NoisyInput (epsilon : DiagonalErrorRate) (m w : Nat) :
    DensityOperator
      (QubitRegister (HH18PuncturedReedMuller.PhysicalSite m w)) :=
  independentNoisyTRegister epsilon

/-- The concrete `m = 4`, `r = 1`, `w = 0` HH18 block is admissible. -/
theorem hh18_15_1_0_admissible : Admissible 0 1 4 := by
  norm_num [Admissible]

/-- The consumed #759 construction really supplies the `[[15,1,3]]` carrier,
not an input-supplied code parameter. -/
theorem hh18_15_1_0_parameters :
    Length (ZMod 2) (HH18PuncturedReedMuller.PhysicalSite 4 0) = 15 ∧
      Length (ZMod 2) (HH18PuncturedReedMuller.PhysicalSite 4 0) -
          Dimension (HH18PuncturedReedMuller.xCode 0 1 4) -
          Dimension (HH18PuncturedReedMuller.zCode 0 1 4) = 1 ∧
        Module.finrank Complex
            (HH18PuncturedReedMuller.cssCode hh18_15_1_0_admissible).stabilizer.code.carrier =
              2 ∧
          StabilizerCode.SemanticStabilizerDistance
            (HH18PuncturedReedMuller.sourceValidStabilizer
              hh18_15_1_0_admissible) 3 := by
  have hlength : binomialTail 4 0 = 15 := by native_decide
  have hlogical : Coding.ReedMuller.binomialUpTo 4 0 = 1 := by native_decide
  have hcarrier : 2 ^ Coding.ReedMuller.binomialUpTo 4 0 = 2 := by native_decide
  have hdistance : binomialTail (1 + 1) 0 = 3 := by native_decide
  simpa only [hlength, hlogical, hcarrier, hdistance, pow_one] using
    HH18PuncturedReedMuller.cssParameters hh18_15_1_0_admissible

/-- The independent `T†` phase-resource input mixture specialized to the
actual 15 physical sites. -/
noncomputable def hh18_15_1_0_noisyInput (epsilon : DiagonalErrorRate) :
    DensityOperator
      (QubitRegister (HH18PuncturedReedMuller.PhysicalSite 4 0)) :=
  hh18NoisyInput epsilon 4 0

/-- The real #759 encoded carrier for the concrete HH18 `[[15,1,3]]` block. -/
noncomputable def hh18_15_1_0_encodedCode :=
  HH18PuncturedReedMuller.encodedCode hh18_15_1_0_admissible

/-- The genuine logical `|+⟩` seed on the #759 logical register. It is
distinct from the independent physical phase-resource mixture. -/
noncomputable def hh18LogicalPlusInput :
    QubitRegister (HH18PuncturedReedMuller.LogicalSite 4 0) :=
  Triorthogonal.BinaryRowFamily.logicalPlusState
    (HH18PuncturedReedMuller.LogicalSite 4 0)

/-- The actual #759 encoding of the logical plus seed into the physical
15-site code carrier. -/
noncomputable def hh18EncodedLogicalPlusInput :
    QubitRegister (HH18PuncturedReedMuller.PhysicalSite 4 0) :=
  hh18_15_1_0_encodedCode.encode hh18LogicalPlusInput

/-- The orientation supplied by #759 for the actual 15-site encoding:
physical `T†` implements logical `T`. -/
theorem hh18PhysicalTInv_implements_logicalT :
    hh18_15_1_0_encodedCode.ImplementsLogicalGate
      (HH18PuncturedReedMuller.physicalTInv 0 4)
      (HH18PuncturedReedMuller.logicalT 0 4) := by
  simpa only [hh18_15_1_0_encodedCode] using
    (HH18PuncturedReedMuller.physicalTInv_implements_logicalT
      hh18_15_1_0_admissible (by norm_num))

/-- The error-free physical target branch used by the future resource consumer:
apply the actual transversal physical `T†` after #759 encoding. -/
noncomputable def hh18PhysicalTInvBranch :
    QubitRegister (HH18PuncturedReedMuller.PhysicalSite 4 0) :=
  HH18PuncturedReedMuller.physicalTInv 0 4 hh18EncodedLogicalPlusInput

/-- The concrete error-free target branch is exactly the #759 encoded logical
`T` action; this is an equality derived from transversality, not a field of a
protocol specification. -/
theorem hh18PhysicalTInvBranch_eq_logicalT :
    hh18PhysicalTInvBranch =
      hh18_15_1_0_encodedCode.encode
        (HH18PuncturedReedMuller.logicalT 0 4 hh18LogicalPlusInput) := by
  simpa only [hh18PhysicalTInvBranch, hh18EncodedLogicalPlusInput] using
    (hh18PhysicalTInv_implements_logicalT hh18LogicalPlusInput)

/-- The actual physical `Z`-error action on the encoded transversal target,
indexed by the same 15-site error word as `hh18_15_1_0_noisyInput`.  This is
only a branch state for the future finite-Kraus consumer, not a channel or a
postselected result. -/
noncomputable def hh18PhysicalTInvErrorBranch
    (error : PhysicalErrorWord 4 0) :
    QubitRegister (HH18PuncturedReedMuller.PhysicalSite 4 0) :=
  zErrorOperator error hh18PhysicalTInvBranch

end HH18NoisyInput
end Distillation
end QEC
