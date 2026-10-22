import QEC.Distillation.MultiplicativeQuditProtocol.NormalClosureDistance
import QEC.Distillation.MultiplicativeQuditProtocol.CubicPhase

/-!
# The fixed F256 qudit family with parallel cubic phase gates

This is the concrete specialization of Ngu24's qudit-family corollary:
`K = floor(n/10)`, `N = n-K`, and distance at least `ceil(n/5)-K`.
The quantum carriers and both encodings are the actual normalized coset
constructions, while every parameter and gate property is derived below.
-/

noncomputable section

namespace QEC.Distillation.Ngu24MultiplicativeCSS

open Coding Coding.AlgebraicGeometry.F256GarciaStichtenoth Semantics
open Ngu24MultiplicativeCCZ
open Filter
open scoped BigOperators Topology

section Native

local instance {J : Type} [Fintype J] : Fintype (Word F256 J) := Fintype.ofFinite _

/-- The actual retained physical length. -/
def f256QuditLength (i : ℕ) : ℕ :=
  f256GarciaStichtenothLength i - f256MultiplicationLogicalCount i

/-- The proved integer lower bound, not an assumed value of quantum distance. -/
def f256QuditDistanceBound (i : ℕ) : ℕ :=
  (f256GarciaStichtenothLength i + 4) / 5 - f256MultiplicationLogicalCount i

/-- The indexed source encoder with its actual range code. -/
def f256QuditEncodedCode (i : ℕ) :
    EncodedCode (ComputationalBasisRegister F256 (Fin (f256MultiplicationLogicalCount i)))
      (ComputationalBasisRegister F256 (f256SourceInput i).PivotComplement) :=
  (f256SourceInput i).encodedCode

/-- Physical coordinates are the actual complement, with no stored length witness. -/
theorem f256QuditLength_eq_card (i : ℕ) :
    f256QuditLength i = Fintype.card (f256SourceInput i).PivotComplement := by
  have h := (f256MultiplicationRetained_card i).symm
  simp only [← Nat.card_eq_fintype_card] at h ⊢
  exact h

/-- `K` is the number of logical qudits; the complex carrier dimension is `256^K`. -/
theorem f256QuditEncodedCode_dimension (i : ℕ) :
    (f256QuditEncodedCode i).code.dimension = 256 ^ f256MultiplicationLogicalCount i := by
  have h := (f256QuditEncodedCode i).encoding.toLinearEquiv.finrank_eq
  rw [finrank_euclideanSpace] at h
  change Fintype.card (Fin (f256MultiplicationLogicalCount i) → F256) =
    (f256QuditEncodedCode i).code.dimension at h
  rw [← Nat.card_eq_fintype_card, Nat.card_fun, Nat.card_fin,
    Nat.card_eq_fintype_card, f256_card] at h
  exact h.symm

/-- These are precisely the source's uniform coset CSS states, extended by linearity. -/
theorem f256QuditEncodedCode_carrier_eq_span (i : ℕ) :
    (f256QuditEncodedCode i).code.carrier =
      Submodule.span Complex (Set.range (f256SourceInput i).shortenedCosetKet) := by
  apply le_antisymm
  · rintro x ⟨psi, rfl⟩
    change (∑ u : Word F256 (Fin (f256MultiplicationLogicalCount i)),
      psi u • (f256SourceInput i).shortenedCosetKet u) ∈ _
    apply Submodule.sum_mem
    intro u _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨u, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨u, rfl⟩
    exact ⟨registerBasisKet u, (f256SourceInput i).encodingLinearMap_apply_logical_basis u⟩

/-- The actual retained lengths diverge along the proved explicit tower. -/
theorem f256QuditLength_tendsto_atTop : Tendsto f256QuditLength atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hn := (tendsto_atTop.1 f256GarciaStichtenothLength_tendsto_atTop) (2 * b)
  filter_upwards [hn] with i hi
  unfold f256QuditLength f256MultiplicationLogicalCount
  omega

theorem f256QuditDistanceBound_pos (i : ℕ) : 0 < f256QuditDistanceBound i := by
  have hn := f256GarciaStichtenothLength_two_hundred_forty_le i
  unfold f256QuditDistanceBound f256MultiplicationLogicalCount
  omega

/-- The source's rational distance estimate follows from the actual integer bound. -/
theorem f256QuditDistanceBound_source_lower (i : ℕ) :
    (f256GarciaStichtenothLength i : ℚ) / 5 - f256MultiplicationLogicalCount i ≤
      f256QuditDistanceBound i := by
  have hn := f256GarciaStichtenothLength_two_hundred_forty_le i
  have h : f256GarciaStichtenothLength i ≤
      5 * (f256QuditDistanceBound i + f256MultiplicationLogicalCount i) := by
    unfold f256QuditDistanceBound f256MultiplicationLogicalCount
    omega
  have hq := (show (f256GarciaStichtenothLength i : ℚ) ≤
      5 * (f256QuditDistanceBound i + f256MultiplicationLogicalCount i) by exact_mod_cast h)
  linarith

/-- The parameter bound is realized by standard semantic measurement distance. -/
theorem f256QuditEncodedCode_measurementDistance (i : ℕ) :
    QuditSubsystem.BPTMeasurementDistance
      ((f256QuditEncodedCode i).code.transport
        (FiniteAlphabet.registerUnitary F256 (f256SourceInput i).PivotComplement))
      (f256QuditDistanceBound i) :=
  f256SourceInput_measurementDistance i

end Native

local instance (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance : CharP F256 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2

/-- Every binary-linear cubic phase is implemented on all logical coordinates
through the actual full three-tag encoding equation. -/
theorem f256QuditFamily_cubic_implements_logical (i : ℕ)
    (f : F256 →ₗ[ZMod 2] ZMod 2) :
    (taggedEncodedCode (f256SourceInput i)).ImplementsLogicalGate
      (taggedCubicPhysicalTransport f)
      (taggedCubicPhaseTransport f Finset.univ) :=
  taggedCubicPhysicalTransport_implements_logical (f256SourceInput i) f

end QEC.Distillation.Ngu24MultiplicativeCSS
