import QEC.Coding.ChainComplex.Duality
import QEC.Coding.FourDimensionalToricCode.Decoder.RZCoarseGraining
import QEC.Coding.FourDimensionalToricCode.Decoder.RXCoarseGraining

/-!
# The terminating BDL26 multiscale decoder

This module assembles the already proved finite `R_Z` and `R_X` steps.  The
only hypotheses accepted by the assembly are per-level step functions and the
finite base right-inverse.  Termination, correction lifting, and the global
syndrome equation are derived here; no global correctness or termination
certificate is an input.
-/

namespace QEC
namespace Coding
namespace MultiscaleDecoder

open scoped BigOperators

universe u v w x y z

variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]

/-- The typed dual of a finite BDL26 cochain family.  Coordinates are reversed
`C², C¹, C⁰` and every level complex is replaced by the exact
transpose-boundary `dualChainComplex`; no untyped identification between the
two sectors is introduced. -/
noncomputable def BDL26CochainFamily.dual
    (F : BDL26CochainFamily depth C0 C1 C2) :
    BDL26CochainFamily depth C2 C1 C0 where
  complex := fun i => dualChainComplex (F.complex i)

abbrev TopIndex (depth : Nat) : LevelIndex depth :=
  ⟨depth, Nat.lt_succ_self depth⟩

structure AssemblyStepOutput
    (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth) :=
  input : D.family.Syndrome i.succ
  coarse : D.family.Syndrome i.castSucc
  correction : D.family.Correction i.succ
  /-- The local correction pieces retained for downstream provenance. -/
  localComponents : List (D.family.Correction i.succ)
  /-- Explicit support snapshots for the local pieces. -/
  componentSupports : List (Finset (C1 i.succ))
  /-- Explicit coboundary snapshots for the local pieces. -/
  componentCoboundaries : List (D.family.Cochain2 i.succ)
  relation : (input : D.family.Cochain2 i.succ) =
    D.family.coboundary1 i.succ correction +
      (D.selectedMap i).map2 coarse
  correction_decomposition : correction = localComponents.sum
  componentSupports_length : componentSupports.length = localComponents.length
  componentCoboundaries_length : componentCoboundaries.length = localComponents.length
  componentSupport_eq : ∀ (j : Fin localComponents.length),
    componentSupports.get ⟨j.val, by
      rw [componentSupports_length]
      exact j.isLt⟩ = hammingSupport (localComponents.get j)
  componentCoboundary_eq : ∀ (j : Fin localComponents.length),
    componentCoboundaries.get ⟨j.val, by
      rw [componentCoboundaries_length]
      exact j.isLt⟩ =
      D.family.coboundary1 i.succ (localComponents.get j)

namespace AssemblyStepOutput

variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}

/-- Constructor used by the RZ/RX theorem adapters.  Support and coboundary
snapshots are derived from the supplied local pieces, so they cannot drift
from the correction history. -/
noncomputable def ofComponents
    (input : D.family.Syndrome i.succ)
    (coarse : D.family.Syndrome i.castSucc)
    (correction : D.family.Correction i.succ)
    (components : List (D.family.Correction i.succ))
    (hrel : (input : D.family.Cochain2 i.succ) =
      D.family.coboundary1 i.succ correction +
        (D.selectedMap i).map2 coarse)
    (hdecomp : correction = components.sum) : AssemblyStepOutput D i where
  input := input
  coarse := coarse
  correction := correction
  localComponents := components
  componentSupports := components.map hammingSupport
  componentCoboundaries := components.map (D.family.coboundary1 i.succ)
  relation := hrel
  correction_decomposition := hdecomp
  componentSupports_length := by simp
  componentCoboundaries_length := by simp
  componentSupport_eq := by
    intro j
    have hj : (⟨j.val, j.isLt⟩ : Fin components.length) = j := Fin.ext rfl
    simp [hj]
  componentCoboundary_eq := by
    intro j
    have hj : (⟨j.val, j.isLt⟩ : Fin components.length) = j := Fin.ext rfl
    simp [hj]

end AssemblyStepOutput

/-! ## Raw assembly owner labels

The owner-label extension is compatible with the closed M12
`AssemblyStepOutput`: labels are supplied separately and point back to an
existing finite output index, correction-support snapshot, and coboundary
support.  `none` is retained for an unowned connector piece.  No decoder,
component, or stability conclusion is stored here.
-/

namespace AssemblyStepOutput

variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}

def componentAt
    (O : AssemblyStepOutput D i)
    (j : Fin O.localComponents.length) : D.family.Correction i.succ :=
  O.localComponents.get j

def componentSupportAt
    (O : AssemblyStepOutput D i)
    (j : Fin O.localComponents.length) : Finset (C1 i.succ) :=
  O.componentSupports.get ⟨j.val, by
    rw [O.componentSupports_length]
    exact j.isLt⟩

def componentCoboundaryAt
    (O : AssemblyStepOutput D i)
    (j : Fin O.localComponents.length) : D.family.Cochain2 i.succ :=
  O.componentCoboundaries.get ⟨j.val, by
    rw [O.componentCoboundaries_length]
    exact j.isLt⟩

@[simp]
theorem componentSupportAt_eq
    (O : AssemblyStepOutput D i)
    (j : Fin O.localComponents.length) :
    O.componentSupportAt j = hammingSupport (O.componentAt j) :=
  O.componentSupport_eq j

@[simp]
theorem componentCoboundaryAt_eq
    (O : AssemblyStepOutput D i)
    (j : Fin O.localComponents.length) :
    O.componentCoboundaryAt j = D.family.coboundary1 i.succ (O.componentAt j) :=
  O.componentCoboundary_eq j

end AssemblyStepOutput

structure AssemblyOwnerLabel
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth)
    {V : Type v} [Fintype V] [DecidableEq V]
    (O : AssemblyStepOutput D i) where
  outputIndex : Fin O.localComponents.length
  owner : Option V
  correctionSupport : Finset (C1 i.succ)
  coboundarySupport : Finset (C2 i.succ)
  correctionSupport_eq : correctionSupport = O.componentSupportAt outputIndex
  coboundarySupport_eq : coboundarySupport =
    hammingSupport (O.componentCoboundaryAt outputIndex)

structure AssemblyOwnerLabels
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth)
    {V : Type v} [Fintype V] [DecidableEq V]
    (O : AssemblyStepOutput D i) where
  label : ∀ j : Fin O.localComponents.length, AssemblyOwnerLabel (V := V) D i O
  outputIndex_eq : ∀ j, (label j).outputIndex = j

namespace AssemblyOwnerLabels

variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {V : Type v} [Fintype V] [DecidableEq V]

def owner
    {O : AssemblyStepOutput D i}
    (A : AssemblyOwnerLabels (V := V) D i O)
    (j : Fin O.localComponents.length) : Option V :=
  (A.label j).owner

def ofOwners
    (O : AssemblyStepOutput D i)
    (owners : Fin O.localComponents.length → Option V) :
    AssemblyOwnerLabels (V := V) D i O where
  label := fun j =>
    { outputIndex := j
      owner := owners j
      correctionSupport := O.componentSupportAt j
      coboundarySupport := hammingSupport (O.componentCoboundaryAt j)
      correctionSupport_eq := rfl
      coboundarySupport_eq := rfl }
  outputIndex_eq := by intro j; rfl

@[simp]
theorem ofOwners_owner
    (O : AssemblyStepOutput D i)
    (owners : Fin O.localComponents.length → Option V)
    (j : Fin O.localComponents.length) :
    (ofOwners (V := V) O owners).owner j = owners j :=
  rfl

end AssemblyOwnerLabels

abbrev AssemblyStep
    (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth) :=
  D.family.Syndrome i.succ → AssemblyStepOutput D i

structure AssemblyStepRelation
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth)
    (step : AssemblyStep D i) : Prop where
  input_eq : ∀ sigma, (step sigma).input = sigma
  relation : ∀ sigma,
    ((step sigma).input : D.family.Cochain2 i.succ) =
      D.family.coboundary1 i.succ (step sigma).correction +
        (D.selectedMap i).map2 (step sigma).coarse

/-- A finite base decoder with its audited right-inverse condition. -/
structure AuditedBaseDecoder
    (D : BDL26DecoderData depth C0 C1 C2) where
  decode : D.family.Syndrome (0 : LevelIndex depth) →
    D.family.Correction (0 : LevelIndex depth)
  rightInverse : ∀ sigma,
    D.family.coboundary1 (0 : LevelIndex depth) (decode sigma) =
      (sigma : D.family.Cochain2 (0 : LevelIndex depth))

namespace AuditedBaseDecoder

variable {D : BDL26DecoderData depth C0 C1 C2}

/-- Canonical finite base decoder obtained from the syndrome range preimage.
This is only a finite choice of a preimage of `δ¹`; it does not assert a
global decoder, uniqueness, locality, or a weight bound. -/
noncomputable def fromRange (D : BDL26DecoderData depth C0 C1 C2) :
    AuditedBaseDecoder D where
  decode := fun sigma => Classical.choose sigma.property
  rightInverse := fun sigma => Classical.choose_spec sigma.property

@[simp] theorem fromRange_rightInverse
    (D : BDL26DecoderData depth C0 C1 C2)
    (sigma : D.family.Syndrome (0 : LevelIndex depth)) :
    D.family.coboundary1 (0 : LevelIndex depth)
        ((fromRange D).decode sigma) =
      (sigma : D.family.Cochain2 (0 : LevelIndex depth)) := by
  exact (fromRange D).rightInverse sigma

end AuditedBaseDecoder

/-! ## F17 level-two stability adapter (separate from Section 4 `f₀`) -/

/-- The F17 level-two decoder is a distinct input surface from the recursive
Section 4 base `AuditedBaseDecoder`.  Its right-inverse and radius-two
small-error predicates are retained verbatim, but no level-two decoder is
silently reinterpreted as the recursive level-zero map. -/
structure F17LevelTwoBaseAdapter
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (G : DecodingGraphFamily depth V)
    (hdepth : 2 ≤ depth) where
  decode : BaseLevelTwoDecoder D G hdepth
  rightInverse : BaseLevelTwoDecoderIsRightInverse D G hdepth decode
  stability : BaseLevelTwoDecoderSmallError D G hdepth decode

namespace F17LevelTwoBaseAdapter

variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {G : DecodingGraphFamily depth V}
variable {hdepth : 2 ≤ depth}

@[simp] theorem rightInverse_apply
    (A : F17LevelTwoBaseAdapter D G hdepth)
    (sigma : D.family.Syndrome (levelTwoIndex hdepth)) :
    D.family.coboundary1 (levelTwoIndex hdepth) (A.decode sigma) =
      (sigma : D.family.Cochain2 (levelTwoIndex hdepth)) :=
  A.rightInverse sigma

theorem stability_apply
    (A : F17LevelTwoBaseAdapter D G hdepth)
    (I : StabilityBaseLevelTwoInput D G hdepth)
    (error : D.family.Correction (levelTwoIndex hdepth))
    (hfit : I.supportFitsRadiusTwo)
    (hsyndrome : (I.syndrome : D.family.Cochain2 (levelTwoIndex hdepth)) =
      D.family.coboundary1 (levelTwoIndex hdepth) error) :
    error + A.decode I.syndrome ∈
      (D.family.complex (levelTwoIndex hdepth)).firstCoboundaryCheckCode.carrier :=
  A.stability I error hfit hsyndrome

end F17LevelTwoBaseAdapter

/-! ## Version-two F17 data-only adapter -/

/-- The repaired F17 adapter stores only the syndrome decoder.  Right-inverse
and actual-error-local correction are external propositions proved by concrete
consumers; neither is a structure field. -/
structure F17LevelTwoBaseAdapterV2
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (G : DecodingGraphFamily depth V)
    (hdepth : 2 ≤ depth) where
  decode : BaseLevelTwoDecoder D G hdepth

namespace F17LevelTwoBaseAdapterV2

variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {G : DecodingGraphFamily depth V}
variable {hdepth : 2 ≤ depth}

/-- The unchanged F17 right-inverse obligation, stated outside the adapter. -/
def IsRightInverse (A : F17LevelTwoBaseAdapterV2 D G hdepth) : Prop :=
  BaseLevelTwoDecoderIsRightInverse D G hdepth A.decode

@[simp] theorem rightInverse_apply
    (A : F17LevelTwoBaseAdapterV2 D G hdepth)
    (hRightInverse : A.IsRightInverse)
    (sigma : D.family.Syndrome (levelTwoIndex hdepth)) :
    D.family.coboundary1 (levelTwoIndex hdepth) (A.decode sigma) =
      (sigma : D.family.Cochain2 (levelTwoIndex hdepth)) :=
  hRightInverse sigma

variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]

/-- The version-two actual-error-local correction obligation, stated outside
the adapter and conditional on the concrete local-region data. -/
noncomputable def CorrectsLocalErrors
    (L : LocalComplexData
      (V (levelTwoIndex hdepth))
      (C2 (levelTwoIndex hdepth))
      (C1 (levelTwoIndex hdepth)))
    (A : F17LevelTwoBaseAdapterV2 D G hdepth) : Prop :=
  BaseLevelTwoDecoderSmallErrorV2 D G hdepth L A.decode

theorem correctsLocalError_apply
    (L : LocalComplexData
      (V (levelTwoIndex hdepth))
      (C2 (levelTwoIndex hdepth))
      (C1 (levelTwoIndex hdepth)))
    (A : F17LevelTwoBaseAdapterV2 D G hdepth)
    (hCorrects : A.CorrectsLocalErrors L)
    (I : LevelTwoSmallErrorInputV2 D hdepth)
    (hLocal : I.IsLocal L) :
    I.error + A.decode I.syndrome ∈
      (D.family.complex (levelTwoIndex hdepth)).firstCoboundaryCheckCode.carrier :=
  hCorrects I hLocal

end F17LevelTwoBaseAdapterV2

/-- The alternating finite step data consumed by the terminating recursion. -/
structure AlternatingStepData
    (D : BDL26DecoderData depth C0 C1 C2) where
  step : ∀ i : StepIndex depth, AssemblyStep D i
  relation : ∀ i, AssemblyStepRelation D i (step i)

namespace AlternatingStepData

variable {D : BDL26DecoderData depth C0 C1 C2}

@[simp] theorem relation_apply
    (S : AlternatingStepData D) (i : StepIndex depth)
    (sigma : D.family.Syndrome i.succ) :
    (sigma : D.family.Cochain2 i.succ) =
      D.family.coboundary1 i.succ (S.step i sigma).correction +
        (D.selectedMap i).map2 (S.step i sigma).coarse := by
  have hin := congrArg
    (fun t : D.family.Syndrome i.succ =>
      (t : D.family.Cochain2 i.succ)) ((S.relation i).input_eq sigma)
  calc
    (sigma : D.family.Cochain2 i.succ) =
        ((S.step i sigma).input : D.family.Cochain2 i.succ) := hin.symm
    _ = D.family.coboundary1 i.succ (S.step i sigma).correction +
        (D.selectedMap i).map2 (S.step i sigma).coarse :=
      (S.relation i).relation sigma

end AlternatingStepData

/-! ## Parity-selected audited providers -/

/-- The two source theorem families remain explicit at the assembly boundary:
odd input levels consume the proved RX theorem and even input levels consume
the proved RZ theorem.  The weight bounds are local-step conclusions, not a
global decoder invariant supplied by the caller. -/
structure AuditedAlternatingStepProvider
    (D : BDL26DecoderData depth C0 C1 C2) where
  /-- RX is only required on the odd-input branch where its source theorem applies. -/
  rxStep : ∀ (i : StepIndex depth), i.succ.val % 2 = 1 → AssemblyStep D i
  /-- RZ is only required on the even-input branch where its source theorem applies. -/
  rzStep : ∀ (i : StepIndex depth), i.succ.val % 2 = 0 → AssemblyStep D i
  rxRelation : ∀ i h, AssemblyStepRelation D i (rxStep i h)
  rzRelation : ∀ i h, AssemblyStepRelation D i (rzStep i h)
  rxWeight : ∀ i h sigma,
    2 * HammingWeight ((rxStep i h sigma).coarse : D.family.Cochain2 i.castSucc) ≤
      HammingWeight (sigma : D.family.Cochain2 i.succ)
  rzWeight : ∀ i h sigma,
    HammingWeight ((rzStep i h sigma).coarse : D.family.Cochain2 i.castSucc) ≤
      HammingWeight (sigma : D.family.Cochain2 i.succ)

namespace AuditedAlternatingStepProvider

variable {D : BDL26DecoderData depth C0 C1 C2}

theorem even_of_not_odd {n : Nat} (h : n % 2 ≠ 1) : n % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with hzero | hone
  · exact hzero
  · exact False.elim (h hone)

def selected (P : AuditedAlternatingStepProvider D)
    (i : StepIndex depth) : AssemblyStep D i :=
  if h : i.succ.val % 2 = 1 then P.rxStep i h
  else P.rzStep i (even_of_not_odd h)

theorem selected_relation
    (P : AuditedAlternatingStepProvider D)
    (i : StepIndex depth) :
    AssemblyStepRelation D i (P.selected i) := by
  by_cases h : i.succ.val % 2 = 1
  · have h' : (i.val + 1) % 2 = 1 := by simpa using h
    have hs : P.selected i = P.rxStep i h := by simp [selected, h']
    rw [hs]
    exact P.rxRelation i h
  · have h' : ¬ ((i.val + 1) % 2 = 1) := by simpa using h
    have hEven' : (i.val + 1) % 2 = 0 := even_of_not_odd h'
    have hEven : i.succ.val % 2 = 0 := even_of_not_odd h
    have hs : P.selected i = P.rzStep i hEven := by simp [selected, h', hEven']
    rw [hs]
    exact P.rzRelation i hEven

theorem selected_weight
    (P : AuditedAlternatingStepProvider D)
    (i : StepIndex depth) (sigma : D.family.Syndrome i.succ) :
    (i.succ.val % 2 = 1 ∧
      2 * HammingWeight ((P.selected i sigma).coarse : D.family.Cochain2 i.castSucc) ≤
        HammingWeight (sigma : D.family.Cochain2 i.succ)) ∨
    (i.succ.val % 2 ≠ 1 ∧
      HammingWeight ((P.selected i sigma).coarse : D.family.Cochain2 i.castSucc) ≤
        HammingWeight (sigma : D.family.Cochain2 i.succ)) := by
  by_cases h : i.succ.val % 2 = 1
  · left
    refine ⟨h, ?_⟩
    rw [selected, dif_pos h]
    exact P.rxWeight i h sigma
  · right
    have hEven := even_of_not_odd h
    refine ⟨h, ?_⟩
    rw [selected, dif_neg h]
    exact P.rzWeight i hEven sigma

def toAlternating (P : AuditedAlternatingStepProvider D) :
    AlternatingStepData D where
  step := P.selected
  relation := P.selected_relation

end AuditedAlternatingStepProvider

/-! ## Finite lifting along the selected cochain maps -/

private def liftCorrectionAux
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : LevelIndex depth)
    (f : D.family.Correction i) : D.family.Correction (TopIndex depth) := by
  by_cases h : i.val = depth
  · exact cast (by congr 1; exact Fin.ext h) f
  · have hi_le : i.val ≤ depth := Nat.le_of_lt_succ i.isLt
    have hi : i.val < depth := Nat.lt_of_le_of_ne hi_le h
    let j : StepIndex depth := ⟨i.val, hi⟩
    have hi' : j.castSucc = i := by
      exact Fin.ext rfl
    exact liftCorrectionAux D j.succ ((D.selectedMap j).map1 (hi' ▸ f))
termination_by depth - i.val

noncomputable def liftCorrection
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : LevelIndex depth)
    (f : D.family.Correction i) : D.family.Correction (TopIndex depth) :=
  liftCorrectionAux D i f

private def liftSyndromeAux
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : LevelIndex depth)
    (s : D.family.Cochain2 i) : D.family.Cochain2 (TopIndex depth) := by
  by_cases h : i.val = depth
  · exact cast (by congr 1; exact Fin.ext h) s
  · have hi_le : i.val ≤ depth := Nat.le_of_lt_succ i.isLt
    have hi : i.val < depth := Nat.lt_of_le_of_ne hi_le h
    let j : StepIndex depth := ⟨i.val, hi⟩
    have hi' : j.castSucc = i := by
      exact Fin.ext rfl
    exact liftSyndromeAux D j.succ ((D.selectedMap j).map2 (hi' ▸ s))
termination_by depth - i.val

noncomputable def liftSyndrome
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : LevelIndex depth)
    (s : D.family.Cochain2 i) : D.family.Cochain2 (TopIndex depth) :=
  liftSyndromeAux D i s

theorem liftCorrection_top
    (D : BDL26DecoderData depth C0 C1 C2)
    (f : D.family.Correction (TopIndex depth)) :
    liftCorrection D (TopIndex depth) f = f := by
  simp [liftCorrection, liftCorrectionAux, TopIndex]

theorem liftSyndrome_top
    (D : BDL26DecoderData depth C0 C1 C2)
    (s : D.family.Cochain2 (TopIndex depth)) :
    liftSyndrome D (TopIndex depth) s = s := by
  simp [liftSyndrome, liftSyndromeAux, TopIndex]

theorem coboundary_liftCorrection
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : LevelIndex depth)
    (f : D.family.Correction i) :
    D.family.coboundary1 (TopIndex depth) (liftCorrection D i f) =
      liftSyndrome D i (D.family.coboundary1 i f) := by
  by_cases h : i.val = depth
  · have hi : i = TopIndex depth := Fin.ext h
    subst hi
    simp [liftCorrection, liftCorrectionAux, liftSyndrome, liftSyndromeAux,
      TopIndex]
  · have hi_le : i.val ≤ depth := Nat.le_of_lt_succ i.isLt
    have hi : i.val < depth := Nat.lt_of_le_of_ne hi_le h
    let j : StepIndex depth := ⟨i.val, hi⟩
    have hi' : j.castSucc = i := by exact Fin.ext rfl
    change D.family.coboundary1 (TopIndex depth)
        (liftCorrectionAux D i f) =
      liftSyndromeAux D i (D.family.coboundary1 i f)
    rw [liftCorrectionAux, liftSyndromeAux]
    simp [h]
    change D.family.coboundary1 (TopIndex depth)
        (liftCorrectionAux D j.succ ((D.selectedMap j).map1 (hi' ▸ f))) =
      liftSyndromeAux D j.succ
        ((D.selectedMap j).map2 (D.family.coboundary1 i f))
    change D.family.coboundary1 (TopIndex depth)
        (liftCorrectionAux D j.succ ((D.selectedMap j).map1 (hi' ▸ f))) =
      liftSyndrome D j.succ
        ((D.selectedMap j).map2 (D.family.coboundary1 i f))
    change D.family.coboundary1 (TopIndex depth)
        (liftCorrection D j.succ ((D.selectedMap j).map1 (hi' ▸ f))) =
      liftSyndrome D j.succ
        ((D.selectedMap j).map2 (D.family.coboundary1 i f))
    rw [coboundary_liftCorrection D j.succ
      ((D.selectedMap j).map1 (hi' ▸ f))]
    have hmap := (D.selectedMap j).commutes_coboundary1
    have hmap' := LinearMap.congr_fun hmap (hi' ▸ f)
    simp only [LinearMap.comp_apply] at hmap'
    rw [show (D.family.coboundary1 j.succ)
          ((D.selectedMap j).map1 (hi' ▸ f)) =
          (D.selectedMap j).map2 (D.family.coboundary1 i f) by
      exact hmap']
termination_by depth - i.val

theorem liftSyndrome_add
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : LevelIndex depth)
    (a b : D.family.Cochain2 i) :
    liftSyndrome D i (a + b) =
      liftSyndrome D i a + liftSyndrome D i b := by
  by_cases h : i.val = depth
  · have hi : i = TopIndex depth := Fin.ext h
    subst hi
    simp [liftSyndrome, liftSyndromeAux, TopIndex]
  · have hi_le : i.val ≤ depth := Nat.le_of_lt_succ i.isLt
    have hi : i.val < depth := Nat.lt_of_le_of_ne hi_le h
    let j : StepIndex depth := ⟨i.val, hi⟩
    have hi' : j.castSucc = i := by exact Fin.ext rfl
    change liftSyndromeAux D i (a + b) =
      liftSyndromeAux D i a + liftSyndromeAux D i b
    rw [liftSyndromeAux, liftSyndromeAux, liftSyndromeAux]
    simp [h]
    exact liftSyndrome_add D j.succ
      ((D.selectedMap j).map2 (hi' ▸ a))
      ((D.selectedMap j).map2 (hi' ▸ b))
termination_by depth - i.val

theorem liftSyndrome_map2_eq
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth)
    (s : D.family.Cochain2 i.castSucc) :
    liftSyndrome D i.castSucc s =
      liftSyndrome D i.succ ((D.selectedMap i).map2 s) := by
  have hi : i.val < depth := i.isLt
  change liftSyndromeAux D i.castSucc s =
    liftSyndromeAux D i.succ ((D.selectedMap i).map2 s)
  rw [liftSyndromeAux]
  simp [Nat.ne_of_lt hi]

/-! ## Correction history -/

/-- One entry of the source decoder history.  Step entries retain local
correction pieces, their supports, and their coboundaries; the base entry is
kept separate because it has no preceding coarse-graining relation. -/
inductive CorrectionHistoryEntry
    (D : BDL26DecoderData depth C0 C1 C2) where
  | base (B : RecursiveBaseLevelCorrection D) : CorrectionHistoryEntry D
  | step (i : StepIndex depth) (S : AssemblyStepOutput D i) :
      CorrectionHistoryEntry D

abbrev CorrectionHistory
    (D : BDL26DecoderData depth C0 C1 C2) := List (CorrectionHistoryEntry D)

namespace CorrectionHistoryEntry

variable {D : BDL26DecoderData depth C0 C1 C2}

def level : CorrectionHistoryEntry D → Nat
  | .base _ => 0
  | .step i _ => i.succ.val

def inputSyndrome : CorrectionHistoryEntry D →
    Σ i : LevelIndex depth, D.family.Syndrome i
  | .base B => ⟨0, B.input⟩
  | .step i S => ⟨i.succ, S.input⟩

def correction : CorrectionHistoryEntry D →
    Σ i : LevelIndex depth, D.family.Correction i
  | .base B => ⟨0, B.correction⟩
  | .step i S => ⟨i.succ, S.correction⟩

def coarseSyndrome : CorrectionHistoryEntry D →
    Option (Σ i : LevelIndex depth, D.family.Syndrome i)
  | .base _ => none
  | .step i S => some ⟨i.castSucc, S.coarse⟩

def localComponents : CorrectionHistoryEntry D →
    List (Σ i : LevelIndex depth, D.family.Correction i)
  | .base B => [⟨0, B.correction⟩]
  | .step i S => S.localComponents.map (fun f => ⟨i.succ, f⟩)

end CorrectionHistoryEntry

namespace CorrectionHistory

variable {D : BDL26DecoderData depth C0 C1 C2}

def inputSyndrome : CorrectionHistory D →
    Option (Σ i : LevelIndex depth, D.family.Syndrome i)
  | [] => none
  | e :: _ => some e.inputSyndrome

def levels : CorrectionHistory D → List Nat :=
  List.map CorrectionHistoryEntry.level

def localComponentCount (H : CorrectionHistory D) : Nat :=
  (H.map CorrectionHistoryEntry.localComponents).foldl (· + ·.length) 0

end CorrectionHistory

/-! A terminating history generator.  The recursion decreases the concrete
natural level index; no termination theorem is accepted from the caller. -/

private def buildHistoryAux
    (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (n : Nat)
    (hn : n ≤ depth)
    (sigma : D.family.Syndrome ⟨n, Nat.lt_succ_of_le hn⟩) :
    CorrectionHistory D := by
  cases n with
  | zero =>
      exact [.base {
        input := sigma
        correction := B.decode sigma
        relation := (B.rightInverse sigma).symm }]
  | succ n =>
      have hstep : n < depth := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
      let i : StepIndex depth := ⟨n, hstep⟩
      have hi : i.succ = ⟨n + 1, Nat.lt_succ_of_le hn⟩ := by
        exact Fin.ext rfl
      let sigma' : D.family.Syndrome i.succ := hi ▸ sigma
      let out := S.step i sigma'
      have hnext : n ≤ depth := Nat.le_of_lt hstep
      have hcoarse : i.castSucc = ⟨n, Nat.lt_succ_of_le hnext⟩ := by
        exact Fin.ext rfl
      exact .step i out ::
        buildHistoryAux D S B n hnext (hcoarse ▸ out.coarse)
termination_by n

/-- Compute the complete top-to-base correction history from one top syndrome. -/
noncomputable def buildCorrectionHistory
    (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (sigma : D.family.Syndrome (TopIndex depth)) : CorrectionHistory D :=
  buildHistoryAux D S B depth (Nat.le_refl _) sigma

/-- The base-only history stores the selected base correction without any step. -/
theorem buildCorrectionHistory_zero
    {A0 A1 A2 : LevelIndex 0 → Type u}
    [∀ i, Fintype (A0 i)] [∀ i, Fintype (A1 i)] [∀ i, Fintype (A2 i)]
    (D : BDL26DecoderData 0 A0 A1 A2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D) (sigma : D.family.Syndrome (TopIndex 0)) :
    buildCorrectionHistory D S B sigma =
      [.base {
        input := sigma
        correction := B.decode sigma
        relation := (B.rightInverse sigma).symm }] := by
  rw [buildCorrectionHistory, buildHistoryAux]
  rfl

/-- Every generated entry retains its actual decoder provenance. In particular,
the step output is computed from its own stored input and the base correction
is computed by the selected base decoder. -/
theorem buildCorrectionHistory_entry_provenance
    (D : BDL26DecoderData depth C0 C1 C2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D) (sigma : D.family.Syndrome (TopIndex depth)) :
    ∀ e ∈ buildCorrectionHistory D S B sigma,
      match e with
      | .base b => b.correction = B.decode b.input
      | .step i out => out = S.step i out.input := by
  have aux : ∀ (n : Nat) (hn : n ≤ depth)
      (s : D.family.Syndrome ⟨n, Nat.lt_succ_of_le hn⟩),
      ∀ e ∈ buildHistoryAux D S B n hn s,
        match e with
        | .base b => b.correction = B.decode b.input
        | .step i out => out = S.step i out.input := by
    intro n
    induction n with
    | zero =>
        intro hn s e he
        rw [buildHistoryAux] at he
        have he' : e = .base {
            input := s
            correction := B.decode s
            relation := (B.rightInverse s).symm } := List.mem_singleton.mp he
        subst e
        rfl
    | succ n ih =>
        intro hn s e he
        rw [buildHistoryAux] at he
        rcases List.mem_cons.mp he with he | he
        · subst e
          dsimp
          rw [(S.relation _).input_eq]
        · exact ih _ _ e he
  exact aux depth (Nat.le_refl _) sigma

/-- The actual nonempty history starts with the canonical top step. This
exposes only the head and leaves the recursively constructed tail intact. -/
theorem buildCorrectionHistory_head
    (n : Nat) {A0 A1 A2 : LevelIndex (n + 1) → Type u}
    [∀ i, Fintype (A0 i)] [∀ i, Fintype (A1 i)] [∀ i, Fintype (A2 i)]
    (D : BDL26DecoderData (n + 1) A0 A1 A2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D) (sigma : D.family.Syndrome (TopIndex (n + 1))) :
    ∃ tail, buildCorrectionHistory D S B sigma =
      CorrectionHistoryEntry.step (Fin.last n) (S.step (Fin.last n) sigma) :: tail := by
  refine ⟨buildHistoryAux D S B n (Nat.le_succ n)
    (S.step (Fin.last n) sigma).coarse, ?_⟩
  rw [buildCorrectionHistory, buildHistoryAux]
  rfl

/-- Exact three-entry expansion, retaining both step outputs and the actual base.
This shape lemma avoids unfolding the recursive implementation at a large
concrete family. -/
theorem buildCorrectionHistory_two
    {A0 A1 A2 : LevelIndex 2 → Type u}
    [∀ i, Fintype (A0 i)] [∀ i, Fintype (A1 i)] [∀ i, Fintype (A2 i)]
    (D : BDL26DecoderData 2 A0 A1 A2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D) (sigma : D.family.Syndrome (TopIndex 2)) :
    buildCorrectionHistory D S B sigma =
      [.step 1 (S.step 1 sigma),
       .step 0 (S.step 0 (S.step 1 sigma).coarse),
       .base { input := (S.step 0 (S.step 1 sigma).coarse).coarse
               correction := B.decode (S.step 0 (S.step 1 sigma).coarse).coarse
               relation := (B.rightInverse (S.step 0 (S.step 1 sigma).coarse).coarse).symm }] := by
  unfold buildCorrectionHistory
  rw [buildHistoryAux]
  change CorrectionHistoryEntry.step 1 (S.step 1 sigma) ::
    buildHistoryAux D S B 1 (by decide) (S.step 1 sigma).coarse = _
  rw [buildHistoryAux]
  change CorrectionHistoryEntry.step 1 (S.step 1 sigma) ::
    CorrectionHistoryEntry.step 0 (S.step 0 (S.step 1 sigma).coarse) ::
    buildHistoryAux D S B 0 (by decide) (S.step 0 (S.step 1 sigma).coarse).coarse = _
  rw [buildHistoryAux]
  rfl

theorem buildCorrectionHistory_terminates
    (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (sigma : D.family.Syndrome (TopIndex depth)) :
    (buildCorrectionHistory D S B sigma).length = depth + 1 := by
  have aux : ∀ (n : Nat) (hn : n ≤ depth)
      (sigma : D.family.Syndrome ⟨n, Nat.lt_succ_of_le hn⟩),
      (buildHistoryAux D S B n hn sigma).length = n + 1 := by
    intro n
    induction n with
    | zero =>
        intro hn sigma
        rw [buildHistoryAux]
        simp
    | succ n ih =>
        intro hn sigma
        have hstep : n < depth :=
          Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
        let i : StepIndex depth := ⟨n, hstep⟩
        have hi : i.succ = ⟨n + 1, Nat.lt_succ_of_le hn⟩ := by
          exact Fin.ext rfl
        let sigma' : D.family.Syndrome i.succ := hi ▸ sigma
        let out := S.step i sigma'
        have hnext : n ≤ depth := Nat.le_of_lt hstep
        have hcoarse : i.castSucc = ⟨n, Nat.lt_succ_of_le hnext⟩ := by
          exact Fin.ext rfl
        rw [buildHistoryAux]
        simp only [List.length_cons]
        rw [ih hnext (hcoarse ▸ out.coarse)]
  simpa [buildCorrectionHistory] using
    aux depth (Nat.le_refl _) sigma


/-! Actual input snapshots and accumulated alternating contraction. -/

/-- Read a physical word from the stored input snapshots of a history. -/
noncomputable def historyInputReadout
    (D : BDL26DecoderData depth C0 C1 C2) (H : CorrectionHistory D)
    (i : LevelIndex depth) : D.family.Cochain2 i := by
  classical
  exact (H.map (fun e => if h : e.inputSyndrome.1 = i then
    h ▸ e.inputSyndrome.2.val else 0)).sum

@[simp] theorem historyInputReadout_base
    (D : BDL26DecoderData depth C0 C1 C2) (B : RecursiveBaseLevelCorrection D) :
    historyInputReadout D [.base B] 0 = B.input.val := by
  classical
  simp [historyInputReadout, CorrectionHistoryEntry.inputSyndrome]

@[simp] theorem historyInputReadout_step_zero
    (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth)
    (out : AssemblyStepOutput D i) (H : CorrectionHistory D) :
    historyInputReadout D (.step i out :: H) 0 = historyInputReadout D H 0 := by
  classical
  have hi : i.succ ≠ (0 : LevelIndex depth) := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  simp [historyInputReadout, CorrectionHistoryEntry.inputSyndrome, hi]

/-- The terminal syndrome is computed by the same selected coarse outputs. -/
private def terminalInputAux
    (D : BDL26DecoderData depth C0 C1 C2) (S : AlternatingStepData D)
    (n : Nat) (hn : n ≤ depth)
    (sigma : D.family.Syndrome ⟨n, Nat.lt_succ_of_le hn⟩) : D.family.Syndrome 0 := by
  cases n with
  | zero => exact sigma
  | succ n =>
      have hs : n < depth := by omega
      exact terminalInputAux D S n (by omega) (S.step ⟨n,hs⟩ sigma).coarse
termination_by n

/-- The actual top-to-base coarse input, before applying the base correction. -/
noncomputable def terminalInput
    (D : BDL26DecoderData depth C0 C1 C2) (S : AlternatingStepData D)
    (sigma : D.family.Syndrome (TopIndex depth)) : D.family.Syndrome 0 :=
  terminalInputAux D S depth (Nat.le_refl _) sigma

/-- The genuine recursive history contains each input level exactly once. -/
theorem buildCorrectionHistory_input_levels
    (D : BDL26DecoderData depth C0 C1 C2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D) (sigma : D.family.Syndrome (TopIndex depth)) :
    (buildCorrectionHistory D S B sigma).map (fun e => e.inputSyndrome.1.val) =
      (List.range (depth + 1)).reverse := by
  have aux : ∀ (n : Nat) (hn : n ≤ depth)
      (s : D.family.Syndrome ⟨n, Nat.lt_succ_of_le hn⟩),
      (buildHistoryAux D S B n hn s).map (fun e => e.inputSyndrome.1.val) =
        (List.range (n + 1)).reverse := by
    intro n
    induction n with
    | zero =>
        intro hn s
        rw [buildHistoryAux]
        rfl
    | succ n ih =>
        intro hn s
        rw [buildHistoryAux]
        change (n + 1) :: (buildHistoryAux D S B n _ _).map
          (fun e => e.inputSyndrome.1.val) = _
        rw [ih]
        simp [List.range_succ, List.reverse_append]
  exact aux depth (Nat.le_refl _) sigma

/-- Uniqueness is about actual stored input levels, not merely history length. -/
theorem buildCorrectionHistory_input_levels_nodup
    (D : BDL26DecoderData depth C0 C1 C2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D) (sigma : D.family.Syndrome (TopIndex depth)) :
    ((buildCorrectionHistory D S B sigma).map
      (fun e => e.inputSyndrome.1.val)).Nodup := by
  rw [buildCorrectionHistory_input_levels]
  exact List.nodup_reverse.mpr List.nodup_range

/-- The sole base snapshot is the recursively selected coarse input. -/
theorem buildCorrectionHistory_base_readout
    (D : BDL26DecoderData depth C0 C1 C2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D) (sigma : D.family.Syndrome (TopIndex depth)) :
    historyInputReadout D (buildCorrectionHistory D S B sigma) 0 =
      (terminalInput D S sigma).val := by
  have aux : ∀ (n : Nat) (hn : n ≤ depth)
      (s : D.family.Syndrome ⟨n, Nat.lt_succ_of_le hn⟩),
      historyInputReadout D (buildHistoryAux D S B n hn s) 0 =
        (terminalInputAux D S n hn s).val := by
    intro n
    induction n with
    | zero =>
        intro hn s
        rw [buildHistoryAux, terminalInputAux]
        exact historyInputReadout_base D _
    | succ n ih =>
        intro hn s
        rw [buildHistoryAux, terminalInputAux]
        change historyInputReadout D (.step _ _ :: buildHistoryAux D S B n _ _) 0 = _
        rw [historyInputReadout_step_zero]
        exact ih _ _
  exact aux depth (Nat.le_refl _) sigma

/-- Accumulate primitive global RX/RZ inequalities through actual selected inputs. -/
theorem terminalInput_alternating_weight
    (D : BDL26DecoderData depth C0 C1 C2) (S : AlternatingStepData D)
    (hstep : ∀ (i : StepIndex depth) (s : D.family.Syndrome i.succ),
      if i.val % 2 = 0 then
        2 * HammingWeight (S.step i s).coarse.val ≤ HammingWeight s.val
      else HammingWeight (S.step i s).coarse.val ≤ HammingWeight s.val)
    (sigma : D.family.Syndrome (TopIndex depth)) :
    2 ^ ((depth + 1) / 2) * HammingWeight (terminalInput D S sigma).val ≤
      HammingWeight sigma.val := by
  have aux : ∀ (n : Nat) (hn : n ≤ depth)
      (s : D.family.Syndrome ⟨n, Nat.lt_succ_of_le hn⟩),
      2 ^ ((n + 1) / 2) * HammingWeight (terminalInputAux D S n hn s).val ≤
        HammingWeight s.val := by
    intro n
    induction n with
    | zero =>
        intro hn s
        rw [terminalInputAux]
        change 1 * HammingWeight s.val ≤ HammingWeight s.val
        simp only [one_mul, le_refl]
    | succ n ih =>
        intro hn s
        have hs : n < depth := by omega
        let i : StepIndex depth := ⟨n,hs⟩
        have ht := hstep i s
        have hi := ih (Nat.le_of_lt hs) (S.step i s).coarse
        rw [terminalInputAux]
        change 2 ^ ((n + 2) / 2) *
          HammingWeight (terminalInputAux D S n _ (S.step i s).coarse).val ≤ _
        by_cases hp : n % 2 = 0
        · have hc : (n + 2) / 2 = (n + 1) / 2 + 1 := by omega
          have hh : 2 * HammingWeight (S.step i s).coarse.val ≤
              HammingWeight s.val := by simpa [i, hp] using ht
          rw [hc, pow_succ]
          nlinarith
        · have hc : (n + 2) / 2 = (n + 1) / 2 := by omega
          have hh : HammingWeight (S.step i s).coarse.val ≤
              HammingWeight s.val := by simpa [i, hp] using ht
          rw [hc]
          exact hi.trans hh
  exact aux depth (Nat.le_refl _) sigma

/-- The accumulated bound is on the stored base snapshot itself. -/
theorem buildCorrectionHistory_base_weight
    (D : BDL26DecoderData depth C0 C1 C2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (hstep : ∀ (i : StepIndex depth) (s : D.family.Syndrome i.succ),
      if i.val % 2 = 0 then
        2 * HammingWeight (S.step i s).coarse.val ≤ HammingWeight s.val
      else HammingWeight (S.step i s).coarse.val ≤ HammingWeight s.val)
    (sigma : D.family.Syndrome (TopIndex depth)) :
    2 ^ ((depth + 1) / 2) *
      HammingWeight (historyInputReadout D (buildCorrectionHistory D S B sigma) 0) ≤
        HammingWeight sigma.val := by
  rw [buildCorrectionHistory_base_readout]
  exact terminalInput_alternating_weight D S hstep sigma

/-- Zero-preserving steps retain zero input snapshots throughout the fixed history.
No assertion is made about corrections or local pieces. -/
theorem buildCorrectionHistory_zero_inputs
    (D : BDL26DecoderData depth C0 C1 C2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (hzero : ∀ i sigma, sigma.val = 0 → (S.step i sigma).coarse.val = 0)
    (sigma : D.family.Syndrome (TopIndex depth)) (hs : sigma.val = 0) :
    ∀ e ∈ buildCorrectionHistory D S B sigma, e.inputSyndrome.2.val = 0 := by
  have aux : ∀ (n : Nat) (hn : n ≤ depth)
      (s : D.family.Syndrome ⟨n, Nat.lt_succ_of_le hn⟩), s.val = 0 →
      ∀ e ∈ buildHistoryAux D S B n hn s, e.inputSyndrome.2.val = 0 := by
    intro n
    induction n with
    | zero =>
        intro hn s hz e he
        rw [buildHistoryAux] at he
        change e ∈ [CorrectionHistoryEntry.base
          { input := s, correction := B.decode s, relation := (B.rightInverse s).symm }] at he
        simp only [List.mem_singleton] at he
        subst e
        exact hz
    | succ n ih =>
        intro hn s hz e he
        have hstep : n < depth := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
        let i : StepIndex depth := ⟨n, hstep⟩
        rw [buildHistoryAux] at he
        rcases List.mem_cons.mp he with he | he
        · subst e
          change (S.step i s).input.val = 0
          rw [(S.relation i).input_eq]
          exact hz
        · exact ih (Nat.le_of_lt hstep) (S.step i s).coarse (hzero i s hz) e he
  exact aux depth (Nat.le_refl _) sigma hs

private noncomputable def assembleCorrectionAux
    (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (n : Nat)
    (hn : n ≤ depth)
    (sigma : D.family.Syndrome ⟨n, Nat.lt_succ_of_le hn⟩) :
    D.family.Correction (TopIndex depth) := by
  cases n with
  | zero =>
      exact liftCorrection D ⟨0, Nat.zero_lt_succ _⟩ (B.decode sigma)
  | succ n =>
      have hstep : n < depth := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
      let i : StepIndex depth := ⟨n, hstep⟩
      have hi : i.succ = ⟨n + 1, Nat.lt_succ_of_le hn⟩ := by
        exact Fin.ext rfl
      let sigma' : D.family.Syndrome i.succ := hi ▸ sigma
      let out := S.step i sigma'
      have hnext : n ≤ depth := Nat.le_of_lt hstep
      have hcoarse : i.castSucc = ⟨n, Nat.lt_succ_of_le hnext⟩ := by
        exact Fin.ext rfl
      exact liftCorrection D i.succ out.correction +
        assembleCorrectionAux D S B n hnext (hcoarse ▸ out.coarse)
termination_by n

/-- Sum of all level corrections after lifting each one to the terminal level.
The history argument is retained in the public definition so downstream
provenance consumers inspect the same deterministic choices used by the
correction. -/
noncomputable def historyLiftedCorrection
    (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) : D.family.Correction (TopIndex depth) :=
  (H.map (fun e =>
    liftCorrection D (CorrectionHistoryEntry.correction e).1
      (CorrectionHistoryEntry.correction e).2)).sum

private theorem assembleCorrectionAux_eq
    (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (n : Nat)
    (hn : n ≤ depth)
    (sigma : D.family.Syndrome ⟨n, Nat.lt_succ_of_le hn⟩) :
    D.family.coboundary1 (TopIndex depth)
        (assembleCorrectionAux D S B n hn sigma) =
      liftSyndrome D ⟨n, Nat.lt_succ_of_le hn⟩ sigma := by
  cases n with
  | zero =>
      have hbase := B.rightInverse sigma
      have hnat := coboundary_liftCorrection D
        (⟨0, Nat.zero_lt_succ _⟩ : LevelIndex depth) (B.decode sigma)
      rw [assembleCorrectionAux]
      calc
        D.family.coboundary1 (TopIndex depth)
            (liftCorrection D ⟨0, Nat.zero_lt_succ _⟩ (B.decode sigma)) =
            liftSyndrome D ⟨0, Nat.lt_succ_of_le hn⟩
              (D.family.coboundary1 (⟨0, Nat.zero_lt_succ _⟩ : LevelIndex depth)
                (B.decode sigma)) := by simpa using hnat
        _ = liftSyndrome D ⟨0, Nat.lt_succ_of_le hn⟩ sigma := by
          exact congrArg
            (liftSyndrome D (⟨0, Nat.lt_succ_of_le hn⟩ : LevelIndex depth)) hbase
  | succ n =>
      have hstep : n < depth := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
      let i : StepIndex depth := ⟨n, hstep⟩
      have hi : i.succ = ⟨n + 1, Nat.lt_succ_of_le hn⟩ := by
        exact Fin.ext rfl
      let sigma' : D.family.Syndrome i.succ := hi ▸ sigma
      let out := S.step i sigma'
      have hnext : n ≤ depth := Nat.le_of_lt hstep
      have hcoarse : i.castSucc = ⟨n, Nat.lt_succ_of_le hnext⟩ := by
        exact Fin.ext rfl
      have hrec := assembleCorrectionAux_eq D S B n hnext
        (hcoarse ▸ out.coarse)
      have hrec' :
          D.family.coboundary1 (TopIndex depth)
              (assembleCorrectionAux D S B n hnext (hcoarse ▸ out.coarse)) =
            liftSyndrome D i.castSucc
              (out.coarse : D.family.Cochain2 i.castSucc) := by
        exact hrec
      have hstepRel := (S.relation i).relation sigma'
      have hnat := coboundary_liftCorrection D i.succ out.correction
      have hmap := liftSyndrome_map2_eq D i (out.coarse : D.family.Cochain2 i.castSucc)
      have hadd := liftSyndrome_add D i.succ
        (D.family.coboundary1 i.succ out.correction)
        ((D.selectedMap i).map2 (out.coarse : D.family.Cochain2 i.castSucc))
      rw [assembleCorrectionAux]
      rw [map_add, hnat, hrec', hmap, ← hadd]
      rw [← hstepRel]
      have hinput := (S.relation i).input_eq sigma'
      have hinput' := congrArg
        (fun t : D.family.Syndrome i.succ =>
          (t : D.family.Cochain2 i.succ)) hinput
      have hinput'' :
          (out.input : D.family.Cochain2 i.succ) =
            (sigma' : D.family.Cochain2 i.succ) := by
        simpa only [out] using hinput'
      rw [hinput'']
      cases hi
      rfl
termination_by n

theorem globalCorrection_eq_input
    (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (sigma : D.family.Syndrome (TopIndex depth)) :
    D.family.coboundary1 (TopIndex depth)
        (assembleCorrectionAux D S B depth (Nat.le_refl _) sigma) =
      (sigma : D.family.Cochain2 (TopIndex depth)) := by
  simpa [liftSyndrome_top] using
    assembleCorrectionAux_eq D S B depth (Nat.le_refl _) sigma

/-! The recursive form is definitionally the sum of the current correction and
the recursively lifted lower-level correction.  Keeping this definition
separate from `historyLiftedCorrection` makes the telescoping proof independent
of list bookkeeping while the latter remains available to provenance
consumers. -/
noncomputable def globalCorrection
    (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (sigma : D.family.Syndrome (TopIndex depth)) :
    D.family.Correction (TopIndex depth) :=
  assembleCorrectionAux D S B depth (Nat.le_refl _) sigma

theorem historyLiftedCorrection_eq_globalCorrection
    (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (sigma : D.family.Syndrome (TopIndex depth)) :
    historyLiftedCorrection D (buildCorrectionHistory D S B sigma) =
      globalCorrection D S B sigma := by
  have aux : ∀ (n : Nat) (hn : n ≤ depth)
      (sigma : D.family.Syndrome ⟨n, Nat.lt_succ_of_le hn⟩),
      historyLiftedCorrection D (buildHistoryAux D S B n hn sigma) =
        assembleCorrectionAux D S B n hn sigma := by
    intro n
    induction n with
    | zero =>
        intro hn sigma
        rw [buildHistoryAux]
        simp only [Nat.casesAuxOn]
        rw [assembleCorrectionAux]
        simp only [Nat.rec_zero]
        simp only [Nat.casesAuxOn, Nat.rec, historyLiftedCorrection,
          List.map, List.sum, List.foldr, CorrectionHistoryEntry.correction]
        simpa only [add_zero, Fin.zero_eta]
    | succ n ih =>
        intro hn sigma
        have hstep : n < depth :=
          Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
        let i : StepIndex depth := ⟨n, hstep⟩
        have hi : i.succ = ⟨n + 1, Nat.lt_succ_of_le hn⟩ := by
          exact Fin.ext rfl
        let sigma' : D.family.Syndrome i.succ := hi ▸ sigma
        let out := S.step i sigma'
        have hnext : n ≤ depth := Nat.le_of_lt hstep
        have hcoarse : i.castSucc = ⟨n, Nat.lt_succ_of_le hnext⟩ := by
          exact Fin.ext rfl
        rw [buildHistoryAux]
        simp only [Nat.casesAuxOn]
        rw [assembleCorrectionAux]
        simp only [Nat.casesAuxOn, Nat.rec, historyLiftedCorrection,
          List.map, List.sum, List.foldr, CorrectionHistoryEntry.correction]
        have ih' := ih hnext (hcoarse ▸ out.coarse)
        simp only [historyLiftedCorrection, List.map, List.sum,
          CorrectionHistoryEntry.correction] at ih'
        rw [ih']
  simpa [buildCorrectionHistory, globalCorrection] using
    aux depth (Nat.le_refl _) sigma

theorem globalCorrection_syndrome_eq
    (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (sigma : D.family.Syndrome (TopIndex depth)) :
    D.family.coboundary1 (TopIndex depth) (globalCorrection D S B sigma) =
      (sigma : D.family.Cochain2 (TopIndex depth)) := by
  exact globalCorrection_eq_input D S B sigma

theorem historyLiftedCorrection_syndrome_eq
    (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (sigma : D.family.Syndrome (TopIndex depth)) :
    D.family.coboundary1 (TopIndex depth)
        (historyLiftedCorrection D (buildCorrectionHistory D S B sigma)) =
      (sigma : D.family.Cochain2 (TopIndex depth)) := by
  rw [historyLiftedCorrection_eq_globalCorrection D S B sigma]
  exact globalCorrection_syndrome_eq D S B sigma

/-- The source BDL26 family uses terminal levels `2 * k`; the generic
assembly is valid for every finite depth, and this wrapper records the source
quantifier without strengthening any conclusion. -/
def SourceTerminalDepth (depth : Nat) : Prop := ∃ k, depth = 2 * k

theorem globalCorrection_syndrome_eq_even_depth
    {k : Nat}
    {C0 : LevelIndex (2 * k) → Type u}
    {C1 : LevelIndex (2 * k) → Type u}
    {C2 : LevelIndex (2 * k) → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
    [∀ i, Fintype (C2 i)]
    (D : BDL26DecoderData (2 * k) C0 C1 C2)
    (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (sigma : D.family.Syndrome (TopIndex (2 * k))) :
    D.family.coboundary1 (TopIndex (2 * k))
        (globalCorrection D S B sigma) =
      (sigma : D.family.Cochain2 (TopIndex (2 * k))) := by
  exact globalCorrection_syndrome_eq D S B sigma


/-! ## Direct adapters for the proved RZ/RX leaves -/

namespace AuditedLeafAdapters

open RZCoarseGraining RXCoarseGraining

variable {D : BDL26DecoderData depth C0 C1 C2}
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]

noncomputable def rzOutput
    {V : Type v} [Fintype V] [DecidableEq V]
    {i : StepIndex depth}
    (A : RZCoarseGraining.RZCoarseGrainingData D i V)
    (hcoh : RZCoarseGraining.LocalTopCohomologyIdentification A)
    (hcompat : RZCoarseGraining.InducedCoboundaryCompatibility A)
    (hEven : i.succ.val % 2 = 0)
    (sigma : D.family.Syndrome i.succ) : AssemblyStepOutput D i := by
  let hsrc :=
    RZCoarseGraining.rz_coarse_graining_even A hcoh hcompat hEven sigma
  let coarse := Classical.choose hsrc
  let hsrc' := Classical.choose_spec hsrc
  let correction := Classical.choose hsrc'
  have hcorrection := (Classical.choose_spec hsrc').1
  have hrelation := (Classical.choose_spec hsrc').2.1
  let components : List (D.family.Correction i.succ) :=
    (Finset.univ : Finset (C2 i.castSucc)).toList.map
      (fun z => RZCoarseGraining.localCorrectionComponent A hcoh z sigma.1)
  apply AssemblyStepOutput.ofComponents sigma coarse correction components
  · exact hrelation
  · dsimp [correction]
    calc
      Classical.choose hsrc' =
          RZCoarseGraining.correctionFromSyndrome A hcoh sigma.1 := hcorrection
      _ = ∑ z, RZCoarseGraining.localCorrectionComponent A hcoh z sigma.1 :=
        (RZCoarseGraining.localComputabilityCertificate A hcoh hcompat).totalCorrectionDecomposition _
      _ = components.sum := by simp [components]

/-- Recover the chosen correction from its explicit existential specification. -/
theorem rzOutput_correction
    {V : Type v} [Fintype V] [DecidableEq V]
    {i : StepIndex depth}
    (A : RZCoarseGraining.RZCoarseGrainingData D i V)
    (hcoh : RZCoarseGraining.LocalTopCohomologyIdentification A)
    (hcompat : RZCoarseGraining.InducedCoboundaryCompatibility A)
    (hEven : i.succ.val % 2 = 0)
    (sigma : D.family.Syndrome i.succ) :
    (rzOutput A hcoh hcompat hEven sigma).correction =
      RZCoarseGraining.correctionFromSyndrome A hcoh sigma.1 := by
  let hsrc := RZCoarseGraining.rz_coarse_graining_even A hcoh hcompat hEven sigma
  exact (Classical.choose_spec (Classical.choose_spec hsrc)).1

theorem rzOutput_coarse
    {V : Type v} [Fintype V] [DecidableEq V]
    {i : StepIndex depth}
    (A : RZCoarseGraining.RZCoarseGrainingData D i V)
    (hcoh : RZCoarseGraining.LocalTopCohomologyIdentification A)
    (hcompat : RZCoarseGraining.InducedCoboundaryCompatibility A)
    (hEven : i.succ.val % 2 = 0)
    (sigma : D.family.Syndrome i.succ) :
    (rzOutput A hcoh hcompat hEven sigma).coarse =
      RZCoarseGraining.coarseSyndrome A hcompat sigma := by
  apply Subtype.ext
  apply RZCoarseGraining.selectedMap_map2_injective A hEven
  have hactual := (rzOutput A hcoh hcompat hEven sigma).relation
  change (sigma : D.family.Cochain2 i.succ) = _ at hactual
  rw [rzOutput_correction] at hactual
  have hcanonical := RZCoarseGraining.rz_exact_relation A hcoh hcompat hEven sigma
  exact add_left_cancel (hactual.symm.trans hcanonical)

theorem rzOutput_coarse_apply
    {V : Type v} [Fintype V] [DecidableEq V]
    {i : StepIndex depth}
    (A : RZCoarseGraining.RZCoarseGrainingData D i V)
    (hcoh : RZCoarseGraining.LocalTopCohomologyIdentification A)
    (hcompat : RZCoarseGraining.InducedCoboundaryCompatibility A)
    (hEven : i.succ.val % 2 = 0)
    (sigma : D.family.Syndrome i.succ) (z : C2 i.castSucc) :
    ((rzOutput A hcoh hcompat hEven sigma).coarse : D.family.Cochain2 i.castSucc) z =
      RZCoarseGraining.RZCoarseGrainingData.topParity A sigma.1 z := by
  rw [rzOutput_coarse]
  rfl

theorem rzOutput_localComponents
    {V : Type v} [Fintype V] [DecidableEq V]
    {i : StepIndex depth}
    (A : RZCoarseGraining.RZCoarseGrainingData D i V)
    (hcoh : RZCoarseGraining.LocalTopCohomologyIdentification A)
    (hcompat : RZCoarseGraining.InducedCoboundaryCompatibility A)
    (hEven : i.succ.val % 2 = 0)
    (sigma : D.family.Syndrome i.succ) :
    (rzOutput A hcoh hcompat hEven sigma).localComponents =
      (Finset.univ : Finset (C2 i.castSucc)).toList.map
        (fun z => RZCoarseGraining.localCorrectionComponent A hcoh z sigma.1) := rfl

theorem rzOutput_componentSupports
    {V : Type v} [Fintype V] [DecidableEq V]
    {i : StepIndex depth}
    (A : RZCoarseGraining.RZCoarseGrainingData D i V)
    (hcoh : RZCoarseGraining.LocalTopCohomologyIdentification A)
    (hcompat : RZCoarseGraining.InducedCoboundaryCompatibility A)
    (hEven : i.succ.val % 2 = 0)
    (sigma : D.family.Syndrome i.succ) :
    (rzOutput A hcoh hcompat hEven sigma).componentSupports =
      ((Finset.univ : Finset (C2 i.castSucc)).toList.map
        (fun z => RZCoarseGraining.localCorrectionComponent A hcoh z sigma.1)).map
          hammingSupport := rfl

theorem rzOutput_componentCoboundaries
    {V : Type v} [Fintype V] [DecidableEq V]
    {i : StepIndex depth}
    (A : RZCoarseGraining.RZCoarseGrainingData D i V)
    (hcoh : RZCoarseGraining.LocalTopCohomologyIdentification A)
    (hcompat : RZCoarseGraining.InducedCoboundaryCompatibility A)
    (hEven : i.succ.val % 2 = 0)
    (sigma : D.family.Syndrome i.succ) :
    (rzOutput A hcoh hcompat hEven sigma).componentCoboundaries =
      ((Finset.univ : Finset (C2 i.castSucc)).toList.map
        (fun z => RZCoarseGraining.localCorrectionComponent A hcoh z sigma.1)).map
          (D.family.coboundary1 i.succ) := rfl

theorem rzOutput_weight
    {V : Type v} [Fintype V] [DecidableEq V]
    {i : StepIndex depth}
    (A : RZCoarseGraining.RZCoarseGrainingData D i V)
    (hcoh : RZCoarseGraining.LocalTopCohomologyIdentification A)
    (hcompat : RZCoarseGraining.InducedCoboundaryCompatibility A)
    (hEven : i.succ.val % 2 = 0)
    (sigma : D.family.Syndrome i.succ) :
    HammingWeight ((rzOutput A hcoh hcompat hEven sigma).coarse :
      D.family.Cochain2 i.castSucc) ≤
      HammingWeight (sigma : D.family.Cochain2 i.succ) := by
  let hsrc :=
    RZCoarseGraining.rz_coarse_graining_even A hcoh hcompat hEven sigma
  let hsrc' := Classical.choose_spec hsrc
  have hweight := (Classical.choose_spec hsrc').2.2.1
  exact hweight

theorem rzOutput_relation
    {V : Type v} [Fintype V] [DecidableEq V]
    {i : StepIndex depth}
    (A : RZCoarseGraining.RZCoarseGrainingData D i V)
    (hcoh : RZCoarseGraining.LocalTopCohomologyIdentification A)
    (hcompat : RZCoarseGraining.InducedCoboundaryCompatibility A)
    (hEven : i.succ.val % 2 = 0) :
    AssemblyStepRelation D i (rzOutput A hcoh hcompat hEven) := by
  refine ⟨?_, ?_⟩
  · intro sigma
    rfl
  · intro sigma
    exact (rzOutput A hcoh hcompat hEven sigma).relation

noncomputable def rxOutput
    {X Q Z : Type v} [Fintype X] [DecidableEq X]
    [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
    {X0 : X → Type u} {Q0 : Q → Type u}
    {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
    [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
    [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
    {i : StepIndex depth}
    {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
    {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
    {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
    (A : RXCoarseGraining.RXCoarseGrainingData
      (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (hOdd : i.succ.val % 2 = 1)
    (sigma : D.family.Syndrome i.succ) : AssemblyStepOutput D i := by
  let hsrc :=
    RXCoarseGraining.RXCoarseGrainingData.rx_coarse_graining_odd A hOdd sigma
  let coarse := Classical.choose hsrc
  let hsrc' := Classical.choose_spec hsrc
  let correction := Classical.choose hsrc'
  have hcorrection := (Classical.choose_spec hsrc').2.1
  have hrelation := (Classical.choose_spec hsrc').2.2.1
  let components : List (D.family.Correction i.succ) :=
    (Finset.univ : Finset (RXCoarseGraining.RXVertex X Q Z)).toList.map
      (fun v =>
        (RXCoarseGraining.RXCoarseGrainingData.rxLocalComponents A).component v sigma.1)
  apply AssemblyStepOutput.ofComponents sigma coarse correction components
  · exact hrelation
  · dsimp [correction]
    calc
      Classical.choose hsrc' =
          RXCoarseGraining.RXCoarseGrainingData.rxCorrectionTotal A sigma.1 := hcorrection
      _ = (∑ x, RXCoarseGraining.RXCoarseGrainingData.cxComponentTotal A sigma.1 x) +
            ∑ q, RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal A sigma.1 q :=
        RXCoarseGraining.RXCoarseGrainingData.rx_total_eq_components A sigma.1
      _ = components.sum := by
        simp [components, RXCoarseGraining.RXCoarseGrainingData.rxLocalComponents,
          LocalCorrectionComponents.totalCorrection, Fintype.sum_sum_type]

theorem rxOutput_weight
    {X Q Z : Type v} [Fintype X] [DecidableEq X]
    [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
    {X0 : X → Type u} {Q0 : Q → Type u}
    {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
    [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
    [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
    {i : StepIndex depth}
    {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
    {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
    {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
    (A : RXCoarseGraining.RXCoarseGrainingData
      (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (hOdd : i.succ.val % 2 = 1)
    (sigma : D.family.Syndrome i.succ) :
    2 * HammingWeight ((rxOutput A hOdd sigma).coarse :
      D.family.Cochain2 i.castSucc) ≤
      HammingWeight (sigma : D.family.Cochain2 i.succ) := by
  let hsrc :=
    RXCoarseGraining.RXCoarseGrainingData.rx_coarse_graining_odd A hOdd sigma
  let hsrc' := Classical.choose_spec hsrc
  have hweight := (Classical.choose_spec hsrc').2.2.2.1
  exact hweight

theorem rxOutput_relation
    {X Q Z : Type v} [Fintype X] [DecidableEq X]
    [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
    {X0 : X → Type u} {Q0 : Q → Type u}
    {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
    [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
    [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
    {i : StepIndex depth}
    {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
    {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
    {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
    (A : RXCoarseGraining.RXCoarseGrainingData
      (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (hOdd : i.succ.val % 2 = 1) :
    AssemblyStepRelation D i (rxOutput A hOdd) := by
  refine ⟨?_, ?_⟩
  · intro sigma
    rfl
  · intro sigma
    exact (rxOutput A hOdd sigma).relation

end AuditedLeafAdapters

/-! ## Separate X/Z sector assembly -/

/-- A sector assembly keeps the X and Z complexes as independent typed data.
No chain/cochain coercion or definitional equality between the two sectors is
introduced. -/
structure XZAssembly
    (DX : BDL26DecoderData depth C0 C1 C2)
    {Z0 Z1 Z2 : LevelIndex depth → Type v}
    [∀ i, Fintype (Z0 i)] [∀ i, Fintype (Z1 i)] [∀ i, Fintype (Z2 i)] where
  DZ : BDL26DecoderData depth Z0 Z1 Z2
  xSteps : AlternatingStepData DX
  zSteps : AlternatingStepData DZ
  xBase : AuditedBaseDecoder DX
  zBase : AuditedBaseDecoder DZ

namespace XZAssembly

variable {DX : BDL26DecoderData depth C0 C1 C2}
variable {Z0 Z1 Z2 : LevelIndex depth → Type v}
variable [∀ i, Fintype (Z0 i)] [∀ i, Fintype (Z1 i)] [∀ i, Fintype (Z2 i)]

noncomputable def xCorrection (A : XZAssembly (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) DX)
    (sigma : DX.family.Syndrome (TopIndex depth)) :
    DX.family.Correction (TopIndex depth) :=
  globalCorrection DX A.xSteps A.xBase sigma

noncomputable def zCorrection (A : XZAssembly (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) DX)
    (sigma : A.DZ.family.Syndrome (TopIndex depth)) :
    A.DZ.family.Correction (TopIndex depth) :=
  globalCorrection A.DZ A.zSteps A.zBase sigma

theorem xCorrection_syndrome_eq
    (A : XZAssembly (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) DX)
    (sigma : DX.family.Syndrome (TopIndex depth)) :
    DX.family.coboundary1 (TopIndex depth) (A.xCorrection sigma) =
      (sigma : DX.family.Cochain2 (TopIndex depth)) := by
  exact globalCorrection_syndrome_eq DX A.xSteps A.xBase sigma

theorem zCorrection_syndrome_eq
    (A : XZAssembly (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) DX)
    (sigma : A.DZ.family.Syndrome (TopIndex depth)) :
    A.DZ.family.coboundary1 (TopIndex depth) (A.zCorrection sigma) =
      (sigma : A.DZ.family.Cochain2 (TopIndex depth)) := by
  exact globalCorrection_syndrome_eq A.DZ A.zSteps A.zBase sigma

end XZAssembly

/-! ## Dual-sector assembly -/

/-- An X/Z assembly whose second sector is explicitly the typed chain dual of
the first family.  The equality field is intentional: it makes every
boundary/boundary-transpose obligation auditable instead of treating the two
decoder records as unrelated data.  The adjacent-level dual maps and their
local leaves remain separate inputs because their direction/locality contracts
are source-specific. -/
structure DualSectorAssembly
    (DX : BDL26DecoderData depth C0 C1 C2) where
  DZ : BDL26DecoderData depth C2 C1 C0
  family_eq_dual : DZ.family = BDL26CochainFamily.dual DX.family
  xSteps : AlternatingStepData DX
  zSteps : AlternatingStepData DZ
  xBase : AuditedBaseDecoder DX
  zBase : AuditedBaseDecoder DZ

namespace DualSectorAssembly

variable {DX : BDL26DecoderData depth C0 C1 C2}

def toXZAssembly (A : DualSectorAssembly DX) :
    XZAssembly (Z0 := C2) (Z1 := C1) (Z2 := C0) DX where
  DZ := A.DZ
  xSteps := A.xSteps
  zSteps := A.zSteps
  xBase := A.xBase
  zBase := A.zBase

theorem family_complex_eq_dual
    (A : DualSectorAssembly DX) (i : LevelIndex depth) :
    A.DZ.family.complex i = dualChainComplex (DX.family.complex i) := by
  rw [A.family_eq_dual]
  rfl

theorem xCorrection_syndrome_eq
    (A : DualSectorAssembly DX)
    (sigma : DX.family.Syndrome (TopIndex depth)) :
    DX.family.coboundary1 (TopIndex depth)
        ((A.toXZAssembly).xCorrection sigma) =
      (sigma : DX.family.Cochain2 (TopIndex depth)) := by
  exact XZAssembly.xCorrection_syndrome_eq A.toXZAssembly sigma

theorem zCorrection_syndrome_eq
    (A : DualSectorAssembly DX)
    (sigma : A.DZ.family.Syndrome (TopIndex depth)) :
    A.DZ.family.coboundary1 (TopIndex depth)
        ((A.toXZAssembly).zCorrection sigma) =
      (sigma : A.DZ.family.Cochain2 (TopIndex depth)) := by
  exact XZAssembly.zCorrection_syndrome_eq A.toXZAssembly sigma

end DualSectorAssembly

/-- The actual history agrees with any finite recursion having exactly its
base constructor and selected-step equation. This exposes uniqueness without
exporting the private recursive implementation or changing the algorithm. -/
theorem buildCorrectionHistory_eq_of_recursion
    (D : BDL26DecoderData depth C0 C1 C2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (F : ∀ (n : Nat) (hn : n ≤ depth),
      D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩ → CorrectionHistory D)
    (hzero : ∀ hn sigma, F 0 hn sigma = [.base {
      input := sigma, correction := B.decode sigma,
      relation := (B.rightInverse sigma).symm }])
    (hsucc : ∀ (n : Nat) (hn : n+1 ≤ depth)
      (sigma : D.family.Syndrome ⟨n+1,Nat.lt_succ_of_le hn⟩),
      F (n+1) hn sigma =
        .step ⟨n,by omega⟩ (S.step ⟨n,by omega⟩ sigma) ::
          F n (by omega) (S.step ⟨n,by omega⟩ sigma).coarse)
    (sigma : D.family.Syndrome (TopIndex depth)) :
    buildCorrectionHistory D S B sigma = F depth (Nat.le_refl _) sigma := by
  have aux : ∀ (n : Nat) (hn : n ≤ depth)
      (s : D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩),
      buildHistoryAux D S B n hn s = F n hn s := by
    intro n
    induction n with
    | zero =>
        intro hn s
        rw [buildHistoryAux]
        change [CorrectionHistoryEntry.base ({
          input := s
          correction := B.decode s
          relation := (B.rightInverse s).symm
        } : RecursiveBaseLevelCorrection D)] = F 0 hn s
        exact (hzero hn s).symm
    | succ n ih =>
        intro hn s
        rw [buildHistoryAux]
        change CorrectionHistoryEntry.step (⟨n,by omega⟩ : StepIndex depth)
          (S.step ⟨n,by omega⟩ s) ::
            buildHistoryAux D S B n (by omega) (S.step ⟨n,by omega⟩ s).coarse = F (n+1) hn s
        rw [hsucc]
        exact congrArg (fun H => CorrectionHistoryEntry.step
          (⟨n,by omega⟩ : StepIndex depth) (S.step ⟨n,by omega⟩ s) :: H) (ih _ _)
  exact aux depth (Nat.le_refl _) sigma

/-- The original correction lift factors through its actual next selected
map. This equation exposes the unchanged private recursion at adjacent levels.
It is appended after the existing declarations to preserve their elaboration
order and private proof identities. -/
theorem liftCorrection_map1_eq
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth) (w : D.family.Correction i.castSucc) :
    liftCorrection D i.castSucc w =
      liftCorrection D i.succ ((D.selectedMap i).map1 w) := by
  have hi : i.val < depth := i.isLt
  change liftCorrectionAux D i.castSucc w =
    liftCorrectionAux D i.succ ((D.selectedMap i).map1 w)
  rw [liftCorrectionAux]
  simp [Nat.ne_of_lt hi]

end MultiscaleDecoder
end Coding
end QEC
