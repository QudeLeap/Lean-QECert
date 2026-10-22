import QEC.Semantics.Core.Definitions
/-!
# Field-labelled computational-basis registers for Ngu24

This first #725 interface fixes the finite-field labels and the literal three
physical-copy coordinates used by the Ngu24 qudit construction.  It introduces
no gate, encoding, or physical-product result.
-/

noncomputable section

namespace QEC.Distillation

universe u

/-- One computational-basis qudit with labels in the finite field `F`. -/
abbrev ComputationalBasisQudit (F : Type u) [Fintype F] : Type u :=
  EuclideanSpace Complex F

/-- Computational-basis labels for an `ι`-site register over `F`. -/
abbrev ComputationalBasisRegisterLabel (F ι : Type u) : Type u :=
  ι → F

/-- The finite register whose basis is indexed by field-labelled words. -/
abbrev ComputationalBasisRegister (F ι : Type u) : Type u :=
  EuclideanSpace Complex (ComputationalBasisRegisterLabel F ι)

variable {F ι : Type u} [Field F] [Fintype F]

/-- The computational-basis ket of one field-labelled qudit. -/
def quditBasisKet (label : F) : ComputationalBasisQudit F :=
  EuclideanSpace.basisFun F Complex label

/-- The computational-basis ket of a finite field-labelled register. -/
def registerBasisKet [Fintype ι] [DecidableEq ι]
    (label : ComputationalBasisRegisterLabel F ι) :
    ComputationalBasisRegister F ι :=
  EuclideanSpace.basisFun (ComputationalBasisRegisterLabel F ι) Complex label

/-- Tags which make the three physical copies distinct in the type of a coordinate. -/
inductive ThreeCopyTag
  | first
  | second
  | third
  deriving DecidableEq

instance : Fintype ThreeCopyTag where
  elems := {.first, .second, .third}
  complete := by intro tag; cases tag <;> simp

/-- A physical coordinate records both its copy tag and its within-copy site. -/
abbrev TaggedThreeCopyCoordinate (ι : Type u) : Type u :=
  ThreeCopyTag × ι

/-- A computational-basis label for all three tagged copies at once. -/
abbrev TaggedThreeCopyRegisterLabel (F ι : Type u) : Type u :=
  TaggedThreeCopyCoordinate ι → F

/-- The computational-basis Hilbert space of the three tagged copies. -/
abbrev TaggedThreeCopyRegister (F ι : Type u) : Type u :=
  EuclideanSpace Complex (TaggedThreeCopyRegisterLabel F ι)

/-- Assemble the three separately tagged register labels into one global label. -/
def assembleTagged (blocks : ThreeCopyTag → ComputationalBasisRegisterLabel F ι) :
    TaggedThreeCopyRegisterLabel F ι :=
  fun coordinate => blocks coordinate.1 coordinate.2

/-- Recover one explicitly tagged block from a global three-copy label. -/
def extractBlock (label : TaggedThreeCopyRegisterLabel F ι) (tag : ThreeCopyTag) :
    ComputationalBasisRegisterLabel F ι :=
  fun site => label (tag, site)

omit [Field F] [Fintype F] in
@[simp]
theorem extractBlock_assembleTagged
    (blocks : ThreeCopyTag → ComputationalBasisRegisterLabel F ι) (tag : ThreeCopyTag) :
    extractBlock (assembleTagged blocks) tag = blocks tag :=
  rfl

omit [Field F] [Fintype F] in
@[simp]
theorem assembleTagged_extractBlock (label : TaggedThreeCopyRegisterLabel F ι) :
    assembleTagged (extractBlock label) = label := by
  funext coordinate
  rcases coordinate with ⟨tag, site⟩
  rfl

/-- The three tagged coordinates belonging to one within-copy site. -/
def coordinateSupport [Fintype ι] [DecidableEq ι] (site : ι) :
    Finset (TaggedThreeCopyCoordinate ι) :=
  Finset.univ.filter (fun coordinate => coordinate.2 = site)

@[simp]
theorem mem_coordinateSupport [Fintype ι] [DecidableEq ι]
    {coordinate : TaggedThreeCopyCoordinate ι} {site : ι} :
    coordinate ∈ coordinateSupport site ↔ coordinate.2 = site := by
  simp [coordinateSupport]

/-- Distinct within-copy sites determine disjoint tagged three-copy supports. -/
theorem coordinateSupport_disjoint [Fintype ι] [DecidableEq ι]
    {first second : ι} (hne : first ≠ second) :
    Disjoint (coordinateSupport first) (coordinateSupport second) := by
  apply Finset.disjoint_left.mpr
  intro coordinate hfirst hsecond
  have hfirst' : coordinate.2 = first := mem_coordinateSupport.mp hfirst
  have hsecond' : coordinate.2 = second := mem_coordinateSupport.mp hsecond
  exact hne (hfirst'.symm.trans hsecond')

/-- Every tag appears in the support of its corresponding within-copy site. -/
theorem taggedCoordinate_mem_coordinateSupport [Fintype ι] [DecidableEq ι]
    (tag : ThreeCopyTag) (site : ι) :
    (tag, site) ∈ coordinateSupport site := by
  simp [coordinateSupport]

end QEC.Distillation
