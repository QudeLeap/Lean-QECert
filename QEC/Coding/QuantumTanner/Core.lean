import QEC.Coding.QLDPC.Core
import QEC.Coding.CSS.ParityChecks
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Quantum Tanner code interface

This module records the construction-level data used for Quantum Tanner codes:
left-right Cayley square complexes, tensor local codes, puncturing and robustness,
the finite random local-code experiment, and the induced binary CSS chain code.

The definitions follow the construction in Leverrier--Zemor, *Quantum Tanner
codes* (arXiv:2202.13641v3, Sections 2--4).  In particular, this file contains
no asymptotic-goodness witness, positive-probability existence theorem, or
lifted-product identification.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner

open Classical

universe u v

/-! ## Local tensor codes -/

/-- Restrict a word on `A × B` to the column with second coordinate `b`. -/
def columnRestriction {F : Type u} {A B : Type v} [Field F] [Fintype A] [Fintype B]
    (b : B) : Word F (A × B) →ₗ[F] Word F A where
  toFun x a := x (a, b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restrict a word on `A × B` to the row with first coordinate `a`. -/
def rowRestriction {F : Type u} {A B : Type v} [Field F] [Fintype A] [Fintype B]
    (a : A) : Word F (A × B) →ₗ[F] Word F B where
  toFun x b := x (a, b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Words whose every column belongs to `C`. -/
def columnCode {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (C : LinearCode F A) : LinearCode F (A × B) where
  carrier := {
    carrier := {x | ∀ b, columnRestriction b x ∈ C.carrier}
    zero_mem' := fun _ => C.carrier.zero_mem
    add_mem' := fun hx hy b => C.carrier.add_mem (hx b) (hy b)
    smul_mem' := fun c _ hx b => C.carrier.smul_mem c (hx b) }

/-- Words whose every row belongs to `C`. -/
def rowCode {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (C : LinearCode F B) : LinearCode F (A × B) where
  carrier := {
    carrier := {x | ∀ a, rowRestriction a x ∈ C.carrier}
    zero_mem' := fun _ => C.carrier.zero_mem
    add_mem' := fun hx hy a => C.carrier.add_mem (hx a) (hy a)
    smul_mem' := fun c _ hx a => C.carrier.smul_mem c (hx a) }

/-- The product code `C_A ⊗ C_B`, characterized by its column and row constraints. -/
def tensorCode {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (CA : LinearCode F A) (CB : LinearCode F B) : LinearCode F (A × B) where
  carrier := (columnCode (B := B) CA).carrier ⊓ (rowCode (A := A) CB).carrier

/-- The dual-tensor sum `C_A ⊗ F^B + F^A ⊗ C_B`. -/
def dualTensorCode {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (CA : LinearCode F A) (CB : LinearCode F B) : LinearCode F (A × B) where
  carrier := (columnCode (B := B) CA).carrier ⊔ (rowCode (A := A) CB).carrier

@[simp]
theorem mem_tensorCode {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A]
    [Fintype B] (CA : LinearCode F A) (CB : LinearCode F B) (x : Word F (A × B)) :
    x ∈ (tensorCode CA CB).carrier ↔
      (∀ b, columnRestriction b x ∈ CA.carrier) ∧
      ∀ a, rowRestriction a x ∈ CB.carrier := by
  rfl

theorem mem_dualTensorCode_of_column {F : Type u} {A B : Type v} [Field F] [Fintype F]
    [Fintype A] [Fintype B] (CA : LinearCode F A) (CB : LinearCode F B)
    {x : Word F (A × B)} (hx : ∀ b, columnRestriction b x ∈ CA.carrier) :
    x ∈ (dualTensorCode CA CB).carrier := by
  exact Submodule.mem_sup_left hx

theorem mem_dualTensorCode_of_row {F : Type u} {A B : Type v} [Field F] [Fintype F]
    [Fintype A] [Fintype B] (CA : LinearCode F A) (CB : LinearCode F B)
    {x : Word F (A × B)} (hx : ∀ a, rowRestriction a x ∈ CB.carrier) :
    x ∈ (dualTensorCode CA CB).carrier := by
  exact Submodule.mem_sup_right hx

/-! ## Puncturing and robustness -/

/-- Coordinates retained after deleting the finite set `removed`. -/
abbrev KeptCoordinate {ι : Type v} [Fintype ι] (removed : Finset ι) :=
  {i : ι // i ∉ removed}

/-- Restrict a word to the coordinates not punctured away. -/
def punctureMap {F : Type u} {ι : Type v} [Field F] [Fintype ι] (removed : Finset ι) :
    Word F ι →ₗ[F] Word F (KeptCoordinate removed) where
  toFun x i := x i.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The image of a linear code after puncturing the selected coordinates. -/
def puncturedCode {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
    (C : LinearCode F ι) (removed : Finset ι) :
    LinearCode F (KeptCoordinate removed) where
  carrier := C.carrier.map (punctureMap removed)

@[simp]
theorem mem_puncturedCode {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
    (C : LinearCode F ι) (removed : Finset ι)
    (x : Word F (KeptCoordinate removed)) :
    x ∈ (puncturedCode C removed).carrier ↔
      ∃ y, y ∈ C.carrier ∧ punctureMap removed y = x := by
  exact Submodule.mem_map

/-- A support is covered by the indicated collection of rows and columns. -/
def SupportCovered {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (rows : Finset A) (columns : Finset B) : Prop :=
  hammingSupport x ⊆
    (rows.product (Finset.univ : Finset B)) ∪
      ((Finset.univ : Finset A).product columns)

/--
Robustness of the dual-tensor code up to weight `w`: a low-weight word is
supported on few rows and columns, with the source's distance-normalized bounds.
-/
def IsRobust {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B) (w : Nat) : Prop :=
  ∀ dA dB, MinimumDistance CA dA → MinimumDistance CB dB →
    ∀ x, x ∈ (dualTensorCode CA CB).carrier → HammingWeight x ≤ w →
      ∃ rows : Finset A, ∃ columns : Finset B,
        SupportCovered x rows columns ∧
          rows.card ≤ HammingWeight x / dB ∧
          columns.card ≤ HammingWeight x / dA

/-- Robustness remains valid after matching punctures of size at most `p`. -/
def IsRobustWithPunctureResistance {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (w p : Nat) : Prop :=
  ∀ removedA : Finset A, ∀ removedB : Finset B,
    removedA.card = removedB.card → removedA.card ≤ p →
      IsRobust (puncturedCode CA removedA) (puncturedCode CB removedB) w

/-! ## The finite random local-code experiment -/

/-- A pair consisting of an `r × |A|` generator matrix and an `r × |B|` check matrix.

The row type is universe-lifted so that `Matrix.toLin'` can interpret the matrices when
the local coordinate types live above `Type 0`; the lift does not change its cardinality. -/
abbrev RandomLocalCodeSample (r : Nat) (A B : Type v) :=
  Matrix (ULift.{v} (Fin r)) A (ZMod 2) × Matrix (ULift.{v} (Fin r)) B (ZMod 2)

/-- The row-span local code selected by the first random matrix. -/
def RandomLocalCodeSample.codeA {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B) : LinearCode (ZMod 2) A :=
  parityCheckRowCode (Matrix.toLin' sample.1)

/-- The kernel local code selected by the second random matrix. -/
def RandomLocalCodeSample.codeB {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B) : LinearCode (ZMod 2) B :=
  parityCheckKernelCode (Matrix.toLin' sample.2)

/-- The local event used by the source's finite random experiment. -/
def LocalCodeEvent {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (dimensionA dimensionB dA dB w p : Nat)
    (sample : RandomLocalCodeSample r A B) : Prop :=
  Dimension sample.codeA = dimensionA ∧
    Dimension sample.codeB = dimensionB ∧
    MinimumDistance sample.codeA dA ∧
    MinimumDistance sample.codeB dB ∧
    IsRobustWithPunctureResistance sample.codeA sample.codeB w p

/-- The finite set of samples satisfying a decidable event. -/
def eventFinset {Ω : Type u} [Fintype Ω] (event : Ω → Prop) [DecidablePred event] :
    Finset Ω :=
  Finset.univ.filter event

@[simp]
theorem mem_eventFinset {Ω : Type u} [Fintype Ω] (event : Ω → Prop)
    [DecidablePred event] (sample : Ω) :
    sample ∈ eventFinset event ↔ event sample := by
  simp [eventFinset]

/-! ## Left-right Cayley square complexes -/

/--
Finite left-right Cayley square-complex data.  `link (g, side)` identifies the
`A × B` link of a vertex with its incident squares.  The last law records the
source regularity that every square meets exactly two vertices on each side.
-/
structure LeftRightCayleySquareComplex
    (G A B Square : Type v) [Group G] [Fintype G] [Fintype A] [Fintype B]
    [Fintype Square] where
  leftGenerator : A → G
  rightGenerator : B → G
  leftInverse : Equiv.Perm A
  rightInverse : Equiv.Perm B
  leftGenerator_inverse : ∀ a, leftGenerator (leftInverse a) = (leftGenerator a)⁻¹
  rightGenerator_inverse : ∀ b, rightGenerator (rightInverse b) = (rightGenerator b)⁻¹
  noConjugacy : ∀ g a b, leftGenerator a * g ≠ g * rightGenerator b
  link : G × Bool → A × B → Square
  link_injective : ∀ vertex, Function.Injective (link vertex)
  square_side_degree : ∀ square side,
    (Finset.univ.filter fun g => ∃ ab, link (g, side) ab = square).card = 2

namespace LeftRightCayleySquareComplex

variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

/-- A vertex is incident to a square when that square occurs in its link. -/
def Incident (X : LeftRightCayleySquareComplex G A B Square)
    (vertex : G × Bool) (square : Square) : Prop :=
  ∃ ab, X.link vertex ab = square

/-- Every vertex has exactly `|A| |B|` incident squares. -/
theorem incidentSquares_card (X : LeftRightCayleySquareComplex G A B Square)
    (vertex : G × Bool) :
    (Finset.univ.image (X.link vertex)).card = Fintype.card A * Fintype.card B := by
  rw [Finset.card_image_of_injective _ (X.link_injective vertex)]
  simp

/-- Exactly two vertices on either side are incident to each square. -/
theorem incidentVerticesOnSide_card (X : LeftRightCayleySquareComplex G A B Square)
    (square : Square) (side : Bool) :
    (Finset.univ.filter fun g => X.Incident (g, side) square).card = 2 := by
  have hfilter :
      (Finset.univ.filter fun g => X.Incident (g, side) square) =
        (Finset.univ.filter fun g => ∃ ab, X.link (g, side) ab = square) := by
    ext g
    constructor
    · intro hg
      have hIncident := (Finset.mem_filter.mp hg).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ g, by
        simpa only [Incident] using hIncident⟩
    · intro hg
      have hIncident := (Finset.mem_filter.mp hg).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ g, by
        simpa only [Incident] using hIncident⟩
  rw [hfilter]
  exact X.square_side_degree square side

/-- Extend a local link word by zero to the global square coordinates. -/
def localExtension (X : LeftRightCayleySquareComplex G A B Square)
    (vertex : G × Bool) :
    Word (ZMod 2) (A × B) →ₗ[ZMod 2] Word (ZMod 2) Square where
  toFun x := ∑ ab : A × B, x ab • Pi.single (X.link vertex ab) 1
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, RingHom.id_apply, smul_eq_mul]

theorem localExtension_support_subset (X : LeftRightCayleySquareComplex G A B Square)
    (vertex : G × Bool) (x : Word (ZMod 2) (A × B)) :
    hammingSupport (X.localExtension vertex x) ⊆ Finset.univ.image (X.link vertex) := by
  intro square hsquare
  classical
  by_contra hnot
  have hzero : X.localExtension vertex x square = 0 := by
    simp only [localExtension, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
      Pi.smul_apply, Pi.single_apply]
    apply Finset.sum_eq_zero
    intro ab _hab
    have hne : X.link vertex ab ≠ square := by
      intro heq
      exact hnot (Finset.mem_image.2 ⟨ab, Finset.mem_univ _, heq⟩)
    split
    · next heq => exact (hne heq.symm).elim
    · simp
  exact (Finset.mem_filter.1 hsquare).2 hzero

end LeftRightCayleySquareComplex

/-! ## Global checks and the associated CSS code -/

/-- The linear map whose columns are a finite family of words. -/
def linearMapOfGenerators {F : Type u} {ι κ : Type v} [Field F] [Fintype ι] [Fintype κ]
    (generator : κ → Word F ι) : Word F κ →ₗ[F] Word F ι where
  toFun coefficient := ∑ k : κ, coefficient k • generator k
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, RingHom.id_apply, smul_eq_mul]

/-- Raw source data before the single CSS commutation law is supplied. -/
structure RawData
    (G A B Square XBasis ZBasis : Type v)
    [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
    [Fintype XBasis] [Fintype ZBasis] where
  complex : LeftRightCayleySquareComplex G A B Square
  codeA : LinearCode (ZMod 2) A
  codeB : LinearCode (ZMod 2) B
  xBasis : Module.Basis XBasis (ZMod 2) (tensorCode codeA.dual codeB.dual).carrier
  zBasis : Module.Basis ZBasis (ZMod 2) (tensorCode codeA codeB).carrier

namespace RawData

variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]

/-- A selected X-check obtained by extending one local tensor-code basis word. -/
def xGenerator (D : RawData G A B Square XBasis ZBasis) (check : G × XBasis) :
    Word (ZMod 2) Square :=
  D.complex.localExtension (check.1, true) (D.xBasis check.2).1

/-- A selected Z-check obtained by extending one local tensor-code basis word. -/
def zGenerator (D : RawData G A B Square XBasis ZBasis) (check : G × ZBasis) :
    Word (ZMod 2) Square :=
  D.complex.localExtension (check.1, false) (D.zBasis check.2).1

/-- X-check generator map. -/
def xGeneratorMap (D : RawData G A B Square XBasis ZBasis) :
    Word (ZMod 2) (G × XBasis) →ₗ[ZMod 2] Word (ZMod 2) Square :=
  linearMapOfGenerators D.xGenerator

/-- Z-check generator map. -/
def zGeneratorMap (D : RawData G A B Square XBasis ZBasis) :
    Word (ZMod 2) (G × ZBasis) →ₗ[ZMod 2] Word (ZMod 2) Square :=
  linearMapOfGenerators D.zGenerator

/-- First boundary: evaluate a qubit word against all selected X checks. -/
def boundary1 (D : RawData G A B Square XBasis ZBasis) :
    Word (ZMod 2) Square →ₗ[ZMod 2] Word (ZMod 2) (G × XBasis) :=
  wordLinearMapTranspose D.xGeneratorMap

/-- Second boundary: sum selected Z checks with the supplied coefficients. -/
def boundary2 (D : RawData G A B Square XBasis ZBasis) :
    Word (ZMod 2) (G × ZBasis) →ₗ[ZMod 2] Word (ZMod 2) Square :=
  D.zGeneratorMap

end RawData

/--
Quantum Tanner construction data.  The sole additional law is CSS
well-definedness (`X` and `Z` checks commute); no parameter lower bound,
probability statement, or comparison with another construction is stored.
-/
structure Data
    (G A B Square XBasis ZBasis : Type v)
    [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
    [Fintype XBasis] [Fintype ZBasis] extends
    RawData G A B Square XBasis ZBasis where
  boundary_squared : toRawData.boundary1.comp toRawData.boundary2 = 0

namespace Data

variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]

/-- The honest three-term binary chain complex extracted from Quantum Tanner data. -/
def chainComplex (D : Data G A B Square XBasis ZBasis) :
    ChainComplexData (ZMod 2)
      (Word (ZMod 2) (G × XBasis))
      (Word (ZMod 2) Square)
      (Word (ZMod 2) (G × ZBasis)) where
  boundary1 := D.toRawData.boundary1
  boundary2 := D.toRawData.boundary2
  boundary_squared := D.boundary_squared

/-- The associated binary CSS code. -/
def cssCode (D : Data G A B Square XBasis ZBasis) :=
  D.chainComplex.binaryCSSCode

/-- The block length is the number of squares (qubits). -/
def blockLength (_D : Data G A B Square XBasis ZBasis) : Nat :=
  Fintype.card Square

/-- The encoded dimension is the middle-homology dimension. -/
def encodedDimension (D : Data G A B Square XBasis ZBasis) : Nat :=
  Module.finrank (ZMod 2) D.chainComplex.middleHomology

/-- Exact algebraic parameters of one extracted Quantum Tanner CSS code. -/
def HasParameters (D : Data G A B Square XBasis ZBasis) (n k d : Nat) : Prop :=
  n = D.blockLength ∧
    k = D.encodedDimension ∧
    AlgebraicCSSMinimumDistance
      D.chainComplex.firstCoboundaryCheckCode
      D.chainComplex.middleBoundaryCode d

@[simp]
theorem blockLength_eq (D : Data G A B Square XBasis ZBasis) :
    D.blockLength = Fintype.card Square :=
  rfl

theorem encodedDimension_eq (D : Data G A B Square XBasis ZBasis) :
    D.encodedDimension =
      Dimension D.chainComplex.middleCycleCode -
        Dimension D.chainComplex.middleBoundaryCode := by
  exact D.chainComplex.finrank_middleHomology_eq

theorem hasParameters_iff (D : Data G A B Square XBasis ZBasis) (n k d : Nat) :
    D.HasParameters n k d ↔
      n = Fintype.card Square ∧
      k = Module.finrank (ZMod 2) D.chainComplex.middleHomology ∧
      AlgebraicCSSMinimumDistance
        D.chainComplex.firstCoboundaryCheckCode
        D.chainComplex.middleBoundaryCode d := by
  rfl

end Data

end QEC.Coding.QuantumTanner
