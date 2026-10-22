import QEC.Coding.QLDPC.SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Fiber-bundle chain complexes

This module formalizes the twisted boundary used by Hastings--Haah--O'Donnell.
The source route is
`hastings-haah-odonnell-2020-fiber-bundle/bundle.tex:372-409`
(`eq:auto-consistency`, `eq:twist-def`, and `bdef`).

The base is one-dimensional.  A fiber automorphism acts by permutations in
degrees zero and one and commutes with the fiber boundary.  A connection
selects one such automorphism for each incident base-cell pair.  Over
`ZMod 2`, the two terms in the composite twisted boundary cancel.
-/

namespace QEC.Coding.FiberBundle

universe u

/-- Coordinates of total degree zero. -/
abbrev C0Index (baseZero fiberZero : Type*) := baseZero × fiberZero

/-- Coordinates of total degree one: horizontal followed by vertical cells. -/
abbrev QubitIndex
    (baseZero baseOne fiberZero fiberOne : Type*) :=
  Sum (baseOne × fiberZero) (baseZero × fiberOne)

/-- Coordinates of total degree two. -/
abbrev C2Index (baseOne fiberOne : Type*) := baseOne × fiberOne

/--
A cellular fiber automorphism in degrees zero and one.

The pointwise naturality equation says exactly that applying the permutation
before or after the fiber boundary gives the same chain.
-/
structure FiberAutomorphism
    (fiberZero fiberOne : Type*) [Fintype fiberZero] [Fintype fiberOne]
    (fiberBoundary : Matrix fiberZero fiberOne (ZMod 2)) where
  onZero : Equiv.Perm fiberZero
  onOne : Equiv.Perm fiberOne
  boundary_naturality :
    ∀ i j, fiberBoundary (onZero i) (onOne j) = fiberBoundary i j

/--
Finite source data for an HHO20 twisted product over a one-dimensional base.

The connection is total as a function, but its value contributes to the
boundary only when the corresponding base-boundary coefficient is nonzero.
-/
structure Data
    (baseZero baseOne fiberZero fiberOne : Type*)
    [Fintype fiberZero] [Fintype fiberOne] where
  baseBoundary : Matrix baseZero baseOne (ZMod 2)
  fiberBoundary : Matrix fiberZero fiberOne (ZMod 2)
  connection :
    baseOne → baseZero →
      FiberAutomorphism fiberZero fiberOne fiberBoundary

/-- The exact two-block number of total-degree-one coordinates. -/
theorem card_qubitIndex
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype baseZero] [Fintype baseOne]
    [Fintype fiberZero] [Fintype fiberOne] :
    Fintype.card (QubitIndex baseZero baseOne fiberZero fiberOne) =
      Fintype.card baseOne * Fintype.card fiberZero +
        Fintype.card baseZero * Fintype.card fiberOne := by
  simp [QubitIndex]

/-- The total-degree-one to total-degree-zero twisted boundary matrix. -/
def boundary1Matrix
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype fiberZero] [Fintype fiberOne]
    [DecidableEq baseZero] [DecidableEq fiberZero]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    Matrix
      (C0Index baseZero fiberZero)
      (QubitIndex baseZero baseOne fiberZero fiberOne)
      (ZMod 2) :=
  fun (a, i) q =>
    match q with
    | Sum.inl (b, j) =>
        if i = (D.connection b a).onZero j
        then D.baseBoundary a b
        else 0
    | Sum.inr (a', j) =>
        if a = a' then D.fiberBoundary i j else 0

/-- The total-degree-two to total-degree-one twisted boundary matrix. -/
def boundary2Matrix
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype fiberZero] [Fintype fiberOne]
    [DecidableEq baseOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    Matrix
      (QubitIndex baseZero baseOne fiberZero fiberOne)
      (C2Index baseOne fiberOne)
      (ZMod 2) :=
  fun q (b, j) =>
    match q with
    | Sum.inl (b', i) =>
        if b' = b then D.fiberBoundary i j else 0
    | Sum.inr (a, j') =>
        if j' = (D.connection b a).onOne j
        then D.baseBoundary a b
        else 0

@[simp]
theorem boundary1Matrix_inl_apply
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype fiberZero] [Fintype fiberOne]
    [DecidableEq baseZero] [DecidableEq fiberZero]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (a : baseZero) (i j : fiberZero) (b : baseOne) :
    boundary1Matrix D (a, i) (Sum.inl (b, j)) =
      if i = (D.connection b a).onZero j
      then D.baseBoundary a b
      else 0 := by
  rfl

@[simp]
theorem boundary1Matrix_inr_apply
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype fiberZero] [Fintype fiberOne]
    [DecidableEq baseZero] [DecidableEq fiberZero]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (a a' : baseZero) (i : fiberZero) (j : fiberOne) :
    boundary1Matrix D (a, i) (Sum.inr (a', j)) =
      if a = a' then D.fiberBoundary i j else 0 := by
  rfl

@[simp]
theorem boundary2Matrix_inl_apply
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype fiberZero] [Fintype fiberOne]
    [DecidableEq baseOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (b b' : baseOne) (i : fiberZero) (j : fiberOne) :
    boundary2Matrix D (Sum.inl (b', i)) (b, j) =
      if b' = b then D.fiberBoundary i j else 0 := by
  rfl

@[simp]
theorem boundary2Matrix_inr_apply
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype fiberZero] [Fintype fiberOne]
    [DecidableEq baseOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (a : baseZero) (b : baseOne) (j j' : fiberOne) :
    boundary2Matrix D (Sum.inr (a, j')) (b, j) =
      if j' = (D.connection b a).onOne j
      then D.baseBoundary a b
      else 0 := by
  rfl

/--
The two HHO20 twisted boundary matrices compose to zero.

The proof exposes both paths through a total-degree-one basis.  Naturality of
the selected fiber automorphism identifies their coefficients, and the two
equal coefficients cancel over `ZMod 2`.
-/
theorem boundary1Matrix_mul_boundary2Matrix
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    boundary1Matrix D * boundary2Matrix D = 0 := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, boundary1Matrix_inl_apply,
    boundary1Matrix_inr_apply, boundary2Matrix_inl_apply,
    boundary2Matrix_inr_apply]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  have hhorizontal :
      (∑ x : fiberZero,
        if i = (D.connection b a).onZero x
        then D.baseBoundary a b * D.fiberBoundary x j
        else 0) =
      D.baseBoundary a b *
        D.fiberBoundary ((D.connection b a).onZero.symm i) j := by
    calc
      _ = ∑ y : fiberZero,
          if i = y
          then D.baseBoundary a b *
            D.fiberBoundary ((D.connection b a).onZero.symm y) j
          else 0 := by
            apply Fintype.sum_equiv (D.connection b a).onZero
            intro x
            simp
      _ = _ := by simp
  have hnaturality :
      D.fiberBoundary i ((D.connection b a).onOne j) =
        D.fiberBoundary ((D.connection b a).onZero.symm i) j := by
    simpa using (D.connection b a).boundary_naturality
      ((D.connection b a).onZero.symm i) j
  have hvertical :
      (∑ x : baseZero,
        if a = x
        then D.fiberBoundary i ((D.connection b x).onOne j) *
          D.baseBoundary x b
        else 0) =
      D.fiberBoundary i ((D.connection b a).onOne j) *
        D.baseBoundary a b := by
    classical
    rw [Finset.sum_eq_single a]
    · simp
    · intro x _hx hxa
      simp [Ne.symm hxa]
    · simp
  rw [hhorizontal, hvertical]
  change _ = (0 : ZMod 2)
  rw [hnaturality]
  rw [mul_comm
    (D.fiberBoundary ((D.connection b a).onZero.symm i) j)
    (D.baseBoundary a b)]
  let x :=
    D.baseBoundary a b *
      D.fiberBoundary ((D.connection b a).onZero.symm i) j
  change x + x = 0
  calc
    x + x = x + (-x) := by rw [ZMod.neg_eq_self_mod_two]
    _ = 0 := add_neg_cancel x

/-- The first twisted boundary as a linear map on finite-coordinate words. -/
noncomputable def boundary1
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne) →ₗ[ZMod 2]
      Word (ZMod 2) (C0Index baseZero fiberZero) :=
  Matrix.toLin' (boundary1Matrix D)

/-- The second twisted boundary as a linear map on finite-coordinate words. -/
noncomputable def boundary2
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    Word (ZMod 2) (C2Index baseOne fiberOne) →ₗ[ZMod 2]
      Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne) :=
  Matrix.toLin' (boundary2Matrix D)

/-- The two HHO20 twisted boundary maps compose to zero. -/
theorem boundary_squared
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    (boundary1 D).comp (boundary2 D) = 0 := by
  change (Matrix.toLin' (boundary1Matrix D)).comp
    (Matrix.toLin' (boundary2Matrix D)) = 0
  rw [← Matrix.toLin'_mul]
  rw [boundary1Matrix_mul_boundary2Matrix]
  simp

/-- The three-term chain complex defined by the HHO20 twisted boundary. -/
noncomputable def chainComplex
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    ChainComplexData
      (ZMod 2)
      (Word (ZMod 2) (C0Index baseZero fiberZero))
      (Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne))
      (Word (ZMod 2) (C2Index baseOne fiberOne)) where
  boundary1 := boundary1 D
  boundary2 := boundary2 D
  boundary_squared := boundary_squared D

/-! ## Induced binary CSS code -/

/-- The binary CSS code induced by the twisted fiber-bundle chain complex. -/
noncomputable def binaryCSSCode
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    CSSCode
      (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)
      (Semantics.Qubit.QubitRegister
        (QubitIndex baseZero baseOne fiberZero fiberOne)) :=
  (chainComplex D).binaryCSSCode

@[simp]
theorem binaryCSSCode_xCode
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    (binaryCSSCode D).xCode = (chainComplex D).firstCoboundaryCheckCode := by
  rfl

@[simp]
theorem binaryCSSCode_zCode
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    (binaryCSSCode D).zCode = (chainComplex D).middleBoundaryCode := by
  rfl

/-- Package the fiber-bundle CSS code as a chain-complex code. -/
noncomputable def binaryChainComplexCode
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :=
  (chainComplex D).binaryChainComplexCode

/-- The exact induced stabilizer satisfies the repository's binary source-validity contract. -/
theorem binaryCSSCode_stabilizer_isSourceValidBinary
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    (binaryCSSCode D).stabilizer.IsSourceValidBinary := by
  exact (chainComplex D).binaryCSSCode_stabilizer_isSourceValidBinary

/-- Package the induced stabilizer together with binary source validity. -/
noncomputable def binarySourceValidStabilizer
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    StabilizerCode.SourceValidBinary
      (QubitIndex baseZero baseOne fiberZero fiberOne) :=
  (chainComplex D).binaryCSSSourceValidStabilizer

/-- The semantic carrier dimension is determined by middle homology. -/
theorem binaryCSSCode_finrank_carrier
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    Module.finrank Complex (binaryCSSCode D).stabilizer.code.carrier =
      2 ^ Module.finrank (ZMod 2) (chainComplex D).middleHomology := by
  exact
    QEC.Coding.ChainComplexData.binaryCSSCode_finrank_stabilizer_code_carrier_eq_pow_finrank_middleHomology
      (chainComplex D)

/-- Exact pure-X minimum distance for the induced fiber-bundle CSS code. -/
abbrev BinaryPureXMinimumDistance
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) (dX : Nat) : Prop :=
  PureXLogicalMinimumDistance
    (binaryCSSCode D).xCode (binaryCSSCode D).zCode dX

/-- Exact pure-Z minimum distance for the induced fiber-bundle CSS code. -/
abbrev BinaryPureZMinimumDistance
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) (dZ : Nat) : Prop :=
  PureZLogicalMinimumDistance
    (binaryCSSCode D).xCode (binaryCSSCode D).zCode dZ

/-- Exact algebraic CSS minimum distance for the induced fiber-bundle code. -/
abbrev BinaryAlgebraicCSSMinimumDistance
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) (d : Nat) : Prop :=
  AlgebraicCSSMinimumDistance
    (binaryCSSCode D).xCode (binaryCSSCode D).zCode d

/-- Exact X and Z sector minima combine into the minimum of the two distances. -/
theorem binaryAlgebraicCSSMinimumDistance_of_sector_minima
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    {dX dZ : Nat}
    (hX : BinaryPureXMinimumDistance D dX)
    (hZ : BinaryPureZMinimumDistance D dZ) :
    BinaryAlgebraicCSSMinimumDistance D (min dX dZ) := by
  exact algebraicCSSMinimumDistance_of_sector_minima hX hZ

/-! ## Cycle fibers and rotation connections -/

/--
The cellular boundary matrix of a cycle with `n` vertices and `n` edges.

The edge at position `j` is incident to the vertices at `j` and `j + 1`.
Signs disappear over `ZMod 2`.
-/
def cycleBoundary (n : Nat) [NeZero n] :
    Matrix (ZMod n) (ZMod n) (ZMod 2) :=
  fun i j => if i = j ∨ i = j + 1 then 1 else 0

/-- A simultaneous rotation of the zero- and one-cells of a cycle. -/
def cycleRotationAutomorphism (n : Nat) [NeZero n] (t : ZMod n) :
    FiberAutomorphism (ZMod n) (ZMod n) (cycleBoundary n) where
  onZero := Equiv.addRight t
  onOne := Equiv.addRight t
  boundary_naturality := by
    intro i j
    simp only [cycleBoundary]
    congr 1
    apply propext
    constructor
    · intro h
      rcases h with h | h
      · left
        exact add_right_cancel h
      · right
        apply add_right_cancel (b := t)
        simpa [add_assoc, add_comm, add_left_comm] using h
    · intro h
      rcases h with h | h
      · left
        simp [h]
      · right
        simp [h, add_assoc, add_comm]

/--
The HHO20 twisted product with a cycle fiber and arbitrary rotation-valued
connection selected by the construction.
-/
def cycleData
    {baseZero baseOne : Type*}
    [Fintype baseZero] [Fintype baseOne]
    (n : Nat) [NeZero n]
    (baseBoundary : Matrix baseZero baseOne (ZMod 2))
    (twist : baseOne → baseZero → ZMod n) :
    Data baseZero baseOne (ZMod n) (ZMod n) where
  baseBoundary := baseBoundary
  fiberBoundary := cycleBoundary n
  connection := fun b a => cycleRotationAutomorphism n (twist b a)

/--
One of the `ell` rotations by a multiple of `ell` in the cycle of length
`ell^2`.
-/
def multipleRotation (ell : Nat) [NeZero ell] (k : Fin ell) :
    ZMod (ell * ell) :=
  (k.val * ell : Nat)

@[simp]
theorem multipleRotation_val
    (ell : Nat) [NeZero ell] (k : Fin ell) :
    multipleRotation ell k = (k.val * ell : Nat) := by
  rfl

/--
The exact HHO20 circle-bundle source data: both fiber cell sets have size
`ell^2`, and every connection value is definitionally a multiple of `ell`.
-/
def multipleRotationCycleData
    {baseZero baseOne : Type*}
    [Fintype baseZero] [Fintype baseOne]
    (ell : Nat) [NeZero ell]
    (baseBoundary : Matrix baseZero baseOne (ZMod 2))
    (twistIndex : baseOne → baseZero → Fin ell) :
    Data baseZero baseOne (ZMod (ell * ell)) (ZMod (ell * ell)) :=
  cycleData (ell * ell) baseBoundary
    (fun b a => multipleRotation ell (twistIndex b a))

/-- A cycle of length `n` has exactly `n` zero-cells and `n` one-cells. -/
theorem card_cycleCells (n : Nat) [NeZero n] :
    Fintype.card (ZMod n) = n :=
  ZMod.card n

/-- The exact HHO20 two-block qubit count for a cycle fiber. -/
theorem card_cycleQubitIndex
    {baseZero baseOne : Type*}
    [Fintype baseZero] [Fintype baseOne]
    (n : Nat) [NeZero n] :
    Fintype.card
      (QubitIndex baseZero baseOne (ZMod n) (ZMod n)) =
      Fintype.card baseOne * n + Fintype.card baseZero * n := by
  rw [card_qubitIndex, ZMod.card n]

end QEC.Coding.FiberBundle
