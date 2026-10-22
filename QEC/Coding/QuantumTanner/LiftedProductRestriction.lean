import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Selected lifted-product stabilizer supports

The ordered matrix formulas below are the selected construction in
[LZDec22, Section "Quantum Tanner codes from Lifted Product codes"].
They work over a noncommutative coefficient ring, in particular the binary
group algebra. The cancellation lemmas concern the auxiliary blocks only;
they do not assert the final Quantum Tanner check-space identification.
-/

namespace QEC.Coding.QuantumTanner.LiftedProductRestriction

variable {R A B C D C' D' : Type*} [Ring R]
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [Fintype C'] [Fintype D']

/-- Retained support of the source's full Z-stabilizer family. -/
def zRetained (hA HA : Matrix C A R) (U0 U1 : Matrix C B R) : Matrix A B R :=
  hA.transpose * U0 + HA.transpose * U1

/-- Retained support of the source's full X-stabilizer family. -/
def xRetained (hB HB : Matrix D B R) (V0 V1 : Matrix A D R) : Matrix A B R :=
  V0 * hB + V1 * HB

/-- Four auxiliary blocks, with the first Boolean indexing C0/C1. -/
def zAuxiliary (hB HB : Matrix D B R) (U0 U1 : Matrix C B R) :
    Matrix (Bool × C) (Bool × D) R :=
  fun c d =>
    if c.1 then
      if d.1 then (U1 * HB.transpose) c.2 d.2 else (U1 * hB.transpose) c.2 d.2
    else
      if d.1 then (U0 * HB.transpose) c.2 d.2 else (U0 * hB.transpose) c.2 d.2

/-- Four auxiliary blocks of the source's X-stabilizer family. -/
def xAuxiliary (hA HA : Matrix C A R) (V0 V1 : Matrix A D R) :
    Matrix (Bool × C) (Bool × D) R :=
  fun c d =>
    if c.1 then
      if d.1 then (HA * V1) c.2 d.2 else (HA * V0) c.2 d.2
    else
      if d.1 then (hA * V1) c.2 d.2 else (hA * V0) c.2 d.2

/-- The selected Z parameters are U0 = U0' GB and U1 = U1' gB. -/
def selectedZRetained (hA HA : Matrix C A R) (gB GB : Matrix D' B R)
    (U0 U1 : Matrix C D' R) : Matrix A B R :=
  zRetained hA HA (U0 * GB) (U1 * gB)

/-- The selected X parameters are V0 = gA^T V0' and V1 = GA^T V1'. -/
def selectedXRetained (hB HB : Matrix D B R) (gA GA : Matrix C' A R)
    (V0 V1 : Matrix C' D R) : Matrix A B R :=
  xRetained hB HB (gA.transpose * V0) (GA.transpose * V1)

omit [Fintype C] [Fintype D] in
/-- Local dual-check cancellation eliminates both off-diagonal Z blocks.
These local matrix identities are later derived from dual parity-check data. -/
theorem zAuxiliary_offDiagonal_zero
    (hB HB : Matrix D B R) (gB GB : Matrix D' B R)
    (h0 : gB * hB.transpose = 0) (h1 : GB * HB.transpose = 0)
    (U0 U1 : Matrix C D' R) (c : C) (d : D) :
    zAuxiliary hB HB (U0 * GB) (U1 * gB) (false, c) (true, d) = 0 ∧
      zAuxiliary hB HB (U0 * GB) (U1 * gB) (true, c) (false, d) = 0 := by
  constructor
  · simp [zAuxiliary, Matrix.mul_assoc, h1]
  · simp [zAuxiliary, Matrix.mul_assoc, h0]

omit [Fintype C] [Fintype D] in
/-- Local dual-check cancellation eliminates both diagonal X blocks. -/
theorem xAuxiliary_diagonal_zero
    (hA HA : Matrix C A R) (gA GA : Matrix C' A R)
    (h0 : hA * gA.transpose = 0) (h1 : HA * GA.transpose = 0)
    (V0 V1 : Matrix C' D R) (c : C) (d : D) :
    xAuxiliary hA HA (gA.transpose * V0) (GA.transpose * V1)
        (false, c) (false, d) = 0 ∧
      xAuxiliary hA HA (gA.transpose * V0) (GA.transpose * V1)
        (true, c) (true, d) = 0 := by
  constructor
  · simp [xAuxiliary, ← Matrix.mul_assoc, h0]
  · simp [xAuxiliary, ← Matrix.mul_assoc, h1]

omit [Fintype C] [Fintype D] in
/-- Every auxiliary coordinate has at least one selected support equal to zero.
No equality of retained check spaces is assumed or concluded here. -/
theorem selected_auxiliary_pointwise_disjoint
    (hA HA : Matrix C A R) (hB HB : Matrix D B R)
    (gA GA : Matrix C' A R) (gB GB : Matrix D' B R)
    (hA0 : hA * gA.transpose = 0) (hA1 : HA * GA.transpose = 0)
    (hB0 : gB * hB.transpose = 0) (hB1 : GB * HB.transpose = 0)
    (U0 U1 : Matrix C D' R) (V0 V1 : Matrix C' D R)
    (c : Bool × C) (d : Bool × D) :
    zAuxiliary hB HB (U0 * GB) (U1 * gB) c d = 0 ∨
      xAuxiliary hA HA (gA.transpose * V0) (GA.transpose * V1) c d = 0 := by
  rcases c with ⟨s, c⟩
  rcases d with ⟨t, d⟩
  cases s <;> cases t
  · exact Or.inr (xAuxiliary_diagonal_zero hA HA gA GA hA0 hA1 V0 V1 c d).1
  · exact Or.inl (zAuxiliary_offDiagonal_zero hB HB gB GB hB0 hB1 U0 U1 c d).1
  · exact Or.inl (zAuxiliary_offDiagonal_zero hB HB gB GB hB0 hB1 U0 U1 c d).2
  · exact Or.inr (xAuxiliary_diagonal_zero hA HA gA GA hA0 hA1 V0 V1 c d).2

noncomputable section GroupAlgebra

variable {F G I J K : Type*} [CommRing F] [Group G] [Fintype K]

/-- Multiply each scalar column by its specified group-basis element on the right.
This is the source's ordered h D, not commutative scalar matrix multiplication. -/
def twistedMatrix (h : Matrix I K F) (s : K → G) : Matrix I K (MonoidAlgebra F G) :=
  fun i k => MonoidAlgebra.single (s k) (h i k)

/-- Scalar matrices embedded at the identity group element. -/
def scalarMatrix (h : Matrix I K F) : Matrix I K (MonoidAlgebra F G) :=
  twistedMatrix h (fun _ => 1)

/-- Opposite column twists cancel in their original order, without assuming G abelian. -/
theorem twisted_mul_inverse_twisted_transpose
    (h : Matrix I K F) (g : Matrix J K F) (s : K → G) :
    twistedMatrix h s * (twistedMatrix g (fun k => (s k)⁻¹)).transpose =
      scalarMatrix (G := G) (h * g.transpose) := by
  funext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, twistedMatrix, scalarMatrix,
    MonoidAlgebra.single_mul_single, mul_inv_cancel]
  exact (map_sum (MonoidAlgebra.singleAddHom 1)
    (fun k => h i k * g j k) Finset.univ).symm

/-- A raw scalar orthogonality identity implies the corresponding twisted cancellation. -/
theorem twisted_mul_inverse_twisted_transpose_eq_zero
    (h : Matrix I K F) (g : Matrix J K F) (s : K → G)
    (hzero : h * g.transpose = 0) :
    twistedMatrix h s * (twistedMatrix g (fun k => (s k)⁻¹)).transpose = 0 := by
  rw [twisted_mul_inverse_twisted_transpose, hzero]
  ext i j
  simp [scalarMatrix, twistedMatrix]

/-- The untwisted scalar embedding preserves a raw dual-check cancellation. -/
theorem scalar_mul_scalar_transpose_eq_zero
    (h : Matrix I K F) (g : Matrix J K F) (hzero : h * g.transpose = 0) :
    scalarMatrix (G := G) h * (scalarMatrix (G := G) g).transpose = 0 := by
  simpa only [scalarMatrix, inv_one] using
    twisted_mul_inverse_twisted_transpose_eq_zero h g (fun _ => (1 : G)) hzero

omit [Fintype C] [Fintype D] in
/-- Instantiate the auxiliary-support separation from raw local dual checks.
The only zero-product inputs are the two scalar dual-check identities in
[LZDec22, Section "Quantum Tanner codes from Lifted Product codes"].
All twisted group-algebra cancellations are derived, not supplied as data. -/
theorem selected_groupAlgebra_auxiliary_disjoint
    (hA : Matrix C A F) (hB : Matrix D B F)
    (gA : Matrix C' A F) (gB : Matrix D' B F)
    (a : A → G) (b : B → G)
    (hDualA : gA * hA.transpose = 0) (hDualB : gB * hB.transpose = 0)
    (U0 U1 : Matrix C D' (MonoidAlgebra F G))
    (V0 V1 : Matrix C' D (MonoidAlgebra F G))
    (c : Bool × C) (d : Bool × D) :
    zAuxiliary (scalarMatrix hB) (twistedMatrix hB b)
        (U0 * twistedMatrix gB (fun k => (b k)⁻¹)) (U1 * scalarMatrix gB) c d = 0 ∨
      xAuxiliary (scalarMatrix hA) (twistedMatrix hA a)
        ((scalarMatrix gA).transpose * V0)
        ((twistedMatrix gA (fun k => (a k)⁻¹)).transpose * V1) c d = 0 := by
  have hDualA' : hA * gA.transpose = 0 := by
    have ht := congrArg Matrix.transpose hDualA
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero]
      using ht
  apply selected_auxiliary_pointwise_disjoint
  · exact scalar_mul_scalar_transpose_eq_zero hA gA hDualA'
  · exact twisted_mul_inverse_twisted_transpose_eq_zero hA gA a hDualA'
  · exact scalar_mul_scalar_transpose_eq_zero gB hB hDualB
  · simpa only [inv_inv] using
      twisted_mul_inverse_twisted_transpose_eq_zero gB hB (fun k => (b k)⁻¹) hDualB

end GroupAlgebra

end QEC.Coding.QuantumTanner.LiftedProductRestriction
