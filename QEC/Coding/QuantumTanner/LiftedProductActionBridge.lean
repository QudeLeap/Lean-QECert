import QEC.Coding.ExpanderCodes.LiftedProduct
import QEC.Coding.QuantumTanner.LiftedProductRestriction

/-!
# Canonical regular-action normalization of the selected bridge

The coordinate convention for [LZDec22, Section "Quantum Tanner codes from
Lifted Product codes"] uses the actual lifted-product boundary matrices.
The retained Z block uses left regular action; the retained X block is a
transposed right regular action. Their inverse shifts are adjoints, not a
commutativity assumption on the group. The auxiliary blocks retain the
source's ordered formulas. This module does not yet identify both Tanner
check spaces.
-/

namespace QEC.Coding.QuantumTanner.LiftedProductActionBridge

open QEC.Coding.LiftedProduct
open QEC.Coding.QuantumTanner.LiftedProductRestriction

noncomputable section

variable {G A B C D : Type*} [Group G] [Fintype G] [DecidableEq G]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

/-- The index-exchanged lifted product whose boundaries give the bridge checks.
The B matrix carries inverse A shifts because Z uses left regular action. -/
def canonicalData (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (a : A → G) (b : B → G) : Data (ZMod 2) G (Bool × D) B A (Bool × C) where
  A := fun d k => if d.1 then twistedMatrix hB b d.2 k else scalarMatrix hB d.2 k
  B := fun k c => if c.1 then twistedMatrix hA (fun i => (a i)⁻¹) c.2 k
    else scalarMatrix hA c.2 k

/-- Retained square coordinates, in the source's A/B order. -/
def retainedCoordinate (a : A) (b : B) (g : G) :
    QubitIndex (Bool × D) B A (Bool × C) G := Sum.inl (b, a, g)

/-- The same index exchange on auxiliary coordinates, with no deletion yet. -/
def auxiliaryCoordinate (c : Bool × C) (d : Bool × D) (g : G) :
    QubitIndex (Bool × D) B A (Bool × C) G := Sum.inr (d, c, g)

omit [Fintype G] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D] in
/-- A group-basis left action shifts its output by left multiplication. -/
theorem leftRegular_single (k go gi : G) (r : ZMod 2) :
    leftRegularMatrix (MonoidAlgebra.single k r) go gi =
      if go = k * gi then r else 0 := by
  have h : k = go * gi⁻¹ ↔ go = k * gi := by
    rw [eq_comm, mul_inv_eq_iff_eq_mul]
  simp only [leftRegularMatrix, MonoidAlgebra.coeff_single, Finsupp.single_apply, h]

omit [Fintype G] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D] in
/-- A group-basis right action shifts its output by right multiplication. -/
theorem rightRegular_single (k go gi : G) (r : ZMod 2) :
    rightRegularMatrix (MonoidAlgebra.single k r) go gi =
      if go = gi * k then r else 0 := by
  have h : k = gi⁻¹ * go ↔ go = gi * k := by
    rw [eq_comm, inv_mul_eq_iff_eq_mul]
  simp only [rightRegularMatrix, MonoidAlgebra.coeff_single, Finsupp.single_apply, h]

/-- Actual Z boundary entries on the retained qubits, including the inverse A shift. -/
theorem z_retained_entry (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (a : A → G) (b : B → G) (s : Bool) (c : C) (b₀ : B) (u : G)
    (i : A) (j : B) (g : G) :
    boundary2Matrix (canonicalData hA hB a b) (retainedCoordinate i j g)
        (b₀, (s, c), u) =
      if j = b₀ then
        if g = (if s then (a i)⁻¹ * u else u) then hA c i else 0
      else 0 := by
  cases s <;> simp [retainedCoordinate, canonicalData, scalarMatrix, twistedMatrix,
    leftRegular_single]

/-- Actual transposed X boundary entries: the B shift is adjointed. -/
theorem x_retained_entry (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (a : A → G) (b : B → G) (t : Bool) (d : D) (a₀ : A) (u : G)
    (i : A) (j : B) (g : G) :
    boundary1Matrix (canonicalData hA hB a b) ((t, d), a₀, u)
        (retainedCoordinate i j g) =
      if a₀ = i then
        if u = (if t then g * b j else g) then hB d j else 0
      else 0 := by
  cases t <;> simp [retainedCoordinate, canonicalData, scalarMatrix, twistedMatrix,
    rightRegular_single]

/-- Actual Z auxiliary entries retain the positive right B shift. -/
theorem z_auxiliary_entry (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (a : A → G) (b : B → G) (s : Bool) (c : C) (j : B) (u : G)
    (c₀ : Bool × C) (t : Bool) (d : D) (g : G) :
    boundary2Matrix (canonicalData hA hB a b)
        (auxiliaryCoordinate c₀ (t, d) g) (j, (s, c), u) =
      if c₀ = (s, c) then
        if g = (if t then u * b j else u) then hB d j else 0
      else 0 := by
  cases t <;> simp [auxiliaryCoordinate, canonicalData, scalarMatrix, twistedMatrix,
    rightRegular_single]

/-- Actual X auxiliary entries retain the positive left A shift.
The boundary sign disappears only because the coefficient field is binary. -/
theorem x_auxiliary_entry (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (a : A → G) (b : B → G) (t : Bool) (d : D) (i : A) (u : G)
    (s : Bool) (c : C) (d₀ : Bool × D) (g : G) :
    boundary1Matrix (canonicalData hA hB a b) ((t, d), i, u)
        (auxiliaryCoordinate (s, c) d₀ g) =
      if (t, d) = d₀ then
        if u = (if s then (a i)⁻¹ * g else g) then hA c i else 0
      else 0 := by
  cases s <;> simp [auxiliaryCoordinate, canonicalData, scalarMatrix, twistedMatrix,
    leftRegular_single]

/-- Full Z support, before restricting the stabilizer parameters or puncturing. -/
def zWord (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (a : A → G) (b : B → G) (U : C2Index B (Bool × C) G → ZMod 2) :=
  (boundary2Matrix (canonicalData hA hB a b)).mulVec U

/-- Full X support uses the transpose of the actual first boundary. -/
def xWord (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (a : A → G) (b : B → G) (V : C0Index (Bool × D) A G → ZMod 2) :=
  (boundary1Matrix (canonicalData hA hB a b)).transpose.mulVec V

/-- Coefficient words of the source's two Z parameter matrices. -/
def zParameter (U0 U1 : Matrix C B (MonoidAlgebra (ZMod 2) G)) :
    C2Index B (Bool × C) G → ZMod 2 :=
  fun (j, (s, c), u) => (if s then U1 c j else U0 c j).coeff u

/-- Coefficient words of the source's two X parameter matrices. -/
def xParameter (V0 V1 : Matrix A D (MonoidAlgebra (ZMod 2) G)) :
    C0Index (Bool × D) A G → ZMod 2 :=
  fun ((t, d), i, u) => (if t then V1 i d else V0 i d).coeff u

/-- The inverse A twist in retained Z support is determined by the boundary. -/
theorem zWord_retained_coeff (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (a : A → G) (b : B → G)
    (U0 U1 : Matrix C B (MonoidAlgebra (ZMod 2) G)) (i : A) (j : B) (g : G) :
    zWord hA hB a b (zParameter U0 U1) (retainedCoordinate i j g) =
      (∑ c : C, hA c i * (U0 c j).coeff g) +
        ∑ c : C, hA c i * (U1 c j).coeff (a i * g) := by
  simp only [zWord, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    z_retained_entry]
  simp [zParameter, eq_inv_mul_iff_mul_eq, eq_comm, add_comm]

/-- The inverse B twist in retained X support is determined by the transpose. -/
theorem xWord_retained_coeff (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (a : A → G) (b : B → G)
    (V0 V1 : Matrix A D (MonoidAlgebra (ZMod 2) G)) (i : A) (j : B) (g : G) :
    xWord hA hB a b (xParameter V0 V1) (retainedCoordinate i j g) =
      (∑ d : D, hB d j * (V0 i d).coeff g) +
        ∑ d : D, hB d j * (V1 i d).coeff (g * b j) := by
  simp only [xWord, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Fintype.sum_prod_type, x_retained_entry]
  simp [xParameter, eq_comm, add_comm]

/-- Actual Z auxiliary coefficients are the source's ordered right multiplication. -/
theorem zWord_auxiliary_coeff (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (a : A → G) (b : B → G)
    (U0 U1 : Matrix C B (MonoidAlgebra (ZMod 2) G))
    (s t : Bool) (c : C) (d : D) (g : G) :
    zWord hA hB a b (zParameter U0 U1) (auxiliaryCoordinate (s, c) (t, d) g) =
      ∑ j : B, hB d j * (if s then U1 c j else U0 c j).coeff
        (if t then g * (b j)⁻¹ else g) := by
  simp only [zWord, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    z_auxiliary_entry]
  have shift (j : B) (u : G) : g = u * b j ↔ u = g * (b j)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, eq_comm]
  cases s <;> cases t <;> simp [zParameter, shift, eq_comm]

/-- Actual X auxiliary coefficients are the source's ordered left multiplication. -/
theorem xWord_auxiliary_coeff (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (a : A → G) (b : B → G)
    (V0 V1 : Matrix A D (MonoidAlgebra (ZMod 2) G))
    (s t : Bool) (c : C) (d : D) (g : G) :
    xWord hA hB a b (xParameter V0 V1) (auxiliaryCoordinate (s, c) (t, d) g) =
      ∑ i : A, hA c i * (if t then V1 i d else V0 i d).coeff
        (if s then (a i)⁻¹ * g else g) := by
  simp only [xWord, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Fintype.sum_prod_type, x_auxiliary_entry]
  cases s <;> cases t <;> simp [xParameter, eq_comm]

/-- Coefficientwise identification of actual Z auxiliaries with the ordered source blocks. -/
theorem zWord_auxiliary_eq (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (a : A → G) (b : B → G)
    (U0 U1 : Matrix C B (MonoidAlgebra (ZMod 2) G))
    (c : Bool × C) (d : Bool × D) (g : G) :
    zWord hA hB a b (zParameter U0 U1) (auxiliaryCoordinate c d g) =
      (zAuxiliary (scalarMatrix hB) (twistedMatrix hB b) U0 U1 c d).coeff g := by
  rcases c with ⟨s, c⟩
  rcases d with ⟨t, d⟩
  rw [zWord_auxiliary_coeff]
  cases s <;> cases t <;>
    simp [zAuxiliary, scalarMatrix, twistedMatrix, Matrix.mul_apply,
      MonoidAlgebra.coeff_mul_single_apply, mul_comm]

/-- Coefficientwise identification of actual X auxiliaries with the ordered source blocks. -/
theorem xWord_auxiliary_eq (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (a : A → G) (b : B → G)
    (V0 V1 : Matrix A D (MonoidAlgebra (ZMod 2) G))
    (c : Bool × C) (d : Bool × D) (g : G) :
    xWord hA hB a b (xParameter V0 V1) (auxiliaryCoordinate c d g) =
      (xAuxiliary (scalarMatrix hA) (twistedMatrix hA a) V0 V1 c d).coeff g := by
  rcases c with ⟨s, c⟩
  rcases d with ⟨t, d⟩
  rw [xWord_auxiliary_coeff]
  cases s <;> cases t <;>
    simp [xAuxiliary, scalarMatrix, twistedMatrix, Matrix.mul_apply,
      MonoidAlgebra.coeff_single_mul_apply]

variable {C' D' : Type*} [Fintype C'] [Fintype D']

/-- The selected actual boundary supports are disjoint on every auxiliary qubit.
Only the two raw scalar dual-check equations are assumed. -/
theorem selected_words_auxiliary_disjoint
    (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (gA : Matrix C' A (ZMod 2)) (gB : Matrix D' B (ZMod 2))
    (a : A → G) (b : B → G)
    (hDualA : gA * hA.transpose = 0) (hDualB : gB * hB.transpose = 0)
    (U0 U1 : Matrix C D' (MonoidAlgebra (ZMod 2) G))
    (V0 V1 : Matrix C' D (MonoidAlgebra (ZMod 2) G))
    (c : Bool × C) (d : Bool × D) (g : G) :
    zWord hA hB a b
        (zParameter (U0 * twistedMatrix gB (fun j => (b j)⁻¹)) (U1 * scalarMatrix gB))
        (auxiliaryCoordinate c d g) = 0 ∨
      xWord hA hB a b
        (xParameter ((scalarMatrix gA).transpose * V0)
          ((twistedMatrix gA (fun i => (a i)⁻¹)).transpose * V1))
        (auxiliaryCoordinate c d g) = 0 := by
  rw [zWord_auxiliary_eq, xWord_auxiliary_eq]
  rcases selected_groupAlgebra_auxiliary_disjoint hA hB gA gB a b hDualA hDualB
      U0 U1 V0 V1 c d with hz | hx
  · exact Or.inl (congrArg (fun x : MonoidAlgebra (ZMod 2) G => x.coeff g) hz)
  · exact Or.inr (congrArg (fun x : MonoidAlgebra (ZMod 2) G => x.coeff g) hx)

/-- The canonical full checks commute, by the actual lifted-product chain identity.
There is no spectral, no-conjugacy, or group-commutativity premise. -/
theorem full_checks_orthogonal (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (a : A → G) (b : B → G)
    (U : C2Index B (Bool × C) G → ZMod 2)
    (V : C0Index (Bool × D) A G → ZMod 2) :
    dotProduct (zWord hA hB a b U) (xWord hA hB a b V) = 0 := by
  rw [zWord, xWord, Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
    boundary1Matrix_mul_boundary2Matrix]
  simp

/-- Puncturing retains orthogonality exactly when the deleted supports contribute zero.
This lemma alone is not a claim about arbitrary CSS puncturing; the selected
families must establish its pointwise hypothesis from local dual checks. -/
theorem retained_checks_orthogonal_of_auxiliary_disjoint
    (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2)) (a : A → G) (b : B → G)
    (U : C2Index B (Bool × C) G → ZMod 2)
    (V : C0Index (Bool × D) A G → ZMod 2)
    (hAux : ∀ d c g, zWord hA hB a b U (auxiliaryCoordinate c d g) = 0 ∨
      xWord hA hB a b V (auxiliaryCoordinate c d g) = 0) :
    (∑ j : B, ∑ i : A, ∑ g : G,
      zWord hA hB a b U (retainedCoordinate i j g) *
        xWord hA hB a b V (retainedCoordinate i j g)) = 0 := by
  have h := full_checks_orthogonal hA hB a b U V
  have hDeleted : (∑ d : Bool × D, ∑ c : Bool × C, ∑ g : G,
      zWord hA hB a b U (auxiliaryCoordinate c d g) *
        xWord hA hB a b V (auxiliaryCoordinate c d g)) = 0 := by
    apply Finset.sum_eq_zero
    intro d _
    apply Finset.sum_eq_zero
    intro c _
    apply Finset.sum_eq_zero
    intro g _
    rcases hAux d c g with hz | hx
    · rw [hz, zero_mul]
    · rw [hx, mul_zero]
  simp only [auxiliaryCoordinate, Fintype.sum_prod_type] at hDeleted
  simpa only [dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
    retainedCoordinate, hDeleted, add_zero] using h

/-- Actual selected checks commute after deleting the auxiliary coordinates.
Disjointness is derived from raw dual parity checks, not supplied as a bridge certificate. -/
theorem selected_retained_checks_orthogonal
    (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (gA : Matrix C' A (ZMod 2)) (gB : Matrix D' B (ZMod 2))
    (a : A → G) (b : B → G)
    (hDualA : gA * hA.transpose = 0) (hDualB : gB * hB.transpose = 0)
    (U0 U1 : Matrix C D' (MonoidAlgebra (ZMod 2) G))
    (V0 V1 : Matrix C' D (MonoidAlgebra (ZMod 2) G)) :
    let U := zParameter (U0 * twistedMatrix gB (fun j => (b j)⁻¹)) (U1 * scalarMatrix gB)
    let V := xParameter ((scalarMatrix gA).transpose * V0)
      ((twistedMatrix gA (fun i => (a i)⁻¹)).transpose * V1)
    (∑ j : B, ∑ i : A, ∑ g : G,
      zWord hA hB a b U (retainedCoordinate i j g) *
        xWord hA hB a b V (retainedCoordinate i j g)) = 0 := by
  dsimp only
  apply retained_checks_orthogonal_of_auxiliary_disjoint
  intro d c g
  exact selected_words_auxiliary_disjoint hA hB gA gB a b hDualA hDualB U0 U1 V0 V1 c d g

end

end QEC.Coding.QuantumTanner.LiftedProductActionBridge
