import QEC.Coding.ExpanderCodes.LPSEffectivePrime
import QEC.Coding.ExpanderCodes.TannerLiftedProduct
import Mathlib.Data.List.OfFn

/-!
# Computed sparse CSS boundaries on actual indexed LPS vertices

The row generator uses the computable actual PSL enumeration and operations,
not group-algebra support enumeration. Every emitted coefficient is proved equal
to the semantic Tanner lifted-product boundary after decoding coordinates.
The negative X block is retained over every finite field. Complete all-row
outputs use consecutive numeric physical coordinates; exact emitted sizes are
proved, without claiming a bit/runtime bound or unconditional spectral theorem.

Source motivation: `panteleev-kalachev-2021-good/main.tex:248-273,349-410,589-620`.
As with `TannerLiftedProduct.data`, labels use its right-regular convention; a
source left-lift voltage is supplied inverted. Fixed local matrices and fixed
quaternion directions may be chosen once; the variable PSL carrier is computed.
-/

namespace QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance (q : ℕ) [Fact q.Prime] : DecidableEq PSL(2, ZMod q) := lpsPSLDecidableEq q

/-- Consecutive indices of the actual computed PSL list. -/
abbrev LPSSparseGroupIndex (q : ℕ) [Fact q.Prime] := Fin (lpsPSLList q).length
/-- Face and vertex physical cells with numeric group coordinates. -/
abbrev LPSSparseQubitIndex (q D r r' : ℕ) [Fact q.Prime] :=
  Sum (Fin D × Fin D × LPSSparseGroupIndex q) (Fin (2 * r) × Fin (2 * r') × LPSSparseGroupIndex q)
/-- Degree-zero check coordinates, with the local side/row pair flattened. -/
abbrev LPSSparseXIndex (q D r : ℕ) [Fact q.Prime] := Fin (2 * r) × Fin D × LPSSparseGroupIndex q
/-- Degree-two check coordinates, with the local side/row pair flattened. -/
abbrev LPSSparseZIndex (q D r' : ℕ) [Fact q.Prime] := Fin D × Fin (2 * r') × LPSSparseGroupIndex q

/-- Computed double-cover voltage in actual group indices. -/
def lpsSparseVoltage {q D : ℕ} [Fact q.Prime] (label : Fin D → LPSSparseGroupIndex q)
    (side : Fin 2) (j : Fin D) : LPSSparseGroupIndex q :=
  if side = 0 then lpsPSLIndexOne q else label j

theorem lpsSparseVoltage_decode {q D : ℕ} [Fact q.Prime]
    (label : Fin D → LPSSparseGroupIndex q) (side : Fin 2) (j : Fin D) :
    (lpsPSLEnumerationEquiv q) (lpsSparseVoltage label side j) =
      doubleCoverVoltage (fun j => (lpsPSLEnumerationEquiv q) (label j)) side j := by
  by_cases h : side = 0 <;> simp [lpsSparseVoltage, doubleCoverVoltage, h, lpsPSLIndexOne]

/-- Sparse first-boundary row: right-regular A followed by negative left-regular B. -/
def lpsSparseXRow {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) (row : LPSSparseXIndex q D r) :
    List (LPSSparseQubitIndex q D r r' × F) :=
  let ar := finProdFinEquiv.symm row.1
  (List.ofFn fun ac : Fin D =>
    (Sum.inl (ac, row.2.1, lpsPSLIndexMul q row.2.2
      (lpsPSLIndexInv q (lpsSparseVoltage label ar.1 ac))), h ar.2 ac)) ++
  (List.ofFn fun bc : Fin (2 * r') =>
    let bcPair := finProdFinEquiv.symm bc
    (Sum.inr (row.1, bc, lpsPSLIndexMul q
      (lpsSparseVoltage label bcPair.1 row.2.1) row.2.2), -h' bcPair.2 row.2.1))

/-- Sparse transposed second-boundary row: left-regular B followed by right-regular A. -/
def lpsSparseZRow {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) (row : LPSSparseZIndex q D r') :
    List (LPSSparseQubitIndex q D r r' × F) :=
  let bc := finProdFinEquiv.symm row.2.1
  (List.ofFn fun br : Fin D =>
    (Sum.inl (row.1, br, lpsPSLIndexMul q
      (lpsPSLIndexInv q (lpsSparseVoltage label bc.1 br)) row.2.2), h' bc.2 br)) ++
  (List.ofFn fun ar : Fin (2 * r) =>
    let arPair := finProdFinEquiv.symm ar
    (Sum.inr (ar, row.2.1, lpsPSLIndexMul q row.2.2
      (lpsSparseVoltage label arPair.1 row.1)), h arPair.2 row.1))

theorem lpsSparseXRow_length {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) (row : LPSSparseXIndex q D r) :
    (lpsSparseXRow label h h' row).length = D + 2 * r' := by simp [lpsSparseXRow]

theorem lpsSparseZRow_length {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) (row : LPSSparseZIndex q D r') :
    (lpsSparseZRow label h h' row).length = D + 2 * r := by simp [lpsSparseZRow]

/-- Sum of coefficients emitted at a selected physical coordinate. -/
def lpsSparseRowValue {Q F : Type} [DecidableEq Q] [AddCommMonoid F]
    (row : List (Q × F)) (q : Q) : F :=
  (row.map fun entry => if entry.1 = q then entry.2 else 0).sum

def lpsSparseQubitDecode {q D r r' : ℕ} [Fact q.Prime] :
    LPSSparseQubitIndex q D r r' →
      LiftedProduct.QubitIndex (Fin 2 × Fin r) (Fin D) (Fin D)
        (Fin 2 × Fin r') PSL(2, ZMod q)
  | Sum.inl (ac, br, g) => Sum.inl (ac, br, (lpsPSLEnumerationEquiv q) g)
  | Sum.inr (ar, bc, g) => Sum.inr (finProdFinEquiv.symm ar,
      finProdFinEquiv.symm bc, (lpsPSLEnumerationEquiv q) g)

def lpsSparseXDecode {q D r : ℕ} [Fact q.Prime] (row : LPSSparseXIndex q D r) :
    LiftedProduct.C0Index (Fin 2 × Fin r) (Fin D) PSL(2, ZMod q) :=
  (finProdFinEquiv.symm row.1, row.2.1, (lpsPSLEnumerationEquiv q) row.2.2)

def lpsSparseZDecode {q D r' : ℕ} [Fact q.Prime] (row : LPSSparseZIndex q D r') :
    LiftedProduct.C2Index (Fin D) (Fin 2 × Fin r') PSL(2, ZMod q) :=
  (row.1, finProdFinEquiv.symm row.2.1, (lpsPSLEnumerationEquiv q) row.2.2)

theorem lpsSparseXRow_value_inl {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) (row : LPSSparseXIndex q D r)
    (ac br : Fin D) (gi : LPSSparseGroupIndex q) :
    lpsSparseRowValue (lpsSparseXRow label h h' row) (Sum.inl (ac, br, gi)) =
      if row.2.1 = br ∧ lpsPSLIndexMul q row.2.2
          (lpsPSLIndexInv q (lpsSparseVoltage label (finProdFinEquiv.symm row.1).1 ac)) = gi
      then h (finProdFinEquiv.symm row.1).2 ac else 0 := by
  simp [lpsSparseRowValue, lpsSparseXRow, List.map_ofFn, List.sum_ofFn,
    Prod.mk.injEq, ite_and]

theorem lpsSparseXRow_value_inr {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) (row : LPSSparseXIndex q D r)
    (ar : Fin (2 * r)) (bc : Fin (2 * r')) (gi : LPSSparseGroupIndex q) :
    lpsSparseRowValue (lpsSparseXRow label h h' row) (Sum.inr (ar, bc, gi)) =
      if row.1 = ar ∧ lpsPSLIndexMul q
          (lpsSparseVoltage label (finProdFinEquiv.symm bc).1 row.2.1) row.2.2 = gi
      then -h' (finProdFinEquiv.symm bc).2 row.2.1 else 0 := by
  simp [lpsSparseRowValue, lpsSparseXRow, List.map_ofFn, List.sum_ofFn,
    Prod.mk.injEq, ite_and, eq_comm]

theorem lpsSparseZRow_value_inl {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) (row : LPSSparseZIndex q D r')
    (ac br : Fin D) (go : LPSSparseGroupIndex q) :
    lpsSparseRowValue (lpsSparseZRow label h h' row) (Sum.inl (ac, br, go)) =
      if row.1 = ac ∧ lpsPSLIndexMul q
          (lpsPSLIndexInv q (lpsSparseVoltage label (finProdFinEquiv.symm row.2.1).1 br))
          row.2.2 = go
      then h' (finProdFinEquiv.symm row.2.1).2 br else 0 := by
  simp [lpsSparseRowValue, lpsSparseZRow, List.map_ofFn, List.sum_ofFn,
    Prod.mk.injEq, ite_and, eq_comm]

theorem lpsSparseZRow_value_inr {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) (row : LPSSparseZIndex q D r')
    (ar : Fin (2 * r)) (bc : Fin (2 * r')) (go : LPSSparseGroupIndex q) :
    lpsSparseRowValue (lpsSparseZRow label h h' row) (Sum.inr (ar, bc, go)) =
      if row.2.1 = bc ∧ lpsPSLIndexMul q row.2.2
          (lpsSparseVoltage label (finProdFinEquiv.symm ar).1 row.1) = go
      then h (finProdFinEquiv.symm ar).2 row.1 else 0 := by
  simp [lpsSparseRowValue, lpsSparseZRow, List.map_ofFn, List.sum_ofFn,
    Prod.mk.injEq, ite_and]

private theorem index_mul_inv_eq_iff {q : ℕ} [Fact q.Prime] (a b c : LPSSparseGroupIndex q) :
    lpsPSLIndexMul q a (lpsPSLIndexInv q b) = c ↔
      ((lpsPSLEnumerationEquiv q) c)⁻¹ * (lpsPSLEnumerationEquiv q) a =
        (lpsPSLEnumerationEquiv q) b := by
  rw [← (lpsPSLEnumerationEquiv q).injective.eq_iff,
    lpsPSLIndexMul_decode, lpsPSLIndexInv_decode]
  constructor
  · intro h
    rw [← h]
    simp
  · intro h
    calc
      _ = (lpsPSLEnumerationEquiv q) c *
          ((lpsPSLEnumerationEquiv q) c)⁻¹ *
          (lpsPSLEnumerationEquiv q) a * ((lpsPSLEnumerationEquiv q) b)⁻¹ := by simp
      _ = (lpsPSLEnumerationEquiv q) c := by rw [mul_assoc _ _ ((lpsPSLEnumerationEquiv q) a), h]; simp

private theorem index_mul_eq_iff {q : ℕ} [Fact q.Prime] (a b c : LPSSparseGroupIndex q) :
    lpsPSLIndexMul q a b = c ↔
      (lpsPSLEnumerationEquiv q) b * ((lpsPSLEnumerationEquiv q) c)⁻¹ =
        ((lpsPSLEnumerationEquiv q) a)⁻¹ := by
  rw [← (lpsPSLEnumerationEquiv q).injective.eq_iff, lpsPSLIndexMul_decode]
  constructor
  · intro h
    rw [← h]
    simp
  · intro h
    have h' := congrArg (fun x => (lpsPSLEnumerationEquiv q) a * x *
        (lpsPSLEnumerationEquiv q) c) h
    simpa [mul_assoc] using h'

private theorem index_inv_mul_eq_iff {q : ℕ} [Fact q.Prime]
    (a b c : LPSSparseGroupIndex q) :
    lpsPSLIndexMul q (lpsPSLIndexInv q a) b = c ↔
      ((lpsPSLEnumerationEquiv q) c * ((lpsPSLEnumerationEquiv q) b)⁻¹)⁻¹ =
        (lpsPSLEnumerationEquiv q) a := by
  rw [← (lpsPSLEnumerationEquiv q).injective.eq_iff,
    lpsPSLIndexMul_decode, lpsPSLIndexInv_decode]
  constructor
  · intro h
    rw [← h]
    simp
  · intro h
    have h' := congrArg (fun x => x⁻¹ * (lpsPSLEnumerationEquiv q) b) h
    simpa [mul_assoc] using h'.symm

private theorem index_mul_eq_iff_inv_mul {q : ℕ} [Fact q.Prime]
    (a b c : LPSSparseGroupIndex q) :
    lpsPSLIndexMul q a b = c ↔
      ((lpsPSLEnumerationEquiv q) a)⁻¹ * (lpsPSLEnumerationEquiv q) c =
        (lpsPSLEnumerationEquiv q) b := by
  rw [← (lpsPSLEnumerationEquiv q).injective.eq_iff, lpsPSLIndexMul_decode,
    inv_mul_eq_iff_eq_mul, eq_comm]

/-- Every computed X coefficient equals the actual first-boundary coefficient. -/
theorem lpsSparseXRow_value_eq {q D r r' : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) (row : LPSSparseXIndex q D r)
    (qubit : LPSSparseQubitIndex q D r r') :
    lpsSparseRowValue (lpsSparseXRow label h h' row) qubit =
      LiftedProduct.boundary1Matrix
        (data (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h')
        (lpsSparseXDecode row) (lpsSparseQubitDecode qubit) := by
  classical
  rcases qubit with ⟨ac, br, gi⟩ | ⟨ar, bc, gi⟩
  · rw [lpsSparseXRow_value_inl]
    simp only [index_mul_inv_eq_iff, lpsSparseVoltage_decode,
      LiftedProduct.boundary1Matrix, data, doubleCoverTannerMatrix,
      LiftedProduct.rightRegularMatrix, lpsSparseXDecode, lpsSparseQubitDecode,
      MonoidAlgebra.coeff_single, Finsupp.single_apply]
    simp only [ite_and, eq_comm]
  · rw [lpsSparseXRow_value_inr]
    simp only [index_mul_eq_iff, lpsSparseVoltage_decode,
      LiftedProduct.boundary1Matrix, data, doubleCoverTannerMatrix,
      LiftedProduct.leftRegularMatrix, lpsSparseXDecode, lpsSparseQubitDecode,
      LiftedProduct.starTranspose_apply, LiftedProduct.groupConj_apply,
      MonoidAlgebra.coeff_single, Finsupp.single_apply,
      finProdFinEquiv.symm.injective.eq_iff]
    have hInv (a b : PSL(2, ZMod q)) : a = b⁻¹ ↔ b = a⁻¹ := by
      constructor <;> intro hh
      · have hh' := congrArg (fun x => x⁻¹) hh
        simpa using hh'.symm
      · have hh' := congrArg (fun x => x⁻¹) hh
        simpa using hh'.symm
    simp only [hInv (doubleCoverVoltage (fun j => (lpsPSLEnumerationEquiv q) (label j))
      (finProdFinEquiv.symm bc).1 row.2.1)
      ((lpsPSLEnumerationEquiv q) row.2.2 * ((lpsPSLEnumerationEquiv q) gi)⁻¹),
      ite_and, neg_ite, neg_zero]

/-- Every computed Z coefficient equals the actual second-boundary transpose coefficient. -/
theorem lpsSparseZRow_value_eq {q D r r' : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) (row : LPSSparseZIndex q D r')
    (qubit : LPSSparseQubitIndex q D r r') :
    lpsSparseRowValue (lpsSparseZRow label h h' row) qubit =
      LiftedProduct.boundary2Matrix
        (data (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h')
        (lpsSparseQubitDecode qubit) (lpsSparseZDecode row) := by
  classical
  rcases qubit with ⟨ac, br, go⟩ | ⟨ar, bc, go⟩
  · rw [lpsSparseZRow_value_inl]
    simp only [index_inv_mul_eq_iff, lpsSparseVoltage_decode,
      LiftedProduct.boundary2Matrix, data, doubleCoverTannerMatrix,
      LiftedProduct.leftRegularMatrix, lpsSparseZDecode, lpsSparseQubitDecode,
      LiftedProduct.starTranspose_apply, LiftedProduct.groupConj_apply,
      MonoidAlgebra.coeff_single, Finsupp.single_apply]
    simp only [ite_and, eq_comm]
  · rw [lpsSparseZRow_value_inr]
    simp only [index_mul_eq_iff_inv_mul, lpsSparseVoltage_decode,
      LiftedProduct.boundary2Matrix, data, doubleCoverTannerMatrix,
      LiftedProduct.rightRegularMatrix, lpsSparseZDecode, lpsSparseQubitDecode,
      MonoidAlgebra.coeff_single, Finsupp.single_apply,
      finProdFinEquiv.symm.injective.eq_iff]
    simp only [ite_and, eq_comm]

/-- Actual physical coordinate equivalence, including both lifted-product blocks. -/
def lpsSparseQubitEquiv {q D r r' : ℕ} [Fact q.Prime] :
    LPSSparseQubitIndex q D r r' ≃
      LiftedProduct.QubitIndex (Fin 2 × Fin r) (Fin D) (Fin D)
        (Fin 2 × Fin r') PSL(2, ZMod q) :=
  Equiv.sumCongr
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
      (lpsPSLEnumerationEquiv q)))
    (Equiv.prodCongr finProdFinEquiv.symm
      (Equiv.prodCongr finProdFinEquiv.symm (lpsPSLEnumerationEquiv q)))

theorem lpsSparseQubitEquiv_apply {q D r r' : ℕ} [Fact q.Prime]
    (qubit : LPSSparseQubitIndex q D r r') :
    lpsSparseQubitEquiv qubit = lpsSparseQubitDecode qubit := by cases qubit <;> rfl

/-- The computed sparse rows satisfy CSS commutation over every finite field. -/
theorem lpsSparseRows_commute {q D r r' : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F)
    (x : LPSSparseXIndex q D r) (z : LPSSparseZIndex q D r') :
    ∑ qubit : LPSSparseQubitIndex q D r r',
      lpsSparseRowValue (lpsSparseXRow label h h' x) qubit *
        lpsSparseRowValue (lpsSparseZRow label h h' z) qubit = 0 := by
  classical
  simp_rw [lpsSparseXRow_value_eq, lpsSparseZRow_value_eq, ← lpsSparseQubitEquiv_apply]
  calc
    _ = ∑ y, LiftedProduct.boundary1Matrix
        (data (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h')
        (lpsSparseXDecode x) y * LiftedProduct.boundary2Matrix
        (data (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h')
        y (lpsSparseZDecode z) := lpsSparseQubitEquiv.sum_comp _
    _ = 0 := congrFun (congrFun
    (LiftedProduct.boundary1Matrix_mul_boundary2Matrix
      (data (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h'))
    (lpsSparseXDecode x)) (lpsSparseZDecode z)

/-- Computed flattening of three consecutive finite coordinates. -/
def lpsSparseTripleEquiv (a b c : ℕ) :
    (Fin a × Fin b × Fin c) ≃ Fin (a * (b * c)) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv

/-- Consecutive numeric physical numbering for both actual cell blocks. -/
def lpsSparseQubitNumbering {q D r r' : ℕ} [Fact q.Prime] :
    LPSSparseQubitIndex q D r r' ≃
      Fin (D * (D * (lpsPSLList q).length) + (2 * r) * ((2 * r') * (lpsPSLList q).length)) :=
  (Equiv.sumCongr (lpsSparseTripleEquiv _ _ _) (lpsSparseTripleEquiv _ _ _)).trans
    finSumFinEquiv

/-- Complete sparse X output, generated in consecutive check order. -/
def lpsSparseXOutput {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) :=
  List.ofFn fun i : Fin ((2 * r) * (D * (lpsPSLList q).length)) =>
    (lpsSparseXRow label h h' ((lpsSparseTripleEquiv _ _ _).symm i)).map
      (fun e => (lpsSparseQubitNumbering e.1, e.2))

/-- Complete sparse Z output, generated in consecutive check order. -/
def lpsSparseZOutput {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) :=
  List.ofFn fun i : Fin (D * ((2 * r') * (lpsPSLList q).length)) =>
    (lpsSparseZRow label h h' ((lpsSparseTripleEquiv _ _ _).symm i)).map
      (fun e => (lpsSparseQubitNumbering e.1, e.2))

theorem lpsSparseXOutput_length {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) :
    (lpsSparseXOutput label h h').length = (2 * r) * (D * (lpsPSLList q).length) := by
  simp [lpsSparseXOutput]

theorem lpsSparseZOutput_length {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) :
    (lpsSparseZOutput label h h').length = D * ((2 * r') * (lpsPSLList q).length) := by
  simp [lpsSparseZOutput]

theorem lpsSparseRowValue_map_equiv {Q Q' F : Type} [DecidableEq Q] [DecidableEq Q']
    [AddCommMonoid F] (e : Q ≃ Q') (row : List (Q × F)) (x : Q) :
    lpsSparseRowValue (row.map fun entry => (e entry.1, entry.2)) (e x) =
      lpsSparseRowValue row x := by
  simp [lpsSparseRowValue, List.map_map, Function.comp_def, e.injective.eq_iff]

theorem lpsSparseXOutput_getElem {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F)
    (i : Fin ((2 * r) * (D * (lpsPSLList q).length))) :
    (lpsSparseXOutput label h h')[i.val]'(by simp [lpsSparseXOutput]) =
      (lpsSparseXRow label h h' ((lpsSparseTripleEquiv _ _ _).symm i)).map
        (fun e => (lpsSparseQubitNumbering e.1, e.2)) := by
  simp [lpsSparseXOutput]

theorem lpsSparseZOutput_getElem {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F)
    (i : Fin (D * ((2 * r') * (lpsPSLList q).length))) :
    (lpsSparseZOutput label h h')[i.val]'(by simp [lpsSparseZOutput]) =
      (lpsSparseZRow label h h' ((lpsSparseTripleEquiv _ _ _).symm i)).map
        (fun e => (lpsSparseQubitNumbering e.1, e.2)) := by
  simp [lpsSparseZOutput]

/-- Every coefficient in the complete numeric X output has the semantic value. -/
theorem lpsSparseXOutput_value_eq {q D r r' : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F)
    (i : Fin ((2 * r) * (D * (lpsPSLList q).length)))
    (qubit : LPSSparseQubitIndex q D r r') :
    lpsSparseRowValue ((lpsSparseXOutput label h h')[i.val]'(by simp [lpsSparseXOutput]))
      (lpsSparseQubitNumbering qubit) =
      LiftedProduct.boundary1Matrix
        (data (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h')
        (lpsSparseXDecode ((lpsSparseTripleEquiv _ _ _).symm i)) (lpsSparseQubitDecode qubit) := by
  rw [lpsSparseXOutput_getElem, lpsSparseRowValue_map_equiv, lpsSparseXRow_value_eq]

/-- Every coefficient in the complete numeric Z output has the semantic value. -/
theorem lpsSparseZOutput_value_eq {q D r r' : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F)
    (i : Fin (D * ((2 * r') * (lpsPSLList q).length)))
    (qubit : LPSSparseQubitIndex q D r r') :
    lpsSparseRowValue ((lpsSparseZOutput label h h')[i.val]'(by simp [lpsSparseZOutput]))
      (lpsSparseQubitNumbering qubit) =
      LiftedProduct.boundary2Matrix
        (data (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h')
        (lpsSparseQubitDecode qubit) (lpsSparseZDecode ((lpsSparseTripleEquiv _ _ _).symm i)) := by
  rw [lpsSparseZOutput_getElem, lpsSparseRowValue_map_equiv, lpsSparseZRow_value_eq]

/-- Exact emitted X pair count; this is output size, not running time. -/
theorem lpsSparseXOutput_pairs {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) :
    ((lpsSparseXOutput label h h').map List.length).sum =
      ((2 * r) * (D * (lpsPSLList q).length)) * (D + 2 * r') := by
  simp [lpsSparseXOutput, List.map_ofFn, List.sum_ofFn, lpsSparseXRow_length]

/-- Exact emitted Z pair count; this is output size, not running time. -/
theorem lpsSparseZOutput_pairs {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) :
    ((lpsSparseZOutput label h h').map List.length).sum =
      (D * ((2 * r') * (lpsPSLList q).length)) * (D + 2 * r) := by
  simp [lpsSparseZOutput, List.map_ofFn, List.sum_ofFn, lpsSparseZRow_length]

/-- The numeric physical extent is the source face-plus-vertex count. -/
theorem lpsSparseQubitCount_eq {q D r r' : ℕ} [Fact q.Prime] :
    D * (D * (lpsPSLList q).length) + (2 * r) * ((2 * r') * (lpsPSLList q).length) =
      (lpsPSLList q).length * (D ^ 2 + 4 * r * r') := by ring

/-- Complete numeric output rows satisfy CSS commutation, including the field sign. -/
theorem lpsSparseOutputRows_commute {q D r r' : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F)
    (i : Fin ((2 * r) * (D * (lpsPSLList q).length)))
    (j : Fin (D * ((2 * r') * (lpsPSLList q).length))) :
    ∑ coordinate : Fin (D * (D * (lpsPSLList q).length)+
        (2 * r) * ((2 * r') * (lpsPSLList q).length)),
      lpsSparseRowValue ((lpsSparseXOutput label h h')[i.val]'(by simp [lpsSparseXOutput]))
        coordinate *
      lpsSparseRowValue ((lpsSparseZOutput label h h')[j.val]'(by simp [lpsSparseZOutput]))
        coordinate = 0 := by
  classical
  let xr := (lpsSparseXOutput label h h')[i.val]'(by simp [lpsSparseXOutput])
  let zr := (lpsSparseZOutput label h h')[j.val]'(by simp [lpsSparseZOutput])
  change ∑ coordinate, lpsSparseRowValue xr coordinate * lpsSparseRowValue zr coordinate = 0
  calc
    _ = ∑ qubit : LPSSparseQubitIndex q D r r',
        lpsSparseRowValue xr (lpsSparseQubitNumbering qubit) *
          lpsSparseRowValue zr (lpsSparseQubitNumbering qubit) :=
      (lpsSparseQubitNumbering.sum_comp
        (fun coordinate => lpsSparseRowValue xr coordinate *
          lpsSparseRowValue zr coordinate)).symm
    _ = ∑ qubit : LPSSparseQubitIndex q D r r',
        lpsSparseRowValue
          (lpsSparseXRow label h h' ((lpsSparseTripleEquiv _ _ _).symm i)) qubit *
        lpsSparseRowValue
          (lpsSparseZRow label h h' ((lpsSparseTripleEquiv _ _ _).symm j)) qubit := by
      simp only [xr, zr, lpsSparseXOutput_getElem, lpsSparseZOutput_getElem,
        lpsSparseRowValue_map_equiv]
    _ = 0 := lpsSparseRows_commute label h h' _ _

/-- Actual effective-prime quaternion labels consumed by the sparse X generator. -/
def lpsEffectiveSparseXRow {p D r r' : ℕ} {F : Type} [Field F]
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
    (generators : Fin D → LPSGeneratorIndex p)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (x : LPSSparseXIndex (lpsEffectiveResiduePrimeAt hp hp4 n).q D r) :=
  lpsSparseXRow (fun j => lpsEffectiveQuaternionFamilyIndex hp hp4 n (generators j)) h h' x

/-- Actual effective-prime quaternion labels consumed by the sparse Z generator. -/
def lpsEffectiveSparseZRow {p D r r' : ℕ} {F : Type} [Field F]
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
    (generators : Fin D → LPSGeneratorIndex p)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (z : LPSSparseZIndex (lpsEffectiveResiduePrimeAt hp hp4 n).q D r') :=
  lpsSparseZRow (fun j => lpsEffectiveQuaternionFamilyIndex hp hp4 n (generators j)) h h' z

theorem lpsEffectiveSparseXRow_value_eq {p D r r' : ℕ} {F : Type} [Field F] [Fintype F]
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
    (generators : Fin D → LPSGeneratorIndex p)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (x : LPSSparseXIndex (lpsEffectiveResiduePrimeAt hp hp4 n).q D r)
    (qubit : LPSSparseQubitIndex (lpsEffectiveResiduePrimeAt hp hp4 n).q D r r') :
    lpsSparseRowValue (lpsEffectiveSparseXRow hp hp4 n generators h h' x) qubit =
      LiftedProduct.boundary1Matrix
        (data (fun j => lpsEffectiveQuaternionFamilyLabel hp hp4 n (generators j)) h h')
        (lpsSparseXDecode x) (lpsSparseQubitDecode qubit) := by
  simpa only [lpsEffectiveSparseXRow, lpsEffectiveQuaternionFamilyIndex_decode] using
    lpsSparseXRow_value_eq
      (fun j => lpsEffectiveQuaternionFamilyIndex hp hp4 n (generators j)) h h' x qubit

theorem lpsEffectiveSparseZRow_value_eq {p D r r' : ℕ} {F : Type} [Field F] [Fintype F]
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
    (generators : Fin D → LPSGeneratorIndex p)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (z : LPSSparseZIndex (lpsEffectiveResiduePrimeAt hp hp4 n).q D r')
    (qubit : LPSSparseQubitIndex (lpsEffectiveResiduePrimeAt hp hp4 n).q D r r') :
    lpsSparseRowValue (lpsEffectiveSparseZRow hp hp4 n generators h h' z) qubit =
      LiftedProduct.boundary2Matrix
        (data (fun j => lpsEffectiveQuaternionFamilyLabel hp hp4 n (generators j)) h h')
        (lpsSparseQubitDecode qubit) (lpsSparseZDecode z) := by
  simpa only [lpsEffectiveSparseZRow, lpsEffectiveQuaternionFamilyIndex_decode] using
    lpsSparseZRow_value_eq
      (fun j => lpsEffectiveQuaternionFamilyIndex hp hp4 n (generators j)) h h' z qubit

/-- Actual computed X rows represent the original PK22 family boundary. -/
theorem lpsEffectiveSparseXRow_value_eq_original {p D r r' : ℕ}
    {F : Type} [Field F] [Fintype F]
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
    (generators : Fin D → LPSGeneratorIndex p)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (x : LPSSparseXIndex (lpsResiduePrimeSequence hp hp4 n).q D r)
    (qubit : LPSSparseQubitIndex (lpsResiduePrimeSequence hp hp4 n).q D r r') :
    lpsSparseRowValue (lpsEffectiveSparseXRow hp hp4 n generators h h' x) qubit =
      LiftedProduct.boundary1Matrix
        (data (fun j => lpsQuaternionFamilyLabel hp hp4 n (generators j)) h h')
        (lpsSparseXDecode x) (lpsSparseQubitDecode qubit) := by
  have hLabel : (fun j => lpsEffectiveQuaternionFamilyLabel hp hp4 n (generators j)) =
      (fun j => lpsQuaternionFamilyLabel hp hp4 n (generators j)) :=
    funext (fun j => congrFun (lpsEffectiveQuaternionFamilyLabel_eq_original hp hp4 n)
      (generators j))
  exact (lpsEffectiveSparseXRow_value_eq hp hp4 n generators h h' x qubit).trans
    (congrArg (fun label => LiftedProduct.boundary1Matrix (data label h h')
      (lpsSparseXDecode x) (lpsSparseQubitDecode qubit)) hLabel)

/-- Actual computed Z rows represent the original PK22 family boundary transpose. -/
theorem lpsEffectiveSparseZRow_value_eq_original {p D r r' : ℕ}
    {F : Type} [Field F] [Fintype F]
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
    (generators : Fin D → LPSGeneratorIndex p)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (z : LPSSparseZIndex (lpsResiduePrimeSequence hp hp4 n).q D r')
    (qubit : LPSSparseQubitIndex (lpsResiduePrimeSequence hp hp4 n).q D r r') :
    lpsSparseRowValue (lpsEffectiveSparseZRow hp hp4 n generators h h' z) qubit =
      LiftedProduct.boundary2Matrix
        (data (fun j => lpsQuaternionFamilyLabel hp hp4 n (generators j)) h h')
        (lpsSparseQubitDecode qubit) (lpsSparseZDecode z) := by
  have hLabel : (fun j => lpsEffectiveQuaternionFamilyLabel hp hp4 n (generators j)) =
      (fun j => lpsQuaternionFamilyLabel hp hp4 n (generators j)) :=
    funext (fun j => congrFun (lpsEffectiveQuaternionFamilyLabel_eq_original hp hp4 n)
      (generators j))
  exact (lpsEffectiveSparseZRow_value_eq hp hp4 n generators h h' z qubit).trans
    (congrArg (fun label => LiftedProduct.boundary2Matrix (data label h h')
      (lpsSparseQubitDecode qubit) (lpsSparseZDecode z)) hLabel)

end QEC.Coding.TannerLiftedProduct
