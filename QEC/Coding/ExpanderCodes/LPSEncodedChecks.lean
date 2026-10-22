import QEC.Coding.ExpanderCodes.LPSSparseCSS

/-!
# Numeric all-scalar checks for the actual PK22 family

Finite zero/add/mul/negation tables and local matrix entries are fixed once for
an arbitrary finite field. All variable output uses numeric coefficients and
actual indexed PSL operations. Every scalar-decorated sparse check is enumerated;
a numeric scan of aggregated coefficients computes its exact nonzero region.
Decoded words and Pauli operators are proved equal to the semantic checks, whose
common fixed space is the original family code. Encoded zero need not be index zero.

Source motivation: `panteleev-kalachev-2021-good/main.tex:231-238,248-273,1744`.
This supplies output semantics, not a bit/runtime or unconditional spectral bound.
The once-fixed field numbering is a proof interpretation; dynamic row generation,
scaling, coefficient lookup and support scanning take only numeric tables/data.
-/

namespace QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups

/-- A once-fixed finite alphabet's concrete numeric operation tables. -/
structure EncodedFieldTables (s : ℕ) where
  zero : Fin s
  add : List (List (Fin s))
  mul : List (List (Fin s))
  neg : List (Fin s)

def encodedFieldTables {F : Type} [Field F] {s : ℕ} (e : Fin s ≃ F) :
    EncodedFieldTables s where
  zero := e.symm 0
  add := List.ofFn fun a => List.ofFn fun b => e.symm (e a + e b)
  mul := List.ofFn fun a => List.ofFn fun b => e.symm (e a * e b)
  neg := List.ofFn fun a => e.symm (-e a)

-- Total list lookup is intentional; correctly derived tables have full extent.
def encodedFieldAdd {s : ℕ} (t : EncodedFieldTables s) (a b : Fin s) : Fin s :=
  ((t.add[a.val]?).getD []).getD b.val t.zero

def encodedFieldMul {s : ℕ} (t : EncodedFieldTables s) (a b : Fin s) : Fin s :=
  ((t.mul[a.val]?).getD []).getD b.val t.zero

theorem encodedFieldAdd_decode {F : Type} [Field F] {s : ℕ} (e : Fin s ≃ F)
    (a b : Fin s) : e (encodedFieldAdd (encodedFieldTables e) a b) = e a + e b := by
  simp [encodedFieldAdd, encodedFieldTables, List.getD]

theorem encodedFieldMul_decode {F : Type} [Field F] {s : ℕ} (e : Fin s ≃ F)
    (a b : Fin s) : e (encodedFieldMul (encodedFieldTables e) a b) = e a * e b := by
  simp [encodedFieldMul, encodedFieldTables, List.getD]

def encodedSparseRowValue {Q : Type} [DecidableEq Q] {s : ℕ}
    (t : EncodedFieldTables s) (row : List (Q × Fin s)) (x : Q) : Fin s :=
  row.foldr (fun entry acc => if entry.1 = x then encodedFieldAdd t entry.2 acc else acc) t.zero

theorem encodedSparseRowValue_decode {Q F : Type} [DecidableEq Q] [Field F]
    {s : ℕ} (e : Fin s ≃ F) (row : List (Q × Fin s)) (x : Q) :
    e (encodedSparseRowValue (encodedFieldTables e) row x) =
      lpsSparseRowValue (row.map fun entry => (entry.1, e entry.2)) x := by
  induction row with
  | nil => simp [encodedSparseRowValue, encodedFieldTables, lpsSparseRowValue]
  | cons a row ih =>
      simp only [encodedSparseRowValue, lpsSparseRowValue, List.map_map] at ih
      by_cases h : a.1 = x
      · simp [encodedSparseRowValue, lpsSparseRowValue, h, encodedFieldAdd_decode, ih]
      · simp [encodedSparseRowValue, lpsSparseRowValue, h, ih]

def encodedSparseScalarRow {Q : Type} {s : ℕ} (t : EncodedFieldTables s)
    (scalar : Fin s) (row : List (Q × Fin s)) : List (Q × Fin s) :=
  row.map fun entry => (entry.1, encodedFieldMul t scalar entry.2)

theorem encodedSparseScalarRow_value {Q F : Type} [DecidableEq Q] [Field F]
    {s : ℕ} (e : Fin s ≃ F) (scalar : Fin s) (row : List (Q × F)) (x : Q) :
    e (encodedSparseRowValue (encodedFieldTables e)
      (encodedSparseScalarRow (encodedFieldTables e) scalar
        (row.map fun entry => (entry.1, e.symm entry.2))) x) =
        e scalar * lpsSparseRowValue row x := by
  rw [encodedSparseRowValue_decode]
  simp only [encodedSparseScalarRow, List.map_map, Function.comp_def,
    encodedFieldMul_decode, Equiv.apply_symm_apply]
  induction row with
  | nil => simp [lpsSparseRowValue]
  | cons a row ih =>
      simp only [lpsSparseRowValue, List.map_map] at ih
      by_cases ha : a.1 = x <;>
        simp [lpsSparseRowValue, ha, mul_add, ih]

def encodedSparseRegion {n s : ℕ} (t : EncodedFieldTables s)
    (row : List (Fin n × Fin s)) : List (Fin n) :=
  (List.finRange n).filter fun x => encodedSparseRowValue t row x != t.zero

theorem mem_encodedSparseRegion {F : Type} [Field F] {n s : ℕ}
    (e : Fin s ≃ F) (row : List (Fin n × Fin s)) (x : Fin n) :
    x ∈ encodedSparseRegion (encodedFieldTables e) row ↔
      lpsSparseRowValue (row.map fun entry => (entry.1, e entry.2)) x ≠ 0 := by
  simp only [encodedSparseRegion, List.mem_filter, List.mem_finRange, true_and,
    bne_iff_ne]
  rw [← e.injective.ne_iff]
  rw [encodedSparseRowValue_decode]
  simp only [encodedFieldTables, Equiv.apply_symm_apply]

theorem encodedSparseRegion_nodup {n s : ℕ} (t : EncodedFieldTables s)
    (row : List (Fin n × Fin s)) : (encodedSparseRegion t row).Nodup :=
  (List.nodup_finRange n).filter _


def encodedFieldNeg {s : ℕ} (t : EncodedFieldTables s) (a : Fin s) : Fin s :=
  t.neg.getD a.val t.zero

theorem encodedFieldNeg_decode {F : Type} [Field F] {s : ℕ} (e : Fin s ≃ F)
    (a : Fin s) : e (encodedFieldNeg (encodedFieldTables e) a) = -e a := by
  simp [encodedFieldNeg, encodedFieldTables, List.getD]

local instance (q : ℕ) [Fact q.Prime] : DecidableEq PSL(2, ZMod q) := lpsPSLDecidableEq q

def lpsEncodedXRow {q D r r' s : ℕ} [Fact q.Prime]
    (t : EncodedFieldTables s) (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) (Fin s)) (h' : Matrix (Fin r') (Fin D) (Fin s))
    (row : LPSSparseXIndex q D r) : List (LPSSparseQubitIndex q D r r' × Fin s) :=
  let ar := finProdFinEquiv.symm row.1
  (List.ofFn fun ac : Fin D =>
    (Sum.inl (ac, row.2.1, lpsPSLIndexMul q row.2.2
      (lpsPSLIndexInv q (lpsSparseVoltage label ar.1 ac))), h ar.2 ac)) ++
  (List.ofFn fun bc : Fin (2 * r') =>
    let bcPair := finProdFinEquiv.symm bc
    (Sum.inr (row.1, bc, lpsPSLIndexMul q
      (lpsSparseVoltage label bcPair.1 row.2.1) row.2.2),
      encodedFieldNeg t (h' bcPair.2 row.2.1)))

def lpsEncodedZRow {q D r r' s : ℕ} [Fact q.Prime]
    (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) (Fin s)) (h' : Matrix (Fin r') (Fin D) (Fin s))
    (row : LPSSparseZIndex q D r') : List (LPSSparseQubitIndex q D r r' × Fin s) :=
  let bc := finProdFinEquiv.symm row.2.1
  (List.ofFn fun br : Fin D =>
    (Sum.inl (row.1, br, lpsPSLIndexMul q
      (lpsPSLIndexInv q (lpsSparseVoltage label bc.1 br)) row.2.2), h' bc.2 br)) ++
  (List.ofFn fun ar : Fin (2 * r) =>
    let arPair := finProdFinEquiv.symm ar
    (Sum.inr (ar, row.2.1, lpsPSLIndexMul q row.2.2
      (lpsSparseVoltage label arPair.1 row.1)), h arPair.2 row.1))

theorem lpsEncodedXRow_eq {q D r r' s : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (e : Fin s ≃ F) (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (x : LPSSparseXIndex q D r) :
    lpsEncodedXRow (encodedFieldTables e) label (h.map e.symm)
      (h'.map e.symm) x =
      (lpsSparseXRow label h h' x).map (fun entry => (entry.1, e.symm entry.2)) := by
  have hneg (a : F) : encodedFieldNeg (encodedFieldTables e) (e.symm a) = e.symm (-a) := by
    apply e.injective
    simp [encodedFieldNeg_decode]
  simp [lpsEncodedXRow, lpsSparseXRow, List.map_ofFn, Function.comp_def, hneg]

theorem lpsEncodedZRow_eq {q D r r' s : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (e : Fin s ≃ F) (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (z : LPSSparseZIndex q D r') :
    lpsEncodedZRow label (h.map e.symm) (h'.map e.symm) z =
      (lpsSparseZRow label h h' z).map (fun entry => (entry.1, e.symm entry.2)) := by
  simp [lpsEncodedZRow, lpsSparseZRow, List.map_ofFn, Function.comp_def]

abbrev LPSEncodedCheckIndex (q D r r' s : ℕ) [Fact q.Prime] :=
  Sum (LPSSparseXIndex q D r × Fin s) (LPSSparseZIndex q D r' × Fin s)

def lpsEncodedCheckRow {q D r r' s : ℕ} [Fact q.Prime]
    (t : EncodedFieldTables s) (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) (Fin s)) (h' : Matrix (Fin r') (Fin D) (Fin s))
    (c : LPSEncodedCheckIndex q D r r' s) :
    List (LPSSparseQubitIndex q D r r' × Fin s) :=
  match c with
  | Sum.inl (x, a) => encodedSparseScalarRow t a (lpsEncodedXRow t label h h' x)
  | Sum.inr (z, a) => encodedSparseScalarRow t a (lpsEncodedZRow label h h' z)

def lpsEncodedCheckDecode {q D r r' s : ℕ} [Fact q.Prime] {F : Type}
    (e : Fin s ≃ F) (c : LPSEncodedCheckIndex q D r r' s) :
    FiniteFieldCSSPresentation.CheckIndex F
      (LiftedProduct.C0Index (Fin 2 × Fin r) (Fin D) PSL(2, ZMod q))
      (LiftedProduct.C2Index (Fin D) (Fin 2 × Fin r') PSL(2, ZMod q)) :=
  match c with
  | Sum.inl (x, a) => Sum.inl (lpsSparseXDecode x, e a)
  | Sum.inr (z, a) => Sum.inr (lpsSparseZDecode z, e a)

noncomputable def lpsPresentationCheckWord {F : Type} [Field F] [Fintype F]
    {q D r r' : ℕ} [Fact q.Prime] (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (c : FiniteFieldCSSPresentation.CheckIndex F
      (LiftedProduct.C0Index (Fin 2 × Fin r) (Fin D) PSL(2, ZMod q))
      (LiftedProduct.C2Index (Fin D) (Fin 2 × Fin r') PSL(2, ZMod q))) :=
  match c with
  | Sum.inl p => FiniteFieldCSSPresentation.xCheckWord
      (LiftedProduct.chainComplex (data (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h')) p
  | Sum.inr p => FiniteFieldCSSPresentation.zCheckWord
      (LiftedProduct.chainComplex (data (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h')) p

theorem lpsEncodedCheckRow_value_eq {q D r r' s : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F] (e : Fin s ≃ F)
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) (c : LPSEncodedCheckIndex q D r r' s)
    (qubit : LPSSparseQubitIndex q D r r') :
    e (encodedSparseRowValue (encodedFieldTables e)
      (lpsEncodedCheckRow (encodedFieldTables e) label (h.map e.symm)
        (h'.map e.symm) c) qubit) =
      lpsPresentationCheckWord label h h' (lpsEncodedCheckDecode e c)
        (lpsSparseQubitDecode qubit) := by
  classical
  rcases c with ⟨x,a⟩ | ⟨z,a⟩
  · simp only [lpsEncodedCheckRow, lpsEncodedXRow_eq, encodedSparseScalarRow_value,
      lpsSparseXRow_value_eq, lpsPresentationCheckWord, lpsEncodedCheckDecode,
      FiniteFieldCSSPresentation.xCheckWord, LinearMap.map_smul, Pi.smul_apply,
      smul_eq_mul]
    congr 1
    exact (LiftedProduct.transpose_boundary1_canonicalBasisWord_apply _ _ _).symm
  · simp only [lpsEncodedCheckRow, lpsEncodedZRow_eq, encodedSparseScalarRow_value,
      lpsSparseZRow_value_eq, lpsPresentationCheckWord, lpsEncodedCheckDecode,
      FiniteFieldCSSPresentation.zCheckWord, LinearMap.map_smul, Pi.smul_apply,
      smul_eq_mul]
    congr 1
    exact (LiftedProduct.boundary2_canonicalBasisWord_apply _ _ _).symm


def lpsEncodedCheckNumbering {q D r r' s : ℕ} [Fact q.Prime] :
    LPSEncodedCheckIndex q D r r' s ≃
      Fin (((2 * r) * (D * (lpsPSLList q).length)) * s +
        (D * ((2 * r') * (lpsPSLList q).length)) * s) :=
  (Equiv.sumCongr
    ((Equiv.prodCongr (lpsSparseTripleEquiv _ _ _) (Equiv.refl _)).trans finProdFinEquiv)
    ((Equiv.prodCongr (lpsSparseTripleEquiv _ _ _) (Equiv.refl _)).trans finProdFinEquiv)).trans
      finSumFinEquiv

def lpsEncodedCheckEquiv {q D r r' s : ℕ} [Fact q.Prime] {F : Type} (e : Fin s ≃ F) :
    LPSEncodedCheckIndex q D r r' s ≃
    FiniteFieldCSSPresentation.CheckIndex F
      (LiftedProduct.C0Index (Fin 2 × Fin r) (Fin D) PSL(2, ZMod q))
      (LiftedProduct.C2Index (Fin D) (Fin 2 × Fin r') PSL(2, ZMod q)) :=
  Equiv.sumCongr
    (Equiv.prodCongr
      (Equiv.prodCongr finProdFinEquiv.symm
        (Equiv.prodCongr (Equiv.refl _) (lpsPSLEnumerationEquiv q))) e)
    (Equiv.prodCongr
      (Equiv.prodCongr (Equiv.refl _)
        (Equiv.prodCongr finProdFinEquiv.symm (lpsPSLEnumerationEquiv q))) e)

theorem lpsEncodedCheckEquiv_apply {q D r r' s : ℕ} [Fact q.Prime] {F : Type}
    (e : Fin s ≃ F) (c : LPSEncodedCheckIndex q D r r' s) :
    lpsEncodedCheckEquiv e c = lpsEncodedCheckDecode e c := by cases c <;> rfl

/-- Complete scalar-decorated output using only fixed numeric field tables and numeric indices. -/
def lpsEncodedCheckOutput {q D r r' s : ℕ} [Fact q.Prime]
    (t : EncodedFieldTables s) (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) (Fin s)) (h' : Matrix (Fin r') (Fin D) (Fin s)) :=
  List.ofFn fun i : Fin (((2 * r) * (D * (lpsPSLList q).length)) * s +
        (D * ((2 * r') * (lpsPSLList q).length)) * s) =>
    (lpsEncodedCheckRow t label h h' (lpsEncodedCheckNumbering.symm i)).map
      (fun entry => (lpsSparseQubitNumbering entry.1, entry.2))

theorem lpsEncodedCheckOutput_length {q D r r' s : ℕ} [Fact q.Prime]
    (t : EncodedFieldTables s) (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) (Fin s)) (h' : Matrix (Fin r') (Fin D) (Fin s)) :
    (lpsEncodedCheckOutput t label h h').length =
      (((2 * r) * (D * (lpsPSLList q).length)) * s +
        (D * ((2 * r') * (lpsPSLList q).length)) * s) := by
  simp [lpsEncodedCheckOutput]

theorem encodedSparseRowValue_map_equiv {Q Q' : Type} [DecidableEq Q] [DecidableEq Q']
    {s : ℕ} (t : EncodedFieldTables s) (e : Q ≃ Q') (row : List (Q × Fin s)) (x : Q) :
    encodedSparseRowValue t (row.map fun entry => (e entry.1, entry.2)) (e x) =
      encodedSparseRowValue t row x := by
  induction row with
  | nil => rfl
  | cons a row ih =>
      simp only [encodedSparseRowValue] at ih
      simp only [List.map_cons, encodedSparseRowValue, List.foldr_cons, e.injective.eq_iff,
        ih]

theorem lpsEncodedCheckOutput_value_eq {q D r r' s : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F] (e : Fin s ≃ F)
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F)
    (i : Fin (((2 * r) * (D * (lpsPSLList q).length)) * s +
        (D * ((2 * r') * (lpsPSLList q).length)) * s))
    (qubit : LPSSparseQubitIndex q D r r') :
    e (encodedSparseRowValue (encodedFieldTables e)
      ((lpsEncodedCheckOutput (encodedFieldTables e) label
        (h.map e.symm) (h'.map e.symm))[i.val]'(by
          simp [lpsEncodedCheckOutput])) (lpsSparseQubitNumbering qubit)) =
      lpsPresentationCheckWord label h h'
        (lpsEncodedCheckDecode e (lpsEncodedCheckNumbering.symm i))
        (lpsSparseQubitDecode qubit) := by
  simp only [lpsEncodedCheckOutput, List.getElem_ofFn]
  rw [encodedSparseRowValue_map_equiv]
  exact lpsEncodedCheckRow_value_eq e label h h' _ qubit

/-- Computed nonzero-coordinate lists for every scalar-decorated check. -/
def lpsEncodedCheckRegions {q D r r' s : ℕ} [Fact q.Prime]
    (t : EncodedFieldTables s) (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) (Fin s)) (h' : Matrix (Fin r') (Fin D) (Fin s)) :=
  (lpsEncodedCheckOutput t label h h').map (encodedSparseRegion t)

theorem lpsEncodedCheckRegions_length {q D r r' s : ℕ} [Fact q.Prime]
    (t : EncodedFieldTables s) (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) (Fin s)) (h' : Matrix (Fin r') (Fin D) (Fin s)) :
    (lpsEncodedCheckRegions t label h h').length =
      (((2 * r) * (D * (lpsPSLList q).length)) * s +
        (D * ((2 * r') * (lpsPSLList q).length)) * s) := by
  simp [lpsEncodedCheckRegions, lpsEncodedCheckOutput_length]

noncomputable local instance {q D r r' : ℕ} [Fact q.Prime] : DecidableEq
    (LiftedProduct.QubitIndex (Fin 2 × Fin r) (Fin D) (Fin D)
      (Fin 2 × Fin r') PSL(2, ZMod q)) := Classical.decEq _

/-- Exact support, including the zero scalar and fields whose encoded zero is not index zero. -/
theorem lpsEncodedCheckRegions_mem_iff {q D r r' s : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F] (e : Fin s ≃ F)
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F)
    (i : Fin (((2 * r) * (D * (lpsPSLList q).length)) * s +
        (D * ((2 * r') * (lpsPSLList q).length)) * s))
    (qubit : LPSSparseQubitIndex q D r r') :
    lpsSparseQubitNumbering qubit ∈
      (lpsEncodedCheckRegions (encodedFieldTables e) label
        (h.map e.symm) (h'.map e.symm))[i.val]'(by
          rw [lpsEncodedCheckRegions_length]; exact i.isLt) ↔
      lpsSparseQubitDecode qubit ∈
        ((semanticPresentation (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h').checks
          (lpsEncodedCheckDecode e (lpsEncodedCheckNumbering.symm i))).region.selected := by
  classical
  simp only [lpsEncodedCheckRegions, List.getElem_map, mem_encodedSparseRegion]
  rw [← encodedSparseRowValue_decode, lpsEncodedCheckOutput_value_eq]
  cases hc : lpsEncodedCheckNumbering.symm i with
  | inl p =>
      simp [lpsPresentationCheckWord, lpsEncodedCheckDecode, semanticPresentation,
        FiniteFieldCSSPresentation.presentation, FiniteFieldCSSPresentation.check,
        FiniteFieldCSSPresentation.wordRegion, hammingSupport]
  | inr p =>
      simp [lpsPresentationCheckWord, lpsEncodedCheckDecode, semanticPresentation,
        FiniteFieldCSSPresentation.presentation, FiniteFieldCSSPresentation.check,
        FiniteFieldCSSPresentation.wordRegion, hammingSupport]


/-- Interpret a numeric output row as a finite-field word on actual physical cells. -/
def lpsEncodedOutputWord {q D r r' s : ℕ} [Fact q.Prime] {F : Type}
    (e : Fin s ≃ F) (t : EncodedFieldTables s)
    (row : List (Fin (D * (D * (lpsPSLList q).length) +
      (2 * r) * ((2 * r') * (lpsPSLList q).length)) × Fin s))
    (physical : LiftedProduct.QubitIndex (Fin 2 × Fin r) (Fin D) (Fin D)
      (Fin 2 × Fin r') PSL(2, ZMod q)) : F :=
  e (encodedSparseRowValue t row
    (lpsSparseQubitNumbering (lpsSparseQubitEquiv.symm physical)))

theorem lpsEncodedOutputWord_eq {q D r r' s : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F] (e : Fin s ≃ F)
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F)
    (i : Fin (((2 * r) * (D * (lpsPSLList q).length)) * s +
        (D * ((2 * r') * (lpsPSLList q).length)) * s)) :
    lpsEncodedOutputWord e (encodedFieldTables e)
      ((lpsEncodedCheckOutput (encodedFieldTables e) label
        (h.map e.symm) (h'.map e.symm))[i.val]'(by simp [lpsEncodedCheckOutput])) =
      lpsPresentationCheckWord label h h'
        (lpsEncodedCheckDecode e (lpsEncodedCheckNumbering.symm i)) := by
  funext physical
  have hv := lpsEncodedCheckOutput_value_eq e label h h' i
    (lpsSparseQubitEquiv.symm physical)
  simpa only [lpsEncodedOutputWord, ← lpsSparseQubitEquiv_apply,
    Equiv.apply_symm_apply] using hv

open FiniteFieldPauli
/-- Pauli interpretation of the output word, using the computed X/Z check tag. -/
noncomputable def lpsEncodedOutputOperator {q D r r' s : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F] (e : Fin s ≃ F)
    (t : EncodedFieldTables s) (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) (Fin s)) (h' : Matrix (Fin r') (Fin D) (Fin s))
    (i : Fin (((2 * r) * (D * (lpsPSLList q).length)) * s +
        (D * ((2 * r') * (lpsPSLList q).length)) * s)) :=
  let word := lpsEncodedOutputWord e t
    ((lpsEncodedCheckOutput t label h h')[i.val]'(by simp [lpsEncodedCheckOutput]))
  match lpsEncodedCheckNumbering.symm i with
  | Sum.inl _ => (registerUnitary (F := F) (ι' := LiftedProduct.QubitIndex
      (Fin 2 × Fin r) (Fin D) (Fin D) (Fin 2 × Fin r') PSL(2, ZMod q))).conjOperator (shift word)
  | Sum.inr _ => (registerUnitary (F := F) (ι' := LiftedProduct.QubitIndex
      (Fin 2 × Fin r) (Fin D) (Fin D) (Fin 2 × Fin r') PSL(2, ZMod q))).conjOperator (phase word)

theorem lpsEncodedOutputOperator_eq {q D r r' s : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F] (e : Fin s ≃ F)
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F)
    (i : Fin (((2 * r) * (D * (lpsPSLList q).length)) * s +
        (D * ((2 * r') * (lpsPSLList q).length)) * s)) :
    lpsEncodedOutputOperator e (encodedFieldTables e) label (h.map e.symm) (h'.map e.symm) i =
      ((semanticPresentation (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h').checks
        (lpsEncodedCheckDecode e (lpsEncodedCheckNumbering.symm i))).globalOperator := by
  simp only [lpsEncodedOutputOperator, lpsEncodedOutputWord_eq]
  cases hc : lpsEncodedCheckNumbering.symm i with
  | inl p =>
      exact (FiniteFieldCSSPresentation.check_inl_globalOperator _ _).symm
  | inr p =>
      exact (FiniteFieldCSSPresentation.check_inr_globalOperator _ _).symm

/-- All computed scalar checks cut out exactly the actual Tanner CSS carrier. -/
theorem mem_carrier_iff_lpsEncodedOutput {q D r r' s : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F] (e : Fin s ≃ F)
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F)
    (ψ : Semantics.Qudit.QuditRegister (fun _ : LiftedProduct.QubitIndex
      (Fin 2 × Fin r) (Fin D) (Fin D) (Fin 2 × Fin r') PSL(2, ZMod q) => Fintype.card F)) :
    ψ ∈ (semanticPresentation (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h').code.carrier ↔
      ∀ i, lpsEncodedOutputOperator e (encodedFieldTables e) label
        (h.map e.symm) (h'.map e.symm) i ψ = ψ := by
  refine ((semanticPresentation (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h').carrier_iff_fixed ψ).trans ?_
  simp_rw [lpsEncodedOutputOperator_eq]
  constructor
  · intro hall i
    exact hall _
  · intro hall c
    obtain ⟨i, hi⟩ := (lpsEncodedCheckNumbering.symm.trans (lpsEncodedCheckEquiv e)).surjective c
    have hi' : lpsEncodedCheckDecode e (lpsEncodedCheckNumbering.symm i) = c := by
      simpa only [Equiv.trans_apply, lpsEncodedCheckEquiv_apply] using hi
    exact hi' ▸ hall i


/-- The original PK22 family is cut out by these complete numeric scalar checks. -/
theorem mem_originalFamily_carrier_iff_lpsEncodedOutput {p D r r' s : ℕ}
    {F : Type} [Field F] [Fintype F] (e : Fin s ≃ F)
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
    (generators : Fin D → LPSGeneratorIndex p)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (ψ : Semantics.Qudit.QuditRegister (fun _ : LiftedProduct.QubitIndex
      (Fin 2 × Fin r) (Fin D) (Fin D) (Fin 2 × Fin r')
      PSL(2, ZMod (lpsResiduePrimeSequence hp hp4 n).q) => Fintype.card F)) :
    ψ ∈ (semanticPresentation (fun j => lpsQuaternionFamilyLabel hp hp4 n (generators j))
      h h').code.carrier ↔
      ∀ i, lpsEncodedOutputOperator e (encodedFieldTables e)
        (fun j => lpsEffectiveQuaternionFamilyIndex hp hp4 n (generators j))
        (h.map e.symm) (h'.map e.symm) i ψ = ψ := by
  have hLabel :
      (fun j => (lpsPSLEnumerationEquiv (lpsResiduePrimeSequence hp hp4 n).q)
        (lpsEffectiveQuaternionFamilyIndex hp hp4 n (generators j))) =
      (fun j => lpsQuaternionFamilyLabel hp hp4 n (generators j)) :=
    funext (fun j => lpsEffectiveQuaternionFamilyIndex_decode_original hp hp4 n (generators j))
  have hCarrier := congrArg (fun label => ψ ∈ (semanticPresentation label h h').code.carrier) hLabel
  exact (Iff.of_eq hCarrier.symm).trans
    (mem_carrier_iff_lpsEncodedOutput e
      (fun j => lpsEffectiveQuaternionFamilyIndex hp hp4 n (generators j)) h h' ψ)

end QEC.Coding.TannerLiftedProduct
