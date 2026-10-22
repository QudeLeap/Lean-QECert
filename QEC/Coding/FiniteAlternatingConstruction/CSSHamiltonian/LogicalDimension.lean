import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.Gibbs
import QEC.Coding.FiniteAlternatingConstruction.FiniteCohomology
import QEC.Coding.Stabilizer.FiniteFieldPauli

/-!
# Actual binary CSS dimension and syndrome multiplicity

BDL26 v1 `paper.tex:1817–1935,2097–2114,2202–2225,2240,2258`, approved
source gate #840. Actual finite H¹ classification determines the dimension
of the existing binary QubitRegister code. The generic finite-field module
is used only for its proved cohomology/homology rank identity.
-/

noncomputable section
namespace QEC.Coding.BDL26CSSHamiltonian

open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder

variable (S : OddScale) (n : Nat)

/-- The actual semantic cohomology uses the literal transposed incidence maps. -/
theorem cohomology_finrank_one :
    Module.finrank (ZMod 2) (complex S n).middleCohomology = 1 :=
  BDL26FiniteCohomology.finrank_eq_one S n

/-- Reconcile the binary CSS homology convention by a proved finite-rank identity. -/
theorem homology_finrank_one :
    Module.finrank (ZMod 2) (complex S n).middleHomology = 1 := by
  have h := FiniteFieldPauli.chainComplex_finrank_middleCohomology_eq_middleHomology (complex S n)
  exact h.symm.trans (cohomology_finrank_one S n)

/-- The actual binary CSS code lives on the existing physical QubitRegister. -/
theorem chain_css_carrier_finrank_two :
    Module.finrank ℂ (complex S n).binaryCSSCode.stabilizer.code.carrier = 2 := by
  rw [(complex S n).binaryCSSCode_finrank_stabilizer_code_carrier_eq_pow_finrank_middleHomology,
    homology_finrank_one]
  norm_num

/-- The literal labelled-check quantum code; no alternate register or new code model. -/
def labelledCode : QuantumCode (Qubit.QubitRegister (Physical S n)) :=
  (binaryCSSStabilizerCodeOfParityChecks (zSyndrome S n) (xSyndrome S n)
    (row_orthogonal S n)).code

theorem labelledCode_carrier :
    (labelledCode S n).carrier = (complex S n).binaryCSSCode.stabilizer.code.carrier :=
  code_carrier S n

theorem labelled_code_carrier_finrank_two :
    Module.finrank ℂ (labelledCode S n).carrier = 2 := by
  rw [labelledCode_carrier]
  exact chain_css_carrier_finrank_two S n

/-- Binary logical exponent one corresponds to complex codespace dimension two. -/
theorem labelled_code_dimension_two : (labelledCode S n).dimension = 2 := by
  rw [QuantumCode.dimension_eq_finrank_carrier]
  exact labelled_code_carrier_finrank_two S n

/-- Actual image ranks account for every repeated or identity labelled check. -/
theorem binary_logical_exponent_one :
    Fintype.card (Physical S n) - CSSGibbs.checkRank (zSyndrome S n) -
      CSSGibbs.checkRank (xSyndrome S n) = 1 := by
  have h := (complex S n).length_sub_firstCoboundaryCheckCode_sub_middleBoundaryCode_eq_finrank_middleHomology
  rw [homology_finrank_one S n] at h
  have hz := CSSGibbs.checkRank_eq_rowDimension (zSyndrome S n)
  have hx := CSSGibbs.checkRank_eq_rowDimension (xSyndrome S n)
  rw [zRowCode S n] at hz
  rw [xRowCode S n] at hx
  change Fintype.card (Physical S n) - Dimension (complex S n).firstCoboundaryCheckCode -
    Dimension (complex S n).middleBoundaryCode = 1 at h
  omega

theorem check_rank_sum_plus_one :
    CSSGibbs.checkRank (zSyndrome S n) + CSSGibbs.checkRank (xSyndrome S n) + 1 =
      Fintype.card (Physical S n) := by
  have h := binary_logical_exponent_one S n
  have hle := CSSGibbs.checkRanks_le (zSyndrome S n) (xSyndrome S n) (row_orthogonal S n)
  omega

/-- The actual zero syndrome eigenspace is the actual binary CSS codespace. -/
theorem zero_sector_finrank_two : Module.finrank ℂ (sector S n 0) = 2 := by
  rw [zero_sector_code S n]
  exact chain_css_carrier_finrank_two S n

/-- Equal multiplicity is derived from the actual zero-sector dimension. -/
theorem multiplicity_two : multiplicity S n = 2 := by
  have h := CSSGibbs.sector_zero_finrank (zSyndrome S n) (xSyndrome S n) (row_orthogonal S n)
  exact h.symm.trans (zero_sector_finrank_two S n)

theorem zero_projector_range_labelledCode :
    LinearMap.range (projector S n 0) = (labelledCode S n).carrier := by
  change sector S n 0 = (labelledCode S n).carrier
  rw [zero_sector_code S n, labelledCode_carrier S n]

theorem zero_projector_range_finrank_two :
    Module.finrank ℂ (LinearMap.range (projector S n 0)) = 2 := by
  rw [zero_projector_range_labelledCode S n]
  exact labelled_code_carrier_finrank_two S n

theorem zero_projector_fixed_iff_labelledCode (v : Qubit.QubitRegister (Physical S n)) :
    projector S n 0 v = v ↔ v ∈ (labelledCode S n).carrier := by
  rw [labelledCode_carrier S n]
  exact zero_projector_code S n v

/-- Proved Pauli sector transport applies to every actual realizable pair. -/
theorem realizable_sector_finrank_two (u : LinearMap.range (zSyndrome S n))
    (v : LinearMap.range (xSyndrome S n)) :
    Module.finrank ℂ (sector S n (CSSGibbs.joinSyndrome u.val v.val)) = 2 :=
  (sector_multiplicity S n u v).trans (multiplicity_two S n)

theorem realizable_projector_trace_two (u : LinearMap.range (zSyndrome S n))
    (v : LinearMap.range (xSyndrome S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      (projector S n (CSSGibbs.joinSyndrome u.val v.val)) = (2 : ℂ) := by
  rw [CSSGibbs.trace_projector]
  exact_mod_cast realizable_sector_finrank_two S n u v

local instance : Fintype (LinearMap.range (zSyndrome S n)) := Fintype.ofFinite _
local instance : Fintype (LinearMap.range (xSyndrome S n)) := Fintype.ofFinite _

/-- Finite visible realizability, with the original redundant row labels retained. -/
abbrev visibleRealizable := CSSGibbs.realizableSyndromes (zSyndrome S n) (xSyndrome S n)

theorem visible_sector_finrank_two
    (s : Word (ZMod 2) (Sum (ZLabel S n) (XLabel S n)))
    (hs : s ∈ visibleRealizable S n) : Module.finrank ℂ (sector S n s) = 2 := by
  have huv := (CSSGibbs.mem_realizableSyndromes_iff (zSyndrome S n) (xSyndrome S n) s).mp hs
  let u : LinearMap.range (zSyndrome S n) := ⟨fun z => s (.inl z), huv.1⟩
  let v : LinearMap.range (xSyndrome S n) := ⟨fun x => s (.inr x), huv.2⟩
  have hword : CSSGibbs.joinSyndrome u.val v.val = s := by
    funext j
    cases j <;> rfl
  have hr := realizable_sector_finrank_two S n u v
  exact (congrArg (fun t : Word (ZMod 2) (Sum (ZLabel S n) (XLabel S n)) =>
    Module.finrank ℂ (sector S n t)) hword).symm.trans hr

theorem invisible_sector_finrank_zero
    (s : Word (ZMod 2) (Sum (ZLabel S n) (XLabel S n)))
    (hs : s ∉ visibleRealizable S n) : Module.finrank ℂ (sector S n s) = 0 :=
  CSSGibbs.sector_finrank_zero_of_not_realizable (zSyndrome S n) (xSyndrome S n)
    (row_orthogonal S n) s hs

/-- Complete visible-syndrome formula, including the unrealizable zero branch. -/
theorem visible_sector_finrank_formula
    (s : Word (ZMod 2) (Sum (ZLabel S n) (XLabel S n))) :
    Module.finrank ℂ (sector S n s) = if s ∈ visibleRealizable S n then 2 else 0 := by
  by_cases hs : s ∈ visibleRealizable S n
  · exact (visible_sector_finrank_two S n s hs).trans (if_pos hs).symm
  · exact (invisible_sector_finrank_zero S n s hs).trans (if_neg hs).symm

theorem visible_projector_trace_formula
    (s : Word (ZMod 2) (Sum (ZLabel S n) (XLabel S n))) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n)) (projector S n s) =
      if s ∈ visibleRealizable S n then (2 : ℂ) else 0 := by
  calc
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n)) (projector S n s) =
        (Module.finrank ℂ (sector S n s) : ℂ) :=
      CSSGibbs.trace_projector (zSyndrome S n) (xSyndrome S n) (row_orthogonal S n) s
    _ = if s ∈ visibleRealizable S n then (2 : ℂ) else 0 := by
      by_cases hs : s ∈ visibleRealizable S n
      · have hr := visible_sector_finrank_two S n s hs
        calc
          (Module.finrank ℂ (sector S n s) : ℂ) = (2 : ℂ) := by exact_mod_cast hr
          _ = if s ∈ visibleRealizable S n then (2 : ℂ) else 0 := (if_pos hs).symm
      · have hr := invisible_sector_finrank_zero S n s hs
        calc
          (Module.finrank ℂ (sector S n s) : ℂ) = (0 : ℂ) := by exact_mod_cast hr
          _ = if s ∈ visibleRealizable S n then (2 : ℂ) else 0 := (if_neg hs).symm

/-- The literal even-prefix specialization selected by the source. -/
theorem even_code_dimension_two (k : Nat) : (labelledCode S (2*k)).dimension = 2 :=
  labelled_code_dimension_two S (2*k)

theorem even_binary_logical_exponent_one (k : Nat) :
    Fintype.card (Physical S (2*k)) - CSSGibbs.checkRank (zSyndrome S (2*k)) -
      CSSGibbs.checkRank (xSyndrome S (2*k)) = 1 := binary_logical_exponent_one S (2*k)

/-- Exact existing indexed physical carrier at every depth and level. -/
def indexedLabelledCode (depth : Nat) (i : LevelIndex depth) :
    QuantumCode (Qubit.QubitRegister (BDL26IndexedDecoder.FamilyQ S depth i)) :=
  labelledCode S i.val

theorem indexedLabelledCode_carrier (depth : Nat) (i : LevelIndex depth) :
    (indexedLabelledCode S depth i).carrier =
      ((indexedFamily S depth).complex i).binaryCSSCode.stabilizer.code.carrier :=
  labelledCode_carrier S i.val

theorem indexed_code_dimension_two (depth : Nat) (i : LevelIndex depth) :
    (indexedLabelledCode S depth i).dimension = 2 := labelled_code_dimension_two S i.val

theorem indexed_projector_range_finrank_two (depth : Nat) (i : LevelIndex depth) :
    Module.finrank ℂ (LinearMap.range (projector S i.val 0)) = 2 :=
  zero_projector_range_finrank_two S i.val

theorem indexed_binary_logical_exponent_one (depth : Nat) (i : LevelIndex depth) :
    Fintype.card (BDL26IndexedDecoder.FamilyQ S depth i) -
      CSSGibbs.checkRank (zSyndrome S i.val) - CSSGibbs.checkRank (xSyndrome S i.val) = 1 :=
  binary_logical_exponent_one S i.val

end QEC.Coding.BDL26CSSHamiltonian
