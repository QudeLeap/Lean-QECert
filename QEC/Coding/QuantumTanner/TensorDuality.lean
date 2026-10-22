import QEC.Coding.QuantumTanner.Core
import QEC.Coding.Core.Duality

/-!
# Tensor-code orthogonal complements

The actual row/column sum is the dual of the tensor of the dual local codes,
as in [LZ22, Section 2, Tensor codes and dual tensor codes: robustness].
This identifies subspaces; it does not assume robustness or a distance bound.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner

open Classical

universe u v

variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

/-- Embed one column and put zero in all other columns. -/
def columnExtension (b : B) (c : Word F A) : Word F (A × B) :=
  fun ab => if ab.2 = b then c ab.1 else 0

/-- Embed one row and put zero in all other rows. -/
def rowExtension (a : A) (r : Word F B) : Word F (A × B) :=
  fun ab => if ab.1 = a then r ab.2 else 0

theorem wordPairing_columnExtension (x : Word F (A × B)) (b : B) (c : Word F A) :
    wordPairing x (columnExtension b c) = wordPairing (columnRestriction b x) c := by
  simp [wordPairing_apply, dotProduct, columnExtension, columnRestriction,
    Fintype.sum_prod_type]

theorem wordPairing_rowExtension (x : Word F (A × B)) (a : A) (r : Word F B) :
    wordPairing x (rowExtension a r) = wordPairing (rowRestriction a x) r := by
  simp [wordPairing_apply, dotProduct, rowExtension, rowRestriction,
    Fintype.sum_prod_type, Finset.mul_sum]

/-- The global pairing is the sum of its column pairings. -/
theorem wordPairing_eq_sum_column (x y : Word F (A × B)) :
    wordPairing x y = ∑ b : B, wordPairing (columnRestriction b x) (columnRestriction b y) := by
  simp only [wordPairing_apply, dotProduct, Fintype.sum_prod_type,
    columnRestriction, LinearMap.coe_mk, AddHom.coe_mk]
  exact Finset.sum_comm

/-- The global pairing is the sum of its row pairings. -/
theorem wordPairing_eq_sum_row (x y : Word F (A × B)) :
    wordPairing x y = ∑ a : A, wordPairing (rowRestriction a x) (rowRestriction a y) := by
  simp [wordPairing_apply, dotProduct, Fintype.sum_prod_type, rowRestriction]

/-- Column constraints dualize column by column, including empty coordinate sets. -/
theorem columnCode_dual_carrier_eq (CA : LinearCode F A) :
    (columnCode (B := B) CA).dual.carrier = (columnCode (B := B) CA.dual).carrier := by
  apply Submodule.ext
  intro x
  constructor
  · intro hx b
    refine (CA.mem_dual _).2 ?_
    intro c hc
    rw [← wordPairing_columnExtension]
    apply (columnCode CA).orthogonal_of_mem_dual hx
    intro b'
    by_cases hb : b' = b
    · subst b'
      simpa [columnRestriction, columnExtension] using hc
    · have hzero : columnRestriction b' (columnExtension b c) = 0 := by
        ext a
        simp [columnRestriction, columnExtension, hb]
      rw [hzero]
      exact CA.carrier.zero_mem
  · intro hx
    refine (LinearCode.mem_dual _ x).2 ?_
    intro y hy
    rw [wordPairing_eq_sum_column]
    apply Finset.sum_eq_zero
    intro b _hb
    exact CA.orthogonal_of_mem_dual (hx b) (hy b)

/-- Row constraints dualize row by row. -/
theorem rowCode_dual_carrier_eq (CB : LinearCode F B) :
    (rowCode (A := A) CB).dual.carrier = (rowCode (A := A) CB.dual).carrier := by
  apply Submodule.ext
  intro x
  constructor
  · intro hx a
    refine (CB.mem_dual _).2 ?_
    intro r hr
    rw [← wordPairing_rowExtension]
    apply (rowCode CB).orthogonal_of_mem_dual hx
    intro a'
    by_cases ha : a' = a
    · subst a'
      simpa [rowRestriction, rowExtension] using hr
    · have hzero : rowRestriction a' (rowExtension a r) = 0 := by
        ext b
        simp [rowRestriction, rowExtension, ha]
      rw [hzero]
      exact CB.carrier.zero_mem
  · intro hx
    refine (LinearCode.mem_dual _ x).2 ?_
    intro y hy
    rw [wordPairing_eq_sum_row]
    apply Finset.sum_eq_zero
    intro a _ha
    exact CB.orthogonal_of_mem_dual (hx a) (hy a)

/-- The orthogonal complement of the tensor intersection is the row/column sum. -/
theorem tensorCode_dual_carrier_eq (CA : LinearCode F A) (CB : LinearCode F B) :
    (tensorCode CA CB).dual.carrier = (dualTensorCode CA.dual CB.dual).carrier := by
  change ({ carrier := (columnCode CA).carrier ⊓ (rowCode CB).carrier } :
    LinearCode F (A × B)).dual.carrier = _
  rw [LinearCode.dual_inf_carrier_eq, columnCode_dual_carrier_eq, rowCode_dual_carrier_eq]
  rfl

/-- In particular, the tensor of dual codes has the primal row/column sum as dual. -/
theorem tensorCode_dual_dual_carrier_eq (CA : LinearCode F A) (CB : LinearCode F B) :
    (tensorCode CA.dual CB.dual).dual.carrier = (dualTensorCode CA CB).carrier := by
  rw [tensorCode_dual_carrier_eq, LinearCode.dual_dual_eq, LinearCode.dual_dual_eq]

end QEC.Coding.QuantumTanner
