import QEC.Coding.QuantumTanner.TensorPuncture

/-!
# Assembling approximate rows and columns

Attained local-code words on retained rows and columns assemble into actual
punctured row- and column-code words. Summing their residual weights gives
the error budget used in [LZ22, proof of Theorem thm:main].
-/

noncomputable section

namespace QEC.Coding.QuantumTanner

open Classical

universe v

variable {A B : Type v} [Fintype A] [Fintype B]

/-- Removing coordinates does not increase the number of nonzero entries. -/
theorem hammingWeight_punctureMap_le {ι : Type v} [Fintype ι]
    (removed : Finset ι) (x : Word (ZMod 2) ι) :
    HammingWeight (punctureMap removed x) ≤ HammingWeight x := by
  have hSubset : (hammingSupport (punctureMap removed x)).image Subtype.val ⊆
      hammingSupport x := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  have hCard := Finset.card_le_card hSubset
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hCard
  exact hCard

/-- Matrix weight is the sum of the actual row weights. -/
theorem hammingWeight_matrix_eq_sum_rows (x : Word (ZMod 2) (A × B)) :
    HammingWeight x = ∑ a : A, HammingWeight (rowRestriction a x) := by
  simp only [HammingWeight, hammingSupport, Finset.card_filter,
    Fintype.sum_prod_type]
  rfl

/-- Matrix weight is also the sum of the actual column weights. -/
theorem hammingWeight_matrix_eq_sum_columns (x : Word (ZMod 2) (A × B)) :
    HammingWeight x = ∑ b : B, HammingWeight (columnRestriction b x) := by
  simp only [HammingWeight, hammingSupport, Finset.card_filter,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rfl

/-- Per-line attained approximations give two genuine punctured-code words
with a total residual budget; no nearest-word oracle is assumed. -/
theorem exists_punctured_row_column_approximations
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (removedA : Finset A) (removedB : Finset B)
    (x : Word (ZMod 2) (A × B)) (rowError columnError : Nat)
    (hRows : ∀ a : KeptCoordinate removedA, ∃ r : Word (ZMod 2) B,
      r ∈ CB.carrier ∧ HammingWeight (rowRestriction a.1 x + r) ≤ rowError)
    (hColumns : ∀ b : KeptCoordinate removedB, ∃ c : Word (ZMod 2) A,
      c ∈ CA.carrier ∧ HammingWeight (columnRestriction b.1 x + c) ≤ columnError) :
    ∃ C R : Word (ZMod 2) (KeptCoordinate removedA × KeptCoordinate removedB),
      C ∈ (columnCode (puncturedCode CA removedA)).carrier ∧
      R ∈ (rowCode (puncturedCode CB removedB)).carrier ∧
      HammingWeight (tensorPunctureMap removedA removedB x + C) ≤
        Fintype.card B * columnError ∧
      HammingWeight (tensorPunctureMap removedA removedB x + R) ≤
        Fintype.card A * rowError := by
  choose rowWord hRowMem hRowClose using hRows
  choose columnWord hColumnMem hColumnClose using hColumns
  let R : Word (ZMod 2) (KeptCoordinate removedA × KeptCoordinate removedB) :=
    fun ab => rowWord ab.1 ab.2.1
  let C : Word (ZMod 2) (KeptCoordinate removedA × KeptCoordinate removedB) :=
    fun ab => columnWord ab.2 ab.1.1
  have hR : R ∈ (rowCode (puncturedCode CB removedB)).carrier := by
    intro a
    exact (mem_puncturedCode CB removedB _).mpr ⟨rowWord a, hRowMem a, rfl⟩
  have hC : C ∈ (columnCode (puncturedCode CA removedA)).carrier := by
    intro b
    exact (mem_puncturedCode CA removedA _).mpr ⟨columnWord b, hColumnMem b, rfl⟩
  have hColumnError (b : KeptCoordinate removedB) :
      HammingWeight (columnRestriction b (tensorPunctureMap removedA removedB x + C)) ≤
        columnError := by
    have hSame : columnRestriction b (tensorPunctureMap removedA removedB x + C) =
        punctureMap removedA (columnRestriction b.1 x + columnWord b) := by
      ext a
      rfl
    rw [hSame]
    exact (hammingWeight_punctureMap_le removedA _).trans (hColumnClose b)
  have hRowError (a : KeptCoordinate removedA) :
      HammingWeight (rowRestriction a (tensorPunctureMap removedA removedB x + R)) ≤
        rowError := by
    have hSame : rowRestriction a (tensorPunctureMap removedA removedB x + R) =
        punctureMap removedB (rowRestriction a.1 x + rowWord a) := by
      ext b
      rfl
    rw [hSame]
    exact (hammingWeight_punctureMap_le removedB _).trans (hRowClose a)
  refine ⟨C, R, hC, hR, ?_, ?_⟩
  · calc
      HammingWeight (tensorPunctureMap removedA removedB x + C) =
          ∑ b : KeptCoordinate removedB,
            HammingWeight (columnRestriction b (tensorPunctureMap removedA removedB x + C)) :=
        hammingWeight_matrix_eq_sum_columns _
      _ ≤ ∑ _b : KeptCoordinate removedB, columnError :=
        Finset.sum_le_sum fun b _ => hColumnError b
      _ = Fintype.card (KeptCoordinate removedB) * columnError := by simp
      _ ≤ Fintype.card B * columnError :=
        Nat.mul_le_mul_right _ (Fintype.card_subtype_le _)
  · calc
      HammingWeight (tensorPunctureMap removedA removedB x + R) =
          ∑ a : KeptCoordinate removedA,
            HammingWeight (rowRestriction a (tensorPunctureMap removedA removedB x + R)) :=
        hammingWeight_matrix_eq_sum_rows _
      _ ≤ ∑ _a : KeptCoordinate removedA, rowError :=
        Finset.sum_le_sum fun a _ => hRowError a
      _ = Fintype.card (KeptCoordinate removedA) * rowError := by simp
      _ ≤ Fintype.card A * rowError :=
        Nat.mul_le_mul_right _ (Fintype.card_subtype_le _)

end QEC.Coding.QuantumTanner
