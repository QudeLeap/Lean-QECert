import QEC.Coding.QuantumTanner.LiftedProductActionBridge
import QEC.Coding.QuantumTanner.Goodness

/-!
# Local tensor words in the selected lifted-product bridge

The row-and-column tensor-code constraints in [LZDec22, Section "Quantum
Tanner codes from Lifted Product codes"] are identified with actual products
of the two scalar generator matrices. Both directions are proved, rather
than supplied as a construction-equivalence assumption.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner.LiftedProductTensorBridge

open Classical

universe v

variable {A B C D : Type v} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

/-- The ordinary binary row code of the specified scalar matrix. -/
def matrixRowCode (P : Matrix C A (ZMod 2)) : LinearCode (ZMod 2) A :=
  parityCheckRowCode (Matrix.toLin' P)

/-- Row membership is an actual finite coefficient combination of the rows. -/
theorem mem_matrixRowCode (P : Matrix C A (ZMod 2)) (x : Word (ZMod 2) A) :
    x ∈ (matrixRowCode P).carrier ↔
      ∃ r : C → ZMod 2, ∀ i, (∑ c, r c * P c i) = x i := by
  rw [matrixRowCode, mem_parityCheckRowCode]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    intro i
    simpa only [wordLinearMapTranspose_toLin'_apply] using congrFun hr i
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    ext i
    simpa only [wordLinearMapTranspose_toLin'_apply] using hr i

/-- A coefficient matrix gives a local tensor word by the two scalar row generators. -/
def tensorMatrix (P : Matrix C A (ZMod 2)) (Q : Matrix D B (ZMod 2))
    (U : Matrix C D (ZMod 2)) : Word (ZMod 2) (A × B) :=
  fun ij => ∑ c, ∑ d, U c d * P c ij.1 * Q d ij.2

/-- Every matrix product satisfies the local tensor row and column constraints. -/
theorem tensorMatrix_mem (P : Matrix C A (ZMod 2)) (Q : Matrix D B (ZMod 2))
    (U : Matrix C D (ZMod 2)) :
    tensorMatrix P Q U ∈ (tensorCode (matrixRowCode P) (matrixRowCode Q)).carrier := by
  rw [mem_tensorCode]
  constructor
  · intro j
    apply (mem_matrixRowCode P _).2
    refine ⟨fun c => ∑ d, U c d * Q d j, ?_⟩
    intro i
    simp [tensorMatrix, columnRestriction, Finset.sum_mul, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm]
  · intro i
    apply (mem_matrixRowCode Q _).2
    refine ⟨fun d => ∑ c, U c d * P c i, ?_⟩
    intro j
    simp only [rowRestriction, LinearMap.coe_mk, AddHom.coe_mk, tensorMatrix,
      Finset.sum_mul]
    exact Finset.sum_comm

/-- Both tensor-code constraints are sufficient for an actual matrix-product parameter.
The proof uses tensor-code induction on pure products of local row-code words.
No global bridge equality or factorization certificate is an input. -/
theorem mem_tensorCode_iff_tensorMatrix
    (P : Matrix C A (ZMod 2)) (Q : Matrix D B (ZMod 2)) (x : Word (ZMod 2) (A × B)) :
    x ∈ (tensorCode (matrixRowCode P) (matrixRowCode Q)).carrier ↔
      ∃ U : Matrix C D (ZMod 2), tensorMatrix P Q U = x := by
  constructor
  · intro hx
    apply tensorCode_induction (matrixRowCode P) (matrixRowCode Q)
      (P := fun y => ∃ U, tensorMatrix P Q U = y) ?_ ?_ ?_ x hx
    · refine ⟨0, ?_⟩
      ext ij
      simp [tensorMatrix]
    · rintro y z ⟨U, rfl⟩ ⟨V, rfl⟩
      refine ⟨U + V, ?_⟩
      ext ij
      simp [tensorMatrix, add_mul, Finset.sum_add_distrib]
    · intro a ha b hb
      obtain ⟨r, hr⟩ := (mem_matrixRowCode P a).1 ha
      obtain ⟨s, hs⟩ := (mem_matrixRowCode Q b).1 hb
      refine ⟨fun c d => r c * s d, ?_⟩
      ext ij
      rw [← hr ij.1, ← hs ij.2]
      simp only [tensorMatrix, Finset.sum_mul, Finset.mul_sum]
      simp only [mul_assoc, mul_left_comm, mul_comm]
      exact Finset.sum_comm
  · rintro ⟨U, rfl⟩
    exact tensorMatrix_mem P Q U

end QEC.Coding.QuantumTanner.LiftedProductTensorBridge
