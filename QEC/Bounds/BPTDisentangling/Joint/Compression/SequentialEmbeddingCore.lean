import QEC.Bounds.BPTDisentangling.Joint.Compression.ResidualProjection
import QEC.Bounds.BPTDisentangling.ScalarCompression.SelectedB

/-!
# BPT sequential joint-sector embedding core

Internal proof layer for the finite-dimensional BPT Disentangling Lemma.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/-- Compression through a composite embedding is the corresponding sequential compression. -/
theorem compression_comp_embedding
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (E : B →ₗ[Complex] A) (K : C →ₗ[Complex] B) (R : Semantics.Operator A) :
    (LinearMap.adjoint (E.comp K)).comp (R.comp (E.comp K)) =
      (LinearMap.adjoint K).comp
        (((LinearMap.adjoint E).comp (R.comp E)).comp K) := by
  rw [LinearMap.adjoint_comp]
  simp only [LinearMap.comp_assoc]

/-- Transport the sequential-compression identity along a concrete embedding factorization. -/
theorem compression_eq_sequential_of_eq_comp
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (J : C →ₗ[Complex] A) (E : B →ₗ[Complex] A) (K : C →ₗ[Complex] B)
    (R : Semantics.Operator A) (hJ : J = E.comp K) :
    (LinearMap.adjoint J).comp (R.comp J) =
      (LinearMap.adjoint K).comp
        (((LinearMap.adjoint E).comp (R.comp E)).comp K) := by
  subst J
  exact compression_comp_embedding E K R

/-- Compression respects equality of the underlying embeddings. -/
theorem compression_congr_of_embedding_eq
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (R : Semantics.Operator A) {J K : B →ₗ[Complex] A} (hJ : J = K) :
    (LinearMap.adjoint J).comp (R.comp J) =
      (LinearMap.adjoint K).comp (R.comp K) := by
  exact congrArg (fun E => (LinearMap.adjoint E).comp (R.comp E)) hJ

/-- The selected `C`-sector embedding after restricting the second-cut `B` sector. -/
def secondCutSelectedCAfterBEmbedding
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) pB)
      (Semantics.CompositeSystem pC (M.fourFactorD region))) →ₗ[Complex]
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) pB)
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) :=
  TensorProduct.map (1 : Semantics.Operator
    (Semantics.CompositeSystem (M.fourFactorA region) pB))
    (TensorProduct.map pC.subtype (1 : Semantics.Operator (M.fourFactorD region)))

/-- The selected `C`-sector embedding in first-cut coordinates. -/
def firstCutSelectedCEmbedding
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pC : Submodule Complex (M.fourFactorC region)) :
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) pC)
      (M.fourFactorD region)) →ₗ[Complex]
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (M.fourFactorC region))
      (M.fourFactorD region)) :=
  tensorTripleSubtypeEmbedding
    (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
    (C := M.fourFactorD region) pC

/-- The selected `B`-sector embedding after restricting the first-cut `C` sector. -/
def firstCutSelectedBAfterCEmbedding
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (Semantics.CompositeSystem (M.fourFactorA region) pB) pC)
      (M.fourFactorD region)) →ₗ[Complex]
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) pC)
      (M.fourFactorD region)) :=
  TensorProduct.map
    (TensorProduct.map
      (TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region)) pB.subtype)
      (1 : Semantics.Operator pC))
    (1 : Semantics.Operator (M.fourFactorD region))

/-- The first-cut code compressed to one selected `C` sector. -/
noncomputable def firstCutSelectedCCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pC : Submodule Complex (M.fourFactorC region)) :
    Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) pC)
      (M.fourFactorD region)) :=
  (LinearMap.adjoint (M.firstCutSelectedCEmbedding region pC)).comp
    ((M.firstCutCodeLift region).comp (M.firstCutSelectedCEmbedding region pC))

/-- The common active block obtained by sequential second-cut then first-cut compression. -/
noncomputable def sequentialSecondCutJointCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) pB)
      (Semantics.CompositeSystem pC (M.fourFactorD region))) :=
  (LinearMap.adjoint (M.secondCutSelectedCAfterBEmbedding region pB pC)).comp
    ((M.secondCutSelectedBCompression region pB).comp
      (M.secondCutSelectedCAfterBEmbedding region pB pC))

/-- The common active block obtained by sequential first-cut then second-cut compression. -/
noncomputable def sequentialFirstCutJointCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem (Semantics.CompositeSystem (M.fourFactorA region) pB) pC)
      (M.fourFactorD region)) :=
  (LinearMap.adjoint (M.firstCutSelectedBAfterCEmbedding region pB pC)).comp
    ((M.firstCutSelectedCCompression region pC).comp
      (M.firstCutSelectedBAfterCEmbedding region pB pC))

/--
The simultaneous `B,C` compression in second-cut coordinates is literally the
second-cut `B` compression followed by the selected first-cut `C` sector.
This is the concrete embedding identity used to compare the two active BV03
blocks, rather than an additional factorization assumption.
-/
theorem jointBCSectorEmbeddingRight_eq_secondCutSector_then_firstCutSector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    jointBCSectorEmbeddingRight (A := M.fourFactorA region) pB pC =
      (M.secondCutSelectedBEmbedding region pB).comp
        (M.secondCutSelectedCAfterBEmbedding region pB pC) := by
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul ab cd =>
      induction ab using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
          induction cd using TensorProduct.induction_on with
          | zero => simp
          | tmul c d => rfl
          | add first second hfirst hsecond =>
              simpa only [TensorProduct.tmul_add, map_add] using
                congrArg₂ (· + ·) hfirst hsecond
      | add first second hfirst hsecond =>
          simpa only [TensorProduct.add_tmul, map_add] using
            congrArg₂ (· + ·) hfirst hsecond
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

set_option maxHeartbeats 800000 in
/-- The factorized second-cut embedding realizes the named sequential compression block. -/
theorem secondCutFactorizedCompression_eq_sequential
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    (LinearMap.adjoint ((M.secondCutSelectedBEmbedding region pB).comp
      (M.secondCutSelectedCAfterBEmbedding region pB pC))).comp
      ((M.secondCutCodeLift region).comp
        ((M.secondCutSelectedBEmbedding region pB).comp
          (M.secondCutSelectedCAfterBEmbedding region pB pC))) =
      M.sequentialSecondCutJointCompression region pB pC := by
  exact compression_comp_embedding
    (M.secondCutSelectedBEmbedding region pB)
    (M.secondCutSelectedCAfterBEmbedding region pB pC)
    (M.secondCutCodeLift region)

/-- The simultaneous active `B,C` compression in second-cut coordinates. -/
noncomputable def secondCutJointCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) pB)
      (Semantics.CompositeSystem pC (M.fourFactorD region))) :=
  (LinearMap.adjoint
    (jointBCSectorEmbeddingRight (A := M.fourFactorA region)
      (D := M.fourFactorD region) pB pC)).comp
    ((M.secondCutCodeLift region).comp
      (jointBCSectorEmbeddingRight (A := M.fourFactorA region)
        (D := M.fourFactorD region) pB pC))

set_option maxHeartbeats 800000 in
/--
Compressing `secondCutCodeLift` through the simultaneous active `B,C`
embedding is exactly its sequential `B`-then-`C` compression.  This names the
middle block shared by the fixed-witness D5 chain.
-/
theorem jointBCSectorCompressionRight_eq_sequentialSecondCutCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    M.secondCutJointCompression region pB pC =
      M.sequentialSecondCutJointCompression region pB pC := by
  unfold secondCutJointCompression
  have hJ := M.jointBCSectorEmbeddingRight_eq_secondCutSector_then_firstCutSector
    region pB pC
  calc
    (LinearMap.adjoint
      (jointBCSectorEmbeddingRight (A := M.fourFactorA region)
        (D := M.fourFactorD region) pB pC)).comp
      ((M.secondCutCodeLift region).comp
        (jointBCSectorEmbeddingRight (A := M.fourFactorA region)
          (D := M.fourFactorD region) pB pC)) =
      (LinearMap.adjoint ((M.secondCutSelectedBEmbedding region pB).comp
        (M.secondCutSelectedCAfterBEmbedding region pB pC))).comp
        ((M.secondCutCodeLift region).comp
          ((M.secondCutSelectedBEmbedding region pB).comp
            (M.secondCutSelectedCAfterBEmbedding region pB pC))) :=
        compression_congr_of_embedding_eq (M.secondCutCodeLift region) hJ
    _ = _ := M.secondCutFactorizedCompression_eq_sequential region pB pC

/--
The simultaneous `B,C` compression in first-cut coordinates is literally the
first-cut `C` compression following the selected second-cut `B` sector.  It
is the companion concrete coordinate identity for the common active block.
-/
theorem jointBCSectorEmbeddingLeft_eq_firstCutSector_after_secondCutSector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    jointBCSectorEmbeddingLeft (A := M.fourFactorA region) pB pC =
      (M.firstCutSelectedCEmbedding region pC).comp
        (M.firstCutSelectedBAfterCEmbedding region pB pC) := by
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul abc d =>
      induction abc using TensorProduct.induction_on with
      | zero => simp
      | tmul ab c =>
          induction ab using TensorProduct.induction_on with
          | zero => simp
          | tmul a b => rfl
          | add first second hfirst hsecond =>
              simpa only [TensorProduct.add_tmul, map_add] using
                congrArg₂ (· + ·) hfirst hsecond
      | add first second hfirst hsecond =>
          simpa only [TensorProduct.add_tmul, map_add] using
            congrArg₂ (· + ·) hfirst hsecond
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond
end BPTCommutingProjectorModel

end Bounds
end QEC
