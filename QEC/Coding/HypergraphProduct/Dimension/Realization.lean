import QEC.Coding.HypergraphProduct.Dimension.Coordinates
import QEC.Coding.ChainComplex.Duality

/-!
# Concrete coordinate realization of hypergraph-product dimensions

This module identifies the concrete finite-coordinate boundary maps of the
Tillich--Zémor hypergraph product with the abstract tensor maps whose kernels
were calculated in `HypergraphProductDimensionCoordinates`.
-/

noncomputable section

namespace QEC.Coding.HypergraphProduct

universe u v w

open TensorProduct

/-- The canonical coordinate equivalence between a tensor product of two word
spaces and the word space on the Cartesian product of their coordinates. -/
def wordTensorEquiv
    (F : Type u) (A : Type v) (B : Type w)
    [Field F] [Fintype B] [DecidableEq B] :
    (Word F A ⊗[F] Word F B) ≃ₗ[F] Word F (A × B) :=
  (TensorProduct.piScalarRight F F (Word F A) B).trans
    ((LinearEquiv.curry F F B A).symm.trans
      (LinearEquiv.funCongrLeft F F (Equiv.prodComm A B)))

@[simp]
theorem wordTensorEquiv_tmul_apply
    {F : Type u} {A : Type v} {B : Type w}
    [Field F] [Fintype B] [DecidableEq B]
    (x : Word F A) (y : Word F B) (a : A) (b : B) :
    wordTensorEquiv F A B (x ⊗ₜ[F] y) (a, b) = x a * y b := by
  simp [wordTensorEquiv, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, mul_comm]

/-- Splitting a word on a sum of coordinate types into its two blocks. -/
def wordSumEquiv (F : Type u) (A : Type v) (B : Type w) [Semiring F] :
    Word F (Sum A B) ≃ₗ[F] Word F A × Word F B :=
  LinearEquiv.sumPiEquivProdPi F A B (fun _ => F)

/-- The same block splitting, with the second physical block listed first. -/
def wordSumEquivSwap (F : Type u) (A : Type v) (B : Type w) [Semiring F] :
    Word F (Sum A B) ≃ₗ[F] Word F B × Word F A :=
  (wordSumEquiv F A B).trans (LinearEquiv.prodComm F (Word F A) (Word F B))

end QEC.Coding.HypergraphProduct
