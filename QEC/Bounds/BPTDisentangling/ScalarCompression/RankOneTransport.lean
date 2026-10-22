import QEC.Bounds.BPTDisentangling.ScalarCompression.RightProjection

/-!
# Rank-one scalar-compression transport

Generic finite-dimensional algebra used by both residual branches of the BPT
argument.
-/

noncomputable section

namespace QEC
namespace Bounds

open scoped ComplexOrder TensorProduct

universe u

namespace BPTCommutingProjectorModel

/--
After a unitary block transport exposes a normalized rank-one left factor, a
scalar compression relation descends to the right tensor factor.  Keeping this
step independent of the BPT coordinate types prevents their definitions from
being unfolded during tensor cancellation.
-/
theorem right_factor_scalar_compression_of_rankOne_transport
    {H A B : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B]
    (T : Semantics.UnitaryTransport H (Semantics.CompositeSystem A B))
    (R L : Semantics.Operator H) (phi : A) (hphi : ‖phi‖ = 1)
    (Q X : Semantics.Operator B) (scalar : Complex)
    (hR : T.conjOperator R =
      TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Q)
    (hL : T.conjOperator L =
      TensorProduct.map (1 : Semantics.Operator A) X)
    (hscalar : R * L * R = scalar • R) :
    Q * X * Q = scalar • Q := by
  have hinner : inner Complex phi phi = 1 := by
    rw [inner_self_eq_norm_sq_to_K]
    simpa [hphi]
  have hphi0 : phi ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hphi
    norm_num at hphi
  have htransported :
      TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Q *
          TensorProduct.map (1 : Semantics.Operator A) X *
          TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Q =
        scalar •
          TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Q := by
    calc
      _ = T.conjOperator R * T.conjOperator L * T.conjOperator R := by
        rw [hR, hL]
      _ = T.conjOperator (R * L * R) := by
        rw [Semantics.UnitaryTransport.conjOperator_mul,
          Semantics.UnitaryTransport.conjOperator_mul]
      _ = T.conjOperator (scalar • R) := congrArg T.conjOperator hscalar
      _ = scalar • T.conjOperator R :=
        T.conjOperatorLinearMap.map_smul scalar R
      _ = scalar •
          TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Q := by
        rw [hR]
  apply LinearMap.ext
  intro vector
  apply tmul_right_eq_of_tmul_left_eq_of_ne_zero phi hphi0
  have happly := congrArg
    (fun operator => operator (phi ⊗ₜ[Complex] vector)) htransported
  simpa [InnerProductSpace.rankOne_apply, hinner, hphi, TensorProduct.map_tmul,
    LinearMap.smul_apply] using happly

end BPTCommutingProjectorModel

end Bounds
end QEC
