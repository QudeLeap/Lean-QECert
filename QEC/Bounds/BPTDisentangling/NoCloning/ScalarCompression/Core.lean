import QEC.Bounds.BPTDisentangling.NoCloning.ScalarCompression.Data

/-!
# BPT scalar-compression transport core

Cacheable internal proof layer for the finite-dimensional BPT Disentangling Lemma.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

set_option maxHeartbeats 800000

/--
Unitary coordinates preserve a scalar compression equation.  This is the last
generic transport used after the active isometric-sector compression below.
-/
theorem unitaryTransport_conj_scalar_compression
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (Q R : Semantics.Operator H)
    (scalar : Complex) (hscalar : Q * R * Q = scalar • Q) :
    U.conjOperator Q * U.conjOperator R * U.conjOperator Q =
      scalar • U.conjOperator Q := by
  calc
    U.conjOperator Q * U.conjOperator R * U.conjOperator Q =
        U.conjOperator (Q * R * Q) := by
          rw [Semantics.UnitaryTransport.conjOperator_mul,
            Semantics.UnitaryTransport.conjOperator_mul]
    _ = U.conjOperator (scalar • Q) := congrArg U.conjOperator hscalar
    _ = scalar • U.conjOperator Q := U.conjOperatorLinearMap.map_smul scalar Q

/--
Scalar compression survives an active isometric-sector compression and a
subsequent unitary coordinate transport.  The active support is derived from
the ambient orthogonal projection; it is not a scalar-compression hypothesis.
-/
theorem activeIsometric_unitaryTransport_scalar_compression_of_intertwining
    {H K K' : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup K'] [InnerProductSpace Complex K']
    [Semantics.FiniteQuantumSystem K']
    (J : H →ₗ[Complex] K) (Jadj : K →ₗ[Complex] H)
    (Q R : Semantics.Operator K) (Rsub : Semantics.Operator H)
    (T : Semantics.UnitaryTransport H K') (scalar : Complex)
    (hJadj_eq : LinearMap.adjoint J = Jadj)
    (hQ : Q.IsSymmetricProjection)
    (hright : Q.comp (J.comp Jadj) = Q)
    (hscalar : Q * R * Q = scalar • Q)
    (hintertwines : J.comp Rsub = R.comp J) :
    T.conjOperator (Jadj.comp (Q.comp J)) * T.conjOperator Rsub *
        T.conjOperator (Jadj.comp (Q.comp J)) =
      scalar • T.conjOperator (Jadj.comp (Q.comp J)) := by
  have hleft : (J.comp Jadj).comp Q = Q :=
    isometricCompression_left_support_of_right_support J Jadj Q hJadj_eq hQ hright
  have hcompressed :
      (Jadj.comp (Q.comp J)) * Rsub * (Jadj.comp (Q.comp J)) =
        scalar • (Jadj.comp (Q.comp J)) :=
    isometricCompression_scalar_of_intertwining J Jadj Q R Rsub scalar hleft hscalar
      hintertwines
  exact unitaryTransport_conj_scalar_compression T
    (Jadj.comp (Q.comp J)) Rsub scalar hcompressed

/--
Zero-extending a probe on an active subtype intertwines the subtype coordinates
with the physical coordinates.  This is the concrete lifting step used for
the external-boundary `C'` probes below.
-/
theorem subtypeTensor_right_intertwines_zeroExtension
    {N C D : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N]
    [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D]
    [Semantics.FiniteQuantumSystem D]
    (p : Submodule Complex C) (E : Semantics.Operator p) :
    (TensorProduct.map (1 : Semantics.Operator N)
      (TensorProduct.map p.subtype (1 : Semantics.Operator D))).comp
      (TensorProduct.map (1 : Semantics.Operator N)
        (TensorProduct.map E (1 : Semantics.Operator D))) =
    (TensorProduct.map (1 : Semantics.Operator N)
      (TensorProduct.map (p.subtype.comp (E.comp (LinearMap.adjoint p.subtype)))
        (1 : Semantics.Operator D))).comp
      (TensorProduct.map (1 : Semantics.Operator N)
        (TensorProduct.map p.subtype (1 : Semantics.Operator D))) := by
  rw [← TensorProduct.map_comp, ← TensorProduct.map_comp,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp]
  simp only [LinearMap.comp_assoc]
  rw [adjoint_submoduleSubtype_comp_subtype_eq_one p]
  rfl

end BPTCommutingProjectorModel

end Bounds
end QEC
