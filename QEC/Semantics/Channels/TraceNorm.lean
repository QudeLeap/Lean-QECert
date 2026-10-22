import QEC.Semantics.Channels.Core
import QEC.Semantics.Core.OperatorTraceNorm
/-!
# Trace-norm contraction for finite quantum channels

This module proves the finite-dimensional CPTP data-processing inequality on
self-adjoint operators.  The proof constructs the positive and negative parts
of a self-adjoint operator, realizes the spectral sign as a dual trace-norm
witness, and then uses positivity and trace preservation of a quantum channel.

No contractivity field is added to `QuantumChannel`: contractivity is derived
from the existing complete-positivity and trace-preservation laws.
-/

universe u

namespace QEC.Semantics

open scoped ComplexOrder

noncomputable section

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

namespace QuantumChannel

variable {K L : Type u}
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

theorem map_isSymmetric (Phi : QuantumChannel H K) {A : Operator H}
    (hA : A.IsSymmetric) : (Phi A).IsSymmetric := by
  have hdecomp := positivePart_sub_negativePart A hA
  rw [← hdecomp, map_sub]
  exact (Phi.map_positive (positivePart_positive A)).isSymmetric.sub
    (Phi.map_positive (negativePart_positive A)).isSymmetric

/-- Finite CPTP maps contract the trace norm on self-adjoint operators. -/
theorem traceNorm_apply_le_of_isSymmetric [Nontrivial H] [Nontrivial K]
    (Phi : QuantumChannel H K) (A : Operator H) (hA : A.IsSymmetric) :
    traceNorm (Phi A) ≤ traceNorm A := by
  have hdecomp := positivePart_sub_negativePart A hA
  calc
    traceNorm (Phi A) =
        traceNorm (Phi (positivePart A) - Phi (negativePart A)) := by
      rw [← map_sub, hdecomp]
    _ ≤ traceNorm (Phi (positivePart A)) + traceNorm (-Phi (negativePart A)) := by
      simpa [sub_eq_add_neg] using
        traceNorm_add_le (Phi (positivePart A)) (-Phi (negativePart A))
    _ = traceNorm (Phi (positivePart A)) + traceNorm (Phi (negativePart A)) := by
      rw [traceNorm_neg]
    _ = Complex.re (LinearMap.trace Complex K (Phi (positivePart A))) +
        Complex.re (LinearMap.trace Complex K (Phi (negativePart A))) := by
      rw [traceNorm_eq_re_trace_of_positive _
          (Phi.map_positive (positivePart_positive A)),
        traceNorm_eq_re_trace_of_positive _
          (Phi.map_positive (negativePart_positive A))]
    _ = Complex.re (LinearMap.trace Complex H (positivePart A)) +
        Complex.re (LinearMap.trace Complex H (negativePart A)) := by
      rw [Phi.trace_map, Phi.trace_map]
    _ = traceNorm (positivePart A) + traceNorm (negativePart A) := by
      rw [traceNorm_eq_re_trace_of_positive _ (positivePart_positive A),
        traceNorm_eq_re_trace_of_positive _ (negativePart_positive A)]
    _ = traceNorm A := (traceNorm_eq_sum_parts A hA).symm

theorem traceNorm_mapDensity_eq_one [Nontrivial K]
    (Phi : QuantumChannel H K) (rho : DensityOperator H) :
    traceNorm (Phi rho.toOperator) = 1 := by
  simpa using (Phi.mapDensity rho).traceNorm_eq_one

theorem traceNorm_density_sub_le [Nontrivial H] [Nontrivial K]
    (Phi : QuantumChannel H K) (rho sigma : DensityOperator H) :
    traceNorm (Phi rho.toOperator - Phi sigma.toOperator) ≤
      traceNorm (rho.toOperator - sigma.toOperator) := by
  have hsym : (rho.toOperator - sigma.toOperator).IsSymmetric :=
    rho.positive.isSymmetric.sub sigma.positive.isSymmetric
  simpa [map_sub] using
    Phi.traceNorm_apply_le_of_isSymmetric (rho.toOperator - sigma.toOperator) hsym

theorem traceNorm_comp_apply_le_of_isSymmetric
    [Nontrivial H] [Nontrivial K] [Nontrivial L]
    (Psi : QuantumChannel K L) (Phi : QuantumChannel H K)
    (A : Operator H) (hA : A.IsSymmetric) :
    traceNorm ((comp Psi Phi) A) ≤ traceNorm A := by
  change traceNorm (Psi (Phi A)) ≤ traceNorm A
  calc
    traceNorm (Psi (Phi A)) ≤ traceNorm (Phi A) :=
      Psi.traceNorm_apply_le_of_isSymmetric (Phi A) (Phi.map_isSymmetric hA)
    _ ≤ traceNorm A := Phi.traceNorm_apply_le_of_isSymmetric A hA

end QuantumChannel

end

end QEC.Semantics
