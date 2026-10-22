import QEC.Bounds.GeometricLocalityTradeoff.SquarePartition
/-!
# BPT geometric commuting-projector tradeoff

The public BPT10 realization exposes the finite open square-lattice
commuting-projector model and the source measurement/no-information distance.
Its numerical coefficient is a Lean-QEC witness for the source's existential
locality-dependent constant.
-/

noncomputable section

namespace QEC
namespace Bounds

open scoped BigOperators

universe v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/--
[BPT10, Main result].  For the actual finite open square-lattice
commuting-projector model, the source measurement/no-information distance
obeys the geometric locality tradeoff.

The coefficient `16384 * w^4 * log_2(Q)` is Lean-QEC's explicit witness for
BPT10's existential constant depending only on the projector range `w` and
the uniform local-dimension bound `Q`; BPT10 does not state `16384`.
-/
theorem bpt_geometric_locality_tradeoff
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (distance : Nat)
    (hDistance : Semantics.QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (hdistance : 0 < distance)
    (hregular : L.lattice.rows = L.lattice.columns) :
    (parameter.encodedQubits : Real) * (distance : Real) ^ 2 <=
      (16384 : Real) * (M.interactionRange : Real) ^ 4 *
        Real.logb 2 (L.uniformDimensionBound : Real) * (L.lattice.siteCount : Real) := by
  cases distance with
  | zero => exact (Nat.not_lt_zero _ hdistance).elim
  | succ distance =>
      exact M.encodedQubits_mul_measurementDistance_sq_le_bpt_squarePartition
        parameter (Nat.succ distance) hDistance hregular

end BPTCommutingProjectorModel

end Bounds
end QEC
