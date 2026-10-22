import QEC.Coding.FourDimensionalToricCode.CoordinateSymmetry

/-!
# The finite linear energy barrier of the four-dimensional toric code

This module is the public integration layer for the project-derived finite
`Theta(L)` statement.  It combines the separator lower bound from #569, the
explicit membrane sweeps from #570, and the coordinate-symmetry closure over
all 63 nonzero coefficient vectors on the six membrane planes.

DKLP02 supplies the periodic four-dimensional toric model, membrane geometry,
and loop-energy interpretation.  The assembled min-max bounds below are a
formal project derivation, not a theorem quoted directly from DKLP02.

No thermodynamic-limit or memory-lifetime conclusion is made here.
-/

noncomputable section

namespace QEC.Coding.PeriodicCubical4

open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian

variable {L : Nat} [NeZero L] [Fact (1 < L)]

/-- The explicit primal sweep ends in the corresponding nontrivial membrane
sector used by the lower-bound theorem. -/
theorem primalMembraneSweepPath_hasPrimalMembraneEndpoint (z w : ZMod L) :
    HasPrimalMembraneEndpoint (primalMembraneSweepPath z w) := by
  refine ⟨z, w, 0, ?_⟩
  simp [primalMembraneError]

/-- The explicit dual sweep ends in the corresponding nontrivial membrane
sector used by the lower-bound theorem. -/
theorem dualMembraneSweepPath_hasDualMembraneEndpoint (x y : ZMod L) :
    HasDualMembraneEndpoint (dualMembraneSweepPath x y) := by
  refine ⟨x, y, 0, ?_⟩
  simp [dualMembraneError]

/--
Finite `Theta(L)` energy-barrier bounds for every nonzero primal and dual
coordinate-membrane sector of the periodic four-dimensional toric code.

Every single-plaquette Pauli path ending in any specified sector has BT
excess-energy height at least `L / 2`. Conversely, concatenating at most six
coordinate-framed basis sweeps gives an explicit path to every sector with
height at most `384 * L`. Each individual basis sweep retains the sharper
`64 * L` bound proved in #570.
-/
theorem fourDimensionalToric_linearEnergyBarrier_theta :
    (∀ (s : MembraneSector) (γ : PauliErrorPath (ι := Plaquette L)),
      HasPrimalSectorEndpoint γ s →
        L / 2 ≤ (toricHamiltonian (L := L)).pathHeight γ) ∧
    (∀ (s : MembraneSector) (γ : PauliErrorPath (ι := Plaquette L)),
      HasDualSectorEndpoint γ s →
        L / 2 ≤ (toricHamiltonian (L := L)).pathHeight γ) ∧
    (∀ s : MembraneSector,
      HasPrimalSectorEndpoint (primalSectorSweepPath (L := L) s) s ∧
        (toricHamiltonian (L := L)).pathHeight
          (primalSectorSweepPath (L := L) s) ≤ 384 * L) ∧
    (∀ s : MembraneSector,
      HasDualSectorEndpoint (dualSectorSweepPath (L := L) s) s ∧
        (toricHamiltonian (L := L)).pathHeight
          (dualSectorSweepPath (L := L) s) ≤ 384 * L) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s gamma hgamma
    exact half_le_pathHeight_of_hasPrimalSectorEndpoint gamma s hgamma
  · intro s gamma hgamma
    exact half_le_pathHeight_of_hasDualSectorEndpoint gamma s hgamma
  · intro s
    exact ⟨primalSectorSweepPath_hasPrimalSectorEndpoint s,
      pathHeight_primalSectorSweepPath_le s⟩
  · intro s
    exact ⟨dualSectorSweepPath_hasDualSectorEndpoint s,
      pathHeight_dualSectorSweepPath_le s⟩

end QEC.Coding.PeriodicCubical4
