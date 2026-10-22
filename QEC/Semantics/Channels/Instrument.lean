import QEC.Semantics.Channels.ChoiKraus
import QEC.Semantics.Instruments.Sequential.DependentComposition
/-!
# Finite instruments chosen from quantum channels

Every finite-dimensional quantum channel admits a finite Choi--Kraus family.
This module chooses one such family and exposes it as a complete instrument
with its sole observable outcome in `PUnit`.
-/

universe u

namespace QEC
namespace Semantics

open scoped BigOperators ComplexOrder

noncomputable section

namespace QuantumChannel

variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

/-- The finite raw Kraus-index cardinality selected from a channel's Choi representation. -/
noncomputable def chosenKrausCount (Φ : QuantumChannel H K) : Nat :=
  Classical.choose Φ.exists_finiteKrausFamily_representation

/-- A chosen finite Kraus family representing the channel. -/
noncomputable def chosenKrausFamily (Φ : QuantumChannel H K) :
    FiniteKrausFamily (Fin (Φ.chosenKrausCount)) H K :=
  Classical.choose
    (Classical.choose_spec Φ.exists_finiteKrausFamily_representation)

/-- The chosen family is complete and has exactly the channel's operator map. -/
theorem chosenKrausFamily_representation (Φ : QuantumChannel H K) :
    (Φ.chosenKrausFamily).Complete ∧
      (Φ.chosenKrausFamily).inducedMap = Φ.toLinearMap :=
  Classical.choose_spec
    (Classical.choose_spec Φ.exists_finiteKrausFamily_representation)

/-- Completeness of the chosen finite Choi--Kraus family. -/
theorem chosenKrausFamily_complete (Φ : QuantumChannel H K) :
    (Φ.chosenKrausFamily).Complete :=
  (Φ.chosenKrausFamily_representation).1

/-- The chosen finite Choi--Kraus family induces exactly the channel map. -/
theorem chosenKrausFamily_inducedMap_eq (Φ : QuantumChannel H K) :
    (Φ.chosenKrausFamily).inducedMap = Φ.toLinearMap :=
  (Φ.chosenKrausFamily_representation).2

/--
Forget the raw chosen Kraus index at the observable level.

For an outcome-indexed channel family, the functions
`fun outcome => (channels outcome).toFiniteInstrument` can be supplied
directly to `FiniteInstrument.bindDependent`.
-/
noncomputable def toFiniteInstrument (Φ : QuantumChannel H K) :
    FiniteInstrument (Fin (Φ.chosenKrausCount)) PUnit.{1} H K where
  kraus := Φ.chosenKrausFamily
  observe := fun _ => PUnit.unit

/-- The raw family of the unit-observed instrument is the chosen Choi--Kraus family. -/
theorem toFiniteInstrument_kraus (Φ : QuantumChannel H K) :
    (Φ.toFiniteInstrument).kraus = Φ.chosenKrausFamily :=
  rfl

/-- The unit-observed chosen-Kraus instrument is complete. -/
theorem toFiniteInstrument_complete (Φ : QuantumChannel H K) :
    (Φ.toFiniteInstrument).kraus.Complete :=
  Φ.chosenKrausFamily_complete

/-- The induced map of the unit-observed instrument is exactly the channel map. -/
theorem toFiniteInstrument_inducedMap_eq (Φ : QuantumChannel H K) :
    (Φ.toFiniteInstrument).kraus.inducedMap = Φ.toLinearMap :=
  Φ.chosenKrausFamily_inducedMap_eq

/-- Pointwise form of the exact chosen-instrument/channel map equality. -/
theorem toFiniteInstrument_inducedMap_apply (Φ : QuantumChannel H K)
    (A : Operator H) :
    (Φ.toFiniteInstrument).kraus.inducedMap A = Φ A := by
  exact LinearMap.congr_fun Φ.toFiniteInstrument_inducedMap_eq A

/-- The sole observed outcome has normalized total Born mass. -/
theorem toFiniteInstrument_sum_bornWeight_eq_one (Φ : QuantumChannel H K)
    (rho : DensityOperator H) :
    ∑ outcome, (Φ.toFiniteInstrument).bornWeight outcome rho = 1 :=
  (Φ.toFiniteInstrument).sum_bornWeight_eq_one Φ.toFiniteInstrument_complete rho

end QuantumChannel

end
end Semantics
end QEC
