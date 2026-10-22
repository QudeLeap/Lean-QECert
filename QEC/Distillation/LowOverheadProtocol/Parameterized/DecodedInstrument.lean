import QEC.Distillation.LowOverheadProtocol.Parameterized.PhysicalEndpoint
import QEC.Distillation.LowOverheadProtocol.Parameterized.Decoder
import QEC.Semantics.Channels.Instrument
import QEC.Semantics.Instruments.TensorPower.BornMass
/-!
# Parameterized HH18 decoded finite instrument

This internal API packages one actual parameterized HH18 block as a finite
instrument.  Its raw index retains the selected Kraus branches of resource
consumption and total decoding together with the real postselection syndrome.
Only the visible outcome is coarsened to `DistillationOutcome`.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

local instance instDecodedInstrumentClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The raw branches after actual resource consumption and real syndrome
postselection. -/
abbrev resourcePostselectionRawIndex {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) : Type :=
  Sigma fun _ : Fin ((resourceConsumerChannel h hdegree).chosenKrausCount) =>
    Syndrome w r m

/-- The complete resource-consumption and syndrome-postselection instrument
before total logical decoding. -/
noncomputable def resourcePostselectionInstrument {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    FiniteInstrument (resourcePostselectionRawIndex h hdegree)
      (Sigma fun _ : PUnit => DistillationOutcome)
      (PhysicalRegister m w) (PhysicalRegister m w) :=
  (QuantumChannel.toFiniteInstrument (resourceConsumerChannel h hdegree)).bindDependent
    (fun _ => postselectionInstrument h)

/-- Completeness of the actual resource-consumption and postselection
instrument. -/
theorem resourcePostselectionInstrument_complete {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    (resourcePostselectionInstrument h hdegree).kraus.Complete := by
  exact FiniteInstrument.bindDependent_complete
    (QuantumChannel.toFiniteInstrument (resourceConsumerChannel h hdegree))
    (fun _ => postselectionInstrument h)
    (QuantumChannel.toFiniteInstrument_complete (resourceConsumerChannel h hdegree))
    (fun _ => postselectionInstrument_complete h)

/-- The raw branches of one fully decoded block.  The outer sigma fibre is the
real decoder Kraus index selected after the resource-and-syndrome branch. -/
abbrev decodedRawIndex {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) : Type :=
  Sigma fun _ : resourcePostselectionRawIndex h hdegree =>
    Fin ((decoderChannel h).chosenKrausCount)

/-- The literal three-stage raw instrument, retaining both channel Kraus
indices and the physical syndrome before observation coarsening. -/
noncomputable def decodedRawInstrument {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    FiniteInstrument (decodedRawIndex h hdegree)
      (Sigma fun _ : (Sigma fun _ : PUnit => DistillationOutcome) => PUnit)
      (PhysicalRegister m w) (LogicalRegister m w) :=
  (resourcePostselectionInstrument h hdegree).bindDependent
    (fun _ => QuantumChannel.toFiniteInstrument (decoderChannel h))

/-- Completeness of the literal decoded raw Kraus family. -/
theorem decodedRawInstrument_complete {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    (decodedRawInstrument h hdegree).kraus.Complete := by
  exact FiniteInstrument.bindDependent_complete
    (resourcePostselectionInstrument h hdegree)
    (fun _ => QuantumChannel.toFiniteInstrument (decoderChannel h))
    (resourcePostselectionInstrument_complete h hdegree)
    (fun _ => QuantumChannel.toFiniteInstrument_complete (decoderChannel h))

/-- One actual decoded HH18 block as a finite instrument.  The raw Kraus index
is unchanged from `decodedRawInstrument`; only the two unit observations are
discarded, leaving the real coarse postselection outcome. -/
noncomputable def decodedInstrument {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    FiniteInstrument (decodedRawIndex h hdegree) DistillationOutcome
      (PhysicalRegister m w) (LogicalRegister m w) where
  kraus := (decodedRawInstrument h hdegree).kraus
  observe := fun index => (postselectionInstrument h).observe index.1.2

/-- The visible observation is exactly the real postselection outcome of the
retained syndrome branch. -/
theorem decodedInstrument_observe {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (index : decodedRawIndex h hdegree) :
    (decodedInstrument h hdegree).observe index =
      (postselectionInstrument h).observe index.1.2 :=
  rfl

/-- Coarsening only observations leaves the actual decoded Kraus family
complete. -/
theorem decodedInstrument_complete {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    (decodedInstrument h hdegree).kraus.Complete :=
  decodedRawInstrument_complete h hdegree

/-- Coarsening the two unit observations preserves the Born weight of each
real postselection outcome. -/
theorem decodedInstrument_bornWeight_eq_decodedRawInstrument {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (outcome : DistillationOutcome) (rho : DensityOperator (PhysicalRegister m w)) :
    (decodedInstrument h hdegree).bornWeight outcome rho =
      (decodedRawInstrument h hdegree).bornWeight
        ⟨⟨PUnit.unit, outcome⟩, PUnit.unit⟩ rho := by
  unfold FiniteInstrument.bornWeight
  congr 1
  congr 1
  unfold FiniteInstrument.branchOperator
  apply Finset.sum_congr rfl
  intro index _
  simp [decodedInstrument, decodedRawInstrument, resourcePostselectionInstrument,
    FiniteInstrument.bindDependent]

/-- Before total decoding, the retained visible branch is exactly the real
postselection branch after actual resource consumption. -/
theorem resourcePostselectionInstrument_branchOperator {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (outcome : DistillationOutcome) (A : Operator (PhysicalRegister m w)) :
    (resourcePostselectionInstrument h hdegree).branchOperator
        ⟨PUnit.unit, outcome⟩ A =
      (postselectionInstrument h).branchOperator outcome
        (resourceConsumerChannel h hdegree A) := by
  rw [← QuantumChannel.toFiniteInstrument_inducedMap_apply
    (resourceConsumerChannel h hdegree) A]
  unfold resourcePostselectionInstrument FiniteInstrument.branchOperator
  rw [Fintype.sum_sigma]
  simp only [FiniteInstrument.bindDependent, QuantumChannel.toFiniteInstrument,
    FiniteKrausFamily.inducedMap_apply, LinearMap.adjoint_comp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro syndrome _
  by_cases hsyndrome : (postselectionInstrument h).observe syndrome = outcome
  · simp only [hsyndrome, if_true]
    ext x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    rw [← map_sum]
  · simp [hsyndrome]

/-- The resource-and-postselection instrument has precisely the coarse
postselection Born weight after the actual resource channel. -/
theorem resourcePostselectionInstrument_bornWeight {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (outcome : DistillationOutcome) (rho : DensityOperator (PhysicalRegister m w)) :
    (resourcePostselectionInstrument h hdegree).bornWeight
        ⟨PUnit.unit, outcome⟩ rho =
      postselectionWeight h outcome
        ((resourceConsumerChannel h hdegree).mapDensity rho) := by
  unfold postselectionWeight FiniteInstrument.bornWeight
  rw [resourcePostselectionInstrument_branchOperator h hdegree outcome rho.toOperator]
  rfl

/-- A complete decoder contributes no additional visible Born mass. -/
theorem decodedInstrument_bornWeight_eq_resourcePostselection {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (outcome : DistillationOutcome) (rho : DensityOperator (PhysicalRegister m w)) :
    (decodedInstrument h hdegree).bornWeight outcome rho =
      (resourcePostselectionInstrument h hdegree).bornWeight
        ⟨PUnit.unit, outcome⟩ rho := by
  rw [decodedInstrument_bornWeight_eq_decodedRawInstrument]
  change ((resourcePostselectionInstrument h hdegree).bindDependent
      (fun _ => QuantumChannel.toFiniteInstrument (decoderChannel h))).bornWeight
        ⟨⟨PUnit.unit, outcome⟩, PUnit.unit⟩ rho = _
  exact FiniteInstrument.bindDependent_bornWeight_punit
    (resourcePostselectionInstrument h hdegree)
    (fun _ => QuantumChannel.toFiniteInstrument (decoderChannel h))
    (fun _ => QuantumChannel.toFiniteInstrument_complete (decoderChannel h))
    ⟨PUnit.unit, outcome⟩ rho

/-- On the actual measured-resource record, each decoded visible Born weight
is exactly the existing physical endpoint weight. -/
theorem decodedInstrument_bornWeight_prepareMeasuredResources {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace)
    (outcome : DistillationOutcome) :
    (decodedInstrument h hdegree).bornWeight outcome
        (prepareMeasuredResources m w inputs) =
      endpointWeight h hdegree inputs outcome := by
  rw [decodedInstrument_bornWeight_eq_resourcePostselection,
    resourcePostselectionInstrument_bornWeight]
  rfl

/-- The noisy accepted decoded branch has exactly the existing accepted
Bernoulli mass. -/
theorem decodedInstrument_bornWeight_noisyResources_accepted_eq_acceptedBernoulliMass
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (decodedInstrument h hdegree).bornWeight .accepted
        (prepareMeasuredResources m w (noisyResources m w epsilon)) =
      acceptedBernoulliMass w r m epsilon := by
  rw [decodedInstrument_bornWeight_prepareMeasuredResources]
  exact endpointWeight_accepted_eq_acceptedBernoulliMass h hdegree epsilon

end HH18Parameterized
end Distillation
end QEC
