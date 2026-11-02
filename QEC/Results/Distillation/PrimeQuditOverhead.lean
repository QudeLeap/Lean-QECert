import Batteries.Tactic.OpenPrivate
import QEC.Distillation.PrimeQuditProtocol.VanishingOverhead

/-!
# Prime-qudit vanishing overhead

Final theorem assembly over the reusable Distillation methods.
-/

noncomputable section

namespace QEC.Distillation.KT19VanishingOverhead

open Semantics
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19Protocol
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open Filter Topology
open scoped BigOperators

attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype

-- Retain the concrete physical witnesses already present in the complete type.
open private kt19SmallIIDLaw kt19SmallIIDLaw_nonneg kt19SmallIIDLaw_sum
  kt19FixedFamilyPhysicalPackage
  from QEC.Distillation.PrimeQuditProtocol.VanishingOverhead

/-- KT19's terminal result has two deliberately separate quantifier layers.
The first is a fixed-prime physical statement for every admissible displayed
row family.  The second selects unbounded concrete primes only to make that
fixed-prime exponent arbitrarily small; it never holds the alphabet,
resource, gate, or protocol fixed while the prime changes. -/
theorem kt19_qudit_zero_exponent :
    (∀ (p l k : Nat) (hp : Nat.Prime p) (hfive : 5 ≤ p)
        (hadmissible : Admissible p l k) (hdistance : 2 ≤ l - k),
      letI : NeZero p := ⟨hp.ne_zero⟩
      letI : Fact p.Prime := ⟨hp⟩
      ∃ family : KT19DistillationFamily p l k,
        family = kt19ExplicitFixedPrimeDistillationFamily p l k hfive hadmissible ∧
          let mu := kt19SmallIIDLaw family
          let hmu_nonneg := kt19SmallIIDLaw_nonneg family
          let hmu_sum := kt19SmallIIDLaw_sum family
          ∃ resource : DensityOperator (KT19SingleQudit.{0} p),
            ∃ gate : UnitaryTransport
                (PrimeQuditRegister p (KeptPunctureLocation p k))
                (PrimeQuditRegister p (KeptPunctureLocation p k)),
              ∃ protocol : MagicStateDistillationProtocol (KT19SingleQudit.{0} p)
                  (PrimeQuditRegister p (KeptPunctureLocation p k))
                  (PrimeQuditRegister p (Fin k)),
                resource = family.inputResource mu hmu_nonneg hmu_sum ∧
                  gate = family.physicalGate ∧
                    protocol = family.protocol mu hmu_nonneg hmu_sum ∧
                      protocol.run = family.run mu hmu_nonneg hmu_sum ∧
                        Admissible p l k ∧
                          2 ≤ l - k ∧
                            kt19Length p k = p - k ∧
                              kt19LogicalDimension p l k = k ∧
                                kt19SafeDistance p l k ≥ l - k ∧
                                  stabilizerCarrier family.rowFamily =
                                    (shortenedReedSolomonCode p l k).carrier ∧
                                    family.encodedCode.ImplementsLogicalGate gate
                                      family.rowFamily.logicalInverseU13 ∧
                                      0 < kt19ErrorRate mu ∧
                                        ∃ coefficient : ℝ,
                                          0 < coefficient ∧
                                            coefficient =
                                              kt19FixedPrimeCostCoefficient family mu ∧
                                            kt19FixedPrimeGamma p l k =
                                              Real.log (((p - k : Nat) : ℝ) / (k : ℝ)) /
                                                Real.log ((l - k : Nat) : ℝ) ∧
                                            Tendsto (fun depth : Nat =>
                                              kt19FixedPrimeScheduleTargetError family mu depth)
                                              atTop (𝓝 0) ∧
                                            Tendsto (fun depth : Nat =>
                                              kt19FixedPrimeActualOutputError family mu
                                                hmu_nonneg hmu_sum depth)
                                              atTop (𝓝 0) ∧
                                            DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
                                              (fun depth => kt19FixedPrimeInputSlots p k depth)
                                              (fun depth => kt19FixedPrimeOutputSlots k depth)
                                              (kt19FixedPrimeScheduleTargetError family mu)
                                              (kt19FixedPrimeActualOutputError family mu
                                                hmu_nonneg hmu_sum)
                                              (kt19FixedPrimeExpectedYield family mu
                                                hmu_nonneg hmu_sum)
                                              (kt19FixedPrimeGamma p l k) coefficient) ∧
      ∀ (bound : Nat) (eta : ℝ), 0 < eta →
        ∃ p : Nat, ∃ hp : Nat.Prime p, ∃ hlarge : 32 ≤ p,
          bound ≤ p ∧ p ≡ 1 [MOD 8] ∧
            letI : NeZero p := ⟨hp.ne_zero⟩
            letI : Fact p.Prime := ⟨hp⟩
            ∃ family : KT19DistillationFamily p (kt19ExplicitL p) (kt19ExplicitK p),
              family = kt19ExplicitDistillationFamily p hlarge ∧
                kt19FixedPrimeGamma p (kt19ExplicitL p) (kt19ExplicitK p) < eta ∧
                let mu := kt19SmallIIDLaw family
                let hmu_nonneg := kt19SmallIIDLaw_nonneg family
                let hmu_sum := kt19SmallIIDLaw_sum family
                ∃ resource : DensityOperator (KT19SingleQudit.{0} p),
                  ∃ gate : UnitaryTransport
                      (PrimeQuditRegister p
                        (KeptPunctureLocation p (kt19ExplicitK p)))
                      (PrimeQuditRegister p
                        (KeptPunctureLocation p (kt19ExplicitK p))),
                    ∃ protocol : MagicStateDistillationProtocol
                        (KT19SingleQudit.{0} p)
                        (PrimeQuditRegister p
                          (KeptPunctureLocation p (kt19ExplicitK p)))
                        (PrimeQuditRegister p (Fin (kt19ExplicitK p))),
                      resource = family.inputResource mu hmu_nonneg hmu_sum ∧
                        gate = family.physicalGate ∧
                          protocol = family.protocol mu hmu_nonneg hmu_sum ∧
                            protocol.run = family.run mu hmu_nonneg hmu_sum ∧
                              Admissible p (kt19ExplicitL p) (kt19ExplicitK p) ∧
                                stabilizerCarrier family.rowFamily =
                                  (shortenedReedSolomonCode p (kt19ExplicitL p)
                                    (kt19ExplicitK p)).carrier ∧
                                  family.encodedCode.ImplementsLogicalGate gate
                                    family.rowFamily.logicalInverseU13 := by
  constructor
  · intro p l k hp hfive hadmissible hdistance
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Fact p.Prime := ⟨hp⟩
    let family : KT19DistillationFamily p l k :=
      kt19ExplicitFixedPrimeDistillationFamily p l k hfive hadmissible
    refine ⟨family, rfl, ?_⟩
    exact kt19FixedFamilyPhysicalPackage family hdistance
  · intro bound eta heta
    rcases kt19ChangingPrimeExponent bound eta heta with
      ⟨p, hbound, hp, hlarge, hmod, hgamma⟩
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Fact p.Prime := ⟨hp⟩
    let family : KT19DistillationFamily p (kt19ExplicitL p) (kt19ExplicitK p) :=
      kt19ExplicitDistillationFamily p hlarge
    let mu : ZMod p → ℝ := kt19SmallIIDLaw family
    have hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a :=
      kt19SmallIIDLaw_nonneg family
    have hmu_sum : ∑ a : ZMod p, mu a = 1 :=
      kt19SmallIIDLaw_sum family
    refine ⟨p, hp, hlarge, hbound, hmod, ?_⟩
    change ∃ family : KT19DistillationFamily p (kt19ExplicitL p) (kt19ExplicitK p),
      family = kt19ExplicitDistillationFamily p hlarge ∧
        kt19FixedPrimeGamma p (kt19ExplicitL p) (kt19ExplicitK p) < eta ∧
        let mu := kt19SmallIIDLaw family
        let hmu_nonneg := kt19SmallIIDLaw_nonneg family
        let hmu_sum := kt19SmallIIDLaw_sum family
        ∃ resource : DensityOperator (KT19SingleQudit.{0} p),
          ∃ gate : UnitaryTransport
              (PrimeQuditRegister p (KeptPunctureLocation p (kt19ExplicitK p)))
              (PrimeQuditRegister p (KeptPunctureLocation p (kt19ExplicitK p))),
            ∃ protocol : MagicStateDistillationProtocol (KT19SingleQudit.{0} p)
                (PrimeQuditRegister p (KeptPunctureLocation p (kt19ExplicitK p)))
                (PrimeQuditRegister p (Fin (kt19ExplicitK p))),
              resource = family.inputResource mu hmu_nonneg hmu_sum ∧
                gate = family.physicalGate ∧
                  protocol = family.protocol mu hmu_nonneg hmu_sum ∧
                    protocol.run = family.run mu hmu_nonneg hmu_sum ∧
                      Admissible p (kt19ExplicitL p) (kt19ExplicitK p) ∧
                        stabilizerCarrier family.rowFamily =
                          (shortenedReedSolomonCode p (kt19ExplicitL p)
                            (kt19ExplicitK p)).carrier ∧
                          family.encodedCode.ImplementsLogicalGate gate
                            family.rowFamily.logicalInverseU13
    refine ⟨family, rfl, hgamma, ?_⟩
    change ∃ resource : DensityOperator (KT19SingleQudit.{0} p),
      ∃ gate : UnitaryTransport
          (PrimeQuditRegister p (KeptPunctureLocation p (kt19ExplicitK p)))
          (PrimeQuditRegister p (KeptPunctureLocation p (kt19ExplicitK p))),
        ∃ protocol : MagicStateDistillationProtocol (KT19SingleQudit.{0} p)
            (PrimeQuditRegister p (KeptPunctureLocation p (kt19ExplicitK p)))
            (PrimeQuditRegister p (Fin (kt19ExplicitK p))),
          resource = family.inputResource mu hmu_nonneg hmu_sum ∧
            gate = family.physicalGate ∧
              protocol = family.protocol mu hmu_nonneg hmu_sum ∧
                protocol.run = family.run mu hmu_nonneg hmu_sum ∧
                  Admissible p (kt19ExplicitL p) (kt19ExplicitK p) ∧
                    stabilizerCarrier family.rowFamily =
                      (shortenedReedSolomonCode p (kt19ExplicitL p)
                        (kt19ExplicitK p)).carrier ∧
                      family.encodedCode.ImplementsLogicalGate gate
                        family.rowFamily.logicalInverseU13
    refine ⟨family.inputResource mu hmu_nonneg hmu_sum, family.physicalGate,
      family.protocol mu hmu_nonneg hmu_sum, rfl, rfl, rfl, rfl,
      family.admissible, family.stabilizerCarrier_eq_shortened,
      KT19DistillationFamily.physicalGate_implements_inverseLogicalU13 family⟩

end QEC.Distillation.KT19VanishingOverhead
