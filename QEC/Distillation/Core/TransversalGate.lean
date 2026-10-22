import QEC.Semantics.Core.Definitions
/-!
# QEC.Distillation.TransversalGate

Exact encoded logical-gate semantics and proof-relevant finite physical-gate
factorizations.

The implementation relation is stronger than preservation of a code carrier:
it records the commuting equation for a specified logical gate.  The locality
interfaces separately retain the permitted local factors, their finite
supports, and the equation assembling them into the physical gate.
-/

universe u

namespace QEC
namespace Semantics
namespace UnitaryTransport

variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

/-- The identity unitary transport on a finite quantum system. -/
def identity (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] : UnitaryTransport H H where
  toLinearEquiv := LinearEquiv.refl Complex H
  map_inner := by
    intro x y
    rfl

@[simp]
theorem identity_apply (x : H) : identity H x = x :=
  rfl

/-- Sequential composition: first `U`, then `V`. -/
def trans (U : UnitaryTransport H K) (V : UnitaryTransport K L) :
    UnitaryTransport H L where
  toLinearEquiv := U.toLinearEquiv.trans V.toLinearEquiv
  map_inner := by
    intro x y
    exact (V.map_inner (U x) (U y)).trans (U.map_inner x y)

@[simp]
theorem trans_apply (U : UnitaryTransport H K) (V : UnitaryTransport K L) (x : H) :
    U.trans V x = V (U x) :=
  rfl

end UnitaryTransport
end Semantics

namespace Distillation

open Semantics

variable {Logical Physical Site : Type u}
variable [NormedAddCommGroup Logical] [InnerProductSpace Complex Logical]
variable [FiniteQuantumSystem Logical]
variable [NormedAddCommGroup Physical] [InnerProductSpace Complex Physical]
variable [FiniteQuantumSystem Physical]

/--
An encoded code explicitly identifies the logical Hilbert space with the
carrier of a code in the physical Hilbert space.
-/
structure EncodedCode (Logical Physical : Type u)
    [NormedAddCommGroup Logical] [InnerProductSpace Complex Logical]
    [FiniteQuantumSystem Logical]
    [NormedAddCommGroup Physical] [InnerProductSpace Complex Physical]
    [FiniteQuantumSystem Physical] where
  code : QuantumCode Physical
  encoding : Logical ≃ₗᵢ[Complex] code.carrier

namespace EncodedCode

/-- The ambient physical vector obtained by encoding a logical vector. -/
def encode (E : EncodedCode Logical Physical) (psi : Logical) : Physical :=
  E.encoding psi

@[simp]
theorem encode_mem (E : EncodedCode Logical Physical) (psi : Logical) :
    E.encode psi ∈ E.code.carrier :=
  (E.encoding psi).property

/-- Every vector in the code carrier has a logical preimage. -/
theorem exists_encode_eq_of_mem (E : EncodedCode Logical Physical) {x : Physical}
    (hx : x ∈ E.code.carrier) :
    ∃ psi : Logical, E.encode psi = x := by
  let xInCode : E.code.carrier := ⟨x, hx⟩
  refine ⟨E.encoding.symm xInCode, ?_⟩
  simp [encode, xInCode]

/--
A physical gate implements a specified logical gate when encoding commutes
with their actions pointwise.
-/
def ImplementsLogicalGate (E : EncodedCode Logical Physical)
    (physical : UnitaryTransport Physical Physical)
    (logical : UnitaryTransport Logical Logical) : Prop :=
  ∀ psi : Logical, physical (E.encode psi) = E.encode (logical psi)

namespace ImplementsLogicalGate

/-- Identity gates satisfy the encoded implementation equation. -/
theorem identity (E : EncodedCode Logical Physical) :
    E.ImplementsLogicalGate (UnitaryTransport.identity Physical)
      (UnitaryTransport.identity Logical) := by
  intro psi
  rfl

/-- Exact logical-gate implementations compose in the same order as their gates. -/
theorem trans (E : EncodedCode Logical Physical)
    {physical₁ physical₂ : UnitaryTransport Physical Physical}
    {logical₁ logical₂ : UnitaryTransport Logical Logical}
    (h₁ : E.ImplementsLogicalGate physical₁ logical₁)
    (h₂ : E.ImplementsLogicalGate physical₂ logical₂) :
    E.ImplementsLogicalGate (physical₁.trans physical₂) (logical₁.trans logical₂) := by
  intro psi
  simp only [UnitaryTransport.trans_apply]
  rw [h₁ psi, h₂ (logical₁ psi)]

/-- Implementing a logical gate sends code vectors back into the code carrier. -/
theorem maps_codeCarrier (E : EncodedCode Logical Physical)
    {physical : UnitaryTransport Physical Physical}
    {logical : UnitaryTransport Logical Logical}
    (h : E.ImplementsLogicalGate physical logical) {x : Physical}
    (hx : x ∈ E.code.carrier) :
    physical x ∈ E.code.carrier := by
  obtain ⟨psi, rfl⟩ := E.exists_encode_eq_of_mem hx
  rw [h psi]
  exact E.encode_mem (logical psi)

/-- The inverse physical gate implements the inverse logical gate. -/
theorem symm (E : EncodedCode Logical Physical)
    {physical : UnitaryTransport Physical Physical}
    {logical : UnitaryTransport Logical Logical}
    (h : E.ImplementsLogicalGate physical logical) :
    E.ImplementsLogicalGate physical.symm logical.symm := by
  intro psi
  have hpsi := congrArg physical.toLinearEquiv.symm (h (logical.symm psi))
  simpa [UnitaryTransport.symm] using hpsi.symm

/-- Exact logical implementation implies two-sided preservation of the code carrier. -/
theorem transportedBy (E : EncodedCode Logical Physical)
    {physical : UnitaryTransport Physical Physical}
    {logical : UnitaryTransport Logical Logical}
    (h : E.ImplementsLogicalGate physical logical) :
    QuantumCode.TransportedBy physical E.code E.code := by
  intro x
  constructor
  · exact h.maps_codeCarrier
  · intro hx
    have hback := maps_codeCarrier E (symm E h) hx
    simpa [UnitaryTransport.symm] using hback

end ImplementsLogicalGate
end EncodedCode

namespace UnitaryTransport

/-- Compose a finite ordered family of physical gates. -/
def composeList : List (UnitaryTransport Physical Physical) →
    UnitaryTransport Physical Physical
  | [] => Semantics.UnitaryTransport.identity Physical
  | gate :: gates => gate.trans (composeList gates)

/-- Compose a family indexed by `Fin n` in its canonical order. -/
def composeFamily {n : Nat} (gates : Fin n → UnitaryTransport Physical Physical) :
    UnitaryTransport Physical Physical :=
  composeList (List.ofFn gates)

end UnitaryTransport

/--
A finite physical-gate model.  `LocalGate support` is the type of permitted
local factors on exactly the supplied finite support; `realize` embeds such a
factor into the full physical system.
-/
structure FinitePhysicalGateModel (Site Physical : Type u)
    [Fintype Site] [DecidableEq Site]
    [NormedAddCommGroup Physical] [InnerProductSpace Complex Physical]
    [FiniteQuantumSystem Physical] where
  LocalGate : Finset Site → Type u
  realize : {support : Finset Site} → LocalGate support →
    UnitaryTransport Physical Physical

/-- One permitted support-indexed local factor. -/
structure LocalGateFactor [Fintype Site] [DecidableEq Site]
    (model : FinitePhysicalGateModel Site Physical) where
  support : Finset Site
  gate : model.LocalGate support

namespace LocalGateFactor

/-- Realize a local factor as a gate on the full physical system. -/
def realized [Fintype Site] [DecidableEq Site]
    {model : FinitePhysicalGateModel Site Physical}
    (factor : LocalGateFactor model) : UnitaryTransport Physical Physical :=
  model.realize factor.gate

end LocalGateFactor

/--
Proof-relevant finite factorization of a physical gate into permitted local
factors with disjoint supports.
-/
structure PhysicalGateFactorization [Fintype Site] [DecidableEq Site]
    (model : FinitePhysicalGateModel Site Physical)
    (physical : UnitaryTransport Physical Physical) where
  factorCount : Nat
  support : Fin factorCount → Finset Site
  factor : (j : Fin factorCount) → model.LocalGate (support j)
  pairwise_disjoint : ∀ ⦃i j : Fin factorCount⦄, i ≠ j →
    Disjoint (support i) (support j)
  realizes :
    UnitaryTransport.composeFamily (fun j => model.realize (factor j)) = physical

/-- A finite disjoint block cover of the physical sites. -/
structure FiniteBlockDecomposition (Site : Type u) [Fintype Site] [DecidableEq Site] where
  blockCount : Nat
  sites : Fin blockCount → Finset Site
  pairwise_disjoint : ∀ ⦃i j : Fin blockCount⦄, i ≠ j → Disjoint (sites i) (sites j)
  covers : Finset.univ.biUnion sites = Finset.univ

/-- Strong/sitewise transversality: every realized factor has support at most one. -/
structure SitewiseTransversalityData [Fintype Site] [DecidableEq Site]
    (model : FinitePhysicalGateModel Site Physical)
    (physical : UnitaryTransport Physical Physical)
    extends PhysicalGateFactorization model physical where
  support_card_le_one : ∀ j, (toPhysicalGateFactorization.support j).card ≤ 1

/--
Block transversality: factors realize the target gate and each factor remains
inside one block of an explicit finite disjoint cover.
-/
structure BlockTransversalityData [Fintype Site] [DecidableEq Site]
    (model : FinitePhysicalGateModel Site Physical)
    (physical : UnitaryTransport Physical Physical)
    (blocks : FiniteBlockDecomposition Site)
    extends PhysicalGateFactorization model physical where
  support_within_block : ∀ j, ∃ b,
    toPhysicalGateFactorization.support j ⊆ blocks.sites b

/--
Subset transversality: factors realize the target gate and every factor support
belongs to an explicit finite family of permitted subsets.
-/
structure SubsetTransversalityData [Fintype Site] [DecidableEq Site]
    (model : FinitePhysicalGateModel Site Physical)
    (physical : UnitaryTransport Physical Physical)
    (permittedSupports : Finset (Finset Site))
    extends PhysicalGateFactorization model physical where
  support_permitted : ∀ j,
    toPhysicalGateFactorization.support j ∈ permittedSupports

/-- A specified logical gate implemented by a sitewise-factorized physical gate. -/
structure SitewiseTransversalLogicalGate [Fintype Site] [DecidableEq Site]
    (E : EncodedCode Logical Physical)
    (logical : UnitaryTransport Logical Logical)
    (model : FinitePhysicalGateModel Site Physical) where
  physicalGate : UnitaryTransport Physical Physical
  implements : E.ImplementsLogicalGate physicalGate logical
  transversality : SitewiseTransversalityData model physicalGate

/-- A specified logical gate implemented by a block-factorized physical gate. -/
structure BlockTransversalLogicalGate [Fintype Site] [DecidableEq Site]
    (E : EncodedCode Logical Physical)
    (logical : UnitaryTransport Logical Logical)
    (model : FinitePhysicalGateModel Site Physical)
    (blocks : FiniteBlockDecomposition Site) where
  physicalGate : UnitaryTransport Physical Physical
  implements : E.ImplementsLogicalGate physicalGate logical
  transversality : BlockTransversalityData model physicalGate blocks

/-- A specified logical gate implemented by a subset-factorized physical gate. -/
structure SubsetTransversalLogicalGate [Fintype Site] [DecidableEq Site]
    (E : EncodedCode Logical Physical)
    (logical : UnitaryTransport Logical Logical)
    (model : FinitePhysicalGateModel Site Physical)
    (permittedSupports : Finset (Finset Site)) where
  physicalGate : UnitaryTransport Physical Physical
  implements : E.ImplementsLogicalGate physicalGate logical
  transversality : SubsetTransversalityData model physicalGate permittedSupports

end Distillation
end QEC
